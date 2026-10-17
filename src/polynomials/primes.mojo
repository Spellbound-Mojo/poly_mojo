"""The fixed descending prime sequence and exact Chinese remaindering."""
from std.atomic import Atomic, Ordering
from std.ffi import _get_global
from std.memory import alloc, dealloc, Layout, ThinAllocation
from apn_mojo import Integer, div_rem_euclid
from .errors import Budget, PolyError, PolyErrorKind, _allocation, _sum
from .coefficients import ZZ, _work, _prime, _mod_mul, _mod_pow


@fieldwise_init
struct _PrimeCache(Movable):
    var busy: Atomic[Int64]
    var values: List[UInt64]


comptime _Context = Optional[Pointer[NoneType, MutUntrackedOrigin]]


def _start_cache() -> _Context:
    var block = alloc(Layout[_PrimeCache](count=1))
    block.unsafe_ptr().unsafe_write(_PrimeCache(Atomic(Int64(0)), List[UInt64]()))
    return block^.unsafe_leak().unsafe_bitcast[NoneType]()


def _stop_cache(ctx: _Context):
    if ctx:
        var pointer = ctx.value().unsafe_bitcast[_PrimeCache]()
        _ = pointer.unsafe_take_pointee()
        dealloc(ThinAllocation(unsafe_owned_ptr=pointer).unsafe_with_layout(Layout[_PrimeCache](count=1)))


comptime _PRIME_WORK = UInt64(128)
"""The work one `prime` call charges, whatever the cache holds."""


def _extend(mut values: List[UInt64], i: Int) raises PolyError -> UInt64:
    # The search is not charged to the caller, whose fixed charge must not
    # depend on what earlier calls left in the cache; a caller reaches index i
    # only through calls it paid for, so the search stays bounded by them.
    var work = Budget()
    var candidate = (UInt64(1) << 62) - 1
    if len(values):
        candidate = values[len(values) - 1] - 1
        if candidate > 2 and candidate % 2 == 0:
            candidate -= 1
    while len(values) <= i:
        work.charge(1)
        if candidate < 2:
            raise PolyError(PolyErrorKind.CAPACITY, "prime sequence exhausted")
        if _prime(candidate, work):
            _ = _sum(len(values), 1)
            _allocation[UInt64](1, work)
            values.append(candidate)
        candidate = candidate - 2 if candidate > 3 else candidate - 1
    return values[i]


def prime(i: Int, mut budget: Budget) raises PolyError -> UInt64:
    """Return a cached prime from the fixed descending sequence below 2**62.

    Every call charges the same fixed work, whatever the cache holds, so a
    computation is charged the same however often it runs.

    Args:
        i: The zero-based sequence index.
        budget: The shared work allowance.

    Returns:
        The i-th prime, independent of cache state and thread scheduling.

    Raises:
        PolyError: DOMAIN for a negative index, LIMIT or CAPACITY on work limits.
    """
    budget.charge(_PRIME_WORK)
    if i < 0:
        raise PolyError(PolyErrorKind.DOMAIN, "negative prime index")
    _allocation[_PrimeCache](1, budget)
    var cache = _get_global["polynomials.primes.v1", _start_cache, _stop_cache]().value().unsafe_bitcast[_PrimeCache]()
    var expected = Int64(0)
    if not cache[].busy.compare_exchange[success_ordering=Ordering.ACQUIRE, failure_ordering=Ordering.RELAXED](expected, 1):
        # Contention does not spin or spend an unpredictable wait budget.
        var local = List[UInt64]()
        return _extend(local, i)
    var result: UInt64
    try:
        result = _extend(cache[].values, i)
    except e:
        cache[].busy.store[ordering=Ordering.RELEASE](0)
        raise e^
    cache[].busy.store[ordering=Ordering.RELEASE](0)
    return result


def _residue(value: Integer, p: UInt64, mut budget: Budget) raises PolyError -> UInt64:
    _work(value.magnitude_bit_length() // 8 + 1, 8, True, budget)
    try:
        var qr = div_rem_euclid(value, Integer(Int(p)))
        return UInt64(Int(qr[1]))
    except e:
        raise PolyError(PolyErrorKind.CAPACITY, String(e))


def _merge_residue(value: Integer, modulus: Integer, residue: UInt64, p: UInt64, mut budget: Budget) raises PolyError -> Integer:
    var old = _residue(value, p, budget)
    var m = _residue(modulus, p, budget)
    if m == 0:
        raise PolyError(PolyErrorKind.DOMAIN, "CRT moduli are not coprime")
    var difference = (residue % p + p - old) % p
    var correction = _mod_mul(difference, _mod_pow(m, p - 2, p, budget), p)
    return ZZ(value.copy()).add(ZZ(modulus.copy()).mul(ZZ(Integer(Int(correction))), budget), budget).value


def _symmetric(value: Integer, modulus: Integer, mut budget: Budget) raises PolyError -> Integer:
    _work(value.magnitude_bit_length() // 8 + 1, modulus.magnitude_bit_length() // 8 + 1, True, budget)
    try:
        var reduced = div_rem_euclid(value, modulus)[1].copy()
        if reduced + reduced > modulus:
            reduced -= modulus
        return reduced^
    except e:
        raise PolyError(PolyErrorKind.CAPACITY, String(e))


def crt(residues: List[UInt64], primes: List[UInt64], mut budget: Budget) raises PolyError -> Integer:
    """Combine prime residues into the unique symmetric representative.

    Args:
        residues: Residues, reduced modulo the corresponding primes.
        primes: Distinct prime moduli strictly below 2**62.
        budget: The shared work allowance.

    Returns:
        The representative in (-M/2, M/2], where M is the product of the primes.

    Raises:
        PolyError: DOMAIN for empty, mismatched, composite, or repeated moduli; LIMIT or CAPACITY on work limits.
    """
    budget.charge(1)
    if not len(primes) or len(primes) != len(residues):
        raise PolyError(PolyErrorKind.DOMAIN, "CRT requires equally sized nonempty lists")
    var value = Integer(0)
    var modulus = Integer(1)
    for i in range(len(primes)):
        budget.charge(1)
        var p = primes[i]
        if not _prime(p, budget):
            raise PolyError(PolyErrorKind.DOMAIN, "CRT modulus is not a supported prime")
        value = _merge_residue(value, modulus, residues[i], p, budget)
        modulus = ZZ(modulus.copy()).mul(ZZ(Integer(Int(p))), budget).value
    return _symmetric(value, modulus, budget)
