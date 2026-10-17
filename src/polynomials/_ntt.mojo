"""Multi-modular number-theoretic transform products for ZZ and prime-field dense polynomials.

Each product is computed modulo enough word-sized primes q = c * 2^32 + 1 to
determine every exact coefficient, then reassembled by Garner's mixed-radix
CRT. The transforms follow Harvey's lazy-reduction butterflies: residues stay
below 2q between stages, twiddle factors use Shoup's precomputed quotients,
and pointwise products use Montgomery reduction, whose factor 2^-64 is folded
into the final scaling. The forward transform is decimation in frequency
(natural order in, bit-reversed out) and the inverse is decimation in time
(bit-reversed in, natural out), so no permutation pass is needed.

Every choice depends only on operand lengths and coefficient sizes, and work
is charged before it is done, so budgets stay deterministic.
"""
from .coefficient_buffer import _CoefficientView, _view
from .coefficients import CoefficientRing, ZZ, ModInt, _mod_mul
from .errors import Budget, PolyError, PolyErrorKind, _allocation, _charge_size, _product, _sum
from apn_mojo import Integer

comptime _PRIME_COUNT = 48
comptime _PRIMES: Array[UInt64, _PRIME_COUNT] = [
    4611685941117976577,
    4611685692009873409,
    4611685606110527489,
    4611685318347718657,
    4611685232448372737,
    4611685219563470849,
    4611685125074190337,
    4611685090714451969,
    4611685039174844417,
    4611685021994975233,
    4611684738527133697,
    4611684691282493441,
    4611684674102624257,
    4611684609678114817,
    4611684588203278337,
    4611684274670665729,
    4611684098577006593,
    4611683789339361281,
    4611683647605440513,
    4611683643310473217,
    4611683578885963777,
    4611683557411127297,
    4611683437152043009,
    4611683282533220353,
    4611683157979168769,
    4611682913166032897,
    4611682857331458049,
    4611682702712635393,
    4611682681237798913,
    4611682591043485697,
    4611682483669303297,
    4611682165841723393,
    4611682084237344769,
    4611681955388325889,
    4611681581726171137,
    4611681491531857921,
    4611681341208002561,
    4611681302553296897,
    4611681147934474241,
    4611680937481076737,
    4611680903121338369,
    4611680877351534593,
    4611680731322646529,
    4611680580998791169,
    4611680439264870401,
    4611680374840360961,
    4611680078487617537,
    4611680074192650241,
]
"""Primes c * 2^32 + 1 between 2^61 and 2^62, largest first."""
comptime _ROOTS: Array[UInt64, _PRIME_COUNT] = [
    69433692538710738,
    458164920477615602,
    3318345213167893729,
    1987246491706964068,
    822924968455585315,
    2469127682168071965,
    1285830752081625251,
    183752203409188909,
    1921765219434798347,
    1227545647024351629,
    581778145267535569,
    2333496873055744784,
    1412740095042473410,
    1744787301615277891,
    1892334733857228946,
    1097498912578000954,
    4072886070187700477,
    694260992632473271,
    2937129682549285438,
    3031671718196792365,
    2814492735415149199,
    2610097204125386037,
    802260124231727687,
    1364591620262808040,
    3170439535044416886,
    467562035637133407,
    2897245213038952993,
    3177353734570521344,
    2441845749430210104,
    4205508554796425389,
    1706969373386532637,
    3200581903816233914,
    3174698838480727617,
    4435658554110039189,
    3435850728227909831,
    3876497104351613006,
    1723151487789990176,
    233548603520891187,
    4038448730184238371,
    2955703765147922460,
    2467354294034433290,
    3761130333586122566,
    4169086568370993452,
    2726591661292192631,
    4262110156144202909,
    809397819001368147,
    500353882891617265,
    1504575058755676207,
]
"""For each prime, a root of unity of order 2^32."""
comptime _PRIME_BITS = 61
"""Every prime exceeds 2^61, so each contributes at least 61 bits of modulus."""
comptime _MAX_LOG = 32
"""The roots of unity bound transform lengths by 2^32."""


@always_inline
def _mulhi(a: UInt64, b: UInt64) -> UInt64:
    return UInt64((UInt128(a) * UInt128(b)) >> 64)


@always_inline
def _shoup_quotient(w: UInt64, q: UInt64) -> UInt64:
    """floor(w * 2^64 / q) for w < q."""
    return UInt64((UInt128(w) << 64) // UInt128(q))


@always_inline
def _shoup(x: UInt64, w: UInt64, w_quotient: UInt64, q: UInt64) -> UInt64:
    """x * w mod q in [0, 2q), for any x below 2^64 and w < q < 2^62."""
    return x * w - _mulhi(x, w_quotient) * q


@always_inline
def _reduce_2q(x: UInt64, q: UInt64) -> UInt64:
    return x - q if x >= q else x


def _montgomery_inverse(q: UInt64) -> UInt64:
    """-q^-1 modulo 2^64 for odd q."""
    var inverse = q  # correct to 3 bits; each Newton step doubles them
    for _ in range(5):
        inverse *= 2 - q * inverse
    return UInt64(0) - inverse


@always_inline
def _redc(a: UInt64, b: UInt64, q: UInt64, q_inverse: UInt64) -> UInt64:
    """a * b * 2^-64 mod q in [0, 2q), for a, b < 2q and q < 2^62."""
    var t = UInt128(a) * UInt128(b)
    var m = UInt64(t) * q_inverse
    return UInt64((t + UInt128(m) * UInt128(q)) >> 64)


def _power(a: UInt64, n: UInt64, q: UInt64) -> UInt64:
    var base = a
    var exponent = n
    var result = UInt64(1)
    while exponent:
        if exponent & 1:
            result = _mod_mul(result, base, q)
        exponent >>= 1
        if exponent:
            base = _mod_mul(base, base, q)
    return result


struct _Tables(Movable):
    """Twiddles of one prime and length: entry m + j holds w_2m^j (forward) or w_2m^-j (inverse)."""
    var forward: List[UInt64]
    var forward_quotients: List[UInt64]
    var inverse: List[UInt64]
    var inverse_quotients: List[UInt64]

    def __init__(out self, q: UInt64, root: UInt64, n: Int):
        self.forward = List[UInt64](length=n, fill=0)
        self.forward_quotients = List[UInt64](length=n, fill=0)
        self.inverse = List[UInt64](length=n, fill=0)
        self.inverse_quotients = List[UInt64](length=n, fill=0)
        if n < 2:
            return
        # The last stage holds w^j, j < n/2, for w of order n; every other stage
        # takes a stride of it. Shoup quotients cost a 128-bit division each, so
        # only these n/2 are divided: w^-j = q - w^(n/2 - j), and the quotient of
        # q - x is 2^64 - 1 - the quotient of x.
        var half = n // 2
        var log = 0
        while (1 << log) < n:
            log += 1
        var w = _power(root, UInt64(1) << UInt64(_MAX_LOG - log), q)
        var step = _shoup_quotient(w, q)
        var x = UInt64(1)
        for j in range(half):
            self.forward[half + j] = x
            self.forward_quotients[half + j] = _shoup_quotient(x, q)
            x = _reduce_2q(_shoup(x, w, step, q), q)
        self.inverse[half] = 1
        self.inverse_quotients[half] = self.forward_quotients[half]
        for j in range(1, half):
            self.inverse[half + j] = q - self.forward[n - j]
            self.inverse_quotients[half + j] = UInt64.MAX - self.forward_quotients[n - j]
        var m = half // 2
        var stride = 2
        while m >= 1:
            for j in range(m):
                self.forward[m + j] = self.forward[half + j * stride]
                self.forward_quotients[m + j] = self.forward_quotients[half + j * stride]
                self.inverse[m + j] = self.inverse[half + j * stride]
                self.inverse_quotients[m + j] = self.inverse_quotients[half + j * stride]
            m //= 2
            stride *= 2


def _forward(mut a: List[UInt64], tables: _Tables, q: UInt64):
    """Decimation in frequency; values below 2q in and out, output in bit-reversed order."""
    var n = len(a)
    var q2 = 2 * q
    ref w = tables.forward
    ref wq = tables.forward_quotients
    var m = n // 2
    while m >= 1:
        var start = 0
        while start < n:
            for j in range(m):
                var u = a.unsafe_get(start + j)
                var v = a.unsafe_get(start + j + m)
                var x = u + v
                a.unsafe_get(start + j) = x - q2 if x >= q2 else x
                a.unsafe_get(start + j + m) = _shoup(u - v + q2, w.unsafe_get(m + j), wq.unsafe_get(m + j), q)
            start += 2 * m
        m //= 2


def _inverse(mut a: List[UInt64], tables: _Tables, q: UInt64):
    """Decimation in time without the 1/n factor; values below 2q in and out, bit-reversed input."""
    var n = len(a)
    var q2 = 2 * q
    ref w = tables.inverse
    ref wq = tables.inverse_quotients
    var m = 1
    while m < n:
        var start = 0
        while start < n:
            for j in range(m):
                var u = a.unsafe_get(start + j)
                var t = _shoup(a.unsafe_get(start + j + m), w.unsafe_get(m + j), wq.unsafe_get(m + j), q)
                var x = u + t
                var y = u - t + q2
                a.unsafe_get(start + j) = x - q2 if x >= q2 else x
                a.unsafe_get(start + j + m) = y - q2 if y >= q2 else y
            start += 2 * m
        m *= 2


def _convolve(var a: List[UInt64], var b: List[UInt64], count: Int, square: Bool, index: Int, n: Int) -> List[UInt64]:
    """The first `count` cyclic convolution coefficients modulo prime `index`, reduced below q.

    Operands hold residues below 2q, zero-padded to the transform length n.
    """
    var primes = materialize[_PRIMES]()
    var roots = materialize[_ROOTS]()
    var q = primes[index]
    var tables = _Tables(q, roots[index], n)
    var q_inverse = _montgomery_inverse(q)
    _forward(a, tables, q)
    if not square:
        _forward(b, tables, q)
    if square:
        for i in range(n):
            var v = a.unsafe_get(i)
            a.unsafe_get(i) = _redc(v, v, q, q_inverse)
    else:
        for i in range(n):
            a.unsafe_get(i) = _redc(a.unsafe_get(i), b.unsafe_get(i), q, q_inverse)
    _inverse(a, tables, q)
    # Undo the Montgomery factor and divide by n: multiply by 2^64 / n.
    var r = UInt64(((UInt128(1) << 64) % UInt128(q)))
    var scale = _mod_mul(r, _power(UInt64(n) % q, q - 2, q), q)
    var scale_quotient = _shoup_quotient(scale, q)
    var result = List[UInt64](capacity=count)
    for i in range(count):
        result.append(_reduce_2q(_shoup(a.unsafe_get(i), scale, scale_quotient, q), q))
    return result^


def _transform_length(count: Int) -> Int:
    var n = 1
    while n < count:
        n *= 2
    return n


def _charge_transforms(primes: Int, n: Int, square: Bool, mut budget: Budget) raises PolyError:
    """Charge the tables, two or three transforms, and the pointwise pass of every prime."""
    var log = 0
    while (1 << log) < n:
        log += 1
    _allocation[UInt64](_product(6, n), budget)
    var per_prime = _product(n, _sum(_product(2 if square else 3, log), 6))
    _charge_size(_product(primes, per_prime), budget)


@fieldwise_init
struct _Garner(Movable):
    """Mixed-radix CRT constants for the first k primes."""
    var k: Int
    var prefix_inverse: List[UInt64]
    """(q_0 ... q_(i-1))^-1 mod q_i, and its Shoup quotient."""
    var prefix_inverse_quotient: List[UInt64]
    var residue: List[UInt64]
    """Row i, column j < i: q_j mod q_i, and its Shoup quotient."""
    var residue_quotient: List[UInt64]
    var moduli: List[UInt64]
    """The primes q_0 ... q_(k-1)."""


def _garner(k: Int) -> _Garner:
    var primes = materialize[_PRIMES]()
    var prefix_inverse = List[UInt64](length=k, fill=0)
    var prefix_quotient = List[UInt64](length=k, fill=0)
    var residue = List[UInt64](length=k * k, fill=0)
    var residue_quotient = List[UInt64](length=k * k, fill=0)
    for i in range(k):
        var q = primes[i]
        var prefix = UInt64(1)
        for j in range(i):
            var r = primes[j] % q
            residue[i * k + j] = r
            residue_quotient[i * k + j] = _shoup_quotient(r, q)
            prefix = _mod_mul(prefix, r, q)
        var inverse = _power(prefix, q - 2, q)
        prefix_inverse[i] = inverse
        prefix_quotient[i] = _shoup_quotient(inverse, q)
    var moduli = List[UInt64](capacity=k)
    for i in range(k):
        moduli.append(primes[i])
    return _Garner(k, prefix_inverse^, prefix_quotient^, residue^, residue_quotient^, moduli^)


def _digits(g: _Garner, residues: List[List[UInt64]], index: Int, mut digits: List[UInt64]):
    """The mixed-radix digits v_i < q_i of the coefficient whose residues are residues[i][index]."""
    for i in range(g.k):
        var q = g.moduli[i]
        # acc = v_0 + v_1 q_0 + ... + v_(i-1) q_0 ... q_(i-2) mod q_i, by Horner.
        var acc = UInt64(0)
        var j = i - 1
        while j >= 0:
            # Digits are below q_j < 2^62 < 2 q_i, so the sum stays below 3 q_i.
            acc = _reduce_2q(_shoup(acc, g.residue[i * g.k + j], g.residue_quotient[i * g.k + j], q), q) + digits[j]
            acc = _reduce_2q(_reduce_2q(acc, q), q)
            j -= 1
        var r = residues[i][index]
        var difference = r - acc if r >= acc else r + q - acc
        digits[i] = _reduce_2q(_shoup(difference, g.prefix_inverse[i], g.prefix_inverse_quotient[i], q), q)


def _radix_limbs(k: Int) -> List[UInt64]:
    """The product q_0 ... q_(k-1) in 64-bit limbs, least significant first."""
    var primes = materialize[_PRIMES]()
    var limbs: List[UInt64] = [1]
    for i in range(k):
        _scale_add(limbs, primes[i], 0)
    return limbs^


@always_inline
def _scale_add(mut limbs: List[UInt64], factor: UInt64, addend: UInt64):
    var carry = UInt128(addend)
    for l in range(len(limbs)):
        var t = UInt128(limbs[l]) * UInt128(factor) + carry
        limbs[l] = UInt64(t)
        carry = t >> 64
    if carry:
        limbs.append(UInt64(carry))


def _compare(a: List[UInt64], b: List[UInt64]) -> Int:
    var n = max(len(a), len(b))
    var l = n - 1
    while l >= 0:
        var x = a[l] if l < len(a) else UInt64(0)
        var y = b[l] if l < len(b) else UInt64(0)
        if x != y:
            return 1 if x > y else -1
        l -= 1
    return 0


def _subtract_from(m: List[UInt64], mut x: List[UInt64]):
    """x = m - x in place, for x <= m."""
    var borrow = UInt64(0)
    for l in range(len(m)):
        var a = m[l]
        var b = x[l] if l < len(x) else UInt64(0)
        var d = a - b - borrow
        borrow = UInt64(1) if (a < b or (a == b and borrow == 1)) else UInt64(0)
        if l < len(x):
            x[l] = d
        else:
            x.append(d)


def _subtract_in_place(mut x: List[UInt64], m: List[UInt64]):
    """x = x - m in place, for m <= x."""
    var borrow = UInt64(0)
    for l in range(len(x)):
        var a = x[l]
        var b = m[l] if l < len(m) else UInt64(0)
        x[l] = a - b - borrow
        borrow = UInt64(1) if (a < b or (a == b and borrow == 1)) else UInt64(0)


def _magnitude(value: Integer, mut limbs: List[UInt64]):
    """Append the magnitude of value in 64-bit limbs, least significant first."""
    var bits = value.magnitude_bit_length()
    if bits == 0:
        return
    if bits <= 64:
        # Negating a value of at most 64 bits stays inline.
        try:
            limbs.append((-value if value.sign() < 0 else value).to_native_exact[DType.uint64]())
            return
        except:
            pass
    var bytes = value.to_bytes()
    var count = len(bytes)
    var full = count // 8
    for l in range(full):
        var limb = UInt64(0)
        comptime for b in range(8):
            limb |= UInt64(bytes.unsafe_get(8 * l + b)) << UInt64(8 * b)
        limbs.append(limb)
    if full * 8 < count:
        var limb = UInt64(0)
        for i in range(full * 8, count):
            limb |= UInt64(bytes.unsafe_get(i)) << UInt64(8 * (i - 8 * full))
        limbs.append(limb)


def _residues_zz[C: CoefficientRing](values: _CoefficientView[C, _], k: Int, n: Int, mut budget: Budget) raises PolyError -> List[List[UInt64]]:
    """Each coefficient modulo each of the first k primes, as residues below q, padded to n."""
    var primes = materialize[_PRIMES]()
    var limbs = List[UInt64]()
    var offsets = List[Int](capacity=len(values) + 1)
    var negative = List[Bool](capacity=len(values))
    offsets.append(0)
    for i in range(len(values)):
        ref c = rebind[ZZ](values[i])
        _charge_size(c.size(), budget)
        _magnitude(c.value, limbs)
        offsets.append(len(limbs))
        negative.append(c.value.sign() < 0)
    _charge_size(_product(k, len(limbs)), budget)
    var out = List[List[UInt64]](capacity=k)
    for p in range(k):
        var q = primes[p]
        var radix = UInt64(((UInt128(1) << 64) % UInt128(q)))
        var radix_quotient = _shoup_quotient(radix, q)
        var one_quotient = _shoup_quotient(1, q)
        var residues = List[UInt64](length=n, fill=0)
        for i in range(len(values)):
            var r = UInt64(0)
            var l = offsets[i + 1] - 1
            while l >= offsets[i]:
                r = _reduce_2q(_shoup(r, radix, radix_quotient, q), q) + _reduce_2q(_shoup(limbs[l], 1, one_quotient, q), q)
                r = _reduce_2q(r, q)
                l -= 1
            residues[i] = (q - r if r else r) if negative[i] else r
        out.append(residues^)
    return out^


def _bits_zz[C: CoefficientRing](values: _CoefficientView[C, _]) -> Int:
    var bits = 0
    for i in range(len(values)):
        bits = max(bits, rebind[ZZ](values[i]).value.magnitude_bit_length())
    return bits


def _bit_length(n: Int) -> Int:
    var bits = 0
    while (1 << bits) <= n:
        bits += 1
    return bits


def _ntt_zz[C: CoefficientRing](a: _CoefficientView[C, _], b: _CoefficientView[C, _], square: Bool, mut budget: Budget) raises PolyError -> Optional[List[C]]:
    """The exact product by multi-modular transforms, or None when the coefficients need more primes than the table holds."""
    var count = len(a) + len(b) - 1
    # |c_i| <= min(len) * max|a| * max|b|; the symmetric range needs one more bit.
    var bits_a = _bits_zz(a)
    var bits = bits_a + (bits_a if square else _bits_zz(b)) + _bit_length(min(len(a), len(b))) + 1
    var k = (bits + _PRIME_BITS - 1) // _PRIME_BITS
    var n = _transform_length(count)
    if k > _PRIME_COUNT or n > (1 << 30):
        return None
    _charge_transforms(k, n, square, budget)
    _allocation[UInt64](_product(k, count), budget)
    var left = _residues_zz(a, k, n, budget)
    var right = List[List[UInt64]]() if square else _residues_zz(b, k, n, budget)
    var residues = List[List[UInt64]](capacity=k)
    for p in range(k):
        var x = List[UInt64]()
        swap(x, left[p])
        var y = List[UInt64]()
        if not square:
            swap(y, right[p])
        residues.append(_convolve(x^, y^, count, square, p, n))
    var result = _reconstruct_zz[C](residues, k, count, budget)
    while len(result) and result[len(result) - 1].is_zero():
        _ = result.pop()
    return result^


def _reconstruct_zz[C: CoefficientRing](residues: List[List[UInt64]], k: Int, count: Int, mut budget: Budget) raises PolyError -> List[C]:
    """The symmetric CRT representatives, as ZZ values, of the first `count` residue columns modulo the first k primes."""
    _charge_size(_product(count, _product(k, k)), budget)
    _allocation[C](count, budget)
    var g = _garner(k)
    var result = List[C](capacity=count)
    var digits = List[UInt64](length=k, fill=0)
    var bytes = List[UInt8](length=8 * (k + 1), fill=0)
    if k <= 2:
        # Values below q_0 q_1 < 2^124 fit one 128-bit word.
        var modulus = UInt128(g.moduli[0]) * (UInt128(g.moduli[1]) if k == 2 else UInt128(1))
        var half = modulus >> 1
        for i in range(count):
            var x = UInt128(residues[0][i])
            if k == 2:
                _digits(g, residues, i, digits)
                x = UInt128(digits[0]) + UInt128(digits[1]) * UInt128(g.moduli[0])
            var negative = x > half
            if negative:
                x = modulus - x
            result.append(rebind_var[C](ZZ(_integer_128(x, negative, bytes))))
        return result^
    var modulus = _radix_limbs(k)
    var half = modulus.copy()
    var low = UInt64(0)
    var l = len(half) - 1
    while l >= 0:
        var next_low = half[l] & 1
        half[l] = (half[l] >> 1) | (low << 63)
        low = next_low
        l -= 1
    # Explicit CRT: x = sum y_i (M / q_i) - t M with y_i = r_i (M / q_i)^-1 mod q_i
    # and t = floor(sum y_i / q_i). A floating-point estimate of the sum, taken
    # slightly low, gives t or t - 1, and one subtraction of M corrects the latter.
    var size = len(modulus)
    var cofactors = List[List[UInt64]](capacity=k)
    var inverses = List[UInt64](capacity=k)
    var inverse_quotients = List[UInt64](capacity=k)
    var reciprocals = List[Float64](capacity=k)
    for i in range(k):
        var q = g.moduli[i]
        var cofactor: List[UInt64] = [1]
        for j in range(k):
            if j != i:
                _scale_add(cofactor, g.moduli[j], 0)
        cofactor.resize(size, 0)
        var residue = UInt64(0)
        var l = size - 1
        while l >= 0:
            residue = UInt64(((UInt128(residue) << 64) | UInt128(cofactor[l])) % UInt128(q))
            l -= 1
        var inverse = _power(residue, q - 2, q)
        cofactors.append(cofactor^)
        inverses.append(inverse)
        inverse_quotients.append(_shoup_quotient(inverse, q))
        reciprocals.append(1.0 / Float64(q))
    var x = List[UInt64](length=size + 1, fill=0)
    for i in range(count):
        for l in range(size + 1):
            x.unsafe_get(l) = 0
        var estimate = Float64(0)
        for j in range(k):
            var q = g.moduli[j]
            var y = _reduce_2q(_shoup(residues[j].unsafe_get(i), inverses[j], inverse_quotients[j], q), q)
            estimate += Float64(y) * reciprocals[j]
            ref cofactor = cofactors[j]
            var carry = UInt128(0)
            for l in range(size):
                var t = UInt128(cofactor.unsafe_get(l)) * UInt128(y) + UInt128(x.unsafe_get(l)) + carry
                x.unsafe_get(l) = UInt64(t)
                carry = t >> 64
            x.unsafe_get(size) += UInt64(carry)
        var multiple = UInt64(estimate - 1e-6) if estimate > 1e-6 else UInt64(0)
        var carry = UInt128(0)
        var borrow = UInt64(0)
        for l in range(size + 1):
            var t = UInt128(modulus[l] if l < size else UInt64(0)) * UInt128(multiple) + carry
            carry = t >> 64
            var a = x.unsafe_get(l)
            var b = UInt64(t)
            x.unsafe_get(l) = a - b - borrow
            borrow = UInt64(1) if (a < b or (a == b and borrow == 1)) else UInt64(0)
        if _compare(x, modulus) >= 0:
            _subtract_in_place(x, modulus)
        while len(x) > size:
            _ = x.pop()
        var negative = _compare(x, half) > 0
        if negative:
            _subtract_from(modulus, x)
        var used = len(x)
        while used > 1 and x[used - 1] == 0:
            used -= 1
        result.append(rebind_var[C](ZZ(_integer(x, used, negative, bytes))))
        x.resize(size + 1, 0)
    return result^


def _integer_128(x: UInt128, negative: Bool, mut bytes: List[UInt8]) -> Integer:
    """The integer with magnitude x and the given sign, inline when it fits a word."""
    var lo = UInt64(x)
    var hi = UInt64(x >> 64)
    if hi == 0:
        if lo <= UInt64(Int64.MAX):
            return Integer(-Int64(lo) if negative else Int64(lo))
        if not negative:
            return Integer(lo)
    comptime for shift in range(8):
        bytes[shift] = UInt8((lo >> UInt64(8 * shift)) & 0xFF)
        bytes[8 + shift] = UInt8((hi >> UInt64(8 * shift)) & 0xFF)
    return Integer.from_bytes(Span(bytes)[:16], negative=negative)


def _integer(limbs: List[UInt64], used: Int, negative: Bool, mut bytes: List[UInt8]) -> Integer:
    """The integer with magnitude limbs[0 ..< used] and the given sign, inline when it fits a word."""
    if used == 1:
        var m = limbs[0]
        if m <= UInt64(Int64.MAX):
            return Integer(-Int64(m) if negative else Int64(m))
        if not negative:
            return Integer(m)
    for l in range(used):
        comptime for shift in range(8):
            bytes[8 * l + shift] = UInt8((limbs[l] >> UInt64(8 * shift)) & 0xFF)
    return Integer.from_bytes(Span(bytes)[: 8 * used], negative=negative)


def _prime_index(p: UInt64) -> Int:
    """The table index of p when p is one of the transform primes, otherwise -1."""
    var primes = materialize[_PRIMES]()
    for i in range(_PRIME_COUNT):
        if primes[i] == p:
            return i
    return -1


def _modular_product(a: List[UInt64], b: List[UInt64], count: Int, p: UInt64, square: Bool, mut budget: Budget) raises PolyError -> List[UInt64]:
    """The first `count` coefficients of a * b modulo a prime p < 2^62, for nonempty residue lists below p.

    A transform prime is its own single modulus; any other p combines up to
    three transform primes by Garner's CRT and reduces the result.
    """
    var primes = materialize[_PRIMES]()
    var la = min(len(a), count)
    var lb = la if square else min(len(b), count)
    var full = la + lb - 1
    var n = _transform_length(full)
    var index = _prime_index(p)
    var k = 1
    if index < 0:
        var bits = 2 * _bit_length(Int(p - 1)) + _bit_length(min(la, lb))
        k = (bits + _PRIME_BITS - 1) // _PRIME_BITS
    _charge_transforms(k, n, square, budget)
    _allocation[UInt64](_product(k, full), budget)
    var out = min(count, full)
    var residues = List[List[UInt64]](capacity=k)
    for j in range(k):
        # Residues below p < 2^62 are already below 2q for every q > 2^61.
        var x = List[UInt64](length=n, fill=0)
        for i in range(la):
            x[i] = a[i]
        var y = List[UInt64]()
        if not square:
            y = List[UInt64](length=n, fill=0)
            for i in range(lb):
                y[i] = b[i]
        residues.append(_convolve(x^, y^, out, square, index if index >= 0 else j, n))
    if index >= 0:
        var single = List[UInt64]()
        swap(single, residues[0])
        single.resize(count, 0)
        return single^
    _charge_size(_product(out, _product(k, k)), budget)
    var g = _garner(k)
    # x mod p = sum v_i (q_0 ... q_(i-1) mod p).
    var weights = List[UInt64](capacity=k)
    var w = UInt64(1)
    for i in range(k):
        weights.append(w)
        w = _mod_mul(w, primes[i] % p, p)
    var digits = List[UInt64](length=k, fill=0)
    var result = List[UInt64](length=count, fill=0)
    for i in range(out):
        var value = residues[0][i] % p
        if k > 1:
            _digits(g, residues, i, digits)
            value = digits[0] % p
            for j in range(1, k):
                value = (value + _mod_mul(digits[j] % p, weights[j], p)) % p
        result[i] = value
    return result^


def _ntt_modular[C: CoefficientRing](a: _CoefficientView[C, _], b: _CoefficientView[C, _], square: Bool, mut budget: Budget) raises PolyError -> Optional[List[C]]:
    """The product over GF(p) by transforms modulo one to three word primes."""
    var count = len(a) + len(b) - 1
    if _transform_length(count) > (1 << 30):
        return None
    ref lead = rebind[ModInt](a[0])
    var p = lead.modulus
    var x = List[UInt64](capacity=len(a))
    for i in range(len(a)):
        x.append(rebind[ModInt](a[i]).value)
    var y = List[UInt64]()
    if not square:
        y.reserve(len(b))
        for i in range(len(b)):
            y.append(rebind[ModInt](b[i]).value)
    # A square ignores its second operand.
    var values = _modular_product(x, y, count, p, square, budget)
    _allocation[C](count, budget)
    var result = List[C](capacity=count)
    for i in range(count):
        result.append(rebind_var[C](lead._with_residue(values[i])))
    while len(result) and result[len(result) - 1].is_zero():
        _ = result.pop()
    return result^


struct _Convolver(Movable):
    """Cyclic convolutions of length n modulo a prime p < 2^62 that keep their operands' transforms.

    A transform prime is its own modulus; any other p uses enough transform
    primes for sums of n products below p^2, then Garner's CRT.
    """
    var n: Int
    var p: UInt64
    var indices: List[Int]
    var tables: List[_Tables]
    var garner: _Garner
    var weights: List[UInt64]
    """(q_0 ... q_(i-1)) mod p."""

    def __init__(out self, p: UInt64, n: Int, mut budget: Budget) raises PolyError:
        var primes = materialize[_PRIMES]()
        var roots = materialize[_ROOTS]()
        self.n = n
        self.p = p
        self.indices = List[Int]()
        var index = _prime_index(p)
        if index >= 0:
            self.indices.append(index)
        else:
            var bits = 2 * _bit_length(Int(p - 1)) + _bit_length(n)
            for j in range((bits + _PRIME_BITS - 1) // _PRIME_BITS):
                self.indices.append(j)
        var k = len(self.indices)
        _allocation[UInt64](_product(4 * k, n), budget)
        _charge_size(_product(k, n), budget)
        self.tables = List[_Tables](capacity=k)
        for j in self.indices:
            self.tables.append(_Tables(primes[j], roots[j], n))
        self.garner = _garner(k)
        self.weights = List[UInt64](capacity=k)
        var w = UInt64(1)
        for j in range(k):
            self.weights.append(w)
            w = _mod_mul(w, primes[j] % p, p)

    def transform(self, values: List[UInt64], mut budget: Budget) raises PolyError -> List[List[UInt64]]:
        """The forward transforms, one per prime, of residues below p (at most n of them)."""
        var primes = materialize[_PRIMES]()
        var log = _bit_length(self.n)
        _charge_size(_product(len(self.indices), _product(self.n, log)), budget)
        _allocation[UInt64](_product(len(self.indices), self.n), budget)
        var out = List[List[UInt64]](capacity=len(self.indices))
        for j in range(len(self.indices)):
            # Residues below p < 2^62 are already below 2q for every q > 2^61.
            var x = List[UInt64](length=self.n, fill=0)
            for i in range(len(values)):
                x[i] = values[i]
            _forward(x, self.tables[j], primes[self.indices[j]])
            out.append(x^)
        return out^

    def multiply(self, a: List[List[UInt64]], b: List[List[UInt64]], count: Int, mut budget: Budget) raises PolyError -> List[UInt64]:
        """The first `count` cyclic convolution coefficients of two transforms, reduced modulo p."""
        var primes = materialize[_PRIMES]()
        var k = len(self.indices)
        var log = _bit_length(self.n)
        _charge_size(_product(k, _product(self.n, log + 2)), budget)
        _allocation[UInt64](_product(k, self.n), budget)
        var residues = List[List[UInt64]](capacity=k)
        for j in range(k):
            var q = primes[self.indices[j]]
            var q_inverse = _montgomery_inverse(q)
            var x = List[UInt64](length=self.n, fill=0)
            for i in range(self.n):
                x.unsafe_get(i) = _redc(a[j].unsafe_get(i), b[j].unsafe_get(i), q, q_inverse)
            _inverse(x, self.tables[j], q)
            var r = UInt64(((UInt128(1) << 64) % UInt128(q)))
            var scale = _mod_mul(r, _power(UInt64(self.n) % q, q - 2, q), q)
            var scale_quotient = _shoup_quotient(scale, q)
            for i in range(count):
                x.unsafe_get(i) = _reduce_2q(_shoup(x.unsafe_get(i), scale, scale_quotient, q), q)
            x.resize(count, 0)
            residues.append(x^)
        if k == 1 and self.indices[0] >= 0 and primes[self.indices[0]] == self.p:
            var single = List[UInt64]()
            swap(single, residues[0])
            return single^
        _charge_size(_product(count, _product(k, k)), budget)
        var digits = List[UInt64](length=k, fill=0)
        var result = List[UInt64](length=count, fill=0)
        for i in range(count):
            var value = residues[0][i] % self.p
            if k > 1:
                _digits(self.garner, residues, i, digits)
                value = digits[0] % self.p
                for j in range(1, k):
                    value = (value + _mod_mul(digits[j] % self.p, self.weights[j], self.p)) % self.p
            result[i] = value
        return result^


comptime _NEWTON_SCHOOLBOOK = 64
"""Below this precision, series inversion steps use schoolbook products."""


def _low_product(a: List[UInt64], b: List[UInt64], lo: Int, hi: Int, p: UInt64, mut budget: Budget) raises PolyError -> List[UInt64]:
    """Coefficients lo ..< hi of a * b modulo p, by schoolbook."""
    _charge_size(_product(hi - lo, min(len(a), hi)), budget)
    var result = List[UInt64](capacity=hi - lo)
    for c in range(lo, hi):
        var acc = UInt128(0)
        for i in range(max(0, c - len(b) + 1), min(len(a), c + 1)):
            acc += UInt128(a[i]) * UInt128(b[c - i])
            if acc >= UInt128(1) << 126:
                acc %= UInt128(p)
        result.append(UInt64(acc % UInt128(p)))
    return result^


def _series_inverse(b: List[UInt64], m: Int, p: UInt64, mut budget: Budget) raises PolyError -> List[UInt64]:
    """The inverse of the power series b (b[0] invertible) modulo x^m and p, by Newton iteration.

    Each step from precision k to k2 <= 2k needs e = b * inverse modulo x^k2,
    which equals 1 + x^k d; a cyclic convolution of length n >= k2 gives its
    coefficients k ..< k2 intact, since the wrapped part lands below k. The
    correction -inverse * d modulo x^(k2 - k) reuses the inverse's transform.
    """
    var inverse: List[UInt64] = [_power(b[0], p - 2, p)]
    var k = 1
    while k < m:
        budget.charge(1)
        var k2 = min(2 * k, m)
        var head = List[UInt64](capacity=k2)
        for i in range(min(k2, len(b))):
            head.append(b[i])
        var d: List[UInt64]
        var convolver = Optional[_Convolver](None)
        var inverse_transform = List[List[UInt64]]()
        if k2 <= _NEWTON_SCHOOLBOOK:
            d = _low_product(head, inverse, k, k2, p, budget)
        else:
            convolver = _Convolver(p, _transform_length(k2), budget)
            inverse_transform = convolver.value().transform(inverse, budget)
            var e = convolver.value().multiply(convolver.value().transform(head, budget), inverse_transform, k2, budget)
            d = List[UInt64](capacity=k2 - k)
            for i in range(k, k2):
                d.append(e[i])
        var allzero = True
        for v in d:
            if v:
                allzero = False
                break
        if allzero:
            inverse.resize(k2, 0)
        else:
            var t: List[UInt64]
            if k2 <= _NEWTON_SCHOOLBOOK:
                t = _low_product(inverse, d, 0, k2 - k, p, budget)
            else:
                # inverse * d has length k2 - 1 < n: no wrap.
                t = convolver.value().multiply(convolver.value().transform(d, budget), inverse_transform, k2 - k, budget)
            for i in range(k2 - k):
                inverse.append(p - t[i] if t[i] else UInt64(0))
        k = k2
    return inverse^


def _quotient_mod(a: List[UInt64], b: List[UInt64], p: UInt64, mut budget: Budget) raises PolyError -> List[UInt64]:
    """The quotient of the division with remainder of a by b modulo p, for len(a) >= len(b) and a unit leading coefficient."""
    var m = len(a) - len(b) + 1
    var a_rev = List[UInt64](capacity=m)
    for i in range(m):
        a_rev.append(a[len(a) - 1 - i])
    var b_rev = List[UInt64](capacity=min(m, len(b)))
    for i in range(min(m, len(b))):
        b_rev.append(b[len(b) - 1 - i])
    var inverse = _series_inverse(b_rev, m, p, budget)
    var q_rev = _modular_product(a_rev, inverse, m, p, False, budget)
    var q = List[UInt64](capacity=m)
    for i in range(m):
        q.append(q_rev[m - 1 - i])
    return q^


def _equal_mod(a: List[UInt64], q: List[UInt64], b: List[UInt64], p: UInt64, mut budget: Budget) raises PolyError -> Bool:
    """Whether q * b == a modulo p, for q the quotient of a divided by b with remainder.

    q * b already agrees with a from degree len(b) - 1 up, so a remainder of
    lower degree is zero exactly when q * b and a agree modulo x^n - 1 for
    any n >= len(b) - 1: a cyclic convolution of half the full length.
    """
    var n = _transform_length(max(len(q), len(b)))
    var convolver = _Convolver(p, n, budget)
    var wrapped = convolver.multiply(convolver.transform(q, budget), convolver.transform(b, budget), n, budget)
    var folded = List[UInt64](length=n, fill=0)
    for i in range(len(a)):
        var s = folded[i % n] + a[i]
        folded[i % n] = s - p if s >= p else s
    for i in range(n):
        if wrapped[i] != folded[i]:
            return False
    return True


def _ntt_divide_exact[C: CoefficientRing](a: _CoefficientView[C, _], b: _CoefficientView[C, _], mut budget: Budget) raises PolyError -> Optional[Optional[List[C]]]:
    """The exact quotient a / b (inner None when b does not divide a), or None when this method cannot decide.

    Requires len(a) >= len(b) >= 2 with nonzero leading coefficients.
    """
    var primes = materialize[_PRIMES]()
    comptime if C == ModInt:
        ref lead = rebind[ModInt](a[0])
        var p = lead.modulus
        var x = List[UInt64](capacity=len(a))
        for i in range(len(a)):
            x.append(rebind[ModInt](a[i]).value)
        var y = List[UInt64](capacity=len(b))
        for i in range(len(b)):
            y.append(rebind[ModInt](b[i]).value)
        var q = _quotient_mod(x, y, p, budget)
        if not _equal_mod(x, q, y, p, budget):
            return Optional(Optional[List[C]](None))
        _allocation[C](len(q), budget)
        var result = List[C](capacity=len(q))
        for v in q:
            result.append(rebind_var[C](lead._with_residue(v)))
        return Optional(Optional(result^))
    elif C == ZZ:
        # The quotient's coefficients are usually no larger than the dividend's;
        # a candidate that fails the exact check is retried with twice the primes.
        var bits = _bits_zz(a) + _bit_length(len(a)) + 2
        var k = (bits + _PRIME_BITS - 1) // _PRIME_BITS
        var m = len(a) - len(b) + 1
        var residues = List[List[UInt64]]()
        while k <= _PRIME_COUNT:
            var all_a = _residues_zz(a, k, len(a), budget)
            var all_b = _residues_zz(b, k, len(b), budget)
            for i in range(len(residues), k):
                if all_b[i][len(b) - 1] == 0:
                    return None  # the divisor's leading coefficient vanishes modulo this prime
                var q = _quotient_mod(all_a[i], all_b[i], primes[i], budget)
                if i == 0 and not _equal_mod(all_a[0], q, all_b[0], primes[0], budget):
                    # Not divisible modulo a prime that keeps the leading coefficient: not divisible in ZZ[x].
                    return Optional(Optional[List[C]](None))
                residues.append(q^)
            var candidate = _reconstruct_zz[C](residues, k, m, budget)
            while len(candidate) and candidate[len(candidate) - 1].is_zero():
                _ = candidate.pop()
            if len(candidate) == m:
                var check = _ntt_zz(_view(candidate), b, False, budget)
                if check:
                    ref product = check.value()
                    var same = len(product) == len(a)
                    if same:
                        for i in range(len(a)):
                            if not (rebind[ZZ](product[i]) == rebind[ZZ](a[i])):
                                same = False
                                break
                    if same:
                        return Optional(Optional(candidate^))
            if k == _PRIME_COUNT:
                break
            k = min(2 * k, _PRIME_COUNT)
        return None
    else:
        return None


def _ntt_product[C: CoefficientRing](a: _CoefficientView[C, _], b: _CoefficientView[C, _], square: Bool, mut budget: Budget) raises PolyError -> Optional[List[C]]:
    """The product of nonempty ZZ or GF(p) coefficient vectors by transforms, or None for other rings and oversized coefficients."""
    comptime if C == ZZ:
        return _ntt_zz(a, b, square, budget)
    elif C == ModInt:
        return _ntt_modular(a, b, square, budget)
    else:
        return None
