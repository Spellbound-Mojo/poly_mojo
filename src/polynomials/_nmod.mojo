"""Native Montgomery residue vectors for odd prime-field factorization.

A polynomial is a `List[UInt64]` of Montgomery residues, lowest degree first,
without trailing zeros; the zero polynomial is empty. Products accumulate exact
128-bit sums and reduce once per `_Field.batch` terms, so convolution and
matrix inner loops perform no division. Every operation charges the shared
budget in proportion to its coefficient work before doing it.
"""
from .errors import Budget, PolyError, PolyErrorKind, _allocation, _charge_size, _product, _sum
from ._ntt import _modular_product, _Tables, _forward, _inverse, _redc as _transform_redc, _montgomery_inverse, _shoup, _shoup_quotient, _reduce_2q, _power as _transform_power, _transform_length, _PRIMES, _ROOTS, _MAX_LOG
from std.memory import ArcPointer
from ._nmod_euclid import _Field as _EuclidField, _gcd_words

comptime _KARATSUBA = 128
"""Operand length at which products switch from schoolbook to Karatsuba;
SIMD schoolbook for primes below _SMALL wins up to _KARATSUBA_SMALL."""
comptime _KARATSUBA_SMALL = 1024
comptime _SMALL = UInt64(1) << 28
"""Primes below this bound keep products under 2^56, so 64-bit SIMD lanes
accumulate 256 of them exactly before a reduction."""
comptime _TRANSFORM = 512
"""Shorter operand length at which products switch from Karatsuba to number-theoretic transforms."""
comptime _TRANSFORM_ONE = 384
"""The same, when one transform prime holds every coefficient sum."""
comptime _TRANSFORM_SMALL = 2048
"""The same, for primes below _SMALL that need two transform primes, against SIMD schoolbook."""


@fieldwise_init
struct _Field(ImplicitlyCopyable, Movable):
    var p: UInt64
    var neg_inverse: UInt64
    var r2: UInt64
    var one: UInt64
    var batch: Int
    var karatsuba: Int


def _field(p: UInt64) raises PolyError -> _Field:
    if p < 3 or p % 2 == 0 or p >= UInt64(1) << 62:
        raise PolyError(PolyErrorKind.DOMAIN, "native residues require an odd prime below 2**62")
    var inverse = p
    for _ in range(5):
        inverse *= 2 - p * inverse
    var r = UInt64((UInt128(1) << 64) % UInt128(p))
    var r2 = UInt64((UInt128(r) * UInt128(r)) % UInt128(p))
    # batch * (p-1)^2 < p * 2^64 keeps every partial sum valid for REDC.
    var batch = Int(min(UInt64.MAX // p, UInt64(1) << 20))
    return _Field(p, 0 - inverse, r2, r, batch, _KARATSUBA_SMALL if p < _SMALL else _KARATSUBA)


@always_inline
def _redc(t: UInt128, f: _Field) -> UInt64:
    var m = UInt64(t) * f.neg_inverse
    var u = UInt64((t + UInt128(m) * UInt128(f.p)) >> 64)
    return u - f.p if u >= f.p else u


@always_inline
def _mulm(a: UInt64, b: UInt64, f: _Field) -> UInt64:
    return _redc(UInt128(a) * UInt128(b), f)


@always_inline
def _addm(a: UInt64, b: UInt64, f: _Field) -> UInt64:
    var s = a + b
    return s - f.p if s >= f.p else s


@always_inline
def _subm(a: UInt64, b: UInt64, f: _Field) -> UInt64:
    return a - b if a >= b else a + f.p - b


@always_inline
def _negm(a: UInt64, f: _Field) -> UInt64:
    return f.p - a if a else 0


def _to(value: UInt64, f: _Field) -> UInt64:
    return _mulm(value % f.p, f.r2, f)


def _from(value: UInt64, f: _Field) -> UInt64:
    return _redc(UInt128(value), f)


def _powm(a: UInt64, e: UInt64, f: _Field) -> UInt64:
    var result = f.one
    var base = a
    var n = e
    while n:
        if n & 1:
            result = _mulm(result, base, f)
        n >>= 1
        if n:
            base = _mulm(base, base, f)
    return result


def _invm(a: UInt64, f: _Field, mut budget: Budget) raises PolyError -> UInt64:
    if a == 0:
        raise PolyError(PolyErrorKind.DOMAIN, "inverse of zero")
    budget.charge(64)
    return _powm(a, f.p - 2, f)


def _trim(mut a: List[UInt64]):
    while len(a) and a[len(a) - 1] == 0:
        _ = a.pop()


def _dot(a: Pointer[mut=False, UInt64, _], b: Pointer[mut=False, UInt64, _], n: Int, f: _Field) -> UInt64:
    """Return the Montgomery sum of a[i] * b[i] for i below n."""
    var total = UInt64(0)
    var i = 0
    if f.p < _SMALL and n >= 16:
        var mask = SIMD[DType.uint64, 8](0xFFFFFFFF)
        while i + 8 <= n:
            var stop = min(n, i + 8 * 256)
            var acc = SIMD[DType.uint64, 8](0)
            while i + 8 <= stop:
                var x = a.unsafe_offset(i).unsafe_load[width=8]()
                var y = b.unsafe_offset(i).unsafe_load[width=8]()
                acc += (x & mask) * (y & mask)
                i += 8
            comptime for lane in range(8):
                total = _addm(total, _redc(UInt128(acc[lane]), f), f)
    while i < n:
        var stop = min(n, i + f.batch)
        var acc = UInt128(0)
        for j in range(i, stop):
            acc += UInt128(a.unsafe_offset(j).unsafe_load()) * UInt128(b.unsafe_offset(j).unsafe_load())
        total = _addm(total, _redc(acc, f), f)
        i = stop
    return total


def _reversed(a: List[UInt64], n: Int, mut budget: Budget) raises PolyError -> List[UInt64]:
    """The first n coefficients of a, zero-padded, in reverse order."""
    _allocation[UInt64](n, budget)
    var result = List[UInt64](length=n, fill=0)
    for i in range(min(n, len(a))):
        result[n - 1 - i] = a[i]
    return result^


def _schoolbook(a: List[UInt64], b: List[UInt64], limit: Int, f: _Field, mut budget: Budget) raises PolyError -> List[UInt64]:
    """The product's coefficients below `limit`, trimmed."""
    var n = len(a)
    var m = len(b)
    if n == 0 or m == 0 or limit <= 0:
        return List[UInt64]()
    var size = min(n + m - 1, limit)
    _charge_size(_product(min(n, size), min(m, size)), budget)
    var reversed = _reversed(b, m, budget)
    _allocation[UInt64](size, budget)
    var result = List[UInt64](capacity=size)
    var pa = a.unsafe_ptr()
    var pb = reversed.unsafe_ptr()
    if a.unsafe_ptr() == b.unsafe_ptr() and n == m:
        # Squares pair a_i a_j with a_j a_i: half the terms, doubled.
        for k in range(size):
            var lo = max(0, k - m + 1)
            var hi = (k - 1) // 2
            var s = UInt64(0)
            if hi >= lo:
                s = _dot(pa.unsafe_offset(lo), pb.unsafe_offset(m - 1 - k + lo), hi - lo + 1, f)
                s = _addm(s, s, f)
            if k % 2 == 0:
                s = _addm(s, _mulm(a[k // 2], a[k // 2], f), f)
            result.append(s)
    else:
        for k in range(size):
            var lo = max(0, k - m + 1)
            var hi = min(k, n - 1)
            result.append(_dot(pa.unsafe_offset(lo), pb.unsafe_offset(m - 1 - k + lo), hi - lo + 1, f))
    _trim(result)
    return result^


def _add(a: List[UInt64], b: List[UInt64], f: _Field, mut budget: Budget) raises PolyError -> List[UInt64]:
    var n = max(len(a), len(b))
    _allocation[UInt64](n, budget)
    var result = List[UInt64](capacity=n)
    for i in range(n):
        var x = a[i] if i < len(a) else UInt64(0)
        var y = b[i] if i < len(b) else UInt64(0)
        result.append(_addm(x, y, f))
    _trim(result)
    return result^


def _sub(a: List[UInt64], b: List[UInt64], f: _Field, mut budget: Budget) raises PolyError -> List[UInt64]:
    var n = max(len(a), len(b))
    _allocation[UInt64](n, budget)
    var result = List[UInt64](capacity=n)
    for i in range(n):
        var x = a[i] if i < len(a) else UInt64(0)
        var y = b[i] if i < len(b) else UInt64(0)
        result.append(_subm(x, y, f))
    _trim(result)
    return result^


def _slice(a: List[UInt64], lo: Int, hi: Int, mut budget: Budget) raises PolyError -> List[UInt64]:
    var stop = min(hi, len(a))
    var n = max(stop - lo, 0)
    _allocation[UInt64](n, budget)
    var result = List[UInt64](capacity=n)
    for i in range(lo, stop):
        result.append(a[i])
    _trim(result)
    return result^


def _accumulate(mut target: List[UInt64], source: List[UInt64], shift: Int, f: _Field):
    for i in range(len(source)):
        target[shift + i] = _addm(target[shift + i], source[i], f)


def _karatsuba(a: List[UInt64], b: List[UInt64], f: _Field, mut budget: Budget) raises PolyError -> List[UInt64]:
    var n = len(a)
    var m = len(b)
    if min(n, m) < f.karatsuba:
        return _schoolbook(a, b, n + m, f, budget)
    if 2 * min(n, m) <= max(n, m):
        # Unbalanced: multiply the shorter operand by consecutive blocks.
        var shorter = a.copy() if n <= m else b.copy()
        var longer = b.copy() if n <= m else a.copy()
        var s = len(shorter)
        _allocation[UInt64](n + m - 1, budget)
        var result = List[UInt64](length=n + m - 1, fill=0)
        var start = 0
        while start < len(longer):
            var block = _slice(longer, start, start + s, budget)
            _accumulate(result, _karatsuba(shorter, block, f, budget), start, f)
            start += s
        _trim(result)
        return result^
    var k = (max(n, m) + 1) // 2
    var a0 = _slice(a, 0, k, budget)
    var a1 = _slice(a, k, n, budget)
    var b0 = _slice(b, 0, k, budget)
    var b1 = _slice(b, k, m, budget)
    var low = _karatsuba(a0, b0, f, budget)
    var high = _karatsuba(a1, b1, f, budget)
    var middle = _karatsuba(_add(a0, a1, f, budget), _add(b0, b1, f, budget), f, budget)
    middle = _sub(_sub(middle, low, f, budget), high, f, budget)
    _allocation[UInt64](n + m - 1, budget)
    var result = List[UInt64](length=n + m - 1, fill=0)
    _accumulate(result, low, 0, f)
    _accumulate(result, middle, k, f)
    _accumulate(result, high, 2 * k, f)
    _trim(result)
    return result^


def _mul(a: List[UInt64], b: List[UInt64], f: _Field, mut budget: Budget) raises PolyError -> List[UInt64]:
    if len(a) == 0 or len(b) == 0:
        return List[UInt64]()
    var shorter = min(len(a), len(b))
    var bits = 0
    while (UInt64(1) << UInt64(bits)) <= f.p - 1:
        bits += 1
    var magnitude = 0
    while (1 << magnitude) <= shorter:
        magnitude += 1
    var threshold = _TRANSFORM_ONE if 2 * bits + magnitude <= 61 else (_TRANSFORM_SMALL if f.p < _SMALL else _TRANSFORM)
    if shorter >= threshold:
        # The convolution of Montgomery residues aR, bR is abR^2; one REDC per
        # coefficient returns it to Montgomery form.
        var square = a == b
        var c = _modular_product(a, b, len(a) + len(b) - 1, f.p, square, budget)
        for i in range(len(c)):
            c[i] = _redc(UInt128(c[i]), f)
        _trim(c)
        return c^
    return _karatsuba(a, b, f, budget)


def _mullow(a: List[UInt64], b: List[UInt64], limit: Int, f: _Field, mut budget: Budget) raises PolyError -> List[UInt64]:
    if min(len(a), len(b), limit) < 2 * f.karatsuba:
        return _schoolbook(a, b, limit, f, budget)
    var full = _mul(_slice(a, 0, limit, budget), _slice(b, 0, limit, budget), f, budget)
    return _slice(full, 0, limit, budget)


def _scale(a: List[UInt64], c: UInt64, f: _Field, mut budget: Budget) raises PolyError -> List[UInt64]:
    _allocation[UInt64](len(a), budget)
    var result = List[UInt64](capacity=len(a))
    for v in a:
        result.append(_mulm(v, c, f))
    _trim(result)
    return result^


def _monic(a: List[UInt64], f: _Field, mut budget: Budget) raises PolyError -> List[UInt64]:
    if len(a) == 0 or a[len(a) - 1] == f.one:
        return a.copy()
    return _scale(a, _invm(a[len(a) - 1], f, budget), f, budget)


def _divmod_classic(a: List[UInt64], b: List[UInt64], quotient: Bool, f: _Field, mut budget: Budget) raises PolyError -> Tuple[List[UInt64], List[UInt64]]:
    """Long division by any nonzero divisor; returns (quotient or empty, remainder)."""
    if len(b) == 0:
        raise PolyError(PolyErrorKind.DOMAIN, "division by the zero polynomial")
    var r = a.copy()
    var q = List[UInt64]()
    var n = len(b)
    if len(r) < n:
        return (q^, r^)
    _charge_size(_product(len(r) - n + 1, n), budget)
    var inverse = _invm(b[n - 1], f, budget)
    if quotient:
        q = List[UInt64](length=len(r) - n + 1, fill=0)
    var top = len(r) - 1
    while top >= n - 1:
        var c = r[top]
        if c:
            var factor = _mulm(c, inverse, f)
            var shift = top - n + 1
            if quotient:
                q[shift] = factor
            for i in range(n - 1):
                r[shift + i] = _subm(r[shift + i], _mulm(factor, b[i], f), f)
            r[top] = 0
        top -= 1
    _trim(r)
    return (q^, r^)


def _gcd(a: List[UInt64], b: List[UInt64], f: _Field, mut budget: Budget) raises PolyError -> List[UInt64]:
    """The monic gcd; zero only when both inputs are zero.

    Residues share the Montgomery form a 2^64 mod p of the word-size Euclidean
    kernels, which run the remainder sequence.
    """
    _allocation[UInt64](len(a) + len(b), budget)
    return _gcd_words(a.copy(), b.copy(), _EuclidField.of(f.p), budget)


comptime _SPECTRAL = 128
"""Modulus degree from which reductions, modular products and compositions
keep their fixed operands as transforms modulo one transform prime."""
comptime _SPECTRAL_BOUND = UInt128(1) << 61
"""Every transform prime exceeds 2^61: exact integer coefficients below it survive."""


def _spectral_ok(f: _Field, terms: Int) -> Bool:
    """Whether sums of `terms` products of residues stay below every transform prime."""
    return UInt128(f.p - 1) * UInt128(f.p - 1) * UInt128(terms) < _SPECTRAL_BOUND


struct _Spectral(Movable):
    """Cyclic convolutions of length n modulo the first transform prime, for
    Montgomery residues whose exact integer convolutions stay below it.

    Transforms hold values below 2q; pointwise products use the transform
    prime's Montgomery reduction, whose 2^-64 is folded, with 1/n, into the
    scale of the inverse; the exact result v then leaves through one
    reduction modulo p, which turns a R^2 into a R.
    """
    var n: Int
    var q: UInt64
    var q_inverse: UInt64
    var scale: UInt64
    var scale_quotient: UInt64
    var tables: _Tables
    var field: _Field

    def __init__(out self, n: Int, field: _Field, mut budget: Budget) raises PolyError:
        var primes = materialize[_PRIMES]()
        var roots = materialize[_ROOTS]()
        _charge_size(_product(4, n), budget)
        _allocation[UInt64](_product(4, n), budget)
        self.n = n
        self.q = primes[0]
        self.q_inverse = _montgomery_inverse(self.q)
        var r = UInt64(((UInt128(1) << 64) % UInt128(self.q)))
        self.scale = UInt64((UInt128(r) * UInt128(_transform_power(UInt64(n) % self.q, self.q - 2, self.q))) % UInt128(self.q))
        self.scale_quotient = _shoup_quotient(self.scale, self.q)
        self.tables = _Tables(self.q, roots[0], n)
        self.field = field

    def forward(self, values: List[UInt64], mut budget: Budget) raises PolyError -> List[UInt64]:
        """The transform of at most n residues below p."""
        _charge_size(_product(self.n, _log2(self.n) + 1), budget)
        _allocation[UInt64](self.n, budget)
        var x = List[UInt64](length=self.n, fill=0)
        for i in range(min(len(values), self.n)):
            x.unsafe_get(i) = values[i]
        _forward(x, self.tables, self.q)
        return x^

    def accumulate(self, mut total: List[UInt64], a: List[UInt64], b: List[UInt64]):
        """total += a b pointwise, everything below 2q."""
        var q2 = 2 * self.q
        for i in range(self.n):
            var s = total.unsafe_get(i) + _transform_redc(a.unsafe_get(i), b.unsafe_get(i), self.q, self.q_inverse)
            total.unsafe_get(i) = s - q2 if s >= q2 else s

    def product(self, a: List[UInt64], b: List[UInt64]) -> List[UInt64]:
        var x = List[UInt64](length=self.n, fill=0)
        for i in range(self.n):
            x.unsafe_get(i) = _transform_redc(a.unsafe_get(i), b.unsafe_get(i), self.q, self.q_inverse)
        return x^

    def sum(self, a: List[UInt64], b: List[UInt64]) -> List[UInt64]:
        """a + b pointwise, below 2q from inputs below 2q."""
        var q2 = 2 * self.q
        var x = List[UInt64](length=self.n, fill=0)
        for i in range(self.n):
            var t = a.unsafe_get(i) + b.unsafe_get(i)
            x.unsafe_get(i) = t - q2 if t >= q2 else t
        return x^

    def back(self, var x: List[UInt64], lo: Int, hi: Int, mut budget: Budget) raises PolyError -> List[UInt64]:
        """Coefficients lo ..< hi of the convolution whose pointwise products x holds, as Montgomery residues, trimmed."""
        _charge_size(_product(self.n, _log2(self.n) + 1), budget)
        _inverse(x, self.tables, self.q)
        _allocation[UInt64](hi - lo, budget)
        var out = List[UInt64](capacity=hi - lo)
        for i in range(lo, hi):
            var v = _reduce_2q(_shoup(x.unsafe_get(i), self.scale, self.scale_quotient, self.q), self.q)
            out.append(_redc(UInt128(v), self.field))
        _trim(out)
        return out^


def _log2(n: Int) -> Int:
    var log = 0
    while (1 << log) < n:
        log += 1
    return log


@fieldwise_init
struct _ModulusSpectra(Movable):
    """The transforms of a modulus f and of its reversed inverse, at length 2 deg f or more."""
    var spectral: _Spectral
    var f: List[UInt64]
    var inverse: List[UInt64]


@fieldwise_init
struct _Modulus(Copyable, Movable):
    """A monic modulus with the reversed inverse used for division by products."""
    var f: List[UInt64]
    var inverse: List[UInt64]
    var spectra: Optional[ArcPointer[_ModulusSpectra]]


def _modulus(f: List[UInt64], field: _Field, mut budget: Budget) raises PolyError -> _Modulus:
    if len(f) == 0 or f[len(f) - 1] != field.one:
        raise PolyError(PolyErrorKind.DOMAIN, "native modulus must be monic")
    var n = len(f) - 1
    # Power series inverse g of rev(f) to precision n by the triangular
    # recurrence g_k = -sum_{i=1..k} rev_i g_(k-i). The buffer holds g reversed,
    # so each step is one contiguous dot product.
    var reversed = _reversed(f, n + 1, budget)
    _charge_size(_product(n, n) // 2 + 1, budget)
    _allocation[UInt64](max(n, 1), budget)
    var buffer = List[UInt64](length=max(n, 1), fill=0)
    buffer[len(buffer) - 1] = field.one
    for k in range(1, n):
        var s = _dot(reversed.unsafe_ptr().unsafe_offset(1), buffer.unsafe_ptr().unsafe_offset(n - k), k, field)
        buffer[n - 1 - k] = _negm(s, field)
    var g = _reversed(buffer, len(buffer), budget)
    _trim(g)
    var spectra = Optional[ArcPointer[_ModulusSpectra]](None)
    if n >= _SPECTRAL and _spectral_ok(field, n + 1):
        var spectral = _Spectral(_transform_length(2 * n), field, budget)
        var tf = spectral.forward(f, budget)
        var tg = spectral.forward(g, budget)
        spectra = ArcPointer(_ModulusSpectra(spectral^, tf^, tg^))
    return _Modulus(f.copy(), g^, spectra^)


def _rem(a: List[UInt64], m: _Modulus, field: _Field, mut budget: Budget) raises PolyError -> List[UInt64]:
    """Reduce a polynomial of length at most 2*deg(f) - 1 modulo f."""
    var n = len(m.f) - 1
    if len(a) <= n:
        return a.copy()
    if len(a) > 2 * n:
        return _divmod_classic(a, m.f, False, field, budget)[1].copy()
    var size = len(a)
    var length = size - n
    if m.spectra:
        # rev(q) = rev(a) g mod x^length and r = a - q f mod x^n, with the
        # transforms of g and f kept; neither product wraps at length >= 2n.
        ref spectra = m.spectra.value()[]
        var top = _reversed(a, size, budget)
        top.resize(length, 0)
        var rq = spectra.spectral.back(spectra.spectral.product(spectra.spectral.forward(top, budget), spectra.inverse), 0, length, budget)
        var q = _reversed(rq, length, budget)
        _trim(q)
        var qf = spectra.spectral.back(spectra.spectral.product(spectra.spectral.forward(q, budget), spectra.f), 0, n, budget)
        return _sub(_slice(a, 0, n, budget), qf, field, budget)
    if n < 8 * field.karatsuba:
        # rev(q) = rev(a) * g mod x^length, and r = a - q * f mod x^n. With
        # q_i = rq_(length-1-i), both sums are forward dot products, so no
        # operand is reversed.
        _charge_size(_product(length, n) + 1, budget)
        _allocation[UInt64](_sum(length, n), budget)
        var rq = List[UInt64](capacity=length)
        var pa = a.unsafe_ptr()
        var pg = m.inverse.unsafe_ptr()
        for k in range(length):
            var count = min(k + 1, len(m.inverse))
            rq.append(_dot(pa.unsafe_offset(size - 1 - k), pg, count, field))
        var result = List[UInt64](capacity=n)
        var pq = rq.unsafe_ptr()
        var pf = m.f.unsafe_ptr()
        for k in range(n):
            var t0 = max(0, length - 1 - k)
            var product = _dot(pq.unsafe_offset(t0), pf.unsafe_offset(t0 + k - length + 1), length - t0, field)
            result.append(_subm(a[k], product, field))
        _trim(result)
        return result^
    # rev(q) = rev(a) * rev(f)^(-1) mod x^length.
    var ra = _reversed(a, len(a), budget)
    var rq = _mullow(ra, m.inverse, length, field, budget)
    var q = _reversed(rq, length, budget)
    _trim(q)
    var qf = _mullow(q, m.f, n, field, budget)
    var low = _slice(a, 0, n, budget)
    return _sub(low, qf, field, budget)


def _mulmod(a: List[UInt64], b: List[UInt64], m: _Modulus, field: _Field, mut budget: Budget) raises PolyError -> List[UInt64]:
    var n = len(m.f) - 1
    if m.spectra and len(a) <= n and len(b) <= n and len(a) and len(b):
        ref spectral = m.spectra.value()[].spectral
        var product = spectral.back(spectral.product(spectral.forward(a, budget), spectral.forward(b, budget)), 0, len(a) + len(b) - 1, budget)
        return _rem(product, m, field, budget)
    return _rem(_mul(a, b, field, budget), m, field, budget)


def _powmod(a: List[UInt64], e: UInt64, m: _Modulus, field: _Field, mut budget: Budget) raises PolyError -> List[UInt64]:
    var result: List[UInt64] = [field.one]
    if len(m.f) == 1:
        return List[UInt64]()
    var base = _rem(a, m, field, budget)
    var n = e
    while n:
        budget.charge(1)
        if n & 1:
            result = _mulmod(result, base, m, field, budget)
        n >>= 1
        if n:
            base = _mulmod(base, base, m, field, budget)
    return result^


@fieldwise_init
struct _Composer(Copyable, Movable):
    """Brent–Kung powers of h modulo f: h^i for i below `block`, stored
    transposed for dot products, and the giant powers h^(j*block), also as
    transforms when their products can be summed in one transform prime."""
    var block: Int
    var columns: List[List[UInt64]]
    var giants: List[List[UInt64]]
    var spectra: Optional[ArcPointer[_ComposerSpectra]]


@fieldwise_init
struct _ComposerSpectra(Movable):
    var spectral: _Spectral
    var giants: List[List[UInt64]]


def _composer(h: List[UInt64], m: _Modulus, field: _Field, mut budget: Budget) raises PolyError -> _Composer:
    var n = len(m.f) - 1
    var block = 1
    while block * block < n:
        block += 1
    # powers[i] = h^i mod f for i <= block.
    _allocation[List[UInt64]](block + 1, budget)
    var powers = List[List[UInt64]](capacity=block + 1)
    powers.append([field.one])
    for i in range(1, block + 1):
        powers.append(_mulmod(powers[i - 1], h, m, field, budget))
    _allocation[UInt64](_product(n, block), budget)
    var columns = List[List[UInt64]](capacity=n)
    for c in range(n):
        var column = List[UInt64](capacity=block)
        for i in range(block):
            column.append(powers[i][c] if c < len(powers[i]) else UInt64(0))
        columns.append(column^)
    var blocks = (n + block - 1) // block
    _allocation[List[UInt64]](blocks, budget)
    var giants = List[List[UInt64]](capacity=blocks)
    giants.append([field.one])
    for j in range(1, blocks):
        giants.append(_mulmod(giants[j - 1], powers[block], m, field, budget))
    var spectra = Optional[ArcPointer[_ComposerSpectra]](None)
    # A composition sums `blocks` products of at most n terms each.
    if n >= _SPECTRAL and _spectral_ok(field, _product(blocks, n)):
        var spectral = _Spectral(_transform_length(2 * n), field, budget)
        var transforms = List[List[UInt64]](capacity=blocks)
        for j in range(blocks):
            transforms.append(spectral.forward(giants[j], budget))
        spectra = ArcPointer(_ComposerSpectra(spectral^, transforms^))
    return _Composer(block, columns^, giants^, spectra^)


def _compose(g: List[UInt64], c: _Composer, m: _Modulus, field: _Field, mut budget: Budget) raises PolyError -> List[UInt64]:
    """g(h) mod f for the h prepared in c; g has degree below deg(f)."""
    var n = len(m.f) - 1
    if len(g) == 0:
        return List[UInt64]()
    if len(g) > n:
        return _compose(_rem(g, m, field, budget), c, m, field, budget)
    var blocks = (len(g) + c.block - 1) // c.block
    _charge_size(_product(n, len(g)), budget)
    if c.spectra:
        # Sum G_j(h) h^(j block) over the kept transforms of the giants; one
        # inverse transform and one reduction follow.
        ref spectra = c.spectra.value()[]
        var sum = List[UInt64](length=spectra.spectral.n, fill=0)
        for j in range(blocks):
            var start = j * c.block
            var stop = min(len(g), start + c.block)
            var piece = List[UInt64](capacity=n)
            var gp = g.unsafe_ptr().unsafe_offset(start)
            for k in range(n):
                piece.append(_dot(gp, c.columns[k].unsafe_ptr(), stop - start, field))
            _trim(piece)
            if len(piece):
                spectra.spectral.accumulate(sum, spectra.spectral.forward(piece, budget), spectra.giants[j])
        return _rem(spectra.spectral.back(sum^, 0, 2 * n - 1, budget), m, field, budget)
    # Sum the unreduced products G_j(h) * h^(j*block); one reduction follows.
    _allocation[UInt64](2 * n, budget)
    var total = List[UInt64](length=max(2 * n - 1, 1), fill=0)
    for j in range(blocks):
        var start = j * c.block
        var stop = min(len(g), start + c.block)
        var piece = List[UInt64](capacity=n)
        var gp = g.unsafe_ptr().unsafe_offset(start)
        for k in range(n):
            piece.append(_dot(gp, c.columns[k].unsafe_ptr(), stop - start, field))
        _trim(piece)
        if j == 0:
            _accumulate(total, piece, 0, field)
        else:
            _accumulate(total, _mul(piece, c.giants[j], field, budget), 0, field)
    _trim(total)
    return _rem(total, m, field, budget)


def _derivative(a: List[UInt64], f: _Field, mut budget: Budget) raises PolyError -> List[UInt64]:
    var n = max(len(a) - 1, 0)
    _allocation[UInt64](n, budget)
    var result = List[UInt64](capacity=n)
    for i in range(1, len(a)):
        result.append(_mulm(a[i], _to(UInt64(i), f), f))
    _trim(result)
    return result^


def _x(field: _Field) -> List[UInt64]:
    return [UInt64(0), field.one]


def _cost_bits(e: UInt64) -> Int:
    """Products used by square-and-multiply for the exponent e."""
    var bits = 0
    var ones = 0
    var n = e
    while n:
        bits += 1
        ones += Int(n & 1)
        n >>= 1
    return bits + ones - 1


def _prefer_powering(n: Int, exponent_products: Int) -> Bool:
    """Whether raising to p by squaring beats Brent–Kung composition at degree n.

    A Karatsuba product modulo f costs about 3 n^1.58 coefficient operations;
    a composition about n^2 plus sqrt(n) such products. The estimate depends
    only on sizes, never on timings.
    """
    var product = 3.0 * Float64(n) ** 1.585 + 1.0
    var root = Float64(n) ** 0.5
    return Float64(exponent_products) * product <= Float64(n) * Float64(n) + root * product


@fieldwise_init
struct _Frobenius(Movable):
    """Raises residues to the p-th power modulo one monic modulus."""
    var modulus: _Modulus
    var composer: Optional[_Composer]


def _frobenius(xp: List[UInt64], m: _Modulus, field: _Field, mut budget: Budget) raises PolyError -> _Frobenius:
    var n = len(m.f) - 1
    if _prefer_powering(n, _cost_bits(field.p)):
        return _Frobenius(m.copy(), None)
    return _Frobenius(m.copy(), _composer(xp, m, field, budget))


def _apply(g: List[UInt64], frobenius: _Frobenius, field: _Field, mut budget: Budget) raises PolyError -> List[UInt64]:
    if frobenius.composer:
        return _compose(g, frobenius.composer.value(), frobenius.modulus, field, budget)
    return _powmod(g, field.p, frobenius.modulus, field, budget)


struct _Random(Movable):
    var state: UInt64

    def __init__(out self, seed: UInt64):
        self.state = seed

    def next(mut self, mut budget: Budget) raises PolyError -> UInt64:
        budget.charge(1)
        self.state += 0x9E3779B97F4A7C15
        var z = self.state
        z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9
        z = (z ^ (z >> 27)) * 0x94D049BB133111EB
        return z ^ (z >> 31)


def _equal_degree(g: List[UInt64], degree: Int, xp: List[UInt64], field: _Field, mut rng: _Random, mut factors: List[List[UInt64]], mut budget: Budget) raises PolyError:
    """Split a product of distinct monic irreducibles of one degree (odd p)."""
    var n = len(g) - 1
    if n == degree:
        _allocation[List[UInt64]](1, budget)
        factors.append(g.copy())
        return
    var m = _modulus(g, field, budget)
    var frobenius: Optional[_Frobenius] = None
    if degree > 1:
        frobenius = _frobenius(_rem(xp, m, field, budget), m, field, budget)
    var pieces: List[List[UInt64]] = [g.copy()]
    var done = 0
    var half = (field.p - 1) // 2
    while done < len(pieces):
        budget.charge(1)
        _allocation[UInt64](n, budget)
        var a = List[UInt64](capacity=n)
        for _ in range(n):
            a.append(_to(rng.next(budget) % field.p, field))
        _trim(a)
        if len(a) == 0:
            continue
        # b = a^((p^d - 1)/2) = power * frob(power * frob(...)), power = a^((p-1)/2).
        var power = _powmod(a, half, m, field, budget)
        var b = power.copy()
        for _ in range(1, degree):
            budget.charge(1)
            b = _mulmod(_apply(b, frobenius.value(), field, budget), power, m, field, budget)
        b = _sub(b, [field.one], field, budget)
        var next = List[List[UInt64]]()
        done = 0
        for piece in pieces:
            budget.charge(1)
            if len(piece) - 1 == degree:
                next.append(piece.copy())
                done += 1
                continue
            var reduced = _divmod_classic(b, piece, False, field, budget)[1].copy()
            var divisor = _gcd(piece, reduced, field, budget)
            if len(divisor) > 1 and len(divisor) < len(piece):
                var other = _divmod_classic(piece, divisor, True, field, budget)[0].copy()
                done += Int(len(divisor) - 1 == degree) + Int(len(other) - 1 == degree)
                next.append(divisor^)
                next.append(other^)
            else:
                next.append(piece.copy())
        pieces = next^
    for piece in pieces:
        _allocation[List[UInt64]](1, budget)
        factors.append(piece.copy())


def _distinct_degree(f: List[UInt64], field: _Field, seed: UInt64, mut budget: Budget) raises PolyError -> List[List[UInt64]]:
    """Factor a monic squarefree polynomial by baby-step giant-step distinct-degree
    factorization (Kaltofen–Shoup) and Cantor–Zassenhaus equal-degree splitting.
    """
    var factors = List[List[UInt64]]()
    var n = len(f) - 1
    if n <= 0:
        return factors^
    if n == 1:
        factors.append(f.copy())
        return factors^
    var rng = _Random(seed)
    var m = _modulus(f, field, budget)
    var xp = _powmod(_x(field), field.p, m, field, budget)
    var steps = 1
    while 2 * steps * steps < n:
        steps += 1
    # baby[i] = x^(p^i) mod f for i <= steps.
    var frobenius = _frobenius(xp, m, field, budget)
    _allocation[List[UInt64]](steps + 1, budget)
    var baby = List[List[UInt64]](capacity=steps + 1)
    baby.append(_x(field))
    baby.append(xp.copy())
    for i in range(2, steps + 1):
        baby.append(_apply(baby[i - 1], frobenius, field, budget))
    var giant = baby[steps].copy()
    var leap: Optional[_Composer] = None
    if not _prefer_powering(n, _product(steps, _cost_bits(field.p))):
        leap = _composer(giant, m, field, budget)
    # Interval factors H - h_i come from kept transforms of H and of -h_i, as
    # nonnegative residues: H + (p - h_i) has entries below 2p, and products
    # of at most n terms below 2p^2 must stay exact.
    var spectral = Bool(m.spectra) and _spectral_ok(field, 2 * n + 2)
    var negated = List[List[UInt64]]()
    if spectral:
        _allocation[List[UInt64]](steps, budget)
        for i in range(steps):
            var minus = List[UInt64](capacity=len(baby[i]))
            for v in baby[i]:
                minus.append(_negm(v, field))
            negated.append(m.spectra.value()[].spectral.forward(minus, budget))
    var remaining = f.copy()
    var j = 1
    while True:
        budget.charge(1)
        var low = (j - 1) * steps + 1
        if len(remaining) - 1 < 2 * low:
            break
        var interval: List[UInt64] = [field.one]
        if spectral:
            ref transform = m.spectra.value()[].spectral
            var high = transform.forward(giant, budget)
            for i in range(steps):
                var product = transform.back(transform.product(transform.forward(interval, budget), transform.sum(high, negated[i])), 0, len(interval) + n - 1, budget)
                interval = _rem(product, m, field, budget)
        else:
            for i in range(steps):
                interval = _mulmod(interval, _sub(giant, baby[i], field, budget), m, field, budget)
        var block = _gcd(remaining, interval, field, budget)
        if len(block) > 1:
            remaining = _divmod_classic(remaining, block, True, field, budget)[0].copy()
            var i = steps - 1
            while i >= 0 and len(block) > 1:
                budget.charge(1)
                var difference = _sub(giant, baby[i], field, budget)
                var part = _gcd(block, _divmod_classic(difference, block, False, field, budget)[1], field, budget)
                if len(part) > 1:
                    _equal_degree(part, j * steps - i, xp, field, rng, factors, budget)
                    block = _divmod_classic(block, part, True, field, budget)[0].copy()
                i -= 1
        j += 1
        if leap:
            giant = _compose(giant, leap.value(), m, field, budget)
        else:
            for _ in range(steps):
                giant = _apply(giant, frobenius, field, budget)
    if len(remaining) > 1:
        factors.append(remaining^)
    return factors^
