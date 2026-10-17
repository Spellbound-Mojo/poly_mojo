"""Dense univariate Euclid kernels (gcd, resultant) over word-size prime fields.

Coefficients are UInt64 lists in increasing degree, held in Montgomery form
(a·2^64 mod p) by the kernels below. Every prime the library admits is below
2^62, so Montgomery reduction of a product of two residues never overflows
128 bits. The prime 2 has no Montgomery form; callers use the generic path.

Primes below 2^30 run the Euclidean recurrences in a 32-bit Montgomery form
(a·2^32 mod p) instead, where every product fits a 64-bit lane and the row
updates vectorize; the entry points convert on the way in and out.
"""
from .errors import Budget, PolyError, PolyErrorKind, _allocation, _charge_size


comptime _SMALL_PRIME = UInt64(1) << 30
"""Primes below this bound keep three products of residues under p 2^32."""
comptime _LANES = 8


trait _WordField(ImplicitlyCopyable, Movable):
    """Montgomery arithmetic the Euclidean recurrences run on."""

    def mul(self, a: UInt64, b: UInt64) -> UInt64:
        ...

    def add(self, a: UInt64, b: UInt64) -> UInt64:
        ...

    def sub(self, a: UInt64, b: UInt64) -> UInt64:
        ...

    def one(self) -> UInt64:
        ...

    def inverse(self, a: UInt64) raises PolyError -> UInt64:
        """The Montgomery form of 1/a for a nonzero Montgomery residue a."""
        ...

    def combine(self, mut a: List[UInt64], base: Int, b: List[UInt64], count: Int, s: UInt64, m1: UInt64, m0: UInt64):
        """Set a[base + i] to a[base + i] s + m1 b[i - 1] + m0 b[i] for i below count, with b[-1] = 0."""
        ...


def _inverse_mod(value: UInt64, p: UInt64) raises PolyError -> UInt64:
    """The standard residue 1/value modulo p, by the extended Euclidean algorithm."""
    var modulus = Int64(p)
    var t = Int64(0)
    var next_t = Int64(1)
    var r = modulus
    var next_r = Int64(value)
    while next_r != 0:
        var q = r // next_r
        var step = t - q * next_t
        t = next_t
        next_t = step
        step = r - q * next_r
        r = next_r
        next_r = step
    if r != 1:
        raise PolyError(PolyErrorKind.DOMAIN, "residue is not invertible")
    if t < 0:
        t += modulus
    return UInt64(t)


def _power[F: _WordField](field: F, a: UInt64, n: Int) -> UInt64:
    var result = field.one()
    var base = a
    var e = n
    while e > 0:
        if e & 1:
            result = field.mul(result, base)
        e >>= 1
        if e:
            base = field.mul(base, base)
    return result


@fieldwise_init
struct _Field(_WordField):
    var p: UInt64
    var negated_inverse: UInt64
    var r2: UInt64

    @staticmethod
    def of(p: UInt64) -> Self:
        # Newton's iteration doubles the correct low bits of 1/p each step.
        var inverse = p
        for _ in range(6):
            inverse = inverse * (2 - p * inverse)
        var r = (UInt128(1) << 64) % UInt128(p)
        return Self(p, UInt64(0) - inverse, UInt64((r * r) % UInt128(p)))

    @always_inline
    def reduce(self, t: UInt128) -> UInt64:
        var m = t.cast[DType.uint64]() * self.negated_inverse
        var u = ((t + UInt128(m) * UInt128(self.p)) >> 64).cast[DType.uint64]()
        return u - self.p if u >= self.p else u

    @always_inline
    def mul(self, a: UInt64, b: UInt64) -> UInt64:
        return self.reduce(UInt128(a) * UInt128(b))

    @always_inline
    def add(self, a: UInt64, b: UInt64) -> UInt64:
        var s = a + b
        return s - self.p if s >= self.p else s

    @always_inline
    def sub(self, a: UInt64, b: UInt64) -> UInt64:
        return a - b if a >= b else a + (self.p - b)

    @always_inline
    def enter(self, a: UInt64) -> UInt64:
        return self.mul(a, self.r2)

    @always_inline
    def leave(self, a: UInt64) -> UInt64:
        return self.reduce(UInt128(a))

    def one(self) -> UInt64:
        return self.enter(1)

    def inverse(self, a: UInt64) raises PolyError -> UInt64:
        """The Montgomery form of 1/a for a nonzero Montgomery residue a."""
        return self.enter(_inverse_mod(self.leave(a), self.p))

    def power(self, a: UInt64, n: Int) -> UInt64:
        return _power(self, a, n)

    def combine(self, mut a: List[UInt64], base: Int, b: List[UInt64], count: Int, s: UInt64, m1: UInt64, m0: UInt64):
        # The three products sum below 3p^2 < p 2^64: one reduction each.
        if count <= 0:
            return
        var ws = UInt128(s)
        var w1 = UInt128(m1)
        var w0 = UInt128(m0)
        var pa = a.unsafe_ptr().unsafe_offset(base)
        var pb = b.unsafe_ptr()
        var previous = UInt128(0)
        for i in range(count):
            var current = UInt128(pb.unsafe_offset(i).unsafe_load())
            var x = pa.unsafe_offset(i)
            x.unsafe_store(self.reduce(UInt128(x.unsafe_load()) * ws + w1 * previous + w0 * current))
            previous = current


@fieldwise_init
struct _SmallField(_WordField):
    """Montgomery arithmetic modulo p < 2^30 with R = 2^32, in 64-bit words."""
    var p: UInt64
    var negated_inverse: UInt64
    var r2: UInt64

    @staticmethod
    def of(p: UInt64) -> Self:
        var inverse = p
        for _ in range(5):
            inverse = inverse * (2 - p * inverse)
        var r = (UInt64(1) << 32) % p
        return Self(p, (UInt64(0) - inverse) & 0xFFFFFFFF, (r * r) % p)

    @always_inline
    def reduce(self, t: UInt64) -> UInt64:
        """t 2^-32 mod p for t < p 2^32."""
        var m = ((t & 0xFFFFFFFF) * self.negated_inverse) & 0xFFFFFFFF
        var u = (t + m * self.p) >> 32
        return u - self.p if u >= self.p else u

    @always_inline
    def mul(self, a: UInt64, b: UInt64) -> UInt64:
        return self.reduce(a * b)

    @always_inline
    def add(self, a: UInt64, b: UInt64) -> UInt64:
        var s = a + b
        return s - self.p if s >= self.p else s

    @always_inline
    def sub(self, a: UInt64, b: UInt64) -> UInt64:
        return a - b if a >= b else a + (self.p - b)

    def one(self) -> UInt64:
        return self.reduce(self.r2)

    def inverse(self, a: UInt64) raises PolyError -> UInt64:
        """The Montgomery form of 1/a for a nonzero Montgomery residue a."""
        return self.reduce(_inverse_mod(self.reduce(a), self.p) * self.r2)

    def combine(self, mut a: List[UInt64], base: Int, b: List[UInt64], count: Int, s: UInt64, m1: UInt64, m0: UInt64):
        # Residues stay below 2^30, so the three products sum below 3p^2 < p 2^32
        # and t + m p below 2^63; the masks let products use 32-bit multiplies.
        if count <= 0:
            return
        a[base] = self.reduce(a[base] * s + m0 * b[0])
        comptime Lane = SIMD[DType.uint64, _LANES]
        var mask = Lane(0xFFFFFFFF)
        var vs = Lane(s)
        var v1 = Lane(m1)
        var v0 = Lane(m0)
        var vp = Lane(self.p)
        var vn = Lane(self.negated_inverse)
        var pa = a.unsafe_ptr().unsafe_offset(base)
        var pb = b.unsafe_ptr()
        var i = 1
        while i + _LANES <= count:
            var x = pa.unsafe_offset(i).unsafe_load[width=_LANES]()
            var y1 = pb.unsafe_offset(i - 1).unsafe_load[width=_LANES]()
            var y0 = pb.unsafe_offset(i).unsafe_load[width=_LANES]()
            var t = (x & mask) * vs + (y1 & mask) * v1 + (y0 & mask) * v0
            var m = ((t & mask) * vn) & mask
            var u = (t + m * vp) >> 32
            pa.unsafe_offset(i).unsafe_store[width=_LANES](u.ge(vp).select(u - vp, u))
            i += _LANES
        while i < count:
            a[base + i] = self.reduce(a[base + i] * s + m1 * b[i - 1] + m0 * b[i])
            i += 1


def _trim_words(mut a: List[UInt64]):
    while len(a) and a[len(a) - 1] == 0:
        _ = a.pop()


def _reduce[F: _WordField](mut a: List[UInt64], b: List[UInt64], field: F, mut budget: Budget) raises PolyError -> Int:
    """Replace a by lc(b)^e (a mod b), trimmed, for b of positive length, and return e.

    A remainder step of one or two quotient terms (the usual case) takes no
    inverse: e is the number of terms, and lc^2 a - (q1 x + q0) b or
    lc a - q0 b eliminates them, three products per coefficient and one
    Montgomery reduction. Longer quotients use 1/lc(b), two terms per pass,
    with e = 0.
    """
    var db = len(b) - 1
    if len(a) <= db:
        return 0
    var terms = len(a) - db
    _charge_size(terms * len(b), budget)
    if db == 0:
        a.clear()
        return 0
    var lc = b[db]
    var k = len(a) - 1
    if terms == 2:
        var top = a[k]
        var n1 = field.mul(lc, top)
        var n0 = field.sub(field.mul(lc, a[k - 1]), field.mul(top, b[db - 1]))
        field.combine(a, 0, b, db, field.mul(lc, lc), field.sub(0, n1), field.sub(0, n0))
    elif terms == 1:
        field.combine(a, 0, b, db, lc, 0, field.sub(0, a[k]))
    else:
        terms = 0
        var inverse = field.inverse(lc)
        var one = field.one()
        while k > db:
            var q1 = field.mul(a[k], inverse)
            var q0 = field.mul(field.sub(a[k - 1], field.mul(q1, b[db - 1])), inverse)
            field.combine(a, k - 1 - db, b, db, one, field.sub(0, q1), field.sub(0, q0))
            k -= 2
        if k == db:
            var q = field.mul(a[k], inverse)
            if q:
                field.combine(a, 0, b, db, one, 0, field.sub(0, q))
    a.resize(db, 0)
    _trim_words(a)
    return terms


def _monic_gcd[F: _WordField](var a: List[UInt64], var b: List[UInt64], field: F, mut budget: Budget) raises PolyError -> List[UInt64]:
    if len(a) < len(b):
        swap(a, b)
    while len(b):
        budget.charge(1)
        _ = _reduce(a, b, field, budget)
        swap(a, b)
    if len(a):
        var inverse = field.inverse(a[len(a) - 1])
        for i in range(len(a)):
            a[i] = field.mul(a[i], inverse)
    return a^


def _resultant[F: _WordField](var a: List[UInt64], var b: List[UInt64], field: F, mut budget: Budget) raises PolyError -> UInt64:
    var result = field.one()
    var m = len(a) - 1
    var n = len(b) - 1
    if m < n:
        swap(a, b)
        swap(m, n)
        if (m & 1) and (n & 1):
            result = field.sub(0, result)
    # Pseudo-remainders leave a denominator, inverted once at the end.
    var denominator = field.one()
    while n > 0:
        budget.charge(1)
        var lc = b[n]
        var e = _reduce(a, b, field, budget)
        if not len(a):
            return 0
        var k = len(a) - 1
        # res(A, B) = (-1)^(mn) res(B, A), res(B, A) = lc(B)^(m - k) res(B, A mod B),
        # and the remainder came back as lc^e (A mod B), so
        # res(B, A mod B) = res(B, lc^e (A mod B)) / lc^(e n).
        result = field.mul(result, _power(field, lc, m - k))
        if e:
            denominator = field.mul(denominator, _power(field, lc, e * n))
        if (m & 1) and (n & 1):
            result = field.sub(0, result)
        swap(a, b)
        m = n
        n = k
    # b is a nonzero constant: res(A, c) = c^deg(A).
    result = field.mul(result, _power(field, b[0], m))
    return field.mul(result, field.inverse(denominator))


def _narrow(mut a: List[UInt64], small: _SmallField):
    """Montgomery forms a 2^64 to a 2^32, in place."""
    for i in range(len(a)):
        a[i] = small.reduce(a[i])


def _widen(value: UInt64, p: UInt64) -> UInt64:
    """The Montgomery form a 2^32 back to a 2^64."""
    return UInt64((UInt128(value) << 32) % UInt128(p))


def _gcd_words(var a: List[UInt64], var b: List[UInt64], field: _Field, mut budget: Budget) raises PolyError -> List[UInt64]:
    """The monic gcd of two Montgomery-form polynomials, in Montgomery form; zero for two zeros."""
    _trim_words(a)
    _trim_words(b)
    if field.p < _SMALL_PRIME:
        var small = _SmallField.of(field.p)
        _narrow(a, small)
        _narrow(b, small)
        var g = _monic_gcd(a^, b^, small, budget)
        for i in range(len(g)):
            g[i] = _widen(g[i], field.p)
        return g^
    return _monic_gcd(a^, b^, field, budget)


def _resultant_words(var a: List[UInt64], var b: List[UInt64], field: _Field, mut budget: Budget) raises PolyError -> UInt64:
    """The Sylvester resultant of two nonzero Montgomery-form polynomials, in Montgomery form."""
    _trim_words(a)
    _trim_words(b)
    if not len(a) or not len(b):
        return 0
    if field.p < _SMALL_PRIME:
        var small = _SmallField.of(field.p)
        _narrow(a, small)
        _narrow(b, small)
        return _widen(_resultant(a^, b^, small, budget), field.p)
    return _resultant(a^, b^, field, budget)
