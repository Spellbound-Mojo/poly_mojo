"""Dense univariate Euclid kernels (gcd, resultant) over word-size prime fields.

Coefficients are UInt64 lists in increasing degree, held in Montgomery form
(a·2^64 mod p) by the kernels below. Every prime the library admits is below
2^62, so Montgomery reduction of a product of two residues never overflows
128 bits. The prime 2 has no Montgomery form; callers use the generic path.
"""
from .errors import Budget, PolyError, PolyErrorKind, _allocation, _charge_size


@fieldwise_init
struct _Field(ImplicitlyCopyable, Movable):
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

    def inverse(self, a: UInt64) raises PolyError -> UInt64:
        """The Montgomery form of 1/a for a nonzero Montgomery residue a."""
        var value = Int64(self.leave(a))
        var modulus = Int64(self.p)
        var t = Int64(0)
        var next_t = Int64(1)
        var r = modulus
        var next_r = value
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
        return self.enter(UInt64(t))

    def power(self, a: UInt64, n: Int) -> UInt64:
        var result = self.enter(1)
        var base = a
        var e = n
        while e > 0:
            if e & 1:
                result = self.mul(result, base)
            e >>= 1
            if e:
                base = self.mul(base, base)
        return result


def _trim_words(mut a: List[UInt64]):
    while len(a) and a[len(a) - 1] == 0:
        _ = a.pop()


def _enter_words(values: List[UInt64], field: _Field, mut budget: Budget) raises PolyError -> List[UInt64]:
    _allocation[UInt64](len(values), budget)
    var out = List[UInt64](capacity=len(values))
    for v in values:
        out.append(field.enter(v))
    _trim_words(out)
    return out^


def _leave_words(values: List[UInt64], field: _Field, mut budget: Budget) raises PolyError -> List[UInt64]:
    _allocation[UInt64](len(values), budget)
    var out = List[UInt64](capacity=len(values))
    for v in values:
        out.append(field.leave(v))
    return out^


def _scale_words(mut a: List[UInt64], c: UInt64, field: _Field):
    for i in range(len(a)):
        a[i] = field.mul(a[i], c)


def _reduce(mut a: List[UInt64], b: List[UInt64], inverse: UInt64, field: _Field, mut budget: Budget) raises PolyError:
    """Replace a by a mod b, trimmed, for b of positive length and inverse the Montgomery form of 1/lc(b).

    Quotient terms are taken two at a time: subtracting (q1 x + q0) x^j b
    combines both products of each coefficient into one 128-bit sum below
    2p^2 < p 2^64, so one Montgomery reduction serves both.
    """
    var db = len(b) - 1
    if len(a) <= db:
        return
    _charge_size((len(a) - db) * len(b), budget)
    if db == 0:
        a.clear()
        return
    var p = field.p
    var k = len(a) - 1
    while k > db:
        var q1 = field.mul(a[k], inverse)
        var q0 = field.mul(field.sub(a[k - 1], field.mul(q1, b[db - 1])), inverse)
        var n1 = UInt128(p - q1 if q1 else 0)
        var n0 = UInt128(p - q0 if q0 else 0)
        var base = k - 1 - db
        a[base] = field.add(a[base], field.reduce(n0 * UInt128(b[0])))
        for i in range(1, db):
            a[base + i] = field.add(a[base + i], field.reduce(n1 * UInt128(b[i - 1]) + n0 * UInt128(b[i])))
        k -= 2
    if k == db:
        var q = field.mul(a[k], inverse)
        if q:
            var n = UInt128(p - q)
            for i in range(db):
                a[i] = field.add(a[i], field.reduce(n * UInt128(b[i])))
    a.resize(db, 0)
    _trim_words(a)


def _make_monic(mut a: List[UInt64], field: _Field) raises PolyError -> UInt64:
    """Scale a to leading coefficient one and return the leading coefficient it had."""
    var lc = a[len(a) - 1]
    if lc != field.enter(1):
        _scale_words(a, field.inverse(lc), field)
    return lc


def _gcd_words(var a: List[UInt64], var b: List[UInt64], field: _Field, mut budget: Budget) raises PolyError -> List[UInt64]:
    """The monic gcd of two Montgomery-form polynomials, in Montgomery form; zero for two zeros."""
    _trim_words(a)
    _trim_words(b)
    if len(a) < len(b):
        swap(a, b)
    while len(b):
        budget.charge(1)
        _reduce(a, b, field.inverse(b[len(b) - 1]), field, budget)
        swap(a, b)
    if len(a):
        _ = _make_monic(a, field)
    return a^


def _resultant_words(var a: List[UInt64], var b: List[UInt64], field: _Field, mut budget: Budget) raises PolyError -> UInt64:
    """The Sylvester resultant of two nonzero Montgomery-form polynomials, in Montgomery form."""
    _trim_words(a)
    _trim_words(b)
    if not len(a) or not len(b):
        return 0
    var result = field.enter(1)
    var m = len(a) - 1
    var n = len(b) - 1
    if m < n:
        swap(a, b)
        swap(m, n)
        if (m & 1) and (n & 1):
            result = field.sub(0, result)
    while n > 0:
        budget.charge(1)
        var lc = b[n]
        _reduce(a, b, field.inverse(lc), field, budget)
        if not len(a):
            return 0
        var k = len(a) - 1
        # res(A, B) = (-1)^(mn) res(B, A) and res(B, A) = lc(B)^(m - k) res(B, A mod B).
        result = field.mul(result, field.power(lc, m - k))
        if (m & 1) and (n & 1):
            result = field.sub(0, result)
        swap(a, b)
        m = n
        n = k
    # b is a nonzero constant: res(A, c) = c^deg(A).
    return field.mul(result, field.power(b[0], m))
