"""Exact scalar comparisons and sign-variation checks, independent of producers."""
from std.bit import count_trailing_zeros
from apn_mojo import Integer, Rational, lcm as integer_lcm
from ._coefficient_ops import _copy
from .coefficients import QQ, NoContext, _work
from .dense import DensePoly
from .errors import Budget, PolyError, PolyErrorKind, _sum, _product
from .evaluate import _derivative_dense


def _compare(a: QQ, b: QQ, mut budget: Budget) raises PolyError -> Int:
    # Exact ordering without forming the normalized difference.
    budget.charge(1)
    try:
        return _order(a.value, b.value)
    except e:
        raise PolyError(PolyErrorKind.CAPACITY, String(e))


def _order(a: Rational, b: Rational) raises -> Int:
    # sign(a - b) by cross-multiplication: two products, no gcd, and no
    # continued-fraction expansion of nearly equal operands.
    var sa = a.sign()
    var sb = b.sign()
    if sa != sb:
        return -1 if sa < sb else 1
    var da = a.denominator()
    var db = b.denominator()
    if da == db:
        var difference = a.numerator() - b.numerator()
        return difference.sign()
    var ea = _power_of_two(da)
    var eb = _power_of_two(db)
    if ea >= 0 and eb >= 0:
        # Dyadic operands compare after one shift instead of two products.
        if ea < eb:
            return ((a.numerator() << (eb - ea)) - b.numerator()).sign()
        return (a.numerator() - (b.numerator() << (ea - eb))).sign()
    return (a.numerator() * db - b.numerator() * da).sign()


def _twos(x: Integer) -> Int:
    """The number of trailing zero bits of a nonzero magnitude, from its words."""
    for i in range(x._word_count()):
        var word = x._word(i)
        if word != 0:
            return 32 * i + Int(count_trailing_zeros(word))
    return 0


def _power_of_two(x: Integer) -> Int:
    """k when |x| = 2^k, else -1."""
    var bits = x.magnitude_bit_length()
    if bits == 0:
        return -1
    var k = _twos(x)
    return k if k == bits - 1 else -1


def _midpoint(a: QQ, b: QQ, mut budget: Budget) raises PolyError -> QQ:
    var two = QQ.one(NoContext()).add(QQ.one(NoContext()), budget)
    return a.add(b, budget).mul(two.inverse(budget), budget)


def _homogeneous(p: DensePoly[QQ], x: QQ) raises -> Tuple[Integer, Integer]:
    # For x = a/b with b > 0 and the positive common denominator L of the
    # coefficients, returns (L b^n p(a/b), L b^n) as integers.
    var n = len(p.coefficients)
    var common = Integer(1)
    for i in range(n):
        ref value = p.coefficients[i].value
        if value.denominator() != 1:
            common = integer_lcm(common, value.denominator())
    var a = x.value.numerator()
    var b = x.value.denominator()
    var unit = b == 1
    var power = Integer(1)
    ref top = p.coefficients[n - 1].value
    var result = top.numerator() * (common // top.denominator())
    for i in range(n - 2, -1, -1):
        ref value = p.coefficients[i].value
        var term = value.numerator()
        if value.denominator() != common:
            term = term * (common // value.denominator())
        if not unit:
            power = power * b
            term = term * power
        result = result * a + term
    return (result^, common * power)


def _charge_evaluation(p: DensePoly[QQ], x: QQ, mut budget: Budget) raises PolyError:
    var n = len(p.coefficients)
    var coefficient_bytes = 0
    for i in range(n):
        budget.charge(1)
        coefficient_bytes = _sum(coefficient_bytes, p.coefficients[i].size())
    var x_bytes = x.size()
    for i in range(n - 1):
        budget.charge(1)
        _work(_sum(coefficient_bytes, _product(i, x_bytes)), x_bytes, True, budget)


def _value_at(p: DensePoly[QQ], x: QQ, mut budget: Budget) raises PolyError -> QQ:
    """The exact value p(x), normalized once instead of at every Horner step."""
    if len(p.coefficients) == 0:
        return QQ.zero(NoContext())
    _charge_evaluation(p, x, budget)
    try:
        var parts = _homogeneous(p, x)
        _work(parts[0].magnitude_bit_length() // 8 + 1, parts[1].magnitude_bit_length() // 8 + 1, True, budget)
        return QQ(Rational(parts[0], parts[1]))
    except e:
        raise PolyError(PolyErrorKind.CAPACITY, String(e))


def _sign_at(p: DensePoly[QQ], x: QQ, mut budget: Budget) raises PolyError -> Int:
    """The exact sign of p(x), without rational normalization.

    For x = a/b with b > 0 and L the positive common denominator of the
    coefficients, L b^n p(a/b) is an integer of the same sign; homogeneous
    Horner computes it with integer products and sums only. The charge is
    a size bound fixed before the evaluation.
    """
    if len(p.coefficients) == 0:
        return 0
    _charge_evaluation(p, x, budget)
    try:
        return _homogeneous(p, x)[0].sign()
    except e:
        raise PolyError(PolyErrorKind.CAPACITY, String(e))


def _variations(polynomials: List[DensePoly[QQ]], a: QQ, mut budget: Budget, side: Int = 0) raises PolyError -> Int:
    var previous = 0
    var count = 0
    for p in polynomials:
        budget.charge(1)
        var sign = _one_sided(p, _sign_at(p, a, budget), a, side, budget)
        if sign != 0:
            if previous != 0 and previous != sign:
                count += 1
            previous = sign
    return count


def _chain_variations(polynomials: List[DensePoly[QQ]], quotients: List[DensePoly[QQ]], a: QQ, mut budget: Budget, side: Int = 0) raises PolyError -> Int:
    # Equal to _variations for a chain whose recurrences
    # polynomials[i - 1] == quotients[i - 1] * polynomials[i] - polynomials[i + 1]
    # hold: callers either built the chain or have verified it. Two Horner
    # evaluations and one short quotient per entry give the same exact values.
    var n = len(polynomials)
    if n < 3 or len(quotients) + 1 < n:
        return _variations(polynomials, a, budget, side)
    var previous = 0
    var count = 0
    var before = QQ.zero(NoContext())
    var current = QQ.zero(NoContext())
    for i in range(n):
        budget.charge(1)
        if i < 2:
            before = current^
            current = _value_at(polynomials[i], a, budget)
        else:
            var following = _value_at(quotients[i - 2], a, budget).mul(current, budget).sub(before, budget)
            before = current^
            current = following^
        var sign = _one_sided(polynomials[i], current.value.sign(), a, side, budget)
        if sign != 0:
            if previous != 0 and previous != sign:
                count += 1
            previous = sign
    return count


def _one_sided(p: DensePoly[QQ], value_sign: Int, a: QQ, side: Int, mut budget: Budget) raises PolyError -> Int:
    var sign = value_sign
    if sign == 0 and side != 0 and not p.is_zero():
        # At an endpoint root, the first nonzero Taylor coefficient
        # gives the exact one-sided sign, including repeated roots.
        var derivative = _derivative_dense(p, budget)
        var parity = 1
        while True:
            budget.charge(1)
            sign = _sign_at(derivative, a, budget)
            if sign != 0:
                if side < 0 and parity:
                    sign = -sign
                break
            derivative = _derivative_dense(derivative, budget)
            parity = 1 - parity
    return sign


# Certified signs of integer polynomials at rationals, by fixed-point Horner
# with a proved error bound and an exact fallback (used by _real_refine and
# by short Sturm chains).

def _bits(x: Integer) -> Int:
    return x.magnitude_bit_length()


def _power_shift(q: Integer) raises -> Int:
    return _power_of_two(q)


def _error_bits(n: Int, p: Integer, q: Integer) -> Int:
    # Floor rounding in each of the n Horner steps errs by less than one unit,
    # and later steps scale it by |x|, so the total is below
    # sum_{j<n} |x|^j <= n max(1, |x|)^(n-1) units.
    var lx = max(0, _bits(p) - _bits(q) + 1)
    var log_n = 0
    while (1 << log_n) < n:
        log_n += 1
    return log_n + (n - 1) * lx + 1


def _fixed(c: List[Integer], p: Integer, q: Integer, shift: Int, scale: Int) raises -> Integer:
    # 2^scale * c(p/q) within the error of _error_bits, by floor-rounded Horner.
    var n = len(c) - 1
    var t = c[n] << scale
    for i in range(n - 1, -1, -1):
        var product = t * p
        if shift >= 0:
            t = product >> shift
        else:
            t = product // q
        t = t + (c[i] << scale)
    return t^


def _exact_sign(c: List[Integer], p: Integer, q: Integer) raises -> Int:
    # sign(q^n c(p/q)) by homogeneous Horner; q is positive.
    var n = len(c) - 1
    var t = c[n].copy()
    var power = Integer(1)
    for i in range(n - 1, -1, -1):
        power = power * q
        t = t * p + c[i] * power
    return t.sign()


def _sign(c: List[Integer], x: Rational) raises -> Int:
    var n = len(c) - 1
    if n <= 0:
        return c[0].sign() if n == 0 else 0
    var p = x.numerator()
    var q = x.denominator()
    if not p:
        return c[0].sign()
    var shift = _power_shift(q)
    var error = _error_bits(n, p, q)
    var exact_bits = n * (_bits(p) + _bits(q))
    # Near a root, |c(x)| is about |c'| times the grid step of x, so start
    # with as many guard bits as x has fractional bits.
    var extra = 64 + _bits(q)
    while error + extra < exact_bits:
        var t = _fixed(c, p, q, shift, error + extra)
        if t and _bits(t) - 1 > error + 1:
            return t.sign()
        extra *= 4
    return _exact_sign(c, p, q)
