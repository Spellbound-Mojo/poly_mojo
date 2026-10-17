"""Exact scalar comparisons and sign-variation checks, independent of producers."""
from apn_mojo import Integer, Rational, lcm as integer_lcm
from ._coefficient_ops import _copy
from .coefficients import QQ, NoContext, _work
from .dense import DensePoly
from .errors import Budget, PolyError, PolyErrorKind, _sum, _product
from .evaluate import _derivative_dense


def _compare(a: QQ, b: QQ, mut budget: Budget) raises PolyError -> Int:
    return a.sub(b, budget).value.sign()


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
