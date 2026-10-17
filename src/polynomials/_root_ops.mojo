"""Exact scalar comparisons and sign-variation checks, independent of producers."""
from apn_mojo import Integer, lcm as integer_lcm
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


def _homogeneous_sign(p: DensePoly[QQ], x: QQ) raises -> Int:
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
    return result.sign()


def _sign_at(p: DensePoly[QQ], x: QQ, mut budget: Budget) raises PolyError -> Int:
    """The exact sign of p(x), without rational normalization.

    For x = a/b with b > 0 and L the positive common denominator of the
    coefficients, L b^n p(a/b) is an integer of the same sign; homogeneous
    Horner computes it with integer products and sums only. The charge is
    a size bound fixed before the evaluation.
    """
    var n = len(p.coefficients)
    if n == 0:
        return 0
    var coefficient_bytes = 0
    for i in range(n):
        budget.charge(1)
        coefficient_bytes = _sum(coefficient_bytes, p.coefficients[i].size())
    var x_bytes = x.size()
    for i in range(n - 1):
        budget.charge(1)
        _work(_sum(coefficient_bytes, _product(i, x_bytes)), x_bytes, True, budget)
    try:
        return _homogeneous_sign(p, x)
    except e:
        raise PolyError(PolyErrorKind.CAPACITY, String(e))


def _variations(polynomials: List[DensePoly[QQ]], a: QQ, mut budget: Budget, side: Int = 0) raises PolyError -> Int:
    var previous = 0
    var count = 0
    for p in polynomials:
        budget.charge(1)
        var sign = _sign_at(p, a, budget)
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
        if sign != 0:
            if previous != 0 and previous != sign:
                count += 1
            previous = sign
    return count
