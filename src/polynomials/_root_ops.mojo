"""Exact scalar comparisons and sign-variation checks, independent of producers."""
from apn_mojo import Rational
from ._coefficient_ops import _copy
from .coefficients import QQ, NoContext
from .dense import DensePoly
from .errors import Budget, PolyError, PolyErrorKind
from .evaluate import evaluate_dense, _derivative_dense


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
    return (a.numerator() * db - b.numerator() * da).sign()


def _midpoint(a: QQ, b: QQ, mut budget: Budget) raises PolyError -> QQ:
    var two = QQ.one(NoContext()).add(QQ.one(NoContext()), budget)
    return a.add(b, budget).mul(two.inverse(budget), budget)


def _variations(polynomials: List[DensePoly[QQ]], a: QQ, mut budget: Budget, side: Int = 0) raises PolyError -> Int:
    var previous = 0
    var count = 0
    for p in polynomials:
        budget.charge(1)
        var sign = _one_sided(p, evaluate_dense(p, a, budget).value.sign(), a, side, budget)
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
            current = evaluate_dense(polynomials[i], a, budget)
        else:
            var following = evaluate_dense(quotients[i - 2], a, budget).mul(current, budget).sub(before, budget)
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
            sign = evaluate_dense(derivative, a, budget).value.sign()
            if sign != 0:
                if side < 0 and parity:
                    sign = -sign
                break
            derivative = _derivative_dense(derivative, budget)
            parity = 1 - parity
    return sign
