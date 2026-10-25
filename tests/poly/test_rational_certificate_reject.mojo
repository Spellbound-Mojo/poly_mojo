"""Reject identities that conceal incomplete cancellation or reducible factors."""
from poly import rational, dense, algebraic
from poly._rational_certificates import _Irreducibility, _check_irreducible
from polynomials import QQ, QQi, NoContext, DensePoly, Budget, coprimality_certificate
from apn_mojo import Rational, ExactComplex
from std.testing import assert_false


def main() raises:
    var budget = Budget()
    var incomplete = rational.asarray([0, 1], [0, 1])
    var raw = rational.to_core(rational.asarray([0, 1], [1]))
    incomplete._data[].value.numerator = raw.numerator.copy()
    incomplete._data[].value.denominator = raw.numerator.copy()
    incomplete._data[].cancellation.cofactors = (raw.numerator.copy(), raw.numerator.copy())
    incomplete._data[].cancellation.common = raw.denominator.copy()
    # The retained cancellation equation still holds, but x/x is not reduced.
    assert_false(rational.check(incomplete))

    var nonmonic = rational.asarray([1], [0, 1])
    nonmonic._data[].value.numerator = nonmonic._data[].value.numerator.scale(QQ(Rational(2)), budget)
    nonmonic._data[].value.denominator = nonmonic._data[].value.denominator.scale(QQ(Rational(2)), budget)
    nonmonic._data[].cancellation.common = nonmonic._data[].cancellation.common.scale(QQ(Rational(1, 2)), budget)
    nonmonic._data[].cancellation.cofactors = (nonmonic._data[].value.numerator.copy(), nonmonic._data[].value.denominator.copy())
    var proof = coprimality_certificate(nonmonic._data[].value.numerator, nonmonic._data[].value.denominator, budget)
    nonmonic._data[].coprimality = proof.take()
    assert_false(rational.check(nonmonic))
    var wrong_node = rational.asarray([1], [0, 1])
    wrong_node._data[].coprimality.root = -1
    assert_false(rational.check(wrong_node))
    var cycle = rational.from_terms([((1, 0), 1)], [((0, 1), 1)])
    cycle._data[].coprimality.root = 0
    assert_false(rational.check(cycle))

    # Recomposition alone accepts 1/(x^4+4), but its factor is reducible:
    # x^4+4 = (x^2-2x+2)(x^2+2x+2). No rational root exposes this error.
    var parts = rational.partial_fractions(rational.asarray([1], [4, 0, 0, 0, 1]))
    var factor = dense.asarray([Rational(4), 0, 0, 0, 1])
    parts.terms._values[] = [(dense.asarray([Rational(1)]), factor.copy(), Int(1))]
    parts._factors[].value.factors = [(dense.to_core(factor), 1)]
    parts._factors[].certificates = [_Irreducibility(0, 0)]
    assert_false(rational.check(parts))

    var duplicate = rational.partial_fractions(rational.asarray([1], [1, 0, 1]))
    var half = dense.asarray([Rational(1, 2)])
    var q = dense.asarray([Rational(1), 0, 1])
    duplicate.terms._values[] = [(half.copy(), q.copy(), Int(1)), (half.copy(), q.copy(), Int(1))]
    assert_false(rational.check(duplicate))
    var zero = rational.partial_fractions(rational.asarray([1], [1, 0, 1]))
    zero.terms._values[].append((dense.asarray(List[Rational]()), q.copy(), 1))
    assert_false(rational.check(zero))
    var missing = rational.partial_fractions(rational.asarray([1], [0, 1, 1]))
    _ = missing.terms._values[].pop()
    assert_false(rational.check(missing))
    var multiplicity = rational.partial_fractions(rational.asarray([1], [0, 0, 1]))
    multiplicity._factors[].value.factors[0][1] = Int.MAX
    assert_false(rational.check(multiplicity))
    var extra = rational.partial_fractions(rational.asarray([1], [1]))
    extra._factors[].certificates.append(_Irreducibility(3, 0))
    assert_false(rational.check(extra))

    var prime = rational.partial_fractions(rational.asarray([1], [1, 0, 1]))
    prime._factors[].certificates[0].prime = 9
    assert_false(rational.check(prime))
    prime._factors[].certificates[0].prime = 2  # (x+1)^2 modulo 2
    assert_false(rational.check(prime))
    var absent = rational.partial_fractions(rational.asarray([1], [1, 0, 1]))
    _ = absent._factors[].certificates.pop()
    assert_false(rational.check(absent))
    var wrong_unit = rational.partial_fractions(rational.asarray([1], [1, 0, 1]))
    wrong_unit._factors[].value.unit = QQ(Rational(2))
    assert_false(rational.check(wrong_unit))
    var shift = rational.partial_fractions(rational.asarray([ExactComplex(1)], [ExactComplex(-2), ExactComplex(0), ExactComplex(1)]))
    shift._factors[].certificates[0].shift = -1
    assert_false(rational.check(shift))
    shift._factors[].certificates[0].shift = 0  # the norm is a square
    assert_false(rational.check(shift))

    # Degree loss modulo a prime cannot prove the original irreducible.
    var degree_loss = DensePoly[QQ].from_coefficients(0, NoContext(), [QQ(Rational(1)), QQ(Rational(3))], budget)
    assert_false(_check_irreducible(degree_loss, _Irreducibility(3, 0), budget))
    var reducible = DensePoly[QQ].from_coefficients(0, NoContext(), [QQ(Rational(-1)), QQ(Rational(0)), QQ(Rational(9))], budget)
    assert_false(_check_irreducible(reducible, _Irreducibility(3, 0), budget))
    assert_false(_check_irreducible(reducible, _Irreducibility(0, 0), budget))
    var gaussian_reducible = DensePoly[QQi].from_coefficients(0, NoContext(), [QQi(ExactComplex(1)), QQi(ExactComplex(0)), QQi(ExactComplex(1))], budget)
    assert_false(_check_irreducible(gaussian_reducible, _Irreducibility(0, 1), budget))

    # AA rejects positive-discriminant quadratics; QQbar rejects any quadratic.
    var aa = rational.partial_fractions(rational.asarray([algebraic.asreal(1)], [-2, 0, 1]))
    var aq = dense.asarray([algebraic.asreal(-2), algebraic.asreal(0), algebraic.asreal(1)])
    aa._factors[].value.factors = [(dense.to_core(aq), 1)]
    assert_false(rational.check(aa))
    var cc = rational.partial_fractions(rational.asarray([algebraic.ascomplex(1)], [1, 0, 1]))
    var cq = dense.asarray([algebraic.ascomplex(1), algebraic.ascomplex(0), algebraic.ascomplex(1)])
    cc._factors[].value.factors = [(dense.to_core(cq), 1)]
    assert_false(rational.check(cc))
    var local = rational.laurent(rational.asarray([1], [0, 1]), 0, terms=1)
    local._source._data[].coprimality.root = -1
    assert_false(rational.check(local))
    print("array rational certificate rejection checks passed")
