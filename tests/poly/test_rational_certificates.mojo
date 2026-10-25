"""Complete normalization and partial fractions over all four exact fields."""
from poly import rational, dense, algebraic, coefficients
from apn_mojo import Rational, ExactComplex
from polynomials import Budget, check_coprimality
from std.testing import assert_equal, assert_true


def main() raises:
    var f = rational.asarray([-2, 0, 2], [-2, 2])
    assert_true(rational.check(f))
    assert_equal(rational.numerator(f).to_list(), [(0, Rational(1)), (1, Rational(1))])
    assert_equal(rational.denominator(f).to_list(), [(0, Rational(1))])
    var budget = Budget()
    var raw = rational.to_core(f)
    assert_true(check_coprimality(raw.numerator, raw.denominator, f.coprimality_evidence(), budget))
    assert_true(rational.check(rational.asarray([0], [2, 2])))
    assert_true(rational.check(rational.partial_fractions(rational.asarray([2, 3], [1]))))
    assert_true(rational.check(rational.partial_fractions(rational.asarray([0], [1]))))

    # x and y are coprime although no polynomial Bezout identity equals one.
    var xy = rational.from_terms([((1, 0), 1)], [((0, 1), 1)])
    assert_true(rational.check(xy))
    assert_true(Bool(xy.coprimality_evidence().modular))
    var cancelled = rational.from_terms([((2, 1), 2)], [((1, 2), 4)])
    assert_true(rational.check(cancelled))
    assert_equal(rational.numerator(cancelled).to_list(), [((1, 0), Rational(1, 2))])
    assert_equal(rational.denominator(cancelled).to_list(), [((0, 1), Rational(1))])

    # x^4+1 is irreducible over QQ but reducible modulo every prime.
    var quartic = rational.partial_fractions(rational.asarray([1], [1, 0, 0, 0, 1]))
    assert_equal(len(quartic.terms), 1)
    assert_equal(quartic._factors[].certificates[0].prime, UInt64(0))
    assert_true(rational.check(quartic))
    var cubic = rational.partial_fractions(rational.asarray([1], [-2, 0, 0, 1]))
    assert_true(cubic._factors[].certificates[0].prime > 0)
    assert_true(rational.check(cubic))
    var fractional = rational.partial_fractions(rational.asarray([1], [Rational(-1, 2), 0, 1]))
    assert_true(rational.check(fractional))
    assert_equal(fractional.terms[0][0].to_list(), [Rational(1)])
    var repeated = rational.partial_fractions(rational.asarray([1, 1], [0, 0, 1]))
    assert_equal(len(repeated.terms), 2)
    assert_true(rational.check(repeated))
    assert_equal(repeated.terms[0][2], 2)
    assert_equal(repeated.terms[1][2], 1)
    assert_true(rational.check(rational.laurent(repeated._source, 0, terms=3)))

    # x^2-2 remains irreducible over QQi. Its squarefree shifted norm needs
    # the same complete QQ fallback; real coefficients alone do not imply QQ.
    var gaussian = rational.partial_fractions(rational.asarray([ExactComplex(1)], [ExactComplex(-2), ExactComplex(0), ExactComplex(1)]))
    assert_equal(len(gaussian.terms), 1)
    assert_true(gaussian._factors[].certificates[0].shift > 0)
    assert_true(rational.check(gaussian))
    var imaginary = rational.partial_fractions(rational.asarray([ExactComplex(1)], [ExactComplex(0, 1), ExactComplex(0), ExactComplex(1)]))
    assert_true(rational.check(imaginary))
    var split = rational.partial_fractions(rational.asarray([ExactComplex(1)], [ExactComplex(1), ExactComplex(0), ExactComplex(1)]))
    assert_equal(len(split.terms), 2)
    assert_true(rational.check(split))

    var a = dense.root_between([-2, 0, 1], 1, 2)
    var real = rational.asarray(coefficients((a.copy(), 1)), coefficients((algebraic.negative(a), 1)))
    assert_true(rational.check(real))
    assert_true(rational.check(rational.partial_fractions(real)))
    var real_quadratic = rational.partial_fractions(rational.asarray([algebraic.asreal(1)], [1, 0, 1]))
    assert_equal(len(real_quadratic.terms), 1)
    assert_true(rational.check(real_quadratic))
    var complex = rational.asarray(coefficients((a.copy(), ExactComplex(0, 1))), coefficients((a.copy(), ExactComplex(0, 1))))
    assert_true(rational.check(complex))
    assert_equal(complex.domain(), "QQbar")
    var complex_parts = rational.partial_fractions(rational.asarray([algebraic.ascomplex(1)], [1, 0, 1]))
    assert_equal(len(complex_parts.terms), 2)
    assert_true(rational.check(complex_parts))

    # An active axis can sit between unused axes; certificates keep its ID.
    var axis = rational.from_terms([((0, 0, 0), 1)], [((0, 0, 0), 1), ((0, 2, 0), 1)])
    assert_true(rational.check(rational.partial_fractions(axis, axis=1)))
    print("array rational certificate checks passed")
