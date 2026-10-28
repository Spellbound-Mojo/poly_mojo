"""Factor reconstruction, multiplicities, domains, and unsupported boundaries."""
import poly
from apn_mojo import Integer, Rational, ExactComplex
from polynomials import PolyErrorKind
from std.testing import assert_equal, assert_true


def coordinate_factors() raises:
    var x = poly.sparse.asarray([((1, 0), 1)])
    var g = poly.sparse.asarray([((1, 0), 1), ((0, 1), 2)])
    var f = poly.sparse.multiply(poly.sparse.multiply(poly.sparse.power(x, 3), poly.sparse.power(g, 2)), -3)
    var before = f.to_list()
    var ordinary = poly.sparse.factor(f)
    var checked = poly.sparse.factor_checked(f)
    var factors = poly.exact.factors(checked)
    assert_true(poly.exact.check(checked))
    assert_equal(ordinary[0], Integer(-3))
    assert_equal(poly.exact.unit(checked), ordinary[0])
    assert_equal(len(factors), 2)
    assert_equal(factors[0][0].to_list(), x.to_list())
    assert_equal(factors[0][1], 3)
    assert_equal(factors[1][0].to_list(), g.to_list())
    assert_equal(factors[1][1], 2)
    for i in range(len(factors)):
        assert_equal(ordinary[1][i][0].to_list(), factors[i][0].to_list())
        assert_equal(ordinary[1][i][1], factors[i][1])
    # The array API normalizes the residual in its lexicographic order.
    var rational = poly.sparse.multiply(f, Rational(1, 5))
    var rational_result = poly.sparse.factor_checked(rational)
    assert_true(poly.exact.check(rational_result))
    assert_equal(poly.exact.unit(rational_result), Rational(-3, 5))
    var rational_factors = poly.exact.factors(rational_result)
    var normalized = poly.sparse.asarray([((1, 0), Rational(1)), ((0, 1), Rational(2))])
    assert_equal(rational_factors[1][0].to_list(), normalized.to_list())
    assert_equal(rational_factors[1][1], 2)
    # Coordinate multiplicities need no dense image or repeated trial division.
    var maximum = Int(UInt32.MAX)
    var monomial = poly.sparse.asarray([((maximum, 4000000000), -7)])
    var large = poly.sparse.factor_checked(monomial, max_steps=100000)
    assert_true(poly.exact.check(large, max_steps=100000))
    assert_equal(poly.exact.unit(large), Integer(-7))
    var powers = poly.exact.factors(large)
    assert_equal(len(powers), 2)
    var y = poly.sparse.asarray([((0, 1), 1)])
    assert_equal(powers[0][0].to_list(), y.to_list())
    assert_equal(powers[0][1], 4000000000)
    assert_equal(powers[1][0].to_list(), x.to_list())
    assert_equal(powers[1][1], maximum)
    for steps in [UInt64(0), UInt64(100)]:
        var exhausted = False
        try:
            _ = poly.sparse.factor_checked(f, max_steps=steps)
        except e:
            exhausted = e.kind == PolyErrorKind.LIMIT
        assert_true(exhausted)
    assert_equal(f.to_list(), before)


def main() raises:
    coordinate_factors()
    var p = poly.dense.multiply(poly.dense.power([-1, 1], 2), [2, 0, 2])
    var result = poly.dense.factor(p)
    assert_equal(result[0], Integer(2))
    assert_equal(len(result[1]), 2)
    var restored = poly.dense.asarray([result[0].copy()])
    for entry in result[1]:
        restored = poly.dense.multiply(restored, poly.dense.power(entry[0], entry[1]))
    assert_equal(restored.to_list(), p.to_list())
    var blocks = poly.dense.squarefree(p)
    var rational = poly.dense.asarray([blocks[0].copy()])
    for entry in blocks[1]:
        rational = poly.dense.multiply(rational, poly.dense.power(entry[0], entry[1]))
    assert_equal(rational.to_list(), poly.coefficients((Rational(2), -4, 4, -4, 2)).to_list())
    var rational_factors = poly.dense.factor(rational)
    assert_equal(rational_factors[0], Rational(2))
    var finite = poly.dense.asarray([-2, 0, 2], modulus=5)
    var ff = poly.dense.factor(finite)
    assert_equal(ff[0].value, UInt64(2))
    assert_equal(len(ff[1]), 2)
    var rebuilt = poly.dense.asarray([ff[0].copy()])
    for entry in ff[1]:
        rebuilt = poly.dense.multiply(rebuilt, poly.dense.power(entry[0], entry[1]))
    assert_equal(rebuilt.to_list(), finite.to_list())
    var f = poly.sparse.asarray([((1, 0), 1), ((0, 1), 1)])
    var g = poly.sparse.asarray([((1, 0), 1), ((0, 0), -1)])
    var product = poly.sparse.multiply(poly.sparse.power(f, 2), g)
    var sf = poly.sparse.factor(product)
    assert_equal(sf[0], Integer(1))
    assert_equal(len(sf[1]), 2)
    var recovered = poly.sparse.asarray([((0, 0), sf[0].copy())])
    for entry in sf[1]:
        recovered = poly.sparse.multiply(recovered, poly.sparse.power(entry[0], entry[1]))
    assert_equal(recovered.to_list(), product.to_list())
    var univariate = poly.sparse.asarray([(0, 1), (1, -2), (2, 1)])
    var sq = poly.sparse.squarefree(univariate)
    assert_equal(sq[1][0][1], 2)
    var eg = poly.sparse.extended_gcd(univariate, [(0, -1), (1, 1)])
    assert_equal(poly.sparse.degree(eg[0]), 1)
    var pd = poly.sparse.pseudo_divmod([(0, 1), (2, 1)], [(0, 1), (1, 2)])
    assert_equal(pd[0], Integer(4))
    assert_equal(poly.sparse.compose([(2, 1)], [(0, 1), (1, 1)]).to_list(), poly.sparse.asarray([(0, 1), (1, 2), (2, 1)]).to_list())
    var repeated = poly.dense.factor(poly.dense.asarray([1, -2, 1], modulus=5))
    assert_equal(repeated[1][0][1], 2)
    var complex_p = poly.coefficients((1, ExactComplex(0, 1)))
    var complex_result = poly.dense.factor(complex_p)
    assert_equal(len(complex_result[1]), 1)
    assert_equal(complex_result[0], ExactComplex(0, 1))
    print("array factorization checks passed")
