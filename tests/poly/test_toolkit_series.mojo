"""Independent coefficient identities for the functional formal-series API."""
from poly import series, dense, coefficients, modint
from apn_mojo import Rational, ExactComplex
from polynomials import Budget, ModInt, QQ
from std.testing import assert_equal, assert_true


def main() raises:
    var a = series.asarray([1, -1], order=6)
    assert_equal(a.order(), 6)
    assert_equal(len(a), 6)
    assert_equal(a.domain(), "QQ")
    assert_equal(a[5], Rational(0))
    var inverse = series.reciprocal(a)
    assert_equal(series.coefficients(inverse).to_list(), [Rational(1), 1, 1, 1, 1, 1])
    var identity = series.multiply(a, inverse)
    assert_equal(identity[0], Rational(1))
    assert_equal(len(series.to_polynomial(identity)), 1)
    assert_equal(series.coefficients(series.divide([1], [1, -1], order=6)).to_list(), series.coefficients(inverse).to_list())
    assert_equal(series.add(a, [1])[0], Rational(2))
    assert_equal(series.subtract(a, a)[0], Rational(0))
    assert_equal(series.negative(a)[1], Rational(1))
    var x = series.asarray([0, 1], order=6)
    var exponential = series.exp(x)
    assert_equal(exponential[5], Rational(1, 120))
    var logarithm = series.log(series.asarray([1, 1], order=6))
    assert_equal(logarithm[4], Rational(-1, 4))
    assert_equal(series.coefficients(series.log(exponential)).to_list(), series.coefficients(x).to_list())
    var d = series.derivative(exponential)
    assert_equal(d.order(), 5)
    assert_equal(d[4], Rational(1, 24))
    var integral = series.integral(d)
    assert_equal(integral.order(), 6)
    assert_equal(integral[0], Rational(0))
    assert_equal(integral[5], Rational(1, 120))
    var f = series.asarray([0, 1, 1], order=6)
    var reversed = series.revert(f)
    assert_equal(series.coefficients(reversed).to_list(), [Rational(0), 1, -1, 2, -5, 14])
    assert_equal(series.coefficients(series.compose(f, reversed)).to_list(), series.coefficients(x).to_list())
    var root = series.sqrt(series.asarray([1, 1], order=5))
    assert_equal(series.coefficients(root).to_list(), [Rational(1), Rational(1, 2), Rational(-1, 8), Rational(1, 16), Rational(-5, 128)])
    assert_equal(series.coefficients(series.multiply(root, root)).to_list(), [Rational(1), 1, 0, 0, 0])
    assert_equal(series.coefficients(series.power([1, 1], 3, order=5)).to_list(), [Rational(1), 3, 3, 1, 0])
    assert_equal(series.coefficients(series.power([2, 1], 0, order=3)).to_list(), [Rational(1), 0, 0])
    var modular_root = series.sqrt(series.asarray(dense.asarray([1, 1], modulus=7), order=4))
    assert_equal(series.multiply(modular_root, modular_root)[1].value, UInt64(1))
    assert_equal(series.multiply(modular_root, modular_root)[3].value, UInt64(0))
    for scenario in range(3):
        var rejected = False
        try:
            if scenario == 0:
                _ = series.sqrt([2, 1], order=3)
            elif scenario == 1:
                _ = series.sqrt(series.asarray(dense.asarray([1, 1], modulus=2), order=3))
            else:
                _ = series.power([1, 1], -1, order=3)
        except:
            rejected = True
        assert_true(rejected)
    assert_equal(series.truncate(a, 3).order(), 3)
    assert_equal(series.add(a, series.truncate(a, 3), order=2).order(), 2)
    var total = Rational(0)
    for value in inverse:
        total += value
    assert_equal(total, Rational(6))
    var zero = series.asarray(List[Int](), order=4)
    assert_equal(len(zero), 4)
    assert_equal(len(series.to_polynomial(zero)), 0)
    var mixed = coefficients((1, Rational(1, 2), ExactComplex(0, 1)))
    var z = series.asarray(mixed, order=4)
    assert_equal(z.domain(), "QQi")
    assert_equal(series.multiply(z, [1])[2], ExactComplex(0, 1))
    var modular = series.asarray(dense.asarray([1, -1], modulus=7), order=5)
    assert_equal(series.reciprocal(modular)[4].value, UInt64(1))
    assert_equal(series.add([1], modular)[0].value, UInt64(2))
    assert_equal(series.multiply(modular, [2])[1].value, UInt64(5))
    var modular_zero = series.asarray(dense.asarray(List[Int](), modulus=7), order=0)
    assert_equal(modular_zero.modulus(), UInt64(7))
    var copied = series.asarray(a)
    assert_equal(copied.order(), 6)
    var raw = series.to_core(a)
    raw.polynomial.coefficients[0] = QQ(Rational(9))
    assert_equal(a[0], Rational(1))
    var imported = series.from_core(raw)
    assert_equal(imported[0], Rational(9))
    raw.polynomial.coefficients[0] = QQ(Rational(7))
    assert_equal(imported[0], Rational(9))
    var work = Budget()
    _ = series.coefficients(series.exp([0, 1], work, order=4), work)
    print("array toolkit series checks passed")
