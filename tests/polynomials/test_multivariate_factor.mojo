"""Independently planted multivariate factors and lifting regressions."""
from apn_mojo import Rational, Integer
from polynomials import Budget, QQ, DensePoly, SparsePoly, MonomialOrder, factor, factor_multivariate, factor_multivariate_integer, check_multivariate_factorization, PolyErrorKind
from polynomials._multivariate_factor import _lift, _recombine_lifted
from polynomials._power_roots import _power_hint, _exact_hint
from support.check import Checker
from support.corpus import parse_polynomial, as_zz


def coordinate_factors(mut c: Checker, mut work: Budget) raises:
    for kind in [MonomialOrder.KERNEL, MonomialOrder.LEX, MonomialOrder.GRLEX, MonomialOrder.GREVLEX]:
        var order = MonomialOrder()
        if kind != MonomialOrder.KERNEL:
            order = MonomialOrder(kind, [Int64(7), Int64(2), Int64(11)], work)
        var x = parse_polynomial("x2", order, work)
        var y = parse_polynomial("x7", order, work)
        var g = parse_polynomial("x2*x7^3 + x2 + 1", order, work)
        var monomial = parse_polynomial("x2^3*x7^5", order, work)
        var f = monomial.mul(g.pow(2, work), work).scale(QQ(Rational(-6)), work)
        var rational = f.scale(QQ(Rational(1, 5)), work)
        var got = factor_multivariate(rational, work)
        var matched = 0
        for entry in got.factors:
            c.check(entry[0].order == order, "coordinate extraction preserves factor order")
            if (entry[0] == x and entry[1] == 3) or (entry[0] == y and entry[1] == 5) or (entry[0] == g and entry[1] == 2):
                matched += 1
        c.check(matched == 3 and len(got.factors) == 3 and got.unit.value == Rational(-6, 5), "rational coordinate and repeated residual multiplicities")
        c.check(check_multivariate_factorization(rational, got, work), "coordinate rational factors reconstruct")
        var integer = as_zz(f, work)
        var integral = factor_multivariate_integer(integer, work)
        matched = 0
        for entry in integral.factors:
            c.check(entry[0].order == order, "integer coordinate extraction preserves factor order")
            if (entry[0] == as_zz(x, work) and entry[1] == 3) or (entry[0] == as_zz(y, work) and entry[1] == 5) or (entry[0] == as_zz(g, work) and entry[1] == 2):
                matched += 1
        c.check(matched == 3 and len(integral.factors) == 3 and integral.unit.value == Integer(-6), "coordinate multiplicities survive the perfect-power shortcut")
        c.check(check_multivariate_factorization(integer, integral, work), "coordinate integer factors reconstruct")
    # Dividing by x2^3 reverses the KERNEL order of these terms. The
    # residual's last coefficient, rather than the input's, sets its unit.
    var kernel = MonomialOrder()
    var g = parse_polynomial("x2 + 2*x7", kernel, work)
    var f = parse_polynomial("x2^3", kernel, work).mul(g.pow(2, work), work).scale(QQ(Rational(-3, 5)), work)
    var got = factor_multivariate(f, work)
    var normalized = parse_polynomial("1/2*x2 + x7", kernel, work)
    c.check(got.unit.value == Rational(-12, 5) and len(got.factors) == 2 and got.factors[1][0] == normalized and got.factors[1][1] == 2, "KERNEL monomial division restores term order before normalization")
    c.check(check_multivariate_factorization(f, got, work), "KERNEL coordinate factor product reconstructs")


def main() raises:
    var work = Budget()
    var c = Checker("multivariate factorization")
    coordinate_factors(c, work)
    var order = MonomialOrder()
    var left = parse_polynomial("x0*x1 + 1", order, work)
    var right = parse_polynomial("x1^2 + x0 + 1", order, work)
    var content = parse_polynomial("x0 + 2", order, work)
    var f = left.pow(2, work).mul(right, work).mul(content.pow(3, work), work).scale(QQ(Rational(-6)), work)
    var result = factor_multivariate(f, work)
    c.check(check_multivariate_factorization(f, result, work), "nonmonic factors and content reconstruct")
    c.check(len(result.factors) == 3, "three planted irreducibles")
    var found_left = False
    var found_right = False
    var found_content = False
    for entry in result.factors:
        if entry[0] == left:
            found_left = entry[1] == 2
        if entry[0] == right:
            found_right = entry[1] == 1
        if entry[0] == content:
            found_content = entry[1] == 3
    c.check(found_left and found_right and found_content, "correct factors and multiplicities")
    var integer = as_zz(f, work)
    var integer_result = factor_multivariate_integer(integer, work)
    c.check(check_multivariate_factorization(integer, integer_result, work), "integer content and primitive factors")
    var bad = result.copy()
    bad.factors[0][1] += 1
    c.check(not check_multivariate_factorization(f, bad, work), "corrupted multiplicity rejected")
    for text in [String("x1^2 - x0"), String("x1^2 - x0*x2 - 1"), String("x1*x0 + x2")]:
        var irreducible = parse_polynomial(text, order, work)
        var factored = factor_multivariate(irreducible, work)
        c.check(len(factored.factors) == 1 and check_multivariate_factorization(irreducible, factored, work), "irreducible with bad or split first evaluation")
    var crossing = parse_polynomial("x1 - x0", order, work).mul(parse_polynomial("x1 + x0", order, work), work)
    var crossed = factor_multivariate(crossing, work)
    c.check(len(crossed.factors) == 2 and check_multivariate_factorization(crossing, crossed, work), "repeated first specialization is skipped")
    # At x0=0, both irreducible quadratic factors split into linear factors.
    # Lift and recombine at that exact point; selecting a different point
    # would not test recovery of split specialization factors.
    var split_left = parse_polynomial("x1^2 - x0 - 1", order, work)
    var split_right = parse_polynomial("x1^2 + x0 - 4", order, work)
    var split = split_left.mul(split_right, work)
    var specialized = DensePoly[QQ].from_sparse(parse_polynomial("x1^4 - 5*x1^2 + 4", order, work), work, variable=Int64(1))
    var univariate = factor(specialized, work)
    var initial = List[DensePoly[QQ]]()
    for entry in univariate.factors:
        initial.append(entry[0].copy())
    c.check(len(initial) == 4, "four independent specialized linear factors")
    var lifted = _lift(split, 1, initial, specialized, work)
    var combined = _recombine_lifted(split, 1, lifted, work)
    c.check(len(combined) == 2 and ((combined[0] == split_left and combined[1] == split_right) or (combined[1] == split_left and combined[0] == split_right)), "lifted split subsets recover the two irreducible quadratics")
    var public_split = factor_multivariate(split, work)
    c.check(len(public_split.factors) == 2 and check_multivariate_factorization(split, public_split, work), "evaluation heuristics preserve exact factorization")
    for text in [String("0"), String("-3/7")]:
        var constant = parse_polynomial(text, order, work)
        var constants = factor_multivariate(constant, work)
        c.check(len(constants.factors) == 0 and check_multivariate_factorization(constant, constants, work), "zero and constant factor products")
    # Squarefree parts proved by a prime image, and a repeated trivariate
    # factor that the image rejects, both with leading coefficients in x2.
    var a = parse_polynomial("x2*x0 + x1^2 - 3", order, work)
    var b = parse_polynomial("x2^2*x1 - x0 + 2", order, work)
    var d = parse_polynomial("x2 + x1 + x0", order, work)
    for power in range(1, 3):
        var g = a.mul(b, work).mul(d.pow(UInt64(power), work), work)
        var got = factor_multivariate(g, work)
        var multiplicity = 0
        for entry in got.factors:
            if entry[0] == d:
                multiplicity = entry[1]
        c.check(len(got.factors) == 3 and multiplicity == power and check_multivariate_factorization(g, got, work), "trivariate planted factors with squarefree image test")
    # Wang's leading-coefficient distribution: every factor has a nonconstant
    # leading coefficient in the main variable x3, sharing their factors.
    var wang_factors = List[SparsePoly[QQ]]()
    wang_factors.append(parse_polynomial("x1^2*x2*x3^2 + x3^2 + x1*x3 - x2", order, work))
    wang_factors.append(parse_polynomial("x1*x2*x3 - 2*x3 + x1^2 + 3", order, work))
    wang_factors.append(parse_polynomial("x3*x2^3 + x3*x1 + x0 + 1", order, work))
    wang_factors.append(parse_polynomial("x0*x1*x2*x3^2 + x1^2*x2*x3^2 - 2*x0*x3^2 - 2*x1*x3^2 - x0*x2 + 5", order, work))
    var wang_product = parse_polynomial("1", order, work)
    for g in wang_factors:
        wang_product = wang_product.mul(g, work)
    var wang_integer = as_zz(wang_product, work)
    var wang_result = factor_multivariate_integer(wang_integer, work)
    c.check(len(wang_result.factors) == 4 and check_multivariate_factorization(wang_integer, wang_result, work), "Wang lifting with shared nonconstant leading coefficients")
    var rational_result = factor_multivariate(wang_product, work)
    var matched = 0
    for g in wang_factors:
        var alone = factor_multivariate(g, work)
        for entry in rational_result.factors:
            if len(alone.factors) == 1 and entry[0] == alone.factors[0][0] and entry[1] == 1:
                matched += 1
    c.check(matched == 4, "Wang factors match the planted irreducibles")
    # Sparse factors in six variables: the later variables lift by sparse
    # interpolation of the corrections on the earlier factors' supports.
    var sparse_factors = List[SparsePoly[QQ]]()
    sparse_factors.append(parse_polynomial("x0^3*x1*x5 - 4*x2^2*x3*x0 + x4^2*x1^2 + 7*x5*x3 - 2", order, work))
    sparse_factors.append(parse_polynomial("x0^2*x2*x4 + 3*x1^3*x5^2 - x3*x4*x0 + x2*x5 + 5", order, work))
    sparse_factors.append(parse_polynomial("x0*x3^2 - x1*x2*x4 + 2*x5^3 - x0^2*x1 + 1", order, work))
    var sparse_product = parse_polynomial("1", order, work)
    for g in sparse_factors:
        sparse_product = sparse_product.mul(g, work)
    var sparse_integer = as_zz(sparse_product, work)
    var sparse_result = factor_multivariate_integer(sparse_integer, work)
    var sparse_matched = 0
    for g in sparse_factors:
        var planted = as_zz(g, work)
        for entry in sparse_result.factors:
            if (entry[0] == planted or entry[0] == planted.neg(work)) and entry[1] == 1:
                sparse_matched += 1
    c.check(len(sparse_result.factors) == 3 and sparse_matched == 3 and check_multivariate_factorization(sparse_integer, sparse_result, work), "sparse six-variable factors lift to the planted irreducibles")
    # Perfect powers factor through their root: even powers with negative
    # content, a nested power, a non-power and an odd negative power.
    var power_a = parse_polynomial("x0*x1 + 2", order, work)
    var power_b = parse_polynomial("x1^2 + x0*x2 + 3", order, work)
    var shapes: List[Tuple[Int, Int, Int]] = [(2, 2, -5), (2, 4, 6), (2, 3, 1), (3, 3, -1)]
    for shape in shapes:
        var g = power_a.pow(UInt64(shape[0]), work).mul(power_b.pow(UInt64(shape[1]), work), work).scale(QQ(Rational(shape[2])), work)
        var integer_power = as_zz(g, work)
        var got = factor_multivariate_integer(integer_power, work)
        var multiplicities = 0
        for entry in got.factors:
            if entry[0] == as_zz(power_a, work):
                multiplicities += entry[1] * 10
            if entry[0] == as_zz(power_b, work):
                multiplicities += entry[1]
        c.check(len(got.factors) == 2 and multiplicities == shape[0] * 10 + shape[1] and got.unit.value == Integer(shape[2]) and check_multivariate_factorization(integer_power, got, work), "perfect power shortcut keeps factors, multiplicities and unit")
    # The modular multiplicity hint agrees with the exact rational one when
    # f's degrees share a factor, and is one when they rule out every power
    # (the exact image hint of a^2 b^3 is 3, as a is constant in x2).
    var hint_agrees = True
    for shape in [(2, 2), (2, 4), (3, 3), (1, 1), (4, 2), (6, 4)]:
        var g = as_zz(power_a.pow(UInt64(shape[0]), work).mul(power_b.pow(UInt64(shape[1]), work), work), work)
        if _power_hint(g, 2, work) != _exact_hint(g, 2, work):
            hint_agrees = False
    var coprime_degrees = as_zz(power_a.pow(2, work).mul(power_b.pow(3, work), work), work)
    c.check(hint_agrees and _power_hint(coprime_degrees, 2, work) == 1 and _exact_hint(coprime_degrees, 2, work) == 3, "modular power hint matches the exact hint where a power can exist")
    # Degree one and two in the main variable: a square discriminant splits
    # a quadratic with a nonconstant leading coefficient; a non-square one
    # leaves it to the general path.
    var linear_left = parse_polynomial("x0*x2 + x1 - 4", order, work)
    var linear_right = parse_polynomial("x1*x2 - 3*x0^2 + 1", order, work)
    var quadratic = as_zz(linear_left.mul(linear_right, work), work)
    var split_quadratic = factor_multivariate_integer(quadratic, work)
    c.check(len(split_quadratic.factors) == 2 and check_multivariate_factorization(quadratic, split_quadratic, work), "square discriminant splits a quadratic in the main variable")
    for text in [String("x0*x2 + x1^2 + 1"), String("x2^2 - x0*x1 - 1")]:
        var single = as_zz(parse_polynomial(text, order, work), work)
        var got_single = factor_multivariate_integer(single, work)
        c.check(len(got_single.factors) == 1 and got_single.factors[0][1] == 1 and check_multivariate_factorization(single, got_single, work), "linear and non-square quadratic atoms stay irreducible")
    var tiny = Budget(1)
    var exhausted = False
    try:
        _ = factor_multivariate(f, tiny)
    except e:
        exhausted = e.kind == PolyErrorKind.LIMIT
    c.check(exhausted, "multivariate factorization budget is enforced")
    c.finish()
