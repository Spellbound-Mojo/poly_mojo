"""Independently planted multivariate factors and lifting regressions."""
from apn_mojo import Rational
from polynomials import Budget, QQ, DensePoly, SparsePoly, MonomialOrder, factor, factor_multivariate, factor_multivariate_integer, check_multivariate_factorization, PolyErrorKind
from polynomials._multivariate_factor import _lift, _recombine_lifted
from support.check import Checker
from support.corpus import parse_polynomial, as_zz


def main() raises:
    var work = Budget()
    var c = Checker("multivariate factorization")
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
    var tiny = Budget(1)
    var exhausted = False
    try:
        _ = factor_multivariate(f, tiny)
    except e:
        exhausted = e.kind == PolyErrorKind.LIMIT
    c.check(exhausted, "multivariate factorization budget is enforced")
    c.finish()
