"""Resultants and all principal subresultant coefficients from the corpus."""
from polynomials import Budget, CoefficientRing, ZZ, QQ, NoContext, SparsePoly, MonomialOrder
from polynomials.resultant import resultant, subresultants, resultant_value
from polynomials import ModInt, Modulus, prime
from support.gen import polynomial
from support.check import Checker
from support.corpus import read_cases, parse_order, parse_polynomial
from polynomials.certificates import _equal
from polynomials._tower import _split
from polynomials._coefficient_ops import _exact
from support.corpus import as_zz
from support.determinant import subresultant_coefficients
from support.rng import SplitMix64
from support.gen import coefficient
from polynomials import DensePoly, check_resultant_identity, PolyErrorKind

def check_case[C: CoefficientRing](f: SparsePoly[C], g: SparsePoly[C], expected: SparsePoly[C], variable: Int64, mut c: Checker, mut work: Budget) raises:
    var result = resultant(f, g, variable, work)
    c.check(result.resultant == expected, "reference resultant")
    c.check(result.cofactors[0].mul(f, work).add(result.cofactors[1].mul(g, work), work) == expected, "resultant cofactor identity")

def value_matches[C: CoefficientRing](f: SparsePoly[C], g: SparsePoly[C], variable: Int64, mut c: Checker, mut work: Budget) raises:
    c.check(resultant_value(f, g, variable, work) == resultant(f, g, variable, work).resultant, "resultant_value equals the certified resultant")
    c.check(resultant_value(g, f, variable, work) == resultant(g, f, variable, work).resultant, "swapped resultant_value")


def big[C: CoefficientRing](ctx: C.Context, bits: Int, mut rng: SplitMix64, mut work: Budget) raises -> C:
    var v = C.one(ctx)
    for _ in range(bits - 1):
        v = v.add(v, work)
        if rng.below(2):
            v = v.add(C.one(ctx), work)
    if rng.below(2):
        v = v.neg(work)
    return v^


def univariate[C: CoefficientRing](ctx: C.Context, degree: Int, bits: Int, mut rng: SplitMix64, mut work: Budget) raises -> SparsePoly[C]:
    var values = List[C]()
    for i in range(degree + 1):
        var v = big[C](ctx, bits, rng, work) if bits > 0 else coefficient[C](ctx, rng.below(9) - 4, work)
        if i == degree and v.is_zero():
            v = C.one(ctx)
        values.append(v^)
    return DensePoly[C].from_coefficients(0, ctx, values^, work).to_sparse(MonomialOrder(), work)


def value_cases(mut c: Checker) raises:
    """The cofactor-free resultant agrees with the certified one on every route."""
    var work = Budget()
    var rng = SplitMix64(6029)
    for m in range(1, 9):
        for n in range(1, 9):
            # Multi-modular over ZZ, including coefficients wider than one prime.
            var f = univariate[ZZ](NoContext(), m, 0 if (m + n) % 2 else 70, rng, work)
            var g = univariate[ZZ](NoContext(), n, 0 if (m * n) % 3 else 40, rng, work)
            value_matches(f, g, 0, c, work)
            var x = SparsePoly[ZZ].variable(0, MonomialOrder(), NoContext(), work)
            var common = x.add(SparsePoly[ZZ].constant(ZZ.one(NoContext()), MonomialOrder(), work), work)
            c.check(resultant_value(f.mul(common, work), g.mul(common, work), 0, work).is_zero(), "shared factor gives a zero resultant")
            var fq = univariate[QQ](NoContext(), m, 0, rng, work)
            var gq = univariate[QQ](NoContext(), n, 0, rng, work)
            value_matches(fq, gq, 0, c, work)
    var moduli: List[UInt64] = [2, 3, 7, 101, prime(0, work)]
    for modulus in moduli:
        var ctx = Modulus(modulus, work)
        for m in range(0, 7):
            for n in range(1, 7):
                var f = univariate[ModInt](ctx, m, 0, rng, work)
                var g = univariate[ModInt](ctx, n, 0, rng, work)
                value_matches(f, g, 0, c, work)
    # Hadamard bounds past 2048 bits take images modulo sieved primes below 2^30.
    for pair in [(30, 25), (41, 17), (24, 24), (12, 60)]:
        var f = univariate[ZZ](NoContext(), pair[0], 60, rng, work)
        var g = univariate[ZZ](NoContext(), pair[1], 60, rng, work)
        value_matches(f, g, 0, c, work)
    # Long remainder sequences through the vectorized small-prime kernel and
    # the 64-bit one; 1073741789 is the largest prime below 2^30.
    var long_moduli: List[UInt64] = [7, 65521, 1073741789, prime(0, work)]
    for modulus in long_moduli:
        var ctx = Modulus(modulus, work)
        for pair in [(20, 13), (37, 37), (40, 9), (9, 31)]:
            var f = univariate[ModInt](ctx, pair[0], 0, rng, work)
            var g = univariate[ModInt](ctx, pair[1], 0, rng, work)
            value_matches(f, g, 0, c, work)
    var order = MonomialOrder(MonomialOrder.GREVLEX, [0, 1, 2], work)
    for _ in range(12):
        var f = polynomial[ZZ](NoContext(), order, rng, work, terms=5, variables=3, degree=3)
        var g = polynomial[ZZ](NoContext(), order, rng, work, terms=4, variables=3, degree=3)
        for variable in range(3):
            if f.degree_in(Int64(variable), work) > 0 or g.degree_in(Int64(variable), work) > 0:
                value_matches(f, g, Int64(variable), c, work)
    multivariate_value_cases[ZZ](NoContext(), c)
    multivariate_value_cases[ModInt](Modulus(101, work), c)
    multivariate_value_cases[ModInt](Modulus(prime(0, work), work), c)
    multivariate_value_cases[ModInt](Modulus(3, work), c)


def multivariate_value_cases[C: CoefficientRing](ctx: C.Context, mut c: Checker) raises:
    """Evaluation and interpolation, including leading coefficients that vanish on the grid."""
    var work = Budget()
    var rng = SplitMix64(8101)
    var order = MonomialOrder(MonomialOrder.LEX, [0, 1, 2], work)
    for round in range(10):
        var nvars = 2 + round % 2
        var f = polynomial[C](ctx, order, rng, work, terms=4 + round % 3, variables=nvars, degree=2 + round % 3, coefficient_bits=0 if round % 2 else 35)
        var g = polynomial[C](ctx, order, rng, work, terms=3 + round % 4, variables=nvars, degree=2 + round % 2)
        for variable in range(nvars):
            if f.degree_in(Int64(variable), work) > 0 or g.degree_in(Int64(variable), work) > 0:
                value_matches(f, g, Int64(variable), c, work)
    var x = SparsePoly[C].variable(0, order, ctx, work)
    var y = SparsePoly[C].variable(1, order, ctx, work)
    var z = SparsePoly[C].variable(2, order, ctx, work)
    var one = SparsePoly[C].constant(C.one(ctx), order, work)
    var two = one.add(one, work)
    # lc_x(f) = (y - 1)(z - 2) and lc_x(g) = y vanish at grid points, alone and together.
    var f = y.sub(one, work).mul(z.sub(two, work), work).mul(x.pow(2, work), work).add(y.mul(x, work), work).add(z, work)
    var g = y.mul(x.pow(3, work), work).add(z.sub(one, work).mul(x, work), work).add(two.add(one, work), work)
    for variable in range(3):
        value_matches(f, g, Int64(variable), c, work)
    var h = y.mul(z, work).mul(x, work).add(one, work)
    value_matches(f.mul(h, work), g.mul(h, work), 0, c, work)
    c.check(resultant_value(f.mul(h, work), g.mul(h, work), 0, work).is_zero(), "common factor in x gives zero")


def main() raises:
    var c = Checker("resultant")
    var work = Budget()
    var count = 0
    for record in read_cases():
        if record.field("op ") != "resultant":
            continue
        var order = MonomialOrder()
        for line in record.lines:
            if line.startswith("order "):
                order = parse_order(String(line[byte=6:]), work)
        var variable = Int64(0)
        for line in record.lines:
            if line.startswith("in variable "):
                variable = Int64(Int(String(line[byte=12:])))
        var ft = record.field("in f ")
        var gt = record.field("in g ")
        var et = record.field("out resultant ")
        var f = parse_polynomial(ft, order, work)
        var g = parse_polynomial(gt, order, work)
        var expected = parse_polynomial(et, order, work)
        check_case(f, g, expected, variable, c, work)
        if record.field("ring ") == "ZZ":
            var fz = as_zz(f, work)
            var gz = as_zz(g, work)
            var ez = as_zz(expected, work)
            check_case(fz, gz, ez, variable, c, work)
        var family = subresultants(f, g, variable, work)
        for line in record.lines:
            if line.startswith("out psc "):
                var fields = line.split(" ")
                var index = Int(fields[2])
                var coefficient_text = String(fields[3])
                var e = parse_polynomial(coefficient_text, order, work)
                var values = _split(family[index], variable, work)
                var actual = SparsePoly[QQ].zero(order, NoContext(), work)
                if index < len(values):
                    actual = values[index].copy()
                c.check(actual == e, String(record.name, " PSC ", index))
        count += 1
    c.check(count == 12, "all twelve resultant corpus cases")
    var rng = SplitMix64(7981)
    var order = MonomialOrder()
    for m in range(1, 6):
        for n in range(1, 6):
            for _ in range(3):
                var aa = List[ZZ]()
                var bb = List[ZZ]()
                for _ in range(m):
                    aa.append(coefficient[ZZ](NoContext(), rng.below(7) - 3, work))
                for _ in range(n):
                    bb.append(coefficient[ZZ](NoContext(), rng.below(7) - 3, work))
                aa.append(coefficient[ZZ](NoContext(), rng.below(3) + 1, work))
                bb.append(coefficient[ZZ](NoContext(), rng.below(3) + 1, work))
                var f = DensePoly[ZZ].from_coefficients(0, NoContext(), aa^, work)
                var g = DensePoly[ZZ].from_coefficients(0, NoContext(), bb^, work)
                var fs = f.to_sparse(order, work)
                var gs = g.to_sparse(order, work)
                var family = subresultants(fs, gs, 0, work)
                for j in range(min(m, n)):
                    var values = subresultant_coefficients(f, g, j)
                    var expected = DensePoly[ZZ].from_coefficients(0, NoContext(), values^, work).to_sparse(order, work)
                    c.check(family[j] == expected, "all coefficients of a Sylvester subresultant minor")
                var got = resultant(fs, gs, 0, work)
                c.check(got.resultant == family[0] and check_resultant_identity(fs, gs, got, work), "generated resultant identity and determinant")
                got.resultant = got.resultant.add(SparsePoly[ZZ].constant(ZZ.one(NoContext()), order, work), work)
                c.check(not check_resultant_identity(fs, gs, got, work), "corrupt resultant rejected")
    # A degree gap forces defective and zero indexed subresultants.
    var x = SparsePoly[ZZ].variable(0, order, NoContext(), work)
    var one = SparsePoly[ZZ].constant(ZZ.one(NoContext()), order, work)
    var f = x.pow(5, work).add(one, work)
    var g = x.pow(3, work)
    var family = subresultants(f, g, 0, work)
    c.check(family[0] == one.neg(work) and family[1].is_zero() and family[2] == one.neg(work), "defective subresultant family")
    c.check(resultant(f.mul(x, work), g.mul(x, work), 0, work).resultant.is_zero(), "planted common factor vanishes")
    value_cases(c)
    try:
        _ = resultant(one, one, 0, work)
        c.check(False, "undefined constant resultant identity accepted")
    except e:
        c.check(e.kind == PolyErrorKind.DOMAIN, "two constant resultant DOMAIN")
    c.finish()
