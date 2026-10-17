"""Independent gcd corpus, including integer contents and an unlucky prime."""
from apn_mojo import Integer
from polynomials import Budget, QQ, ZZ, ModInt, Modulus, NoContext, CoefficientRing, SparsePoly, DensePoly, MonomialOrder, prime, PolyErrorKind
from polynomials._prs import _prs
from support.gen import coefficient
from support.rng import SplitMix64
from polynomials._gcd import _gcd_value, _modular_primitive, _primitive_zz
from support.corpus import read_cases, parse_order, parse_polynomial, as_zz
from support.check import Checker
from polynomials.gcd import gcd, gcd_value
from polynomials._euclidean import _extended
from polynomials._dense_ops import _gcd as _field_gcd
from polynomials.division import divide_exact
from support.gen import polynomial
from polynomials.certificates import check_common_divisor, check_bezout, check_coprimality

def generated[C: CoefficientRing](ctx: C.Context, mut c: Checker) raises:
    var work = Budget()
    var rng = SplitMix64(941)
    var order = MonomialOrder(MonomialOrder.GREVLEX, [0, 1, 2], work)
    var one = SparsePoly[C].constant(C.one(ctx), order, work)
    var x = SparsePoly[C].variable(0, order, ctx, work)
    var y = SparsePoly[C].variable(1, order, ctx, work)
    var z = SparsePoly[C].variable(2, order, ctx, work)
    var a = x.scale(coefficient[C](ctx, 3, work), work)
    var b = x.add(one, work).scale(coefficient[C](ctx, 4, work), work)
    for i in range(16):
        var expected = one.copy()
        for _ in range(1 + i % 3):
            var shift = SparsePoly[C].constant(coefficient[C](ctx, rng.below(13) - 6, work), order, work)
            var linear = x.add(shift, work)
            if i % 3 > 0:
                linear = linear.add(y, work)
            if i % 3 > 1:
                linear = linear.add(z, work)
            expected = expected.mul(linear, work)
        comptime if C == ZZ:
            expected = expected.scale(coefficient[C](ctx, 2, work), work)
        var f = expected.mul(a, work)
        var h = expected.mul(b, work)
        var got = gcd(f, h, work, certify_maximal=i < 4)
        c.check(got.gcd == expected and check_common_divisor(f, h, got, work), "generated planted gcd and cofactors")
        if got.bezout:
            c.check(check_bezout(f, h, got, work), "generated univariate maximality")
        elif got.coprimality:
            c.check(check_coprimality(got.cofactors[0], got.cofactors[1], got.coprimality.value(), work), "generated content maximality")
    var tiny = Budget(0)
    try:
        _ = gcd(x, one, tiny)
        c.check(False, "gcd ignored budget")
    except e:
        c.check(e.kind == PolyErrorKind.LIMIT, "gcd budget exhaustion")


def modular_cases(mut c: Checker) raises:
    var work = Budget()
    var order = MonomialOrder()
    var x = SparsePoly[ZZ].variable(0, order, NoContext(), work)
    var one = SparsePoly[ZZ].constant(ZZ.one(NoContext()), order, work)
    var p0 = Integer(Int(prime(0, work)))
    var p1 = Integer(Int(prime(1, work)))
    var height = p0 + Integer(123)
    var factor = x.scale(ZZ(height), work).add(one, work)
    var a = x.copy()
    var b = x.add(SparsePoly[ZZ].constant(ZZ(p1), order, work), work)
    # The first prime has the correct image degree but cannot reconstruct
    # height. At the second prime a and b coincide, so its larger-degree
    # gcd image must be discarded. A later lucky image finishes the CRT.
    c.check(_modular_primitive(factor.mul(a, work), factor.mul(b, work), 0, work) == factor, "discard later unlucky image")
    var drop = x.scale(ZZ(p0), work).add(one, work)
    c.check(_modular_primitive(factor.mul(drop, work), factor.mul(x.add(one, work), work), 0, work) == factor, "skip prime dropping one input degree")
    var high = x.pow(12, work).add(SparsePoly[ZZ].constant(ZZ(height), order, work), work)
    c.check(gcd(high.mul(x, work), high.mul(x.add(one, work), work), work).gcd == high, "public modular dispatch and multiple-prime reconstruction")
    var rng = SplitMix64(913)
    for degree in range(2, 14):
        var aa = List[ZZ]()
        var bb = List[ZZ]()
        for _ in range(degree):
            aa.append(ZZ(Integer(rng.below(11) - 5)))
            bb.append(ZZ(Integer(rng.below(11) - 5)))
        aa.append(ZZ.one(NoContext()))
        bb.append(ZZ.one(NoContext()))
        var f = DensePoly[ZZ].from_coefficients(0, NoContext(), aa^, work).to_sparse(order, work)
        var h = DensePoly[ZZ].from_coefficients(0, NoContext(), bb^, work).to_sparse(order, work)
        var sequence = _prs(f, h, 0, False, work)
        var expected = _primitive_zz(sequence[len(sequence) - 1].polynomial, work)
        c.check(_modular_primitive(f, h, 0, work) == expected, "modular and PRS gcd agree")


def dense_random[C: CoefficientRing](ctx: C.Context, degree: Int, mut rng: SplitMix64, mut work: Budget, bits: Int = 0) raises -> DensePoly[C]:
    var values = List[C]()
    for i in range(degree + 1):
        var v = coefficient[C](ctx, rng.below(201) - 100, work)
        if bits > 0:
            # A random bits-bit magnitude with a random sign.
            v = C.one(ctx)
            for _ in range(bits - 1):
                v = v.add(v, work)
                if rng.below(2):
                    v = v.add(C.one(ctx), work)
            if rng.below(2):
                v = v.neg(work)
        if i == degree and v.is_zero():
            v = C.one(ctx)
        values.append(v^)
    return DensePoly[C].from_coefficients(0, ctx, values^, work)


def word_field_cases(mut c: Checker) raises:
    """The word-size prime-field gcd matches the generic Euclidean loop."""
    var work = Budget()
    var rng = SplitMix64(4271)
    # 1073741789 is the largest prime below 2^30, the bound of the 32-bit Montgomery kernel.
    var moduli: List[UInt64] = [3, 5, 101, 65521, 1073741789, 1073741827, prime(0, work), prime(7, work)]
    for modulus in moduli:
        var ctx = Modulus(modulus, work)
        for degree in [0, 1, 2, 7, 23, 60]:
            var g = dense_random[ModInt](ctx, degree // 2, rng, work)
            var f = g.mul(dense_random[ModInt](ctx, degree, rng, work), work)
            var h = g.mul(dense_random[ModInt](ctx, degree - degree // 3, rng, work), work)
            var expected = _extended(f, h, work, carry=False)[0].copy()
            c.check(_field_gcd(f, h, work) == expected, "word field gcd matches the generic loop")
            c.check(_field_gcd(f, DensePoly[ModInt](0, ctx.copy()), work) == _extended(f, DensePoly[ModInt](0, ctx.copy()), work, carry=False)[0], "word field gcd with zero")


def multi_prime_cases(mut c: Checker) raises:
    """Planted gcds whose reconstruction needs several primes, against the PRS."""
    var work = Budget()
    var rng = SplitMix64(5303)
    var order = MonomialOrder()
    for round in range(10):
        var bits = 40 + 30 * (round % 4)
        var g = dense_random[ZZ](NoContext(), 3 + round % 5, rng, work, bits=bits).to_sparse(order, work)
        var a = dense_random[ZZ](NoContext(), 4 + round % 3, rng, work, bits=bits).to_sparse(order, work)
        var b = dense_random[ZZ](NoContext(), 2 + round % 4, rng, work, bits=bits).to_sparse(order, work)
        var f = g.mul(a, work)
        var h = g.mul(b, work)
        var sequence = _prs(f, h, 0, False, work)
        var last = sequence[len(sequence) - 1].polynomial.copy()
        var cf = _primitive_zz(f, work)
        var ch = _primitive_zz(h, work)
        var expected = _primitive_zz(last, work)
        c.check(_modular_primitive(cf, ch, 0, work) == expected, "multi-prime modular gcd matches the PRS")
        c.check(gcd_value(f, h, work) == gcd(f, h, work).gcd, "gcd_value equals the gcd of the full result")


def division_cases[C: CoefficientRing](ctx: C.Context, mut c: Checker) raises:
    """Exact sparse division on packed keys: exact multiples, inexact inputs, and the wide fallback."""
    var work = Budget()
    var rng = SplitMix64(7717)
    var orders = List[MonomialOrder]()
    orders.append(MonomialOrder(MonomialOrder.GREVLEX, [0, 1, 2, 3], work))
    orders.append(MonomialOrder(MonomialOrder.LEX, [2, 0, 3, 1], work))
    orders.append(MonomialOrder())
    for order in orders:
        for round in range(12):
            var q = polynomial[C](ctx, order, rng, work, terms=3 + round % 5, variables=4, degree=2 + round % 3)
            var g = polynomial[C](ctx, order, rng, work, terms=1 + round % 4, variables=4, degree=1 + round % 4)
            if g.is_zero() or q.is_zero():
                continue
            var f = q.mul(g, work)
            var got = divide_exact(f, g, work)
            c.check(Bool(got) and got.value() == q, "packed exact quotient")
            var r = polynomial[C](ctx, order, rng, work, terms=2, variables=4, degree=3)
            var perturbed = f.add(r, work)
            var inexact = divide_exact(perturbed, g, work)
            if inexact:
                c.check(inexact.value().mul(g, work) == perturbed, "accepted quotient is exact")
            if len(g.variables(work)):
                # q g + 1 is not a multiple of a nonconstant g.
                c.check(not divide_exact(f.add(SparsePoly[C].constant(C.one(ctx), order, work), work), g, work), "inexact input rejected")
    # Few terms in a large exponent box take the heap rather than a dense array.
    for order in orders:
        var one = SparsePoly[C].constant(C.one(ctx), order, work)
        var x = SparsePoly[C].variable(0, order, ctx, work)
        var y = SparsePoly[C].variable(1, order, ctx, work)
        var z = SparsePoly[C].variable(3, order, ctx, work)
        var q = x.pow(60, work).mul(y, work).add(y.pow(50, work).mul(z.pow(3, work), work), work).add(one, work)
        var g = x.pow(7, work).mul(z, work).add(y.pow(9, work), work).add(one.add(one, work), work)
        var got = divide_exact(q.mul(g, work), g, work)
        c.check(Bool(got) and got.value() == q, "sparse quotient over a large box")
        c.check(not divide_exact(q.mul(g, work).add(x, work), g, work), "sparse inexact input over a large box")
    # Thirty variables of degree 31 need 150 key bits: the generic path answers.
    var order = MonomialOrder()
    var wide = SparsePoly[C].constant(C.one(ctx), order, work)
    for v in range(30):
        var power = SparsePoly[C].variable(Int64(v), order, ctx, work).pow(31, work)
        if v < 2:
            power = power.add(SparsePoly[C].constant(C.one(ctx), order, work), work)
        wide = wide.mul(power, work)
    var x = SparsePoly[C].variable(0, order, ctx, work).pow(31, work).add(SparsePoly[C].constant(C.one(ctx), order, work), work)
    var quotient = divide_exact(wide, x, work)
    c.check(Bool(quotient) and quotient.value().mul(x, work) == wide, "wide exponents fall back to the generic division")


def shortcut_cases(mut c: Checker) raises:
    """Deflated gcds and the one-image proof of a constant gcd in the main variable."""
    var work = Budget()
    var order = MonomialOrder(MonomialOrder.GREVLEX, [0, 1, 2], work)
    var one = SparsePoly[ZZ].constant(ZZ.one(NoContext()), order, work)
    var two = one.add(one, work)
    var x = SparsePoly[ZZ].variable(0, order, NoContext(), work)
    var y = SparsePoly[ZZ].variable(1, order, NoContext(), work)
    var z = SparsePoly[ZZ].variable(2, order, NoContext(), work)
    # Every exponent of x is even and every exponent of y a multiple of three.
    var x2 = x.pow(2, work)
    var y3 = y.pow(3, work)
    var a = x2.add(y3, work).add(one, work)
    var b = x2.sub(y3.scale(ZZ(Integer(3)), work), work).add(two, work)
    var d = x2.mul(y3, work).sub(two, work)
    var common = a.mul(a, work).scale(ZZ(Integer(6)), work)
    var got = gcd_value(common.mul(b, work).scale(ZZ(Integer(5)), work), common.mul(d, work).scale(ZZ(Integer(4)), work), work)
    c.check(got == common, "deflated gcd inflates back with its content")
    # Mixed: z is not deflatable, x is.
    var e = x2.mul(z, work).add(z.pow(3, work), work).add(one, work)
    c.check(gcd_value(e.mul(a, work), e.mul(b, work), work) == e, "partial deflation")
    # Coprime in x with a shared content in y and z: the content is the gcd.
    var content = y.add(z, work).add(one, work)
    var f = content.mul(x.mul(y, work).add(z, work).add(two, work), work)
    var h = content.mul(x.pow(2, work).sub(y.mul(z, work), work), work).scale(ZZ(Integer(-3)), work)
    c.check(gcd_value(f, h, work) == content, "constant image gcd leaves the content gcd")
    # lc_x(f) = y - 2 vanishes at the first point y = 2, so the test must move on.
    var g = y.sub(two, work).mul(x.pow(3, work), work).add(z, work).add(one, work)
    var k = x.pow(2, work).add(y, work)
    c.check(gcd_value(g, k, work) == one, "vanishing leading coefficient at the first point")
    c.check(gcd_value(g.mul(k, work), k.mul(x.add(z, work), work), work) == k, "planted gcd after an unlucky point")


def heuristic_cases(mut c: Checker) raises:
    """Dense inputs take GCDHEU; the non-heuristic route must give the same gcd."""
    var work = Budget()
    var order = MonomialOrder(MonomialOrder.GREVLEX, [0, 1, 2, 3], work)
    var one = SparsePoly[ZZ].constant(ZZ.one(NoContext()), order, work)
    var x = SparsePoly[ZZ].variable(0, order, NoContext(), work)
    var y = SparsePoly[ZZ].variable(1, order, NoContext(), work)
    var z = SparsePoly[ZZ].variable(2, order, NoContext(), work)
    var t = SparsePoly[ZZ].variable(3, order, NoContext(), work)
    var u = one.add(x, work).add(y.scale(ZZ(Integer(2)), work), work).sub(z, work)
    var v = one.scale(ZZ(Integer(3)), work).add(x, work).add(y, work).add(z, work).add(t, work)
    var w = one.scale(ZZ(Integer(-5)), work).add(x.scale(ZZ(Integer(7)), work), work).sub(y, work).add(z, work).sub(t.scale(ZZ(Integer(4)), work), work)
    for k in range(1, 3):
        var g = u.pow(UInt64(k), work).scale(ZZ(Integer(6)), work)
        var f = g.mul(v.pow(UInt64(k), work), work).scale(ZZ(Integer(5)), work)
        var h = g.mul(w.pow(UInt64(k + 1), work), work).scale(ZZ(Integer(-4)), work)
        var got = _gcd_value(f, h, work)
        c.check(got == _gcd_value(f, h, work, heuristic=False), "heuristic gcd equals the PRS gcd")
        c.check(got == g or got == g.neg(work), "heuristic gcd of planted dense products")
        c.check(_gcd_value(f, v.pow(UInt64(k + 1), work).mul(w, work), work) == _gcd_value(f, v.pow(UInt64(k + 1), work).mul(w, work), work, heuristic=False), "heuristic gcd of a cofactor power")


def main() raises:
    var c = Checker("gcd")
    var work = Budget()
    var count = 0
    for record in read_cases():
        if record.field("op ") != "gcd":
            continue
        var order = MonomialOrder()
        for line in record.lines:
            if line.startswith("order "):
                order = parse_order(String(line[byte=6:]), work)
        var ft = record.field("in f ")
        var ht = record.field("in h ")
        var et = record.field("out gcd ")
        var f = parse_polynomial(ft, order, work)
        var h = parse_polynomial(ht, order, work)
        var expected = parse_polynomial(et, order, work)
        if record.field("ring ") == "ZZ":
            var fz = as_zz(f, work)
            var hz = as_zz(h, work)
            var ez = as_zz(expected, work)
            var got = gcd(fz, hz, work, certify_maximal=True)
            c.check(got.gcd == ez and check_common_divisor(fz, hz, got, work), record.name)
            if got.coprimality:
                c.check(check_coprimality(got.cofactors[0], got.cofactors[1], got.coprimality.value(), work), "integer maximality")
            if record.name == "gcd.uni.unlucky_first_prime":
                var fp = _primitive_zz(fz, work)
                var hp = _primitive_zz(hz, work)
                var ep = _primitive_zz(ez, work)
                c.check(_modular_primitive(fp, hp, 0, work) == ep, "unlucky first prime restart")
        else:
            var got = gcd(f, h, work, certify_maximal=True)
            c.check(got.gcd == expected and check_common_divisor(f, h, got, work), record.name)
            if got.bezout:
                c.check(check_bezout(f, h, got, work), "field Bezout maximality")
            elif got.coprimality:
                c.check(check_coprimality(got.cofactors[0], got.cofactors[1], got.coprimality.value(), work), "field recursive maximality")
        count += 1
    c.check(count == 21, "all 21 gcd corpus cases")
    generated[ZZ](NoContext(), c)
    generated[QQ](NoContext(), c)
    generated[ModInt](Modulus(101, work), c)
    modular_cases(c)
    word_field_cases(c)
    multi_prime_cases(c)
    division_cases[ZZ](NoContext(), c)
    division_cases[QQ](NoContext(), c)
    division_cases[ModInt](Modulus(101, work), c)
    shortcut_cases(c)
    heuristic_cases(c)
    c.finish()
