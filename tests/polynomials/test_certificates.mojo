"""Coprimality soundness, malformed proof arenas, and gcd properties."""
from polynomials import Budget, PolyErrorKind, CoefficientRing, CoefficientField, QQ, ZZ, ModInt, Modulus, NoContext, SparsePoly, DensePoly, MonomialOrder, gcd, extended_gcd, content, primitive_part, coprimality_certificate, check_coprimality, check_bezout, check_common_divisor, ContentGcdStep, CoprimalityNode, CoprimalityCertificate
from polynomials._gcd import _gcd_value, _modular_primitive
from support.check import Checker


def properties[C: CoefficientRing](ctx: C.Context, mut c: Checker) raises:
    var work = Budget()
    for kind in range(4):
        var order = MonomialOrder()
        if kind:
            order = MonomialOrder(UInt8(kind), [0, 1, 2], work)
        var one = SparsePoly[C].constant(C.one(ctx), order, work)
        var zero = SparsePoly[C].zero(order, ctx, work)
        var x = SparsePoly[C].variable(0, order, ctx, work)
        var y = SparsePoly[C].variable(1, order, ctx, work)
        var z = SparsePoly[C].variable(2, order, ctx, work)
        var factor = x.add(y, work).add(z, work).pow(2, work).add(one, work)
        var a = x.mul(y, work)
        var b = x.add(one, work).mul(y.add(one, work), work)
        var f = factor.mul(a, work)
        var h = factor.mul(b, work)
        var got = gcd(f, h, work, certify_maximal=True)
        c.check(got.gcd == factor, "planted normalized multivariate gcd")
        c.check(check_common_divisor(f, h, got, work), "generated common-divisor identities")
        c.check(Bool(got.coprimality) and check_coprimality(got.cofactors[0], got.cofactors[1], got.coprimality.value(), work), "generated maximality proof")
        var proof = got.coprimality.take()
        var corrupt = proof.copy()
        if corrupt.modular:
            corrupt.modular.value().prime = 4
        else:
            corrupt.nodes[corrupt.root].u = corrupt.nodes[corrupt.root].u.add(one, work)
        c.check(not check_coprimality(a, b, corrupt, work), "corrupt coprimality witness")
        corrupt = proof.copy()
        corrupt.root = len(corrupt.nodes)
        c.check(not check_coprimality(a, b, corrupt, work), "out-of-range root")
        corrupt.root = -2
        c.check(not check_coprimality(a, b, corrupt, work), "negative root")
        if not proof.modular:
            corrupt = proof.copy()
            corrupt.nodes[corrupt.root].contents_node = corrupt.root
            c.check(not check_coprimality(a, b, corrupt, work), "cyclic proof reference")
            corrupt = proof.copy()
            corrupt.nodes[corrupt.root].left_content_steps = List[ContentGcdStep[C]]()
            c.check(not check_coprimality(a, b, corrupt, work), "missing content witnesses")
        got.gcd = zero.copy()
        c.check(not check_common_divisor(f, h, got, work), "corrupt common divisor")
        c.check(not coprimality_certificate(f, h, work), "common factor has no coprimality proof")
        var p = y.mul(x.pow(2, work).add(one, work), work)
        c.check(content(p, 0, work) == y, "polynomial content")
        c.check(content(p, 0, work).mul(primitive_part(p, 0, work), work) == p, "content times primitive part")
        c.check(content(zero, 0, work).is_zero() and primitive_part(zero, 0, work).is_zero(), "zero content and primitive part")
        var tiny = Budget(0)
        try:
            _ = check_coprimality(a, b, proof, tiny)
            c.check(False, "checker ignored zero budget")
        except e:
            c.check(e.kind == PolyErrorKind.LIMIT, "checker budget exhaustion")
        comptime if conforms_to(C, CoefficientField):
            var fd = DensePoly[C].from_sparse(x.pow(3, work).sub(x, work), work)
            var hd = DensePoly[C].from_sparse(x.pow(2, work).sub(one, work), work)
            var extended = extended_gcd(fd, hd, work)
            var fs = fd.to_sparse(MonomialOrder(), work)
            var hs = hd.to_sparse(MonomialOrder(), work)
            c.check(check_bezout(fs, hs, extended, work), "extended Euclidean identity")
            extended.bezout.value()[0] = extended.bezout.value()[0].add(SparsePoly[C].constant(C.one(ctx), MonomialOrder(), work), work)
            c.check(not check_bezout(fs, hs, extended, work), "corrupt Bezout multiplier")


def forged_content(mut c: Checker) raises:
    var work = Budget()
    var order = MonomialOrder(MonomialOrder.LEX, [0, 1], work)
    var one = SparsePoly[ZZ].constant(ZZ.one(NoContext()), order, work)
    var zero = SparsePoly[ZZ].zero(order, NoContext(), work)
    var x = SparsePoly[ZZ].variable(0, order, NoContext(), work)
    var y = SparsePoly[ZZ].variable(1, order, NoContext(), work)
    var f = x.mul(y, work)
    var h = x.add(one, work).mul(y, work)
    var nodes = List[CoprimalityNode[ZZ]]()
    nodes.append(CoprimalityNode[ZZ](0, zero.copy(), one.copy(), one.copy(), List[ContentGcdStep[ZZ]](), List[ContentGcdStep[ZZ]](), None))
    nodes.append(CoprimalityNode[ZZ](0, one.copy(), zero.copy(), one.copy(), List[ContentGcdStep[ZZ]](), List[ContentGcdStep[ZZ]](), None))
    var left: List[ContentGcdStep[ZZ]] = [ContentGcdStep[ZZ](zero.copy(), (zero.copy(), zero.copy()), None), ContentGcdStep[ZZ](one.copy(), (zero.copy(), y.copy()), 0)]
    var right: List[ContentGcdStep[ZZ]] = [ContentGcdStep[ZZ](one.copy(), (zero.copy(), y.copy()), 0), ContentGcdStep[ZZ](one.copy(), (one.copy(), y.copy()), 1)]
    nodes.append(CoprimalityNode[ZZ](0, one.neg(work), one.copy(), y.copy(), left^, right^, 1))
    var forged = CoprimalityCertificate[ZZ](nodes^, 2)
    # Every common-divisor equation holds, the claimed contents 1,1 are
    # coprime, and h-f=y is free of x. The missing maximality is essential.
    c.check(not check_coprimality(f, h, forged, work), "forged common divisors cannot masquerade as contents")
    c.check(not coprimality_certificate(f, h, work), "producer refuses shared content")
    var optional_extra = coprimality_certificate(one, one, work)
    var extra = optional_extra.take()
    extra.nodes.append(CoprimalityNode[ZZ](0, one.copy(), zero.copy(), one.copy(), List[ContentGcdStep[ZZ]](), List[ContentGcdStep[ZZ]](), 2))
    c.check(not check_coprimality(one, one, extra, work), "unreachable node still obeys arena reference format")
    var dependent: List[CoprimalityNode[ZZ]] = [CoprimalityNode[ZZ](0, one.copy(), zero.copy(), x.copy(), List[ContentGcdStep[ZZ]](), List[ContentGcdStep[ZZ]](), None)]
    c.check(not check_coprimality(x, one, CoprimalityCertificate[ZZ](dependent^, 0), work), "elimination identity must remove its variable")


def main() raises:
    var c = Checker("certificates")
    var work = Budget()
    properties[ZZ](NoContext(), c)
    properties[QQ](NoContext(), c)
    properties[ModInt](Modulus(101, work), c)
    forged_content(c)
    c.finish()
