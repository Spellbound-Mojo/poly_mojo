"""Every degree through twice the Karatsuba threshold and sparse cross-checks."""
from apn_mojo import Integer
from polynomials import Budget, PolyErrorKind, CoefficientRing, ZZ, QQ, ModInt, Modulus, NoContext, MonomialOrder, SparsePoly, DensePoly
from polynomials._nmod import _field, _mul, _schoolbook, _to, _TRANSFORM, _TRANSFORM_SMALL
from support.check import Checker
from support.gen import coefficient
from support.rng import SplitMix64

def check_ring[C: CoefficientRing](ctx: C.Context, mut c: Checker) raises:
    var work = Budget()
    var rng = SplitMix64(209)
    for degree in range(2 * DensePoly[C].karatsuba_threshold() + 1):
        var aa = List[C]()
        var bb = List[C]()
        for _ in range(degree):
            aa.append(coefficient[C](ctx, rng.below(21) - 10, work))
            bb.append(coefficient[C](ctx, rng.below(21) - 10, work))
        aa.append(C.one(ctx))
        bb.append(C.one(ctx))
        var a = DensePoly[C].from_coefficients(7, ctx, aa^, work)
        var b = DensePoly[C].from_coefficients(7, ctx, bb^, work)
        var product = a.mul(b, work)
        c.check(product == a.mul_schoolbook(b, work), String("schoolbook degree ", degree))
        product.check_invariants(work)
        var sparse = a.to_sparse(MonomialOrder(), work)
        c.check(DensePoly[C].from_sparse(sparse, work, variable=Int64(7)) == a, "dense roundtrip")
        if degree < 8:
            var bs = b.to_sparse(MonomialOrder(), work)
            c.check(product.to_sparse(MonomialOrder(), work) == sparse.mul(bs, work), "sparse product crosscheck")
            c.check(a.add(b, work).to_sparse(MonomialOrder(), work) == sparse.add(bs, work), "sparse sum crosscheck")
            c.check(a.sub(b, work).to_sparse(MonomialOrder(), work) == sparse.sub(bs, work), "sparse difference crosscheck")
            c.check(a.neg(work).to_sparse(MonomialOrder(), work) == sparse.neg(work), "sparse negation crosscheck")
            c.check(a.pow(3, work) == a.mul(a, work).mul(a, work), "dense repeated power")
    # Unequal splits and sums that cancel entire Karatsuba halves.
    var threshold = DensePoly[C].karatsuba_threshold()
    var sizes: List[Int] = [0, 1, threshold - 1, threshold, threshold + 1, 2 * threshold + 1]
    for left in sizes:
        for right in sizes:
            var aa = List[C]()
            var bb = List[C]()
            for i in range(left):
                aa.append(C.one(ctx) if i < left // 2 else C.one(ctx).neg(work))
            for i in range(right):
                bb.append(C.one(ctx) if i < right // 2 else C.one(ctx).neg(work))
            var a = DensePoly[C].from_coefficients(7, ctx, aa^, work)
            var b = DensePoly[C].from_coefficients(7, ctx, bb^, work)
            var product = a.mul(b, work)
            c.check(product == a.mul_schoolbook(b, work), "unbalanced or cancelling Karatsuba split")
            product.check_invariants(work)
    var zero = DensePoly[C].from_coefficients(7, ctx, List[C](), work)
    var one = DensePoly[C].from_coefficients(7, ctx, [C.one(ctx)], work)
    c.check(zero.degree() == -1 and zero.pow(0, work) == one, "zero degree and power")
    c.check(zero.mul(one, work) == zero and one.scale(C.zero(ctx), work) == zero, "zero products")
    c.check(DensePoly[C].from_sparse(zero.to_sparse(MonomialOrder(), work), work, variable=Int64(7)) == zero, "zero roundtrip explicit variable")
    var trimmed = DensePoly[C].from_coefficients(7, ctx, [C.one(ctx), C.zero(ctx), C.zero(ctx)], work)
    c.check(trimmed == one, "trailing zeros removed")
    for kind in range(4):
        var order = MonomialOrder()
        if kind:
            order = MonomialOrder(UInt8(kind), [9, -7, 0], work)
        var x = SparsePoly[C].variable(-7, order, ctx, work)
        var constant = SparsePoly[C].constant(C.one(ctx), order, work)
        var expected = constant.sub(x.pow(2, work), work).add(x.pow(3, work), work)
        var values: List[C] = [C.one(ctx), C.zero(ctx), C.one(ctx).neg(work), C.one(ctx)]
        var dense = DensePoly[C].from_coefficients(-7, ctx, values^, work)
        var converted = dense.to_sparse(order, work)
        converted.check_invariants(work)
        c.check(converted == expected, "linear conversion in every order")
        c.check(DensePoly[C].from_sparse(converted, work) == dense, "negative variable inference")
        c.check(one.to_sparse(order, work) == constant, "constant ignores absent retained variable")
        c.check(zero.to_sparse(order, work).is_zero(), "zero ignores absent retained variable")
    var missing = MonomialOrder(MonomialOrder.LEX, [0], work)
    var nonconstant = DensePoly[C].from_coefficients(7, ctx, [C.zero(ctx), C.one(ctx)], work)
    try:
        _ = nonconstant.to_sparse(missing, work)
        c.check(False, "conversion accepted variable absent from order")
    except e:
        c.check(e.kind == PolyErrorKind.DOMAIN, "conversion validates variable domain")
    var many = List[C](length=1024, fill=C.one(ctx))
    var dense_many = DensePoly[C].from_coefficients(7, ctx, many^, work)
    var linear_budget = Budget(16 * 1024)
    var sparse_many = dense_many.to_sparse(MonomialOrder(), linear_budget)
    c.check(len(sparse_many.terms) == 1024, "dense conversion fits a linear work allowance")
    c.check(DensePoly[C].from_sparse(sparse_many, work) == dense_many, "large conversion roundtrip")
    var small = Budget(0)
    try:
        _ = one.mul(one, small)
        c.check(False, "unbudgeted dense multiplication")
    except e:
        c.check(e.kind == PolyErrorKind.LIMIT, "dense budget exhaustion")

def transforms[C: CoefficientRing](ctx: C.Context, mut c: Checker) raises:
    """Transform products agree with schoolbook products across lengths, coefficient sizes and squares."""
    var work = Budget()
    var rng = SplitMix64(31337)
    for bits in [8, 64, 300]:
        for lengths in [(32, 32), (33, 100), (257, 40), (300, 301)]:
            var aa = List[C]()
            var bb = List[C]()
            for i in range(lengths[0] + lengths[1]):
                var value: C
                comptime if C == ZZ:
                    var x = Integer(Int64(rng.next() >> 1))
                    var shift = bits - 63
                    if shift > 0:
                        x = (x << Integer(shift)) + Integer(Int64(rng.next() >> 1))
                    elif shift < 0:
                        x = x >> Integer(-shift)
                    value = rebind_var[C](ZZ(-x if rng.below(2) else x))
                else:
                    var p = rebind[Modulus](ctx).value
                    value = rebind_var[C](ModInt(rng.next() % p if bits != 8 else p - 1 - UInt64(rng.below(3)), rebind[Modulus](ctx)))
                if i < lengths[0]:
                    aa.append(value^)
                else:
                    bb.append(value^)
            var a = DensePoly[C].from_coefficients(7, ctx, aa^, work)
            var b = DensePoly[C].from_coefficients(7, ctx, bb^, work)
            c.check(a.mul(b, work) == a.mul_schoolbook(b, work), String("transform product, ", bits, " bits, lengths ", lengths[0], " and ", lengths[1]))
            c.check(a.mul(a, work) == a.mul_schoolbook(a, work), "transform square")
    # Extreme values: all coefficients at the top of their range, which exercises the CRT's symmetric range.
    var top = List[C]()
    for _ in range(64):
        comptime if C == ZZ:
            top.append(rebind_var[C](ZZ((Integer(1) << Integer(255)) - Integer(1))))
        else:
            top.append(rebind_var[C](ModInt(rebind[Modulus](ctx).value - 1, rebind[Modulus](ctx))))
    var t = DensePoly[C].from_coefficients(7, ctx, top^, work)
    c.check(t.mul(t.neg(work), work) == t.mul_schoolbook(t.neg(work), work), "transform product at the coefficient bounds")


def native_transforms(mut c: Checker) raises:
    """Montgomery residue products switch to transforms at their thresholds and agree with schoolbook."""
    var work = Budget()
    var rng = SplitMix64(808)
    for p in [UInt64(3), UInt64(2147483647), (UInt64(1) << 62) - 57, UInt64(4611685941117976577), UInt64(268435399)]:
        var f = _field(p)
        var sizes: List[Tuple[Int, Int]] = [(_TRANSFORM, _TRANSFORM), (_TRANSFORM + 1, 3 * _TRANSFORM), (2 * _TRANSFORM, 2 * _TRANSFORM)]
        if p == 268435399:
            # Below _SMALL with two transform primes: the switch is at _TRANSFORM_SMALL.
            sizes = [(_TRANSFORM_SMALL, _TRANSFORM_SMALL + 3)]
        for lengths in sizes:
            var a = List[UInt64]()
            var b = List[UInt64]()
            for _ in range(lengths[0]):
                a.append(_to(rng.next(), f))
            for _ in range(lengths[1]):
                b.append(_to(rng.next(), f))
            a[len(a) - 1] = f.one
            b[len(b) - 1] = f.one
            var expected = _schoolbook(a, b, len(a) + len(b), f, work)
            c.check(_mul(a, b, f, work) == expected, String("native transform product modulo ", p))
            c.check(_mul(a, a, f, work) == _schoolbook(a, a, 2 * len(a), f, work), "native transform square")


def main() raises:
    var c = Checker("dense")
    var work = Budget()
    check_ring[ZZ](NoContext(), c)
    check_ring[QQ](NoContext(), c)
    check_ring[ModInt](Modulus(101, work), c)
    native_transforms(c)
    transforms[ZZ](NoContext(), c)
    transforms[ModInt](Modulus(2, work), c)
    transforms[ModInt](Modulus(101, work), c)
    transforms[ModInt](Modulus((UInt64(1) << 62) - 57, work), c)
    transforms[ModInt](Modulus(4611685941117976577, work), c)
    var x = SparsePoly[ZZ].variable(1, MonomialOrder(), NoContext(), work)
    var y = SparsePoly[ZZ].variable(2, MonomialOrder(), NoContext(), work)
    try:
        _ = DensePoly[ZZ].from_sparse(x.add(y, work), work)
        c.check(False, "multivariate accepted")
    except e:
        c.check(e.kind == PolyErrorKind.DOMAIN, "multivariate DOMAIN")
    try:
        _ = DensePoly[ZZ].from_sparse(x.mul(y, work), work)
        c.check(False, "multivariate monomial accepted")
    except e:
        c.check(e.kind == PolyErrorKind.DOMAIN, "multivariate monomial DOMAIN")
    c.finish()
