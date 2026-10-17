"""Closed-form sparse products across rings, orders, collisions and limits."""
from apn_mojo import Integer, Rational
from polynomials import Budget, CoefficientRing, ZZ, QQ, ModInt, Modulus, NoContext, SparsePoly, Term, Monomial, MonomialOrder, PolyErrorKind
from support.products import geometric, expected_product
from support.check import Checker
from support.gen import polynomial
from support.rng import SplitMix64
from polynomials.sparse import _heap_product


def products[C: CoefficientRing](base: C, mut c: Checker) raises:
    var work = Budget()
    for kind in range(4):
        var order = MonomialOrder() if kind == 0 else MonomialOrder(UInt8(kind), [Int64(1), Int64(0)], work)
        for n in [2, 8, 32, 34]:
            for shape in range(3):
                var a = geometric(n, 0, False, base, order, work)
                var b = geometric(n, Int64(1 if shape == 1 else 0), shape == 2, base, order, work)
                var expected = expected_product(n, shape == 1, shape == 2, base, order, work)
                var product = a.mul(b, work)
                product.check_invariants(work)
                c.check(product == expected and b.mul(a, work) == expected, "closed-form product and reversed operands")
        var a = geometric(2, 0, False, base, order, work)
        var b = geometric(34, 0, False, base, order, work)
        var square = base.mul(base, work)
        var terms = List[Term[C]]()
        for k in range(35):
            var value = square.copy() if k == 0 or k == 34 else square.add(square, work)
            terms.append(Term[C](Monomial([(Int64(0), UInt32(k))], work) if k else Monomial(), value^))
        var expected = SparsePoly[C].from_terms(terms^, order, base.context(), work)
        c.check(a.mul(b, work) == expected and b.mul(a, work) == expected, "asymmetric product")
    var order = MonomialOrder(MonomialOrder.LEX, [Int64(0)], work)
    var a = geometric(34, 0, False, base, order, work)
    var b = geometric(34, 0, True, base, order, work)
    var saved_a = a.copy()
    var saved_b = b.copy()
    var expected = expected_product(34, False, True, base, order, work)
    for limit in [UInt64(0), UInt64(100), UInt64(1000), UInt64(10000)]:
        var tiny = Budget(limit)
        try:
            var result = a.mul(b, tiny)
            c.check(result == expected, "limited product is complete")
        except e:
            c.check(e.kind == PolyErrorKind.LIMIT, "multiplication budget fails closed")
        c.check(a == saved_a and b == saved_b, "failed multiplication preserves operands")
    var rng = SplitMix64(118)
    var kernel = MonomialOrder()
    for kind in [MonomialOrder.LEX, MonomialOrder.GRLEX, MonomialOrder.GREVLEX]:
        var a = polynomial[C](base.context(), kernel, rng, work, terms=48, degree=7)
        var b = polynomial[C](base.context(), kernel, rng, work, terms=35, degree=7)
        var ordered = MonomialOrder(kind, [Int64(2), Int64(0), Int64(1)], work)
        var expected = a.mul(b, work).reorder(ordered, work)
        var left = a.reorder(ordered, work)
        var right = b.reorder(ordered, work)
        c.check(left.mul(right, work) == expected and _heap_product(left, right, work) == expected, "changing order commutes with multiplication on generated multivariate inputs")
    var overflow_order = MonomialOrder(MonomialOrder.LEX, [Int64(0)], work)
    var large = geometric(8, 0, False, base, overflow_order, work)
    large.terms[len(large.terms) - 1].monomial.pairs[0] = (Int64(0), UInt32.MAX)
    var saved = large.copy()
    try:
        _ = _heap_product(large, large, work)
        c.check(False, "overflowing monomial product accepted")
    except e:
        c.check(e.kind == PolyErrorKind.CAPACITY, "heap exponent overflow is CAPACITY")
    c.check(large == saved, "exponent overflow preserves operands")


def word[C: CoefficientRing](ctx: C.Context, x: Int64) -> C:
    comptime if C == ZZ:
        return rebind_var[C](ZZ(Integer(x)))
    else:
        var p = rebind[Modulus](ctx).value
        var r = UInt64(x) % p if x >= 0 else p - UInt64(-x) % p
        return rebind_var[C](ModInt(r, rebind[Modulus](ctx)))


def dense_block[C: CoefficientRing](ctx: C.Context, order: MonomialOrder, mut rng: SplitMix64, n: Int, degree: Int, scale: Int, bits: Int, mut work: Budget) raises -> SparsePoly[C]:
    """Random terms of degree below `degree` in each of n variables, exponents scaled by `scale`, coefficients of `bits` bits."""
    var terms = List[Term[C]]()
    var count = 1
    for _ in range(n):
        count *= degree
    for index in range(count):
        if rng.below(5) == 0:
            continue
        var pairs = List[Tuple[Int64, UInt32]]()
        var rest = index
        for i in range(n):
            var e = rest % degree
            rest //= degree
            if e:
                pairs.append((Int64(i), UInt32(e * scale)))
        var magnitude = Int64(rng.next() >> UInt64(64 - bits)) | 1
        var value = -magnitude if rng.below(2) else magnitude
        terms.append(Term[C](Monomial(pairs^, work), word[C](ctx, value)))
    return SparsePoly[C].from_terms(terms^, order, ctx, work)


def packed[C: CoefficientRing](ctx: C.Context, mut c: Checker) raises:
    """Packed-exponent products agree with the heap product, including window splits and wide accumulators."""
    var work = Budget()
    var rng = SplitMix64(4242)
    for n in [1, 2, 3, 4]:
        var variables = List[Int64]()
        for i in range(n):
            variables.append(Int64(i))
        var order = MonomialOrder(MonomialOrder.LEX, variables^, work)
        for shape in range(4):
            # Shapes: small exponents; large exponents that split the window; 63-bit
            # coefficients; and a product with cancellation against its negation.
            var degree = [200, 14, 6, 4][n - 1]
            var scale = 1 if shape != 1 else 97
            var bits = 63 if shape == 2 else 20
            var a = dense_block[C](ctx, order, rng, n, degree, scale, bits, work)
            var b = dense_block[C](ctx, order, rng, n, degree, scale, bits, work)
            if shape == 3:
                b = b.sub(a, work)
            var expected = _heap_product(a, b, work)
            var product = a.mul(b, work)
            product.check_invariants(work)
            c.check(product == expected, String("packed product, ", n, " variables, shape ", shape))
            c.check(b.mul(a, work) == expected, "packed product commutes")
            c.check(a.mul(a, work) == _heap_product(a, a, work), "packed square")
    # Exponents beyond the packed key range use the heap.
    var order = MonomialOrder(MonomialOrder.LEX, [Int64(0), Int64(1), Int64(2)], work)
    var a = dense_block[C](ctx, order, rng, 3, 8, 1, 10, work)
    var wide = Monomial([(Int64(0), UInt32(1 << 21)), (Int64(1), UInt32(1 << 21)), (Int64(2), UInt32(1 << 21))], work)
    var terms: List[Term[C]] = [Term[C](wide^, C.one(ctx))]
    a = a.add(SparsePoly[C].from_terms(terms^, order, ctx, work), work)
    c.check(a.mul(a, work) == _heap_product(a, a, work), "wide exponents fall back to the heap")


def main() raises:
    var c = Checker("sparse products")
    var work = Budget()
    products(ZZ(Integer(1) << 127), c)
    products(QQ(Rational(1, 1009)), c)
    products(ModInt(1, Modulus(2, work)), c)
    products(ModInt(1, Modulus(101, work)), c)
    packed[ZZ](NoContext(), c)
    packed[ModInt](Modulus(101, work), c)
    packed[ModInt](Modulus((UInt64(1) << 62) - 57, work), c)
    c.finish()
