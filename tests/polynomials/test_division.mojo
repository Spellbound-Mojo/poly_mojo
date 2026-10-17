"""Division identities, independent corpus cases, and malformed certificates."""
from apn_mojo import Integer
from polynomials import Budget, PolyErrorKind, CoefficientRing, CoefficientField, ZZ, QQ, ModInt, Modulus, NoContext, MonomialOrder, DensePoly, SparsePoly, Term, Monomial
from polynomials.division import divmod, pseudo_divmod, divide_exact, divide_by_list
from polynomials.certificates import check_division, check_list_division
from polynomials.coefficients import _pow
from support.check import Checker
from support.gen import coefficient, polynomial
from support.rng import SplitMix64
from support.corpus import read_cases, parse_polynomial, as_zz

def check_ring[C: CoefficientRing](ctx: C.Context, mut c: Checker) raises:
    var work = Budget()
    var rng = SplitMix64(772)
    var order = MonomialOrder(MonomialOrder.GREVLEX, [0, 1, 2], work)
    for i in range(35):
        var a = polynomial[C](ctx, order, rng, work, terms=3, variables=3, degree=2)
        var b = polynomial[C](ctx, order, rng, work, terms=3, variables=3, degree=2)
        if b.is_zero():
            continue
        var product = a.mul(b, work)
        var exact = divide_exact(product, b, work)
        c.check(Bool(exact) and exact.value() == a, "exact generated product")
        var stored = divide_exact(product.reorder(MonomialOrder(), work), b.reorder(MonomialOrder(), work), work)
        c.check(Bool(stored) and stored.value() == a.reorder(MonomialOrder(), work), "exact division in storage order")
        var da = List[C]()
        var db = List[C]()
        for _ in range(i % 9):
            da.append(coefficient[C](ctx, rng.below(11) - 5, work))
        for _ in range(i % 5):
            db.append(coefficient[C](ctx, rng.below(11) - 5, work))
        db.append(C.one(ctx).add(C.one(ctx), work))
        var f = DensePoly[C].from_coefficients(0, ctx, da^, work)
        var g = DensePoly[C].from_coefficients(0, ctx, db^, work)
        var result = pseudo_divmod(f, g, work)
        var scaled = f.scale(_pow(g.coefficients[len(g.coefficients) - 1], UInt64(max(f.degree() - g.degree() + 1, 0)), work), work)
        c.check(check_division(scaled, g, result, work), "pseudo division identity and degree")
        comptime if conforms_to(C, CoefficientField):
            var ordinary = divmod(f, g, work)
            c.check(check_division(f, g, ordinary, work), "field division identity and degree")
            ordinary.remainder = ordinary.remainder.add(DensePoly[C].from_coefficients(0, ctx, [C.one(ctx)], work), work)
            c.check(not check_division(f, g, ordinary, work), "corrupt division rejected")
            var divisors: List[SparsePoly[C]] = [a.copy(), b.copy()]
            if not a.is_zero():
                var listing = divide_by_list(product.add(a, work), divisors, work)
                c.check(check_list_division(product.add(a, work), divisors, listing, work), "list division identity")
                for term in listing.remainder.terms:
                    for divisor in divisors:
                        c.check(not divisor.leading(work).monomial.divides(term.monomial, work), "list remainder irreducible")
                listing.remainder = listing.remainder.add(SparsePoly[C].constant(C.one(ctx), order, work), work)
                c.check(not check_list_division(product.add(a, work), divisors, listing, work), "corrupt list division rejected")
    var zero = SparsePoly[C].zero(order, ctx, work)
    var one = SparsePoly[C].constant(C.one(ctx), order, work)
    var x = SparsePoly[C].variable(0, order, ctx, work)
    c.check(not divide_exact(one, x, work), "nonmultiple refused")
    c.check(divide_exact(zero, x, work).value().is_zero(), "zero quotient")
    try:
        _ = divide_exact(one, zero, work)
        c.check(False, "zero exact divisor accepted")
    except e:
        c.check(e.kind == PolyErrorKind.DOMAIN, "zero divisor DOMAIN")
    var tiny = Budget(0)
    try:
        _ = divide_exact(x, one, tiny)
        c.check(False, "exact division ignored budget")
    except e:
        c.check(e.kind == PolyErrorKind.LIMIT, "division budget exhaustion")

def word[C: CoefficientRing](ctx: C.Context, x: Int64) -> C:
    comptime if C == ZZ:
        return rebind_var[C](ZZ(Integer(x)))
    else:
        var p = rebind[Modulus](ctx).value
        var r = UInt64(x) % p if x >= 0 else p - UInt64(-x) % p
        return rebind_var[C](ModInt(r, rebind[Modulus](ctx)))


def block[C: CoefficientRing](ctx: C.Context, order: MonomialOrder, mut rng: SplitMix64, n: Int, degree: Int, scale: Int, bits: Int, mut work: Budget) raises -> SparsePoly[C]:
    """Random terms of degree below `degree` in each of n variables, exponents scaled by `scale`."""
    var terms = List[Term[C]]()
    var count = 1
    for _ in range(n):
        count *= degree
    for index in range(count):
        if index != count - 1 and rng.below(4) == 0:
            continue
        var pairs = List[Tuple[Int64, UInt32]]()
        var rest = index
        for i in range(n):
            var e = rest % degree
            rest //= degree
            if e:
                pairs.append((Int64(i), UInt32(e * scale)))
        var magnitude = Int64(rng.next() >> UInt64(64 - bits)) | 1
        terms.append(Term[C](Monomial(pairs^, work), word[C](ctx, -magnitude if rng.below(2) else magnitude)))
    return SparsePoly[C].from_terms(terms^, order, ctx, work)


def agrees[C: CoefficientRing](f: SparsePoly[C], g: SparsePoly[C], mut c: Checker, label: String) raises:
    """The fast quotient (or refusal) matches the general algorithm, which storage order selects."""
    var work = Budget()
    var fast = divide_exact(f, g, work)
    var general = divide_exact(f.reorder(MonomialOrder(), work), g.reorder(MonomialOrder(), work), work)
    c.check(Bool(fast) == Bool(general), label + ": divisibility")
    if Bool(fast) and Bool(general):
        c.check(fast.value().reorder(MonomialOrder(), work) == general.value(), label + ": quotient")
        c.check(fast.value().mul(g, work) == f, label + ": quotient times divisor")


def fast_division[C: CoefficientRing](ctx: C.Context, mut c: Checker) raises:
    var work = Budget()
    var rng = SplitMix64(9001)
    for n in [1, 2, 3, 4]:
        var variables = List[Int64]()
        for i in range(n):
            variables.append(Int64(i))
        var order = MonomialOrder(MonomialOrder.LEX, variables^, work)
        for shape in range(3):
            # Shapes: small coefficients; spread exponents that split the window; 40-bit coefficients.
            var degree = [120, 12, 6, 4][n - 1]
            var a = block[C](ctx, order, rng, n, degree, 37 if shape == 1 else 1, 40 if shape == 2 else 12, work)
            var b = block[C](ctx, order, rng, n, max(2, degree - 1), 37 if shape == 1 else 1, 40 if shape == 2 else 12, work)
            var product = a.mul(b, work)
            var q = divide_exact(product, b, work)
            c.check(Bool(q) and q.value() == a, String("fast exact quotient, ", n, " variables, shape ", shape))
            var r = divide_exact(product, a, work)
            c.check(Bool(r) and r.value() == b, "fast exact quotient by the other factor")
            var shifted = product.add(SparsePoly[C].variable(0, order, ctx, work), work)
            agrees(shifted, b, c, "fast refusal of a non-multiple")
            # A divisor whose leading coefficient does not divide the quotient's coefficients.
            var tripled = b.scale(word[C](ctx, 3), work)
            agrees(product, tripled, c, "non-unit divisor content")
    # Sparse operands with few colliding products: the packed chunks decline and the heap divides.
    var spread = MonomialOrder(MonomialOrder.LEX, [Int64(0), Int64(1), Int64(2), Int64(3), Int64(4)], work)
    var sa = polynomial[C](ctx, spread, rng, work, terms=60, variables=5, degree=20, coefficient_bound=1000)
    var sb = polynomial[C](ctx, spread, rng, work, terms=60, variables=5, degree=20, coefficient_bound=1000)
    if not sb.is_zero():
        agrees(sa.mul(sb, work), sb, c, "sparse quotient through the heap")
        agrees(sa.mul(sb, work).add(SparsePoly[C].variable(0, spread, ctx, work), work), sb, c, "sparse refusal through the heap")
    # Quotient coefficients wider than a word, and wide dividend coefficients.
    var order = MonomialOrder(MonomialOrder.LEX, [Int64(0), Int64(1)], work)
    var a = block[C](ctx, order, rng, 2, 12, 1, 12, work)
    var b = block[C](ctx, order, rng, 2, 11, 1, 12, work)
    comptime if C == ZZ:
        a = a.scale(rebind_var[C](ZZ(Integer(1) << 70)), work)
    agrees(a.mul(b, work), b, c, "wide quotient coefficients")
    comptime if C == ZZ:
        # Dividend coefficients of about 134 bits: 1024 colliding products of 62-bit coefficients.
        var square = List[Term[C]]()
        for i in range(32):
            for j in range(32):
                var pairs = List[Tuple[Int64, UInt32]]()
                if i:
                    pairs.append((Int64(0), UInt32(i)))
                if j:
                    pairs.append((Int64(1), UInt32(j)))
                square.append(Term[C](Monomial(pairs^, work), word[C](ctx, Int64((1 << 62) - 1))))
        var u = SparsePoly[C].from_terms(square^, order, ctx, work)
        var v = u.add(SparsePoly[C].variable(1, order, ctx, work), work)
        var wide_product = u.mul(v, work)
        var wide_q = divide_exact(wide_product, v, work)
        c.check(Bool(wide_q) and wide_q.value() == u, "fast quotient of a dividend wider than 127 bits")
        c.check(not divide_exact(wide_product.add(SparsePoly[C].variable(0, order, ctx, work), work), v, work), "fast refusal with a wide dividend")
    var dense = MonomialOrder(MonomialOrder.LEX, [Int64(0)], work)
    var big_a = block[C](ctx, dense, rng, 1, 150, 1, 63, work)
    var big_b = block[C](ctx, dense, rng, 1, 90, 1, 63, work)
    comptime if C == ZZ:
        big_a = big_a.mul(big_a, work).mul(big_a, work)
    agrees(big_a.mul(big_b, work), big_b, c, "dense quotient with wide coefficients")


def main() raises:
    var work = Budget()
    var c = Checker("division")
    fast_division[ZZ](NoContext(), c)
    fast_division[ModInt](Modulus(101, work), c)
    fast_division[ModInt](Modulus((UInt64(1) << 62) - 57, work), c)
    fast_division[ModInt](Modulus(4611685941117976577, work), c)
    check_ring[ZZ](NoContext(), c)
    check_ring[QQ](NoContext(), c)
    check_ring[ModInt](Modulus(101, work), c)
    var count = 0
    for record in read_cases():
        var op = record.field("op ")
        if op != "divmod" and op != "pseudo_divmod":
            continue
        var order = MonomialOrder()
        var ftext = record.field("in f ")
        var gtext = record.field("in g ")
        var qtext = record.field("out quotient ")
        var rtext = record.field("out remainder ")
        var f = parse_polynomial(ftext, order, work)
        var g = parse_polynomial(gtext, order, work)
        var q = parse_polynomial(qtext, order, work)
        var r = parse_polynomial(rtext, order, work)
        if op == "divmod":
            var got = divmod(DensePoly[QQ].from_sparse(f, work), DensePoly[QQ].from_sparse(g, work), work)
            c.check(got.quotient.to_sparse(order, work) == q and got.remainder.to_sparse(order, work) == r, record.name)
        else:
            var fz = as_zz(f, work)
            var gz = as_zz(g, work)
            var qz = as_zz(q, work)
            var rz = as_zz(r, work)
            var got = pseudo_divmod(DensePoly[ZZ].from_sparse(fz, work), DensePoly[ZZ].from_sparse(gz, work), work)
            c.check(got.quotient.to_sparse(order, work) == qz and got.remainder.to_sparse(order, work) == rz, record.name)
        count += 1
    c.check(count == 8, "all eight division corpus cases")
    c.finish()
