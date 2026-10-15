"""Independent ordering corpus, order laws, and monomial boundary failures."""
from polynomials import Budget, PolyErrorKind, Monomial, MonomialOrder
from support.check import Checker
from support.corpus import read_cases, parse_order, parse_monomial, parse_polynomial
from support.rng import SplitMix64

def generated(mut rng: SplitMix64, mut work: Budget) raises -> Monomial:
    var pairs = List[Tuple[Int64, UInt32]]()
    for i in range(4):
        var e = UInt32(rng.below(5))
        if e:
            pairs.append((Int64(i), e))
    return Monomial(pairs^, work)

def dense_divides(a: Monomial, b: Monomial, mut work: Budget) raises -> Bool:
    for i in range(4):
        if a.exponent(Int64(i), work) > b.exponent(Int64(i), work):
            return False
    return True

def main() raises:
    var c = Checker("monomials")
    var work = Budget()
    var count = 0
    var cases = read_cases()
    c.check(len(cases) == 189, "complete reference corpus")
    for row in cases:
        if row.field("op ") != "compare":
            continue
        var order = parse_order(row.field("order "), work)
        var a = parse_monomial(row.field("in a "), work)
        var b = parse_monomial(row.field("in b "), work)
        var polynomial_a = parse_polynomial(row.field("in a "), order, work)
        c.check(len(polynomial_a.terms) == 1 and polynomial_a.terms[0].monomial == a, "corpus polynomial parser")
        var expected = Int(row.field("out compare "))
        c.check(order.compare(a, b, work) == expected, row.name)
        count += 1
    c.check(count == 45, "all 45 ordering cases executed")
    var rng = SplitMix64(77)
    for kind in range(1, 4):
        var order = MonomialOrder(UInt8(kind), [1, 0, 2, 3], work)
        for _ in range(100):
            var a = generated(rng, work)
            var b = generated(rng, work)
            var d = generated(rng, work)
            var ab = order.compare(a, b, work)
            c.check(ab == -order.compare(b, a, work), "antisymmetry")
            c.check(order.compare(a, a, work) == 0, "reflexivity")
            var keys = Dict[Monomial, Int]()
            keys[a.copy()] = 7
            c.check(keys[a.copy()] == 7 and hash(a) == hash(a.copy()), "canonical hash and dictionary lookup")
            c.check(order.compare(Monomial(), a, work) <= 0, "unit least")
            c.check(order.compare(a.mul(d, work), b.mul(d, work), work) == ab, "multiplicativity")
            if ab <= 0 and order.compare(b, d, work) <= 0:
                c.check(order.compare(a, d, work) <= 0, "transitivity")
            var product = a.mul(b, work)
            c.check(a.divides(product, work) and product.div(a, work) == b, "division identity")
            var common = a.lcm(b, work)
            c.check(a.divides(common, work) and b.divides(common, work), "lcm multiple")
            c.check(common.divides(product, work), "lcm divides product")
            c.check(product.degree(work) == a.degree(work) + b.degree(work), "total degree")
    # Orders over variables 0..n-1 compare in one merge pass. An unused extra
    # variable keeps the same priorities but forces the per-variable path.
    for kind in range(1, 4):
        var direct = MonomialOrder(UInt8(kind), [0, 1, 2, 3], work)
        var general = MonomialOrder(UInt8(kind), [0, 1, 2, 3, 9], work)
        for _ in range(300):
            var a = generated(rng, work)
            var b = generated(rng, work)
            c.check(direct.compare(a, b, work) == general.compare(a, b, work), "merge comparison matches per-variable comparison")
            c.check(a.divides(b, work) == dense_divides(a, b, work), "divisibility matches exponentwise comparison")
            if a.divides(b, work):
                c.check(b.div(a, work).mul(a, work) == b, "exact quotient")
    var x = Monomial([(Int64(0), UInt32(1))], work)
    var y = Monomial([(Int64(1), UInt32(1))], work)
    var kernel = MonomialOrder()
    c.check(kernel.compare(x, y, work) < 0, "kernel pair order")
    c.check(kernel.compare(x.mul(x, work), y.mul(x, work), work) > 0, "kernel not multiplicative")
    for i in range(1, 15):
        c.check(kernel.compare(Monomial([(Int64(-i), UInt32(1))], work), Monomial([(Int64(-i - 1), UInt32(1))], work), work) > 0, "kernel descending indices")
    for scenario in range(5):
        try:
            if scenario == 0:
                _ = Monomial([(Int64(1), UInt32(0))], work)
            elif scenario == 1:
                _ = Monomial([(Int64(1), UInt32(2)), (Int64(1), UInt32(1))], work)
            elif scenario == 2:
                _ = x.div(y, work)
            elif scenario == 3:
                _ = MonomialOrder(MonomialOrder.LEX, [0, 0], work)
            else:
                var order = MonomialOrder(MonomialOrder.LEX, [0], work)
                _ = order.compare(x, y, work)
            c.check(False, "invalid monomial/domain accepted")
        except e:
            c.check(e.kind == PolyErrorKind.DOMAIN, "typed domain rejection")
    var huge = Monomial([(Int64(0), UInt32.MAX)], work)
    try:
        _ = huge.mul(x, work)
        c.check(False, "exponent wrapped")
    except e:
        c.check(e.kind == PolyErrorKind.CAPACITY, "exponent overflow")
    var empty = Budget(0)
    try:
        _ = x.mul(y, empty)
        c.check(False, "unbudgeted monomial product")
    except e:
        c.check(e.kind == PolyErrorKind.LIMIT, "monomial budget")
    c.check(x.pairs[0][1] == 1, "failure preserves input")
    c.finish()
