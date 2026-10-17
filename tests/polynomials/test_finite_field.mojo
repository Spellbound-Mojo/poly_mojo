"""Corpus factors and exhaustive small-field irreducibles across explicit seeds."""
from polynomials import Budget, PolyErrorKind, ModInt, Modulus, DensePoly, MonomialOrder, factor_mod_p, divmod
from polynomials.finite_field import factor_finite_field
from support.corpus import read_cases, parse_polynomial, as_mod
from support.check import Checker
from polynomials._nmod import _field, _to, _modulus, _Modulus, _rem, _mulmod, _composer, _Composer, _compose


def exhaustive(prime: UInt64, mut c: Checker) raises:
    var work = Budget()
    var ctx = Modulus(prime, work)
    var irreducibles = List[DensePoly[ModInt]]()
    var extent = Int(prime)
    for degree in range(1, 4):
        for code in range(extent):
            var values = List[ModInt]()
            var digits = code
            for _ in range(degree):
                values.append(ModInt(UInt64(digits % Int(prime)), ctx))
                digits //= Int(prime)
            values.append(ModInt.one(ctx))
            var candidate = DensePoly[ModInt].from_coefficients(0, ctx, values^, work)
            var irreducible = True
            # Every reducible quadratic or cubic has a linear factor.
            if degree > 1:
                for root in range(Int(prime)):
                    var value = UInt64(0)
                    for i in range(degree, -1, -1):
                        value = (value * UInt64(root) + candidate.coefficients[i].value) % prime
                    if value == 0:
                        irreducible = False
            if irreducible:
                irreducibles.append(candidate^)
        extent *= Int(prime)
    for i in range(len(irreducibles)):
        var j = (i + 1) % len(irreducibles)
        var product = irreducibles[i].mul(irreducibles[j], work)
        for seed in range(3):
            var got = factor_mod_p(product, work, UInt64(seed))
            c.check(len(got) == 2, "two planted irreducibles")
            c.check((got[0] == irreducibles[i] and got[1] == irreducibles[j]) or (got[1] == irreducibles[i] and got[0] == irreducibles[j]), "exhaustively verified irreducibles recovered")
    var one = DensePoly[ModInt].from_coefficients(0, ctx, [ModInt.one(ctx)], work)
    c.check(len(factor_mod_p(one, work, 0)) == 0, "one has no factors")
    var repeated = irreducibles[0].pow(2, work)
    try:
        _ = factor_mod_p(repeated, work, 0)
        c.check(False, "repeated factor accepted")
    except e:
        c.check(e.kind == PolyErrorKind.DOMAIN, "repeated factor DOMAIN")
    var zero = DensePoly[ModInt](0, ctx)
    try:
        _ = factor_mod_p(zero, work, 0)
        c.check(False, "zero accepted")
    except e:
        c.check(e.kind == PolyErrorKind.DOMAIN, "zero DOMAIN")
    if prime > 2:
        var nonmonic = one.scale(ModInt(2, ctx), work)
        try:
            _ = factor_mod_p(nonmonic, work, 0)
            c.check(False, "nonmonic accepted")
        except e:
            c.check(e.kind == PolyErrorKind.DOMAIN, "nonmonic DOMAIN")
    var before = repeated.copy()
    var tiny = Budget(5)
    try:
        _ = factor_mod_p(repeated, tiny, 0)
        c.check(False, "budget ignored")
    except e:
        c.check(e.kind == PolyErrorKind.LIMIT and repeated == before, "finite field budget preserves input")


def large_prime(mut c: Checker) raises:
    # Native residues: planted linear and quadratic factors over 2^61 - 1, and
    # seed-independent factor sets for random inputs over a 62-bit prime.
    var work = Budget()
    var prime = UInt64(2305843009213693951)
    var ctx = Modulus(prime, work)
    var expected = List[DensePoly[ModInt]]()
    for i in range(40):
        var root = (UInt64(i) * UInt64(0x9E3779B97F4A7C15)) % prime
        expected.append(DensePoly[ModInt].from_coefficients(0, ctx, [ModInt(prime - root, ctx), ModInt.one(ctx)], work))
    var r = UInt64(3)
    while True:
        var e = (prime - 1) // 2
        var base = r
        var power = UInt64(1)
        while e:
            if e & 1:
                power = UInt64((UInt128(power) * UInt128(base)) % UInt128(prime))
            base = UInt64((UInt128(base) * UInt128(base)) % UInt128(prime))
            e >>= 1
        if power == prime - 1:
            break
        r += 1
    expected.append(DensePoly[ModInt].from_coefficients(0, ctx, [ModInt(prime - r, ctx), ModInt.zero(ctx), ModInt.one(ctx)], work))
    var product = DensePoly[ModInt].from_coefficients(0, ctx, [ModInt.one(ctx)], work)
    for g in expected:
        product = product.mul(g, work)
    var got = factor_mod_p(product, work, 0)
    c.check(len(got) == len(expected), "planted factors over 2^61 - 1")
    for g in expected:
        var found = False
        for h in got:
            if h == g:
                found = True
        c.check(found, "planted factor recovered over 2^61 - 1")
    var big = UInt64(4611686018427387847)
    var bctx = Modulus(big, work)
    var state = UInt64(12345)
    for degree in [37, 120]:
        var values = List[ModInt]()
        for _ in range(degree):
            state = state * 6364136223846793005 + 1442695040888963407
            values.append(ModInt(state >> 2, bctx))
        values.append(ModInt.one(bctx))
        var f = DensePoly[ModInt].from_coefficients(0, bctx, values^, work)
        var first = factor_mod_p(f, work, 0)
        var rebuilt = DensePoly[ModInt].from_coefficients(0, bctx, [ModInt.one(bctx)], work)
        for g in first:
            rebuilt = rebuilt.mul(g, work)
        c.check(rebuilt == f, "62-bit prime factor product")
        for seed in range(1, 3):
            c.check(factor_mod_p(f, work, UInt64(seed)) == first, "62-bit prime factors are seed independent")


def _power_mod(a: UInt64, e: UInt64, p: UInt64) -> UInt64:
    var result = UInt64(1)
    var base = a % p
    var n = e
    while n:
        if n & 1:
            result = UInt64((UInt128(result) * UInt128(base)) % UInt128(p))
        base = UInt64((UInt128(base) * UInt128(base)) % UInt128(p))
        n >>= 1
    return result


def draw(length: Int, monic: Bool, prime: UInt64, mut state: UInt64) raises -> List[UInt64]:
    """Random native residues modulo prime, trimmed, optionally with a leading one."""
    var field = _field(prime)
    var out = List[UInt64]()
    for _ in range(length):
        state = state * 6364136223846793005 + 1442695040888963407
        out.append(_to((state >> 17) % prime, field))
    if monic:
        out.append(_to(1, field))
    while len(out) and out[len(out) - 1] == 0:
        _ = out.pop()
    return out^


def spectral_kernels(mut c: Checker) raises:
    """Reductions, products and compositions kept in transform space agree with the plain kernels."""
    var work = Budget()
    var state = UInt64(98765)
    var primes: List[UInt64] = [3, 65521, 1000003]
    for prime in primes:
        var field = _field(prime)
        var n = 300

        var f = draw(n, True, prime, state)
        var m = _modulus(f, field, work)
        c.check(Bool(m.spectra), "the modulus keeps transforms")
        var plain = _Modulus(m.f.copy(), m.inverse.copy(), None)
        var a = draw(2 * n - 1, False, prime, state)
        c.check(_rem(a, m, field, work) == _rem(a, plain, field, work), "transform reduction matches the plain one")
        var x = draw(n, False, prime, state)
        var y = draw(n, False, prime, state)
        c.check(_mulmod(x, y, m, field, work) == _mulmod(x, y, plain, field, work), "transform modular product matches the plain one")
        var composer = _composer(draw(n, False, prime, state), m, field, work)
        c.check(Bool(composer.spectra), "the composer keeps transforms")
        var flat = _Composer(composer.block, composer.columns.copy(), composer.giants.copy(), None)
        var g = draw(n, False, prime, state)
        c.check(_compose(g, composer, m, field, work) == _compose(g, flat, plain, field, work), "transform composition matches the plain one")


def small_field_products(mut c: Checker) raises:
    """Degree-400 inputs over GF(3) and GF(5), factored through the 32-bit transforms: products rebuild the input, seed independently."""
    var work = Budget()
    var state = UInt64(4242)
    var primes: List[UInt64] = [3, 5]
    for prime in primes:
        var ctx = Modulus(prime, work)
        var values = List[ModInt]()
        for _ in range(400):
            state = state * 6364136223846793005 + 1442695040888963407
            values.append(ModInt((state >> 33) % prime, ctx))
        values.append(ModInt.one(ctx))
        var f = DensePoly[ModInt].from_coefficients(0, ctx, values^, work)
        var first = factor_finite_field(f, work, 0)
        var rebuilt = DensePoly[ModInt].from_coefficients(0, ctx, [first.unit.copy()], work)
        for entry in first.factors:
            for _ in range(entry[1]):
                rebuilt = rebuilt.mul(entry[0], work)
        c.check(rebuilt == f, "small-field factor product")
        var again = factor_finite_field(f, work, 1)
        var same = len(again.factors) == len(first.factors)
        if same:
            for i in range(len(first.factors)):
                same = same and again.factors[i][0] == first.factors[i][0] and again.factors[i][1] == first.factors[i][1]
        c.check(same, "small-field factors are seed independent")


def planted_binomials(mut c: Checker) raises:
    """Degree 280 over GF(65521) from planted irreducibles: distinct linears and x^r - a for primes r | p - 1 with a no r-th power."""
    var work = Budget()
    var prime = UInt64(65521)
    var ctx = Modulus(prime, work)
    var expected = List[DensePoly[ModInt]]()
    for i in range(130):
        expected.append(DensePoly[ModInt].from_coefficients(0, ctx, [ModInt(prime - UInt64(7 * i + 1), ctx), ModInt.one(ctx)], work))
    for pair in [(2, 20), (3, 10), (5, 6), (7, 4), (13, 2)]:
        var r = pair[0]
        var found = 0
        var a = UInt64(2)
        while found < pair[1]:
            if _power_mod(a, (prime - 1) // UInt64(r), prime) != 1:
                var values = List[ModInt]()
                values.append(ModInt(prime - a, ctx))
                for _ in range(1, r):
                    values.append(ModInt.zero(ctx))
                values.append(ModInt.one(ctx))
                expected.append(DensePoly[ModInt].from_coefficients(0, ctx, values^, work))
                found += 1
            a += 1
    var product = DensePoly[ModInt].from_coefficients(0, ctx, [ModInt.one(ctx)], work)
    var degree = 0
    for g in expected:
        product = product.mul(g, work)
        degree += g.degree()
    c.check(degree == 130 + 40 + 30 + 30 + 28 + 26, "planted degree")
    var got = factor_mod_p(product, work, 0)
    c.check(len(got) == len(expected), "planted irreducibles over GF(65521) all split off")
    var all = True
    for g in expected:
        var hit = False
        for h in got:
            if h == g:
                hit = True
        all = all and hit
    c.check(all, "planted irreducibles over GF(65521) recovered")
    for seed in range(1, 3):
        c.check(factor_mod_p(product, work, UInt64(seed)) == got, "planted factors are seed independent")


def main() raises:
    var work = Budget()
    var c = Checker("finite_field")
    var count = 0
    for record in read_cases():
        if record.field("op ") != "factor_mod_p":
            continue
        var ring = record.field("ring ")
        var ctx = Modulus(UInt64(Int(ring[byte=3:])), work)
        var input_text = record.field("in f ")
        var parsed = parse_polynomial(input_text, MonomialOrder(), work)
        var f = DensePoly[ModInt].from_sparse(as_mod(parsed, ctx, work), work)
        var expected = List[DensePoly[ModInt]]()
        for line in record.lines:
            if line.startswith("out factor "):
                var text = String(line[byte=11:])
                var p = parse_polynomial(text, MonomialOrder(), work)
                expected.append(DensePoly[ModInt].from_sparse(as_mod(p, ctx, work), work))
        for seed in range(4):
            var got = factor_mod_p(f, work, UInt64(seed))
            c.check(got == expected, record.name)
            var product = DensePoly[ModInt].from_coefficients(0, ctx, [ModInt.one(ctx)], work)
            for g in got:
                product = product.mul(g, work)
                g.check_invariants(work)
            c.check(product == f, "factor product")
        count += 1
    c.check(count == 11, "all eleven finite-field cases")
    exhaustive(2, c)
    exhaustive(3, c)
    exhaustive(5, c)
    large_prime(c)
    spectral_kernels(c)
    small_field_products(c)
    planted_binomials(c)
    c.finish()
