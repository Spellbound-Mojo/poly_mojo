"""Exact zero-reduction checks by F4 matrices over the integers.

Certifying a reconstructed rational basis reduces every S-pair in a dense row
of fixed-width two's complement limbs. The row's arithmetic must agree with
`Integer` arithmetic through sums, differences, and scalings that change
signs and outgrow the width; and the check must accept exactly the
candidates that are Gröbner bases. A candidate G is one exactly when every
leading monomial of the reduced basis of <G> is divisible by one of G's, which
the library's own Gröbner computation decides independently.
"""
from std.math import max
from apn_mojo import Integer, Rational, div_rem_euclid, div_rem_trunc
from polynomials import Budget, QQ, ZZ, NoContext, SparsePoly, Term, Monomial, MonomialOrder, groebner
from polynomials._integer_f4 import _IFMA, _PAD, _Row, _accumulate, _append_digits, _bits, _divide_exact, _divide_exact_limbs, _ifma, _limbs_of, _pair_routes, _pairs_reduce_to_zero, _Routes, _shift_out
from polynomials._packed_groebner import _Engine, _Term, _divides, _pack
from polynomials._rational_groebner import _integral
from support.check import Checker
from support.rng import SplitMix64


def random_magnitude(mut rng: SplitMix64, limbs: Int) raises -> Integer:
    var x = Integer(0)
    var base = Integer(1) << Integer(64)
    for _ in range(limbs):
        x = x * base + Integer(rng.next())
    return x


def check_row(mut c: Checker, mut work: Budget) raises:
    """Row entries against Integers under random updates, scalings, and resets."""
    var rng = SplitMix64(41)
    var n = 6
    var row = _Row(n)
    row.prepare(64, work)
    var expected = List[Integer](length=n, fill=Integer(0))
    for step in range(1200):
        var kind = rng.below(10)
        var column = rng.below(n)
        if kind < 6:
            # Mostly short factors, sometimes long enough for column sums.
            var long = step % 4 == 0
            var factor = random_magnitude(rng, Int(rng.below(36 if long else 12)) + 1)
            var term = random_magnitude(rng, Int(rng.below(36 if long else 12)) + 1)
            var f = _limbs_of(factor)
            var t = _limbs_of(term)
            var bits = _bits(f) + _bits(t)
            row.room_for_sum(bits, work)
            if kind < 3:
                row.add_product(column, f, t, 0, len(t), bits)
                expected[column] = expected[column] + factor * term
            else:
                row.subtract_product(column, f, t, 0, len(t), bits)
                expected[column] = expected[column] - factor * term
        elif kind < 8:
            # Now and then long enough for the digit products, where there are some.
            var factor = random_magnitude(rng, Int(rng.below(16 if step % 5 == 0 else 4)) + 1) + Integer(1)
            var first = rng.below(n)
            var f = _limbs_of(factor)
            row.room_for_scale(_bits(f), work)
            row.scale(first, f, _bits(f))
            for k in range(first, n):
                expected[k] = expected[k] * factor
        else:
            row.set_zero(column)
            expected[column] = Integer(0)
        for k in range(n):
            c.check(row.value(k) == expected[k], "row entry " + String(k) + " after step " + String(step))
            c.check(row.is_zero(k) == (expected[k].sign() == 0), "zero test of entry " + String(k))


def limbs_value(limbs: List[UInt64]) raises -> Integer:
    var x = Integer(0)
    for l in range(len(limbs) - 1, -1, -1):
        x = (x << Integer(64)) + Integer(limbs[l])
    return x


def check_accumulate(mut c: Checker) raises:
    """Entry updates against Integers modulo 2^(64 width), through every kernel and with truncation."""
    var rng = SplitMix64(13)
    for step in range(400):
        var na = Int(rng.below(40)) + 1
        var nb = Int(rng.below(40)) + 1
        if step % 4 == 0:
            na = Int(rng.below(3)) + 1
        var width = Int(rng.below(na + nb + 3)) + 1
        var a = List[UInt64](length=na, fill=0)
        var b = List[UInt64](length=nb, fill=0)
        var data = List[UInt64](length=width, fill=0)
        # All-ones limbs now and then, for the longest carries.
        var ones = step % 5 == 0
        for i in range(na):
            a[i] = UInt64.MAX if ones else rng.next()
        for i in range(nb):
            b[i] = UInt64.MAX if ones else rng.next()
        for i in range(width):
            data[i] = UInt64.MAX if ones else rng.next()
        var modulus = Integer(1) << Integer(64 * width)
        var product = limbs_value(a) * limbs_value(b)
        var subtract = rng.below(2) == 0
        var expected = limbs_value(data) - product if subtract else limbs_value(data) + product
        expected = div_rem_euclid(expected, modulus)[1]
        if subtract:
            _accumulate[True](data.unsafe_ptr(), width, a.unsafe_ptr(), na, b.unsafe_ptr(), nb)
        else:
            _accumulate[False](data.unsafe_ptr(), width, a.unsafe_ptr(), na, b.unsafe_ptr(), nb)
        c.check(limbs_value(data) == expected, "update " + String(step) + ": " + String(na) + " by " + String(nb) + " limbs into " + String(width))


def padded_digits(limbs: List[UInt64]) -> List[UInt64]:
    var digits = List[UInt64](length=_PAD, fill=0)
    _append_digits(limbs.unsafe_ptr(), len(limbs), digits)
    for _ in range(_PAD):
        digits.append(0)
    return digits^


def check_digit_products(mut c: Checker) raises:
    """Entry updates through 52-bit digit products, where the target has IFMA."""
    comptime if _IFMA:
        var rng = SplitMix64(19)
        for step in range(200):
            var na = Int(rng.below(60)) + 1
            var nb = Int(rng.below(120)) + 1
            var width = Int(rng.below(na + nb + 3)) + 1
            var ones = step % 5 == 0
            var a = List[UInt64](length=na, fill=0)
            var b = List[UInt64](length=nb, fill=0)
            var data = List[UInt64](length=width, fill=0)
            for i in range(na):
                a[i] = UInt64.MAX if ones else rng.next()
            for i in range(nb):
                b[i] = UInt64.MAX if ones else rng.next()
            for i in range(width):
                data[i] = UInt64.MAX if ones else rng.next()
            var x = padded_digits(a)
            var y = padded_digits(b)
            var dx = len(x) - 2 * _PAD
            var dy = len(y) - 2 * _PAD
            var low = List[UInt64](length=dx + dy + _PAD, fill=0)
            var high = List[UInt64](length=dx + dy + _PAD, fill=0)
            var modulus = Integer(1) << Integer(64 * width)
            var product = limbs_value(a) * limbs_value(b)
            var subtract = rng.below(2) == 0
            var expected = limbs_value(data) - product if subtract else limbs_value(data) + product
            expected = div_rem_euclid(expected, modulus)[1]
            var xs = x.unsafe_ptr().unsafe_offset(_PAD)
            var ys = y.unsafe_ptr().unsafe_offset(_PAD)
            # The shorter string first, as the kernel requires.
            if dx <= dy:
                if subtract:
                    _ifma[True](data.unsafe_ptr(), width, xs, dx, ys, dy, low.unsafe_ptr(), high.unsafe_ptr())
                else:
                    _ifma[False](data.unsafe_ptr(), width, xs, dx, ys, dy, low.unsafe_ptr(), high.unsafe_ptr())
            else:
                if subtract:
                    _ifma[True](data.unsafe_ptr(), width, ys, dy, xs, dx, low.unsafe_ptr(), high.unsafe_ptr())
                else:
                    _ifma[False](data.unsafe_ptr(), width, ys, dy, xs, dx, low.unsafe_ptr(), high.unsafe_ptr())
            c.check(limbs_value(data) == expected, "digit update " + String(step) + ": " + String(na) + " by " + String(nb) + " limbs into " + String(width))


def check_exact_division(mut c: Checker) raises:
    """Hensel division by word divisors: exact quotients, and refusals otherwise."""
    var rng = SplitMix64(11)
    for step in range(300):
        var d = UInt64(rng.next() >> UInt64(1 + rng.below(60)))
        if d == 0:
            d = 1
        var q = random_magnitude(rng, Int(rng.below(5)) + 1)
        var value = q * Integer(Int(d))
        if rng.below(2) == 0:
            value = value + Integer(rng.below(1000))
        var twos = 0
        var odd = d
        while (odd & 1) == 0:
            odd >>= 1
            twos += 1
        var inverse = odd
        for _ in range(5):
            inverse *= 2 - odd * inverse
        var limbs = _limbs_of(value)
        var qr = div_rem_trunc(value, Integer(Int(d)))
        var divisible = qr[1].sign() == 0
        var ok = _divide_exact(limbs, odd, twos, inverse)
        c.check(ok == divisible, "divisibility at step " + String(step))
        if ok and divisible:
            var expected = _limbs_of(qr[0])
            var same = len(limbs) == len(expected)
            for l in range(min(len(limbs), len(expected))):
                if limbs[l] != expected[l]:
                    same = False
            c.check(same, "quotient at step " + String(step))


def check_exact_division_limbs(mut c: Checker) raises:
    """Hensel division by multi-limb divisors, odd and even."""
    var rng = SplitMix64(17)
    for step in range(300):
        var d = random_magnitude(rng, Int(rng.below(6)) + 1) + Integer(1)
        if step % 3 == 0:
            d = d << Integer(Int(rng.below(150)))
        var value = random_magnitude(rng, Int(rng.below(8)) + 1) * d
        if rng.below(2) == 0:
            value = value + random_magnitude(rng, Int(rng.below(3)) + 1)
        var odd = _limbs_of(d)
        var twos = 0
        while odd[twos // 64] == 0:
            twos += 64
        var low = odd[twos // 64]
        while (low & 1) == 0:
            low >>= 1
            twos += 1
        _ = _shift_out(odd, twos)
        var inverse = odd[0]
        for _ in range(5):
            inverse *= 2 - odd[0] * inverse
        var limbs = _limbs_of(value)
        var qr = div_rem_trunc(value, d)
        var ok = _divide_exact_limbs(limbs, odd, twos, inverse)
        c.check(ok == (qr[1].sign() == 0), "multi-limb divisibility at step " + String(step))
        if ok:
            c.check(limbs_value(limbs) == qr[0], "multi-limb quotient at step " + String(step))


def packed(polys: List[SparsePoly[QQ]], order: MonomialOrder, mut work: Budget) raises -> List[List[_Term[ZZ, 8]]]:
    var result = List[List[_Term[ZZ, 8]]]()
    for p in polys:
        if not p.is_zero():
            result.append(_integral(_pack[QQ, 8](p.reorder(order, work), order, work), work))
    return result^


def engine_of(candidate: List[SparsePoly[QQ]], order: MonomialOrder, mut work: Budget) raises -> _Engine[ZZ, 8, True]:
    var engine = _Engine[ZZ, 8, True](order.kind, NoContext())
    for p in packed(candidate, order, work):
        var copy = List[_Term[ZZ, 8]]()
        for t in p:
            copy.append(_Term[ZZ, 8](t.monomial, ZZ(t.coefficient.value.copy())))
        engine.insert(copy^, work)
    return engine^


def routes(candidate: List[SparsePoly[QQ]], order: MonomialOrder, primes: Int, mut work: Budget) raises -> _Routes:
    var engine = engine_of(candidate, order, work)
    return _pair_routes(engine, work, primes)


def vanishes(candidate: List[SparsePoly[QQ]], order: MonomialOrder, mut work: Budget) raises -> Bool:
    """The matrix check on the candidate's pairs, which every prime budget decides alike."""
    var engine = engine_of(candidate, order, work)
    var zero = _pairs_reduce_to_zero(engine, work)
    for primes in [0, 8, 16]:
        if routes(candidate, order, primes, work).zero != zero:
            raise Error("prime budgets " + String(primes) + " and default disagree")
    return zero


def is_basis(candidate: List[SparsePoly[QQ]], order: MonomialOrder, mut work: Budget) raises -> Bool:
    """Whether the candidate's leading monomials generate those of its ideal."""
    var leads = packed(candidate, order, work)
    var reduced = groebner(candidate, order, work)
    for b in packed(reduced.basis, order, work):
        var covered = False
        for g in leads:
            if _divides(g[len(g) - 1].monomial, b[len(b) - 1].monomial):
                covered = True
        if not covered:
            return False
    return True


def mutually_nondividing(candidate: List[SparsePoly[QQ]], order: MonomialOrder, mut work: Budget) raises -> Bool:
    var polys = packed(candidate, order, work)
    for i in range(len(polys)):
        for j in range(len(polys)):
            if i != j and _divides(polys[i][len(polys[i]) - 1].monomial, polys[j][len(polys[j]) - 1].monomial):
                return False
    return True


def term(n: Int, exponents: List[Int], coefficient: Rational, order: MonomialOrder, mut work: Budget) raises -> SparsePoly[QQ]:
    var pairs = List[Tuple[Int64, UInt32]]()
    for i in range(n):
        if exponents[i]:
            pairs.append((Int64(i), UInt32(exponents[i])))
    var t = Term[QQ](Monomial(pairs^, work), QQ(coefficient.copy()))
    return SparsePoly[QQ].from_terms([t^], order, NoContext(), work)


def random_system(n: Int, count: Int, scale: Integer, seed: UInt64, order: MonomialOrder, mut work: Budget) raises -> List[SparsePoly[QQ]]:
    """Random quadratics in n variables, coefficients times `scale` plus small ones."""
    var rng = SplitMix64(seed)
    var polys = List[SparsePoly[QQ]]()
    for _ in range(count):
        var p = SparsePoly[QQ].zero(order, NoContext(), work)
        for i in range(n):
            for j in range(i, n):
                if rng.below(3) == 0:
                    continue
                var e = List[Int](length=n, fill=0)
                e[i] += 1
                e[j] += 1
                var value = Rational(Int(rng.below(9)) - 4) + Rational(scale.copy()) * Rational(Int(rng.below(3)))
                p = p.add(term(n, e, value, order, work), work)
            var e = List[Int](length=n, fill=0)
            e[i] = 1
            p = p.add(term(n, e, Rational(Int(rng.below(9)) - 4), order, work), work)
        polys.append(p^)
    return polys^


def perturbed(basis: List[SparsePoly[QQ]], which: Int, order: MonomialOrder, mut work: Budget) raises -> List[SparsePoly[QQ]]:
    """The basis with a tail term of element `which` changed, when it has one."""
    var result = List[SparsePoly[QQ]]()
    for i in range(len(basis)):
        if i == which and len(basis[i].terms) > 1:
            var terms = List[Term[QQ]]()
            for k in range(len(basis[i].terms)):
                var t = basis[i].terms[k].copy()
                if k == 0:
                    t = Term[QQ](t.monomial.copy(), QQ(t.coefficient.value + Rational(1)))
                terms.append(t^)
            result.append(SparsePoly[QQ].from_terms(terms^, order, NoContext(), work))
        else:
            result.append(basis[i].copy())
    return result^


def check_bases(mut c: Checker, mut work: Budget) raises:
    var o4 = MonomialOrder(MonomialOrder.GREVLEX, [0, 1, 2, 3], work)
    var o5 = MonomialOrder(MonomialOrder.GREVLEX, [0, 1, 2, 3, 4], work)
    var x = SparsePoly[QQ].variable(0, o4, NoContext(), work)
    var y = SparsePoly[QQ].variable(1, o4, NoContext(), work)
    var z = SparsePoly[QQ].variable(2, o4, NoContext(), work)
    # x^2 - y and x*y - z: the S-polynomial x*z - y^2 has no reducer.
    c.check(not vanishes([x.mul(x, work).sub(y, work), x.mul(y, work).sub(z, work)], o4, work), "a pair with a nonzero remainder")
    var big = Integer(10) ** 40
    var seed = UInt64(1)
    var rejected = 0
    for order in [o4.copy(), o5.copy()]:
        var n = len(order.variables)
        for scale in [Integer(0), big.copy()]:
            for _ in range(2):
                var system = random_system(n, n - 1, scale, seed, order, work)
                seed += 1
                var basis = groebner(system, order, work).basis.copy()
                c.check(vanishes(basis, order, work), "a reduced basis, " + String(n) + " variables")
                # Perturb a few elements, spread over the basis.
                for which in range(0, len(basis), max(1, len(basis) // 3)):
                    var candidate = perturbed(basis, which, order, work)
                    if not mutually_nondividing(candidate, order, work):
                        continue
                    var expected = is_basis(candidate, order, work)
                    if not expected:
                        rejected += 1
                    c.check(vanishes(candidate, order, work) == expected, "a perturbed basis, element " + String(which))
    c.check(rejected > 0, "some perturbed bases are not Groebner bases")
    # Coefficients of 13 limbs and more reach the digit products, with IFMA.
    var large = groebner(random_system(4, 3, Integer(10) ** 250, seed, o4, work), o4, work).basis.copy()
    c.check(vanishes(large, o4, work), "a reduced basis with long coefficients")
    # Small primes budgets leave the long pairs to the exact check; a large one proves them modularly.
    var few = routes(large, o4, 8, work)
    c.check(few.zero and few.exact > 0, "eight primes leave long pairs to the exact check")
    var many = routes(large, o4, 256, work)
    c.check(many.zero and many.modular > 0, "enough primes prove long pairs modularly")
    var none = routes(large, o4, 0, work)
    c.check(none.zero and none.modular == 0, "no primes prove every pair exactly")
    var small = routes(groebner(random_system(4, 3, Integer(0), seed, o4, work), o4, work).basis, o4, 128, work)
    c.check(small.zero and small.modular > 0, "short pairs are proved modularly")
    var broken = perturbed(large, len(large) - 1, o4, work)
    if mutually_nondividing(broken, o4, work):
        c.check(vanishes(broken, o4, work) == is_basis(broken, o4, work), "a perturbed basis with long coefficients")


def main() raises:
    var work = Budget()
    var c = Checker("integer f4")
    check_accumulate(c)
    check_digit_products(c)
    check_exact_division(c)
    check_exact_division_limbs(c)
    check_row(c, work)
    check_bases(c, work)
    c.finish()
