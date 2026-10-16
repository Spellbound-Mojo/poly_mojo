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
from apn_mojo import Integer, Rational
from polynomials import Budget, QQ, ZZ, NoContext, SparsePoly, Term, Monomial, MonomialOrder, groebner
from polynomials._integer_f4 import _Row, _bits, _limbs_of, _pairs_reduce_to_zero
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
            var factor = random_magnitude(rng, Int(rng.below(12)) + 1)
            var term = random_magnitude(rng, Int(rng.below(12)) + 1)
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
            var factor = random_magnitude(rng, Int(rng.below(4)) + 1) + Integer(1)
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


def packed(polys: List[SparsePoly[QQ]], order: MonomialOrder, mut work: Budget) raises -> List[List[_Term[ZZ, 8]]]:
    var result = List[List[_Term[ZZ, 8]]]()
    for p in polys:
        if not p.is_zero():
            result.append(_integral(_pack[QQ, 8](p.reorder(order, work), order, work), work))
    return result^


def vanishes(candidate: List[SparsePoly[QQ]], order: MonomialOrder, mut work: Budget) raises -> Bool:
    """The matrix check on the candidate's pairs."""
    var engine = _Engine[ZZ, 8, True](order.kind, NoContext())
    for p in packed(candidate, order, work):
        var copy = List[_Term[ZZ, 8]]()
        for t in p:
            copy.append(_Term[ZZ, 8](t.monomial, ZZ(t.coefficient.value.copy())))
        engine.insert(copy^, work)
    return _pairs_reduce_to_zero(engine, work)


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


def main() raises:
    var work = Budget()
    var c = Checker("integer f4")
    check_row(c, work)
    check_bases(c, work)
    c.finish()
