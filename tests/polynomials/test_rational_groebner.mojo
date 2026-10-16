"""Rational Gröbner bases under GREVLEX, by both of their routes.

Over QQ under GREVLEX the library homogenizes the inputs and computes exactly,
or, when coefficients grow large, reconstructs the basis from images modulo
primes and certifies it. Both routes, and the sparse engine that tracks
cofactors, must return the same reduced basis: for inhomogeneous and
homogeneous inputs, for the unit ideal, and for zero generators.
"""
from apn_mojo import Rational
from polynomials import Budget, QQ, NoContext, SparsePoly, Term, Monomial, MonomialOrder, groebner
from polynomials._rational_groebner import _grevlex_groebner_rational
from support.check import Checker
from support.groebner import verify_basis
from support.rng import SplitMix64


def term(n: Int, exponents: List[Int], coefficient: Int, order: MonomialOrder, mut work: Budget) raises -> SparsePoly[QQ]:
    var pairs = List[Tuple[Int64, UInt32]]()
    for i in range(n):
        if exponents[i]:
            pairs.append((Int64(i), UInt32(exponents[i])))
    var t = Term[QQ](Monomial(pairs^, work), QQ(Rational(coefficient)))
    return SparsePoly[QQ].from_terms([t^], order, NoContext(), work)


def unit(n: Int, i: Int, power: Int = 1) -> List[Int]:
    var e = List[Int](length=n, fill=0)
    e[i] = power
    return e^


def plus(a: List[Int], b: List[Int]) -> List[Int]:
    var e = a.copy()
    for i in range(len(b)):
        e[i] += b[i]
    return e^


def katsura(n: Int, order: MonomialOrder, mut work: Budget) raises -> List[SparsePoly[QQ]]:
    var v = n + 1
    var polys = List[SparsePoly[QQ]]()
    var linear = term(v, List[Int](length=v, fill=0), -1, order, work)
    linear = linear.add(term(v, unit(v, 0), 1, order, work), work)
    for i in range(1, v):
        linear = linear.add(term(v, unit(v, i), 2, order, work), work)
    polys.append(linear^)
    for m in range(n):
        var p = term(v, unit(v, m), -1, order, work)
        for i in range(-n, n + 1):
            var j = m - i
            if abs(i) <= n and abs(j) <= n:
                p = p.add(term(v, plus(unit(v, abs(i)), unit(v, abs(j))), 1, order, work), work)
        polys.append(p^)
    return polys^


def cyclic(n: Int, homogeneous: Bool, order: MonomialOrder, mut work: Budget) raises -> List[SparsePoly[QQ]]:
    """Cyclic-n; homogeneous drops the -1 of the last equation."""
    var polys = List[SparsePoly[QQ]]()
    for k in range(1, n):
        var p = SparsePoly[QQ].zero(order, NoContext(), work)
        for i in range(n):
            var e = List[Int](length=n, fill=0)
            for j in range(k):
                e[(i + j) % n] += 1
            p = p.add(term(n, e, 1, order, work), work)
        polys.append(p^)
    var last = term(n, List[Int](length=n, fill=1), 1, order, work)
    if not homogeneous:
        last = last.add(term(n, List[Int](length=n, fill=0), -1, order, work), work)
    polys.append(last^)
    return polys^


def quadratics(n: Int, seed: UInt64, order: MonomialOrder, mut work: Budget) raises -> List[SparsePoly[QQ]]:
    var rng = SplitMix64(seed)
    var polys = List[SparsePoly[QQ]]()
    for _ in range(n):
        var p = term(n, List[Int](length=n, fill=0), Int(rng.below(19)) - 9, order, work)
        for i in range(n):
            p = p.add(term(n, unit(n, i), Int(rng.below(19)) - 9, order, work), work)
            for j in range(i, n):
                p = p.add(term(n, plus(unit(n, i), unit(n, j)), Int(rng.below(19)) - 9, order, work), work)
        polys.append(p^)
    return polys^


def agree(generators: List[SparsePoly[QQ]], order: MonomialOrder, name: String, mut c: Checker, mut work: Budget) raises:
    var chosen = groebner(generators, order, work)
    var reconstructed = _grevlex_groebner_rational(generators, order, work, -1)
    var sparse = groebner(generators, order, work, track_cofactors=True)
    c.check(chosen.basis == sparse.basis, name + ": default route")
    c.check(reconstructed == sparse.basis, name + ": reconstruction")
    verify_basis(chosen, generators, c, work)


def main() raises:
    var work = Budget()
    var c = Checker("rational groebner")
    var o3 = MonomialOrder(MonomialOrder.GREVLEX, [0, 1, 2], work)
    var o4 = MonomialOrder(MonomialOrder.GREVLEX, [0, 1, 2, 3], work)
    var shuffled4 = MonomialOrder(MonomialOrder.GREVLEX, [2, 0, 3, 1], work)
    var o5 = MonomialOrder(MonomialOrder.GREVLEX, [0, 1, 2, 3, 4], work)
    for order in [o4.copy(), shuffled4.copy()]:
        agree(katsura(3, order, work), order, "katsura-3", c, work)
        agree(cyclic(4, False, order, work), order, "cyclic-4", c, work)
        agree(cyclic(4, True, order, work), order, "homogeneous cyclic-4", c, work)
        agree(quadratics(4, 3, order, work), order, "random quadratics", c, work)
    agree(katsura(4, o5, work), o5, "katsura-4", c, work)
    agree(cyclic(5, False, o5, work), o5, "cyclic-5", c, work)
    agree(quadratics(3, 17, o3, work), o3, "random quadratics in three variables", c, work)
    # The unit ideal: x - 1 and x.
    var x = SparsePoly[QQ].variable(0, o3, NoContext(), work)
    var one = SparsePoly[QQ].constant(QQ(Rational(1)), o3, work)
    agree([x.sub(one, work), x.copy()], o3, "unit ideal", c, work)
    # Zero generators are ignored; only zeros give the empty basis.
    agree([SparsePoly[QQ].zero(o3, NoContext(), work), x.copy()], o3, "zero generator", c, work)
    var empty = groebner([SparsePoly[QQ].zero(o3, NoContext(), work)], o3, work)
    c.check(len(empty.basis) == 0, "only zero generators")
    # A large coefficient takes the exact route past its switch point.
    var big = SparsePoly[QQ].variable(0, o3, NoContext(), work).mul(SparsePoly[QQ].variable(1, o3, NoContext(), work), work)
    big = big.sub(SparsePoly[QQ].constant(QQ(Rational(1) * Rational(10) ** 200), o3, work), work)
    agree([big^, x.sub(one, work)], o3, "large input coefficient", c, work)
    c.finish()
