"""The packed Gröbner engine against the sparse engine, on benchmark systems.

Untracked calls over at most sixteen variables use packed exponent vectors;
cofactor tracking keeps the sparse engine. Both run the same algorithm, so
their bases must agree exactly, for every order kind, variable priority list,
and coefficient field.
"""
from apn_mojo import Rational
from polynomials import Budget, QQ, ModInt, Modulus, NoContext, SparsePoly, Term, Monomial, MonomialOrder, groebner
from support.check import Checker
from support.corpus import as_mod
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
    var first = term(v, List[Int](length=v, fill=0), -1, order, work)
    first = first.add(term(v, unit(v, 0), 1, order, work), work)
    for l in range(1, n + 1):
        first = first.add(term(v, unit(v, l), 2, order, work), work)
    polys.append(first^)
    for m in range(n):
        var p = term(v, unit(v, m), -1, order, work)
        for l in range(-n, n + 1):
            var a = l if l >= 0 else -l
            var b = m - l if m - l >= 0 else l - m
            if a <= n and b <= n:
                p = p.add(term(v, plus(unit(v, a), unit(v, b)), 1, order, work), work)
        polys.append(p^)
    return polys^


def cyclic(n: Int, order: MonomialOrder, mut work: Budget) raises -> List[SparsePoly[QQ]]:
    var polys = List[SparsePoly[QQ]]()
    for k in range(1, n):
        var p = SparsePoly[QQ].zero(order, NoContext(), work)
        for i in range(n):
            var e = List[Int](length=n, fill=0)
            for j in range(k):
                e[(i + j) % n] += 1
            p = p.add(term(n, e, 1, order, work), work)
        polys.append(p^)
    polys.append(term(n, List[Int](length=n, fill=1), 1, order, work).add(term(n, List[Int](length=n, fill=0), -1, order, work), work))
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


def agree_qq(generators: List[SparsePoly[QQ]], order: MonomialOrder, name: String, mut c: Checker, mut work: Budget) raises:
    var packed = groebner(generators, order, work)
    var sparse = groebner(generators, order, work, track_cofactors=True)
    c.check(packed.basis == sparse.basis, name + " over QQ")
    verify_basis(packed, generators, c, work)


def agree_mod(generators: List[SparsePoly[QQ]], order: MonomialOrder, name: String, mut c: Checker, mut work: Budget) raises:
    var ctx = Modulus(65521, work)
    var modular = List[SparsePoly[ModInt]]()
    for p in generators:
        modular.append(as_mod(p, ctx, work))
    var packed = groebner(modular, order, work)
    var sparse = groebner(modular, order, work, track_cofactors=True)
    c.check(packed.basis == sparse.basis, name + " over GF(65521)")
    verify_basis(packed, modular, c, work)


def main() raises:
    var work = Budget()
    var c = Checker("packed groebner")
    for kind in range(1, 4):
        var identity3 = MonomialOrder(UInt8(kind), [0, 1, 2], work)
        var identity4 = MonomialOrder(UInt8(kind), [0, 1, 2, 3], work)
        var reversed4 = MonomialOrder(UInt8(kind), [3, 2, 1, 0], work)
        var shuffled4 = MonomialOrder(UInt8(kind), [2, 0, 3, 1], work)
        for order in [identity4.copy(), reversed4.copy(), shuffled4.copy()]:
            agree_qq(katsura(3, order, work), order, "katsura-3", c, work)
            agree_mod(katsura(3, order, work), order, "katsura-3", c, work)
            agree_qq(cyclic(4, order, work), order, "cyclic-4", c, work)
            agree_mod(cyclic(4, order, work), order, "cyclic-4", c, work)
        agree_qq(quadratics(3, 11, identity3, work), identity3, "random quadratics", c, work)
        agree_mod(quadratics(3, 12, identity3, work), identity3, "random quadratics", c, work)
        if kind != Int(MonomialOrder.LEX):
            var identity5 = MonomialOrder(UInt8(kind), [0, 1, 2, 3, 4], work)
            agree_mod(cyclic(5, identity5, work), identity5, "cyclic-5", c, work)
            agree_qq(cyclic(5, identity5, work), identity5, "cyclic-5", c, work)
    # Variable indices need not be 0..n-1: lanes follow the priority list.
    var sparse_ids = MonomialOrder(MonomialOrder.GREVLEX, [7, 2, 5], work)
    var x = SparsePoly[QQ].variable(7, sparse_ids, NoContext(), work)
    var y = SparsePoly[QQ].variable(2, sparse_ids, NoContext(), work)
    var z = SparsePoly[QQ].variable(5, sparse_ids, NoContext(), work)
    var one = SparsePoly[QQ].constant(QQ(Rational(1)), sparse_ids, work)
    var system: List[SparsePoly[QQ]] = [x.mul(y, work).sub(z, work), y.pow(2, work).sub(x, work), z.pow(3, work).sub(one, work)]
    agree_qq(system, sparse_ids, "noncontiguous variable indices", c, work)
    # Seventeen variables exceed the packed lanes and use the sparse engine.
    var wide_variables = List[Int64]()
    for i in range(17):
        wide_variables.append(Int64(i))
    var wide = MonomialOrder(MonomialOrder.GREVLEX, wide_variables^, work)
    var chain = List[SparsePoly[QQ]]()
    for i in range(16):
        chain.append(SparsePoly[QQ].variable(Int64(i), wide, NoContext(), work).sub(SparsePoly[QQ].variable(Int64(i + 1), wide, NoContext(), work), work))
    var wide_basis = groebner(chain, wide, work)
    c.check(len(wide_basis.basis) == 16, "seventeen variables use the sparse engine")
    verify_basis(wide_basis, chain, c, work)
    c.finish()
