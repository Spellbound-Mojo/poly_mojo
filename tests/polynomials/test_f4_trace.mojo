"""Replaying a recorded F4 run modulo other primes.

Rational bases are reconstructed from images modulo many primes: the first
prime's F4 run is recorded, and later primes replay only its matrices. A
replay must either decline or return exactly the basis a full F4 run
computes, for homogeneous and inhomogeneous systems and for small and large
primes; and recording must not change the run it records. A batched replay,
one prime per SIMD lane, must return each single replay's basis for the
primes before the first whose replay declines.
"""
from apn_mojo import Rational
from polynomials import Budget, QQ, ModInt, Modulus, NoContext, SparsePoly, Term, Monomial, MonomialOrder
from polynomials._f4 import _LANES, _Trace, _f4_learn, _f4_packed, _f4_replay, _f4_replay_lanes, _sort_descending
from polynomials._packed_groebner import _Packed, _Term, _compare, _equal, _pack, _packed
from support.check import Checker
from support.corpus import as_mod
from support.rng import SplitMix64


def term(n: Int, exponents: List[Int], coefficient: Int, order: MonomialOrder, mut work: Budget) raises -> SparsePoly[QQ]:
    var pairs = List[Tuple[Int64, UInt32]]()
    for i in range(n):
        if exponents[i]:
            pairs.append((Int64(i), UInt32(exponents[i])))
    var t = Term[QQ](Monomial(pairs^, work), QQ(Rational(coefficient)))
    return SparsePoly[QQ].from_terms([t^], order, NoContext(), work)


def cyclic(n: Int, homogeneous: Bool, order: MonomialOrder, mut work: Budget) raises -> List[SparsePoly[QQ]]:
    """Cyclic-n in the first n variables; homogeneous replaces the -1 by -x_n^n."""
    var v = len(order.variables)
    var polys = List[SparsePoly[QQ]]()
    for k in range(1, n):
        var p = SparsePoly[QQ].zero(order, NoContext(), work)
        for i in range(n):
            var e = List[Int](length=v, fill=0)
            for j in range(k):
                e[(i + j) % n] += 1
            p = p.add(term(v, e, 1, order, work), work)
        polys.append(p^)
    var e = List[Int](length=v, fill=0)
    for i in range(n):
        e[i] = 1
    var last = term(v, e, 1, order, work)
    var f = List[Int](length=v, fill=0)
    if homogeneous:
        f[n] = n
    last = last.add(term(v, f, -1, order, work), work)
    polys.append(last^)
    return polys^


def quadratics(n: Int, seed: UInt64, order: MonomialOrder, mut work: Budget) raises -> List[SparsePoly[QQ]]:
    var rng = SplitMix64(seed)
    var polys = List[SparsePoly[QQ]]()
    for _ in range(n):
        var p = term(n, List[Int](length=n, fill=0), rng.below(19) - 9, order, work)
        for i in range(n):
            for j in range(i, n):
                var e = List[Int](length=n, fill=0)
                e[i] += 1
                e[j] += 1
                p = p.add(term(n, e, rng.below(19) - 9, order, work), work)
        polys.append(p^)
    return polys^


def packed_mod(generators: List[SparsePoly[QQ]], ctx: Modulus, order: MonomialOrder, mut work: Budget) raises -> List[List[_Term[ModInt, 8]]]:
    var result = List[List[_Term[ModInt, 8]]]()
    for p in generators:
        result.append(_pack[ModInt, 8](as_mod(p, ctx, work).reorder(order, work), order, work))
    return result^


def same(a: List[List[_Term[ModInt, 8]]], b: List[List[_Term[ModInt, 8]]]) -> Bool:
    if len(a) != len(b):
        return False
    for i in range(len(a)):
        if len(a[i]) != len(b[i]):
            return False
        for k in range(len(a[i])):
            if not _equal(a[i][k].monomial, b[i][k].monomial) or a[i][k].coefficient.value != b[i][k].coefficient.value:
                return False
    return True


def check_system(generators: List[SparsePoly[QQ]], order: MonomialOrder, name: String, mut c: Checker, mut work: Budget) raises:
    var primes: List[UInt64] = [2147483647, 2147483629, 2147483587, 1000003, 65521, 32749]
    var first = Modulus(primes[0], work)
    var trace = _Trace[8]()
    var learned = _f4_learn[8](packed_mod(generators, first, order, work), order.kind, first, trace, work)
    c.check(same(learned, _f4_packed[8](packed_mod(generators, first, order, work), order.kind, first, work)), name + ": recording leaves the run unchanged")
    if not trace.usable:
        return
    var replays = 0
    for i in range(1, len(primes)):
        var ctx = Modulus(primes[i], work)
        var full = _f4_packed[8](packed_mod(generators, ctx, order, work), order.kind, ctx, work)
        var replayed = _f4_replay[8](trace, packed_mod(generators, ctx, order, work), order.kind, ctx, work)
        if replayed:
            replays += 1
            c.check(same(replayed.value(), full), name + ": replay modulo " + String(primes[i]))
    c.check(replays > 0, name + ": some replay succeeds")
    # Batches of large primes, with primes too small for the run now and then.
    var large: List[UInt64] = [2147483629, 2147483587, 2147483579, 2147483563, 2147483549, 2147483543, 2147483497, 2147483489, 2147483477, 2147483423]
    for shift in range(3):
        var rings = List[Modulus]()
        var batch = List[List[List[_Term[ModInt, 8]]]]()
        for l in range(_LANES):
            var prime = large[l + shift]
            if shift == 1 and l == 5:
                prime = 7
            elif shift == 2 and l == 2:
                prime = 5
            rings.append(Modulus(prime, work))
            batch.append(packed_mod(generators, rings[l], order, work))
        var bases = _f4_replay_lanes[8](trace, batch^, order.kind, rings, work)
        c.check(bases.count <= _LANES, name + ": a batch has a basis per lane at most")
        for l in range(min(bases.count + 1, _LANES)):
            var single = _f4_replay[8](trace, packed_mod(generators, rings[l], order, work), order.kind, rings[l], work)
            var label = name + ": batch " + String(shift) + ", lane " + String(l)
            if l < bases.count:
                c.check(Bool(single) and same(single.value(), bases.basis[8](l, trace)), label + " replays as alone")
            else:
                c.check(not single, label + ", the first left out, declines alone")


def check_column_order(mut c: Checker, mut work: Budget) raises:
    """Column sorting puts distinct monomials in strictly decreasing order, by keys or comparisons."""
    var rng = SplitMix64(23)
    for kind in [MonomialOrder.LEX, MonomialOrder.GRLEX, MonomialOrder.GREVLEX]:
        for large in [False, True]:
            var monomials = List[_Packed[8]]()
            for i in range(600):
                var e = SIMD[DType.uint32, 8](0)
                for lane in range(6):
                    e[lane] = UInt32(rng.below(4))
                # Exponents of 256 and more take the comparison sort.
                if large and i % 50 == 0:
                    e[0] = UInt32(300)
                var fresh = True
                for m in monomials:
                    if _equal(m, _packed[8](e)):
                        fresh = False
                if fresh:
                    monomials.append(_packed[8](e))
            var order = _sort_descending(kind, monomials, work)
            var decreasing = len(order) == len(monomials)
            for k in range(1, len(order)):
                if _compare(kind, monomials[order[k - 1]], monomials[order[k]]) <= 0:
                    decreasing = False
            c.check(decreasing, "column order, kind " + String(kind) + (" with large exponents" if large else ""))


def main() raises:
    var work = Budget()
    var c = Checker("f4 trace")
    check_column_order(c, work)
    var o5 = MonomialOrder(MonomialOrder.GREVLEX, [0, 1, 2, 3, 4], work)
    var o6 = MonomialOrder(MonomialOrder.GREVLEX, [0, 1, 2, 3, 4, 5], work)
    var g6 = MonomialOrder(MonomialOrder.GRLEX, [0, 1, 2, 3, 4, 5], work)
    check_system(cyclic(5, True, o6, work), o6, "homogenized cyclic-5", c, work)
    check_system(cyclic(5, False, o5, work), o5, "cyclic-5", c, work)
    check_system(cyclic(5, True, g6, work), g6, "homogenized cyclic-5 under GRLEX", c, work)
    for seed in range(1, 6):
        check_system(quadratics(5, UInt64(seed), o5, work), o5, "random quadratics " + String(seed), c, work)
    c.finish()
