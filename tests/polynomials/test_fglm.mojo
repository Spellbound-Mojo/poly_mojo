"""LEX bases by FGLM from GREVLEX ones, over prime fields and over QQ.

For a zero-dimensional ideal, `groebner` under LEX converts the GREVLEX
basis, over QQ by FGLM modulo primes and reconstruction; the reduced LEX
basis is unique, so it must equal the one the packed engine computes
directly under LEX, for every prime, variable order, and system here, with
and without certification. An ideal that is not zero-dimensional must be
declined, and `groebner` then computes it directly.
"""
from apn_mojo import Rational
from polynomials import Budget, QQ, ModInt, Modulus, NoContext, SparsePoly, Term, Monomial, MonomialOrder, groebner
from polynomials._fglm import _fglm_groebner, _fglm_rational
from polynomials._packed_groebner import _packed_groebner, _packed_groebner_rational
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


def cyclic(n: Int, order: MonomialOrder, mut work: Budget) raises -> List[SparsePoly[QQ]]:
    """Cyclic-n: zero-dimensional for n = 3, 5, 6, 7; positive-dimensional for n = 4."""
    var polys = List[SparsePoly[QQ]]()
    for k in range(1, n):
        var p = SparsePoly[QQ].zero(order, NoContext(), work)
        for i in range(n):
            var e = List[Int](length=n, fill=0)
            for j in range(k):
                e[(i + j) % n] += 1
            p = p.add(term(n, e, 1, order, work), work)
        polys.append(p^)
    var e = List[Int](length=n, fill=1)
    var last = term(n, e, 1, order, work).add(term(n, List[Int](length=n, fill=0), -1, order, work), work)
    polys.append(last^)
    return polys^


def quadratics(n: Int, seed: UInt64, order: MonomialOrder, mut work: Budget) raises -> List[SparsePoly[QQ]]:
    """Dense random quadrics, n of them in n variables: zero-dimensional with 2^n solutions."""
    var rng = SplitMix64(seed)
    var polys = List[SparsePoly[QQ]]()
    for _ in range(n):
        var p = term(n, List[Int](length=n, fill=0), rng.below(19) - 9, order, work)
        for i in range(n):
            var e = List[Int](length=n, fill=0)
            e[i] = 1
            p = p.add(term(n, e, rng.below(19) - 9, order, work), work)
            for j in range(i, n):
                var f = List[Int](length=n, fill=0)
                f[i] += 1
                f[j] += 1
                p = p.add(term(n, f, rng.below(19) - 9, order, work), work)
        polys.append(p^)
    return polys^


def check_system(generators: List[SparsePoly[QQ]], order: MonomialOrder, zero_dimensional: Bool, rational: Bool, name: String, mut c: Checker, mut work: Budget) raises:
    """Compare with the direct LEX basis modulo several primes and, if `rational`, over QQ, where the direct computation is slow."""
    for prime in [UInt64(65521), UInt64(32749), UInt64(2147483647), UInt64(101)]:
        var ctx = Modulus(prime, work)
        var modular = List[SparsePoly[ModInt]]()
        for g in generators:
            modular.append(as_mod(g, ctx, work))
        var direct = _packed_groebner(modular, order, work)
        var converted = _fglm_groebner(modular, order, work)
        c.check(Bool(converted) == zero_dimensional, name + ": FGLM applies exactly when zero-dimensional, modulo " + String(prime))
        if converted:
            c.check(converted.value() == direct, name + ": FGLM basis equals the direct LEX basis modulo " + String(prime))
        var basis = groebner(modular, order, work)
        c.check(basis.basis == direct, name + ": groebner under LEX equals the direct basis modulo " + String(prime))
    if not rational:
        return
    var direct = _packed_groebner_rational(generators, order, work)
    for certify in [True, False]:
        var converted = _fglm_rational(generators, order, certify, work)
        c.check(Bool(converted) == zero_dimensional, name + ": FGLM over QQ applies exactly when zero-dimensional")
        if converted:
            c.check(converted.value() == direct, name + ": FGLM basis over QQ equals the direct LEX basis, certify " + String(certify))
        var basis = groebner(generators, order, work, certify=certify)
        c.check(basis.basis == direct, name + ": groebner under LEX over QQ equals the direct basis, certify " + String(certify))


def main() raises:
    var work = Budget()
    var c = Checker("fglm")
    for n in [3, 4, 5]:
        var variables = List[Int64]()
        for i in range(n):
            variables.append(Int64(i))
        var lex = MonomialOrder(MonomialOrder.LEX, variables.copy(), work)
        check_system(cyclic(n, lex, work), lex, n != 4, n <= 4, "cyclic-" + String(n), c, work)
    for n in [2, 3, 4]:
        var variables = List[Int64]()
        for i in range(n):
            variables.append(Int64(i))
        var lex = MonomialOrder(MonomialOrder.LEX, variables.copy(), work)
        for seed in range(1, 4):
            check_system(quadratics(n, UInt64(seed), lex, work), lex, True, n <= 3, "quadratics " + String(n) + "/" + String(seed), c, work)
    # A variable order other than the variables' own.
    var permuted = MonomialOrder(MonomialOrder.LEX, [2, 0, 1], work)
    check_system(quadratics(3, 7, permuted, work), permuted, True, True, "quadratics under LEX x2 > x0 > x1", c, work)
    check_system(cyclic(3, permuted, work), permuted, True, True, "cyclic-3 under LEX x2 > x0 > x1", c, work)
    # The unit ideal.
    var lex2 = MonomialOrder(MonomialOrder.LEX, [0, 1], work)
    var unit = List[SparsePoly[QQ]]()
    unit.append(term(2, [1, 0], 1, lex2, work).add(term(2, [0, 0], 1, lex2, work), work))
    unit.append(term(2, [1, 0], 1, lex2, work))
    unit.append(term(2, [0, 1], 1, lex2, work))
    check_system(unit, lex2, True, True, "unit ideal", c, work)
    c.finish()
