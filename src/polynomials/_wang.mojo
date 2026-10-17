"""Wang's EEZ factorization of primitive squarefree integer polynomials.

Guided by SymPy 1.13.3 factortools.py: dmp_zz_wang, dmp_zz_wang_test_points,
dmp_zz_wang_non_divisors, dmp_zz_wang_lead_coeffs, dmp_zz_wang_hensel_lifting
and dmp_zz_diophantine. Evaluation points come from a seeded deterministic
sequence; univariate Diophantine solutions reuse one set of Bezout cofactors
per factor list. Lifting runs modulo a prime above twice the Mignotte bound,
and the lifted product is compared exactly with the input before any factor
is returned, so a failed configuration only costs time.
"""
# Copyright (c) 2006-2023 SymPy Development Team
#
# All rights reserved.
#
# Redistribution and use in source and binary forms, with or without
# modification, are permitted provided that the following conditions are met:
#
#   a. Redistributions of source code must retain the above copyright notice,
#      this list of conditions and the following disclaimer.
#   b. Redistributions in binary form must reproduce the above copyright
#      notice, this list of conditions and the following disclaimer in the
#      documentation and/or other materials provided with the distribution.
#   c. Neither the name of SymPy nor the names of its contributors
#      may be used to endorse or promote products derived from this software
#      without specific prior written permission.
#
#
# THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
# AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
# IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
# ARE DISCLAIMED. IN NO EVENT SHALL THE REGENTS OR CONTRIBUTORS BE LIABLE FOR
# ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
# DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
# SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
# CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
# LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY
# OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH
# DAMAGE.

from apn_mojo import Integer, inverse_mod, next_prime, isqrt
from .errors import Budget, PolyError, PolyErrorKind, _allocation, _charge_size, _sum, _product
from .coefficients import ZZ, NoContext, _work
from .monomial import Monomial, MonomialOrder
from .sparse import SparsePoly, Term
from .dense import DensePoly
from ._grouping import _without
from ._views import _lc
from ._coefficient_ops import _gcd_coefficient, _copy as _copy_coefficient
from ._hensel import _truncate
from .primes import _symmetric
from .factor import factor_integer, _modular_squarefree
from ._integer_ops import _content as _integer_content, _divide_scalar
from ._gcd import _primitive_zz

comptime _CONFIGURATIONS = 3
"""Accepted evaluation points compared before lifting (SymPy's EEZ_NUM_CONFIGS)."""
comptime _ATTEMPTS = 40
"""Evaluation points tried at each point radius before the radius grows."""
comptime _RESTARTS = 4
"""Configurations lifted before the caller falls back to another method."""


@fieldwise_init
struct _LeadFactor(Copyable, Movable):
    """An irreducible factor of the leading coefficient and its multiplicity."""
    var poly: SparsePoly[ZZ]
    var power: Int


# ------------------------------------------------------------ sparse helpers

def _abs(a: Integer) -> Integer:
    return -a if a.sign() < 0 else a.copy()


def _imul(a: Integer, b: Integer, mut budget: Budget) raises PolyError -> Integer:
    _work(a.magnitude_bit_length() // 8 + 1, b.magnitude_bit_length() // 8 + 1, False, budget)
    try:
        return a * b
    except e:
        raise PolyError(PolyErrorKind.CAPACITY, String(e))


def _idiv(a: Integer, b: Integer, mut budget: Budget) raises PolyError -> Integer:
    """Floor quotient."""
    _work(a.magnitude_bit_length() // 8 + 1, b.magnitude_bit_length() // 8 + 1, False, budget)
    try:
        return a // b
    except e:
        raise PolyError(PolyErrorKind.CAPACITY, String(e))


def _divides(b: Integer, a: Integer, mut budget: Budget) raises PolyError -> Bool:
    """Whether the nonzero b divides a."""
    _work(a.magnitude_bit_length() // 8 + 1, b.magnitude_bit_length() // 8 + 1, False, budget)
    try:
        return (a % b).sign() == 0
    except e:
        raise PolyError(PolyErrorKind.CAPACITY, String(e))


def _int_pow(a: Integer, e: Int, mut budget: Budget) raises PolyError -> Integer:
    var result = Integer(1)
    for _ in range(e):
        budget.charge(1)
        result = _imul(result, a, budget)
    return result^


def _trunc(f: SparsePoly[ZZ], p: Integer, mut budget: Budget) raises PolyError -> SparsePoly[ZZ]:
    """Symmetric residues modulo p, dropping zero terms; order is preserved."""
    var result = SparsePoly[ZZ].zero(f.order, NoContext(), budget)
    _allocation[Term[ZZ]](len(f.terms), budget)
    # |c| < 2^(bits(p) - 2) < p / 2 is already its own symmetric residue.
    var small = p.magnitude_bit_length() - 2
    for term in f.terms:
        budget.charge(1)
        if term.coefficient.value.magnitude_bit_length() <= small:
            _charge_size(len(term.monomial.pairs), budget)
            result.terms.append(term._copy(budget))
            continue
        var c = _symmetric(term.coefficient.value, p, budget)
        if c.sign() == 0:
            continue
        _charge_size(len(term.monomial.pairs), budget)
        result.terms.append(Term[ZZ](term.monomial.copy(), ZZ(c^)))
    return result^


def _eval(f: SparsePoly[ZZ], variable: Int64, a: Integer, mut budget: Budget) raises PolyError -> SparsePoly[ZZ]:
    """Substitute the integer a for one variable."""
    _allocation[Term[ZZ]](len(f.terms), budget)
    var terms = List[Term[ZZ]](capacity=len(f.terms))
    var powers = List[Integer]()
    powers.append(Integer(1))
    for term in f.terms:
        budget.charge(1)
        var e = Int(term.monomial.exponent(variable, budget))
        if e == 0:
            terms.append(term._copy(budget))
            continue
        if a.sign() == 0:
            continue
        while len(powers) <= e:
            budget.charge(1)
            powers.append(_imul(powers[len(powers) - 1], a, budget))
        var c = _imul(term.coefficient.value, powers[e], budget)
        terms.append(Term[ZZ](_without(term.monomial, variable, budget), ZZ(c^)))
    return SparsePoly[ZZ].from_terms(terms^, f.order, NoContext(), budget)


def _eval_tail(f: SparsePoly[ZZ], variables: List[Int64], points: List[Integer], start: Int, mut budget: Budget) raises PolyError -> SparsePoly[ZZ]:
    """Substitute points[i] for variables[i] for every i >= start, in one pass."""
    if start >= len(variables):
        return f._copy(budget)
    var powers = List[List[Integer]]()
    for _ in range(start, len(variables)):
        var row = List[Integer]()
        row.append(Integer(1))
        powers.append(row^)
    _allocation[Term[ZZ]](len(f.terms), budget)
    var terms = List[Term[ZZ]](capacity=len(f.terms))
    var univariate = True
    var variable = Int64(-1)
    var degree = 0
    for term in f.terms:
        budget.charge(1)
        var c = term.coefficient.value.copy()
        var vanished = False
        var pairs = List[Tuple[Int64, UInt32]]()
        for pair in term.monomial.pairs:
            budget.charge(1)
            var index = -1
            for i in range(start, len(variables)):
                if variables[i] == pair[0]:
                    index = i - start
            if index < 0:
                pairs.append(pair)
                continue
            ref a = points[start + index]
            if a.sign() == 0:
                vanished = True
                break
            var e = Int(pair[1])
            while len(powers[index]) <= e:
                budget.charge(1)
                powers[index].append(_imul(powers[index][len(powers[index]) - 1], a, budget))
            c = _imul(c, powers[index][e], budget)
        if vanished:
            continue
        if len(pairs) > 1 or (len(pairs) == 1 and variable >= 0 and pairs[0][0] != variable):
            univariate = False
        if len(pairs) == 1:
            variable = pairs[0][0]
            degree = max(degree, Int(pairs[0][1]))
        terms.append(Term[ZZ](Monomial(pairs^, budget), ZZ(c^)))
    if not univariate:
        return SparsePoly[ZZ].from_terms(terms^, f.order, NoContext(), budget)
    # A univariate image collects its terms by exponent instead of sorting them all.
    _allocation[Integer](degree + 1, budget)
    var sums = List[Integer](length=degree + 1, fill=Integer(0))
    for t in terms:
        budget.charge(1)
        var e = Int(t.monomial.pairs[0][1]) if len(t.monomial.pairs) else 0
        sums[e] = _iadd(sums[e], t.coefficient.value, budget)
    var collected = List[Term[ZZ]](capacity=degree + 1)
    for e in range(degree + 1):
        if sums[e].sign() != 0:
            var pairs = List[Tuple[Int64, UInt32]]()
            if e:
                pairs.append((variable, UInt32(e)))
            collected.append(Term[ZZ](Monomial(pairs^, budget), ZZ(sums[e].copy())))
    return SparsePoly[ZZ].from_terms(collected^, f.order, NoContext(), budget)


def _taylor(f: SparsePoly[ZZ], variable: Int64, a: Integer, k: Int, mut budget: Budget) raises PolyError -> SparsePoly[ZZ]:
    """The coefficient of (variable - a)^k in f, a polynomial without variable."""
    var terms = List[Term[ZZ]]()
    # weights[j] = binomial(k + j, k) * a^j
    var weights = List[Integer]()
    var binomials = List[Integer]()
    var powers = List[Integer]()
    binomials.append(Integer(1))
    powers.append(Integer(1))
    weights.append(Integer(1))
    for term in f.terms:
        budget.charge(1)
        var e = Int(term.monomial.exponent(variable, budget))
        if e < k:
            continue
        if e > k and a.sign() == 0:
            continue
        while len(weights) <= e - k:
            budget.charge(1)
            var j = len(weights)
            binomials.append(_idiv(_imul(binomials[j - 1], Integer(k + j), budget), Integer(j), budget))
            powers.append(_imul(powers[j - 1], a, budget))
            weights.append(_imul(binomials[j], powers[j], budget))
        var c = _imul(term.coefficient.value, weights[e - k], budget)
        _allocation[Term[ZZ]](1, budget)
        terms.append(Term[ZZ](_without(term.monomial, variable, budget), ZZ(c^)))
    return SparsePoly[ZZ].from_terms(terms^, f.order, NoContext(), budget)


def _linear(variable: Int64, a: Integer, order: MonomialOrder, mut budget: Budget) raises PolyError -> SparsePoly[ZZ]:
    """variable - a."""
    var x = SparsePoly[ZZ].variable(variable, order, NoContext(), budget)
    return x.sub(SparsePoly[ZZ].constant(ZZ(a.copy()), order, budget), budget)


def _product_of(polys: List[SparsePoly[ZZ]], skip: Int, order: MonomialOrder, mut budget: Budget) raises PolyError -> SparsePoly[ZZ]:
    var result = SparsePoly[ZZ].constant(ZZ.one(NoContext()), order, budget)
    for i in range(len(polys)):
        budget.charge(1)
        if i != skip:
            result = result.mul(polys[i], budget)
    return result^


def _max_norm(f: SparsePoly[ZZ], mut budget: Budget) raises PolyError -> Integer:
    var result = Integer(0)
    for term in f.terms:
        budget.charge(1)
        var a = _abs(term.coefficient.value)
        if a > result:
            result = a^
    return result^


def _replace_lead(h: SparsePoly[ZZ], main: Int64, lc: SparsePoly[ZZ], mut budget: Budget) raises PolyError -> SparsePoly[ZZ]:
    """h with its leading coefficient in main replaced by lc."""
    var degree = h.degree_in(main, budget)
    var terms = List[Term[ZZ]]()
    for term in h.terms:
        budget.charge(1)
        if Int(term.monomial.exponent(main, budget)) != degree:
            _allocation[Term[ZZ]](1, budget)
            terms.append(term._copy(budget))
    var shift = Monomial([(main, UInt32(degree))], budget) if degree > 0 else Monomial()
    for term in lc.terms:
        budget.charge(1)
        _allocation[Term[ZZ]](1, budget)
        terms.append(Term[ZZ](term.monomial.mul(shift, budget), term.coefficient.copy()))
    return SparsePoly[ZZ].from_terms(terms^, h.order, NoContext(), budget)


# --------------------------------------------- univariate arithmetic mod p

def _dense(f: SparsePoly[ZZ], main: Int64, mut budget: Budget) raises PolyError -> DensePoly[ZZ]:
    return DensePoly[ZZ].from_sparse(f, budget, variable=main)


def _inverse(a: Integer, p: Integer) raises PolyError -> Integer:
    try:
        return inverse_mod(a, p)
    except e:
        raise PolyError(PolyErrorKind.DOMAIN, "Wang lifting met a noninvertible residue")


def _pdivmod(a: DensePoly[ZZ], b: DensePoly[ZZ], p: Integer, mut budget: Budget) raises PolyError -> Tuple[DensePoly[ZZ], DensePoly[ZZ]]:
    var n = b.degree()
    if n < 0:
        raise PolyError(PolyErrorKind.DOMAIN, "division by zero modulo p")
    var inverse = _inverse(b.coefficients[n].value, p)
    _allocation[ZZ](len(a.coefficients), budget)
    var r = List[ZZ](capacity=len(a.coefficients))
    for i in range(len(a.coefficients)):
        r.append(a.coefficients[i].copy())
    var length = max(len(r) - n, 0)
    _allocation[ZZ](length, budget)
    var q = List[ZZ](length=length, fill=ZZ.zero(NoContext()))
    var top = len(r) - 1
    while top >= n:
        budget.charge(1)
        var c = ZZ(_symmetric(_imul(r[top].value, inverse, budget), p, budget))
        if not c.is_zero():
            var shift = top - n
            for i in range(n):
                budget.charge(1)
                r[shift + i] = ZZ(_symmetric(r[shift + i].sub(c.mul(b.coefficients[i], budget), budget).value, p, budget))
            q[shift] = c^
        r[top] = ZZ.zero(NoContext())
        top -= 1
    var quotient = DensePoly[ZZ].from_coefficients(a.variable, NoContext(), q^, budget)
    var remainder = _truncate(DensePoly[ZZ].from_coefficients(a.variable, NoContext(), r^, budget), ZZ(p.copy()), budget)
    return (quotient^, remainder^)


def _pinverse(a: DensePoly[ZZ], m: DensePoly[ZZ], p: Integer, mut budget: Budget) raises PolyError -> DensePoly[ZZ]:
    """The inverse of a modulo (m, p), by the extended Euclidean algorithm."""
    var pz = ZZ(p.copy())
    var r0 = m.copy()
    var r1 = _pdivmod(a, m, p, budget)[1].copy()
    var s0 = DensePoly[ZZ](a.variable, NoContext())
    var s1 = DensePoly[ZZ].from_coefficients(a.variable, NoContext(), [ZZ.one(NoContext())], budget)
    while r1.degree() > 0:
        budget.charge(1)
        var qr = _pdivmod(r0, r1, p, budget)
        var s2 = _truncate(s0.sub(qr[0].mul(s1, budget), budget), pz, budget)
        r0 = r1^
        r1 = qr[1].copy()
        s0 = s1^
        s1 = s2^
    if r1.degree() != 0:
        raise PolyError(PolyErrorKind.DOMAIN, "Wang images are not coprime modulo p")
    var scale = _inverse(r1.coefficients[0].value, p)
    return _truncate(s1.scale(ZZ(scale^), budget), pz, budget)


# ------------------------------------------------- multivariate Diophantine

struct _Diophantine(Movable):
    """Solves sum_i s_i prod_(j != i) F_j = c modulo p and (x_k - a_k)^(d+1).

    levels[k] holds F with the variables params[k..] evaluated, products[k]
    the cofactor products at that level, and sigma the univariate Bezout
    cofactors with sum_i sigma_i prod_(j != i) F_j = 1 modulo p.
    """
    var main: Int64
    var params: List[Int64]
    var points: List[Integer]
    var degree: Int
    var p: Integer
    var levels: List[List[SparsePoly[ZZ]]]
    var products: List[List[SparsePoly[ZZ]]]
    var bottom: List[DensePoly[ZZ]]
    var sigma: List[DensePoly[ZZ]]

    def __init__(out self, factors: List[SparsePoly[ZZ]], main: Int64, params: List[Int64], points: List[Integer], degree: Int, p: Integer, mut budget: Budget) raises PolyError:
        self.main = main
        self.params = params.copy()
        self.points = List[Integer]()
        for a in points:
            self.points.append(a.copy())
        self.degree = degree
        self.p = p.copy()
        var n = len(params)
        _allocation[List[SparsePoly[ZZ]]](_sum(n, 1), budget)
        self.levels = List[List[SparsePoly[ZZ]]](length=n + 1, fill=List[SparsePoly[ZZ]]())
        self.products = List[List[SparsePoly[ZZ]]](length=n + 1, fill=List[SparsePoly[ZZ]]())
        self.levels[n] = factors.copy()
        var k = n - 1
        while k >= 0:
            budget.charge(1)
            var evaluated = List[SparsePoly[ZZ]]()
            for g in self.levels[k + 1]:
                evaluated.append(_eval(g, params[k], points[k], budget))
            self.levels[k] = evaluated^
            k -= 1
        var order = factors[0].order.copy()
        for level in range(1, n + 1):
            budget.charge(1)
            var row = List[SparsePoly[ZZ]]()
            for i in range(len(factors)):
                row.append(_product_of(self.levels[level], i, order, budget))
            self.products[level] = row^
        var pz = ZZ(p.copy())
        self.bottom = List[DensePoly[ZZ]]()
        for g in self.levels[0]:
            self.bottom.append(_truncate(_dense(g, main, budget), pz, budget))
        self.sigma = List[DensePoly[ZZ]]()
        for i in range(len(self.bottom)):
            budget.charge(1)
            var cofactor = DensePoly[ZZ].from_coefficients(main, NoContext(), [ZZ.one(NoContext())], budget)
            for j in range(len(self.bottom)):
                if j != i:
                    cofactor = _pdivmod(cofactor.mul(self.bottom[j], budget), self.bottom[i], p, budget)[1].copy()
            self.sigma.append(_pinverse(cofactor, self.bottom[i], p, budget))

    def solve(self, level: Int, c: SparsePoly[ZZ], mut budget: Budget) raises PolyError -> List[SparsePoly[ZZ]]:
        var order = c.order.copy()
        var r = len(self.bottom)
        var pz = ZZ(self.p.copy())
        if level == 0:
            var dense_c = _truncate(_dense(c, self.main, budget), pz, budget)
            var result = List[SparsePoly[ZZ]]()
            for i in range(r):
                budget.charge(1)
                var s = _pdivmod(_truncate(dense_c.mul(self.sigma[i], budget), pz, budget), self.bottom[i], self.p, budget)[1].copy()
                result.append(s.to_sparse(order, budget))
            return result^
        var variable = self.params[level - 1]
        ref a = self.points[level - 1]
        var s = self.solve(level - 1, _eval(c, variable, a, budget), budget)
        var e = c._copy(budget)
        for i in range(r):
            budget.charge(1)
            e = e.sub(s[i].mul(self.products[level][i], budget), budget)
        e = _trunc(e, self.p, budget)
        var m = _linear(variable, a, order, budget)
        var power = SparsePoly[ZZ].constant(ZZ.one(NoContext()), order, budget)
        for k in range(self.degree):
            budget.charge(1)
            if e.is_zero():
                break
            power = power.mul(m, budget)
            var coefficient = _trunc(_taylor(e, variable, a, k + 1, budget), self.p, budget)
            if coefficient.is_zero():
                continue
            var t = self.solve(level - 1, coefficient, budget)
            for i in range(r):
                budget.charge(1)
                var term = t[i].mul(power, budget)
                s[i] = s[i].add(term, budget)
                e = e.sub(term.mul(self.products[level][i], budget), budget)
            e = _trunc(e, self.p, budget)
        for i in range(r):
            s[i] = _trunc(s[i], self.p, budget)
        return s^


# ------------------------------------------------ sparse Diophantine steps

def _iadd(a: Integer, b: Integer, mut budget: Budget) raises PolyError -> Integer:
    _work(a.magnitude_bit_length() // 8 + 1, b.magnitude_bit_length() // 8 + 1, True, budget)
    try:
        return a + b
    except e:
        raise PolyError(PolyErrorKind.CAPACITY, String(e))


def _isub(a: Integer, b: Integer, mut budget: Budget) raises PolyError -> Integer:
    _work(a.magnitude_bit_length() // 8 + 1, b.magnitude_bit_length() // 8 + 1, True, budget)
    try:
        return a - b
    except e:
        raise PolyError(PolyErrorKind.CAPACITY, String(e))


def _residue_mod(a: Integer, p: Integer, mut budget: Budget) raises PolyError -> Integer:
    """The residue of a in [0, p)."""
    var r = _symmetric(a, p, budget)
    if r.sign() < 0:
        return _iadd(r, p, budget)
    return r^


def _mulmod(a: Integer, b: Integer, p: Integer, mut budget: Budget) raises PolyError -> Integer:
    return _residue_mod(_imul(a, b, budget), p, budget)


struct _SparseStep(Movable):
    """Diophantine solves for one lifted variable by sparse interpolation
    (Monagan and Tuncer's sparse Hensel lifting).

    The correction of F_i is guessed to use only monomials of F_i below its
    main degree. With z = M(beta) for a monomial M of the inner variables,
    the images at the points beta^1..beta^T reduce each coefficient to a
    transposed Vandermonde system in the nodes z. A guess is used only after
    the caller verifies it exactly.
    """
    var main: Int64
    var p: Integer
    var inner: List[Int64]
    var beta: List[Integer]
    var count: Int
    var ok: Bool
    var degrees: List[Int]
    var supports: List[List[List[Monomial]]]
    var nodes: List[List[List[Integer]]]
    var weights: List[List[List[List[Integer]]]]
    var scales: List[List[List[Integer]]]
    var images: List[List[DensePoly[ZZ]]]
    var sigma: List[List[DensePoly[ZZ]]]

    def __init__(out self, factors: List[SparsePoly[ZZ]], main: Int64, inner: List[Int64], p: Integer, mut budget: Budget) raises PolyError:
        self.main = main
        self.p = p.copy()
        self.inner = inner.copy()
        self.beta = List[Integer]()
        self.count = 0
        self.ok = True
        self.degrees = List[Int]()
        self.supports = List[List[List[Monomial]]]()
        self.nodes = List[List[List[Integer]]]()
        self.weights = List[List[List[List[Integer]]]]()
        self.scales = List[List[List[Integer]]]()
        self.images = List[List[DensePoly[ZZ]]]()
        self.sigma = List[List[DensePoly[ZZ]]]()
        # A fixed generator keeps the points, and so every charge, reproducible.
        var state = UInt64(0x9E3779B97F4A7C15)
        for _ in range(len(inner)):
            budget.charge(1)
            state = state * 6364136223846793005 + 1442695040888963407
            var b = _residue_mod(Integer(Int(state >> 2)), p, budget)
            if b.sign() == 0:
                b = Integer(1)
            self.beta.append(b^)
        for g in factors:
            budget.charge(1)
            var d = g.degree_in(main, budget)
            self.degrees.append(d)
            var rows = List[List[Monomial]](length=max(d, 0), fill=List[Monomial]())
            for term in g.terms:
                budget.charge(1)
                var e = Int(term.monomial.exponent(main, budget))
                if e < d:
                    rows[e].append(_without(term.monomial, main, budget))
            var row_nodes = List[List[Integer]]()
            for row in rows:
                self.count = max(self.count, len(row))
                var z = List[Integer]()
                for m in row:
                    z.append(self._value(m, budget))
                row_nodes.append(z^)
            self.supports.append(rows^)
            self.nodes.append(row_nodes^)
        for i in range(len(self.nodes)):
            var row_weights = List[List[List[Integer]]]()
            var row_scales = List[List[Integer]]()
            for z in self.nodes[i]:
                budget.charge(1)
                var prepared = self._prepare(z, budget)
                # A zero or repeated node leaves the system singular.
                if len(prepared[1]) != len(z):
                    self.ok = False
                    return
                row_weights.append(prepared[0].copy())
                row_scales.append(prepared[1].copy())
            self.weights.append(row_weights^)
            self.scales.append(row_scales^)
        var pz = ZZ(p.copy())
        var evaluated = List[List[DensePoly[ZZ]]]()
        for g in factors:
            evaluated.append(self._evaluate(g, self.count, budget))
        for j in range(self.count):
            budget.charge(1)
            var row = List[DensePoly[ZZ]]()
            for i in range(len(factors)):
                if evaluated[i][j].degree() != self.degrees[i]:
                    self.ok = False
                    return
                row.append(evaluated[i][j].copy())
            var cofactors = List[DensePoly[ZZ]]()
            for i in range(len(row)):
                budget.charge(1)
                var cofactor = DensePoly[ZZ].from_coefficients(main, NoContext(), [ZZ.one(NoContext())], budget)
                for k in range(len(row)):
                    if k != i:
                        cofactor = _pdivmod(_truncate(cofactor.mul(row[k], budget), pz, budget), row[i], p, budget)[1].copy()
                try:
                    cofactors.append(_pinverse(cofactor, row[i], p, budget))
                except e:
                    if e.kind != PolyErrorKind.DOMAIN:
                        raise e^
                    self.ok = False
                    return
            self.images.append(row^)
            self.sigma.append(cofactors^)

    def _value(self, m: Monomial, mut budget: Budget) raises PolyError -> Integer:
        var z = Integer(1)
        for pair in m.pairs:
            budget.charge(1)
            var index = -1
            for k in range(len(self.inner)):
                if self.inner[k] == pair[0]:
                    index = k
            if index < 0:
                raise PolyError(PolyErrorKind.DOMAIN, "monomial outside the lifted variables")
            for _ in range(Int(pair[1])):
                z = _mulmod(z, self.beta[index], self.p, budget)
        return z^

    def _prepare(self, z: List[Integer], mut budget: Budget) raises PolyError -> Tuple[List[List[Integer]], List[Integer]]:
        """For each node z_l, the quotient P(x) / (x - z_l) of the master
        polynomial and 1 / (z_l P_l(z_l)): sum_m q_lm v_(m+1) times that
        scale solves sum_l c_l z_l^j = v_j for j = 1..t. Fewer scales than
        nodes mark a singular system."""
        var t = len(z)
        var master = List[Integer]()
        master.append(Integer(1))
        for l in range(t):
            budget.charge(1)
            # master *= (x - z_l), coefficients from the constant term up.
            var next = List[Integer](length=len(master) + 1, fill=Integer(0))
            for m in range(len(master)):
                budget.charge(1)
                next[m + 1] = _iadd(next[m + 1], master[m], budget)
                next[m] = _residue_mod(_isub(next[m], _imul(master[m], z[l], budget), budget), self.p, budget)
            master = next^
        var quotients = List[List[Integer]]()
        var scales = List[Integer]()
        for l in range(t):
            budget.charge(1)
            if z[l].sign() == 0:
                return (quotients^, scales^)
            var q = List[Integer](length=t, fill=Integer(0))
            q[t - 1] = Integer(1)
            var m = t - 1
            while m > 0:
                budget.charge(1)
                q[m - 1] = _residue_mod(_iadd(master[m], _imul(z[l], q[m], budget), budget), self.p, budget)
                m -= 1
            var value = Integer(0)
            m = t - 1
            while m >= 0:
                budget.charge(1)
                value = _residue_mod(_iadd(_imul(value, z[l], budget), q[m], budget), self.p, budget)
                m -= 1
            var denominator = _mulmod(value, z[l], self.p, budget)
            if denominator.sign() == 0:
                return (quotients^, scales^)
            scales.append(_inverse(denominator, self.p))
            quotients.append(q^)
        return (quotients^, scales^)

    def _evaluate(self, g: SparsePoly[ZZ], count: Int, mut budget: Budget) raises PolyError -> List[DensePoly[ZZ]]:
        """g(main, beta^j) modulo p for j = 1..count."""
        var top = max(g.degree_in(self.main, budget), 0)
        var sums = List[List[Integer]]()
        for _ in range(count):
            sums.append(List[Integer](length=top + 1, fill=Integer(0)))
        for term in g.terms:
            budget.charge(1)
            var e = Int(term.monomial.exponent(self.main, budget))
            var z = self._value(_without(term.monomial, self.main, budget), budget)
            var power = Integer(1)
            for j in range(count):
                power = _mulmod(power, z, self.p, budget)
                sums[j][e] = _iadd(sums[j][e], _imul(term.coefficient.value, power, budget), budget)
        var result = List[DensePoly[ZZ]]()
        for j in range(count):
            budget.charge(1)
            var coefficients = List[ZZ]()
            for c in sums[j]:
                coefficients.append(ZZ(_residue_mod(c, self.p, budget)))
            result.append(DensePoly[ZZ].from_coefficients(self.main, NoContext(), coefficients^, budget))
        return result^

    def solve(self, c: SparsePoly[ZZ], mut budget: Budget) raises PolyError -> List[SparsePoly[ZZ]]:
        """The guessed corrections s_i with sum_i s_i prod_(k != i) F_k = c."""
        var pz = ZZ(self.p.copy())
        var r = len(self.degrees)
        # values[i][d][j]: coefficient of main^d in s_i at the point beta^(j+1).
        var values = List[List[List[Integer]]]()
        for i in range(r):
            values.append(List[List[Integer]](length=max(self.degrees[i], 0), fill=List[Integer]()))
        var images = self._evaluate(c, self.count, budget)
        for j in range(self.count):
            budget.charge(1)
            ref image = images[j]
            for i in range(r):
                budget.charge(1)
                var s = _pdivmod(_truncate(image.mul(self.sigma[j][i], budget), pz, budget), self.images[j][i], self.p, budget)[1].copy()
                for d in range(self.degrees[i]):
                    var v = Integer(0)
                    if d <= s.degree():
                        v = _residue_mod(s.coefficients[d].value, self.p, budget)
                    values[i][d].append(v^)
        var result = List[SparsePoly[ZZ]]()
        for i in range(r):
            budget.charge(1)
            var terms = List[Term[ZZ]]()
            for d in range(self.degrees[i]):
                var shift = Monomial([(self.main, UInt32(d))], budget) if d > 0 else Monomial()
                for l in range(len(self.supports[i][d])):
                    budget.charge(1)
                    var total = Integer(0)
                    for m in range(len(self.supports[i][d])):
                        total = _iadd(total, _imul(self.weights[i][d][l][m], values[i][d][m], budget), budget)
                    var coefficient = _symmetric(_imul(_residue_mod(total, self.p, budget), self.scales[i][d][l], budget), self.p, budget)
                    if coefficient.sign() != 0:
                        _allocation[Term[ZZ]](1, budget)
                        terms.append(Term[ZZ](self.supports[i][d][l].mul(shift, budget), ZZ(coefficient^)))
            result.append(SparsePoly[ZZ].from_terms(terms^, c.order, NoContext(), budget))
        return result^


# ------------------------------------------------------------- Wang's steps

struct _Points(Movable):
    """The seeded deterministic sequence of integer evaluation points."""
    var state: UInt64
    var radius: Int

    def __init__(out self):
        self.state = 0x5DEECE66D
        self.radius = 1

    def next(mut self, count: Int, mut budget: Budget) raises PolyError -> List[Integer]:
        _allocation[Integer](count, budget)
        var result = List[Integer](capacity=count)
        for _ in range(count):
            budget.charge(1)
            self.state += 0x9E3779B97F4A7C15
            var z = self.state
            z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9
            z = (z ^ (z >> 27)) * 0x94D049BB133111EB
            z = z ^ (z >> 31)
            var width = UInt64(2 * self.radius + 1)
            result.append(Integer(Int(z % width) - self.radius))
        return result^


def _non_divisors(values: List[Integer], cs: Integer, ct: Integer, mut budget: Budget) raises PolyError -> Bool:
    """Whether each evaluated leading factor has a prime divisor that no
    earlier one, nor the contents, shares (dmp_zz_wang_non_divisors)."""
    var result: List[Integer] = [_abs(_imul(cs, ct, budget))]
    for value in values:
        budget.charge(1)
        var q = _abs(value)
        var i = len(result) - 1
        while i >= 0:
            var r = result[i].copy()
            while r != Integer(1):
                budget.charge(1)
                r = _gcd_coefficient(ZZ(r^), ZZ(q.copy()), budget).value
                q = _idiv(q, r, budget)
            if q == Integer(1):
                return False
            i -= 1
        result.append(q^)
    return True


@fieldwise_init
struct _Configuration(Copyable, Movable):
    var points: List[Integer]
    var content: Integer
    var image: DensePoly[ZZ]
    var factors: List[DensePoly[ZZ]]
    var lead_values: List[Integer]


def _test_point(f: SparsePoly[ZZ], main: Int64, params: List[Int64], lead: SparsePoly[ZZ], lead_factors: List[_LeadFactor], ct: Integer, points: List[Integer], mut budget: Budget) raises PolyError -> Optional[_Configuration]:
    var lead_value = _eval_tail(lead, params, points, 0, budget)
    if lead_value.is_zero():
        return None
    var values = List[Integer]()
    for t in lead_factors:
        budget.charge(1)
        var v = _eval_tail(t.poly, params, points, 0, budget)
        values.append(v.terms[0].coefficient.value.copy() if len(v.terms) else Integer(0))
    # A larger content only removes more primes, so failing with content one
    # rejects the point before f is evaluated.
    if not _non_divisors(values, Integer(1), ct, budget):
        return None
    var image = _dense(_eval_tail(f, params, points, 0, budget), main, budget)
    if image.degree() != f.degree_in(main, budget):
        return None
    # Cheap tests first, as in dmp_zz_wang_test_points; only an accepted
    # point pays for the univariate factorization.
    var content = _integer_content(image, budget).value.copy()
    var primitive = _divide_scalar(image, ZZ(content.copy()), budget)
    if not _modular_squarefree(primitive, budget):
        return None
    if not _non_divisors(values, content, ct, budget):
        return None
    var factored = factor_integer(primitive, budget)
    var factors = List[DensePoly[ZZ]]()
    for entry in factored.factors:
        budget.charge(1)
        if entry[1] != 1:
            return None
        factors.append(entry[0].copy())
    var copied = List[Integer]()
    for a in points:
        copied.append(a.copy())
    return _Configuration(copied^, content^, image^, factors^, values^)


def _lead_coefficients(f: SparsePoly[ZZ], main: Int64, params: List[Int64], lead_factors: List[_LeadFactor], config: _Configuration, mut budget: Budget) raises PolyError -> Optional[Tuple[SparsePoly[ZZ], List[DensePoly[ZZ]], List[SparsePoly[ZZ]]]]:
    """Distribute the leading coefficient's factors (dmp_zz_wang_lead_coeffs)."""
    var order = f.order.copy()
    var one = SparsePoly[ZZ].constant(ZZ.one(NoContext()), order, budget)
    var cs = config.content.copy()
    _allocation[Bool](len(lead_factors), budget)
    var used = List[Bool](length=len(lead_factors), fill=False)
    var assigned = List[SparsePoly[ZZ]]()
    for h in config.factors:
        budget.charge(1)
        var c = one._copy(budget)
        var d = _imul(h.coefficients[h.degree()].value, cs, budget)
        var i = len(lead_factors) - 1
        while i >= 0:
            budget.charge(1)
            var e = config.lead_values[i].copy()
            var k = 0
            if e.sign() != 0 and _abs(e) != Integer(1):
                while _divides(e, d, budget):
                    budget.charge(1)
                    d = _idiv(d, e, budget)
                    k += 1
            if k:
                c = c.mul(lead_factors[i].poly.pow(UInt64(k), budget), budget)
                used[i] = True
            i -= 1
        assigned.append(c^)
    for flag in used:
        if not flag:
            return None
    var lcs = List[SparsePoly[ZZ]]()
    var images = List[DensePoly[ZZ]]()
    for j in range(len(assigned)):
        budget.charge(1)
        var dv = _eval_tail(assigned[j], params, config.points, 0, budget)
        var d = dv.terms[0].coefficient.value.copy() if len(dv.terms) else Integer(0)
        if d.sign() == 0:
            return None
        ref h = config.factors[j]
        var lc = h.coefficients[h.degree()].value.copy()
        var cc: Integer
        var image = h.copy()
        if cs == Integer(1):
            if not _divides(d, lc, budget):
                return None
            cc = _idiv(lc, d, budget)
        else:
            var g = _gcd_coefficient(ZZ(lc.copy()), ZZ(d.copy()), budget).value
            d = _idiv(d, g, budget)
            cc = _idiv(lc, g, budget)
            image = image.scale(ZZ(d.copy()), budget)
            if not _divides(d, cs, budget):
                return None
            cs = _idiv(cs, d, budget)
        lcs.append(assigned[j].scale(ZZ(cc^), budget))
        images.append(image^)
    var target = f._copy(budget)
    if cs != Integer(1):
        for j in range(len(lcs)):
            lcs[j] = lcs[j].scale(ZZ(cs.copy()), budget)
            images[j] = images[j].scale(ZZ(cs.copy()), budget)
        target = target.scale(ZZ(_int_pow(cs, len(lcs) - 1, budget)), budget)
    return (target^, images^, lcs^)


def _mignotte(f: SparsePoly[ZZ], mut budget: Budget) raises PolyError -> Integer:
    """sqrt(n + 1) 2^n |f|_max |lc(f)| with n the sum of the variable degrees."""
    var n = 0
    for v in f.variables(budget):
        n = _sum(n, f.degree_in(v, budget))
    var lead = _abs(f.terms[len(f.terms) - 1].coefficient.value)
    var root: Integer
    try:
        root = isqrt(Integer(n + 1)) + Integer(1)
    except e:
        raise PolyError(PolyErrorKind.CAPACITY, String(e))
    return _imul(_imul(_imul(root, _int_pow(Integer(2), n, budget), budget), _max_norm(f, budget), budget), lead, budget)


def _lift(f: SparsePoly[ZZ], main: Int64, params: List[Int64], points: List[Integer], var factors: List[SparsePoly[ZZ]], lcs: List[SparsePoly[ZZ]], p: Integer, mut budget: Budget) raises PolyError -> Optional[List[SparsePoly[ZZ]]]:
    """Multivariate Hensel lifting, one variable at a time (dmp_zz_wang_hensel_lifting)."""
    var order = f.order.copy()
    var u = len(params)
    _allocation[SparsePoly[ZZ]](u, budget)
    var images = List[SparsePoly[ZZ]](length=u, fill=SparsePoly[ZZ](order.copy(), NoContext()))
    images[u - 1] = f._copy(budget)
    var k = u - 2
    while k >= 0:
        budget.charge(1)
        images[k] = _trunc(_eval(images[k + 1], params[k + 1], points[k + 1], budget), p, budget)
        k -= 1
    var degree = 0
    for v in params:
        degree = max(degree, f.degree_in(v, budget))
    for w in range(1, u + 1):
        budget.charge(1)
        ref s = images[w - 1]
        var variable = params[w - 1]
        ref a = points[w - 1]
        var previous = factors.copy()
        var inner_params = List[Int64]()
        var inner_points = List[Integer]()
        for i in range(w - 1):
            inner_params.append(params[i])
            inner_points.append(points[i].copy())
        for i in range(len(factors)):
            budget.charge(1)
            var lc = _trunc(_eval_tail(lcs[i], params, points, w, budget), p, budget)
            factors[i] = _replace_lead(factors[i], main, lc, budget)
        var solver = _Diophantine(previous, main, inner_params, inner_points, degree, p, budget)
        var sparse = Optional[_SparseStep](None)
        if w >= 2:
            sparse = _SparseStep(previous, main, inner_params, p, budget)
        var m = _linear(variable, a, order, budget)
        var power = SparsePoly[ZZ].constant(ZZ.one(NoContext()), order, budget)
        var error = _trunc(s.sub(_product_of(factors, -1, order, budget), budget), p, budget)
        var top = s.degree_in(variable, budget)
        for j in range(top):
            budget.charge(1)
            if error.is_zero():
                break
            power = power.mul(m, budget)
            var coefficient = _trunc(_taylor(error, variable, a, j + 1, budget), p, budget)
            if coefficient.is_zero():
                continue
            if sparse and sparse.value().ok:
                # The Diophantine solution with these degree bounds is unique,
                # so a guess that clears this Taylor coefficient is the one
                # the recursive solver would return.
                var guess = sparse.value().solve(coefficient, budget)
                var trial = List[SparsePoly[ZZ]]()
                for i in range(len(factors)):
                    budget.charge(1)
                    trial.append(_trunc(factors[i].add(guess[i].mul(power, budget), budget), p, budget))
                var remainder = _trunc(s.sub(_product_of(trial, -1, order, budget), budget), p, budget)
                if _trunc(_taylor(remainder, variable, a, j + 1, budget), p, budget).is_zero():
                    factors = trial^
                    error = remainder^
                    continue
                sparse.value().ok = False
            var t = solver.solve(w - 1, coefficient, budget)
            for i in range(len(factors)):
                budget.charge(1)
                factors[i] = _trunc(factors[i].add(t[i].mul(power, budget), budget), p, budget)
            error = _trunc(s.sub(_product_of(factors, -1, order, budget), budget), p, budget)
    var product = _product_of(factors, -1, order, budget)
    if not (product == f):
        return None
    return factors^


def _wang(f: SparsePoly[ZZ], main: Int64, params: List[Int64], lead_factors: List[_LeadFactor], ct: Integer, mut budget: Budget) raises PolyError -> Optional[List[SparsePoly[ZZ]]]:
    """Factor a primitive squarefree f in main and at least one parameter.

    Returns:
        The primitive irreducible factors, or no value when no configuration
        lifted; the caller then uses another method.

    Raises:
        PolyError: LIMIT or CAPACITY on work limits.
    """
    var lead = _lc(f, main, budget)
    var sequence = _Points()
    var tried = 0
    for _ in range(_RESTARTS):
        budget.charge(1)
        var configs = List[_Configuration]()
        var fewest = -1
        var attempts = 0
        while len(configs) < _CONFIGURATIONS:
            budget.charge(1)
            if attempts == _ATTEMPTS:
                attempts = 0
                sequence.radius = _sum(sequence.radius, 1)
                if sequence.radius > 1 << 20:
                    return None
            attempts += 1
            tried += 1
            var points = sequence.next(len(params), budget)
            var found = _test_point(f, main, params, lead, lead_factors, ct, points, budget)
            if not found:
                continue
            var config = found.take()
            var r = len(config.factors)
            if r == 1:
                var single = List[SparsePoly[ZZ]]()
                single.append(f._copy(budget))
                return single^
            if fewest >= 0 and r > fewest:
                continue
            if r < fewest:
                configs = List[_Configuration]()
            fewest = r
            configs.append(config^)
        # The smallest image max norm keeps the lifted coefficients small.
        var best = 0
        var norm = Integer(-1)
        for i in range(len(configs)):
            budget.charge(1)
            var m = Integer(0)
            for c in configs[i].image.coefficients:
                var a = _abs(c.value)
                if a > m:
                    m = a^
            if norm.sign() < 0 or m < norm:
                norm = m^
                best = i
        var distributed = _lead_coefficients(f, main, params, lead_factors, configs[best], budget)
        sequence.radius = _sum(sequence.radius, 1)
        if not distributed:
            continue
        var target = distributed.value()[0].copy()
        var bound = _imul(_mignotte(target, budget), Integer(2), budget)
        _work(bound.magnitude_bit_length() // 8 + 1, 0, True, budget)
        var p: Integer
        try:
            p = next_prime(bound)
        except e:
            raise PolyError(PolyErrorKind.CAPACITY, String(e))
        var initial = List[SparsePoly[ZZ]]()
        for h in distributed.value()[1]:
            initial.append(h.to_sparse(f.order, budget))
        var lifted: Optional[List[SparsePoly[ZZ]]]
        try:
            lifted = _lift(target, main, params, configs[best].points, initial^, distributed.value()[2], p, budget)
        except e:
            if e.kind != PolyErrorKind.DOMAIN:
                raise e^
            lifted = None
        if not lifted:
            continue
        var result = List[SparsePoly[ZZ]]()
        for g in lifted.value():
            budget.charge(1)
            result.append(_primitive_zz(g, budget))
        return result^
    return None
