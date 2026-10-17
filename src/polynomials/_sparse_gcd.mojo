"""Modular gcd reconstruction with support-based sparse interpolation.

Source-guided by Z3's polynomial.cpp skeleton/sparse_interpolator and
mod_gcd_rec. This variant solves for projectively normalized coefficients
simultaneously, avoiding a polynomial leading-coefficient multiplier.
"""
# Copyright (c) Microsoft Corporation. All rights reserved.
# MIT License
# Permission is hereby granted, free of charge, to any person obtaining a copy
# of this software and associated documentation files (the "Software"), to deal
# in the Software without restriction, including without limitation the rights
# to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
# copies of the Software, and to permit persons to whom the Software is
# furnished to do so, subject to the following conditions:
# The above copyright notice and this permission notice shall be included in
# all copies or substantial portions of the Software.
# THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
# IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
# FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
# AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
# LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
# OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
# THE SOFTWARE.
from apn_mojo import Integer
from ._images import _sparse_mod_image as _image
from .errors import Budget, PolyError, PolyErrorKind, _allocation, _sum, _product, _charge_size
from .coefficients import ZZ, ModInt, Modulus, NoContext
from .sparse import SparsePoly, Term
from .monomial import Monomial
from ._gcd import _gcd_value, _primitive_zz, _normalized
from ._sparse_modular import _modular_gcd_cached, _SupportCache, _coefficients
from ._coefficient_ops import _gcd_coefficient
from ._views import _variables, _one, _zero, _is_unit
from ._tower import _exact_poly
from ._dense_ops import _gcd as _dense_gcd
from .division import divide_exact
from .primes import prime, _residue, _merge_residue, _symmetric
from ._modular_linear import _insert_row, _solve_rows
from ._grouping import _CoefficientGroups
from ._sampling import _SamplingPlan, _point_powers


def _interpolate(f: SparsePoly[ModInt], g: SparsePoly[ModInt], support: List[Monomial], main: Int64, degree: Int, mut budget: Budget) raises PolyError -> Optional[SparsePoly[ModInt]]:
    var count = len(support)
    if count == 0:
        return None
    var unknowns = count - 1
    var variables = _variables(f, g, budget)
    _allocation[UInt64](len(variables), budget)
    var point = List[UInt64](length=len(variables), fill=1)
    var radius = UInt64(1)
    var left_plan = _SamplingPlan(f.terms, main, variables, budget)
    var right_plan = _SamplingPlan(g.terms, main, variables, budget)
    _allocation[Term[ModInt]](count, budget)
    var skeleton = List[Term[ModInt]](capacity=count)
    for monomial in support:
        budget.charge(1)
        _charge_size(len(monomial.pairs), budget)
        skeleton.append(Term[ModInt](monomial.copy(), ModInt.one(f.ring)))
    var support_plan: _SamplingPlan
    try:
        support_plan = _SamplingPlan(skeleton, main, variables, budget)
    except e:
        # A new prime may erase an entire variable from both images. Its old
        # support is only a hint: rediscover it instead of rejecting the call.
        if e.kind == PolyErrorKind.DOMAIN:
            return None
        raise e^
    _allocation[List[ModInt]](unknowns, budget)
    var rows = List[List[ModInt]](length=unknowns, fill=List[ModInt]())
    var rank = 0
    # A failed or singular interpolation is a hint to rediscover the support;
    # it is never accepted as a mathematical answer.
    for _ in range(_sum(_product(4, count), 8)):
        budget.charge(1)
        var powers = _point_powers(point, f.ring, budget)
        var a = left_plan.evaluate(f, powers, budget)
        var b = right_plan.evaluate(g, powers, budget)
        if a.degree() == left_plan.degree and b.degree() == right_plan.degree:
            var h = _dense_gcd(a, b, budget)
            if h.degree() < degree:
                return None
            if h.degree() == degree:
                _allocation[ModInt](count, budget)
                var samples = List[ModInt]()
                for i in range(count):
                    budget.charge(1)
                    samples.append(support_plan.sample(i, powers, f.ring, budget))
                for k in range(degree):
                    budget.charge(1)
                    _allocation[ModInt](count, budget)
                    var row = List[ModInt](length=count, fill=ModInt.zero(f.ring))
                    for j in range(count):
                        budget.charge(1)
                        var exponent = support_plan.exponents[j]
                        if exponent == k:
                            row[j] = samples[j].copy()
                        elif exponent == degree:
                            row[j] = samples[j].mul(h.coefficients[k], budget).neg(budget)
                    row[unknowns] = row[unknowns].neg(budget)
                    var added = _insert_row(rows, row^, budget)
                    if added < 0:
                        return None
                    rank += added
                if rank == unknowns:
                    var coefficients = _solve_rows(rows, f.ring, budget)
                    _allocation[ModInt](1, budget)
                    coefficients.append(ModInt.one(f.ring))
                    _allocation[Term[ModInt]](count, budget)
                    var terms = List[Term[ModInt]]()
                    for j in range(count):
                        budget.charge(1)
                        _charge_size(len(support[j].pairs), budget)
                        terms.append(Term[ModInt](support[j].copy(), coefficients[j].copy()))
                    var candidate = SparsePoly[ModInt].from_terms(terms^, f.order, f.ring, budget)
                    if not candidate.is_zero() and divide_exact(f, candidate, budget) and divide_exact(g, candidate, budget):
                        return candidate^
                    return None
        # Deterministic positive grids; no random seeds or hash ordering.
        for j in range(len(point) - 1, -1, -1):
            budget.charge(1)
            if variables[j] == main:
                continue
            if point[j] < radius:
                point[j] += 1
                break
            point[j] = 1
            if j == 0 or (j == 1 and variables[0] == main):
                radius += 1
    return None


def _primitive(f: SparsePoly[ZZ], g: SparsePoly[ZZ], main: Int64, mut budget: Budget) raises PolyError -> SparsePoly[ZZ]:
    var gamma = _gcd_coefficient(f.terms[len(f.terms) - 1].coefficient, g.terms[len(g.terms) - 1].coefficient, budget)
    var support = List[Monomial]()
    var residues = List[Integer]()
    var modulus = Integer(1)
    var best = _sum(min(Int(f.degree_in(main, budget)), Int(g.degree_in(main, budget))), 1)
    var index = 0
    var cache = _SupportCache()
    while True:
        budget.charge(1)
        var p = prime(index, budget)
        index = _sum(index, 1)
        if _residue(f.terms[len(f.terms) - 1].coefficient.value, p, budget) == 0 or _residue(g.terms[len(g.terms) - 1].coefficient.value, p, budget) == 0:
            continue
        var ctx = Modulus(_prime_value=p)
        var a = _image(f, ctx, budget)
        var b = _image(g, ctx, budget)
        var interpolated: Optional[SparsePoly[ModInt]] = None
        if len(support) and index % 4 != 0:
            interpolated = _interpolate(a, b, support, main, best, budget)
        if not interpolated:
            interpolated = _modular_gcd_cached(a, b, cache, budget)
        if not interpolated:
            continue
        var h = interpolated.take()
        var degree = Int(h.degree_in(main, budget))
        if degree > best:
            continue
        if degree == 0:
            return _one(f, budget)
        var changed = degree < best or len(h.terms) != len(support)
        if not changed:
            for j in range(len(support)):
                budget.charge(1)
                _charge_size(_sum(len(support[j].pairs), len(h.terms[j].monomial.pairs)), budget)
                if support[j] != h.terms[j].monomial:
                    changed = True
                    break
        if changed:
            best = degree
            _allocation[Monomial](len(h.terms), budget)
            _allocation[Integer](len(h.terms), budget)
            support = List[Monomial]()
            residues = List[Integer](length=len(h.terms), fill=Integer(0))
            modulus = Integer(1)
            for term in h.terms:
                budget.charge(1)
                _charge_size(len(term.monomial.pairs), budget)
                support.append(term.monomial.copy())
        h = h.scale(ModInt(_residue(gamma.value, p, budget), ctx), budget)
        for j in range(len(support)):
            budget.charge(1)
            residues[j] = _merge_residue(residues[j], modulus, h.terms[j].coefficient.value, p, budget)
        _charge_size(modulus.magnitude_bit_length() // 8 + 1, budget)
        modulus = ZZ(modulus.copy()).mul(ZZ(Integer(Int(p))), budget).value
        _allocation[Term[ZZ]](len(support), budget)
        var terms = List[Term[ZZ]]()
        for j in range(len(support)):
            budget.charge(1)
            _charge_size(len(support[j].pairs), budget)
            terms.append(Term[ZZ](support[j].copy(), ZZ(_symmetric(residues[j], modulus, budget))))
        var candidate = _primitive_zz(SparsePoly[ZZ].from_terms(terms^, f.order, NoContext(), budget), budget)
        if not candidate.is_zero() and Int(candidate.degree_in(main, budget)) == best and divide_exact(f, candidate, budget) and divide_exact(g, candidate, budget):
            return candidate^


def _by_size(sizes: List[Int], mut budget: Budget) raises PolyError -> List[Int]:
    """Indices in increasing size, ties by index (insertion sort; there are few coefficients)."""
    _allocation[Int](len(sizes), budget)
    var order = List[Int](capacity=len(sizes))
    for i in range(len(sizes)):
        budget.charge(1)
        var position = len(order)
        order.append(i)
        while position > 0 and sizes[order[position - 1]] > sizes[i]:
            budget.charge(1)
            order[position] = order[position - 1]
            position -= 1
        order[position] = i
    return order^


def _sparse_content(f: SparsePoly[ZZ], main: Int64, mut budget: Budget) raises PolyError -> SparsePoly[ZZ]:
    # The content is the same in any visiting order; small coefficients first
    # reach a unit, or a small common divisor, soonest.
    var result = _zero(f, budget)
    if len(f.terms) >= 64:
        var groups = _CoefficientGroups(f, main, budget)
        var sizes = List[Int]()
        for i in range(len(groups.starts) - 1):
            sizes.append(groups.starts[i + 1] - groups.starts[i])
        for i in _by_size(sizes, budget):
            var coefficient = groups.coefficient(f, i, budget)
            result = _sparse_gcd(result, coefficient, budget)
            if _is_unit(result, budget):
                break
        return result^
    var coefficients = _coefficients(f, main, False, budget)
    var sizes = List[Int]()
    for coefficient in coefficients:
        sizes.append(len(coefficient.terms))
    for i in _by_size(sizes, budget):
        budget.charge(1)
        result = _sparse_gcd(result, coefficients[i], budget)
        if _is_unit(result, budget):
            break
    return result^


def _sparse_gcd(f: SparsePoly[ZZ], g: SparsePoly[ZZ], mut budget: Budget) raises PolyError -> SparsePoly[ZZ]:
    var variables = _variables(f, g, budget)
    if f.is_zero() or g.is_zero() or len(variables) <= 1:
        return _gcd_value(f, g, budget)
    var main = variables[0]
    var cf = _sparse_content(f, main, budget)
    var cg = _sparse_content(g, main, budget)
    var common = _sparse_gcd(cf, cg, budget)
    var a = _exact_poly(f, cf, budget)
    var b = _exact_poly(g, cg, budget)
    return _normalized(common.mul(_primitive(a, b, main, budget), budget), budget)
