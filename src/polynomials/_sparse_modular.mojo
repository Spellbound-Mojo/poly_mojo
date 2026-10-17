"""Recursive modular support discovery without multivariate remainder sequences.

Source-guided by Z3 2d08bfc, polynomial.cpp mod_gcd_rec. Univariate content
and leading coefficients fix specialization scaling; sparse polynomial
Newton interpolation discovers support, with exact division as the gate.
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
from .errors import Budget, PolyError, _allocation, _sum, _charge_size
from .coefficients import CoefficientRing, ModInt
from .sparse import SparsePoly, Term
from .dense import DensePoly
from .monomial import Monomial
from ._gcd import _gcd_value, _normalized
from ._views import _variables, _one, _zero
from ._tower import _exact_poly
from ._dense_ops import _gcd as _univariate_gcd, _exact as _exact_dense
from .division import divide_exact
from .evaluate import evaluate_dense, evaluate
from .certificates import _dense_equal
from ._modular_linear import _insert_row, _solve_rows
from ._grouping import _without, _coefficient_groups, _index_groups, _separate
from ._powers import _powers


struct _SupportCache(Movable):
    var variables: List[List[Int64]]
    var supports: List[List[Monomial]]
    var hits: Int

    def __init__(out self):
        self.variables = List[List[Int64]]()
        self.supports = List[List[Monomial]]()
        self.hits = 0


def _cache_index(variables: List[Int64], mut cache: _SupportCache, mut budget: Budget) raises PolyError -> Int:
    for i in range(len(cache.variables)):
        budget.charge(1)
        _charge_size(_sum(len(variables), len(cache.variables[i])), budget)
        if variables == cache.variables[i]:
            return i
    var index = len(cache.variables)
    _allocation[List[Int64]](1, budget)
    _allocation[List[Monomial]](1, budget)
    _allocation[Int64](len(variables), budget)
    cache.variables.append(variables.copy())
    cache.supports.append(List[Monomial]())
    return index


def _remember(f: SparsePoly[ModInt], index: Int, mut cache: _SupportCache, mut budget: Budget) raises PolyError:
    _allocation[Monomial](len(f.terms), budget)
    var support = List[Monomial]()
    for term in f.terms:
        budget.charge(1)
        _charge_size(len(term.monomial.pairs), budget)
        support.append(term.monomial.copy())
    cache.supports[index] = support^


def _coefficients[C: CoefficientRing](f: SparsePoly[C], variable: Int64, univariate: Bool, mut budget: Budget) raises PolyError -> List[SparsePoly[C]]:
    var grouped = _coefficient_groups(f, variable, univariate, budget)
    var result = List[SparsePoly[C]]()
    swap(result, grouped[1])
    return result^


def _content_leading(f: SparsePoly[ModInt], variable: Int64, mut budget: Budget) raises PolyError -> Tuple[DensePoly[ModInt], DensePoly[ModInt]]:
    # variable is the final variable of the lexicographic order. Removing it
    # preserves the order of all other monomials, so the last group is leading.
    var groups = _coefficients(f, variable, True, budget)
    var content = DensePoly[ModInt](variable, f.ring.copy())
    for g in groups:
        budget.charge(1)
        content = _univariate_gcd(content, DensePoly[ModInt].from_sparse(g, budget, variable=variable), budget)
        if content.degree() == 0:
            break
    return (content^, DensePoly[ModInt].from_sparse(groups[len(groups) - 1], budget, variable=variable))


def _at(f: SparsePoly[ModInt], variable: Int64, value: ModInt, mut budget: Budget) raises PolyError -> SparsePoly[ModInt]:
    _allocation[Term[ModInt]](len(f.terms), budget)
    var terms = List[Term[ModInt]](capacity=len(f.terms))
    var powers = _powers(value, budget)
    # The variable is the last of the LEX order, so dropping it keeps the
    # remaining monomials in order and equal ones adjacent: merge in one
    # pass. Any other order is detected and sorted as before.
    var ordered = True
    for term in f.terms:
        budget.charge(1)
        var parts = _separate(term.monomial, variable, budget)
        var coefficient = term.coefficient.mul(powers.power(UInt64(parts[0]), budget), budget)
        var monomial = Monomial()
        swap(monomial, parts[1])
        if len(terms):
            var last = len(terms) - 1
            if terms[last].monomial == monomial:
                terms[last].coefficient = terms[last].coefficient.add(coefficient, budget)
                continue
            if ordered and f.order._compare(terms[last].monomial, monomial, budget) > 0:
                ordered = False
        terms.append(Term[ModInt](monomial^, coefficient^))
    if not ordered:
        return SparsePoly[ModInt].from_terms(terms^, f.order, f.ring, budget)
    var kept = List[Term[ModInt]](capacity=len(terms))
    for i in range(len(terms)):
        if not terms[i].coefficient.is_zero():
            var t = Term[ModInt](Monomial(), ModInt.zero(f.ring))
            swap(t, terms[i])
            kept.append(t^)
    var result = SparsePoly[ModInt].zero(f.order, f.ring, budget)
    result.terms = kept^
    return result^


def _support_interpolate(support: List[Monomial], variable: Int64, points: List[ModInt], images: List[SparsePoly[ModInt]], mut budget: Budget) raises PolyError -> Optional[SparsePoly[ModInt]]:
    var count = len(support)
    ref exemplar = images[0]
    _allocation[Term[ModInt]](count, budget)
    _allocation[UInt32](count, budget)
    var keys = List[Term[ModInt]](capacity=count)
    var exponents = List[UInt32](capacity=count)
    for monomial in support:
        budget.charge(1)
        var parts = _separate(monomial, variable, budget)
        exponents.append(parts[0])
        var key = Monomial()
        swap(key, parts[1])
        keys.append(Term[ModInt](key^, ModInt.one(exemplar.ring)))
    var groups = _index_groups(keys, budget)
    _allocation[List[ModInt]](count, budget)
    var rows = List[List[ModInt]](length=count, fill=List[ModInt]())
    var rank = 0
    for sample in range(len(points)):
        budget.charge(1)
        var powers = _powers(points[sample], budget)
        for group in groups:
            budget.charge(1)
            _allocation[ModInt](_sum(count, 1), budget)
            var row = List[ModInt](length=count + 1, fill=ModInt.zero(exemplar.ring))
            for j in group:
                budget.charge(1)
                row[j] = powers.power(UInt64(exponents[j]), budget)
            ref key = keys[group[0]].monomial
            for term in images[sample].terms:
                budget.charge(1)
                _charge_size(_sum(len(term.monomial.pairs), len(key.pairs)), budget)
                if term.monomial == key:
                    row[count] = term.coefficient.copy()
                    break
            var added = _insert_row(rows, row^, budget)
            if added < 0:
                return None
            rank += added
    if rank != count:
        return None
    var coefficients = _solve_rows(rows, exemplar.ring, budget)
    _allocation[Term[ModInt]](count, budget)
    var terms = List[Term[ModInt]]()
    for j in range(count):
        budget.charge(1)
        _charge_size(len(support[j].pairs), budget)
        terms.append(Term[ModInt](support[j].copy(), coefficients[j].copy()))
    return SparsePoly[ModInt].from_terms(terms^, exemplar.order, exemplar.ring, budget)


def _validated(interpolant: SparsePoly[ModInt], gamma: DensePoly[ModInt], a: SparsePoly[ModInt], b: SparsePoly[ModInt], variable: Int64, best: Monomial, mut budget: Budget) raises PolyError -> Optional[SparsePoly[ModInt]]:
    if interpolant.is_zero():
        return None
    var data = _content_leading(interpolant, variable, budget)
    if not _dense_equal(data[1], gamma, budget):
        return None
    var candidate = _exact_poly(interpolant, data[0].to_sparse(a.order, budget), budget)
    var candidate_leading = _without(candidate.terms[len(candidate.terms) - 1].monomial, variable, budget)
    _charge_size(_sum(len(candidate_leading.pairs), len(best.pairs)), budget)
    if candidate_leading != best or not divide_exact(a, candidate, budget) or not divide_exact(b, candidate, budget):
        return None
    return candidate^


def _modular_gcd(f: SparsePoly[ModInt], g: SparsePoly[ModInt], mut budget: Budget) raises PolyError -> Optional[SparsePoly[ModInt]]:
    var cache = _SupportCache()
    return _modular_gcd_cached(f, g, cache, budget)


def _modular_gcd_cached(f: SparsePoly[ModInt], g: SparsePoly[ModInt], mut cache: _SupportCache, mut budget: Budget) raises PolyError -> Optional[SparsePoly[ModInt]]:
    var variables = _variables(f, g, budget)
    if f.is_zero() or g.is_zero() or len(variables) <= 1:
        return _gcd_value(f, g, budget)
    var variable = variables[len(variables) - 1]
    var cache_index = _cache_index(variables, cache, budget)
    var left = _content_leading(f, variable, budget)
    var right = _content_leading(g, variable, budget)
    var common = _univariate_gcd(left[0], right[0], budget).to_sparse(f.order, budget)
    var a = _exact_poly(f, left[0].to_sparse(f.order, budget), budget)
    var b = _exact_poly(g, right[0].to_sparse(g.order, budget), budget)
    var leading_a = _exact_dense(left[1], left[0], budget)
    var leading_b = _exact_dense(right[1], right[0], budget)
    var gamma = _univariate_gcd(leading_a, leading_b, budget)
    var best: Optional[Monomial] = None
    var interpolant = _zero(f, budget)
    var newton = _one(f, budget)
    var indeterminate = SparsePoly[ModInt].variable(variable, f.order, f.ring, budget)
    var sample = UInt64(0)
    var points = List[ModInt]()
    var images = List[SparsePoly[ModInt]]()
    while sample < f.ring.value:
        budget.charge(1)
        var value = ModInt(sample, f.ring)
        sample += 1
        if evaluate_dense(leading_a, value, budget).is_zero() or evaluate_dense(leading_b, value, budget).is_zero():
            continue
        # The sole recursive branch removes one variable (PG5).
        var image = _modular_gcd_cached(_at(a, variable, value, budget), _at(b, variable, value, budget), cache, budget)
        if not image:
            return None
        var h = image.take()
        ref leading = h.terms[len(h.terms) - 1]
        if len(leading.monomial.pairs) == 0:
            return _normalized(common, budget)
        var comparison = -1
        if best:
            comparison = f.order.compare(leading.monomial, best.value(), budget)
        if comparison > 0:
            continue
        if comparison < 0:
            _charge_size(len(leading.monomial.pairs), budget)
            best = leading.monomial.copy()
            interpolant = _zero(f, budget)
            newton = _one(f, budget)
            points = List[ModInt]()
            images = List[SparsePoly[ModInt]]()
        h = h.scale(evaluate_dense(gamma, value, budget).mul(leading.coefficient.inverse(budget), budget), budget)
        if len(cache.supports[cache_index]):
            _allocation[ModInt](1, budget)
            _allocation[SparsePoly[ModInt]](1, budget)
            points.append(value.copy())
            images.append(h._copy(budget))
            if len(points) >= len(cache.supports[cache_index]):
                var proposed = _support_interpolate(cache.supports[cache_index], variable, points, images, budget)
                if proposed:
                    var candidate = _validated(proposed.value(), gamma, a, b, variable, best.value(), budget)
                    if candidate:
                        cache.hits = _sum(cache.hits, 1)
                        return _normalized(common.mul(candidate.value(), budget), budget)
                # A stale or singular skeleton is only a hint. Continue the
                # independent Newton interpolant already built from these samples.
                cache.supports[cache_index] = List[Monomial]()
                points = List[ModInt]()
                images = List[SparsePoly[ModInt]]()
        _allocation[Tuple[Int64, ModInt]](1, budget)
        var denominator = evaluate(newton, [(variable, value.copy())], budget)
        var correction = h.sub(_at(interpolant, variable, value, budget), budget).scale(denominator.inverse(budget), budget)
        interpolant = interpolant.add(newton.mul(correction, budget), budget)
        newton = newton.mul(indeterminate.sub(SparsePoly[ModInt].constant(value, f.order, budget), budget), budget)
        var candidate = _validated(interpolant, gamma, a, b, variable, best.value(), budget)
        if candidate:
            _remember(interpolant, cache_index, cache, budget)
            return _normalized(common.mul(candidate.value(), budget), budget)
    # A finite field can exhaust good evaluation points. The integer caller
    # advances to the next prime; no guessed support is returned.
    return None
