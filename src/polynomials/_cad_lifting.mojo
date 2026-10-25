"""Exact root merging, rational sector sampling, and independent stack checks."""
# Source: SMT-RAT fc28c1d, delineation.h and smtrat-coveringng/Sampling.h.
# Copyright (c) 2015-2022 Florian Corzilius, Gereon Kremer, Jasper Nalbach,
# Sebastian Junges, Stefan Schupp, Erika Abraham.
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
from .errors import Budget, PolyError, PolyErrorKind, _allocation, _sum, _product
from .coefficients import QQ, NoContext
from apn_mojo import Rational
from .sparse import SparsePoly
from .algebraic_types import RealAlgebraic, AlgebraicComparisonCertificate, _rational, _copy_real, _check_real, _check_comparison
from ._algebraic import _compare, _comparison, _refine, _NormalizationCache, _Frame
from ._root_ops import _compare as _compare_q, _midpoint
from .algebraic_specialization import _specialize_cached, check_algebraic_specialization, _zero_specialization, _coefficients
from .algebraic_roots import _roots_with_cache, _roots_in_context, _RootsContext, check_algebraic_roots
from .evaluate import derivative
from .lazard import _lazard_cached, _lazard_memo, _LazardMemo, check_lazard_evaluation
from ._algebraic_filter import _rational_frame
from .cad_projection import CADProjectionCertificate
from .cad_types import CADPolynomialLift, CADStackCertificate


comptime _CANONICAL_SECTORS = True
"""Sector samples are the simplest rational of the open gap between roots,
whatever the roots' isolating intervals; otherwise the midpoint between them."""
def _floor(q: QQ, mut budget: Budget) raises PolyError -> QQ:
    budget.charge(1)
    try:
        var n = q.value.numerator()
        var d = q.value.denominator()
        var f = n // d
        return QQ(Rational(f))
    except e:
        raise PolyError(PolyErrorKind.CAPACITY, String(e))


def _simplest(low: Optional[QQ], high: Optional[QQ], mut budget: Budget) raises PolyError -> QQ:
    """The rational of least denominator, then least magnitude, in the open interval (low, high); None is infinite."""
    budget.charge(1)
    var zero = QQ.zero(NoContext())
    var one = QQ.one(NoContext())
    if (not low or low.value().value.sign() < 0) and (not high or high.value().value.sign() > 0):
        return zero^
    if high and high.value().value.sign() <= 0:
        var negated_low: Optional[QQ] = None
        if low:
            negated_low = low.value().neg(budget)
        return _simplest(high.value().neg(budget), negated_low, budget).neg(budget)
    # Now 0 <= low: the least integer above low, unless (low, high) lies in (f, f + 1].
    var f = _floor(low.value(), budget)
    var next = f.add(one, budget)
    if not high or _compare_q(next, high.value(), budget) < 0:
        return next^
    var below = low.value().sub(f, budget)
    var above = high.value().sub(f, budget)
    var upper: Optional[QQ] = None
    if not below.is_zero():
        upper = below.inverse(budget)
    var inner = _simplest(above.inverse(budget), upper, budget)
    return f.add(inner.inverse(budget), budget)


def _same_q(a: QQ, b: QQ, mut budget: Budget) raises PolyError -> Bool:
    return _compare_q(a, b, budget) == 0


def _sector(roots: List[RealAlgebraic], gap: Int, mut budget: Budget) raises PolyError -> RealAlgebraic:
    if len(roots) == 0:
        return _rational(QQ.zero(NoContext()), budget)
    comptime if not _CANONICAL_SECTORS:
        if gap == 0:
            return _rational(roots[0].low.sub(QQ.one(NoContext()), budget), budget)
        if gap == len(roots):
            return _rational(roots[gap - 1].high.add(QQ.one(NoContext()), budget), budget)
    var has_left = gap > 0
    var has_right = gap < len(roots)
    var left = _copy_real(roots[gap - 1 if has_left else gap], budget)
    var right = _copy_real(roots[gap if has_right else gap - 1], budget)
    if has_left and has_right:
        while _compare_q(left.high, right.low, budget) >= 0:
            budget.charge(1)
            _refine(left, budget)
            _refine(right, budget)
    comptime if not _CANONICAL_SECTORS:
        return _rational(_midpoint(left.high, right.low, budget), budget)
    # The simplest rational of the true gap: inside the gap between the inner
    # endpoints and simplest between the outer ones, so simplest in the gap.
    while True:
        budget.charge(1)
        var inner_low: Optional[QQ] = None
        var outer_low: Optional[QQ] = None
        var inner_high: Optional[QQ] = None
        var outer_high: Optional[QQ] = None
        if has_left:
            inner_low = left.high.copy()
            outer_low = left.low.copy()
        if has_right:
            inner_high = right.low.copy()
            outer_high = right.high.copy()
        var inner = _simplest(inner_low, inner_high, budget)
        if _same_q(inner, _simplest(outer_low, outer_high, budget), budget):
            return _rational(inner, budget)
        if has_left:
            _refine(left, budget)
        if has_right:
            _refine(right, budget)


def _position(roots: List[RealAlgebraic], value: RealAlgebraic, mut budget: Budget) raises PolyError -> Int:
    var low = 0
    var high = len(roots)
    while low < high:
        budget.charge(1)
        var middle = low + (high - low) // 2
        var relation = _compare(value, roots[middle], budget)
        if relation == 0:
            return _sum(_product(2, middle), 1)
        if relation < 0:
            high = middle
        else:
            low = middle + 1
    return _product(2, low)


def _merge_roots(lifts: List[CADPolynomialLift], mut budget: Budget) raises PolyError -> Tuple[List[RealAlgebraic], List[Tuple[Int, Int]], List[List[Int]]]:
    # Merge sorted runs of source indices. Algebraic values are copied only
    # once per distinct boundary, and equal values retain their first source.
    var runs = List[List[Tuple[Int, Int]]]()
    _allocation[List[Int]](len(lifts), budget)
    var mapping = List[List[Int]]()
    for i in range(len(lifts)):
        budget.charge(1)
        var count = len(lifts[i].roots.value().roots) if lifts[i].roots else 0
        _allocation[Int](count, budget)
        mapping.append(List[Int](length=count, fill=-1))
        if count == 0:
            continue
        _allocation[Tuple[Int, Int]](count, budget)
        var run = List[Tuple[Int, Int]](capacity=count)
        for j in range(count):
            budget.charge(1)
            run.append((i, j))
        _allocation[List[Tuple[Int, Int]]](1, budget)
        runs.append(run^)
    while len(runs) > 1:
        budget.charge(1)
        _allocation[List[Tuple[Int, Int]]](len(runs) // 2 + len(runs) % 2, budget)
        var merged = List[List[Tuple[Int, Int]]]()
        for i in range(0, len(runs), 2):
            budget.charge(1)
            var run = List[Tuple[Int, Int]]()
            if i + 1 == len(runs):
                swap(run, runs[i])
            else:
                _allocation[Tuple[Int, Int]](_sum(len(runs[i]), len(runs[i + 1])), budget)
                run = List[Tuple[Int, Int]](capacity=_sum(len(runs[i]), len(runs[i + 1])))
                var left = 0
                var right = 0
                while left < len(runs[i]) or right < len(runs[i + 1]):
                    budget.charge(1)
                    var take_left = right == len(runs[i + 1])
                    if left < len(runs[i]) and not take_left:
                        var a = runs[i][left]
                        var b = runs[i + 1][right]
                        take_left = _compare(lifts[a[0]].roots.value().roots[a[1]], lifts[b[0]].roots.value().roots[b[1]], budget) <= 0
                    if left < len(runs[i]) and take_left:
                        run.append(runs[i][left])
                        left += 1
                    else:
                        run.append(runs[i + 1][right])
                        right += 1
            merged.append(run^)
        runs = merged^
    var roots = List[RealAlgebraic]()
    var sources = List[Tuple[Int, Int]]()
    if len(runs):
        for source in runs[0]:
            budget.charge(1)
            ref root = lifts[source[0]].roots.value().roots[source[1]]
            if len(roots) == 0 or _compare(roots[len(roots) - 1], root, budget) != 0:
                _allocation[RealAlgebraic](1, budget)
                _allocation[Tuple[Int, Int]](1, budget)
                roots.append(_copy_real(root, budget))
                sources.append(source)
            mapping[source[0]][source[1]] = len(roots) - 1
    return (roots^, sources^, mapping^)


def _copy_point(point: List[Tuple[Int64, RealAlgebraic]], mut budget: Budget) raises PolyError -> List[Tuple[Int64, RealAlgebraic]]:
    _allocation[Tuple[Int64, RealAlgebraic]](len(point), budget)
    var result = List[Tuple[Int64, RealAlgebraic]](capacity=len(point))
    for entry in point:
        result.append((entry[0], _copy_real(entry[1], budget)))
    return result^


def _sample_lifting(projection: CADProjectionCertificate, stack: CADStackCertificate, point: List[Tuple[Int64, RealAlgebraic]], sample: Int, mut budget: Budget) raises PolyError -> Optional[SparsePoly[QQ]]:
    # The lifting polynomial whose specialization has a section sample as a root.
    if sample % 2 == 0:
        return None
    var source = stack.sources[sample // 2][0]
    var lifting = projection.levels[stack.level][source]._copy(budget)
    if projection.lazard:
        ref orders = stack.lifts[source].lazard.value().orders
        for i in range(len(point)):
            for _ in range(orders[i]):
                budget.charge(1)
                lifting = derivative(lifting, point[i][0], budget)
    return lifting^


def _stack(projection: CADProjectionCertificate, parent: Int, level: Int, point: List[Tuple[Int64, RealAlgebraic]], dimension: Int, seed: Optional[RealAlgebraic], mut budget: Budget) raises PolyError -> CADStackCertificate:
    var cache = _NormalizationCache()
    return _stack_cached(projection, parent, level, point, dimension, seed, cache, budget)


def _stack_cached(projection: CADProjectionCertificate, parent: Int, level: Int, point: List[Tuple[Int64, RealAlgebraic]], dimension: Int, seed: Optional[RealAlgebraic], mut cache: _NormalizationCache, mut budget: Budget) raises PolyError -> CADStackCertificate:
    var memo = _LazardMemo()
    return _stack_memo(projection, parent, level, point, dimension, seed, cache, memo, budget)


def _stack_memo(projection: CADProjectionCertificate, parent: Int, level: Int, point: List[Tuple[Int64, RealAlgebraic]], dimension: Int, seed: Optional[RealAlgebraic], mut cache: _NormalizationCache, mut memo: _LazardMemo, mut budget: Budget) raises PolyError -> CADStackCertificate:
    # As _stack_cached, with Lazard evaluation steps kept between stacks.
    var variable = projection.variables[level]
    var lifts = List[CADPolynomialLift](capacity=len(projection.levels[level]))
    # At a rational point a rational generator lets each specialized
    # coefficient be evaluated directly over Q instead of step by step; the
    # cache's own frame comes back before the roots are isolated.
    var rational = len(point) > 0 and not cache.frame
    for entry in point:
        if not entry[1].rational:
            rational = False
    var specializing: Optional[_Frame] = None
    if rational:
        specializing = _rational_frame(point, budget)
    for f in projection.levels[level]:
        budget.charge(1)
        var lift = CADPolynomialLift(None, None, None)
        if projection.lazard:
            if rational:
                cache.frame = specializing.copy()
            var evaluation = _lazard_memo(f, variable, point, cache, memo, budget)
            if rational:
                cache.frame = None
            # The lifting polynomial is f differentiated by the vanishing orders.
            var lifting = f._copy(budget)
            for i in range(len(point)):
                for _ in range(evaluation.orders[i]):
                    budget.charge(1)
                    lifting = derivative(lifting, point[i][0], budget)
            lift.roots = _roots_in_context(_coefficients(evaluation.evaluations[len(evaluation.evaluations) - 1], variable, budget), _RootsContext(lifting^, variable, _copy_point(point, budget)), cache, budget)
            lift.lazard = evaluation^
        else:
            if rational:
                cache.frame = specializing.copy()
            var evaluation = _specialize_cached(f, point, cache, budget)
            if rational:
                cache.frame = None
            if _zero_specialization(evaluation, budget):
                if dimension != 0 or level != len(projection.variables) - 1:
                    raise PolyError(PolyErrorKind.UNSUPPORTED, "McCallum nullification requires Lazard mode at this cell")
            else:
                lift.roots = _roots_in_context(_coefficients(evaluation, variable, budget), _RootsContext(f._copy(budget), variable, _copy_point(point, budget)), cache, budget)
            lift.ordinary = evaluation^
        _allocation[CADPolynomialLift](1, budget)
        lifts.append(lift^)
    var merged = _merge_roots(lifts, budget)
    var roots = List[RealAlgebraic]()
    var sources = List[Tuple[Int, Int]]()
    var mapping = List[List[Int]]()
    swap(roots, merged[0])
    swap(sources, merged[1])
    swap(mapping, merged[2])
    # The stack builds every value it compares, so the comparisons skip the
    # public entry's re-verification of each value's Sturm witness.
    var count = 0
    for m in mapping:
        count += len(m)
    var equalities = List[AlgebraicComparisonCertificate](capacity=count)
    for i in range(len(lifts)):
        budget.charge(1)
        if not lifts[i].roots:
            continue
        ref originals = lifts[i].roots.value().roots
        for j in range(len(originals)):
            budget.charge(1)
            _allocation[AlgebraicComparisonCertificate](1, budget)
            equalities.append(_comparison(originals[j], roots[mapping[i][j]], budget))
    var ordering = List[AlgebraicComparisonCertificate](capacity=len(roots))
    for i in range(1, len(roots)):
        budget.charge(1)
        _allocation[AlgebraicComparisonCertificate](1, budget)
        ordering.append(_comparison(roots[i - 1], roots[i], budget))
    _allocation[RealAlgebraic](_sum(_product(2, len(roots)), 1), budget)
    var samples = List[RealAlgebraic](capacity=_sum(_product(2, len(roots)), 1))
    for gap in range(_sum(len(roots), 1)):
        budget.charge(1)
        samples.append(_sector(roots, gap, budget))
        if gap < len(roots):
            samples.append(_copy_real(roots[gap], budget))
    if seed:
        samples[_position(roots, seed.value(), budget)] = _copy_real(seed.value(), budget)
    var separations = List[AlgebraicComparisonCertificate](capacity=_product(2, len(roots)))
    for i in range(len(samples)):
        budget.charge(1)
        var gap = i // 2
        if i % 2:
            _allocation[AlgebraicComparisonCertificate](1, budget)
            separations.append(_comparison(samples[i], roots[gap], budget))
        else:
            if gap:
                _allocation[AlgebraicComparisonCertificate](1, budget)
                separations.append(_comparison(roots[gap - 1], samples[i], budget))
            if gap < len(roots):
                _allocation[AlgebraicComparisonCertificate](1, budget)
                separations.append(_comparison(samples[i], roots[gap], budget))
    return CADStackCertificate(parent, level, lifts^, roots^, sources^, mapping^, equalities^, ordering^, samples^, separations^)


def _relation(a: RealAlgebraic, b: RealAlgebraic, relation: Int, proofs: List[AlgebraicComparisonCertificate], mut cursor: Int, mut budget: Budget) raises PolyError -> Bool:
    if cursor >= len(proofs) or proofs[cursor].relation != relation or not _check_comparison(a, b, proofs[cursor], budget):
        return False
    cursor += 1
    return True


def _check_stack(projection: CADProjectionCertificate, parent: Int, level: Int, point: List[Tuple[Int64, RealAlgebraic]], dimension: Int, certificate: CADStackCertificate, mut budget: Budget) raises PolyError -> Bool:
    if certificate.parent != parent or certificate.level != level or len(certificate.lifts) != len(projection.levels[level]) or len(certificate.mapping) != len(certificate.lifts):
        return False
    var variable = projection.variables[level]
    var equality_cursor = 0
    for i in range(len(certificate.lifts)):
        budget.charge(1)
        ref f = projection.levels[level][i]
        ref lift = certificate.lifts[i]
        if projection.lazard:
            if lift.ordinary or not lift.lazard or not lift.roots:
                return False
            ref evaluation = lift.lazard.value()
            if not check_lazard_evaluation(f, variable, point, evaluation, budget) or not check_algebraic_roots(_coefficients(evaluation.evaluations[len(evaluation.evaluations) - 1], variable, budget), lift.roots.value(), budget):
                return False
        else:
            if lift.lazard or not lift.ordinary:
                return False
            ref evaluation = lift.ordinary.value()
            if not check_algebraic_specialization(f, point, evaluation, budget):
                return False
            if _zero_specialization(evaluation, budget):
                if lift.roots or dimension != 0 or level != len(projection.variables) - 1:
                    return False
            elif not lift.roots or not check_algebraic_roots(_coefficients(evaluation, variable, budget), lift.roots.value(), budget):
                return False
        if not lift.roots:
            if len(certificate.mapping[i]):
                return False
            continue
        ref original = lift.roots.value().roots
        if len(certificate.mapping[i]) != len(original):
            return False
        for j in range(len(original)):
            budget.charge(1)
            var index = certificate.mapping[i][j]
            if index < 0 or index >= len(certificate.roots) or not _relation(original[j], certificate.roots[index], 0, certificate.equalities, equality_cursor, budget):
                return False
    if equality_cursor != len(certificate.equalities) or len(certificate.sources) != len(certificate.roots):
        return False
    for i in range(len(certificate.sources)):
        budget.charge(1)
        var source = certificate.sources[i]
        if source[0] < 0 or source[0] >= len(certificate.mapping) or source[1] < 0 or source[1] >= len(certificate.mapping[source[0]]) or certificate.mapping[source[0]][source[1]] != i:
            return False
    var ordering_cursor = 0
    for i in range(1, len(certificate.roots)):
        budget.charge(1)
        if not _relation(certificate.roots[i - 1], certificate.roots[i], -1, certificate.ordering, ordering_cursor, budget):
            return False
    if ordering_cursor != len(certificate.ordering) or len(certificate.samples) != _sum(_product(2, len(certificate.roots)), 1):
        return False
    var sample_cursor = 0
    for i in range(len(certificate.samples)):
        budget.charge(1)
        ref sample = certificate.samples[i]
        var gap = i // 2
        if not _check_real(sample, budget):
            return False
        if i % 2:
            if not _relation(sample, certificate.roots[gap], 0, certificate.separations, sample_cursor, budget):
                return False
        else:
            if gap and not _relation(certificate.roots[gap - 1], sample, -1, certificate.separations, sample_cursor, budget):
                return False
            if gap < len(certificate.roots) and not _relation(sample, certificate.roots[gap], -1, certificate.separations, sample_cursor, budget):
                return False
    return sample_cursor == len(certificate.separations)
