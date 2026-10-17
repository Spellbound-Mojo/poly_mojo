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
from .algebraic_types import RealAlgebraic, AlgebraicComparisonCertificate, _rational, _copy_real, _check_real, _check_comparison
from .algebraic import algebraic_compare
from ._algebraic import _compare, _refine, _NormalizationCache
from ._root_ops import _compare as _compare_q, _midpoint
from .algebraic_specialization import _specialize_cached, check_algebraic_specialization, _zero_specialization, _coefficients
from .algebraic_roots import _roots_with_cache, _roots_in_context, _RootsContext, check_algebraic_roots
from .evaluate import derivative
from .lazard import _lazard_cached, check_lazard_evaluation
from .cad_projection import CADProjectionCertificate
from .cad_types import CADPolynomialLift, CADStackCertificate


def _sector(roots: List[RealAlgebraic], gap: Int, mut budget: Budget) raises PolyError -> RealAlgebraic:
    if len(roots) == 0:
        return _rational(QQ.zero(NoContext()), budget)
    if gap == 0:
        return _rational(roots[0].low.sub(QQ.one(NoContext()), budget), budget)
    if gap == len(roots):
        return _rational(roots[gap - 1].high.add(QQ.one(NoContext()), budget), budget)
    var left = _copy_real(roots[gap - 1], budget)
    var right = _copy_real(roots[gap], budget)
    while _compare_q(left.high, right.low, budget) >= 0:
        budget.charge(1)
        _refine(left, budget)
        _refine(right, budget)
    return _rational(_midpoint(left.high, right.low, budget), budget)


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


def _stack(projection: CADProjectionCertificate, parent: Int, level: Int, point: List[Tuple[Int64, RealAlgebraic]], dimension: Int, seed: Optional[RealAlgebraic], mut budget: Budget) raises PolyError -> CADStackCertificate:
    var cache = _NormalizationCache()
    return _stack_cached(projection, parent, level, point, dimension, seed, cache, budget)


def _stack_cached(projection: CADProjectionCertificate, parent: Int, level: Int, point: List[Tuple[Int64, RealAlgebraic]], dimension: Int, seed: Optional[RealAlgebraic], mut cache: _NormalizationCache, mut budget: Budget) raises PolyError -> CADStackCertificate:
    var variable = projection.variables[level]
    var lifts = List[CADPolynomialLift]()
    for f in projection.levels[level]:
        budget.charge(1)
        var lift = CADPolynomialLift(None, None, None)
        if projection.lazard:
            var evaluation = _lazard_cached(f, variable, point, cache, budget)
            # The lifting polynomial is f differentiated by the vanishing orders.
            var lifting = f._copy(budget)
            for i in range(len(point)):
                for _ in range(evaluation.orders[i]):
                    budget.charge(1)
                    lifting = derivative(lifting, point[i][0], budget)
            lift.roots = _roots_in_context(_coefficients(evaluation.evaluations[len(evaluation.evaluations) - 1], variable, budget), _RootsContext(lifting^, variable, _copy_point(point, budget)), cache, budget)
            lift.lazard = evaluation^
        else:
            var evaluation = _specialize_cached(f, point, cache, budget)
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
    var equalities = List[AlgebraicComparisonCertificate]()
    for i in range(len(lifts)):
        budget.charge(1)
        if not lifts[i].roots:
            continue
        ref originals = lifts[i].roots.value().roots
        for j in range(len(originals)):
            budget.charge(1)
            _allocation[AlgebraicComparisonCertificate](1, budget)
            equalities.append(algebraic_compare(originals[j], roots[mapping[i][j]], budget))
    var ordering = List[AlgebraicComparisonCertificate]()
    for i in range(1, len(roots)):
        budget.charge(1)
        _allocation[AlgebraicComparisonCertificate](1, budget)
        ordering.append(algebraic_compare(roots[i - 1], roots[i], budget))
    _allocation[RealAlgebraic](_sum(_product(2, len(roots)), 1), budget)
    var samples = List[RealAlgebraic]()
    for gap in range(_sum(len(roots), 1)):
        budget.charge(1)
        samples.append(_sector(roots, gap, budget))
        if gap < len(roots):
            samples.append(_copy_real(roots[gap], budget))
    if seed:
        samples[_position(roots, seed.value(), budget)] = _copy_real(seed.value(), budget)
    var separations = List[AlgebraicComparisonCertificate]()
    for i in range(len(samples)):
        budget.charge(1)
        var gap = i // 2
        if i % 2:
            _allocation[AlgebraicComparisonCertificate](1, budget)
            separations.append(algebraic_compare(samples[i], roots[gap], budget))
        else:
            if gap:
                _allocation[AlgebraicComparisonCertificate](1, budget)
                separations.append(algebraic_compare(roots[gap - 1], samples[i], budget))
            if gap < len(roots):
                _allocation[AlgebraicComparisonCertificate](1, budget)
                separations.append(algebraic_compare(samples[i], roots[gap], budget))
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
