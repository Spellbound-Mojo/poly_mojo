"""Private producers for exact real algebraic arithmetic.

Source: Z3 2d08bfcad30cabb7b2819dd2f4c47b7bbf4c377f,
src/math/polynomial/algebraic_numbers.cpp, mk_binary and interval selection.
Pure Mojo adaptation using this package's rational polynomials and budgets.
"""
# Z3
# Copyright (c) Microsoft Corporation
# All rights reserved.
# MIT License
#
# Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files (the "Software"), to deal in the Software without restriction, including without limitation the rights to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is furnished to do so, subject to the following conditions:
#
# The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.
#
# THE SOFTWARE IS PROVIDED *AS IS*, WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.

from .errors import Budget, PolyError, PolyErrorKind, _allocation
from .coefficients import QQ, NoContext
from .dense import DensePoly
from .certificates import SturmSequence, RootCountCertificate, Factorization, _dense_equal
from ._dense_ops import _copy as _copy_poly, _gcd, _exact
from ._root_ops import _compare as _compare_q, _copy as _copy_q, _midpoint, _variations, _sign_at
from .roots import sturm_sequence, isolate_real_roots
from .factor import factor
from .algebraic_types import RealAlgebraic as _Real, AlgebraicComparisonCertificate as _Comparison, _copy_real, _copy_sequence, _rational
from .algebraic_arithmetic import AlgebraicArithmeticCertificate


struct _NormalizationCache(Movable):
    var polynomials: List[DensePoly[QQ]]
    var factorizations: List[Factorization[QQ]]
    var sequences: List[SturmSequence]
    # Arithmetic results are a function of the operation and the exact operand
    # witnesses, so a repeated step reuses its certificate unchanged.
    var operations: List[Int]
    var operands: List[Tuple[_Real, _Real]]
    var results: List[AlgebraicArithmeticCertificate]

    def __init__(out self):
        self.polynomials = List[DensePoly[QQ]]()
        self.factorizations = List[Factorization[QQ]]()
        self.sequences = List[SturmSequence]()
        self.operations = List[Int]()
        self.operands = List[Tuple[_Real, _Real]]()
        self.results = List[AlgebraicArithmeticCertificate]()


def _same_witness(a: _Real, b: _Real, mut budget: Budget) raises PolyError -> Bool:
    budget.charge(1)
    if a.rational != b.rational or a.polynomial.degree() != b.polynomial.degree():
        return False
    return a.low == b.low and a.high == b.high and _dense_equal(a.polynomial, b.polynomial, budget)


def _sturm_index(f: DensePoly[QQ], mut sequences: List[SturmSequence], mut budget: Budget) raises PolyError -> Int:
    for i in range(len(sequences)):
        budget.charge(1)
        if _dense_equal(sequences[i].polynomials[0], f, budget):
            return i
    var sequence = sturm_sequence(f, budget)
    _allocation[SturmSequence](1, budget)
    sequences.append(sequence^)
    return len(sequences) - 1


def _count_cached(f: DensePoly[QQ], low: QQ, high: QQ, mut sequences: List[SturmSequence], mut budget: Budget) raises PolyError -> Int:
    # Every interval is checked independently. Only the exact polynomial's
    # owned Sturm sequence is reused; returned witnesses receive budgeted copies.
    if _compare_q(low, high, budget) >= 0 or _sign_at(f, low, budget) == 0 or _sign_at(f, high, budget) == 0:
        raise PolyError(PolyErrorKind.DOMAIN, "root count requires ordered nonroot endpoints")
    var index = _sturm_index(f, sequences, budget)
    return _variations(sequences[index].polynomials, low, budget) - _variations(sequences[index].polynomials, high, budget)


def _root(f: DensePoly[QQ], low: QQ, high: QQ, mut budget: Budget) raises PolyError -> _Real:
    var cache = _NormalizationCache()
    return _root_cached(f, low, high, cache, budget)


def _root_cached(f: DensePoly[QQ], low: QQ, high: QQ, mut cache: _NormalizationCache, mut budget: Budget) raises PolyError -> _Real:
    f.check_invariants(budget)
    if f.degree() < 1:
        raise PolyError(PolyErrorKind.DOMAIN, "an algebraic root needs a nonconstant polynomial")
    var ordering = _compare_q(low, high, budget)
    if ordering == 0:
        if not _sign_at(f, low, budget) == 0:
            raise PolyError(PolyErrorKind.DOMAIN, "the rational point is not a root")
        return _rational(low, budget)
    if ordering > 0 or _count_cached(f, low, high, cache.sequences, budget) != 1:
        raise PolyError(PolyErrorKind.DOMAIN, "an algebraic interval must isolate exactly one root")
    var normalized = _copy_poly(f, budget)
    normalized.variable = 0
    var index = -1
    for i in range(len(cache.polynomials)):
        budget.charge(1)
        if _dense_equal(cache.polynomials[i], normalized, budget):
            index = i
            break
    if index < 0:
        var factors = factor(normalized, budget)
        index = len(cache.polynomials)
        _allocation[DensePoly[QQ]](1, budget)
        _allocation[Factorization[QQ]](1, budget)
        cache.polynomials.append(normalized^)
        cache.factorizations.append(factors^)
    for entry in cache.factorizations[index].factors:
        budget.charge(1)
        if _count_cached(entry[0], low, high, cache.sequences, budget) == 1:
            if entry[0].degree() == 1:
                return _rational(entry[0].coefficients[0].neg(budget).mul(entry[0].coefficients[1].inverse(budget), budget), budget)
            var sequence_index = _sturm_index(entry[0], cache.sequences, budget)
            var sequence = _copy_sequence(cache.sequences[sequence_index], budget)
            return _Real(_copy_poly(entry[0], budget), _copy_q(low, budget), _copy_q(high, budget), sequence^, False)
    raise PolyError(PolyErrorKind.DOMAIN, "no factor contains the selected root")


def _refine(mut a: _Real, mut budget: Budget) raises PolyError:
    budget.charge(1)
    if a.rational:
        return
    var middle = _midpoint(a.low, a.high, budget)
    if _sign_at(a.polynomial, middle, budget) == 0:
        # Keep the defining polynomial: refinement witnesses must remain
        # bound to their input, even for a nonminimal caller-built value.
        a.low = _midpoint(a.low, middle, budget)
        a.high = _midpoint(middle, a.high, budget)
    elif _variations(a.sequence.polynomials, a.low, budget) - _variations(a.sequence.polynomials, middle, budget) == 1:
        a.high = middle^
    else:
        a.low = middle^


def _interval_relation(a: _Real, b: _Real, mut budget: Budget) raises PolyError -> Optional[Int]:
    if a.rational and b.rational:
        return _compare_q(a.low, b.low, budget)
    if _compare_q(a.high, b.low, budget) <= 0:
        return -1
    if _compare_q(b.high, a.low, budget) <= 0:
        return 1
    return None


def _resolve_overlap(mut left: _Real, mut right: _Real, mut common: DensePoly[QQ], mut shared: Optional[RootCountCertificate], mut budget: Budget) raises PolyError -> Int:
    if left.rational or right.rational:
        if _sign_at(right.polynomial if left.rational else left.polynomial, left.low if left.rational else right.low, budget) == 0:
            return 0
    else:
        common = _gcd(left.polynomial, right.polynomial, budget)
        if common.degree() > 0:
            var low = _copy_q(left.low if _compare_q(left.low, right.low, budget) >= 0 else right.low, budget)
            var high = _copy_q(left.high if _compare_q(left.high, right.high, budget) <= 0 else right.high, budget)
            var sequence = sturm_sequence(common, budget)
            var count = _variations(sequence.polynomials, low, budget) - _variations(sequence.polynomials, high, budget)
            if count == 1:
                shared = RootCountCertificate(sequence^, low^, high^, count)
                return 0
    # Equality has been excluded on the original overlap. Refine once and keep
    # these endpoints for the ordering certificate instead of replaying the work.
    while True:
        budget.charge(1)
        _refine(left, budget)
        _refine(right, budget)
        var relation = _interval_relation(left, right, budget)
        if relation:
            return relation.value()


def _compare(a: _Real, b: _Real, mut budget: Budget) raises PolyError -> Int:
    var relation = _interval_relation(a, b, budget)
    if relation:
        return relation.value()
    var left = _copy_real(a, budget)
    var right = _copy_real(b, budget)
    var common = DensePoly[QQ](0, NoContext())
    var shared: Optional[RootCountCertificate] = None
    return _resolve_overlap(left, right, common, shared, budget)


def _comparison(a: _Real, b: _Real, mut budget: Budget) raises PolyError -> _Comparison:
    var left = _copy_real(a, budget)
    var right = _copy_real(b, budget)
    var common = DensePoly[QQ](0, NoContext())
    var shared: Optional[RootCountCertificate] = None
    var separated = _interval_relation(left, right, budget)
    var relation = separated.value() if separated else _resolve_overlap(left, right, common, shared, budget)
    if relation == 0 and not a.rational and not b.rational:
        var left_cofactor = _exact(a.polynomial, common, budget)
        var right_cofactor = _exact(b.polynomial, common, budget)
        return _Comparison(0, left^, right^, common^, left_cofactor^, right_cofactor^, shared^)
    return _Comparison(relation, left^, right^, DensePoly[QQ](0, NoContext()), DensePoly[QQ](0, NoContext()), DensePoly[QQ](0, NoContext()), None)


def _sign(a: _Real, mut budget: Budget) raises PolyError -> Int:
    if a.rational:
        budget.charge(1)
        return a.low.value.sign()
    var value = _copy_real(a, budget)
    while True:
        budget.charge(1)
        if value.low.value.sign() >= 0:
            return 1
        if value.high.value.sign() <= 0:
            return -1
        if value.polynomial.coefficients[0].is_zero():
            return 0
        _refine(value, budget)
        if value.rational:
            return value.low.value.sign()


def _roots(f: DensePoly[QQ], mut budget: Budget) raises PolyError -> List[_Real]:
    var cache = _NormalizationCache()
    return _roots_cached(f, cache, budget)


def _roots_cached(f: DensePoly[QQ], mut cache: _NormalizationCache, mut budget: Budget) raises PolyError -> List[_Real]:
    var isolation = isolate_real_roots(f, budget)
    var roots = List[_Real]()
    for q in isolation.exact_roots:
        budget.charge(1)
        _allocation[_Real](1, budget)
        roots.append(_rational(q, budget))
    for interval in isolation.intervals:
        budget.charge(1)
        _allocation[_Real](1, budget)
        roots.append(_root_cached(f, interval.low, interval.high, cache, budget))
    for i in range(1, len(roots)):
        budget.charge(1)
        var j = i
        while j > 0 and _compare(roots[j], roots[j - 1], budget) < 0:
            budget.charge(1)
            var moved = _copy_real(roots[j], budget)
            roots[j] = _copy_real(roots[j - 1], budget)
            roots[j - 1] = moved^
            j -= 1
    return roots^


def _roots_by_factors(f: DensePoly[QQ], mut cache: _NormalizationCache, mut budget: Budget) raises PolyError -> List[_Real]:
    # Every distinct real root of f, isolated on the irreducible factor that
    # defines it: smaller Sturm chains than isolating f, the same roots.
    var normalized = _copy_poly(f, budget)
    normalized.variable = 0
    var index = -1
    for i in range(len(cache.polynomials)):
        budget.charge(1)
        if _dense_equal(cache.polynomials[i], normalized, budget):
            index = i
            break
    if index < 0:
        var factors = factor(normalized, budget)
        index = len(cache.polynomials)
        _allocation[DensePoly[QQ]](1, budget)
        _allocation[Factorization[QQ]](1, budget)
        cache.polynomials.append(normalized^)
        cache.factorizations.append(factors^)
    var roots = List[_Real]()
    for entry in cache.factorizations[index].factors:
        budget.charge(1)
        ref p = entry[0]
        if p.degree() == 1:
            _allocation[_Real](1, budget)
            roots.append(_rational(p.coefficients[0].neg(budget).mul(p.coefficients[1].inverse(budget), budget), budget))
            continue
        var isolation = isolate_real_roots(p, budget)
        for interval in isolation.intervals:
            budget.charge(1)
            var sequence_index = _sturm_index(p, cache.sequences, budget)
            _allocation[_Real](1, budget)
            roots.append(_Real(_copy_poly(p, budget), _copy_q(interval.low, budget), _copy_q(interval.high, budget), _copy_sequence(cache.sequences[sequence_index], budget), False))
    for i in range(1, len(roots)):
        budget.charge(1)
        var j = i
        while j > 0 and _compare(roots[j], roots[j - 1], budget) < 0:
            budget.charge(1)
            var moved = _copy_real(roots[j], budget)
            roots[j] = _copy_real(roots[j - 1], budget)
            roots[j - 1] = moved^
            j -= 1
    return roots^
