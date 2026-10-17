"""Shared CAD cells, coordinate paths, signs and constraint masks."""
from .errors import Budget, PolyError, PolyErrorKind, _allocation, _sum
from .coefficients import QQ, NoContext
from .sparse import SparsePoly
from .algebraic_types import RealAlgebraic, AlgebraicComparisonCertificate, _rational, _copy_real, _check_comparison
from .algebraic import algebraic_sign
from .algebraic_specialization import AlgebraicPolynomialEvaluation, _evaluate_sparse_cached, check_algebraic_evaluate_sparse
from .cad_types import CADCell
from ._algebraic import _NormalizationCache


def _cell(parent: Int, level: Int, position: Int, sample: RealAlgebraic, mut budget: Budget) raises PolyError -> CADCell:
    return CADCell(parent, level, position, _copy_real(sample, budget), List[AlgebraicPolynomialEvaluation](), List[AlgebraicComparisonCertificate]())


def _coordinates(cells: List[CADCell], index: Int, variables: List[Int64], mut budget: Budget) raises PolyError -> Tuple[List[Tuple[Int64, RealAlgebraic]], Int]:
    var indices = List[Int]()
    var dimension = 0
    var cursor = index
    var expected = cells[index].level
    while cursor != 0:
        budget.charge(1)
        if cursor < 0 or cursor >= len(cells) or expected < 0 or expected >= len(variables):
            raise PolyError(PolyErrorKind.DOMAIN, "invalid CAD parent chain")
        ref node = cells[cursor]
        if node.level != expected or node.parent < 0 or node.parent >= cursor:
            raise PolyError(PolyErrorKind.DOMAIN, "noncylindrical CAD parent chain")
        _allocation[Int](1, budget)
        indices.append(cursor)
        if node.position % 2 == 0:
            dimension = _sum(dimension, 1)
        expected -= 1
        cursor = node.parent
    if expected != -1:
        raise PolyError(PolyErrorKind.DOMAIN, "incomplete CAD parent chain")
    _allocation[Tuple[Int64, RealAlgebraic]](len(indices), budget)
    var point = List[Tuple[Int64, RealAlgebraic]]()
    for i in range(len(indices) - 1, -1, -1):
        budget.charge(1)
        ref node = cells[indices[i]]
        point.append((variables[node.level], _copy_real(node.sample, budget)))
    return (point^, dimension)


def _signs(inputs: List[SparsePoly[QQ]], point: List[Tuple[Int64, RealAlgebraic]], mut evaluations: List[AlgebraicPolynomialEvaluation], mut signs: List[AlgebraicComparisonCertificate], mut budget: Budget) raises PolyError:
    var cache = _NormalizationCache()
    _signs_cached(inputs, point, evaluations, signs, cache, budget)


def _signs_cached(inputs: List[SparsePoly[QQ]], point: List[Tuple[Int64, RealAlgebraic]], mut evaluations: List[AlgebraicPolynomialEvaluation], mut signs: List[AlgebraicComparisonCertificate], mut cache: _NormalizationCache, mut budget: Budget) raises PolyError:
    _allocation[AlgebraicPolynomialEvaluation](len(inputs), budget)
    _allocation[AlgebraicComparisonCertificate](len(inputs), budget)
    for f in inputs:
        budget.charge(1)
        var evaluation = _evaluate_sparse_cached(f, point, cache, budget)
        signs.append(algebraic_sign(evaluation.value, budget))
        evaluations.append(evaluation^)


def _check_signs(inputs: List[SparsePoly[QQ]], point: List[Tuple[Int64, RealAlgebraic]], evaluations: List[AlgebraicPolynomialEvaluation], signs: List[AlgebraicComparisonCertificate], mut budget: Budget) raises PolyError -> Bool:
    if len(evaluations) != len(inputs) or len(signs) != len(inputs):
        return False
    var zero = _rational(QQ.zero(NoContext()), budget)
    for i in range(len(inputs)):
        budget.charge(1)
        if not check_algebraic_evaluate_sparse(inputs[i], point, evaluations[i], budget) or not _check_comparison(evaluations[i].value, zero, signs[i], budget):
            return False
    return True


def _masks(inputs: List[SparsePoly[QQ]], masks: List[UInt8], mut budget: Budget) raises PolyError:
    if len(inputs) != len(masks):
        raise PolyError(PolyErrorKind.DOMAIN, "one allowed-sign mask is required per polynomial")
    for mask in masks:
        budget.charge(1)
        if mask > 7:
            raise PolyError(PolyErrorKind.DOMAIN, "allowed signs use only bits 1, 2 and 4")


def _violation(cell: CADCell, masks: List[UInt8], mut budget: Budget) raises PolyError -> Int:
    for i in range(len(masks)):
        budget.charge(1)
        if masks[i] & (UInt8(1) << UInt8(cell.signs[i].relation + 1)) == 0:
            return i
    return -1
