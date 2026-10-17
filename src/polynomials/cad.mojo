"""Certified sign-invariant cylindrical decomposition and individual cells.

Projection and lifting follow SMT-RAT and QEPCAD B. Cells
are indexed sections/sectors over their parents; their boundaries denote
root functions, not constants copied from a sample point.
"""
from .errors import Budget, PolyError, PolyErrorKind, _allocation, _sum
from .coefficients import QQ, NoContext
from .sparse import SparsePoly
from .algebraic_types import RealAlgebraic, AlgebraicComparisonCertificate, _rational, _copy_real, _check_real, _same_root
from .algebraic_specialization import AlgebraicPolynomialEvaluation
from .cad_projection import cad_projection, check_cad_projection
from .cad_types import CADCell, CADStackCertificate, CADCertificate, CADCellCertificate
from ._cad_common import _cell, _coordinates, _signs, _signs_cached, _check_signs, _signs_witnessed, _check_cell_signs
from .cad_types import CADSignWitness
from ._cad_lifting import _stack, _stack_cached, _check_stack, _position
from ._algebraic import _NormalizationCache
from ._cad_fiber_common import _validate_fixed, _selection


def cad(inputs: List[SparsePoly[QQ]], variables: List[Int64], mut budget: Budget, lazard: Bool = False) raises PolyError -> CADCertificate:
    """Decompose real coordinate space into certified sign-invariant cylindrical cells.

    Args:
        inputs: The rational polynomials whose signs must be invariant.
        variables: Distinct variables in base-to-top cylindrical order.
        budget: The shared work allowance.
        lazard: Whether to use Lazard projection and vanishing-order lifting.

    Returns:
        A complete tree of sections and sectors with projection, lifting, coverage and sign witnesses.

    Raises:
        PolyError: UNSUPPORTED for McCallum nullification outside a terminal point base, DOMAIN for malformed inputs, LIMIT or CAPACITY on work limits.
    """
    return _cad(inputs, variables, List[RealAlgebraic](), budget, lazard)


def _cad(inputs: List[SparsePoly[QQ]], variables: List[Int64], fixed: List[RealAlgebraic], mut budget: Budget, lazard: Bool) raises PolyError -> CADCertificate:
    _validate_fixed(fixed, len(variables), budget)
    var projection = cad_projection(inputs, variables, budget, lazard=lazard)
    _allocation[CADCell](1, budget)
    var cells: List[CADCell] = [_cell(-1, -1, 0, _rational(QQ.zero(NoContext()), budget), budget)]
    var stacks = List[CADStackCertificate]()
    var parent = 0
    # Sibling cells share every coordinate but the last, and the breadth-first
    # order keeps them adjacent; one cache serves each sibling group.
    var cache = _NormalizationCache()
    var group = -2
    while parent < len(cells):
        budget.charge(1)
        var point = _coordinates(cells, parent, variables, budget)
        var level = cells[parent].level + 1
        if cells[parent].parent != group:
            group = cells[parent].parent
            cache = _NormalizationCache()
        if level == len(variables):
            var evaluations = List[AlgebraicPolynomialEvaluation]()
            var signs = List[AlgebraicComparisonCertificate]()
            var witnesses = List[CADSignWitness]()
            _signs_witnessed(inputs, point[0], evaluations, signs, witnesses, cache, budget)
            cells[parent].evaluations = evaluations^
            cells[parent].signs = signs^
            cells[parent].witnesses = witnesses^
        else:
            var stack = _stack_cached(projection, parent, level, point[0], point[1], None, cache, budget)
            var selected = _selection(stack, fixed, budget)
            _allocation[CADCell](selected[1] - selected[0], budget)
            for i in range(selected[0], selected[1]):
                budget.charge(1)
                cells.append(_cell(parent, level, i, stack.samples[i], budget))
            _allocation[CADStackCertificate](1, budget)
            stacks.append(stack^)
        parent += 1
    return CADCertificate(projection^, cells^, stacks^)


def _check_cad(inputs: List[SparsePoly[QQ]], certificate: CADCertificate, fixed: List[RealAlgebraic], mut budget: Budget) raises PolyError -> Bool:
    if not check_cad_projection(inputs, certificate.projection, budget) or len(certificate.cells) == 0:
        return False
    ref variables = certificate.projection.variables
    _validate_fixed(fixed, len(variables), budget)
    ref cells = certificate.cells
    ref root = cells[0]
    if root.parent != -1 or root.level != -1 or root.position != 0 or not _same_root(root.sample, _rational(QQ.zero(NoContext()), budget), budget):
        return False
    var next_child = 1
    var next_stack = 0
    for parent in range(len(cells)):
        budget.charge(1)
        if parent >= next_child:
            return False
        var point = _coordinates(cells, parent, variables, budget)
        var level = cells[parent].level + 1
        if level == len(variables):
            if not _check_cell_signs(inputs, point[0], cells[parent], budget):
                return False
            continue
        if len(cells[parent].evaluations) or len(cells[parent].signs) or len(cells[parent].witnesses) or next_stack >= len(certificate.stacks):
            return False
        ref stack = certificate.stacks[next_stack]
        if not _check_stack(certificate.projection, parent, level, point[0], point[1], stack, budget):
            return False
        var selected = _selection(stack, fixed, budget)
        for i in range(selected[0], selected[1]):
            budget.charge(1)
            if next_child >= len(cells):
                return False
            ref child = cells[next_child]
            if child.parent != parent or child.level != level or child.position != i or not _same_root(child.sample, stack.samples[i], budget):
                return False
            next_child += 1
        next_stack += 1
    return next_child == len(cells) and next_stack == len(certificate.stacks)


def check_cad(inputs: List[SparsePoly[QQ]], certificate: CADCertificate, mut budget: Budget) raises PolyError -> Bool:
    """Verify global CAD sign invariance and cylindrical coverage from local witnesses.

    Args:
        inputs: The original polynomial family.
        certificate: The complete proposed decomposition.
        budget: The shared work allowance.

    Returns:
        Whether projection, every complete stack, the cell tree and all terminal signs are valid.

    Raises:
        PolyError: LIMIT or CAPACITY on work limits.
    """
    try:
        return _check_cad(inputs, certificate, List[RealAlgebraic](), budget)
    except e:
        if e.kind == PolyErrorKind.DOMAIN:
            return False
        raise e^


def cad_cell(inputs: List[SparsePoly[QQ]], variables: List[Int64], point: List[RealAlgebraic], mut budget: Budget, lazard: Bool = False) raises PolyError -> CADCellCertificate:
    """Construct only the cylindrical cell path containing an exact algebraic point.

    Args:
        inputs: The rational polynomials whose signs must be invariant.
        variables: Distinct variables in base-to-top order.
        point: Exact coordinates aligned with the variable order.
        budget: The shared work allowance.
        lazard: Whether to use Lazard projection and evaluation.

    Returns:
        A certified cell containing the point, with symbolic root-function boundaries and constant signs.

    Raises:
        PolyError: UNSUPPORTED for disallowed McCallum nullification, DOMAIN for invalid coordinates, LIMIT or CAPACITY on work limits.
    """
    if len(point) != len(variables):
        raise PolyError(PolyErrorKind.DOMAIN, "CAD point dimension mismatch")
    var projection = cad_projection(inputs, variables, budget, lazard=lazard)
    var prefix = List[Tuple[Int64, RealAlgebraic]]()
    var stacks = List[CADStackCertificate]()
    var positions = List[Int]()
    var dimension = 0
    for level in range(len(variables)):
        budget.charge(1)
        if not _check_real(point[level], budget):
            raise PolyError(PolyErrorKind.DOMAIN, "invalid CAD query coordinate")
        var stack = _stack(projection, level, level, prefix, dimension, _copy_real(point[level], budget), budget)
        var position = _position(stack.roots, point[level], budget)
        if position % 2 == 0:
            dimension = _sum(dimension, 1)
        _allocation[Tuple[Int64, RealAlgebraic]](1, budget)
        prefix.append((variables[level], _copy_real(point[level], budget)))
        _allocation[Int](1, budget)
        _allocation[CADStackCertificate](1, budget)
        positions.append(position)
        stacks.append(stack^)
    var evaluations = List[AlgebraicPolynomialEvaluation]()
    var signs = List[AlgebraicComparisonCertificate]()
    _signs(inputs, prefix, evaluations, signs, budget)
    return CADCellCertificate(projection^, stacks^, positions^, evaluations^, signs^)


def _check_cell(inputs: List[SparsePoly[QQ]], point: List[RealAlgebraic], certificate: CADCellCertificate, mut budget: Budget) raises PolyError -> Bool:
    ref variables = certificate.projection.variables
    if not check_cad_projection(inputs, certificate.projection, budget) or len(point) != len(variables) or len(certificate.stacks) != len(point) or len(certificate.positions) != len(point):
        return False
    var prefix = List[Tuple[Int64, RealAlgebraic]]()
    var dimension = 0
    for level in range(len(variables)):
        budget.charge(1)
        ref stack = certificate.stacks[level]
        var position = certificate.positions[level]
        if not _check_real(point[level], budget) or not _check_stack(certificate.projection, level, level, prefix, dimension, stack, budget):
            return False
        if position < 0 or position >= len(stack.samples) or not _same_root(stack.samples[position], point[level], budget):
            return False
        if position % 2 == 0:
            dimension = _sum(dimension, 1)
        _allocation[Tuple[Int64, RealAlgebraic]](1, budget)
        prefix.append((variables[level], _copy_real(point[level], budget)))
    return _check_signs(inputs, prefix, certificate.evaluations, certificate.signs, budget)


def check_cad_cell(inputs: List[SparsePoly[QQ]], point: List[RealAlgebraic], certificate: CADCellCertificate, mut budget: Budget) raises PolyError -> Bool:
    """Verify a sign-invariant cylindrical cell and exact query-point containment.

    Args:
        inputs: The original polynomial family.
        point: The original exact coordinates in the certificate's variable order.
        certificate: The proposed single-cell path.
        budget: The shared work allowance.

    Returns:
        Whether the certified cell contains the query point and has the stated constant signs.

    Raises:
        PolyError: LIMIT or CAPACITY on work limits.
    """
    try:
        return _check_cell(inputs, point, certificate, budget)
    except e:
        if e.kind == PolyErrorKind.DOMAIN:
            return False
        raise e^
