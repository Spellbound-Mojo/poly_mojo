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
from .cad_projection import cad_projection, check_cad_projection, CADProjectionCertificate, _cad_projection_brown
from .cad_types import CADCell, CADStackCertificate, CADCertificate, CADCellCertificate
from ._cad_common import _cell, _coordinates, _signs, _signs_cached, _check_signs, _signs_leveled, _check_cell_signs, _LazyFrame
from .cad_types import CADSignWitness
from ._cad_lifting import _stack, _stack_cached, _stack_memo, _check_stack, _position, _sample_lifting
from .lazard import _LazardMemo
from ._algebraic import _next_group, _NormalizationCache, _Frame
from ._algebraic_filter import _child_frame, _installed, _PointLevels
from ._cad_fiber_common import _validate_fixed, _selection
from .division import divide_exact


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


def _cad(inputs: List[SparsePoly[QQ]], variables: List[Int64], fixed: List[RealAlgebraic], mut budget: Budget, lazard: Bool, *, brown: Bool = False, brown_finite: Bool = False) raises PolyError -> CADCertificate:
    _validate_fixed(fixed, len(variables), budget)
    if brown and not lazard:
        raise PolyError(PolyErrorKind.DOMAIN, "Brown reductions require Lazard lifting")
    if brown_finite and not brown:
        raise PolyError(PolyErrorKind.DOMAIN, "finite nullification requires Brown projection")
    var projection = _cad_projection_brown(inputs, variables, budget, finite=brown_finite) if brown else cad_projection(inputs, variables, budget, lazard=lazard)
    _allocation[CADCell](1, budget)
    var cells: List[CADCell] = [_cell(-1, -1, 0, _rational(QQ.zero(NoContext()), budget), budget)]
    var stacks = List[CADStackCertificate]()
    var parent = 0
    # Sibling cells share every coordinate but the last, and the breadth-first
    # order keeps them adjacent; one cache serves each sibling group.
    var cache = _NormalizationCache()
    var group = -2
    # Each cell's frame writes its coordinates as polynomials in one generator,
    # for direct evaluation at points with several irrational coordinates.
    var frames: List[_Frame] = [_Frame()]
    # A terminal cell's frame serves only exact sign evaluations, which most
    # cells never reach: keep what builds it and build it on demand.
    var pending: List[Optional[_LazyFrame]] = [None]
    # An input vanishes at every section that is a root of a top-level basis
    # member dividing it; such a section is its sign witness.
    var dividing = _dividing(inputs, projection, budget)
    var sections: List[List[Int]] = [List[Int]()]
    # The bisections of the last terminal point: its siblings keep all but the last coordinate's.
    var levels = _PointLevels(List[RealAlgebraic](), budget)
    # Lazard evaluation steps of the last stack: the next sibling's point shares all but its last coordinate.
    var memo = _LazardMemo()
    while parent < len(cells):
        budget.charge(1)
        var point = _coordinates(cells, parent, variables, budget)
        var level = cells[parent].level + 1
        if cells[parent].parent != group:
            group = cells[parent].parent
            _next_group(cache)
        var frame = _Frame()
        swap(frame, frames[parent])
        var lazy: Optional[_LazyFrame] = None
        swap(lazy, pending[parent])
        if lazy:
            cache.frame = None
        else:
            cache.frame = _installed(frame, point[0], budget)
        if level == len(variables):
            var evaluations = List[AlgebraicPolynomialEvaluation]()
            var signs = List[AlgebraicComparisonCertificate]()
            var witnesses = List[CADSignWitness]()
            var vanishing = List[Int]()
            swap(vanishing, sections[parent])
            _signs_leveled(inputs, point[0], evaluations, signs, witnesses, cache, levels, budget, lazy, vanishing)
            cells[parent].evaluations = evaluations^
            cells[parent].signs = signs^
            cells[parent].witnesses = witnesses^
        else:
            var stack = _stack_memo(projection, parent, level, point[0], point[1], None, cache, memo, budget)
            var irrational = 0
            for entry in point[0]:
                if not entry[1].rational:
                    irrational += 1
            var selected = _selection(stack, fixed, budget)
            _allocation[CADCell](selected[1] - selected[0], budget)
            for i in range(selected[0], selected[1]):
                budget.charge(1)
                cells.append(_cell(parent, level, i, stack.samples[i], budget))
                sections.append(_first_divisors(_section_divisors(stack, i, dividing, budget)) if level + 1 == len(variables) else List[Int]())
                # A second irrational coordinate needs a gcd; a terminal cell
                # with two is signed by its own zero proofs and skips it.
                if frame.generator and not stack.samples[i].rational and level + 1 == len(variables) and irrational < 2:
                    var skipped = _Frame()
                    skipped.valid = False
                    frames.append(skipped^)
                    pending.append(None)
                    continue
                var lifting: Optional[SparsePoly[QQ]] = None
                if frame.generator and not stack.samples[i].rational:
                    lifting = _sample_lifting(projection, stack, point[0], i, budget)
                if level + 1 == len(variables):
                    frames.append(_Frame())
                    pending.append(_LazyFrame(frame.copy(), variables[level], lifting^, _copy_real(stack.samples[i], budget)))
                else:
                    frames.append(_child_frame(frame, variables[level], lifting, stack.samples[i], budget))
                    pending.append(None)
            _allocation[CADStackCertificate](1, budget)
            stacks.append(stack^)
        parent += 1
    return CADCertificate(projection^, cells^, stacks^)


def _dividing(inputs: List[SparsePoly[QQ]], projection: CADProjectionCertificate, mut budget: Budget) raises PolyError -> List[List[Int]]:
    """For each input, the top-level basis members dividing it exactly."""
    var result = List[List[Int]]()
    if len(projection.variables) == 0:
        return result^
    ref top = projection.levels[len(projection.variables) - 1]
    for f in inputs:
        var row = List[Int]()
        for j in range(len(top)):
            budget.charge(1)
            if divide_exact(f.reorder(top[j].order, budget), top[j], budget):
                row.append(j)
        _allocation[List[Int]](1, budget)
        result.append(row^)
    return result^


def _section_divisors(stack: CADStackCertificate, position: Int, dividing: List[List[Int]], mut budget: Budget) raises PolyError -> List[List[Int]]:
    """For each input, its dividing basis members with a root at the section in this stack position."""
    var result = List[List[Int]]()
    for i in range(len(dividing)):
        var row = List[Int]()
        if position % 2 == 1:
            var boundary = (position - 1) // 2
            for j in dividing[i]:
                if j < len(stack.mapping):
                    for k in stack.mapping[j]:
                        budget.charge(1)
                        if k == boundary:
                            row.append(j)
                            break
        result.append(row^)
    return result^


def _first_divisors(divisors: List[List[Int]]) -> List[Int]:
    var result = List[Int]()
    for row in divisors:
        result.append(row[0] if len(row) else -1)
    return result^


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
    var dividing = _dividing(inputs, certificate.projection, budget)
    # The checked stack of each cell that has one, for the section witnesses
    # of its terminal children.
    var stack_of = List[Int](length=len(cells), fill=-1)
    for parent in range(len(cells)):
        budget.charge(1)
        if parent >= next_child:
            return False
        var point = _coordinates(cells, parent, variables, budget)
        var level = cells[parent].level + 1
        if level == len(variables):
            var divisors = List[List[Int]]()
            var above = cells[parent].parent
            if above >= 0 and stack_of[above] >= 0:
                divisors = _section_divisors(certificate.stacks[stack_of[above]], cells[parent].position, dividing, budget)
            if not _check_cell_signs(inputs, point[0], cells[parent], budget, divisors):
                return False
            continue
        if len(cells[parent].evaluations) or len(cells[parent].signs) or len(cells[parent].witnesses) or next_stack >= len(certificate.stacks):
            return False
        ref stack = certificate.stacks[next_stack]
        if not _check_stack(certificate.projection, parent, level, point[0], point[1], stack, budget):
            return False
        stack_of[parent] = next_stack
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
