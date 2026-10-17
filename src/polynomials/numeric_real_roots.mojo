"""Bounded real isolation with Sturm or uniform interval-family certificates."""
from apn_mojo import Rational
from .coefficients import QQ, CoefficientRing, NoContext
from .dense import DensePoly
from .root_stream import RootStreamReceipt
from .errors import Budget, PolyError, PolyErrorKind, _allocation, _charge_size, _sum
from .evaluate import evaluate_dense
from .roots import sturm_sequence, sign_changes
from .certificates import SturmSequence, _check_root_count_parts
from ._root_ops import _compare, _midpoint, _chain_variations
from .numeric_domains import NumericDomain, BallDomain
from .numeric_dense import NumericDensePoly
from .numeric_bounds import NumericBox, numeric_bounds, _box_real, _box_zero, _box_sub, _box_div_real, _box_center, _box_valid
from .numeric_evaluate import EnclosureEvaluation, _evaluate_program, _check_program, _enclosure_context, _exact_dense_boxes, _numeric_dense_boxes
from ._numeric_program import _NumericProgram, _dense_program
from .numeric_options import NumericOptions, NumericOutcome, _accurate, _next_precision
from ._numeric_roots import _root_degree, _root_bound, _derivative_boxes, _rational_polynomial, _strict_inside, _require_success, _exact_box_evaluate


@fieldwise_init
struct RealRootCell(Copyable, Movable):
    """A real cover cell with a distinct-root count and local evidence."""
    var interval: NumericBox
    """The real interval; counted roots lie strictly inside it."""
    var count: Int
    """Distinct-root count, or minus one for an unresolved cell."""
    var method: UInt8
    """Zero for Sturm, one for image exclusion, two for signs, three/four for Newton."""
    var evaluations: List[EnclosureEvaluation[BallDomain]]
    """Image, derivative, midpoint, left and right traces as needed by the method."""


@fieldwise_init
struct RealRootResult(Copyable, Movable):
    """A checked real cover, with separate completeness and accuracy flags."""
    var outcome: NumericOutcome
    """SUCCESS only for all requested guarantees."""
    var complete: Bool
    """Every cell has a checked uniform count and outside roots are excluded."""
    var accurate: Bool
    """Every positive-count cell meets the requested widths."""
    var isolated: Bool
    """Every positive-count cell contains one distinct real root."""
    var cells: List[RealRootCell]
    """Ordered cover of the global search interval, including excluded cells."""
    var sequence: Optional[SturmSequence]
    """Shared exact-point Sturm evidence, absent for uncertain coefficient families."""


trait RealRootSink:
    """Consume completed real root witnesses without retaining their prefix."""

    def begin(mut self, sequence: Optional[SturmSequence], mut budget: Budget) raises PolyError:
        """Receive the shared exact Sturm witness before any cells.

        Args:
            sequence: Borrowed Sturm evidence, absent for coefficient families.
            budget: The shared transport allowance.

        Raises:
            PolyError: On transport or resource failure.
        """
        ...

    def write(mut self, var cell: RealRootCell, mut budget: Budget) raises PolyError:
        """Consume one completed real root witness.

        Args:
            cell: The next owned witness in traversal order.
            budget: The shared transport allowance.

        Raises:
            PolyError: On transport or resource failure.
        """
        ...


@fieldwise_init
struct _RealCollector(RealRootSink):
    var cells: List[RealRootCell]

    def begin(mut self, sequence: Optional[SturmSequence], mut budget: Budget) raises PolyError:
        pass

    def write(mut self, var cell: RealRootCell, mut budget: Budget) raises PolyError:
        _allocation[RealRootCell](1, budget)
        self.cells.append(cell^)


def _real_predicate(interval: NumericBox, images: List[NumericBox], mut budget: Budget) raises PolyError -> Tuple[Int, UInt8]:
    if len(images) == 0:
        return (-1, UInt8(1))
    if not _box_zero(images[0], budget):
        return (0, UInt8(1))
    if len(images) != 5 or _box_zero(images[1], budget):
        return (-1, UInt8(2))
    var left_positive = images[3].real_low.value.sign() > 0
    var left_negative = images[3].real_high.value.sign() < 0
    var right_positive = images[4].real_low.value.sign() > 0
    var right_negative = images[4].real_high.value.sign() < 0
    if (left_positive and right_negative) or (left_negative and right_positive):
        return (1, UInt8(2))
    var newton = _box_sub(_box_center(interval, budget), _box_div_real(images[2], images[1], budget), budget)
    if _strict_inside(newton, interval, budget, True):
        return (1, UInt8(3))
    if _compare(newton.real_high, interval.real_low, budget) < 0 or _compare(interval.real_high, newton.real_low, budget) < 0:
        return (0, UInt8(4))
    return (-1, UInt8(2))


def _family_cell(coefficients: List[NumericBox], derivative: List[NumericBox], interval: NumericBox, options: NumericOptions, mut budget: Budget) raises PolyError -> RealRootCell:
    var bits = options.initial_precision
    # Rational program inputs do not change when only working precision changes.
    var program = _dense_program(coefficients, interval, budget)
    var extra = List[_NumericProgram]()
    while True:
        var ctx = _enclosure_context[BallDomain](bits, options.max_precision)
        _allocation[EnclosureEvaluation[BallDomain]](5, budget)
        _allocation[NumericBox](5, budget)
        var proofs = List[EnclosureEvaluation[BallDomain]]()
        var images = List[NumericBox]()
        proofs.append(_evaluate_program[BallDomain](program, ctx, budget))
        images.append(numeric_bounds[BallDomain](proofs[0].value(budget), budget))
        if _box_zero(images[0], budget):
            if not len(extra):
                _allocation[_NumericProgram](4, budget)
                extra.reserve(4)
                extra.append(_dense_program(derivative, interval, budget))
                var middle = _box_center(interval, budget)
                var left = NumericBox.point(interval.real_low, QQ(Rational(0)), budget)
                var right = NumericBox.point(interval.real_high, QQ(Rational(0)), budget)
                for argument in [middle^, left^, right^]:
                    extra.append(_dense_program(coefficients, argument, budget))
            for prepared in extra:
                proofs.append(_evaluate_program[BallDomain](prepared, ctx, budget))
            for i in range(1, 5):
                images.append(numeric_bounds[BallDomain](proofs[i].value(budget), budget))
        var predicate = _real_predicate(interval, images, budget)
        if predicate[0] >= 0 or bits == options.max_precision:
            return RealRootCell(interval.copy(), predicate[0], predicate[1], proofs^)
        bits = _next_precision(bits, options.max_precision)


def _real_cell(coefficients: List[NumericBox], derivative: List[NumericBox], exact: Optional[DensePoly[QQ]], sequence: Optional[SturmSequence], interval: NumericBox, options: NumericOptions, mut budget: Budget) raises PolyError -> RealRootCell:
    if exact:
        var count = _chain_variations(sequence.value().polynomials, sequence.value().quotients, interval.real_low, budget) - _chain_variations(sequence.value().polynomials, sequence.value().quotients, interval.real_high, budget)
        return RealRootCell(interval.copy(), count, 0, List[EnclosureEvaluation[BallDomain]]())
    return _family_cell(coefficients, derivative, interval, options, budget)


def _real_split(coefficients: List[NumericBox], interval: NumericBox, exact: Optional[DensePoly[QQ]], degree: Int, mut budget: Budget) raises PolyError -> QQ:
    var width = interval.real_high.sub(interval.real_low, budget)
    for k in range(1, degree + 2):
        var fraction = QQ(Rational(k)).mul(QQ(Rational(k + 1)).inverse(budget), budget)
        var middle = interval.real_low.add(width.mul(fraction, budget), budget)
        if (exact and not evaluate_dense(exact.value(), middle, budget).is_zero()) or (not exact and not _box_zero(_exact_box_evaluate(coefficients, NumericBox.point(middle, QQ(Rational(0)), budget), budget), budget)):
            return middle^
    return _midpoint(interval.real_low, interval.real_high, budget)


def _family_count_changes(coefficients: List[NumericBox], bound: QQ, mut budget: Budget) raises PolyError -> Bool:
    # Two explicit family members with different global Sturm counts prove
    # that no uniform distinct-real-root count exists. Agreement proves nothing.
    _allocation[QQ](len(coefficients), budget)
    _allocation[QQ](len(coefficients), budget)
    var low = List[QQ]()
    var high = List[QQ]()
    for box in coefficients:
        if not _box_real(box, budget):
            raise PolyError(PolyErrorKind.DOMAIN, "real roots require real coefficients")
        _charge_size(box.real_low.size(), budget)
        _charge_size(box.real_high.size(), budget)
        low.append(box.real_low.copy())
        high.append(box.real_high.copy())
    var a = DensePoly[QQ].from_coefficients(0, NoContext(), low^, budget)
    var b = DensePoly[QQ].from_coefficients(0, NoContext(), high^, budget)
    var sa = sturm_sequence(a, budget)
    var sb = sturm_sequence(b, budget)
    var left = bound.neg(budget)
    return _chain_variations(sa.polynomials, sa.quotients, left, budget) - _chain_variations(sa.polynomials, sa.quotients, bound, budget) != _chain_variations(sb.polynomials, sb.quotients, left, budget) - _chain_variations(sb.polynomials, sb.quotients, bound, budget)


def _real_roots(coefficients: List[NumericBox], options: NumericOptions, mut budget: Budget, complete_only: Bool) raises PolyError -> RealRootResult:
    options._validate()
    var exact = _rational_polynomial(coefficients, budget)
    var degree = _root_degree(coefficients, budget)
    if not degree:
        _require_success(NumericOutcome.UNCERTAIN_DEGREE, complete_only)
        return RealRootResult(NumericOutcome.UNCERTAIN_DEGREE, False, False, False, List[RealRootCell](), None)
    var sequence = Optional[SturmSequence]()
    if exact:
        sequence = sturm_sequence(exact.value(), budget)
    var bound = _root_bound(coefficients, degree.value(), budget)
    if not exact and _family_count_changes(coefficients, bound, budget):
        _require_success(NumericOutcome.INPUT_UNCERTAINTY, complete_only)
        return RealRootResult(NumericOutcome.INPUT_UNCERTAINTY, False, False, False, List[RealRootCell](), None)
    var interval = NumericBox.real_interval(bound.neg(budget), bound, budget)
    var derivative = _derivative_boxes(coefficients, budget)
    _allocation[RealRootCell](1, budget)
    var pending: List[RealRootCell] = [_real_cell(coefficients, derivative, exact, sequence, interval, options, budget)]
    return _refine_real_cells(coefficients, derivative, exact, sequence^, pending^, degree.value(), options, budget, complete_only)


def _refine_real_cells(coefficients: List[NumericBox], derivative: List[NumericBox], exact: Optional[DensePoly[QQ]], var sequence: Optional[SturmSequence], var pending: List[RealRootCell], degree: Int, options: NumericOptions, mut budget: Budget, complete_only: Bool) raises PolyError -> RealRootResult:
    var sink = _RealCollector(List[RealRootCell]())
    var receipt = _refine_real_cells_to(coefficients, derivative, exact, sequence, pending^, degree, options, budget, complete_only, sink)
    var completed = List[RealRootCell]()
    swap(completed, sink.cells)
    return RealRootResult(receipt.outcome, receipt.complete, receipt.accurate, receipt.isolated, completed^, sequence^)


def _refine_real_cells_to[S: RealRootSink](coefficients: List[NumericBox], derivative: List[NumericBox], exact: Optional[DensePoly[QQ]], sequence: Optional[SturmSequence], var pending: List[RealRootCell], degree: Int, options: NumericOptions, mut budget: Budget, complete_only: Bool, mut sink: S) raises PolyError -> RootStreamReceipt:
    var items = 0
    var splits = 0
    var complete = True
    var accurate = True
    var isolated = True
    # Sturm variations at each pending cell's endpoints, minus one until
    # evaluated; a split shares its new point between both halves.
    var variations = List[Tuple[Int, Int]](length=len(pending), fill=(-1, -1))
    while len(pending):
        budget.charge(1)
        var cell = pending.pop()
        var known = variations.pop()
        var enough = cell.count == 0 or (cell.count > 0 and _accurate(cell.interval, options, budget) and (not options.require_isolation or cell.count == 1))
        if enough or splits == options.max_subdivisions:
            complete = complete and cell.count >= 0
            accurate = accurate and (cell.count == 0 or (cell.count > 0 and _accurate(cell.interval, options, budget)))
            isolated = isolated and cell.count >= 0 and cell.count <= 1
            items = _sum(items, 1)
            sink.write(cell^, budget)
            continue
        splits += 1
        var split = _real_split(coefficients, cell.interval, exact, degree, budget)
        var left = NumericBox.real_interval(cell.interval.real_low, split, budget)
        var right = NumericBox.real_interval(split, cell.interval.real_high, budget)
        _allocation[RealRootCell](2, budget)
        if exact:
            ref chain = sequence.value()
            var low = known[0] if known[0] >= 0 else _chain_variations(chain.polynomials, chain.quotients, cell.interval.real_low, budget)
            var high = known[1] if known[1] >= 0 else _chain_variations(chain.polynomials, chain.quotients, cell.interval.real_high, budget)
            var middle = _chain_variations(chain.polynomials, chain.quotients, split, budget)
            pending.append(RealRootCell(right^, middle - high, 0, List[EnclosureEvaluation[BallDomain]]()))
            pending.append(RealRootCell(left^, low - middle, 0, List[EnclosureEvaluation[BallDomain]]()))
            variations.append((middle, high))
            variations.append((low, middle))
            continue
        var right_cell = _real_cell(coefficients, derivative, exact, sequence, right, options, budget)
        var left_cell = _real_cell(coefficients, derivative, exact, sequence, left, options, budget)
        if cell.count >= 0 and (left_cell.count < 0 or right_cell.count < 0 or _sum(left_cell.count, right_cell.count) != cell.count):
            # A family may cross every available cut. Retain its certified
            # parent instead of replacing a proved count with unresolved data.
            accurate = accurate and _accurate(cell.interval, options, budget)
            isolated = isolated and cell.count <= 1
            items = _sum(items, 1)
            sink.write(cell^, budget)
            continue
        pending.append(right_cell^)
        pending.append(left_cell^)
        variations.append((-1, -1))
        variations.append((-1, -1))
    var outcome = NumericOutcome.SUCCESS if complete and accurate and (isolated or not options.require_isolation) else NumericOutcome.SUBDIVISION_LIMIT
    _require_success(outcome, complete_only)
    return RootStreamReceipt(outcome, complete, accurate, isolated, items)


def _check_real(coefficients: List[NumericBox], result: RealRootResult, options: NumericOptions, mut budget: Budget, *, allow_partial: Bool = False) raises PolyError -> Bool:
    options._validate()
    var degree = _root_degree(coefficients, budget)
    if not degree or (not result.complete and not allow_partial) or len(result.cells) == 0:
        return False
    var exact = _rational_polynomial(coefficients, budget)
    if Bool(exact) != Bool(result.sequence):
        return False
    var bound = _root_bound(coefficients, degree.value(), budget)
    if result.cells[0].interval.real_low != bound.neg(budget) or result.cells[len(result.cells) - 1].interval.real_high != bound:
        return False
    var previous_variations = 0
    if exact:
        var total = 0
        for cell in result.cells:
            if cell.count < 0:
                return False
            total = _sum(total, cell.count)
            budget.charge(1)
        var left = bound.neg(budget)
        if not _check_root_count_parts(exact.value(), result.sequence.value(), left, bound, total, budget):
            return False
        previous_variations = _chain_variations(result.sequence.value().polynomials, result.sequence.value().quotients, left, budget)
    var derivative = _derivative_boxes(coefficients, budget)
    var complete = True
    var accurate = True
    var isolated = True
    for i in range(len(result.cells)):
        ref cell = result.cells[i]
        if not _box_valid(cell.interval, budget) or not _box_real(cell.interval, budget) or _compare(cell.interval.real_low, cell.interval.real_high, budget) >= 0 or cell.count < -1 or (cell.count < 0 and not allow_partial):
            return False
        if i and result.cells[i - 1].interval.real_high != cell.interval.real_low:
            return False
        var next_variations = _check_real_cell(coefficients, derivative, exact, result.sequence, cell, previous_variations, budget)
        if not next_variations:
            return False
        previous_variations = next_variations.value()
        complete = complete and cell.count >= 0
        accurate = accurate and (cell.count == 0 or (cell.count > 0 and _accurate(cell.interval, options, budget)))
        isolated = isolated and cell.count >= 0 and cell.count <= 1
    var success = complete and accurate and (isolated or not options.require_isolation)
    return result.complete == complete and result.accurate == accurate and result.isolated == isolated and ((result.outcome == NumericOutcome.SUCCESS and success) or (result.outcome == NumericOutcome.SUBDIVISION_LIMIT and not success))


def real_roots_exact[C: CoefficientRing](poly: DensePoly[C], options: NumericOptions, mut budget: Budget, *, complete_only: Bool = False) raises PolyError -> RealRootResult:
    """Isolate distinct real roots of an exact ZZ/QQ polynomial.

    Parameters:
        C: ZZ or QQ.

    Args:
        poly: The original univariate polynomial.
        options: Accuracy, isolation and resource settings.
        budget: The shared work allowance.
        complete_only: Raise unless every requested guarantee succeeds.

    Returns:
        A cover with shared Sturm evidence and explicit outcome flags.

    Raises:
        PolyError: DOMAIN for zero or invalid input, UNSUPPORTED for other domains, LIMIT or CAPACITY on resource limits.
    """
    return _real_roots(_exact_dense_boxes(poly, budget), options, budget, complete_only)


def real_roots_numeric[D: NumericDomain](poly: NumericDensePoly[D], options: NumericOptions, mut budget: Budget, *, complete_only: Bool = False) raises PolyError -> RealRootResult:
    """Isolate real roots uniformly over stored real coefficient enclosures.

    Parameters:
        D: A numerical coefficient domain with real coefficients.

    Args:
        poly: The point or coefficient-family polynomial.
        options: Accuracy, isolation and resource settings.
        budget: The shared work allowance.
        complete_only: Raise unless every requested guarantee succeeds.

    Returns:
        A complete checked cover or an explicitly inconclusive analysis.

    Raises:
        PolyError: DOMAIN for zero or nonreal input, LIMIT or CAPACITY on resource limits.
    """
    return _real_roots(_numeric_dense_boxes(poly, budget), options, budget, complete_only)


def check_real_roots_exact[C: CoefficientRing](poly: DensePoly[C], result: RealRootResult, options: NumericOptions, mut budget: Budget) raises PolyError -> Bool:
    """Verify a complete real cover without repeating root search.

    Parameters:
        C: ZZ or QQ.

    Args:
        poly: The original exact polynomial.
        result: The proposed complete cover and evidence.
        options: The original accuracy and isolation requirements.
        budget: The shared work allowance.

    Returns:
        Whether coverage, counts and outcome flags are justified.

    Raises:
        PolyError: DOMAIN for invalid input, LIMIT or CAPACITY on resource limits.
    """
    return _check_real(_exact_dense_boxes(poly, budget), result, options, budget)


def check_real_roots_numeric[D: NumericDomain](poly: NumericDensePoly[D], result: RealRootResult, options: NumericOptions, mut budget: Budget) raises PolyError -> Bool:
    """Verify uniform real-root counts for a numerical coefficient family.

    Parameters:
        D: The original numerical coefficient domain.

    Args:
        poly: The original point or family polynomial.
        result: The proposed complete cover and evidence.
        options: The original accuracy and isolation requirements.
        budget: The shared work allowance.

    Returns:
        Whether all local witnesses and global coverage are valid.

    Raises:
        PolyError: DOMAIN for invalid input, LIMIT or CAPACITY on resource limits.
    """
    return _check_real(_numeric_dense_boxes(poly, budget), result, options, budget)


def _real_roots_to[S: RealRootSink](coefficients: List[NumericBox], options: NumericOptions, mut budget: Budget, complete_only: Bool, mut sink: S) raises PolyError -> RootStreamReceipt:
    options._validate()
    var exact = _rational_polynomial(coefficients, budget)
    var degree = _root_degree(coefficients, budget)
    if not degree:
        _require_success(NumericOutcome.UNCERTAIN_DEGREE, complete_only)
        return RootStreamReceipt(NumericOutcome.UNCERTAIN_DEGREE, False, False, False, 0)
    var sequence = Optional[SturmSequence]()
    if exact:
        sequence = sturm_sequence(exact.value(), budget)
    var bound = _root_bound(coefficients, degree.value(), budget)
    if not exact and _family_count_changes(coefficients, bound, budget):
        _require_success(NumericOutcome.INPUT_UNCERTAINTY, complete_only)
        return RootStreamReceipt(NumericOutcome.INPUT_UNCERTAINTY, False, False, False, 0)
    var interval = NumericBox.real_interval(bound.neg(budget), bound, budget)
    var derivative = _derivative_boxes(coefficients, budget)
    _allocation[RealRootCell](1, budget)
    var pending: List[RealRootCell] = [_real_cell(coefficients, derivative, exact, sequence, interval, options, budget)]
    sink.begin(sequence, budget)
    return _refine_real_cells_to(coefficients, derivative, exact, sequence, pending^, degree.value(), options, budget, complete_only, sink)


def real_roots_exact_to[C: CoefficientRing, S: RealRootSink](poly: DensePoly[C], options: NumericOptions, mut sink: S, mut budget: Budget, *, complete_only: Bool = False) raises PolyError -> RootStreamReceipt:
    """Produce real root witnesses directly into an incremental consumer.

    Parameters:
        C: The source coefficient domain.
        S: The witness destination type.

    Args:
        poly: The original polynomial or coefficient family.
        options: The explicit accuracy and subdivision settings.
        sink: The consumer receiving completed witnesses.
        budget: The shared computation and transport allowance.
        complete_only: Raise unless all requested guarantees hold.

    Returns:
        A completion receipt; the receipt alone is not a root certificate.

    Raises:
        PolyError: DOMAIN for invalid input, UNSUPPORTED for unsupported domains, LIMIT or CAPACITY on work limits; failure can leave an incomplete destination.
    """
    return _real_roots_to(_exact_dense_boxes(poly, budget), options, budget, complete_only, sink)


def real_roots_numeric_to[D: NumericDomain, S: RealRootSink](poly: NumericDensePoly[D], options: NumericOptions, mut sink: S, mut budget: Budget, *, complete_only: Bool = False) raises PolyError -> RootStreamReceipt:
    """Produce real root witnesses directly into an incremental consumer.

    Parameters:
        D: The source coefficient domain.
        S: The witness destination type.

    Args:
        poly: The original polynomial or coefficient family.
        options: The explicit accuracy and subdivision settings.
        sink: The consumer receiving completed witnesses.
        budget: The shared computation and transport allowance.
        complete_only: Raise unless all requested guarantees hold.

    Returns:
        A completion receipt; the receipt alone is not a root certificate.

    Raises:
        PolyError: DOMAIN for invalid input, UNSUPPORTED for unsupported domains, LIMIT or CAPACITY on work limits; failure can leave an incomplete destination.
    """
    return _real_roots_to(_numeric_dense_boxes(poly, budget), options, budget, complete_only, sink)


def _check_real_cell(coefficients: List[NumericBox], derivative: List[NumericBox], exact: Optional[DensePoly[QQ]], sequence: Optional[SturmSequence], cell: RealRootCell, previous_variations: Int, mut budget: Budget) raises PolyError -> Optional[Int]:
    if exact:
        if cell.method != 0 or len(cell.evaluations) or evaluate_dense(exact.value(), cell.interval.real_high, budget).is_zero():
            return None
        var next_variations = _chain_variations(sequence.value().polynomials, sequence.value().quotients, cell.interval.real_high, budget)
        if cell.count != previous_variations - next_variations:
            return None
        return next_variations
    else:
        var n = len(cell.evaluations)
        if n != 1 and n != 5:
            return None
        _allocation[NumericBox](5, budget)
        var arguments: List[NumericBox] = [cell.interval.copy(), cell.interval.copy(), _box_center(cell.interval, budget), NumericBox.point(cell.interval.real_low, QQ(Rational(0)), budget), NumericBox.point(cell.interval.real_high, QQ(Rational(0)), budget)]
        var images = List[NumericBox]()
        for j in range(n):
            if not _check_program[BallDomain](_dense_program(derivative if j == 1 else coefficients, arguments[j], budget), cell.evaluations[j], budget):
                return None
            images.append(numeric_bounds[BallDomain](cell.evaluations[j].value(budget), budget))
        var predicate = _real_predicate(cell.interval, images, budget)
        if predicate[0] != cell.count or predicate[1] != cell.method:
            return None
    return previous_variations
