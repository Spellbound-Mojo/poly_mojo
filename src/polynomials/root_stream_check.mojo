"""Independent root-stream checking with retained geometry and shared Sturm evidence."""
from apn_mojo import Rational
from .errors import Budget, PolyError, PolyErrorKind, _allocation, _sum
from .coefficients import QQ, CoefficientRing
from .dense import DensePoly
from .numeric_dense import NumericDensePoly
from .numeric_domains import NumericDomain
from .numeric_options import NumericOptions, NumericOutcome, _accurate
from .numeric_bounds import NumericBox, _box_valid, _box_real, _box_charge
from .numeric_evaluate import _exact_dense_boxes, _numeric_dense_boxes
from ._numeric_roots import _root_degree, _root_bound, _rational_polynomial, _derivative_boxes, _disjoint
from .numeric_real_roots import RealRootCell, RealRootSink, _check_real_cell
from .numeric_complex_roots import ComplexRootRegion, ComplexRootSink, _representative, _check_region
from .algebraic_types import _copy_sequence as _copy_sturm
from .certificates import SturmSequence, _check_root_count_parts
from .roots import sign_changes
from ._root_ops import _compare, _chain_variations
from .root_stream import RootStreamReceipt


@fieldwise_init
struct RealRootStreamChecker(RealRootSink, Movable):
    """Verify real root witnesses incrementally without retaining completed proofs."""
    var _coefficients: List[NumericBox]
    var _options: NumericOptions
    var _degree: Int
    var _bound: QQ
    var _items: Int
    var _accurate: Bool
    var _isolated: Bool
    var _failed: Bool
    var _derivative: List[NumericBox]
    var _exact: Optional[DensePoly[QQ]]
    var _sequence: Optional[SturmSequence]
    var _edge: QQ
    var _variations: Int
    var _started: Bool

    @staticmethod
    def from_dense[C: CoefficientRing](poly: DensePoly[C], options: NumericOptions, mut budget: Budget) raises PolyError -> Self:
        """Prepare independent checking for an original polynomial.

        Parameters:
            C: The source coefficient domain.

        Args:
            poly: The original polynomial or coefficient family.
            options: The original requested guarantees.
            budget: The shared preparation allowance.

        Returns:
            A checker owning the input bounds and retained checking state.

        Raises:
            PolyError: DOMAIN for invalid input, UNSUPPORTED for unsupported domains, LIMIT or CAPACITY on work limits.
        """
        return Self._prepare(_exact_dense_boxes(poly, budget), options, budget)

    @staticmethod
    def from_numeric[D: NumericDomain](poly: NumericDensePoly[D], options: NumericOptions, mut budget: Budget) raises PolyError -> Self:
        """Prepare independent checking for an original polynomial.

        Parameters:
            D: The source coefficient domain.

        Args:
            poly: The original polynomial or coefficient family.
            options: The original requested guarantees.
            budget: The shared preparation allowance.

        Returns:
            A checker owning the input bounds and retained checking state.

        Raises:
            PolyError: DOMAIN for invalid input, UNSUPPORTED for unsupported domains, LIMIT or CAPACITY on work limits.
        """
        return Self._prepare(_numeric_dense_boxes(poly, budget), options, budget)

    @staticmethod
    def _prepare(var coefficients: List[NumericBox], options: NumericOptions, mut budget: Budget) raises PolyError -> Self:
        options._validate()
        var degree = _root_degree(coefficients, budget)
        var n = degree.value() if degree else -1
        var bound = _root_bound(coefficients, n, budget) if degree else QQ(Rational(0))
        var derivative = _derivative_boxes(coefficients, budget)
        var exact = _rational_polynomial(coefficients, budget)
        var edge = bound.neg(budget)
        return Self(coefficients^, options, n, bound^, 0, True, True, n < 0, derivative^, exact^, None, edge^, 0, False)

    def begin(mut self, sequence: Optional[SturmSequence], mut budget: Budget) raises PolyError:
        """Validate and retain the shared exact Sturm witness once.

        Args:
            sequence: The producer's shared evidence, absent for families.
            budget: The shared checking allowance.

        Raises:
            PolyError: DOMAIN for invalid or repeated headers, LIMIT or CAPACITY on work limits; failure invalidates this checker.
        """
        if self._failed or self._started:
            self._failed = True
            raise PolyError(PolyErrorKind.DOMAIN, "invalid root stream header")
        self._failed = True
        if Bool(sequence) != Bool(self._exact):
            raise PolyError(PolyErrorKind.DOMAIN, "root stream Sturm mismatch")
        if sequence:
            var first = _chain_variations(sequence.value().polynomials, sequence.value().quotients, self._edge, budget)
            var last = _chain_variations(sequence.value().polynomials, sequence.value().quotients, self._bound, budget)
            if not _check_root_count_parts(self._exact.value(), sequence.value(), self._edge, self._bound, first - last, budget):
                raise PolyError(PolyErrorKind.DOMAIN, "invalid root stream Sturm evidence")
            self._sequence = _copy_sturm(sequence.value(), budget)
            self._variations = first
        self._started = True
        self._failed = False

    def write(mut self, var witness: RealRootCell, mut budget: Budget) raises PolyError:
        """Check a producer witness directly as a streaming destination.

        Args:
            witness: The next owned local root certificate.
            budget: The shared checking allowance.

        Raises:
            PolyError: DOMAIN for rejected evidence, LIMIT or CAPACITY on work limits.
        """
        if not self.accept(witness^, budget):
            raise PolyError(PolyErrorKind.DOMAIN, "invalid root stream witness")

    def accept(mut self, var witness: RealRootCell, mut budget: Budget) raises PolyError -> Bool:
        """Check and discard a local witness while retaining coverage state.

        Args:
            witness: The next owned local certificate.
            budget: The shared checking allowance.

        Returns:
            Whether the witness is valid; rejection permanently invalidates the checker.

        Raises:
            PolyError: LIMIT or CAPACITY on work limits; failure invalidates the checker.
        """
        if self._failed:
            return False
        self._failed = True
        budget.charge(1)
        ref cell = witness
        if not self._started or not _box_valid(cell.interval, budget) or not _box_real(cell.interval, budget) or _compare(cell.interval.real_low, cell.interval.real_high, budget) >= 0 or cell.count < 0 or cell.interval.real_low != self._edge or _compare(cell.interval.real_high, self._bound, budget) > 0:
            return False
        var next_variations = _check_real_cell(self._coefficients, self._derivative, self._exact, self._sequence, cell, self._variations, budget)
        if not next_variations:
            return False
        var accurate = cell.count == 0 or _accurate(cell.interval, self._options, budget)
        _box_charge(cell.interval, budget)
        var items = _sum(self._items, 1)
        self._edge = cell.interval.real_high.copy()
        self._variations = next_variations.value()
        self._accurate = self._accurate and accurate
        self._isolated = self._isolated and cell.count <= 1
        self._items = items
        self._failed = False
        return True

    def finish(self, receipt: RootStreamReceipt, mut budget: Budget) raises PolyError -> Bool:
        """Check global completeness and all receipt claims after consumption.

        Args:
            receipt: The producer's completed receipt.
            budget: The shared checking allowance.

        Returns:
            True only for a complete valid stream with consistent outcome flags.

        Raises:
            PolyError: LIMIT on exhaustion.
        """
        budget.charge(1)
        if self._failed or not receipt.complete or receipt.items != self._items or receipt.accurate != self._accurate or receipt.isolated != self._isolated:
            return False
        if not self._started or not self._items or self._edge != self._bound:
            return False
        var success = self._accurate and (self._isolated or not self._options.require_isolation)
        return (receipt.outcome == NumericOutcome.SUCCESS and success) or (not success and (receipt.outcome == NumericOutcome.SUBDIVISION_LIMIT))


@fieldwise_init
struct ComplexRootStreamChecker(ComplexRootSink, Movable):
    """Verify complex root witnesses incrementally without retaining completed proofs."""
    var _coefficients: List[NumericBox]
    var _options: NumericOptions
    var _degree: Int
    var _bound: QQ
    var _items: Int
    var _accurate: Bool
    var _isolated: Bool
    var _failed: Bool
    var _representative: List[NumericBox]
    var _rectangles: List[NumericBox]
    var _total: Int

    @staticmethod
    def from_dense[C: CoefficientRing](poly: DensePoly[C], options: NumericOptions, mut budget: Budget) raises PolyError -> Self:
        """Prepare independent checking for an original polynomial.

        Parameters:
            C: The source coefficient domain.

        Args:
            poly: The original polynomial or coefficient family.
            options: The original requested guarantees.
            budget: The shared preparation allowance.

        Returns:
            A checker owning the input bounds and retained checking state.

        Raises:
            PolyError: DOMAIN for invalid input, UNSUPPORTED for unsupported domains, LIMIT or CAPACITY on work limits.
        """
        return Self._prepare(_exact_dense_boxes(poly, budget), options, budget)

    @staticmethod
    def from_numeric[D: NumericDomain](poly: NumericDensePoly[D], options: NumericOptions, mut budget: Budget) raises PolyError -> Self:
        """Prepare independent checking for an original polynomial.

        Parameters:
            D: The source coefficient domain.

        Args:
            poly: The original polynomial or coefficient family.
            options: The original requested guarantees.
            budget: The shared preparation allowance.

        Returns:
            A checker owning the input bounds and retained checking state.

        Raises:
            PolyError: DOMAIN for invalid input, UNSUPPORTED for unsupported domains, LIMIT or CAPACITY on work limits.
        """
        return Self._prepare(_numeric_dense_boxes(poly, budget), options, budget)

    @staticmethod
    def _prepare(var coefficients: List[NumericBox], options: NumericOptions, mut budget: Budget) raises PolyError -> Self:
        options._validate()
        var degree = _root_degree(coefficients, budget)
        var n = degree.value() if degree else -1
        var bound = _root_bound(coefficients, n, budget) if degree else QQ(Rational(0))
        var representative = _representative(coefficients, budget)
        return Self(coefficients^, options, n, bound^, 0, True, True, n < 0, representative^, List[NumericBox](), 0)

    def write(mut self, var witness: ComplexRootRegion, mut budget: Budget) raises PolyError:
        """Check a producer witness directly as a streaming destination.

        Args:
            witness: The next owned local root certificate.
            budget: The shared checking allowance.

        Raises:
            PolyError: DOMAIN for rejected evidence, LIMIT or CAPACITY on work limits.
        """
        if not self.accept(witness^, budget):
            raise PolyError(PolyErrorKind.DOMAIN, "invalid root stream witness")

    def accept(mut self, var witness: ComplexRootRegion, mut budget: Budget) raises PolyError -> Bool:
        """Check and discard a local witness while retaining coverage state.

        Args:
            witness: The next owned local certificate.
            budget: The shared checking allowance.

        Returns:
            Whether the witness is valid; rejection permanently invalidates the checker.

        Raises:
            PolyError: LIMIT or CAPACITY on work limits; failure invalidates the checker.
        """
        if self._failed:
            return False
        self._failed = True
        budget.charge(1)
        ref region = witness
        var global_box = NumericBox(self._bound.neg(budget), self._bound.copy(), self._bound.neg(budget), self._bound.copy())
        if region.count <= 0 or not global_box.contains(region.rectangle, budget) or not _check_region(self._coefficients, self._representative, region, budget):
            return False
        for rectangle in self._rectangles:
            if not _disjoint(region.rectangle, rectangle, budget, True):
                return False
        var total = _sum(self._total, region.count)
        if total > self._degree:
            return False
        var accurate = _accurate(region.rectangle, self._options, budget)
        _box_charge(region.rectangle, budget)
        _allocation[NumericBox](1, budget)
        var items = _sum(self._items, 1)
        self._rectangles.append(region.rectangle.copy())
        self._total = total
        self._accurate = self._accurate and accurate
        self._isolated = self._isolated and region.count == 1
        self._items = items
        self._failed = False
        return True

    def finish(self, receipt: RootStreamReceipt, mut budget: Budget) raises PolyError -> Bool:
        """Check global completeness and all receipt claims after consumption.

        Args:
            receipt: The producer's completed receipt.
            budget: The shared checking allowance.

        Returns:
            True only for a complete valid stream with consistent outcome flags.

        Raises:
            PolyError: LIMIT on exhaustion.
        """
        budget.charge(1)
        if self._failed or not receipt.complete or receipt.items != self._items or receipt.accurate != self._accurate or receipt.isolated != self._isolated:
            return False
        if self._total != self._degree:
            return False
        var success = self._accurate and (self._isolated or not self._options.require_isolation)
        return (receipt.outcome == NumericOutcome.SUCCESS and success) or (not success and (receipt.outcome == NumericOutcome.SUBDIVISION_LIMIT or receipt.outcome == NumericOutcome.UNRESOLVED_BOUNDARY))
