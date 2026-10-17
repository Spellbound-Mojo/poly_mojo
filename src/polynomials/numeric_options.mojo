"""Deterministic accuracy targets and explicit inconclusive numerical outcomes."""
from apn_mojo import Integer, Rational
from .coefficients import QQ
from .errors import Budget, PolyError, PolyErrorKind, _charge_size
from ._root_ops import _compare, _power_of_two, _twos
from .numeric_bounds import NumericBox, _box_valid


@fieldwise_init
struct NumericOutcome(ImplicitlyCopyable, Equatable, Writable):
    """Classify a completed numerical request or an inconclusive analysis."""
    var code: UInt8
    """The stable outcome code."""
    comptime SUCCESS = Self(0)
    """The requested claims were established."""
    comptime UNCERTAIN_DEGREE = Self(1)
    """The leading coefficient may vanish."""
    comptime INPUT_UNCERTAINTY = Self(2)
    """Coefficient or argument uncertainty prevents the requested guarantee."""
    comptime PRECISION_CEILING = Self(3)
    """The configured precision did not establish the requested accuracy."""
    comptime SUBDIVISION_LIMIT = Self(4)
    """The configured subdivision allowance did not finish the analysis."""
    comptime UNRESOLVED_BOUNDARY = Self(5)
    """A search boundary could not be certified root-free."""

    def __eq__(self, other: Self) -> Bool:
        """Compare outcome codes.

        Args:
            other: The other outcome.

        Returns:
            Whether the codes agree.
        """
        return self.code == other.code


struct NumericOptions(ImplicitlyCopyable, Writable):
    """Explicit precision, accuracy and subdivision limits for adaptive algorithms."""
    var initial_precision: Int
    """Initial midpoint precision in bits, at least two."""
    var max_precision: Int
    """The largest permitted midpoint precision."""
    var absolute_bits: Int
    """An absolute width target of two to the negative power, or zero to disable."""
    var relative_bits: Int
    """A relative width target of two to the negative power, or zero to disable."""
    var max_subdivisions: Int
    """Maximum search subdivisions, separate from the shared work budget."""
    var require_isolation: Bool
    """Require single-root regions rather than allowing certified clusters."""

    def __init__(out self, *, initial_precision: Int = 128, max_precision: Int = 1024, absolute_bits: Int = 32, relative_bits: Int = 0, max_subdivisions: Int = 4096, require_isolation: Bool = True):
        """Set explicit numerical options, validated when an algorithm starts.

        Args:
            initial_precision: The first working precision.
            max_precision: The precision ceiling.
            absolute_bits: The absolute width exponent, zero to disable.
            relative_bits: The relative width exponent, zero to disable.
            max_subdivisions: The deterministic search allowance.
            require_isolation: Require single-root regions.
        """
        self.initial_precision = initial_precision
        self.max_precision = max_precision
        self.absolute_bits = absolute_bits
        self.relative_bits = relative_bits
        self.max_subdivisions = max_subdivisions
        self.require_isolation = require_isolation

    def _validate(self) raises PolyError:
        if self.initial_precision < 2 or self.max_precision < self.initial_precision or self.absolute_bits < 0 or self.relative_bits < 0 or (self.absolute_bits == 0 and self.relative_bits == 0) or self.max_subdivisions < 0:
            raise PolyError(PolyErrorKind.DOMAIN, "invalid numerical precision or accuracy options")


def _dyadic(bits: Int, mut budget: Budget) raises PolyError -> QQ:
    _charge_size(bits, budget)
    try:
        return QQ(Rational(Integer(1), Integer(1) << bits))
    except e:
        raise PolyError(PolyErrorKind.CAPACITY, String(e))


def _next_precision(current: Int, maximum: Int) -> Int:
    return maximum if current > maximum // 2 else current * 2


def _abs_q(value: QQ, mut budget: Budget) raises PolyError -> QQ:
    _charge_size(value.size(), budget)
    return value.neg(budget) if value.value.sign() < 0 else value.copy()


def _axis_lower(low: QQ, high: QQ, mut budget: Budget) raises PolyError -> QQ:
    if low.value.sign() > 0:
        _charge_size(low.size(), budget)
        return low.copy()
    if high.value.sign() < 0:
        return high.neg(budget)
    return QQ(Rational(0))


def _norm_lower(box: NumericBox, mut budget: Budget) raises PolyError -> QQ:
    var a = _axis_lower(box.real_low, box.real_high, budget)
    var b = _axis_lower(box.imag_low, box.imag_high, budget)
    return a^ if _compare(a, b, budget) >= 0 else b^


def _norm_upper(box: NumericBox, mut budget: Budget) raises PolyError -> QQ:
    var a = _abs_q(box.real_low, budget)
    var b = _abs_q(box.real_high, budget)
    var c = _abs_q(box.imag_low, budget)
    var d = _abs_q(box.imag_high, budget)
    var real = a.copy() if _compare(a, b, budget) >= 0 else b.copy()
    var imag = c.copy() if _compare(c, d, budget) >= 0 else d.copy()
    return real.add(imag, budget)


def _target_width(box: NumericBox, options: NumericOptions, mut budget: Budget) raises PolyError -> QQ:
    var result = _dyadic(options.absolute_bits, budget) if options.absolute_bits else QQ(Rational(0))
    if options.relative_bits:
        result = result.add(_dyadic(options.relative_bits, budget).mul(_norm_lower(box, budget), budget), budget)
    return result^


def _accurate(box: NumericBox, options: NumericOptions, mut budget: Budget) raises PolyError -> Bool:
    if not _box_valid(box, budget):
        return False
    if options.relative_bits == 0 and box.imag_low.is_zero() and box.imag_high.is_zero():
        var fast = _dyadic_accurate(box.real_low, box.real_high, options.absolute_bits)
        if fast >= 0:
            return fast == 1
    var target = _target_width(box, options, budget)
    return _compare(box.real_high.sub(box.real_low, budget), target, budget) <= 0 and _compare(box.imag_high.sub(box.imag_low, budget), target, budget) <= 0


def _dyadic_accurate(low: QQ, high: QQ, bits: Int) raises PolyError -> Int:
    """Whether high - low <= 2^-bits for dyadic endpoints (1 or 0), or -1 otherwise.

    With low = a / 2^p and high = b / 2^q, the width is d / 2^e for
    e = max(p, q), and d <= 2^(e - bits) is a bit-length test.
    """
    var p = _power_of_two(low.value.denominator())
    var q = _power_of_two(high.value.denominator())
    if p < 0 or q < 0:
        return -1
    var e = max(p, q)
    var d: Integer
    try:
        d = (high.value.numerator() << (e - q)) - (low.value.numerator() << (e - p))
    except err:
        raise PolyError(PolyErrorKind.CAPACITY, String(err))
    if d.sign() <= 0:
        return 1
    var limit = e - bits
    if limit < 0:
        return 0
    var length = d.magnitude_bit_length()
    if length <= limit:
        return 1
    if length > limit + 1:
        return 0
    return 1 if _twos(d) == limit else 0
