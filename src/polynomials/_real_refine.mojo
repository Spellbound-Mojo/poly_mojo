"""Certified signs and root enclosures that replace Sturm counts on single-root cells.

A cell with exactly one distinct root r splits into a child with count one and
a child with count zero, so its children's counts only need the side of r
relative to the split point. The squarefree part g changes sign exactly at r
inside the cell; an enclosure low <= r <= high, tightened by quadratic
interval refinement (Abbott), answers most sides by comparison, and a
certified sign of g answers the rest. Signs come from fixed-point Horner with
a proved error bound, and from exact integer evaluation when that bound is
too coarse, so every answer is exact.
"""
from apn_mojo import Integer, Rational
from .coefficients import QQ, NoContext
from .dense import DensePoly
from .errors import Budget, PolyError, PolyErrorKind, _charge_size
from .division import divmod
from ._images import _integer_dense
from ._integer_ops import _primitive
from ._root_ops import _order


struct _RootOracle(Copyable, Movable):
    """A primitive squarefree integer polynomial and its derivative, ascending."""
    var g: List[Integer]
    var dg: List[Integer]

    def __init__(out self, var g: List[Integer], var dg: List[Integer]):
        self.g = g^
        self.dg = dg^


@fieldwise_init
struct _Enclosure(Copyable, Movable):
    """A closed rational enclosure of the only root of g in a cell."""
    var low: Rational
    var high: Rational
    var left: Int
    """The sign of g between the cell's lower endpoint and the root."""
    var exact: Bool
    """Whether low == high is the root itself."""
    var grid: Int
    """The refinement grid has 2**grid parts."""


def _root_oracle(f: DensePoly[QQ], last: DensePoly[QQ], mut budget: Budget) raises PolyError -> _RootOracle:
    # The last Sturm entry is gcd(f, f') up to a scalar, so f / last is squarefree.
    var division = divmod(f, last, budget)
    var integer = _primitive(_integer_dense(division.quotient, budget), budget)
    var g = List[Integer](capacity=len(integer.coefficients))
    var dg = List[Integer](capacity=len(integer.coefficients))
    budget.charge(UInt64(len(integer.coefficients)))
    try:
        for i in range(len(integer.coefficients)):
            g.append(integer.coefficients[i].value.copy())
            if i:
                dg.append(integer.coefficients[i].value * Integer(i))
    except e:
        raise PolyError(PolyErrorKind.CAPACITY, String(e))
    return _RootOracle(g^, dg^)


def _bits(x: Integer) -> Int:
    return x.magnitude_bit_length()


def _power_shift(q: Integer) raises -> Int:
    var b = _bits(q)
    return b - 1 if (Integer(1) << (b - 1)) == q else -1


def _error_bits(n: Int, p: Integer, q: Integer) -> Int:
    # Floor rounding in each of the n Horner steps errs by less than one unit,
    # and later steps scale it by |x|, so the total is below
    # sum_{j<n} |x|^j <= n max(1, |x|)^(n-1) units.
    var lx = max(0, _bits(p) - _bits(q) + 1)
    var log_n = 0
    while (1 << log_n) < n:
        log_n += 1
    return log_n + (n - 1) * lx + 1


def _fixed(c: List[Integer], p: Integer, q: Integer, shift: Int, scale: Int) raises -> Integer:
    # 2^scale * c(p/q) within the error of _error_bits, by floor-rounded Horner.
    var n = len(c) - 1
    var t = c[n] << scale
    for i in range(n - 1, -1, -1):
        var product = t * p
        if shift >= 0:
            t = product >> shift
        else:
            t = product // q
        t = t + (c[i] << scale)
    return t^


def _exact_sign(c: List[Integer], p: Integer, q: Integer) raises -> Int:
    # sign(q^n c(p/q)) by homogeneous Horner; q is positive.
    var n = len(c) - 1
    var t = c[n].copy()
    var power = Integer(1)
    for i in range(n - 1, -1, -1):
        power = power * q
        t = t * p + c[i] * power
    return t.sign()


def _sign(c: List[Integer], x: Rational) raises -> Int:
    var n = len(c) - 1
    if n <= 0:
        return c[0].sign() if n == 0 else 0
    var p = x.numerator()
    var q = x.denominator()
    if not p:
        return c[0].sign()
    var shift = _power_shift(q)
    var error = _error_bits(n, p, q)
    var exact_bits = n * (_bits(p) + _bits(q))
    var extra = 64
    while error + extra < exact_bits:
        var t = _fixed(c, p, q, shift, error + extra)
        if t and _bits(t) - 1 > error + 1:
            return t.sign()
        extra *= 4
    return _exact_sign(c, p, q)


def _check_sign(oracle: _RootOracle, x: Rational, mut budget: Budget) raises PolyError -> Int:
    budget.charge(UInt64(len(oracle.g)))
    _charge_size((_bits(x.numerator()) + _bits(x.denominator())) // 8 + 1, budget)
    try:
        return _sign(oracle.g, x)
    except e:
        raise PolyError(PolyErrorKind.CAPACITY, String(e))


def _enclosure(oracle: _RootOracle, low: QQ, high: QQ, mut budget: Budget) raises PolyError -> _Enclosure:
    var left = _check_sign(oracle, low.value, budget)
    if left == 0:
        raise PolyError(PolyErrorKind.DOMAIN, "single-root cell has a root endpoint")
    return _Enclosure(low.value.copy(), high.value.copy(), left, False, 2)


def _side(oracle: _RootOracle, mut enclosure: _Enclosure, m: QQ, mut budget: Budget) raises PolyError -> Int:
    """Return -1 when the root is below m, 0 when it is m, and 1 when it is above."""
    var known = _compare_enclosure(enclosure, m.value)
    if known != 2:
        return known
    var s = _check_sign(oracle, m.value, budget)
    if s == 0:
        enclosure.low = m.value.copy()
        enclosure.high = m.value.copy()
        enclosure.exact = True
        return 0
    if s == enclosure.left:
        enclosure.low = m.value.copy()
        return 1
    enclosure.high = m.value.copy()
    return -1


def _compare_enclosure(enclosure: _Enclosure, m: Rational) raises PolyError -> Int:
    # The side of the root decided by the enclosure alone, or 2.
    try:
        if enclosure.exact:
            return -_order(m, enclosure.low)
        if _order(m, enclosure.low) < 0:
            return 1
        if _order(enclosure.high, m) < 0:
            return -1
        return 2
    except e:
        raise PolyError(PolyErrorKind.CAPACITY, String(e))


def _ratio_bits(enclosure: _Enclosure, target: Rational) raises PolyError -> Int:
    # An upper bound on log2((high - low) / target).
    try:
        var ratio = (enclosure.high - enclosure.low) / target
        return _bits(ratio.numerator()) - _bits(ratio.denominator()) + 1
    except e:
        raise PolyError(PolyErrorKind.CAPACITY, String(e))


def _wider(enclosure: _Enclosure, target: Rational) raises PolyError -> Bool:
    try:
        return _order(enclosure.high - enclosure.low, target) > 0
    except e:
        raise PolyError(PolyErrorKind.CAPACITY, String(e))


def _tighten(oracle: _RootOracle, mut enclosure: _Enclosure, cell_width: QQ, guard: Int, mut budget: Budget) raises PolyError:
    """Shrink the enclosure below cell_width / 2**guard."""
    var target: Rational
    try:
        target = cell_width.value / Rational(Integer(1) << guard)
    except e:
        raise PolyError(PolyErrorKind.CAPACITY, String(e))
    while not enclosure.exact and _wider(enclosure, target):
        budget.charge(1)
        # Never subdivide below the target: 2**grid parts of the enclosure.
        enclosure.grid = max(2, min(enclosure.grid, _ratio_bits(enclosure, target) + 1))
        if _qir_step(oracle, enclosure, budget):
            enclosure.grid = min(enclosure.grid * 2, 1 << 20)
        else:
            enclosure.grid = max(2, enclosure.grid // 2)
            if not enclosure.exact and _wider(enclosure, target):
                var middle: Rational
                try:
                    middle = (enclosure.low + enclosure.high) / Rational(2)
                except e:
                    raise PolyError(PolyErrorKind.CAPACITY, String(e))
                _ = _side(oracle, enclosure, QQ(middle^), budget)


@fieldwise_init
struct _Plan(Movable):
    var kind: Int
    """-1 without a guess; 0, 1 or 2 for the lowest, highest or an interior grid point."""
    var point: Rational
    var step: Rational


def _qir_plan(oracle: _RootOracle, enclosure: _Enclosure) raises -> _Plan:
    # Quadratic interval refinement with a Newton guess from the midpoint:
    # the grid part of width w/N around the guess is tested next.
    var low = enclosure.low.copy()
    var width = enclosure.high - low
    var k = enclosure.grid
    var parts = Integer(1) << k
    var middle = (low + enclosure.high) / Rational(2)
    var p = middle.numerator()
    var q = middle.denominator()
    var n = len(oracle.g) - 1
    var precision = _error_bits(n, p, q) + max(0, _bits(width.denominator()) - _bits(width.numerator())) + k + 64
    var shift = _power_shift(q)
    var value = _fixed(oracle.g, p, q, shift, precision)
    var slope = _fixed(oracle.dg, p, q, shift, precision) if len(oracle.dg) else Integer(0)
    var step = width / Rational(parts)
    if not slope:
        return _Plan(-1, low^, step^)
    var guess = middle - Rational(value, slope)
    var position = (guess - low) * Rational(parts) / width
    var index = (position.numerator() * Integer(2) + position.denominator()) // (position.denominator() * Integer(2))
    if index <= Integer(0):
        return _Plan(0, low + step, step^)
    if index >= parts:
        return _Plan(1, enclosure.high - step, step^)
    return _Plan(2, low + step * Rational(index), step^)


def _qir_step(oracle: _RootOracle, mut enclosure: _Enclosure, mut budget: Budget) raises PolyError -> Bool:
    budget.charge(UInt64(2 * len(oracle.g)))
    var plan: _Plan
    var beside: Rational
    try:
        plan = _qir_plan(oracle, enclosure)
        beside = plan.point + plan.step if plan.kind == 2 else plan.point.copy()
    except e:
        raise PolyError(PolyErrorKind.CAPACITY, String(e))
    if plan.kind < 0:
        return False
    if plan.kind == 0:
        return _side(oracle, enclosure, QQ(plan.point.copy()), budget) <= 0
    if plan.kind == 1:
        return _side(oracle, enclosure, QQ(plan.point.copy()), budget) >= 0
    var side = _side(oracle, enclosure, QQ(plan.point.copy()), budget)
    if side == 0:
        return True
    if side > 0:
        return _side(oracle, enclosure, QQ(beside^), budget) <= 0
    var below: Rational
    try:
        below = plan.point - plan.step
    except e:
        raise PolyError(PolyErrorKind.CAPACITY, String(e))
    return _side(oracle, enclosure, QQ(below^), budget) >= 0


def _oracle_split(oracle: _RootOracle, mut enclosure: _Enclosure, low: QQ, high: QQ, degree: Int, absolute_bits: Int, mut budget: Budget) raises PolyError -> Tuple[QQ, Int]:
    """The cover's split point for a single-root cell and the side of its root.

    The candidates and their order are those of the Sturm path: the first
    k/(k+1) point of the cell that is not a root of f, and the only root of f
    in the cell is the enclosed root. When a candidate falls inside the
    enclosure and the cell still needs more than a few halvings for an
    absolute target of 2^-absolute_bits (or any target when absolute_bits is
    zero), the enclosure is tightened by QIR to below the cell width / 2^guard,
    guard = min(32, needed + 2); otherwise one sign evaluation decides.
    """
    var width = Optional[QQ]()
    for k in range(1, degree + 2):
        var middle: QQ
        var dyadic = _dyadic_midpoint(low, high) if k == 1 else Optional[QQ]()
        if dyadic:
            middle = dyadic.take()
        else:
            if not width:
                width = high.sub(low, budget)
            var fraction = QQ(Rational(k)).mul(QQ(Rational(k + 1)).inverse(budget), budget)
            middle = low.add(width.value().mul(fraction, budget), budget)
        if _compare_enclosure(enclosure, middle.value) == 2:
            if not width:
                width = high.sub(low, budget)
            var needed = 64
            if absolute_bits > 0:
                ref span = width.value().value
                needed = max(0, _bits(span.numerator()) - _bits(span.denominator()) + 1 + absolute_bits)
            if needed > 4:
                _tighten(oracle, enclosure, width.value(), min(32, needed + 2), budget)
        var side = _side(oracle, enclosure, middle, budget)
        if side != 0:
            return (middle^, side)
    raise PolyError(PolyErrorKind.DOMAIN, "single-root cell has no nonroot split")


def _dyadic_midpoint(low: QQ, high: QQ) raises PolyError -> Optional[QQ]:
    # (low + high) / 2 in lowest terms when both denominators are powers of
    # two, by shifts instead of normalized rational arithmetic.
    try:
        var a = low.value.denominator()
        var b = high.value.denominator()
        var ea = _power_shift(a)
        var eb = _power_shift(b)
        if ea < 0 or eb < 0:
            return None
        var e = max(ea, eb)
        var total = (low.value.numerator() << (e - ea)) + (high.value.numerator() << (e - eb))
        if not total:
            return QQ(Rational(0))
        # Strip the common powers of two from total / 2^(e + 1).
        var magnitude = abs(total)
        var twos = _bits(magnitude & -magnitude) - 1
        var strip = min(twos, e + 1)
        return QQ(Rational(_numerator=total >> strip, _denominator=Integer(1) << (e + 1 - strip)))
    except e:
        raise PolyError(PolyErrorKind.CAPACITY, String(e))
