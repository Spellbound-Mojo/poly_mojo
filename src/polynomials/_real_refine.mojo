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
from ._root_ops import _order, _twos, _power_of_two, _bits, _power_shift, _error_bits, _fixed, _exact_sign, _sign
from .certificates import SturmSequence, _IntegerChain, _integer_variations


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
    zero), the enclosure is tightened by QIR to below the cell width /
    2^(needed + 32); otherwise one sign evaluation decides.
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
                # Straight to the final target, with a 32-bit margin: QIR
                # converges quadratically, so one tightening per root costs
                # a few steps instead of one round per 32 halvings.
                _tighten(oracle, enclosure, width.value(), needed + 32, budget)
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
        var strip = min(_twos(total), e + 1)
        return QQ(Rational(_numerator=total >> strip, _denominator=Integer(1) << (e + 1 - strip)))
    except e:
        raise PolyError(PolyErrorKind.CAPACITY, String(e))


@fieldwise_init
struct _IsolationTask(Movable):
    var low: QQ
    var high: QQ
    var low_variations: Int
    var high_variations: Int
    var stuck: Int
    """Bisections in a row that kept every root of the parent."""
    var grid: Int
    """Cluster refinement tries a part of 2**grid parts."""


def _isolate_all(oracle: _RootOracle, chain: _IntegerChain, sequence: SturmSequence, mut budget: Budget) raises PolyError -> List[_Enclosure]:
    """Enclose every distinct real root, in increasing order.

    Bisection of (-2^bound, 2^bound) at dyadic points, whose chain values
    stay small, until each interval holds one root. Cuts avoid roots (the
    nearest nonroot point of a finer dyadic grid), so every enclosure has
    nonroot endpoints and no one-sided variations are needed.
    """
    var roots = List[_Enclosure]()
    var bound: QQ
    try:
        bound = QQ(Rational(Integer(1) << chain.bound)) if chain.bound >= 0 else QQ(Rational(Integer(1), Integer(1) << -chain.bound))
    except e:
        raise PolyError(PolyErrorKind.CAPACITY, String(e))
    var low = bound.neg(budget)
    var tasks = List[_IsolationTask]()
    tasks.append(_IsolationTask(low.copy(), bound.copy(), _integer_variations(chain, sequence, low, budget), _integer_variations(chain, sequence, bound, budget), 0, 2))
    while len(tasks):
        budget.charge(1)
        var task = tasks.pop()
        var count = task.low_variations - task.high_variations
        if count >= 2 and count <= 4 and task.stuck >= 2:
            # A cluster survived repeated bisection: jump towards it with
            # quadratic interval refinement, keeping only parts that still
            # hold every root of the cluster.
            if _cluster_step(oracle, chain, sequence, task, count, budget):
                task.grid = min(task.grid * 2, 1 << 20)
                tasks.append(task^)
                continue
            task.grid = max(2, task.grid // 2)
        if count == 0:
            continue
        if count == 1:
            var left = _check_sign(oracle, task.low.value, budget)
            roots.append(_Enclosure(task.low.value.copy(), task.high.value.copy(), left, False, 2))
            continue
        var m = _nonroot_cut(oracle, task.low, task.high, budget)
        var at = _integer_variations(chain, sequence, m, budget)
        var kept = 1 if at == task.high_variations or at == task.low_variations else 0
        var stuck = (task.stuck + 1) * kept
        tasks.append(_IsolationTask(m.copy(), task.high.copy(), at, task.high_variations, stuck, task.grid))
        tasks.append(_IsolationTask(task.low.copy(), m^, task.low_variations, at, stuck, task.grid))
    return roots^


def _derivative(c: List[Integer]) raises -> List[Integer]:
    var result = List[Integer](capacity=max(0, len(c) - 1))
    for i in range(1, len(c)):
        result.append(c[i] * Integer(i))
    if len(result) == 0:
        result.append(Integer(0))
    return result^


def _cluster_step(oracle: _RootOracle, chain: _IntegerChain, sequence: SturmSequence, mut task: _IsolationTask, count: Int, mut budget: Budget) raises PolyError -> Bool:
    # The (count - 1)-th derivative of g has a root near a cluster of count
    # roots; a Newton step on it from the midpoint picks the part to test.
    budget.charge(UInt64(len(oracle.g) * count))
    var a: QQ
    var b: QQ
    try:
        var h = oracle.g.copy()
        for _ in range(count - 1):
            h = _derivative(h)
        var slope_poly = _derivative(h)
        var width = task.high.value - task.low.value
        var middle = (task.low.value + task.high.value) / Rational(2)
        var p = middle.numerator()
        var q = middle.denominator()
        var precision = _error_bits(len(h) - 1, p, q) + max(0, _bits(width.denominator()) - _bits(width.numerator())) + task.grid + 64
        var shift = _power_shift(q)
        var value = _fixed(h, p, q, shift, precision)
        var slope = _fixed(slope_poly, p, q, shift, precision)
        if not slope:
            return False
        var guess = middle - Rational(value, slope)
        var parts = Integer(1) << task.grid
        var step = width / Rational(parts)
        var position = (guess - task.low.value) / step
        var index = position.numerator() // position.denominator()
        var first = index - Integer(1)
        var last = index + Integer(2)
        if first < Integer(0):
            first = Integer(0)
        if last > parts:
            last = parts.copy()
        if first >= last or (first == Integer(0) and last == parts):
            return False
        a = QQ(task.low.value + step * Rational(first))
        b = QQ(task.low.value + step * Rational(last))
    except e:
        raise PolyError(PolyErrorKind.CAPACITY, String(e))
    var low_variations = task.low_variations
    var high_variations = task.high_variations
    if a.value != task.low.value:
        if _check_sign(oracle, a.value, budget) == 0:
            return False
        low_variations = _integer_variations(chain, sequence, a, budget)
    if b.value != task.high.value:
        if _check_sign(oracle, b.value, budget) == 0:
            return False
        high_variations = _integer_variations(chain, sequence, b, budget)
    if low_variations - high_variations != count:
        return False
    task.low = a^
    task.high = b^
    task.low_variations = low_variations
    task.high_variations = high_variations
    return True


def _nonroot_cut(oracle: _RootOracle, low: QQ, high: QQ, mut budget: Budget) raises PolyError -> QQ:
    # The midpoint, or else the grid point nearest to it on ever finer
    # dyadic grids that is not a root of g; finitely many roots end the search.
    var parts = 2
    while True:
        var width = high.sub(low, budget)
        var center = parts // 2
        for offset in range(parts // 2):
            for direction in [-1, 1]:
                if offset == 0 and direction > 0:
                    continue
                var j = center + direction * offset
                if j <= 0 or j >= parts or (j % 2 == 0 and parts > 2):
                    continue
                var fraction = QQ(Rational(j)).mul(QQ(Rational(parts)).inverse(budget), budget)
                var point = low.add(width.mul(fraction, budget), budget)
                if _check_sign(oracle, point.value, budget) != 0:
                    return point^
        parts *= 2


def _locate(oracle: _RootOracle, mut roots: List[_Enclosure], start: Int, end: Int, m: QQ, mut budget: Budget) raises PolyError -> Tuple[Int, Bool]:
    """The index in [start, end] of the first enclosed root above m, and whether a root equals m."""
    var lo = start
    var hi = end
    while lo < hi:
        budget.charge(1)
        var middle = (lo + hi) // 2
        var side = _compare_enclosure(roots[middle], m.value)
        if side == 2:
            side = _side(oracle, roots[middle], m, budget)
        if side == 0:
            return (middle, True)
        if side < 0:
            lo = middle + 1
        else:
            hi = middle
    return (lo, False)


def _ranged_split(oracle: _RootOracle, mut roots: List[_Enclosure], start: Int, end: Int, low: QQ, high: QQ, degree: Int, mut budget: Budget) raises PolyError -> Tuple[QQ, Int]:
    """The cover's split point for a cell holding roots[start:end], and the index splitting them.

    Candidates follow the Sturm path (the first k/(k+1) point that is not a
    root of f); the roots of f in the cell are exactly the enclosed ones.
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
        var found = _locate(oracle, roots, start, end, middle, budget)
        if not found[1]:
            return (middle^, found[0])
    raise PolyError(PolyErrorKind.DOMAIN, "cell has no nonroot split")
