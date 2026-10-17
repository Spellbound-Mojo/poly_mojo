"""Exact Sturm counts and dyadic real-root isolation with rational reconstruction."""
from apn_mojo import Rational, div_rem_euclid
from .coefficients import QQ, ZZ, NoContext, _work
from .dense import DensePoly
from .errors import Budget, PolyError, PolyErrorKind, _allocation, _charge_size
from .evaluate import _derivative_dense
from .division import divmod
from .certificates import SturmSequence, RootCountCertificate
from ._dense_ops import _copy as _copy_poly
from ._root_ops import _copy, _compare, _midpoint, _variations, _sign_at
from ._images import _integer_dense
from ._integer_ops import _primitive


@fieldwise_init
struct RootInterval(Copyable, Movable, Writable):
    """An open rational interval containing exactly one distinct real root."""
    var low: QQ
    """The lower endpoint, strictly below the root."""
    var high: QQ
    """The upper endpoint, strictly above the root."""


@fieldwise_init
struct RootIsolation(Copyable, Movable, Writable):
    """The distinct real roots as exact rationals and disjoint open intervals."""
    var exact_roots: List[QQ]
    """All rational roots in increasing order, without multiplicities."""
    var intervals: List[RootInterval]
    """Increasing disjoint intervals for the remaining roots, excluding exact roots."""


def sturm_sequence(f: DensePoly[QQ], mut budget: Budget) raises PolyError -> SturmSequence:
    """Construct the unnormalized Sturm sequence and every quotient witness.

    Args:
        f: A nonzero rational polynomial; constants give a one-element sequence.
        budget: The shared work allowance.

    Returns:
        The sequence starting with f and f-prime, including its last nonzero entry.

    Raises:
        PolyError: DOMAIN for zero or malformed input, LIMIT or CAPACITY on work limits.
    """
    f.check_invariants(budget)
    if f.is_zero():
        raise PolyError(PolyErrorKind.DOMAIN, "zero polynomial has no finite root count")
    _allocation[DensePoly[QQ]](1, budget)
    var polynomials: List[DensePoly[QQ]] = [_copy_poly(f, budget)]
    var quotients = List[DensePoly[QQ]]()
    if f.degree() > 0:
        _allocation[DensePoly[QQ]](1, budget)
        polynomials.append(_derivative_dense(f, budget))
        while True:
            budget.charge(1)
            var n = len(polynomials)
            var division = divmod(polynomials[n - 2], polynomials[n - 1], budget)
            var quotient = DensePoly[QQ](f.variable, NoContext())
            swap(quotient, division.quotient)
            _allocation[DensePoly[QQ]](1, budget)
            quotients.append(quotient^)
            if division.remainder.is_zero():
                break
            _allocation[DensePoly[QQ]](1, budget)
            polynomials.append(division.remainder.neg(budget))
    return SturmSequence(polynomials^, quotients^)


def sign_changes(sequence: SturmSequence, a: QQ, mut budget: Budget) raises PolyError -> Int:
    """Count changes of sign at an exact point, omitting zero evaluations.

    Args:
        sequence: The polynomial sequence to evaluate.
        a: The exact evaluation point.
        budget: The shared work allowance.

    Returns:
        The number of adjacent opposite nonzero signs.

    Raises:
        PolyError: LIMIT or CAPACITY on work limits.
    """
    return _variations(sequence.polynomials, a, budget)


def count_roots(f: DensePoly[QQ], a: QQ, b: QQ, mut budget: Budget) raises PolyError -> RootCountCertificate:
    """Count distinct real roots in an open interval with nonroot endpoints.

    Args:
        f: A nonzero polynomial, with repeated roots allowed.
        a: The lower endpoint.
        b: The upper endpoint.
        budget: The shared work allowance.

    Returns:
        The count and a complete Sturm certificate.

    Raises:
        PolyError: DOMAIN for zero, endpoint roots, or a not below b; LIMIT or CAPACITY on work limits.
    """
    if _compare(a, b, budget) >= 0 or _sign_at(f, a, budget) == 0 or _sign_at(f, b, budget) == 0:
        raise PolyError(PolyErrorKind.DOMAIN, "root count requires ordered nonroot endpoints")
    var sequence = sturm_sequence(f, budget)
    var count = sign_changes(sequence, a, budget) - sign_changes(sequence, b, budget)
    return RootCountCertificate(sequence^, _copy(a, budget), _copy(b, budget), count)


def _bound(f: DensePoly[QQ], mut budget: Budget) raises PolyError -> QQ:
    var inverse = f.coefficients[f.degree()].inverse(budget)
    var maximum = QQ.zero(NoContext())
    for i in range(f.degree()):
        budget.charge(1)
        var ratio = f.coefficients[i].mul(inverse, budget)
        if ratio.value.sign() < 0:
            ratio = ratio.neg(budget)
        if _compare(ratio, maximum, budget) > 0:
            maximum = ratio^
    var bound = maximum.add(QQ.one(NoContext()), budget)
    var power = QQ.one(NoContext())
    while _compare(power, bound, budget) < 0:
        budget.charge(1)
        power = power.add(power, budget)
    return power^


def _denominator_bound(f: DensePoly[QQ], mut budget: Budget) raises PolyError -> ZZ:
    var integer = _primitive(_integer_dense(f, budget), budget)
    ref lc = integer.coefficients[integer.degree()]
    _charge_size(lc.size(), budget)
    return lc.copy()


def _rational_root(f: DensePoly[QQ], low: QQ, high: QQ, bound: ZZ, mut budget: Budget) raises PolyError -> Optional[QQ]:
    # Rational-root theorem: the reduced denominator divides the primitive
    # leading coefficient A. Width < 1/(2*A*A) makes any root of denominator
    # <= A a continued-fraction convergent of the midpoint (Legendre).
    # Exact evaluation admits only actual roots, including negative ones.
    var middle = _midpoint(low, high, budget)
    _charge_size(middle.size(), budget)
    var numerator = ZZ(middle.value.numerator())
    var denominator = ZZ(middle.value.denominator())
    var h0 = ZZ.zero(NoContext())
    var h1 = ZZ.one(NoContext())
    var k0 = ZZ.one(NoContext())
    var k1 = ZZ.zero(NoContext())
    while not denominator.is_zero():
        budget.charge(1)
        _work(numerator.size(), denominator.size(), True, budget)
        var a: ZZ
        var remainder: ZZ
        try:
            var qr = div_rem_euclid(numerator.value, denominator.value)
            a = ZZ(qr[0].copy())
            remainder = ZZ(qr[1].copy())
        except e:
            raise PolyError(PolyErrorKind.CAPACITY, String(e))
        var h = a.mul(h1, budget).add(h0, budget)
        var k = a.mul(k1, budget).add(k0, budget)
        _work(k.size(), bound.size(), False, budget)
        if k.value > bound.value:
            break
        _work(h.size(), k.size(), True, budget)
        var candidate: QQ
        try:
            candidate = QQ(Rational(h.value, k.value))
        except e:
            raise PolyError(PolyErrorKind.CAPACITY, String(e))
        if _compare(low, candidate, budget) < 0 and _compare(candidate, high, budget) < 0 and _sign_at(f, candidate, budget) == 0:
            return candidate^
        h0 = h1^
        h1 = h^
        k0 = k1^
        k1 = k^
        numerator = denominator^
        denominator = remainder^
    return None


@fieldwise_init
struct _IntervalTask(Movable):
    var low: QQ
    var high: QQ
    var left_variations: Int
    var right_variations: Int
    var left_root: Bool
    var right_root: Bool
    var tried_rational: Bool
    var rational_excluded: Bool


def isolate_real_roots(f: DensePoly[QQ], mut budget: Budget) raises PolyError -> RootIsolation:
    """Isolate every distinct real root by exact dyadic Sturm bisection.

    Args:
        f: A nonzero rational polynomial; constants have no roots.
        budget: The shared work allowance.

    Returns:
        Every rational root exactly and sorted disjoint intervals of width below 2**-40 for the others.

    Raises:
        PolyError: DOMAIN for zero or malformed input, LIMIT or CAPACITY on work limits.
    """
    var sequence = sturm_sequence(f, budget)
    var exact = List[QQ]()
    var intervals = List[RootInterval]()
    if f.degree() == 0:
        return RootIsolation(exact^, intervals^)
    var denominator = _denominator_bound(f, budget)
    var square = denominator.mul(denominator, budget)
    _charge_size(square.size(), budget)
    _charge_size(square.size(), budget)
    var precision = QQ(Rational(square.value)).add(QQ(Rational(square.value)), budget).inverse(budget)
    var display_width = QQ.one(NoContext())
    for _ in range(40):
        budget.charge(1)
        display_width = _midpoint(QQ.zero(NoContext()), display_width, budget)
    var high = _bound(f, budget)
    var low = high.neg(budget)
    var va = sign_changes(sequence, low, budget)
    var vb = sign_changes(sequence, high, budget)
    _allocation[_IntervalTask](1, budget)
    var pending: List[_IntervalTask] = [_IntervalTask(low^, high^, va, vb, False, False, False, False)]
    while len(pending):
        budget.charge(1)
        var task = pending.pop()
        var count = task.left_variations - task.right_variations
        if count == 0:
            continue
        if count == 1:
            var width = task.high.sub(task.low, budget)
            var narrow = _compare(width, precision, budget) < 0
            if not task.rational_excluded and (not task.tried_rational or narrow):
                # Exact evaluation permits recognition at any width. A miss
                # excludes rational roots only at the denominator bound.
                var rational = _rational_root(f, task.low, task.high, denominator, budget)
                task.tried_rational = True
                if rational:
                    _allocation[QQ](1, budget)
                    exact.append(rational.take())
                    continue
                task.rational_excluded = narrow
            if task.rational_excluded and not task.left_root and not task.right_root and _compare(width, display_width, budget) < 0:
                _allocation[RootInterval](1, budget)
                intervals.append(RootInterval(_copy(task.low, budget), _copy(task.high, budget)))
                continue
        var middle = _midpoint(task.low, task.high, budget)
        var root = _sign_at(f, middle, budget) == 0
        var vm_left = _variations(sequence.polynomials, middle, budget, side=-1 if root else 0)
        var vm_right = _variations(sequence.polynomials, middle, budget, side=1) if root else vm_left
        if root:
            _allocation[QQ](1, budget)
            exact.append(_copy(middle, budget))
        _allocation[_IntervalTask](2, budget)
        # Push the right half first so intervals emerge in increasing order.
        pending.append(_IntervalTask(_copy(middle, budget), _copy(task.high, budget), vm_right, task.right_variations, root, task.right_root, task.tried_rational, task.rational_excluded))
        pending.append(_IntervalTask(_copy(task.low, budget), middle^, task.left_variations, vm_left, task.left_root, root, task.tried_rational, task.rational_excluded))
    # Midpoint discoveries precede their left subtrees, so exact points need
    # a separate stable sort. Intervals are already ordered by the worklist.
    for i in range(1, len(exact)):
        budget.charge(1)
        var value = QQ.zero(NoContext())
        swap(value, exact[i])
        var j = i
        while j > 0 and _compare(value, exact[j - 1], budget) < 0:
            var moved = QQ.zero(NoContext())
            swap(moved, exact[j - 1])
            swap(moved, exact[j])
            j -= 1
        swap(value, exact[j])
    return RootIsolation(exact^, intervals^)


def refine(f: DensePoly[QQ], interval: RootInterval, width: QQ, mut budget: Budget) raises PolyError -> RootInterval:
    """Bisect a validated isolating interval to strictly less than the requested width.

    Args:
        f: The polynomial defining the root.
        interval: An open interval with exactly one root and nonroot endpoints.
        width: The positive target width.
        budget: The shared work allowance.

    Returns:
        A narrower open interval containing the same root, including rational midpoint roots.

    Raises:
        PolyError: DOMAIN for nonpositive width or an invalid isolating interval, LIMIT or CAPACITY on work limits.
    """
    if width.value.sign() <= 0:
        raise PolyError(PolyErrorKind.DOMAIN, "refinement requires a positive width")
    var certificate = count_roots(f, interval.low, interval.high, budget)
    if certificate.count != 1:
        raise PolyError(PolyErrorKind.DOMAIN, "refinement requires exactly one root")
    var low = _copy(interval.low, budget)
    var high = _copy(interval.high, budget)
    var va = sign_changes(certificate.sequence, low, budget)
    while _compare(high.sub(low, budget), width, budget) >= 0:
        budget.charge(1)
        var middle = _midpoint(low, high, budget)
        if _sign_at(f, middle, budget) == 0:
            low = _midpoint(low, middle, budget)
            high = _midpoint(middle, high, budget)
            va = sign_changes(certificate.sequence, low, budget)
        else:
            var vm = sign_changes(certificate.sequence, middle, budget)
            if va - vm == 1:
                high = middle^
            else:
                low = middle^
                va = vm
    return RootInterval(low^, high^)


def sign_on_interval(f: DensePoly[QQ], low: QQ, high: QQ, mut budget: Budget) raises PolyError -> Optional[Int]:
    """Determine the strict sign on a closed interval when no root occurs there.

    Args:
        f: The rational polynomial.
        low: The lower endpoint.
        high: The upper endpoint, possibly equal to low.
        budget: The shared work allowance.

    Returns:
        Positive or negative one for a root-free interval, otherwise None.

    Raises:
        PolyError: DOMAIN for reversed endpoints or malformed input, LIMIT or CAPACITY on work limits.
    """
    f.check_invariants(budget)
    var comparison = _compare(low, high, budget)
    if comparison > 0:
        raise PolyError(PolyErrorKind.DOMAIN, "sign interval has reversed endpoints")
    var sign = _sign_at(f, low, budget)
    if sign == 0 or _sign_at(f, high, budget) == 0:
        return None
    if comparison < 0 and count_roots(f, low, high, budget).count != 0:
        return None
    return sign
