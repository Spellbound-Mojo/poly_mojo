"""Truncated power series over odd word prime fields on Montgomery residues.

Series are `List[UInt64]` Montgomery residues as in `_nmod`, lowest degree
first; results have exactly the requested length. Inverses, logarithms and
exponentials double their precision by Newton steps over the transform
products of `_multipoint`, and short orders use the direct recurrences.
Callers check constant terms and the invertibility of 1 ... n - 1 first, so
these routines see only valid inputs. Every step charges the shared budget
in proportion to its coefficient work.
"""
from .errors import Budget, PolyError, _allocation, _charge_size, _product
from .coefficients import ModInt, Modulus
from ._nmod import _Field, _field, _mulm, _addm, _subm, _negm, _to, _from, _invm
from ._multipoint import _mullow_fast, _redc_all, _TRANSFORM, _compose_series
from ._ntt import _modular_range
from ._nmod import _slice
from ._series_words import _INVERSE_WORDS, _EXP_WORDS, _word_divide, _word_exp, _naturals

comptime _SETUP = 64
"""Work charged for preparing a native field, before any series work."""


def _middle(a: List[UInt64], b: List[UInt64], lo: Int, hi: Int, f: _Field, mut budget: Budget) raises PolyError -> List[UInt64]:
    """Coefficients lo ... hi - 1 of a * b, zero-padded; one cyclic transform from _TRANSFORM terms."""
    var result: List[UInt64]
    if len(a) == 0 or len(b) == 0:
        result = List[UInt64]()
    elif min(len(a), len(b)) < _TRANSFORM:
        var low = _mullow_fast(a, b, hi, f, budget)
        result = List[UInt64](capacity=hi - lo)
        for i in range(lo, min(hi, len(low))):
            result.append(low[i])
    else:
        # A cyclic transform of length >= hi needs operands no longer than hi;
        # coefficients from hi on cannot reach the requested range.
        result = _modular_range(_slice(a, 0, hi, budget), _slice(b, 0, hi, budget), lo, hi, f.p, budget)
        _redc_all(result, f)
    result.resize(hi - lo, 0)
    return result^


def _padded(a: List[UInt64], n: Int, mut budget: Budget) raises PolyError -> List[UInt64]:
    """The first n coefficients of a, zero-padded."""
    _allocation[UInt64](n, budget)
    var result = List[UInt64](length=n, fill=0)
    for i in range(min(n, len(a))):
        result[i] = a[i]
    return result^


def _inverse(a: List[UInt64], n: Int, f: _Field, mut budget: Budget) raises PolyError -> List[UInt64]:
    """1 / a modulo x^n for a unit constant term.

    Below _INVERSE_WORDS the quadratic word recurrence wins outright; above it
    seeds Newton at the largest order below the crossover that doubles to n.
    """
    var one: List[UInt64] = [f.one]
    if n < _INVERSE_WORDS:
        return _word_divide(one, a, n, f, budget)
    var k = n
    while k >= _INVERSE_WORDS:
        k = (k + 1) // 2
    var g = _word_divide(one, a, k, f, budget)
    while k < n:
        budget.charge(1)
        var k2 = min(2 * k, n)
        # a * g = 1 + x^k e + O(x^k2); the next coefficients are -g * e.
        var e = _middle(_padded(a, k2, budget), g, k, k2, f, budget)
        var t = _mullow_fast(g, e, k2 - k, f, budget)
        for i in range(k2 - k):
            g.append(_negm(t[i], f) if i < len(t) else UInt64(0))
        k = k2
    return g^


def _log(a: List[UInt64], n: Int, naturals: List[UInt64], f: _Field, mut budget: Budget) raises PolyError -> List[UInt64]:
    """log(a) modulo x^n for a(0) = 1, given the inverses of 1 ... n - 1."""
    var result = List[UInt64](length=n, fill=0)
    if n <= 1:
        return result^
    _allocation[UInt64](n - 1, budget)
    var derivative = List[UInt64](capacity=n - 1)
    var k = UInt64(0)
    for i in range(1, min(n, len(a))):
        k = _addm(k, f.one, f)
        derivative.append(_mulm(a[i], k, f))
    var quotient = _mullow_fast(derivative, _inverse(a, n - 1, f, budget), n - 1, f, budget)
    for i in range(1, n):
        if i - 1 < len(quotient):
            result[i] = _mulm(quotient[i - 1], naturals[i], f)
    return result^


def _exp(a: List[UInt64], n: Int, naturals: List[UInt64], f: _Field, mut budget: Budget) raises PolyError -> List[UInt64]:
    """exp(a) modulo x^n for a(0) = 0, given the inverses of 1 ... n - 1."""
    # The quadratic word recurrence below _EXP_WORDS; above, it seeds Newton at
    # the largest order below the crossover that doubles to n.
    var direct = n
    while direct >= _EXP_WORDS:
        direct = (direct + 1) // 2
    _allocation[UInt64](n, budget)
    var g = _word_exp(a, direct, naturals, f, budget)
    if direct == n:
        return g^
    # h = 1 / g is carried along: extended by one Newton step per doubling and
    # corrected after g changes, so log g needs no fresh inverse.
    var h = _inverse(g, direct, f, budget)
    var known = direct
    while known < n:
        budget.charge(1)
        var next = min(2 * known, n)
        var width = next - known
        # 1. h <- h + h (1 - g h) to precision next.
        var e = _middle(g, h, known, next, f, budget)
        var t = _mullow_fast(h, e, width, f, budget)
        for i in range(width):
            h.append(_negm(t[i], f) if i < len(t) else UInt64(0))
        # 2. (log g)' = g' h; only coefficients known ... next - 1 of log g are new.
        var derivative = List[UInt64](capacity=known - 1)
        var k = UInt64(0)
        for i in range(1, known):
            k = _addm(k, f.one, f)
            derivative.append(_mulm(g[i], k, f))
        var slope = _middle(derivative, h, known - 1, next - 1, f, budget)
        var high = List[UInt64](capacity=width)
        for i in range(known, next):
            var logarithm = _mulm(slope[i - known], naturals[i], f)
            high.append(_subm(a[i] if i < len(a) else UInt64(0), logarithm, f))
        # 3. g <- g (1 + x^known high).
        var correction = _mullow_fast(g, high, width, f, budget)
        for i in range(width):
            g.append(correction[i] if i < len(correction) else UInt64(0))
        # 4. 1 / g_new = h (1 - x^known high) modulo x^next.
        var shift = _mullow_fast(h, high, width, f, budget)
        for i in range(min(width, len(shift))):
            h[known + i] = _subm(h[known + i], shift[i], f)
        known = next
    return g^



def _derivative(a: List[UInt64], n: Int, f: _Field) -> List[UInt64]:
    """The first n coefficients of a', zero-padded."""
    var result = List[UInt64](length=n, fill=0)
    var k = UInt64(0)
    for i in range(1, min(n + 1, len(a))):
        k = _addm(k, f.one, f)
        result[i - 1] = _mulm(a[i], k, f)
    return result^


def _revert(a: List[UInt64], n: Int, f: _Field, mut budget: Budget) raises PolyError -> List[UInt64]:
    """The compositional inverse of a modulo x^n, for a(0) = 0 and a unit a(1).

    Newton steps g <- g - (a(g) - x) / a'(g) take a'(g) = (a o g)' / g', so
    each doubling needs one composition and one short inverse.
    """
    var g: List[UInt64] = [UInt64(0), _invm(a[1], f, budget)]
    var known = 2
    while known < n:
        budget.charge(1)
        var next = min(2 * known, n)
        var width = next - known
        var prefix = _padded(a, min(len(a), next), budget)
        var composed = _compose_series(prefix, g, next, f, budget)
        composed.resize(next, 0)
        var high = List[UInt64](capacity=width)
        for i in range(known, next):
            high.append(composed[i])
        # (a o g)' / g' = a'(g); the correction is high * g' / (a o g)'.
        var slope = _inverse(_derivative(composed, width, f), width, f, budget)
        var ratio = _mullow_fast(_derivative(g, width, f), slope, width, f, budget)
        var correction = _mullow_fast(high, ratio, width, f, budget)
        for i in range(width):
            g.append(_negm(correction[i], f) if i < len(correction) else UInt64(0))
        known = next
    g.resize(n, 0)
    return g^

def _native_series(coefficients: List[ModInt], ring: Modulus, order: Int, operation: Int, mut budget: Budget) raises PolyError -> Optional[List[ModInt]]:
    """Operation 0 (inverse), 1 (logarithm), 2 (exponential) or 3 (reversion) modulo x^order.

    None when the generic routine must decide instead: the field GF(2), a
    constant term outside the operation's domain, or an order whose integer
    divisions are not all invertible. The generic routine then raises the
    same errors as before.
    """
    if ring.value <= 2 or order < 1:
        return None
    if (operation == 1 or operation == 2) and UInt64(order) > ring.value:
        return None
    var constant = coefficients[0].value if len(coefficients) else UInt64(0)
    if (operation == 0 and constant == 0) or (operation == 1 and constant != 1) or (operation >= 2 and constant != 0):
        return None
    if operation == 3 and (order < 2 or len(coefficients) < 2 or coefficients[1].value == 0):
        return None
    var f = _field(ring.value)
    # Field setup and the Newton schedule are charged before any work, like
    # the generic routines: a constant plus order * log2(order).
    var steps = 1
    while (1 << steps) < order:
        steps += 1
    _charge_size(_product(order, steps) + _SETUP, budget)
    _allocation[UInt64](len(coefficients), budget)
    var a = List[UInt64](capacity=min(len(coefficients), order))
    for i in range(min(len(coefficients), order)):
        a.append(_to(coefficients[i].value, f))
    var values: List[UInt64]
    if operation == 0:
        values = _inverse(a, order, f, budget)
    elif operation == 3:
        values = _revert(a, order, f, budget)
    else:
        var naturals = _naturals(order, f, budget)
        values = _log(a, order, naturals, f, budget) if operation == 1 else _exp(a, order, naturals, f, budget)
    _allocation[ModInt](order, budget)
    var result = List[ModInt](capacity=order)
    for i in range(order):
        result.append(ModInt(_from(values[i], f) if i < len(values) else UInt64(0), ring))
    return result^
