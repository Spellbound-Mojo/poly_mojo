"""Exact-only dispatch and Newton updates for formal logarithms and exponentials."""
from .coefficients import CoefficientField, ModInt
from .coefficient_buffer import _CoefficientView, _view
from .errors import Budget, PolyError, PolyErrorKind, _allocation, _sum
from ._coefficient_ops import _copy
from ._toolkit_exact import _ExactOps, _use_newton
from ._toolkit_ops import _mul_values, _derivative_values, _values, _divide_values
from ._series_ops import _log_values, _exp_values, _series_constant, _newton_divide
from ._ntt import _ntt_middle_product


def _exact_log[C: CoefficientField](a: _CoefficientView[C, _], length: Int, context: C.Context, mut budget: Budget) raises PolyError -> List[C]:
    if not _use_newton[C](max(0, length - 1), len(a)):
        return _log_values[_ExactOps[C]](_view(a), length, context, budget)
    if length < 1:
        raise PolyError(PolyErrorKind.DOMAIN, "logarithm needs a known constant coefficient")
    _series_constant[_ExactOps[C]](_view(a), 1, context, budget)
    var derivative = _derivative_values[_ExactOps[C]](_view(a), context, budget)
    var quotient = _exact_divide(_view(derivative), _view(a), length - 1, context, budget)
    # Every required integer must be invertible, even when its numerator is zero.
    _allocation[C](length, budget)
    var result = List[C](capacity=length)
    result.append(C.zero(context))
    for k in range(1, length):
        result.append(_ExactOps[C].apply(quotient[k - 1], _ExactOps[C].integer(k, context, budget), 3, context, budget))
    return result^


def _exact_exp[C: CoefficientField](a: _CoefficientView[C, _], length: Int, context: C.Context, mut budget: Budget) raises PolyError -> List[C]:
    comptime threshold = 1024 if C == ModInt else 32
    if length < threshold or len(a) < 16:
        return _exp_values[_ExactOps[C]](_view(a), length, context, budget)
    return _newton_exp(_view(a), length, context, budget)


def _middle_values[C: CoefficientField](a: List[C], b: List[C], lo: Int, hi: Int, context: C.Context, mut budget: Budget) raises PolyError -> List[C]:
    """Coefficients lo ... hi - 1 of a * b, zero-padded: one cyclic transform where the kernel applies."""
    var middle = _ntt_middle_product(_view(a), _view(b), lo, hi, budget)
    if middle:
        return middle.take()
    var low = _mul_values[_ExactOps[C]](_view(a), _view(b), hi, context, budget)
    _allocation[C](hi - lo, budget)
    var result = List[C](capacity=hi - lo)
    for i in range(lo, hi):
        result.append(_copy(low[i], budget) if i < len(low) else C.zero(context))
    return result^


def _exact_divide[C: CoefficientField](a: _CoefficientView[C, _], b: _CoefficientView[C, _], length: Int, context: C.Context, mut budget: Budget) raises PolyError -> List[C]:
    """a / b modulo x^length by Newton inversion; b * g is needed only in its upper half, a middle product."""
    var known = min(length, 16)
    var divisor = _values[_ExactOps[C]](_view(b), min(len(b), length), context, budget)
    var inverse = _divide_values[_ExactOps[C]](_view([C.one(context)]), _view(divisor), known, context, budget)
    while known < length:
        var next = _sum(known, min(known, length - known))
        # b g = 1 + x^known e + O(x^next); the next coefficients are -g e.
        var e = _middle_values(_values[_ExactOps[C]](_view(divisor), min(len(divisor), next), context, budget), inverse, known, next, context, budget)
        var correction = _mul_values[_ExactOps[C]](_view(inverse), _view(e), next - known, context, budget)
        _allocation[C](next - known, budget)
        inverse.reserve(next)
        for i in range(next - known):
            inverse.append(correction[i].neg(budget) if i < len(correction) else C.zero(context))
        known = next
    if len(a) == 1 and _ExactOps[C].matches_integer(a[0], 1, context, budget):
        return inverse^
    var quotient = _mul_values[_ExactOps[C]](_view(a), _view(inverse), length, context, budget)
    _allocation[C](length - len(quotient), budget)
    while len(quotient) < length:
        budget.charge(1)
        quotient.append(C.zero(context))
    return quotient^


def _newton_exp[C: CoefficientField](a: _CoefficientView[C, _], length: Int, context: C.Context, mut budget: Budget) raises PolyError -> List[C]:
    if length < 1:
        raise PolyError(PolyErrorKind.DOMAIN, "exponential needs a known constant coefficient")
    _series_constant[_ExactOps[C]](_view(a), 0, context, budget)
    var known = min(length, 16)
    var g = _exp_values[_ExactOps[C]](_view(a), known, context, budget)
    # h = 1 / g is carried along: extended by one Newton step per doubling and
    # corrected after g changes, so log g needs no fresh inverse.
    var h = _newton_divide[_ExactOps[C]](_view([C.one(context)]), _view(g), known, context, budget)
    while known < length:
        var next = _sum(known, min(known, length - known))
        var width = next - known
        # 1. h <- h + h (1 - g h) to precision next.
        var e = _middle_values(g, h, known, next, context, budget)
        var t = _mul_values[_ExactOps[C]](_view(h), _view(e), width, context, budget)
        _allocation[C](width, budget)
        h.reserve(next)
        for i in range(width):
            h.append(t[i].neg(budget) if i < len(t) else C.zero(context))
        # 2. (log g)' = g' h; only coefficients known ... next - 1 of log g are new.
        # Every divisor k is inverted, even under a zero numerator, so a
        # characteristic obstruction is reported as before.
        var derivative = _derivative_values[_ExactOps[C]](_view(g), context, budget)
        var slope = _middle_values(derivative, h, known - 1, next - 1, context, budget)
        _allocation[C](width, budget)
        var high = List[C](capacity=width)
        for k in range(known, next):
            var divisor = _ExactOps[C].integer(k, context, budget).inverse(budget)
            var value = _copy(a[k], budget) if k < len(a) else C.zero(context)
            high.append(value.sub(slope[k - known].mul(divisor, budget), budget))
        # 3. g <- g (1 + x^known high).
        var correction = _mul_values[_ExactOps[C]](_view(g), _view(high), width, context, budget)
        g.reserve(next)
        for i in range(width):
            budget.charge(1)
            g.append(_copy(correction[i], budget) if i < len(correction) else C.zero(context))
        # 4. 1 / g_new = h (1 - x^known high) modulo x^next.
        var shift = _mul_values[_ExactOps[C]](_view(h), _view(high), width, context, budget)
        for i in range(min(width, len(shift))):
            h[known + i] = h[known + i].sub(shift[i], budget)
        known = next
    return g^
