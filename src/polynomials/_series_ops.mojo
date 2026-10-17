"""Shared formal-series schedules with explicit truncation and scalar domains."""
from .coefficient_buffer import _CoefficientView, _view
from .errors import Budget, PolyError, PolyErrorKind, _allocation, _sum
from ._toolkit_ops import _ScalarOps, _values, _mul_values, _divide_values, _compose_values, _derivative_values, _NATIVE_SERIES, _montgomery_of, _from_montgomery
from ._series_words import _word_exp, _naturals
from ._nmod import _field
from .coefficients import ModInt, Modulus


def _series_shape(order: Int, count: Int, mut budget: Budget) raises PolyError:
    budget.charge(1)
    if order < 0 or count > order:
        raise PolyError(PolyErrorKind.DOMAIN, "invalid truncated series representation")


def _series_same_order(a: Int, b: Int) raises PolyError:
    if a != b:
        raise PolyError(PolyErrorKind.DOMAIN, "series orders differ; truncate explicitly")


def _series_truncation(current: Int, requested: Int) raises PolyError:
    if requested < 0 or requested > current:
        raise PolyError(PolyErrorKind.DOMAIN, "series truncation cannot increase precision")


def _series_composition[O: _ScalarOps](inner: _CoefficientView[O.Scalar, _], order: Int, context: O.Context, mut budget: Budget) raises PolyError:
    if order == 0:
        raise PolyError(PolyErrorKind.DOMAIN, "composition needs a known constant coefficient")
    _series_constant[O](_view(inner), 0, context, budget)


def _series_constant[O: _ScalarOps](a: _CoefficientView[O.Scalar, _], wanted: Int, context: O.Context, mut budget: Budget) raises PolyError:
    var constant = O.copy(a[0], budget) if len(a) else O.integer(0, context, budget)
    if not O.matches_integer(constant, wanted, context, budget):
        raise PolyError(PolyErrorKind.DOMAIN, "formal series has an incompatible constant coefficient")


def _log_values[O: _ScalarOps, fast: Bool = False](a: _CoefficientView[O.Scalar, _], length: Int, context: O.Context, mut budget: Budget) raises PolyError -> List[O.Scalar]:
    if length < 1:
        raise PolyError(PolyErrorKind.DOMAIN, "logarithm needs a known constant coefficient")
    _series_constant[O](_view(a), 1, context, budget)
    var derivative = _derivative_values[O](_view(a), context, budget)
    var quotient: List[O.Scalar]
    comptime if fast:
        comptime assert O.EXACT
        quotient = _newton_divide[O](_view(derivative), _view(a), length - 1, context, budget)
    else:
        quotient = _divide_values[O](_view(derivative), _view(a), length - 1, context, budget)
    # Every required integer must be invertible, even when its numerator is zero.
    _allocation[O.Scalar](length, budget)
    var result = List[O.Scalar](capacity=length)
    result.append(O.integer(0, context, budget))
    for k in range(1, length):
        result.append(O.apply(quotient[k - 1], O.integer(k, context, budget), 3, context, budget))
    return result^


def _exp_values[O: _ScalarOps](a: _CoefficientView[O.Scalar, _], length: Int, context: O.Context, mut budget: Budget) raises PolyError -> List[O.Scalar]:
    if length < 1:
        raise PolyError(PolyErrorKind.DOMAIN, "exponential needs a known constant coefficient")
    _series_constant[O](_view(a), 0, context, budget)
    comptime if O.Scalar == ModInt and O.EXACT:
        # Every n < length must be invertible; otherwise the generic path raises.
        ref ring = rebind[Modulus](context)
        if length >= _NATIVE_SERIES and UInt64(length) <= ring.value and ring.value > 2:
            var f = _field(ring.value)
            return _from_montgomery[O.Scalar](_word_exp(_montgomery_of(a, f), length, _naturals(length, f, budget), f, budget), ring, f, budget)
    _allocation[O.Scalar](length, budget)
    var result = List[O.Scalar](capacity=length)
    result.append(O.integer(1, context, budget))
    for n in range(1, length):
        var value = O.integer(0, context, budget)
        for k in range(1, min(n + 1, len(a))):
            var term = O.apply(O.integer(k, context, budget), a[k], 2, context, budget)
            value = O.apply(value, O.apply(term, result[n - k], 2, context, budget), 0, context, budget)
        result.append(O.apply(value, O.integer(n, context, budget), 3, context, budget))
    return result^


def _revert_values[O: _ScalarOps](a: _CoefficientView[O.Scalar, _], length: Int, context: O.Context, mut budget: Budget) raises PolyError -> List[O.Scalar]:
    if length < 2 or len(a) < 2:
        raise PolyError(PolyErrorKind.DOMAIN, "reversion needs a known nonzero linear coefficient")
    _series_constant[O](_view(a), 0, context, budget)
    var inverse = O.apply(O.integer(1, context, budget), a[1], 3, context, budget)
    comptime if O.EXACT:
        if length >= 8:
            return _newton_revert[O](_view(a), inverse, length, context, budget)
    _allocation[O.Scalar](length, budget)
    var result = List[O.Scalar](length=length, fill=O.integer(0, context, budget))
    result[1] = O.copy(inverse, budget)
    for k in range(2, length):
        var composed = _compose_values[O, False](_view(a), _view(result), k + 1, context, budget)
        if k < len(composed):
            result[k] = O.apply(O.integer(0, context, budget), O.apply(composed[k], inverse, 2, context, budget), 1, context, budget)
    return result^


def _newton_divide[O: _ScalarOps](a: _CoefficientView[O.Scalar, _], b: _CoefficientView[O.Scalar, _], length: Int, context: O.Context, mut budget: Budget) raises PolyError -> List[O.Scalar]:
    # g_new = g - x^k * (g * high_k(b*g)) mod x^min(2*k,n).
    # The lower k coefficients are already correct and need no recomputation.
    var known = min(length, 16)
    var inverse = _divide_values[O](_view([O.integer(1, context, budget)]), _view(b), known, context, budget)
    while known < length:
        var next = _sum(known, min(known, length - known))
        var product = _mul_values[O](_view(b), _view(inverse), next, context, budget)
        _allocation[O.Scalar](next - known, budget)
        var high = List[O.Scalar](capacity=next - known)
        for i in range(known, next):
            high.append(O.copy(product[i], budget) if i < len(product) else O.integer(0, context, budget))
        var correction = _mul_values[O](_view(inverse), _view(high), next - known, context, budget)
        _allocation[O.Scalar](next - known, budget)
        inverse.reserve(next)
        for i in range(next - known):
            inverse.append(O.apply(O.integer(0, context, budget), correction[i], 1, context, budget) if i < len(correction) else O.integer(0, context, budget))
        known = next
    if len(a) == 1 and O.matches_integer(a[0], 1, context, budget):
        return inverse^
    var quotient = _mul_values[O](_view(a), _view(inverse), length, context, budget)
    _allocation[O.Scalar](length - len(quotient), budget)
    while len(quotient) < length:
        budget.charge(1)
        quotient.append(O.integer(0, context, budget))
    return quotient^


def _newton_revert[O: _ScalarOps](a: _CoefficientView[O.Scalar, _], linear_inverse: O.Scalar, length: Int, context: O.Context, mut budget: Budget) raises PolyError -> List[O.Scalar]:
    # g_new = g - (a(g)-x)/a'(g), doubling formal precision. Only a'(0)
    # must be invertible; no division by factorials or by the characteristic.
    _allocation[O.Scalar](2, budget)
    var result: List[O.Scalar] = [O.integer(0, context, budget), O.copy(linear_inverse, budget)]
    var known = 2
    while known < length:
        var next = _sum(known, min(known, length - known))
        var prefix = _values[O](_view(a), min(len(a), next), context, budget)
        var composed = _values[O](_view(_compose_values[O](_view(prefix), _view(result), next, context, budget)), next, context, budget)
        _allocation[O.Scalar](next - known, budget)
        var high = List[O.Scalar](capacity=next - known)
        for i in range(known, next):
            high.append(O.copy(composed[i], budget))
        # a'(g) = (a o g)' / g', so the correction (a(g) - x) / a'(g) is
        # high * g' / (a o g)' and needs no second composition.
        var slope = _values[O](_view(_derivative_values[O](_view(composed), context, budget)), next - known, context, budget)
        var numerator = _mul_values[O](_view(high), _view(_derivative_values[O](_view(result), context, budget)), next - known, context, budget)
        var correction = _newton_divide[O](_view(numerator), _view(slope), next - known, context, budget)
        _allocation[O.Scalar](next - known, budget)
        result.reserve(next)
        for value in correction:
            result.append(O.apply(O.integer(0, context, budget), value, 1, context, budget))
        known = next
    return result^
