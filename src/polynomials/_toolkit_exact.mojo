"""Exact scalar operations for shared coefficient-vector algorithms."""
from ._toolkit_ops import _ScalarOps, _convolve_values
from .coefficients import CoefficientRing, ModInt, ZZ, QQ
from ._ntt import _ntt_low_product
from .dense import _karatsuba, _slice
from ._coefficient_ops import _exact, _copy
from .evaluate import _natural
from .coefficient_buffer import _CoefficientView, _view
from .errors import Budget, PolyError, PolyErrorKind, _charge_size, _sum, _allocation


struct _ExactOps[C: CoefficientRing](_ScalarOps):
    comptime Scalar = Self.C
    comptime Context = Self.C.Context
    comptime EXACT = True

    @staticmethod
    @always_inline
    def multiply(a: _CoefficientView[Self.Scalar, _], b: _CoefficientView[Self.Scalar, _], length: Int, context: Self.Context, mut budget: Budget) raises PolyError -> List[Self.Scalar]:
        # Keep the small kernel visible to callers; the larger work-stack
        # implementation must not make short Horner products pay call overhead.
        if min(length, min(len(a), len(b))) < 64:
            return _convolve_values[Self](_view(a), _view(b), length, context, budget)
        return _exact_product(_view(a), _view(b), length, context, budget)

    @staticmethod
    def integer(value: Int, context: Self.Context, mut budget: Budget) raises PolyError -> Self.Scalar:
        var magnitude = UInt64(value) if value >= 0 else UInt64(-(value + 1)) + 1
        var result = _natural[Self.C](magnitude, context, budget)
        return result.neg(budget) if value < 0 else result^

    @staticmethod
    @always_inline
    def apply(a: Self.Scalar, b: Self.Scalar, operation: Int, context: Self.Context, mut budget: Budget) raises PolyError -> Self.Scalar:
        if operation == 0:
            return a.add(b, budget)
        if operation == 1:
            return a.sub(b, budget)
        if operation == 2:
            return a.mul(b, budget)
        return _exact(a, b, budget)

    @staticmethod
    def copy(value: Self.Scalar, mut budget: Budget) raises PolyError -> Self.Scalar:
        return _copy(value, budget)

    @staticmethod
    def matches_integer(value: Self.Scalar, integer: Int, context: Self.Context, mut budget: Budget) raises PolyError -> Bool:
        var expected = Self.integer(integer, context, budget)
        _charge_size(_sum(value.size(), expected.size()), budget)
        return value == expected

    @staticmethod
    def zero(value: Self.Scalar) -> Bool:
        return value.is_zero()


@fieldwise_init
struct _LowProduct[C: CoefficientRing](Movable):
    var a: List[Self.C]
    var b: List[Self.C]
    var length: Int
    var split: Int


def _exact_product[C: CoefficientRing](a: _CoefficientView[C, _], b: _CoefficientView[C, _], length: Int, context: C.Context, mut budget: Budget) raises PolyError -> List[C]:
    if length < 0:
        raise PolyError(PolyErrorKind.DOMAIN, "negative truncation order")
    var na = min(length, len(a))
    var nb = min(length, len(b))
    if min(na, nb) < 64:
        return _convolve_values[_ExactOps[C]](_view(a), _view(b), length, context, budget)
    comptime if C == ModInt or C == ZZ or C == QQ:
        # Rational operands first pay for a common denominator and its gcds.
        if C != QQ or min(na, nb) >= 128:
            var transformed = _transform_product(a, b, na, nb, length, budget)
            if transformed:
                return transformed.take()
    _allocation[_LowProduct[C]](1, budget)
    var tasks = List[_LowProduct[C]]()
    tasks.append(_LowProduct[C](_slice(_view(a), 0, na, budget), _slice(_view(b), 0, nb, budget), length, 0))
    var answers = List[List[C]]()
    while len(tasks):
        budget.charge(1)
        var task = tasks.pop()
        if task.split:
            var right = answers.pop()
            var left = answers.pop()
            var result = answers.pop()
            while len(result) > task.length:
                budget.charge(1)
                _ = result.pop()
            _allocation[C](max(0, task.length - len(result)), budget)
            while len(result) < task.length:
                budget.charge(1)
                result.append(C.zero(context))
            for i in range(len(left)):
                result[task.split + i] = result[task.split + i].add(left[i], budget)
            for i in range(len(right)):
                result[task.split + i] = result[task.split + i].add(right[i], budget)
            _allocation[List[C]](1, budget)
            answers.append(result^)
            continue
        var n = min(task.length, _sum(len(task.a), len(task.b)) - 1) if len(task.a) and len(task.b) else 0
        var size = max(len(task.a), len(task.b))
        if min(len(task.a), len(task.b)) < 64 or n < 64:
            _allocation[List[C]](1, budget)
            answers.append(_convolve_values[_ExactOps[C]](_view(task.a), _view(task.b), n, context, budget))
        elif n > size:
            var result = _karatsuba(_view(task.a), _view(task.b), context, budget)
            while len(result) > n:
                budget.charge(1)
                _ = result.pop()
            _allocation[List[C]](1, budget)
            answers.append(result^)
        else:
            # Below x^n with n <= 2*k, the high/high product is irrelevant.
            # Existing full Karatsuba handles the low/low product; only the low
            # n-k coefficients of each cross product are needed.
            var k = size // 2 + size % 2
            var a0 = _slice(_view(task.a), 0, min(k, len(task.a)), budget)
            var b0 = _slice(_view(task.b), 0, min(k, len(task.b)), budget)
            var a1 = _slice(_view(task.a), min(k, len(task.a)), len(task.a), budget)
            var b1 = _slice(_view(task.b), min(k, len(task.b)), len(task.b), budget)
            _allocation[List[C]](1, budget)
            answers.append(_karatsuba(_view(a0), _view(b0), context, budget))
            _allocation[_LowProduct[C]](3, budget)
            tasks.append(_LowProduct[C](List[C](), List[C](), n, k))
            tasks.append(_LowProduct[C](a1^, b0^, n - k, 0))
            tasks.append(_LowProduct[C](a0^, b1^, n - k, 0))
    return answers.pop()


def _transform_product[C: CoefficientRing](a: _CoefficientView[C, _], b: _CoefficientView[C, _], na: Int, nb: Int, length: Int, mut budget: Budget) raises PolyError -> Optional[List[C]]:
    """The work-stack product's exact output by transforms, or None when they do not apply.

    The work stack returns n = min(length, na + nb - 1) coefficients when n is
    at most max(na, nb); otherwise its full product loses trailing zeros
    before truncation to n. The transform result keeps both shapes.
    """
    var full = na + nb - 1
    var n = min(length, full)
    if n <= max(na, nb):
        return _ntt_low_product(a, b, length, budget)
    var values = _ntt_low_product(a, b, full, budget)
    if not values:
        return None
    var result = values.take()
    while len(result) and result[len(result) - 1].is_zero():
        budget.charge(1)
        _ = result.pop()
    while len(result) > n:
        budget.charge(1)
        _ = result.pop()
    return result^


def _use_newton[C: CoefficientRing](length: Int, divisor_length: Int) -> Bool:
    comptime threshold = 2048 if C == ModInt else 256
    return length >= threshold and divisor_length >= 16
