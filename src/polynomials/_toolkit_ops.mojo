"""Private arithmetic schedules shared by exact and numerical coefficient vectors."""
from .coefficient_buffer import _CoefficientView, _view
from .errors import Budget, PolyError, PolyErrorKind, _allocation, _charge_size, _product, _sum
from .coefficients import ModInt, Modulus, QQ
from ._series_rational import _compose_rational
from ._nmod import _field, _to, _from
from ._multipoint import _compose_series

comptime _NATIVE_COMPOSE = 16
"""Truncation order from which prime field and rational compositions use Brent-Kung steps."""


trait _ScalarOps:
    comptime Scalar: Copyable & Writable & Deinitable
    comptime Context: Copyable & Deinitable
    comptime EXACT: Bool

    @staticmethod
    def multiply(a: _CoefficientView[Self.Scalar, _], b: _CoefficientView[Self.Scalar, _], length: Int, context: Self.Context, mut budget: Budget) raises PolyError -> List[Self.Scalar]:
        ...

    @staticmethod
    def integer(value: Int, context: Self.Context, mut budget: Budget) raises PolyError -> Self.Scalar:
        ...

    @staticmethod
    def apply(a: Self.Scalar, b: Self.Scalar, operation: Int, context: Self.Context, mut budget: Budget) raises PolyError -> Self.Scalar:
        ...

    @staticmethod
    def copy(value: Self.Scalar, mut budget: Budget) raises PolyError -> Self.Scalar:
        ...

    @staticmethod
    def matches_integer(value: Self.Scalar, integer: Int, context: Self.Context, mut budget: Budget) raises PolyError -> Bool:
        ...

    @staticmethod
    def zero(value: Self.Scalar) -> Bool:
        ...


def _values[O: _ScalarOps](values: _CoefficientView[O.Scalar, _], length: Int, context: O.Context, mut budget: Budget) raises PolyError -> List[O.Scalar]:
    _allocation[O.Scalar](length, budget)
    var result = List[O.Scalar](capacity=length)
    for i in range(length):
        budget.charge(1)
        result.append(O.copy(values[i], budget) if i < len(values) else O.integer(0, context, budget))
    return result^


def _add_values[O: _ScalarOps](a: _CoefficientView[O.Scalar, _], b: _CoefficientView[O.Scalar, _], length: Int, subtract: Bool, context: O.Context, mut budget: Budget) raises PolyError -> List[O.Scalar]:
    var result = _values[O](_view(a), min(length, max(len(a), len(b))), context, budget)
    for i in range(min(length, len(b))):
        result[i] = O.apply(result[i], b[i], 1 if subtract else 0, context, budget)
    return result^


def _mul_values[O: _ScalarOps](a: _CoefficientView[O.Scalar, _], b: _CoefficientView[O.Scalar, _], length: Int, context: O.Context, mut budget: Budget) raises PolyError -> List[O.Scalar]:
    return O.multiply(_view(a), _view(b), length, context, budget)


def _convolve_values[O: _ScalarOps](a: _CoefficientView[O.Scalar, _], b: _CoefficientView[O.Scalar, _], length: Int, context: O.Context, mut budget: Budget) raises PolyError -> List[O.Scalar]:
    if length < 0:
        raise PolyError(PolyErrorKind.DOMAIN, "negative truncation order")
    var n = min(length, _sum(len(a), len(b)) - 1) if len(a) and len(b) else 0
    comptime if O.Scalar == ModInt and O.EXACT:
        if n >= _NATIVE_SERIES:
            ref ring = rebind[Modulus](context)
            return _as_mod_ints[O.Scalar](_native_convolve(_residues_of(a), _residues_of(b), n, ring.value, budget), ring, budget)
    _allocation[O.Scalar](n, budget)
    var result = List[O.Scalar](length=n, fill=O.integer(0, context, budget))
    for i in range(min(n, len(a))):
        for j in range(min(n - i, len(b))):
            var product = O.apply(a[i], b[j], 2, context, budget)
            result[i + j] = O.apply(result[i + j], product, 0, context, budget)
    return result^


def _compose_values[O: _ScalarOps, optimized: Bool = True](outer: _CoefficientView[O.Scalar, _], inner: _CoefficientView[O.Scalar, _], length: Int, context: O.Context, mut budget: Budget) raises PolyError -> List[O.Scalar]:
    if length < 0:
        raise PolyError(PolyErrorKind.DOMAIN, "negative truncation order")
    var result = List[O.Scalar]()
    if not length:
        return result^
    comptime if O.Scalar == ModInt and optimized:
        ref ring = rebind[Modulus](context)
        if length >= _NATIVE_COMPOSE and len(outer) >= _NATIVE_COMPOSE and ring.value > 2:
            var field = _field(ring.value)
            _allocation[UInt64](len(outer) + len(inner), budget)
            var f = List[UInt64](capacity=len(outer))
            for i in range(len(outer)):
                f.append(_to(rebind[ModInt](outer[i]).value, field))
            var g = List[UInt64](capacity=len(inner))
            for i in range(len(inner)):
                g.append(_to(rebind[ModInt](inner[i]).value, field))
            var values = _compose_series(f, g, length, field, budget)
            _allocation[O.Scalar](len(values), budget)
            result.reserve(len(values))
            for v in values:
                result.append(rebind_var[O.Scalar](ModInt(_from(v, field), ring)))
            return result^
    comptime if O.Scalar == QQ and optimized:
        if length >= _NATIVE_COMPOSE and len(outer) >= _NATIVE_COMPOSE:
            _allocation[QQ](len(outer) + len(inner), budget)
            var f = List[QQ](capacity=len(outer))
            for i in range(len(outer)):
                f.append(rebind[QQ](outer[i]).copy())
            var g = List[QQ](capacity=len(inner))
            for i in range(len(inner)):
                g.append(rebind[QQ](inner[i]).copy())
            var composed = _compose_rational(_view(f), _view(g), length, budget)
            if composed:
                return rebind_var[List[O.Scalar]](composed.take())
    for i in range(len(outer) - 1, -1, -1):
        budget.charge(1)
        comptime if optimized:
            var updated_result_1 = _mul_values[O](_view(result), _view(inner), length, context, budget)
            result = updated_result_1^
        else:
            var updated_result_2 = _convolve_values[O](_view(result), _view(inner), length, context, budget)
            result = updated_result_2^
        if not len(result):
            _allocation[O.Scalar](1, budget)
            result.append(O.copy(outer[i], budget))
        else:
            result[0] = O.apply(result[0], outer[i], 0, context, budget)
    return result^


def _derivative_values[O: _ScalarOps](values: _CoefficientView[O.Scalar, _], context: O.Context, mut budget: Budget) raises PolyError -> List[O.Scalar]:
    _allocation[O.Scalar](max(0, len(values) - 1), budget)
    var result = List[O.Scalar](capacity=max(0, len(values) - 1))
    for i in range(1, len(values)):
        result.append(O.apply(values[i], O.integer(i, context, budget), 2, context, budget))
    return result^


def _integral_values[O: _ScalarOps](values: _CoefficientView[O.Scalar, _], context: O.Context, mut budget: Budget) raises PolyError -> List[O.Scalar]:
    _allocation[O.Scalar](_sum(len(values), 1), budget)
    var result = List[O.Scalar](capacity=_sum(len(values), 1))
    result.append(O.integer(0, context, budget))
    for i in range(len(values)):
        budget.charge(1)
        if O.zero(values[i]):
            result.append(O.copy(values[i], budget))
        else:
            result.append(O.apply(values[i], O.integer(i + 1, context, budget), 3, context, budget))
    return result^


def _jet_values[O: _ScalarOps](values: _CoefficientView[O.Scalar, _], point: O.Scalar, length: Int, context: O.Context, mut budget: Budget) raises PolyError -> List[O.Scalar]:
    if length < 0:
        raise PolyError(PolyErrorKind.DOMAIN, "negative jet order")
    _allocation[O.Scalar](length, budget)
    var result = List[O.Scalar](length=length, fill=O.integer(0, context, budget))
    var n = min(length, len(values))
    if n:
        for i in range(len(values) - 1, -1, -1):
            for j in range(n - 1, 0, -1):
                result[j] = O.apply(O.apply(result[j], point, 2, context, budget), result[j - 1], 0, context, budget)
            result[0] = O.apply(O.apply(result[0], point, 2, context, budget), values[i], 0, context, budget)
    return result^


@always_inline
def _divide_values[O: _ScalarOps, inverse_only: Bool = False](a: _CoefficientView[O.Scalar, _], b: _CoefficientView[O.Scalar, _], length: Int, context: O.Context, mut budget: Budget) raises PolyError -> List[O.Scalar]:
    if length < 0:
        raise PolyError(PolyErrorKind.DOMAIN, "negative truncation order")
    if not len(b):
        raise PolyError(PolyErrorKind.DOMAIN, "zero series divisor")
    comptime if O.Scalar == ModInt and O.EXACT:
        # A zero constant takes the generic path, which raises.
        if length >= _NATIVE_SERIES and rebind[ModInt](b[0]).value != 0:
            ref ring = rebind[Modulus](context)
            var numerator = List[UInt64]() if inverse_only else _residues_of(a)
            if inverse_only:
                numerator.append(1)
            return _as_mod_ints[O.Scalar](_native_divide(numerator, _residues_of(b), length, ring.value, budget), ring, budget)
    var inverse = O.apply(O.integer(1, context, budget), b[0], 3, context, budget)
    _allocation[O.Scalar](length, budget)
    var result = List[O.Scalar](capacity=length)
    var begin = 0
    comptime if inverse_only:
        # Exact inverse callers need no allocated unit numerator or multiply by
        # one. Numerical callers retain the original rounded scalar schedule.
        comptime assert O.EXACT
        if length:
            result.append(O.copy(inverse, budget))
            begin = 1
    for k in range(begin, length):
        var value = O.copy(a[k], budget) if k < len(a) else O.integer(0, context, budget)
        for j in range(1, min(k + 1, len(b))):
            value = O.apply(value, O.apply(b[j], result[k - j], 2, context, budget), 1, context, budget)
        result.append(O.apply(value, inverse, 2, context, budget))
    return result^


def _newton_values[O: _ScalarOps](coefficients: _CoefficientView[O.Scalar, _], nodes: _CoefficientView[O.Scalar, _], context: O.Context, mut budget: Budget) raises PolyError -> List[O.Scalar]:
    if len(nodes) != max(0, len(coefficients) - 1):
        raise PolyError(PolyErrorKind.DOMAIN, "Newton node count must be one less than coefficient count")
    var result = List[O.Scalar]()
    for k in range(len(coefficients) - 1, -1, -1):
        if len(result):
            var minus = O.apply(O.integer(0, context, budget), nodes[k], 1, context, budget)
            var linear: List[O.Scalar] = [minus^, O.integer(1, context, budget)]
            var updated_result_3 = _mul_values[O](_view(result), _view(linear), len(coefficients), context, budget)
            result = updated_result_3^
            result[0] = O.apply(result[0], coefficients[k], 0, context, budget)
        else:
            _allocation[O.Scalar](1, budget)
            result.append(O.copy(coefficients[k], budget))
    return result^


def _divided_differences[O: _ScalarOps](points: _CoefficientView[O.Scalar, _], values: _CoefficientView[O.Scalar, _], context: O.Context, mut budget: Budget) raises PolyError -> List[O.Scalar]:
    if len(points) != len(values):
        raise PolyError(PolyErrorKind.DOMAIN, "interpolation point/value count mismatch")
    var coefficients = _values[O](_view(values), len(values), context, budget)
    for order in range(1, len(points)):
        for j in range(len(points) - 1, order - 1, -1):
            var numerator = O.apply(coefficients[j], coefficients[j - 1], 1, context, budget)
            var denominator = O.apply(points[j], points[j - order], 1, context, budget)
            coefficients[j] = O.apply(numerator, denominator, 3, context, budget)
    return coefficients^


def _hermite_values[O: _ScalarOps](points: _CoefficientView[O.Scalar, _], jets: List[List[O.Scalar]], derivatives: Bool, context: O.Context, mut budget: Budget) raises PolyError -> List[O.Scalar]:
    if len(points) != len(jets):
        raise PolyError(PolyErrorKind.DOMAIN, "Hermite point/jet count mismatch")
    var total = 0
    for values in jets:
        budget.charge(1)
        if not len(values):
            raise PolyError(PolyErrorKind.DOMAIN, "empty Hermite constraint")
        total = _sum(total, len(values))
    var result = List[O.Scalar]()
    var basis: List[O.Scalar] = [O.integer(1, context, budget)]
    for k in range(len(points)):
        var n = len(jets[k])
        var current = _jet_values[O](_view(result), points[k], n, context, budget)
        var divisor = _jet_values[O](_view(basis), points[k], n, context, budget)
        var wanted = _values[O](_view(jets[k]), n, context, budget)
        var factorial = O.integer(1, context, budget)
        for j in range(n):
            if derivatives and j:
                factorial = O.apply(factorial, O.integer(j, context, budget), 2, context, budget)
                wanted[j] = O.apply(wanted[j], factorial, 3, context, budget)
            wanted[j] = O.apply(wanted[j], current[j], 1, context, budget)
        var local = _divide_values[O](_view(wanted), _view(divisor), n, context, budget)
        var minus = O.apply(O.integer(0, context, budget), points[k], 1, context, budget)
        var linear: List[O.Scalar] = [minus^, O.integer(1, context, budget)]
        var shifted = _compose_values[O](_view(local), _view(linear), n, context, budget)
        var updated_result_4 = _add_values[O](_view(result), _view(_mul_values[O](_view(basis), _view(shifted), total, context, budget)), total, False, context, budget)
        result = updated_result_4^
        for _ in range(n):
            var updated_basis_5 = _mul_values[O](_view(basis), _view(linear), _sum(total, 1), context, budget)
            basis = updated_basis_5^
    return result^


# ------------------------------------------- native residue recurrences

comptime _NATIVE_SERIES = 32
"""Prime-field quadratic recurrences of at least this length run on native words."""


@always_inline
def _wide_mod(low: UInt128, carry: UInt64, p: UInt64, wrap: UInt64) -> UInt64:
    """(carry * 2^128 + low) mod p, given wrap = 2^128 mod p."""
    var r = UInt64(low % UInt128(p))
    if carry:
        r = UInt64((UInt128(r) + UInt128(carry) * UInt128(wrap)) % UInt128(p))
    return r


def _wrap(p: UInt64) -> UInt64:
    var r = UInt64((UInt128(1) << 64) % UInt128(p))
    return UInt64((UInt128(r) * UInt128(r)) % UInt128(p))


def _residues_of[T: Copyable & Deinitable](values: _CoefficientView[T, _]) -> List[UInt64]:
    var out = List[UInt64](capacity=len(values))
    for i in range(len(values)):
        out.append(rebind[ModInt](values[i]).value)
    return out^


def _native_divide(a: List[UInt64], b: List[UInt64], length: Int, p: UInt64, mut budget: Budget) raises PolyError -> List[UInt64]:
    """The first `length` coefficients of a / b modulo p, for b[0] invertible; one reduction per coefficient."""
    var inverse = _mod_power(b[0], p - 2, p)
    var wrap = _wrap(p)
    var r = List[UInt64](capacity=length)
    for k in range(length):
        var terms = min(k + 1, len(b)) - 1
        _charge_size(_sum(_product(2, terms), 2), budget)
        var low = UInt128(0)
        var carry = UInt64(0)
        for j in range(1, terms + 1):
            var t = low + UInt128(b.unsafe_get(j)) * UInt128(r.unsafe_get(k - j))
            carry += UInt64(1) if t < low else UInt64(0)
            low = t
        var sum = _wide_mod(low, carry, p, wrap)
        var value = a[k] if k < len(a) else UInt64(0)
        value = value - sum if value >= sum else value + p - sum
        r.append(UInt64((UInt128(value) * UInt128(inverse)) % UInt128(p)))
    return r^


def _native_exp(a: List[UInt64], length: Int, p: UInt64, mut budget: Budget) raises PolyError -> List[UInt64]:
    """exp(a) to `length` coefficients modulo p > length, a[0] = 0: n g_n = sum k a_k g_(n-k)."""
    var wrap = _wrap(p)
    # Inverses of 1 ..< length in linear time: 1/i = -(p // i) / (p mod i).
    var inverses = List[UInt64](length=max(length, 2), fill=0)
    inverses[1] = 1
    for i in range(2, length):
        inverses[i] = UInt64((UInt128(p - p // UInt64(i)) * UInt128(inverses[Int(p % UInt64(i))])) % UInt128(p))
    var scaled = List[UInt64](length=len(a), fill=0)
    for k in range(1, len(a)):
        scaled[k] = UInt64((UInt128(a[k]) * UInt128(UInt64(k))) % UInt128(p))
    var g = List[UInt64](capacity=length)
    g.append(1)
    for n in range(1, length):
        var terms = max(0, min(n + 1, len(a)) - 1)
        _charge_size(_sum(_product(4, terms), 2), budget)
        var low = UInt128(0)
        var carry = UInt64(0)
        for k in range(1, terms + 1):
            var t = low + UInt128(scaled.unsafe_get(k)) * UInt128(g.unsafe_get(n - k))
            carry += UInt64(1) if t < low else UInt64(0)
            low = t
        g.append(UInt64((UInt128(_wide_mod(low, carry, p, wrap)) * UInt128(inverses[n])) % UInt128(p)))
    return g^


def _native_convolve(a: List[UInt64], b: List[UInt64], n: Int, p: UInt64, mut budget: Budget) raises PolyError -> List[UInt64]:
    """The first n coefficients of a * b modulo p, one reduction per coefficient."""
    var wrap = _wrap(p)
    var out = List[UInt64](capacity=n)
    for s in range(n):
        var lo = max(0, s - len(b) + 1)
        var hi = min(s, len(a) - 1)
        _charge_size(_product(2, max(0, hi - lo + 1)), budget)
        var low = UInt128(0)
        var carry = UInt64(0)
        for i in range(lo, hi + 1):
            var t = low + UInt128(a.unsafe_get(i)) * UInt128(b.unsafe_get(s - i))
            carry += UInt64(1) if t < low else UInt64(0)
            low = t
        out.append(_wide_mod(low, carry, p, wrap))
    return out^


def _mod_power(a: UInt64, e: UInt64, p: UInt64) -> UInt64:
    var base = a % p
    var exponent = e
    var result = UInt64(1)
    while exponent:
        if exponent & 1:
            result = UInt64((UInt128(result) * UInt128(base)) % UInt128(p))
        exponent >>= 1
        if exponent:
            base = UInt64((UInt128(base) * UInt128(base)) % UInt128(p))
    return result


def _as_mod_ints[T: Writable & Copyable & Deinitable](values: List[UInt64], ring: Modulus, mut budget: Budget) raises PolyError -> List[T]:
    _allocation[T](len(values), budget)
    var out = List[T](capacity=len(values))
    for v in values:
        out.append(rebind_var[T](ModInt(v, ring)))
    return out^
