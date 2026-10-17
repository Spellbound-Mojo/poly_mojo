"""Functional formal series with explicit truncation and exact field inference."""
from ._io_meta import _Record, _Series
from std.iter import Iterable, Iterator, StopIteration
from std.builtin.rebind import downcast
from std.memory import ArcPointer
from polynomials import Budget, PolyError, PolyErrorKind, CoefficientField, DensePoly, Modulus
from . import dense
from ._common import _Kind, _CoreKind, _Element, _Scalar, _Ring, _FieldKind, _Join, _WithModulus, _unwrap, _allocation, _charge_size, _compact, _domain, _data_context, Values
from ._interop import _dense_copy

comptime _Field[k: Int] = downcast[_Ring[k], CoefficientField]
from polynomials import TruncatedSeries


@fieldwise_init
struct Array[k: Int](Copyable, Movable, Iterable, Sized, _WithModulus, _Record):
    """Immutable formal-series coefficients with retained representation metadata.

    Parameters:
        k: The inferred exact field: QQ, QQi, GF(p), AA, or QQbar.
    """
    comptime _Format = _Series
    comptime _Item = _Scalar[Self.k]
    comptime _Power = Int
    var _core: ArcPointer[TruncatedSeries[_Field[Self.k]]]
    comptime IteratorType[iterable_mut: Bool, //, iterable_origin: Origin[mut=iterable_mut]]: Iterator = _SeriesIterator[Self.k, ImmOrigin(iterable_origin)]
    """A borrowing coefficient iterator.

    Parameters:
        iterable_mut: Whether the source origin permits mutation.
        iterable_origin: The lifetime of the source.
    """

    def __iter__(ref self) -> Self.IteratorType[origin_of(self)]:
        """Iterate in ascending coefficient order.

        Returns:
            A borrowing iterator over all retained coefficients.
        """
        return _SeriesIterator[Self.k, ImmOrigin(origin_of(self))](Pointer(to=self).as_imm(), 0)

    def __len__(self) -> Int:
        """Return the coefficient extent, including trailing zeros.

        Returns:
            The number of retained coefficients.
        """
        return self._core[].order

    def __getitem__(self, index: Int) -> _Scalar[Self.k]:
        """Read a coefficient at a valid zero-based index.

        Args:
            index: An index from zero through len(self)-1.

        Returns:
            An independent exact scalar.
        """
        debug_assert(index >= 0 and index < self.order(), "series index outside known coefficients")
        if index < len(self._core[].polynomial.coefficients):
            return _unwrap[Self.k](rebind[_Ring[Self.k]](self._core[].polynomial.coefficients[index]))
        return _unwrap[Self.k](rebind_var[_Ring[Self.k]](_Field[Self.k].zero(self._core[].polynomial.ring)))

    def modulus(self) -> UInt64:
        """Return the retained prime, or zero for QQ and QQi.

        Returns:
            The prime modulus or zero.
        """
        comptime if Self.k == 3:
            return rebind[Modulus](self._core[].polynomial.ring).value
        return 0

    def domain(self) -> String:
        """Return the retained coefficient field.

        Returns:
            QQ, QQi, or GF(p).
        """
        return _domain[Self.k](self.modulus())

    def order(self) -> Int:
        """Return the exponent of the unknown tail.

        Returns:
            The exponent n in the formal remainder O(x**n).
        """
        return self._core[].order


@fieldwise_init
struct _SeriesIterator[k: Int, origin: ImmOrigin](Iterator):
    comptime Element = _Scalar[Self.k]
    var source: Pointer[Array[Self.k], Self.origin]
    var position: Int

    def __next__(mut self) raises StopIteration -> Self.Element:
        if self.position == len(self.source[]):
            raise StopIteration()
        var value = self.source[][self.position]
        self.position += 1
        return value^

    def bounds(self) -> Tuple[Int, Optional[Int]]:
        var remaining = len(self.source[]) - self.position
        return remaining, Optional(remaining)


def _wrap_series[k: Int](var core: TruncatedSeries[_Field[k]], mut budget: Budget) raises PolyError -> Array[k]:
    core.polynomial.coefficients._compact(budget)
    _allocation[TruncatedSeries[_Field[k]]](1, budget)
    return Array[k](ArcPointer(core^))


def _order[I: Iterable](values: I) -> Int:
    comptime k = _Kind[_Element[I]]
    comptime if I == Array[k]:
        return rebind[Array[k]](values).order()
    return -1


def _polynomial[I: Iterable](values: I, mut budget: Budget) raises PolyError -> dense.Array[_Kind[_Element[I]]]:
    comptime k = _Kind[_Element[I]]
    comptime if I == Array[k]:
        return dense.Array[k](rebind_var[DensePoly[_Ring[k]]](_dense_copy(rebind[Array[k]](values)._core[].polynomial, 0, budget)), budget)
    else:
        return dense.asarray(values, budget)


def _requested(a: Int, b: Int, requested: Int) raises PolyError -> Int:
    if requested < -1:
        raise PolyError(PolyErrorKind.DOMAIN, "series order must be nonnegative")
    if requested >= 0:
        if (a >= 0 and requested > a) or (b >= 0 and requested > b):
            raise PolyError(PolyErrorKind.DOMAIN, "cannot invent unknown series coefficients")
        return requested
    if a < 0 and b < 0:
        raise PolyError(PolyErrorKind.DOMAIN, "coefficient inputs require order=")
    if a >= 0 and b >= 0 and a != b:
        raise PolyError(PolyErrorKind.DOMAIN, "series orders differ; pass a lower order explicitly")
    return max(a, b)


def _prepare[I: Iterable](values: I, order: Int, mut budget: Budget) raises PolyError -> Array[_FieldKind[_Kind[_Element[I]]]]:
    comptime k = _FieldKind[_Kind[_Element[I]]]
    var n = _requested(_order(values), -1, order)
    comptime if I == Array[k]:
        ref prepared = rebind[Array[k]](values)
        if n == prepared.order():
            budget.charge(1)
            return prepared.copy()
        return _wrap_series[k](prepared._core[].truncate(n, budget), budget)
    else:
        var p = dense.asarray(values, budget)
        var q = dense._promote[k](p, _data_context[k](p.modulus(), 0, budget), budget)
        return _wrap_series[k](TruncatedSeries[_Field[k]].from_polynomial(rebind[DensePoly[_Field[k]]](q._core[]), n, budget), budget)


def asarray[I: Iterable](values: I, mut budget: Budget, *, order: Int = -1) raises PolyError -> Array[_FieldKind[_Kind[_Element[I]]]]:
    """Construct a formal series; integer coefficients promote to QQ.

    Parameters:
        I: The inferred coefficient iterable type.

    Args:
        values: Ascending exact coefficients or a prepared series.
        budget: The shared work allowance, including preparation and result storage.
        order: Known coefficient count; omit only when a prepared series supplies it. An explicit lower order truncates inputs.

    Returns:
        An immutable series retaining its unknown-tail order.

    Raises:
        PolyError: DOMAIN for incompatible inputs or unavailable divisions, LIMIT for exhausted work, or CAPACITY for unrepresentable storage.
    """
    return _prepare(values, order, budget)


def asarray[I: Iterable](values: I, *, max_steps: UInt64 = UInt64.MAX, order: Int = -1) raises PolyError -> Array[_FieldKind[_Kind[_Element[I]]]]:
    """Construct a formal series; integer coefficients promote to QQ.

    Parameters:
        I: The inferred coefficient iterable type.

    Args:
        values: Ascending exact coefficients or a prepared series.
        max_steps: The complete call's work allowance; defaults to UInt64.MAX.
        order: Known coefficient count; omit only when a prepared series supplies it. An explicit lower order truncates inputs.

    Returns:
        An immutable series retaining its unknown-tail order.

    Raises:
        PolyError: DOMAIN for incompatible inputs or unavailable divisions, LIMIT for exhausted work, or CAPACITY for unrepresentable storage.
    """
    var budget = Budget(max_steps)
    return asarray(values, budget, order=order)


def add[A: Iterable, B: Iterable](a: A, b: B, mut budget: Budget, *, order: Int = -1) raises PolyError -> Array[_FieldKind[_Join[_Kind[_Element[A]], _Kind[_Element[B]]]]]:
    """Add series at a common explicit precision.

    Parameters:
        A: The left input iterable type.
        B: The right input iterable type.

    Args:
        a: The left series or ascending coefficients.
        b: The right series or ascending coefficients.
        budget: The shared work allowance, including preparation and result storage.
        order: Known coefficient count; omit only when a prepared series supplies it. An explicit lower order truncates inputs.

    Returns:
        A new series in the common inferred field.

    Raises:
        PolyError: DOMAIN for incompatible inputs or unavailable divisions, LIMIT for exhausted work, or CAPACITY for unrepresentable storage.
    """
    var n = _requested(_order(a), _order(b), order)
    comptime k = _FieldKind[_Join[_Kind[_Element[A]], _Kind[_Element[B]]]]
    var left = _polynomial(a, budget)
    var right = _polynomial(b, budget)
    var ctx = _data_context[k](left.modulus(), right.modulus(), budget)
    var p = dense._promote[k](left, ctx, budget)
    var q = dense._promote[k](right, ctx, budget)
    var first = TruncatedSeries[_Field[k]].from_polynomial(rebind[DensePoly[_Field[k]]](p._core[]), n, budget)
    var second = TruncatedSeries[_Field[k]].from_polynomial(rebind[DensePoly[_Field[k]]](q._core[]), n, budget)
    return _wrap_series[k](first.add(second, budget), budget)


def add[A: Iterable, B: Iterable](a: A, b: B, *, max_steps: UInt64 = UInt64.MAX, order: Int = -1) raises PolyError -> Array[_FieldKind[_Join[_Kind[_Element[A]], _Kind[_Element[B]]]]]:
    """Add series at a common explicit precision.

    Parameters:
        A: The left input iterable type.
        B: The right input iterable type.

    Args:
        a: The left series or ascending coefficients.
        b: The right series or ascending coefficients.
        max_steps: The complete call's work allowance; defaults to UInt64.MAX.
        order: Known coefficient count; omit only when a prepared series supplies it. An explicit lower order truncates inputs.

    Returns:
        A new series in the common inferred field.

    Raises:
        PolyError: DOMAIN for incompatible inputs or unavailable divisions, LIMIT for exhausted work, or CAPACITY for unrepresentable storage.
    """
    var budget = Budget(max_steps)
    return add(a, b, budget, order=order)


def subtract[A: Iterable, B: Iterable](a: A, b: B, mut budget: Budget, *, order: Int = -1) raises PolyError -> Array[_FieldKind[_Join[_Kind[_Element[A]], _Kind[_Element[B]]]]]:
    """Subtract series at a common explicit precision.

    Parameters:
        A: The left input iterable type.
        B: The right input iterable type.

    Args:
        a: The left series or ascending coefficients.
        b: The right series or ascending coefficients.
        budget: The shared work allowance, including preparation and result storage.
        order: Known coefficient count; omit only when a prepared series supplies it. An explicit lower order truncates inputs.

    Returns:
        A new series in the common inferred field.

    Raises:
        PolyError: DOMAIN for incompatible inputs or unavailable divisions, LIMIT for exhausted work, or CAPACITY for unrepresentable storage.
    """
    var n = _requested(_order(a), _order(b), order)
    comptime k = _FieldKind[_Join[_Kind[_Element[A]], _Kind[_Element[B]]]]
    var left = _polynomial(a, budget)
    var right = _polynomial(b, budget)
    var ctx = _data_context[k](left.modulus(), right.modulus(), budget)
    var p = dense._promote[k](left, ctx, budget)
    var q = dense._promote[k](right, ctx, budget)
    var first = TruncatedSeries[_Field[k]].from_polynomial(rebind[DensePoly[_Field[k]]](p._core[]), n, budget)
    var second = TruncatedSeries[_Field[k]].from_polynomial(rebind[DensePoly[_Field[k]]](q._core[]), n, budget)
    return _wrap_series[k](first.sub(second, budget), budget)


def subtract[A: Iterable, B: Iterable](a: A, b: B, *, max_steps: UInt64 = UInt64.MAX, order: Int = -1) raises PolyError -> Array[_FieldKind[_Join[_Kind[_Element[A]], _Kind[_Element[B]]]]]:
    """Subtract series at a common explicit precision.

    Parameters:
        A: The left input iterable type.
        B: The right input iterable type.

    Args:
        a: The left series or ascending coefficients.
        b: The right series or ascending coefficients.
        max_steps: The complete call's work allowance; defaults to UInt64.MAX.
        order: Known coefficient count; omit only when a prepared series supplies it. An explicit lower order truncates inputs.

    Returns:
        A new series in the common inferred field.

    Raises:
        PolyError: DOMAIN for incompatible inputs or unavailable divisions, LIMIT for exhausted work, or CAPACITY for unrepresentable storage.
    """
    var budget = Budget(max_steps)
    return subtract(a, b, budget, order=order)


def multiply[A: Iterable, B: Iterable](a: A, b: B, mut budget: Budget, *, order: Int = -1) raises PolyError -> Array[_FieldKind[_Join[_Kind[_Element[A]], _Kind[_Element[B]]]]]:
    """Multiply modulo the retained power of x.

    Parameters:
        A: The left input iterable type.
        B: The right input iterable type.

    Args:
        a: The left series or ascending coefficients.
        b: The right series or ascending coefficients.
        budget: The shared work allowance, including preparation and result storage.
        order: Known coefficient count; omit only when a prepared series supplies it. An explicit lower order truncates inputs.

    Returns:
        A new series in the common inferred field.

    Raises:
        PolyError: DOMAIN for incompatible inputs or unavailable divisions, LIMIT for exhausted work, or CAPACITY for unrepresentable storage.
    """
    var n = _requested(_order(a), _order(b), order)
    comptime k = _FieldKind[_Join[_Kind[_Element[A]], _Kind[_Element[B]]]]
    var left = _polynomial(a, budget)
    var right = _polynomial(b, budget)
    var ctx = _data_context[k](left.modulus(), right.modulus(), budget)
    var p = dense._promote[k](left, ctx, budget)
    var q = dense._promote[k](right, ctx, budget)
    var first = TruncatedSeries[_Field[k]].from_polynomial(rebind[DensePoly[_Field[k]]](p._core[]), n, budget)
    var second = TruncatedSeries[_Field[k]].from_polynomial(rebind[DensePoly[_Field[k]]](q._core[]), n, budget)
    return _wrap_series[k](first.mul(second, budget), budget)


def multiply[A: Iterable, B: Iterable](a: A, b: B, *, max_steps: UInt64 = UInt64.MAX, order: Int = -1) raises PolyError -> Array[_FieldKind[_Join[_Kind[_Element[A]], _Kind[_Element[B]]]]]:
    """Multiply modulo the retained power of x.

    Parameters:
        A: The left input iterable type.
        B: The right input iterable type.

    Args:
        a: The left series or ascending coefficients.
        b: The right series or ascending coefficients.
        max_steps: The complete call's work allowance; defaults to UInt64.MAX.
        order: Known coefficient count; omit only when a prepared series supplies it. An explicit lower order truncates inputs.

    Returns:
        A new series in the common inferred field.

    Raises:
        PolyError: DOMAIN for incompatible inputs or unavailable divisions, LIMIT for exhausted work, or CAPACITY for unrepresentable storage.
    """
    var budget = Budget(max_steps)
    return multiply(a, b, budget, order=order)


def divide[A: Iterable, B: Iterable](a: A, b: B, mut budget: Budget, *, order: Int = -1) raises PolyError -> Array[_FieldKind[_Join[_Kind[_Element[A]], _Kind[_Element[B]]]]]:
    """Divide by a series with invertible constant coefficient.

    Parameters:
        A: The left input iterable type.
        B: The right input iterable type.

    Args:
        a: The left series or ascending coefficients.
        b: The right series or ascending coefficients.
        budget: The shared work allowance, including preparation and result storage.
        order: Known coefficient count; omit only when a prepared series supplies it. An explicit lower order truncates inputs.

    Returns:
        A new series in the common inferred field.

    Raises:
        PolyError: DOMAIN for incompatible inputs or unavailable divisions, LIMIT for exhausted work, or CAPACITY for unrepresentable storage.
    """
    var n = _requested(_order(a), _order(b), order)
    comptime k = _FieldKind[_Join[_Kind[_Element[A]], _Kind[_Element[B]]]]
    var left = _polynomial(a, budget)
    var right = _polynomial(b, budget)
    var ctx = _data_context[k](left.modulus(), right.modulus(), budget)
    var p = dense._promote[k](left, ctx, budget)
    var q = dense._promote[k](right, ctx, budget)
    var first = TruncatedSeries[_Field[k]].from_polynomial(rebind[DensePoly[_Field[k]]](p._core[]), n, budget)
    var second = TruncatedSeries[_Field[k]].from_polynomial(rebind[DensePoly[_Field[k]]](q._core[]), n, budget)
    return _wrap_series[k](first.divide(second, budget), budget)


def divide[A: Iterable, B: Iterable](a: A, b: B, *, max_steps: UInt64 = UInt64.MAX, order: Int = -1) raises PolyError -> Array[_FieldKind[_Join[_Kind[_Element[A]], _Kind[_Element[B]]]]]:
    """Divide by a series with invertible constant coefficient.

    Parameters:
        A: The left input iterable type.
        B: The right input iterable type.

    Args:
        a: The left series or ascending coefficients.
        b: The right series or ascending coefficients.
        max_steps: The complete call's work allowance; defaults to UInt64.MAX.
        order: Known coefficient count; omit only when a prepared series supplies it. An explicit lower order truncates inputs.

    Returns:
        A new series in the common inferred field.

    Raises:
        PolyError: DOMAIN for incompatible inputs or unavailable divisions, LIMIT for exhausted work, or CAPACITY for unrepresentable storage.
    """
    var budget = Budget(max_steps)
    return divide(a, b, budget, order=order)


def compose[A: Iterable, B: Iterable](a: A, b: B, mut budget: Budget, *, order: Int = -1) raises PolyError -> Array[_FieldKind[_Join[_Kind[_Element[A]], _Kind[_Element[B]]]]]:
    """Compose with a zero-constant inner series.

    Parameters:
        A: The left input iterable type.
        B: The right input iterable type.

    Args:
        a: The left series or ascending coefficients.
        b: The right series or ascending coefficients.
        budget: The shared work allowance, including preparation and result storage.
        order: Known coefficient count; omit only when a prepared series supplies it. An explicit lower order truncates inputs.

    Returns:
        A new series in the common inferred field.

    Raises:
        PolyError: DOMAIN for incompatible inputs or unavailable divisions, LIMIT for exhausted work, or CAPACITY for unrepresentable storage.
    """
    var n = _requested(_order(a), _order(b), order)
    comptime k = _FieldKind[_Join[_Kind[_Element[A]], _Kind[_Element[B]]]]
    var left = _polynomial(a, budget)
    var right = _polynomial(b, budget)
    var ctx = _data_context[k](left.modulus(), right.modulus(), budget)
    var p = dense._promote[k](left, ctx, budget)
    var q = dense._promote[k](right, ctx, budget)
    var first = TruncatedSeries[_Field[k]].from_polynomial(rebind[DensePoly[_Field[k]]](p._core[]), n, budget)
    var second = TruncatedSeries[_Field[k]].from_polynomial(rebind[DensePoly[_Field[k]]](q._core[]), n, budget)
    return _wrap_series[k](first.compose(second, budget), budget)


def compose[A: Iterable, B: Iterable](a: A, b: B, *, max_steps: UInt64 = UInt64.MAX, order: Int = -1) raises PolyError -> Array[_FieldKind[_Join[_Kind[_Element[A]], _Kind[_Element[B]]]]]:
    """Compose with a zero-constant inner series.

    Parameters:
        A: The left input iterable type.
        B: The right input iterable type.

    Args:
        a: The left series or ascending coefficients.
        b: The right series or ascending coefficients.
        max_steps: The complete call's work allowance; defaults to UInt64.MAX.
        order: Known coefficient count; omit only when a prepared series supplies it. An explicit lower order truncates inputs.

    Returns:
        A new series in the common inferred field.

    Raises:
        PolyError: DOMAIN for incompatible inputs or unavailable divisions, LIMIT for exhausted work, or CAPACITY for unrepresentable storage.
    """
    var budget = Budget(max_steps)
    return compose(a, b, budget, order=order)


def reciprocal[I: Iterable](values: I, mut budget: Budget, *, order: Int = -1) raises PolyError -> Array[_FieldKind[_Kind[_Element[I]]]]:
    """Invert a series with nonzero constant coefficient.

    Parameters:
        I: The inferred input iterable type.

    Args:
        values: A prepared series or ascending exact coefficients.
        budget: The shared work allowance, including preparation and result storage.
        order: Known coefficient count; omit only when a prepared series supplies it. An explicit lower order truncates inputs.

    Returns:
        A new series with the mathematically available order.

    Raises:
        PolyError: DOMAIN for incompatible inputs or unavailable divisions, LIMIT for exhausted work, or CAPACITY for unrepresentable storage.
    """
    var p = _prepare(values, order, budget)
    return _wrap_series[_FieldKind[_Kind[_Element[I]]]](p._core[].inverse(budget), budget)


def reciprocal[I: Iterable](values: I, *, max_steps: UInt64 = UInt64.MAX, order: Int = -1) raises PolyError -> Array[_FieldKind[_Kind[_Element[I]]]]:
    """Invert a series with nonzero constant coefficient.

    Parameters:
        I: The inferred input iterable type.

    Args:
        values: A prepared series or ascending exact coefficients.
        max_steps: The complete call's work allowance; defaults to UInt64.MAX.
        order: Known coefficient count; omit only when a prepared series supplies it. An explicit lower order truncates inputs.

    Returns:
        A new series with the mathematically available order.

    Raises:
        PolyError: DOMAIN for incompatible inputs or unavailable divisions, LIMIT for exhausted work, or CAPACITY for unrepresentable storage.
    """
    var budget = Budget(max_steps)
    return reciprocal(values, budget, order=order)


def derivative[I: Iterable](values: I, mut budget: Budget, *, order: Int = -1) raises PolyError -> Array[_FieldKind[_Kind[_Element[I]]]]:
    """Differentiate, decreasing known order by one.

    Parameters:
        I: The inferred input iterable type.

    Args:
        values: A prepared series or ascending exact coefficients.
        budget: The shared work allowance, including preparation and result storage.
        order: Known coefficient count; omit only when a prepared series supplies it. An explicit lower order truncates inputs.

    Returns:
        A new series with the mathematically available order.

    Raises:
        PolyError: DOMAIN for incompatible inputs or unavailable divisions, LIMIT for exhausted work, or CAPACITY for unrepresentable storage.
    """
    var p = _prepare(values, order, budget)
    return _wrap_series[_FieldKind[_Kind[_Element[I]]]](p._core[].derivative(budget), budget)


def derivative[I: Iterable](values: I, *, max_steps: UInt64 = UInt64.MAX, order: Int = -1) raises PolyError -> Array[_FieldKind[_Kind[_Element[I]]]]:
    """Differentiate, decreasing known order by one.

    Parameters:
        I: The inferred input iterable type.

    Args:
        values: A prepared series or ascending exact coefficients.
        max_steps: The complete call's work allowance; defaults to UInt64.MAX.
        order: Known coefficient count; omit only when a prepared series supplies it. An explicit lower order truncates inputs.

    Returns:
        A new series with the mathematically available order.

    Raises:
        PolyError: DOMAIN for incompatible inputs or unavailable divisions, LIMIT for exhausted work, or CAPACITY for unrepresentable storage.
    """
    var budget = Budget(max_steps)
    return derivative(values, budget, order=order)


def integral[I: Iterable](values: I, mut budget: Budget, *, order: Int = -1) raises PolyError -> Array[_FieldKind[_Kind[_Element[I]]]]:
    """Integrate with zero constant, increasing known order by one.

    Parameters:
        I: The inferred input iterable type.

    Args:
        values: A prepared series or ascending exact coefficients.
        budget: The shared work allowance, including preparation and result storage.
        order: Known coefficient count; omit only when a prepared series supplies it. An explicit lower order truncates inputs.

    Returns:
        A new series with the mathematically available order.

    Raises:
        PolyError: DOMAIN for incompatible inputs or unavailable divisions, LIMIT for exhausted work, or CAPACITY for unrepresentable storage.
    """
    var p = _prepare(values, order, budget)
    return _wrap_series[_FieldKind[_Kind[_Element[I]]]](p._core[].integrate(budget), budget)


def integral[I: Iterable](values: I, *, max_steps: UInt64 = UInt64.MAX, order: Int = -1) raises PolyError -> Array[_FieldKind[_Kind[_Element[I]]]]:
    """Integrate with zero constant, increasing known order by one.

    Parameters:
        I: The inferred input iterable type.

    Args:
        values: A prepared series or ascending exact coefficients.
        max_steps: The complete call's work allowance; defaults to UInt64.MAX.
        order: Known coefficient count; omit only when a prepared series supplies it. An explicit lower order truncates inputs.

    Returns:
        A new series with the mathematically available order.

    Raises:
        PolyError: DOMAIN for incompatible inputs or unavailable divisions, LIMIT for exhausted work, or CAPACITY for unrepresentable storage.
    """
    var budget = Budget(max_steps)
    return integral(values, budget, order=order)


def log[I: Iterable](values: I, mut budget: Budget, *, order: Int = -1) raises PolyError -> Array[_FieldKind[_Kind[_Element[I]]]]:
    """Compute the formal logarithm of a unit-constant series.

    Parameters:
        I: The inferred input iterable type.

    Args:
        values: A prepared series or ascending exact coefficients.
        budget: The shared work allowance, including preparation and result storage.
        order: Known coefficient count; omit only when a prepared series supplies it. An explicit lower order truncates inputs.

    Returns:
        A new series with the mathematically available order.

    Raises:
        PolyError: DOMAIN for incompatible inputs or unavailable divisions, LIMIT for exhausted work, or CAPACITY for unrepresentable storage.
    """
    var p = _prepare(values, order, budget)
    return _wrap_series[_FieldKind[_Kind[_Element[I]]]](p._core[].log(budget), budget)


def log[I: Iterable](values: I, *, max_steps: UInt64 = UInt64.MAX, order: Int = -1) raises PolyError -> Array[_FieldKind[_Kind[_Element[I]]]]:
    """Compute the formal logarithm of a unit-constant series.

    Parameters:
        I: The inferred input iterable type.

    Args:
        values: A prepared series or ascending exact coefficients.
        max_steps: The complete call's work allowance; defaults to UInt64.MAX.
        order: Known coefficient count; omit only when a prepared series supplies it. An explicit lower order truncates inputs.

    Returns:
        A new series with the mathematically available order.

    Raises:
        PolyError: DOMAIN for incompatible inputs or unavailable divisions, LIMIT for exhausted work, or CAPACITY for unrepresentable storage.
    """
    var budget = Budget(max_steps)
    return log(values, budget, order=order)


def exp[I: Iterable](values: I, mut budget: Budget, *, order: Int = -1) raises PolyError -> Array[_FieldKind[_Kind[_Element[I]]]]:
    """Compute the formal exponential of a zero-constant series.

    Parameters:
        I: The inferred input iterable type.

    Args:
        values: A prepared series or ascending exact coefficients.
        budget: The shared work allowance, including preparation and result storage.
        order: Known coefficient count; omit only when a prepared series supplies it. An explicit lower order truncates inputs.

    Returns:
        A new series with the mathematically available order.

    Raises:
        PolyError: DOMAIN for incompatible inputs or unavailable divisions, LIMIT for exhausted work, or CAPACITY for unrepresentable storage.
    """
    var p = _prepare(values, order, budget)
    return _wrap_series[_FieldKind[_Kind[_Element[I]]]](p._core[].exp(budget), budget)


def exp[I: Iterable](values: I, *, max_steps: UInt64 = UInt64.MAX, order: Int = -1) raises PolyError -> Array[_FieldKind[_Kind[_Element[I]]]]:
    """Compute the formal exponential of a zero-constant series.

    Parameters:
        I: The inferred input iterable type.

    Args:
        values: A prepared series or ascending exact coefficients.
        max_steps: The complete call's work allowance; defaults to UInt64.MAX.
        order: Known coefficient count; omit only when a prepared series supplies it. An explicit lower order truncates inputs.

    Returns:
        A new series with the mathematically available order.

    Raises:
        PolyError: DOMAIN for incompatible inputs or unavailable divisions, LIMIT for exhausted work, or CAPACITY for unrepresentable storage.
    """
    var budget = Budget(max_steps)
    return exp(values, budget, order=order)


def revert[I: Iterable](values: I, mut budget: Budget, *, order: Int = -1) raises PolyError -> Array[_FieldKind[_Kind[_Element[I]]]]:
    """Invert composition for zero constant and nonzero linear coefficient.

    Parameters:
        I: The inferred input iterable type.

    Args:
        values: A prepared series or ascending exact coefficients.
        budget: The shared work allowance, including preparation and result storage.
        order: Known coefficient count; omit only when a prepared series supplies it. An explicit lower order truncates inputs.

    Returns:
        A new series with the mathematically available order.

    Raises:
        PolyError: DOMAIN for incompatible inputs or unavailable divisions, LIMIT for exhausted work, or CAPACITY for unrepresentable storage.
    """
    var p = _prepare(values, order, budget)
    return _wrap_series[_FieldKind[_Kind[_Element[I]]]](p._core[].revert(budget), budget)


def revert[I: Iterable](values: I, *, max_steps: UInt64 = UInt64.MAX, order: Int = -1) raises PolyError -> Array[_FieldKind[_Kind[_Element[I]]]]:
    """Invert composition for zero constant and nonzero linear coefficient.

    Parameters:
        I: The inferred input iterable type.

    Args:
        values: A prepared series or ascending exact coefficients.
        max_steps: The complete call's work allowance; defaults to UInt64.MAX.
        order: Known coefficient count; omit only when a prepared series supplies it. An explicit lower order truncates inputs.

    Returns:
        A new series with the mathematically available order.

    Raises:
        PolyError: DOMAIN for incompatible inputs or unavailable divisions, LIMIT for exhausted work, or CAPACITY for unrepresentable storage.
    """
    var budget = Budget(max_steps)
    return revert(values, budget, order=order)


def _constant[C: CoefficientField](value: C, like: TruncatedSeries[C], order: Int, mut budget: Budget) raises PolyError -> TruncatedSeries[C]:
    var poly = DensePoly[C].from_coefficients(like.polynomial.variable, like.polynomial.ring, [value.copy()], budget)
    return TruncatedSeries[C].from_polynomial(poly, order, budget)


def _series_sqrt[C: CoefficientField](f: TruncatedSeries[C], mut budget: Budget) raises PolyError -> TruncatedSeries[C]:
    # g = 1 / sqrt(f) doubles its precision by g <- g + g (1 - f g^2) / 2, and
    # sqrt(f) = f g. Only 2 must be invertible.
    var n = f.order
    var one = C.one(f.polynomial.ring)
    if n == 0:
        return f.copy()
    if len(f.polynomial.coefficients) == 0 or f.polynomial.coefficients[0] != one:
        raise PolyError(PolyErrorKind.DOMAIN, "series square root needs the constant term one")
    var two = one.add(one, budget)
    if two.is_zero():
        raise PolyError(PolyErrorKind.DOMAIN, "series square root needs 2 to be invertible")
    var half = two.inverse(budget)
    var g = _constant(one, f, 1, budget)
    var known = 1
    while known < n:
        budget.charge(1)
        var next = min(2 * known, n)
        var extended = TruncatedSeries[C].from_polynomial(g.polynomial, next, budget)
        var square = f.truncate(next, budget).mul(extended, budget).mul(extended, budget)
        var error = _constant(one, f, next, budget).sub(square, budget)
        g = extended.add(extended.mul(error, budget).mul(_constant(half, f, next, budget), budget), budget)
        known = next
    return f.mul(g, budget)


def _series_power[C: CoefficientField](f: TruncatedSeries[C], exponent: Int, mut budget: Budget) raises PolyError -> TruncatedSeries[C]:
    if exponent < 0:
        raise PolyError(PolyErrorKind.DOMAIN, "series power needs a nonnegative exponent")
    var result = _constant(C.one(f.polynomial.ring), f, f.order, budget)
    var base = f.copy()
    var remaining = exponent
    while remaining:
        budget.charge(1)
        if remaining & 1:
            result = result.mul(base, budget)
        remaining >>= 1
        if remaining:
            base = base.mul(base, budget)
    return result^


def sqrt[I: Iterable](values: I, mut budget: Budget, *, order: Int = -1) raises PolyError -> Array[_FieldKind[_Kind[_Element[I]]]]:
    """Compute the square root of a series whose constant term is one.

    Parameters:
        I: The inferred input iterable type.

    Args:
        values: A prepared series or ascending exact coefficients.
        budget: The shared work allowance, including preparation and result storage.
        order: Known coefficient count; omit only when a prepared series supplies it. An explicit lower order truncates inputs.

    Returns:
        The square root with constant term one, at the same order.

    Raises:
        PolyError: DOMAIN for another constant term or a field of characteristic two, LIMIT for exhausted work, or CAPACITY for unrepresentable storage.
    """
    var p = _prepare(values, order, budget)
    return _wrap_series[_FieldKind[_Kind[_Element[I]]]](_series_sqrt(p._core[], budget), budget)


def sqrt[I: Iterable](values: I, *, max_steps: UInt64 = UInt64.MAX, order: Int = -1) raises PolyError -> Array[_FieldKind[_Kind[_Element[I]]]]:
    """Compute the square root of a series whose constant term is one.

    Parameters:
        I: The inferred input iterable type.

    Args:
        values: A prepared series or ascending exact coefficients.
        max_steps: The complete call's work allowance; defaults to UInt64.MAX.
        order: Known coefficient count; omit only when a prepared series supplies it. An explicit lower order truncates inputs.

    Returns:
        The square root with constant term one, at the same order.

    Raises:
        PolyError: DOMAIN for another constant term or a field of characteristic two, LIMIT for exhausted work, or CAPACITY for unrepresentable storage.
    """
    var budget = Budget(max_steps)
    return sqrt(values, budget, order=order)


def power[I: Iterable](values: I, exponent: Int, mut budget: Budget, *, order: Int = -1) raises PolyError -> Array[_FieldKind[_Kind[_Element[I]]]]:
    """Raise a series to a nonnegative integer power at its order.

    Parameters:
        I: The inferred input iterable type.

    Args:
        values: A prepared series or ascending exact coefficients.
        exponent: A nonnegative exponent; zero returns one.
        budget: The shared work allowance, including preparation and result storage.
        order: Known coefficient count; omit only when a prepared series supplies it. An explicit lower order truncates inputs.

    Returns:
        The truncated power at the same order.

    Raises:
        PolyError: DOMAIN for a negative exponent, LIMIT for exhausted work, or CAPACITY for unrepresentable storage.
    """
    var p = _prepare(values, order, budget)
    return _wrap_series[_FieldKind[_Kind[_Element[I]]]](_series_power(p._core[], exponent, budget), budget)


def power[I: Iterable](values: I, exponent: Int, *, max_steps: UInt64 = UInt64.MAX, order: Int = -1) raises PolyError -> Array[_FieldKind[_Kind[_Element[I]]]]:
    """Raise a series to a nonnegative integer power at its order.

    Parameters:
        I: The inferred input iterable type.

    Args:
        values: A prepared series or ascending exact coefficients.
        exponent: A nonnegative exponent; zero returns one.
        max_steps: The complete call's work allowance; defaults to UInt64.MAX.
        order: Known coefficient count; omit only when a prepared series supplies it. An explicit lower order truncates inputs.

    Returns:
        The truncated power at the same order.

    Raises:
        PolyError: DOMAIN for a negative exponent, LIMIT for exhausted work, or CAPACITY for unrepresentable storage.
    """
    var budget = Budget(max_steps)
    return power(values, exponent, budget, order=order)


def negative[I: Iterable](values: I, mut budget: Budget, *, order: Int = -1) raises PolyError -> Array[_FieldKind[_Kind[_Element[I]]]]:
    """Negate the known coefficients without changing their order.

    Parameters:
        I: The inferred coefficient iterable type.

    Args:
        values: A prepared series or ascending coefficients.
        budget: The shared work allowance, including preparation and result storage.
        order: Known coefficient count; omit only when a prepared series supplies it. An explicit lower order truncates inputs.

    Returns:
        A new formal series.

    Raises:
        PolyError: DOMAIN for incompatible inputs or unavailable divisions, LIMIT for exhausted work, or CAPACITY for unrepresentable storage.
    """
    var p = _prepare(values, order, budget)
    comptime k = _FieldKind[_Kind[_Element[I]]]
    return _wrap_series[k](TruncatedSeries[_Field[k]](p._core[].polynomial.neg(budget), p.order()), budget)


def negative[I: Iterable](values: I, *, max_steps: UInt64 = UInt64.MAX, order: Int = -1) raises PolyError -> Array[_FieldKind[_Kind[_Element[I]]]]:
    """Negate the known coefficients without changing their order.

    Parameters:
        I: The inferred coefficient iterable type.

    Args:
        values: A prepared series or ascending coefficients.
        max_steps: The complete call's work allowance; defaults to UInt64.MAX.
        order: Known coefficient count; omit only when a prepared series supplies it. An explicit lower order truncates inputs.

    Returns:
        A new formal series.

    Raises:
        PolyError: DOMAIN for incompatible inputs or unavailable divisions, LIMIT for exhausted work, or CAPACITY for unrepresentable storage.
    """
    var budget = Budget(max_steps)
    return negative(values, budget, order=order)


def truncate[k: Int](values: Array[k], order: Int, mut budget: Budget) raises PolyError -> Array[k]:
    """Lower a series order without inventing unknown coefficients.

    Parameters:
        k: The inferred coefficient field.

    Args:
        values: The prepared input series.
        order: A nonnegative order no greater than the input order.
        budget: The shared work allowance, including preparation and result storage.

    Returns:
        A new series at the requested order.

    Raises:
        PolyError: DOMAIN for incompatible inputs or unavailable divisions, LIMIT for exhausted work, or CAPACITY for unrepresentable storage.
    """
    return _wrap_series[k](values._core[].truncate(order, budget), budget)


def truncate[k: Int](values: Array[k], order: Int, *, max_steps: UInt64 = UInt64.MAX) raises PolyError -> Array[k]:
    """Lower a series order without inventing unknown coefficients.

    Parameters:
        k: The inferred coefficient field.

    Args:
        values: The prepared input series.
        order: A nonnegative order no greater than the input order.
        max_steps: The complete call's work allowance; defaults to UInt64.MAX.

    Returns:
        A new series at the requested order.

    Raises:
        PolyError: DOMAIN for incompatible inputs or unavailable divisions, LIMIT for exhausted work, or CAPACITY for unrepresentable storage.
    """
    var budget = Budget(max_steps)
    return truncate(values, order, budget)


def to_polynomial[k: Int](values: Array[k], mut budget: Budget) raises PolyError -> dense.Array[k]:
    """Copy the known coefficients into a polynomial, explicitly discarding the unknown tail.

    Parameters:
        k: The inferred coefficient field.

    Args:
        values: The prepared input series.
        budget: The shared work allowance, including preparation and result storage.

    Returns:
        A canonical polynomial representing only the known part.

    Raises:
        PolyError: DOMAIN for incompatible inputs or unavailable divisions, LIMIT for exhausted work, or CAPACITY for unrepresentable storage.
    """
    return dense.Array[k](rebind_var[DensePoly[_Ring[k]]](_dense_copy(values._core[].polynomial, 0, budget)), budget)


def to_polynomial[k: Int](values: Array[k], *, max_steps: UInt64 = UInt64.MAX) raises PolyError -> dense.Array[k]:
    """Copy the known coefficients into a polynomial, explicitly discarding the unknown tail.

    Parameters:
        k: The inferred coefficient field.

    Args:
        values: The prepared input series.
        max_steps: The complete call's work allowance; defaults to UInt64.MAX.

    Returns:
        A canonical polynomial representing only the known part.

    Raises:
        PolyError: DOMAIN for incompatible inputs or unavailable divisions, LIMIT for exhausted work, or CAPACITY for unrepresentable storage.
    """
    var budget = Budget(max_steps)
    return to_polynomial(values, budget)


def coefficients[k: Int](values: Array[k], mut budget: Budget) raises PolyError -> Values[_Scalar[k], k]:
    """Materialize every known coefficient, including implicit trailing zeros.

    Parameters:
        k: The inferred coefficient field.

    Args:
        values: The prepared input series.
        budget: The shared work allowance, including preparation and result storage.

    Returns:
        An immutable scalar sequence of length order().

    Raises:
        PolyError: DOMAIN for incompatible inputs or unavailable divisions, LIMIT for exhausted work, or CAPACITY for unrepresentable storage.
    """
    _allocation[_Scalar[k]](values.order(), budget)
    var result = List[_Scalar[k]](capacity=values.order())
    for i in range(values.order()):
        budget.charge(1)
        if i < len(values._core[].polynomial.coefficients):
            _charge_size(values._core[].polynomial.coefficients[i].size(), budget)
        result.append(values[i])
    return Values[_Scalar[k], k](result^, values.modulus(), budget)


def coefficients[k: Int](values: Array[k], *, max_steps: UInt64 = UInt64.MAX) raises PolyError -> Values[_Scalar[k], k]:
    """Materialize every known coefficient, including implicit trailing zeros.

    Parameters:
        k: The inferred coefficient field.

    Args:
        values: The prepared input series.
        max_steps: The complete call's work allowance; defaults to UInt64.MAX.

    Returns:
        An immutable scalar sequence of length order().

    Raises:
        PolyError: DOMAIN for incompatible inputs or unavailable divisions, LIMIT for exhausted work, or CAPACITY for unrepresentable storage.
    """
    var budget = Budget(max_steps)
    return coefficients(values, budget)


def to_core[k: Int](values: Array[k], mut budget: Budget, *, variable: Int64 = 0) raises PolyError -> TruncatedSeries[_Field[k]]:
    """Export independent mutable core storage.

    Parameters:
        k: The inferred coefficient field.

    Args:
        values: The prepared input series.
        budget: The shared work allowance, including preparation and result storage.
        variable: The core variable ID assigned to the exported value.

    Returns:
        A core series with the same order and field.

    Raises:
        PolyError: DOMAIN for incompatible inputs or unavailable divisions, LIMIT for exhausted work, or CAPACITY for unrepresentable storage.
    """
    return TruncatedSeries[_Field[k]](_dense_copy(values._core[].polynomial, variable, budget), values.order())


def to_core[k: Int](values: Array[k], *, max_steps: UInt64 = UInt64.MAX, variable: Int64 = 0) raises PolyError -> TruncatedSeries[_Field[k]]:
    """Export independent mutable core storage.

    Parameters:
        k: The inferred coefficient field.

    Args:
        values: The prepared input series.
        max_steps: The complete call's work allowance; defaults to UInt64.MAX.
        variable: The core variable ID assigned to the exported value.

    Returns:
        A core series with the same order and field.

    Raises:
        PolyError: DOMAIN for incompatible inputs or unavailable divisions, LIMIT for exhausted work, or CAPACITY for unrepresentable storage.
    """
    var budget = Budget(max_steps)
    return to_core(values, budget, variable=variable)


def from_core[C: CoefficientField](values: TruncatedSeries[C], mut budget: Budget) raises PolyError -> Array[_CoreKind[C]]:
    """Validate and copy a core series into immutable array storage.

    Parameters:
        C: The inferred supported exact coefficient field.

    Args:
        values: The core series to import.
        budget: The shared work allowance, including preparation and result storage.

    Returns:
        An independent series using array axis zero.

    Raises:
        PolyError: DOMAIN for incompatible inputs or unavailable divisions, LIMIT for exhausted work, or CAPACITY for unrepresentable storage.
    """
    comptime k = _CoreKind[C]
    comptime assert k >= 1, "series supports QQ, QQi, and ModInt"
    if values.order < 0 or len(values.polynomial.coefficients) > values.order:
        raise PolyError(PolyErrorKind.DOMAIN, "invalid core series order")
    var p = _dense_copy(values.polynomial, 0, budget)
    return _wrap_series[k](TruncatedSeries[_Field[k]](rebind_var[DensePoly[_Field[k]]](p^), values.order), budget)


def from_core[C: CoefficientField](values: TruncatedSeries[C], *, max_steps: UInt64 = UInt64.MAX) raises PolyError -> Array[_CoreKind[C]]:
    """Validate and copy a core series into immutable array storage.

    Parameters:
        C: The inferred supported exact coefficient field.

    Args:
        values: The core series to import.
        max_steps: The complete call's work allowance; defaults to UInt64.MAX.

    Returns:
        An independent series using array axis zero.

    Raises:
        PolyError: DOMAIN for incompatible inputs or unavailable divisions, LIMIT for exhausted work, or CAPACITY for unrepresentable storage.
    """
    var budget = Budget(max_steps)
    return from_core(values, budget)


from . import _numeric as _num
from polynomials import NumericDomain, NumericSeries


@fieldwise_init
struct NumericArray[D: NumericDomain](Copyable, Movable, Iterable, Sized, _Record):
    """Immutable numerical formal coefficients with a known truncation order.

    Parameters:
        D: The numerical coefficient domain.
    """
    comptime _Format = _Series
    comptime _Item = Self.D.Scalar
    comptime _Power = Int
    var _core: ArcPointer[NumericSeries[Self.D]]
    var _zero: ArcPointer[List[Self.D.Scalar]]
    comptime IteratorType[iterable_mut: Bool, //, iterable_origin: Origin[mut=iterable_mut]]: Iterator = _NumericIterator[Self.D, ImmOrigin(iterable_origin)]
    """Borrow the representation's complete coefficient sequence.

    Parameters:
        iterable_mut: Whether the borrowing origin is mutable.
        iterable_origin: The source origin.
    """

    def __iter__(ref self) -> Self.IteratorType[origin_of(self)]:
        """Iterate over stored and implicit zero coefficients.

        Returns:
            An iterator borrowing the immutable representation.
        """
        return _NumericIterator[Self.D, ImmOrigin(origin_of(self))](Pointer(to=self).as_imm(), 0)

    def __len__(self) -> Int:
        """Return the full coefficient extent, including zeros.

        Returns:
            The retained coefficient count.
        """
        return self._core[].order

    def __getitem__(self, index: Int) -> Self.D.Scalar:
        """Copy a coefficient at a valid zero-based index.

        Args:
            index: An index below len(self).

        Returns:
            An independent coefficient value.
        """
        debug_assert(index >= 0 and index < len(self), "coefficient index out of range")
        if index < len(self._core[].polynomial.coefficients):
            return self._core[].polynomial.coefficients[index].copy()
        return self._zero[][0].copy()

    def order(self) -> Int:
        """Return the exponent of the unknown formal tail.

        Returns:
            The n in O(x**n); this is not an analytic error bound.
        """
        return self._core[].order


@fieldwise_init
struct _NumericIterator[D: NumericDomain, origin: ImmOrigin](Iterator):
    comptime Element = Self.D.Scalar
    var source: Pointer[NumericArray[Self.D], Self.origin]
    var position: Int

    def __next__(mut self) raises StopIteration -> Self.D.Scalar:
        if self.position == len(self.source[]):
            raise StopIteration()
        var result = self.source[][self.position]
        self.position += 1
        return result^


def _numeric_wrap[D: NumericDomain](var core: NumericSeries[D], context: D.Context, mut budget: Budget) raises PolyError -> NumericArray[D]:
    _num._context[D](context, budget)
    _compact(core.polynomial.coefficients, budget)
    _allocation[NumericSeries[D]](1, budget)
    _allocation[D.Scalar](1, budget)
    _allocation[List[D.Scalar]](1, budget)
    var zero: List[D.Scalar] = [_num._value[D](0, context, budget)]
    return NumericArray[D](ArcPointer(core^), ArcPointer(zero^))


def asarray[I: Iterable, Context: Copyable & Deinitable](values: I, mut budget: Budget, *, context: Context, order: Int = -1) raises PolyError -> NumericArray[_num._Domain[Context, _Element[I]]]:
    """Construct numerical formal coefficients with an explicit unknown-tail order.

    Parameters:
        I: Inferred from the input types.
        Context: Inferred from the input types.

    Args:
        values: Coefficients, terms, or a prepared value.
        budget: The shared work allowance.
        context: Explicit output precision and rounding or enclosure settings.
        order: Known coefficient count; -1 reuses a prepared series' order. Raw sequences require a nonnegative value.

    Returns:
        Numerical formal coefficients with a retained unknown-tail order; balls enclose coefficients only.

    Raises:
        PolyError: DOMAIN for invalid input, or LIMIT/CAPACITY on resource limits.
    """
    comptime D = _num._Domain[Context, _Element[I]]
    _num._context[D](rebind[D.Context](context), budget)
    comptime if I == NumericArray[D]:
        ref prepared = rebind[NumericArray[D]](values)
        var n = prepared.order() if order == -1 else order
        if n == prepared.order():
            budget.charge(1)
            return prepared.copy()
        var core = prepared._core[].truncate(n, rebind[D.Context](context), budget)
        return _numeric_wrap(core^, rebind[D.Context](context), budget)
    else:
        if order < 0:
            raise PolyError(PolyErrorKind.DOMAIN, "raw series coefficients require a nonnegative order")
        var p = _num._dense[D](values, rebind[D.Context](context), budget)
        var core = NumericSeries[D].from_polynomial(p._core[], order, rebind[D.Context](context), budget)
        return _numeric_wrap(core^, rebind[D.Context](context), budget)


def asarray[I: Iterable, Context: Copyable & Deinitable](values: I, *, context: Context, order: Int = -1, max_steps: UInt64 = UInt64.MAX) raises PolyError -> NumericArray[_num._Domain[Context, _Element[I]]]:
    """Construct numerical formal coefficients with an explicit unknown-tail order.

    Parameters:
        I: Inferred from the input types.
        Context: Inferred from the input types.

    Args:
        values: Coefficients, terms, or a prepared value.
        context: Explicit output precision and rounding or enclosure settings.
        order: Known coefficient count; -1 reuses a prepared series' order. Raw sequences require a nonnegative value.
        max_steps: The complete call's work allowance.

    Returns:
        Numerical formal coefficients with a retained unknown-tail order; balls enclose coefficients only.

    Raises:
        PolyError: DOMAIN for invalid input, or LIMIT/CAPACITY on resource limits.
    """
    var budget = Budget(max_steps)
    return asarray(values, budget, context=context, order=order)


def add[D: NumericDomain](a: NumericArray[D], b: NumericArray[D], mut budget: Budget, *, context: D.Context, order: Int = -1) raises PolyError -> NumericArray[D]:
    """Add numerical series at a common formal order.

    Parameters:
        D: The numerical coefficient domain.

    Args:
        a: The first prepared value.
        b: The second prepared value.
        budget: The shared work allowance.
        context: Explicit output precision and rounding or enclosure settings.
        order: Explicit common lower order, or -1 to require matching prepared orders.

    Returns:
        Numerical formal coefficients with a retained unknown-tail order; balls enclose coefficients only.

    Raises:
        PolyError: DOMAIN for invalid input, or LIMIT/CAPACITY on resource limits.
    """
    var n = _requested(a.order(), b.order(), order)
    var left = a._core[].truncate(n, context, budget)
    var right = b._core[].truncate(n, context, budget)
    var result = left.add(right, context, budget)
    return _numeric_wrap(result^, context, budget)


def add[D: NumericDomain](a: NumericArray[D], b: NumericArray[D], *, context: D.Context, order: Int = -1, max_steps: UInt64 = UInt64.MAX) raises PolyError -> NumericArray[D]:
    """Add numerical series at a common formal order.

    Parameters:
        D: The numerical coefficient domain.

    Args:
        a: The first prepared value.
        b: The second prepared value.
        context: Explicit output precision and rounding or enclosure settings.
        order: Explicit common lower order, or -1 to require matching prepared orders.
        max_steps: The complete call's work allowance.

    Returns:
        Numerical formal coefficients with a retained unknown-tail order; balls enclose coefficients only.

    Raises:
        PolyError: DOMAIN for invalid input, or LIMIT/CAPACITY on resource limits.
    """
    var budget = Budget(max_steps)
    return add(a, b, budget, context=context, order=order)


def subtract[D: NumericDomain](a: NumericArray[D], b: NumericArray[D], mut budget: Budget, *, context: D.Context, order: Int = -1) raises PolyError -> NumericArray[D]:
    """Subtract numerical series at a common formal order.

    Parameters:
        D: The numerical coefficient domain.

    Args:
        a: The first prepared value.
        b: The second prepared value.
        budget: The shared work allowance.
        context: Explicit output precision and rounding or enclosure settings.
        order: Explicit common lower order, or -1 to require matching prepared orders.

    Returns:
        Numerical formal coefficients with a retained unknown-tail order; balls enclose coefficients only.

    Raises:
        PolyError: DOMAIN for invalid input, or LIMIT/CAPACITY on resource limits.
    """
    var n = _requested(a.order(), b.order(), order)
    var left = a._core[].truncate(n, context, budget)
    var right = b._core[].truncate(n, context, budget)
    var result = left.sub(right, context, budget)
    return _numeric_wrap(result^, context, budget)


def subtract[D: NumericDomain](a: NumericArray[D], b: NumericArray[D], *, context: D.Context, order: Int = -1, max_steps: UInt64 = UInt64.MAX) raises PolyError -> NumericArray[D]:
    """Subtract numerical series at a common formal order.

    Parameters:
        D: The numerical coefficient domain.

    Args:
        a: The first prepared value.
        b: The second prepared value.
        context: Explicit output precision and rounding or enclosure settings.
        order: Explicit common lower order, or -1 to require matching prepared orders.
        max_steps: The complete call's work allowance.

    Returns:
        Numerical formal coefficients with a retained unknown-tail order; balls enclose coefficients only.

    Raises:
        PolyError: DOMAIN for invalid input, or LIMIT/CAPACITY on resource limits.
    """
    var budget = Budget(max_steps)
    return subtract(a, b, budget, context=context, order=order)


def multiply[D: NumericDomain](a: NumericArray[D], b: NumericArray[D], mut budget: Budget, *, context: D.Context, order: Int = -1) raises PolyError -> NumericArray[D]:
    """Multiply numerical series at a common formal order.

    Parameters:
        D: The numerical coefficient domain.

    Args:
        a: The first prepared value.
        b: The second prepared value.
        budget: The shared work allowance.
        context: Explicit output precision and rounding or enclosure settings.
        order: Explicit common lower order, or -1 to require matching prepared orders.

    Returns:
        Numerical formal coefficients with a retained unknown-tail order; balls enclose coefficients only.

    Raises:
        PolyError: DOMAIN for invalid input, or LIMIT/CAPACITY on resource limits.
    """
    var n = _requested(a.order(), b.order(), order)
    var left = a._core[].truncate(n, context, budget)
    var right = b._core[].truncate(n, context, budget)
    var result = left.mul(right, context, budget)
    return _numeric_wrap(result^, context, budget)


def multiply[D: NumericDomain](a: NumericArray[D], b: NumericArray[D], *, context: D.Context, order: Int = -1, max_steps: UInt64 = UInt64.MAX) raises PolyError -> NumericArray[D]:
    """Multiply numerical series at a common formal order.

    Parameters:
        D: The numerical coefficient domain.

    Args:
        a: The first prepared value.
        b: The second prepared value.
        context: Explicit output precision and rounding or enclosure settings.
        order: Explicit common lower order, or -1 to require matching prepared orders.
        max_steps: The complete call's work allowance.

    Returns:
        Numerical formal coefficients with a retained unknown-tail order; balls enclose coefficients only.

    Raises:
        PolyError: DOMAIN for invalid input, or LIMIT/CAPACITY on resource limits.
    """
    var budget = Budget(max_steps)
    return multiply(a, b, budget, context=context, order=order)


def divide[D: NumericDomain](a: NumericArray[D], b: NumericArray[D], mut budget: Budget, *, context: D.Context, order: Int = -1) raises PolyError -> NumericArray[D]:
    """Divide numerical series at a common formal order.

    Parameters:
        D: The numerical coefficient domain.

    Args:
        a: The first prepared value.
        b: The second prepared value.
        budget: The shared work allowance.
        context: Explicit output precision and rounding or enclosure settings.
        order: Explicit common lower order, or -1 to require matching prepared orders.

    Returns:
        Numerical formal coefficients with a retained unknown-tail order; balls enclose coefficients only.

    Raises:
        PolyError: DOMAIN for invalid input, or LIMIT/CAPACITY on resource limits.
    """
    var n = _requested(a.order(), b.order(), order)
    var left = a._core[].truncate(n, context, budget)
    var right = b._core[].truncate(n, context, budget)
    var result = left.divide(right, context, budget)
    return _numeric_wrap(result^, context, budget)


def divide[D: NumericDomain](a: NumericArray[D], b: NumericArray[D], *, context: D.Context, order: Int = -1, max_steps: UInt64 = UInt64.MAX) raises PolyError -> NumericArray[D]:
    """Divide numerical series at a common formal order.

    Parameters:
        D: The numerical coefficient domain.

    Args:
        a: The first prepared value.
        b: The second prepared value.
        context: Explicit output precision and rounding or enclosure settings.
        order: Explicit common lower order, or -1 to require matching prepared orders.
        max_steps: The complete call's work allowance.

    Returns:
        Numerical formal coefficients with a retained unknown-tail order; balls enclose coefficients only.

    Raises:
        PolyError: DOMAIN for invalid input, or LIMIT/CAPACITY on resource limits.
    """
    var budget = Budget(max_steps)
    return divide(a, b, budget, context=context, order=order)


def compose[D: NumericDomain](a: NumericArray[D], b: NumericArray[D], mut budget: Budget, *, context: D.Context, order: Int = -1) raises PolyError -> NumericArray[D]:
    """Compose numerical series at a common formal order.

    Parameters:
        D: The numerical coefficient domain.

    Args:
        a: The first prepared value.
        b: The second prepared value.
        budget: The shared work allowance.
        context: Explicit output precision and rounding or enclosure settings.
        order: Explicit common lower order, or -1 to require matching prepared orders.

    Returns:
        Numerical formal coefficients with a retained unknown-tail order; balls enclose coefficients only.

    Raises:
        PolyError: DOMAIN for invalid input, or LIMIT/CAPACITY on resource limits.
    """
    var n = _requested(a.order(), b.order(), order)
    var left = a._core[].truncate(n, context, budget)
    var right = b._core[].truncate(n, context, budget)
    var result = left.compose(right, context, budget)
    return _numeric_wrap(result^, context, budget)


def compose[D: NumericDomain](a: NumericArray[D], b: NumericArray[D], *, context: D.Context, order: Int = -1, max_steps: UInt64 = UInt64.MAX) raises PolyError -> NumericArray[D]:
    """Compose numerical series at a common formal order.

    Parameters:
        D: The numerical coefficient domain.

    Args:
        a: The first prepared value.
        b: The second prepared value.
        context: Explicit output precision and rounding or enclosure settings.
        order: Explicit common lower order, or -1 to require matching prepared orders.
        max_steps: The complete call's work allowance.

    Returns:
        Numerical formal coefficients with a retained unknown-tail order; balls enclose coefficients only.

    Raises:
        PolyError: DOMAIN for invalid input, or LIMIT/CAPACITY on resource limits.
    """
    var budget = Budget(max_steps)
    return compose(a, b, budget, context=context, order=order)


def reciprocal[D: NumericDomain](values: NumericArray[D], mut budget: Budget, *, context: D.Context) raises PolyError -> NumericArray[D]:
    """Compute the numerical formal reciprocal with explicit precision.

    Parameters:
        D: The numerical coefficient domain.

    Args:
        values: Coefficients, terms, or a prepared value.
        budget: The shared work allowance.
        context: Explicit output precision and rounding or enclosure settings.

    Returns:
        Numerical formal coefficients with a retained unknown-tail order; balls enclose coefficients only.

    Raises:
        PolyError: DOMAIN for invalid input, or LIMIT/CAPACITY on resource limits.
    """
    var result = values._core[].inverse(context, budget)
    return _numeric_wrap(result^, context, budget)


def reciprocal[D: NumericDomain](values: NumericArray[D], *, context: D.Context, max_steps: UInt64 = UInt64.MAX) raises PolyError -> NumericArray[D]:
    """Compute the numerical formal reciprocal with explicit precision.

    Parameters:
        D: The numerical coefficient domain.

    Args:
        values: Coefficients, terms, or a prepared value.
        context: Explicit output precision and rounding or enclosure settings.
        max_steps: The complete call's work allowance.

    Returns:
        Numerical formal coefficients with a retained unknown-tail order; balls enclose coefficients only.

    Raises:
        PolyError: DOMAIN for invalid input, or LIMIT/CAPACITY on resource limits.
    """
    var budget = Budget(max_steps)
    return reciprocal(values, budget, context=context)


def derivative[D: NumericDomain](values: NumericArray[D], mut budget: Budget, *, context: D.Context) raises PolyError -> NumericArray[D]:
    """Compute the numerical formal derivative with explicit precision.

    Parameters:
        D: The numerical coefficient domain.

    Args:
        values: Coefficients, terms, or a prepared value.
        budget: The shared work allowance.
        context: Explicit output precision and rounding or enclosure settings.

    Returns:
        Numerical formal coefficients with a retained unknown-tail order; balls enclose coefficients only.

    Raises:
        PolyError: DOMAIN for invalid input, or LIMIT/CAPACITY on resource limits.
    """
    var result = values._core[].derivative(context, budget)
    return _numeric_wrap(result^, context, budget)


def derivative[D: NumericDomain](values: NumericArray[D], *, context: D.Context, max_steps: UInt64 = UInt64.MAX) raises PolyError -> NumericArray[D]:
    """Compute the numerical formal derivative with explicit precision.

    Parameters:
        D: The numerical coefficient domain.

    Args:
        values: Coefficients, terms, or a prepared value.
        context: Explicit output precision and rounding or enclosure settings.
        max_steps: The complete call's work allowance.

    Returns:
        Numerical formal coefficients with a retained unknown-tail order; balls enclose coefficients only.

    Raises:
        PolyError: DOMAIN for invalid input, or LIMIT/CAPACITY on resource limits.
    """
    var budget = Budget(max_steps)
    return derivative(values, budget, context=context)


def integral[D: NumericDomain](values: NumericArray[D], mut budget: Budget, *, context: D.Context) raises PolyError -> NumericArray[D]:
    """Compute the numerical formal integral with explicit precision.

    Parameters:
        D: The numerical coefficient domain.

    Args:
        values: Coefficients, terms, or a prepared value.
        budget: The shared work allowance.
        context: Explicit output precision and rounding or enclosure settings.

    Returns:
        Numerical formal coefficients with a retained unknown-tail order; balls enclose coefficients only.

    Raises:
        PolyError: DOMAIN for invalid input, or LIMIT/CAPACITY on resource limits.
    """
    var result = values._core[].integrate(context, budget)
    return _numeric_wrap(result^, context, budget)


def integral[D: NumericDomain](values: NumericArray[D], *, context: D.Context, max_steps: UInt64 = UInt64.MAX) raises PolyError -> NumericArray[D]:
    """Compute the numerical formal integral with explicit precision.

    Parameters:
        D: The numerical coefficient domain.

    Args:
        values: Coefficients, terms, or a prepared value.
        context: Explicit output precision and rounding or enclosure settings.
        max_steps: The complete call's work allowance.

    Returns:
        Numerical formal coefficients with a retained unknown-tail order; balls enclose coefficients only.

    Raises:
        PolyError: DOMAIN for invalid input, or LIMIT/CAPACITY on resource limits.
    """
    var budget = Budget(max_steps)
    return integral(values, budget, context=context)


def log[D: NumericDomain](values: NumericArray[D], mut budget: Budget, *, context: D.Context) raises PolyError -> NumericArray[D]:
    """Compute the formal logarithm at the requested precision.

    Parameters:
        D: The numerical coefficient domain.

    Args:
        values: Coefficients, terms, or a prepared value.
        budget: The shared work allowance.
        context: Explicit output precision and rounding or enclosure settings.

    Returns:
        Numerical formal coefficients with a retained unknown-tail order; balls enclose coefficients only.

    Raises:
        PolyError: DOMAIN for invalid input, or LIMIT/CAPACITY on resource limits.
    """
    var result = values._core[].log(context, budget)
    return _numeric_wrap(result^, context, budget)


def log[D: NumericDomain](values: NumericArray[D], *, context: D.Context, max_steps: UInt64 = UInt64.MAX) raises PolyError -> NumericArray[D]:
    """Compute the formal logarithm at the requested precision.

    Parameters:
        D: The numerical coefficient domain.

    Args:
        values: Coefficients, terms, or a prepared value.
        context: Explicit output precision and rounding or enclosure settings.
        max_steps: The complete call's work allowance.

    Returns:
        Numerical formal coefficients with a retained unknown-tail order; balls enclose coefficients only.

    Raises:
        PolyError: DOMAIN for invalid input, or LIMIT/CAPACITY on resource limits.
    """
    var budget = Budget(max_steps)
    return log(values, budget, context=context)


def exp[D: NumericDomain](values: NumericArray[D], mut budget: Budget, *, context: D.Context) raises PolyError -> NumericArray[D]:
    """Compute the formal exponential at the requested precision.

    Parameters:
        D: The numerical coefficient domain.

    Args:
        values: Coefficients, terms, or a prepared value.
        budget: The shared work allowance.
        context: Explicit output precision and rounding or enclosure settings.

    Returns:
        Numerical formal coefficients with a retained unknown-tail order; balls enclose coefficients only.

    Raises:
        PolyError: DOMAIN for invalid input, or LIMIT/CAPACITY on resource limits.
    """
    var result = values._core[].exp(context, budget)
    return _numeric_wrap(result^, context, budget)


def exp[D: NumericDomain](values: NumericArray[D], *, context: D.Context, max_steps: UInt64 = UInt64.MAX) raises PolyError -> NumericArray[D]:
    """Compute the formal exponential at the requested precision.

    Parameters:
        D: The numerical coefficient domain.

    Args:
        values: Coefficients, terms, or a prepared value.
        context: Explicit output precision and rounding or enclosure settings.
        max_steps: The complete call's work allowance.

    Returns:
        Numerical formal coefficients with a retained unknown-tail order; balls enclose coefficients only.

    Raises:
        PolyError: DOMAIN for invalid input, or LIMIT/CAPACITY on resource limits.
    """
    var budget = Budget(max_steps)
    return exp(values, budget, context=context)


def revert[D: NumericDomain](values: NumericArray[D], mut budget: Budget, *, context: D.Context) raises PolyError -> NumericArray[D]:
    """Compute the inverse under formal composition at the requested precision.

    Parameters:
        D: The numerical coefficient domain.

    Args:
        values: Coefficients, terms, or a prepared value.
        budget: The shared work allowance.
        context: Explicit output precision and rounding or enclosure settings.

    Returns:
        Numerical formal coefficients with a retained unknown-tail order; balls enclose coefficients only.

    Raises:
        PolyError: DOMAIN for invalid input, or LIMIT/CAPACITY on resource limits.
    """
    var result = values._core[].revert(context, budget)
    return _numeric_wrap(result^, context, budget)


def revert[D: NumericDomain](values: NumericArray[D], *, context: D.Context, max_steps: UInt64 = UInt64.MAX) raises PolyError -> NumericArray[D]:
    """Compute the inverse under formal composition at the requested precision.

    Parameters:
        D: The numerical coefficient domain.

    Args:
        values: Coefficients, terms, or a prepared value.
        context: Explicit output precision and rounding or enclosure settings.
        max_steps: The complete call's work allowance.

    Returns:
        Numerical formal coefficients with a retained unknown-tail order; balls enclose coefficients only.

    Raises:
        PolyError: DOMAIN for invalid input, or LIMIT/CAPACITY on resource limits.
    """
    var budget = Budget(max_steps)
    return revert(values, budget, context=context)


def negative[D: NumericDomain](values: NumericArray[D], mut budget: Budget, *, context: D.Context) raises PolyError -> NumericArray[D]:
    """Negate every known numerical coefficient.

    Parameters:
        D: The numerical coefficient domain.

    Args:
        values: Coefficients, terms, or a prepared value.
        budget: The shared work allowance.
        context: Explicit output precision and rounding or enclosure settings.

    Returns:
        Numerical formal coefficients with a retained unknown-tail order; balls enclose coefficients only.

    Raises:
        PolyError: DOMAIN for invalid input, or LIMIT/CAPACITY on resource limits.
    """
    var polynomial = dense.NumericArray[D](_num._copy_dense(values._core[].polynomial, budget), budget)
    var result = dense.negative(polynomial, budget, context=context)
    return _numeric_wrap(NumericSeries[D](_num._copy_dense(result._core[], budget), values.order()), context, budget)


def negative[D: NumericDomain](values: NumericArray[D], *, context: D.Context, max_steps: UInt64 = UInt64.MAX) raises PolyError -> NumericArray[D]:
    """Negate every known numerical coefficient.

    Parameters:
        D: The numerical coefficient domain.

    Args:
        values: Coefficients, terms, or a prepared value.
        context: Explicit output precision and rounding or enclosure settings.
        max_steps: The complete call's work allowance.

    Returns:
        Numerical formal coefficients with a retained unknown-tail order; balls enclose coefficients only.

    Raises:
        PolyError: DOMAIN for invalid input, or LIMIT/CAPACITY on resource limits.
    """
    var budget = Budget(max_steps)
    return negative(values, budget, context=context)


def truncate[D: NumericDomain](values: NumericArray[D], order: Int, mut budget: Budget, *, context: D.Context) raises PolyError -> NumericArray[D]:
    """Lower the formal order without inventing unknown coefficients.

    Parameters:
        D: The numerical coefficient domain.

    Args:
        values: Coefficients, terms, or a prepared value.
        order: The number of retained coefficients.
        budget: The shared work allowance.
        context: Explicit output precision and rounding or enclosure settings.

    Returns:
        Numerical formal coefficients with a retained unknown-tail order; balls enclose coefficients only.

    Raises:
        PolyError: DOMAIN for invalid input, or LIMIT/CAPACITY on resource limits.
    """
    var result = values._core[].truncate(order, context, budget)
    return _numeric_wrap(result^, context, budget)


def truncate[D: NumericDomain](values: NumericArray[D], order: Int, *, context: D.Context, max_steps: UInt64 = UInt64.MAX) raises PolyError -> NumericArray[D]:
    """Lower the formal order without inventing unknown coefficients.

    Parameters:
        D: The numerical coefficient domain.

    Args:
        values: Coefficients, terms, or a prepared value.
        order: The number of retained coefficients.
        context: Explicit output precision and rounding or enclosure settings.
        max_steps: The complete call's work allowance.

    Returns:
        Numerical formal coefficients with a retained unknown-tail order; balls enclose coefficients only.

    Raises:
        PolyError: DOMAIN for invalid input, or LIMIT/CAPACITY on resource limits.
    """
    var budget = Budget(max_steps)
    return truncate(values, order, budget, context=context)


def to_polynomial[D: NumericDomain](values: NumericArray[D], mut budget: Budget) raises PolyError -> dense.NumericArray[D]:
    """Copy the known numerical polynomial, dropping the unknown-tail metadata.

    Parameters:
        D: The numerical coefficient domain.

    Args:
        values: Coefficients, terms, or a prepared value.
        budget: The shared work allowance.

    Returns:
        An independent dense array of numerical monomial coefficients.

    Raises:
        PolyError: DOMAIN for invalid input, or LIMIT/CAPACITY on resource limits.
    """
    return dense.NumericArray[D](_num._copy_dense(values._core[].polynomial, budget), budget)


def to_polynomial[D: NumericDomain](values: NumericArray[D], *, max_steps: UInt64 = UInt64.MAX) raises PolyError -> dense.NumericArray[D]:
    """Copy the known numerical polynomial, dropping the unknown-tail metadata.

    Parameters:
        D: The numerical coefficient domain.

    Args:
        values: Coefficients, terms, or a prepared value.
        max_steps: The complete call's work allowance.

    Returns:
        An independent dense array of numerical monomial coefficients.

    Raises:
        PolyError: DOMAIN for invalid input, or LIMIT/CAPACITY on resource limits.
    """
    var budget = Budget(max_steps)
    return to_polynomial(values, budget)


def coefficients[D: NumericDomain](values: NumericArray[D], mut budget: Budget) raises PolyError -> _num.Values[D]:
    """Materialize all known coefficients, including implicit zeros.

    Parameters:
        D: The numerical coefficient domain.

    Args:
        values: Coefficients, terms, or a prepared value.
        budget: The shared work allowance.

    Returns:
        A numerical sequence retaining every entry, including zeros.

    Raises:
        PolyError: DOMAIN for invalid input, or LIMIT/CAPACITY on resource limits.
    """
    _allocation[D.Scalar](len(values), budget)
    var result = List[D.Scalar](capacity=len(values))
    for i in range(len(values)):
        var c = values[i]
        _ = _num._bounds(c, budget)
        result.append(c^)
    return _num.Values[D](result^, budget)


def coefficients[D: NumericDomain](values: NumericArray[D], *, max_steps: UInt64 = UInt64.MAX) raises PolyError -> _num.Values[D]:
    """Materialize all known coefficients, including implicit zeros.

    Parameters:
        D: The numerical coefficient domain.

    Args:
        values: Coefficients, terms, or a prepared value.
        max_steps: The complete call's work allowance.

    Returns:
        A numerical sequence retaining every entry, including zeros.

    Raises:
        PolyError: DOMAIN for invalid input, or LIMIT/CAPACITY on resource limits.
    """
    var budget = Budget(max_steps)
    return coefficients(values, budget)


def to_core[D: NumericDomain](values: NumericArray[D], mut budget: Budget, *, variable: Int64 = 0) raises PolyError -> NumericSeries[D]:
    """Copy numerical series into independent mutable core storage.

    Parameters:
        D: The numerical coefficient domain.

    Args:
        values: Coefficients, terms, or a prepared value.
        budget: The shared work allowance.
        variable: The core variable ID assigned to the exported value.

    Returns:
        An independent mutable core representation, including its metadata.

    Raises:
        PolyError: DOMAIN for invalid input, or LIMIT/CAPACITY on resource limits.
    """
    return NumericSeries[D](_ni._dense(values._core[].polynomial, variable, budget), values.order())


def to_core[D: NumericDomain](values: NumericArray[D], *, max_steps: UInt64 = UInt64.MAX, variable: Int64 = 0) raises PolyError -> NumericSeries[D]:
    """Copy numerical series into independent mutable core storage.

    Parameters:
        D: The numerical coefficient domain.

    Args:
        values: Coefficients, terms, or a prepared value.
        max_steps: The complete call's work allowance.
        variable: The core variable ID assigned to the exported value.

    Returns:
        An independent mutable core representation, including its metadata.

    Raises:
        PolyError: DOMAIN for invalid input, or LIMIT/CAPACITY on resource limits.
    """
    var budget = Budget(max_steps)
    return to_core(values, budget, variable=variable)


def from_core[D: NumericDomain](values: NumericSeries[D], mut budget: Budget, *, context: D.Context) raises PolyError -> NumericArray[D]:
    """Validate and copy a numerical core series.

    Parameters:
        D: The numerical coefficient domain.

    Args:
        values: Coefficients, terms, or a prepared value.
        budget: The shared work allowance.
        context: Explicit output precision and rounding or enclosure settings.

    Returns:
        Numerical formal coefficients with a retained unknown-tail order; balls enclose coefficients only.

    Raises:
        PolyError: DOMAIN for invalid input, or LIMIT/CAPACITY on resource limits.
    """
    if values.order < 0 or values.order < len(values.polynomial.coefficients):
        raise PolyError(PolyErrorKind.DOMAIN, "invalid numerical series metadata")
    var validated = dense.from_core(values.polynomial, budget)
    var result = NumericSeries[D](dense.to_core[D](validated, budget), values.order)
    return _numeric_wrap(result^, context, budget)


def from_core[D: NumericDomain](values: NumericSeries[D], *, context: D.Context, max_steps: UInt64 = UInt64.MAX) raises PolyError -> NumericArray[D]:
    """Validate and copy a numerical core series.

    Parameters:
        D: The numerical coefficient domain.

    Args:
        values: Coefficients, terms, or a prepared value.
        context: Explicit output precision and rounding or enclosure settings.
        max_steps: The complete call's work allowance.

    Returns:
        Numerical formal coefficients with a retained unknown-tail order; balls enclose coefficients only.

    Raises:
        PolyError: DOMAIN for invalid input, or LIMIT/CAPACITY on resource limits.
    """
    var budget = Budget(max_steps)
    return from_core(values, budget, context=context)

from . import _numeric_interop as _ni
