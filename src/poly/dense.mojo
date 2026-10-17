"""Ascending polynomial coefficients with exact or explicitly numerical arithmetic."""
from ._io_meta import _Record, _Dense
from polynomials import NumericDensePoly
from std.iter import Iterable, IterableOwned, Iterator, iter, next, StopIteration
from std.builtin.rebind import downcast
from std.memory import ArcPointer
from polynomials import CoefficientBuffer
from polynomials import compose_dense, integrate_dense, CoefficientField, PolyErrorKind, DensePoly, Budget, evaluate_dense, derivative_dense, PolyError, ModInt, Modulus, NoContext
from polynomials import divmod as _divmod
from ._common import _allocation, _charge_size, _take_coefficient, _DirectInput, _input_view, _move_coefficient, _integer, _Native, _product, _sum
from ._common import Values, _FieldKind, _Join, _Element, _OwnedElement, _Kind, _Scalar, _Ring, _convert, _wrap, _unwrap, _Context, _initial_modulus, _merge_modulus, _WithModulus, _domain, _grow, _check_batch, _compact
from polynomials import CoefficientRing
from ._common import _CoreKind
from ._interop import _dense_copy
from polynomials import SparsePoly, gcd as _gcd, gcd_value as _gcd_value, content as _content, primitive_part as _primitive_part, extended_gcd as _extended_gcd, resultant as _resultant, subresultants as _subresultants, divide_exact as _divide_exact, pseudo_divmod as _pseudo_divmod
from ._interop import _dense_sparse, _take_dense
from polynomials import interpolate as _interpolate, hermite_interpolate as _hermite_interpolate, MultipointPlan, affine_transform as _affine_transform, taylor_shift as _taylor_shift, jet_evaluate as _jet_evaluate, definite_integral as _definite_integral
from ._common import _sequence, _sequence_coefficients, _values_from_core, _data_context, _Nested, _rows
from polynomials import QQi, factor_gaussian as _factor_gaussian, factor_finite_field as _factor_finite_field
from polynomials import ZZ, QQ, Factorization, factor_integer as _factor_integer, factor as _factor, squarefree as _squarefree
from polynomials import divide_by_list as _divide_by_list


comptime _BLOCK = CoefficientBuffer[ZZ]._block_size
comptime _FIRST = CoefficientBuffer[ZZ]._initial_size
comptime _SECOND = CoefficientBuffer[ZZ]._second_size


struct Array[k: Int](Copyable, Movable, Iterable, Sized, _WithModulus, _Record):
    """An immutable polynomial; copies share its canonical coefficient buffer.

    Parameters:
        k: The inferred coefficient kind: 0 for ZZ, 1 for QQ, 2 for QQi, 3 for a prime field, 4 for AA, or 5 for QQbar.
    """
    comptime _Format = _Dense
    comptime _Item = _Scalar[Self.k]
    comptime _Power = Int
    var _core: ArcPointer[DensePoly[_Ring[Self.k]]]
    comptime IteratorType[iterable_mut: Bool, //, iterable_origin: Origin[mut=iterable_mut]]: Iterator = _ArrayIterator[Self.k, ImmOrigin(iterable_origin)]
    """A borrowing iterator over the shared storage.

    Parameters:
        iterable_mut: Whether the borrowing origin is mutable.
        iterable_origin: The lifetime of the borrowed array.
    """

    def __init__(out self, var core: DensePoly[_Ring[Self.k]], mut budget: Budget) raises PolyError:
        """Take ownership of canonical storage; use asarray for coefficient inputs.

        Args:
            core: An owned canonical core polynomial in the array's variable layout and domain.
            budget: The caller-owned work allowance, shared through preparation and computation.

        Raises:
            PolyError: LIMIT on exhausted work, CAPACITY on unrepresentable sizes, or DOMAIN for incompatible input.
        """
        core.coefficients._compact(budget)
        _allocation[DensePoly[_Ring[Self.k]]](1, budget)
        self._core = ArcPointer(core^)

    def __iter__(ref self) -> Self.IteratorType[origin_of(self)]:
        """Iterate over values without copying the backing buffer.

        Returns:
            An iterator borrowing the shared storage.
        """
        return _ArrayIterator[Self.k, ImmOrigin(origin_of(self))](Pointer(to=self).as_imm(), 0)

    def __len__(self) -> Int:
        """Return the number of stored values.

        Returns:
            The number of stored entries.
        """
        return len(self._core[].coefficients)

    def __getitem__(self, index: Int) -> _Scalar[Self.k]:
        """Return the entry at a valid zero-based index.

        Args:
            index: A valid zero-based index into stored entries.

        Returns:
            The scalar or sparse term at the requested index.
        """
        return _unwrap[Self.k](self._core[].coefficients[index])

    def to_list(self, mut budget: Budget) raises PolyError -> List[_Scalar[Self.k]]:
        """Return an independent mutable list, charging allocation and coefficient work.

        Args:
            budget: The caller-owned work allowance, shared through preparation and computation.

        Returns:
            An independent mutable list in the current entry order.

        Raises:
            PolyError: LIMIT on exhausted work, CAPACITY on unrepresentable sizes, or DOMAIN for incompatible input.
        """
        _allocation[_Scalar[Self.k]](len(self), budget)
        var result = List[_Scalar[Self.k]](capacity=len(self))
        for index in range(len(self)):
            _charge_size(self._core[].coefficients[index].size(), budget)
            result.append(self[index])
        return result^

    def to_list(self, *, max_steps: UInt64 = UInt64.MAX) raises PolyError -> List[_Scalar[Self.k]]:
        """Return an independent mutable list, charging allocation and coefficient work.

        Args:
            max_steps: The complete call's work allowance; defaults to UInt64.MAX.

        Returns:
            An independent mutable list in the current entry order.

        Raises:
            PolyError: LIMIT on exhausted work, CAPACITY on unrepresentable sizes, or DOMAIN for incompatible input.
        """
        var budget = Budget(max_steps)
        return self.to_list(budget)

    def modulus(self) -> UInt64:
        """Return the retained prime modulus, or zero outside a prime field.

        Returns:
            The prime modulus for modular data, or zero otherwise.
        """
        comptime if Self.k == 3:
            return rebind[Modulus](self._core[].ring).value
        return 0

    def domain(self) -> String:
        """Return ZZ, QQ, QQi, GF(p), AA, or QQbar, including for an empty result.

        Returns:
            ZZ, QQ, QQi, GF(p), AA, or QQbar, including for an empty result.
        """
        return _domain[Self.k](self.modulus())


@fieldwise_init
struct _ArrayIterator[k: Int, origin: ImmOrigin](Iterator):
    comptime Element = _Scalar[Self.k]
    var source: Pointer[Array[Self.k], Self.origin]
    var position: Int

    def __next__(mut self) raises StopIteration -> Self.Element:
        if self.position == len(self.source[]):
            raise StopIteration()
        var result = self.source[][self.position]
        self.position += 1
        return result^

    def bounds(self) -> Tuple[Int, Optional[Int]]:
        var remaining = len(self.source[]) - self.position
        return remaining, Optional(remaining)


def _finish_coefficients[k: Int](var values: List[_Ring[k]], ctx: _Ring[k].Context, mut budget: Budget) raises PolyError -> Array[k]:
    # Only conversion and same-ring arithmetic call this helper. They already
    # establish every coefficient's domain, so a second validation pass would
    # copy handles merely to rediscover that fact. Trim the output as the core
    # arithmetic does, then transfer its canonical storage.
    while len(values):
        budget.charge(1)
        if not values[len(values) - 1].is_zero():
            break
        _ = values.pop()
    var core = DensePoly[_Ring[k]](0, ctx.copy())
    core.coefficients = values^
    return Array[k](core^, budget)


def _finish_coefficients[k: Int](var values: CoefficientBuffer[_Ring[k]], ctx: _Ring[k].Context, mut budget: Budget) raises PolyError -> Array[k]:
    # Only conversion and same-ring arithmetic call this helper. They already
    # establish every coefficient's domain, so a second validation pass would
    # copy handles merely to rediscover that fact. Trim the output as the core
    # arithmetic does, then transfer its canonical storage.
    while len(values):
        budget.charge(1)
        if not values[len(values) - 1].is_zero():
            break
        _ = values.pop()
    var core = DensePoly[_Ring[k]](0, ctx.copy())
    core.coefficients = values^
    return Array[k](core^, budget)


@no_inline
def _grow_coefficients[T: Copyable & Deinitable](mut values: List[T], mut budget: Budget) raises PolyError:
    # Keep overflow checks, allocation charges and their error construction out
    # of the ingestion loop. This is called only when an actual value needs room.
    _grow(values, budget)


@no_inline
def _next_chunk[T: Copyable & Deinitable](mut current: List[T], mut chunks: List[List[T]], mut completed: Int, mut budget: Budget) raises PolyError:
    var limit = _FIRST if not len(chunks) else _SECOND if len(chunks) == 1 else _BLOCK
    if len(current) == limit:
        var total = _sum(completed, limit)
        _grow(chunks, budget)
        var capacity = _SECOND if not len(chunks) else _BLOCK
        _allocation[T](capacity, budget)
        chunks.append(current^)
        current = List[T](capacity=capacity)
        completed = total
    else:
        _grow_coefficients(current, budget)


def _finish_chunks[k: Int](var current: List[_Ring[k]], var chunks: List[List[_Ring[k]]], completed: Int, ctx: _Ring[k].Context, mut budget: Budget) raises PolyError -> Array[k]:
    if not len(chunks):
        return _finish_coefficients[k](current^, ctx, budget)
    var total = _sum(completed, len(current))
    if len(current):
        _grow(chunks, budget)
        chunks.append(current^)
    return _finish_coefficients[k](CoefficientBuffer[_Ring[k]]._from_chunks(chunks^, total), ctx, budget)


@no_inline
def _fill_scalars[k: Int, It: Iterator](mut cursor: It, mut result: List[_Ring[k]], mut budget: Budget, count: Int) -> Bool:
    # No allocation or fallible conversion occurs here. Each successful next
    # initializes exactly one spare slot; publish the initialized prefix before
    # returning, including early EOF. The caller proved count fits both bounds.
    comptime T = downcast[It.Element, Copyable & Deinitable]
    comptime native = _Native[T] and k == 0
    comptime cost = 8 if native else 1
    var begin = len(result)
    var filled = 0
    var remaining = budget.remaining()
    while filled < count:
        remaining -= 1
        var raw: It.Element
        try:
            raw = next(cursor)
        except StopIteration:
            result.resize(unsafe_uninit_length=begin + filled)
            budget = Budget(remaining)
            return True
        var value = rebind_var[T](raw^)
        remaining -= UInt64(cost)
        comptime if native:
            result.unsafe_ptr().unsafe_offset(begin + filled).unsafe_write(rebind_var[_Ring[k]](_move_coefficient[0](_integer(value))))
        else:
            result.unsafe_ptr().unsafe_offset(begin + filled).unsafe_write(_move_coefficient[k](rebind_var[_Scalar[k]](value^)))
        filled += 1
    result.resize(unsafe_uninit_length=begin + filled)
    budget = Budget(remaining)
    return False


def _collect_scalars[k: Int, It: Iterator](var cursor: It, ctx: _Ring[k].Context, mut budget: Budget, capacity: Int) raises PolyError -> Array[k]:
    comptime T = downcast[It.Element, Copyable & Deinitable]
    comptime native = _Native[T] and k == 0
    comptime cost = 8 if native else 1
    comptime assert (T == _Scalar[k] and k != 3) or native, "ingestion requires a constant-cost scalar transfer"
    _allocation[_Ring[k]](capacity, budget)
    var result = List[_Ring[k]](capacity=capacity)
    var chunks = List[List[_Ring[k]]]()
    var completed = 0
    while True:
        var count = Int(min(UInt64(result.capacity() - len(result)), budget.remaining() // UInt64(cost + 1)))
        if _fill_scalars[k](cursor, result, budget, count):
            break
        # Read before growth: EOF never allocates another coefficient block.
        budget.charge(1)
        var raw: It.Element
        try:
            raw = next(cursor)
        except StopIteration:
            break
        var value = rebind_var[T](raw^)
        if len(result) == result.capacity():
            _next_chunk(result, chunks, completed, budget)
        result.append(_take_coefficient[k](value^, ctx, budget))
    return _finish_chunks[k](result^, chunks^, completed, ctx, budget)


def _collect[k: Int, It: Iterator](var cursor: It, var context: _Context[k], mut budget: Budget, capacity: Int = 0) raises PolyError -> Array[k]:
    comptime T = downcast[It.Element, Copyable & Deinitable]
    comptime assert _Kind[T] >= 0, "exact coefficients must be integers, Rational, ExactComplex or ModInt; convert floats explicitly"
    comptime if (T == _Scalar[k] and k != 3) or (_Native[T] and k == 0):
        return _collect_scalars[k](cursor^, context.get(), budget, capacity)
    _allocation[_Ring[k]](capacity, budget)
    var result = List[_Ring[k]](capacity=capacity)
    var chunks = List[List[_Ring[k]]]()
    var completed = 0
    while True:
        budget.charge(1)
        var raw: It.Element
        try:
            raw = next(cursor)
        except StopIteration:
            break
        var value = rebind_var[T](raw^)
        comptime if T == ModInt:
            context.observe(rebind[ModInt](value).modulus, budget)
        var ctx = context.get()
        if len(result) == result.capacity():
            _next_chunk(result, chunks, completed, budget)
        result.append(_take_coefficient[k](value^, ctx, budget))
    return _finish_chunks[k](result^, chunks^, completed, context.get(), budget)



def _from_input[k: Int, T: Copyable & Deinitable, origin: ImmOrigin](values: Span[T, origin], mut budget: Budget) raises PolyError -> Array[k]:
    # A standard list or fixed array exposes its actual extent. Precharge all
    # constant-time handle transfers before borrowing any entry, as core bulk
    # operations do. Arbitrary iterators still use _collect's per-read charges.
    _allocation[_Ring[k]](len(values), budget)
    _charge_size(_product(len(values), 8 if _Native[T] else 1), budget)
    var result = List[_Ring[k]](capacity=len(values))
    for i in range(len(values)):
        comptime if T == _Scalar[k]:
            result.append(_move_coefficient[k](rebind[_Scalar[k]](values[i]).copy()))
        else:
            comptime assert k == 0 and _Native[T], "bulk construction needs same-domain scalars or native integers"
            result.append(rebind_var[_Ring[k]](_move_coefficient[0](_integer(values[i]))))
    return _finish_coefficients[k](result^, rebind_var[_Ring[k].Context](NoContext()), budget)

def _prepare[I: Iterable](values: I, mut budget: Budget) raises PolyError -> Array[_Kind[_Element[I]]]:
    comptime k = _Kind[_Element[I]]
    comptime if I == Array[k]:
        return rebind[Array[k]](values).copy()
    elif _DirectInput[I] and k >= 0 and k != 3:
        return _from_input[k](_input_view(values), budget)
    else:
        _check_batch(values)
        var context = _Context[k]()
        var modulus = _initial_modulus(values)
        if modulus:
            context.observe(modulus, budget)
        comptime if conforms_to(I, Sized):
            return _collect[k](iter(values), context^, budget, len(values))
        else:
            return _collect[k](iter(values), context^, budget)


def _promote[k: Int, source: Int](values: Array[source], ctx: _Ring[k].Context, mut budget: Budget) raises PolyError -> Array[k]:
    comptime if k == source:
        return rebind[Array[k]](values).copy()
    else:
        _allocation[_Ring[k]](len(values), budget)
        var result = List[_Ring[k]](capacity=len(values))
        for index in range(len(values)):
            budget.charge(1)
            _charge_size(values._core[].coefficients[index].size(), budget)
            result.append(_wrap[k](_convert[k](values[index], ctx, budget)))
        return Array[k](DensePoly[_Ring[k]].from_coefficients(0, ctx, result^, budget), budget)


def asarray[I: Iterable](values: I, mut budget: Budget) raises PolyError -> Array[_Kind[_Element[I]]]:
    """Normalize one pass over coefficients, or share an already prepared array.

    Parameters:
        I: The inferred input iterable type.

    Args:
        values: The coefficient sequence, sparse terms, or prepared array.
        budget: The caller-owned work allowance, shared through preparation and computation.

    Returns:
        An immutable canonical polynomial that retains its exact domain and modulus.

    Raises:
        PolyError: LIMIT on exhausted work, CAPACITY on unrepresentable sizes, or DOMAIN for incompatible input.
    """
    return _prepare(values, budget)


def asarray[I: Iterable](values: I, *, max_steps: UInt64 = UInt64.MAX) raises PolyError -> Array[_Kind[_Element[I]]]:
    """Normalize exact inputs with an optional work limit; prepared arrays share storage.

    Parameters:
        I: The inferred input iterable type.

    Args:
        values: The coefficient sequence, sparse terms, or prepared array.
        max_steps: The complete call's work allowance; defaults to UInt64.MAX.

    Returns:
        An immutable canonical polynomial that retains its exact domain and modulus.

    Raises:
        PolyError: LIMIT on exhausted work, CAPACITY on unrepresentable sizes, or DOMAIN for incompatible input.
    """
    var budget = Budget(max_steps)
    return asarray(values, budget)


def asarray[I: Iterable](values: I, mut budget: Budget, *, modulus: UInt64) raises PolyError -> Array[3]:
    """Choose a prime field for integer or modular coefficients.

    Parameters:
        I: The inferred input iterable type.

    Args:
        values: The coefficient sequence, sparse terms, or prepared array.
        budget: The caller-owned work allowance, shared through preparation and computation.
        modulus: The prime modulus; supported primes are below 2**62.

    Returns:
        An immutable canonical polynomial that retains its exact domain and modulus.

    Raises:
        PolyError: LIMIT on exhausted work, CAPACITY on unrepresentable sizes, or DOMAIN for incompatible input.
    """
    _ = _merge_modulus(_initial_modulus(values), modulus)
    comptime if I == Array[3]:
        # A prepared array already carries a validated field.
        if modulus == rebind[Array[3]](values).modulus():
            return rebind[Array[3]](values).copy()
    _check_batch(values)
    var context = _Context[3]()
    context.observe(modulus, budget)
    return _collect[3](iter(values), context^, budget)


def asarray[I: Iterable](values: I, *, modulus: UInt64, max_steps: UInt64 = UInt64.MAX) raises PolyError -> Array[3]:
    """Normalize exact inputs with an optional work limit; prepared arrays share storage.

    Parameters:
        I: The inferred input iterable type.

    Args:
        values: The coefficient sequence, sparse terms, or prepared array.
        modulus: The prime modulus; supported primes are below 2**62.
        max_steps: The complete call's work allowance; defaults to UInt64.MAX.

    Returns:
        An immutable canonical polynomial that retains its exact domain and modulus.

    Raises:
        PolyError: LIMIT on exhausted work, CAPACITY on unrepresentable sizes, or DOMAIN for incompatible input.
    """
    var budget = Budget(max_steps)
    return asarray(values, budget, modulus=modulus)


def _pair[k: Int, A: Iterable, B: Iterable](a: A, b: B, mut budget: Budget) raises PolyError -> Tuple[Array[k], Array[k]]:
    comptime ka = _Kind[_Element[A]]
    comptime kb = _Kind[_Element[B]]
    var left = _prepare(a, budget)
    var right = _prepare(b, budget)
    _ = _merge_modulus(left.modulus(), right.modulus())
    var ctx: _Ring[k].Context
    comptime if ka == 3:
        ctx = rebind_var[_Ring[k].Context](left._core[].ring.copy())
    elif kb == 3:
        ctx = rebind_var[_Ring[k].Context](right._core[].ring.copy())
    else:
        ctx = rebind_var[_Ring[k].Context](NoContext())
    var p = _promote[k](left, ctx, budget)
    var q = _promote[k](right, ctx, budget)
    return p^, q^


def _list_sum[k: Int, T: Copyable & Deinitable, U: Copyable & Deinitable, a_origin: ImmOrigin, b_origin: ImmOrigin](a: Span[T, a_origin], b: Span[U, b_origin], subtract: Bool, mut budget: Budget) raises PolyError -> Array[k]:
    # Borrow caller storage throughout; allocate only the result. The ring
    # operations below are the same operations used by DensePoly._add.
    var n = max(len(a), len(b))
    _allocation[_Ring[k]](n, budget)
    var result = List[_Ring[k]](capacity=n)
    var ctx = rebind_var[_Ring[k].Context](NoContext())
    for i in range(n):
        budget.charge(1)
        if i < len(a) and i < len(b):
            var left = _take_coefficient[k](a[i].copy(), ctx, budget)
            var right = _take_coefficient[k](b[i].copy(), ctx, budget)
            result.append(left.sub(right, budget) if subtract else left.add(right, budget))
        elif i < len(a):
            result.append(_take_coefficient[k](a[i].copy(), ctx, budget))
        else:
            var right = _take_coefficient[k](b[i].copy(), ctx, budget)
            result.append(right.neg(budget) if subtract else right^)
    return _finish_coefficients[k](result^, ctx, budget)


def add[A: Iterable, B: Iterable](a: A, b: B, mut budget: Budget) raises PolyError -> Array[_Join[_Kind[_Element[A]], _Kind[_Element[B]]]]:
    """Add polynomials, promoting their coefficients together.

    Parameters:
        A: The first inferred iterable type.
        B: The second inferred iterable type.

    Args:
        a: The first polynomial.
        b: The second polynomial.
        budget: The caller-owned work allowance, shared through preparation and computation.

    Returns:
        The canonical sum in the common exact domain.

    Raises:
        PolyError: LIMIT on exhausted work, CAPACITY on unrepresentable sizes, or DOMAIN for incompatible input.
    """
    comptime k = _Join[_Kind[_Element[A]], _Kind[_Element[B]]]
    comptime if _DirectInput[A] and _DirectInput[B] and 0 <= k and k < 3:
        return _list_sum[k](_input_view(a), _input_view(b), False, budget)
    else:
        var pair = _pair[k](a, b, budget)
        return Array[k](pair[0]._core[].add(pair[1]._core[], budget), budget)


def add[A: Iterable, B: Iterable](a: A, b: B, *, max_steps: UInt64 = UInt64.MAX) raises PolyError -> Array[_Join[_Kind[_Element[A]], _Kind[_Element[B]]]]:
    """Add polynomials with an optional work limit and exact coefficient promotion.

    Parameters:
        A: The first inferred iterable type.
        B: The second inferred iterable type.

    Args:
        a: The first polynomial.
        b: The second polynomial.
        max_steps: The complete call's work allowance; defaults to UInt64.MAX.

    Returns:
        The canonical sum in the common exact domain.

    Raises:
        PolyError: LIMIT on exhausted work, CAPACITY on unrepresentable sizes, or DOMAIN for incompatible input.
    """
    var budget = Budget(max_steps)
    return add(a, b, budget)


def multiply[A: Iterable, B: Iterable](a: A, b: B, mut budget: Budget) raises PolyError -> Array[_Join[_Kind[_Element[A]], _Kind[_Element[B]]]]:
    """Multiply polynomials, promoting their coefficients together.

    Parameters:
        A: The first inferred iterable type.
        B: The second inferred iterable type.

    Args:
        a: The first polynomial.
        b: The second polynomial.
        budget: The caller-owned work allowance, shared through preparation and computation.

    Returns:
        The canonical product in the common exact domain.

    Raises:
        PolyError: LIMIT on exhausted work, CAPACITY on unrepresentable sizes, or DOMAIN for incompatible input.
    """
    comptime k = _Join[_Kind[_Element[A]], _Kind[_Element[B]]]
    var pair = _pair[k](a, b, budget)
    return Array[k](pair[0]._core[].mul(pair[1]._core[], budget), budget)


def multiply[A: Iterable, B: Iterable](a: A, b: B, *, max_steps: UInt64 = UInt64.MAX) raises PolyError -> Array[_Join[_Kind[_Element[A]], _Kind[_Element[B]]]]:
    """Multiply polynomials with an optional work limit and exact coefficient promotion.

    Parameters:
        A: The first inferred iterable type.
        B: The second inferred iterable type.

    Args:
        a: The first polynomial.
        b: The second polynomial.
        max_steps: The complete call's work allowance; defaults to UInt64.MAX.

    Returns:
        The canonical product in the common exact domain.

    Raises:
        PolyError: LIMIT on exhausted work, CAPACITY on unrepresentable sizes, or DOMAIN for incompatible input.
    """
    var budget = Budget(max_steps)
    return multiply(a, b, budget)


def evaluate[I: Iterable, X: Copyable & Deinitable](values: I, x: X, mut budget: Budget) raises PolyError -> _Evaluation[I, X]:
    """Evaluate at an exact scalar, retaining a full proof for algebraic values.

    Parameters:
        I: The inferred input iterable type.
        X: The inferred point or point-sequence type.

    Args:
        values: The coefficient sequence, sparse terms, or prepared array.
        x: The exact evaluation point.
        budget: The caller-owned work allowance, shared through preparation and computation.

    Returns:
        The exact scalar after joint promotion, or an algebraic Real retaining evaluation evidence.

    Raises:
        PolyError: LIMIT on exhausted work, CAPACITY on unrepresentable sizes, or DOMAIN for incompatible input.
    """
    comptime if _Join[_Kind[_Element[I]], _Kind[X]] == 4:
        return rebind_var[_Evaluation[I, X]](_alg.evaluate(values, x, budget))
    else:
        comptime source = _Kind[_Element[I]]
        comptime k = _Join[source, _Kind[X]]
        var input = _prepare(values, budget)
        var ctx: _Ring[k].Context
        comptime if source == 3:
            ctx = rebind_var[_Ring[k].Context](input._core[].ring.copy())
        elif _Kind[X] == 3:
            ctx = rebind_var[_Ring[k].Context](Modulus(rebind[ModInt](x).modulus, budget))
        else:
            ctx = rebind_var[_Ring[k].Context](NoContext())
        var p = _promote[k](input, ctx, budget)
        var point = _wrap[k](_convert[k](x, ctx, budget))
        var result = evaluate_dense(p._core[], point, budget)
        _charge_size(result.size(), budget)
        return rebind_var[_Evaluation[I, X]](_unwrap[k](result))


def evaluate[I: Iterable, X: Copyable & Deinitable](values: I, x: X, *, max_steps: UInt64 = UInt64.MAX) raises PolyError -> _Evaluation[I, X]:
    """Evaluate at an exact point with an optional work limit.

    Parameters:
        I: The inferred input iterable type.
        X: The inferred point or point-sequence type.

    Args:
        values: The coefficient sequence, sparse terms, or prepared array.
        x: The exact evaluation point.
        max_steps: The complete call's work allowance; defaults to UInt64.MAX.

    Returns:
        The exact scalar after joint promotion, or an algebraic Real retaining evaluation evidence.

    Raises:
        PolyError: LIMIT on exhausted work, CAPACITY on unrepresentable sizes, or DOMAIN for incompatible input.
    """
    var budget = Budget(max_steps)
    return evaluate(values, x, budget)


def derivative[I: Iterable](values: I, mut budget: Budget) raises PolyError -> Array[_Kind[_Element[I]]]:
    """Differentiate while preserving the inferred domain.

    Parameters:
        I: The inferred input iterable type.

    Args:
        values: The coefficient sequence, sparse terms, or prepared array.
        budget: The caller-owned work allowance, shared through preparation and computation.

    Returns:
        The derivative, retaining the exact coefficient domain.

    Raises:
        PolyError: LIMIT on exhausted work, CAPACITY on unrepresentable sizes, or DOMAIN for incompatible input.
    """
    comptime k = _Kind[_Element[I]]
    var p = _prepare(values, budget)
    return Array[k](derivative_dense(p._core[], budget), budget)


def derivative[I: Iterable](values: I, *, max_steps: UInt64 = UInt64.MAX) raises PolyError -> Array[_Kind[_Element[I]]]:
    """Differentiate with an optional work limit, retaining the coefficient domain.

    Parameters:
        I: The inferred input iterable type.

    Args:
        values: The coefficient sequence, sparse terms, or prepared array.
        max_steps: The complete call's work allowance; defaults to UInt64.MAX.

    Returns:
        The derivative, retaining the exact coefficient domain.

    Raises:
        PolyError: LIMIT on exhausted work, CAPACITY on unrepresentable sizes, or DOMAIN for incompatible input.
    """
    var budget = Budget(max_steps)
    return derivative(values, budget)


def asarray[I: IterableOwned & Deinitable](var values: I, mut budget: Budget) raises PolyError -> Array[_Kind[_OwnedElement[I]]]:
    """Consume an owning iterator directly into the core coefficient buffer.

    Parameters:
        I: The inferred input iterable type.

    Args:
        values: The coefficient sequence, sparse terms, or prepared array.
        budget: The caller-owned work allowance, shared through preparation and computation.

    Returns:
        An immutable canonical polynomial that retains its exact domain and modulus.

    Raises:
        PolyError: LIMIT on exhausted work, CAPACITY on unrepresentable sizes, or DOMAIN for incompatible input.
    """
    comptime k = _Kind[_OwnedElement[I]]
    _check_batch(values)
    return _collect[k](iter(values^), _Context[k](), budget)


def asarray[I: IterableOwned & Deinitable](var values: I, *, max_steps: UInt64 = UInt64.MAX) raises PolyError -> Array[_Kind[_OwnedElement[I]]]:
    """Normalize exact inputs with an optional work limit; prepared arrays share storage.

    Parameters:
        I: The inferred input iterable type.

    Args:
        values: The coefficient sequence, sparse terms, or prepared array.
        max_steps: The complete call's work allowance; defaults to UInt64.MAX.

    Returns:
        An immutable canonical polynomial that retains its exact domain and modulus.

    Raises:
        PolyError: LIMIT on exhausted work, CAPACITY on unrepresentable sizes, or DOMAIN for incompatible input.
    """
    var budget = Budget(max_steps)
    return asarray(values^, budget)


def asarray[I: IterableOwned & Deinitable](var values: I, mut budget: Budget, *, modulus: UInt64) raises PolyError -> Array[3]:
    """Normalize exact inputs with an optional work limit; prepared arrays share storage.

    Parameters:
        I: The inferred input iterable type.

    Args:
        values: The coefficient sequence, sparse terms, or prepared array.
        budget: The caller-owned work allowance, shared through preparation and computation.
        modulus: The prime modulus; supported primes are below 2**62.

    Returns:
        An immutable canonical polynomial that retains its exact domain and modulus.

    Raises:
        PolyError: LIMIT on exhausted work, CAPACITY on unrepresentable sizes, or DOMAIN for incompatible input.
    """
    _check_batch(values)
    var context = _Context[3]()
    context.observe(modulus, budget)
    return _collect[3](iter(values^), context^, budget)


def asarray[I: IterableOwned & Deinitable](var values: I, *, modulus: UInt64, max_steps: UInt64 = UInt64.MAX) raises PolyError -> Array[3]:
    """Normalize exact inputs with an optional work limit; prepared arrays share storage.

    Parameters:
        I: The inferred input iterable type.

    Args:
        values: The coefficient sequence, sparse terms, or prepared array.
        modulus: The prime modulus; supported primes are below 2**62.
        max_steps: The complete call's work allowance; defaults to UInt64.MAX.

    Returns:
        An immutable canonical polynomial that retains its exact domain and modulus.

    Raises:
        PolyError: LIMIT on exhausted work, CAPACITY on unrepresentable sizes, or DOMAIN for incompatible input.
    """
    var budget = Budget(max_steps)
    return asarray(values^, budget, modulus=modulus)


def subtract[A: Iterable, B: Iterable](a: A, b: B, mut budget: Budget) raises PolyError -> Array[_Join[_Kind[_Element[A]], _Kind[_Element[B]]]]:
    """Subtract polynomials, promoting their coefficients together.

    Parameters:
        A: The first inferred iterable type.
        B: The second inferred iterable type.

    Args:
        a: The first polynomial.
        b: The second polynomial.
        budget: The caller-owned work allowance, shared through preparation and computation.

    Returns:
        The canonical first polynomial minus the second.

    Raises:
        PolyError: LIMIT on exhausted work, CAPACITY on unrepresentable sizes, or DOMAIN for incompatible input.
    """
    comptime k = _Join[_Kind[_Element[A]], _Kind[_Element[B]]]
    comptime if _DirectInput[A] and _DirectInput[B] and 0 <= k and k < 3:
        return _list_sum[k](_input_view(a), _input_view(b), True, budget)
    else:
        var pair = _pair[k](a, b, budget)
        return Array[k](pair[0]._core[].sub(pair[1]._core[], budget), budget)


def subtract[A: Iterable, B: Iterable](a: A, b: B, *, max_steps: UInt64 = UInt64.MAX) raises PolyError -> Array[_Join[_Kind[_Element[A]], _Kind[_Element[B]]]]:
    """Subtract the second polynomial from the first with an optional work limit.

    Parameters:
        A: The first inferred iterable type.
        B: The second inferred iterable type.

    Args:
        a: The first polynomial.
        b: The second polynomial.
        max_steps: The complete call's work allowance; defaults to UInt64.MAX.

    Returns:
        The canonical first polynomial minus the second.

    Raises:
        PolyError: LIMIT on exhausted work, CAPACITY on unrepresentable sizes, or DOMAIN for incompatible input.
    """
    var budget = Budget(max_steps)
    return subtract(a, b, budget)




def negative[I: Iterable](values: I, mut budget: Budget) raises PolyError -> Array[_Kind[_Element[I]]]:
    """Negate every coefficient, preserving its exact domain.

    Parameters:
        I: The inferred input iterable type.

    Args:
        values: The coefficient sequence, sparse terms, or prepared array.
        budget: The caller-owned work allowance, shared through preparation and computation.

    Returns:
        The polynomial with every coefficient negated.

    Raises:
        PolyError: LIMIT on exhausted work, CAPACITY on unrepresentable sizes, or DOMAIN for incompatible input.
    """
    comptime k = _Kind[_Element[I]]
    var p = _prepare(values, budget)
    return Array[k](p._core[].neg(budget), budget)


def degree[I: Iterable](values: I, mut budget: Budget) raises PolyError -> Int:
    """Return the highest nonzero power, or -1 for the zero polynomial.

    Parameters:
        I: The inferred input iterable type.

    Args:
        values: The coefficient sequence, sparse terms, or prepared array.
        budget: The caller-owned work allowance, shared through preparation and computation.

    Returns:
        The degree, or -1 for the zero polynomial.

    Raises:
        PolyError: LIMIT on exhausted work, CAPACITY on unrepresentable sizes, or DOMAIN for incompatible input.
    """
    var p = _prepare(values, budget)
    return len(p) - 1


def power[I: Iterable](values: I, exponent: Int, mut budget: Budget) raises PolyError -> Array[_Kind[_Element[I]]]:
    """Raise a polynomial to a nonnegative power by repeated squaring.

    Zero to power zero returns the constant one. Negative exponents raise DOMAIN.

    Parameters:
        I: The inferred input iterable type.

    Args:
        values: The coefficient sequence, sparse terms, or prepared array.
        exponent: A nonnegative integer exponent; zero returns one, including for a zero input.
        budget: The caller-owned work allowance, shared through preparation and computation.

    Returns:
        The canonical power in the input domain.

    Raises:
        PolyError: LIMIT on exhausted work, CAPACITY on unrepresentable sizes, or DOMAIN for incompatible input.
    """
    if exponent < 0:
        raise PolyError(PolyErrorKind.DOMAIN, "polynomial exponent must be nonnegative")
    comptime k = _Kind[_Element[I]]
    var factor = _prepare(values, budget)
    _allocation[_Ring[k]](1, budget)
    var one: List[_Ring[k]] = [_Ring[k].one(factor._core[].ring)]
    var result = Array[k](DensePoly[_Ring[k]].from_coefficients(0, factor._core[].ring, one^, budget), budget)
    var remaining = exponent
    while remaining:
        budget.charge(1)
        if remaining & 1:
            result = Array[k](result._core[].mul(factor._core[], budget), budget)
        remaining >>= 1
        if remaining:
            factor = Array[k](factor._core[].mul(factor._core[], budget), budget)
    return result^


def integral[I: Iterable](values: I, mut budget: Budget) raises PolyError -> Array[_FieldKind[_Kind[_Element[I]]]]:
    """Return the antiderivative with zero constant, promoting integers to rationals.

    Other domains are retained. In a prime field, a nonzero coefficient that
    requires division by zero raises DOMAIN.

    Parameters:
        I: The inferred input iterable type.

    Args:
        values: The coefficient sequence, sparse terms, or prepared array.
        budget: The caller-owned work allowance, shared through preparation and computation.

    Returns:
        The zero-constant antiderivative; integer coefficients promote to QQ.

    Raises:
        PolyError: LIMIT on exhausted work, CAPACITY on unrepresentable sizes, or DOMAIN for incompatible input.
    """
    comptime k = _FieldKind[_Kind[_Element[I]]]
    var p = _prepare(values, budget)
    var ctx: _Ring[k].Context
    comptime if k == 3:
        ctx = rebind_var[_Ring[k].Context](p._core[].ring.copy())
    else:
        ctx = rebind_var[_Ring[k].Context](NoContext())
    var promoted = _promote[k](p, ctx, budget)
    return Array[k](integrate_dense(promoted._core[], budget), budget)


def compose[A: Iterable, B: Iterable](outer: A, inner: B, mut budget: Budget) raises PolyError -> Array[_Join[_Kind[_Element[A]], _Kind[_Element[B]]]]:
    """Substitute the inner polynomial for x in the outer polynomial.

    Parameters:
        A: The first inferred iterable type.
        B: The second inferred iterable type.

    Args:
        outer: The polynomial whose variable is replaced.
        inner: The replacement polynomial.
        budget: The caller-owned work allowance, shared through preparation and computation.

    Returns:
        The outer polynomial evaluated at the inner polynomial.

    Raises:
        PolyError: LIMIT on exhausted work, CAPACITY on unrepresentable sizes, or DOMAIN for incompatible input.
    """
    comptime k = _Join[_Kind[_Element[A]], _Kind[_Element[B]]]
    var pair = _pair[k](outer, inner, budget)
    return Array[k](compose_dense(pair[0]._core[], pair[1]._core[], budget), budget)


def divmod[A: Iterable, B: Iterable](a: A, b: B, mut budget: Budget) raises PolyError -> Tuple[Array[_FieldKind[_Join[_Kind[_Element[A]], _Kind[_Element[B]]]]], Array[_FieldKind[_Join[_Kind[_Element[A]], _Kind[_Element[B]]]]]]:
    """Return quotient and remainder, promoting integer inputs to QQ.

    The remainder has degree below the divisor. A zero divisor raises DOMAIN.

    Parameters:
        A: The first inferred iterable type.
        B: The second inferred iterable type.

    Args:
        a: The first polynomial.
        b: The second polynomial.
        budget: The caller-owned work allowance, shared through preparation and computation.

    Returns:
        A pair (quotient, remainder); integer coefficients promote to QQ.

    Raises:
        PolyError: LIMIT on exhausted work, CAPACITY on unrepresentable sizes, or DOMAIN for incompatible input.
    """
    comptime k = _FieldKind[_Join[_Kind[_Element[A]], _Kind[_Element[B]]]]
    comptime Field = downcast[_Ring[k], CoefficientField]
    var pair = _pair[k](a, b, budget)
    var result = _divmod(rebind[DensePoly[Field]](pair[0]._core[]), rebind[DensePoly[Field]](pair[1]._core[]), budget)
    var quotient = DensePoly[Field](0, result.quotient.ring.copy())
    var remainder = DensePoly[Field](0, result.remainder.ring.copy())
    swap(quotient, result.quotient)
    swap(remainder, result.remainder)
    return (Array[k](rebind_var[DensePoly[_Ring[k]]](quotient^), budget),
            Array[k](rebind_var[DensePoly[_Ring[k]]](remainder^), budget))


def evaluate_many[I: Iterable, X: Iterable](values: I, points: X, mut budget: Budget) raises PolyError -> Values[_Scalar[_Join[_Kind[_Element[I]], _Kind[_Element[X]]]], _Join[_Kind[_Element[I]], _Kind[_Element[X]]]]:
    """Evaluate at each point in a one-dimensional iterable, preserving order and zeros.

    The result is an immutable sequence of values. Coefficients and points
    promote together; the polynomial is prepared once for the whole call.

    Parameters:
        I: The inferred input iterable type.
        X: The inferred point or point-sequence type.

    Args:
        values: The coefficient sequence, sparse terms, or prepared array.
        points: A one-dimensional sequence of exact points, in output order.
        budget: The caller-owned work allowance, shared through preparation and computation.

    Returns:
        An immutable Values sequence, preserving every input point and returned zero.

    Raises:
        PolyError: LIMIT on exhausted work, CAPACITY on unrepresentable sizes, or DOMAIN for incompatible input.
    """
    comptime k = _Join[_Kind[_Element[I]], _Kind[_Element[X]]]
    _check_batch(points, message="evaluation points must form a one-dimensional sequence")
    var input = _prepare(values, budget)
    var context = _Context[k]()
    comptime if _Kind[_Element[I]] == 3:
        context._value = rebind_var[_Ring[k].Context](input._core[].ring.copy())
    var modulus = _merge_modulus(input.modulus(), _initial_modulus(points))
    if modulus:
        context.observe(modulus, budget)
    var prepared = Optional[Array[k]]()
    var output = List[_Scalar[k]]()
    var cursor = iter(points)
    comptime T = downcast[type_of(cursor).Element, Copyable & Deinitable]
    while True:
        budget.charge(1)
        var raw: type_of(cursor).Element
        try:
            raw = next(cursor)
        except StopIteration:
            break
        var point = rebind_var[T](raw^)
        comptime if T == ModInt:
            context.observe(rebind[ModInt](point).modulus, budget)
        var ctx = context.get()
        if not prepared:
            prepared = _promote[k](input, ctx, budget)
        var value = evaluate_dense(prepared.value()._core[], _wrap[k](_convert[k](point, ctx, budget)), budget)
        _charge_size(value.size(), budget)
        _grow(output, budget)
        output.append(_unwrap[k](value))
    var ctx = context.get()
    comptime if k == 3:
        modulus = rebind[Modulus](ctx).value
    return Values[_Scalar[k], k](output^, modulus, budget)


def negative[I: Iterable](values: I, *, max_steps: UInt64 = UInt64.MAX) raises PolyError -> Array[_Kind[_Element[I]]]:
    """Compute with an optional work limit; see the shared-budget overload.

    Parameters:
        I: The inferred input iterable type.

    Args:
        values: The coefficient sequence, sparse terms, or prepared array.
        max_steps: The complete call's work allowance; defaults to UInt64.MAX.

    Returns:
        The polynomial with every coefficient negated.

    Raises:
        PolyError: LIMIT on exhausted work, CAPACITY on unrepresentable sizes, or DOMAIN for incompatible input.
    """
    var budget = Budget(max_steps)
    return negative(values, budget)


def power[I: Iterable](values: I, exponent: Int, *, max_steps: UInt64 = UInt64.MAX) raises PolyError -> Array[_Kind[_Element[I]]]:
    """Compute with an optional work limit; see the shared-budget overload.

    Parameters:
        I: The inferred input iterable type.

    Args:
        values: The coefficient sequence, sparse terms, or prepared array.
        exponent: A nonnegative integer exponent; zero returns one, including for a zero input.
        max_steps: The complete call's work allowance; defaults to UInt64.MAX.

    Returns:
        The canonical power in the input domain.

    Raises:
        PolyError: LIMIT on exhausted work, CAPACITY on unrepresentable sizes, or DOMAIN for incompatible input.
    """
    var budget = Budget(max_steps)
    return power(values, exponent, budget)


def integral[I: Iterable](values: I, *, max_steps: UInt64 = UInt64.MAX) raises PolyError -> Array[_FieldKind[_Kind[_Element[I]]]]:
    """Compute with an optional work limit; see the shared-budget overload.

    Parameters:
        I: The inferred input iterable type.

    Args:
        values: The coefficient sequence, sparse terms, or prepared array.
        max_steps: The complete call's work allowance; defaults to UInt64.MAX.

    Returns:
        The zero-constant antiderivative; integer coefficients promote to QQ.

    Raises:
        PolyError: LIMIT on exhausted work, CAPACITY on unrepresentable sizes, or DOMAIN for incompatible input.
    """
    var budget = Budget(max_steps)
    return integral(values, budget)


def compose[A: Iterable, B: Iterable](outer: A, inner: B, *, max_steps: UInt64 = UInt64.MAX) raises PolyError -> Array[_Join[_Kind[_Element[A]], _Kind[_Element[B]]]]:
    """Compute with an optional work limit; see the shared-budget overload.

    Parameters:
        A: The first inferred iterable type.
        B: The second inferred iterable type.

    Args:
        outer: The polynomial whose variable is replaced.
        inner: The replacement polynomial.
        max_steps: The complete call's work allowance; defaults to UInt64.MAX.

    Returns:
        The outer polynomial evaluated at the inner polynomial.

    Raises:
        PolyError: LIMIT on exhausted work, CAPACITY on unrepresentable sizes, or DOMAIN for incompatible input.
    """
    var budget = Budget(max_steps)
    return compose(outer, inner, budget)


def divmod[A: Iterable, B: Iterable](a: A, b: B, *, max_steps: UInt64 = UInt64.MAX) raises PolyError -> Tuple[Array[_FieldKind[_Join[_Kind[_Element[A]], _Kind[_Element[B]]]]], Array[_FieldKind[_Join[_Kind[_Element[A]], _Kind[_Element[B]]]]]]:
    """Divide with an optional work limit; see the shared-budget overload.

    Parameters:
        A: The first inferred iterable type.
        B: The second inferred iterable type.

    Args:
        a: The first polynomial.
        b: The second polynomial.
        max_steps: The complete call's work allowance; defaults to UInt64.MAX.

    Returns:
        A pair (quotient, remainder); integer coefficients promote to QQ.

    Raises:
        PolyError: LIMIT on exhausted work, CAPACITY on unrepresentable sizes, or DOMAIN for incompatible input.
    """
    var budget = Budget(max_steps)
    return divmod(a, b, budget)


def degree[I: Iterable](values: I, *, max_steps: UInt64 = UInt64.MAX) raises PolyError -> Int:
    """Compute with an optional work limit; see the shared-budget overload.

    Parameters:
        I: The inferred input iterable type.

    Args:
        values: The coefficient sequence, sparse terms, or prepared array.
        max_steps: The complete call's work allowance; defaults to UInt64.MAX.

    Returns:
        The degree, or -1 for the zero polynomial.

    Raises:
        PolyError: LIMIT on exhausted work, CAPACITY on unrepresentable sizes, or DOMAIN for incompatible input.
    """
    var budget = Budget(max_steps)
    return degree(values, budget)


def evaluate_many[I: Iterable, X: Iterable](values: I, points: X, *, max_steps: UInt64 = UInt64.MAX) raises PolyError -> Values[_Scalar[_Join[_Kind[_Element[I]], _Kind[_Element[X]]]], _Join[_Kind[_Element[I]], _Kind[_Element[X]]]]:
    """Compute with an optional work limit; see the shared-budget overload.

    Parameters:
        I: The inferred input iterable type.
        X: The inferred point or point-sequence type.

    Args:
        values: The coefficient sequence, sparse terms, or prepared array.
        points: A one-dimensional sequence of exact points, in output order.
        max_steps: The complete call's work allowance; defaults to UInt64.MAX.

    Returns:
        An immutable Values sequence, preserving every input point and returned zero.

    Raises:
        PolyError: LIMIT on exhausted work, CAPACITY on unrepresentable sizes, or DOMAIN for incompatible input.
    """
    var budget = Budget(max_steps)
    return evaluate_many(values, points, budget)


def from_roots[I: Iterable](roots: I, mut budget: Budget) raises PolyError -> Array[_Kind[_Element[I]]]:
    """Build the monic product of (x - root), including repeated and zero roots.

    An empty typed sequence returns one in its domain. Empty modular input
    must retain field metadata, for example through a prepared empty modular array.

    Parameters:
        I: The inferred input iterable type.

    Args:
        roots: A finite iterable of exact roots; repeats and zeros are retained.
        budget: The caller-owned work allowance, shared through preparation and computation.

    Returns:
        The monic product of linear factors, or one for an empty input.

    Raises:
        PolyError: LIMIT on exhausted work, CAPACITY on unrepresentable sizes, or DOMAIN for incompatible input.
    """
    comptime k = _Kind[_Element[I]]
    _check_batch(roots, message="roots must form a one-dimensional sequence")
    var context = _Context[k]()
    var modulus = _initial_modulus(roots)
    if modulus:
        context.observe(modulus, budget)
    var result = Optional[Array[k]]()
    var cursor = iter(roots)
    comptime T = downcast[type_of(cursor).Element, Copyable & Deinitable]
    while True:
        budget.charge(1)
        var raw: type_of(cursor).Element
        try:
            raw = next(cursor)
        except StopIteration:
            break
        var root = rebind_var[T](raw^)
        comptime if T == ModInt:
            context.observe(rebind[ModInt](root).modulus, budget)
        var ctx = context.get()
        var coefficient = _wrap[k](_convert[k](root, ctx, budget))
        _allocation[_Ring[k]](2, budget)
        var entries: List[_Ring[k]] = [coefficient.neg(budget), _Ring[k].one(ctx)]
        var factor = Array[k](DensePoly[_Ring[k]].from_coefficients(0, ctx, entries^, budget), budget)
        if result:
            result = Array[k](result.value()._core[].mul(factor._core[], budget), budget)
        else:
            result = factor^
    if result:
        return result.take()
    var ctx = context.get()
    _allocation[_Ring[k]](1, budget)
    var one: List[_Ring[k]] = [_Ring[k].one(ctx)]
    return Array[k](DensePoly[_Ring[k]].from_coefficients(0, ctx, one^, budget), budget)


def from_roots[I: Iterable](roots: I, *, max_steps: UInt64 = UInt64.MAX) raises PolyError -> Array[_Kind[_Element[I]]]:
    """Build a monic polynomial from exact roots with an optional work limit.

    Parameters:
        I: The inferred input iterable type.

    Args:
        roots: A finite iterable of exact roots; repeats and zeros are retained.
        max_steps: The complete call's work allowance; defaults to UInt64.MAX.

    Returns:
        The monic product of linear factors, or one for an empty input.

    Raises:
        PolyError: LIMIT on exhausted work, CAPACITY on unrepresentable sizes, or DOMAIN for incompatible input.
    """
    var budget = Budget(max_steps)
    return from_roots(roots, budget)




def to_core[I: Iterable](values: I, mut budget: Budget, *, variable: Int64 = 0) raises PolyError -> DensePoly[_Ring[_Kind[_Element[I]]]] where _Kind[_Element[I]] >= 0:
    """Return an independent mutable core polynomial, optionally naming its variable.

    Changing the returned core storage cannot affect a prepared input.

    Parameters:
        I: The inferred input iterable type.

    Args:
        values: The coefficient sequence, sparse terms, or prepared array.
        budget: The caller-owned work allowance, shared through preparation and computation.
        variable: The core variable ID assigned to the dense array; defaults to zero.

    Returns:
        An independent mutable core polynomial with the requested variable IDs and the same exact domain.

    Raises:
        PolyError: LIMIT on exhausted work, CAPACITY on unrepresentable sizes, DOMAIN for invalid input, or UNSUPPORTED for a documented domain restriction.
    """
    var p = _prepare(values, budget)
    return _dense_copy(p._core[], variable, budget)


def from_core[C: CoefficientRing](values: DensePoly[C], mut budget: Budget) raises PolyError -> Array[_CoreKind[C]]:
    """Validate and copy a core polynomial into the array's single unnamed variable.

    Mutating either representation afterward leaves the other unchanged.

    Checks core invariants and modular residues, then copies storage. Mutating the core afterwards cannot affect the result. Dense import normalizes the sole variable to zero. Sparse import rejects used IDs absent from the map and normalizes term order to lexicographic.

    Parameters:
        C: The supported core ring: ZZ, QQ, QQi, or ModInt.

    Args:
        values: The mutable core DensePoly to validate and copy.
        budget: The caller-owned work allowance, shared through preparation and computation.

    Returns:
        An independent immutable array in the core coefficient domain, with normalized variable IDs.

    Raises:
        PolyError: LIMIT on exhausted work, CAPACITY on unrepresentable sizes, DOMAIN for invalid input, or UNSUPPORTED for a documented domain restriction.
    """
    comptime k = _CoreKind[C]
    return Array[k](rebind_var[DensePoly[_Ring[k]]](_dense_copy(values, 0, budget)), budget)


def to_core[I: Iterable](values: I, *, max_steps: UInt64 = UInt64.MAX, variable: Int64 = 0) raises PolyError -> DensePoly[_Ring[_Kind[_Element[I]]]] where _Kind[_Element[I]] >= 0:
    """Copy between array and core representations with an optional work limit.

    Changing the returned core storage cannot affect a prepared input.

    Parameters:
        I: The inferred input iterable type.

    Args:
        values: The coefficient sequence, sparse terms, or prepared array.
        max_steps: The complete call's work allowance; defaults to UInt64.MAX.
        variable: The core variable ID assigned to the dense array; defaults to zero.

    Returns:
        An independent mutable core polynomial with the requested variable IDs and the same exact domain.

    Raises:
        PolyError: LIMIT on exhausted work, CAPACITY on unrepresentable sizes, DOMAIN for invalid input, or UNSUPPORTED for a documented domain restriction.
    """
    var budget = Budget(max_steps)
    return to_core(values, budget, variable=variable)


def from_core[C: CoefficientRing](values: DensePoly[C], *, max_steps: UInt64 = UInt64.MAX) raises PolyError -> Array[_CoreKind[C]]:
    """Copy between array and core representations with an optional work limit.

    Checks core invariants and modular residues, then copies storage. Mutating the core afterwards cannot affect the result. Dense import normalizes the sole variable to zero. Sparse import rejects used IDs absent from the map and normalizes term order to lexicographic.

    Parameters:
        C: The supported core ring: ZZ, QQ, QQi, or ModInt.

    Args:
        values: The mutable core DensePoly to validate and copy.
        max_steps: The complete call's work allowance; defaults to UInt64.MAX.

    Returns:
        An independent immutable array in the core coefficient domain, with normalized variable IDs.

    Raises:
        PolyError: LIMIT on exhausted work, CAPACITY on unrepresentable sizes, DOMAIN for invalid input, or UNSUPPORTED for a documented domain restriction.
    """
    var budget = Budget(max_steps)
    return from_core(values, budget)



def _from_sparse[k: Int](p: SparsePoly[_Ring[k]], mut budget: Budget) raises PolyError -> Array[k]:
    return Array[k](DensePoly[_Ring[k]].from_sparse(p, budget, variable=Optional(Int64(0))), budget)


def content[I: Iterable](values: I, mut budget: Budget) raises PolyError -> _Scalar[_Kind[_Element[I]]]:
    """Return the normalized coefficient GCD.

    Integer content is nonnegative. Field content is monic; a nonzero univariate field polynomial has content one. Zero has content zero.

    Parameters:
        I: The inferred input iterable type.

    Args:
        values: The coefficient sequence, sparse terms, or prepared array.
        budget: The caller-owned work allowance, shared through preparation and computation.

    Returns:
        The normalized coefficient GCD; a scalar for dense input or a polynomial in the remaining sparse axes.

    Raises:
        PolyError: LIMIT on exhausted work, CAPACITY on unrepresentable sizes, DOMAIN for invalid input, or UNSUPPORTED for a documented domain restriction.
    """
    comptime k = _Kind[_Element[I]]
    var p = _prepare(values, budget)
    var result = _content(_dense_sparse(p._core[], budget), 0, budget)
    if not len(result.terms):
        return _unwrap[k](_Ring[k].zero(p._core[].ring))
    _charge_size(result.terms[0].coefficient.size(), budget)
    return _unwrap[k](result.terms[0].coefficient)

def content[I: Iterable](values: I, *, max_steps: UInt64 = UInt64.MAX) raises PolyError -> _Scalar[_Kind[_Element[I]]]:
    """Return the normalized coefficient GCD.

    Integer content is nonnegative. Field content is monic; a nonzero univariate field polynomial has content one. Zero has content zero.

    Parameters:
        I: The inferred input iterable type.

    Args:
        values: The coefficient sequence, sparse terms, or prepared array.
        max_steps: The complete call's work allowance; defaults to UInt64.MAX.

    Returns:
        The normalized coefficient GCD; a scalar for dense input or a polynomial in the remaining sparse axes.

    Raises:
        PolyError: LIMIT on exhausted work, CAPACITY on unrepresentable sizes, DOMAIN for invalid input, or UNSUPPORTED for a documented domain restriction.
    """
    var budget = Budget(max_steps)
    return content(values, budget)


def primitive_part[I: Iterable](values: I, mut budget: Budget) raises PolyError -> Array[_Kind[_Element[I]]]:
    """Divide by the coefficient content, preserving the coefficient ring.

    Parameters:
        I: The inferred input iterable type.

    Args:
        values: The coefficient sequence, sparse terms, or prepared array.
        budget: The caller-owned work allowance, shared through preparation and computation.

    Returns:
        The input divided by its content, or zero for a zero input.

    Raises:
        PolyError: LIMIT on exhausted work, CAPACITY on unrepresentable sizes, DOMAIN for invalid input, or UNSUPPORTED for a documented domain restriction.
    """
    comptime k = _Kind[_Element[I]]
    var p = _prepare(values, budget)
    var result = _primitive_part(_dense_sparse(p._core[], budget), 0, budget)
    return _from_sparse[k](result, budget)

def primitive_part[I: Iterable](values: I, *, max_steps: UInt64 = UInt64.MAX) raises PolyError -> Array[_Kind[_Element[I]]]:
    """Divide by the coefficient content, preserving the coefficient ring.

    Parameters:
        I: The inferred input iterable type.

    Args:
        values: The coefficient sequence, sparse terms, or prepared array.
        max_steps: The complete call's work allowance; defaults to UInt64.MAX.

    Returns:
        The input divided by its content, or zero for a zero input.

    Raises:
        PolyError: LIMIT on exhausted work, CAPACITY on unrepresentable sizes, DOMAIN for invalid input, or UNSUPPORTED for a documented domain restriction.
    """
    var budget = Budget(max_steps)
    return primitive_part(values, budget)


def gcd[A: Iterable, B: Iterable](a: A, b: B, mut budget: Budget) raises PolyError -> Array[_Join[_Kind[_Element[A]], _Kind[_Element[B]]]]:
    """Return a positive-leading integer GCD or a monic field GCD.

    Parameters:
        A: The first inferred iterable type.
        B: The second inferred iterable type.

    Args:
        a: The first polynomial.
        b: The second polynomial.
        budget: The caller-owned work allowance, shared through preparation and computation.

    Returns:
        The positive-leading integer GCD, including integer content, or the monic field GCD. GCD(0, 0) is zero.

    Raises:
        PolyError: LIMIT on exhausted work, CAPACITY on unrepresentable sizes, DOMAIN for invalid input, or UNSUPPORTED for a documented domain restriction.
    """
    comptime k = _Join[_Kind[_Element[A]], _Kind[_Element[B]]]
    var pair = _pair[k](a, b, budget)
    var left = _dense_sparse(pair[0]._core[], budget)
    var right = _dense_sparse(pair[1]._core[], budget)
    return _from_sparse[k](_gcd_value(left, right, budget), budget)

def gcd[A: Iterable, B: Iterable](a: A, b: B, *, max_steps: UInt64 = UInt64.MAX) raises PolyError -> Array[_Join[_Kind[_Element[A]], _Kind[_Element[B]]]]:
    """Return a positive-leading integer GCD or a monic field GCD.

    Parameters:
        A: The first inferred iterable type.
        B: The second inferred iterable type.

    Args:
        a: The first polynomial.
        b: The second polynomial.
        max_steps: The complete call's work allowance; defaults to UInt64.MAX.

    Returns:
        The positive-leading integer GCD, including integer content, or the monic field GCD. GCD(0, 0) is zero.

    Raises:
        PolyError: LIMIT on exhausted work, CAPACITY on unrepresentable sizes, DOMAIN for invalid input, or UNSUPPORTED for a documented domain restriction.
    """
    var budget = Budget(max_steps)
    return gcd(a, b, budget)


def divide_exact[A: Iterable, B: Iterable](a: A, b: B, mut budget: Budget) raises PolyError -> Optional[Array[_Join[_Kind[_Element[A]], _Kind[_Element[B]]]]]:
    """Return a quotient in the inferred ring, or None when division is not exact.

    Integer inputs stay in ZZ unless another operand widens the domain. Use divmod for field division or an explicit Rational coefficient to request QQ.

    Parameters:
        A: The first inferred iterable type.
        B: The second inferred iterable type.

    Args:
        a: The first polynomial.
        b: The second polynomial.
        budget: The caller-owned work allowance, shared through preparation and computation.

    Returns:
        A quotient in the inferred coefficient ring, or None if that ring contains no exact quotient.

    Raises:
        PolyError: LIMIT on exhausted work, CAPACITY on unrepresentable sizes, DOMAIN for invalid input, or UNSUPPORTED for a documented domain restriction.
    """
    comptime k = _Join[_Kind[_Element[A]], _Kind[_Element[B]]]
    var pair = _pair[k](a, b, budget)
    var left = _dense_sparse(pair[0]._core[], budget)
    var right = _dense_sparse(pair[1]._core[], budget)
    var result = _divide_exact(left, right, budget)
    if not result:
        return None
    return Optional(_from_sparse[k](result.value(), budget))

def divide_exact[A: Iterable, B: Iterable](a: A, b: B, *, max_steps: UInt64 = UInt64.MAX) raises PolyError -> Optional[Array[_Join[_Kind[_Element[A]], _Kind[_Element[B]]]]]:
    """Return a quotient in the inferred ring, or None when division is not exact.

    Integer inputs stay in ZZ unless another operand widens the domain. Use divmod for field division or an explicit Rational coefficient to request QQ.

    Parameters:
        A: The first inferred iterable type.
        B: The second inferred iterable type.

    Args:
        a: The first polynomial.
        b: The second polynomial.
        max_steps: The complete call's work allowance; defaults to UInt64.MAX.

    Returns:
        A quotient in the inferred coefficient ring, or None if that ring contains no exact quotient.

    Raises:
        PolyError: LIMIT on exhausted work, CAPACITY on unrepresentable sizes, DOMAIN for invalid input, or UNSUPPORTED for a documented domain restriction.
    """
    var budget = Budget(max_steps)
    return divide_exact(a, b, budget)


def resultant[A: Iterable, B: Iterable](a: A, b: B, mut budget: Budget) raises PolyError -> _Scalar[_Join[_Kind[_Element[A]], _Kind[_Element[B]]]]:
    """Eliminate the variable using the Sylvester sign convention.

    Two nonzero constants in the elimination variable raise DOMAIN; a zero operand returns zero. Sparse output retains the eliminated axis with exponent zero.

    Parameters:
        A: The first inferred iterable type.
        B: The second inferred iterable type.

    Args:
        a: The first polynomial.
        b: The second polynomial.
        budget: The caller-owned work allowance, shared through preparation and computation.

    Returns:
        The Sylvester-convention resultant; a scalar for dense input or an array retaining the sparse power shape.

    Raises:
        PolyError: LIMIT on exhausted work, CAPACITY on unrepresentable sizes, DOMAIN for invalid input, or UNSUPPORTED for a documented domain restriction.
    """
    comptime k = _Join[_Kind[_Element[A]], _Kind[_Element[B]]]
    var pair = _pair[k](a, b, budget)
    var left = _dense_sparse(pair[0]._core[], budget)
    var right = _dense_sparse(pair[1]._core[], budget)
    var result = _resultant(left, right, 0, budget)
    if not len(result.resultant.terms):
        return _unwrap[k](_Ring[k].zero(left.ring))
    _charge_size(result.resultant.terms[0].coefficient.size(), budget)
    return _unwrap[k](result.resultant.terms[0].coefficient)

def resultant[A: Iterable, B: Iterable](a: A, b: B, *, max_steps: UInt64 = UInt64.MAX) raises PolyError -> _Scalar[_Join[_Kind[_Element[A]], _Kind[_Element[B]]]]:
    """Eliminate the variable using the Sylvester sign convention.

    Two nonzero constants in the elimination variable raise DOMAIN; a zero operand returns zero. Sparse output retains the eliminated axis with exponent zero.

    Parameters:
        A: The first inferred iterable type.
        B: The second inferred iterable type.

    Args:
        a: The first polynomial.
        b: The second polynomial.
        max_steps: The complete call's work allowance; defaults to UInt64.MAX.

    Returns:
        The Sylvester-convention resultant; a scalar for dense input or an array retaining the sparse power shape.

    Raises:
        PolyError: LIMIT on exhausted work, CAPACITY on unrepresentable sizes, DOMAIN for invalid input, or UNSUPPORTED for a documented domain restriction.
    """
    var budget = Budget(max_steps)
    return resultant(a, b, budget)


def subresultants[A: Iterable, B: Iterable](a: A, b: B, mut budget: Budget) raises PolyError -> List[Array[_Join[_Kind[_Element[A]], _Kind[_Element[B]]]]]:
    """Return the indexed subresultants, retaining zero entries.

    Parameters:
        A: The first inferred iterable type.
        B: The second inferred iterable type.

    Args:
        a: The first polynomial.
        b: The second polynomial.
        budget: The caller-owned work allowance, shared through preparation and computation.

    Returns:
        The list S_0 through S_(min(deg(a), deg(b))-1), including zeros; empty when the smaller degree is nonpositive.

    Raises:
        PolyError: LIMIT on exhausted work, CAPACITY on unrepresentable sizes, DOMAIN for invalid input, or UNSUPPORTED for a documented domain restriction.
    """
    comptime k = _Join[_Kind[_Element[A]], _Kind[_Element[B]]]
    var pair = _pair[k](a, b, budget)
    var left = _dense_sparse(pair[0]._core[], budget)
    var right = _dense_sparse(pair[1]._core[], budget)
    var result = _subresultants(left, right, 0, budget)
    _allocation[Array[k]](len(result), budget)
    var arrays = List[Array[k]](capacity=len(result))
    for item in result:
        arrays.append(_from_sparse[k](item, budget))
    return arrays^

def subresultants[A: Iterable, B: Iterable](a: A, b: B, *, max_steps: UInt64 = UInt64.MAX) raises PolyError -> List[Array[_Join[_Kind[_Element[A]], _Kind[_Element[B]]]]]:
    """Return the indexed subresultants, retaining zero entries.

    Parameters:
        A: The first inferred iterable type.
        B: The second inferred iterable type.

    Args:
        a: The first polynomial.
        b: The second polynomial.
        max_steps: The complete call's work allowance; defaults to UInt64.MAX.

    Returns:
        The list S_0 through S_(min(deg(a), deg(b))-1), including zeros; empty when the smaller degree is nonpositive.

    Raises:
        PolyError: LIMIT on exhausted work, CAPACITY on unrepresentable sizes, DOMAIN for invalid input, or UNSUPPORTED for a documented domain restriction.
    """
    var budget = Budget(max_steps)
    return subresultants(a, b, budget)


def extended_gcd[A: Iterable, B: Iterable](a: A, b: B, mut budget: Budget) raises PolyError -> Tuple[Array[_FieldKind[_Join[_Kind[_Element[A]], _Kind[_Element[B]]]]], Array[_FieldKind[_Join[_Kind[_Element[A]], _Kind[_Element[B]]]]], Array[_FieldKind[_Join[_Kind[_Element[A]], _Kind[_Element[B]]]]]]:
    """Return (g, u, v) with u*a + v*b = g; integer inputs promote to QQ.

    Sparse input must have one axis and is converted to dense storage. For several variables, use gcd or the core certificate API.

    Parameters:
        A: The first inferred iterable type.
        B: The second inferred iterable type.

    Args:
        a: The first polynomial.
        b: The second polynomial.
        budget: The caller-owned work allowance, shared through preparation and computation.

    Returns:
        The tuple (g, u, v) with u*a + v*b = g and monic nonzero g; integers promote to QQ.

    Raises:
        PolyError: LIMIT on exhausted work, CAPACITY on unrepresentable sizes, DOMAIN for invalid input, or UNSUPPORTED for a documented domain restriction.
    """
    comptime k = _FieldKind[_Join[_Kind[_Element[A]], _Kind[_Element[B]]]]
    var pair = _pair[k](a, b, budget)
    return _extended_gcd_arrays(pair[0], pair[1], budget)

def _extended_gcd_arrays[k: Int](a: Array[k], b: Array[k], mut budget: Budget) raises PolyError -> Tuple[Array[k], Array[k], Array[k]]:
    comptime F = downcast[_Ring[k], CoefficientField]
    var result = _extended_gcd(rebind[DensePoly[F]](a._core[]), rebind[DensePoly[F]](b._core[]), budget)
    var g = _from_sparse[k](rebind[SparsePoly[_Ring[k]]](result.gcd), budget)
    var u = _from_sparse[k](rebind[SparsePoly[_Ring[k]]](result.bezout.value()[0]), budget)
    var v = _from_sparse[k](rebind[SparsePoly[_Ring[k]]](result.bezout.value()[1]), budget)
    return g^, u^, v^

def extended_gcd[A: Iterable, B: Iterable](a: A, b: B, *, max_steps: UInt64 = UInt64.MAX) raises PolyError -> Tuple[Array[_FieldKind[_Join[_Kind[_Element[A]], _Kind[_Element[B]]]]], Array[_FieldKind[_Join[_Kind[_Element[A]], _Kind[_Element[B]]]]], Array[_FieldKind[_Join[_Kind[_Element[A]], _Kind[_Element[B]]]]]]:
    """Return (g, u, v) with u*a + v*b = g; integer inputs promote to QQ.

    Sparse input must have one axis and is converted to dense storage. For several variables, use gcd or the core certificate API.

    Parameters:
        A: The first inferred iterable type.
        B: The second inferred iterable type.

    Args:
        a: The first polynomial.
        b: The second polynomial.
        max_steps: The complete call's work allowance; defaults to UInt64.MAX.

    Returns:
        The tuple (g, u, v) with u*a + v*b = g and monic nonzero g; integers promote to QQ.

    Raises:
        PolyError: LIMIT on exhausted work, CAPACITY on unrepresentable sizes, DOMAIN for invalid input, or UNSUPPORTED for a documented domain restriction.
    """
    var budget = Budget(max_steps)
    return extended_gcd(a, b, budget)


def pseudo_divmod[A: Iterable, B: Iterable](a: A, b: B, mut budget: Budget) raises PolyError -> Tuple[_Scalar[_Join[_Kind[_Element[A]], _Kind[_Element[B]]]], Array[_Join[_Kind[_Element[A]], _Kind[_Element[B]]]], Array[_Join[_Kind[_Element[A]], _Kind[_Element[B]]]]]:
    """Return (scale, q, r) with scale*a = q*b + r without introducing fractions.

    The remainder has smaller degree than the divisor. Sparse input must have one axis and is converted to dense storage; use a finite work limit for large sparse powers.

    Parameters:
        A: The first inferred iterable type.
        B: The second inferred iterable type.

    Args:
        a: The first polynomial.
        b: The second polynomial.
        budget: The caller-owned work allowance, shared through preparation and computation.

    Returns:
        The tuple (scale, q, r), where scale = lc(b)**max(deg(a)-deg(b)+1, 0) and scale*a = q*b + r.

    Raises:
        PolyError: LIMIT on exhausted work, CAPACITY on unrepresentable sizes, DOMAIN for invalid input, or UNSUPPORTED for a documented domain restriction.
    """
    comptime k = _Join[_Kind[_Element[A]], _Kind[_Element[B]]]
    var pair = _pair[k](a, b, budget)
    return _pseudo_divmod_arrays(pair[0], pair[1], budget)

def _pseudo_divmod_arrays[k: Int](a: Array[k], b: Array[k], mut budget: Budget) raises PolyError -> Tuple[_Scalar[k], Array[k], Array[k]]:
    var result = _pseudo_divmod(a._core[], b._core[], budget)
    var exponent = max(len(a) - len(b) + 1, 0)
    var scale = _Ring[k].one(a._core[].ring)
    # The core rejects a zero divisor before its leading coefficient is read.
    _charge_size(b._core[].coefficients[len(b) - 1].size(), budget)
    var base = b._core[].coefficients[len(b) - 1].copy()
    while exponent:
        budget.charge(1)
        if exponent & 1:
            scale = scale.mul(base, budget)
        exponent >>= 1
        if exponent:
            base = base.mul(base, budget)
    var quotient = Array[k](_take_dense(result.quotient), budget)
    var remainder = Array[k](_take_dense(result.remainder), budget)
    _charge_size(scale.size(), budget)
    return _unwrap[k](scale), quotient^, remainder^

def pseudo_divmod[A: Iterable, B: Iterable](a: A, b: B, *, max_steps: UInt64 = UInt64.MAX) raises PolyError -> Tuple[_Scalar[_Join[_Kind[_Element[A]], _Kind[_Element[B]]]], Array[_Join[_Kind[_Element[A]], _Kind[_Element[B]]]], Array[_Join[_Kind[_Element[A]], _Kind[_Element[B]]]]]:
    """Return (scale, q, r) with scale*a = q*b + r without introducing fractions.

    The remainder has smaller degree than the divisor. Sparse input must have one axis and is converted to dense storage; use a finite work limit for large sparse powers.

    Parameters:
        A: The first inferred iterable type.
        B: The second inferred iterable type.

    Args:
        a: The first polynomial.
        b: The second polynomial.
        max_steps: The complete call's work allowance; defaults to UInt64.MAX.

    Returns:
        The tuple (scale, q, r), where scale = lc(b)**max(deg(a)-deg(b)+1, 0) and scale*a = q*b + r.

    Raises:
        PolyError: LIMIT on exhausted work, CAPACITY on unrepresentable sizes, DOMAIN for invalid input, or UNSUPPORTED for a documented domain restriction.
    """
    var budget = Budget(max_steps)
    return pseudo_divmod(a, b, budget)



def interpolate[A: Iterable, B: Iterable](points: A, values: B, mut budget: Budget) raises PolyError -> Array[_FieldKind[_Join[_Kind[_Element[A]], _Kind[_Element[B]]]]]:
    """Interpolate distinct nodes exactly; integer data promotes to QQ.

    Nodes must be distinct and sample counts must match. Empty data returns zero; trailing zero samples are retained as constraints.

    Parameters:
        A: The first inferred iterable type.
        B: The second inferred iterable type.

    Args:
        points: A one-dimensional sequence of exact points, in output order.
        values: Exact samples in node order, including every zero.
        budget: The caller-owned work allowance, shared through preparation and computation.

    Returns:
        The polynomial of degree below the node count matching every sample; integer data promotes to QQ.

    Raises:
        PolyError: LIMIT on exhausted work, CAPACITY on unrepresentable sizes, DOMAIN for invalid input, or UNSUPPORTED for a documented domain restriction.
    """
    comptime k = _FieldKind[_Join[_Kind[_Element[A]], _Kind[_Element[B]]]]
    comptime F = downcast[_Ring[k], CoefficientField]
    var nodes = _sequence(points, budget)
    var samples = _sequence(values, budget)
    var ctx = _data_context[k](nodes.modulus(), samples.modulus(), budget)
    var xs = _sequence_coefficients[k](nodes, ctx, budget)
    var ys = _sequence_coefficients[k](samples, ctx, budget)
    return Array[k](rebind_var[DensePoly[_Ring[k]]](_interpolate[F](0, rebind[F.Context](ctx), rebind[List[F]](xs), rebind[List[F]](ys), budget)), budget)

def interpolate[A: Iterable, B: Iterable](points: A, values: B, *, max_steps: UInt64 = UInt64.MAX) raises PolyError -> Array[_FieldKind[_Join[_Kind[_Element[A]], _Kind[_Element[B]]]]]:
    """Interpolate distinct nodes exactly; integer data promotes to QQ.

    Nodes must be distinct and sample counts must match. Empty data returns zero; trailing zero samples are retained as constraints.

    Parameters:
        A: The first inferred iterable type.
        B: The second inferred iterable type.

    Args:
        points: A one-dimensional sequence of exact points, in output order.
        values: Exact samples in node order, including every zero.
        max_steps: The complete call's work allowance; defaults to UInt64.MAX.

    Returns:
        The polynomial of degree below the node count matching every sample; integer data promotes to QQ.

    Raises:
        PolyError: LIMIT on exhausted work, CAPACITY on unrepresentable sizes, DOMAIN for invalid input, or UNSUPPORTED for a documented domain restriction.
    """
    var budget = Budget(max_steps)
    return interpolate(points, values, budget)


def hermite_interpolate[A: Iterable, B: Iterable](points: A, jets: B, mut budget: Budget, *, derivatives: Bool = True) raises PolyError -> Array[_FieldKind[_Join[_Kind[_Element[A]], _Kind[_Element[_Nested[B]]]]]]:
    """Interpolate value and consecutive derivative constraints at distinct nodes.

    Node and jet counts must match, nodes must be distinct, and each jet must be nonempty. Raw derivatives in a finite field require invertible factorials; use derivatives=False for Taylor coefficients.

    Parameters:
        A: The first inferred iterable type.
        B: The second inferred iterable type.

    Args:
        points: A one-dimensional sequence of exact points, in output order.
        jets: One nonempty exact sequence per node, beginning with the value and followed by consecutive derivatives.
        budget: The caller-owned work allowance, shared through preparation and computation.
        derivatives: True interprets jets as raw derivatives; False interprets them as Taylor coefficients.

    Returns:
        The polynomial of degree below the total constraint count matching every jet; integers promote to QQ.

    Raises:
        PolyError: LIMIT on exhausted work, CAPACITY on unrepresentable sizes, DOMAIN for invalid input, or UNSUPPORTED for a documented domain restriction.
    """
    comptime k = _FieldKind[_Join[_Kind[_Element[A]], _Kind[_Element[_Nested[B]]]]]
    comptime F = downcast[_Ring[k], CoefficientField]
    var nodes = _sequence(points, budget)
    var rows = _rows(jets, budget)
    var modulus = nodes.modulus()
    for row in rows:
        budget.charge(1)
        modulus = _merge_modulus(modulus, row.modulus())
    var ctx = _data_context[k](modulus, 0, budget)
    var xs = _sequence_coefficients[k](nodes, ctx, budget)
    _allocation[List[F]](len(rows), budget)
    var ys = List[List[F]](capacity=len(rows))
    for row in rows:
        ys.append(rebind_var[List[F]](_sequence_coefficients[k](row, ctx, budget)))
    return Array[k](rebind_var[DensePoly[_Ring[k]]](_hermite_interpolate[F](0, rebind[F.Context](ctx), rebind[List[F]](xs), ys, budget, derivatives=derivatives)), budget)

def hermite_interpolate[A: Iterable, B: Iterable](points: A, jets: B, *, max_steps: UInt64 = UInt64.MAX, derivatives: Bool = True) raises PolyError -> Array[_FieldKind[_Join[_Kind[_Element[A]], _Kind[_Element[_Nested[B]]]]]]:
    """Interpolate value and consecutive derivative constraints at distinct nodes.

    Node and jet counts must match, nodes must be distinct, and each jet must be nonempty. Raw derivatives in a finite field require invertible factorials; use derivatives=False for Taylor coefficients.

    Parameters:
        A: The first inferred iterable type.
        B: The second inferred iterable type.

    Args:
        points: A one-dimensional sequence of exact points, in output order.
        jets: One nonempty exact sequence per node, beginning with the value and followed by consecutive derivatives.
        max_steps: The complete call's work allowance; defaults to UInt64.MAX.
        derivatives: True interprets jets as raw derivatives; False interprets them as Taylor coefficients.

    Returns:
        The polynomial of degree below the total constraint count matching every jet; integers promote to QQ.

    Raises:
        PolyError: LIMIT on exhausted work, CAPACITY on unrepresentable sizes, DOMAIN for invalid input, or UNSUPPORTED for a documented domain restriction.
    """
    var budget = Budget(max_steps)
    return hermite_interpolate(points, jets, budget, derivatives=derivatives)


def affine_transform[I: Iterable, T: Copyable & Deinitable, U: Copyable & Deinitable](values: I, scale: T, shift: U, mut budget: Budget) raises PolyError -> Array[_Join[_Kind[_Element[I]], _Join[_Kind[T], _Kind[U]]]]:
    """Return p(scale*x + shift), promoting polynomial and scalars together.

    Parameters:
        I: The inferred input iterable type.
        T: The sequence's exact scalar type.
        U: The inferred type of the second exact scalar.

    Args:
        values: The coefficient sequence, sparse terms, or prepared array.
        scale: The exact multiplier of the selected variable.
        shift: The exact constant added to the scaled variable.
        budget: The caller-owned work allowance, shared through preparation and computation.

    Returns:
        The polynomial with the selected variable replaced by scale*x + shift.

    Raises:
        PolyError: LIMIT on exhausted work, CAPACITY on unrepresentable sizes, DOMAIN for invalid input, or UNSUPPORTED for a documented domain restriction.
    """
    comptime k = _Join[_Kind[_Element[I]], _Join[_Kind[T], _Kind[U]]]
    var p = _prepare(values, budget)
    var context = _Context[k]()
    if p.modulus():
        context.observe(p.modulus(), budget)
    comptime if T == ModInt:
        context.observe(rebind[ModInt](scale).modulus, budget)
    comptime if U == ModInt:
        context.observe(rebind[ModInt](shift).modulus, budget)
    var ctx = context.get()
    var promoted = _promote[k](p, ctx, budget)
    var c_scale = _wrap[k](_convert[k](scale, ctx, budget))
    var c_shift = _wrap[k](_convert[k](shift, ctx, budget))
    return Array[k](_affine_transform(promoted._core[], c_scale, c_shift, budget), budget)

def affine_transform[I: Iterable, T: Copyable & Deinitable, U: Copyable & Deinitable](values: I, scale: T, shift: U, *, max_steps: UInt64 = UInt64.MAX) raises PolyError -> Array[_Join[_Kind[_Element[I]], _Join[_Kind[T], _Kind[U]]]]:
    """Return p(scale*x + shift), promoting polynomial and scalars together.

    Parameters:
        I: The inferred input iterable type.
        T: The sequence's exact scalar type.
        U: The inferred type of the second exact scalar.

    Args:
        values: The coefficient sequence, sparse terms, or prepared array.
        scale: The exact multiplier of the selected variable.
        shift: The exact constant added to the scaled variable.
        max_steps: The complete call's work allowance; defaults to UInt64.MAX.

    Returns:
        The polynomial with the selected variable replaced by scale*x + shift.

    Raises:
        PolyError: LIMIT on exhausted work, CAPACITY on unrepresentable sizes, DOMAIN for invalid input, or UNSUPPORTED for a documented domain restriction.
    """
    var budget = Budget(max_steps)
    return affine_transform(values, scale, shift, budget)


def taylor_shift[I: Iterable, T: Copyable & Deinitable](values: I, point: T, mut budget: Budget) raises PolyError -> Array[_Join[_Kind[_Element[I]], _Kind[T]]]:
    """Return p(x + point) in the promoted exact ring.

    Parameters:
        I: The inferred input iterable type.
        T: The sequence's exact scalar type.

    Args:
        values: The coefficient sequence, sparse terms, or prepared array.
        point: An exact scalar for one variable, or a coordinate tuple in variable order.
        budget: The caller-owned work allowance, shared through preparation and computation.

    Returns:
        The polynomial with the selected variable replaced by x + point.

    Raises:
        PolyError: LIMIT on exhausted work, CAPACITY on unrepresentable sizes, DOMAIN for invalid input, or UNSUPPORTED for a documented domain restriction.
    """
    comptime k = _Join[_Kind[_Element[I]], _Kind[T]]
    var p = _prepare(values, budget)
    var context = _Context[k]()
    if p.modulus():
        context.observe(p.modulus(), budget)
    comptime if T == ModInt:
        context.observe(rebind[ModInt](point).modulus, budget)
    var ctx = context.get()
    var promoted = _promote[k](p, ctx, budget)
    var c_point = _wrap[k](_convert[k](point, ctx, budget))
    return Array[k](_taylor_shift(promoted._core[], c_point, budget), budget)

def taylor_shift[I: Iterable, T: Copyable & Deinitable](values: I, point: T, *, max_steps: UInt64 = UInt64.MAX) raises PolyError -> Array[_Join[_Kind[_Element[I]], _Kind[T]]]:
    """Return p(x + point) in the promoted exact ring.

    Parameters:
        I: The inferred input iterable type.
        T: The sequence's exact scalar type.

    Args:
        values: The coefficient sequence, sparse terms, or prepared array.
        point: An exact scalar for one variable, or a coordinate tuple in variable order.
        max_steps: The complete call's work allowance; defaults to UInt64.MAX.

    Returns:
        The polynomial with the selected variable replaced by x + point.

    Raises:
        PolyError: LIMIT on exhausted work, CAPACITY on unrepresentable sizes, DOMAIN for invalid input, or UNSUPPORTED for a documented domain restriction.
    """
    var budget = Budget(max_steps)
    return taylor_shift(values, point, budget)


def jet_evaluate[I: Iterable, T: Copyable & Deinitable](values: I, point: T, order: Int, mut budget: Budget) raises PolyError -> Values[_Scalar[_Join[_Kind[_Element[I]], _Kind[T]]], _Join[_Kind[_Element[I]], _Kind[T]]]:
    """Return order Taylor coefficients p^(j)(point)/j!, including trailing zeros.

    This computes Taylor coefficients without dividing by factorials, so it also works in a finite field. A negative order raises DOMAIN.

    Parameters:
        I: The inferred input iterable type.
        T: The sequence's exact scalar type.

    Args:
        values: The coefficient sequence, sparse terms, or prepared array.
        point: An exact scalar for one variable, or a coordinate tuple in variable order.
        order: The number of Taylor coefficients to return, including trailing zeros; must be nonnegative.
        budget: The caller-owned work allowance, shared through preparation and computation.

    Returns:
        A Values sequence of p^(j)(point)/j! for 0 <= j < order, including zeros. These are Hasse derivatives in a finite field.

    Raises:
        PolyError: LIMIT on exhausted work, CAPACITY on unrepresentable sizes, DOMAIN for invalid input, or UNSUPPORTED for a documented domain restriction.
    """
    comptime k = _Join[_Kind[_Element[I]], _Kind[T]]
    var p = _prepare(values, budget)
    var context = _Context[k]()
    if p.modulus():
        context.observe(p.modulus(), budget)
    comptime if T == ModInt:
        context.observe(rebind[ModInt](point).modulus, budget)
    var ctx = context.get()
    var promoted = _promote[k](p, ctx, budget)
    var c_point = _wrap[k](_convert[k](point, ctx, budget))
    return _values_from_core[k](_jet_evaluate(promoted._core[], c_point, order, budget), ctx, budget)

def jet_evaluate[I: Iterable, T: Copyable & Deinitable](values: I, point: T, order: Int, *, max_steps: UInt64 = UInt64.MAX) raises PolyError -> Values[_Scalar[_Join[_Kind[_Element[I]], _Kind[T]]], _Join[_Kind[_Element[I]], _Kind[T]]]:
    """Return order Taylor coefficients p^(j)(point)/j!, including trailing zeros.

    This computes Taylor coefficients without dividing by factorials, so it also works in a finite field. A negative order raises DOMAIN.

    Parameters:
        I: The inferred input iterable type.
        T: The sequence's exact scalar type.

    Args:
        values: The coefficient sequence, sparse terms, or prepared array.
        point: An exact scalar for one variable, or a coordinate tuple in variable order.
        order: The number of Taylor coefficients to return, including trailing zeros; must be nonnegative.
        max_steps: The complete call's work allowance; defaults to UInt64.MAX.

    Returns:
        A Values sequence of p^(j)(point)/j! for 0 <= j < order, including zeros. These are Hasse derivatives in a finite field.

    Raises:
        PolyError: LIMIT on exhausted work, CAPACITY on unrepresentable sizes, DOMAIN for invalid input, or UNSUPPORTED for a documented domain restriction.
    """
    var budget = Budget(max_steps)
    return jet_evaluate(values, point, order, budget)


def definite_integral[I: Iterable, T: Copyable & Deinitable, U: Copyable & Deinitable](values: I, low: T, high: U, mut budget: Budget) raises PolyError -> _Scalar[_FieldKind[_Join[_Kind[_Element[I]], _Join[_Kind[T], _Kind[U]]]]]:
    """Integrate between exact endpoints; integer inputs promote to QQ.

    Integer coefficients and endpoints promote to QQ. In a prime field, a nonzero term needing a noninvertible antiderivative denominator raises DOMAIN. Sparse integration retains all axes, with exponent zero on the integrated axis.

    Parameters:
        I: The inferred input iterable type.
        T: The sequence's exact scalar type.
        U: The inferred type of the second exact scalar.

    Args:
        values: The coefficient sequence, sparse terms, or prepared array.
        low: The exact lower integration endpoint.
        high: The exact upper integration endpoint.
        budget: The caller-owned work allowance, shared through preparation and computation.

    Returns:
        The exact endpoint difference of an antiderivative; a scalar for dense input or an array retaining the sparse power shape.

    Raises:
        PolyError: LIMIT on exhausted work, CAPACITY on unrepresentable sizes, DOMAIN for invalid input, or UNSUPPORTED for a documented domain restriction.
    """
    comptime k = _FieldKind[_Join[_Kind[_Element[I]], _Join[_Kind[T], _Kind[U]]]]
    var p = _prepare(values, budget)
    var context = _Context[k]()
    if p.modulus():
        context.observe(p.modulus(), budget)
    comptime if T == ModInt:
        context.observe(rebind[ModInt](low).modulus, budget)
    comptime if U == ModInt:
        context.observe(rebind[ModInt](high).modulus, budget)
    var ctx = context.get()
    var promoted = _promote[k](p, ctx, budget)
    var c_low = _wrap[k](_convert[k](low, ctx, budget))
    var c_high = _wrap[k](_convert[k](high, ctx, budget))
    var result = _definite_integral(promoted._core[], c_low, c_high, budget)
    _charge_size(result.size(), budget)
    return _unwrap[k](result)

def definite_integral[I: Iterable, T: Copyable & Deinitable, U: Copyable & Deinitable](values: I, low: T, high: U, *, max_steps: UInt64 = UInt64.MAX) raises PolyError -> _Scalar[_FieldKind[_Join[_Kind[_Element[I]], _Join[_Kind[T], _Kind[U]]]]]:
    """Integrate between exact endpoints; integer inputs promote to QQ.

    Integer coefficients and endpoints promote to QQ. In a prime field, a nonzero term needing a noninvertible antiderivative denominator raises DOMAIN. Sparse integration retains all axes, with exponent zero on the integrated axis.

    Parameters:
        I: The inferred input iterable type.
        T: The sequence's exact scalar type.
        U: The inferred type of the second exact scalar.

    Args:
        values: The coefficient sequence, sparse terms, or prepared array.
        low: The exact lower integration endpoint.
        high: The exact upper integration endpoint.
        max_steps: The complete call's work allowance; defaults to UInt64.MAX.

    Returns:
        The exact endpoint difference of an antiderivative; a scalar for dense input or an array retaining the sparse power shape.

    Raises:
        PolyError: LIMIT on exhausted work, CAPACITY on unrepresentable sizes, DOMAIN for invalid input, or UNSUPPORTED for a documented domain restriction.
    """
    var budget = Budget(max_steps)
    return definite_integral(values, low, high, budget)


struct PointPlan[k: Int](Copyable, Movable, _WithModulus):
    """Share an immutable product tree for repeated evaluation and interpolation.

    Parameters:
        k: The retained field kind: 1 for QQ, 2 for QQi, or 3 for a prime field.
    """
    comptime _Field = downcast[_Ring[Self.k], CoefficientField]
    var _core: ArcPointer[MultipointPlan[Self._Field]]
    var _ctx: _Ring[Self.k].Context

    def __init__(out self, var core: MultipointPlan[Self._Field], ctx: _Ring[Self.k].Context, mut budget: Budget) raises PolyError:
        """Own prepared storage; use prepare_points to infer its field from nodes.

        Args:
            core: The owned product tree in the plan's retained field.
            ctx: The prepared plan field context.
            budget: The caller-owned work allowance, shared through preparation and computation.

        Raises:
            PolyError: LIMIT on exhausted work, CAPACITY on unrepresentable sizes, DOMAIN for invalid input, or UNSUPPORTED for a documented domain restriction.
        """
        _allocation[MultipointPlan[Self._Field]](1, budget)
        self._core = ArcPointer(core^)
        self._ctx = ctx.copy()

    def point_count(self) -> Int:
        """Return the number of nodes, including repetitions.

        Returns:
            The number of nodes retained by the plan, including repeated nodes.
        """
        return self._core[].point_count()

    def modulus(self) -> UInt64:
        """Return the prime modulus, or zero for characteristic-zero fields.

        Returns:
            The prime modulus for modular data, or zero otherwise.
        """
        comptime if Self.k == 3:
            return rebind[Modulus](self._ctx).value
        return 0

    def domain(self) -> String:
        """Return the field retained by this plan.

        Returns:
            QQ, QQi, or GF(p), including for an empty plan.
        """
        return _domain[Self.k](self.modulus())

    def evaluate[I: Iterable](self, values: I, mut budget: Budget) raises PolyError -> Values[_Scalar[Self.k], Self.k]:
        """Evaluate in node order; inputs must embed into the plan's fixed field.

        Parameters:
            I: The inferred input iterable type.

        Args:
            values: The polynomial coefficient sequence or prepared dense array.
            budget: The caller-owned work allowance, shared through preparation and computation.

        Returns:
            A Values sequence in node order, including every zero, in the fixed plan field.

        Raises:
            PolyError: LIMIT on exhausted work, CAPACITY on unrepresentable sizes, DOMAIN for invalid input, or UNSUPPORTED for a documented domain restriction.
        """
        comptime assert _Join[Self.k, _Kind[_Element[I]]] == Self.k, "input exceeds the plan field; prepare points in the wider domain"
        var p = _prepare(values, budget)
        _ = _merge_modulus(self.modulus(), p.modulus())
        var promoted = _promote[Self.k](p, self._ctx, budget)
        var result = self._core[].evaluate(rebind[DensePoly[Self._Field]](promoted._core[]), budget)
        return _values_from_core[Self.k](rebind_var[List[_Ring[Self.k]]](result^), self._ctx, budget)

    def evaluate[I: Iterable](self, values: I, *, max_steps: UInt64 = UInt64.MAX) raises PolyError -> Values[_Scalar[Self.k], Self.k]:
        """Evaluate a polynomial at the prepared nodes with an optional work limit.

        Parameters:
            I: The inferred input iterable type.

        Args:
            values: The polynomial coefficient sequence or prepared dense array.
            max_steps: The complete call's work allowance; defaults to UInt64.MAX.

        Returns:
            A Values sequence in node order, including every zero, in the fixed plan field.

        Raises:
            PolyError: LIMIT on exhausted work, CAPACITY on unrepresentable sizes, DOMAIN for invalid input, or UNSUPPORTED for a documented domain restriction.
        """
        var budget = Budget(max_steps)
        return self.evaluate(values, budget)

    def interpolate[I: Iterable](self, values: I, mut budget: Budget) raises PolyError -> Array[Self.k]:
        """Interpolate samples in node order; repeated nodes raise DOMAIN.

        Nodes must be distinct and sample counts must match. An empty plan with empty samples returns zero; trailing zero samples are retained as constraints.

        Parameters:
            I: The inferred input iterable type.

        Args:
            values: Exact samples in node order, including every zero.
            budget: The caller-owned work allowance, shared through preparation and computation.

        Returns:
            The polynomial matching the samples in the plan's fixed field, with degree below the node count.

        Raises:
            PolyError: LIMIT on exhausted work, CAPACITY on unrepresentable sizes, DOMAIN for invalid input, or UNSUPPORTED for a documented domain restriction.
        """
        comptime assert _Join[Self.k, _Kind[_Element[I]]] == Self.k, "input exceeds the plan field; prepare points in the wider domain"
        var samples = _sequence(values, budget)
        _ = _merge_modulus(self.modulus(), samples.modulus())
        var ys = _sequence_coefficients[Self.k](samples, self._ctx, budget)
        return Array[Self.k](rebind_var[DensePoly[_Ring[Self.k]]](self._core[].interpolate(rebind[List[Self._Field]](ys), budget)), budget)

    def interpolate[I: Iterable](self, values: I, *, max_steps: UInt64 = UInt64.MAX) raises PolyError -> Array[Self.k]:
        """Interpolate samples at the prepared nodes with an optional work limit.

        Nodes must be distinct and sample counts must match. An empty plan with empty samples returns zero; trailing zero samples are retained as constraints.

        Parameters:
            I: The inferred input iterable type.

        Args:
            values: Exact samples in node order, including every zero.
            max_steps: The complete call's work allowance; defaults to UInt64.MAX.

        Returns:
            The polynomial matching the samples in the plan's fixed field, with degree below the node count.

        Raises:
            PolyError: LIMIT on exhausted work, CAPACITY on unrepresentable sizes, DOMAIN for invalid input, or UNSUPPORTED for a documented domain restriction.
        """
        var budget = Budget(max_steps)
        return self.interpolate(values, budget)


def prepare_points[I: Iterable](points: I, mut budget: Budget, *, interpolation: Bool = False) raises PolyError -> PointPlan[_FieldKind[_Kind[_Element[I]]]]:
    """Prepare reusable evaluation nodes, optionally caching interpolation weights.

    Repeated nodes are allowed for evaluation when interpolation=False; interpolation later rejects them. The plan fixes its field at preparation. Prepare it from wider-domain nodes when evaluating or interpolating wider-domain inputs. Copies share the product tree.

    Parameters:
        I: The inferred input iterable type.

    Args:
        points: A one-dimensional sequence of exact points, in output order.
        budget: The caller-owned work allowance, shared through preparation and computation.
        interpolation: Also cache inverse interpolation weights and reject duplicate nodes during preparation; defaults to False.

    Returns:
        An immutable shared plan in the inferred field, with integer nodes promoted to QQ.

    Raises:
        PolyError: LIMIT on exhausted work, CAPACITY on unrepresentable sizes, DOMAIN for invalid input, or UNSUPPORTED for a documented domain restriction.
    """
    comptime k = _FieldKind[_Kind[_Element[I]]]
    comptime F = downcast[_Ring[k], CoefficientField]
    var nodes = _sequence(points, budget)
    var ctx = _data_context[k](nodes.modulus(), 0, budget)
    var xs = _sequence_coefficients[k](nodes, ctx, budget)
    if interpolation:
        return PointPlan[k](MultipointPlan[F].prepare_interpolation(0, rebind[F.Context](ctx), rebind[List[F]](xs), budget), ctx, budget)
    return PointPlan[k](MultipointPlan[F].prepare(0, rebind[F.Context](ctx), rebind[List[F]](xs), budget), ctx, budget)

def prepare_points[I: Iterable](points: I, *, max_steps: UInt64 = UInt64.MAX, interpolation: Bool = False) raises PolyError -> PointPlan[_FieldKind[_Kind[_Element[I]]]]:
    """Prepare reusable evaluation nodes, optionally caching interpolation weights.

    Repeated nodes are allowed for evaluation when interpolation=False; interpolation later rejects them. The plan fixes its field at preparation. Prepare it from wider-domain nodes when evaluating or interpolating wider-domain inputs. Copies share the product tree.

    Parameters:
        I: The inferred input iterable type.

    Args:
        points: A one-dimensional sequence of exact points, in output order.
        max_steps: The complete call's work allowance; defaults to UInt64.MAX.
        interpolation: Also cache inverse interpolation weights and reject duplicate nodes during preparation; defaults to False.

    Returns:
        An immutable shared plan in the inferred field, with integer nodes promoted to QQ.

    Raises:
        PolyError: LIMIT on exhausted work, CAPACITY on unrepresentable sizes, DOMAIN for invalid input, or UNSUPPORTED for a documented domain restriction.
    """
    var budget = Budget(max_steps)
    return prepare_points(points, budget, interpolation=interpolation)



def factor[I: Iterable](values: I, mut budget: Budget, *, seed: UInt64 = 0) raises PolyError -> Tuple[_Scalar[_Kind[_Element[I]]], List[Tuple[Array[_Kind[_Element[I]]], Int]]]:
    """Return a scalar and irreducible factors with exact multiplicities.

    ZZ factors are primitive with positive leading coefficient; factors over fields are monic. Zero and constants have no factors. Repeated factors retain their exact multiplicities, including inseparable prime-field inputs. Factors retain deterministic ordering. AA gives linear factors and quadratics with negative discriminant; QQbar gives linear factors. Algebraic factors sort by degree, then leading-to-constant coefficients (real component before imaginary component).

    Parameters:
        I: The inferred input iterable type.

    Args:
        values: The coefficient sequence, sparse terms, or prepared array.
        budget: The caller-owned work allowance, shared through preparation and computation.
        seed: The deterministic finite-field splitting seed; defaults to zero and is ignored outside finite fields.

    Returns:
        The tuple (scalar, factors), where each entry is (irreducible polynomial, positive multiplicity) and their powered product times the scalar equals the input.

    Raises:
        PolyError: LIMIT on exhausted work, CAPACITY on unrepresentable sizes, DOMAIN for invalid input, or UNSUPPORTED for a documented domain restriction.
    """
    return _factor_array(_prepare(values, budget), budget, seed=seed)

def _take_factors[k: Int, C: CoefficientRing](mut source: List[Tuple[DensePoly[C], Int]], mut budget: Budget) raises PolyError -> List[Tuple[Array[k], Int]]:
    comptime assert C == _Ring[k], "factor coefficients must match the array domain"
    _allocation[Tuple[Array[k], Int]](len(source), budget)
    var factors = List[Tuple[Array[k], Int]](capacity=len(source))
    for i in range(len(source)):
        var exponent = source[i][1]
        factors.append((Array[k](rebind_var[DensePoly[_Ring[k]]](_take_dense(source[i][0])), budget), exponent))
    return factors^


def _factor_array[k: Int](p: Array[k], mut budget: Budget, *, seed: UInt64) raises PolyError -> Tuple[_Scalar[k], List[Tuple[Array[k], Int]]]:
    var result = _factor_evidence(p, budget, seed)
    var factors = _take_factors[k](result.factors, budget)
    _charge_size(result.unit.size(), budget)
    return _unwrap[k](result.unit), factors^

def factor[I: Iterable](values: I, *, max_steps: UInt64 = UInt64.MAX, seed: UInt64 = 0) raises PolyError -> Tuple[_Scalar[_Kind[_Element[I]]], List[Tuple[Array[_Kind[_Element[I]]], Int]]]:
    """Return a scalar and irreducible factors with exact multiplicities.

    ZZ factors are primitive with positive leading coefficient; factors over fields are monic. Zero and constants have no factors. Repeated factors retain their exact multiplicities, including inseparable prime-field inputs. Factors retain deterministic ordering. AA gives linear factors and quadratics with negative discriminant; QQbar gives linear factors. Algebraic factors sort by degree, then leading-to-constant coefficients (real component before imaginary component).

    Parameters:
        I: The inferred input iterable type.

    Args:
        values: The coefficient sequence, sparse terms, or prepared array.
        max_steps: The complete call's work allowance; defaults to UInt64.MAX.
        seed: The deterministic finite-field splitting seed; defaults to zero and is ignored outside finite fields.

    Returns:
        The tuple (scalar, factors), where each entry is (irreducible polynomial, positive multiplicity) and their powered product times the scalar equals the input.

    Raises:
        PolyError: LIMIT on exhausted work, CAPACITY on unrepresentable sizes, DOMAIN for invalid input, or UNSUPPORTED for a documented domain restriction.
    """
    var budget = Budget(max_steps)
    return factor(values, budget, seed=seed)


def squarefree[I: Iterable](values: I, mut budget: Budget) raises PolyError -> Tuple[_Scalar[_FieldKind[_Kind[_Element[I]]]], List[Tuple[Array[_FieldKind[_Kind[_Element[I]]]], Int]]]:
    """Return the leading scalar and monic multiplicity blocks; integers promote to QQ.

    Blocks group irreducible factors with the same multiplicity and need not themselves be irreducible. ZZ inputs promote to QQ; QQ, QQi and prime fields retain their domains. Zero and constants have no blocks. Prime-field decomposition includes inverse Frobenius when derivatives vanish.

    Parameters:
        I: The inferred input iterable type.

    Args:
        values: The coefficient sequence, sparse terms, or prepared array.
        budget: The caller-owned work allowance, shared through preparation and computation.

    Returns:
        The tuple (leading scalar, blocks), where each entry is (monic block, positive multiplicity), ordered by multiplicity.

    Raises:
        PolyError: LIMIT on exhausted work, CAPACITY on unrepresentable sizes, DOMAIN for invalid input, or UNSUPPORTED for a documented domain restriction.
    """
    comptime k = _FieldKind[_Kind[_Element[I]]]
    var p = _prepare(values, budget)
    var ctx = _data_context[k](p.modulus(), 0, budget)
    var promoted = _promote[k](p, ctx, budget)
    return _squarefree_array(promoted, budget)

def _squarefree_array[k: Int](p: Array[k], mut budget: Budget) raises PolyError -> Tuple[_Scalar[k], List[Tuple[Array[k], Int]]]:
    comptime F = downcast[_Ring[k], CoefficientField]
    var result = _squarefree[F](rebind[DensePoly[F]](p._core[]), budget)
    var factors = _take_factors[k](result.factors, budget)
    _charge_size(result.unit.size(), budget)
    return _unwrap[k](rebind[_Ring[k]](result.unit)), factors^

def squarefree[I: Iterable](values: I, *, max_steps: UInt64 = UInt64.MAX) raises PolyError -> Tuple[_Scalar[_FieldKind[_Kind[_Element[I]]]], List[Tuple[Array[_FieldKind[_Kind[_Element[I]]]], Int]]]:
    """Return the leading scalar and monic multiplicity blocks; integers promote to QQ.

    Blocks group irreducible factors with the same multiplicity and need not themselves be irreducible. ZZ inputs promote to QQ; QQ, QQi and prime fields retain their domains. Zero and constants have no blocks. Prime-field decomposition includes inverse Frobenius when derivatives vanish.

    Parameters:
        I: The inferred input iterable type.

    Args:
        values: The coefficient sequence, sparse terms, or prepared array.
        max_steps: The complete call's work allowance; defaults to UInt64.MAX.

    Returns:
        The tuple (leading scalar, blocks), where each entry is (monic block, positive multiplicity), ordered by multiplicity.

    Raises:
        PolyError: LIMIT on exhausted work, CAPACITY on unrepresentable sizes, DOMAIN for invalid input, or UNSUPPORTED for a documented domain restriction.
    """
    var budget = Budget(max_steps)
    return squarefree(values, budget)



def _many[k: Int, A: Iterable, B: Iterable](values: A, others: B, mut budget: Budget) raises PolyError -> Tuple[Array[k], List[Array[k]]]:
    var p = _prepare(values, budget)
    var modulus = p.modulus()
    var prepared = List[Array[_Kind[_Element[_Nested[B]]]]]()
    var cursor = iter(others)
    while True:
        budget.charge(1)
        var raw: type_of(cursor).Element
        try:
            raw = next(cursor)
        except StopIteration:
            break
        var raw_values = rebind_var[_Nested[B]](raw^)
        var q = _prepare(raw_values, budget)
        modulus = _merge_modulus(modulus, q.modulus())
        _grow(prepared, budget)
        prepared.append(q^)
    var ctx = _data_context[k](modulus, 0, budget)
    var promoted = _promote[k](p, ctx, budget)
    _allocation[Array[k]](len(prepared), budget)
    var result = List[Array[k]](capacity=len(prepared))
    for q in prepared:
        result.append(_promote[k](q, ctx, budget))
    return promoted^, result^


def divide_many[A: Iterable, B: Iterable](values: A, divisors: B, mut budget: Budget) raises PolyError -> Tuple[List[Array[_FieldKind[_Join[_Kind[_Element[A]], _Kind[_Element[_Nested[B]]]]]]], Array[_FieldKind[_Join[_Kind[_Element[A]], _Kind[_Element[_Nested[B]]]]]]]:
    """Return ordered quotients and a remainder; integer coefficients promote to QQ.

    Sparse reduction uses lexicographic order with axis zero first. Changing divisor order can change quotients and remainder; this is not a Groebner-basis computation. An empty divisor collection returns no quotients and the promoted input as remainder. A zero divisor raises DOMAIN.

    Parameters:
        A: The first inferred iterable type.
        B: The second inferred iterable type.

    Args:
        values: The coefficient sequence, sparse terms, or prepared array.
        divisors: A finite iterable of polynomials of one Mojo input type, tried in the supplied order.
        budget: The caller-owned work allowance, shared through preparation and computation.

    Returns:
        A quotient list in divisor order and a remainder, with input = sum(quotient_i * divisor_i) + remainder.

    Raises:
        PolyError: LIMIT on exhausted work, CAPACITY on unrepresentable sizes, DOMAIN for invalid input, or UNSUPPORTED for a documented domain restriction.
    """
    comptime k = _FieldKind[_Join[_Kind[_Element[A]], _Kind[_Element[_Nested[B]]]]]
    comptime F = downcast[_Ring[k], CoefficientField]
    var prepared = _many[k](values, divisors, budget)
    _allocation[SparsePoly[F]](len(prepared[1]), budget)
    var cores = List[SparsePoly[F]](capacity=len(prepared[1]))
    for q in prepared[1]:
        cores.append(rebind_var[SparsePoly[F]](_dense_sparse(q._core[], budget)))
    var p = _dense_sparse(prepared[0]._core[], budget)
    var result = _divide_by_list[F](rebind[SparsePoly[F]](p), cores, budget)
    _allocation[Array[k]](len(result.quotients), budget)
    var quotients = List[Array[k]](capacity=len(result.quotients))
    for i in range(len(result.quotients)):
        quotients.append(_from_sparse[k](rebind[SparsePoly[_Ring[k]]](result.quotients[i]), budget))
    var remainder = _from_sparse[k](rebind[SparsePoly[_Ring[k]]](result.remainder), budget)
    return quotients^, remainder^

def divide_many[A: Iterable, B: Iterable](values: A, divisors: B, *, max_steps: UInt64 = UInt64.MAX) raises PolyError -> Tuple[List[Array[_FieldKind[_Join[_Kind[_Element[A]], _Kind[_Element[_Nested[B]]]]]]], Array[_FieldKind[_Join[_Kind[_Element[A]], _Kind[_Element[_Nested[B]]]]]]]:
    """Return ordered quotients and a remainder; integer coefficients promote to QQ.

    Sparse reduction uses lexicographic order with axis zero first. Changing divisor order can change quotients and remainder; this is not a Groebner-basis computation. An empty divisor collection returns no quotients and the promoted input as remainder. A zero divisor raises DOMAIN.

    Parameters:
        A: The first inferred iterable type.
        B: The second inferred iterable type.

    Args:
        values: The coefficient sequence, sparse terms, or prepared array.
        divisors: A finite iterable of polynomials of one Mojo input type, tried in the supplied order.
        max_steps: The complete call's work allowance; defaults to UInt64.MAX.

    Returns:
        A quotient list in divisor order and a remainder, with input = sum(quotient_i * divisor_i) + remainder.

    Raises:
        PolyError: LIMIT on exhausted work, CAPACITY on unrepresentable sizes, DOMAIN for invalid input, or UNSUPPORTED for a documented domain restriction.
    """
    var budget = Budget(max_steps)
    return divide_many(values, divisors, budget)

from . import roots as _roots
comptime _AlgebraicInterval[C: AnyType, L: AnyType, H: AnyType] = _Kind[C] == 4 or _Kind[L] == 4 or _Kind[H] == 4
comptime _Count[C: AnyType, L: AnyType, H: AnyType] = _roots.AlgebraicCount if _AlgebraicInterval[C, L, H] else _roots.RootCount
from . import algebraic as _algebraic
from polynomials import real_root as _real_root, NumericOptions, real_roots_exact, complex_roots_exact, real_roots_exact_to, complex_roots_exact_to, RealRootSink, ComplexRootSink, RootStreamReceipt, RealRootStreamChecker, ComplexRootStreamChecker


def _real_input[I: Iterable](values: I, mut budget: Budget) raises PolyError -> Array[1]:
    comptime assert _Kind[_Element[I]] == 0 or _Kind[_Element[I]] == 1, "real roots require exact integer or rational coefficients"
    return _promote[1](_prepare(values, budget), NoContext(), budget)


def real_roots[I: Iterable](values: I, mut budget: Budget) raises PolyError -> _roots.ExactRoots:
    """Find all distinct real roots as exact algebraic values.

    Repeated roots appear once. Constants have no roots; the zero polynomial raises DOMAIN.

    Parameters:
        I: The inferred input type.

    Args:
        values: Ascending integer, rational, or algebraic.Real coefficients, or a prepared array.
        budget: The shared work allowance for preparation and computation.

    Returns:
        An iterable of exact Real values in increasing order, with completeness evidence.

    Raises:
        PolyError: DOMAIN for incompatible input, UNSUPPORTED for an unavailable operation, or LIMIT/CAPACITY on resource limits.
    """
    comptime if _Element[I] == _algebraic.Real:
        return _roots._exact_coefficients(values, budget)
    else:
        return _roots._exact(_real_input(values, budget)._core[], budget)


def real_roots[I: Iterable](values: I, *, max_steps: UInt64 = UInt64.MAX) raises PolyError -> _roots.ExactRoots:
    """Find all distinct real roots as exact algebraic values.

    Repeated roots appear once. Constants have no roots; the zero polynomial raises DOMAIN.

    Parameters:
        I: The inferred input type.

    Args:
        values: Ascending integer, rational, or algebraic.Real coefficients, or a prepared array.
        max_steps: The complete call's work allowance; defaults to UInt64.MAX.

    Returns:
        An iterable of exact Real values in increasing order, with completeness evidence.

    Raises:
        PolyError: DOMAIN for incompatible input, UNSUPPORTED for an unavailable operation, or LIMIT/CAPACITY on resource limits.
    """
    var budget = Budget(max_steps)
    return real_roots(values, budget)


def count_roots[I: Iterable, L: Copyable & Deinitable, H: Copyable & Deinitable](values: I, low: L, high: H, mut budget: Budget) raises PolyError -> _Count[_Element[I], L, H]:
    """Count distinct real roots between exact nonroot endpoints.

    Parameters:
        I: The inferred input type.
        L: The inferred input type.
        H: The inferred input type.

    Args:
        values: Ascending integer or rational coefficients.
        low: The lower rational or integer endpoint.
        high: The larger rational or integer endpoint.
        budget: The shared work allowance for preparation and computation.

    Returns:
        A RootCount containing the count and its checkable certificate.

    Raises:
        PolyError: DOMAIN for incompatible input, UNSUPPORTED for an unavailable operation, or LIMIT/CAPACITY on resource limits.
    """
    comptime if _AlgebraicInterval[_Element[I], L, H]:
        var result = real_roots(values, budget)
        var a = _algebraic.asreal(low, budget)
        var b = _algebraic.asreal(high, budget)
        var count = _roots._interval_count(result, a, b, budget)
        return rebind_var[_Count[_Element[I], L, H]](_roots.AlgebraicCount(result^, a^, b^, count))
    else:
        var p = _real_input(values, budget)
        var a = QQ(_convert[1](low, NoContext(), budget))
        var b = QQ(_convert[1](high, NoContext(), budget))
        return rebind_var[_Count[_Element[I], L, H]](_roots._count(_dense_copy(p._core[], 0, budget), a, b, budget))


def count_roots[I: Iterable, L: Copyable & Deinitable, H: Copyable & Deinitable](values: I, low: L, high: H, *, max_steps: UInt64 = UInt64.MAX) raises PolyError -> _Count[_Element[I], L, H]:
    """Count distinct real roots between exact nonroot endpoints.

    Parameters:
        I: The inferred input type.
        L: The inferred input type.
        H: The inferred input type.

    Args:
        values: Ascending integer or rational coefficients.
        low: The lower rational or integer endpoint.
        high: The larger rational or integer endpoint.
        max_steps: The complete call's work allowance; defaults to UInt64.MAX.

    Returns:
        A RootCount containing the count and its checkable certificate.

    Raises:
        PolyError: DOMAIN for incompatible input, UNSUPPORTED for an unavailable operation, or LIMIT/CAPACITY on resource limits.
    """
    var budget = Budget(max_steps)
    return count_roots(values, low, high, budget)


def root_between[I: Iterable, L: Copyable & Deinitable, H: Copyable & Deinitable](values: I, low: L, high: H, mut budget: Budget) raises PolyError -> _algebraic.Real:
    """Select the unique exact real root in an interval.

    Parameters:
        I: The inferred input type.
        L: The inferred input type.
        H: The inferred input type.

    Args:
        values: Ascending integer or rational coefficients.
        low: The lower nonroot endpoint, or an exact root if endpoints agree.
        high: The upper nonroot endpoint, or the same exact root.
        budget: The shared work allowance for preparation and computation.

    Returns:
        An exact algebraic value with its root-selection witness.

    Raises:
        PolyError: DOMAIN for incompatible input, UNSUPPORTED for an unavailable operation, or LIMIT/CAPACITY on resource limits.
    """
    comptime if _AlgebraicInterval[_Element[I], L, H]:
        var a = _algebraic.asreal(low, budget)
        var b = _algebraic.asreal(high, budget)
        var relation = _algebraic.compare(a, b, budget)
        if relation > 0:
            raise PolyError(PolyErrorKind.DOMAIN, "root interval is reversed")
        var result = real_roots(values, budget)
        var selected = Optional[_algebraic.Real]()
        for root in result:
            var left = _algebraic.compare(root, a, budget)
            var right = _algebraic.compare(root, b, budget)
            if relation == 0 and left == 0:
                return root.copy()
            if relation < 0 and (left == 0 or right == 0):
                raise PolyError(PolyErrorKind.DOMAIN, "root interval endpoints must not be roots")
            if left > 0 and right < 0:
                if selected:
                    raise PolyError(PolyErrorKind.DOMAIN, "root interval must select exactly one root")
                selected = root.copy()
        if not selected:
            raise PolyError(PolyErrorKind.DOMAIN, "root interval must select exactly one root")
        return selected.take()
    else:
        var p = _real_input(values, budget)
        var a = QQ(_convert[1](low, NoContext(), budget))
        var b = QQ(_convert[1](high, NoContext(), budget))
        return _algebraic._plain(_real_root(p._core[], a, b, budget), budget)


def root_between[I: Iterable, L: Copyable & Deinitable, H: Copyable & Deinitable](values: I, low: L, high: H, *, max_steps: UInt64 = UInt64.MAX) raises PolyError -> _algebraic.Real:
    """Select the unique exact real root in an interval.

    Parameters:
        I: The inferred input type.
        L: The inferred input type.
        H: The inferred input type.

    Args:
        values: Ascending integer or rational coefficients.
        low: The lower nonroot endpoint, or an exact root if endpoints agree.
        high: The upper nonroot endpoint, or the same exact root.
        max_steps: The complete call's work allowance; defaults to UInt64.MAX.

    Returns:
        An exact algebraic value with its root-selection witness.

    Raises:
        PolyError: DOMAIN for incompatible input, UNSUPPORTED for an unavailable operation, or LIMIT/CAPACITY on resource limits.
    """
    var budget = Budget(max_steps)
    return root_between(values, low, high, budget)


def real_root_cover[I: Iterable](values: I, mut budget: Budget, *, options: NumericOptions = NumericOptions(), complete_only: Bool = False) raises PolyError -> _RealCover[_Kind[_Element[I]]] where _Kind[_Element[I]] >= 0:
    """Enclose real roots with explicit completeness and accuracy claims.

    Counts are distinct real roots.

    Parameters:
        I: The inferred input type.

    Args:
        values: Exact ascending coefficients or a prepared array.
        budget: The shared work allowance for preparation and computation.
        options: Precision, width, subdivision, and isolation settings.
        complete_only: Raise unless all requested properties succeed.

    Returns:
        The computed result, with its evidence retained.

    Raises:
        PolyError: DOMAIN for incompatible input, UNSUPPORTED for an unavailable operation, or LIMIT/CAPACITY on resource limits.
    """
    comptime if _Kind[_Element[I]] >= 4:
        return rebind_var[_RealCover[_Kind[_Element[I]]]](_roots._ac._make[_Kind[_Element[I]], False](_prepare(values, budget), options, budget, complete_only))
    else:
        var p = _real_input(values, budget)
        var core = _dense_copy(p._core[], 0, budget)
        var proof = real_roots_exact(core, options, budget, complete_only=complete_only)
        _allocation[_roots._RealCoverData[1]](1, budget)
        return rebind_var[_RealCover[_Kind[_Element[I]]]](_roots.RealCover[1](ArcPointer(_roots._RealCoverData[1](core^, options, proof^))))


def real_root_cover[I: Iterable](values: I, *, max_steps: UInt64 = UInt64.MAX, options: NumericOptions = NumericOptions(), complete_only: Bool = False) raises PolyError -> _RealCover[_Kind[_Element[I]]] where _Kind[_Element[I]] >= 0:
    """Enclose real roots with explicit completeness and accuracy claims.

    Counts are distinct real roots.

    Parameters:
        I: The inferred input type.

    Args:
        values: Exact ascending coefficients or a prepared array.
        max_steps: The complete call's work allowance; defaults to UInt64.MAX.
        options: Precision, width, subdivision, and isolation settings.
        complete_only: Raise unless all requested properties succeed.

    Returns:
        The computed result, with its evidence retained.

    Raises:
        PolyError: DOMAIN for incompatible input, UNSUPPORTED for an unavailable operation, or LIMIT/CAPACITY on resource limits.
    """
    var budget = Budget(max_steps)
    return rebind_var[_RealCover[_Kind[_Element[I]]]](real_root_cover(values, budget, options=options, complete_only=complete_only))


def real_root_cover_to[I: Iterable, S: RealRootSink](values: I, mut sink: S, mut budget: Budget, *, options: NumericOptions = NumericOptions(), complete_only: Bool = False) raises PolyError -> RootStreamReceipt where _Kind[_Element[I]] >= 0:
    """Stream real root witnesses without collecting the output.

    Parameters:
        I: The inferred input type.
        S: The inferred input type.

    Args:
        values: Exact ascending coefficients or a prepared array.
        sink: The consumer receiving owned witnesses under the same work budget.
        budget: The shared work allowance for preparation and computation.
        options: The requested precision and root-cover properties.
        complete_only: Raise unless all requested properties succeed.

    Returns:
        A completion receipt; partial writes before an error are not a complete cover.

    Raises:
        PolyError: DOMAIN for incompatible input, UNSUPPORTED for an unavailable operation, or LIMIT/CAPACITY on resource limits.
    """
    comptime if _Kind[_Element[I]] >= 4:
        return _roots._ac._real_to(_prepare(values, budget), options, sink, budget, complete_only)
    else:
        var p = _real_input(values, budget)
        return real_roots_exact_to(p._core[], options, sink, budget, complete_only=complete_only)


def real_root_cover_to[I: Iterable, S: RealRootSink](values: I, mut sink: S, *, max_steps: UInt64 = UInt64.MAX, options: NumericOptions = NumericOptions(), complete_only: Bool = False) raises PolyError -> RootStreamReceipt where _Kind[_Element[I]] >= 0:
    """Stream real root witnesses without collecting the output.

    Parameters:
        I: The inferred input type.
        S: The inferred input type.

    Args:
        values: Exact ascending coefficients or a prepared array.
        sink: The consumer receiving owned witnesses under the same work budget.
        max_steps: The complete call's work allowance; defaults to UInt64.MAX.
        options: The requested precision and root-cover properties.
        complete_only: Raise unless all requested properties succeed.

    Returns:
        A completion receipt; partial writes before an error are not a complete cover.

    Raises:
        PolyError: DOMAIN for incompatible input, UNSUPPORTED for an unavailable operation, or LIMIT/CAPACITY on resource limits.
    """
    var budget = Budget(max_steps)
    return real_root_cover_to(values, sink, budget, options=options, complete_only=complete_only)


def real_root_checker[I: Iterable](values: I, mut budget: Budget, *, options: NumericOptions = NumericOptions()) raises PolyError -> _RealChecker[_Kind[_Element[I]]] where _Kind[_Element[I]] >= 0:
    """Prepare independent incremental checking of a real root stream.

    Parameters:
        I: The inferred input type.

    Args:
        values: The exact input polynomial whose streamed evidence will be checked.
        budget: The shared work allowance for preparation and computation.
        options: The same options passed to the producer.

    Returns:
        A streaming checker; call finish(receipt, budget) after successful production.

    Raises:
        PolyError: DOMAIN for incompatible input, UNSUPPORTED for an unavailable operation, or LIMIT/CAPACITY on resource limits.
    """
    comptime if _Kind[_Element[I]] >= 4:
        return rebind_var[_RealChecker[_Kind[_Element[I]]]](_roots._ac._real_checker(_prepare(values, budget), options, budget))
    else:
        var p = _real_input(values, budget)
        return rebind_var[_RealChecker[_Kind[_Element[I]]]](RealRootStreamChecker.from_dense(p._core[], options, budget))


def real_root_checker[I: Iterable](values: I, *, max_steps: UInt64 = UInt64.MAX, options: NumericOptions = NumericOptions()) raises PolyError -> _RealChecker[_Kind[_Element[I]]] where _Kind[_Element[I]] >= 0:
    """Prepare independent incremental checking of a real root stream.

    Parameters:
        I: The inferred input type.

    Args:
        values: The exact input polynomial whose streamed evidence will be checked.
        max_steps: The complete call's work allowance; defaults to UInt64.MAX.
        options: The same options passed to the producer.

    Returns:
        A streaming checker; call finish(receipt, budget) after successful production.

    Raises:
        PolyError: DOMAIN for incompatible input, UNSUPPORTED for an unavailable operation, or LIMIT/CAPACITY on resource limits.
    """
    var budget = Budget(max_steps)
    return rebind_var[_RealChecker[_Kind[_Element[I]]]](real_root_checker(values, budget, options=options))


def complex_root_cover[I: Iterable](values: I, mut budget: Budget, *, options: NumericOptions = NumericOptions(), complete_only: Bool = False) raises PolyError -> _ComplexCover[_Kind[_Element[I]]] where _Kind[_Element[I]] >= 0:
    """Enclose complex roots with explicit completeness and accuracy claims.

    Counts include multiplicity. Allow clusters with require_isolation=False for repeated roots.

    Parameters:
        I: The inferred input type.

    Args:
        values: Exact ascending coefficients or a prepared array.
        budget: The shared work allowance for preparation and computation.
        options: Precision, width, subdivision, and isolation settings.
        complete_only: Raise unless all requested properties succeed.

    Returns:
        The computed result, with its evidence retained.

    Raises:
        PolyError: DOMAIN for incompatible input, UNSUPPORTED for an unavailable operation, or LIMIT/CAPACITY on resource limits.
    """
    comptime if _Kind[_Element[I]] >= 4:
        return rebind_var[_ComplexCover[_Kind[_Element[I]]]](_roots._ac._make[_Kind[_Element[I]], True](_prepare(values, budget), options, budget, complete_only))
    else:
        comptime assert _Kind[_Element[I]] >= 0 and _Kind[_Element[I]] <= 2, "complex roots require exact integer, rational, or complex coefficients"
        var p = _prepare(values, budget)
        var core = _dense_copy(p._core[], 0, budget)
        var proof = complex_roots_exact(core, options, budget, complete_only=complete_only)
        _allocation[_roots._ComplexCoverData[_Kind[_Element[I]]]](1, budget)
        return rebind_var[_ComplexCover[_Kind[_Element[I]]]](_roots.ComplexCover[_Kind[_Element[I]]](ArcPointer(_roots._ComplexCoverData[_Kind[_Element[I]]](core^, options, proof^))))


def complex_root_cover[I: Iterable](values: I, *, max_steps: UInt64 = UInt64.MAX, options: NumericOptions = NumericOptions(), complete_only: Bool = False) raises PolyError -> _ComplexCover[_Kind[_Element[I]]] where _Kind[_Element[I]] >= 0:
    """Enclose complex roots with explicit completeness and accuracy claims.

    Counts include multiplicity. Allow clusters with require_isolation=False for repeated roots.

    Parameters:
        I: The inferred input type.

    Args:
        values: Exact ascending coefficients or a prepared array.
        max_steps: The complete call's work allowance; defaults to UInt64.MAX.
        options: Precision, width, subdivision, and isolation settings.
        complete_only: Raise unless all requested properties succeed.

    Returns:
        The computed result, with its evidence retained.

    Raises:
        PolyError: DOMAIN for incompatible input, UNSUPPORTED for an unavailable operation, or LIMIT/CAPACITY on resource limits.
    """
    var budget = Budget(max_steps)
    return rebind_var[_ComplexCover[_Kind[_Element[I]]]](complex_root_cover(values, budget, options=options, complete_only=complete_only))


def complex_root_cover_to[I: Iterable, S: ComplexRootSink](values: I, mut sink: S, mut budget: Budget, *, options: NumericOptions = NumericOptions(), complete_only: Bool = False) raises PolyError -> RootStreamReceipt where _Kind[_Element[I]] >= 0:
    """Stream complex root witnesses without collecting the output.

    Parameters:
        I: The inferred input type.
        S: The inferred input type.

    Args:
        values: Exact ascending coefficients or a prepared array.
        sink: The consumer receiving owned witnesses under the same work budget.
        budget: The shared work allowance for preparation and computation.
        options: The requested precision and root-cover properties.
        complete_only: Raise unless all requested properties succeed.

    Returns:
        A completion receipt; partial writes before an error are not a complete cover.

    Raises:
        PolyError: DOMAIN for incompatible input, UNSUPPORTED for an unavailable operation, or LIMIT/CAPACITY on resource limits.
    """
    comptime if _Kind[_Element[I]] >= 4:
        return _roots._ac._complex_to(_prepare(values, budget), options, sink, budget, complete_only)
    else:
        comptime assert _Kind[_Element[I]] >= 0 and _Kind[_Element[I]] <= 2, "complex roots require exact integer, rational, or complex coefficients"
        var p = _prepare(values, budget)
        return complex_roots_exact_to(p._core[], options, sink, budget, complete_only=complete_only)


def complex_root_cover_to[I: Iterable, S: ComplexRootSink](values: I, mut sink: S, *, max_steps: UInt64 = UInt64.MAX, options: NumericOptions = NumericOptions(), complete_only: Bool = False) raises PolyError -> RootStreamReceipt where _Kind[_Element[I]] >= 0:
    """Stream complex root witnesses without collecting the output.

    Parameters:
        I: The inferred input type.
        S: The inferred input type.

    Args:
        values: Exact ascending coefficients or a prepared array.
        sink: The consumer receiving owned witnesses under the same work budget.
        max_steps: The complete call's work allowance; defaults to UInt64.MAX.
        options: The requested precision and root-cover properties.
        complete_only: Raise unless all requested properties succeed.

    Returns:
        A completion receipt; partial writes before an error are not a complete cover.

    Raises:
        PolyError: DOMAIN for incompatible input, UNSUPPORTED for an unavailable operation, or LIMIT/CAPACITY on resource limits.
    """
    var budget = Budget(max_steps)
    return complex_root_cover_to(values, sink, budget, options=options, complete_only=complete_only)


def complex_root_checker[I: Iterable](values: I, mut budget: Budget, *, options: NumericOptions = NumericOptions()) raises PolyError -> _ComplexChecker[_Kind[_Element[I]]] where _Kind[_Element[I]] >= 0:
    """Prepare independent incremental checking of a complex root stream.

    Parameters:
        I: The inferred input type.

    Args:
        values: The exact input polynomial whose streamed evidence will be checked.
        budget: The shared work allowance for preparation and computation.
        options: The same options passed to the producer.

    Returns:
        A streaming checker; call finish(receipt, budget) after successful production.

    Raises:
        PolyError: DOMAIN for incompatible input, UNSUPPORTED for an unavailable operation, or LIMIT/CAPACITY on resource limits.
    """
    comptime if _Kind[_Element[I]] >= 4:
        return rebind_var[_ComplexChecker[_Kind[_Element[I]]]](_roots._ac._complex_checker(_prepare(values, budget), options, budget))
    else:
        comptime assert _Kind[_Element[I]] >= 0 and _Kind[_Element[I]] <= 2, "complex roots require exact integer, rational, or complex coefficients"
        var p = _prepare(values, budget)
        return rebind_var[_ComplexChecker[_Kind[_Element[I]]]](ComplexRootStreamChecker.from_dense(p._core[], options, budget))


def complex_root_checker[I: Iterable](values: I, *, max_steps: UInt64 = UInt64.MAX, options: NumericOptions = NumericOptions()) raises PolyError -> _ComplexChecker[_Kind[_Element[I]]] where _Kind[_Element[I]] >= 0:
    """Prepare independent incremental checking of a complex root stream.

    Parameters:
        I: The inferred input type.

    Args:
        values: The exact input polynomial whose streamed evidence will be checked.
        max_steps: The complete call's work allowance; defaults to UInt64.MAX.
        options: The same options passed to the producer.

    Returns:
        A streaming checker; call finish(receipt, budget) after successful production.

    Raises:
        PolyError: DOMAIN for incompatible input, UNSUPPORTED for an unavailable operation, or LIMIT/CAPACITY on resource limits.
    """
    var budget = Budget(max_steps)
    return rebind_var[_ComplexChecker[_Kind[_Element[I]]]](complex_root_checker(values, budget, options=options))



# Numerical operations keep output precision explicit.
from . import _numeric as _num
from ._numeric import DenseArray as NumericArray
from polynomials import NumericDomain


def asarray[I: Iterable, Context: Copyable & Deinitable](values: I, mut budget: Budget, *, context: Context) raises PolyError -> NumericArray[_num._Domain[Context, _Element[I]]]:
    """Construct finite numerical coefficients using an explicit precision context.

    Parameters:
        I: The inferred input iterable type.
        Context: The explicit APN arithmetic context type.

    Args:
        values: Input coefficients, sparse terms, or prepared values as required by this overload.
        budget: The shared work allowance, including preparation, computation, and result storage.
        context: Explicit output precision, rounding settings, or ball working precision.

    Returns:
        An immutable prepared array in the selected domain or batch shape.

    Raises:
        PolyError: DOMAIN for invalid or incompatible input, or LIMIT/CAPACITY on resource limits.
    """
    comptime assert Context == _num.ArithmeticContext or Context == _num.ComplexContext or Context == _num.BallContext, "choose ArithmeticContext, ComplexContext, or BallContext"
    comptime D = _num._Domain[Context, _Element[I]]
    return _num._dense[D](values, rebind[D.Context](context), budget)


def asarray[I: Iterable, Context: Copyable & Deinitable](values: I, *, context: Context, max_steps: UInt64 = UInt64.MAX) raises PolyError -> NumericArray[_num._Domain[Context, _Element[I]]]:
    """Construct finite numerical coefficients using an explicit precision context.

    Parameters:
        I: The inferred input iterable type.
        Context: The explicit APN arithmetic context type.

    Args:
        values: Input coefficients, sparse terms, or prepared values as required by this overload.
        context: Explicit output precision, rounding settings, or ball working precision.
        max_steps: The complete call's work allowance; defaults to UInt64.MAX.

    Returns:
        An immutable prepared array in the selected domain or batch shape.

    Raises:
        PolyError: DOMAIN for invalid or incompatible input, or LIMIT/CAPACITY on resource limits.
    """
    var budget = Budget(max_steps)
    return asarray(values, budget, context=context)

from polynomials import numeric_integrate_dense, numeric_compose_dense


def add[D: NumericDomain](a: NumericArray[D], b: NumericArray[D], mut budget: Budget, *, context: D.Context) raises PolyError -> NumericArray[D]:
    """Add numerical polynomials in a fixed accumulation order.

    Parameters:
        D: The APN numerical domain associated with the stored scalars.

    Args:
        a: The first input value.
        b: The second input value.
        budget: The shared work allowance, including preparation, computation, and result storage.
        context: Explicit output precision, rounding settings, or ball working precision.

    Returns:
        The coefficientwise sum in the selected output context.

    Raises:
        PolyError: DOMAIN for invalid or incompatible input, or LIMIT/CAPACITY on resource limits.
    """
    _num._context[D](context, budget)
    var result = a._core[].add(b._core[], context, budget)
    return NumericArray[D](result^, budget)


def add[D: NumericDomain](a: NumericArray[D], b: NumericArray[D], *, context: D.Context, max_steps: UInt64 = UInt64.MAX) raises PolyError -> NumericArray[D]:
    """Add numerical polynomials in a fixed accumulation order.

    Parameters:
        D: The APN numerical domain associated with the stored scalars.

    Args:
        a: The first input value.
        b: The second input value.
        context: Explicit output precision, rounding settings, or ball working precision.
        max_steps: The complete call's work allowance; defaults to UInt64.MAX.

    Returns:
        The coefficientwise sum in the selected output context.

    Raises:
        PolyError: DOMAIN for invalid or incompatible input, or LIMIT/CAPACITY on resource limits.
    """
    var budget = Budget(max_steps)
    return add(a, b, budget, context=context)


def subtract[D: NumericDomain](a: NumericArray[D], b: NumericArray[D], mut budget: Budget, *, context: D.Context) raises PolyError -> NumericArray[D]:
    """Subtract numerical polynomials with explicit rounding.

    Parameters:
        D: The APN numerical domain associated with the stored scalars.

    Args:
        a: The first input value.
        b: The second input value.
        budget: The shared work allowance, including preparation, computation, and result storage.
        context: Explicit output precision, rounding settings, or ball working precision.

    Returns:
        The coefficientwise difference in the selected output context.

    Raises:
        PolyError: DOMAIN for invalid or incompatible input, or LIMIT/CAPACITY on resource limits.
    """
    _num._context[D](context, budget)
    var result = a._core[].sub(b._core[], context, budget)
    return NumericArray[D](result^, budget)


def subtract[D: NumericDomain](a: NumericArray[D], b: NumericArray[D], *, context: D.Context, max_steps: UInt64 = UInt64.MAX) raises PolyError -> NumericArray[D]:
    """Subtract numerical polynomials with explicit rounding.

    Parameters:
        D: The APN numerical domain associated with the stored scalars.

    Args:
        a: The first input value.
        b: The second input value.
        context: Explicit output precision, rounding settings, or ball working precision.
        max_steps: The complete call's work allowance; defaults to UInt64.MAX.

    Returns:
        The coefficientwise difference in the selected output context.

    Raises:
        PolyError: DOMAIN for invalid or incompatible input, or LIMIT/CAPACITY on resource limits.
    """
    var budget = Budget(max_steps)
    return subtract(a, b, budget, context=context)


def multiply[D: NumericDomain](a: NumericArray[D], b: NumericArray[D], mut budget: Budget, *, context: D.Context) raises PolyError -> NumericArray[D]:
    """Multiply numerical polynomials with explicit rounding.

    Parameters:
        D: The APN numerical domain associated with the stored scalars.

    Args:
        a: The first input value.
        b: The second input value.
        budget: The shared work allowance, including preparation, computation, and result storage.
        context: Explicit output precision, rounding settings, or ball working precision.

    Returns:
        The polynomial product in the selected output context.

    Raises:
        PolyError: DOMAIN for invalid or incompatible input, or LIMIT/CAPACITY on resource limits.
    """
    _num._context[D](context, budget)
    var result = a._core[].mul(b._core[], context, budget)
    return NumericArray[D](result^, budget)


def multiply[D: NumericDomain](a: NumericArray[D], b: NumericArray[D], *, context: D.Context, max_steps: UInt64 = UInt64.MAX) raises PolyError -> NumericArray[D]:
    """Multiply numerical polynomials with explicit rounding.

    Parameters:
        D: The APN numerical domain associated with the stored scalars.

    Args:
        a: The first input value.
        b: The second input value.
        context: Explicit output precision, rounding settings, or ball working precision.
        max_steps: The complete call's work allowance; defaults to UInt64.MAX.

    Returns:
        The polynomial product in the selected output context.

    Raises:
        PolyError: DOMAIN for invalid or incompatible input, or LIMIT/CAPACITY on resource limits.
    """
    var budget = Budget(max_steps)
    return multiply(a, b, budget, context=context)


def negative[D: NumericDomain](a: NumericArray[D], mut budget: Budget, *, context: D.Context) raises PolyError -> NumericArray[D]:
    """Negate numerical coefficients.

    Parameters:
        D: The APN numerical domain associated with the stored scalars.

    Args:
        a: The first input value.
        budget: The shared work allowance, including preparation, computation, and result storage.
        context: Explicit output precision, rounding settings, or ball working precision.

    Returns:
        The polynomial with negated coefficients.

    Raises:
        PolyError: DOMAIN for invalid or incompatible input, or LIMIT/CAPACITY on resource limits.
    """
    _num._context[D](context, budget)
    var result = a._core[].neg(context, budget)
    return NumericArray[D](result^, budget)


def negative[D: NumericDomain](a: NumericArray[D], *, context: D.Context, max_steps: UInt64 = UInt64.MAX) raises PolyError -> NumericArray[D]:
    """Negate numerical coefficients.

    Parameters:
        D: The APN numerical domain associated with the stored scalars.

    Args:
        a: The first input value.
        context: Explicit output precision, rounding settings, or ball working precision.
        max_steps: The complete call's work allowance; defaults to UInt64.MAX.

    Returns:
        The polynomial with negated coefficients.

    Raises:
        PolyError: DOMAIN for invalid or incompatible input, or LIMIT/CAPACITY on resource limits.
    """
    var budget = Budget(max_steps)
    return negative(a, budget, context=context)


def power[D: NumericDomain](a: NumericArray[D], exponent: Int, mut budget: Budget, *, context: D.Context) raises PolyError -> NumericArray[D]:
    """Raise a numerical polynomial to a nonnegative integer power.

    Parameters:
        D: The APN numerical domain associated with the stored scalars.

    Args:
        a: The first input value.
        exponent: A nonnegative integer exponent.
        budget: The shared work allowance, including preparation, computation, and result storage.
        context: Explicit output precision, rounding settings, or ball working precision.

    Returns:
        The requested nonnegative power.

    Raises:
        PolyError: DOMAIN for invalid or incompatible input, or LIMIT/CAPACITY on resource limits.
    """
    _num._context[D](context, budget)
    if exponent < 0:
        raise PolyError(PolyErrorKind.DOMAIN, "polynomial powers must be nonnegative")
    var result = a._core[].pow(UInt64(exponent), context, budget)
    return NumericArray[D](result^, budget)


def power[D: NumericDomain](a: NumericArray[D], exponent: Int, *, context: D.Context, max_steps: UInt64 = UInt64.MAX) raises PolyError -> NumericArray[D]:
    """Raise a numerical polynomial to a nonnegative integer power.

    Parameters:
        D: The APN numerical domain associated with the stored scalars.

    Args:
        a: The first input value.
        exponent: A nonnegative integer exponent.
        context: Explicit output precision, rounding settings, or ball working precision.
        max_steps: The complete call's work allowance; defaults to UInt64.MAX.

    Returns:
        The requested nonnegative power.

    Raises:
        PolyError: DOMAIN for invalid or incompatible input, or LIMIT/CAPACITY on resource limits.
    """
    var budget = Budget(max_steps)
    return power(a, exponent, budget, context=context)


def derivative[D: NumericDomain](a: NumericArray[D], mut budget: Budget, *, context: D.Context) raises PolyError -> NumericArray[D]:
    """Differentiate using the requested output precision.

    Parameters:
        D: The APN numerical domain associated with the stored scalars.

    Args:
        a: The first input value.
        budget: The shared work allowance, including preparation, computation, and result storage.
        context: Explicit output precision, rounding settings, or ball working precision.

    Returns:
        The derivative along the selected axis.

    Raises:
        PolyError: DOMAIN for invalid or incompatible input, or LIMIT/CAPACITY on resource limits.
    """
    _num._context[D](context, budget)
    var result = a._core[].derivative(context, budget)
    return NumericArray[D](result^, budget)


def derivative[D: NumericDomain](a: NumericArray[D], *, context: D.Context, max_steps: UInt64 = UInt64.MAX) raises PolyError -> NumericArray[D]:
    """Differentiate using the requested output precision.

    Parameters:
        D: The APN numerical domain associated with the stored scalars.

    Args:
        a: The first input value.
        context: Explicit output precision, rounding settings, or ball working precision.
        max_steps: The complete call's work allowance; defaults to UInt64.MAX.

    Returns:
        The derivative along the selected axis.

    Raises:
        PolyError: DOMAIN for invalid or incompatible input, or LIMIT/CAPACITY on resource limits.
    """
    var budget = Budget(max_steps)
    return derivative(a, budget, context=context)


def integral[D: NumericDomain](a: NumericArray[D], mut budget: Budget, *, context: D.Context) raises PolyError -> NumericArray[D]:
    """Integrate with zero integration constant and explicit rounding.

    Parameters:
        D: The APN numerical domain associated with the stored scalars.

    Args:
        a: The first input value.
        budget: The shared work allowance, including preparation, computation, and result storage.
        context: Explicit output precision, rounding settings, or ball working precision.

    Returns:
        An antiderivative with zero integration constant.

    Raises:
        PolyError: DOMAIN for invalid or incompatible input, or LIMIT/CAPACITY on resource limits.
    """
    _num._context[D](context, budget)
    var result = numeric_integrate_dense(a._core[], context, budget)
    return NumericArray[D](result^, budget)


def integral[D: NumericDomain](a: NumericArray[D], *, context: D.Context, max_steps: UInt64 = UInt64.MAX) raises PolyError -> NumericArray[D]:
    """Integrate with zero integration constant and explicit rounding.

    Parameters:
        D: The APN numerical domain associated with the stored scalars.

    Args:
        a: The first input value.
        context: Explicit output precision, rounding settings, or ball working precision.
        max_steps: The complete call's work allowance; defaults to UInt64.MAX.

    Returns:
        An antiderivative with zero integration constant.

    Raises:
        PolyError: DOMAIN for invalid or incompatible input, or LIMIT/CAPACITY on resource limits.
    """
    var budget = Budget(max_steps)
    return integral(a, budget, context=context)


def compose[D: NumericDomain](a: NumericArray[D], b: NumericArray[D], mut budget: Budget, *, context: D.Context) raises PolyError -> NumericArray[D]:
    """Compose numerical polynomials with explicit rounding.

    Parameters:
        D: The APN numerical domain associated with the stored scalars.

    Args:
        a: The first input value.
        b: The second input value.
        budget: The shared work allowance, including preparation, computation, and result storage.
        context: Explicit output precision, rounding settings, or ball working precision.

    Returns:
        The outer polynomial evaluated at the inner polynomial.

    Raises:
        PolyError: DOMAIN for invalid or incompatible input, or LIMIT/CAPACITY on resource limits.
    """
    _num._context[D](context, budget)
    var result = numeric_compose_dense(a._core[], b._core[], context, budget)
    return NumericArray[D](result^, budget)


def compose[D: NumericDomain](a: NumericArray[D], b: NumericArray[D], *, context: D.Context, max_steps: UInt64 = UInt64.MAX) raises PolyError -> NumericArray[D]:
    """Compose numerical polynomials with explicit rounding.

    Parameters:
        D: The APN numerical domain associated with the stored scalars.

    Args:
        a: The first input value.
        b: The second input value.
        context: Explicit output precision, rounding settings, or ball working precision.
        max_steps: The complete call's work allowance; defaults to UInt64.MAX.

    Returns:
        The outer polynomial evaluated at the inner polynomial.

    Raises:
        PolyError: DOMAIN for invalid or incompatible input, or LIMIT/CAPACITY on resource limits.
    """
    var budget = Budget(max_steps)
    return compose(a, b, budget, context=context)


def evaluate[D: NumericDomain, X: Copyable & Deinitable](a: NumericArray[D], x: X, mut budget: Budget, *, context: D.Context) raises PolyError -> D.Scalar:
    """Evaluate with Horner arithmetic in the requested context.

    Parameters:
        D: The APN numerical domain associated with the stored scalars.
        X: The evaluation point or seed type.

    Args:
        a: The first input value.
        x: The evaluation point.
        budget: The shared work allowance, including preparation, computation, and result storage.
        context: Explicit output precision, rounding settings, or ball working precision.

    Returns:
        The evaluated scalar; algebraic results retain the evaluation proof.

    Raises:
        PolyError: DOMAIN for invalid or incompatible input, or LIMIT/CAPACITY on resource limits.
    """
    _num._context[D](context, budget)
    var result = a._core[].evaluate(_num._value[D](x, context, budget), context, budget)
    return result^


def evaluate[D: NumericDomain, X: Copyable & Deinitable](a: NumericArray[D], x: X, *, context: D.Context, max_steps: UInt64 = UInt64.MAX) raises PolyError -> D.Scalar:
    """Evaluate with Horner arithmetic in the requested context.

    Parameters:
        D: The APN numerical domain associated with the stored scalars.
        X: The evaluation point or seed type.

    Args:
        a: The first input value.
        x: The evaluation point.
        context: Explicit output precision, rounding settings, or ball working precision.
        max_steps: The complete call's work allowance; defaults to UInt64.MAX.

    Returns:
        The evaluated scalar; algebraic results retain the evaluation proof.

    Raises:
        PolyError: DOMAIN for invalid or incompatible input, or LIMIT/CAPACITY on resource limits.
    """
    var budget = Budget(max_steps)
    return evaluate(a, x, budget, context=context)


from polynomials import serialize_dense, deserialize_dense, serialize_dense_to, deserialize_dense_from, PolynomialTextSink, PolynomialTextSource


def dumps[I: Iterable](values: I, mut budget: Budget) raises PolyError -> String where _Kind[_Element[I]] >= 0:
    """Write canonical versioned polynomial text.

    AA and QQbar retain their exact root witnesses, which are validated on load.
    Arithmetic history is not serialized. Other exact domains keep their existing format.

    Parameters:
        I: The inferred input iterable type.

    Args:
        values: Input coefficients, sparse terms, or prepared values as required by this overload.
        budget: The shared work allowance, including preparation, computation, and result storage.

    Returns:
        Canonical text including the final newline.

    Raises:
        PolyError: ENCODING for malformed or incompatible records, DOMAIN for invalid settings, or LIMIT/CAPACITY on resource limits.
    """
    var p = asarray(values, budget)
    comptime if _Kind[_Element[I]] >= 4:
        from . import _algebraic_io
        return _algebraic_io._dumps_dense(p._core[], budget)
    else:
        return serialize_dense(p._core[], budget)


def dumps[I: Iterable](values: I, *, max_steps: UInt64 = UInt64.MAX) raises PolyError -> String where _Kind[_Element[I]] >= 0:
    """Write canonical versioned polynomial text.

    AA and QQbar retain their exact root witnesses, which are validated on load.
    Arithmetic history is not serialized. Other exact domains keep their existing format.

    Parameters:
        I: The inferred input iterable type.

    Args:
        values: Input coefficients, sparse terms, or prepared values as required by this overload.
        max_steps: The complete call's work allowance; defaults to UInt64.MAX.

    Returns:
        Canonical text including the final newline.

    Raises:
        PolyError: ENCODING for malformed or incompatible records, DOMAIN for invalid settings, or LIMIT/CAPACITY on resource limits.
    """
    var budget = Budget(max_steps)
    return dumps[I](values, budget)


def dump[I: Iterable, S: PolynomialTextSink](values: I, mut sink: S, mut budget: Budget) raises PolyError where _Kind[_Element[I]] >= 0:
    """Write canonical versioned polynomial text in bounded chunks.

    AA and QQbar retain their exact root witnesses, which are validated on load.
    Arithmetic history is not serialized. Other exact domains keep their existing format.

    Parameters:
        I: The inferred input iterable type.
        S: The text transport implementation.

    Args:
        values: Input coefficients, sparse terms, or prepared values as required by this overload.
        sink: The destination for ordered text chunks.
        budget: The shared work allowance, including preparation, computation, and result storage.

    Raises:
        PolyError: ENCODING for malformed or incompatible records, DOMAIN for invalid settings, or LIMIT/CAPACITY on resource limits.
    """
    var p = asarray(values, budget)
    comptime if _Kind[_Element[I]] >= 4:
        from . import _algebraic_io
        _algebraic_io._dump_dense(p._core[], sink, budget)
    else:
        serialize_dense_to(p._core[], sink, budget)


def dump[I: Iterable, S: PolynomialTextSink](values: I, mut sink: S, *, max_steps: UInt64 = UInt64.MAX) raises PolyError where _Kind[_Element[I]] >= 0:
    """Write canonical versioned polynomial text.

    AA and QQbar retain their exact root witnesses, which are validated on load.
    Arithmetic history is not serialized. Other exact domains keep their existing format.

    Parameters:
        I: The inferred input iterable type.
        S: The text transport implementation.

    Args:
        values: Input coefficients, sparse terms, or prepared values as required by this overload.
        sink: The destination for ordered text chunks.
        max_steps: The complete call's work allowance; defaults to UInt64.MAX.

    Raises:
        PolyError: ENCODING for malformed or incompatible records, DOMAIN for invalid settings, or LIMIT/CAPACITY on resource limits.
    """
    var budget = Budget(max_steps)
    dump[I, S](values, sink, budget)


def loads[T: Copyable & Deinitable](text: String, mut budget: Budget, *, modulus: UInt64 = 0) raises PolyError -> Array[_Kind[T]]:
    """Read canonical text into an exact array; the scalar type selects the expected domain.

    AA and QQbar retain their exact root witnesses, which are validated on load.
    Arithmetic history is not serialized. Other exact domains keep their existing format.

    Parameters:
        T: The scalar or batch item type.

    Args:
        text: One canonical versioned polynomial record.
        budget: The shared work allowance, including preparation, computation, and result storage.
        modulus: The expected prime modulus for ModInt records; zero outside that domain.

    Returns:
        An exact array in the requested scalar domain.

    Raises:
        PolyError: ENCODING for malformed or incompatible records, DOMAIN for invalid settings, or LIMIT/CAPACITY on resource limits.
    """
    comptime k = _Kind[T]
    comptime assert k >= 0, "loads expects an exact coefficient type"
    var ctx = _Context[k]()
    if modulus:
        comptime if k != 3:
            raise PolyError(PolyErrorKind.DOMAIN, "modulus is only valid for ModInt")
        ctx.observe(modulus, budget)
    var core: DensePoly[_Ring[k]]
    comptime if k >= 4:
        from . import _algebraic_io
        core = _algebraic_io._loads_dense[_Ring[k]](text, budget)
    else:
        core = deserialize_dense[_Ring[k]](text, ctx.get(), budget)
    return rebind_var[Array[k]](from_core(core, budget))


def loads[T: Copyable & Deinitable](text: String, *, max_steps: UInt64 = UInt64.MAX, modulus: UInt64 = 0) raises PolyError -> Array[_Kind[T]]:
    """Read canonical text into an exact array with one shared work limit.

    AA and QQbar retain their exact root witnesses, which are validated on load.
    Arithmetic history is not serialized. Other exact domains keep their existing format.

    Parameters:
        T: The scalar or batch item type.

    Args:
        text: One canonical versioned polynomial record.
        max_steps: The complete call's work allowance; defaults to UInt64.MAX.
        modulus: The expected prime modulus for ModInt records; zero outside that domain.

    Returns:
        An exact array in the requested scalar domain.

    Raises:
        PolyError: ENCODING for malformed or incompatible records, DOMAIN for invalid settings, or LIMIT/CAPACITY on resource limits.
    """
    var budget = Budget(max_steps)
    return loads[T](text, budget, modulus=modulus)


def load[T: Copyable & Deinitable, S: PolynomialTextSource](var source: S, mut budget: Budget, *, modulus: UInt64 = 0, max_field_bytes: Int = 16777216) raises PolyError -> Array[_Kind[T]]:
    """Read canonical text into an exact array; the scalar type selects the expected domain.

    AA and QQbar retain their exact root witnesses, which are validated on load.
    Arithmetic history is not serialized. Other exact domains keep their existing format.

    Parameters:
        T: The scalar or batch item type.
        S: The text transport implementation.

    Args:
        source: An owned source of arbitrary text chunks.
        budget: The shared work allowance, including preparation, computation, and result storage.
        modulus: The expected prime modulus for ModInt records; zero outside that domain.
        max_field_bytes: Maximum bytes in one input field; defaults to 16 MiB.

    Returns:
        An exact array decoded from the text stream.

    Raises:
        PolyError: ENCODING for malformed or incompatible records, DOMAIN for invalid settings, or LIMIT/CAPACITY on resource limits.
    """
    comptime k = _Kind[T]
    comptime assert k >= 0, "loads expects an exact coefficient type"
    var ctx = _Context[k]()
    if modulus:
        comptime if k != 3:
            raise PolyError(PolyErrorKind.DOMAIN, "modulus is only valid for ModInt")
        ctx.observe(modulus, budget)
    var core: DensePoly[_Ring[k]]
    comptime if k >= 4:
        from . import _algebraic_io
        core = _algebraic_io._load_dense[_Ring[k]](source^, budget, max_field_bytes)
    else:
        core = deserialize_dense_from[_Ring[k]](source^, ctx.get(), budget, max_field_bytes=max_field_bytes)
    return rebind_var[Array[k]](from_core(core, budget))


def load[T: Copyable & Deinitable, S: PolynomialTextSource](var source: S, *, max_steps: UInt64 = UInt64.MAX, modulus: UInt64 = 0, max_field_bytes: Int = 16777216) raises PolyError -> Array[_Kind[T]]:
    """Read canonical text into an exact array with one shared work limit.

    AA and QQbar retain their exact root witnesses, which are validated on load.
    Arithmetic history is not serialized. Other exact domains keep their existing format.

    Parameters:
        T: The scalar or batch item type.
        S: The text transport implementation.

    Args:
        source: An owned source of arbitrary text chunks.
        max_steps: The complete call's work allowance; defaults to UInt64.MAX.
        modulus: The expected prime modulus for ModInt records; zero outside that domain.
        max_field_bytes: Maximum bytes in one input field; defaults to 16 MiB.

    Returns:
        An exact array decoded from the text stream.

    Raises:
        PolyError: ENCODING for malformed or incompatible records, DOMAIN for invalid settings, or LIMIT/CAPACITY on resource limits.
    """
    var budget = Budget(max_steps)
    return load[T, S](source^, budget, modulus=modulus, max_field_bytes=max_field_bytes)

from polynomials import serialize_numeric_dense, deserialize_numeric_dense


def dumps[D: NumericDomain](values: NumericArray[D], mut budget: Budget) raises PolyError -> String:
    """Serialize numerical coefficients with their stored precision and enclosures.

    Parameters:
        D: The APN numerical domain associated with the stored scalars.

    Args:
        values: Input coefficients, sparse terms, or prepared values as required by this overload.
        budget: The shared work allowance, including preparation, computation, and result storage.

    Returns:
        Canonical text including the final newline.

    Raises:
        PolyError: ENCODING for malformed or incompatible records, DOMAIN for invalid settings, or LIMIT/CAPACITY on resource limits.
    """
    return serialize_numeric_dense(values._core[], budget)


def dumps[D: NumericDomain](values: NumericArray[D], *, max_steps: UInt64 = UInt64.MAX) raises PolyError -> String:
    """Serialize numerical coefficients with their stored precision and enclosures.

    Parameters:
        D: The APN numerical domain associated with the stored scalars.

    Args:
        values: Input coefficients, sparse terms, or prepared values as required by this overload.
        max_steps: The complete call's work allowance; defaults to UInt64.MAX.

    Returns:
        Canonical text including the final newline.

    Raises:
        PolyError: ENCODING for malformed or incompatible records, DOMAIN for invalid settings, or LIMIT/CAPACITY on resource limits.
    """
    var budget = Budget(max_steps)
    return dumps[D](values, budget)


def loads_numeric[T: Copyable & Deinitable](text: String, mut budget: Budget) raises PolyError -> NumericArray[_num._StoredDomain[T]]:
    """Restore stored numerical values exactly; subsequent arithmetic takes an explicit context.

    Parameters:
        T: The scalar or batch item type.

    Args:
        text: One canonical versioned polynomial record.
        budget: The shared work allowance, including preparation, computation, and result storage.

    Returns:
        A numerical array preserving the encoded scalar precision and enclosures.

    Raises:
        PolyError: ENCODING for malformed or incompatible records, DOMAIN for invalid settings, or LIMIT/CAPACITY on resource limits.
    """
    comptime assert T == _num.Float or T == _num.Complex or T == _num.Ball or T == _num.ComplexBall, "loads_numeric expects Float, Complex, Ball, or ComplexBall"
    comptime D = _num._StoredDomain[T]
    var core = deserialize_numeric_dense[D](text, budget)
    core.variable = 0
    return NumericArray[_num._StoredDomain[T]](core^, budget)


def loads_numeric[T: Copyable & Deinitable](text: String, *, max_steps: UInt64 = UInt64.MAX) raises PolyError -> NumericArray[_num._StoredDomain[T]]:
    """Restore stored numerical values exactly; subsequent arithmetic takes an explicit context.

    Parameters:
        T: The scalar or batch item type.

    Args:
        text: One canonical versioned polynomial record.
        max_steps: The complete call's work allowance; defaults to UInt64.MAX.

    Returns:
        A numerical array preserving the encoded scalar precision and enclosures.

    Raises:
        PolyError: ENCODING for malformed or incompatible records, DOMAIN for invalid settings, or LIMIT/CAPACITY on resource limits.
    """
    var budget = Budget(max_steps)
    return loads_numeric[T](text, budget)


from . import algebraic as _alg


def to_core[D: NumericDomain](values: NumericArray[D], mut budget: Budget, *, variable: Int64 = 0) raises PolyError -> NumericDensePoly[D]:
    """Copy the numerical array into independently mutable core storage.

    Parameters:
        D: The APN numerical domain associated with the stored scalars.

    Args:
        values: Input coefficients, sparse terms, or prepared values as required by this overload.
        budget: The shared work allowance, including preparation, computation, and result storage.
        variable: The core variable ID assigned to the exported polynomial.

    Returns:
        An independent mutable core polynomial.

    Raises:
        PolyError: DOMAIN for invalid or incompatible input, or LIMIT/CAPACITY on resource limits.
    """
    return _ni._dense(values._core[], variable, budget)


def to_core[D: NumericDomain](values: NumericArray[D], *, max_steps: UInt64 = UInt64.MAX, variable: Int64 = 0) raises PolyError -> NumericDensePoly[D]:
    """Copy the numerical array into independently mutable core storage.

    Parameters:
        D: The APN numerical domain associated with the stored scalars.

    Args:
        values: Input coefficients, sparse terms, or prepared values as required by this overload.
        max_steps: The complete call's work allowance; defaults to UInt64.MAX.
        variable: The core variable ID assigned to the exported polynomial.

    Returns:
        An independent mutable core polynomial.

    Raises:
        PolyError: DOMAIN for invalid or incompatible input, or LIMIT/CAPACITY on resource limits.
    """
    var budget = Budget(max_steps)
    return to_core[D](values, budget, variable=variable)


def from_core[D: NumericDomain](values: NumericDensePoly[D], mut budget: Budget) raises PolyError -> NumericArray[D]:
    """Validate and copy a numerical core polynomial without rounding its stored values.

    Parameters:
        D: The APN numerical domain associated with the stored scalars.

    Args:
        values: Input coefficients, sparse terms, or prepared values as required by this overload.
        budget: The shared work allowance, including preparation, computation, and result storage.

    Returns:
        A validated immutable array with copied coefficient storage.

    Raises:
        PolyError: DOMAIN for invalid or incompatible input, or LIMIT/CAPACITY on resource limits.
    """
    return NumericArray[D](_ni._dense(values, 0, budget), budget)


def from_core[D: NumericDomain](values: NumericDensePoly[D], *, max_steps: UInt64 = UInt64.MAX) raises PolyError -> NumericArray[D]:
    """Validate and copy a numerical core polynomial without rounding its stored values.

    Parameters:
        D: The APN numerical domain associated with the stored scalars.

    Args:
        values: Input coefficients, sparse terms, or prepared values as required by this overload.
        max_steps: The complete call's work allowance; defaults to UInt64.MAX.

    Returns:
        A validated immutable array with copied coefficient storage.

    Raises:
        PolyError: DOMAIN for invalid or incompatible input, or LIMIT/CAPACITY on resource limits.
    """
    var budget = Budget(max_steps)
    return from_core[D](values, budget)


def degree_bound[D: NumericDomain](values: NumericArray[D], mut budget: Budget) raises PolyError -> Int:
    """Return the stored degree bound.

    Parameters:
        D: The APN numerical domain associated with the stored scalars.

    Args:
        values: Input coefficients, sparse terms, or prepared values as required by this overload.
        budget: The shared work allowance, including preparation, computation, and result storage.

    Returns:
        The largest possible degree, or minus one for zero.

    Raises:
        PolyError: DOMAIN for invalid or incompatible input, or LIMIT/CAPACITY on resource limits.
    """
    budget.charge(1)
    return values._core[].degree_bound()


def degree_bound[D: NumericDomain](values: NumericArray[D], *, max_steps: UInt64 = UInt64.MAX) raises PolyError -> Int:
    """Inspect the polynomial degree with a shared work allowance.

    Parameters:
        D: The APN numerical domain associated with the stored scalars.

    Args:
        values: Input coefficients, sparse terms, or prepared values as required by this overload.
        max_steps: The complete call's work allowance; defaults to UInt64.MAX.

    Returns:
        The largest possible degree, or minus one for zero.

    Raises:
        PolyError: DOMAIN for invalid or incompatible input, or LIMIT/CAPACITY on resource limits.
    """
    var budget = Budget(max_steps)
    return degree_bound(values, budget)


def certified_degree[D: NumericDomain](values: NumericArray[D], mut budget: Budget) raises PolyError -> Optional[Int]:
    """Return a common degree for every represented polynomial, or None when uncertain.

    Parameters:
        D: The APN numerical domain associated with the stored scalars.

    Args:
        values: Input coefficients, sparse terms, or prepared values as required by this overload.
        budget: The shared work allowance, including preparation, computation, and result storage.

    Returns:
        A common degree for every represented polynomial, or None if uncertain.

    Raises:
        PolyError: DOMAIN for invalid or incompatible input, or LIMIT/CAPACITY on resource limits.
    """
    budget.charge(1)
    return values._core[].certified_degree(budget)


def certified_degree[D: NumericDomain](values: NumericArray[D], *, max_steps: UInt64 = UInt64.MAX) raises PolyError -> Optional[Int]:
    """Inspect the polynomial degree with a shared work allowance.

    Parameters:
        D: The APN numerical domain associated with the stored scalars.

    Args:
        values: Input coefficients, sparse terms, or prepared values as required by this overload.
        max_steps: The complete call's work allowance; defaults to UInt64.MAX.

    Returns:
        A common degree for every represented polynomial, or None if uncertain.

    Raises:
        PolyError: DOMAIN for invalid or incompatible input, or LIMIT/CAPACITY on resource limits.
    """
    var budget = Budget(max_steps)
    return certified_degree(values, budget)


def real_root_cover[D: NumericDomain](values: NumericArray[D], mut budget: Budget, *, options: NumericOptions = NumericOptions(), complete_only: Bool = False) raises PolyError -> _roots.NumericCover[D, False]:
    """Enclose roots of numerical coefficients, retaining all unresolved outcomes.

    Parameters:
        D: The APN numerical domain associated with the stored scalars.

    Args:
        values: Input coefficients, sparse terms, or prepared values as required by this overload.
        budget: The shared work allowance, including preparation, computation, and result storage.
        options: Precision, accuracy, isolation, and subdivision requirements.
        complete_only: Raise unless all requested numerical guarantees are established.

    Returns:
        Real cells with completeness, isolation, and accuracy status.

    Raises:
        PolyError: DOMAIN for invalid or incompatible input, or LIMIT/CAPACITY on resource limits.
    """
    var proof = _roots.real_roots_numeric(values._core[], options, budget, complete_only=complete_only)
    _allocation[_roots._NumericProof[False]](1, budget)
    return _roots.NumericCover[D, False](values.copy(), options, ArcPointer(proof^))


def real_root_cover[D: NumericDomain](values: NumericArray[D], *, max_steps: UInt64 = UInt64.MAX, options: NumericOptions = NumericOptions(), complete_only: Bool = False) raises PolyError -> _roots.NumericCover[D, False]:
    """Compute a numerical root cover with explicit precision and subdivision settings.

    Parameters:
        D: The APN numerical domain associated with the stored scalars.

    Args:
        values: Input coefficients, sparse terms, or prepared values as required by this overload.
        max_steps: The complete call's work allowance; defaults to UInt64.MAX.
        options: Precision, accuracy, isolation, and subdivision requirements.
        complete_only: Raise unless all requested numerical guarantees are established.

    Returns:
        Real cells with completeness, isolation, and accuracy status.

    Raises:
        PolyError: DOMAIN for invalid or incompatible input, or LIMIT/CAPACITY on resource limits.
    """
    var budget = Budget(max_steps)
    return real_root_cover[D](values, budget, options=options, complete_only=complete_only)


def complex_root_cover[D: NumericDomain](values: NumericArray[D], mut budget: Budget, *, options: NumericOptions = NumericOptions(), complete_only: Bool = False) raises PolyError -> _roots.NumericCover[D, True]:
    """Enclose roots of numerical coefficients, retaining all unresolved outcomes.

    Parameters:
        D: The APN numerical domain associated with the stored scalars.

    Args:
        values: Input coefficients, sparse terms, or prepared values as required by this overload.
        budget: The shared work allowance, including preparation, computation, and result storage.
        options: Precision, accuracy, isolation, and subdivision requirements.
        complete_only: Raise unless all requested numerical guarantees are established.

    Returns:
        Complex rectangles with root counts and explicit unresolved outcomes.

    Raises:
        PolyError: DOMAIN for invalid or incompatible input, or LIMIT/CAPACITY on resource limits.
    """
    var proof = _roots.complex_roots_numeric(values._core[], options, budget, complete_only=complete_only)
    _allocation[_roots._NumericProof[True]](1, budget)
    return _roots.NumericCover[D, True](values.copy(), options, ArcPointer(proof^))


def complex_root_cover[D: NumericDomain](values: NumericArray[D], *, max_steps: UInt64 = UInt64.MAX, options: NumericOptions = NumericOptions(), complete_only: Bool = False) raises PolyError -> _roots.NumericCover[D, True]:
    """Compute a numerical root cover with explicit precision and subdivision settings.

    Parameters:
        D: The APN numerical domain associated with the stored scalars.

    Args:
        values: Input coefficients, sparse terms, or prepared values as required by this overload.
        max_steps: The complete call's work allowance; defaults to UInt64.MAX.
        options: Precision, accuracy, isolation, and subdivision requirements.
        complete_only: Raise unless all requested numerical guarantees are established.

    Returns:
        Complex rectangles with root counts and explicit unresolved outcomes.

    Raises:
        PolyError: DOMAIN for invalid or incompatible input, or LIMIT/CAPACITY on resource limits.
    """
    var budget = Budget(max_steps)
    return complex_root_cover[D](values, budget, options=options, complete_only=complete_only)


comptime _Evaluation[I: Iterable, X: Movable] = _Scalar[_Join[_Kind[_Element[I]], _Kind[X]]]



def asarray[Context: Copyable & Deinitable, *Ts: Copyable & Deinitable](values: Tuple[*Ts], mut budget: Budget, *, context: Context) raises PolyError -> NumericArray[_num._Domain[Context, _num._TupleScalar[Tuple[*Ts]]]]:
    """Convert a mixed scalar tuple using an explicit real, complex, or ball context.

    Parameters:
        Context: The explicit APN arithmetic context type.
        Ts: The inferred tuple element types.

    Args:
        values: Input coefficients, sparse terms, or prepared values as required by this overload.
        budget: The shared work allowance, including preparation, computation, and result storage.
        context: Explicit output precision, rounding settings, or ball working precision.

    Returns:
        An immutable prepared array in the selected domain or batch shape.

    Raises:
        PolyError: DOMAIN for invalid or incompatible input, or LIMIT/CAPACITY on resource limits.
    """
    comptime assert Context == _num.ArithmeticContext or Context == _num.ComplexContext or Context == _num.BallContext, "choose ArithmeticContext, ComplexContext, or BallContext"
    comptime D = _num._Domain[Context, _num._TupleScalar[Tuple[*Ts]]]
    var ctx = rebind[D.Context](context).copy()
    _num._context[D](ctx, budget)
    _allocation[D.Scalar](Tuple[*Ts].Ts.length, budget)
    var coefficients = List[D.Scalar](capacity=Tuple[*Ts].Ts.length)
    comptime for i in range(Tuple[*Ts].Ts.length):
        budget.charge(1)
        coefficients.append(_num._value[D](values[i], ctx, budget))
    return NumericArray[D](NumericDensePoly[D].from_coefficients(0, coefficients^, budget), budget)


def asarray[Context: Copyable & Deinitable, *Ts: Copyable & Deinitable](values: Tuple[*Ts], *, context: Context, max_steps: UInt64 = UInt64.MAX) raises PolyError -> NumericArray[_num._Domain[Context, _num._TupleScalar[Tuple[*Ts]]]]:
    """Construct numerical coefficients from a mixed tuple without implicit precision choices.

    Parameters:
        Context: The explicit APN arithmetic context type.
        Ts: The inferred tuple element types.

    Args:
        values: Input coefficients, sparse terms, or prepared values as required by this overload.
        context: Explicit output precision, rounding settings, or ball working precision.
        max_steps: The complete call's work allowance; defaults to UInt64.MAX.

    Returns:
        An immutable prepared array in the selected domain or batch shape.

    Raises:
        PolyError: DOMAIN for invalid or incompatible input, or LIMIT/CAPACITY on resource limits.
    """
    var budget = Budget(max_steps)
    return asarray[Context, *Ts](values, budget, context=context)


from polynomials import numeric_divmod, check_numeric_division, numeric_interpolate, numeric_hermite_interpolate, numeric_multipoint_evaluate, numeric_affine_transform, numeric_taylor_shift, numeric_jet_evaluate, numeric_definite_integral


def divmod[D: NumericDomain](a: NumericArray[D], b: NumericArray[D], mut budget: Budget, *, context: D.Context) raises PolyError -> Tuple[NumericArray[D], NumericArray[D]]:
    """Divide numerical polynomials into quotient and remainder.

    Ball divisors must have a leading coefficient excluding zero. Rounded division may have a nonzero residual; use divide_checked to retain its evidence.

    Parameters:
        D: The numerical coefficient domain.

    Args:
        a: The first prepared value.
        b: The second prepared value.
        budget: The shared work allowance.
        context: Explicit output precision and rounding or enclosure settings.

    Returns:
        The numerical quotient and remainder in that order.

    Raises:
        PolyError: DOMAIN for invalid input, or LIMIT/CAPACITY on resource limits.
    """
    _num._context[D](context, budget)
    var result = numeric_divmod(a._core[], b._core[], context, budget)
    var quotient = NumericDensePoly[D]()
    var remainder = NumericDensePoly[D]()
    swap(quotient, result.quotient)
    swap(remainder, result.remainder)
    return NumericArray[D](quotient^, budget), NumericArray[D](remainder^, budget)


def divmod[D: NumericDomain](a: NumericArray[D], b: NumericArray[D], *, context: D.Context, max_steps: UInt64 = UInt64.MAX) raises PolyError -> Tuple[NumericArray[D], NumericArray[D]]:
    """Divide numerical polynomials into quotient and remainder.

    Ball divisors must have a leading coefficient excluding zero. Rounded division may have a nonzero residual; use divide_checked to retain its evidence.

    Parameters:
        D: The numerical coefficient domain.

    Args:
        a: The first prepared value.
        b: The second prepared value.
        context: Explicit output precision and rounding or enclosure settings.
        max_steps: The complete call's work allowance.

    Returns:
        The numerical quotient and remainder in that order.

    Raises:
        PolyError: DOMAIN for invalid input, or LIMIT/CAPACITY on resource limits.
    """
    var budget = Budget(max_steps)
    return divmod(a, b, budget, context=context)


def affine_transform[D: NumericDomain, X: Copyable & Deinitable, Y: Copyable & Deinitable](values: NumericArray[D], scale: X, shift: Y, mut budget: Budget, *, context: D.Context) raises PolyError -> NumericArray[D]:
    """Return p(scale*x + shift) at the requested precision.

    Parameters:
        D: The numerical coefficient domain.
        X: Inferred from the input types.
        Y: Inferred from the input types.

    Args:
        values: Coefficients, terms, or a prepared value.
        scale: The affine scale.
        shift: The affine shift.
        budget: The shared work allowance.
        context: Explicit output precision and rounding or enclosure settings.

    Returns:
        The numerical polynomial in the same representation and variable layout.

    Raises:
        PolyError: DOMAIN for invalid input, or LIMIT/CAPACITY on resource limits.
    """
    _num._context[D](context, budget)
    var result = numeric_affine_transform(values._core[], _num._value[D](scale, context, budget), _num._value[D](shift, context, budget), context, budget)
    return NumericArray[D](result^, budget)


def affine_transform[D: NumericDomain, X: Copyable & Deinitable, Y: Copyable & Deinitable](values: NumericArray[D], scale: X, shift: Y, *, context: D.Context, max_steps: UInt64 = UInt64.MAX) raises PolyError -> NumericArray[D]:
    """Return p(scale*x + shift) at the requested precision.

    Parameters:
        D: The numerical coefficient domain.
        X: Inferred from the input types.
        Y: Inferred from the input types.

    Args:
        values: Coefficients, terms, or a prepared value.
        scale: The affine scale.
        shift: The affine shift.
        context: Explicit output precision and rounding or enclosure settings.
        max_steps: The complete call's work allowance.

    Returns:
        The numerical polynomial in the same representation and variable layout.

    Raises:
        PolyError: DOMAIN for invalid input, or LIMIT/CAPACITY on resource limits.
    """
    var budget = Budget(max_steps)
    return affine_transform(values, scale, shift, budget, context=context)


def taylor_shift[D: NumericDomain, X: Copyable & Deinitable](values: NumericArray[D], point: X, mut budget: Budget, *, context: D.Context) raises PolyError -> NumericArray[D]:
    """Return p(x + point) at the requested precision.

    Parameters:
        D: The numerical coefficient domain.
        X: Inferred from the input types.

    Args:
        values: Coefficients, terms, or a prepared value.
        point: The evaluation or expansion point.
        budget: The shared work allowance.
        context: Explicit output precision and rounding or enclosure settings.

    Returns:
        The numerical polynomial in the same representation and variable layout.

    Raises:
        PolyError: DOMAIN for invalid input, or LIMIT/CAPACITY on resource limits.
    """
    _num._context[D](context, budget)
    var result = numeric_taylor_shift(values._core[], _num._value[D](point, context, budget), context, budget)
    return NumericArray[D](result^, budget)


def taylor_shift[D: NumericDomain, X: Copyable & Deinitable](values: NumericArray[D], point: X, *, context: D.Context, max_steps: UInt64 = UInt64.MAX) raises PolyError -> NumericArray[D]:
    """Return p(x + point) at the requested precision.

    Parameters:
        D: The numerical coefficient domain.
        X: Inferred from the input types.

    Args:
        values: Coefficients, terms, or a prepared value.
        point: The evaluation or expansion point.
        context: Explicit output precision and rounding or enclosure settings.
        max_steps: The complete call's work allowance.

    Returns:
        The numerical polynomial in the same representation and variable layout.

    Raises:
        PolyError: DOMAIN for invalid input, or LIMIT/CAPACITY on resource limits.
    """
    var budget = Budget(max_steps)
    return taylor_shift(values, point, budget, context=context)


def jet_evaluate[D: NumericDomain, X: Copyable & Deinitable](values: NumericArray[D], point: X, order: Int, mut budget: Budget, *, context: D.Context) raises PolyError -> _num.Values[D]:
    """Return consecutive Taylor coefficients at a point, retaining zeros.

    Parameters:
        D: The numerical coefficient domain.
        X: Inferred from the input types.

    Args:
        values: Coefficients, terms, or a prepared value.
        point: The evaluation or expansion point.
        order: The number of retained coefficients.
        budget: The shared work allowance.
        context: Explicit output precision and rounding or enclosure settings.

    Returns:
        A numerical sequence retaining every entry, including zeros.

    Raises:
        PolyError: DOMAIN for invalid input, or LIMIT/CAPACITY on resource limits.
    """
    _num._context[D](context, budget)
    var result = numeric_jet_evaluate(values._core[], _num._value[D](point, context, budget), order, context, budget)
    return _num.Values[D](result^, budget)


def jet_evaluate[D: NumericDomain, X: Copyable & Deinitable](values: NumericArray[D], point: X, order: Int, *, context: D.Context, max_steps: UInt64 = UInt64.MAX) raises PolyError -> _num.Values[D]:
    """Return consecutive Taylor coefficients at a point, retaining zeros.

    Parameters:
        D: The numerical coefficient domain.
        X: Inferred from the input types.

    Args:
        values: Coefficients, terms, or a prepared value.
        point: The evaluation or expansion point.
        order: The number of retained coefficients.
        context: Explicit output precision and rounding or enclosure settings.
        max_steps: The complete call's work allowance.

    Returns:
        A numerical sequence retaining every entry, including zeros.

    Raises:
        PolyError: DOMAIN for invalid input, or LIMIT/CAPACITY on resource limits.
    """
    var budget = Budget(max_steps)
    return jet_evaluate(values, point, order, budget, context=context)


def definite_integral[D: NumericDomain, X: Copyable & Deinitable, Y: Copyable & Deinitable](values: NumericArray[D], low: X, high: Y, mut budget: Budget, *, context: D.Context) raises PolyError -> D.Scalar:
    """Integrate between explicit numerical endpoints.

    Parameters:
        D: The numerical coefficient domain.
        X: Inferred from the input types.
        Y: Inferred from the input types.

    Args:
        values: Coefficients, terms, or a prepared value.
        low: The lower integration endpoint.
        high: The upper integration endpoint.
        budget: The shared work allowance.
        context: Explicit output precision and rounding or enclosure settings.

    Returns:
        The rounded value or enclosing scalar.

    Raises:
        PolyError: DOMAIN for invalid input, or LIMIT/CAPACITY on resource limits.
    """
    _num._context[D](context, budget)
    var result = numeric_definite_integral(values._core[], _num._value[D](low, context, budget), _num._value[D](high, context, budget), context, budget)
    return result^


def definite_integral[D: NumericDomain, X: Copyable & Deinitable, Y: Copyable & Deinitable](values: NumericArray[D], low: X, high: Y, *, context: D.Context, max_steps: UInt64 = UInt64.MAX) raises PolyError -> D.Scalar:
    """Integrate between explicit numerical endpoints.

    Parameters:
        D: The numerical coefficient domain.
        X: Inferred from the input types.
        Y: Inferred from the input types.

    Args:
        values: Coefficients, terms, or a prepared value.
        low: The lower integration endpoint.
        high: The upper integration endpoint.
        context: Explicit output precision and rounding or enclosure settings.
        max_steps: The complete call's work allowance.

    Returns:
        The rounded value or enclosing scalar.

    Raises:
        PolyError: DOMAIN for invalid input, or LIMIT/CAPACITY on resource limits.
    """
    var budget = Budget(max_steps)
    return definite_integral(values, low, high, budget, context=context)


def evaluate_many[D: NumericDomain, I: Iterable](values: NumericArray[D], points: I, mut budget: Budget, *, context: D.Context) raises PolyError -> _num.Values[D]:
    """Evaluate at each point in input order, retaining every zero.

    Parameters:
        D: The numerical coefficient domain.
        I: Inferred from the input types.

    Args:
        values: Coefficients, terms, or a prepared value.
        points: A finite sequence of points, preserving every zero.
        budget: The shared work allowance.
        context: Explicit output precision and rounding or enclosure settings.

    Returns:
        A numerical sequence retaining every entry, including zeros.

    Raises:
        PolyError: DOMAIN for invalid input, or LIMIT/CAPACITY on resource limits.
    """
    var prepared = _num._sequence[D](points, context, budget)
    var result = numeric_multipoint_evaluate(values._core[], prepared, context, budget)
    return _num.Values[D](result^, budget)


def evaluate_many[D: NumericDomain, I: Iterable](values: NumericArray[D], points: I, *, context: D.Context, max_steps: UInt64 = UInt64.MAX) raises PolyError -> _num.Values[D]:
    """Evaluate at each point in input order, retaining every zero.

    Parameters:
        D: The numerical coefficient domain.
        I: Inferred from the input types.

    Args:
        values: Coefficients, terms, or a prepared value.
        points: A finite sequence of points, preserving every zero.
        context: Explicit output precision and rounding or enclosure settings.
        max_steps: The complete call's work allowance.

    Returns:
        A numerical sequence retaining every entry, including zeros.

    Raises:
        PolyError: DOMAIN for invalid input, or LIMIT/CAPACITY on resource limits.
    """
    var budget = Budget(max_steps)
    return evaluate_many(values, points, budget, context=context)


def interpolate[I: Iterable, J: Iterable, Context: Copyable & Deinitable](points: I, samples: J, mut budget: Budget, *, context: Context) raises PolyError -> NumericArray[_num._Domain[Context, _num._CombinedScalar[_Element[I], _Element[J]]]]:
    """Interpolate numerical samples with explicit precision.

    Ball nodes must be pairwise separated. Floating-point coefficients are rounded; ball coefficients enclose every interpolant allowed by the data.

    Parameters:
        I: Inferred from the input types.
        J: Inferred from the input types.
        Context: Inferred from the input types.

    Args:
        points: A finite sequence of points, preserving every zero.
        samples: Values in the same order as the points.
        budget: The shared work allowance.
        context: Explicit output precision and rounding or enclosure settings.

    Returns:
        The numerical polynomial in the same representation and variable layout.

    Raises:
        PolyError: DOMAIN for invalid input, or LIMIT/CAPACITY on resource limits.
    """
    comptime D = _num._Domain[Context, _num._CombinedScalar[_Element[I], _Element[J]]]
    var x = _num._sequence[D](points, rebind[D.Context](context), budget)
    var y = _num._sequence[D](samples, rebind[D.Context](context), budget)
    var result = numeric_interpolate[D](0, x, y, rebind[D.Context](context), budget)
    return NumericArray[D](result^, budget)


def interpolate[I: Iterable, J: Iterable, Context: Copyable & Deinitable](points: I, samples: J, *, context: Context, max_steps: UInt64 = UInt64.MAX) raises PolyError -> NumericArray[_num._Domain[Context, _num._CombinedScalar[_Element[I], _Element[J]]]]:
    """Interpolate numerical samples with explicit precision.

    Ball nodes must be pairwise separated. Floating-point coefficients are rounded; ball coefficients enclose every interpolant allowed by the data.

    Parameters:
        I: Inferred from the input types.
        J: Inferred from the input types.
        Context: Inferred from the input types.

    Args:
        points: A finite sequence of points, preserving every zero.
        samples: Values in the same order as the points.
        context: Explicit output precision and rounding or enclosure settings.
        max_steps: The complete call's work allowance.

    Returns:
        The numerical polynomial in the same representation and variable layout.

    Raises:
        PolyError: DOMAIN for invalid input, or LIMIT/CAPACITY on resource limits.
    """
    var budget = Budget(max_steps)
    return interpolate(points, samples, budget, context=context)


def hermite_interpolate[I: Iterable, J: Iterable, Context: Copyable & Deinitable](points: I, jets: J, mut budget: Budget, *, context: Context, derivatives: Bool = True) raises PolyError -> NumericArray[_num._Domain[Context, _num._CombinedScalar[_Element[I], _Element[downcast[_Element[J], Iterable]]]]]:
    """Interpolate values and consecutive derivative constraints.

    Parameters:
        I: Inferred from the input types.
        J: Inferred from the input types.
        Context: Inferred from the input types.

    Args:
        points: A finite sequence of points, preserving every zero.
        jets: Consecutive value and derivative constraints at each point.
        budget: The shared work allowance.
        context: Explicit output precision and rounding or enclosure settings.
        derivatives: True for raw derivatives; false for Taylor coefficients.

    Returns:
        The numerical polynomial in the same representation and variable layout.

    Raises:
        PolyError: DOMAIN for invalid input, or LIMIT/CAPACITY on resource limits.
    """
    comptime Row = downcast[_Element[J], Iterable & Copyable & Deinitable]
    comptime D = _num._Domain[Context, _num._CombinedScalar[_Element[I], _Element[Row]]]
    var x = _num._sequence[D](points, rebind[D.Context](context), budget)
    var rows = List[List[D.Scalar]]()
    var cursor = iter(jets)
    while True:
        budget.charge(1)
        var row: Row
        try:
            row = rebind_var[Row](next(cursor))
        except StopIteration:
            break
        _grow(rows, budget)
        rows.append(_num._sequence[D](row, rebind[D.Context](context), budget))
    var result = numeric_hermite_interpolate[D](0, x, rows, rebind[D.Context](context), budget, derivatives=derivatives)
    return NumericArray[D](result^, budget)


def hermite_interpolate[I: Iterable, J: Iterable, Context: Copyable & Deinitable](points: I, jets: J, *, context: Context, derivatives: Bool = True, max_steps: UInt64 = UInt64.MAX) raises PolyError -> NumericArray[_num._Domain[Context, _num._CombinedScalar[_Element[I], _Element[downcast[_Element[J], Iterable]]]]]:
    """Interpolate values and consecutive derivative constraints.

    Parameters:
        I: Inferred from the input types.
        J: Inferred from the input types.
        Context: Inferred from the input types.

    Args:
        points: A finite sequence of points, preserving every zero.
        jets: Consecutive value and derivative constraints at each point.
        context: Explicit output precision and rounding or enclosure settings.
        derivatives: True for raw derivatives; false for Taylor coefficients.
        max_steps: The complete call's work allowance.

    Returns:
        The numerical polynomial in the same representation and variable layout.

    Raises:
        PolyError: DOMAIN for invalid input, or LIMIT/CAPACITY on resource limits.
    """
    var budget = Budget(max_steps)
    return hermite_interpolate(points, jets, budget, context=context, derivatives=derivatives)


from . import evaluation as _evaluation
from apn_mojo import BallContext


def enclose[I: Iterable, X: Copyable & Deinitable](values: I, point: X, mut budget: Budget, *, context: BallContext) raises PolyError -> _evaluation.Enclosure[_Ring[_Kind[_Element[I]]], _evaluation._Domain[_Element[I], X], False, False] where _Kind[_Element[I]] >= 0:
    """Evaluate with an independently checkable enclosure.

    Inputs remain unchanged. Exact algebraic coefficients and points retain root witnesses for independent conversion checks. Adaptive calls refine exact algebraic coefficients while preserving supplied numerical uncertainty.

    Parameters:
        I: Inferred from the input types.
        X: Inferred from the input types.

    Args:
        values: Coefficients, terms, or a prepared value.
        point: A scalar for one variable, or a tuple in sparse axis order.
        budget: The shared work allowance.
        context: Explicit output precision and rounding or enclosure settings.

    Returns:
        An enclosing value with the original inputs, proof trace, and any requested accuracy outcome.

    Raises:
        PolyError: DOMAIN for invalid input, or LIMIT/CAPACITY on resource limits.
    """
    comptime E = _evaluation._Domain[_Element[I], X]
    comptime assert _Kind[_Element[I]] >= 0 and _Kind[_Element[I]] != 3, "enclosure evaluation requires characteristic-zero exact coefficients"
    _num._context[E](rebind[E.Context](context), budget)
    var point_witnesses = List[_evaluation._Point[E]]()
    _allocation[Tuple[Int64, E.Scalar]](1, budget)
    var arguments: List[Tuple[Int64, E.Scalar]] = [(Int64(0), _evaluation._argument[E](point, Int64(0), rebind[E.Context](context), point_witnesses, budget))]
    var p = to_core(values, budget)
    return _evaluation._compute[_Ring[_Kind[_Element[I]]], E, False, False](p^, arguments^, context, Optional[NumericOptions](), budget, point_witnesses^)


def enclose[I: Iterable, X: Copyable & Deinitable](values: I, point: X, *, context: BallContext, max_steps: UInt64 = UInt64.MAX) raises PolyError -> _evaluation.Enclosure[_Ring[_Kind[_Element[I]]], _evaluation._Domain[_Element[I], X], False, False] where _Kind[_Element[I]] >= 0:
    """Evaluate with an independently checkable enclosure.

    Inputs remain unchanged. Exact algebraic coefficients and points retain root witnesses for independent conversion checks. Adaptive calls refine exact algebraic coefficients while preserving supplied numerical uncertainty.

    Parameters:
        I: Inferred from the input types.
        X: Inferred from the input types.

    Args:
        values: Coefficients, terms, or a prepared value.
        point: A scalar for one variable, or a tuple in sparse axis order.
        context: Explicit output precision and rounding or enclosure settings.
        max_steps: The complete call's work allowance.

    Returns:
        An enclosing value with the original inputs, proof trace, and any requested accuracy outcome.

    Raises:
        PolyError: DOMAIN for invalid input, or LIMIT/CAPACITY on resource limits.
    """
    var budget = Budget(max_steps)
    return enclose(values, point, budget, context=context)


def adaptive_evaluate[I: Iterable, X: Copyable & Deinitable](values: I, point: X, mut budget: Budget, *, options: NumericOptions) raises PolyError -> _evaluation.Enclosure[_Ring[_Kind[_Element[I]]], _evaluation._Domain[_Element[I], X], False, False] where _Kind[_Element[I]] >= 0:
    """Evaluate with an independently checkable enclosure and a requested accuracy.

    Inputs remain unchanged. Exact algebraic coefficients and points retain root witnesses for independent conversion checks. Adaptive calls refine exact algebraic coefficients while preserving supplied numerical uncertainty.

    Parameters:
        I: Inferred from the input types.
        X: Inferred from the input types.

    Args:
        values: Coefficients, terms, or a prepared value.
        point: A scalar for one variable, or a tuple in sparse axis order.
        budget: The shared work allowance.
        options: Initial and maximum precision, and absolute or relative width targets.

    Returns:
        An enclosing value with the original inputs, proof trace, and any requested accuracy outcome.

    Raises:
        PolyError: DOMAIN for invalid input, or LIMIT/CAPACITY on resource limits.
    """
    comptime E = _evaluation._Domain[_Element[I], X]
    comptime assert _Kind[_Element[I]] >= 0 and _Kind[_Element[I]] != 3, "enclosure evaluation requires characteristic-zero exact coefficients"
    _evaluation._options(options)
    var context = _evaluation._context(options.max_precision, options.max_precision)
    _num._context[E](rebind[E.Context](context), budget)
    var point_witnesses = List[_evaluation._Point[E]]()
    _allocation[Tuple[Int64, E.Scalar]](1, budget)
    var arguments: List[Tuple[Int64, E.Scalar]] = [(Int64(0), _evaluation._argument[E](point, Int64(0), rebind[E.Context](context), point_witnesses, budget))]
    var p = to_core(values, budget)
    return _evaluation._compute[_Ring[_Kind[_Element[I]]], E, False, False](p^, arguments^, context, Optional(options), budget, point_witnesses^)


def adaptive_evaluate[I: Iterable, X: Copyable & Deinitable](values: I, point: X, *, options: NumericOptions, max_steps: UInt64 = UInt64.MAX) raises PolyError -> _evaluation.Enclosure[_Ring[_Kind[_Element[I]]], _evaluation._Domain[_Element[I], X], False, False] where _Kind[_Element[I]] >= 0:
    """Evaluate with an independently checkable enclosure and a requested accuracy.

    Inputs remain unchanged. Exact algebraic coefficients and points retain root witnesses for independent conversion checks. Adaptive calls refine exact algebraic coefficients while preserving supplied numerical uncertainty.

    Parameters:
        I: Inferred from the input types.
        X: Inferred from the input types.

    Args:
        values: Coefficients, terms, or a prepared value.
        point: A scalar for one variable, or a tuple in sparse axis order.
        options: Initial and maximum precision, and absolute or relative width targets.
        max_steps: The complete call's work allowance.

    Returns:
        An enclosing value with the original inputs, proof trace, and any requested accuracy outcome.

    Raises:
        PolyError: DOMAIN for invalid input, or LIMIT/CAPACITY on resource limits.
    """
    var budget = Budget(max_steps)
    return adaptive_evaluate(values, point, budget, options=options)


def enclose[D: NumericDomain, X: Copyable & Deinitable](values: NumericArray[D], point: X, mut budget: Budget, *, context: BallContext) raises PolyError -> _evaluation.Enclosure[D, _evaluation._Domain[D.Scalar, X], True, False]:
    """Evaluate with an independently checkable enclosure.

    Inputs remain unchanged. Exact algebraic coefficients and points retain root witnesses for independent conversion checks. Adaptive calls refine exact algebraic coefficients while preserving supplied numerical uncertainty.

    Parameters:
        D: The numerical coefficient domain.
        X: Inferred from the input types.

    Args:
        values: Coefficients, terms, or a prepared value.
        point: A scalar for one variable, or a tuple in sparse axis order.
        budget: The shared work allowance.
        context: Explicit output precision and rounding or enclosure settings.

    Returns:
        An enclosing value with the original inputs, proof trace, and any requested accuracy outcome.

    Raises:
        PolyError: DOMAIN for invalid input, or LIMIT/CAPACITY on resource limits.
    """
    comptime E = _evaluation._Domain[D.Scalar, X]
    _num._context[E](rebind[E.Context](context), budget)
    var point_witnesses = List[_evaluation._Point[E]]()
    _allocation[Tuple[Int64, E.Scalar]](1, budget)
    var arguments: List[Tuple[Int64, E.Scalar]] = [(Int64(0), _evaluation._argument[E](point, Int64(0), rebind[E.Context](context), point_witnesses, budget))]
    var p = _num._copy_dense(values._core[], budget)
    return _evaluation._compute[D, E, True, False](p^, arguments^, context, Optional[NumericOptions](), budget, point_witnesses^)


def enclose[D: NumericDomain, X: Copyable & Deinitable](values: NumericArray[D], point: X, *, context: BallContext, max_steps: UInt64 = UInt64.MAX) raises PolyError -> _evaluation.Enclosure[D, _evaluation._Domain[D.Scalar, X], True, False]:
    """Evaluate with an independently checkable enclosure.

    Inputs remain unchanged. Exact algebraic coefficients and points retain root witnesses for independent conversion checks. Adaptive calls refine exact algebraic coefficients while preserving supplied numerical uncertainty.

    Parameters:
        D: The numerical coefficient domain.
        X: Inferred from the input types.

    Args:
        values: Coefficients, terms, or a prepared value.
        point: A scalar for one variable, or a tuple in sparse axis order.
        context: Explicit output precision and rounding or enclosure settings.
        max_steps: The complete call's work allowance.

    Returns:
        An enclosing value with the original inputs, proof trace, and any requested accuracy outcome.

    Raises:
        PolyError: DOMAIN for invalid input, or LIMIT/CAPACITY on resource limits.
    """
    var budget = Budget(max_steps)
    return enclose[D, X](values, point, budget, context=context)


def adaptive_evaluate[D: NumericDomain, X: Copyable & Deinitable](values: NumericArray[D], point: X, mut budget: Budget, *, options: NumericOptions) raises PolyError -> _evaluation.Enclosure[D, _evaluation._Domain[D.Scalar, X], True, False]:
    """Evaluate with an independently checkable enclosure and a requested accuracy.

    Inputs remain unchanged. Exact algebraic coefficients and points retain root witnesses for independent conversion checks. Adaptive calls refine exact algebraic coefficients while preserving supplied numerical uncertainty.

    Parameters:
        D: The numerical coefficient domain.
        X: Inferred from the input types.

    Args:
        values: Coefficients, terms, or a prepared value.
        point: A scalar for one variable, or a tuple in sparse axis order.
        budget: The shared work allowance.
        options: Initial and maximum precision, and absolute or relative width targets.

    Returns:
        An enclosing value with the original inputs, proof trace, and any requested accuracy outcome.

    Raises:
        PolyError: DOMAIN for invalid input, or LIMIT/CAPACITY on resource limits.
    """
    comptime E = _evaluation._Domain[D.Scalar, X]
    _evaluation._options(options)
    var context = _evaluation._context(options.max_precision, options.max_precision)
    _num._context[E](rebind[E.Context](context), budget)
    var point_witnesses = List[_evaluation._Point[E]]()
    _allocation[Tuple[Int64, E.Scalar]](1, budget)
    var arguments: List[Tuple[Int64, E.Scalar]] = [(Int64(0), _evaluation._argument[E](point, Int64(0), rebind[E.Context](context), point_witnesses, budget))]
    var p = _num._copy_dense(values._core[], budget)
    return _evaluation._compute[D, E, True, False](p^, arguments^, context, Optional(options), budget, point_witnesses^)


def adaptive_evaluate[D: NumericDomain, X: Copyable & Deinitable](values: NumericArray[D], point: X, *, options: NumericOptions, max_steps: UInt64 = UInt64.MAX) raises PolyError -> _evaluation.Enclosure[D, _evaluation._Domain[D.Scalar, X], True, False]:
    """Evaluate with an independently checkable enclosure and a requested accuracy.

    Inputs remain unchanged. Exact algebraic coefficients and points retain root witnesses for independent conversion checks. Adaptive calls refine exact algebraic coefficients while preserving supplied numerical uncertainty.

    Parameters:
        D: The numerical coefficient domain.
        X: Inferred from the input types.

    Args:
        values: Coefficients, terms, or a prepared value.
        point: A scalar for one variable, or a tuple in sparse axis order.
        options: Initial and maximum precision, and absolute or relative width targets.
        max_steps: The complete call's work allowance.

    Returns:
        An enclosing value with the original inputs, proof trace, and any requested accuracy outcome.

    Raises:
        PolyError: DOMAIN for invalid input, or LIMIT/CAPACITY on resource limits.
    """
    var budget = Budget(max_steps)
    return adaptive_evaluate[D, X](values, point, budget, options=options)


from polynomials import NumericDivisionResult


@fieldwise_init
struct NumericDivision[D: NumericDomain](Copyable, Movable):
    """Quotient, remainder, and independently checkable residual or family bounds.

    Parameters:
        D: The numerical coefficient domain.
    """
    var _left: NumericArray[Self.D]
    var _right: NumericArray[Self.D]
    var _proof: ArcPointer[NumericDivisionResult[Self.D]]

    def evidence(self) -> ref[ImmOrigin(origin_of(self._proof[]))] NumericDivisionResult[Self.D]:
        """Borrow the division result and its residual evidence.

        Returns:
            Immutable core quotient, remainder, residual and family witnesses.
        """
        return self._proof[]

    def quotient(self, mut budget: Budget) raises PolyError -> NumericArray[Self.D]:
        """Copy the numerical quotient from the retained division result.

        Args:
            budget: The shared work allowance.

        Returns:
            An independent numerical coefficient array.

        Raises:
            PolyError: DOMAIN for invalid input, or LIMIT/CAPACITY on resource limits.
        """
        return NumericArray[Self.D](_num._copy_dense(self._proof[].quotient, budget), budget)


    def quotient(self, *, max_steps: UInt64 = UInt64.MAX) raises PolyError -> NumericArray[Self.D]:
        """Copy the numerical quotient from the retained division result.

        Args:
            max_steps: The complete call's work allowance.

        Returns:
            An independent numerical coefficient array.

        Raises:
            PolyError: DOMAIN for invalid input, or LIMIT/CAPACITY on resource limits.
        """
        var budget = Budget(max_steps)
        return self.quotient(budget)

    def remainder(self, mut budget: Budget) raises PolyError -> NumericArray[Self.D]:
        """Copy the numerical remainder from the retained division result.

        Args:
            budget: The shared work allowance.

        Returns:
            An independent numerical coefficient array.

        Raises:
            PolyError: DOMAIN for invalid input, or LIMIT/CAPACITY on resource limits.
        """
        return NumericArray[Self.D](_num._copy_dense(self._proof[].remainder, budget), budget)


    def remainder(self, *, max_steps: UInt64 = UInt64.MAX) raises PolyError -> NumericArray[Self.D]:
        """Copy the numerical remainder from the retained division result.

        Args:
            max_steps: The complete call's work allowance.

        Returns:
            An independent numerical coefficient array.

        Raises:
            PolyError: DOMAIN for invalid input, or LIMIT/CAPACITY on resource limits.
        """
        var budget = Budget(max_steps)
        return self.remainder(budget)


def divide_checked[D: NumericDomain](a: NumericArray[D], b: NumericArray[D], mut budget: Budget, *, context: D.Context) raises PolyError -> NumericDivision[D]:
    """Divide numerical arrays and retain residual or uniform-family evidence.

    Parameters:
        D: The numerical coefficient domain.

    Args:
        a: The first prepared value.
        b: The second prepared value.
        budget: The shared work allowance.
        context: Explicit output precision and rounding or enclosure settings.

    Returns:
        A division result retaining both operands, residual bounds, and any uniform-family evidence.

    Raises:
        PolyError: DOMAIN for invalid input, or LIMIT/CAPACITY on resource limits.
    """
    _num._context[D](context, budget)
    var proof = numeric_divmod(a._core[], b._core[], context, budget)
    _allocation[NumericDivisionResult[D]](1, budget)
    return NumericDivision[D](a.copy(), b.copy(), ArcPointer(proof^))


def divide_checked[D: NumericDomain](a: NumericArray[D], b: NumericArray[D], *, context: D.Context, max_steps: UInt64 = UInt64.MAX) raises PolyError -> NumericDivision[D]:
    """Divide numerical arrays and retain residual or uniform-family evidence.

    Parameters:
        D: The numerical coefficient domain.

    Args:
        a: The first prepared value.
        b: The second prepared value.
        context: Explicit output precision and rounding or enclosure settings.
        max_steps: The complete call's work allowance.

    Returns:
        A division result retaining both operands, residual bounds, and any uniform-family evidence.

    Raises:
        PolyError: DOMAIN for invalid input, or LIMIT/CAPACITY on resource limits.
    """
    var budget = Budget(max_steps)
    return divide_checked(a, b, budget, context=context)


def check_division[D: NumericDomain](result: NumericDivision[D], mut budget: Budget) raises PolyError -> Bool:
    """Verify numerical division against its original operands.

    Parameters:
        D: The numerical coefficient domain.

    Args:
        result: The result and its retained evidence.
        budget: The shared work allowance.

    Returns:
        Whether the evidence is valid.

    Raises:
        PolyError: DOMAIN for invalid input, or LIMIT/CAPACITY on resource limits.
    """
    return check_numeric_division(result._left._core[], result._right._core[], result._proof[], budget)


def check_division[D: NumericDomain](result: NumericDivision[D], *, max_steps: UInt64 = UInt64.MAX) raises PolyError -> Bool:
    """Verify numerical division against its original operands.

    Parameters:
        D: The numerical coefficient domain.

    Args:
        result: The result and its retained evidence.
        max_steps: The complete call's work allowance.

    Returns:
        Whether the evidence is valid.

    Raises:
        PolyError: DOMAIN for invalid input, or LIMIT/CAPACITY on resource limits.
    """
    var budget = Budget(max_steps)
    return check_division(result, budget)


def enclose_stream[I: Iterable, X: Copyable & Deinitable](values: I, point: X, mut budget: Budget, *, context: BallContext) raises PolyError -> _evaluation._Stream[_Ring[_Kind[_Element[I]]], _evaluation._Domain[_Element[I], X], False, False, False, _evaluation._IsAlgebraic[X]] where _Kind[_Element[I]] >= 0:
    """Prepare an enclosure producer that emits one witness event at a time.

    Use the same inputs and context for producer and checker. Algebraic inputs
    are refined automatically at the requested precision, with root evidence
    before the arithmetic events. The receipt alone does not certify evaluation.

    Parameters:
        I: Inferred from the input types.
        X: Inferred from the input types.

    Args:
        values: Coefficients, terms, or a prepared value.
        point: A scalar for one variable, or a tuple in sparse axis order.
        budget: The shared work allowance.
        context: Explicit output precision and rounding or enclosure settings.

    Returns:
        A producer owning its evaluation state without retaining emitted witnesses.

    Raises:
        PolyError: DOMAIN for invalid input, or LIMIT/CAPACITY on resource limits.
    """
    comptime E = _evaluation._Domain[_Element[I], X]
    comptime assert _Kind[_Element[I]] >= 0 and _Kind[_Element[I]] != 3, "enclosure evaluation requires characteristic-zero exact coefficients"
    _num._context[E](rebind[E.Context](context), budget)
    _allocation[Tuple[Int64, E.Scalar]](1, budget)
    var algebraic_points = List[_evaluation._StreamPoint]()
    var arguments: List[Tuple[Int64, E.Scalar]] = [(Int64(0), _evaluation._stream_argument[E](point, 0, rebind[E.Context](context), algebraic_points, budget))]
    var p = to_core(values, budget)
    return _evaluation._stream[_Ring[_Kind[_Element[I]]], E, False, False, False, _evaluation._IsAlgebraic[X]](p^, arguments^, context, budget, algebraic_points^)


def enclose_checker[I: Iterable, X: Copyable & Deinitable](values: I, point: X, mut budget: Budget, *, context: BallContext) raises PolyError -> _evaluation._Stream[_Ring[_Kind[_Element[I]]], _evaluation._Domain[_Element[I], X], False, False, True, _evaluation._IsAlgebraic[X]] where _Kind[_Element[I]] >= 0:
    """Prepare independent incremental enclosure checking.

    Use the same inputs and context for producer and checker. Algebraic inputs
    are refined automatically at the requested precision, with root evidence
    before the arithmetic events. The receipt alone does not certify evaluation.

    Parameters:
        I: Inferred from the input types.
        X: Inferred from the input types.

    Args:
        values: Coefficients, terms, or a prepared value.
        point: A scalar for one variable, or a tuple in sparse axis order.
        budget: The shared work allowance.
        context: Explicit output precision and rounding or enclosure settings.

    Returns:
        A checker accepting events in order and validating the completion receipt.

    Raises:
        PolyError: DOMAIN for invalid input, or LIMIT/CAPACITY on resource limits.
    """
    comptime E = _evaluation._Domain[_Element[I], X]
    comptime assert _Kind[_Element[I]] >= 0 and _Kind[_Element[I]] != 3, "enclosure evaluation requires characteristic-zero exact coefficients"
    _num._context[E](rebind[E.Context](context), budget)
    _allocation[Tuple[Int64, E.Scalar]](1, budget)
    var algebraic_points = List[_evaluation._StreamPoint]()
    var arguments: List[Tuple[Int64, E.Scalar]] = [(Int64(0), _evaluation._stream_argument[E](point, 0, rebind[E.Context](context), algebraic_points, budget))]
    var p = to_core(values, budget)
    return _evaluation._stream[_Ring[_Kind[_Element[I]]], E, False, False, True, _evaluation._IsAlgebraic[X]](p^, arguments^, context, budget, algebraic_points^)


def enclose_stream[I: Iterable, X: Copyable & Deinitable](values: I, point: X, *, context: BallContext, max_steps: UInt64 = UInt64.MAX) raises PolyError -> _evaluation._Stream[_Ring[_Kind[_Element[I]]], _evaluation._Domain[_Element[I], X], False, False, False, _evaluation._IsAlgebraic[X]] where _Kind[_Element[I]] >= 0:
    """Prepare an enclosure producer that emits one witness event at a time.

    Use the same inputs and context for producer and checker. Algebraic inputs
    are refined automatically at the requested precision, with root evidence
    before the arithmetic events. The receipt alone does not certify evaluation.

    Parameters:
        I: Inferred from the input types.
        X: Inferred from the input types.

    Args:
        values: Coefficients, terms, or a prepared value.
        point: A scalar for one variable, or a tuple in sparse axis order.
        context: Explicit output precision and rounding or enclosure settings.
        max_steps: The complete call's work allowance.

    Returns:
        A producer owning its evaluation state without retaining emitted witnesses.

    Raises:
        PolyError: DOMAIN for invalid input, or LIMIT/CAPACITY on resource limits.
    """
    var budget = Budget(max_steps)
    return enclose_stream(values, point, budget, context=context)


def enclose_checker[I: Iterable, X: Copyable & Deinitable](values: I, point: X, *, context: BallContext, max_steps: UInt64 = UInt64.MAX) raises PolyError -> _evaluation._Stream[_Ring[_Kind[_Element[I]]], _evaluation._Domain[_Element[I], X], False, False, True, _evaluation._IsAlgebraic[X]] where _Kind[_Element[I]] >= 0:
    """Prepare independent incremental enclosure checking.

    Use the same inputs and context for producer and checker. Algebraic inputs
    are refined automatically at the requested precision, with root evidence
    before the arithmetic events. The receipt alone does not certify evaluation.

    Parameters:
        I: Inferred from the input types.
        X: Inferred from the input types.

    Args:
        values: Coefficients, terms, or a prepared value.
        point: A scalar for one variable, or a tuple in sparse axis order.
        context: Explicit output precision and rounding or enclosure settings.
        max_steps: The complete call's work allowance.

    Returns:
        A checker accepting events in order and validating the completion receipt.

    Raises:
        PolyError: DOMAIN for invalid input, or LIMIT/CAPACITY on resource limits.
    """
    var budget = Budget(max_steps)
    return enclose_checker(values, point, budget, context=context)


def enclose_stream[D: NumericDomain, X: Copyable & Deinitable](values: NumericArray[D], point: X, mut budget: Budget, *, context: BallContext) raises PolyError -> _evaluation._Stream[D, _evaluation._Domain[D.Scalar, X], True, False, False, _evaluation._IsAlgebraic[X]]:
    """Prepare an enclosure producer that emits one witness event at a time.

    Use the same inputs and context for producer and checker. Algebraic inputs
    are refined automatically at the requested precision, with root evidence
    before the arithmetic events. The receipt alone does not certify evaluation.

    Parameters:
        D: The numerical coefficient domain.
        X: Inferred from the input types.

    Args:
        values: Coefficients, terms, or a prepared value.
        point: A scalar for one variable, or a tuple in sparse axis order.
        budget: The shared work allowance.
        context: Explicit output precision and rounding or enclosure settings.

    Returns:
        A producer owning its evaluation state without retaining emitted witnesses.

    Raises:
        PolyError: DOMAIN for invalid input, or LIMIT/CAPACITY on resource limits.
    """
    comptime E = _evaluation._Domain[D.Scalar, X]
    _num._context[E](rebind[E.Context](context), budget)
    _allocation[Tuple[Int64, E.Scalar]](1, budget)
    var algebraic_points = List[_evaluation._StreamPoint]()
    var arguments: List[Tuple[Int64, E.Scalar]] = [(Int64(0), _evaluation._stream_argument[E](point, 0, rebind[E.Context](context), algebraic_points, budget))]
    var p = _num._copy_dense(values._core[], budget)
    return _evaluation._stream[D, E, True, False, False, _evaluation._IsAlgebraic[X]](p^, arguments^, context, budget, algebraic_points^)


def enclose_checker[D: NumericDomain, X: Copyable & Deinitable](values: NumericArray[D], point: X, mut budget: Budget, *, context: BallContext) raises PolyError -> _evaluation._Stream[D, _evaluation._Domain[D.Scalar, X], True, False, True, _evaluation._IsAlgebraic[X]]:
    """Prepare independent incremental enclosure checking.

    Use the same inputs and context for producer and checker. Algebraic inputs
    are refined automatically at the requested precision, with root evidence
    before the arithmetic events. The receipt alone does not certify evaluation.

    Parameters:
        D: The numerical coefficient domain.
        X: Inferred from the input types.

    Args:
        values: Coefficients, terms, or a prepared value.
        point: A scalar for one variable, or a tuple in sparse axis order.
        budget: The shared work allowance.
        context: Explicit output precision and rounding or enclosure settings.

    Returns:
        A checker accepting events in order and validating the completion receipt.

    Raises:
        PolyError: DOMAIN for invalid input, or LIMIT/CAPACITY on resource limits.
    """
    comptime E = _evaluation._Domain[D.Scalar, X]
    _num._context[E](rebind[E.Context](context), budget)
    _allocation[Tuple[Int64, E.Scalar]](1, budget)
    var algebraic_points = List[_evaluation._StreamPoint]()
    var arguments: List[Tuple[Int64, E.Scalar]] = [(Int64(0), _evaluation._stream_argument[E](point, 0, rebind[E.Context](context), algebraic_points, budget))]
    var p = _num._copy_dense(values._core[], budget)
    return _evaluation._stream[D, E, True, False, True, _evaluation._IsAlgebraic[X]](p^, arguments^, context, budget, algebraic_points^)


def enclose_stream[D: NumericDomain, X: Copyable & Deinitable](values: NumericArray[D], point: X, *, context: BallContext, max_steps: UInt64 = UInt64.MAX) raises PolyError -> _evaluation._Stream[D, _evaluation._Domain[D.Scalar, X], True, False, False, _evaluation._IsAlgebraic[X]]:
    """Prepare an enclosure producer that emits one witness event at a time.

    Use the same inputs and context for producer and checker. Algebraic inputs
    are refined automatically at the requested precision, with root evidence
    before the arithmetic events. The receipt alone does not certify evaluation.

    Parameters:
        D: The numerical coefficient domain.
        X: Inferred from the input types.

    Args:
        values: Coefficients, terms, or a prepared value.
        point: A scalar for one variable, or a tuple in sparse axis order.
        context: Explicit output precision and rounding or enclosure settings.
        max_steps: The complete call's work allowance.

    Returns:
        A producer owning its evaluation state without retaining emitted witnesses.

    Raises:
        PolyError: DOMAIN for invalid input, or LIMIT/CAPACITY on resource limits.
    """
    var budget = Budget(max_steps)
    return enclose_stream[D, X](values, point, budget, context=context)


def enclose_checker[D: NumericDomain, X: Copyable & Deinitable](values: NumericArray[D], point: X, *, context: BallContext, max_steps: UInt64 = UInt64.MAX) raises PolyError -> _evaluation._Stream[D, _evaluation._Domain[D.Scalar, X], True, False, True, _evaluation._IsAlgebraic[X]]:
    """Prepare independent incremental enclosure checking.

    Use the same inputs and context for producer and checker. Algebraic inputs
    are refined automatically at the requested precision, with root evidence
    before the arithmetic events. The receipt alone does not certify evaluation.

    Parameters:
        D: The numerical coefficient domain.
        X: Inferred from the input types.

    Args:
        values: Coefficients, terms, or a prepared value.
        point: A scalar for one variable, or a tuple in sparse axis order.
        context: Explicit output precision and rounding or enclosure settings.
        max_steps: The complete call's work allowance.

    Returns:
        A checker accepting events in order and validating the completion receipt.

    Raises:
        PolyError: DOMAIN for invalid input, or LIMIT/CAPACITY on resource limits.
    """
    var budget = Budget(max_steps)
    return enclose_checker[D, X](values, point, budget, context=context)


from polynomials import serialize_numeric_dense_to, deserialize_numeric_dense_from


def dump[D: NumericDomain, S: PolynomialTextSink](values: NumericArray[D], mut sink: S, mut budget: Budget, *, chunk_bytes: Int = 4096) raises PolyError:
    """Write numerical coefficients in bounded text chunks.

    Stored precision and enclosure bounds are preserved. A failed write can leave an incomplete destination.

    Parameters:
        D: Inferred from the input types unless explicitly supplied.
        S: Inferred from the input types unless explicitly supplied.

    Args:
        values: Input coefficients, sparse terms, or a prepared array.
        sink: The consumer receiving ordered chunks or witnesses.
        budget: The shared work allowance, including preparation and output storage.
        chunk_bytes: Positive target chunk size; a single header or scalar can exceed it.

    Raises:
        PolyError: DOMAIN for incompatible input, UNSUPPORTED for an unavailable coefficient domain, or LIMIT/CAPACITY on resource limits.
    """
    serialize_numeric_dense_to(values._core[], sink, budget, chunk_bytes=chunk_bytes)


def dump[D: NumericDomain, S: PolynomialTextSink](values: NumericArray[D], mut sink: S, *, chunk_bytes: Int = 4096, max_steps: UInt64 = UInt64.MAX) raises PolyError:
    """Write numerical coefficients in bounded text chunks.

    Stored precision and enclosure bounds are preserved. A failed write can leave an incomplete destination.

    Parameters:
        D: Inferred from the input types unless explicitly supplied.
        S: Inferred from the input types unless explicitly supplied.

    Args:
        values: Input coefficients, sparse terms, or a prepared array.
        sink: The consumer receiving ordered chunks or witnesses.
        chunk_bytes: Positive target chunk size; a single header or scalar can exceed it.
        max_steps: The complete call’s work allowance.

    Raises:
        PolyError: DOMAIN for incompatible input, UNSUPPORTED for an unavailable coefficient domain, or LIMIT/CAPACITY on resource limits.
    """
    var budget = Budget(max_steps)
    dump[D, S](values, sink, budget, chunk_bytes=chunk_bytes)


def load_numeric[T: Copyable & Deinitable, S: PolynomialTextSource](var source: S, mut budget: Budget, *, max_field_bytes: Int = 16777216) raises PolyError -> NumericArray[_num._StoredDomain[T]]:
    """Restore stored numerical values exactly; subsequent arithmetic takes an explicit context.

    Parameters:
        T: The expected numerical scalar type.
        S: The text source type.

    Args:
        source: The owned text source, consumed through end of input.
        budget: The shared work allowance, including preparation, computation, and result storage.
        max_field_bytes: Positive maximum encoded field size in bytes.

    Returns:
        A numerical array preserving the encoded scalar precision and enclosures.

    Raises:
        PolyError: ENCODING for malformed or incompatible records, DOMAIN for invalid settings, or LIMIT/CAPACITY on resource limits.
    """
    comptime assert T == _num.Float or T == _num.Complex or T == _num.Ball or T == _num.ComplexBall, "load_numeric expects Float, Complex, Ball, or ComplexBall"
    comptime D = _num._StoredDomain[T]
    var core = deserialize_numeric_dense_from[D](source^, budget, max_field_bytes=max_field_bytes)
    core.variable = 0
    return NumericArray[_num._StoredDomain[T]](core^, budget)


def load_numeric[T: Copyable & Deinitable, S: PolynomialTextSource](var source: S, *, max_steps: UInt64 = UInt64.MAX, max_field_bytes: Int = 16777216) raises PolyError -> NumericArray[_num._StoredDomain[T]]:
    """Restore stored numerical values exactly; subsequent arithmetic takes an explicit context.

    Parameters:
        T: The expected numerical scalar type.
        S: The text source type.

    Args:
        source: The owned text source, consumed through end of input.
        max_steps: The complete call's work allowance; defaults to UInt64.MAX.
        max_field_bytes: Positive maximum encoded field size in bytes.

    Returns:
        A numerical array preserving the encoded scalar precision and enclosures.

    Raises:
        PolyError: ENCODING for malformed or incompatible records, DOMAIN for invalid settings, or LIMIT/CAPACITY on resource limits.
    """
    var budget = Budget(max_steps)
    return load_numeric[T, S](source^, budget, max_field_bytes=max_field_bytes)


from polynomials import real_roots_numeric_to, complex_roots_numeric_to


def real_root_cover_to[D: NumericDomain, S: RealRootSink](values: NumericArray[D], mut sink: S, mut budget: Budget, *, options: NumericOptions = NumericOptions(), complete_only: Bool = False) raises PolyError -> RootStreamReceipt:
    """Stream numerical real root witnesses without collecting them.

    Parameters:
        D: Inferred from the input types unless explicitly supplied.
        S: Inferred from the input types unless explicitly supplied.

    Args:
        values: Input coefficients, sparse terms, or a prepared array.
        sink: The consumer receiving ordered chunks or witnesses.
        budget: The shared work allowance, including preparation and output storage.
        options: Precision, accuracy, subdivision and isolation settings.
        complete_only: Raise unless every requested root-cover property succeeds.

    Returns:
        A completion receipt; finish independent checking before trusting its claim.

    Raises:
        PolyError: DOMAIN for incompatible input, UNSUPPORTED for an unavailable coefficient domain, or LIMIT/CAPACITY on resource limits.
    """
    return real_roots_numeric_to(values._core[], options, sink, budget, complete_only=complete_only)


def real_root_cover_to[D: NumericDomain, S: RealRootSink](values: NumericArray[D], mut sink: S, *, options: NumericOptions = NumericOptions(), complete_only: Bool = False, max_steps: UInt64 = UInt64.MAX) raises PolyError -> RootStreamReceipt:
    """Stream numerical real root witnesses without collecting them.

    Parameters:
        D: Inferred from the input types unless explicitly supplied.
        S: Inferred from the input types unless explicitly supplied.

    Args:
        values: Input coefficients, sparse terms, or a prepared array.
        sink: The consumer receiving ordered chunks or witnesses.
        options: Precision, accuracy, subdivision and isolation settings.
        complete_only: Raise unless every requested root-cover property succeeds.
        max_steps: The complete call’s work allowance.

    Returns:
        A completion receipt; finish independent checking before trusting its claim.

    Raises:
        PolyError: DOMAIN for incompatible input, UNSUPPORTED for an unavailable coefficient domain, or LIMIT/CAPACITY on resource limits.
    """
    var budget = Budget(max_steps)
    return real_root_cover_to[D, S](values, sink, budget, options=options, complete_only=complete_only)


def real_root_checker[D: NumericDomain](values: NumericArray[D], mut budget: Budget, *, options: NumericOptions = NumericOptions()) raises PolyError -> RealRootStreamChecker:
    """Prepare incremental checking for a numerical real root cover.

    Parameters:
        D: Inferred from the input types unless explicitly supplied.

    Args:
        values: Input coefficients, sparse terms, or a prepared array.
        budget: The shared work allowance, including preparation and output storage.
        options: Precision, accuracy, subdivision and isolation settings.

    Returns:
        A checker retaining the original coefficient bounds and requested properties.

    Raises:
        PolyError: DOMAIN for incompatible input, UNSUPPORTED for an unavailable coefficient domain, or LIMIT/CAPACITY on resource limits.
    """
    return RealRootStreamChecker.from_numeric(values._core[], options, budget)


def real_root_checker[D: NumericDomain](values: NumericArray[D], *, options: NumericOptions = NumericOptions(), max_steps: UInt64 = UInt64.MAX) raises PolyError -> RealRootStreamChecker:
    """Prepare incremental checking for a numerical real root cover.

    Parameters:
        D: Inferred from the input types unless explicitly supplied.

    Args:
        values: Input coefficients, sparse terms, or a prepared array.
        options: Precision, accuracy, subdivision and isolation settings.
        max_steps: The complete call’s work allowance.

    Returns:
        A checker retaining the original coefficient bounds and requested properties.

    Raises:
        PolyError: DOMAIN for incompatible input, UNSUPPORTED for an unavailable coefficient domain, or LIMIT/CAPACITY on resource limits.
    """
    var budget = Budget(max_steps)
    return real_root_checker[D](values, budget, options=options)


def complex_root_cover_to[D: NumericDomain, S: ComplexRootSink](values: NumericArray[D], mut sink: S, mut budget: Budget, *, options: NumericOptions = NumericOptions(), complete_only: Bool = False) raises PolyError -> RootStreamReceipt:
    """Stream numerical complex root witnesses without collecting them.

    Parameters:
        D: Inferred from the input types unless explicitly supplied.
        S: Inferred from the input types unless explicitly supplied.

    Args:
        values: Input coefficients, sparse terms, or a prepared array.
        sink: The consumer receiving ordered chunks or witnesses.
        budget: The shared work allowance, including preparation and output storage.
        options: Precision, accuracy, subdivision and isolation settings.
        complete_only: Raise unless every requested root-cover property succeeds.

    Returns:
        A completion receipt; finish independent checking before trusting its claim.

    Raises:
        PolyError: DOMAIN for incompatible input, UNSUPPORTED for an unavailable coefficient domain, or LIMIT/CAPACITY on resource limits.
    """
    return complex_roots_numeric_to(values._core[], options, sink, budget, complete_only=complete_only)


def complex_root_cover_to[D: NumericDomain, S: ComplexRootSink](values: NumericArray[D], mut sink: S, *, options: NumericOptions = NumericOptions(), complete_only: Bool = False, max_steps: UInt64 = UInt64.MAX) raises PolyError -> RootStreamReceipt:
    """Stream numerical complex root witnesses without collecting them.

    Parameters:
        D: Inferred from the input types unless explicitly supplied.
        S: Inferred from the input types unless explicitly supplied.

    Args:
        values: Input coefficients, sparse terms, or a prepared array.
        sink: The consumer receiving ordered chunks or witnesses.
        options: Precision, accuracy, subdivision and isolation settings.
        complete_only: Raise unless every requested root-cover property succeeds.
        max_steps: The complete call’s work allowance.

    Returns:
        A completion receipt; finish independent checking before trusting its claim.

    Raises:
        PolyError: DOMAIN for incompatible input, UNSUPPORTED for an unavailable coefficient domain, or LIMIT/CAPACITY on resource limits.
    """
    var budget = Budget(max_steps)
    return complex_root_cover_to[D, S](values, sink, budget, options=options, complete_only=complete_only)


def complex_root_checker[D: NumericDomain](values: NumericArray[D], mut budget: Budget, *, options: NumericOptions = NumericOptions()) raises PolyError -> ComplexRootStreamChecker:
    """Prepare incremental checking for a numerical complex root cover.

    Parameters:
        D: Inferred from the input types unless explicitly supplied.

    Args:
        values: Input coefficients, sparse terms, or a prepared array.
        budget: The shared work allowance, including preparation and output storage.
        options: Precision, accuracy, subdivision and isolation settings.

    Returns:
        A checker retaining the original coefficient bounds and requested properties.

    Raises:
        PolyError: DOMAIN for incompatible input, UNSUPPORTED for an unavailable coefficient domain, or LIMIT/CAPACITY on resource limits.
    """
    return ComplexRootStreamChecker.from_numeric(values._core[], options, budget)


def complex_root_checker[D: NumericDomain](values: NumericArray[D], *, options: NumericOptions = NumericOptions(), max_steps: UInt64 = UInt64.MAX) raises PolyError -> ComplexRootStreamChecker:
    """Prepare incremental checking for a numerical complex root cover.

    Parameters:
        D: Inferred from the input types unless explicitly supplied.

    Args:
        values: Input coefficients, sparse terms, or a prepared array.
        options: Precision, accuracy, subdivision and isolation settings.
        max_steps: The complete call’s work allowance.

    Returns:
        A checker retaining the original coefficient bounds and requested properties.

    Raises:
        PolyError: DOMAIN for incompatible input, UNSUPPORTED for an unavailable coefficient domain, or LIMIT/CAPACITY on resource limits.
    """
    var budget = Budget(max_steps)
    return complex_root_checker[D](values, budget, options=options)


from . import exact as _exact
from polynomials import GcdResult, CoprimalityCertificate, ResultantResult, DivisionResult, ListDivision, SquarefreeDecomposition, coprimality_certificate


def gcd_checked[A: Iterable, B: Iterable](a: A, b: B, mut budget: Budget) raises PolyError -> _exact.Result[_Join[_Kind[_Element[A]], _Kind[_Element[B]]], Int, False, GcdResult[_Ring[_Join[_Kind[_Element[A]], _Kind[_Element[B]]]]]]:
    """Compute a GCD and retain independent maximality evidence.

    Independent checking proves greatest-common-divisor status up to a unit; the producer returns the usual normalized representative.

    Parameters:
        A: Inferred from the input types unless explicitly supplied.
        B: Inferred from the input types unless explicitly supplied.

    Args:
        a: The first polynomial.
        b: The second polynomial.
        budget: The shared work allowance, including preparation and output storage.

    Returns:
        A retained GCD with maximality evidence for exact.value and exact.check.

    Raises:
        PolyError: DOMAIN for incompatible input, UNSUPPORTED for an unavailable coefficient domain, or LIMIT/CAPACITY on resource limits.
    """
    comptime k = _Join[_Kind[_Element[A]], _Kind[_Element[B]]]
    var pair = _pair[k](a, b, budget)
    var left = _dense_sparse(pair[0]._core[], budget)
    var right = _dense_sparse(pair[1]._core[], budget)
    var proof = _gcd(left, right, budget, certify_maximal=True)
    _allocation[SparsePoly[_Ring[k]]](1, budget)
    var others: List[SparsePoly[_Ring[k]]] = [right^]
    var result = _exact._retain[k, Int, False, GcdResult[_Ring[k]]](left^, others^, proof^, budget)
    return result^


def gcd_checked[A: Iterable, B: Iterable](a: A, b: B, *, max_steps: UInt64 = UInt64.MAX) raises PolyError -> _exact.Result[_Join[_Kind[_Element[A]], _Kind[_Element[B]]], Int, False, GcdResult[_Ring[_Join[_Kind[_Element[A]], _Kind[_Element[B]]]]]]:
    """Compute a GCD and retain independent maximality evidence.

    Independent checking proves greatest-common-divisor status up to a unit; the producer returns the usual normalized representative.

    Parameters:
        A: Inferred from the input types unless explicitly supplied.
        B: Inferred from the input types unless explicitly supplied.

    Args:
        a: The first polynomial.
        b: The second polynomial.
        max_steps: The complete call’s work allowance.

    Returns:
        A retained GCD with maximality evidence for exact.value and exact.check.

    Raises:
        PolyError: DOMAIN for incompatible input, UNSUPPORTED for an unavailable coefficient domain, or LIMIT/CAPACITY on resource limits.
    """
    var budget = Budget(max_steps)
    return gcd_checked[A, B](a, b, budget)


def resultant_checked[A: Iterable, B: Iterable](a: A, b: B, mut budget: Budget) raises PolyError -> _exact.Result[_Join[_Kind[_Element[A]], _Kind[_Element[B]]], Int, False, ResultantResult[_Ring[_Join[_Kind[_Element[A]], _Kind[_Element[B]]]]]]:
    """Compute a resultant and retain its ideal-membership identity.

    The checker proves u*a + v*b = result; it does not independently prove the determinant definition of the resultant.

    Parameters:
        A: Inferred from the input types unless explicitly supplied.
        B: Inferred from the input types unless explicitly supplied.

    Args:
        a: The first polynomial.
        b: The second polynomial.
        budget: The shared work allowance, including preparation and output storage.

    Returns:
        A retained resultant with an ideal-membership identity for exact.value and exact.check.

    Raises:
        PolyError: DOMAIN for incompatible input, UNSUPPORTED for an unavailable coefficient domain, or LIMIT/CAPACITY on resource limits.
    """
    comptime k = _Join[_Kind[_Element[A]], _Kind[_Element[B]]]
    var pair = _pair[k](a, b, budget)
    var left = _dense_sparse(pair[0]._core[], budget)
    var right = _dense_sparse(pair[1]._core[], budget)
    var proof = _resultant(left, right, Int64(0), budget)
    _allocation[SparsePoly[_Ring[k]]](1, budget)
    var others: List[SparsePoly[_Ring[k]]] = [right^]
    var result = _exact._retain[k, Int, False, ResultantResult[_Ring[k]]](left^, others^, proof^, budget)
    return result^


def resultant_checked[A: Iterable, B: Iterable](a: A, b: B, *, max_steps: UInt64 = UInt64.MAX) raises PolyError -> _exact.Result[_Join[_Kind[_Element[A]], _Kind[_Element[B]]], Int, False, ResultantResult[_Ring[_Join[_Kind[_Element[A]], _Kind[_Element[B]]]]]]:
    """Compute a resultant and retain its ideal-membership identity.

    The checker proves u*a + v*b = result; it does not independently prove the determinant definition of the resultant.

    Parameters:
        A: Inferred from the input types unless explicitly supplied.
        B: Inferred from the input types unless explicitly supplied.

    Args:
        a: The first polynomial.
        b: The second polynomial.
        max_steps: The complete call’s work allowance.

    Returns:
        A retained resultant with an ideal-membership identity for exact.value and exact.check.

    Raises:
        PolyError: DOMAIN for incompatible input, UNSUPPORTED for an unavailable coefficient domain, or LIMIT/CAPACITY on resource limits.
    """
    var budget = Budget(max_steps)
    return resultant_checked[A, B](a, b, budget)


def coprimality[A: Iterable, B: Iterable](a: A, b: B, mut budget: Budget) raises PolyError -> Optional[_exact.Result[_Join[_Kind[_Element[A]], _Kind[_Element[B]]], Int, False, CoprimalityCertificate[_Ring[_Join[_Kind[_Element[A]], _Kind[_Element[B]]]]]]]:
    """Produce a coprimality witness when the inputs have no common nonunit factor.

    None means the producer did not establish coprimality.

    Parameters:
        A: Inferred from the input types unless explicitly supplied.
        B: Inferred from the input types unless explicitly supplied.

    Args:
        a: The first polynomial.
        b: The second polynomial.
        budget: The shared work allowance, including preparation and output storage.

    Returns:
        A retained result for exact.check, or None for an unsuccessful coprimality request.

    Raises:
        PolyError: DOMAIN for incompatible input, UNSUPPORTED for an unavailable coefficient domain, or LIMIT/CAPACITY on resource limits.
    """
    comptime k = _Join[_Kind[_Element[A]], _Kind[_Element[B]]]
    var pair = _pair[k](a, b, budget)
    var left = _dense_sparse(pair[0]._core[], budget)
    var right = _dense_sparse(pair[1]._core[], budget)
    var optional = coprimality_certificate(left, right, budget)
    if not optional:
        return None
    var proof = optional.take()
    _allocation[SparsePoly[_Ring[k]]](1, budget)
    var others: List[SparsePoly[_Ring[k]]] = [right^]
    var result = _exact._retain[k, Int, False, CoprimalityCertificate[_Ring[k]]](left^, others^, proof^, budget)
    return Optional(result^)


def coprimality[A: Iterable, B: Iterable](a: A, b: B, *, max_steps: UInt64 = UInt64.MAX) raises PolyError -> Optional[_exact.Result[_Join[_Kind[_Element[A]], _Kind[_Element[B]]], Int, False, CoprimalityCertificate[_Ring[_Join[_Kind[_Element[A]], _Kind[_Element[B]]]]]]]:
    """Produce a coprimality witness when the inputs have no common nonunit factor.

    None means the producer did not establish coprimality.

    Parameters:
        A: Inferred from the input types unless explicitly supplied.
        B: Inferred from the input types unless explicitly supplied.

    Args:
        a: The first polynomial.
        b: The second polynomial.
        max_steps: The complete call’s work allowance.

    Returns:
        A retained result for exact.check, or None for an unsuccessful coprimality request.

    Raises:
        PolyError: DOMAIN for incompatible input, UNSUPPORTED for an unavailable coefficient domain, or LIMIT/CAPACITY on resource limits.
    """
    var budget = Budget(max_steps)
    return coprimality[A, B](a, b, budget)


def divide_checked[A: Iterable, B: Iterable](a: A, b: B, mut budget: Budget) raises PolyError -> _exact.Result[_FieldKind[_Join[_Kind[_Element[A]], _Kind[_Element[B]]]], Int, False, DivisionResult[_Ring[_FieldKind[_Join[_Kind[_Element[A]], _Kind[_Element[B]]]]]]] where _Kind[_Element[A]] >= 0 and _Kind[_Element[B]] >= 0:
    """Divide exact polynomials and retain the inputs and division evidence.

    Integer inputs promote to QQ. Sparse checking proves the reduction identity without claiming a unique remainder.

    Parameters:
        A: Inferred from the input types unless explicitly supplied.
        B: Inferred from the input types unless explicitly supplied.

    Args:
        a: The first polynomial.
        b: The second polynomial.
        budget: The shared work allowance, including preparation and output storage.

    Returns:
        A retained division for exact.quotient, exact.remainder and exact.check.

    Raises:
        PolyError: DOMAIN for incompatible input, UNSUPPORTED for an unavailable coefficient domain, or LIMIT/CAPACITY on resource limits.
    """
    comptime k = _FieldKind[_Join[_Kind[_Element[A]], _Kind[_Element[B]]]]
    var pair = _pair[k](a, b, budget)
    var left = _dense_sparse(pair[0]._core[], budget)
    var right = _dense_sparse(pair[1]._core[], budget)
    _allocation[SparsePoly[_Ring[k]]](1, budget)
    var others: List[SparsePoly[_Ring[k]]] = [right^]
    comptime F = downcast[_Ring[k], CoefficientField]
    var proof = rebind_var[DivisionResult[_Ring[k]]](_divmod(rebind[DensePoly[F]](pair[0]._core[]), rebind[DensePoly[F]](pair[1]._core[]), budget))
    var result = _exact._retain[k, Int, False, DivisionResult[_Ring[k]]](left^, others^, proof^, budget)
    return result^


def divide_checked[A: Iterable, B: Iterable](a: A, b: B, *, max_steps: UInt64 = UInt64.MAX) raises PolyError -> _exact.Result[_FieldKind[_Join[_Kind[_Element[A]], _Kind[_Element[B]]]], Int, False, DivisionResult[_Ring[_FieldKind[_Join[_Kind[_Element[A]], _Kind[_Element[B]]]]]]] where _Kind[_Element[A]] >= 0 and _Kind[_Element[B]] >= 0:
    """Divide exact polynomials and retain the inputs and division evidence.

    Integer inputs promote to QQ. Sparse checking proves the reduction identity without claiming a unique remainder.

    Parameters:
        A: Inferred from the input types unless explicitly supplied.
        B: Inferred from the input types unless explicitly supplied.

    Args:
        a: The first polynomial.
        b: The second polynomial.
        max_steps: The complete call’s work allowance.

    Returns:
        A retained division for exact.quotient, exact.remainder and exact.check.

    Raises:
        PolyError: DOMAIN for incompatible input, UNSUPPORTED for an unavailable coefficient domain, or LIMIT/CAPACITY on resource limits.
    """
    var budget = Budget(max_steps)
    return divide_checked[A, B](a, b, budget)


def factor_checked[I: Iterable](values: I, mut budget: Budget, *, seed: UInt64 = 0) raises PolyError -> _exact.Result[_Kind[_Element[I]], Int, False, Factorization[_Ring[_Kind[_Element[I]]]]]:
    """Factor the polynomial and retain independently checkable evidence.

    exact.check verifies recomposition. Over AA and QQbar it also verifies monicity, ordering, distinct factors, and irreducibility by degree and negative real quadratic discriminants. Other coefficient domains retain the product-only claim.

    Parameters:
        I: Inferred from the input types unless explicitly supplied.

    Args:
        values: Input coefficients, sparse terms, or a prepared array.
        budget: The shared work allowance, including preparation and output storage.
        seed: The deterministic finite-field factorization seed.

    Returns:
        A retained factorization for exact.unit, exact.factors and exact.check.

    Raises:
        PolyError: DOMAIN for incompatible input, UNSUPPORTED for an unavailable coefficient domain, or LIMIT/CAPACITY on resource limits.
    """
    comptime k = _Kind[_Element[I]]
    var prepared = _prepare(values, budget)
    var ctx = _data_context[k](prepared.modulus(), 0, budget)
    var source = _promote[k](prepared, ctx, budget)
    var input = _dense_sparse(source._core[], budget)
    var proof = _factor_evidence[k](source, budget, seed)
    return _exact._retain[k, Int, False, Factorization[_Ring[k]]](input^, List[SparsePoly[_Ring[k]]](), proof^, budget)


def factor_checked[I: Iterable](values: I, *, seed: UInt64 = 0, max_steps: UInt64 = UInt64.MAX) raises PolyError -> _exact.Result[_Kind[_Element[I]], Int, False, Factorization[_Ring[_Kind[_Element[I]]]]]:
    """Factor the polynomial and retain independently checkable evidence.

    exact.check verifies recomposition. Over AA and QQbar it also verifies monicity, ordering, distinct factors, and irreducibility by degree and negative real quadratic discriminants. Other coefficient domains retain the product-only claim.

    Parameters:
        I: Inferred from the input types unless explicitly supplied.

    Args:
        values: Input coefficients, sparse terms, or a prepared array.
        seed: The deterministic finite-field factorization seed.
        max_steps: The complete call’s work allowance.

    Returns:
        A retained factorization for exact.unit, exact.factors and exact.check.

    Raises:
        PolyError: DOMAIN for incompatible input, UNSUPPORTED for an unavailable coefficient domain, or LIMIT/CAPACITY on resource limits.
    """
    var budget = Budget(max_steps)
    return factor_checked[I](values, budget, seed=seed)


def squarefree_checked[I: Iterable](values: I, mut budget: Budget) raises PolyError -> _exact.Result[_FieldKind[_Kind[_Element[I]]], Int, False, SquarefreeDecomposition[_Ring[_FieldKind[_Kind[_Element[I]]]]]]:
    """Decompose by multiplicity and retain the product identity.

    The checker verifies recomposition. It does not certify irreducibility or squarefreeness of the factors.

    Parameters:
        I: Inferred from the input types unless explicitly supplied.

    Args:
        values: Input coefficients, sparse terms, or a prepared array.
        budget: The shared work allowance, including preparation and output storage.

    Returns:
        A retained factorization for exact.unit, exact.factors and exact.check.

    Raises:
        PolyError: DOMAIN for incompatible input, UNSUPPORTED for an unavailable coefficient domain, or LIMIT/CAPACITY on resource limits.
    """
    comptime k = _FieldKind[_Kind[_Element[I]]]
    var prepared = _prepare(values, budget)
    var ctx = _data_context[k](prepared.modulus(), 0, budget)
    var source = _promote[k](prepared, ctx, budget)
    var input = _dense_sparse(source._core[], budget)
    comptime F = downcast[_Ring[k], CoefficientField]
    var proof = rebind_var[SquarefreeDecomposition[_Ring[k]]](_squarefree[F](rebind[DensePoly[F]](source._core[]), budget))
    return _exact._retain[k, Int, False, SquarefreeDecomposition[_Ring[k]]](input^, List[SparsePoly[_Ring[k]]](), proof^, budget)


def squarefree_checked[I: Iterable](values: I, *, max_steps: UInt64 = UInt64.MAX) raises PolyError -> _exact.Result[_FieldKind[_Kind[_Element[I]]], Int, False, SquarefreeDecomposition[_Ring[_FieldKind[_Kind[_Element[I]]]]]]:
    """Decompose by multiplicity and retain the product identity.

    The checker verifies recomposition. It does not certify irreducibility or squarefreeness of the factors.

    Parameters:
        I: Inferred from the input types unless explicitly supplied.

    Args:
        values: Input coefficients, sparse terms, or a prepared array.
        max_steps: The complete call’s work allowance.

    Returns:
        A retained factorization for exact.unit, exact.factors and exact.check.

    Raises:
        PolyError: DOMAIN for incompatible input, UNSUPPORTED for an unavailable coefficient domain, or LIMIT/CAPACITY on resource limits.
    """
    var budget = Budget(max_steps)
    return squarefree_checked[I](values, budget)


def interpolate_checked[A: Iterable, B: Iterable](points: A, values: B, mut budget: Budget) raises PolyError -> _exact.Result[_FieldKind[_Join[_Kind[_Element[A]], _Kind[_Element[B]]]], Int, False, _exact._Interpolation[_Ring[_FieldKind[_Join[_Kind[_Element[A]], _Kind[_Element[B]]]]]]]:
    """Interpolate distinct nodes exactly; integer data promotes to QQ.

    Nodes must be distinct and sample counts must match. Empty data returns zero; trailing zero samples are retained as constraints.

    Parameters:
        A: The first inferred iterable type.
        B: The second inferred iterable type.

    Args:
        points: A one-dimensional sequence of exact points, in output order.
        values: Exact samples in node order, including every zero.
        budget: The caller-owned work allowance, shared through preparation and computation.

    Returns:
        A retained interpolant and its constraints for exact.value and exact.check.

    Raises:
        PolyError: LIMIT on exhausted work, CAPACITY on unrepresentable sizes, DOMAIN for invalid input, or UNSUPPORTED for a documented domain restriction.
    """
    comptime k = _FieldKind[_Join[_Kind[_Element[A]], _Kind[_Element[B]]]]
    comptime F = downcast[_Ring[k], CoefficientField]
    var nodes = _sequence(points, budget)
    var samples = _sequence(values, budget)
    var ctx = _data_context[k](nodes.modulus(), samples.modulus(), budget)
    var xs = _sequence_coefficients[k](nodes, ctx, budget)
    var ys = _sequence_coefficients[k](samples, ctx, budget)
    var polynomial = rebind_var[DensePoly[_Ring[k]]](_interpolate[F](0, rebind[F.Context](ctx), rebind[List[F]](xs), rebind[List[F]](ys), budget))
    var input = _dense_sparse(polynomial, budget)
    var proof = _exact._Interpolation[_Ring[k]](xs^, ys^, List[List[_Ring[k]]](), False, False)
    return _exact._retain[k, Int, False, _exact._Interpolation[_Ring[k]]](input^, List[SparsePoly[_Ring[k]]](), proof^, budget)


def interpolate_checked[A: Iterable, B: Iterable](points: A, values: B, *, max_steps: UInt64 = UInt64.MAX) raises PolyError -> _exact.Result[_FieldKind[_Join[_Kind[_Element[A]], _Kind[_Element[B]]]], Int, False, _exact._Interpolation[_Ring[_FieldKind[_Join[_Kind[_Element[A]], _Kind[_Element[B]]]]]]]:
    """Interpolate distinct nodes exactly; integer data promotes to QQ.

    Nodes must be distinct and sample counts must match. Empty data returns zero; trailing zero samples are retained as constraints.

    Parameters:
        A: The first inferred iterable type.
        B: The second inferred iterable type.

    Args:
        points: A one-dimensional sequence of exact points, in output order.
        values: Exact samples in node order, including every zero.
        max_steps: The complete call's work allowance; defaults to UInt64.MAX.

    Returns:
        A retained interpolant and its constraints for exact.value and exact.check.

    Raises:
        PolyError: LIMIT on exhausted work, CAPACITY on unrepresentable sizes, DOMAIN for invalid input, or UNSUPPORTED for a documented domain restriction.
    """
    var budget = Budget(max_steps)
    return interpolate_checked(points, values, budget)


def hermite_interpolate_checked[A: Iterable, B: Iterable](points: A, jets: B, mut budget: Budget, *, derivatives: Bool = True) raises PolyError -> _exact.Result[_FieldKind[_Join[_Kind[_Element[A]], _Kind[_Element[_Nested[B]]]]], Int, False, _exact._Interpolation[_Ring[_FieldKind[_Join[_Kind[_Element[A]], _Kind[_Element[_Nested[B]]]]]]]]:
    """Interpolate value and consecutive derivative constraints at distinct nodes.

    Node and jet counts must match, nodes must be distinct, and each jet must be nonempty. Raw derivatives in a finite field require invertible factorials; use derivatives=False for Taylor coefficients.

    Parameters:
        A: The first inferred iterable type.
        B: The second inferred iterable type.

    Args:
        points: A one-dimensional sequence of exact points, in output order.
        jets: One nonempty exact sequence per node, beginning with the value and followed by consecutive derivatives.
        budget: The caller-owned work allowance, shared through preparation and computation.
        derivatives: True interprets jets as raw derivatives; False interprets them as Taylor coefficients.

    Returns:
        A retained interpolant and all Hermite constraints for exact.value and exact.check.

    Raises:
        PolyError: LIMIT on exhausted work, CAPACITY on unrepresentable sizes, DOMAIN for invalid input, or UNSUPPORTED for a documented domain restriction.
    """
    comptime k = _FieldKind[_Join[_Kind[_Element[A]], _Kind[_Element[_Nested[B]]]]]
    comptime F = downcast[_Ring[k], CoefficientField]
    var nodes = _sequence(points, budget)
    var rows = _rows(jets, budget)
    var modulus = nodes.modulus()
    for row in rows:
        budget.charge(1)
        modulus = _merge_modulus(modulus, row.modulus())
    var ctx = _data_context[k](modulus, 0, budget)
    var xs = _sequence_coefficients[k](nodes, ctx, budget)
    _allocation[List[F]](len(rows), budget)
    var ys = List[List[F]](capacity=len(rows))
    for row in rows:
        ys.append(rebind_var[List[F]](_sequence_coefficients[k](row, ctx, budget)))
    var polynomial = rebind_var[DensePoly[_Ring[k]]](_hermite_interpolate[F](0, rebind[F.Context](ctx), rebind[List[F]](xs), ys, budget, derivatives=derivatives))
    var input = _dense_sparse(polynomial, budget)
    var proof = _exact._Interpolation[_Ring[k]](xs^, List[_Ring[k]](), rebind_var[List[List[_Ring[k]]]](ys^), derivatives, True)
    return _exact._retain[k, Int, False, _exact._Interpolation[_Ring[k]]](input^, List[SparsePoly[_Ring[k]]](), proof^, budget)


def hermite_interpolate_checked[A: Iterable, B: Iterable](points: A, jets: B, *, max_steps: UInt64 = UInt64.MAX, derivatives: Bool = True) raises PolyError -> _exact.Result[_FieldKind[_Join[_Kind[_Element[A]], _Kind[_Element[_Nested[B]]]]], Int, False, _exact._Interpolation[_Ring[_FieldKind[_Join[_Kind[_Element[A]], _Kind[_Element[_Nested[B]]]]]]]]:
    """Interpolate value and consecutive derivative constraints at distinct nodes.

    Node and jet counts must match, nodes must be distinct, and each jet must be nonempty. Raw derivatives in a finite field require invertible factorials; use derivatives=False for Taylor coefficients.

    Parameters:
        A: The first inferred iterable type.
        B: The second inferred iterable type.

    Args:
        points: A one-dimensional sequence of exact points, in output order.
        jets: One nonempty exact sequence per node, beginning with the value and followed by consecutive derivatives.
        max_steps: The complete call's work allowance; defaults to UInt64.MAX.
        derivatives: True interprets jets as raw derivatives; False interprets them as Taylor coefficients.

    Returns:
        A retained interpolant and all Hermite constraints for exact.value and exact.check.

    Raises:
        PolyError: LIMIT on exhausted work, CAPACITY on unrepresentable sizes, DOMAIN for invalid input, or UNSUPPORTED for a documented domain restriction.
    """
    var budget = Budget(max_steps)
    return hermite_interpolate_checked(points, jets, budget, derivatives=derivatives)


def divide_many_checked[A: Iterable, B: Iterable](values: A, divisors: B, mut budget: Budget) raises PolyError -> _exact.Result[_FieldKind[_Join[_Kind[_Element[A]], _Kind[_Element[_Nested[B]]]]], Int, False, ListDivision[_Ring[_FieldKind[_Join[_Kind[_Element[A]], _Kind[_Element[_Nested[B]]]]]]]]:
    """Divide by ordered polynomials and retain the exact recomposition identity.

    Sparse reduction uses lexicographic order with axis zero first. Changing divisor order can change quotients and remainder; this is not a Groebner-basis computation. An empty divisor collection returns no quotients and the promoted input as remainder. A zero divisor raises DOMAIN.

    Parameters:
        A: The first inferred iterable type.
        B: The second inferred iterable type.

    Args:
        values: The coefficient sequence, sparse terms, or prepared array.
        divisors: A finite iterable of polynomials of one Mojo input type, tried in the supplied order.
        budget: The caller-owned work allowance, shared through preparation and computation.

    Returns:
        A retained result for exact.quotients, exact.remainder and exact.check; the check establishes the identity, not a unique reduced remainder.

    Raises:
        PolyError: LIMIT on exhausted work, CAPACITY on unrepresentable sizes, DOMAIN for invalid input, or UNSUPPORTED for a documented domain restriction.
    """
    comptime k = _FieldKind[_Join[_Kind[_Element[A]], _Kind[_Element[_Nested[B]]]]]
    comptime F = downcast[_Ring[k], CoefficientField]
    var prepared = _many[k](values, divisors, budget)
    _allocation[SparsePoly[F]](len(prepared[1]), budget)
    var cores = List[SparsePoly[F]](capacity=len(prepared[1]))
    for q in prepared[1]:
        cores.append(rebind_var[SparsePoly[F]](_dense_sparse(q._core[], budget)))
    var p = _dense_sparse(prepared[0]._core[], budget)
    var result = _divide_by_list[F](rebind[SparsePoly[F]](p), cores, budget)
    return _exact._retain[k, Int, False, ListDivision[_Ring[k]]](p^, rebind_var[List[SparsePoly[_Ring[k]]]](cores^), rebind_var[ListDivision[_Ring[k]]](result^), budget)



def divide_many_checked[A: Iterable, B: Iterable](values: A, divisors: B, *, max_steps: UInt64 = UInt64.MAX) raises PolyError -> _exact.Result[_FieldKind[_Join[_Kind[_Element[A]], _Kind[_Element[_Nested[B]]]]], Int, False, ListDivision[_Ring[_FieldKind[_Join[_Kind[_Element[A]], _Kind[_Element[_Nested[B]]]]]]]]:
    """Divide by ordered polynomials and retain the exact recomposition identity.

    Sparse reduction uses lexicographic order with axis zero first. Changing divisor order can change quotients and remainder; this is not a Groebner-basis computation. An empty divisor collection returns no quotients and the promoted input as remainder. A zero divisor raises DOMAIN.

    Parameters:
        A: The first inferred iterable type.
        B: The second inferred iterable type.

    Args:
        values: The coefficient sequence, sparse terms, or prepared array.
        divisors: A finite iterable of polynomials of one Mojo input type, tried in the supplied order.
        max_steps: The complete call's work allowance; defaults to UInt64.MAX.

    Returns:
        A retained result for exact.quotients, exact.remainder and exact.check; the check establishes the identity, not a unique reduced remainder.

    Raises:
        PolyError: LIMIT on exhausted work, CAPACITY on unrepresentable sizes, DOMAIN for invalid input, or UNSUPPORTED for a documented domain restriction.
    """
    var budget = Budget(max_steps)
    return divide_many_checked(values, divisors, budget)


def _factor_evidence[k: Int](p: Array[k], mut budget: Budget, seed: UInt64) raises PolyError -> Factorization[_Ring[k]]:
    comptime if k == 0:
        return rebind_var[Factorization[_Ring[k]]](_factor_integer(rebind[DensePoly[ZZ]](p._core[]), budget))
    elif k == 1:
        return rebind_var[Factorization[_Ring[k]]](_factor(rebind[DensePoly[QQ]](p._core[]), budget))
    elif k == 2:
        return rebind_var[Factorization[_Ring[k]]](_factor_gaussian(rebind[DensePoly[QQi]](p._core[]), budget))
    elif k == 3:
        return rebind_var[Factorization[_Ring[k]]](_factor_finite_field(rebind[DensePoly[ModInt]](p._core[]), budget, seed))

    else:
        from . import _algebraic_factor
        return _algebraic_factor._factor(p._core[], budget)


from polynomials import sign_on_interval as _sign_on_interval, projection_resultant as _projection_resultant

def sign_on_interval[I: Iterable, L: Copyable & Deinitable, H: Copyable & Deinitable](values: I, low: L, high: H, mut budget: Budget) raises PolyError -> Optional[Int]:
    """Determine the strict sign throughout a closed exact interval.

    Parameters:
        I: The inferred input type.
        L: The inferred input type.
        H: The inferred input type.

    Args:
        values: Ascending integer or rational coefficients.
        low: The lower rational or integer endpoint.
        high: The upper rational or integer endpoint, possibly equal to low.
        budget: The shared work allowance for preparation and computation.

    Returns:
        Positive or negative one if the interval is root-free; None if it contains a root, including either endpoint. The zero polynomial returns None.

    Raises:
        PolyError: DOMAIN for incompatible input, UNSUPPORTED for an unavailable operation, or LIMIT/CAPACITY on resource limits.
    """
    comptime if _AlgebraicInterval[_Element[I], L, H]:
        var p = asarray(values, budget)
        var a = _algebraic.asreal(low, budget)
        var b = _algebraic.asreal(high, budget)
        if _algebraic.compare(a, b, budget) > 0:
            raise PolyError(PolyErrorKind.DOMAIN, "sign interval is reversed")
        if len(p) == 0:
            return None
        var result = real_roots(p, budget)
        for root in result:
            if _algebraic.compare(root, a, budget) >= 0 and _algebraic.compare(root, b, budget) <= 0:
                return None
        var value = _algebraic.asreal(evaluate(p, a, budget), budget)
        return _algebraic.compare(value, 0, budget)
    else:
        var p = _real_input(values, budget)
        var a = QQ(_convert[1](low, NoContext(), budget))
        var b = QQ(_convert[1](high, NoContext(), budget))
        return _sign_on_interval(p._core[], a, b, budget)



def sign_on_interval[I: Iterable, L: Copyable & Deinitable, H: Copyable & Deinitable](values: I, low: L, high: H, *, max_steps: UInt64 = UInt64.MAX) raises PolyError -> Optional[Int]:
    """Determine the strict sign throughout a closed exact interval.

    Parameters:
        I: The inferred input type.
        L: The inferred input type.
        H: The inferred input type.

    Args:
        values: Ascending integer or rational coefficients.
        low: The lower rational or integer endpoint.
        high: The upper rational or integer endpoint, possibly equal to low.
        max_steps: The complete call's work allowance; defaults to UInt64.MAX.

    Returns:
        Positive or negative one if the interval is root-free; None if it contains a root, including either endpoint. The zero polynomial returns None.

    Raises:
        PolyError: DOMAIN for incompatible input, UNSUPPORTED for an unavailable operation, or LIMIT/CAPACITY on resource limits.
    """
    var budget = Budget(max_steps)
    return sign_on_interval(values, low, high, budget)



def resultant_certified[A: Iterable, B: Iterable](a: A, b: B, mut budget: Budget) raises PolyError -> _exact.Result[_FieldKind[_Join[_Kind[_Element[A]], _Kind[_Element[B]]]], Int, False, _exact._Determinant[_FieldKind[_Join[_Kind[_Element[A]], _Kind[_Element[B]]]]]]:
    """Compute an exact resultant with a complete determinant certificate.

    Integer coefficients promote to rationals. exact.check verifies the Sylvester determinant transcript; exact.value returns its constant coefficient array.

    Parameters:
        A: Inferred from the input types unless explicitly supplied.
        B: Inferred from the input types unless explicitly supplied.

    Args:
        a: The first polynomial.
        b: The second polynomial.
        budget: The shared work allowance, including preparation and output storage.

    Returns:
        A retained exact resultant and determinant evidence for exact.value and exact.check.

    Raises:
        PolyError: DOMAIN for incompatible input, UNSUPPORTED for an unavailable coefficient domain, or LIMIT/CAPACITY on resource limits.
    """
    comptime k = _FieldKind[_Join[_Kind[_Element[A]], _Kind[_Element[B]]]]
    var pair = _pair[k](a, b, budget)
    var left = _dense_sparse(pair[0]._core[], budget)
    var right = _dense_sparse(pair[1]._core[], budget)
    var proof: _exact._Determinant[k]
    comptime if k == 1:
        proof = rebind_var[_exact._Determinant[k]](_projection_resultant(rebind[SparsePoly[QQ]](left), rebind[SparsePoly[QQ]](right), Int64(0), budget))
    else:
        from . import _determinant
        proof = rebind_var[_exact._Determinant[k]](_determinant._produce(left, right, Int64(0), budget))
    _allocation[SparsePoly[_Ring[k]]](1, budget)
    var others: List[SparsePoly[_Ring[k]]] = [right^]
    var result = _exact._retain[k, Int, False, _exact._Determinant[_FieldKind[_Join[_Kind[_Element[A]], _Kind[_Element[B]]]]]](left^, others^, proof^, budget)
    return result^



def resultant_certified[A: Iterable, B: Iterable](a: A, b: B, *, max_steps: UInt64 = UInt64.MAX) raises PolyError -> _exact.Result[_FieldKind[_Join[_Kind[_Element[A]], _Kind[_Element[B]]]], Int, False, _exact._Determinant[_FieldKind[_Join[_Kind[_Element[A]], _Kind[_Element[B]]]]]]:
    """Compute an exact resultant with a complete determinant certificate.

    Integer coefficients promote to rationals. exact.check verifies the Sylvester determinant transcript; exact.value returns its constant coefficient array.

    Parameters:
        A: Inferred from the input types unless explicitly supplied.
        B: Inferred from the input types unless explicitly supplied.

    Args:
        a: The first polynomial.
        b: The second polynomial.
        max_steps: The complete call’s work allowance.

    Returns:
        A retained exact resultant and determinant evidence for exact.value and exact.check.

    Raises:
        PolyError: DOMAIN for incompatible input, UNSUPPORTED for an unavailable coefficient domain, or LIMIT/CAPACITY on resource limits.
    """
    var budget = Budget(max_steps)
    return resultant_certified[A, B](a, b, budget)


def complex_roots[I: Iterable](values: I, mut budget: Budget) raises PolyError -> _roots.ComplexRoots:
    """Find every distinct exact complex root, with multiplicities.

    Results use lexicographic real-part then imaginary-part order. Nonzero
    constants return no roots. Integer, rational, Gaussian-rational, AA, and
    QQbar coefficients are accepted; no numerical precision is needed.

    Parameters:
        I: The inferred input iterable type.

    Args:
        values: Ascending exact coefficients or a prepared dense array.
        budget: The shared work allowance, including preparation and verification.

    Returns:
        Exact algebraic.Complex values with multiplicities and completeness evidence.

    Raises:
        PolyError: DOMAIN for zero or incompatible input, or LIMIT/CAPACITY on resource limits.
    """
    comptime assert _Kind[_Element[I]] >= 0 and _Kind[_Element[I]] != 3, "exact complex roots require characteristic-zero exact coefficients"
    var p = _promote[5](_prepare(values, budget), NoContext(), budget)
    return _roots._complex._solve(p._core[], budget)


def complex_roots[I: Iterable](values: I, *, max_steps: UInt64 = UInt64.MAX) raises PolyError -> _roots.ComplexRoots:
    """Find every distinct exact complex root, with multiplicities.

    Results use lexicographic real-part then imaginary-part order. Nonzero
    constants return no roots. Integer, rational, Gaussian-rational, AA, and
    QQbar coefficients are accepted; no numerical precision is needed.

    Parameters:
        I: The inferred input iterable type.

    Args:
        values: Ascending exact coefficients or a prepared dense array.
        max_steps: The complete call's work allowance; defaults to UInt64.MAX.

    Returns:
        Exact algebraic.Complex values with multiplicities and completeness evidence.

    Raises:
        PolyError: DOMAIN for zero or incompatible input, or LIMIT/CAPACITY on resource limits.
    """
    var budget = Budget(max_steps)
    return complex_roots(values, budget)


def complex_roots_to[I: Iterable, S: _roots.ExactComplexRootSink](values: I, mut sink: S, mut budget: Budget) raises PolyError -> _roots.ExactComplexRootReceipt:
    """Stream exact complex roots with multiplicities and a completion receipt.

    Parameters:
        I: The inferred coefficient iterable.
        S: The event consumer type.

    Args:
        values: Exact coefficients or terms over ZZ, QQ, QQi, AA, or QQbar.
        sink: A consumer of owned ExactComplexRootEvent values.
        budget: The shared preparation, production, and checking allowance.

    Returns:
        A receipt to verify with checker.finish. Events follow deterministic
        factor and coordinate traversal order, which need not be sorted.
        Output witnesses are not collected; algebraic working state is retained.

    Raises:
        PolyError: DOMAIN for zero or invalid input, consumer failures, or
            LIMIT/CAPACITY on resource limits. Partial streams are not complete results.
    """
    comptime assert _Kind[_Element[I]] >= 0 and _Kind[_Element[I]] != 3, "exact complex roots require characteristic-zero exact coefficients"
    var p = _promote[5](_prepare(values, budget), NoContext(), budget)
    return _roots._complex._solve_to(p._core[], sink, budget)


def complex_roots_to[I: Iterable, S: _roots.ExactComplexRootSink](values: I, mut sink: S, *, max_steps: UInt64 = UInt64.MAX) raises PolyError -> _roots.ExactComplexRootReceipt:
    """Stream exact complex roots with multiplicities and a completion receipt.

    Parameters:
        I: The inferred coefficient iterable.
        S: The event consumer type.

    Args:
        values: Exact coefficients or terms over ZZ, QQ, QQi, AA, or QQbar.
        sink: A consumer of owned ExactComplexRootEvent values.
        max_steps: The complete call's work allowance.

    Returns:
        A receipt to verify with checker.finish. Events follow deterministic
        factor and coordinate traversal order, which need not be sorted.
        Output witnesses are not collected; algebraic working state is retained.

    Raises:
        PolyError: DOMAIN for zero or invalid input, consumer failures, or
            LIMIT/CAPACITY on resource limits. Partial streams are not complete results.
    """
    var budget = Budget(max_steps)
    return complex_roots_to(values, sink, budget)


def complex_roots_checker[I: Iterable](values: I, mut budget: Budget) raises PolyError -> _roots.ExactComplexRootChecker:
    """Prepare independent incremental checking of exact complex roots.

    Parameters:
        I: The inferred coefficient iterable.

    Args:
        values: Exact coefficients or terms over ZZ, QQ, QQi, AA, or QQbar.
        budget: The shared preparation, production, and checking allowance.

    Returns:
        A checker accepting root events; finish verifies complete reconstruction.

    Raises:
        PolyError: DOMAIN for zero or invalid input, consumer failures, or
            LIMIT/CAPACITY on resource limits. Partial streams are not complete results.
    """
    comptime assert _Kind[_Element[I]] >= 0 and _Kind[_Element[I]] != 3, "exact complex roots require characteristic-zero exact coefficients"
    var p = _promote[5](_prepare(values, budget), NoContext(), budget)
    return _roots._complex._checker(p._core[], budget)


def complex_roots_checker[I: Iterable](values: I, *, max_steps: UInt64 = UInt64.MAX) raises PolyError -> _roots.ExactComplexRootChecker:
    """Prepare independent incremental checking of exact complex roots.

    Parameters:
        I: The inferred coefficient iterable.

    Args:
        values: Exact coefficients or terms over ZZ, QQ, QQi, AA, or QQbar.
        max_steps: The complete call's work allowance.

    Returns:
        A checker accepting root events; finish verifies complete reconstruction.

    Raises:
        PolyError: DOMAIN for zero or invalid input, consumer failures, or
            LIMIT/CAPACITY on resource limits. Partial streams are not complete results.
    """
    var budget = Budget(max_steps)
    return complex_roots_checker(values, budget)

comptime _RealCover[k: Int] = _roots.AlgebraicCover[k, False] if k >= 4 else _roots.RealCover[1]
comptime _ComplexCover[k: Int] = _roots.AlgebraicCover[k, True] if k >= 4 else _roots.ComplexCover[k]
comptime _RealChecker[k: Int] = _roots.AlgebraicRealRootChecker[k] if k >= 4 else RealRootStreamChecker
comptime _ComplexChecker[k: Int] = _roots.AlgebraicComplexRootChecker[k] if k >= 4 else ComplexRootStreamChecker

from . import _numeric_interop as _ni


def astype[dtype: AnyType, I: Iterable, Context: Copyable & Deinitable](values: I, mut budget: Budget, *, context: Context) raises PolyError -> NumericArray[_num._StoredDomain[dtype]]:
    """Convert every coefficient to an explicit numerical type and precision.

    Unlike asarray on a prepared array, this also converts within the same
    domain. Real destinations require exactly zero imaginary bounds; point
    destinations require certain rounding. Inputs remain unchanged.

    Parameters:
        dtype: Float, Complex, Ball, or ComplexBall.
        I: The inferred coefficient iterable type.
        Context: The matching explicit precision context.

    Args:
        values: Raw coefficients or a prepared dense array.
        budget: The shared conversion allowance.
        context: ArithmeticContext for Float, ComplexContext for Complex, or BallContext for balls.

    Returns:
        An immutable array with rounded points or enclosing balls in the requested type.

    Raises:
        PolyError: DOMAIN for nonreal or uncertain point conversion, or LIMIT/CAPACITY.
    """
    comptime assert dtype == _num.Float or dtype == _num.Complex or dtype == _num.Ball or dtype == _num.ComplexBall, "dtype must be Float, Complex, Ball, or ComplexBall"
    comptime D = _num._StoredDomain[dtype]
    comptime assert Context == D.Context, "context must match the requested dtype"
    var ctx = rebind[D.Context](context).copy()
    _num._context[D](ctx, budget)
    var entries = List[D.Scalar]()
    _num._check_sequence(values)
    var cursor = iter(values)
    while True:
        budget.charge(1)
        var value: downcast[_Element[I], Copyable & Deinitable]
        try:
            value = rebind_var[downcast[_Element[I], Copyable & Deinitable]](next(cursor))
        except StopIteration:
            break
        _grow(entries, budget)
        entries.append(_num._value[D](value, ctx, budget))
    return NumericArray[D](NumericDensePoly[D].from_coefficients(0, entries^, budget), budget)


def astype[dtype: AnyType, I: Iterable, Context: Copyable & Deinitable](values: I, *, context: Context, max_steps: UInt64 = UInt64.MAX) raises PolyError -> NumericArray[_num._StoredDomain[dtype]]:
    """Convert every coefficient to an explicit numerical type and precision.

    Unlike asarray on a prepared array, this also converts within the same
    domain. Real destinations require exactly zero imaginary bounds; point
    destinations require certain rounding. Inputs remain unchanged.

    Parameters:
        dtype: Float, Complex, Ball, or ComplexBall.
        I: The inferred coefficient iterable type.
        Context: The matching explicit precision context.

    Args:
        values: Raw coefficients or a prepared dense array.
        context: ArithmeticContext for Float, ComplexContext for Complex, or BallContext for balls.
        max_steps: The complete conversion allowance.

    Returns:
        An immutable array with rounded points or enclosing balls in the requested type.

    Raises:
        PolyError: DOMAIN for nonreal or uncertain point conversion, or LIMIT/CAPACITY.
    """
    var budget = Budget(max_steps)
    return astype[dtype](values, budget, context=context)


def astype[dtype: AnyType, Context: Copyable & Deinitable, *Ts: Copyable & Deinitable](values: Tuple[*Ts], mut budget: Budget, *, context: Context) raises PolyError -> NumericArray[_num._StoredDomain[dtype]]:
    """Convert every coefficient to an explicit numerical type and precision.

    Unlike asarray on a prepared array, this also converts within the same
    domain. Real destinations require exactly zero imaginary bounds; point
    destinations require certain rounding. Inputs remain unchanged.

    Parameters:
        dtype: Float, Complex, Ball, or ComplexBall.
        Context: The matching explicit precision context.
        Ts: The inferred mixed coefficient types.

    Args:
        values: Raw coefficients or a prepared dense array.
        budget: The shared conversion allowance.
        context: ArithmeticContext for Float, ComplexContext for Complex, or BallContext for balls.

    Returns:
        An immutable array with rounded points or enclosing balls in the requested type.

    Raises:
        PolyError: DOMAIN for nonreal or uncertain point conversion, or LIMIT/CAPACITY.
    """
    comptime assert dtype == _num.Float or dtype == _num.Complex or dtype == _num.Ball or dtype == _num.ComplexBall, "dtype must be Float, Complex, Ball, or ComplexBall"
    comptime D = _num._StoredDomain[dtype]
    comptime assert Context == D.Context, "context must match the requested dtype"
    var ctx = rebind[D.Context](context).copy()
    _num._context[D](ctx, budget)
    var entries = List[D.Scalar]()
    _allocation[D.Scalar](Tuple[*Ts].Ts.length, budget)
    entries.reserve(Tuple[*Ts].Ts.length)
    comptime for i in range(Tuple[*Ts].Ts.length):
        budget.charge(1)
        entries.append(_num._value[D](values[i], ctx, budget))
    return NumericArray[D](NumericDensePoly[D].from_coefficients(0, entries^, budget), budget)


def astype[dtype: AnyType, Context: Copyable & Deinitable, *Ts: Copyable & Deinitable](values: Tuple[*Ts], *, context: Context, max_steps: UInt64 = UInt64.MAX) raises PolyError -> NumericArray[_num._StoredDomain[dtype]]:
    """Convert every coefficient to an explicit numerical type and precision.

    Unlike asarray on a prepared array, this also converts within the same
    domain. Real destinations require exactly zero imaginary bounds; point
    destinations require certain rounding. Inputs remain unchanged.

    Parameters:
        dtype: Float, Complex, Ball, or ComplexBall.
        Context: The matching explicit precision context.
        Ts: The inferred mixed coefficient types.

    Args:
        values: Raw coefficients or a prepared dense array.
        context: ArithmeticContext for Float, ComplexContext for Complex, or BallContext for balls.
        max_steps: The complete conversion allowance.

    Returns:
        An immutable array with rounded points or enclosing balls in the requested type.

    Raises:
        PolyError: DOMAIN for nonreal or uncertain point conversion, or LIMIT/CAPACITY.
    """
    var budget = Budget(max_steps)
    return astype[dtype](values, budget, context=context)

from . import _sturm


def sturm_sequence[I: Iterable](values: I, mut budget: Budget) raises PolyError -> _sturm.SturmPlan:
    """Prepare a reusable rational Sturm chain for root and sign-variation queries.

    Parameters:
        I: The inferred polynomial iterable.

    Args:
        values: Nonzero polynomial coefficients over ZZ or QQ.
        budget: The shared preparation allowance.

    Returns:
        An immutable plan retaining the polynomial, chain, and quotient witnesses.

    Raises:
        PolyError: DOMAIN for the zero polynomial, or LIMIT/CAPACITY.
    """
    comptime assert _Kind[_Element[I]] == 0 or _Kind[_Element[I]] == 1, "Sturm preparation requires integer or rational coefficients"
    var prepared = _prepare(values, budget)
    return _sturm._make(to_core(_promote[1](prepared, NoContext(), budget), budget), budget)


def sturm_sequence[I: Iterable](values: I, *, max_steps: UInt64 = UInt64.MAX) raises PolyError -> _sturm.SturmPlan:
    """Prepare a reusable rational Sturm chain for root and sign-variation queries.

    Parameters:
        I: The inferred polynomial iterable.

    Args:
        values: Nonzero polynomial coefficients over ZZ or QQ.
        max_steps: The complete preparation allowance.

    Returns:
        An immutable plan retaining the polynomial, chain, and quotient witnesses.

    Raises:
        PolyError: DOMAIN for the zero polynomial, or LIMIT/CAPACITY.
    """
    var budget = Budget(max_steps)
    return sturm_sequence(values, budget)

def _scalar_operation[op: Int, reverse: Bool, I: Iterable, S: Copyable & Deinitable](values: I, scalar: S, mut budget: Budget) raises PolyError -> Array[_FieldKind[_Join[_Kind[_Element[I]], _Kind[S]]] if op == 3 else _Join[_Kind[_Element[I]], _Kind[S]]] where (_Kind[_Element[I]] >= 0 and _Kind[S] >= 0):
    comptime k = _FieldKind[_Join[_Kind[_Element[I]], _Kind[S]]] if op == 3 else _Join[_Kind[_Element[I]], _Kind[S]]
    var p: Array[k]
    var ctx: _Ring[k].Context
    comptime if k == 3 and S == ModInt:
        ctx = _data_context[k](_initial_modulus(values), rebind[ModInt](scalar).modulus, budget)
        p = rebind_var[Array[k]](asarray(values, budget, modulus=rebind[Modulus](ctx).value))
    else:
        var original = _prepare(values, budget)
        ctx = _data_context[k](original.modulus(), 0, budget)
        p = _promote[k](original, ctx, budget)
    var c = _wrap[k](_convert[k](scalar, ctx, budget))
    comptime if op == 2:
        return Array[k](p._core[].scale(c, budget), budget)
    elif op == 3:
        return Array[k](p._core[].scale(rebind_var[_Ring[k]](rebind[downcast[_Ring[k], CoefficientField]](c).inverse(budget)), budget), budget)
    else:
        _allocation[_Ring[k]](1, budget)
        var q = DensePoly[_Ring[k]].from_coefficients(0, ctx, [c^], budget)
        comptime if op == 0:
            return Array[k](p._core[].add(q, budget), budget)
        elif reverse:
            return Array[k](q.sub(p._core[], budget), budget)
        else:
            return Array[k](p._core[].sub(q, budget), budget)


def _numeric_scalar_operation[op: Int, reverse: Bool, D: NumericDomain, S: Copyable & Deinitable](values: NumericArray[D], scalar: S, mut budget: Budget, *, context: D.Context) raises PolyError -> NumericArray[D]:
    _num._context[D](context, budget)
    var c = _num._value[D](scalar, context, budget)
    comptime if op == 2 or op == 3:
        return NumericArray[D](values._core[].scale(c, context, budget, divide=op == 3), budget)
    else:
        _allocation[D.Scalar](1, budget)
        var q = NumericDensePoly[D].from_coefficients(0, [c^], budget)
        comptime if op == 0:
            return NumericArray[D](values._core[].add(q, context, budget), budget)
        elif reverse:
            return NumericArray[D](q.sub(values._core[], context, budget), budget)
        else:
            return NumericArray[D](values._core[].sub(q, context, budget), budget)


def add[I: Iterable, S: Copyable & Deinitable](values: I, scalar: S, mut budget: Budget) raises PolyError -> Array[_Join[_Kind[_Element[I]], _Kind[S]]] where (_Kind[_Element[I]] >= 0 and _Kind[S] >= 0):
    """Add a scalar constant to a polynomial.

    Exact domains promote together. Modular inputs must have the same
    prime. Inputs remain unchanged.

    Parameters:
        I: The inferred polynomial iterable.
        S: The scalar operand type.

    Args:
        values: Ascending coefficients or a prepared array.
        scalar: The scalar constant.
        budget: The shared work allowance, including conversion and storage.

    Returns:
        A new polynomial in the common exact domain.

    Raises:
        PolyError: DOMAIN for incompatible scalars; LIMIT/CAPACITY on resource limits.
    """
    return _scalar_operation[0, False, I, S](values, scalar, budget)


def add[I: Iterable, S: Copyable & Deinitable](values: I, scalar: S, *, max_steps: UInt64 = UInt64.MAX) raises PolyError -> Array[_Join[_Kind[_Element[I]], _Kind[S]]] where (_Kind[_Element[I]] >= 0 and _Kind[S] >= 0):
    """Add a scalar constant to a polynomial.

    Exact domains promote together. Modular inputs must have the same
    prime. Inputs remain unchanged.

    Parameters:
        I: The inferred polynomial iterable.
        S: The scalar operand type.

    Args:
        values: Ascending coefficients or a prepared array.
        scalar: The scalar constant.
        max_steps: The complete call allowance.

    Returns:
        A new polynomial in the common exact domain.

    Raises:
        PolyError: DOMAIN for incompatible scalars; LIMIT/CAPACITY on resource limits.
    """
    var budget = Budget(max_steps)
    return _scalar_operation[0, False, I, S](values, scalar, budget)


def add[I: Iterable, S: Copyable & Deinitable](scalar: S, values: I, mut budget: Budget) raises PolyError -> Array[_Join[_Kind[_Element[I]], _Kind[S]]] where (_Kind[_Element[I]] >= 0 and _Kind[S] >= 0):
    """Add a scalar constant to a polynomial.

    Exact domains promote together. Modular inputs must have the same
    prime. Inputs remain unchanged.

    Parameters:
        I: The inferred polynomial iterable.
        S: The scalar operand type.

    Args:
        scalar: The scalar constant.
        values: Ascending coefficients or a prepared array.
        budget: The shared work allowance, including conversion and storage.

    Returns:
        A new polynomial in the common exact domain.

    Raises:
        PolyError: DOMAIN for incompatible scalars; LIMIT/CAPACITY on resource limits.
    """
    return _scalar_operation[0, True, I, S](values, scalar, budget)


def add[I: Iterable, S: Copyable & Deinitable](scalar: S, values: I, *, max_steps: UInt64 = UInt64.MAX) raises PolyError -> Array[_Join[_Kind[_Element[I]], _Kind[S]]] where (_Kind[_Element[I]] >= 0 and _Kind[S] >= 0):
    """Add a scalar constant to a polynomial.

    Exact domains promote together. Modular inputs must have the same
    prime. Inputs remain unchanged.

    Parameters:
        I: The inferred polynomial iterable.
        S: The scalar operand type.

    Args:
        scalar: The scalar constant.
        values: Ascending coefficients or a prepared array.
        max_steps: The complete call allowance.

    Returns:
        A new polynomial in the common exact domain.

    Raises:
        PolyError: DOMAIN for incompatible scalars; LIMIT/CAPACITY on resource limits.
    """
    var budget = Budget(max_steps)
    return _scalar_operation[0, True, I, S](values, scalar, budget)


def subtract[I: Iterable, S: Copyable & Deinitable](values: I, scalar: S, mut budget: Budget) raises PolyError -> Array[_Join[_Kind[_Element[I]], _Kind[S]]] where (_Kind[_Element[I]] >= 0 and _Kind[S] >= 0):
    """Subtract a scalar constant or a polynomial in operand order.

    Exact domains promote together. Modular inputs must have the same
    prime. Inputs remain unchanged.

    Parameters:
        I: The inferred polynomial iterable.
        S: The scalar operand type.

    Args:
        values: Ascending coefficients or a prepared array.
        scalar: The scalar constant.
        budget: The shared work allowance, including conversion and storage.

    Returns:
        A new polynomial in the common exact domain.

    Raises:
        PolyError: DOMAIN for incompatible scalars; LIMIT/CAPACITY on resource limits.
    """
    return _scalar_operation[1, False, I, S](values, scalar, budget)


def subtract[I: Iterable, S: Copyable & Deinitable](values: I, scalar: S, *, max_steps: UInt64 = UInt64.MAX) raises PolyError -> Array[_Join[_Kind[_Element[I]], _Kind[S]]] where (_Kind[_Element[I]] >= 0 and _Kind[S] >= 0):
    """Subtract a scalar constant or a polynomial in operand order.

    Exact domains promote together. Modular inputs must have the same
    prime. Inputs remain unchanged.

    Parameters:
        I: The inferred polynomial iterable.
        S: The scalar operand type.

    Args:
        values: Ascending coefficients or a prepared array.
        scalar: The scalar constant.
        max_steps: The complete call allowance.

    Returns:
        A new polynomial in the common exact domain.

    Raises:
        PolyError: DOMAIN for incompatible scalars; LIMIT/CAPACITY on resource limits.
    """
    var budget = Budget(max_steps)
    return _scalar_operation[1, False, I, S](values, scalar, budget)


def subtract[I: Iterable, S: Copyable & Deinitable](scalar: S, values: I, mut budget: Budget) raises PolyError -> Array[_Join[_Kind[_Element[I]], _Kind[S]]] where (_Kind[_Element[I]] >= 0 and _Kind[S] >= 0):
    """Subtract a scalar constant or a polynomial in operand order.

    Exact domains promote together. Modular inputs must have the same
    prime. Inputs remain unchanged.

    Parameters:
        I: The inferred polynomial iterable.
        S: The scalar operand type.

    Args:
        scalar: The scalar constant.
        values: Ascending coefficients or a prepared array.
        budget: The shared work allowance, including conversion and storage.

    Returns:
        A new polynomial in the common exact domain.

    Raises:
        PolyError: DOMAIN for incompatible scalars; LIMIT/CAPACITY on resource limits.
    """
    return _scalar_operation[1, True, I, S](values, scalar, budget)


def subtract[I: Iterable, S: Copyable & Deinitable](scalar: S, values: I, *, max_steps: UInt64 = UInt64.MAX) raises PolyError -> Array[_Join[_Kind[_Element[I]], _Kind[S]]] where (_Kind[_Element[I]] >= 0 and _Kind[S] >= 0):
    """Subtract a scalar constant or a polynomial in operand order.

    Exact domains promote together. Modular inputs must have the same
    prime. Inputs remain unchanged.

    Parameters:
        I: The inferred polynomial iterable.
        S: The scalar operand type.

    Args:
        scalar: The scalar constant.
        values: Ascending coefficients or a prepared array.
        max_steps: The complete call allowance.

    Returns:
        A new polynomial in the common exact domain.

    Raises:
        PolyError: DOMAIN for incompatible scalars; LIMIT/CAPACITY on resource limits.
    """
    var budget = Budget(max_steps)
    return _scalar_operation[1, True, I, S](values, scalar, budget)


def multiply[I: Iterable, S: Copyable & Deinitable](values: I, scalar: S, mut budget: Budget) raises PolyError -> Array[_Join[_Kind[_Element[I]], _Kind[S]]] where (_Kind[_Element[I]] >= 0 and _Kind[S] >= 0):
    """Multiply every coefficient by a scalar.

    Exact domains promote together. Modular inputs must have the same
    prime. Inputs remain unchanged.

    Parameters:
        I: The inferred polynomial iterable.
        S: The scalar operand type.

    Args:
        values: Ascending coefficients or a prepared array.
        scalar: The scalar constant.
        budget: The shared work allowance, including conversion and storage.

    Returns:
        A new polynomial in the common exact domain.

    Raises:
        PolyError: DOMAIN for incompatible scalars; LIMIT/CAPACITY on resource limits.
    """
    return _scalar_operation[2, False, I, S](values, scalar, budget)


def multiply[I: Iterable, S: Copyable & Deinitable](values: I, scalar: S, *, max_steps: UInt64 = UInt64.MAX) raises PolyError -> Array[_Join[_Kind[_Element[I]], _Kind[S]]] where (_Kind[_Element[I]] >= 0 and _Kind[S] >= 0):
    """Multiply every coefficient by a scalar.

    Exact domains promote together. Modular inputs must have the same
    prime. Inputs remain unchanged.

    Parameters:
        I: The inferred polynomial iterable.
        S: The scalar operand type.

    Args:
        values: Ascending coefficients or a prepared array.
        scalar: The scalar constant.
        max_steps: The complete call allowance.

    Returns:
        A new polynomial in the common exact domain.

    Raises:
        PolyError: DOMAIN for incompatible scalars; LIMIT/CAPACITY on resource limits.
    """
    var budget = Budget(max_steps)
    return _scalar_operation[2, False, I, S](values, scalar, budget)


def multiply[I: Iterable, S: Copyable & Deinitable](scalar: S, values: I, mut budget: Budget) raises PolyError -> Array[_Join[_Kind[_Element[I]], _Kind[S]]] where (_Kind[_Element[I]] >= 0 and _Kind[S] >= 0):
    """Multiply every coefficient by a scalar.

    Exact domains promote together. Modular inputs must have the same
    prime. Inputs remain unchanged.

    Parameters:
        I: The inferred polynomial iterable.
        S: The scalar operand type.

    Args:
        scalar: The scalar constant.
        values: Ascending coefficients or a prepared array.
        budget: The shared work allowance, including conversion and storage.

    Returns:
        A new polynomial in the common exact domain.

    Raises:
        PolyError: DOMAIN for incompatible scalars; LIMIT/CAPACITY on resource limits.
    """
    return _scalar_operation[2, True, I, S](values, scalar, budget)


def multiply[I: Iterable, S: Copyable & Deinitable](scalar: S, values: I, *, max_steps: UInt64 = UInt64.MAX) raises PolyError -> Array[_Join[_Kind[_Element[I]], _Kind[S]]] where (_Kind[_Element[I]] >= 0 and _Kind[S] >= 0):
    """Multiply every coefficient by a scalar.

    Exact domains promote together. Modular inputs must have the same
    prime. Inputs remain unchanged.

    Parameters:
        I: The inferred polynomial iterable.
        S: The scalar operand type.

    Args:
        scalar: The scalar constant.
        values: Ascending coefficients or a prepared array.
        max_steps: The complete call allowance.

    Returns:
        A new polynomial in the common exact domain.

    Raises:
        PolyError: DOMAIN for incompatible scalars; LIMIT/CAPACITY on resource limits.
    """
    var budget = Budget(max_steps)
    return _scalar_operation[2, True, I, S](values, scalar, budget)


def divide[I: Iterable, S: Copyable & Deinitable](values: I, scalar: S, mut budget: Budget) raises PolyError -> Array[_FieldKind[_Join[_Kind[_Element[I]], _Kind[S]]]] where (_Kind[_Element[I]] >= 0 and _Kind[S] >= 0):
    """Divide every coefficient by a nonzero scalar.

    Exact domains promote together; integer division returns rationals.
    Modular inputs must have the same prime. Inputs remain unchanged.

    Parameters:
        I: The inferred polynomial iterable.
        S: The scalar operand type.

    Args:
        values: Ascending coefficients or a prepared array.
        scalar: The scalar constant; division requires a nonzero value.
        budget: The shared work allowance, including conversion and storage.

    Returns:
        A new polynomial in the common exact domain.

    Raises:
        PolyError: DOMAIN for incompatible scalars or zero divisors; LIMIT/CAPACITY on resource limits.
    """
    return _scalar_operation[3, False, I, S](values, scalar, budget)


def divide[I: Iterable, S: Copyable & Deinitable](values: I, scalar: S, *, max_steps: UInt64 = UInt64.MAX) raises PolyError -> Array[_FieldKind[_Join[_Kind[_Element[I]], _Kind[S]]]] where (_Kind[_Element[I]] >= 0 and _Kind[S] >= 0):
    """Divide every coefficient by a nonzero scalar.

    Exact domains promote together; integer division returns rationals.
    Modular inputs must have the same prime. Inputs remain unchanged.

    Parameters:
        I: The inferred polynomial iterable.
        S: The scalar operand type.

    Args:
        values: Ascending coefficients or a prepared array.
        scalar: The scalar constant; division requires a nonzero value.
        max_steps: The complete call allowance.

    Returns:
        A new polynomial in the common exact domain.

    Raises:
        PolyError: DOMAIN for incompatible scalars or zero divisors; LIMIT/CAPACITY on resource limits.
    """
    var budget = Budget(max_steps)
    return _scalar_operation[3, False, I, S](values, scalar, budget)


def add[D: NumericDomain, S: Copyable & Deinitable](values: NumericArray[D], scalar: S, mut budget: Budget, *, context: D.Context) raises PolyError -> NumericArray[D] where (_Kind[S] >= 0 or _num._IsNumeric[S]):
    """Add a scalar constant to a polynomial.

    Use the stored numerical domain and the explicit precision context.
    Inputs remain unchanged.

    Parameters:
        D: The stored numerical domain.
        S: The scalar operand type.

    Args:
        values: The prepared numerical polynomial.
        scalar: The scalar constant.
        budget: The shared work allowance, including conversion and storage.
        context: Explicit precision and rounding or enclosure settings.

    Returns:
        A new polynomial in the stored numerical domain.

    Raises:
        PolyError: DOMAIN for incompatible scalars; LIMIT/CAPACITY on resource limits.
    """
    return _numeric_scalar_operation[0, False, D, S](values, scalar, budget, context=context)


def add[D: NumericDomain, S: Copyable & Deinitable](values: NumericArray[D], scalar: S, *, context: D.Context, max_steps: UInt64 = UInt64.MAX) raises PolyError -> NumericArray[D] where (_Kind[S] >= 0 or _num._IsNumeric[S]):
    """Add a scalar constant to a polynomial.

    Use the stored numerical domain and the explicit precision context.
    Inputs remain unchanged.

    Parameters:
        D: The stored numerical domain.
        S: The scalar operand type.

    Args:
        values: The prepared numerical polynomial.
        scalar: The scalar constant.
        context: Explicit precision and rounding or enclosure settings.
        max_steps: The complete call allowance.

    Returns:
        A new polynomial in the stored numerical domain.

    Raises:
        PolyError: DOMAIN for incompatible scalars; LIMIT/CAPACITY on resource limits.
    """
    var budget = Budget(max_steps)
    return _numeric_scalar_operation[0, False, D, S](values, scalar, budget, context=context)


def add[D: NumericDomain, S: Copyable & Deinitable](scalar: S, values: NumericArray[D], mut budget: Budget, *, context: D.Context) raises PolyError -> NumericArray[D] where (_Kind[S] >= 0 or _num._IsNumeric[S]):
    """Add a scalar constant to a polynomial.

    Use the stored numerical domain and the explicit precision context.
    Inputs remain unchanged.

    Parameters:
        D: The stored numerical domain.
        S: The scalar operand type.

    Args:
        scalar: The scalar constant.
        values: The prepared numerical polynomial.
        budget: The shared work allowance, including conversion and storage.
        context: Explicit precision and rounding or enclosure settings.

    Returns:
        A new polynomial in the stored numerical domain.

    Raises:
        PolyError: DOMAIN for incompatible scalars; LIMIT/CAPACITY on resource limits.
    """
    return _numeric_scalar_operation[0, True, D, S](values, scalar, budget, context=context)


def add[D: NumericDomain, S: Copyable & Deinitable](scalar: S, values: NumericArray[D], *, context: D.Context, max_steps: UInt64 = UInt64.MAX) raises PolyError -> NumericArray[D] where (_Kind[S] >= 0 or _num._IsNumeric[S]):
    """Add a scalar constant to a polynomial.

    Use the stored numerical domain and the explicit precision context.
    Inputs remain unchanged.

    Parameters:
        D: The stored numerical domain.
        S: The scalar operand type.

    Args:
        scalar: The scalar constant.
        values: The prepared numerical polynomial.
        context: Explicit precision and rounding or enclosure settings.
        max_steps: The complete call allowance.

    Returns:
        A new polynomial in the stored numerical domain.

    Raises:
        PolyError: DOMAIN for incompatible scalars; LIMIT/CAPACITY on resource limits.
    """
    var budget = Budget(max_steps)
    return _numeric_scalar_operation[0, True, D, S](values, scalar, budget, context=context)


def subtract[D: NumericDomain, S: Copyable & Deinitable](values: NumericArray[D], scalar: S, mut budget: Budget, *, context: D.Context) raises PolyError -> NumericArray[D] where (_Kind[S] >= 0 or _num._IsNumeric[S]):
    """Subtract a scalar constant or a polynomial in operand order.

    Use the stored numerical domain and the explicit precision context.
    Inputs remain unchanged.

    Parameters:
        D: The stored numerical domain.
        S: The scalar operand type.

    Args:
        values: The prepared numerical polynomial.
        scalar: The scalar constant.
        budget: The shared work allowance, including conversion and storage.
        context: Explicit precision and rounding or enclosure settings.

    Returns:
        A new polynomial in the stored numerical domain.

    Raises:
        PolyError: DOMAIN for incompatible scalars; LIMIT/CAPACITY on resource limits.
    """
    return _numeric_scalar_operation[1, False, D, S](values, scalar, budget, context=context)


def subtract[D: NumericDomain, S: Copyable & Deinitable](values: NumericArray[D], scalar: S, *, context: D.Context, max_steps: UInt64 = UInt64.MAX) raises PolyError -> NumericArray[D] where (_Kind[S] >= 0 or _num._IsNumeric[S]):
    """Subtract a scalar constant or a polynomial in operand order.

    Use the stored numerical domain and the explicit precision context.
    Inputs remain unchanged.

    Parameters:
        D: The stored numerical domain.
        S: The scalar operand type.

    Args:
        values: The prepared numerical polynomial.
        scalar: The scalar constant.
        context: Explicit precision and rounding or enclosure settings.
        max_steps: The complete call allowance.

    Returns:
        A new polynomial in the stored numerical domain.

    Raises:
        PolyError: DOMAIN for incompatible scalars; LIMIT/CAPACITY on resource limits.
    """
    var budget = Budget(max_steps)
    return _numeric_scalar_operation[1, False, D, S](values, scalar, budget, context=context)


def subtract[D: NumericDomain, S: Copyable & Deinitable](scalar: S, values: NumericArray[D], mut budget: Budget, *, context: D.Context) raises PolyError -> NumericArray[D] where (_Kind[S] >= 0 or _num._IsNumeric[S]):
    """Subtract a scalar constant or a polynomial in operand order.

    Use the stored numerical domain and the explicit precision context.
    Inputs remain unchanged.

    Parameters:
        D: The stored numerical domain.
        S: The scalar operand type.

    Args:
        scalar: The scalar constant.
        values: The prepared numerical polynomial.
        budget: The shared work allowance, including conversion and storage.
        context: Explicit precision and rounding or enclosure settings.

    Returns:
        A new polynomial in the stored numerical domain.

    Raises:
        PolyError: DOMAIN for incompatible scalars; LIMIT/CAPACITY on resource limits.
    """
    return _numeric_scalar_operation[1, True, D, S](values, scalar, budget, context=context)


def subtract[D: NumericDomain, S: Copyable & Deinitable](scalar: S, values: NumericArray[D], *, context: D.Context, max_steps: UInt64 = UInt64.MAX) raises PolyError -> NumericArray[D] where (_Kind[S] >= 0 or _num._IsNumeric[S]):
    """Subtract a scalar constant or a polynomial in operand order.

    Use the stored numerical domain and the explicit precision context.
    Inputs remain unchanged.

    Parameters:
        D: The stored numerical domain.
        S: The scalar operand type.

    Args:
        scalar: The scalar constant.
        values: The prepared numerical polynomial.
        context: Explicit precision and rounding or enclosure settings.
        max_steps: The complete call allowance.

    Returns:
        A new polynomial in the stored numerical domain.

    Raises:
        PolyError: DOMAIN for incompatible scalars; LIMIT/CAPACITY on resource limits.
    """
    var budget = Budget(max_steps)
    return _numeric_scalar_operation[1, True, D, S](values, scalar, budget, context=context)


def multiply[D: NumericDomain, S: Copyable & Deinitable](values: NumericArray[D], scalar: S, mut budget: Budget, *, context: D.Context) raises PolyError -> NumericArray[D] where (_Kind[S] >= 0 or _num._IsNumeric[S]):
    """Multiply every coefficient by a scalar.

    Use the stored numerical domain and the explicit precision context.
    Inputs remain unchanged.

    Parameters:
        D: The stored numerical domain.
        S: The scalar operand type.

    Args:
        values: The prepared numerical polynomial.
        scalar: The scalar constant.
        budget: The shared work allowance, including conversion and storage.
        context: Explicit precision and rounding or enclosure settings.

    Returns:
        A new polynomial in the stored numerical domain.

    Raises:
        PolyError: DOMAIN for incompatible scalars; LIMIT/CAPACITY on resource limits.
    """
    return _numeric_scalar_operation[2, False, D, S](values, scalar, budget, context=context)


def multiply[D: NumericDomain, S: Copyable & Deinitable](values: NumericArray[D], scalar: S, *, context: D.Context, max_steps: UInt64 = UInt64.MAX) raises PolyError -> NumericArray[D] where (_Kind[S] >= 0 or _num._IsNumeric[S]):
    """Multiply every coefficient by a scalar.

    Use the stored numerical domain and the explicit precision context.
    Inputs remain unchanged.

    Parameters:
        D: The stored numerical domain.
        S: The scalar operand type.

    Args:
        values: The prepared numerical polynomial.
        scalar: The scalar constant.
        context: Explicit precision and rounding or enclosure settings.
        max_steps: The complete call allowance.

    Returns:
        A new polynomial in the stored numerical domain.

    Raises:
        PolyError: DOMAIN for incompatible scalars; LIMIT/CAPACITY on resource limits.
    """
    var budget = Budget(max_steps)
    return _numeric_scalar_operation[2, False, D, S](values, scalar, budget, context=context)


def multiply[D: NumericDomain, S: Copyable & Deinitable](scalar: S, values: NumericArray[D], mut budget: Budget, *, context: D.Context) raises PolyError -> NumericArray[D] where (_Kind[S] >= 0 or _num._IsNumeric[S]):
    """Multiply every coefficient by a scalar.

    Use the stored numerical domain and the explicit precision context.
    Inputs remain unchanged.

    Parameters:
        D: The stored numerical domain.
        S: The scalar operand type.

    Args:
        scalar: The scalar constant.
        values: The prepared numerical polynomial.
        budget: The shared work allowance, including conversion and storage.
        context: Explicit precision and rounding or enclosure settings.

    Returns:
        A new polynomial in the stored numerical domain.

    Raises:
        PolyError: DOMAIN for incompatible scalars; LIMIT/CAPACITY on resource limits.
    """
    return _numeric_scalar_operation[2, True, D, S](values, scalar, budget, context=context)


def multiply[D: NumericDomain, S: Copyable & Deinitable](scalar: S, values: NumericArray[D], *, context: D.Context, max_steps: UInt64 = UInt64.MAX) raises PolyError -> NumericArray[D] where (_Kind[S] >= 0 or _num._IsNumeric[S]):
    """Multiply every coefficient by a scalar.

    Use the stored numerical domain and the explicit precision context.
    Inputs remain unchanged.

    Parameters:
        D: The stored numerical domain.
        S: The scalar operand type.

    Args:
        scalar: The scalar constant.
        values: The prepared numerical polynomial.
        context: Explicit precision and rounding or enclosure settings.
        max_steps: The complete call allowance.

    Returns:
        A new polynomial in the stored numerical domain.

    Raises:
        PolyError: DOMAIN for incompatible scalars; LIMIT/CAPACITY on resource limits.
    """
    var budget = Budget(max_steps)
    return _numeric_scalar_operation[2, True, D, S](values, scalar, budget, context=context)


def divide[D: NumericDomain, S: Copyable & Deinitable](values: NumericArray[D], scalar: S, mut budget: Budget, *, context: D.Context) raises PolyError -> NumericArray[D] where (_Kind[S] >= 0 or _num._IsNumeric[S]):
    """Divide every coefficient by a nonzero scalar.

    Use the stored domain and explicit context. A ball divisor must
    exclude zero; inputs remain unchanged.

    Parameters:
        D: The stored numerical domain.
        S: The scalar operand type.

    Args:
        values: The prepared numerical polynomial.
        scalar: The scalar constant; division requires a nonzero value.
        budget: The shared work allowance, including conversion and storage.
        context: Explicit precision and rounding or enclosure settings.

    Returns:
        A new polynomial in the stored numerical domain.

    Raises:
        PolyError: DOMAIN for incompatible scalars or zero divisors; LIMIT/CAPACITY on resource limits.
    """
    return _numeric_scalar_operation[3, False, D, S](values, scalar, budget, context=context)


def divide[D: NumericDomain, S: Copyable & Deinitable](values: NumericArray[D], scalar: S, *, context: D.Context, max_steps: UInt64 = UInt64.MAX) raises PolyError -> NumericArray[D] where (_Kind[S] >= 0 or _num._IsNumeric[S]):
    """Divide every coefficient by a nonzero scalar.

    Use the stored domain and explicit context. A ball divisor must
    exclude zero; inputs remain unchanged.

    Parameters:
        D: The stored numerical domain.
        S: The scalar operand type.

    Args:
        values: The prepared numerical polynomial.
        scalar: The scalar constant; division requires a nonzero value.
        context: Explicit precision and rounding or enclosure settings.
        max_steps: The complete call allowance.

    Returns:
        A new polynomial in the stored numerical domain.

    Raises:
        PolyError: DOMAIN for incompatible scalars or zero divisors; LIMIT/CAPACITY on resource limits.
    """
    var budget = Budget(max_steps)
    return _numeric_scalar_operation[3, False, D, S](values, scalar, budget, context=context)

from polynomials import to_kernel_bytes as _kernel_encode, from_kernel_bytes as _kernel_decode
from . import _display


def to_kernel_bytes[I: Iterable](values: I, mut budget: Budget, *, variable: Int64 = 0) raises PolyError -> List[UInt8] where (_Kind[_Element[I]] >= 0 and _Kind[_Element[I]] <= 1):
    """Encode integer or rational coefficients as a canonical kernel literal.

    Zero and one use separate kernel atoms and cannot be encoded here.
    For application archives, use poly.io instead.

    Parameters:
        I: The inferred input iterable.

    Args:
        values: Exact integer or rational polynomial input.
        budget: The shared work allowance.
        variable: The core variable ID used by the encoded polynomial.

    Returns:
        Canonical little-endian kernel bytes, at most 1 MiB.

    Raises:
        PolyError: ENCODING for zero or one, DOMAIN for invalid maps,
            LIMIT on exhaustion, or CAPACITY beyond the kernel size ceiling.
    """
    var p = _promote[1](_prepare(values, budget), NoContext(), budget)
    var core = _dense_sparse(to_core(p, budget, variable=variable), budget)
    return _kernel_encode(core, budget)


def to_kernel_bytes[I: Iterable](values: I, *, max_steps: UInt64 = UInt64.MAX, variable: Int64 = 0) raises PolyError -> List[UInt8] where (_Kind[_Element[I]] >= 0 and _Kind[_Element[I]] <= 1):
    """Encode integer or rational coefficients as a canonical kernel literal.

    Zero and one use separate kernel atoms and cannot be encoded here.
    For application archives, use poly.io instead.

    Parameters:
        I: The inferred input iterable.

    Args:
        values: Exact integer or rational polynomial input.
        max_steps: The complete work allowance.
        variable: The core variable ID used by the encoded polynomial.

    Returns:
        Canonical little-endian kernel bytes, at most 1 MiB.

    Raises:
        PolyError: ENCODING for zero or one, DOMAIN for invalid maps,
            LIMIT on exhaustion, or CAPACITY beyond the kernel size ceiling.
    """
    var budget = Budget(max_steps)
    return to_kernel_bytes[I](values, budget, variable=variable)


def from_kernel_bytes(data: Span[UInt8, _], mut budget: Budget, *, variable: Int64 = 0) raises PolyError -> Array[1]:
    """Decode and validate a kernel literal into rational coefficient storage.

    Malformed or noncanonical bytes are rejected, never silently repaired.
    The variable map supplies axis metadata absent from the wire format.

    Args:
        data: The kernel literal payload.
        budget: The shared work allowance.
        variable: The core variable ID used by the encoded polynomial.

    Returns:
        A canonical polynomial over QQ with array axes starting at zero.

    Raises:
        PolyError: ENCODING for malformed bytes, DOMAIN for unmapped variables,
            LIMIT on exhaustion, or CAPACITY for excessive input or output size.
    """
    var core = _kernel_decode(data, budget)
    var converted = DensePoly[QQ].from_sparse(core, budget, variable=Optional(variable))
    return from_core(converted, budget)


def from_kernel_bytes(data: Span[UInt8, _], *, max_steps: UInt64 = UInt64.MAX, variable: Int64 = 0) raises PolyError -> Array[1]:
    """Decode and validate a kernel literal into rational coefficient storage.

    Malformed or noncanonical bytes are rejected, never silently repaired.
    The variable map supplies axis metadata absent from the wire format.

    Args:
        data: The kernel literal payload.
        max_steps: The complete work allowance.
        variable: The core variable ID used by the encoded polynomial.

    Returns:
        A canonical polynomial over QQ with array axes starting at zero.

    Raises:
        PolyError: ENCODING for malformed bytes, DOMAIN for unmapped variables,
            LIMIT on exhaustion, or CAPACITY for excessive input or output size.
    """
    var budget = Budget(max_steps)
    return from_kernel_bytes(data, budget, variable=variable)


def format[I: Iterable](values: I, mut budget: Budget, *, variable: String = "x") raises PolyError -> String where (_Kind[_Element[I]] >= 0 and _Kind[_Element[I]] <= 3):
    """Display an exact polynomial with readable variable names.

    Supports ZZ, QQ, QQi, and prime fields. Coefficients remain exact;
    terms appear in decreasing lexicographic order. This is display text,
    not an archive carrying domain or axis metadata.

    Parameters:
        I: The inferred input iterable.

    Args:
        values: Polynomial coefficients, terms, or a prepared exact array.
        budget: The shared work allowance.
        variable: The ASCII identifier used for the polynomial variable.

    Returns:
        A named-variable expression, or 0 for the zero polynomial.

    Raises:
        PolyError: DOMAIN for invalid or duplicate names (i is reserved over QQi),
            LIMIT on exhaustion, or CAPACITY for excessive sizes.
    """
    var p = _prepare(values, budget)
    _allocation[String](1, budget)
    _charge_size(variable.byte_length(), budget)
    return _display._format(_dense_sparse(p._core[], budget), 1, [variable.copy()], budget)


def format[I: Iterable](values: I, *, max_steps: UInt64 = UInt64.MAX, variable: String = "x") raises PolyError -> String where (_Kind[_Element[I]] >= 0 and _Kind[_Element[I]] <= 3):
    """Display an exact polynomial with readable variable names.

    Supports ZZ, QQ, QQi, and prime fields. Coefficients remain exact;
    terms appear in decreasing lexicographic order. This is display text,
    not an archive carrying domain or axis metadata.

    Parameters:
        I: The inferred input iterable.

    Args:
        values: Polynomial coefficients, terms, or a prepared exact array.
        max_steps: The complete work allowance.
        variable: The ASCII identifier used for the polynomial variable.

    Returns:
        A named-variable expression, or 0 for the zero polynomial.

    Raises:
        PolyError: DOMAIN for invalid or duplicate names (i is reserved over QQi),
            LIMIT on exhaustion, or CAPACITY for excessive sizes.
    """
    var budget = Budget(max_steps)
    return format[I](values, budget, variable=variable)
