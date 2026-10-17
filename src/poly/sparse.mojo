"""Sparse polynomials with integer or tuple powers and explicit numerical contexts."""
from ._io_meta import _Record, _Sparse
from polynomials import NumericSparsePoly
from std.iter import Iterable, IterableOwned, Iterator, iter, next, StopIteration
from std.builtin.rebind import downcast
from std.builtin.variadics import TypeList
from std.memory import ArcPointer
from apn_mojo import Integer, Rational, ExactComplex
from polynomials import SparsePoly, Term, Monomial, MonomialOrder, Budget, ModInt, Modulus, NoContext, PolyError, PolyErrorKind
from polynomials import evaluate as _evaluate, derivative as _derivative, integrate_sparse, divide_by_list, CoefficientField
from ._common import _allocation, _sum, _product, _charge_size, _take_coefficient, _DirectInput, _input_view
from ._common import Values, _check_batch, _FieldKind, _Element, _OwnedElement, _Join, _Kind, _Scalar, _Ring, _convert, _wrap, _unwrap, _Context, _initial_modulus, _merge_modulus, _TupleKind, _WithModulus, _domain, _grow, _size, _compact
from polynomials import CoefficientRing
from ._common import _CoreKind
from ._interop import _sparse_copy, _variables, _Shape
from polynomials import gcd as _gcd, gcd_value as _gcd_value, resultant_value as _resultant_value, content as _content, primitive_part as _primitive_part, resultant as _resultant, subresultants as _subresultants, divide_exact as _divide_exact
from ._interop import _take_sparse
from polynomials import QQi, factor_multivariate_gaussian, factor_multivariate_finite_field, SparseSquarefreeDecomposition, squarefree_multivariate
from polynomials import compose_dense
from . import dense as _dense
from ._common import _Nested, _data_context
from ._interop import _dense_sparse
from polynomials import sparse_gcd as _sparse_gcd, sparse_gcd_integer as _sparse_gcd_integer
from polynomials import DensePoly, ZZ, QQ, MultivariateFactorization, factor_multivariate as _factor_multivariate, factor_multivariate_integer as _factor_multivariate_integer
from polynomials import substitute_many as _substitute_many


trait _Powers:
    @staticmethod
    def width() -> Int: ...
    def _monomial(self, mut budget: Budget) raises PolyError -> Monomial: ...
    def _powers_compare(self, other: Self) -> Int: ...
    def _powers_validate(self, mut budget: Budget) raises PolyError: ...
    @staticmethod
    def _unpack(monomial: Monomial) -> Self: ...


__extension Tuple(_Powers):
    @staticmethod
    def width() -> Int:
        comptime for i in range(Self.Ts.length):
            comptime assert Self.Ts[i] == Int, "each power must be Int"
        return Self.Ts.length

    def _powers_compare(self, other: Self) -> Int:
        comptime for i in range(Self.Ts.length):
            comptime assert Self.Ts[i] == Int, "each power must be Int"
            if rebind[Int](self[i]) != rebind[Int](other[i]):
                return -1 if rebind[Int](self[i]) < rebind[Int](other[i]) else 1
        return 0

    def _powers_validate(self, mut budget: Budget) raises PolyError:
        comptime for i in range(Self.Ts.length):
            comptime assert Self.Ts[i] == Int, "each power must be Int"
            budget.charge(1)
            _ = _power(rebind[Int](self[i]))

    def _monomial(self, mut budget: Budget) raises PolyError -> Monomial:
        _allocation[Tuple[Int64, UInt32]](Self.Ts.length, budget)
        var pairs = List[Tuple[Int64, UInt32]](capacity=Self.Ts.length)
        comptime for i in range(Self.Ts.length):
            comptime assert Self.Ts[i] == Int, "each power must be Int"
            budget.charge(1)
            var exponent = _power(rebind[Int](self[i]))
            if exponent:
                pairs.append((Int64(i), exponent))
        return Monomial(pairs^, budget)

    @staticmethod
    def _unpack(monomial: Monomial) -> Self:
        comptime Ints = TypeList.splat[Self.Ts.length, Int]()
        comptime assert Ints.all_conforms_to[Defaultable]()
        var result = Tuple[*Ints]()
        var position = 0
        comptime for i in range(Self.Ts.length):
            comptime assert Self.Ts[i] == Int, "each power must be Int"
            if position < len(monomial.pairs) and monomial.pairs[position][0] == Int64(i):
                result[i] = Int(UInt64(monomial.pairs[position][1]))
                position += 1
        return rebind_var[Self](result^)


def _width[P: AnyType]() -> Int:
    comptime if P == Int:
        return 1
    else:
        return downcast[P, _Powers].width()


def _power(value: Int) raises PolyError -> UInt32:
    if value < 0 or UInt64(value) > UInt64(UInt32.MAX):
        raise PolyError(PolyErrorKind.DOMAIN, String("powers must be nonnegative integers no larger than UInt32.MAX: ", value))
    return UInt32(value)


def _monomial[P: Copyable](powers: P, mut budget: Budget) raises PolyError -> Monomial:
    comptime if P == Int:
        budget.charge(1)
        var exponent = _power(rebind[Int](powers))
        var pairs = List[Tuple[Int64, UInt32]]()
        if exponent:
            _allocation[Tuple[Int64, UInt32]](1, budget)
            pairs.reserve(1)
            pairs.append((Int64(0), exponent))
        return Monomial(pairs^, budget)
    else:
        return rebind[downcast[P, _Powers]](powers)._monomial(budget)


def _powers[P: Copyable](monomial: Monomial) -> P:
    comptime if P == Int:
        var power = 0
        if len(monomial.pairs):
            power = Int(UInt64(monomial.pairs[0][1]))
        return rebind_var[P](power)
    else:
        return rebind_var[P](downcast[P, _Powers]._unpack(monomial))


struct Array[P: Copyable & Deinitable, k: Int](Copyable, Movable, Iterable, Sized, _WithModulus, _Record):
    """An immutable polynomial sharing its canonical term storage.

    Parameters:
        P: The power shape: Int or a tuple of Int powers.
        k: The inferred coefficient kind: 0 for ZZ, 1 for QQ, 2 for QQi, 3 for a prime field, 4 for AA, or 5 for QQbar.
    """
    comptime _Format = _Sparse
    comptime _Item = _Scalar[Self.k]
    comptime _Power = Self.P
    var _core: ArcPointer[SparsePoly[_Ring[Self.k]]]
    comptime IteratorType[iterable_mut: Bool, //, iterable_origin: Origin[mut=iterable_mut]]: Iterator = _ArrayIterator[Self.P, Self.k, ImmOrigin(iterable_origin)]
    """A borrowing iterator over the shared storage.

    Parameters:
        iterable_mut: Whether the borrowing origin is mutable.
        iterable_origin: The lifetime of the borrowed array.
    """

    def __init__(out self, var core: SparsePoly[_Ring[Self.k]], mut budget: Budget) raises PolyError:
        """Take ownership of canonical storage; use asarray for coefficient inputs.

        Args:
            core: An owned canonical core polynomial in the array's variable layout and domain.
            budget: The caller-owned work allowance, shared through preparation and computation.

        Raises:
            PolyError: LIMIT on exhausted work, CAPACITY on unrepresentable sizes, or DOMAIN for incompatible input.
        """
        _compact(core.terms, budget)
        _allocation[SparsePoly[_Ring[Self.k]]](1, budget)
        self._core = ArcPointer(core^)

    def __iter__(ref self) -> Self.IteratorType[origin_of(self)]:
        """Iterate over values without copying the backing buffer.

        Returns:
            An iterator borrowing the shared storage.
        """
        return _ArrayIterator[Self.P, Self.k, ImmOrigin(origin_of(self))](Pointer(to=self).as_imm(), 0)

    def __len__(self) -> Int:
        """Return the number of stored terms.

        Returns:
            The number of stored entries.
        """
        return len(self._core[].terms)

    def __getitem__(self, index: Int) -> Tuple[Self.P, _Scalar[Self.k]]:
        """Return the entry at a valid zero-based index.

        Args:
            index: A valid zero-based index into stored entries.

        Returns:
            The scalar or sparse term at the requested index.
        """
        ref term = self._core[].terms[index]
        return (_powers[Self.P](term.monomial), _unwrap[Self.k](term.coefficient))

    def to_list(self, mut budget: Budget) raises PolyError -> List[Tuple[Self.P, _Scalar[Self.k]]]:
        """Return an independent mutable list, charging allocation and coefficient work.

        Args:
            budget: The caller-owned work allowance, shared through preparation and computation.

        Returns:
            An independent mutable list in the current entry order.

        Raises:
            PolyError: LIMIT on exhausted work, CAPACITY on unrepresentable sizes, or DOMAIN for incompatible input.
        """
        _allocation[Tuple[Self.P, _Scalar[Self.k]]](len(self), budget)
        var result = List[Tuple[Self.P, _Scalar[Self.k]]](capacity=len(self))
        for index in range(len(self)):
            _charge_size(_sum(_width[Self.P](), self._core[].terms[index].coefficient.size()), budget)
            result.append(self[index])
        return result^

    def to_list(self, *, max_steps: UInt64 = UInt64.MAX) raises PolyError -> List[Tuple[Self.P, _Scalar[Self.k]]]:
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
struct _ArrayIterator[P: Copyable & Deinitable, k: Int, origin: ImmOrigin](Iterator):
    comptime Element = Tuple[Self.P, _Scalar[Self.k]]
    var source: Pointer[Array[Self.P, Self.k], Self.origin]
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


def _order[P: AnyType](mut budget: Budget) raises PolyError -> MonomialOrder:
    _allocation[Int64](_width[P](), budget)
    var variables = List[Int64](capacity=_width[P]())
    for i in range(_width[P]()):
        budget.charge(1)
        variables.append(Int64(i))
    return MonomialOrder(MonomialOrder.LEX, variables^, budget)


def _finish[P: Copyable & Deinitable, k: Int](var terms: List[Term[_Ring[k]]], ctx: _Ring[k].Context, mut budget: Budget) raises PolyError -> Array[P, k]:
    var order = _order[P](budget)
    # The core normalizer grows an output list while moving owned terms.
    # Precharge its geometric allocations and moves, bounded by 6*n slots.
    _allocation[Term[_Ring[k]]](_product(len(terms), 6), budget)
    var core = SparsePoly[_Ring[k]].from_terms(terms^, order, ctx, budget)
    return Array[P, k](core^, budget)


@always_inline
def _term[k: Int, P: Copyable & Deinitable, C: Copyable & Deinitable](pair: Tuple[P, C], ctx: _Ring[k].Context, mut budget: Budget) raises PolyError -> Term[_Ring[k]]:
    return Term[_Ring[k]](_monomial(pair[0], budget), _take_coefficient[k](pair[1].copy(), ctx, budget))


def _collect[P: Copyable & Deinitable, C: Copyable & Deinitable, k: Int, It: Iterator](var cursor: It, var context: _Context[k], mut budget: Budget, capacity: Int = 0) raises PolyError -> Array[P, k]:
    comptime assert _Kind[C] >= 0, "sparse coefficients must be exact numbers; convert floats explicitly"
    _allocation[Term[_Ring[k]]](capacity, budget)
    var terms = List[Term[_Ring[k]]](capacity=capacity)
    while True:
        budget.charge(1)
        var raw: It.Element
        try:
            raw = next(cursor)
        except StopIteration:
            break
        var pair = rebind_var[Tuple[P, C]](raw^)
        comptime if C == ModInt:
            context.observe(rebind[ModInt](pair[1]).modulus, budget)
        _grow(terms, budget)
        terms.append(_term[k](pair, context.get(), budget))
    return _finish[P, k](terms^, context.get(), budget)


def _prepare[I: Iterable, P: Copyable & Deinitable, C: Copyable & Deinitable](values: I, mut budget: Budget) raises PolyError -> Array[P, _Kind[C]] where _Element[I] == Tuple[P, C]:
    comptime k = _Kind[C]
    comptime if I == Array[P, k]:
        return rebind[Array[P, k]](values).copy()
    else:
        var context = _Context[k]()
        var modulus = _initial_modulus(values)
        if modulus:
            context.observe(modulus, budget)
        comptime if conforms_to(I, Sized):
            return _collect[P, C, k](iter(values), context^, budget, len(values))
        else:
            return _collect[P, C, k](iter(values), context^, budget)


def _promote[k: Int, P: Copyable & Deinitable, source: Int](values: Array[P, source], ctx: _Ring[k].Context, mut budget: Budget) raises PolyError -> Array[P, k]:
    comptime if k == source:
        return rebind[Array[P, k]](values).copy()
    else:
        _allocation[Term[_Ring[k]]](len(values), budget)
        var terms = List[Term[_Ring[k]]](capacity=len(values))
        for index in range(len(values)):
            budget.charge(1)
            ref original = values._core[].terms[index]
            _allocation[Tuple[Int64, UInt32]](len(original.monomial.pairs), budget)
            _charge_size(original.coefficient.size(), budget)
            var c = _wrap[k](_convert[k](_unwrap[source](original.coefficient), ctx, budget))
            terms.append(Term[_Ring[k]](original.monomial.copy(), c^))
        return _finish[P, k](terms^, ctx, budget)


def asarray[I: Iterable, P: Copyable & Deinitable, C: Copyable & Deinitable](values: I, mut budget: Budget) raises PolyError -> Array[P, _Kind[C]] where _Element[I] == Tuple[P, C]:
    """Normalize one pass over terms, or share a prepared sparse array.

    Parameters:
        I: The inferred input iterable type.
        P: The power shape: Int or a tuple of Int powers.
        C: The inferred input coefficient type.

    Args:
        values: The coefficient sequence, sparse terms, or prepared array.
        budget: The caller-owned work allowance, shared through preparation and computation.

    Returns:
        An immutable canonical polynomial that retains its exact domain and modulus.

    Raises:
        PolyError: LIMIT on exhausted work, CAPACITY on unrepresentable sizes, or DOMAIN for incompatible input.
    """
    return _prepare[I, P, C](values, budget)


def asarray[I: Iterable, P: Copyable & Deinitable, C: Copyable & Deinitable](values: I, *, max_steps: UInt64 = UInt64.MAX) raises PolyError -> Array[P, _Kind[C]] where _Element[I] == Tuple[P, C]:
    """Normalize exact inputs with an optional work limit; prepared arrays share storage.

    Parameters:
        I: The inferred input iterable type.
        P: The power shape: Int or a tuple of Int powers.
        C: The inferred input coefficient type.

    Args:
        values: The coefficient sequence, sparse terms, or prepared array.
        max_steps: The complete call's work allowance; defaults to UInt64.MAX.

    Returns:
        An immutable canonical polynomial that retains its exact domain and modulus.

    Raises:
        PolyError: LIMIT on exhausted work, CAPACITY on unrepresentable sizes, or DOMAIN for incompatible input.
    """
    var budget = Budget(max_steps)
    return asarray[I, P, C](values, budget)


def asarray[I: Iterable, P: Copyable & Deinitable, C: Copyable & Deinitable](values: I, mut budget: Budget, *, modulus: UInt64) raises PolyError -> Array[P, 3] where _Element[I] == Tuple[P, C]:
    """Normalize exact inputs with an optional work limit; prepared arrays share storage.

    Parameters:
        I: The inferred input iterable type.
        P: The power shape: Int or a tuple of Int powers.
        C: The inferred input coefficient type.

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
    comptime if I == Array[P, 3]:
        if modulus == rebind[Array[P, 3]](values).modulus():
            return rebind[Array[P, 3]](values).copy()
    var context = _Context[3]()
    context.observe(modulus, budget)
    return _collect[P, C, 3](iter(values), context^, budget)


def asarray[I: Iterable, P: Copyable & Deinitable, C: Copyable & Deinitable](values: I, *, modulus: UInt64, max_steps: UInt64 = UInt64.MAX) raises PolyError -> Array[P, 3] where _Element[I] == Tuple[P, C]:
    """Normalize exact inputs with an optional work limit; prepared arrays share storage.

    Parameters:
        I: The inferred input iterable type.
        P: The power shape: Int or a tuple of Int powers.
        C: The inferred input coefficient type.

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
    return asarray[I, P, C](values, budget, modulus=modulus)


def _pair[k: Int, A: Iterable, B: Iterable, P: Copyable & Deinitable, C: Copyable & Deinitable, D: Copyable & Deinitable](a: A, b: B, mut budget: Budget) raises PolyError -> Tuple[Array[P, k], Array[P, k]] where (_Element[A] == Tuple[P, C] and _Element[B] == Tuple[P, D]):
    var left = _prepare[A, P, C](a, budget)
    var right = _prepare[B, P, D](b, budget)
    _ = _merge_modulus(left.modulus(), right.modulus())
    var ctx: _Ring[k].Context
    comptime if _Kind[C] == 3:
        ctx = rebind_var[_Ring[k].Context](left._core[].ring.copy())
    elif _Kind[D] == 3:
        ctx = rebind_var[_Ring[k].Context](right._core[].ring.copy())
    else:
        ctx = rebind_var[_Ring[k].Context](NoContext())
    var p = _promote[k](left, ctx, budget)
    var q = _promote[k](right, ctx, budget)
    return p^, q^



def _compare_powers[P: Copyable & Deinitable](a: P, b: P) -> Int:
    comptime if P == Int:
        return -1 if rebind[Int](a) < rebind[Int](b) else 1 if rebind[Int](a) > rebind[Int](b) else 0
    else:
        return rebind[downcast[P, _Powers]](a)._powers_compare(rebind[downcast[P, _Powers]](b))


def _ascending[P: Copyable & Deinitable, C: Copyable & Deinitable, origin: ImmOrigin](values: Span[Tuple[P, C], origin], mut budget: Budget) raises PolyError -> Bool:
    var ordered = True
    for i in range(len(values)):
        budget.charge(1)
        comptime if P == Int:
            _ = _power(rebind[Int](values[i][0]))
        else:
            rebind[downcast[P, _Powers]](values[i][0])._powers_validate(budget)
        if i and _compare_powers(values[i - 1][0], values[i][0]) >= 0:
            ordered = False
    return ordered


def _list_sum[k: Int, P: Copyable & Deinitable, C: Copyable & Deinitable, D: Copyable & Deinitable, a_origin: ImmOrigin, b_origin: ImmOrigin](a: Span[Tuple[P, C], a_origin], b: Span[Tuple[P, D], b_origin], subtract: Bool, mut budget: Budget) raises PolyError -> Array[P, k]:
    # Strictly increasing input powers let us merge borrowed tuples directly.
    # Unsorted inputs and repeated powers retain the general normalization path.
    var left_ordered = _ascending(a, budget)
    var right_ordered = _ascending(b, budget)
    if not left_ordered or not right_ordered:
        var pair = _pair[k, Span[Tuple[P, C], a_origin], Span[Tuple[P, D], b_origin], P, C, D](a, b, budget)
        return Array[P, k](pair[0]._core[].sub(pair[1]._core[], budget) if subtract else pair[0]._core[].add(pair[1]._core[], budget), budget)
    var ctx = rebind_var[_Ring[k].Context](NoContext())
    var result = SparsePoly[_Ring[k]](_order[P](budget), ctx.copy())
    var capacity = _sum(len(a), len(b))
    _allocation[Term[_Ring[k]]](capacity, budget)
    result.terms = List[Term[_Ring[k]]](capacity=capacity)
    var i = 0
    var j = 0
    while i < len(a) or j < len(b):
        budget.charge(1)
        var comparison = 1 if i == len(a) else -1 if j == len(b) else _compare_powers(a[i][0], b[j][0])
        var coefficient: _Ring[k]
        var powers: P
        if comparison < 0:
            powers = a[i][0].copy()
            coefficient = _take_coefficient[k](a[i][1].copy(), ctx, budget)
            i += 1
        elif comparison > 0:
            powers = b[j][0].copy()
            var right = _take_coefficient[k](b[j][1].copy(), ctx, budget)
            coefficient = right.neg(budget) if subtract else right^
            j += 1
        else:
            powers = a[i][0].copy()
            var left = _take_coefficient[k](a[i][1].copy(), ctx, budget)
            var right = _take_coefficient[k](b[j][1].copy(), ctx, budget)
            coefficient = left.sub(right, budget) if subtract else left.add(right, budget)
            i += 1
            j += 1
        if not coefficient.is_zero():
            result.terms.append(Term[_Ring[k]](_monomial(powers, budget), coefficient^))
    return Array[P, k](result^, budget)

def add[A: Iterable, B: Iterable, P: Copyable & Deinitable, C: Copyable & Deinitable, D: Copyable & Deinitable](a: A, b: B, mut budget: Budget) raises PolyError -> Array[P, _Join[_Kind[C], _Kind[D]]] where (_Element[A] == Tuple[P, C] and _Element[B] == Tuple[P, D]):
    """Add polynomials, promoting their coefficients together.

    Parameters:
        A: The first inferred iterable type.
        B: The second inferred iterable type.
        P: The power shape: Int or a tuple of Int powers.
        C: The inferred input coefficient type.
        D: The second inferred coefficient type.

    Args:
        a: The first polynomial.
        b: The second polynomial.
        budget: The caller-owned work allowance, shared through preparation and computation.

    Returns:
        The canonical sum in the common exact domain.

    Raises:
        PolyError: LIMIT on exhausted work, CAPACITY on unrepresentable sizes, or DOMAIN for incompatible input.
    """
    comptime k = _Join[_Kind[C], _Kind[D]]
    comptime if _DirectInput[A] and _DirectInput[B] and 0 <= k and k < 3:
        return _list_sum[k, P, C, D](rebind_var[Span[Tuple[P, C], origin_of(a)]](_input_view(a)), rebind_var[Span[Tuple[P, D], origin_of(b)]](_input_view(b)), False, budget)
    else:
        var pair = _pair[k, A, B, P, C, D](a, b, budget)
        return Array[P, k](pair[0]._core[].add(pair[1]._core[], budget), budget)


def add[A: Iterable, B: Iterable, P: Copyable & Deinitable, C: Copyable & Deinitable, D: Copyable & Deinitable](a: A, b: B, *, max_steps: UInt64 = UInt64.MAX) raises PolyError -> Array[P, _Join[_Kind[C], _Kind[D]]] where (_Element[A] == Tuple[P, C] and _Element[B] == Tuple[P, D]):
    """Add polynomials with an optional work limit and exact coefficient promotion.

    Parameters:
        A: The first inferred iterable type.
        B: The second inferred iterable type.
        P: The power shape: Int or a tuple of Int powers.
        C: The inferred input coefficient type.
        D: The second inferred coefficient type.

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
    return add[A, B, P, C, D](a, b, budget)


def multiply[A: Iterable, B: Iterable, P: Copyable & Deinitable, C: Copyable & Deinitable, D: Copyable & Deinitable](a: A, b: B, mut budget: Budget) raises PolyError -> Array[P, _Join[_Kind[C], _Kind[D]]] where (_Element[A] == Tuple[P, C] and _Element[B] == Tuple[P, D]):
    """Multiply polynomials, promoting their coefficients together.

    Parameters:
        A: The first inferred iterable type.
        B: The second inferred iterable type.
        P: The power shape: Int or a tuple of Int powers.
        C: The inferred input coefficient type.
        D: The second inferred coefficient type.

    Args:
        a: The first polynomial.
        b: The second polynomial.
        budget: The caller-owned work allowance, shared through preparation and computation.

    Returns:
        The canonical product in the common exact domain.

    Raises:
        PolyError: LIMIT on exhausted work, CAPACITY on unrepresentable sizes, or DOMAIN for incompatible input.
    """
    comptime k = _Join[_Kind[C], _Kind[D]]
    var pair = _pair[k, A, B, P, C, D](a, b, budget)
    return Array[P, k](pair[0]._core[].mul(pair[1]._core[], budget), budget)


def multiply[A: Iterable, B: Iterable, P: Copyable & Deinitable, C: Copyable & Deinitable, D: Copyable & Deinitable](a: A, b: B, *, max_steps: UInt64 = UInt64.MAX) raises PolyError -> Array[P, _Join[_Kind[C], _Kind[D]]] where (_Element[A] == Tuple[P, C] and _Element[B] == Tuple[P, D]):
    """Multiply polynomials with an optional work limit and exact coefficient promotion.

    Parameters:
        A: The first inferred iterable type.
        B: The second inferred iterable type.
        P: The power shape: Int or a tuple of Int powers.
        C: The inferred input coefficient type.
        D: The second inferred coefficient type.

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
    return multiply[A, B, P, C, D](a, b, budget)


def derivative[I: Iterable, P: Copyable & Deinitable, C: Copyable & Deinitable](values: I, mut budget: Budget, *, axis: Int = 0) raises PolyError -> Array[P, _Kind[C]] where _Element[I] == Tuple[P, C]:
    """Differentiate along the selected variable, numbered from zero.

    Parameters:
        I: The inferred input iterable type.
        P: The power shape: Int or a tuple of Int powers.
        C: The inferred input coefficient type.

    Args:
        values: The coefficient sequence, sparse terms, or prepared array.
        budget: The caller-owned work allowance, shared through preparation and computation.
        axis: The zero-based variable index.

    Returns:
        The derivative, retaining the exact coefficient domain.

    Raises:
        PolyError: LIMIT on exhausted work, CAPACITY on unrepresentable sizes, or DOMAIN for incompatible input.
    """
    if axis < 0 or axis >= _width[P]():
        raise PolyError(PolyErrorKind.DOMAIN, "derivative axis is outside the polynomial's variables")
    var p = _prepare[I, P, C](values, budget)
    return Array[P, _Kind[C]](_derivative(p._core[], Int64(axis), budget), budget)


def derivative[I: Iterable, P: Copyable & Deinitable, C: Copyable & Deinitable](values: I, *, axis: Int = 0, max_steps: UInt64 = UInt64.MAX) raises PolyError -> Array[P, _Kind[C]] where _Element[I] == Tuple[P, C]:
    """Differentiate with an optional work limit, retaining the coefficient domain.

    Parameters:
        I: The inferred input iterable type.
        P: The power shape: Int or a tuple of Int powers.
        C: The inferred input coefficient type.

    Args:
        values: The coefficient sequence, sparse terms, or prepared array.
        axis: The zero-based variable index.
        max_steps: The complete call's work allowance; defaults to UInt64.MAX.

    Returns:
        The derivative, retaining the exact coefficient domain.

    Raises:
        PolyError: LIMIT on exhausted work, CAPACITY on unrepresentable sizes, or DOMAIN for incompatible input.
    """
    var budget = Budget(max_steps)
    return derivative[I, P, C](values, budget, axis=axis)


def evaluate[I: Iterable, P: Copyable & Deinitable, C: Copyable & Deinitable, *Ts: Copyable & Deinitable](values: I, point: Tuple[*Ts], mut budget: Budget) raises PolyError -> _Evaluation[C, Tuple[*Ts]] where _Element[I] == Tuple[P, C]:
    """Evaluate at exact coordinates in variable order.

    Parameters:
        I: The inferred input iterable type.
        P: The power shape: Int or a tuple of Int powers.
        C: The inferred input coefficient type.
        Ts: The inferred element types of the input tuple.

    Args:
        values: The coefficient sequence, sparse terms, or prepared array.
        point: An exact scalar for one variable, or a coordinate tuple in variable order.
        budget: The caller-owned work allowance, shared through preparation and computation.

    Returns:
        The exact scalar after joint promotion, or an algebraic Real for algebraic coordinates.

    Raises:
        PolyError: LIMIT on exhausted work, CAPACITY on unrepresentable sizes, or DOMAIN for incompatible input.
    """
    comptime if _alg._HasReal[Tuple[*Ts]] and (_Kind[C] == 0 or _Kind[C] == 1) and _TupleKind[Tuple[*Ts]] == 4:
        return rebind_var[_Evaluation[C, Tuple[*Ts]]](evaluate_algebraic[I, P, C, *Ts](values, point, budget))
    else:
        comptime assert Tuple[*Ts].Ts.length == _width[P](), "evaluation point has the wrong number of coordinates"
        comptime k = _Join[_Kind[C], _TupleKind[Tuple[*Ts]]]
        var input = _prepare[I, P, C](values, budget)
        var context = _Context[k]()
        comptime if _Kind[C] == 3:
            context._value = rebind_var[_Ring[k].Context](input._core[].ring.copy())
        comptime for i in range(Tuple[*Ts].Ts.length):
            budget.charge(1)
            comptime if Tuple[*Ts].Ts[i] == ModInt:
                context.observe(rebind[ModInt](point[i]).modulus, budget)
        var ctx = context.get()
        var p = _promote[k](input, ctx, budget)
        _allocation[Tuple[Int64, _Ring[k]]](Tuple[*Ts].Ts.length, budget)
        var assignments = List[Tuple[Int64, _Ring[k]]](capacity=Tuple[*Ts].Ts.length)
        comptime for i in range(Tuple[*Ts].Ts.length):
            assignments.append((Int64(i), _wrap[k](_convert[k](point[i], ctx, budget))))
        var result = _evaluate(p._core[], assignments, budget)
        _charge_size(result.size(), budget)
        return rebind_var[_Evaluation[C, Tuple[*Ts]]](_unwrap[k](result))


def evaluate[I: Iterable, P: Copyable & Deinitable, C: Copyable & Deinitable, *Ts: Copyable & Deinitable](values: I, point: Tuple[*Ts], *, max_steps: UInt64 = UInt64.MAX) raises PolyError -> _Evaluation[C, Tuple[*Ts]] where _Element[I] == Tuple[P, C]:
    """Evaluate at an exact point with an optional work limit.

    Parameters:
        I: The inferred input iterable type.
        P: The power shape: Int or a tuple of Int powers.
        C: The inferred input coefficient type.
        Ts: The inferred element types of the input tuple.

    Args:
        values: The coefficient sequence, sparse terms, or prepared array.
        point: An exact scalar for one variable, or a coordinate tuple in variable order.
        max_steps: The complete call's work allowance; defaults to UInt64.MAX.

    Returns:
        The exact scalar after joint promotion, or an algebraic Real for algebraic coordinates.

    Raises:
        PolyError: LIMIT on exhausted work, CAPACITY on unrepresentable sizes, or DOMAIN for incompatible input.
    """
    var budget = Budget(max_steps)
    return evaluate[I, P, C, *Ts](values, point, budget)


def evaluate[I: Iterable, P: Copyable & Deinitable, C: Copyable & Deinitable, X: Copyable & Deinitable](values: I, point: X, mut budget: Budget) raises PolyError -> _Scalar[_Join[_Kind[C], _Kind[X]]] where (_Element[I] == Tuple[P, C] and _Kind[X] >= 0):
    """Evaluate at an exact point with an optional work limit.

    Parameters:
        I: The inferred input iterable type.
        P: The power shape: Int or a tuple of Int powers.
        C: The inferred input coefficient type.
        X: The inferred point or point-sequence type.

    Args:
        values: The coefficient sequence, sparse terms, or prepared array.
        point: An exact scalar for one variable, or a coordinate tuple in variable order.
        budget: The caller-owned work allowance, shared through preparation and computation.

    Returns:
        The exact scalar after joint promotion, or an algebraic Real for algebraic coordinates.

    Raises:
        PolyError: LIMIT on exhausted work, CAPACITY on unrepresentable sizes, or DOMAIN for incompatible input.
    """
    comptime assert _width[P]() == 1, "multivariate evaluation needs a tuple of coordinates"
    _charge_size(_size(point), budget)
    return rebind_var[_Scalar[_Join[_Kind[C], _Kind[X]]]](evaluate[I, P, C, X](values, (point.copy(),), budget))


def evaluate[I: Iterable, P: Copyable & Deinitable, C: Copyable & Deinitable, X: Copyable & Deinitable](values: I, point: X, *, max_steps: UInt64 = UInt64.MAX) raises PolyError -> _Scalar[_Join[_Kind[C], _Kind[X]]] where (_Element[I] == Tuple[P, C] and _Kind[X] >= 0):
    """Evaluate at an exact point with an optional work limit.

    Parameters:
        I: The inferred input iterable type.
        P: The power shape: Int or a tuple of Int powers.
        C: The inferred input coefficient type.
        X: The inferred point or point-sequence type.

    Args:
        values: The coefficient sequence, sparse terms, or prepared array.
        point: An exact scalar for one variable, or a coordinate tuple in variable order.
        max_steps: The complete call's work allowance; defaults to UInt64.MAX.

    Returns:
        The exact scalar after joint promotion, or an algebraic Real for algebraic coordinates.

    Raises:
        PolyError: LIMIT on exhausted work, CAPACITY on unrepresentable sizes, or DOMAIN for incompatible input.
    """
    var budget = Budget(max_steps)
    return evaluate[I, P, C, X](values, point, budget)


def asarray[I: IterableOwned & Deinitable, P: Copyable & Deinitable, C: Copyable & Deinitable](var values: I, mut budget: Budget) raises PolyError -> Array[P, _Kind[C]] where _OwnedElement[I] == Tuple[P, C]:
    """Consume an owning iterator directly into the core term buffer.

    Parameters:
        I: The inferred input iterable type.
        P: The power shape: Int or a tuple of Int powers.
        C: The inferred input coefficient type.

    Args:
        values: The coefficient sequence, sparse terms, or prepared array.
        budget: The caller-owned work allowance, shared through preparation and computation.

    Returns:
        An immutable canonical polynomial that retains its exact domain and modulus.

    Raises:
        PolyError: LIMIT on exhausted work, CAPACITY on unrepresentable sizes, or DOMAIN for incompatible input.
    """
    return _collect[P, C, _Kind[C]](iter(values^), _Context[_Kind[C]](), budget)


def asarray[I: IterableOwned & Deinitable, P: Copyable & Deinitable, C: Copyable & Deinitable](var values: I, *, max_steps: UInt64 = UInt64.MAX) raises PolyError -> Array[P, _Kind[C]] where _OwnedElement[I] == Tuple[P, C]:
    """Normalize exact inputs with an optional work limit; prepared arrays share storage.

    Parameters:
        I: The inferred input iterable type.
        P: The power shape: Int or a tuple of Int powers.
        C: The inferred input coefficient type.

    Args:
        values: The coefficient sequence, sparse terms, or prepared array.
        max_steps: The complete call's work allowance; defaults to UInt64.MAX.

    Returns:
        An immutable canonical polynomial that retains its exact domain and modulus.

    Raises:
        PolyError: LIMIT on exhausted work, CAPACITY on unrepresentable sizes, or DOMAIN for incompatible input.
    """
    var budget = Budget(max_steps)
    return asarray[I, P, C](values^, budget)


def asarray[I: IterableOwned & Deinitable, P: Copyable & Deinitable, C: Copyable & Deinitable](var values: I, mut budget: Budget, *, modulus: UInt64) raises PolyError -> Array[P, 3] where _OwnedElement[I] == Tuple[P, C]:
    """Normalize exact inputs with an optional work limit; prepared arrays share storage.

    Parameters:
        I: The inferred input iterable type.
        P: The power shape: Int or a tuple of Int powers.
        C: The inferred input coefficient type.

    Args:
        values: The coefficient sequence, sparse terms, or prepared array.
        budget: The caller-owned work allowance, shared through preparation and computation.
        modulus: The prime modulus; supported primes are below 2**62.

    Returns:
        An immutable canonical polynomial that retains its exact domain and modulus.

    Raises:
        PolyError: LIMIT on exhausted work, CAPACITY on unrepresentable sizes, or DOMAIN for incompatible input.
    """
    var context = _Context[3]()
    context.observe(modulus, budget)
    return _collect[P, C, 3](iter(values^), context^, budget)


def asarray[I: IterableOwned & Deinitable, P: Copyable & Deinitable, C: Copyable & Deinitable](var values: I, *, modulus: UInt64, max_steps: UInt64 = UInt64.MAX) raises PolyError -> Array[P, 3] where _OwnedElement[I] == Tuple[P, C]:
    """Normalize exact inputs with an optional work limit; prepared arrays share storage.

    Parameters:
        I: The inferred input iterable type.
        P: The power shape: Int or a tuple of Int powers.
        C: The inferred input coefficient type.

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
    return asarray[I, P, C](values^, budget, modulus=modulus)


# Mojo 1.1 cannot project Ts from a Tuple after an AnyType downcast.
# Match accepted scalar types while keeping P available to the type solver.
comptime _TermScalar[P: Movable, T: Movable] = _alg.Complex if T == Tuple[P, _alg.Complex] else _alg.Real if T == Tuple[P, _alg.Real] else ModInt if T == Tuple[P, ModInt] else ExactComplex if T == Tuple[P, ExactComplex] else Rational if T == Tuple[P, Rational] else Integer if T == Tuple[P, Integer] else Int8 if T == Tuple[P, Int8] else UInt8 if T == Tuple[P, UInt8] else Int16 if T == Tuple[P, Int16] else UInt16 if T == Tuple[P, UInt16] else Int32 if T == Tuple[P, Int32] else UInt32 if T == Tuple[P, UInt32] else Int64 if T == Tuple[P, Int64] else UInt64 if T == Tuple[P, UInt64] else Int
comptime _TermKind[P: Movable, T: Movable] = (
    5 if T == Tuple[P, _alg.Complex] else
    4 if T == Tuple[P, _alg.Real] else
    3 if T == Tuple[P, ModInt] else
    2 if T == Tuple[P, ExactComplex] else
    1 if T == Tuple[P, Rational] else
    0 if T == Tuple[P, Int] or T == Tuple[P, Integer] or T == Tuple[P, Int8] or T == Tuple[P, UInt8] or T == Tuple[P, Int16] or T == Tuple[P, UInt16] or T == Tuple[P, Int32] or T == Tuple[P, UInt32] or T == Tuple[P, Int64] or T == Tuple[P, UInt64] else -1
)
comptime _TermRank[P: Movable, previous: Int, T: Movable] = _Join[previous, _TermKind[P, T]]
comptime _TermsKind[P: Movable, T: type_of(Tuple)] = T.Ts.reduce[0, _TermRank[P, ...]]


def _mixed[k: Int, P: Copyable & Deinitable, C: Copyable & Deinitable, *Ts: Copyable & Deinitable](values: Tuple[*Ts], var context: _Context[k], mut budget: Budget) raises PolyError -> Array[P, k] where Tuple[*Ts].Ts[0] == Tuple[P, C]:
    comptime for i in range(Tuple[*Ts].Ts.length):
        comptime T = Tuple[*Ts].Ts[i]
        comptime assert _TermKind[P, T] >= 0, "sparse tuples need (power, exact coefficient) pairs with the same power shape; convert floats explicitly"
        budget.charge(1)
        comptime if _TermKind[P, T] == 3:
            context.observe(rebind[Tuple[P, ModInt]](values[i])[1].modulus, budget)
    var ctx = context.get()
    _allocation[Term[_Ring[k]]](Tuple[*Ts].Ts.length, budget)
    var terms = List[Term[_Ring[k]]](capacity=Tuple[*Ts].Ts.length)
    comptime for i in range(Tuple[*Ts].Ts.length):
        comptime T = Tuple[*Ts].Ts[i]
        terms.append(_term[k](rebind[Tuple[P, _TermScalar[P, T]]](values[i]), ctx, budget))
    return _finish[P, k](terms^, ctx, budget)


def asarray[P: Copyable & Deinitable, C: Copyable & Deinitable, *Ts: Copyable & Deinitable](values: Tuple[*Ts], mut budget: Budget) raises PolyError -> Array[P, _TermsKind[P, Tuple[*Ts]]] where Tuple[*Ts].Ts[0] == Tuple[P, C]:
    """Promote mixed term coefficients together, then normalize their powers.

    Parameters:
        P: The power shape: Int or a tuple of Int powers.
        C: The inferred input coefficient type.
        Ts: The inferred element types of the input tuple.

    Args:
        values: The coefficient sequence, sparse terms, or prepared array.
        budget: The caller-owned work allowance, shared through preparation and computation.

    Returns:
        An immutable canonical polynomial that retains its exact domain and modulus.

    Raises:
        PolyError: LIMIT on exhausted work, CAPACITY on unrepresentable sizes, or DOMAIN for incompatible input.
    """
    comptime k = _TermsKind[P, Tuple[*Ts]]
    return _mixed[k, P, C, *Ts](values, _Context[k](), budget)


def asarray[P: Copyable & Deinitable, C: Copyable & Deinitable, *Ts: Copyable & Deinitable](values: Tuple[*Ts], *, max_steps: UInt64 = UInt64.MAX) raises PolyError -> Array[P, _TermsKind[P, Tuple[*Ts]]] where Tuple[*Ts].Ts[0] == Tuple[P, C]:
    """Normalize exact inputs with an optional work limit; prepared arrays share storage.

    Parameters:
        P: The power shape: Int or a tuple of Int powers.
        C: The inferred input coefficient type.
        Ts: The inferred element types of the input tuple.

    Args:
        values: The coefficient sequence, sparse terms, or prepared array.
        max_steps: The complete call's work allowance; defaults to UInt64.MAX.

    Returns:
        An immutable canonical polynomial that retains its exact domain and modulus.

    Raises:
        PolyError: LIMIT on exhausted work, CAPACITY on unrepresentable sizes, or DOMAIN for incompatible input.
    """
    var budget = Budget(max_steps)
    return asarray[P, C, *Ts](values, budget)


def asarray[P: Copyable & Deinitable, C: Copyable & Deinitable, *Ts: Copyable & Deinitable](values: Tuple[*Ts], mut budget: Budget, *, modulus: UInt64) raises PolyError -> Array[P, 3] where Tuple[*Ts].Ts[0] == Tuple[P, C]:
    """Normalize exact inputs with an optional work limit; prepared arrays share storage.

    Parameters:
        P: The power shape: Int or a tuple of Int powers.
        C: The inferred input coefficient type.
        Ts: The inferred element types of the input tuple.

    Args:
        values: The coefficient sequence, sparse terms, or prepared array.
        budget: The caller-owned work allowance, shared through preparation and computation.
        modulus: The prime modulus; supported primes are below 2**62.

    Returns:
        An immutable canonical polynomial that retains its exact domain and modulus.

    Raises:
        PolyError: LIMIT on exhausted work, CAPACITY on unrepresentable sizes, or DOMAIN for incompatible input.
    """
    var context = _Context[3]()
    context.observe(modulus, budget)
    return _mixed[3, P, C, *Ts](values, context^, budget)


def asarray[P: Copyable & Deinitable, C: Copyable & Deinitable, *Ts: Copyable & Deinitable](values: Tuple[*Ts], *, modulus: UInt64, max_steps: UInt64 = UInt64.MAX) raises PolyError -> Array[P, 3] where Tuple[*Ts].Ts[0] == Tuple[P, C]:
    """Normalize exact inputs with an optional work limit; prepared arrays share storage.

    Parameters:
        P: The power shape: Int or a tuple of Int powers.
        C: The inferred input coefficient type.
        Ts: The inferred element types of the input tuple.

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
    return asarray[P, C, *Ts](values, budget, modulus=modulus)


def subtract[A: Iterable, B: Iterable, P: Copyable & Deinitable, C: Copyable & Deinitable, D: Copyable & Deinitable](a: A, b: B, mut budget: Budget) raises PolyError -> Array[P, _Join[_Kind[C], _Kind[D]]] where (_Element[A] == Tuple[P, C] and _Element[B] == Tuple[P, D]):
    """Subtract polynomials, promoting their coefficients together.

    Parameters:
        A: The first inferred iterable type.
        B: The second inferred iterable type.
        P: The power shape: Int or a tuple of Int powers.
        C: The inferred input coefficient type.
        D: The second inferred coefficient type.

    Args:
        a: The first polynomial.
        b: The second polynomial.
        budget: The caller-owned work allowance, shared through preparation and computation.

    Returns:
        The canonical first polynomial minus the second.

    Raises:
        PolyError: LIMIT on exhausted work, CAPACITY on unrepresentable sizes, or DOMAIN for incompatible input.
    """
    comptime k = _Join[_Kind[C], _Kind[D]]
    comptime if _DirectInput[A] and _DirectInput[B] and 0 <= k and k < 3:
        return _list_sum[k, P, C, D](rebind_var[Span[Tuple[P, C], origin_of(a)]](_input_view(a)), rebind_var[Span[Tuple[P, D], origin_of(b)]](_input_view(b)), True, budget)
    else:
        var pair = _pair[k, A, B, P, C, D](a, b, budget)
        return Array[P, k](pair[0]._core[].sub(pair[1]._core[], budget), budget)


def subtract[A: Iterable, B: Iterable, P: Copyable & Deinitable, C: Copyable & Deinitable, D: Copyable & Deinitable](a: A, b: B, *, max_steps: UInt64 = UInt64.MAX) raises PolyError -> Array[P, _Join[_Kind[C], _Kind[D]]] where (_Element[A] == Tuple[P, C] and _Element[B] == Tuple[P, D]):
    """Subtract the second polynomial from the first with an optional work limit.

    Parameters:
        A: The first inferred iterable type.
        B: The second inferred iterable type.
        P: The power shape: Int or a tuple of Int powers.
        C: The inferred input coefficient type.
        D: The second inferred coefficient type.

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
    return subtract[A, B, P, C, D](a, b, budget)




def negative[I: Iterable, P: Copyable & Deinitable, C: Copyable & Deinitable](values: I, mut budget: Budget) raises PolyError -> Array[P, _Kind[C]] where _Element[I] == Tuple[P, C]:
    """Negate every coefficient, preserving the domain and power shape.

    Parameters:
        I: The inferred input iterable type.
        P: The power shape: Int or a tuple of Int powers.
        C: The inferred input coefficient type.

    Args:
        values: The coefficient sequence, sparse terms, or prepared array.
        budget: The caller-owned work allowance, shared through preparation and computation.

    Returns:
        The polynomial with every coefficient negated.

    Raises:
        PolyError: LIMIT on exhausted work, CAPACITY on unrepresentable sizes, or DOMAIN for incompatible input.
    """
    var p = _prepare[I, P, C](values, budget)
    return Array[P, _Kind[C]](p._core[].neg(budget), budget)


def power[I: Iterable, P: Copyable & Deinitable, C: Copyable & Deinitable](values: I, exponent: Int, mut budget: Budget) raises PolyError -> Array[P, _Kind[C]] where _Element[I] == Tuple[P, C]:
    """Raise a polynomial to a nonnegative power by repeated squaring.

    Zero to power zero returns the constant one. Negative exponents raise DOMAIN.

    Parameters:
        I: The inferred input iterable type.
        P: The power shape: Int or a tuple of Int powers.
        C: The inferred input coefficient type.

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
    comptime k = _Kind[C]
    var factor = _prepare[I, P, C](values, budget)
    var result = Array[P, k](SparsePoly[_Ring[k]].constant(_Ring[k].one(factor._core[].ring), factor._core[].order, budget), budget)
    var remaining = exponent
    while remaining:
        budget.charge(1)
        if remaining & 1:
            result = Array[P, k](result._core[].mul(factor._core[], budget), budget)
        remaining >>= 1
        if remaining:
            factor = Array[P, k](factor._core[].mul(factor._core[], budget), budget)
    return result^


def integral[I: Iterable, P: Copyable & Deinitable, C: Copyable & Deinitable](values: I, mut budget: Budget, *, axis: Int = 0) raises PolyError -> Array[P, _FieldKind[_Kind[C]]] where _Element[I] == Tuple[P, C]:
    """Integrate along an axis with zero constant, promoting integers to rationals.

    Other domains are retained. In a prime field, a nonzero coefficient that
    requires division by zero raises DOMAIN. Axis numbers start at zero.

    Parameters:
        I: The inferred input iterable type.
        P: The power shape: Int or a tuple of Int powers.
        C: The inferred input coefficient type.

    Args:
        values: The coefficient sequence, sparse terms, or prepared array.
        budget: The caller-owned work allowance, shared through preparation and computation.
        axis: The zero-based variable index.

    Returns:
        The zero-constant antiderivative; integer coefficients promote to QQ.

    Raises:
        PolyError: LIMIT on exhausted work, CAPACITY on unrepresentable sizes, or DOMAIN for incompatible input.
    """
    if axis < 0 or axis >= _width[P]():
        raise PolyError(PolyErrorKind.DOMAIN, "integral axis is outside the polynomial's variables")
    comptime k = _FieldKind[_Kind[C]]
    var p = _prepare[I, P, C](values, budget)
    var ctx: _Ring[k].Context
    comptime if k == 3:
        ctx = rebind_var[_Ring[k].Context](p._core[].ring.copy())
    else:
        ctx = rebind_var[_Ring[k].Context](NoContext())
    var promoted = _promote[k](p, ctx, budget)
    return Array[P, k](integrate_sparse(promoted._core[], Int64(axis), budget), budget)


def divmod[A: Iterable, B: Iterable, P: Copyable & Deinitable, C: Copyable & Deinitable, D: Copyable & Deinitable](a: A, b: B, mut budget: Budget, *, order: String = "lex", axes: List[Int] = List[Int]()) raises PolyError -> Tuple[Array[P, _FieldKind[_Join[_Kind[C], _Kind[D]]]], Array[P, _FieldKind[_Join[_Kind[C], _Kind[D]]]]] where (_Element[A] == Tuple[P, C] and _Element[B] == Tuple[P, D]):
    """Return quotient and remainder in the requested monomial order.

    Integer inputs promote to QQ. A zero divisor raises DOMAIN. For several
    variables, the remainder is reduced by the divisor's leading monomial;
    order defaults to lex with axis zero first. Returned arrays keep canonical storage order.

    Parameters:
        A: The first inferred iterable type.
        B: The second inferred iterable type.
        P: The power shape: Int or a tuple of Int powers.
        C: The inferred input coefficient type.
        D: The second inferred coefficient type.

    Args:
        a: The first polynomial.
        b: The second polynomial.
        budget: The caller-owned work allowance, shared through preparation and computation.
        order: One of lex, grlex, or grevlex; defaults to lex.
        axes: All axes in descending priority; empty uses tuple order.

    Returns:
        A pair (quotient, remainder); integer coefficients promote to QQ.

    Raises:
        PolyError: LIMIT on exhausted work, CAPACITY on unrepresentable sizes, or DOMAIN for incompatible input.
    """
    var monomial_order = _monomial_order[P](order, axes, budget)
    comptime k = _FieldKind[_Join[_Kind[C], _Kind[D]]]
    comptime Field = downcast[_Ring[k], CoefficientField]
    var pair = _pair[k, A, B, P, C, D](a, b, budget)
    var p = pair[0]._core[].reorder(monomial_order, budget)
    ref q = pair[1]._core[]
    _allocation[SparsePoly[Field]](1, budget)
    var divisors = List[SparsePoly[Field]](capacity=1)
    # reorder makes a budgeted owned copy for the core's divisor collection.
    divisors.append(rebind_var[SparsePoly[Field]](q.reorder(monomial_order, budget)))
    var result = divide_by_list(rebind[SparsePoly[Field]](p), divisors, budget)
    var quotient = result.quotients.pop()
    var remainder = SparsePoly[Field].zero(p.order, p.ring, budget)
    swap(remainder, result.remainder)
    return (_division_output[P, k](rebind_var[SparsePoly[_Ring[k]]](quotient^), budget),
            _division_output[P, k](rebind_var[SparsePoly[_Ring[k]]](remainder^), budget))


def degree[I: Iterable, P: Copyable & Deinitable, C: Copyable & Deinitable](values: I, mut budget: Budget, *, axis: Int = -1) raises PolyError -> Int where _Element[I] == Tuple[P, C]:
    """Return total degree, or degree in one axis; the zero polynomial has degree -1.

    The default axis=-1 selects total degree. Other axes are numbered from zero.

    Parameters:
        I: The inferred input iterable type.
        P: The power shape: Int or a tuple of Int powers.
        C: The inferred input coefficient type.

    Args:
        values: The coefficient sequence, sparse terms, or prepared array.
        budget: The caller-owned work allowance, shared through preparation and computation.
        axis: The zero-based variable index; -1 selects total degree.

    Returns:
        The degree, or -1 for the zero polynomial.

    Raises:
        PolyError: LIMIT on exhausted work, CAPACITY on unrepresentable sizes, or DOMAIN for incompatible input.
    """
    if axis < -1 or axis >= _width[P]():
        raise PolyError(PolyErrorKind.DOMAIN, "degree axis is outside the polynomial's variables")
    var p = _prepare[I, P, C](values, budget)
    var result = -1
    for term in p._core[].terms:
        budget.charge(1)
        var current = 0
        for entry in term.monomial.pairs:
            budget.charge(1)
            if axis == -1 or entry[0] == Int64(axis):
                current = _sum(current, Int(UInt64(entry[1])))
        result = max(result, current)
    return result


def negative[I: Iterable, P: Copyable & Deinitable, C: Copyable & Deinitable](values: I, *, max_steps: UInt64 = UInt64.MAX) raises PolyError -> Array[P, _Kind[C]] where _Element[I] == Tuple[P, C]:
    """Compute with an optional work limit; see the shared-budget overload.

    Parameters:
        I: The inferred input iterable type.
        P: The power shape: Int or a tuple of Int powers.
        C: The inferred input coefficient type.

    Args:
        values: The coefficient sequence, sparse terms, or prepared array.
        max_steps: The complete call's work allowance; defaults to UInt64.MAX.

    Returns:
        The polynomial with every coefficient negated.

    Raises:
        PolyError: LIMIT on exhausted work, CAPACITY on unrepresentable sizes, or DOMAIN for incompatible input.
    """
    var budget = Budget(max_steps)
    return negative[I, P, C](values, budget)


def power[I: Iterable, P: Copyable & Deinitable, C: Copyable & Deinitable](values: I, exponent: Int, *, max_steps: UInt64 = UInt64.MAX) raises PolyError -> Array[P, _Kind[C]] where _Element[I] == Tuple[P, C]:
    """Compute with an optional work limit; see the shared-budget overload.

    Parameters:
        I: The inferred input iterable type.
        P: The power shape: Int or a tuple of Int powers.
        C: The inferred input coefficient type.

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
    return power[I, P, C](values, exponent, budget)


def integral[I: Iterable, P: Copyable & Deinitable, C: Copyable & Deinitable](values: I, *, max_steps: UInt64 = UInt64.MAX, axis: Int = 0) raises PolyError -> Array[P, _FieldKind[_Kind[C]]] where _Element[I] == Tuple[P, C]:
    """Compute with an optional work limit; see the shared-budget overload.

    Parameters:
        I: The inferred input iterable type.
        P: The power shape: Int or a tuple of Int powers.
        C: The inferred input coefficient type.

    Args:
        values: The coefficient sequence, sparse terms, or prepared array.
        max_steps: The complete call's work allowance; defaults to UInt64.MAX.
        axis: The zero-based variable index.

    Returns:
        The zero-constant antiderivative; integer coefficients promote to QQ.

    Raises:
        PolyError: LIMIT on exhausted work, CAPACITY on unrepresentable sizes, or DOMAIN for incompatible input.
    """
    var budget = Budget(max_steps)
    return integral[I, P, C](values, budget, axis=axis)


def divmod[A: Iterable, B: Iterable, P: Copyable & Deinitable, C: Copyable & Deinitable, D: Copyable & Deinitable](a: A, b: B, *, max_steps: UInt64 = UInt64.MAX, order: String = "lex", axes: List[Int] = List[Int]()) raises PolyError -> Tuple[Array[P, _FieldKind[_Join[_Kind[C], _Kind[D]]]], Array[P, _FieldKind[_Join[_Kind[C], _Kind[D]]]]] where (_Element[A] == Tuple[P, C] and _Element[B] == Tuple[P, D]):
    """Divide with an optional work limit; see the shared-budget overload.

    Parameters:
        A: The first inferred iterable type.
        B: The second inferred iterable type.
        P: The power shape: Int or a tuple of Int powers.
        C: The inferred input coefficient type.
        D: The second inferred coefficient type.

    Args:
        a: The first polynomial.
        b: The second polynomial.
        max_steps: The complete call's work allowance; defaults to UInt64.MAX.
        order: One of lex, grlex, or grevlex; defaults to lex.
        axes: All axes in descending priority; empty uses tuple order.

    Returns:
        A pair (quotient, remainder); integer coefficients promote to QQ.

    Raises:
        PolyError: LIMIT on exhausted work, CAPACITY on unrepresentable sizes, or DOMAIN for incompatible input.
    """
    var budget = Budget(max_steps)
    return divmod[A, B, P, C, D](a, b, budget, order=order, axes=axes)


def degree[I: Iterable, P: Copyable & Deinitable, C: Copyable & Deinitable](values: I, *, max_steps: UInt64 = UInt64.MAX, axis: Int = -1) raises PolyError -> Int where _Element[I] == Tuple[P, C]:
    """Compute with an optional work limit; see the shared-budget overload.

    Parameters:
        I: The inferred input iterable type.
        P: The power shape: Int or a tuple of Int powers.
        C: The inferred input coefficient type.

    Args:
        values: The coefficient sequence, sparse terms, or prepared array.
        max_steps: The complete call's work allowance; defaults to UInt64.MAX.
        axis: The zero-based variable index; -1 selects total degree.

    Returns:
        The degree, or -1 for the zero polynomial.

    Raises:
        PolyError: LIMIT on exhausted work, CAPACITY on unrepresentable sizes, or DOMAIN for incompatible input.
    """
    var budget = Budget(max_steps)
    return degree[I, P, C](values, budget, axis=axis)


def evaluate_many[I: Iterable, X: Iterable, P: Copyable & Deinitable, C: Copyable & Deinitable](values: I, points: X, mut budget: Budget) raises PolyError -> Values[_Scalar[_Join[_Kind[C], _Kind[_Element[X]]]], _Join[_Kind[C], _Kind[_Element[X]]]] where (_Element[I] == Tuple[P, C] and _Kind[_Element[X]] >= 0):
    """Evaluate at each point, returning values in input order, including zeros.

    Multivariate points are coordinate tuples. The polynomial is prepared and
    promoted once; every point must use the same exact coefficient domain.

    Parameters:
        I: The inferred input iterable type.
        X: The inferred point or point-sequence type.
        P: The power shape: Int or a tuple of Int powers.
        C: The inferred input coefficient type.

    Args:
        values: The coefficient sequence, sparse terms, or prepared array.
        points: A one-dimensional sequence of exact points, in output order.
        budget: The caller-owned work allowance, shared through preparation and computation.

    Returns:
        An immutable Values sequence, preserving every input point and returned zero.

    Raises:
        PolyError: LIMIT on exhausted work, CAPACITY on unrepresentable sizes, or DOMAIN for incompatible input.
    """
    comptime k = _Join[_Kind[C], _Kind[_Element[X]]]
    comptime assert _width[P]() == 1, "multivariate evaluation needs tuples of coordinates"
    _check_batch(points, message="evaluation points must form a one-dimensional sequence")
    var input = _prepare[I, P, C](values, budget)
    var context = _Context[k]()
    comptime if _Kind[C] == 3:
        context._value = rebind_var[_Ring[k].Context](input._core[].ring.copy())
    var modulus = _merge_modulus(input.modulus(), _initial_modulus(points))
    if modulus:
        context.observe(modulus, budget)
    var prepared = Optional[Array[P, k]]()
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
        _allocation[Tuple[Int64, _Ring[k]]](1, budget)
        var assignments: List[Tuple[Int64, _Ring[k]]] = [(Int64(0), _wrap[k](_convert[k](point, ctx, budget)))]
        var result = _evaluate(prepared.value()._core[], assignments, budget)
        _charge_size(result.size(), budget)
        _grow(output, budget)
        output.append(_unwrap[k](result))
    var ctx = context.get()
    comptime if k == 3:
        modulus = rebind[Modulus](ctx).value
    return Values[_Scalar[k], k](output^, modulus, budget)


def evaluate_many[I: Iterable, X: Iterable, P: Copyable & Deinitable, C: Copyable & Deinitable](values: I, points: X, *, max_steps: UInt64 = UInt64.MAX) raises PolyError -> Values[_Scalar[_Join[_Kind[C], _Kind[_Element[X]]]], _Join[_Kind[C], _Kind[_Element[X]]]] where (_Element[I] == Tuple[P, C] and _Kind[_Element[X]] >= 0):
    """Evaluate a sequence of points with an optional work limit.

    Parameters:
        I: The inferred input iterable type.
        X: The inferred point or point-sequence type.
        P: The power shape: Int or a tuple of Int powers.
        C: The inferred input coefficient type.

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
    return evaluate_many[I, X, P, C](values, points, budget)


def evaluate_many[I: Iterable, X: Iterable, P: Copyable & Deinitable, C: Copyable & Deinitable, *Ts: Copyable & Deinitable](values: I, points: X, mut budget: Budget) raises PolyError -> Values[_Scalar[_Join[_Kind[C], _TupleKind[Tuple[*Ts]]]], _Join[_Kind[C], _TupleKind[Tuple[*Ts]]]] where (_Element[I] == Tuple[P, C] and _Element[X] == Tuple[*Ts]):
    """Evaluate at each point, returning values in input order, including zeros.

    Multivariate points are coordinate tuples. The polynomial is prepared and
    promoted once; every point must use the same exact coefficient domain.

    Parameters:
        I: The inferred input iterable type.
        X: The inferred point or point-sequence type.
        P: The power shape: Int or a tuple of Int powers.
        C: The inferred input coefficient type.
        Ts: The inferred element types of the input tuple.

    Args:
        values: The coefficient sequence, sparse terms, or prepared array.
        points: A one-dimensional sequence of exact points, in output order.
        budget: The caller-owned work allowance, shared through preparation and computation.

    Returns:
        An immutable Values sequence, preserving every input point and returned zero.

    Raises:
        PolyError: LIMIT on exhausted work, CAPACITY on unrepresentable sizes, or DOMAIN for incompatible input.
    """
    comptime k = _Join[_Kind[C], _TupleKind[Tuple[*Ts]]]
    comptime assert Tuple[*Ts].Ts.length == _width[P](), "evaluation point has the wrong number of coordinates"
    _check_batch(points, message="evaluation points must form a one-dimensional sequence")
    var input = _prepare[I, P, C](values, budget)
    var context = _Context[k]()
    comptime if _Kind[C] == 3:
        context._value = rebind_var[_Ring[k].Context](input._core[].ring.copy())
    var modulus = _merge_modulus(input.modulus(), _initial_modulus(points))
    if modulus:
        context.observe(modulus, budget)
    var prepared = Optional[Array[P, k]]()
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
        var point = rebind_var[Tuple[*Ts]](raw^)
        comptime for i in range(Tuple[*Ts].Ts.length):
            budget.charge(1)
            comptime if Tuple[*Ts].Ts[i] == ModInt:
                context.observe(rebind[ModInt](point[i]).modulus, budget)
        var ctx = context.get()
        if not prepared:
            prepared = _promote[k](input, ctx, budget)
        _allocation[Tuple[Int64, _Ring[k]]](Tuple[*Ts].Ts.length, budget)
        var assignments = List[Tuple[Int64, _Ring[k]]](capacity=Tuple[*Ts].Ts.length)
        comptime for i in range(Tuple[*Ts].Ts.length):
            assignments.append((Int64(i), _wrap[k](_convert[k](point[i], ctx, budget))))
        var result = _evaluate(prepared.value()._core[], assignments, budget)
        _charge_size(result.size(), budget)
        _grow(output, budget)
        output.append(_unwrap[k](result))
    var ctx = context.get()
    comptime if k == 3:
        modulus = rebind[Modulus](ctx).value
    return Values[_Scalar[k], k](output^, modulus, budget)


def evaluate_many[I: Iterable, X: Iterable, P: Copyable & Deinitable, C: Copyable & Deinitable, *Ts: Copyable & Deinitable](values: I, points: X, *, max_steps: UInt64 = UInt64.MAX) raises PolyError -> Values[_Scalar[_Join[_Kind[C], _TupleKind[Tuple[*Ts]]]], _Join[_Kind[C], _TupleKind[Tuple[*Ts]]]] where (_Element[I] == Tuple[P, C] and _Element[X] == Tuple[*Ts]):
    """Evaluate a sequence of points with an optional work limit.

    Parameters:
        I: The inferred input iterable type.
        X: The inferred point or point-sequence type.
        P: The power shape: Int or a tuple of Int powers.
        C: The inferred input coefficient type.
        Ts: The inferred element types of the input tuple.

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
    return evaluate_many[I, X, P, C, *Ts](values, points, budget)




def to_core[I: Iterable, P: Copyable & Deinitable, C: Copyable & Deinitable](values: I, mut budget: Budget, *, variables: List[Int64] = List[Int64]()) raises PolyError -> SparsePoly[_Ring[_Kind[C]]] where (_Element[I] == Tuple[P, C] and _Kind[C] >= 0):
    """Return an independent mutable core polynomial with an explicit axis-to-ID map.

    An empty map uses IDs 0 through the number of axes minus one. Output uses
    lexicographic priority in array-axis order, even when IDs are not increasing.

    Changing the returned core storage cannot affect a prepared input. Sparse export uses lexicographic order with the supplied IDs in axis-priority order.

    Parameters:
        I: The inferred input iterable type.
        P: The power shape: Int or a tuple of Int powers.
        C: The inferred input coefficient type.

    Args:
        values: The coefficient sequence, sparse terms, or prepared array.
        budget: The caller-owned work allowance, shared through preparation and computation.
        variables: Core variable IDs in array-axis order. An empty list selects 0, 1, and so on.

    Returns:
        An independent mutable core polynomial with the requested variable IDs and the same exact domain.

    Raises:
        PolyError: LIMIT on exhausted work, CAPACITY on unrepresentable sizes, DOMAIN for invalid input, or UNSUPPORTED for a documented domain restriction.
    """
    var p = _prepare[I, P, C](values, budget)
    var mapping = _variables(_width[P](), variables, budget)
    return _sparse_copy(p._core[], mapping, True, budget)


def from_core[C: CoefficientRing, *, ndim: Int = 1](values: SparsePoly[C], mut budget: Budget, *, variables: List[Int64] = List[Int64]()) raises PolyError -> Array[_Shape[ndim], _CoreKind[C]]:
    """Validate and copy a core polynomial into a fixed number of array axes.

    Use from_core[ndim=2] for two variables. The optional map lists core IDs in array
    axis order; its default is 0, 1, and so on. Unknown variables are rejected.
    One axis produces integer powers; several axes produce power tuples.

    Checks core invariants and modular residues, then copies storage. Mutating the core afterwards cannot affect the result. Dense import normalizes the sole variable to zero. Sparse import rejects used IDs absent from the map and normalizes term order to lexicographic.

    Parameters:
        C: The supported core ring: ZZ, QQ, QQi, ModInt, AA, or QQbar.
        ndim: The nonnegative number of sparse axes, including unused axes; zero accepts constants only.

    Args:
        values: The mutable core SparsePoly to validate and copy.
        budget: The caller-owned work allowance, shared through preparation and computation.
        variables: Core variable IDs in array-axis order. An empty list selects 0, 1, and so on.

    Returns:
        An independent immutable array in the core coefficient domain, with normalized variable IDs.

    Raises:
        PolyError: LIMIT on exhausted work, CAPACITY on unrepresentable sizes, DOMAIN for invalid input, or UNSUPPORTED for a documented domain restriction.
    """
    comptime assert ndim >= 0, "sparse core import needs a nonnegative axis count"
    comptime k = _CoreKind[C]
    var mapping = _variables(ndim, variables, budget)
    return Array[_Shape[ndim], k](rebind_var[SparsePoly[_Ring[k]]](_sparse_copy(values, mapping, False, budget)), budget)


def to_core[I: Iterable, P: Copyable & Deinitable, C: Copyable & Deinitable](values: I, *, max_steps: UInt64 = UInt64.MAX, variables: List[Int64] = List[Int64]()) raises PolyError -> SparsePoly[_Ring[_Kind[C]]] where (_Element[I] == Tuple[P, C] and _Kind[C] >= 0):
    """Copy between array and core representations with an optional work limit.

    Changing the returned core storage cannot affect a prepared input. Sparse export uses lexicographic order with the supplied IDs in axis-priority order.

    Parameters:
        I: The inferred input iterable type.
        P: The power shape: Int or a tuple of Int powers.
        C: The inferred input coefficient type.

    Args:
        values: The coefficient sequence, sparse terms, or prepared array.
        max_steps: The complete call's work allowance; defaults to UInt64.MAX.
        variables: Core variable IDs in array-axis order. An empty list selects 0, 1, and so on.

    Returns:
        An independent mutable core polynomial with the requested variable IDs and the same exact domain.

    Raises:
        PolyError: LIMIT on exhausted work, CAPACITY on unrepresentable sizes, DOMAIN for invalid input, or UNSUPPORTED for a documented domain restriction.
    """
    var budget = Budget(max_steps)
    return to_core[I, P, C](values, budget, variables=variables)


def from_core[C: CoefficientRing, *, ndim: Int = 1](values: SparsePoly[C], *, max_steps: UInt64 = UInt64.MAX, variables: List[Int64] = List[Int64]()) raises PolyError -> Array[_Shape[ndim], _CoreKind[C]]:
    """Copy between array and core representations with an optional work limit.

    Checks core invariants and modular residues, then copies storage. Mutating the core afterwards cannot affect the result. Dense import normalizes the sole variable to zero. Sparse import rejects used IDs absent from the map and normalizes term order to lexicographic.

    Parameters:
        C: The supported core ring: ZZ, QQ, QQi, ModInt, AA, or QQbar.
        ndim: The nonnegative number of sparse axes, including unused axes; zero accepts constants only.

    Args:
        values: The mutable core SparsePoly to validate and copy.
        max_steps: The complete call's work allowance; defaults to UInt64.MAX.
        variables: Core variable IDs in array-axis order. An empty list selects 0, 1, and so on.

    Returns:
        An independent immutable array in the core coefficient domain, with normalized variable IDs.

    Raises:
        PolyError: LIMIT on exhausted work, CAPACITY on unrepresentable sizes, DOMAIN for invalid input, or UNSUPPORTED for a documented domain restriction.
    """
    var budget = Budget(max_steps)
    return from_core[C, ndim=ndim](values, budget, variables=variables)



def content[I: Iterable, P: Copyable & Deinitable, C: Copyable & Deinitable](values: I, mut budget: Budget, *, axis: Int = 0) raises PolyError -> Array[P, _Kind[C]] where _Element[I] == Tuple[P, C]:
    """Return the coefficient content in the other axes.

    Integer content is nonnegative. Field content is monic; a nonzero univariate field polynomial has content one. Zero has content zero.

    Parameters:
        I: The inferred input iterable type.
        P: The power shape: Int or a tuple of Int powers.
        C: The inferred input coefficient type.

    Args:
        values: The coefficient sequence, sparse terms, or prepared array.
        budget: The caller-owned work allowance, shared through preparation and computation.
        axis: The zero-based variable index.

    Returns:
        The normalized coefficient GCD; a scalar for dense input or a polynomial in the remaining sparse axes.

    Raises:
        PolyError: LIMIT on exhausted work, CAPACITY on unrepresentable sizes, DOMAIN for invalid input, or UNSUPPORTED for a documented domain restriction.
    """
    comptime k = _Kind[C]
    _axis[P](axis)
    var p = _prepare[I, P, C](values, budget)
    return Array[P, k](_content(p._core[], Int64(axis), budget), budget)

def content[I: Iterable, P: Copyable & Deinitable, C: Copyable & Deinitable](values: I, *, max_steps: UInt64 = UInt64.MAX, axis: Int = 0) raises PolyError -> Array[P, _Kind[C]] where _Element[I] == Tuple[P, C]:
    """Return the coefficient content in the other axes.

    Integer content is nonnegative. Field content is monic; a nonzero univariate field polynomial has content one. Zero has content zero.

    Parameters:
        I: The inferred input iterable type.
        P: The power shape: Int or a tuple of Int powers.
        C: The inferred input coefficient type.

    Args:
        values: The coefficient sequence, sparse terms, or prepared array.
        max_steps: The complete call's work allowance; defaults to UInt64.MAX.
        axis: The zero-based variable index.

    Returns:
        The normalized coefficient GCD; a scalar for dense input or a polynomial in the remaining sparse axes.

    Raises:
        PolyError: LIMIT on exhausted work, CAPACITY on unrepresentable sizes, DOMAIN for invalid input, or UNSUPPORTED for a documented domain restriction.
    """
    var budget = Budget(max_steps)
    return content[I, P, C](values, budget, axis=axis)


def primitive_part[I: Iterable, P: Copyable & Deinitable, C: Copyable & Deinitable](values: I, mut budget: Budget, *, axis: Int = 0) raises PolyError -> Array[P, _Kind[C]] where _Element[I] == Tuple[P, C]:
    """Remove the content with respect to one axis.

    Parameters:
        I: The inferred input iterable type.
        P: The power shape: Int or a tuple of Int powers.
        C: The inferred input coefficient type.

    Args:
        values: The coefficient sequence, sparse terms, or prepared array.
        budget: The caller-owned work allowance, shared through preparation and computation.
        axis: The zero-based variable index.

    Returns:
        The input divided by its content, or zero for a zero input.

    Raises:
        PolyError: LIMIT on exhausted work, CAPACITY on unrepresentable sizes, DOMAIN for invalid input, or UNSUPPORTED for a documented domain restriction.
    """
    comptime k = _Kind[C]
    _axis[P](axis)
    var p = _prepare[I, P, C](values, budget)
    return Array[P, k](_primitive_part(p._core[], Int64(axis), budget), budget)

def primitive_part[I: Iterable, P: Copyable & Deinitable, C: Copyable & Deinitable](values: I, *, max_steps: UInt64 = UInt64.MAX, axis: Int = 0) raises PolyError -> Array[P, _Kind[C]] where _Element[I] == Tuple[P, C]:
    """Remove the content with respect to one axis.

    Parameters:
        I: The inferred input iterable type.
        P: The power shape: Int or a tuple of Int powers.
        C: The inferred input coefficient type.

    Args:
        values: The coefficient sequence, sparse terms, or prepared array.
        max_steps: The complete call's work allowance; defaults to UInt64.MAX.
        axis: The zero-based variable index.

    Returns:
        The input divided by its content, or zero for a zero input.

    Raises:
        PolyError: LIMIT on exhausted work, CAPACITY on unrepresentable sizes, DOMAIN for invalid input, or UNSUPPORTED for a documented domain restriction.
    """
    var budget = Budget(max_steps)
    return primitive_part[I, P, C](values, budget, axis=axis)


def gcd[A: Iterable, B: Iterable, P: Copyable & Deinitable, C: Copyable & Deinitable, D: Copyable & Deinitable](a: A, b: B, mut budget: Budget, *, method: String = "auto") raises PolyError -> Array[P, _Join[_Kind[C], _Kind[D]]] where _Element[A] == Tuple[P, C] and _Element[B] == Tuple[P, D]:
    """Return a positive-leading integer GCD or a monic field GCD.

    Parameters:
        A: The first inferred iterable type.
        B: The second inferred iterable type.
        P: The power shape: Int or a tuple of Int powers.
        C: The inferred input coefficient type.
        D: The second inferred coefficient type.

    Args:
        a: The first polynomial.
        b: The second polynomial.
        budget: The caller-owned work allowance, shared through preparation and computation.
        method: Use auto for existing dispatch or modular for sparse reconstruction over ZZ or QQ.

    Returns:
        The positive-leading integer GCD, including integer content, or the monic field GCD. GCD(0, 0) is zero.

    Raises:
        PolyError: LIMIT on exhausted work, CAPACITY on unrepresentable sizes, DOMAIN for invalid input, or UNSUPPORTED for a documented domain restriction.
    """
    comptime k = _Join[_Kind[C], _Kind[D]]
    var pair = _pair[k, A, B, P, C, D](a, b, budget)
    if method == "auto":
        var value = _gcd_value(pair[0]._core[], pair[1]._core[], budget)
        return Array[P, k](_take_sparse(value), budget)
    var result = _gcd_dispatch(pair[0]._core[], pair[1]._core[], method, budget)
    return Array[P, k](_take_sparse(result.gcd), budget)

def gcd[A: Iterable, B: Iterable, P: Copyable & Deinitable, C: Copyable & Deinitable, D: Copyable & Deinitable](a: A, b: B, *, max_steps: UInt64 = UInt64.MAX, method: String = "auto") raises PolyError -> Array[P, _Join[_Kind[C], _Kind[D]]] where _Element[A] == Tuple[P, C] and _Element[B] == Tuple[P, D]:
    """Return a positive-leading integer GCD or a monic field GCD.

    Parameters:
        A: The first inferred iterable type.
        B: The second inferred iterable type.
        P: The power shape: Int or a tuple of Int powers.
        C: The inferred input coefficient type.
        D: The second inferred coefficient type.

    Args:
        a: The first polynomial.
        b: The second polynomial.
        max_steps: The complete call's work allowance; defaults to UInt64.MAX.
        method: Use auto for existing dispatch or modular for sparse reconstruction over ZZ or QQ.

    Returns:
        The positive-leading integer GCD, including integer content, or the monic field GCD. GCD(0, 0) is zero.

    Raises:
        PolyError: LIMIT on exhausted work, CAPACITY on unrepresentable sizes, DOMAIN for invalid input, or UNSUPPORTED for a documented domain restriction.
    """
    var budget = Budget(max_steps)
    return gcd[A, B, P, C, D](a, b, budget, method=method)


def divide_exact[A: Iterable, B: Iterable, P: Copyable & Deinitable, C: Copyable & Deinitable, D: Copyable & Deinitable](a: A, b: B, mut budget: Budget) raises PolyError -> Optional[Array[P, _Join[_Kind[C], _Kind[D]]]] where _Element[A] == Tuple[P, C] and _Element[B] == Tuple[P, D]:
    """Return a quotient in the inferred ring, or None when division is not exact.

    Integer inputs stay in ZZ unless another operand widens the domain. Use divmod for field division or an explicit Rational coefficient to request QQ.

    Parameters:
        A: The first inferred iterable type.
        B: The second inferred iterable type.
        P: The power shape: Int or a tuple of Int powers.
        C: The inferred input coefficient type.
        D: The second inferred coefficient type.

    Args:
        a: The first polynomial.
        b: The second polynomial.
        budget: The caller-owned work allowance, shared through preparation and computation.

    Returns:
        A quotient in the inferred coefficient ring, or None if that ring contains no exact quotient.

    Raises:
        PolyError: LIMIT on exhausted work, CAPACITY on unrepresentable sizes, DOMAIN for invalid input, or UNSUPPORTED for a documented domain restriction.
    """
    comptime k = _Join[_Kind[C], _Kind[D]]
    var pair = _pair[k, A, B, P, C, D](a, b, budget)
    var result = _divide_exact(pair[0]._core[], pair[1]._core[], budget)
    if not result:
        return None
    return Optional(Array[P, k](result.take(), budget))

def divide_exact[A: Iterable, B: Iterable, P: Copyable & Deinitable, C: Copyable & Deinitable, D: Copyable & Deinitable](a: A, b: B, *, max_steps: UInt64 = UInt64.MAX) raises PolyError -> Optional[Array[P, _Join[_Kind[C], _Kind[D]]]] where _Element[A] == Tuple[P, C] and _Element[B] == Tuple[P, D]:
    """Return a quotient in the inferred ring, or None when division is not exact.

    Integer inputs stay in ZZ unless another operand widens the domain. Use divmod for field division or an explicit Rational coefficient to request QQ.

    Parameters:
        A: The first inferred iterable type.
        B: The second inferred iterable type.
        P: The power shape: Int or a tuple of Int powers.
        C: The inferred input coefficient type.
        D: The second inferred coefficient type.

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
    return divide_exact[A, B, P, C, D](a, b, budget)


def resultant[A: Iterable, B: Iterable, P: Copyable & Deinitable, C: Copyable & Deinitable, D: Copyable & Deinitable](a: A, b: B, mut budget: Budget, *, axis: Int = 0) raises PolyError -> Array[P, _Join[_Kind[C], _Kind[D]]] where _Element[A] == Tuple[P, C] and _Element[B] == Tuple[P, D]:
    """Eliminate the variable using the Sylvester sign convention.

    Two nonzero constants in the elimination variable raise DOMAIN; a zero operand returns zero. Sparse output retains the eliminated axis with exponent zero.

    Parameters:
        A: The first inferred iterable type.
        B: The second inferred iterable type.
        P: The power shape: Int or a tuple of Int powers.
        C: The inferred input coefficient type.
        D: The second inferred coefficient type.

    Args:
        a: The first polynomial.
        b: The second polynomial.
        budget: The caller-owned work allowance, shared through preparation and computation.
        axis: The zero-based variable index.

    Returns:
        The Sylvester-convention resultant; a scalar for dense input or an array retaining the sparse power shape.

    Raises:
        PolyError: LIMIT on exhausted work, CAPACITY on unrepresentable sizes, DOMAIN for invalid input, or UNSUPPORTED for a documented domain restriction.
    """
    comptime k = _Join[_Kind[C], _Kind[D]]
    _axis[P](axis)
    var pair = _pair[k, A, B, P, C, D](a, b, budget)
    var value = _resultant_value(pair[0]._core[], pair[1]._core[], Int64(axis), budget)
    return Array[P, k](_take_sparse(value), budget)

def resultant[A: Iterable, B: Iterable, P: Copyable & Deinitable, C: Copyable & Deinitable, D: Copyable & Deinitable](a: A, b: B, *, max_steps: UInt64 = UInt64.MAX, axis: Int = 0) raises PolyError -> Array[P, _Join[_Kind[C], _Kind[D]]] where _Element[A] == Tuple[P, C] and _Element[B] == Tuple[P, D]:
    """Eliminate the variable using the Sylvester sign convention.

    Two nonzero constants in the elimination variable raise DOMAIN; a zero operand returns zero. Sparse output retains the eliminated axis with exponent zero.

    Parameters:
        A: The first inferred iterable type.
        B: The second inferred iterable type.
        P: The power shape: Int or a tuple of Int powers.
        C: The inferred input coefficient type.
        D: The second inferred coefficient type.

    Args:
        a: The first polynomial.
        b: The second polynomial.
        max_steps: The complete call's work allowance; defaults to UInt64.MAX.
        axis: The zero-based variable index.

    Returns:
        The Sylvester-convention resultant; a scalar for dense input or an array retaining the sparse power shape.

    Raises:
        PolyError: LIMIT on exhausted work, CAPACITY on unrepresentable sizes, DOMAIN for invalid input, or UNSUPPORTED for a documented domain restriction.
    """
    var budget = Budget(max_steps)
    return resultant[A, B, P, C, D](a, b, budget, axis=axis)


def subresultants[A: Iterable, B: Iterable, P: Copyable & Deinitable, C: Copyable & Deinitable, D: Copyable & Deinitable](a: A, b: B, mut budget: Budget, *, axis: Int = 0) raises PolyError -> List[Array[P, _Join[_Kind[C], _Kind[D]]]] where _Element[A] == Tuple[P, C] and _Element[B] == Tuple[P, D]:
    """Return the indexed subresultants, retaining zero entries.

    Parameters:
        A: The first inferred iterable type.
        B: The second inferred iterable type.
        P: The power shape: Int or a tuple of Int powers.
        C: The inferred input coefficient type.
        D: The second inferred coefficient type.

    Args:
        a: The first polynomial.
        b: The second polynomial.
        budget: The caller-owned work allowance, shared through preparation and computation.
        axis: The zero-based variable index.

    Returns:
        The list S_0 through S_(min(deg(a), deg(b))-1), including zeros; empty when the smaller degree is nonpositive.

    Raises:
        PolyError: LIMIT on exhausted work, CAPACITY on unrepresentable sizes, DOMAIN for invalid input, or UNSUPPORTED for a documented domain restriction.
    """
    comptime k = _Join[_Kind[C], _Kind[D]]
    _axis[P](axis)
    var pair = _pair[k, A, B, P, C, D](a, b, budget)
    var result = _subresultants(pair[0]._core[], pair[1]._core[], Int64(axis), budget)
    _allocation[Array[P, k]](len(result), budget)
    var arrays = List[Array[P, k]](capacity=len(result))
    for i in range(len(result)):
        arrays.append(Array[P, k](_take_sparse(result[i]), budget))
    return arrays^

def subresultants[A: Iterable, B: Iterable, P: Copyable & Deinitable, C: Copyable & Deinitable, D: Copyable & Deinitable](a: A, b: B, *, max_steps: UInt64 = UInt64.MAX, axis: Int = 0) raises PolyError -> List[Array[P, _Join[_Kind[C], _Kind[D]]]] where _Element[A] == Tuple[P, C] and _Element[B] == Tuple[P, D]:
    """Return the indexed subresultants, retaining zero entries.

    Parameters:
        A: The first inferred iterable type.
        B: The second inferred iterable type.
        P: The power shape: Int or a tuple of Int powers.
        C: The inferred input coefficient type.
        D: The second inferred coefficient type.

    Args:
        a: The first polynomial.
        b: The second polynomial.
        max_steps: The complete call's work allowance; defaults to UInt64.MAX.
        axis: The zero-based variable index.

    Returns:
        The list S_0 through S_(min(deg(a), deg(b))-1), including zeros; empty when the smaller degree is nonpositive.

    Raises:
        PolyError: LIMIT on exhausted work, CAPACITY on unrepresentable sizes, DOMAIN for invalid input, or UNSUPPORTED for a documented domain restriction.
    """
    var budget = Budget(max_steps)
    return subresultants[A, B, P, C, D](a, b, budget, axis=axis)


def _axis[P: Copyable & Deinitable](axis: Int) raises PolyError:
    if axis < 0 or axis >= _width[P]():
        raise PolyError(PolyErrorKind.DOMAIN, "axis is outside the polynomial power shape")



def _univariate[P: Copyable & Deinitable, k: Int](p: Array[P, k], mut budget: Budget) raises PolyError -> _dense.Array[k]:
    if _width[P]() != 1:
        raise PolyError(PolyErrorKind.DOMAIN, "operation requires a one-variable power shape")
    return _dense.Array[k](DensePoly[_Ring[k]].from_sparse(p._core[], budget, variable=Optional(Int64(0))), budget)


def _from_dense[P: Copyable & Deinitable, k: Int](p: _dense.Array[k], mut budget: Budget) raises PolyError -> Array[P, k]:
    return Array[P, k](_dense_sparse(p._core[], budget), budget)


def factor[I: Iterable, P: Copyable & Deinitable, C: Copyable & Deinitable](values: I, mut budget: Budget, *, seed: UInt64 = 0) raises PolyError -> Tuple[_Scalar[_Kind[C]], List[Tuple[Array[P, _Kind[C]], Int]]] where _Element[I] == Tuple[P, C]:
    """Return a scalar and irreducible factors in the inferred exact domain.

    ZZ factors are primitive with positive leading coefficient; factors over fields are monic. Zero and constants have no factors. Repeated factors retain their exact multiplicities, including inseparable prime-field inputs. Factors retain deterministic ordering. AA and QQbar support any number of active variables and preserve the full power shape. In one variable, AA factors have degree one or two and QQbar factors are linear; multivariate irreducibles can have higher degree. Multivariate algebraic factors sort by total degree, then compare term lists from greatest monomial to least, comparing each monomial before its coefficient (real component before imaginary component). Their greatest stored coefficient is one. Multivariable QQi, prime-field, AA and QQbar factorization uses budgeted dense Kronecker images and potentially exponential recombination. Algebraic inputs first remove coordinate factors, repeated factors, and coefficient content; dense storage is charged before allocation.

    Parameters:
        I: The inferred input iterable type.
        P: The power shape: Int or a tuple of Int powers.
        C: The inferred input coefficient type.

    Args:
        values: The coefficient sequence, sparse terms, or prepared array.
        budget: The caller-owned work allowance, shared through preparation and computation.
        seed: The deterministic finite-field splitting seed; defaults to zero and is ignored outside finite fields.

    Returns:
        The tuple (scalar, factors), where each entry is (irreducible polynomial, positive multiplicity) and their powered product times the scalar equals the input.

    Raises:
        PolyError: LIMIT on exhausted work, CAPACITY on unrepresentable sizes, DOMAIN for invalid input, or UNSUPPORTED for a documented domain restriction.
    """
    comptime k = _Kind[C]
    var p = _prepare[I, P, C](values, budget)
    var result = _factor_evidence(p, budget, seed)
    var factors = _take_factors[P, k](result.factors, budget)
    _charge_size(result.unit.size(), budget)
    return _unwrap[k](result.unit), factors^


def _take_factors[P: Copyable & Deinitable, k: Int, C: CoefficientRing](mut source: List[Tuple[SparsePoly[C], Int]], mut budget: Budget) raises PolyError -> List[Tuple[Array[P, k], Int]]:
    comptime assert C == _Ring[k], "factor coefficients must match the array domain"
    _allocation[Tuple[Array[P, k], Int]](len(source), budget)
    var factors = List[Tuple[Array[P, k], Int]](capacity=len(source))
    for i in range(len(source)):
        var exponent = source[i][1]
        factors.append((Array[P, k](rebind_var[SparsePoly[_Ring[k]]](_take_sparse(source[i][0])), budget), exponent))
    return factors^


def _factor_evidence[P: Copyable & Deinitable, k: Int](p: Array[P, k], mut budget: Budget, seed: UInt64) raises PolyError -> MultivariateFactorization[_Ring[k]]:
    comptime if k == 0:
        return rebind_var[MultivariateFactorization[_Ring[k]]](_factor_multivariate_integer(rebind[SparsePoly[ZZ]](p._core[]), budget))
    elif k == 1:
        return rebind_var[MultivariateFactorization[_Ring[k]]](_factor_multivariate(rebind[SparsePoly[QQ]](p._core[]), budget))
    elif k == 4 or k == 5:
        from . import _algebraic_factor
        return _algebraic_factor._factor_sparse(p._core[], budget)
    else:
        comptime if _width[P]() == 1:
            var univariate = _dense._factor_evidence[k](_univariate(p, budget), budget, seed)
            _allocation[Tuple[SparsePoly[_Ring[k]], Int]](len(univariate.factors), budget)
            var factors = List[Tuple[SparsePoly[_Ring[k]], Int]](capacity=len(univariate.factors))
            for entry in univariate.factors:
                factors.append((_dense_sparse(entry[0], budget), entry[1]))
            _charge_size(univariate.unit.size(), budget)
            return MultivariateFactorization[_Ring[k]](univariate.unit.copy(), factors^)
        elif k == 2:
            return rebind_var[MultivariateFactorization[_Ring[k]]](factor_multivariate_gaussian(rebind[SparsePoly[QQi]](p._core[]), budget))
        elif k == 3:
            return rebind_var[MultivariateFactorization[_Ring[k]]](factor_multivariate_finite_field(rebind[SparsePoly[ModInt]](p._core[]), budget, seed))

        else:
            comptime assert False, "unsupported factorization coefficient domain"

def factor[I: Iterable, P: Copyable & Deinitable, C: Copyable & Deinitable](values: I, *, max_steps: UInt64 = UInt64.MAX, seed: UInt64 = 0) raises PolyError -> Tuple[_Scalar[_Kind[C]], List[Tuple[Array[P, _Kind[C]], Int]]] where _Element[I] == Tuple[P, C]:
    """Return a scalar and irreducible factors in the inferred exact domain.

    ZZ factors are primitive with positive leading coefficient; factors over fields are monic. Zero and constants have no factors. Repeated factors retain their exact multiplicities, including inseparable prime-field inputs. Factors retain deterministic ordering. AA and QQbar support any number of active variables and preserve the full power shape. In one variable, AA factors have degree one or two and QQbar factors are linear; multivariate irreducibles can have higher degree. Multivariate algebraic factors sort by total degree, then compare term lists from greatest monomial to least, comparing each monomial before its coefficient (real component before imaginary component). Their greatest stored coefficient is one. Multivariable QQi, prime-field, AA and QQbar factorization uses budgeted dense Kronecker images and potentially exponential recombination. Algebraic inputs first remove coordinate factors, repeated factors, and coefficient content; dense storage is charged before allocation.

    Parameters:
        I: The inferred input iterable type.
        P: The power shape: Int or a tuple of Int powers.
        C: The inferred input coefficient type.

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
    return factor[I, P, C](values, budget, seed=seed)


def squarefree[I: Iterable, P: Copyable & Deinitable, C: Copyable & Deinitable](values: I, mut budget: Budget) raises PolyError -> Tuple[_Scalar[_FieldKind[_Kind[C]]], List[Tuple[Array[P, _FieldKind[_Kind[C]]], Int]]] where _Element[I] == Tuple[P, C]:
    """Return monic multiplicity blocks for a sparse polynomial in any number of variables.

    Blocks group irreducible factors with the same multiplicity and need not themselves be irreducible. ZZ inputs promote to QQ; QQ, QQi and prime fields retain their domains. Zero and constants have no blocks. Prime-field decomposition includes inverse Frobenius when derivatives vanish. All power shapes are supported; ordinary decomposition operates directly on sparse terms.

    Parameters:
        I: The inferred input iterable type.
        P: The power shape: Int or a tuple of Int powers.
        C: The inferred input coefficient type.

    Args:
        values: The coefficient sequence, sparse terms, or prepared array.
        budget: The caller-owned work allowance, shared through preparation and computation.

    Returns:
        The tuple (leading scalar, blocks), where each entry is (monic block, positive multiplicity), ordered by multiplicity.

    Raises:
        PolyError: LIMIT on exhausted work, CAPACITY on unrepresentable sizes, DOMAIN for invalid input, or UNSUPPORTED for a documented domain restriction.
    """
    comptime k = _FieldKind[_Kind[C]]
    var p = _prepare[I, P, C](values, budget)
    var ctx = _data_context[k](p.modulus(), 0, budget)
    var promoted = _promote[k](p, ctx, budget)
    comptime F = downcast[_Ring[k], CoefficientField]
    var result = squarefree_multivariate[F](rebind[SparsePoly[F]](promoted._core[]), budget)
    var factors = _take_factors[P, k](result.factors, budget)
    _charge_size(result.unit.size(), budget)
    return _unwrap[k](rebind[_Ring[k]](result.unit)), factors^

def squarefree[I: Iterable, P: Copyable & Deinitable, C: Copyable & Deinitable](values: I, *, max_steps: UInt64 = UInt64.MAX) raises PolyError -> Tuple[_Scalar[_FieldKind[_Kind[C]]], List[Tuple[Array[P, _FieldKind[_Kind[C]]], Int]]] where _Element[I] == Tuple[P, C]:
    """Return monic multiplicity blocks for a sparse polynomial in any number of variables.

    Blocks group irreducible factors with the same multiplicity and need not themselves be irreducible. ZZ inputs promote to QQ; QQ, QQi and prime fields retain their domains. Zero and constants have no blocks. Prime-field decomposition includes inverse Frobenius when derivatives vanish. All power shapes are supported; ordinary decomposition operates directly on sparse terms.

    Parameters:
        I: The inferred input iterable type.
        P: The power shape: Int or a tuple of Int powers.
        C: The inferred input coefficient type.

    Args:
        values: The coefficient sequence, sparse terms, or prepared array.
        max_steps: The complete call's work allowance; defaults to UInt64.MAX.

    Returns:
        The tuple (leading scalar, blocks), where each entry is (monic block, positive multiplicity), ordered by multiplicity.

    Raises:
        PolyError: LIMIT on exhausted work, CAPACITY on unrepresentable sizes, DOMAIN for invalid input, or UNSUPPORTED for a documented domain restriction.
    """
    var budget = Budget(max_steps)
    return squarefree[I, P, C](values, budget)


def extended_gcd[A: Iterable, B: Iterable, P: Copyable & Deinitable, C: Copyable & Deinitable, D: Copyable & Deinitable](a: A, b: B, mut budget: Budget) raises PolyError -> Tuple[Array[P, _FieldKind[_Join[_Kind[C], _Kind[D]]]], Array[P, _FieldKind[_Join[_Kind[C], _Kind[D]]]], Array[P, _FieldKind[_Join[_Kind[C], _Kind[D]]]]] where _Element[A] == Tuple[P, C] and _Element[B] == Tuple[P, D]:
    """Return univariate (g, u, v) with u*a + v*b = g; integers promote to QQ.

    Sparse input must have one axis and is converted to dense storage. For several variables, use gcd or the core certificate API.

    Parameters:
        A: The first inferred iterable type.
        B: The second inferred iterable type.
        P: The power shape: Int or a tuple of Int powers.
        C: The inferred input coefficient type.
        D: The second inferred coefficient type.

    Args:
        a: The first polynomial.
        b: The second polynomial.
        budget: The caller-owned work allowance, shared through preparation and computation.

    Returns:
        The tuple (g, u, v) with u*a + v*b = g and monic nonzero g; integers promote to QQ.

    Raises:
        PolyError: LIMIT on exhausted work, CAPACITY on unrepresentable sizes, DOMAIN for invalid input, or UNSUPPORTED for a documented domain restriction.
    """
    comptime k = _FieldKind[_Join[_Kind[C], _Kind[D]]]
    var pair = _pair[k, A, B, P, C, D](a, b, budget)
    var result = _dense._extended_gcd_arrays(_univariate(pair[0], budget), _univariate(pair[1], budget), budget)
    return _from_dense[P](result[0], budget), _from_dense[P](result[1], budget), _from_dense[P](result[2], budget)

def extended_gcd[A: Iterable, B: Iterable, P: Copyable & Deinitable, C: Copyable & Deinitable, D: Copyable & Deinitable](a: A, b: B, *, max_steps: UInt64 = UInt64.MAX) raises PolyError -> Tuple[Array[P, _FieldKind[_Join[_Kind[C], _Kind[D]]]], Array[P, _FieldKind[_Join[_Kind[C], _Kind[D]]]], Array[P, _FieldKind[_Join[_Kind[C], _Kind[D]]]]] where _Element[A] == Tuple[P, C] and _Element[B] == Tuple[P, D]:
    """Return univariate (g, u, v) with u*a + v*b = g; integers promote to QQ.

    Sparse input must have one axis and is converted to dense storage. For several variables, use gcd or the core certificate API.

    Parameters:
        A: The first inferred iterable type.
        B: The second inferred iterable type.
        P: The power shape: Int or a tuple of Int powers.
        C: The inferred input coefficient type.
        D: The second inferred coefficient type.

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
    return extended_gcd[A, B, P, C, D](a, b, budget)


def pseudo_divmod[A: Iterable, B: Iterable, P: Copyable & Deinitable, C: Copyable & Deinitable, D: Copyable & Deinitable](a: A, b: B, mut budget: Budget) raises PolyError -> Tuple[_Scalar[_Join[_Kind[C], _Kind[D]]], Array[P, _Join[_Kind[C], _Kind[D]]], Array[P, _Join[_Kind[C], _Kind[D]]]] where _Element[A] == Tuple[P, C] and _Element[B] == Tuple[P, D]:
    """Return univariate (scale, q, r) with scale*a = q*b + r in the inferred ring.

    The remainder has smaller degree than the divisor. Sparse input must have one axis and is converted to dense storage; use a finite work limit for large sparse powers.

    Parameters:
        A: The first inferred iterable type.
        B: The second inferred iterable type.
        P: The power shape: Int or a tuple of Int powers.
        C: The inferred input coefficient type.
        D: The second inferred coefficient type.

    Args:
        a: The first polynomial.
        b: The second polynomial.
        budget: The caller-owned work allowance, shared through preparation and computation.

    Returns:
        The tuple (scale, q, r), where scale = lc(b)**max(deg(a)-deg(b)+1, 0) and scale*a = q*b + r.

    Raises:
        PolyError: LIMIT on exhausted work, CAPACITY on unrepresentable sizes, DOMAIN for invalid input, or UNSUPPORTED for a documented domain restriction.
    """
    comptime k = _Join[_Kind[C], _Kind[D]]
    var pair = _pair[k, A, B, P, C, D](a, b, budget)
    var result = _dense._pseudo_divmod_arrays(_univariate(pair[0], budget), _univariate(pair[1], budget), budget)
    _charge_size(_size(result[0]), budget)
    return result[0].copy(), _from_dense[P](result[1], budget), _from_dense[P](result[2], budget)

def pseudo_divmod[A: Iterable, B: Iterable, P: Copyable & Deinitable, C: Copyable & Deinitable, D: Copyable & Deinitable](a: A, b: B, *, max_steps: UInt64 = UInt64.MAX) raises PolyError -> Tuple[_Scalar[_Join[_Kind[C], _Kind[D]]], Array[P, _Join[_Kind[C], _Kind[D]]], Array[P, _Join[_Kind[C], _Kind[D]]]] where _Element[A] == Tuple[P, C] and _Element[B] == Tuple[P, D]:
    """Return univariate (scale, q, r) with scale*a = q*b + r in the inferred ring.

    The remainder has smaller degree than the divisor. Sparse input must have one axis and is converted to dense storage; use a finite work limit for large sparse powers.

    Parameters:
        A: The first inferred iterable type.
        B: The second inferred iterable type.
        P: The power shape: Int or a tuple of Int powers.
        C: The inferred input coefficient type.
        D: The second inferred coefficient type.

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
    return pseudo_divmod[A, B, P, C, D](a, b, budget)


def compose[A: Iterable, B: Iterable, P: Copyable & Deinitable, C: Copyable & Deinitable, D: Copyable & Deinitable](a: A, b: B, mut budget: Budget) raises PolyError -> Array[P, _Join[_Kind[C], _Kind[D]]] where _Element[A] == Tuple[P, C] and _Element[B] == Tuple[P, D]:
    """Compose univariate polynomials as a(b(x)); use substitute for several axes.

    Parameters:
        A: The first inferred iterable type.
        B: The second inferred iterable type.
        P: The power shape: Int or a tuple of Int powers.
        C: The inferred input coefficient type.
        D: The second inferred coefficient type.

    Args:
        a: The first polynomial.
        b: The second polynomial.
        budget: The caller-owned work allowance, shared through preparation and computation.

    Returns:
        The outer polynomial evaluated at the inner polynomial.

    Raises:
        PolyError: LIMIT on exhausted work, CAPACITY on unrepresentable sizes, DOMAIN for invalid input, or UNSUPPORTED for a documented domain restriction.
    """
    comptime k = _Join[_Kind[C], _Kind[D]]
    var pair = _pair[k, A, B, P, C, D](a, b, budget)
    var left = _univariate(pair[0], budget)
    var right = _univariate(pair[1], budget)
    var result = _dense.Array[k](compose_dense(left._core[], right._core[], budget), budget)
    return _from_dense[P](result, budget)

def compose[A: Iterable, B: Iterable, P: Copyable & Deinitable, C: Copyable & Deinitable, D: Copyable & Deinitable](a: A, b: B, *, max_steps: UInt64 = UInt64.MAX) raises PolyError -> Array[P, _Join[_Kind[C], _Kind[D]]] where _Element[A] == Tuple[P, C] and _Element[B] == Tuple[P, D]:
    """Compose univariate polynomials as a(b(x)); use substitute for several axes.

    Parameters:
        A: The first inferred iterable type.
        B: The second inferred iterable type.
        P: The power shape: Int or a tuple of Int powers.
        C: The inferred input coefficient type.
        D: The second inferred coefficient type.

    Args:
        a: The first polynomial.
        b: The second polynomial.
        max_steps: The complete call's work allowance; defaults to UInt64.MAX.

    Returns:
        The outer polynomial evaluated at the inner polynomial.

    Raises:
        PolyError: LIMIT on exhausted work, CAPACITY on unrepresentable sizes, DOMAIN for invalid input, or UNSUPPORTED for a documented domain restriction.
    """
    var budget = Budget(max_steps)
    return compose[A, B, P, C, D](a, b, budget)



def _many[k: Int, A: Iterable, B: Iterable, P: Copyable & Deinitable, C: Copyable & Deinitable, D: Copyable & Deinitable](values: A, others: B, mut budget: Budget) raises PolyError -> Tuple[Array[P, k], List[Array[P, k]]] where _Element[A] == Tuple[P, C] and _Element[_Nested[B]] == Tuple[P, D]:
    var p = _prepare[A, P, C](values, budget)
    var modulus = p.modulus()
    var prepared = List[Array[P, _Kind[D]]]()
    var cursor = iter(others)
    while True:
        budget.charge(1)
        var raw: type_of(cursor).Element
        try:
            raw = next(cursor)
        except StopIteration:
            break
        var raw_values = rebind_var[_Nested[B]](raw^)
        var q = _prepare[_Nested[B], P, D](raw_values, budget)
        modulus = _merge_modulus(modulus, q.modulus())
        _grow(prepared, budget)
        prepared.append(q^)
    var ctx = _data_context[k](modulus, 0, budget)
    var promoted = _promote[k](p, ctx, budget)
    _allocation[Array[P, k]](len(prepared), budget)
    var result = List[Array[P, k]](capacity=len(prepared))
    for q in prepared:
        result.append(_promote[k](q, ctx, budget))
    return promoted^, result^


def divide_many[A: Iterable, B: Iterable, P: Copyable & Deinitable, C: Copyable & Deinitable, D: Copyable & Deinitable](values: A, divisors: B, mut budget: Budget, *, order: String = "lex", axes: List[Int] = List[Int]()) raises PolyError -> Tuple[List[Array[P, _FieldKind[_Join[_Kind[C], _Kind[D]]]]], Array[P, _FieldKind[_Join[_Kind[C], _Kind[D]]]]] where _Element[A] == Tuple[P, C] and _Element[_Nested[B]] == Tuple[P, D]:
    """Return ordered quotients and a remainder; integer coefficients promote to QQ.

    Sparse reduction uses the requested monomial order; lex with axis zero first is the default. Returned arrays keep canonical storage order. Changing divisor order can change quotients and remainder; this is not a Groebner-basis computation. An empty divisor collection returns no quotients and the promoted input as remainder. A zero divisor raises DOMAIN.

    Parameters:
        A: The first inferred iterable type.
        B: The second inferred iterable type.
        P: The power shape: Int or a tuple of Int powers.
        C: The inferred input coefficient type.
        D: The second inferred coefficient type.

    Args:
        values: The coefficient sequence, sparse terms, or prepared array.
        divisors: A finite iterable of polynomials of one Mojo input type, tried in the supplied order.
        budget: The caller-owned work allowance, shared through preparation and computation.
        order: One of lex, grlex, or grevlex; defaults to lex.
        axes: All axes in descending priority; empty uses tuple order.

    Returns:
        A quotient list in divisor order and a remainder, with input = sum(quotient_i * divisor_i) + remainder.

    Raises:
        PolyError: LIMIT on exhausted work, CAPACITY on unrepresentable sizes, DOMAIN for invalid input, or UNSUPPORTED for a documented domain restriction.
    """
    var monomial_order = _monomial_order[P](order, axes, budget)
    comptime k = _FieldKind[_Join[_Kind[C], _Kind[D]]]
    comptime F = downcast[_Ring[k], CoefficientField]
    var prepared = _many[k, A, B, P, C, D](values, divisors, budget)
    _allocation[SparsePoly[F]](len(prepared[1]), budget)
    var cores = List[SparsePoly[F]](capacity=len(prepared[1]))
    for q in prepared[1]:
        cores.append(rebind_var[SparsePoly[F]](q._core[].reorder(monomial_order, budget)))
    var p = prepared[0]._core[].reorder(monomial_order, budget)
    var result = divide_by_list[F](rebind[SparsePoly[F]](p), cores, budget)
    _allocation[Array[P, k]](len(result.quotients), budget)
    var quotients = List[Array[P, k]](capacity=len(result.quotients))
    for i in range(len(result.quotients)):
        quotients.append(_division_output[P, k](rebind_var[SparsePoly[_Ring[k]]](_take_sparse(result.quotients[i])), budget))
    var remainder = _division_output[P, k](rebind_var[SparsePoly[_Ring[k]]](_take_sparse(result.remainder)), budget)
    return quotients^, remainder^

def divide_many[A: Iterable, B: Iterable, P: Copyable & Deinitable, C: Copyable & Deinitable, D: Copyable & Deinitable](values: A, divisors: B, *, max_steps: UInt64 = UInt64.MAX, order: String = "lex", axes: List[Int] = List[Int]()) raises PolyError -> Tuple[List[Array[P, _FieldKind[_Join[_Kind[C], _Kind[D]]]]], Array[P, _FieldKind[_Join[_Kind[C], _Kind[D]]]]] where _Element[A] == Tuple[P, C] and _Element[_Nested[B]] == Tuple[P, D]:
    """Return ordered quotients and a remainder; integer coefficients promote to QQ.

    Sparse reduction uses the requested monomial order; lex with axis zero first is the default. Returned arrays keep canonical storage order. Changing divisor order can change quotients and remainder; this is not a Groebner-basis computation. An empty divisor collection returns no quotients and the promoted input as remainder. A zero divisor raises DOMAIN.

    Parameters:
        A: The first inferred iterable type.
        B: The second inferred iterable type.
        P: The power shape: Int or a tuple of Int powers.
        C: The inferred input coefficient type.
        D: The second inferred coefficient type.

    Args:
        values: The coefficient sequence, sparse terms, or prepared array.
        divisors: A finite iterable of polynomials of one Mojo input type, tried in the supplied order.
        max_steps: The complete call's work allowance; defaults to UInt64.MAX.
        order: One of lex, grlex, or grevlex; defaults to lex.
        axes: All axes in descending priority; empty uses tuple order.

    Returns:
        A quotient list in divisor order and a remainder, with input = sum(quotient_i * divisor_i) + remainder.

    Raises:
        PolyError: LIMIT on exhausted work, CAPACITY on unrepresentable sizes, DOMAIN for invalid input, or UNSUPPORTED for a documented domain restriction.
    """
    var budget = Budget(max_steps)
    return divide_many[A, B, P, C, D](values, divisors, budget, order=order, axes=axes)


def substitute[A: Iterable, B: Iterable, P: Copyable & Deinitable, C: Copyable & Deinitable, D: Copyable & Deinitable](values: A, replacements: B, mut budget: Budget, *, axes: List[Int] = List[Int]()) raises PolyError -> Array[P, _Join[_Kind[C], _Kind[D]]] where _Element[A] == Tuple[P, C] and _Element[_Nested[B]] == Tuple[P, D]:
    """Replace axes simultaneously; replacements retain the same power shape.

    Replacements are evaluated in the original variables; they are not recursively substituted into one another. By default there must be one replacement per axis. Explicit axes select a subset; duplicates and invalid axes raise DOMAIN.

    Parameters:
        A: The first inferred iterable type.
        B: The second inferred iterable type.
        P: The power shape: Int or a tuple of Int powers.
        C: The inferred input coefficient type.
        D: The second inferred coefficient type.

    Args:
        values: The coefficient sequence, sparse terms, or prepared array.
        replacements: A finite iterable of replacement polynomials of one Mojo input type and the same power shape.
        budget: The caller-owned work allowance, shared through preparation and computation.
        axes: Distinct zero-based axes to replace; an empty list assigns every axis in order.

    Returns:
        The simultaneously substituted polynomial in the common exact domain, with unchanged power shape.

    Raises:
        PolyError: LIMIT on exhausted work, CAPACITY on unrepresentable sizes, DOMAIN for invalid input, or UNSUPPORTED for a documented domain restriction.
    """
    comptime k = _Join[_Kind[C], _Kind[D]]
    var prepared = _many[k, A, B, P, C, D](values, replacements, budget)
    var count = len(prepared[1])
    if (len(axes) and len(axes) != count) or (not len(axes) and count != _width[P]()):
        raise PolyError(PolyErrorKind.DOMAIN, "provide one replacement per axis, or matching explicit axes")
    _allocation[Tuple[Int64, SparsePoly[_Ring[k]]]](count, budget)
    var assignments = List[Tuple[Int64, SparsePoly[_Ring[k]]]](capacity=count)
    for i in range(count):
        budget.charge(1)
        var axis = axes[i] if len(axes) else i
        _axis[P](axis)
        for j in range(i):
            budget.charge(1)
            if (axes[j] if len(axes) else j) == axis:
                raise PolyError(PolyErrorKind.DOMAIN, "substitution axes must be distinct")
        ref q = prepared[1][i]._core[]
        assignments.append((Int64(axis), q.reorder(q.order, budget)))
    return Array[P, k](_substitute_many(prepared[0]._core[], assignments, budget), budget)

def substitute[A: Iterable, B: Iterable, P: Copyable & Deinitable, C: Copyable & Deinitable, D: Copyable & Deinitable](values: A, replacements: B, *, max_steps: UInt64 = UInt64.MAX, axes: List[Int] = List[Int]()) raises PolyError -> Array[P, _Join[_Kind[C], _Kind[D]]] where _Element[A] == Tuple[P, C] and _Element[_Nested[B]] == Tuple[P, D]:
    """Replace axes simultaneously; replacements retain the same power shape.

    Replacements are evaluated in the original variables; they are not recursively substituted into one another. By default there must be one replacement per axis. Explicit axes select a subset; duplicates and invalid axes raise DOMAIN.

    Parameters:
        A: The first inferred iterable type.
        B: The second inferred iterable type.
        P: The power shape: Int or a tuple of Int powers.
        C: The inferred input coefficient type.
        D: The second inferred coefficient type.

    Args:
        values: The coefficient sequence, sparse terms, or prepared array.
        replacements: A finite iterable of replacement polynomials of one Mojo input type and the same power shape.
        max_steps: The complete call's work allowance; defaults to UInt64.MAX.
        axes: Distinct zero-based axes to replace; an empty list assigns every axis in order.

    Returns:
        The simultaneously substituted polynomial in the common exact domain, with unchanged power shape.

    Raises:
        PolyError: LIMIT on exhausted work, CAPACITY on unrepresentable sizes, DOMAIN for invalid input, or UNSUPPORTED for a documented domain restriction.
    """
    var budget = Budget(max_steps)
    return substitute[A, B, P, C, D](values, replacements, budget, axes=axes)


def _replace_axis[P: Copyable & Deinitable, k: Int](p: Array[P, k], scale: _Ring[k], shift: _Ring[k], axis: Int, mut budget: Budget) raises PolyError -> Array[P, k]:
    _axis[P](axis)
    var variable = SparsePoly[_Ring[k]].variable(Int64(axis), p._core[].order, p._core[].ring, budget)
    _charge_size(shift.size(), budget)
    var replacement = variable.scale(scale, budget).add(SparsePoly[_Ring[k]].constant(shift.copy(), p._core[].order, budget), budget)
    _allocation[Tuple[Int64, SparsePoly[_Ring[k]]]](1, budget)
    var assignments = List[Tuple[Int64, SparsePoly[_Ring[k]]]](capacity=1)
    assignments.append((Int64(axis), replacement^))
    return Array[P, k](_substitute_many(p._core[], assignments, budget), budget)


def affine_transform[I: Iterable, P: Copyable & Deinitable, C: Copyable & Deinitable, T: Copyable & Deinitable, U: Copyable & Deinitable](values: I, scale: T, shift: U, mut budget: Budget, *, axis: Int = 0) raises PolyError -> Array[P, _Join[_Kind[C], _Join[_Kind[T], _Kind[U]]]] where _Element[I] == Tuple[P, C]:
    """Substitute scale*x + shift along one axis, retaining the power shape.

    Parameters:
        I: The inferred input iterable type.
        P: The power shape: Int or a tuple of Int powers.
        C: The inferred input coefficient type.
        T: The sequence's exact scalar type.
        U: The inferred type of the second exact scalar.

    Args:
        values: The coefficient sequence, sparse terms, or prepared array.
        scale: The exact multiplier of the selected variable.
        shift: The exact constant added to the scaled variable.
        budget: The caller-owned work allowance, shared through preparation and computation.
        axis: The zero-based variable index.

    Returns:
        The polynomial with the selected variable replaced by scale*x + shift.

    Raises:
        PolyError: LIMIT on exhausted work, CAPACITY on unrepresentable sizes, DOMAIN for invalid input, or UNSUPPORTED for a documented domain restriction.
    """
    comptime k = _Join[_Kind[C], _Join[_Kind[T], _Kind[U]]]
    _axis[P](axis)
    var p = _prepare[I, P, C](values, budget)
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
    return _replace_axis(promoted, c_scale, c_shift, axis, budget)

def affine_transform[I: Iterable, P: Copyable & Deinitable, C: Copyable & Deinitable, T: Copyable & Deinitable, U: Copyable & Deinitable](values: I, scale: T, shift: U, *, max_steps: UInt64 = UInt64.MAX, axis: Int = 0) raises PolyError -> Array[P, _Join[_Kind[C], _Join[_Kind[T], _Kind[U]]]] where _Element[I] == Tuple[P, C]:
    """Substitute scale*x + shift along one axis, retaining the power shape.

    Parameters:
        I: The inferred input iterable type.
        P: The power shape: Int or a tuple of Int powers.
        C: The inferred input coefficient type.
        T: The sequence's exact scalar type.
        U: The inferred type of the second exact scalar.

    Args:
        values: The coefficient sequence, sparse terms, or prepared array.
        scale: The exact multiplier of the selected variable.
        shift: The exact constant added to the scaled variable.
        max_steps: The complete call's work allowance; defaults to UInt64.MAX.
        axis: The zero-based variable index.

    Returns:
        The polynomial with the selected variable replaced by scale*x + shift.

    Raises:
        PolyError: LIMIT on exhausted work, CAPACITY on unrepresentable sizes, DOMAIN for invalid input, or UNSUPPORTED for a documented domain restriction.
    """
    var budget = Budget(max_steps)
    return affine_transform[I, P, C, T, U](values, scale, shift, budget, axis=axis)


def taylor_shift[I: Iterable, P: Copyable & Deinitable, C: Copyable & Deinitable, T: Copyable & Deinitable](values: I, point: T, mut budget: Budget, *, axis: Int = 0) raises PolyError -> Array[P, _Join[_Kind[C], _Kind[T]]] where _Element[I] == Tuple[P, C]:
    """Shift one axis by an exact scalar, retaining the power shape.

    Parameters:
        I: The inferred input iterable type.
        P: The power shape: Int or a tuple of Int powers.
        C: The inferred input coefficient type.
        T: The sequence's exact scalar type.

    Args:
        values: The coefficient sequence, sparse terms, or prepared array.
        point: An exact scalar for one variable, or a coordinate tuple in variable order.
        budget: The caller-owned work allowance, shared through preparation and computation.
        axis: The zero-based variable index.

    Returns:
        The polynomial with the selected variable replaced by x + point.

    Raises:
        PolyError: LIMIT on exhausted work, CAPACITY on unrepresentable sizes, DOMAIN for invalid input, or UNSUPPORTED for a documented domain restriction.
    """
    comptime k = _Join[_Kind[C], _Kind[T]]
    _axis[P](axis)
    var p = _prepare[I, P, C](values, budget)
    var context = _Context[k]()
    if p.modulus():
        context.observe(p.modulus(), budget)
    comptime if T == ModInt:
        context.observe(rebind[ModInt](point).modulus, budget)
    var ctx = context.get()
    var promoted = _promote[k](p, ctx, budget)
    var c_point = _wrap[k](_convert[k](point, ctx, budget))
    return _replace_axis(promoted, _Ring[k].one(ctx), c_point, axis, budget)

def taylor_shift[I: Iterable, P: Copyable & Deinitable, C: Copyable & Deinitable, T: Copyable & Deinitable](values: I, point: T, *, max_steps: UInt64 = UInt64.MAX, axis: Int = 0) raises PolyError -> Array[P, _Join[_Kind[C], _Kind[T]]] where _Element[I] == Tuple[P, C]:
    """Shift one axis by an exact scalar, retaining the power shape.

    Parameters:
        I: The inferred input iterable type.
        P: The power shape: Int or a tuple of Int powers.
        C: The inferred input coefficient type.
        T: The sequence's exact scalar type.

    Args:
        values: The coefficient sequence, sparse terms, or prepared array.
        point: An exact scalar for one variable, or a coordinate tuple in variable order.
        max_steps: The complete call's work allowance; defaults to UInt64.MAX.
        axis: The zero-based variable index.

    Returns:
        The polynomial with the selected variable replaced by x + point.

    Raises:
        PolyError: LIMIT on exhausted work, CAPACITY on unrepresentable sizes, DOMAIN for invalid input, or UNSUPPORTED for a documented domain restriction.
    """
    var budget = Budget(max_steps)
    return taylor_shift[I, P, C, T](values, point, budget, axis=axis)


def definite_integral[I: Iterable, P: Copyable & Deinitable, C: Copyable & Deinitable, T: Copyable & Deinitable, U: Copyable & Deinitable](values: I, low: T, high: U, mut budget: Budget, *, axis: Int = 0) raises PolyError -> Array[P, _FieldKind[_Join[_Kind[C], _Join[_Kind[T], _Kind[U]]]]] where _Element[I] == Tuple[P, C]:
    """Integrate out one axis between exact scalar endpoints; integers promote to QQ.

    Integer coefficients and endpoints promote to QQ. In a prime field, a nonzero term needing a noninvertible antiderivative denominator raises DOMAIN. Sparse integration retains all axes, with exponent zero on the integrated axis.

    Parameters:
        I: The inferred input iterable type.
        P: The power shape: Int or a tuple of Int powers.
        C: The inferred input coefficient type.
        T: The sequence's exact scalar type.
        U: The inferred type of the second exact scalar.

    Args:
        values: The coefficient sequence, sparse terms, or prepared array.
        low: The exact lower integration endpoint.
        high: The exact upper integration endpoint.
        budget: The caller-owned work allowance, shared through preparation and computation.
        axis: The zero-based variable index.

    Returns:
        The exact endpoint difference of an antiderivative; a scalar for dense input or an array retaining the sparse power shape.

    Raises:
        PolyError: LIMIT on exhausted work, CAPACITY on unrepresentable sizes, DOMAIN for invalid input, or UNSUPPORTED for a documented domain restriction.
    """
    comptime k = _FieldKind[_Join[_Kind[C], _Join[_Kind[T], _Kind[U]]]]
    _axis[P](axis)
    var p = _prepare[I, P, C](values, budget)
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
    var integrated = Array[P, k](integrate_sparse(promoted._core[], Int64(axis), budget), budget)
    var upper = _replace_axis(integrated, _Ring[k].zero(ctx), c_high, axis, budget)
    var lower = _replace_axis(integrated, _Ring[k].zero(ctx), c_low, axis, budget)
    return Array[P, k](upper._core[].sub(lower._core[], budget), budget)

def definite_integral[I: Iterable, P: Copyable & Deinitable, C: Copyable & Deinitable, T: Copyable & Deinitable, U: Copyable & Deinitable](values: I, low: T, high: U, *, max_steps: UInt64 = UInt64.MAX, axis: Int = 0) raises PolyError -> Array[P, _FieldKind[_Join[_Kind[C], _Join[_Kind[T], _Kind[U]]]]] where _Element[I] == Tuple[P, C]:
    """Integrate out one axis between exact scalar endpoints; integers promote to QQ.

    Integer coefficients and endpoints promote to QQ. In a prime field, a nonzero term needing a noninvertible antiderivative denominator raises DOMAIN. Sparse integration retains all axes, with exponent zero on the integrated axis.

    Parameters:
        I: The inferred input iterable type.
        P: The power shape: Int or a tuple of Int powers.
        C: The inferred input coefficient type.
        T: The sequence's exact scalar type.
        U: The inferred type of the second exact scalar.

    Args:
        values: The coefficient sequence, sparse terms, or prepared array.
        low: The exact lower integration endpoint.
        high: The exact upper integration endpoint.
        max_steps: The complete call's work allowance; defaults to UInt64.MAX.
        axis: The zero-based variable index.

    Returns:
        The exact endpoint difference of an antiderivative; a scalar for dense input or an array retaining the sparse power shape.

    Raises:
        PolyError: LIMIT on exhausted work, CAPACITY on unrepresentable sizes, DOMAIN for invalid input, or UNSUPPORTED for a documented domain restriction.
    """
    var budget = Budget(max_steps)
    return definite_integral[I, P, C, T, U](values, low, high, budget, axis=axis)

from . import roots as _roots
from . import algebraic as _algebraic
from polynomials import NumericOptions, RealRootSink, ComplexRootSink, RootStreamReceipt, RealRootStreamChecker, ComplexRootStreamChecker


def real_roots[I: Iterable, P: Copyable & Deinitable, C: Copyable & Deinitable](values: I, mut budget: Budget) raises PolyError -> _roots.ExactRoots where _Element[I] == Tuple[P, C]:
    """Find every distinct real root of a univariate sparse polynomial.

    Parameters:
        I: The inferred input type.
        P: The inferred power shape.
        C: The inferred input type.

    Args:
        values: Univariate integer or rational sparse terms, or a prepared array.
        budget: The shared work allowance for preparation and computation.

    Returns:
        The computed result, with its evidence retained.

    Raises:
        PolyError: DOMAIN for incompatible input, UNSUPPORTED for an unavailable operation, or LIMIT/CAPACITY on resource limits.
    """
    return _dense.real_roots(_univariate(_prepare[I, P, C](values, budget), budget), budget)


def real_roots[I: Iterable, P: Copyable & Deinitable, C: Copyable & Deinitable](values: I, *, max_steps: UInt64 = UInt64.MAX) raises PolyError -> _roots.ExactRoots where _Element[I] == Tuple[P, C]:
    """Find every distinct real root of a univariate sparse polynomial.

    Parameters:
        I: The inferred input type.
        P: The inferred power shape.
        C: The inferred input type.

    Args:
        values: Univariate integer or rational sparse terms, or a prepared array.
        max_steps: The complete call's work allowance; defaults to UInt64.MAX.

    Returns:
        The computed result, with its evidence retained.

    Raises:
        PolyError: DOMAIN for incompatible input, UNSUPPORTED for an unavailable operation, or LIMIT/CAPACITY on resource limits.
    """
    var budget = Budget(max_steps)
    return real_roots[I, P, C](values, budget)


def count_roots[I: Iterable, P: Copyable & Deinitable, C: Copyable & Deinitable, L: Copyable & Deinitable, H: Copyable & Deinitable](values: I, low: L, high: H, mut budget: Budget) raises PolyError -> _dense._Count[C, L, H] where _Element[I] == Tuple[P, C]:
    """Count or select roots between exact endpoints.

    Parameters:
        I: The inferred input type.
        P: The inferred power shape.
        C: The inferred input type.
        L: The inferred input type.
        H: The inferred input type.

    Args:
        values: Univariate integer or rational terms.
        low: The lower exact endpoint.
        high: The upper exact endpoint.
        budget: The shared work allowance for preparation and computation.

    Returns:
        The computed result, with its evidence retained.

    Raises:
        PolyError: DOMAIN for incompatible input, UNSUPPORTED for an unavailable operation, or LIMIT/CAPACITY on resource limits.
    """
    return rebind_var[_dense._Count[C, L, H]](_dense.count_roots(_univariate(_prepare[I, P, C](values, budget), budget), low, high, budget))


def count_roots[I: Iterable, P: Copyable & Deinitable, C: Copyable & Deinitable, L: Copyable & Deinitable, H: Copyable & Deinitable](values: I, low: L, high: H, *, max_steps: UInt64 = UInt64.MAX) raises PolyError -> _dense._Count[C, L, H] where _Element[I] == Tuple[P, C]:
    """Count or select roots between exact endpoints.

    Parameters:
        I: The inferred input type.
        P: The inferred power shape.
        C: The inferred input type.
        L: The inferred input type.
        H: The inferred input type.

    Args:
        values: Univariate integer or rational terms.
        low: The lower exact endpoint.
        high: The upper exact endpoint.
        max_steps: The complete call's work allowance; defaults to UInt64.MAX.

    Returns:
        The computed result, with its evidence retained.

    Raises:
        PolyError: DOMAIN for incompatible input, UNSUPPORTED for an unavailable operation, or LIMIT/CAPACITY on resource limits.
    """
    var budget = Budget(max_steps)
    return count_roots[I, P, C, L, H](values, low, high, budget)


def root_between[I: Iterable, P: Copyable & Deinitable, C: Copyable & Deinitable, L: Copyable & Deinitable, H: Copyable & Deinitable](values: I, low: L, high: H, mut budget: Budget) raises PolyError -> _algebraic.Real where _Element[I] == Tuple[P, C]:
    """Count or select roots between exact endpoints.

    Parameters:
        I: The inferred input type.
        P: The inferred power shape.
        C: The inferred input type.
        L: The inferred input type.
        H: The inferred input type.

    Args:
        values: Univariate integer or rational terms.
        low: The lower exact endpoint.
        high: The upper exact endpoint.
        budget: The shared work allowance for preparation and computation.

    Returns:
        The computed result, with its evidence retained.

    Raises:
        PolyError: DOMAIN for incompatible input, UNSUPPORTED for an unavailable operation, or LIMIT/CAPACITY on resource limits.
    """
    return _dense.root_between(_univariate(_prepare[I, P, C](values, budget), budget), low, high, budget)


def root_between[I: Iterable, P: Copyable & Deinitable, C: Copyable & Deinitable, L: Copyable & Deinitable, H: Copyable & Deinitable](values: I, low: L, high: H, *, max_steps: UInt64 = UInt64.MAX) raises PolyError -> _algebraic.Real where _Element[I] == Tuple[P, C]:
    """Count or select roots between exact endpoints.

    Parameters:
        I: The inferred input type.
        P: The inferred power shape.
        C: The inferred input type.
        L: The inferred input type.
        H: The inferred input type.

    Args:
        values: Univariate integer or rational terms.
        low: The lower exact endpoint.
        high: The upper exact endpoint.
        max_steps: The complete call's work allowance; defaults to UInt64.MAX.

    Returns:
        The computed result, with its evidence retained.

    Raises:
        PolyError: DOMAIN for incompatible input, UNSUPPORTED for an unavailable operation, or LIMIT/CAPACITY on resource limits.
    """
    var budget = Budget(max_steps)
    return root_between[I, P, C, L, H](values, low, high, budget)


def real_root_cover[I: Iterable, P: Copyable & Deinitable, C: Copyable & Deinitable](values: I, mut budget: Budget, *, options: NumericOptions = NumericOptions(), complete_only: Bool = False) raises PolyError -> _dense._RealCover[_Kind[C]] where _Element[I] == Tuple[P, C]:
    """Prepare a real root cover.

    The sparse polynomial is converted to dense storage under the shared budget.
    Only one-variable power shapes are accepted.

    Parameters:
        I: The inferred input type.
        P: The inferred power shape.
        C: The inferred input type.

    Args:
        values: A univariate sparse polynomial with exact coefficients.
        budget: The shared work allowance for preparation and computation.
        options: The precision and root-cover settings.
        complete_only: Raise unless all requested properties succeed.

    Returns:
        The computed result, with its evidence retained.

    Raises:
        PolyError: DOMAIN for incompatible input, UNSUPPORTED for an unavailable operation, or LIMIT/CAPACITY on resource limits.
    """
    comptime assert _Kind[_Element[_dense.Array[_Kind[C]]]] >= 0, "root covers require exact coefficients"
    return rebind_var[_dense._RealCover[_Kind[C]]](_dense.real_root_cover(_univariate(_prepare[I, P, C](values, budget), budget), budget, options=options, complete_only=complete_only))


def real_root_cover[I: Iterable, P: Copyable & Deinitable, C: Copyable & Deinitable](values: I, *, max_steps: UInt64 = UInt64.MAX, options: NumericOptions = NumericOptions(), complete_only: Bool = False) raises PolyError -> _dense._RealCover[_Kind[C]] where _Element[I] == Tuple[P, C]:
    """Prepare a real root cover.

    The sparse polynomial is converted to dense storage under the shared budget.
    Only one-variable power shapes are accepted.

    Parameters:
        I: The inferred input type.
        P: The inferred power shape.
        C: The inferred input type.

    Args:
        values: A univariate sparse polynomial with exact coefficients.
        max_steps: The complete call's work allowance; defaults to UInt64.MAX.
        options: The precision and root-cover settings.
        complete_only: Raise unless all requested properties succeed.

    Returns:
        The computed result, with its evidence retained.

    Raises:
        PolyError: DOMAIN for incompatible input, UNSUPPORTED for an unavailable operation, or LIMIT/CAPACITY on resource limits.
    """
    var budget = Budget(max_steps)
    return rebind_var[_dense._RealCover[_Kind[C]]](real_root_cover[I, P, C](values, budget, options=options, complete_only=complete_only))


def real_root_cover_to[I: Iterable, P: Copyable & Deinitable, C: Copyable & Deinitable, S: RealRootSink](values: I, mut sink: S, mut budget: Budget, *, options: NumericOptions = NumericOptions(), complete_only: Bool = False) raises PolyError -> RootStreamReceipt where _Element[I] == Tuple[P, C]:
    """Prepare a real root cover stream.

    The sparse polynomial is converted to dense storage under the shared budget.
    Only one-variable power shapes are accepted.

    Parameters:
        I: The inferred input type.
        P: The inferred power shape.
        C: The inferred input type.
        S: The inferred input type.

    Args:
        values: A univariate sparse polynomial with exact coefficients.
        sink: The incremental witness consumer.
        budget: The shared work allowance for preparation and computation.
        options: The precision and root-cover settings.
        complete_only: Raise unless all requested properties succeed.

    Returns:
        The computed result, with its evidence retained.

    Raises:
        PolyError: DOMAIN for incompatible input, UNSUPPORTED for an unavailable operation, or LIMIT/CAPACITY on resource limits.
    """
    comptime assert _Kind[_Element[_dense.Array[_Kind[C]]]] >= 0, "root covers require exact coefficients"
    return _dense.real_root_cover_to(_univariate(_prepare[I, P, C](values, budget), budget), sink, budget, options=options, complete_only=complete_only)


def real_root_cover_to[I: Iterable, P: Copyable & Deinitable, C: Copyable & Deinitable, S: RealRootSink](values: I, mut sink: S, *, max_steps: UInt64 = UInt64.MAX, options: NumericOptions = NumericOptions(), complete_only: Bool = False) raises PolyError -> RootStreamReceipt where _Element[I] == Tuple[P, C]:
    """Prepare a real root cover stream.

    The sparse polynomial is converted to dense storage under the shared budget.
    Only one-variable power shapes are accepted.

    Parameters:
        I: The inferred input type.
        P: The inferred power shape.
        C: The inferred input type.
        S: The inferred input type.

    Args:
        values: A univariate sparse polynomial with exact coefficients.
        sink: The incremental witness consumer.
        max_steps: The complete call's work allowance; defaults to UInt64.MAX.
        options: The precision and root-cover settings.
        complete_only: Raise unless all requested properties succeed.

    Returns:
        The computed result, with its evidence retained.

    Raises:
        PolyError: DOMAIN for incompatible input, UNSUPPORTED for an unavailable operation, or LIMIT/CAPACITY on resource limits.
    """
    var budget = Budget(max_steps)
    return real_root_cover_to[I, P, C, S](values, sink, budget, options=options, complete_only=complete_only)


def real_root_checker[I: Iterable, P: Copyable & Deinitable, C: Copyable & Deinitable](values: I, mut budget: Budget, *, options: NumericOptions = NumericOptions()) raises PolyError -> _dense._RealChecker[_Kind[C]] where _Element[I] == Tuple[P, C]:
    """Prepare a real root stream checker.

    The sparse polynomial is converted to dense storage under the shared budget.
    Only one-variable power shapes are accepted.

    Parameters:
        I: The inferred input type.
        P: The inferred power shape.
        C: The inferred input type.

    Args:
        values: A univariate sparse polynomial with exact coefficients.
        budget: The shared work allowance for preparation and computation.
        options: The precision and root-cover settings.

    Returns:
        The computed result, with its evidence retained.

    Raises:
        PolyError: DOMAIN for incompatible input, UNSUPPORTED for an unavailable operation, or LIMIT/CAPACITY on resource limits.
    """
    comptime assert _Kind[_Element[_dense.Array[_Kind[C]]]] >= 0, "root covers require exact coefficients"
    return rebind_var[_dense._RealChecker[_Kind[C]]](_dense.real_root_checker(_univariate(_prepare[I, P, C](values, budget), budget), budget, options=options))


def real_root_checker[I: Iterable, P: Copyable & Deinitable, C: Copyable & Deinitable](values: I, *, max_steps: UInt64 = UInt64.MAX, options: NumericOptions = NumericOptions()) raises PolyError -> _dense._RealChecker[_Kind[C]] where _Element[I] == Tuple[P, C]:
    """Prepare a real root stream checker.

    The sparse polynomial is converted to dense storage under the shared budget.
    Only one-variable power shapes are accepted.

    Parameters:
        I: The inferred input type.
        P: The inferred power shape.
        C: The inferred input type.

    Args:
        values: A univariate sparse polynomial with exact coefficients.
        max_steps: The complete call's work allowance; defaults to UInt64.MAX.
        options: The precision and root-cover settings.

    Returns:
        The computed result, with its evidence retained.

    Raises:
        PolyError: DOMAIN for incompatible input, UNSUPPORTED for an unavailable operation, or LIMIT/CAPACITY on resource limits.
    """
    var budget = Budget(max_steps)
    return rebind_var[_dense._RealChecker[_Kind[C]]](real_root_checker[I, P, C](values, budget, options=options))


def complex_root_cover[I: Iterable, P: Copyable & Deinitable, C: Copyable & Deinitable](values: I, mut budget: Budget, *, options: NumericOptions = NumericOptions(), complete_only: Bool = False) raises PolyError -> _dense._ComplexCover[_Kind[C]] where _Element[I] == Tuple[P, C]:
    """Prepare a complex root cover.

    The sparse polynomial is converted to dense storage under the shared budget.
    Only one-variable power shapes are accepted.

    Parameters:
        I: The inferred input type.
        P: The inferred power shape.
        C: The inferred input type.

    Args:
        values: A univariate sparse polynomial with exact coefficients.
        budget: The shared work allowance for preparation and computation.
        options: The precision and root-cover settings.
        complete_only: Raise unless all requested properties succeed.

    Returns:
        The computed result, with its evidence retained.

    Raises:
        PolyError: DOMAIN for incompatible input, UNSUPPORTED for an unavailable operation, or LIMIT/CAPACITY on resource limits.
    """
    comptime assert _Kind[_Element[_dense.Array[_Kind[C]]]] >= 0, "root covers require exact coefficients"
    return rebind_var[_dense._ComplexCover[_Kind[C]]](rebind_var[_dense._ComplexCover[_Kind[C]]](_dense.complex_root_cover(_univariate(_prepare[I, P, C](values, budget), budget), budget, options=options, complete_only=complete_only)))


def complex_root_cover[I: Iterable, P: Copyable & Deinitable, C: Copyable & Deinitable](values: I, *, max_steps: UInt64 = UInt64.MAX, options: NumericOptions = NumericOptions(), complete_only: Bool = False) raises PolyError -> _dense._ComplexCover[_Kind[C]] where _Element[I] == Tuple[P, C]:
    """Prepare a complex root cover.

    The sparse polynomial is converted to dense storage under the shared budget.
    Only one-variable power shapes are accepted.

    Parameters:
        I: The inferred input type.
        P: The inferred power shape.
        C: The inferred input type.

    Args:
        values: A univariate sparse polynomial with exact coefficients.
        max_steps: The complete call's work allowance; defaults to UInt64.MAX.
        options: The precision and root-cover settings.
        complete_only: Raise unless all requested properties succeed.

    Returns:
        The computed result, with its evidence retained.

    Raises:
        PolyError: DOMAIN for incompatible input, UNSUPPORTED for an unavailable operation, or LIMIT/CAPACITY on resource limits.
    """
    var budget = Budget(max_steps)
    return rebind_var[_dense._ComplexCover[_Kind[C]]](complex_root_cover[I, P, C](values, budget, options=options, complete_only=complete_only))


def complex_root_cover_to[I: Iterable, P: Copyable & Deinitable, C: Copyable & Deinitable, S: ComplexRootSink](values: I, mut sink: S, mut budget: Budget, *, options: NumericOptions = NumericOptions(), complete_only: Bool = False) raises PolyError -> RootStreamReceipt where _Element[I] == Tuple[P, C]:
    """Prepare a complex root cover stream.

    The sparse polynomial is converted to dense storage under the shared budget.
    Only one-variable power shapes are accepted.

    Parameters:
        I: The inferred input type.
        P: The inferred power shape.
        C: The inferred input type.
        S: The inferred input type.

    Args:
        values: A univariate sparse polynomial with exact coefficients.
        sink: The incremental witness consumer.
        budget: The shared work allowance for preparation and computation.
        options: The precision and root-cover settings.
        complete_only: Raise unless all requested properties succeed.

    Returns:
        The computed result, with its evidence retained.

    Raises:
        PolyError: DOMAIN for incompatible input, UNSUPPORTED for an unavailable operation, or LIMIT/CAPACITY on resource limits.
    """
    comptime assert _Kind[_Element[_dense.Array[_Kind[C]]]] >= 0, "root covers require exact coefficients"
    return _dense.complex_root_cover_to(_univariate(_prepare[I, P, C](values, budget), budget), sink, budget, options=options, complete_only=complete_only)


def complex_root_cover_to[I: Iterable, P: Copyable & Deinitable, C: Copyable & Deinitable, S: ComplexRootSink](values: I, mut sink: S, *, max_steps: UInt64 = UInt64.MAX, options: NumericOptions = NumericOptions(), complete_only: Bool = False) raises PolyError -> RootStreamReceipt where _Element[I] == Tuple[P, C]:
    """Prepare a complex root cover stream.

    The sparse polynomial is converted to dense storage under the shared budget.
    Only one-variable power shapes are accepted.

    Parameters:
        I: The inferred input type.
        P: The inferred power shape.
        C: The inferred input type.
        S: The inferred input type.

    Args:
        values: A univariate sparse polynomial with exact coefficients.
        sink: The incremental witness consumer.
        max_steps: The complete call's work allowance; defaults to UInt64.MAX.
        options: The precision and root-cover settings.
        complete_only: Raise unless all requested properties succeed.

    Returns:
        The computed result, with its evidence retained.

    Raises:
        PolyError: DOMAIN for incompatible input, UNSUPPORTED for an unavailable operation, or LIMIT/CAPACITY on resource limits.
    """
    var budget = Budget(max_steps)
    return complex_root_cover_to[I, P, C, S](values, sink, budget, options=options, complete_only=complete_only)


def complex_root_checker[I: Iterable, P: Copyable & Deinitable, C: Copyable & Deinitable](values: I, mut budget: Budget, *, options: NumericOptions = NumericOptions()) raises PolyError -> _dense._ComplexChecker[_Kind[C]] where _Element[I] == Tuple[P, C]:
    """Prepare a complex root stream checker.

    The sparse polynomial is converted to dense storage under the shared budget.
    Only one-variable power shapes are accepted.

    Parameters:
        I: The inferred input type.
        P: The inferred power shape.
        C: The inferred input type.

    Args:
        values: A univariate sparse polynomial with exact coefficients.
        budget: The shared work allowance for preparation and computation.
        options: The precision and root-cover settings.

    Returns:
        The computed result, with its evidence retained.

    Raises:
        PolyError: DOMAIN for incompatible input, UNSUPPORTED for an unavailable operation, or LIMIT/CAPACITY on resource limits.
    """
    comptime assert _Kind[_Element[_dense.Array[_Kind[C]]]] >= 0, "root covers require exact coefficients"
    return rebind_var[_dense._ComplexChecker[_Kind[C]]](_dense.complex_root_checker(_univariate(_prepare[I, P, C](values, budget), budget), budget, options=options))


def complex_root_checker[I: Iterable, P: Copyable & Deinitable, C: Copyable & Deinitable](values: I, *, max_steps: UInt64 = UInt64.MAX, options: NumericOptions = NumericOptions()) raises PolyError -> _dense._ComplexChecker[_Kind[C]] where _Element[I] == Tuple[P, C]:
    """Prepare a complex root stream checker.

    The sparse polynomial is converted to dense storage under the shared budget.
    Only one-variable power shapes are accepted.

    Parameters:
        I: The inferred input type.
        P: The inferred power shape.
        C: The inferred input type.

    Args:
        values: A univariate sparse polynomial with exact coefficients.
        max_steps: The complete call's work allowance; defaults to UInt64.MAX.
        options: The precision and root-cover settings.

    Returns:
        The computed result, with its evidence retained.

    Raises:
        PolyError: DOMAIN for incompatible input, UNSUPPORTED for an unavailable operation, or LIMIT/CAPACITY on resource limits.
    """
    var budget = Budget(max_steps)
    return rebind_var[_dense._ComplexChecker[_Kind[C]]](complex_root_checker[I, P, C](values, budget, options=options))

from polynomials import GroebnerBasis as _CoreBasis, groebner as _groebner, reduce as _reduce, MembershipCertificate, check_membership as _check_membership

comptime _Field[k: Int] = downcast[_Ring[k], CoefficientField]


def _axes[P: Copyable & Deinitable](requested: List[Int], mut budget: Budget) raises PolyError -> List[Int64]:
    var width = _width[P]()
    if len(requested) and len(requested) != width:
        raise PolyError(PolyErrorKind.DOMAIN, "axis order must be a permutation of all polynomial axes")
    _allocation[Int64](width, budget)
    var result = List[Int64](capacity=width)
    for i in range(width):
        budget.charge(1)
        var axis = requested[i] if len(requested) else i
        _axis[P](axis)
        for previous in result:
            budget.charge(1)
            if previous == Int64(axis):
                raise PolyError(PolyErrorKind.DOMAIN, "axis order contains a duplicate")
        result.append(Int64(axis))
    return result^


def _system[k: Int, I: Iterable, P: Copyable & Deinitable, C: Copyable & Deinitable](values: I, mut budget: Budget) raises PolyError -> Tuple[List[Array[P, k]], _Ring[k].Context] where _Element[_Nested[I]] == Tuple[P, C]:
    var prepared = List[Array[P, _Kind[C]]]()
    var modulus = UInt64(0)
    var cursor = iter(values)
    while True:
        budget.charge(1)
        var raw: type_of(cursor).Element
        try:
            raw = next(cursor)
        except StopIteration:
            break
        var row = rebind_var[_Nested[I]](raw^)
        var p = _prepare[_Nested[I], P, C](row, budget)
        modulus = _merge_modulus(modulus, p.modulus())
        _grow(prepared, budget)
        prepared.append(p^)
    var ctx = _data_context[k](modulus, 0, budget)
    _allocation[Array[P, k]](len(prepared), budget)
    var promoted = List[Array[P, k]](capacity=len(prepared))
    for p in prepared:
        promoted.append(_promote[k](p, ctx, budget))
    return promoted^, ctx^


@fieldwise_init
struct _BasisData[k: Int](Copyable, Movable):
    var generators: List[SparsePoly[_Field[Self.k]]]
    var basis: _CoreBasis[_Field[Self.k]]
    var context: _Ring[Self.k].Context


@fieldwise_init
struct Basis[P: Copyable & Deinitable, k: Int](Copyable, Movable, Iterable, Sized):
    """A reusable reduced monic basis with original generator order retained.

    Its polynomials use the usual canonical array storage. The retained core
    basis keeps the chosen computational monomial order. Copies share storage.

    Parameters:
        P: The sparse power shape.
        k: The inferred coefficient field kind.
    """
    var _data: ArcPointer[_BasisData[Self.k]]
    var _values: Values[Array[Self.P, Self.k], Self.k]
    comptime IteratorType[iterable_mut: Bool, //, iterable_origin: Origin[mut=iterable_mut]]: Iterator = _BasisIterator[Self.P, Self.k, ImmOrigin(iterable_origin)]
    """An iterator borrowing the prepared basis.

    Parameters:
        iterable_mut: Whether the source origin is mutable.
        iterable_origin: The source lifetime.
    """

    def __iter__(ref self) -> Self.IteratorType[origin_of(self)]:
        """Iterate over basis polynomials in deterministic basis order.

        Returns:
            A borrowing iterator returning shared polynomial arrays.
        """
        return _BasisIterator[Self.P, Self.k, ImmOrigin(origin_of(self))](Pointer(to=self).as_imm(), 0)

    def __len__(self) -> Int:
        """Return the number of basis polynomials.

        Returns:
            Zero for the zero ideal.
        """
        return len(self._values)

    def __getitem__(self, index: Int) -> Array[Self.P, Self.k]:
        """Return a basis polynomial at a valid index.

        Args:
            index: The zero-based index in basis order.

        Returns:
            An immutable array sharing its canonical term storage.
        """
        return self._values[index]

    def evidence(self) -> ref[ImmOrigin(origin_of(self._data[].basis))] _CoreBasis[_Field[Self.k]]:
        """Borrow the basis and optional original-generator cofactor rows.

        Returns:
            Immutable core basis data in the requested monomial order.
        """
        return self._data[].basis


@fieldwise_init
struct _BasisIterator[P: Copyable & Deinitable, k: Int, origin: ImmOrigin](Iterator):
    comptime Element = Array[Self.P, Self.k]
    var source: Pointer[Basis[Self.P, Self.k], Self.origin]
    var position: Int

    def __next__(mut self) raises StopIteration -> Self.Element:
        if self.position == len(self.source[]):
            raise StopIteration()
        var result = self.source[][self.position]
        self.position += 1
        return result^


def _monomial_order[P: Copyable & Deinitable](order: String, axes: List[Int], mut budget: Budget) raises PolyError -> MonomialOrder:
    var kind = MonomialOrder.GREVLEX
    if order == "lex":
        kind = MonomialOrder.LEX
    elif order == "grlex":
        kind = MonomialOrder.GRLEX
    elif order != "grevlex":
        raise PolyError(PolyErrorKind.DOMAIN, "order must be lex, grlex, or grevlex")
    return MonomialOrder(kind, _axes[P](axes, budget), budget)


def _basis[P: Copyable & Deinitable, k: Int](prepared: List[Array[P, k]], ctx: _Ring[k].Context, order: String, axes: List[Int], witnesses: Bool, certify: Bool, mut budget: Budget) raises PolyError -> Basis[P, k]:
    var monomial_order = _monomial_order[P](order, axes, budget)
    _allocation[SparsePoly[_Field[k]]](len(prepared), budget)
    var generators = List[SparsePoly[_Field[k]]](capacity=len(prepared))
    for p in prepared:
        generators.append(rebind_var[SparsePoly[_Field[k]]](p._core[].reorder(monomial_order, budget)))
    var result = _groebner(generators, monomial_order, budget, track_cofactors=witnesses, certify=certify)
    _allocation[Array[P, k]](len(result.basis), budget)
    var values = List[Array[P, k]](capacity=len(result.basis))
    var canonical = _order[P](budget)
    for p in result.basis:
        values.append(Array[P, k](rebind_var[SparsePoly[_Ring[k]]](p.reorder(canonical, budget)), budget))
    _allocation[_BasisData[k]](1, budget)
    var modulus = UInt64(0)
    comptime if k == 3:
        modulus = rebind[Modulus](ctx).value
    return Basis[P, k](ArcPointer(_BasisData[k](generators^, result^, ctx.copy())), Values[Array[P, k], k](values^, modulus, budget))


def groebner[I: Iterable, P: Copyable & Deinitable, C: Copyable & Deinitable](generators: I, mut budget: Budget, *, order: String = "grevlex", axes: List[Int] = List[Int](), witnesses: Bool = True, certify: Bool = True) raises PolyError -> Basis[P, _FieldKind[_Kind[C]]] where _Element[_Nested[I]] == Tuple[P, C]:
    """Compute a reusable reduced monic Groebner basis from sparse polynomials.

    Integer coefficients promote to QQ. QQi and prime fields remain in their
    own fields. Set witnesses=False when only reduction or Boolean membership is needed.

    Parameters:
        I: The inferred input type.
        P: The inferred power shape.
        C: The inferred input type.

    Args:
        generators: A finite iterable of sparse term iterables or prepared arrays with one power shape.
        budget: The shared work allowance for preparation and computation.
        order: One of lex, grlex, or grevlex; defaults to grevlex.
        axes: Variable priority, highest first; defaults to increasing axis order.
        witnesses: Retain cofactor rows for membership witnesses and basis verification.
        certify: Over QQ without witnesses, prove the basis computed from modular images exactly; False skips the proof, and the result is then the reduced basis with high probability.

    Returns:
        The computed result, with its evidence retained.

    Raises:
        PolyError: DOMAIN for incompatible input, UNSUPPORTED for an unavailable operation, or LIMIT/CAPACITY on resource limits.
    """
    comptime k = _FieldKind[_Kind[C]]
    var prepared = _system[k, I, P, C](generators, budget)
    return _basis(prepared[0], prepared[1], order, axes, witnesses, certify, budget)


def groebner[I: Iterable, P: Copyable & Deinitable, C: Copyable & Deinitable](generators: I, *, max_steps: UInt64 = UInt64.MAX, order: String = "grevlex", axes: List[Int] = List[Int](), witnesses: Bool = True, certify: Bool = True) raises PolyError -> Basis[P, _FieldKind[_Kind[C]]] where _Element[_Nested[I]] == Tuple[P, C]:
    """Compute a reusable reduced monic Groebner basis from sparse polynomials.

    Integer coefficients promote to QQ. QQi and prime fields remain in their
    own fields. Set witnesses=False when only reduction or Boolean membership is needed.

    Parameters:
        I: The inferred input type.
        P: The inferred power shape.
        C: The inferred input type.

    Args:
        generators: A finite iterable of sparse term iterables or prepared arrays with one power shape.
        max_steps: The complete call's work allowance; defaults to UInt64.MAX.
        order: One of lex, grlex, or grevlex; defaults to grevlex.
        axes: Variable priority, highest first; defaults to increasing axis order.
        witnesses: Retain cofactor rows for membership witnesses and basis verification.
        certify: Over QQ without witnesses, prove the basis computed from modular images exactly; False skips the proof, and the result is then the reduced basis with high probability.

    Returns:
        The computed result, with its evidence retained.

    Raises:
        PolyError: DOMAIN for incompatible input, UNSUPPORTED for an unavailable operation, or LIMIT/CAPACITY on resource limits.
    """
    var budget = Budget(max_steps)
    return groebner[I, P, C](generators, budget, order=order, axes=axes, witnesses=witnesses, certify=certify)


def _basis_input[I: Iterable, P: Copyable & Deinitable, C: Copyable & Deinitable, k: Int](values: I, basis: Basis[P, k], mut budget: Budget) raises PolyError -> Array[P, k] where _Element[I] == Tuple[P, C]:
    comptime assert _Kind[C] <= k, "basis queries cannot widen the prepared coefficient field"
    var p = _prepare[I, P, C](values, budget)
    _ = _merge_modulus(p.modulus(), basis._values.modulus())
    return _promote[k](p, basis._data[].context, budget)


def reduce[I: Iterable, P: Copyable & Deinitable, C: Copyable & Deinitable, k: Int](values: I, basis: Basis[P, k], mut budget: Budget) raises PolyError -> Array[P, k] where _Element[I] == Tuple[P, C]:
    """Return the unique normal form modulo a prepared Groebner basis.

    Parameters:
        I: The inferred input type.
        P: The inferred power shape.
        C: The inferred input type.
        k: The inferred coefficient kind.

    Args:
        values: The sparse polynomial to reduce.
        basis: A prepared basis in the same field and power shape.
        budget: The shared work allowance for preparation and computation.

    Returns:
        A canonical sparse polynomial array in the basis field.

    Raises:
        PolyError: DOMAIN for incompatible input, UNSUPPORTED for an unavailable operation, or LIMIT/CAPACITY on resource limits.
    """
    var p = _basis_input[I, P, C, k](values, basis, budget)
    var division = _reduce(rebind[SparsePoly[_Field[k]]](p._core[]), basis._data[].basis, budget)
    return Array[P, k](rebind_var[SparsePoly[_Ring[k]]](division.remainder.reorder(_order[P](budget), budget)), budget)


def reduce[I: Iterable, P: Copyable & Deinitable, C: Copyable & Deinitable, k: Int](values: I, basis: Basis[P, k], *, max_steps: UInt64 = UInt64.MAX) raises PolyError -> Array[P, k] where _Element[I] == Tuple[P, C]:
    """Return the unique normal form modulo a prepared Groebner basis.

    Parameters:
        I: The inferred input type.
        P: The inferred power shape.
        C: The inferred input type.
        k: The inferred coefficient kind.

    Args:
        values: The sparse polynomial to reduce.
        basis: A prepared basis in the same field and power shape.
        max_steps: The complete call's work allowance; defaults to UInt64.MAX.

    Returns:
        A canonical sparse polynomial array in the basis field.

    Raises:
        PolyError: DOMAIN for incompatible input, UNSUPPORTED for an unavailable operation, or LIMIT/CAPACITY on resource limits.
    """
    var budget = Budget(max_steps)
    return reduce[I, P, C, k](values, basis, budget)


def contains[I: Iterable, P: Copyable & Deinitable, C: Copyable & Deinitable, k: Int](values: I, basis: Basis[P, k], mut budget: Budget) raises PolyError -> Bool where _Element[I] == Tuple[P, C]:
    """Test ideal membership using a prepared basis.

    Parameters:
        I: The inferred input type.
        P: The inferred power shape.
        C: The inferred input type.
        k: The inferred coefficient kind.

    Args:
        values: The sparse polynomial to test.
        basis: The prepared basis; cofactor tracking is not required.
        budget: The shared work allowance for preparation and computation.

    Returns:
        True exactly when the normal form is zero. Exhausted work raises instead of returning False.

    Raises:
        PolyError: DOMAIN for incompatible input, UNSUPPORTED for an unavailable operation, or LIMIT/CAPACITY on resource limits.
    """
    return len(reduce[I, P, C, k](values, basis, budget)) == 0


def contains[I: Iterable, P: Copyable & Deinitable, C: Copyable & Deinitable, k: Int](values: I, basis: Basis[P, k], *, max_steps: UInt64 = UInt64.MAX) raises PolyError -> Bool where _Element[I] == Tuple[P, C]:
    """Test ideal membership using a prepared basis.

    Parameters:
        I: The inferred input type.
        P: The inferred power shape.
        C: The inferred input type.
        k: The inferred coefficient kind.

    Args:
        values: The sparse polynomial to test.
        basis: The prepared basis; cofactor tracking is not required.
        max_steps: The complete call's work allowance; defaults to UInt64.MAX.

    Returns:
        True exactly when the normal form is zero. Exhausted work raises instead of returning False.

    Raises:
        PolyError: DOMAIN for incompatible input, UNSUPPORTED for an unavailable operation, or LIMIT/CAPACITY on resource limits.
    """
    var budget = Budget(max_steps)
    return contains[I, P, C, k](values, basis, budget)


@fieldwise_init
struct _MembershipData[k: Int](Copyable, Movable):
    var polynomial: SparsePoly[_Field[Self.k]]
    var certificate: MembershipCertificate[_Field[Self.k]]
    var basis: ArcPointer[_BasisData[Self.k]]


@fieldwise_init
struct Membership[P: Copyable & Deinitable, k: Int](Copyable, Movable):
    """A checked-identity candidate against the original ordered generators.

    Parameters:
        P: The sparse power shape.
        k: The prepared coefficient field.
    """
    var cofactors: Values[Array[Self.P, Self.k], Self.k]
    """Multipliers in original generator order, with canonical array storage."""
    var _data: ArcPointer[_MembershipData[Self.k]]

    def evidence(self) -> ref[ImmOrigin(origin_of(self._data[].certificate))] MembershipCertificate[_Field[Self.k]]:
        """Borrow the exact membership identity certificate.

        Returns:
            Immutable multipliers in original generator order.
        """
        return self._data[].certificate


def membership[I: Iterable, P: Copyable & Deinitable, C: Copyable & Deinitable, k: Int](values: I, basis: Basis[P, k], mut budget: Budget) raises PolyError -> Optional[Membership[P, k]] where _Element[I] == Tuple[P, C]:
    """Express a polynomial as a combination of the original generators.

    Parameters:
        I: The inferred input type.
        P: The inferred power shape.
        C: The inferred input type.
        k: The inferred coefficient kind.

    Args:
        values: The proposed ideal member.
        basis: A basis constructed with witnesses=True.
        budget: The shared work allowance for preparation and computation.

    Returns:
        A membership witness, or None for a nonmember. Budget exhaustion raises.

    Raises:
        PolyError: DOMAIN for incompatible input, UNSUPPORTED for an unavailable operation, or LIMIT/CAPACITY on resource limits.
    """
    if not basis._data[].basis.cofactors:
        raise PolyError(PolyErrorKind.DOMAIN, "membership witnesses require groebner(..., witnesses=True)")
    var p = _basis_input[I, P, C, k](values, basis, budget)
    var core = rebind_var[SparsePoly[_Field[k]]](p._core[].reorder(basis._data[].basis.order, budget))
    var division = _reduce(core, basis._data[].basis, budget)
    if not division.remainder.is_zero():
        return None
    var n = len(basis._data[].generators)
    _allocation[SparsePoly[_Field[k]]](n, budget)
    var row = List[SparsePoly[_Field[k]]](capacity=n)
    for i in range(n):
        budget.charge(1)
        var total = SparsePoly[_Field[k]].zero(core.order, core.ring, budget)
        for j in range(len(division.quotients)):
            budget.charge(1)
            total = total.add(division.quotients[j].mul(basis._data[].basis.cofactors.value()[j][i], budget), budget)
        row.append(total^)
    _allocation[Array[P, k]](n, budget)
    var values_out = List[Array[P, k]](capacity=n)
    for q in row:
        values_out.append(Array[P, k](rebind_var[SparsePoly[_Ring[k]]](q.reorder(_order[P](budget), budget)), budget))
    _allocation[_MembershipData[k]](1, budget)
    return Membership[P, k](Values[Array[P, k], k](values_out^, basis._values.modulus(), budget), ArcPointer(_MembershipData[k](core^, MembershipCertificate[_Field[k]](row^), basis._data.copy())))


def membership[I: Iterable, P: Copyable & Deinitable, C: Copyable & Deinitable, k: Int](values: I, basis: Basis[P, k], *, max_steps: UInt64 = UInt64.MAX) raises PolyError -> Optional[Membership[P, k]] where _Element[I] == Tuple[P, C]:
    """Express a polynomial as a combination of the original generators.

    Parameters:
        I: The inferred input type.
        P: The inferred power shape.
        C: The inferred input type.
        k: The inferred coefficient kind.

    Args:
        values: The proposed ideal member.
        basis: A basis constructed with witnesses=True.
        max_steps: The complete call's work allowance; defaults to UInt64.MAX.

    Returns:
        A membership witness, or None for a nonmember. Budget exhaustion raises.

    Raises:
        PolyError: DOMAIN for incompatible input, UNSUPPORTED for an unavailable operation, or LIMIT/CAPACITY on resource limits.
    """
    var budget = Budget(max_steps)
    return membership[I, P, C, k](values, basis, budget)


def check_membership[P: Copyable & Deinitable, k: Int](result: Membership[P, k], mut budget: Budget) raises PolyError -> Bool:
    """Verify the retained identity against the original generators.

    Parameters:
        P: The inferred power shape.
        k: The inferred coefficient kind.

    Args:
        result: The membership result, including its visible cofactor arrays.
        budget: The shared work allowance for preparation and computation.

    Returns:
        Whether the multipliers prove the original membership identity.

    Raises:
        PolyError: DOMAIN for incompatible input, UNSUPPORTED for an unavailable operation, or LIMIT/CAPACITY on resource limits.
    """
    if len(result.cofactors) != len(result.evidence().cofactors):
        return False
    for i in range(len(result.cofactors)):
        budget.charge(1)
        if not result.cofactors[i]._core[].sub(rebind[SparsePoly[_Ring[k]]](result.evidence().cofactors[i]).reorder(_order[P](budget), budget), budget).is_zero():
            return False
    return _check_membership(result._data[].polynomial, result._data[].basis[].generators, result._data[].certificate, budget)


def check_membership[P: Copyable & Deinitable, k: Int](result: Membership[P, k], *, max_steps: UInt64 = UInt64.MAX) raises PolyError -> Bool:
    """Verify the retained identity against the original generators.

    Parameters:
        P: The inferred power shape.
        k: The inferred coefficient kind.

    Args:
        result: The membership result, including its visible cofactor arrays.
        max_steps: The complete call's work allowance; defaults to UInt64.MAX.

    Returns:
        Whether the multipliers prove the original membership identity.

    Raises:
        PolyError: DOMAIN for incompatible input, UNSUPPORTED for an unavailable operation, or LIMIT/CAPACITY on resource limits.
    """
    var budget = Budget(max_steps)
    return check_membership(result, budget)


def check_groebner[P: Copyable & Deinitable, k: Int](basis: Basis[P, k], mut budget: Budget) raises PolyError -> Bool:
    """Verify the Groebner property and equality with the original ideal.

    This checks ideal equality and the Groebner property independently of the
    producer. It does not certify the reducedness or ordering of the basis.

    Parameters:
        P: The inferred power shape.
        k: The inferred coefficient kind.

    Args:
        basis: A basis produced with witnesses=True.
        budget: The shared work allowance for preparation and computation.

    Returns:
        Whether both ideal containments and every Buchberger pair check succeed.

    Raises:
        PolyError: DOMAIN for incompatible input, UNSUPPORTED for an unavailable operation, or LIMIT/CAPACITY on resource limits.
    """
    ref data = basis._data[]
    ref core = data.basis
    if not core.cofactors:
        raise PolyError(PolyErrorKind.DOMAIN, "basis checking requires witnesses=True")
    if len(core.basis) != len(core.cofactors.value()) or len(core.basis) != len(basis):
        return False
    for i in range(len(core.basis)):
        budget.charge(1)
        ref p = core.basis[i]
        var visible = basis[i]
        if not visible._core[].sub(rebind[SparsePoly[_Ring[k]]](p).reorder(_order[P](budget), budget), budget).is_zero():
            return False
        if p.is_zero():
            return False
        _allocation[SparsePoly[_Field[k]]](len(core.cofactors.value()[i]), budget)
        var row = List[SparsePoly[_Field[k]]]()
        for q in core.cofactors.value()[i]:
            row.append(q.reorder(core.order, budget))
        if not _check_membership(p, data.generators, MembershipCertificate[_Field[k]](row^), budget):
            return False
        if not p.leading(budget).coefficient.sub(_Field[k].one(p.ring), budget).is_zero():
            return False
    for p in data.generators:
        if not _reduce(p, core, budget).remainder.is_zero():
            return False
    for i in range(len(core.basis)):
        for j in range(i):
            budget.charge(1)
            var a = core.basis[i].leading(budget)
            var b = core.basis[j].leading(budget)
            var common = a.monomial.lcm(b.monomial, budget)
            _allocation[Term[_Field[k]]](2, budget)
            var left = SparsePoly[_Field[k]].from_terms([Term[_Field[k]](common.div(a.monomial, budget), a.coefficient.inverse(budget))], core.order, data.context, budget)
            var right = SparsePoly[_Field[k]].from_terms([Term[_Field[k]](common.div(b.monomial, budget), b.coefficient.inverse(budget))], core.order, data.context, budget)
            var s_polynomial = left.mul(core.basis[i], budget).sub(right.mul(core.basis[j], budget), budget)
            if not _reduce(s_polynomial, core, budget).remainder.is_zero():
                return False
    return True


def check_groebner[P: Copyable & Deinitable, k: Int](basis: Basis[P, k], *, max_steps: UInt64 = UInt64.MAX) raises PolyError -> Bool:
    """Verify the Groebner property and equality with the original ideal.

    This checks ideal equality and the Groebner property independently of the
    producer. It does not certify the reducedness or ordering of the basis.

    Parameters:
        P: The inferred power shape.
        k: The inferred coefficient kind.

    Args:
        basis: A basis produced with witnesses=True.
        max_steps: The complete call's work allowance; defaults to UInt64.MAX.

    Returns:
        Whether both ideal containments and every Buchberger pair check succeed.

    Raises:
        PolyError: DOMAIN for incompatible input, UNSUPPORTED for an unavailable operation, or LIMIT/CAPACITY on resource limits.
    """
    var budget = Budget(max_steps)
    return check_groebner(basis, budget)


comptime _PolynomialElement[I: AnyType] = _Element[downcast[I, Iterable]]
comptime _SystemRank[P: Copyable & Deinitable, previous: Int, I: Movable] = _Join[previous, _TermKind[P, _PolynomialElement[I]]]
comptime _SystemKind[P: Copyable & Deinitable, T: type_of(Tuple)] = _FieldKind[T.Ts.reduce[0, _SystemRank[P, ...]]]

def _system_tuple[P: Copyable & Deinitable, k: Int, *Ts: Copyable & Deinitable](values: Tuple[*Ts], mut budget: Budget) raises PolyError -> Tuple[List[Array[P, k]], _Ring[k].Context]:
    comptime assert Tuple[*Ts].Ts.length > 0, "an empty system needs a typed iterable to preserve its power shape"
    _allocation[Optional[Array[P, k]]](Tuple[*Ts].Ts.length, budget)
    var slots = List[Optional[Array[P, k]]](length=Tuple[*Ts].Ts.length, fill=None)
    var modulus = UInt64(0)
    # Read modular polynomials first to establish their common context. Each
    # input iterator is still consumed once; output preserves generator order.
    comptime if k == 3:
        comptime for i in range(Tuple[*Ts].Ts.length):
            comptime T = Tuple[*Ts].Ts[i]
            comptime if _TermKind[P, _PolynomialElement[T]] == 3:
                comptime R = downcast[T, Iterable & Copyable & Deinitable]
                comptime assert _Element[R] == Tuple[P, ModInt], "modular polynomial terms must share the same power shape"
                var p = _prepare[R, P, ModInt](rebind[R](values[i]), budget)
                modulus = _merge_modulus(modulus, p.modulus())
                slots[i] = rebind_var[Array[P, k]](p^)
    var ctx = _data_context[k](modulus, 0, budget)
    comptime for i in range(Tuple[*Ts].Ts.length):
        comptime T = Tuple[*Ts].Ts[i]
        comptime assert _TermKind[P, _PolynomialElement[T]] >= 0, "every polynomial must use the same power shape and exact coefficients"
        comptime if k != 3 or _TermKind[P, _PolynomialElement[T]] != 3:
            comptime R = downcast[T, Iterable & Copyable & Deinitable]
            comptime C = downcast[_TermScalar[P, _PolynomialElement[T]], Copyable & Deinitable]
            comptime assert _Element[R] == Tuple[P, C], "every polynomial must use the same power shape and exact coefficients"
            var p = _prepare[R, P, C](rebind[R](values[i]), budget)
            slots[i] = _promote[k](p, ctx, budget)
    _allocation[Array[P, k]](Tuple[*Ts].Ts.length, budget)
    var result = List[Array[P, k]](capacity=Tuple[*Ts].Ts.length)
    for slot in slots:
        budget.charge(1)
        result.append(slot.value().copy())
    return result^, ctx^


def groebner[P: Copyable & Deinitable, C: Copyable & Deinitable, *Ts: Copyable & Deinitable](generators: Tuple[*Ts], mut budget: Budget, *, order: String = "grevlex", axes: List[Int] = List[Int](), witnesses: Bool = True, certify: Bool = True) raises PolyError -> Basis[P, _SystemKind[P, Tuple[*Ts]]] where _PolynomialElement[Tuple[*Ts].Ts[0]] == Tuple[P, C]:
    """Infer a common field across a tuple of differently typed polynomials.

    Parameters:
        P: The shared power shape.
        C: The first polynomial coefficient type.
        Ts: The independently inferred polynomial iterable types.

    Args:
        generators: A nonempty tuple of sparse polynomials with one power shape.
        budget: The shared work allowance for preparation and computation.
        order: One of lex, grlex, or grevlex.
        axes: Variable priority, highest first.
        witnesses: Retain original-generator cofactors for independent checking.
        certify: Over QQ without witnesses, prove the basis computed from modular images exactly; False skips the proof, and the result is then the reduced basis with high probability.

    Returns:
        The computed result, with its evidence retained.

    Raises:
        PolyError: DOMAIN for incompatible input, UNSUPPORTED for an unavailable operation, or LIMIT/CAPACITY on resource limits.
    """
    comptime k = _SystemKind[P, Tuple[*Ts]]
    var prepared = _system_tuple[P, k](generators, budget)
    return _basis(prepared[0], prepared[1], order, axes, witnesses, certify, budget)


def groebner[P: Copyable & Deinitable, C: Copyable & Deinitable, *Ts: Copyable & Deinitable](generators: Tuple[*Ts], *, max_steps: UInt64 = UInt64.MAX, order: String = "grevlex", axes: List[Int] = List[Int](), witnesses: Bool = True, certify: Bool = True) raises PolyError -> Basis[P, _SystemKind[P, Tuple[*Ts]]] where _PolynomialElement[Tuple[*Ts].Ts[0]] == Tuple[P, C]:
    """Infer a common field across a tuple of differently typed polynomials.

    Parameters:
        P: The shared power shape.
        C: The first polynomial coefficient type.
        Ts: The independently inferred polynomial iterable types.

    Args:
        generators: A nonempty tuple of sparse polynomials with one power shape.
        max_steps: The complete call's work allowance; defaults to UInt64.MAX.
        order: One of lex, grlex, or grevlex.
        axes: Variable priority, highest first.
        witnesses: Retain original-generator cofactors for independent checking.
        certify: Over QQ without witnesses, prove the basis computed from modular images exactly; False skips the proof, and the result is then the reduced basis with high probability.

    Returns:
        The computed result, with its evidence retained.

    Raises:
        PolyError: DOMAIN for incompatible input, UNSUPPORTED for an unavailable operation, or LIMIT/CAPACITY on resource limits.
    """
    var budget = Budget(max_steps)
    return groebner[P, C, *Ts](generators, budget, order=order, axes=axes, witnesses=witnesses, certify=certify)


# Numerical operations keep output precision explicit.
from . import _numeric as _num
from ._numeric import SparseArray as NumericArray
from polynomials import NumericDomain


def asarray[I: Iterable, Context: Copyable & Deinitable, P: Copyable & Deinitable, T: Copyable & Deinitable](values: I, mut budget: Budget, *, context: Context) raises PolyError -> NumericArray[P, _num._Domain[Context, T]] where _Element[I] == Tuple[P, T]:
    """Construct finite numerical coefficients using an explicit precision context.

    Parameters:
        I: The inferred input iterable type.
        Context: The explicit APN arithmetic context type.
        P: The sparse power shape or retained source array type, inferred from the input.
        T: The scalar or batch item type.

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
    comptime D = _num._Domain[Context, T]
    return _num._sparse[D, I, P, T](values, rebind[D.Context](context), budget)


def asarray[I: Iterable, Context: Copyable & Deinitable, P: Copyable & Deinitable, T: Copyable & Deinitable](values: I, *, context: Context, max_steps: UInt64 = UInt64.MAX) raises PolyError -> NumericArray[P, _num._Domain[Context, T]] where _Element[I] == Tuple[P, T]:
    """Construct finite numerical coefficients using an explicit precision context.

    Parameters:
        I: The inferred input iterable type.
        Context: The explicit APN arithmetic context type.
        P: The sparse power shape or retained source array type, inferred from the input.
        T: The scalar or batch item type.

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
    return asarray[I, Context, P, T](values, budget, context=context)

from polynomials import numeric_integrate_sparse


def add[P: Copyable & Deinitable, D: NumericDomain](a: NumericArray[P, D], b: NumericArray[P, D], mut budget: Budget, *, context: D.Context) raises PolyError -> NumericArray[P, D]:
    """Add numerical polynomials in a fixed accumulation order.

    Parameters:
        P: The sparse power shape or retained source array type, inferred from the input.
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
    return NumericArray[P, D](result^, budget)


def add[P: Copyable & Deinitable, D: NumericDomain](a: NumericArray[P, D], b: NumericArray[P, D], *, context: D.Context, max_steps: UInt64 = UInt64.MAX) raises PolyError -> NumericArray[P, D]:
    """Add numerical polynomials in a fixed accumulation order.

    Parameters:
        P: The sparse power shape or retained source array type, inferred from the input.
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


def subtract[P: Copyable & Deinitable, D: NumericDomain](a: NumericArray[P, D], b: NumericArray[P, D], mut budget: Budget, *, context: D.Context) raises PolyError -> NumericArray[P, D]:
    """Subtract numerical polynomials with explicit rounding.

    Parameters:
        P: The sparse power shape or retained source array type, inferred from the input.
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
    return NumericArray[P, D](result^, budget)


def subtract[P: Copyable & Deinitable, D: NumericDomain](a: NumericArray[P, D], b: NumericArray[P, D], *, context: D.Context, max_steps: UInt64 = UInt64.MAX) raises PolyError -> NumericArray[P, D]:
    """Subtract numerical polynomials with explicit rounding.

    Parameters:
        P: The sparse power shape or retained source array type, inferred from the input.
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


def multiply[P: Copyable & Deinitable, D: NumericDomain](a: NumericArray[P, D], b: NumericArray[P, D], mut budget: Budget, *, context: D.Context) raises PolyError -> NumericArray[P, D]:
    """Multiply numerical polynomials with explicit rounding.

    Parameters:
        P: The sparse power shape or retained source array type, inferred from the input.
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
    return NumericArray[P, D](result^, budget)


def multiply[P: Copyable & Deinitable, D: NumericDomain](a: NumericArray[P, D], b: NumericArray[P, D], *, context: D.Context, max_steps: UInt64 = UInt64.MAX) raises PolyError -> NumericArray[P, D]:
    """Multiply numerical polynomials with explicit rounding.

    Parameters:
        P: The sparse power shape or retained source array type, inferred from the input.
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


def negative[P: Copyable & Deinitable, D: NumericDomain](a: NumericArray[P, D], mut budget: Budget, *, context: D.Context) raises PolyError -> NumericArray[P, D]:
    """Negate numerical coefficients.

    Parameters:
        P: The sparse power shape or retained source array type, inferred from the input.
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
    return NumericArray[P, D](result^, budget)


def negative[P: Copyable & Deinitable, D: NumericDomain](a: NumericArray[P, D], *, context: D.Context, max_steps: UInt64 = UInt64.MAX) raises PolyError -> NumericArray[P, D]:
    """Negate numerical coefficients.

    Parameters:
        P: The sparse power shape or retained source array type, inferred from the input.
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


def power[P: Copyable & Deinitable, D: NumericDomain](a: NumericArray[P, D], exponent: Int, mut budget: Budget, *, context: D.Context) raises PolyError -> NumericArray[P, D]:
    """Raise a numerical polynomial to a nonnegative integer power.

    Parameters:
        P: The sparse power shape or retained source array type, inferred from the input.
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
    return NumericArray[P, D](result^, budget)


def power[P: Copyable & Deinitable, D: NumericDomain](a: NumericArray[P, D], exponent: Int, *, context: D.Context, max_steps: UInt64 = UInt64.MAX) raises PolyError -> NumericArray[P, D]:
    """Raise a numerical polynomial to a nonnegative integer power.

    Parameters:
        P: The sparse power shape or retained source array type, inferred from the input.
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


def derivative[P: Copyable & Deinitable, D: NumericDomain](a: NumericArray[P, D], mut budget: Budget, *, context: D.Context, axis: Int = 0) raises PolyError -> NumericArray[P, D]:
    """Differentiate using the requested output precision.

    Parameters:
        P: The sparse power shape or retained source array type, inferred from the input.
        D: The APN numerical domain associated with the stored scalars.

    Args:
        a: The first input value.
        budget: The shared work allowance, including preparation, computation, and result storage.
        context: Explicit output precision, rounding settings, or ball working precision.
        axis: The zero-based polynomial axis; defaults to zero.

    Returns:
        The derivative along the selected axis.

    Raises:
        PolyError: DOMAIN for invalid or incompatible input, or LIMIT/CAPACITY on resource limits.
    """
    _num._context[D](context, budget)
    if axis < 0 or axis >= _width[P]():
        raise PolyError(PolyErrorKind.DOMAIN, "axis is outside the sparse power shape")
    var result = a._core[].derivative(Int64(axis), context, budget)
    return NumericArray[P, D](result^, budget)


def derivative[P: Copyable & Deinitable, D: NumericDomain](a: NumericArray[P, D], *, context: D.Context, max_steps: UInt64 = UInt64.MAX, axis: Int = 0) raises PolyError -> NumericArray[P, D]:
    """Differentiate using the requested output precision.

    Parameters:
        P: The sparse power shape or retained source array type, inferred from the input.
        D: The APN numerical domain associated with the stored scalars.

    Args:
        a: The first input value.
        context: Explicit output precision, rounding settings, or ball working precision.
        max_steps: The complete call's work allowance; defaults to UInt64.MAX.
        axis: The zero-based polynomial axis; defaults to zero.

    Returns:
        The derivative along the selected axis.

    Raises:
        PolyError: DOMAIN for invalid or incompatible input, or LIMIT/CAPACITY on resource limits.
    """
    var budget = Budget(max_steps)
    return derivative(a, budget, context=context, axis=axis)


def integral[P: Copyable & Deinitable, D: NumericDomain](a: NumericArray[P, D], mut budget: Budget, *, context: D.Context, axis: Int = 0) raises PolyError -> NumericArray[P, D]:
    """Integrate with zero integration constant and explicit rounding.

    Parameters:
        P: The sparse power shape or retained source array type, inferred from the input.
        D: The APN numerical domain associated with the stored scalars.

    Args:
        a: The first input value.
        budget: The shared work allowance, including preparation, computation, and result storage.
        context: Explicit output precision, rounding settings, or ball working precision.
        axis: The zero-based polynomial axis; defaults to zero.

    Returns:
        An antiderivative with zero integration constant.

    Raises:
        PolyError: DOMAIN for invalid or incompatible input, or LIMIT/CAPACITY on resource limits.
    """
    _num._context[D](context, budget)
    if axis < 0 or axis >= _width[P]():
        raise PolyError(PolyErrorKind.DOMAIN, "axis is outside the sparse power shape")
    var result = numeric_integrate_sparse(a._core[], Int64(axis), context, budget)
    return NumericArray[P, D](result^, budget)


def integral[P: Copyable & Deinitable, D: NumericDomain](a: NumericArray[P, D], *, context: D.Context, max_steps: UInt64 = UInt64.MAX, axis: Int = 0) raises PolyError -> NumericArray[P, D]:
    """Integrate with zero integration constant and explicit rounding.

    Parameters:
        P: The sparse power shape or retained source array type, inferred from the input.
        D: The APN numerical domain associated with the stored scalars.

    Args:
        a: The first input value.
        context: Explicit output precision, rounding settings, or ball working precision.
        max_steps: The complete call's work allowance; defaults to UInt64.MAX.
        axis: The zero-based polynomial axis; defaults to zero.

    Returns:
        An antiderivative with zero integration constant.

    Raises:
        PolyError: DOMAIN for invalid or incompatible input, or LIMIT/CAPACITY on resource limits.
    """
    var budget = Budget(max_steps)
    return integral(a, budget, context=context, axis=axis)


from polynomials import serialize_sparse, deserialize_sparse, serialize_sparse_to, deserialize_sparse_from, PolynomialTextSink, PolynomialTextSource


def dumps[I: Iterable, P: Copyable & Deinitable, C: Copyable & Deinitable](values: I, mut budget: Budget) raises PolyError -> String where _Element[I] == Tuple[P, C]:
    """Write canonical versioned polynomial text.

    AA and QQbar retain their exact root witnesses, which are validated on load.
    Arithmetic history is not serialized. Other exact domains keep their existing format.

    Parameters:
        I: The inferred input iterable type.
        P: The sparse power shape or retained source array type, inferred from the input.
        C: The input coefficient type.

    Args:
        values: Input coefficients, sparse terms, or prepared values as required by this overload.
        budget: The shared work allowance, including preparation, computation, and result storage.

    Returns:
        Canonical text including the final newline.

    Raises:
        PolyError: ENCODING for malformed or incompatible records, DOMAIN for invalid settings, or LIMIT/CAPACITY on resource limits.
    """
    var p = asarray[I, P, C](values, budget)
    comptime if _Kind[C] >= 4:
        from . import _algebraic_io
        return _algebraic_io._dumps_sparse(p._core[], budget)
    else:
        return serialize_sparse(p._core[], budget)


def dumps[I: Iterable, P: Copyable & Deinitable, C: Copyable & Deinitable](values: I, *, max_steps: UInt64 = UInt64.MAX) raises PolyError -> String where _Element[I] == Tuple[P, C]:
    """Write canonical versioned polynomial text.

    AA and QQbar retain their exact root witnesses, which are validated on load.
    Arithmetic history is not serialized. Other exact domains keep their existing format.

    Parameters:
        I: The inferred input iterable type.
        P: The sparse power shape or retained source array type, inferred from the input.
        C: The input coefficient type.

    Args:
        values: Input coefficients, sparse terms, or prepared values as required by this overload.
        max_steps: The complete call's work allowance; defaults to UInt64.MAX.

    Returns:
        Canonical text including the final newline.

    Raises:
        PolyError: ENCODING for malformed or incompatible records, DOMAIN for invalid settings, or LIMIT/CAPACITY on resource limits.
    """
    var budget = Budget(max_steps)
    return dumps[I, P, C](values, budget)


def dump[I: Iterable, P: Copyable & Deinitable, C: Copyable & Deinitable, S: PolynomialTextSink](values: I, mut sink: S, mut budget: Budget) raises PolyError where _Element[I] == Tuple[P, C] and _Kind[C] >= 0:
    """Write canonical versioned polynomial text in bounded chunks.

    AA and QQbar retain their exact root witnesses, which are validated on load.
    Arithmetic history is not serialized. Other exact domains keep their existing format.

    Parameters:
        I: The inferred input iterable type.
        P: The sparse power shape or retained source array type, inferred from the input.
        C: The input coefficient type.
        S: The text transport implementation.

    Args:
        values: Input coefficients, sparse terms, or prepared values as required by this overload.
        sink: The destination for ordered text chunks.
        budget: The shared work allowance, including preparation, computation, and result storage.

    Raises:
        PolyError: ENCODING for malformed or incompatible records, DOMAIN for invalid settings, or LIMIT/CAPACITY on resource limits.
    """
    var p = asarray[I, P, C](values, budget)
    comptime if _Kind[C] >= 4:
        from . import _algebraic_io
        _algebraic_io._dump_sparse(p._core[], sink, budget)
    else:
        serialize_sparse_to(p._core[], sink, budget)


def dump[I: Iterable, P: Copyable & Deinitable, C: Copyable & Deinitable, S: PolynomialTextSink](values: I, mut sink: S, *, max_steps: UInt64 = UInt64.MAX) raises PolyError where _Element[I] == Tuple[P, C] and _Kind[C] >= 0:
    """Write canonical versioned polynomial text.

    AA and QQbar retain their exact root witnesses, which are validated on load.
    Arithmetic history is not serialized. Other exact domains keep their existing format.

    Parameters:
        I: The inferred input iterable type.
        P: The sparse power shape or retained source array type, inferred from the input.
        C: The input coefficient type.
        S: The text transport implementation.

    Args:
        values: Input coefficients, sparse terms, or prepared values as required by this overload.
        sink: The destination for ordered text chunks.
        max_steps: The complete call's work allowance; defaults to UInt64.MAX.

    Raises:
        PolyError: ENCODING for malformed or incompatible records, DOMAIN for invalid settings, or LIMIT/CAPACITY on resource limits.
    """
    var budget = Budget(max_steps)
    dump[I, P, C, S](values, sink, budget)


def loads[T: Copyable & Deinitable, *, ndim: Int = 1](text: String, mut budget: Budget, *, modulus: UInt64 = 0) raises PolyError -> Array[_Shape[ndim], _Kind[T]]:
    """Read canonical text into an exact array; the scalar type selects the expected domain.

    AA and QQbar retain their exact root witnesses, which are validated on load.
    Arithmetic history is not serialized. Other exact domains keep their existing format.

    Parameters:
        T: The scalar or batch item type.
        ndim: The expected sparse axis count, including unused axes; defaults to one.

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
    var core: SparsePoly[_Ring[k]]
    comptime if k >= 4:
        from . import _algebraic_io
        core = _algebraic_io._loads_sparse[_Ring[k]](text, budget)
    else:
        core = deserialize_sparse[_Ring[k]](text, ctx.get(), budget)
    return rebind_var[Array[_Shape[ndim], k]](from_core[_Ring[k], ndim=ndim](core, budget))


def loads[T: Copyable & Deinitable, *, ndim: Int = 1](text: String, *, max_steps: UInt64 = UInt64.MAX, modulus: UInt64 = 0) raises PolyError -> Array[_Shape[ndim], _Kind[T]]:
    """Read canonical text into an exact array with one shared work limit.

    AA and QQbar retain their exact root witnesses, which are validated on load.
    Arithmetic history is not serialized. Other exact domains keep their existing format.

    Parameters:
        T: The scalar or batch item type.
        ndim: The expected sparse axis count, including unused axes; defaults to one.

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
    return loads[T, ndim=ndim](text, budget, modulus=modulus)


def load[T: Copyable & Deinitable, S: PolynomialTextSource, *, ndim: Int = 1](var source: S, mut budget: Budget, *, modulus: UInt64 = 0, max_field_bytes: Int = 16777216) raises PolyError -> Array[_Shape[ndim], _Kind[T]]:
    """Read canonical text into an exact array; the scalar type selects the expected domain.

    AA and QQbar retain their exact root witnesses, which are validated on load.
    Arithmetic history is not serialized. Other exact domains keep their existing format.

    Parameters:
        T: The scalar or batch item type.
        S: The text transport implementation.
        ndim: The expected sparse axis count, including unused axes; defaults to one.

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
    var core: SparsePoly[_Ring[k]]
    comptime if k >= 4:
        from . import _algebraic_io
        core = _algebraic_io._load_sparse[_Ring[k]](source^, budget, max_field_bytes)
    else:
        core = deserialize_sparse_from[_Ring[k]](source^, ctx.get(), budget, max_field_bytes=max_field_bytes)
    return rebind_var[Array[_Shape[ndim], k]](from_core[_Ring[k], ndim=ndim](core, budget))


def load[T: Copyable & Deinitable, S: PolynomialTextSource, *, ndim: Int = 1](var source: S, *, max_steps: UInt64 = UInt64.MAX, modulus: UInt64 = 0, max_field_bytes: Int = 16777216) raises PolyError -> Array[_Shape[ndim], _Kind[T]]:
    """Read canonical text into an exact array with one shared work limit.

    AA and QQbar retain their exact root witnesses, which are validated on load.
    Arithmetic history is not serialized. Other exact domains keep their existing format.

    Parameters:
        T: The scalar or batch item type.
        S: The text transport implementation.
        ndim: The expected sparse axis count, including unused axes; defaults to one.

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
    return load[T, S, ndim=ndim](source^, budget, modulus=modulus, max_field_bytes=max_field_bytes)

from polynomials import serialize_numeric_sparse, deserialize_numeric_sparse


def dumps[P: Copyable & Deinitable, D: NumericDomain](values: NumericArray[P, D], mut budget: Budget) raises PolyError -> String:
    """Serialize numerical coefficients with their stored precision and enclosures.

    Parameters:
        P: The sparse power shape or retained source array type, inferred from the input.
        D: The APN numerical domain associated with the stored scalars.

    Args:
        values: Input coefficients, sparse terms, or prepared values as required by this overload.
        budget: The shared work allowance, including preparation, computation, and result storage.

    Returns:
        Canonical text including the final newline.

    Raises:
        PolyError: ENCODING for malformed or incompatible records, DOMAIN for invalid settings, or LIMIT/CAPACITY on resource limits.
    """
    return serialize_numeric_sparse(values._core[], budget)


def dumps[P: Copyable & Deinitable, D: NumericDomain](values: NumericArray[P, D], *, max_steps: UInt64 = UInt64.MAX) raises PolyError -> String:
    """Serialize numerical coefficients with their stored precision and enclosures.

    Parameters:
        P: The sparse power shape or retained source array type, inferred from the input.
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
    return dumps(values, budget)


def loads_numeric[T: Copyable & Deinitable, *, ndim: Int = 1](text: String, mut budget: Budget) raises PolyError -> NumericArray[_Shape[ndim], _num._StoredDomain[T]]:
    """Restore stored numerical values exactly; subsequent arithmetic takes an explicit context.

    Parameters:
        T: The scalar or batch item type.
        ndim: The expected sparse axis count, including unused axes; defaults to one.

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
    var core = deserialize_numeric_sparse[D](text, budget)
    from ._numeric import _validate_sparse_axes
    _validate_sparse_axes(core, ndim, budget)
    return NumericArray[_Shape[ndim], _num._StoredDomain[T]](core^, budget)


def loads_numeric[T: Copyable & Deinitable, *, ndim: Int = 1](text: String, *, max_steps: UInt64 = UInt64.MAX) raises PolyError -> NumericArray[_Shape[ndim], _num._StoredDomain[T]]:
    """Restore stored numerical values exactly; subsequent arithmetic takes an explicit context.

    Parameters:
        T: The scalar or batch item type.
        ndim: The expected sparse axis count, including unused axes; defaults to one.

    Args:
        text: One canonical versioned polynomial record.
        max_steps: The complete call's work allowance; defaults to UInt64.MAX.

    Returns:
        A numerical array preserving the encoded scalar precision and enclosures.

    Raises:
        PolyError: ENCODING for malformed or incompatible records, DOMAIN for invalid settings, or LIMIT/CAPACITY on resource limits.
    """
    var budget = Budget(max_steps)
    return loads_numeric[T, ndim=ndim](text, budget)


from . import algebraic as _alg
from polynomials import RealAlgebraic


def _algebraic_assignments[P: Copyable & Deinitable, I: Iterable, X: Copyable & Deinitable](assignments: I, mut budget: Budget) raises PolyError -> List[Tuple[Int64, RealAlgebraic]] where _Element[I] == Tuple[Int, X]:
    var result = List[Tuple[Int64, RealAlgebraic]]()
    var cursor = iter(assignments)
    while True:
        budget.charge(1)
        var entry: Tuple[Int, X]
        try:
            entry = rebind_var[Tuple[Int, X]](next(cursor))
        except StopIteration:
            break
        if entry[0] < 0 or entry[0] >= _width[P]():
            raise PolyError(PolyErrorKind.DOMAIN, "algebraic assignment axis is outside the power shape")
        var value = _alg.asreal(entry[1], budget)
        _grow(result, budget)
        result.append((Int64(entry[0]), _alg._copy_witness(value.witness(), budget)))
    return result^


def specialize[I: Iterable, A: Iterable, P: Copyable & Deinitable, C: Copyable & Deinitable, X: Copyable & Deinitable](values: I, assignments: A, mut budget: Budget) raises PolyError -> _Specialized[P, C, X] where (_Element[I] == Tuple[P, C] and _Element[A] == Tuple[Int, X]):
    """Assign exact values to selected axes, retaining the remaining power shape.

    Parameters:
        I: The inferred input iterable type.
        A: The first input type.
        P: The sparse power shape or retained source array type, inferred from the input.
        C: The input coefficient type.
        X: The evaluation point or seed type.

    Args:
        values: Input coefficients, sparse terms, or prepared values as required by this overload.
        assignments: An iterable of (axis, exact real value) pairs; axes must be unique and in range.
        budget: The shared work allowance, including preparation, computation, and result storage.

    Returns:
        For rational or AA inputs and real assignments, retained coefficient-group proofs.
        Complex coefficients or assignments return a sparse array in the promoted field.

    Raises:
        PolyError: DOMAIN for invalid or incompatible input, or LIMIT/CAPACITY on resource limits.
    """
    comptime if (_Kind[C] == 0 or _Kind[C] == 1) and (_Kind[X] == 0 or _Kind[X] == 1 or _Kind[X] == 4):
        var p = _promote[1](_prepare[I, P, C](values, budget), NoContext(), budget)
        var point = _algebraic_assignments[P, A, X](assignments, budget)
        return rebind_var[_Specialized[P, C, X]](_alg._specialize[P](_sparse_copy(p._core[], _variables(_width[P](), List[Int64](), budget), True, budget), point^, budget))
    elif _Kind[C] == 4 and (_Kind[X] == 0 or _Kind[X] == 1 or _Kind[X] == 4):
        var p = _prepare[I, P, C](values, budget)
        var point = _algebraic_assignments[P, A, X](assignments, budget)
        return rebind_var[_Specialized[P, C, X]](_alg._specialized._make(rebind[Array[P, 4]](p), point^, budget))
    else:
        comptime assert _Kind[C] != 3 and _Kind[X] != 3, "algebraic specialization does not accept modular values"
        comptime k = _Join[_Kind[C], _Kind[X]]
        var ctx = _Context[k]().get()
        var p = _promote[k](_prepare[I, P, C](values, budget), ctx, budget)
        var replacements = List[Tuple[Int64, SparsePoly[_Ring[k]]]]()
        var cursor = iter(assignments)
        while True:
            budget.charge(1)
            var entry: Tuple[Int, X]
            try:
                entry = rebind_var[Tuple[Int, X]](next(cursor))
            except StopIteration:
                break
            _axis[P](entry[0])
            for previous in replacements:
                budget.charge(1)
                if previous[0] == Int64(entry[0]):
                    raise PolyError(PolyErrorKind.DOMAIN, "specialization axes must be distinct")
            var value = _wrap[k](_convert[k](entry[1], ctx, budget))
            _allocation[Term[_Ring[k]]](1, budget)
            var terms = List[Term[_Ring[k]]]()
            if not value.is_zero():
                terms.append(Term[_Ring[k]](Monomial(List[Tuple[Int64, UInt32]](), budget), value^))
            var replacement = SparsePoly[_Ring[k]].from_terms(terms^, p._core[].order, ctx, budget)
            _grow(replacements, budget)
            replacements.append((Int64(entry[0]), replacement^))
        return rebind_var[_Specialized[P, C, X]](Array[P, k](_substitute_many(p._core[], replacements, budget), budget))


def specialize[I: Iterable, A: Iterable, P: Copyable & Deinitable, C: Copyable & Deinitable, X: Copyable & Deinitable](values: I, assignments: A, *, max_steps: UInt64 = UInt64.MAX) raises PolyError -> _Specialized[P, C, X] where (_Element[I] == Tuple[P, C] and _Element[A] == Tuple[Int, X]):
    """Specialize selected axes with one work allowance.

    Parameters:
        I: The inferred input iterable type.
        A: The first input type.
        P: The sparse power shape or retained source array type, inferred from the input.
        C: The input coefficient type.
        X: The evaluation point or seed type.

    Args:
        values: Input coefficients, sparse terms, or prepared values as required by this overload.
        assignments: An iterable of (axis, exact real value) pairs; axes must be unique and in range.
        max_steps: The complete call's work allowance; defaults to UInt64.MAX.

    Returns:
        For rational or AA inputs and real assignments, retained coefficient-group proofs.
        Complex coefficients or assignments return a sparse array in the promoted field.

    Raises:
        PolyError: DOMAIN for invalid or incompatible input, or LIMIT/CAPACITY on resource limits.
    """
    var budget = Budget(max_steps)
    return specialize[I, A, P, C, X](values, assignments, budget)


def evaluate_algebraic[I: Iterable, P: Copyable & Deinitable, C: Copyable & Deinitable, *Ts: Copyable & Deinitable](values: I, point: Tuple[*Ts], mut budget: Budget) raises PolyError -> _alg.Real where _Element[I] == Tuple[P, C]:
    """Evaluate exactly at a coordinate tuple containing rational or algebraic values.

    Parameters:
        I: The inferred input iterable type.
        P: The sparse power shape or retained source array type, inferred from the input.
        C: The input coefficient type.
        Ts: The inferred tuple element types.

    Args:
        values: Input coefficients, sparse terms, or prepared values as required by this overload.
        point: The evaluation scalar or ordered coordinate tuple.
        budget: The shared work allowance, including preparation, computation, and result storage.

    Returns:
        An exact real value retaining the sparse evaluation certificate.

    Raises:
        PolyError: DOMAIN for invalid or incompatible input, or LIMIT/CAPACITY on resource limits.
    """
    comptime assert Tuple[*Ts].Ts.length == _width[P](), "evaluation point has the wrong number of coordinates"
    comptime assert _Kind[C] == 0 or _Kind[C] == 1, "algebraic evaluation requires integer or rational coefficients"
    var p = _promote[1](_prepare[I, P, C](values, budget), NoContext(), budget)
    _allocation[Tuple[Int64, RealAlgebraic]](_width[P](), budget)
    var assignments = List[Tuple[Int64, RealAlgebraic]](capacity=_width[P]())
    comptime for i in range(Tuple[*Ts].Ts.length):
        var value = _alg.asreal(point[i], budget)
        assignments.append((Int64(i), _alg._copy_witness(value.witness(), budget)))
    return _alg._evaluate_sparse(_sparse_copy(p._core[], _variables(_width[P](), List[Int64](), budget), True, budget), assignments^, budget)


def evaluate_algebraic[I: Iterable, P: Copyable & Deinitable, C: Copyable & Deinitable, *Ts: Copyable & Deinitable](values: I, point: Tuple[*Ts], *, max_steps: UInt64 = UInt64.MAX) raises PolyError -> _alg.Real where _Element[I] == Tuple[P, C]:
    """Evaluate a sparse polynomial at an exact real coordinate tuple.

    Parameters:
        I: The inferred input iterable type.
        P: The sparse power shape or retained source array type, inferred from the input.
        C: The input coefficient type.
        Ts: The inferred tuple element types.

    Args:
        values: Input coefficients, sparse terms, or prepared values as required by this overload.
        point: The evaluation scalar or ordered coordinate tuple.
        max_steps: The complete call's work allowance; defaults to UInt64.MAX.

    Returns:
        An exact real value retaining the sparse evaluation certificate.

    Raises:
        PolyError: DOMAIN for invalid or incompatible input, or LIMIT/CAPACITY on resource limits.
    """
    var budget = Budget(max_steps)
    return evaluate_algebraic[I, P, C, *Ts](values, point, budget)



def to_core[P: Copyable & Deinitable, D: NumericDomain](values: NumericArray[P, D], mut budget: Budget, *, variables: List[Int64] = List[Int64]()) raises PolyError -> NumericSparsePoly[D]:
    """Copy the numerical array into independently mutable core storage.

    Parameters:
        P: The sparse power shape or retained source array type, inferred from the input.
        D: The APN numerical domain associated with the stored scalars.

    Args:
        values: Input coefficients, sparse terms, or prepared values as required by this overload.
        budget: The shared work allowance, including preparation, computation, and result storage.
        variables: Core variable IDs in array-axis order; empty uses consecutive IDs.

    Returns:
        An independent mutable core polynomial.

    Raises:
        PolyError: DOMAIN for invalid or incompatible input, or LIMIT/CAPACITY on resource limits.
    """
    var mapping = _variables(_width[P](), variables, budget)
    return _ni._sparse(values._core[], mapping, True, budget)


def to_core[P: Copyable & Deinitable, D: NumericDomain](values: NumericArray[P, D], *, max_steps: UInt64 = UInt64.MAX, variables: List[Int64] = List[Int64]()) raises PolyError -> NumericSparsePoly[D]:
    """Copy the numerical array into independently mutable core storage.

    Parameters:
        P: The sparse power shape or retained source array type, inferred from the input.
        D: The APN numerical domain associated with the stored scalars.

    Args:
        values: Input coefficients, sparse terms, or prepared values as required by this overload.
        max_steps: The complete call's work allowance; defaults to UInt64.MAX.
        variables: Core variable IDs in array-axis order; empty uses consecutive IDs.

    Returns:
        An independent mutable core polynomial.

    Raises:
        PolyError: DOMAIN for invalid or incompatible input, or LIMIT/CAPACITY on resource limits.
    """
    var budget = Budget(max_steps)
    return to_core[P, D](values, budget, variables=variables)


def from_core[D: NumericDomain, *, ndim: Int = 1](values: NumericSparsePoly[D], mut budget: Budget, *, variables: List[Int64] = List[Int64]()) raises PolyError -> NumericArray[_Shape[ndim], D]:
    """Validate and copy a numerical core polynomial without rounding its stored values.

    Parameters:
        D: The APN numerical domain associated with the stored scalars.
        ndim: The expected sparse axis count, including unused axes; defaults to one.

    Args:
        values: Input coefficients, sparse terms, or prepared values as required by this overload.
        budget: The shared work allowance, including preparation, computation, and result storage.
        variables: Core variable IDs in array-axis order; empty uses consecutive IDs. Imports normalize any valid core monomial order.

    Returns:
        A validated immutable array with copied coefficient storage.

    Raises:
        PolyError: DOMAIN for invalid or incompatible input, or LIMIT/CAPACITY on resource limits.
    """
    comptime assert ndim >= 0, "sparse core import needs a nonnegative axis count"
    var mapping = _variables(ndim, variables, budget)
    return NumericArray[_Shape[ndim], D](_ni._sparse(values, mapping, False, budget), budget)


def from_core[D: NumericDomain, *, ndim: Int = 1](values: NumericSparsePoly[D], *, max_steps: UInt64 = UInt64.MAX, variables: List[Int64] = List[Int64]()) raises PolyError -> NumericArray[_Shape[ndim], D]:
    """Validate and copy a numerical core polynomial without rounding its stored values.

    Parameters:
        D: The APN numerical domain associated with the stored scalars.
        ndim: The expected sparse axis count, including unused axes; defaults to one.

    Args:
        values: Input coefficients, sparse terms, or prepared values as required by this overload.
        max_steps: The complete call's work allowance; defaults to UInt64.MAX.
        variables: Core variable IDs in array-axis order; empty uses consecutive IDs. Imports normalize any valid core monomial order.

    Returns:
        A validated immutable array with copied coefficient storage.

    Raises:
        PolyError: DOMAIN for invalid or incompatible input, or LIMIT/CAPACITY on resource limits.
    """
    var budget = Budget(max_steps)
    return from_core[D, ndim=ndim](values, budget, variables=variables)


def degree_bound[P: Copyable & Deinitable, D: NumericDomain](values: NumericArray[P, D], mut budget: Budget) raises PolyError -> Int:
    """Return the stored degree bound.

    Parameters:
        P: The sparse power shape or retained source array type, inferred from the input.
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
    return values._core[].degree_bound(budget)


def degree_bound[P: Copyable & Deinitable, D: NumericDomain](values: NumericArray[P, D], *, max_steps: UInt64 = UInt64.MAX) raises PolyError -> Int:
    """Inspect the polynomial degree with a shared work allowance.

    Parameters:
        P: The sparse power shape or retained source array type, inferred from the input.
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


def certified_degree[P: Copyable & Deinitable, D: NumericDomain](values: NumericArray[P, D], mut budget: Budget) raises PolyError -> Optional[Int]:
    """Return a common degree for every represented polynomial, or None when uncertain.

    Parameters:
        P: The sparse power shape or retained source array type, inferred from the input.
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


def certified_degree[P: Copyable & Deinitable, D: NumericDomain](values: NumericArray[P, D], *, max_steps: UInt64 = UInt64.MAX) raises PolyError -> Optional[Int]:
    """Inspect the polynomial degree with a shared work allowance.

    Parameters:
        P: The sparse power shape or retained source array type, inferred from the input.
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


def evaluate[P: Copyable & Deinitable, D: NumericDomain, *Ts: Copyable & Deinitable](values: NumericArray[P, D], point: Tuple[*Ts], mut budget: Budget, *, context: D.Context) raises PolyError -> D.Scalar:
    """Evaluate a numerical sparse polynomial at an ordered coordinate tuple.

    Parameters:
        P: The sparse power shape or retained source array type, inferred from the input.
        D: The APN numerical domain associated with the stored scalars.
        Ts: The inferred tuple element types.

    Args:
        values: Input coefficients, sparse terms, or prepared values as required by this overload.
        point: The evaluation scalar or ordered coordinate tuple.
        budget: The shared work allowance, including preparation, computation, and result storage.
        context: Explicit output precision, rounding settings, or ball working precision.

    Returns:
        The evaluated scalar; algebraic results retain the evaluation proof.

    Raises:
        PolyError: DOMAIN for invalid or incompatible input, or LIMIT/CAPACITY on resource limits.
    """
    _num._context[D](context, budget)
    comptime assert Tuple[*Ts].Ts.length == _width[P](), "evaluation point has the wrong number of coordinates"
    _allocation[Tuple[Int64, D.Scalar]](_width[P](), budget)
    var assignments = List[Tuple[Int64, D.Scalar]](capacity=_width[P]())
    comptime for i in range(Tuple[*Ts].Ts.length):
        assignments.append((Int64(i), _num._value[D](point[i], context, budget)))
    return values._core[].evaluate(assignments, context, budget)


def evaluate[P: Copyable & Deinitable, D: NumericDomain, *Ts: Copyable & Deinitable](values: NumericArray[P, D], point: Tuple[*Ts], *, context: D.Context, max_steps: UInt64 = UInt64.MAX) raises PolyError -> D.Scalar:
    """Evaluate using the supplied precision and rounding context.

    Parameters:
        P: The sparse power shape or retained source array type, inferred from the input.
        D: The APN numerical domain associated with the stored scalars.
        Ts: The inferred tuple element types.

    Args:
        values: Input coefficients, sparse terms, or prepared values as required by this overload.
        point: The evaluation scalar or ordered coordinate tuple.
        context: Explicit output precision, rounding settings, or ball working precision.
        max_steps: The complete call's work allowance; defaults to UInt64.MAX.

    Returns:
        The evaluated scalar; algebraic results retain the evaluation proof.

    Raises:
        PolyError: DOMAIN for invalid or incompatible input, or LIMIT/CAPACITY on resource limits.
    """
    var budget = Budget(max_steps)
    return evaluate[P, D, *Ts](values, point, budget, context=context)


def evaluate[P: Copyable & Deinitable, D: NumericDomain, X: Copyable & Deinitable](values: NumericArray[P, D], point: X, mut budget: Budget, *, context: D.Context) raises PolyError -> D.Scalar where (_Kind[X] >= 0 or _num._IsNumeric[X]):
    """Evaluate a univariate numerical sparse polynomial at a scalar.

    Parameters:
        P: The sparse power shape or retained source array type, inferred from the input.
        D: The APN numerical domain associated with the stored scalars.
        X: The evaluation point or seed type.

    Args:
        values: Input coefficients, sparse terms, or prepared values as required by this overload.
        point: The evaluation scalar or ordered coordinate tuple.
        budget: The shared work allowance, including preparation, computation, and result storage.
        context: Explicit output precision, rounding settings, or ball working precision.

    Returns:
        The evaluated scalar; algebraic results retain the evaluation proof.

    Raises:
        PolyError: DOMAIN for invalid or incompatible input, or LIMIT/CAPACITY on resource limits.
    """
    _num._context[D](context, budget)
    comptime assert _width[P]() == 1, "a multivariate evaluation requires a coordinate tuple"
    return evaluate[P, D, X](values, (point.copy(),), budget, context=context)


def evaluate[P: Copyable & Deinitable, D: NumericDomain, X: Copyable & Deinitable](values: NumericArray[P, D], point: X, *, context: D.Context, max_steps: UInt64 = UInt64.MAX) raises PolyError -> D.Scalar where (_Kind[X] >= 0 or _num._IsNumeric[X]):
    """Evaluate a univariate numerical sparse polynomial at a scalar.

    Parameters:
        P: The sparse power shape or retained source array type, inferred from the input.
        D: The APN numerical domain associated with the stored scalars.
        X: The evaluation point or seed type.

    Args:
        values: Input coefficients, sparse terms, or prepared values as required by this overload.
        point: The evaluation scalar or ordered coordinate tuple.
        context: Explicit output precision, rounding settings, or ball working precision.
        max_steps: The complete call's work allowance; defaults to UInt64.MAX.

    Returns:
        The evaluated scalar; algebraic results retain the evaluation proof.

    Raises:
        PolyError: DOMAIN for invalid or incompatible input, or LIMIT/CAPACITY on resource limits.
    """
    var budget = Budget(max_steps)
    return evaluate[P, D, X](values, point, budget, context=context)


comptime _Evaluation[C: AnyType, Point: type_of(Tuple)] = _Scalar[_Join[_Kind[C], _TupleKind[Point]]]


from polynomials import numeric_substitute_many


def substitute[P: Copyable & Deinitable, D: NumericDomain, I: Iterable](values: NumericArray[P, D], assignments: I, mut budget: Budget, *, context: D.Context) raises PolyError -> NumericArray[P, D] where _Element[I] == Tuple[Int, NumericArray[P, D]]:
    """Substitute numerical polynomials simultaneously, retaining the original axes.

    Parameters:
        P: Inferred from the input types.
        D: The numerical coefficient domain.
        I: Inferred from the input types.

    Args:
        values: Coefficients, terms, or a prepared value.
        assignments: Distinct axis and replacement-polynomial pairs.
        budget: The shared work allowance.
        context: Explicit output precision and rounding or enclosure settings.

    Returns:
        The numerical polynomial in the same representation and variable layout.

    Raises:
        PolyError: DOMAIN for invalid input, or LIMIT/CAPACITY on resource limits.
    """
    _num._context[D](context, budget)
    var replacements = List[Tuple[Int64, NumericSparsePoly[D]]]()
    var cursor = iter(assignments)
    while True:
        budget.charge(1)
        var entry: Tuple[Int, NumericArray[P, D]]
        try:
            entry = rebind_var[Tuple[Int, NumericArray[P, D]]](next(cursor))
        except StopIteration:
            break
        if entry[0] < 0 or entry[0] >= _width[P]():
            raise PolyError(PolyErrorKind.DOMAIN, "substitution axis outside the power shape")
        _grow(replacements, budget)
        replacements.append((Int64(entry[0]), _num._copy_sparse(entry[1]._core[], _width[P](), budget)))
    var result = numeric_substitute_many(values._core[], replacements, context, budget)
    return NumericArray[P, D](result^, budget)


def substitute[P: Copyable & Deinitable, D: NumericDomain, I: Iterable](values: NumericArray[P, D], assignments: I, *, context: D.Context, max_steps: UInt64 = UInt64.MAX) raises PolyError -> NumericArray[P, D] where _Element[I] == Tuple[Int, NumericArray[P, D]]:
    """Substitute numerical polynomials simultaneously, retaining the original axes.

    Parameters:
        P: Inferred from the input types.
        D: The numerical coefficient domain.
        I: Inferred from the input types.

    Args:
        values: Coefficients, terms, or a prepared value.
        assignments: Distinct axis and replacement-polynomial pairs.
        context: Explicit output precision and rounding or enclosure settings.
        max_steps: The complete call's work allowance.

    Returns:
        The numerical polynomial in the same representation and variable layout.

    Raises:
        PolyError: DOMAIN for invalid input, or LIMIT/CAPACITY on resource limits.
    """
    var budget = Budget(max_steps)
    return substitute(values, assignments, budget, context=context)


def divmod[P: Copyable & Deinitable, D: NumericDomain](a: NumericArray[P, D], b: NumericArray[P, D], mut budget: Budget, *, context: D.Context) raises PolyError -> Tuple[NumericArray[P, D], NumericArray[P, D]]:
    """Divide univariate numerical sparse polynomials into quotient and remainder.

    Conversion charges the complete dense extent before allocation.

    Parameters:
        P: Inferred from the input types.
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
    from ._conversion import to_dense, to_sparse
    comptime assert _width[P]() == 1, "this numerical sparse operation requires one variable"
    var x = to_dense(a, budget, context=context)
    var y = to_dense(b, budget, context=context)
    var result = _dense.divmod(x, y, budget, context=context)
    var q = to_sparse(result[0], budget, context=context)
    var r = to_sparse(result[1], budget, context=context)
    return NumericArray[P, D](_num._copy_sparse(q._core[], 1, budget), budget), NumericArray[P, D](_num._copy_sparse(r._core[], 1, budget), budget)


def divmod[P: Copyable & Deinitable, D: NumericDomain](a: NumericArray[P, D], b: NumericArray[P, D], *, context: D.Context, max_steps: UInt64 = UInt64.MAX) raises PolyError -> Tuple[NumericArray[P, D], NumericArray[P, D]]:
    """Divide univariate numerical sparse polynomials into quotient and remainder.

    Conversion charges the complete dense extent before allocation.

    Parameters:
        P: Inferred from the input types.
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


def compose[P: Copyable & Deinitable, D: NumericDomain](a: NumericArray[P, D], b: NumericArray[P, D], mut budget: Budget, *, context: D.Context) raises PolyError -> NumericArray[P, D]:
    """Compose univariate numerical sparse polynomials.

    Conversion charges the complete dense extent before allocation.

    Parameters:
        P: Inferred from the input types.
        D: The numerical coefficient domain.

    Args:
        a: The first prepared value.
        b: The second prepared value.
        budget: The shared work allowance.
        context: Explicit output precision and rounding or enclosure settings.

    Returns:
        The numerical polynomial in the same representation and variable layout.

    Raises:
        PolyError: DOMAIN for invalid input, or LIMIT/CAPACITY on resource limits.
    """
    from ._conversion import to_dense, to_sparse
    comptime assert _width[P]() == 1, "this numerical sparse operation requires one variable"
    var x = to_dense(a, budget, context=context)
    var y = to_dense(b, budget, context=context)
    var result = _dense.compose(x, y, budget, context=context)
    var converted = to_sparse(result, budget, context=context)
    return NumericArray[P, D](_num._copy_sparse(converted._core[], 1, budget), budget)


def compose[P: Copyable & Deinitable, D: NumericDomain](a: NumericArray[P, D], b: NumericArray[P, D], *, context: D.Context, max_steps: UInt64 = UInt64.MAX) raises PolyError -> NumericArray[P, D]:
    """Compose univariate numerical sparse polynomials.

    Conversion charges the complete dense extent before allocation.

    Parameters:
        P: Inferred from the input types.
        D: The numerical coefficient domain.

    Args:
        a: The first prepared value.
        b: The second prepared value.
        context: Explicit output precision and rounding or enclosure settings.
        max_steps: The complete call's work allowance.

    Returns:
        The numerical polynomial in the same representation and variable layout.

    Raises:
        PolyError: DOMAIN for invalid input, or LIMIT/CAPACITY on resource limits.
    """
    var budget = Budget(max_steps)
    return compose(a, b, budget, context=context)


def jet_evaluate[P: Copyable & Deinitable, D: NumericDomain, X: Copyable & Deinitable](values: NumericArray[P, D], point: X, order: Int, mut budget: Budget, *, context: D.Context) raises PolyError -> _num.Values[D]:
    """Return consecutive Taylor coefficients of a univariate sparse polynomial.

    Conversion charges the complete dense extent before allocation.

    Parameters:
        P: Inferred from the input types.
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
    from ._conversion import to_dense, to_sparse
    comptime assert _width[P]() == 1, "this numerical sparse operation requires one variable"
    var x = to_dense(values, budget, context=context)
    var result = _dense.jet_evaluate(x, point, order, budget, context=context)
    return result^


def jet_evaluate[P: Copyable & Deinitable, D: NumericDomain, X: Copyable & Deinitable](values: NumericArray[P, D], point: X, order: Int, *, context: D.Context, max_steps: UInt64 = UInt64.MAX) raises PolyError -> _num.Values[D]:
    """Return consecutive Taylor coefficients of a univariate sparse polynomial.

    Conversion charges the complete dense extent before allocation.

    Parameters:
        P: Inferred from the input types.
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


def evaluate_many[P: Copyable & Deinitable, D: NumericDomain, I: Iterable, *Ts: Copyable & Deinitable](values: NumericArray[P, D], points: I, mut budget: Budget, *, context: D.Context) raises PolyError -> _num.Values[D] where _Element[I] == Tuple[*Ts]:
    """Evaluate numerical sparse arrays at a sequence of points.

    Parameters:
        P: Inferred from the input types.
        D: The numerical coefficient domain.
        I: Inferred from the input types.
        Ts: Inferred from the input types.

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
    _num._context[D](context, budget)
    _num._check_sequence(points)
    var result = List[D.Scalar]()
    var cursor = iter(points)
    while True:
        budget.charge(1)
        var point: Tuple[*Ts]
        try:
            point = rebind_var[Tuple[*Ts]](next(cursor))
        except StopIteration:
            break
        _grow(result, budget)
        result.append(evaluate[P, D, *Ts](values, point, budget, context=context))
    return _num.Values[D](result^, budget)


def evaluate_many[P: Copyable & Deinitable, D: NumericDomain, I: Iterable, *Ts: Copyable & Deinitable](values: NumericArray[P, D], points: I, *, context: D.Context, max_steps: UInt64 = UInt64.MAX) raises PolyError -> _num.Values[D] where _Element[I] == Tuple[*Ts]:
    """Evaluate numerical sparse arrays at a sequence of points.

    Parameters:
        P: Inferred from the input types.
        D: The numerical coefficient domain.
        I: Inferred from the input types.
        Ts: Inferred from the input types.

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
    return evaluate_many[P, D, I, *Ts](values, points, budget, context=context)


def evaluate_many[P: Copyable & Deinitable, D: NumericDomain, I: Iterable, X: Copyable & Deinitable](values: NumericArray[P, D], points: I, mut budget: Budget, *, context: D.Context) raises PolyError -> _num.Values[D] where (_Element[I] == X and (_Kind[X] >= 0 or _num._IsNumeric[X])):
    """Evaluate numerical sparse arrays at a sequence of points.

    Parameters:
        P: Inferred from the input types.
        D: The numerical coefficient domain.
        I: Inferred from the input types.
        X: Inferred from the input types.

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
    _num._context[D](context, budget)
    _num._check_sequence(points)
    var result = List[D.Scalar]()
    var cursor = iter(points)
    while True:
        budget.charge(1)
        var point: X
        try:
            point = rebind_var[X](next(cursor))
        except StopIteration:
            break
        _grow(result, budget)
        result.append(evaluate[P, D, X](values, point, budget, context=context))
    return _num.Values[D](result^, budget)


def evaluate_many[P: Copyable & Deinitable, D: NumericDomain, I: Iterable, X: Copyable & Deinitable](values: NumericArray[P, D], points: I, *, context: D.Context, max_steps: UInt64 = UInt64.MAX) raises PolyError -> _num.Values[D] where (_Element[I] == X and (_Kind[X] >= 0 or _num._IsNumeric[X])):
    """Evaluate numerical sparse arrays at a sequence of points.

    Parameters:
        P: Inferred from the input types.
        D: The numerical coefficient domain.
        I: Inferred from the input types.
        X: Inferred from the input types.

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
    return evaluate_many[P, D, I, X](values, points, budget, context=context)


def real_roots[P: Copyable & Deinitable](values: _alg.Specialization[P], mut budget: Budget, *, axis: Int = 0) raises PolyError -> _roots.SpecializedRoots[P]:
    """Find every distinct real root of a univariate specialization.

    Parameters:
        P: Inferred from the input types.

    Args:
        values: Coefficients, terms, or a prepared value.
        budget: The shared work allowance.
        axis: The zero-based variable axis.

    Returns:
        All distinct real roots in increasing order, with specialization and completeness evidence.

    Raises:
        PolyError: DOMAIN for invalid input, or LIMIT/CAPACITY on resource limits.
    """
    if axis < 0 or axis >= _width[P]():
        raise PolyError(PolyErrorKind.DOMAIN, "root axis outside the power shape")
    for assignment in values._data[].point:
        budget.charge(1)
        if assignment[0] == Int64(axis):
            raise PolyError(PolyErrorKind.DOMAIN, "root axis must remain unassigned")
    var coefficients = _alg.coefficients(values, budget, axis=axis)
    var result = _roots._exact_coefficients(coefficients, budget)
    return _roots.SpecializedRoots[P](values.copy(), result^, axis)


def real_roots[P: Copyable & Deinitable](values: _alg.Specialization[P], *, axis: Int = 0, max_steps: UInt64 = UInt64.MAX) raises PolyError -> _roots.SpecializedRoots[P]:
    """Find every distinct real root of a univariate specialization.

    Parameters:
        P: Inferred from the input types.

    Args:
        values: Coefficients, terms, or a prepared value.
        axis: The zero-based variable axis.
        max_steps: The complete call's work allowance.

    Returns:
        All distinct real roots in increasing order, with specialization and completeness evidence.

    Raises:
        PolyError: DOMAIN for invalid input, or LIMIT/CAPACITY on resource limits.
    """
    var budget = Budget(max_steps)
    return real_roots(values, budget, axis=axis)


comptime _RootsAt[P: Copyable & Deinitable, C: Copyable & Deinitable, X: Copyable & Deinitable] = _roots.SpecializedRoots[P, 4] if _Kind[C] == 4 else _roots.SpecializedRoots[P]


def roots_at[I: Iterable, A: Iterable, P: Copyable & Deinitable, C: Copyable & Deinitable, X: Copyable & Deinitable](values: I, assignments: A, mut budget: Budget, *, axis: Int = 0) raises PolyError -> _RootsAt[P, C, X] where (_Element[I] == Tuple[P, C] and _Element[A] == Tuple[Int, X]):
    """Specialize all other occurring variables and find the remaining real roots.

    Parameters:
        I: Inferred from the input types.
        A: Inferred from the input types.
        P: Inferred from the input types.
        C: Inferred from the input types.
        X: Inferred from the input types.

    Args:
        values: Coefficients, terms, or a prepared value.
        assignments: Distinct axis and exact-real-value pairs; leave the root axis unassigned.
        budget: The shared work allowance.
        axis: The zero-based variable axis.

    Returns:
        All distinct real roots in increasing order, with specialization and completeness evidence.

    Raises:
        PolyError: DOMAIN for invalid input, or LIMIT/CAPACITY on resource limits.
    """
    comptime assert (_Kind[C] == 0 or _Kind[C] == 1 or _Kind[C] == 4) and (_Kind[X] == 0 or _Kind[X] == 1 or _Kind[X] == 4), "real roots require exact real coefficients and assignments"
    _axis[P](axis)
    var saved = List[Tuple[Int, X]]()
    var cursor = iter(assignments)
    while True:
        budget.charge(1)
        var entry: Tuple[Int, X]
        try:
            entry = rebind_var[Tuple[Int, X]](next(cursor))
        except StopIteration:
            break
        _grow(saved, budget)
        saved.append(entry^)
    for entry in saved:
        if entry[0] == axis:
            raise PolyError(PolyErrorKind.DOMAIN, "root axis must remain unassigned")
    var prepared = specialize[I, List[Tuple[Int, X]], P, C, X](values, saved, budget)
    comptime if _Specialized[P, C, X] == _alg.Specialization[P]:
        return rebind_var[_RootsAt[P, C, X]](real_roots(rebind[_alg.Specialization[P]](prepared), budget, axis=axis))
    else:
        return rebind_var[_RootsAt[P, C, X]](real_roots(rebind[_alg.AlgebraicSpecialization[P]](prepared), budget, axis=axis))


def roots_at[I: Iterable, A: Iterable, P: Copyable & Deinitable, C: Copyable & Deinitable, X: Copyable & Deinitable](values: I, assignments: A, *, axis: Int = 0, max_steps: UInt64 = UInt64.MAX) raises PolyError -> _RootsAt[P, C, X] where (_Element[I] == Tuple[P, C] and _Element[A] == Tuple[Int, X]):
    """Specialize all other occurring variables and find the remaining real roots.

    Parameters:
        I: Inferred from the input types.
        A: Inferred from the input types.
        P: Inferred from the input types.
        C: Inferred from the input types.
        X: Inferred from the input types.

    Args:
        values: Coefficients, terms, or a prepared value.
        assignments: Distinct axis and exact-real-value pairs; leave the root axis unassigned.
        axis: The zero-based variable axis.
        max_steps: The complete call's work allowance.

    Returns:
        All distinct real roots in increasing order, with specialization and completeness evidence.

    Raises:
        PolyError: DOMAIN for invalid input, or LIMIT/CAPACITY on resource limits.
    """
    var budget = Budget(max_steps)
    return roots_at[I, A, P, C, X](values, assignments, budget, axis=axis)


from . import evaluation as _evaluation
from apn_mojo import BallContext


def enclose[I: Iterable, P: Copyable & Deinitable, C: Copyable & Deinitable, *Ts: Copyable & Deinitable](values: I, point: Tuple[*Ts], mut budget: Budget, *, context: BallContext) raises PolyError -> _evaluation.Enclosure[_Ring[_Kind[C]], _evaluation._Domain[C, _num._TupleScalar[Tuple[*Ts]]], False, True] where (_Element[I] == Tuple[P, C] and _Kind[C] >= 0):
    """Evaluate with an independently checkable enclosure.

    Inputs remain unchanged. Exact algebraic coefficients and points retain root witnesses for independent conversion checks. Adaptive calls refine exact algebraic coefficients while preserving supplied numerical uncertainty.

    Parameters:
        I: Inferred from the input types.
        P: Inferred from the input types.
        C: Inferred from the input types.
        Ts: Inferred from the input types.

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
    comptime E = _evaluation._Domain[C, _num._TupleScalar[Tuple[*Ts]]]
    comptime assert Tuple[*Ts].Ts.length == _width[P](), "evaluation point has the wrong number of coordinates"
    comptime assert _Kind[C] >= 0 and _Kind[C] != 3, "enclosure evaluation requires characteristic-zero exact coefficients"
    _num._context[E](rebind[E.Context](context), budget)
    var point_witnesses = List[_evaluation._Point[E]]()
    _allocation[Tuple[Int64, E.Scalar]](_width[P](), budget)
    var arguments = List[Tuple[Int64, E.Scalar]](capacity=_width[P]())
    comptime for i in range(Tuple[*Ts].Ts.length):
        arguments.append((Int64(i), _evaluation._argument[E](point[i], Int64(i), rebind[E.Context](context), point_witnesses, budget)))
    var p = to_core[I, P, C](values, budget)
    return _evaluation._compute[_Ring[_Kind[C]], E, False, True](p^, arguments^, context, Optional[NumericOptions](), budget, point_witnesses^)


def enclose[I: Iterable, P: Copyable & Deinitable, C: Copyable & Deinitable, *Ts: Copyable & Deinitable](values: I, point: Tuple[*Ts], *, context: BallContext, max_steps: UInt64 = UInt64.MAX) raises PolyError -> _evaluation.Enclosure[_Ring[_Kind[C]], _evaluation._Domain[C, _num._TupleScalar[Tuple[*Ts]]], False, True] where (_Element[I] == Tuple[P, C] and _Kind[C] >= 0):
    """Evaluate with an independently checkable enclosure.

    Inputs remain unchanged. Exact algebraic coefficients and points retain root witnesses for independent conversion checks. Adaptive calls refine exact algebraic coefficients while preserving supplied numerical uncertainty.

    Parameters:
        I: Inferred from the input types.
        P: Inferred from the input types.
        C: Inferred from the input types.
        Ts: Inferred from the input types.

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
    return enclose[I, P, C, *Ts](values, point, budget, context=context)


def adaptive_evaluate[I: Iterable, P: Copyable & Deinitable, C: Copyable & Deinitable, *Ts: Copyable & Deinitable](values: I, point: Tuple[*Ts], mut budget: Budget, *, options: NumericOptions) raises PolyError -> _evaluation.Enclosure[_Ring[_Kind[C]], _evaluation._Domain[C, _num._TupleScalar[Tuple[*Ts]]], False, True] where (_Element[I] == Tuple[P, C] and _Kind[C] >= 0):
    """Evaluate with an independently checkable enclosure and a requested accuracy.

    Inputs remain unchanged. Exact algebraic coefficients and points retain root witnesses for independent conversion checks. Adaptive calls refine exact algebraic coefficients while preserving supplied numerical uncertainty.

    Parameters:
        I: Inferred from the input types.
        P: Inferred from the input types.
        C: Inferred from the input types.
        Ts: Inferred from the input types.

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
    comptime E = _evaluation._Domain[C, _num._TupleScalar[Tuple[*Ts]]]
    comptime assert Tuple[*Ts].Ts.length == _width[P](), "evaluation point has the wrong number of coordinates"
    comptime assert _Kind[C] >= 0 and _Kind[C] != 3, "enclosure evaluation requires characteristic-zero exact coefficients"
    _evaluation._options(options)
    var context = _evaluation._context(options.max_precision, options.max_precision)
    _num._context[E](rebind[E.Context](context), budget)
    var point_witnesses = List[_evaluation._Point[E]]()
    _allocation[Tuple[Int64, E.Scalar]](_width[P](), budget)
    var arguments = List[Tuple[Int64, E.Scalar]](capacity=_width[P]())
    comptime for i in range(Tuple[*Ts].Ts.length):
        arguments.append((Int64(i), _evaluation._argument[E](point[i], Int64(i), rebind[E.Context](context), point_witnesses, budget)))
    var p = to_core[I, P, C](values, budget)
    return _evaluation._compute[_Ring[_Kind[C]], E, False, True](p^, arguments^, context, Optional(options), budget, point_witnesses^)


def adaptive_evaluate[I: Iterable, P: Copyable & Deinitable, C: Copyable & Deinitable, *Ts: Copyable & Deinitable](values: I, point: Tuple[*Ts], *, options: NumericOptions, max_steps: UInt64 = UInt64.MAX) raises PolyError -> _evaluation.Enclosure[_Ring[_Kind[C]], _evaluation._Domain[C, _num._TupleScalar[Tuple[*Ts]]], False, True] where (_Element[I] == Tuple[P, C] and _Kind[C] >= 0):
    """Evaluate with an independently checkable enclosure and a requested accuracy.

    Inputs remain unchanged. Exact algebraic coefficients and points retain root witnesses for independent conversion checks. Adaptive calls refine exact algebraic coefficients while preserving supplied numerical uncertainty.

    Parameters:
        I: Inferred from the input types.
        P: Inferred from the input types.
        C: Inferred from the input types.
        Ts: Inferred from the input types.

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
    return adaptive_evaluate[I, P, C, *Ts](values, point, budget, options=options)


def enclose[P: Copyable & Deinitable, D: NumericDomain, *Ts: Copyable & Deinitable](values: NumericArray[P, D], point: Tuple[*Ts], mut budget: Budget, *, context: BallContext) raises PolyError -> _evaluation.Enclosure[D, _evaluation._Domain[D.Scalar, _num._TupleScalar[Tuple[*Ts]]], True, True]:
    """Evaluate with an independently checkable enclosure.

    Inputs remain unchanged. Exact algebraic coefficients and points retain root witnesses for independent conversion checks. Adaptive calls refine exact algebraic coefficients while preserving supplied numerical uncertainty.

    Parameters:
        P: Inferred from the input types.
        D: The numerical coefficient domain.
        Ts: Inferred from the input types.

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
    comptime E = _evaluation._Domain[D.Scalar, _num._TupleScalar[Tuple[*Ts]]]
    comptime assert Tuple[*Ts].Ts.length == _width[P](), "evaluation point has the wrong number of coordinates"
    _num._context[E](rebind[E.Context](context), budget)
    var point_witnesses = List[_evaluation._Point[E]]()
    _allocation[Tuple[Int64, E.Scalar]](_width[P](), budget)
    var arguments = List[Tuple[Int64, E.Scalar]](capacity=_width[P]())
    comptime for i in range(Tuple[*Ts].Ts.length):
        arguments.append((Int64(i), _evaluation._argument[E](point[i], Int64(i), rebind[E.Context](context), point_witnesses, budget)))
    var p = _num._copy_sparse(values._core[], _width[P](), budget)
    return _evaluation._compute[D, E, True, True](p^, arguments^, context, Optional[NumericOptions](), budget, point_witnesses^)


def enclose[P: Copyable & Deinitable, D: NumericDomain, *Ts: Copyable & Deinitable](values: NumericArray[P, D], point: Tuple[*Ts], *, context: BallContext, max_steps: UInt64 = UInt64.MAX) raises PolyError -> _evaluation.Enclosure[D, _evaluation._Domain[D.Scalar, _num._TupleScalar[Tuple[*Ts]]], True, True]:
    """Evaluate with an independently checkable enclosure.

    Inputs remain unchanged. Exact algebraic coefficients and points retain root witnesses for independent conversion checks. Adaptive calls refine exact algebraic coefficients while preserving supplied numerical uncertainty.

    Parameters:
        P: Inferred from the input types.
        D: The numerical coefficient domain.
        Ts: Inferred from the input types.

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
    return enclose[P, D, *Ts](values, point, budget, context=context)


def adaptive_evaluate[P: Copyable & Deinitable, D: NumericDomain, *Ts: Copyable & Deinitable](values: NumericArray[P, D], point: Tuple[*Ts], mut budget: Budget, *, options: NumericOptions) raises PolyError -> _evaluation.Enclosure[D, _evaluation._Domain[D.Scalar, _num._TupleScalar[Tuple[*Ts]]], True, True]:
    """Evaluate with an independently checkable enclosure and a requested accuracy.

    Inputs remain unchanged. Exact algebraic coefficients and points retain root witnesses for independent conversion checks. Adaptive calls refine exact algebraic coefficients while preserving supplied numerical uncertainty.

    Parameters:
        P: Inferred from the input types.
        D: The numerical coefficient domain.
        Ts: Inferred from the input types.

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
    comptime E = _evaluation._Domain[D.Scalar, _num._TupleScalar[Tuple[*Ts]]]
    comptime assert Tuple[*Ts].Ts.length == _width[P](), "evaluation point has the wrong number of coordinates"
    _evaluation._options(options)
    var context = _evaluation._context(options.max_precision, options.max_precision)
    _num._context[E](rebind[E.Context](context), budget)
    var point_witnesses = List[_evaluation._Point[E]]()
    _allocation[Tuple[Int64, E.Scalar]](_width[P](), budget)
    var arguments = List[Tuple[Int64, E.Scalar]](capacity=_width[P]())
    comptime for i in range(Tuple[*Ts].Ts.length):
        arguments.append((Int64(i), _evaluation._argument[E](point[i], Int64(i), rebind[E.Context](context), point_witnesses, budget)))
    var p = _num._copy_sparse(values._core[], _width[P](), budget)
    return _evaluation._compute[D, E, True, True](p^, arguments^, context, Optional(options), budget, point_witnesses^)


def adaptive_evaluate[P: Copyable & Deinitable, D: NumericDomain, *Ts: Copyable & Deinitable](values: NumericArray[P, D], point: Tuple[*Ts], *, options: NumericOptions, max_steps: UInt64 = UInt64.MAX) raises PolyError -> _evaluation.Enclosure[D, _evaluation._Domain[D.Scalar, _num._TupleScalar[Tuple[*Ts]]], True, True]:
    """Evaluate with an independently checkable enclosure and a requested accuracy.

    Inputs remain unchanged. Exact algebraic coefficients and points retain root witnesses for independent conversion checks. Adaptive calls refine exact algebraic coefficients while preserving supplied numerical uncertainty.

    Parameters:
        P: Inferred from the input types.
        D: The numerical coefficient domain.
        Ts: Inferred from the input types.

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
    return adaptive_evaluate[P, D, *Ts](values, point, budget, options=options)


from polynomials import NumericTerm


def _numeric_replace_axis[P: Copyable & Deinitable, D: NumericDomain, X: Copyable & Deinitable, Y: Copyable & Deinitable](values: NumericArray[P, D], scale: X, shift: Y, axis: Int, context: D.Context, mut budget: Budget) raises PolyError -> NumericArray[P, D]:
    _axis[P](axis)
    _num._context[D](context, budget)
    _allocation[NumericTerm[D]](2, budget)
    _allocation[Tuple[Int64, UInt32]](1, budget)
    var terms: List[NumericTerm[D]] = [NumericTerm[D](Monomial(), _num._value[D](shift, context, budget)), NumericTerm[D](Monomial([(Int64(axis), UInt32(1))], budget), _num._value[D](scale, context, budget))]
    var replacement = NumericSparsePoly[D].from_terms(terms^, values._core[].order, context, budget)
    _allocation[Tuple[Int64, NumericSparsePoly[D]]](1, budget)
    var assignments: List[Tuple[Int64, NumericSparsePoly[D]]] = [(Int64(axis), replacement^)]
    var result = numeric_substitute_many(values._core[], assignments, context, budget)
    return NumericArray[P, D](result^, budget)


def affine_transform[P: Copyable & Deinitable, D: NumericDomain, X: Copyable & Deinitable, Y: Copyable & Deinitable](values: NumericArray[P, D], scale: X, shift: Y, mut budget: Budget, *, context: D.Context, axis: Int = 0) raises PolyError -> NumericArray[P, D]:
    """Replace one numerical variable by scale*x + shift, retaining all axes.

    Parameters:
        P: Inferred from the input types.
        D: The numerical coefficient domain.
        X: Inferred from the input types.
        Y: Inferred from the input types.

    Args:
        values: Coefficients, terms, or a prepared value.
        scale: The affine scale.
        shift: The affine shift.
        budget: The shared work allowance.
        context: Explicit output precision and rounding or enclosure settings.
        axis: The zero-based variable axis.

    Returns:
        The numerical polynomial in the same representation and variable layout.

    Raises:
        PolyError: DOMAIN for invalid input, or LIMIT/CAPACITY on resource limits.
    """
    return _numeric_replace_axis(values, scale, shift, axis, context, budget)


def affine_transform[P: Copyable & Deinitable, D: NumericDomain, X: Copyable & Deinitable, Y: Copyable & Deinitable](values: NumericArray[P, D], scale: X, shift: Y, *, context: D.Context, axis: Int = 0, max_steps: UInt64 = UInt64.MAX) raises PolyError -> NumericArray[P, D]:
    """Replace one numerical variable by scale*x + shift, retaining all axes.

    Parameters:
        P: Inferred from the input types.
        D: The numerical coefficient domain.
        X: Inferred from the input types.
        Y: Inferred from the input types.

    Args:
        values: Coefficients, terms, or a prepared value.
        scale: The affine scale.
        shift: The affine shift.
        context: Explicit output precision and rounding or enclosure settings.
        axis: The zero-based variable axis.
        max_steps: The complete call's work allowance.

    Returns:
        The numerical polynomial in the same representation and variable layout.

    Raises:
        PolyError: DOMAIN for invalid input, or LIMIT/CAPACITY on resource limits.
    """
    var budget = Budget(max_steps)
    return affine_transform(values, scale, shift, budget, context=context, axis=axis)


def taylor_shift[P: Copyable & Deinitable, D: NumericDomain, X: Copyable & Deinitable](values: NumericArray[P, D], point: X, mut budget: Budget, *, context: D.Context, axis: Int = 0) raises PolyError -> NumericArray[P, D]:
    """Shift one numerical variable by a scalar, retaining all axes.

    Parameters:
        P: Inferred from the input types.
        D: The numerical coefficient domain.
        X: Inferred from the input types.

    Args:
        values: Coefficients, terms, or a prepared value.
        point: The evaluation or expansion point.
        budget: The shared work allowance.
        context: Explicit output precision and rounding or enclosure settings.
        axis: The zero-based variable axis.

    Returns:
        The numerical polynomial in the same representation and variable layout.

    Raises:
        PolyError: DOMAIN for invalid input, or LIMIT/CAPACITY on resource limits.
    """
    return _numeric_replace_axis(values, 1, point, axis, context, budget)


def taylor_shift[P: Copyable & Deinitable, D: NumericDomain, X: Copyable & Deinitable](values: NumericArray[P, D], point: X, *, context: D.Context, axis: Int = 0, max_steps: UInt64 = UInt64.MAX) raises PolyError -> NumericArray[P, D]:
    """Shift one numerical variable by a scalar, retaining all axes.

    Parameters:
        P: Inferred from the input types.
        D: The numerical coefficient domain.
        X: Inferred from the input types.

    Args:
        values: Coefficients, terms, or a prepared value.
        point: The evaluation or expansion point.
        context: Explicit output precision and rounding or enclosure settings.
        axis: The zero-based variable axis.
        max_steps: The complete call's work allowance.

    Returns:
        The numerical polynomial in the same representation and variable layout.

    Raises:
        PolyError: DOMAIN for invalid input, or LIMIT/CAPACITY on resource limits.
    """
    var budget = Budget(max_steps)
    return taylor_shift(values, point, budget, context=context, axis=axis)


def definite_integral[P: Copyable & Deinitable, D: NumericDomain, X: Copyable & Deinitable, Y: Copyable & Deinitable](values: NumericArray[P, D], low: X, high: Y, mut budget: Budget, *, context: D.Context, axis: Int = 0) raises PolyError -> NumericArray[P, D]:
    """Integrate out one numerical axis between scalar endpoints.

    The output retains the sparse power shape with exponent zero on the integrated axis.

    Parameters:
        P: Inferred from the input types.
        D: The numerical coefficient domain.
        X: Inferred from the input types.
        Y: Inferred from the input types.

    Args:
        values: Coefficients, terms, or a prepared value.
        low: The lower integration endpoint.
        high: The upper integration endpoint.
        budget: The shared work allowance.
        context: Explicit output precision and rounding or enclosure settings.
        axis: The zero-based variable axis.

    Returns:
        The numerical polynomial in the same representation and variable layout.

    Raises:
        PolyError: DOMAIN for invalid input, or LIMIT/CAPACITY on resource limits.
    """
    _axis[P](axis)
    var integrated = integral(values, budget, context=context, axis=axis)
    var upper = _numeric_replace_axis(integrated, 0, high, axis, context, budget)
    var lower = _numeric_replace_axis(integrated, 0, low, axis, context, budget)
    return subtract(upper, lower, budget, context=context)


def definite_integral[P: Copyable & Deinitable, D: NumericDomain, X: Copyable & Deinitable, Y: Copyable & Deinitable](values: NumericArray[P, D], low: X, high: Y, *, context: D.Context, axis: Int = 0, max_steps: UInt64 = UInt64.MAX) raises PolyError -> NumericArray[P, D]:
    """Integrate out one numerical axis between scalar endpoints.

    The output retains the sparse power shape with exponent zero on the integrated axis.

    Parameters:
        P: Inferred from the input types.
        D: The numerical coefficient domain.
        X: Inferred from the input types.
        Y: Inferred from the input types.

    Args:
        values: Coefficients, terms, or a prepared value.
        low: The lower integration endpoint.
        high: The upper integration endpoint.
        context: Explicit output precision and rounding or enclosure settings.
        axis: The zero-based variable axis.
        max_steps: The complete call's work allowance.

    Returns:
        The numerical polynomial in the same representation and variable layout.

    Raises:
        PolyError: DOMAIN for invalid input, or LIMIT/CAPACITY on resource limits.
    """
    var budget = Budget(max_steps)
    return definite_integral(values, low, high, budget, context=context, axis=axis)


def enclose[I: Iterable, P: Copyable & Deinitable, C: Copyable & Deinitable, X: Copyable & Deinitable](values: I, point: X, mut budget: Budget, *, context: BallContext) raises PolyError -> _evaluation.Enclosure[_Ring[_Kind[C]], _evaluation._Domain[C, X], False, True] where (_Element[I] == Tuple[P, C] and _Kind[C] >= 0 and (_Kind[X] >= 0 or _num._IsNumeric[X])):
    """Enclose a univariate sparse polynomial at a scalar argument.

    Parameters:
        I: Inferred from the input types.
        P: Inferred from the input types.
        C: Inferred from the input types.
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
    comptime assert _width[P]() == 1, "scalar enclosure evaluation requires one variable"
    return rebind_var[_evaluation.Enclosure[_Ring[_Kind[C]], _evaluation._Domain[C, X], False, True]](enclose[I, P, C, X](values, (point.copy(),), budget, context=context))


def enclose[I: Iterable, P: Copyable & Deinitable, C: Copyable & Deinitable, X: Copyable & Deinitable](values: I, point: X, *, context: BallContext, max_steps: UInt64 = UInt64.MAX) raises PolyError -> _evaluation.Enclosure[_Ring[_Kind[C]], _evaluation._Domain[C, X], False, True] where (_Element[I] == Tuple[P, C] and _Kind[C] >= 0 and (_Kind[X] >= 0 or _num._IsNumeric[X])):
    """Enclose a univariate sparse polynomial at a scalar argument.

    Parameters:
        I: Inferred from the input types.
        P: Inferred from the input types.
        C: Inferred from the input types.
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
    return enclose[I, P, C, X](values, point, budget, context=context)


def adaptive_evaluate[I: Iterable, P: Copyable & Deinitable, C: Copyable & Deinitable, X: Copyable & Deinitable](values: I, point: X, mut budget: Budget, *, options: NumericOptions) raises PolyError -> _evaluation.Enclosure[_Ring[_Kind[C]], _evaluation._Domain[C, X], False, True] where (_Element[I] == Tuple[P, C] and _Kind[C] >= 0 and (_Kind[X] >= 0 or _num._IsNumeric[X])):
    """Enclose a univariate sparse polynomial at a scalar argument.

    Parameters:
        I: Inferred from the input types.
        P: Inferred from the input types.
        C: Inferred from the input types.
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
    comptime assert _width[P]() == 1, "scalar enclosure evaluation requires one variable"
    return rebind_var[_evaluation.Enclosure[_Ring[_Kind[C]], _evaluation._Domain[C, X], False, True]](adaptive_evaluate[I, P, C, X](values, (point.copy(),), budget, options=options))


def adaptive_evaluate[I: Iterable, P: Copyable & Deinitable, C: Copyable & Deinitable, X: Copyable & Deinitable](values: I, point: X, *, options: NumericOptions, max_steps: UInt64 = UInt64.MAX) raises PolyError -> _evaluation.Enclosure[_Ring[_Kind[C]], _evaluation._Domain[C, X], False, True] where (_Element[I] == Tuple[P, C] and _Kind[C] >= 0 and (_Kind[X] >= 0 or _num._IsNumeric[X])):
    """Enclose a univariate sparse polynomial at a scalar argument.

    Parameters:
        I: Inferred from the input types.
        P: Inferred from the input types.
        C: Inferred from the input types.
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
    return adaptive_evaluate[I, P, C, X](values, point, budget, options=options)


def enclose[P: Copyable & Deinitable, D: NumericDomain, X: Copyable & Deinitable](values: NumericArray[P, D], point: X, mut budget: Budget, *, context: BallContext) raises PolyError -> _evaluation.Enclosure[D, _evaluation._Domain[D.Scalar, X], True, True] where (_Kind[X] >= 0 or _num._IsNumeric[X]):
    """Enclose a univariate sparse polynomial at a scalar argument.

    Parameters:
        P: Inferred from the input types.
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
    comptime assert _width[P]() == 1, "scalar enclosure evaluation requires one variable"
    return rebind_var[_evaluation.Enclosure[D, _evaluation._Domain[D.Scalar, X], True, True]](enclose[P, D, X](values, (point.copy(),), budget, context=context))


def enclose[P: Copyable & Deinitable, D: NumericDomain, X: Copyable & Deinitable](values: NumericArray[P, D], point: X, *, context: BallContext, max_steps: UInt64 = UInt64.MAX) raises PolyError -> _evaluation.Enclosure[D, _evaluation._Domain[D.Scalar, X], True, True] where (_Kind[X] >= 0 or _num._IsNumeric[X]):
    """Enclose a univariate sparse polynomial at a scalar argument.

    Parameters:
        P: Inferred from the input types.
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
    return enclose[P, D, X](values, point, budget, context=context)


def adaptive_evaluate[P: Copyable & Deinitable, D: NumericDomain, X: Copyable & Deinitable](values: NumericArray[P, D], point: X, mut budget: Budget, *, options: NumericOptions) raises PolyError -> _evaluation.Enclosure[D, _evaluation._Domain[D.Scalar, X], True, True] where (_Kind[X] >= 0 or _num._IsNumeric[X]):
    """Enclose a univariate sparse polynomial at a scalar argument.

    Parameters:
        P: Inferred from the input types.
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
    comptime assert _width[P]() == 1, "scalar enclosure evaluation requires one variable"
    return rebind_var[_evaluation.Enclosure[D, _evaluation._Domain[D.Scalar, X], True, True]](adaptive_evaluate[P, D, X](values, (point.copy(),), budget, options=options))


def adaptive_evaluate[P: Copyable & Deinitable, D: NumericDomain, X: Copyable & Deinitable](values: NumericArray[P, D], point: X, *, options: NumericOptions, max_steps: UInt64 = UInt64.MAX) raises PolyError -> _evaluation.Enclosure[D, _evaluation._Domain[D.Scalar, X], True, True] where (_Kind[X] >= 0 or _num._IsNumeric[X]):
    """Enclose a univariate sparse polynomial at a scalar argument.

    Parameters:
        P: Inferred from the input types.
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
    return adaptive_evaluate[P, D, X](values, point, budget, options=options)


def enclose_stream[I: Iterable, P: Copyable & Deinitable, C: Copyable & Deinitable, *Ts: Copyable & Deinitable](values: I, point: Tuple[*Ts], mut budget: Budget, *, context: BallContext) raises PolyError -> _evaluation._Stream[_Ring[_Kind[C]], _evaluation._Domain[C, _num._TupleScalar[Tuple[*Ts]]], False, True, False, _evaluation._AlgebraicTuple[Tuple[*Ts]]] where (_Element[I] == Tuple[P, C] and _Kind[C] >= 0):
    """Prepare an enclosure producer that emits one witness event at a time.

    Use the same inputs and context for producer and checker. Algebraic inputs
    are refined automatically at the requested precision, with root evidence
    before the arithmetic events. The receipt alone does not certify evaluation.

    Parameters:
        I: Inferred from the input types.
        P: Inferred from the input types.
        C: Inferred from the input types.
        Ts: Inferred from the input types.

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
    comptime E = _evaluation._Domain[C, _num._TupleScalar[Tuple[*Ts]]]
    comptime assert Tuple[*Ts].Ts.length == _width[P](), "evaluation point has the wrong number of coordinates"
    comptime assert _Kind[C] >= 0 and _Kind[C] != 3, "enclosure evaluation requires characteristic-zero exact coefficients"
    _num._context[E](rebind[E.Context](context), budget)
    _allocation[Tuple[Int64, E.Scalar]](_width[P](), budget)
    var algebraic_points = List[_evaluation._StreamPoint]()
    var arguments = List[Tuple[Int64, E.Scalar]](capacity=_width[P]())
    comptime for i in range(Tuple[*Ts].Ts.length):
        arguments.append((Int64(i), _evaluation._stream_argument[E](point[i], i, rebind[E.Context](context), algebraic_points, budget)))
    var p = to_core[I, P, C](values, budget)
    return _evaluation._stream[_Ring[_Kind[C]], E, False, True, False, _evaluation._AlgebraicTuple[Tuple[*Ts]]](p^, arguments^, context, budget, algebraic_points^)


def enclose_checker[I: Iterable, P: Copyable & Deinitable, C: Copyable & Deinitable, *Ts: Copyable & Deinitable](values: I, point: Tuple[*Ts], mut budget: Budget, *, context: BallContext) raises PolyError -> _evaluation._Stream[_Ring[_Kind[C]], _evaluation._Domain[C, _num._TupleScalar[Tuple[*Ts]]], False, True, True, _evaluation._AlgebraicTuple[Tuple[*Ts]]] where (_Element[I] == Tuple[P, C] and _Kind[C] >= 0):
    """Prepare independent incremental enclosure checking.

    Use the same inputs and context for producer and checker. Algebraic inputs
    are refined automatically at the requested precision, with root evidence
    before the arithmetic events. The receipt alone does not certify evaluation.

    Parameters:
        I: Inferred from the input types.
        P: Inferred from the input types.
        C: Inferred from the input types.
        Ts: Inferred from the input types.

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
    comptime E = _evaluation._Domain[C, _num._TupleScalar[Tuple[*Ts]]]
    comptime assert Tuple[*Ts].Ts.length == _width[P](), "evaluation point has the wrong number of coordinates"
    comptime assert _Kind[C] >= 0 and _Kind[C] != 3, "enclosure evaluation requires characteristic-zero exact coefficients"
    _num._context[E](rebind[E.Context](context), budget)
    _allocation[Tuple[Int64, E.Scalar]](_width[P](), budget)
    var algebraic_points = List[_evaluation._StreamPoint]()
    var arguments = List[Tuple[Int64, E.Scalar]](capacity=_width[P]())
    comptime for i in range(Tuple[*Ts].Ts.length):
        arguments.append((Int64(i), _evaluation._stream_argument[E](point[i], i, rebind[E.Context](context), algebraic_points, budget)))
    var p = to_core[I, P, C](values, budget)
    return _evaluation._stream[_Ring[_Kind[C]], E, False, True, True, _evaluation._AlgebraicTuple[Tuple[*Ts]]](p^, arguments^, context, budget, algebraic_points^)


def enclose_stream[I: Iterable, P: Copyable & Deinitable, C: Copyable & Deinitable, *Ts: Copyable & Deinitable](values: I, point: Tuple[*Ts], *, context: BallContext, max_steps: UInt64 = UInt64.MAX) raises PolyError -> _evaluation._Stream[_Ring[_Kind[C]], _evaluation._Domain[C, _num._TupleScalar[Tuple[*Ts]]], False, True, False, _evaluation._AlgebraicTuple[Tuple[*Ts]]] where (_Element[I] == Tuple[P, C] and _Kind[C] >= 0):
    """Prepare an enclosure producer that emits one witness event at a time.

    Use the same inputs and context for producer and checker. Algebraic inputs
    are refined automatically at the requested precision, with root evidence
    before the arithmetic events. The receipt alone does not certify evaluation.

    Parameters:
        I: Inferred from the input types.
        P: Inferred from the input types.
        C: Inferred from the input types.
        Ts: Inferred from the input types.

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
    return enclose_stream[I, P, C, *Ts](values, point, budget, context=context)


def enclose_checker[I: Iterable, P: Copyable & Deinitable, C: Copyable & Deinitable, *Ts: Copyable & Deinitable](values: I, point: Tuple[*Ts], *, context: BallContext, max_steps: UInt64 = UInt64.MAX) raises PolyError -> _evaluation._Stream[_Ring[_Kind[C]], _evaluation._Domain[C, _num._TupleScalar[Tuple[*Ts]]], False, True, True, _evaluation._AlgebraicTuple[Tuple[*Ts]]] where (_Element[I] == Tuple[P, C] and _Kind[C] >= 0):
    """Prepare independent incremental enclosure checking.

    Use the same inputs and context for producer and checker. Algebraic inputs
    are refined automatically at the requested precision, with root evidence
    before the arithmetic events. The receipt alone does not certify evaluation.

    Parameters:
        I: Inferred from the input types.
        P: Inferred from the input types.
        C: Inferred from the input types.
        Ts: Inferred from the input types.

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
    return enclose_checker[I, P, C, *Ts](values, point, budget, context=context)


def enclose_stream[P: Copyable & Deinitable, D: NumericDomain, *Ts: Copyable & Deinitable](values: NumericArray[P, D], point: Tuple[*Ts], mut budget: Budget, *, context: BallContext) raises PolyError -> _evaluation._Stream[D, _evaluation._Domain[D.Scalar, _num._TupleScalar[Tuple[*Ts]]], True, True, False, _evaluation._AlgebraicTuple[Tuple[*Ts]]]:
    """Prepare an enclosure producer that emits one witness event at a time.

    Use the same inputs and context for producer and checker. Algebraic inputs
    are refined automatically at the requested precision, with root evidence
    before the arithmetic events. The receipt alone does not certify evaluation.

    Parameters:
        P: Inferred from the input types.
        D: The numerical coefficient domain.
        Ts: Inferred from the input types.

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
    comptime E = _evaluation._Domain[D.Scalar, _num._TupleScalar[Tuple[*Ts]]]
    comptime assert Tuple[*Ts].Ts.length == _width[P](), "evaluation point has the wrong number of coordinates"
    _num._context[E](rebind[E.Context](context), budget)
    _allocation[Tuple[Int64, E.Scalar]](_width[P](), budget)
    var algebraic_points = List[_evaluation._StreamPoint]()
    var arguments = List[Tuple[Int64, E.Scalar]](capacity=_width[P]())
    comptime for i in range(Tuple[*Ts].Ts.length):
        arguments.append((Int64(i), _evaluation._stream_argument[E](point[i], i, rebind[E.Context](context), algebraic_points, budget)))
    var p = _num._copy_sparse(values._core[], _width[P](), budget)
    return _evaluation._stream[D, E, True, True, False, _evaluation._AlgebraicTuple[Tuple[*Ts]]](p^, arguments^, context, budget, algebraic_points^)


def enclose_checker[P: Copyable & Deinitable, D: NumericDomain, *Ts: Copyable & Deinitable](values: NumericArray[P, D], point: Tuple[*Ts], mut budget: Budget, *, context: BallContext) raises PolyError -> _evaluation._Stream[D, _evaluation._Domain[D.Scalar, _num._TupleScalar[Tuple[*Ts]]], True, True, True, _evaluation._AlgebraicTuple[Tuple[*Ts]]]:
    """Prepare independent incremental enclosure checking.

    Use the same inputs and context for producer and checker. Algebraic inputs
    are refined automatically at the requested precision, with root evidence
    before the arithmetic events. The receipt alone does not certify evaluation.

    Parameters:
        P: Inferred from the input types.
        D: The numerical coefficient domain.
        Ts: Inferred from the input types.

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
    comptime E = _evaluation._Domain[D.Scalar, _num._TupleScalar[Tuple[*Ts]]]
    comptime assert Tuple[*Ts].Ts.length == _width[P](), "evaluation point has the wrong number of coordinates"
    _num._context[E](rebind[E.Context](context), budget)
    _allocation[Tuple[Int64, E.Scalar]](_width[P](), budget)
    var algebraic_points = List[_evaluation._StreamPoint]()
    var arguments = List[Tuple[Int64, E.Scalar]](capacity=_width[P]())
    comptime for i in range(Tuple[*Ts].Ts.length):
        arguments.append((Int64(i), _evaluation._stream_argument[E](point[i], i, rebind[E.Context](context), algebraic_points, budget)))
    var p = _num._copy_sparse(values._core[], _width[P](), budget)
    return _evaluation._stream[D, E, True, True, True, _evaluation._AlgebraicTuple[Tuple[*Ts]]](p^, arguments^, context, budget, algebraic_points^)


def enclose_stream[P: Copyable & Deinitable, D: NumericDomain, *Ts: Copyable & Deinitable](values: NumericArray[P, D], point: Tuple[*Ts], *, context: BallContext, max_steps: UInt64 = UInt64.MAX) raises PolyError -> _evaluation._Stream[D, _evaluation._Domain[D.Scalar, _num._TupleScalar[Tuple[*Ts]]], True, True, False, _evaluation._AlgebraicTuple[Tuple[*Ts]]]:
    """Prepare an enclosure producer that emits one witness event at a time.

    Use the same inputs and context for producer and checker. Algebraic inputs
    are refined automatically at the requested precision, with root evidence
    before the arithmetic events. The receipt alone does not certify evaluation.

    Parameters:
        P: Inferred from the input types.
        D: The numerical coefficient domain.
        Ts: Inferred from the input types.

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
    return enclose_stream[P, D, *Ts](values, point, budget, context=context)


def enclose_checker[P: Copyable & Deinitable, D: NumericDomain, *Ts: Copyable & Deinitable](values: NumericArray[P, D], point: Tuple[*Ts], *, context: BallContext, max_steps: UInt64 = UInt64.MAX) raises PolyError -> _evaluation._Stream[D, _evaluation._Domain[D.Scalar, _num._TupleScalar[Tuple[*Ts]]], True, True, True, _evaluation._AlgebraicTuple[Tuple[*Ts]]]:
    """Prepare independent incremental enclosure checking.

    Use the same inputs and context for producer and checker. Algebraic inputs
    are refined automatically at the requested precision, with root evidence
    before the arithmetic events. The receipt alone does not certify evaluation.

    Parameters:
        P: Inferred from the input types.
        D: The numerical coefficient domain.
        Ts: Inferred from the input types.

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
    return enclose_checker[P, D, *Ts](values, point, budget, context=context)


def enclose_stream[I: Iterable, P: Copyable & Deinitable, C: Copyable & Deinitable, X: Copyable & Deinitable](values: I, point: X, mut budget: Budget, *, context: BallContext) raises PolyError -> _evaluation._Stream[_Ring[_Kind[C]], _evaluation._Domain[C, X], False, True, False, _evaluation._IsAlgebraic[X]] where (_Element[I] == Tuple[P, C] and _Kind[C] >= 0 and (_Kind[X] >= 0 or _num._IsNumeric[X])):
    """Prepare a univariate enclosure stream at a scalar argument.

    Parameters:
        I: Inferred from the input types.
        P: Inferred from the input types.
        C: Inferred from the input types.
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
    comptime assert _width[P]() == 1, "scalar enclosure evaluation requires one variable"
    return rebind_var[_evaluation._Stream[_Ring[_Kind[C]], _evaluation._Domain[C, X], False, True, False, _evaluation._IsAlgebraic[X]]](enclose_stream[I, P, C, X](values, (point.copy(),), budget, context=context))


def enclose_checker[I: Iterable, P: Copyable & Deinitable, C: Copyable & Deinitable, X: Copyable & Deinitable](values: I, point: X, mut budget: Budget, *, context: BallContext) raises PolyError -> _evaluation._Stream[_Ring[_Kind[C]], _evaluation._Domain[C, X], False, True, True, _evaluation._IsAlgebraic[X]] where (_Element[I] == Tuple[P, C] and _Kind[C] >= 0 and (_Kind[X] >= 0 or _num._IsNumeric[X])):
    """Prepare incremental enclosure checking at a scalar argument.

    Parameters:
        I: Inferred from the input types.
        P: Inferred from the input types.
        C: Inferred from the input types.
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
    comptime assert _width[P]() == 1, "scalar enclosure evaluation requires one variable"
    return rebind_var[_evaluation._Stream[_Ring[_Kind[C]], _evaluation._Domain[C, X], False, True, True, _evaluation._IsAlgebraic[X]]](enclose_checker[I, P, C, X](values, (point.copy(),), budget, context=context))


def enclose_stream[I: Iterable, P: Copyable & Deinitable, C: Copyable & Deinitable, X: Copyable & Deinitable](values: I, point: X, *, context: BallContext, max_steps: UInt64 = UInt64.MAX) raises PolyError -> _evaluation._Stream[_Ring[_Kind[C]], _evaluation._Domain[C, X], False, True, False, _evaluation._IsAlgebraic[X]] where (_Element[I] == Tuple[P, C] and _Kind[C] >= 0 and (_Kind[X] >= 0 or _num._IsNumeric[X])):
    """Prepare a univariate enclosure stream at a scalar argument.

    Parameters:
        I: Inferred from the input types.
        P: Inferred from the input types.
        C: Inferred from the input types.
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
    return enclose_stream[I, P, C, X](values, point, budget, context=context)


def enclose_checker[I: Iterable, P: Copyable & Deinitable, C: Copyable & Deinitable, X: Copyable & Deinitable](values: I, point: X, *, context: BallContext, max_steps: UInt64 = UInt64.MAX) raises PolyError -> _evaluation._Stream[_Ring[_Kind[C]], _evaluation._Domain[C, X], False, True, True, _evaluation._IsAlgebraic[X]] where (_Element[I] == Tuple[P, C] and _Kind[C] >= 0 and (_Kind[X] >= 0 or _num._IsNumeric[X])):
    """Prepare incremental enclosure checking at a scalar argument.

    Parameters:
        I: Inferred from the input types.
        P: Inferred from the input types.
        C: Inferred from the input types.
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
    return enclose_checker[I, P, C, X](values, point, budget, context=context)


def enclose_stream[P: Copyable & Deinitable, D: NumericDomain, X: Copyable & Deinitable](values: NumericArray[P, D], point: X, mut budget: Budget, *, context: BallContext) raises PolyError -> _evaluation._Stream[D, _evaluation._Domain[D.Scalar, X], True, True, False, _evaluation._IsAlgebraic[X]] where (_Kind[X] >= 0 or _num._IsNumeric[X]):
    """Prepare a univariate enclosure stream at a scalar argument.

    Parameters:
        P: Inferred from the input types.
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
    comptime assert _width[P]() == 1, "scalar enclosure evaluation requires one variable"
    return rebind_var[_evaluation._Stream[D, _evaluation._Domain[D.Scalar, X], True, True, False, _evaluation._IsAlgebraic[X]]](enclose_stream[P, D, X](values, (point.copy(),), budget, context=context))


def enclose_checker[P: Copyable & Deinitable, D: NumericDomain, X: Copyable & Deinitable](values: NumericArray[P, D], point: X, mut budget: Budget, *, context: BallContext) raises PolyError -> _evaluation._Stream[D, _evaluation._Domain[D.Scalar, X], True, True, True, _evaluation._IsAlgebraic[X]] where (_Kind[X] >= 0 or _num._IsNumeric[X]):
    """Prepare incremental enclosure checking at a scalar argument.

    Parameters:
        P: Inferred from the input types.
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
    comptime assert _width[P]() == 1, "scalar enclosure evaluation requires one variable"
    return rebind_var[_evaluation._Stream[D, _evaluation._Domain[D.Scalar, X], True, True, True, _evaluation._IsAlgebraic[X]]](enclose_checker[P, D, X](values, (point.copy(),), budget, context=context))


def enclose_stream[P: Copyable & Deinitable, D: NumericDomain, X: Copyable & Deinitable](values: NumericArray[P, D], point: X, *, context: BallContext, max_steps: UInt64 = UInt64.MAX) raises PolyError -> _evaluation._Stream[D, _evaluation._Domain[D.Scalar, X], True, True, False, _evaluation._IsAlgebraic[X]] where (_Kind[X] >= 0 or _num._IsNumeric[X]):
    """Prepare a univariate enclosure stream at a scalar argument.

    Parameters:
        P: Inferred from the input types.
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
    return enclose_stream[P, D, X](values, point, budget, context=context)


def enclose_checker[P: Copyable & Deinitable, D: NumericDomain, X: Copyable & Deinitable](values: NumericArray[P, D], point: X, *, context: BallContext, max_steps: UInt64 = UInt64.MAX) raises PolyError -> _evaluation._Stream[D, _evaluation._Domain[D.Scalar, X], True, True, True, _evaluation._IsAlgebraic[X]] where (_Kind[X] >= 0 or _num._IsNumeric[X]):
    """Prepare incremental enclosure checking at a scalar argument.

    Parameters:
        P: Inferred from the input types.
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
    return enclose_checker[P, D, X](values, point, budget, context=context)


from polynomials import serialize_numeric_sparse_to, deserialize_numeric_sparse_from


def dump[P: Copyable & Deinitable, D: NumericDomain, S: PolynomialTextSink](values: NumericArray[P, D], mut sink: S, mut budget: Budget, *, chunk_bytes: Int = 4096) raises PolyError:
    """Write numerical coefficients in bounded text chunks.

    Stored precision and enclosure bounds are preserved. A failed write can leave an incomplete destination.

    Parameters:
        P: Inferred from the input types unless explicitly supplied.
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
    serialize_numeric_sparse_to(values._core[], sink, budget, chunk_bytes=chunk_bytes)


def dump[P: Copyable & Deinitable, D: NumericDomain, S: PolynomialTextSink](values: NumericArray[P, D], mut sink: S, *, chunk_bytes: Int = 4096, max_steps: UInt64 = UInt64.MAX) raises PolyError:
    """Write numerical coefficients in bounded text chunks.

    Stored precision and enclosure bounds are preserved. A failed write can leave an incomplete destination.

    Parameters:
        P: Inferred from the input types unless explicitly supplied.
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
    dump[P, D, S](values, sink, budget, chunk_bytes=chunk_bytes)


def load_numeric[T: Copyable & Deinitable, S: PolynomialTextSource, *, ndim: Int = 1](var source: S, mut budget: Budget, *, max_field_bytes: Int = 16777216) raises PolyError -> NumericArray[_Shape[ndim], _num._StoredDomain[T]]:
    """Restore stored numerical values exactly; subsequent arithmetic takes an explicit context.

    Parameters:
        T: The expected numerical scalar type.
        S: The text source type.
        ndim: The expected sparse axis count, including unused axes; defaults to one.

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
    var core = deserialize_numeric_sparse_from[D](source^, budget, max_field_bytes=max_field_bytes)
    from ._numeric import _validate_sparse_axes
    _validate_sparse_axes(core, ndim, budget)
    return NumericArray[_Shape[ndim], _num._StoredDomain[T]](core^, budget)


def load_numeric[T: Copyable & Deinitable, S: PolynomialTextSource, *, ndim: Int = 1](var source: S, *, max_steps: UInt64 = UInt64.MAX, max_field_bytes: Int = 16777216) raises PolyError -> NumericArray[_Shape[ndim], _num._StoredDomain[T]]:
    """Restore stored numerical values exactly; subsequent arithmetic takes an explicit context.

    Parameters:
        T: The expected numerical scalar type.
        S: The text source type.
        ndim: The expected sparse axis count, including unused axes; defaults to one.

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
    return load_numeric[T, S, ndim=ndim](source^, budget, max_field_bytes=max_field_bytes)


from . import exact as _exact
from polynomials import GcdResult, CoprimalityCertificate, ResultantResult, ListDivision, SquarefreeDecomposition, coprimality_certificate


def gcd_checked[A: Iterable, B: Iterable, P: Copyable & Deinitable, C: Copyable & Deinitable, D: Copyable & Deinitable](a: A, b: B, mut budget: Budget, *, method: String = "auto") raises PolyError -> _exact.Result[_Join[_Kind[C], _Kind[D]], P, True, GcdResult[_Ring[_Join[_Kind[C], _Kind[D]]]]] where _Element[A] == Tuple[P, C] and _Element[B] == Tuple[P, D]:
    """Compute a GCD and retain independent maximality evidence.

    Independent checking proves greatest-common-divisor status up to a unit; the producer returns the usual normalized representative.

    Parameters:
        A: Inferred from the input types unless explicitly supplied.
        B: Inferred from the input types unless explicitly supplied.
        P: Inferred from the input types unless explicitly supplied.
        C: Inferred from the input types unless explicitly supplied.
        D: Inferred from the input types unless explicitly supplied.

    Args:
        a: The first polynomial.
        b: The second polynomial.
        budget: The shared work allowance, including preparation and output storage.
        method: Use auto for existing dispatch or modular for sparse reconstruction over ZZ or QQ.

    Returns:
        A retained GCD with maximality evidence for exact.value and exact.check.

    Raises:
        PolyError: DOMAIN for incompatible input, UNSUPPORTED for an unavailable coefficient domain, or LIMIT/CAPACITY on resource limits.
    """
    comptime k = _Join[_Kind[C], _Kind[D]]
    var pair = _pair[k, A, B, P, C, D](a, b, budget)
    var left = pair[0]._core[].reorder(pair[0]._core[].order, budget)
    var right = pair[1]._core[].reorder(pair[1]._core[].order, budget)
    var proof = _gcd_dispatch(left, right, method, budget, certify=True)
    _allocation[SparsePoly[_Ring[k]]](1, budget)
    var others: List[SparsePoly[_Ring[k]]] = [right^]
    var result = _exact._retain[k, P, True, GcdResult[_Ring[k]]](left^, others^, proof^, budget)
    return result^


def gcd_checked[A: Iterable, B: Iterable, P: Copyable & Deinitable, C: Copyable & Deinitable, D: Copyable & Deinitable](a: A, b: B, *, max_steps: UInt64 = UInt64.MAX, method: String = "auto") raises PolyError -> _exact.Result[_Join[_Kind[C], _Kind[D]], P, True, GcdResult[_Ring[_Join[_Kind[C], _Kind[D]]]]] where _Element[A] == Tuple[P, C] and _Element[B] == Tuple[P, D]:
    """Compute a GCD and retain independent maximality evidence.

    Independent checking proves greatest-common-divisor status up to a unit; the producer returns the usual normalized representative.

    Parameters:
        A: Inferred from the input types unless explicitly supplied.
        B: Inferred from the input types unless explicitly supplied.
        P: Inferred from the input types unless explicitly supplied.
        C: Inferred from the input types unless explicitly supplied.
        D: Inferred from the input types unless explicitly supplied.

    Args:
        a: The first polynomial.
        b: The second polynomial.
        max_steps: The complete call’s work allowance.
        method: Use auto for existing dispatch or modular for sparse reconstruction over ZZ or QQ.

    Returns:
        A retained GCD with maximality evidence for exact.value and exact.check.

    Raises:
        PolyError: DOMAIN for incompatible input, UNSUPPORTED for an unavailable coefficient domain, or LIMIT/CAPACITY on resource limits.
    """
    var budget = Budget(max_steps)
    return gcd_checked[A, B, P, C, D](a, b, budget, method=method)


def resultant_checked[A: Iterable, B: Iterable, P: Copyable & Deinitable, C: Copyable & Deinitable, D: Copyable & Deinitable](a: A, b: B, mut budget: Budget, *, axis: Int = 0) raises PolyError -> _exact.Result[_Join[_Kind[C], _Kind[D]], P, True, ResultantResult[_Ring[_Join[_Kind[C], _Kind[D]]]]] where _Element[A] == Tuple[P, C] and _Element[B] == Tuple[P, D]:
    """Compute a resultant and retain its ideal-membership identity.

    The checker proves u*a + v*b = result; it does not independently prove the determinant definition of the resultant.

    Parameters:
        A: Inferred from the input types unless explicitly supplied.
        B: Inferred from the input types unless explicitly supplied.
        P: Inferred from the input types unless explicitly supplied.
        C: Inferred from the input types unless explicitly supplied.
        D: Inferred from the input types unless explicitly supplied.

    Args:
        a: The first polynomial.
        b: The second polynomial.
        budget: The shared work allowance, including preparation and output storage.
        axis: The zero-based polynomial axis.

    Returns:
        A retained resultant with an ideal-membership identity for exact.value and exact.check.

    Raises:
        PolyError: DOMAIN for incompatible input, UNSUPPORTED for an unavailable coefficient domain, or LIMIT/CAPACITY on resource limits.
    """
    comptime k = _Join[_Kind[C], _Kind[D]]
    var pair = _pair[k, A, B, P, C, D](a, b, budget)
    var left = pair[0]._core[].reorder(pair[0]._core[].order, budget)
    var right = pair[1]._core[].reorder(pair[1]._core[].order, budget)
    _axis[P](axis)
    var proof = _resultant(left, right, Int64(axis), budget)
    _allocation[SparsePoly[_Ring[k]]](1, budget)
    var others: List[SparsePoly[_Ring[k]]] = [right^]
    var result = _exact._retain[k, P, True, ResultantResult[_Ring[k]]](left^, others^, proof^, budget)
    return result^


def resultant_checked[A: Iterable, B: Iterable, P: Copyable & Deinitable, C: Copyable & Deinitable, D: Copyable & Deinitable](a: A, b: B, *, axis: Int = 0, max_steps: UInt64 = UInt64.MAX) raises PolyError -> _exact.Result[_Join[_Kind[C], _Kind[D]], P, True, ResultantResult[_Ring[_Join[_Kind[C], _Kind[D]]]]] where _Element[A] == Tuple[P, C] and _Element[B] == Tuple[P, D]:
    """Compute a resultant and retain its ideal-membership identity.

    The checker proves u*a + v*b = result; it does not independently prove the determinant definition of the resultant.

    Parameters:
        A: Inferred from the input types unless explicitly supplied.
        B: Inferred from the input types unless explicitly supplied.
        P: Inferred from the input types unless explicitly supplied.
        C: Inferred from the input types unless explicitly supplied.
        D: Inferred from the input types unless explicitly supplied.

    Args:
        a: The first polynomial.
        b: The second polynomial.
        axis: The zero-based polynomial axis.
        max_steps: The complete call’s work allowance.

    Returns:
        A retained resultant with an ideal-membership identity for exact.value and exact.check.

    Raises:
        PolyError: DOMAIN for incompatible input, UNSUPPORTED for an unavailable coefficient domain, or LIMIT/CAPACITY on resource limits.
    """
    var budget = Budget(max_steps)
    return resultant_checked[A, B, P, C, D](a, b, budget, axis=axis)


def coprimality[A: Iterable, B: Iterable, P: Copyable & Deinitable, C: Copyable & Deinitable, D: Copyable & Deinitable](a: A, b: B, mut budget: Budget) raises PolyError -> Optional[_exact.Result[_Join[_Kind[C], _Kind[D]], P, True, CoprimalityCertificate[_Ring[_Join[_Kind[C], _Kind[D]]]]]] where _Element[A] == Tuple[P, C] and _Element[B] == Tuple[P, D]:
    """Produce a coprimality witness when the inputs have no common nonunit factor.

    None means the producer did not establish coprimality.

    Parameters:
        A: Inferred from the input types unless explicitly supplied.
        B: Inferred from the input types unless explicitly supplied.
        P: Inferred from the input types unless explicitly supplied.
        C: Inferred from the input types unless explicitly supplied.
        D: Inferred from the input types unless explicitly supplied.

    Args:
        a: The first polynomial.
        b: The second polynomial.
        budget: The shared work allowance, including preparation and output storage.

    Returns:
        A retained result for exact.check, or None for an unsuccessful coprimality request.

    Raises:
        PolyError: DOMAIN for incompatible input, UNSUPPORTED for an unavailable coefficient domain, or LIMIT/CAPACITY on resource limits.
    """
    comptime k = _Join[_Kind[C], _Kind[D]]
    var pair = _pair[k, A, B, P, C, D](a, b, budget)
    var left = pair[0]._core[].reorder(pair[0]._core[].order, budget)
    var right = pair[1]._core[].reorder(pair[1]._core[].order, budget)
    var optional = coprimality_certificate(left, right, budget)
    if not optional:
        return None
    var proof = optional.take()
    _allocation[SparsePoly[_Ring[k]]](1, budget)
    var others: List[SparsePoly[_Ring[k]]] = [right^]
    var result = _exact._retain[k, P, True, CoprimalityCertificate[_Ring[k]]](left^, others^, proof^, budget)
    return Optional(result^)


def coprimality[A: Iterable, B: Iterable, P: Copyable & Deinitable, C: Copyable & Deinitable, D: Copyable & Deinitable](a: A, b: B, *, max_steps: UInt64 = UInt64.MAX) raises PolyError -> Optional[_exact.Result[_Join[_Kind[C], _Kind[D]], P, True, CoprimalityCertificate[_Ring[_Join[_Kind[C], _Kind[D]]]]]] where _Element[A] == Tuple[P, C] and _Element[B] == Tuple[P, D]:
    """Produce a coprimality witness when the inputs have no common nonunit factor.

    None means the producer did not establish coprimality.

    Parameters:
        A: Inferred from the input types unless explicitly supplied.
        B: Inferred from the input types unless explicitly supplied.
        P: Inferred from the input types unless explicitly supplied.
        C: Inferred from the input types unless explicitly supplied.
        D: Inferred from the input types unless explicitly supplied.

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
    return coprimality[A, B, P, C, D](a, b, budget)


def divide_checked[A: Iterable, B: Iterable, P: Copyable & Deinitable, C: Copyable & Deinitable, D: Copyable & Deinitable](a: A, b: B, mut budget: Budget, *, order: String = "lex", axes: List[Int] = List[Int]()) raises PolyError -> _exact.Result[_FieldKind[_Join[_Kind[C], _Kind[D]]], P, True, ListDivision[_Ring[_FieldKind[_Join[_Kind[C], _Kind[D]]]]]] where _Element[A] == Tuple[P, C] and _Element[B] == Tuple[P, D]:
    """Divide exact polynomials and retain the inputs and division evidence.

    Integer inputs promote to QQ. Sparse checking proves the reduction identity without claiming a unique remainder.

    Parameters:
        A: Inferred from the input types unless explicitly supplied.
        B: Inferred from the input types unless explicitly supplied.
        P: Inferred from the input types unless explicitly supplied.
        C: Inferred from the input types unless explicitly supplied.
        D: Inferred from the input types unless explicitly supplied.

    Args:
        a: The first polynomial.
        b: The second polynomial.
        budget: The shared work allowance, including preparation and output storage.
        order: One of lex, grlex, or grevlex; defaults to lex.
        axes: All axes in descending priority; empty uses tuple order.

    Returns:
        A retained division for exact.quotient, exact.remainder and exact.check.

    Raises:
        PolyError: DOMAIN for incompatible input, UNSUPPORTED for an unavailable coefficient domain, or LIMIT/CAPACITY on resource limits.
    """
    var monomial_order = _monomial_order[P](order, axes, budget)
    comptime k = _FieldKind[_Join[_Kind[C], _Kind[D]]]
    var pair = _pair[k, A, B, P, C, D](a, b, budget)
    var left = pair[0]._core[].reorder(monomial_order, budget)
    var right = pair[1]._core[].reorder(monomial_order, budget)
    _allocation[SparsePoly[_Ring[k]]](1, budget)
    var others: List[SparsePoly[_Ring[k]]] = [right^]
    comptime F = downcast[_Ring[k], CoefficientField]
    var proof = rebind_var[ListDivision[_Ring[k]]](divide_by_list(rebind[SparsePoly[F]](left), rebind[List[SparsePoly[F]]](others), budget))
    var result = _exact._retain[k, P, True, ListDivision[_Ring[k]]](left^, others^, proof^, budget)
    return result^


def divide_checked[A: Iterable, B: Iterable, P: Copyable & Deinitable, C: Copyable & Deinitable, D: Copyable & Deinitable](a: A, b: B, *, max_steps: UInt64 = UInt64.MAX, order: String = "lex", axes: List[Int] = List[Int]()) raises PolyError -> _exact.Result[_FieldKind[_Join[_Kind[C], _Kind[D]]], P, True, ListDivision[_Ring[_FieldKind[_Join[_Kind[C], _Kind[D]]]]]] where _Element[A] == Tuple[P, C] and _Element[B] == Tuple[P, D]:
    """Divide exact polynomials and retain the inputs and division evidence.

    Integer inputs promote to QQ. Sparse checking proves the reduction identity without claiming a unique remainder.

    Parameters:
        A: Inferred from the input types unless explicitly supplied.
        B: Inferred from the input types unless explicitly supplied.
        P: Inferred from the input types unless explicitly supplied.
        C: Inferred from the input types unless explicitly supplied.
        D: Inferred from the input types unless explicitly supplied.

    Args:
        a: The first polynomial.
        b: The second polynomial.
        max_steps: The complete call’s work allowance.
        order: One of lex, grlex, or grevlex; defaults to lex.
        axes: All axes in descending priority; empty uses tuple order.

    Returns:
        A retained division for exact.quotient, exact.remainder and exact.check.

    Raises:
        PolyError: DOMAIN for incompatible input, UNSUPPORTED for an unavailable coefficient domain, or LIMIT/CAPACITY on resource limits.
    """
    var budget = Budget(max_steps)
    return divide_checked[A, B, P, C, D](a, b, budget, order=order, axes=axes)


def factor_checked[I: Iterable, P: Copyable & Deinitable, C: Copyable & Deinitable](values: I, mut budget: Budget, *, seed: UInt64 = 0) raises PolyError -> _exact.Result[_Kind[C], P, True, MultivariateFactorization[_Ring[_Kind[C]]]] where _Element[I] == Tuple[P, C]:
    """Factor the polynomial and retain independently checkable evidence.

    exact.check verifies recomposition. Over AA and QQbar it also verifies monicity, ordering, distinct factors, and irreducibility. Multivariate results retain auxiliary univariate image factorizations; the checker verifies those certificates and exhausts possible proper divisors without calling the factorization producer. Checking can require exponential work. evidence() exposes the core product certificate; retain the complete Result for the stronger check. Other coefficient domains retain the product-only claim.

    Parameters:
        I: Inferred from the input types unless explicitly supplied.
        P: Inferred from the input types unless explicitly supplied.
        C: Inferred from the input types unless explicitly supplied.

    Args:
        values: Input coefficients, sparse terms, or a prepared array.
        budget: The shared work allowance, including preparation and output storage.
        seed: The deterministic finite-field factorization seed.

    Returns:
        A retained factorization for exact.unit, exact.factors and exact.check.

    Raises:
        PolyError: DOMAIN for incompatible input, UNSUPPORTED for an unavailable coefficient domain, or LIMIT/CAPACITY on resource limits.
    """
    comptime k = _Kind[C]
    var prepared = _prepare[I, P, C](values, budget)
    var ctx = _data_context[k](prepared.modulus(), 0, budget)
    var source = _promote[k](prepared, ctx, budget)
    var input = source._core[].reorder(source._core[].order, budget)
    comptime if k == 4 or k == 5:
        from . import _algebraic_factor
        var proof = _algebraic_factor._factor_sparse_evidence(source._core[], budget)
        var product = MultivariateFactorization[_Ring[k]](_Ring[k].zero(source._core[].ring), List[Tuple[SparsePoly[_Ring[k]], Int]]())
        swap(product, proof[0])
        var result = _exact._retain[k, P, True, MultivariateFactorization[_Ring[k]]](input^, List[SparsePoly[_Ring[k]]](), product^, budget)
        swap(result._data[].algebraic_images, proof[1])
        return result^
    else:
        var proof = _factor_evidence(source, budget, seed)
        return _exact._retain[k, P, True, MultivariateFactorization[_Ring[k]]](input^, List[SparsePoly[_Ring[k]]](), proof^, budget)


def factor_checked[I: Iterable, P: Copyable & Deinitable, C: Copyable & Deinitable](values: I, *, seed: UInt64 = 0, max_steps: UInt64 = UInt64.MAX) raises PolyError -> _exact.Result[_Kind[C], P, True, MultivariateFactorization[_Ring[_Kind[C]]]] where _Element[I] == Tuple[P, C]:
    """Factor the polynomial and retain independently checkable evidence.

    exact.check verifies recomposition. Over AA and QQbar it also verifies monicity, ordering, distinct factors, and irreducibility. Multivariate results retain auxiliary univariate image factorizations; the checker verifies those certificates and exhausts possible proper divisors without calling the factorization producer. Checking can require exponential work. evidence() exposes the core product certificate; retain the complete Result for the stronger check. Other coefficient domains retain the product-only claim.

    Parameters:
        I: Inferred from the input types unless explicitly supplied.
        P: Inferred from the input types unless explicitly supplied.
        C: Inferred from the input types unless explicitly supplied.

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
    return factor_checked[I, P, C](values, budget, seed=seed)


def squarefree_checked[I: Iterable, P: Copyable & Deinitable, C: Copyable & Deinitable](values: I, mut budget: Budget) raises PolyError -> _exact.Result[_FieldKind[_Kind[C]], P, True, _SquarefreeProof[P, _FieldKind[_Kind[C]]]] where _Element[I] == Tuple[P, C]:
    """Decompose by multiplicity and retain the product identity.

    The checker verifies recomposition. It does not certify irreducibility or squarefreeness of the factors.

    Parameters:
        I: Inferred from the input types unless explicitly supplied.
        P: Inferred from the input types unless explicitly supplied.
        C: Inferred from the input types unless explicitly supplied.

    Args:
        values: Input coefficients, sparse terms, or a prepared array.
        budget: The shared work allowance, including preparation and output storage.

    Returns:
        A retained factorization for exact.unit, exact.factors and exact.check.

    Raises:
        PolyError: DOMAIN for incompatible input, UNSUPPORTED for an unavailable coefficient domain, or LIMIT/CAPACITY on resource limits.
    """
    comptime k = _FieldKind[_Kind[C]]
    var prepared = _prepare[I, P, C](values, budget)
    var ctx = _data_context[k](prepared.modulus(), 0, budget)
    var source = _promote[k](prepared, ctx, budget)
    var input = source._core[].reorder(source._core[].order, budget)
    comptime F = downcast[_Ring[k], CoefficientField]
    var proof: _SquarefreeProof[P, k]
    comptime if _width[P]() == 1:
        var univariate = _univariate(source, budget)
        proof = rebind_var[_SquarefreeProof[P, k]](_dense._squarefree[F](rebind[DensePoly[F]](univariate._core[]), budget))
    else:
        proof = rebind_var[_SquarefreeProof[P, k]](squarefree_multivariate[F](rebind[SparsePoly[F]](input), budget))
    return _exact._retain[k, P, True, _SquarefreeProof[P, k]](input^, List[SparsePoly[_Ring[k]]](), proof^, budget)


def squarefree_checked[I: Iterable, P: Copyable & Deinitable, C: Copyable & Deinitable](values: I, *, max_steps: UInt64 = UInt64.MAX) raises PolyError -> _exact.Result[_FieldKind[_Kind[C]], P, True, _SquarefreeProof[P, _FieldKind[_Kind[C]]]] where _Element[I] == Tuple[P, C]:
    """Decompose by multiplicity and retain the product identity.

    The checker verifies recomposition. It does not certify irreducibility or squarefreeness of the factors.

    Parameters:
        I: Inferred from the input types unless explicitly supplied.
        P: Inferred from the input types unless explicitly supplied.
        C: Inferred from the input types unless explicitly supplied.

    Args:
        values: Input coefficients, sparse terms, or a prepared array.
        max_steps: The complete call’s work allowance.

    Returns:
        A retained factorization for exact.unit, exact.factors and exact.check.

    Raises:
        PolyError: DOMAIN for incompatible input, UNSUPPORTED for an unavailable coefficient domain, or LIMIT/CAPACITY on resource limits.
    """
    var budget = Budget(max_steps)
    return squarefree_checked[I, P, C](values, budget)


def divide_many_checked[A: Iterable, B: Iterable, P: Copyable & Deinitable, C: Copyable & Deinitable, D: Copyable & Deinitable](values: A, divisors: B, mut budget: Budget, *, order: String = "lex", axes: List[Int] = List[Int]()) raises PolyError -> _exact.Result[_FieldKind[_Join[_Kind[C], _Kind[D]]], P, True, ListDivision[_Ring[_FieldKind[_Join[_Kind[C], _Kind[D]]]]]] where _Element[A] == Tuple[P, C] and _Element[_Nested[B]] == Tuple[P, D]:
    """Divide by ordered polynomials and retain the exact recomposition identity.

    Sparse reduction uses the requested monomial order; lex with axis zero first is the default. Returned arrays keep canonical storage order. Changing divisor order can change quotients and remainder; this is not a Groebner-basis computation. An empty divisor collection returns no quotients and the promoted input as remainder. A zero divisor raises DOMAIN.

    Parameters:
        A: The first inferred iterable type.
        B: The second inferred iterable type.
        P: The power shape: Int or a tuple of Int powers.
        C: The inferred input coefficient type.
        D: The second inferred coefficient type.

    Args:
        values: The coefficient sequence, sparse terms, or prepared array.
        divisors: A finite iterable of polynomials of one Mojo input type, tried in the supplied order.
        budget: The caller-owned work allowance, shared through preparation and computation.
        order: One of lex, grlex, or grevlex; defaults to lex.
        axes: All axes in descending priority; empty uses tuple order.

    Returns:
        A retained result for exact.quotients, exact.remainder and exact.check; the check establishes the identity, not a unique reduced remainder.

    Raises:
        PolyError: LIMIT on exhausted work, CAPACITY on unrepresentable sizes, DOMAIN for invalid input, or UNSUPPORTED for a documented domain restriction.
    """
    var monomial_order = _monomial_order[P](order, axes, budget)
    comptime k = _FieldKind[_Join[_Kind[C], _Kind[D]]]
    comptime F = downcast[_Ring[k], CoefficientField]
    var prepared = _many[k, A, B, P, C, D](values, divisors, budget)
    _allocation[SparsePoly[F]](len(prepared[1]), budget)
    var cores = List[SparsePoly[F]](capacity=len(prepared[1]))
    for q in prepared[1]:
        cores.append(rebind_var[SparsePoly[F]](q._core[].reorder(monomial_order, budget)))
    var p = prepared[0]._core[].reorder(monomial_order, budget)
    var result = divide_by_list[F](rebind[SparsePoly[F]](p), cores, budget)
    return _exact._retain[k, P, True, ListDivision[_Ring[k]]](p^, rebind_var[List[SparsePoly[_Ring[k]]]](cores^), rebind_var[ListDivision[_Ring[k]]](result^), budget)



def divide_many_checked[A: Iterable, B: Iterable, P: Copyable & Deinitable, C: Copyable & Deinitable, D: Copyable & Deinitable](values: A, divisors: B, *, max_steps: UInt64 = UInt64.MAX, order: String = "lex", axes: List[Int] = List[Int]()) raises PolyError -> _exact.Result[_FieldKind[_Join[_Kind[C], _Kind[D]]], P, True, ListDivision[_Ring[_FieldKind[_Join[_Kind[C], _Kind[D]]]]]] where _Element[A] == Tuple[P, C] and _Element[_Nested[B]] == Tuple[P, D]:
    """Divide by ordered polynomials and retain the exact recomposition identity.

    Sparse reduction uses the requested monomial order; lex with axis zero first is the default. Returned arrays keep canonical storage order. Changing divisor order can change quotients and remainder; this is not a Groebner-basis computation. An empty divisor collection returns no quotients and the promoted input as remainder. A zero divisor raises DOMAIN.

    Parameters:
        A: The first inferred iterable type.
        B: The second inferred iterable type.
        P: The power shape: Int or a tuple of Int powers.
        C: The inferred input coefficient type.
        D: The second inferred coefficient type.

    Args:
        values: The coefficient sequence, sparse terms, or prepared array.
        divisors: A finite iterable of polynomials of one Mojo input type, tried in the supplied order.
        max_steps: The complete call's work allowance; defaults to UInt64.MAX.
        order: One of lex, grlex, or grevlex; defaults to lex.
        axes: All axes in descending priority; empty uses tuple order.

    Returns:
        A retained result for exact.quotients, exact.remainder and exact.check; the check establishes the identity, not a unique reduced remainder.

    Raises:
        PolyError: LIMIT on exhausted work, CAPACITY on unrepresentable sizes, DOMAIN for invalid input, or UNSUPPORTED for a documented domain restriction.
    """
    var budget = Budget(max_steps)
    return divide_many_checked[A, B, P, C, D](values, divisors, budget, order=order, axes=axes)


def real_root_cover[P: Copyable & Deinitable, D: NumericDomain](values: NumericArray[P, D], mut budget: Budget, *, context: D.Context, options: NumericOptions = NumericOptions(), complete_only: Bool = False) raises PolyError -> _roots.NumericCover[D, False]:
    """Prepare a numerical real root cover.

    Conversion to dense coefficients shares the call budget; large sparse degrees can require substantial memory.

    Parameters:
        P: Inferred from the input types unless explicitly supplied.
        D: Inferred from the input types unless explicitly supplied.

    Args:
        values: Input coefficients, sparse terms, or a prepared array.
        budget: The shared work allowance, including preparation and output storage.
        context: Explicit precision and rounding or enclosure settings.
        options: Precision, accuracy, subdivision and isolation settings.
        complete_only: Raise unless every requested root-cover property succeeds.

    Returns:
        The same checked root-cover result or stream interface as dense inputs.

    Raises:
        PolyError: DOMAIN for incompatible input, UNSUPPORTED for an unavailable coefficient domain, or LIMIT/CAPACITY on resource limits.
    """
    from . import _conversion
    comptime assert _width[P]() == 1, "root covers require a univariate power shape"
    var prepared = _conversion.to_dense(values, budget, context=context)
    return _dense.real_root_cover[D](prepared, budget, options=options, complete_only=complete_only)


def real_root_cover[P: Copyable & Deinitable, D: NumericDomain](values: NumericArray[P, D], *, context: D.Context, options: NumericOptions = NumericOptions(), complete_only: Bool = False, max_steps: UInt64 = UInt64.MAX) raises PolyError -> _roots.NumericCover[D, False]:
    """Prepare a numerical real root cover.

    Conversion to dense coefficients shares the call budget; large sparse degrees can require substantial memory.

    Parameters:
        P: Inferred from the input types unless explicitly supplied.
        D: Inferred from the input types unless explicitly supplied.

    Args:
        values: Input coefficients, sparse terms, or a prepared array.
        context: Explicit precision and rounding or enclosure settings.
        options: Precision, accuracy, subdivision and isolation settings.
        complete_only: Raise unless every requested root-cover property succeeds.
        max_steps: The complete call’s work allowance.

    Returns:
        The same checked root-cover result or stream interface as dense inputs.

    Raises:
        PolyError: DOMAIN for incompatible input, UNSUPPORTED for an unavailable coefficient domain, or LIMIT/CAPACITY on resource limits.
    """
    var budget = Budget(max_steps)
    return real_root_cover[P, D](values, budget, context=context, options=options, complete_only=complete_only)


def real_root_cover_to[P: Copyable & Deinitable, D: NumericDomain, S: RealRootSink](values: NumericArray[P, D], mut sink: S, mut budget: Budget, *, context: D.Context, options: NumericOptions = NumericOptions(), complete_only: Bool = False) raises PolyError -> RootStreamReceipt:
    """Prepare a numerical real root cover witness stream.

    Conversion to dense coefficients shares the call budget; large sparse degrees can require substantial memory.

    Parameters:
        P: Inferred from the input types unless explicitly supplied.
        D: Inferred from the input types unless explicitly supplied.
        S: Inferred from the input types unless explicitly supplied.

    Args:
        values: Input coefficients, sparse terms, or a prepared array.
        sink: The consumer receiving ordered chunks or witnesses.
        budget: The shared work allowance, including preparation and output storage.
        context: Explicit precision and rounding or enclosure settings.
        options: Precision, accuracy, subdivision and isolation settings.
        complete_only: Raise unless every requested root-cover property succeeds.

    Returns:
        The same checked root-cover result or stream interface as dense inputs.

    Raises:
        PolyError: DOMAIN for incompatible input, UNSUPPORTED for an unavailable coefficient domain, or LIMIT/CAPACITY on resource limits.
    """
    from . import _conversion
    comptime assert _width[P]() == 1, "root covers require a univariate power shape"
    var prepared = _conversion.to_dense(values, budget, context=context)
    return _dense.real_root_cover_to[D, S](prepared, sink, budget, options=options, complete_only=complete_only)


def real_root_cover_to[P: Copyable & Deinitable, D: NumericDomain, S: RealRootSink](values: NumericArray[P, D], mut sink: S, *, context: D.Context, options: NumericOptions = NumericOptions(), complete_only: Bool = False, max_steps: UInt64 = UInt64.MAX) raises PolyError -> RootStreamReceipt:
    """Prepare a numerical real root cover witness stream.

    Conversion to dense coefficients shares the call budget; large sparse degrees can require substantial memory.

    Parameters:
        P: Inferred from the input types unless explicitly supplied.
        D: Inferred from the input types unless explicitly supplied.
        S: Inferred from the input types unless explicitly supplied.

    Args:
        values: Input coefficients, sparse terms, or a prepared array.
        sink: The consumer receiving ordered chunks or witnesses.
        context: Explicit precision and rounding or enclosure settings.
        options: Precision, accuracy, subdivision and isolation settings.
        complete_only: Raise unless every requested root-cover property succeeds.
        max_steps: The complete call’s work allowance.

    Returns:
        The same checked root-cover result or stream interface as dense inputs.

    Raises:
        PolyError: DOMAIN for incompatible input, UNSUPPORTED for an unavailable coefficient domain, or LIMIT/CAPACITY on resource limits.
    """
    var budget = Budget(max_steps)
    return real_root_cover_to[P, D, S](values, sink, budget, context=context, options=options, complete_only=complete_only)


def real_root_checker[P: Copyable & Deinitable, D: NumericDomain](values: NumericArray[P, D], mut budget: Budget, *, context: D.Context, options: NumericOptions = NumericOptions()) raises PolyError -> RealRootStreamChecker:
    """Prepare a numerical real root stream checker.

    Conversion to dense coefficients shares the call budget; large sparse degrees can require substantial memory.

    Parameters:
        P: Inferred from the input types unless explicitly supplied.
        D: Inferred from the input types unless explicitly supplied.

    Args:
        values: Input coefficients, sparse terms, or a prepared array.
        budget: The shared work allowance, including preparation and output storage.
        context: Explicit precision and rounding or enclosure settings.
        options: Precision, accuracy, subdivision and isolation settings.

    Returns:
        The same checked root-cover result or stream interface as dense inputs.

    Raises:
        PolyError: DOMAIN for incompatible input, UNSUPPORTED for an unavailable coefficient domain, or LIMIT/CAPACITY on resource limits.
    """
    from . import _conversion
    comptime assert _width[P]() == 1, "root covers require a univariate power shape"
    var prepared = _conversion.to_dense(values, budget, context=context)
    return _dense.real_root_checker[D](prepared, budget, options=options)


def real_root_checker[P: Copyable & Deinitable, D: NumericDomain](values: NumericArray[P, D], *, context: D.Context, options: NumericOptions = NumericOptions(), max_steps: UInt64 = UInt64.MAX) raises PolyError -> RealRootStreamChecker:
    """Prepare a numerical real root stream checker.

    Conversion to dense coefficients shares the call budget; large sparse degrees can require substantial memory.

    Parameters:
        P: Inferred from the input types unless explicitly supplied.
        D: Inferred from the input types unless explicitly supplied.

    Args:
        values: Input coefficients, sparse terms, or a prepared array.
        context: Explicit precision and rounding or enclosure settings.
        options: Precision, accuracy, subdivision and isolation settings.
        max_steps: The complete call’s work allowance.

    Returns:
        The same checked root-cover result or stream interface as dense inputs.

    Raises:
        PolyError: DOMAIN for incompatible input, UNSUPPORTED for an unavailable coefficient domain, or LIMIT/CAPACITY on resource limits.
    """
    var budget = Budget(max_steps)
    return real_root_checker[P, D](values, budget, context=context, options=options)


def complex_root_cover[P: Copyable & Deinitable, D: NumericDomain](values: NumericArray[P, D], mut budget: Budget, *, context: D.Context, options: NumericOptions = NumericOptions(), complete_only: Bool = False) raises PolyError -> _roots.NumericCover[D, True]:
    """Prepare a numerical complex root cover.

    Conversion to dense coefficients shares the call budget; large sparse degrees can require substantial memory.

    Parameters:
        P: Inferred from the input types unless explicitly supplied.
        D: Inferred from the input types unless explicitly supplied.

    Args:
        values: Input coefficients, sparse terms, or a prepared array.
        budget: The shared work allowance, including preparation and output storage.
        context: Explicit precision and rounding or enclosure settings.
        options: Precision, accuracy, subdivision and isolation settings.
        complete_only: Raise unless every requested root-cover property succeeds.

    Returns:
        The same checked root-cover result or stream interface as dense inputs.

    Raises:
        PolyError: DOMAIN for incompatible input, UNSUPPORTED for an unavailable coefficient domain, or LIMIT/CAPACITY on resource limits.
    """
    from . import _conversion
    comptime assert _width[P]() == 1, "root covers require a univariate power shape"
    var prepared = _conversion.to_dense(values, budget, context=context)
    return _dense.complex_root_cover[D](prepared, budget, options=options, complete_only=complete_only)


def complex_root_cover[P: Copyable & Deinitable, D: NumericDomain](values: NumericArray[P, D], *, context: D.Context, options: NumericOptions = NumericOptions(), complete_only: Bool = False, max_steps: UInt64 = UInt64.MAX) raises PolyError -> _roots.NumericCover[D, True]:
    """Prepare a numerical complex root cover.

    Conversion to dense coefficients shares the call budget; large sparse degrees can require substantial memory.

    Parameters:
        P: Inferred from the input types unless explicitly supplied.
        D: Inferred from the input types unless explicitly supplied.

    Args:
        values: Input coefficients, sparse terms, or a prepared array.
        context: Explicit precision and rounding or enclosure settings.
        options: Precision, accuracy, subdivision and isolation settings.
        complete_only: Raise unless every requested root-cover property succeeds.
        max_steps: The complete call’s work allowance.

    Returns:
        The same checked root-cover result or stream interface as dense inputs.

    Raises:
        PolyError: DOMAIN for incompatible input, UNSUPPORTED for an unavailable coefficient domain, or LIMIT/CAPACITY on resource limits.
    """
    var budget = Budget(max_steps)
    return complex_root_cover[P, D](values, budget, context=context, options=options, complete_only=complete_only)


def complex_root_cover_to[P: Copyable & Deinitable, D: NumericDomain, S: ComplexRootSink](values: NumericArray[P, D], mut sink: S, mut budget: Budget, *, context: D.Context, options: NumericOptions = NumericOptions(), complete_only: Bool = False) raises PolyError -> RootStreamReceipt:
    """Prepare a numerical complex root cover witness stream.

    Conversion to dense coefficients shares the call budget; large sparse degrees can require substantial memory.

    Parameters:
        P: Inferred from the input types unless explicitly supplied.
        D: Inferred from the input types unless explicitly supplied.
        S: Inferred from the input types unless explicitly supplied.

    Args:
        values: Input coefficients, sparse terms, or a prepared array.
        sink: The consumer receiving ordered chunks or witnesses.
        budget: The shared work allowance, including preparation and output storage.
        context: Explicit precision and rounding or enclosure settings.
        options: Precision, accuracy, subdivision and isolation settings.
        complete_only: Raise unless every requested root-cover property succeeds.

    Returns:
        The same checked root-cover result or stream interface as dense inputs.

    Raises:
        PolyError: DOMAIN for incompatible input, UNSUPPORTED for an unavailable coefficient domain, or LIMIT/CAPACITY on resource limits.
    """
    from . import _conversion
    comptime assert _width[P]() == 1, "root covers require a univariate power shape"
    var prepared = _conversion.to_dense(values, budget, context=context)
    return _dense.complex_root_cover_to[D, S](prepared, sink, budget, options=options, complete_only=complete_only)


def complex_root_cover_to[P: Copyable & Deinitable, D: NumericDomain, S: ComplexRootSink](values: NumericArray[P, D], mut sink: S, *, context: D.Context, options: NumericOptions = NumericOptions(), complete_only: Bool = False, max_steps: UInt64 = UInt64.MAX) raises PolyError -> RootStreamReceipt:
    """Prepare a numerical complex root cover witness stream.

    Conversion to dense coefficients shares the call budget; large sparse degrees can require substantial memory.

    Parameters:
        P: Inferred from the input types unless explicitly supplied.
        D: Inferred from the input types unless explicitly supplied.
        S: Inferred from the input types unless explicitly supplied.

    Args:
        values: Input coefficients, sparse terms, or a prepared array.
        sink: The consumer receiving ordered chunks or witnesses.
        context: Explicit precision and rounding or enclosure settings.
        options: Precision, accuracy, subdivision and isolation settings.
        complete_only: Raise unless every requested root-cover property succeeds.
        max_steps: The complete call’s work allowance.

    Returns:
        The same checked root-cover result or stream interface as dense inputs.

    Raises:
        PolyError: DOMAIN for incompatible input, UNSUPPORTED for an unavailable coefficient domain, or LIMIT/CAPACITY on resource limits.
    """
    var budget = Budget(max_steps)
    return complex_root_cover_to[P, D, S](values, sink, budget, context=context, options=options, complete_only=complete_only)


def complex_root_checker[P: Copyable & Deinitable, D: NumericDomain](values: NumericArray[P, D], mut budget: Budget, *, context: D.Context, options: NumericOptions = NumericOptions()) raises PolyError -> ComplexRootStreamChecker:
    """Prepare a numerical complex root stream checker.

    Conversion to dense coefficients shares the call budget; large sparse degrees can require substantial memory.

    Parameters:
        P: Inferred from the input types unless explicitly supplied.
        D: Inferred from the input types unless explicitly supplied.

    Args:
        values: Input coefficients, sparse terms, or a prepared array.
        budget: The shared work allowance, including preparation and output storage.
        context: Explicit precision and rounding or enclosure settings.
        options: Precision, accuracy, subdivision and isolation settings.

    Returns:
        The same checked root-cover result or stream interface as dense inputs.

    Raises:
        PolyError: DOMAIN for incompatible input, UNSUPPORTED for an unavailable coefficient domain, or LIMIT/CAPACITY on resource limits.
    """
    from . import _conversion
    comptime assert _width[P]() == 1, "root covers require a univariate power shape"
    var prepared = _conversion.to_dense(values, budget, context=context)
    return _dense.complex_root_checker[D](prepared, budget, options=options)


def complex_root_checker[P: Copyable & Deinitable, D: NumericDomain](values: NumericArray[P, D], *, context: D.Context, options: NumericOptions = NumericOptions(), max_steps: UInt64 = UInt64.MAX) raises PolyError -> ComplexRootStreamChecker:
    """Prepare a numerical complex root stream checker.

    Conversion to dense coefficients shares the call budget; large sparse degrees can require substantial memory.

    Parameters:
        P: Inferred from the input types unless explicitly supplied.
        D: Inferred from the input types unless explicitly supplied.

    Args:
        values: Input coefficients, sparse terms, or a prepared array.
        context: Explicit precision and rounding or enclosure settings.
        options: Precision, accuracy, subdivision and isolation settings.
        max_steps: The complete call’s work allowance.

    Returns:
        The same checked root-cover result or stream interface as dense inputs.

    Raises:
        PolyError: DOMAIN for incompatible input, UNSUPPORTED for an unavailable coefficient domain, or LIMIT/CAPACITY on resource limits.
    """
    var budget = Budget(max_steps)
    return complex_root_checker[P, D](values, budget, context=context, options=options)


def _division_output[P: Copyable & Deinitable, k: Int](var core: SparsePoly[_Ring[k]], mut budget: Budget) raises PolyError -> Array[P, k]:
    var canonical = _order[P](budget)
    if core.order != canonical:
        core = core.reorder(canonical, budget)
    return Array[P, k](core^, budget)


def _gcd_dispatch[C: CoefficientRing](a: SparsePoly[C], b: SparsePoly[C], method: String, mut budget: Budget, *, certify: Bool = False) raises PolyError -> GcdResult[C]:
    if method == "auto":
        return _gcd(a, b, budget, certify_maximal=certify)
    if method != "modular":
        raise PolyError(PolyErrorKind.DOMAIN, "GCD method must be auto or modular")
    comptime if C == ZZ:
        return rebind_var[GcdResult[C]](_sparse_gcd_integer(rebind[SparsePoly[ZZ]](a), rebind[SparsePoly[ZZ]](b), budget))
    elif C == QQ:
        return rebind_var[GcdResult[C]](_sparse_gcd(rebind[SparsePoly[QQ]](a), rebind[SparsePoly[QQ]](b), budget))
    else:
        raise PolyError(PolyErrorKind.UNSUPPORTED, "modular sparse GCD requires integer or rational coefficients")



def sign_on_interval[I: Iterable, P: Copyable & Deinitable, C: Copyable & Deinitable, L: Copyable & Deinitable, H: Copyable & Deinitable](values: I, low: L, high: H, mut budget: Budget) raises PolyError -> Optional[Int] where _Element[I] == Tuple[P, C]:
    """Determine the strict sign throughout a closed exact interval.

    Parameters:
        I: The inferred input type.
        P: The inferred power shape.
        C: The inferred input type.
        L: The inferred input type.
        H: The inferred input type.

    Args:
        values: Univariate integer or rational terms.
        low: The lower exact endpoint.
        high: The upper exact endpoint, possibly equal to low.
        budget: The shared work allowance for preparation and computation.

    Returns:
        Positive or negative one on a root-free closed interval; None if a root occurs, including either endpoint. The zero polynomial returns None.

    Raises:
        PolyError: DOMAIN for incompatible input, UNSUPPORTED for an unavailable operation, or LIMIT/CAPACITY on resource limits.
    """
    return _dense.sign_on_interval(_univariate(_prepare[I, P, C](values, budget), budget), low, high, budget)



def sign_on_interval[I: Iterable, P: Copyable & Deinitable, C: Copyable & Deinitable, L: Copyable & Deinitable, H: Copyable & Deinitable](values: I, low: L, high: H, *, max_steps: UInt64 = UInt64.MAX) raises PolyError -> Optional[Int] where _Element[I] == Tuple[P, C]:
    """Determine the strict sign throughout a closed exact interval.

    Parameters:
        I: The inferred input type.
        P: The inferred power shape.
        C: The inferred input type.
        L: The inferred input type.
        H: The inferred input type.

    Args:
        values: Univariate integer or rational terms.
        low: The lower exact endpoint.
        high: The upper exact endpoint, possibly equal to low.
        max_steps: The complete call's work allowance; defaults to UInt64.MAX.

    Returns:
        Positive or negative one on a root-free closed interval; None if a root occurs, including either endpoint. The zero polynomial returns None.

    Raises:
        PolyError: DOMAIN for incompatible input, UNSUPPORTED for an unavailable operation, or LIMIT/CAPACITY on resource limits.
    """
    var budget = Budget(max_steps)
    return sign_on_interval[I, P, C, L, H](values, low, high, budget)




from polynomials import projection_resultant as _projection_resultant

def resultant_certified[A: Iterable, B: Iterable, P: Copyable & Deinitable, C: Copyable & Deinitable, D: Copyable & Deinitable](a: A, b: B, mut budget: Budget, *, axis: Int = 0) raises PolyError -> _exact.Result[_FieldKind[_Join[_Kind[C], _Kind[D]]], P, True, _exact._Determinant[_FieldKind[_Join[_Kind[C], _Kind[D]]]]] where _Element[A] == Tuple[P, C] and _Element[B] == Tuple[P, D]:
    """Compute an exact resultant with a complete determinant certificate.

    Integer coefficients promote to rationals. exact.check verifies the Sylvester determinant transcript. The result retains the original power shape.

    Parameters:
        A: Inferred from the input types unless explicitly supplied.
        B: Inferred from the input types unless explicitly supplied.
        P: Inferred from the input types unless explicitly supplied.
        C: Inferred from the input types unless explicitly supplied.
        D: Inferred from the input types unless explicitly supplied.

    Args:
        a: The first polynomial.
        b: The second polynomial.
        budget: The shared work allowance, including preparation and output storage.
        axis: The zero-based polynomial axis.

    Returns:
        A retained exact resultant and determinant evidence for exact.value and exact.check.

    Raises:
        PolyError: DOMAIN for incompatible input, UNSUPPORTED for an unavailable coefficient domain, or LIMIT/CAPACITY on resource limits.
    """
    comptime k = _FieldKind[_Join[_Kind[C], _Kind[D]]]
    var pair = _pair[k, A, B, P, C, D](a, b, budget)
    var left = pair[0]._core[].reorder(pair[0]._core[].order, budget)
    var right = pair[1]._core[].reorder(pair[1]._core[].order, budget)
    _axis[P](axis)
    var proof: _exact._Determinant[k]
    comptime if k == 1:
        proof = rebind_var[_exact._Determinant[k]](_projection_resultant(rebind[SparsePoly[QQ]](left), rebind[SparsePoly[QQ]](right), Int64(axis), budget))
    else:
        from . import _determinant
        proof = rebind_var[_exact._Determinant[k]](_determinant._produce(left, right, Int64(axis), budget))
    _allocation[SparsePoly[_Ring[k]]](1, budget)
    var others: List[SparsePoly[_Ring[k]]] = [right^]
    var result = _exact._retain[k, P, True, _exact._Determinant[_FieldKind[_Join[_Kind[C], _Kind[D]]]]](left^, others^, proof^, budget, axis=axis)
    return result^



def resultant_certified[A: Iterable, B: Iterable, P: Copyable & Deinitable, C: Copyable & Deinitable, D: Copyable & Deinitable](a: A, b: B, *, axis: Int = 0, max_steps: UInt64 = UInt64.MAX) raises PolyError -> _exact.Result[_FieldKind[_Join[_Kind[C], _Kind[D]]], P, True, _exact._Determinant[_FieldKind[_Join[_Kind[C], _Kind[D]]]]] where _Element[A] == Tuple[P, C] and _Element[B] == Tuple[P, D]:
    """Compute an exact resultant with a complete determinant certificate.

    Integer coefficients promote to rationals. exact.check verifies the Sylvester determinant transcript. The result retains the original power shape.

    Parameters:
        A: Inferred from the input types unless explicitly supplied.
        B: Inferred from the input types unless explicitly supplied.
        P: Inferred from the input types unless explicitly supplied.
        C: Inferred from the input types unless explicitly supplied.
        D: Inferred from the input types unless explicitly supplied.

    Args:
        a: The first polynomial.
        b: The second polynomial.
        axis: The zero-based polynomial axis.
        max_steps: The complete call’s work allowance.

    Returns:
        A retained exact resultant and determinant evidence for exact.value and exact.check.

    Raises:
        PolyError: DOMAIN for incompatible input, UNSUPPORTED for an unavailable coefficient domain, or LIMIT/CAPACITY on resource limits.
    """
    var budget = Budget(max_steps)
    return resultant_certified[A, B, P, C, D](a, b, budget, axis=axis)


comptime _SquarefreeProof[P: Copyable & Deinitable, k: Int] = SquarefreeDecomposition[_Ring[k]] if _width[P]() == 1 else SparseSquarefreeDecomposition[_Ring[k]]


comptime _Specialized[P: Copyable & Deinitable, C: AnyType, X: AnyType] = _alg.Specialization[P] if (_Kind[C] == 0 or _Kind[C] == 1) and (_Kind[X] == 0 or _Kind[X] == 1 or _Kind[X] == 4) else _alg.AlgebraicSpecialization[P] if _Kind[C] == 4 and (_Kind[X] == 0 or _Kind[X] == 1 or _Kind[X] == 4) else Array[P, _Join[_Kind[C], _Kind[X]]]


def complex_roots[I: Iterable, P: Copyable & Deinitable, C: Copyable & Deinitable](values: I, mut budget: Budget, *, axis: Int = 0) raises PolyError -> _roots.ComplexRoots where _Element[I] == Tuple[P, C]:
    """Find every distinct exact complex root, with multiplicities.

    Results use lexicographic real-part then imaginary-part order. Nonzero
    constants return no roots. Integer, rational, Gaussian-rational, AA, and
    QQbar coefficients are accepted; no numerical precision is needed.

    Parameters:
        I: The inferred input iterable type.
        P: The sparse power shape.
        C: The exact coefficient type.

    Args:
        values: Exact sparse terms or a prepared sparse array.
        budget: The shared work allowance, including preparation and verification.
        axis: The zero-based root variable; all other axes must be absent.

    Returns:
        Exact algebraic.Complex values with multiplicities and completeness evidence.

    Raises:
        PolyError: DOMAIN for zero or incompatible input, or LIMIT/CAPACITY on resource limits.
    """
    comptime assert _Kind[C] >= 0 and _Kind[C] != 3, "exact complex roots require characteristic-zero exact coefficients"
    if axis < 0 or axis >= _width[P]():
        raise PolyError(PolyErrorKind.DOMAIN, "axis is outside the sparse power shape")
    var p = _prepare[I, P, C](values, budget)
    var core = DensePoly[_Ring[_Kind[C]]].from_sparse(p._core[], budget, variable=Int64(axis))
    return _dense.complex_roots(_dense.Array[_Kind[C]](core^, budget), budget)


def complex_roots[I: Iterable, P: Copyable & Deinitable, C: Copyable & Deinitable](values: I, *, max_steps: UInt64 = UInt64.MAX, axis: Int = 0) raises PolyError -> _roots.ComplexRoots where _Element[I] == Tuple[P, C]:
    """Find every distinct exact complex root, with multiplicities.

    Results use lexicographic real-part then imaginary-part order. Nonzero
    constants return no roots. Integer, rational, Gaussian-rational, AA, and
    QQbar coefficients are accepted; no numerical precision is needed.

    Parameters:
        I: The inferred input iterable type.
        P: The sparse power shape.
        C: The exact coefficient type.

    Args:
        values: Exact sparse terms or a prepared sparse array.
        max_steps: The complete call's work allowance; defaults to UInt64.MAX.
        axis: The zero-based root variable; all other axes must be absent.

    Returns:
        Exact algebraic.Complex values with multiplicities and completeness evidence.

    Raises:
        PolyError: DOMAIN for zero or incompatible input, or LIMIT/CAPACITY on resource limits.
    """
    var budget = Budget(max_steps)
    return complex_roots[I, P, C](values, budget, axis=axis)


def complex_roots_to[I: Iterable, S: _roots.ExactComplexRootSink, P: Copyable & Deinitable, C: Copyable & Deinitable](values: I, mut sink: S, mut budget: Budget, *, axis: Int = 0) raises PolyError -> _roots.ExactComplexRootReceipt where _Element[I] == Tuple[P, C]:
    """Stream exact complex roots with multiplicities and a completion receipt.

    Parameters:
        I: The inferred coefficient iterable.
        S: The event consumer type.
        P: The sparse power shape.
        C: The exact coefficient type.

    Args:
        values: Exact coefficients or terms over ZZ, QQ, QQi, AA, or QQbar.
        sink: A consumer of owned ExactComplexRootEvent values.
        budget: The shared preparation, production, and checking allowance.
        axis: The root variable; other axes must be absent.

    Returns:
        A receipt to verify with checker.finish. Events follow deterministic
        factor and coordinate traversal order, which need not be sorted.
        Output witnesses are not collected; algebraic working state is retained.

    Raises:
        PolyError: DOMAIN for zero or invalid input, consumer failures, or
            LIMIT/CAPACITY on resource limits. Partial streams are not complete results.
    """
    _axis[P](axis)
    var p = _prepare[I, P, C](values, budget)
    var core = DensePoly[_Ring[_Kind[C]]].from_sparse(p._core[], budget, variable=Int64(axis))
    return _dense.complex_roots_to(_dense.Array[_Kind[C]](core^, budget), sink, budget)


def complex_roots_to[I: Iterable, S: _roots.ExactComplexRootSink, P: Copyable & Deinitable, C: Copyable & Deinitable](values: I, mut sink: S, *, axis: Int = 0, max_steps: UInt64 = UInt64.MAX) raises PolyError -> _roots.ExactComplexRootReceipt where _Element[I] == Tuple[P, C]:
    """Stream exact complex roots with multiplicities and a completion receipt.

    Parameters:
        I: The inferred coefficient iterable.
        S: The event consumer type.
        P: The sparse power shape.
        C: The exact coefficient type.

    Args:
        values: Exact coefficients or terms over ZZ, QQ, QQi, AA, or QQbar.
        sink: A consumer of owned ExactComplexRootEvent values.
        axis: The root variable; other axes must be absent.
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
    return complex_roots_to[I, S, P, C](values, sink, budget, axis=axis)


def complex_roots_checker[I: Iterable, P: Copyable & Deinitable, C: Copyable & Deinitable](values: I, mut budget: Budget, *, axis: Int = 0) raises PolyError -> _roots.ExactComplexRootChecker where _Element[I] == Tuple[P, C]:
    """Prepare independent incremental checking of exact complex roots.

    Parameters:
        I: The inferred coefficient iterable.
        P: The sparse power shape.
        C: The exact coefficient type.

    Args:
        values: Exact coefficients or terms over ZZ, QQ, QQi, AA, or QQbar.
        budget: The shared preparation, production, and checking allowance.
        axis: The root variable; other axes must be absent.

    Returns:
        A checker accepting root events; finish verifies complete reconstruction.

    Raises:
        PolyError: DOMAIN for zero or invalid input, consumer failures, or
            LIMIT/CAPACITY on resource limits. Partial streams are not complete results.
    """
    _axis[P](axis)
    var p = _prepare[I, P, C](values, budget)
    var core = DensePoly[_Ring[_Kind[C]]].from_sparse(p._core[], budget, variable=Int64(axis))
    return _dense.complex_roots_checker(_dense.Array[_Kind[C]](core^, budget), budget)


def complex_roots_checker[I: Iterable, P: Copyable & Deinitable, C: Copyable & Deinitable](values: I, *, axis: Int = 0, max_steps: UInt64 = UInt64.MAX) raises PolyError -> _roots.ExactComplexRootChecker where _Element[I] == Tuple[P, C]:
    """Prepare independent incremental checking of exact complex roots.

    Parameters:
        I: The inferred coefficient iterable.
        P: The sparse power shape.
        C: The exact coefficient type.

    Args:
        values: Exact coefficients or terms over ZZ, QQ, QQi, AA, or QQbar.
        axis: The root variable; other axes must be absent.
        max_steps: The complete call's work allowance.

    Returns:
        A checker accepting root events; finish verifies complete reconstruction.

    Raises:
        PolyError: DOMAIN for zero or invalid input, consumer failures, or
            LIMIT/CAPACITY on resource limits. Partial streams are not complete results.
    """
    var budget = Budget(max_steps)
    return complex_roots_checker[I, P, C](values, budget, axis=axis)


def real_roots[P: Copyable & Deinitable](values: _alg.AlgebraicSpecialization[P], mut budget: Budget, *, axis: Int = 0) raises PolyError -> _roots.SpecializedRoots[P, 4]:
    """Find every distinct real root of a univariate specialization.

    Parameters:
        P: Inferred from the input types.

    Args:
        values: Coefficients, terms, or a prepared value.
        budget: The shared work allowance.
        axis: The zero-based variable axis.

    Returns:
        All distinct real roots in increasing order, with specialization and completeness evidence.

    Raises:
        PolyError: DOMAIN for invalid input, or LIMIT/CAPACITY on resource limits.
    """
    if axis < 0 or axis >= _width[P]():
        raise PolyError(PolyErrorKind.DOMAIN, "root axis outside the power shape")
    for assignment in values._point[]:
        budget.charge(1)
        if assignment[0] == Int64(axis):
            raise PolyError(PolyErrorKind.DOMAIN, "root axis must remain unassigned")
    var coefficients = _alg.coefficients(values, budget, axis=axis)
    var result = _roots._exact_coefficients(coefficients, budget)
    return _roots.SpecializedRoots[P, 4](values.copy(), result^, axis)


def real_roots[P: Copyable & Deinitable](values: _alg.AlgebraicSpecialization[P], *, axis: Int = 0, max_steps: UInt64 = UInt64.MAX) raises PolyError -> _roots.SpecializedRoots[P, 4]:
    """Find every distinct real root of a univariate specialization.

    Parameters:
        P: Inferred from the input types.

    Args:
        values: Coefficients, terms, or a prepared value.
        axis: The zero-based variable axis.
        max_steps: The complete call's work allowance.

    Returns:
        All distinct real roots in increasing order, with specialization and completeness evidence.

    Raises:
        PolyError: DOMAIN for invalid input, or LIMIT/CAPACITY on resource limits.
    """
    var budget = Budget(max_steps)
    return real_roots(values, budget, axis=axis)

from . import _numeric_interop as _ni


def astype[dtype: AnyType, I: Iterable, Context: Copyable & Deinitable, P: Copyable & Deinitable, C: Copyable & Deinitable](values: I, mut budget: Budget, *, context: Context) raises PolyError -> NumericArray[P, _num._StoredDomain[dtype]] where _Element[I] == Tuple[P, C]:
    """Convert every coefficient to an explicit numerical type and precision.

    Unlike asarray on a prepared array, this also converts within the same
    domain. Real destinations require exactly zero imaginary bounds; point
    destinations require certain rounding. Inputs remain unchanged.

    Parameters:
        dtype: Float, Complex, Ball, or ComplexBall.
        I: The inferred term iterable type.
        Context: The matching explicit precision context.
        P: The common sparse power shape.
        C: The first or homogeneous coefficient type.

    Args:
        values: Raw sparse terms or a prepared sparse array.
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
    var entries = List[NumericTerm[D]]()
    var cursor = iter(values)
    while True:
        budget.charge(1)
        var value: Tuple[P, C]
        try:
            value = rebind_var[Tuple[P, C]](next(cursor))
        except StopIteration:
            break
        _grow(entries, budget)
        entries.append(NumericTerm[D](_monomial(value[0], budget), _num._value[D](value[1], ctx, budget)))
    return NumericArray[P, D](NumericSparsePoly[D].from_terms(entries^, _order[P](budget), ctx, budget), budget)


def astype[dtype: AnyType, I: Iterable, Context: Copyable & Deinitable, P: Copyable & Deinitable, C: Copyable & Deinitable](values: I, *, context: Context, max_steps: UInt64 = UInt64.MAX) raises PolyError -> NumericArray[P, _num._StoredDomain[dtype]] where _Element[I] == Tuple[P, C]:
    """Convert every coefficient to an explicit numerical type and precision.

    Unlike asarray on a prepared array, this also converts within the same
    domain. Real destinations require exactly zero imaginary bounds; point
    destinations require certain rounding. Inputs remain unchanged.

    Parameters:
        dtype: Float, Complex, Ball, or ComplexBall.
        I: The inferred term iterable type.
        Context: The matching explicit precision context.
        P: The common sparse power shape.
        C: The first or homogeneous coefficient type.

    Args:
        values: Raw sparse terms or a prepared sparse array.
        context: ArithmeticContext for Float, ComplexContext for Complex, or BallContext for balls.
        max_steps: The complete conversion allowance.

    Returns:
        An immutable array with rounded points or enclosing balls in the requested type.

    Raises:
        PolyError: DOMAIN for nonreal or uncertain point conversion, or LIMIT/CAPACITY.
    """
    var budget = Budget(max_steps)
    return astype[dtype, I, Context, P, C](values, budget, context=context)


def astype[dtype: AnyType, Context: Copyable & Deinitable, P: Copyable & Deinitable, C: Copyable & Deinitable, *Ts: Copyable & Deinitable](values: Tuple[*Ts], mut budget: Budget, *, context: Context) raises PolyError -> NumericArray[P, _num._StoredDomain[dtype]] where Tuple[*Ts].Ts[0] == Tuple[P, C]:
    """Convert every coefficient to an explicit numerical type and precision.

    Unlike asarray on a prepared array, this also converts within the same
    domain. Real destinations require exactly zero imaginary bounds; point
    destinations require certain rounding. Inputs remain unchanged.

    Parameters:
        dtype: Float, Complex, Ball, or ComplexBall.
        Context: The matching explicit precision context.
        P: The common sparse power shape.
        C: The first or homogeneous coefficient type.
        Ts: The inferred mixed term types.

    Args:
        values: Raw sparse terms or a prepared sparse array.
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
    var entries = List[NumericTerm[D]]()
    _allocation[NumericTerm[D]](Tuple[*Ts].Ts.length, budget)
    entries.reserve(Tuple[*Ts].Ts.length)
    comptime for i in range(Tuple[*Ts].Ts.length):
        budget.charge(1)
        comptime T = Tuple[*Ts].Ts[i]
        comptime S = _NumericTermScalar[P, T]
        comptime assert T == Tuple[P, S] and (_Kind[S] >= 0 or _num._IsNumeric[S]), "sparse tuples need numeric pairs with one power shape"
        ref term = rebind[Tuple[P, S]](values[i])
        entries.append(NumericTerm[D](_monomial(term[0], budget), _num._value[D](term[1], ctx, budget)))
    return NumericArray[P, D](NumericSparsePoly[D].from_terms(entries^, _order[P](budget), ctx, budget), budget)


def astype[dtype: AnyType, Context: Copyable & Deinitable, P: Copyable & Deinitable, C: Copyable & Deinitable, *Ts: Copyable & Deinitable](values: Tuple[*Ts], *, context: Context, max_steps: UInt64 = UInt64.MAX) raises PolyError -> NumericArray[P, _num._StoredDomain[dtype]] where Tuple[*Ts].Ts[0] == Tuple[P, C]:
    """Convert every coefficient to an explicit numerical type and precision.

    Unlike asarray on a prepared array, this also converts within the same
    domain. Real destinations require exactly zero imaginary bounds; point
    destinations require certain rounding. Inputs remain unchanged.

    Parameters:
        dtype: Float, Complex, Ball, or ComplexBall.
        Context: The matching explicit precision context.
        P: The common sparse power shape.
        C: The first or homogeneous coefficient type.
        Ts: The inferred mixed term types.

    Args:
        values: Raw sparse terms or a prepared sparse array.
        context: ArithmeticContext for Float, ComplexContext for Complex, or BallContext for balls.
        max_steps: The complete conversion allowance.

    Returns:
        An immutable array with rounded points or enclosing balls in the requested type.

    Raises:
        PolyError: DOMAIN for nonreal or uncertain point conversion, or LIMIT/CAPACITY.
    """
    var budget = Budget(max_steps)
    return astype[dtype, Context, P, C, *Ts](values, budget, context=context)


def leading_term[I: Iterable, P: Copyable & Deinitable, C: Copyable & Deinitable](values: I, mut budget: Budget, *, order: String = "lex", axes: List[Int] = List[Int]()) raises PolyError -> Tuple[P, _Scalar[_Kind[C]]] where (_Element[I] == Tuple[P, C] and _Kind[C] >= 0):
    """Return the greatest stored term under the requested monomial order.

    Parameters:
        I: The inferred sparse input iterable.
        P: The common sparse power shape.
        C: The inferred exact coefficient type.

    Args:
        values: Sparse terms or a prepared array.
        budget: The shared query allowance.
        order: One of lex, grlex, or grevlex; defaults to lex.
        axes: All axes in descending priority; empty uses tuple order.

    Returns:
        The power and coefficient, leaving input storage unchanged.

    Raises:
        PolyError: DOMAIN for zero or invalid order settings, or LIMIT/CAPACITY.
    """
    var p = _prepare[I, P, C](values, budget)
    var choice = _monomial_order[P](order, axes, budget)
    if not len(p):
        raise PolyError(PolyErrorKind.DOMAIN, "zero has no leading term")
    var index = 0
    for i in range(1, len(p)):
        if choice.compare(p._core[].terms[index].monomial, p._core[].terms[i].monomial, budget) < 0:
            index = i
    _charge_size(_width[P](), budget)
    _charge_size(p._core[].terms[index].coefficient.size(), budget)
    return p[index]


def leading_term[I: Iterable, P: Copyable & Deinitable, C: Copyable & Deinitable](values: I, *, max_steps: UInt64 = UInt64.MAX, order: String = "lex", axes: List[Int] = List[Int]()) raises PolyError -> Tuple[P, _Scalar[_Kind[C]]] where (_Element[I] == Tuple[P, C] and _Kind[C] >= 0):
    """Return the greatest stored term under the requested monomial order.

    Parameters:
        I: The inferred sparse input iterable.
        P: The common sparse power shape.
        C: The inferred exact coefficient type.

    Args:
        values: Sparse terms or a prepared array.
        max_steps: The complete query allowance.
        order: One of lex, grlex, or grevlex; defaults to lex.
        axes: All axes in descending priority; empty uses tuple order.

    Returns:
        The power and coefficient, leaving input storage unchanged.

    Raises:
        PolyError: DOMAIN for zero or invalid order settings, or LIMIT/CAPACITY.
    """
    var budget = Budget(max_steps)
    return leading_term[I, P, C](values, budget, order=order, axes=axes)


def variables[I: Iterable, P: Copyable & Deinitable, C: Copyable & Deinitable](values: I, mut budget: Budget) raises PolyError -> List[Int] where (_Element[I] == Tuple[P, C] and _Kind[C] >= 0):
    """Return the sorted axes occurring in stored nonzero terms.

    Parameters:
        I: The inferred sparse input iterable.
        P: The common sparse power shape.
        C: The inferred exact coefficient type.

    Args:
        values: Sparse terms or a prepared array.
        budget: The shared query allowance.

    Returns:
        Occurring axis numbers; constants and zero return an empty list.

    Raises:
        PolyError: DOMAIN for invalid input, or LIMIT/CAPACITY.
    """
    var p = _prepare[I, P, C](values, budget)
    _allocation[Bool](_width[P](), budget)
    var active = List[Bool](capacity=_width[P]())
    for _ in range(_width[P]()):
        budget.charge(1)
        active.append(False)
    for term in p._core[].terms:
        budget.charge(1)
        for pair in term.monomial.pairs:
            budget.charge(1)
            active[Int(pair[0])] = True
    var result = List[Int]()
    for i in range(len(active)):
        budget.charge(1)
        if active[i]:
            _grow(result, budget)
            result.append(i)
    return result^


def variables[I: Iterable, P: Copyable & Deinitable, C: Copyable & Deinitable](values: I, *, max_steps: UInt64 = UInt64.MAX) raises PolyError -> List[Int] where (_Element[I] == Tuple[P, C] and _Kind[C] >= 0):
    """Return the sorted axes occurring in stored nonzero terms.

    Parameters:
        I: The inferred sparse input iterable.
        P: The common sparse power shape.
        C: The inferred exact coefficient type.

    Args:
        values: Sparse terms or a prepared array.
        max_steps: The complete query allowance.

    Returns:
        Occurring axis numbers; constants and zero return an empty list.

    Raises:
        PolyError: DOMAIN for invalid input, or LIMIT/CAPACITY.
    """
    var budget = Budget(max_steps)
    return variables[I, P, C](values, budget)


def leading_term[P: Copyable & Deinitable, D: NumericDomain](values: NumericArray[P, D], mut budget: Budget, *, order: String = "lex", axes: List[Int] = List[Int]()) raises PolyError -> Tuple[P, D.Scalar]:
    """Return the greatest stored term under the requested monomial order.

    Ball coefficients may contain zero; this inspects stored support, not a
    uniform leading term or variable set for every member of a ball family.

    Parameters:
        P: The common sparse power shape.
        D: The stored numerical domain.

    Args:
        values: Sparse terms or a prepared array.
        budget: The shared query allowance.
        order: One of lex, grlex, or grevlex; defaults to lex.
        axes: All axes in descending priority; empty uses tuple order.

    Returns:
        The power and coefficient, leaving input storage unchanged.

    Raises:
        PolyError: DOMAIN for zero or invalid order settings, or LIMIT/CAPACITY.
    """
    ref p = values
    var choice = _monomial_order[P](order, axes, budget)
    if not len(p):
        raise PolyError(PolyErrorKind.DOMAIN, "zero has no leading term")
    var index = 0
    for i in range(1, len(p)):
        if choice.compare(p._core[].terms[index].monomial, p._core[].terms[i].monomial, budget) < 0:
            index = i
    _charge_size(_width[P](), budget)
    _ = _num._bounds(p._core[].terms[index].coefficient, budget)
    return p[index]


def leading_term[P: Copyable & Deinitable, D: NumericDomain](values: NumericArray[P, D], *, max_steps: UInt64 = UInt64.MAX, order: String = "lex", axes: List[Int] = List[Int]()) raises PolyError -> Tuple[P, D.Scalar]:
    """Return the greatest stored term under the requested monomial order.

    Ball coefficients may contain zero; this inspects stored support, not a
    uniform leading term or variable set for every member of a ball family.

    Parameters:
        P: The common sparse power shape.
        D: The stored numerical domain.

    Args:
        values: Sparse terms or a prepared array.
        max_steps: The complete query allowance.
        order: One of lex, grlex, or grevlex; defaults to lex.
        axes: All axes in descending priority; empty uses tuple order.

    Returns:
        The power and coefficient, leaving input storage unchanged.

    Raises:
        PolyError: DOMAIN for zero or invalid order settings, or LIMIT/CAPACITY.
    """
    var budget = Budget(max_steps)
    return leading_term[P, D](values, budget, order=order, axes=axes)


def variables[P: Copyable & Deinitable, D: NumericDomain](values: NumericArray[P, D], mut budget: Budget) raises PolyError -> List[Int]:
    """Return the sorted axes occurring in stored nonzero terms.

    Ball coefficients may contain zero; this inspects stored support, not a
    uniform leading term or variable set for every member of a ball family.

    Parameters:
        P: The common sparse power shape.
        D: The stored numerical domain.

    Args:
        values: Sparse terms or a prepared array.
        budget: The shared query allowance.

    Returns:
        Occurring axis numbers; constants and zero return an empty list.

    Raises:
        PolyError: DOMAIN for invalid input, or LIMIT/CAPACITY.
    """
    ref p = values
    _allocation[Bool](_width[P](), budget)
    var active = List[Bool](capacity=_width[P]())
    for _ in range(_width[P]()):
        budget.charge(1)
        active.append(False)
    for term in p._core[].terms:
        budget.charge(1)
        for pair in term.monomial.pairs:
            budget.charge(1)
            active[Int(pair[0])] = True
    var result = List[Int]()
    for i in range(len(active)):
        budget.charge(1)
        if active[i]:
            _grow(result, budget)
            result.append(i)
    return result^


def variables[P: Copyable & Deinitable, D: NumericDomain](values: NumericArray[P, D], *, max_steps: UInt64 = UInt64.MAX) raises PolyError -> List[Int]:
    """Return the sorted axes occurring in stored nonzero terms.

    Ball coefficients may contain zero; this inspects stored support, not a
    uniform leading term or variable set for every member of a ball family.

    Parameters:
        P: The common sparse power shape.
        D: The stored numerical domain.

    Args:
        values: Sparse terms or a prepared array.
        max_steps: The complete query allowance.

    Returns:
        Occurring axis numbers; constants and zero return an empty list.

    Raises:
        PolyError: DOMAIN for invalid input, or LIMIT/CAPACITY.
    """
    var budget = Budget(max_steps)
    return variables[P, D](values, budget)

from . import _sturm


def sturm_sequence[I: Iterable, P: Copyable & Deinitable, C: Copyable & Deinitable](values: I, mut budget: Budget, *, axis: Int = 0) raises PolyError -> _sturm.SturmPlan where _Element[I] == Tuple[P, C]:
    """Prepare a reusable rational Sturm chain for root and sign-variation queries.

    Parameters:
        I: The inferred polynomial iterable.
        P: The sparse power shape.
        C: The integer or rational coefficient type.

    Args:
        values: Nonzero sparse polynomial terms over ZZ or QQ.
        budget: The shared preparation allowance.
        axis: The only axis allowed to have nonzero powers.

    Returns:
        An immutable plan retaining the polynomial, chain, and quotient witnesses.

    Raises:
        PolyError: DOMAIN for zero or an invalid axis, or LIMIT/CAPACITY.
    """
    comptime assert _Kind[C] == 0 or _Kind[C] == 1, "Sturm preparation requires integer or rational coefficients"
    if axis < 0 or axis >= _width[P]():
        raise PolyError(PolyErrorKind.DOMAIN, "Sturm axis is outside the power shape")
    var prepared = _prepare[I, P, C](values, budget)
    var rational = _promote[1](prepared, NoContext(), budget)
    var core = DensePoly[QQ].from_sparse(rational._core[], budget, variable=Optional(Int64(axis)))
    core.variable = 0
    return _sturm._make(core^, budget)


def sturm_sequence[I: Iterable, P: Copyable & Deinitable, C: Copyable & Deinitable](values: I, *, max_steps: UInt64 = UInt64.MAX, axis: Int = 0) raises PolyError -> _sturm.SturmPlan where _Element[I] == Tuple[P, C]:
    """Prepare a reusable rational Sturm chain for root and sign-variation queries.

    Parameters:
        I: The inferred polynomial iterable.
        P: The sparse power shape.
        C: The integer or rational coefficient type.

    Args:
        values: Nonzero sparse polynomial terms over ZZ or QQ.
        max_steps: The complete preparation allowance.
        axis: The only axis allowed to have nonzero powers.

    Returns:
        An immutable plan retaining the polynomial, chain, and quotient witnesses.

    Raises:
        PolyError: DOMAIN for zero or an invalid axis, or LIMIT/CAPACITY.
    """
    var budget = Budget(max_steps)
    return sturm_sequence[I, P, C](values, budget, axis=axis)

comptime _NumericTermScalar[P: Movable, T: Movable] = _num.Float if T == Tuple[P, _num.Float] else _num.Complex if T == Tuple[P, _num.Complex] else _num.Ball if T == Tuple[P, _num.Ball] else _num.ComplexBall if T == Tuple[P, _num.ComplexBall] else Float64 if T == Tuple[P, Float64] else Float32 if T == Tuple[P, Float32] else Float16 if T == Tuple[P, Float16] else BFloat16 if T == Tuple[P, BFloat16] else _TermScalar[P, T]

def _scalar_operation[op: Int, reverse: Bool, I: Iterable, S: Copyable & Deinitable, P: Copyable & Deinitable, C: Copyable & Deinitable](values: I, scalar: S, mut budget: Budget) raises PolyError -> Array[P, _FieldKind[_Join[_Kind[C], _Kind[S]]] if op == 3 else _Join[_Kind[C], _Kind[S]]] where (_Element[I] == Tuple[P, C] and _Kind[C] >= 0 and _Kind[S] >= 0):
    comptime k = _FieldKind[_Join[_Kind[C], _Kind[S]]] if op == 3 else _Join[_Kind[C], _Kind[S]]
    var p: Array[P, k]
    var ctx: _Ring[k].Context
    comptime if k == 3 and S == ModInt:
        ctx = _data_context[k](_initial_modulus(values), rebind[ModInt](scalar).modulus, budget)
        p = rebind_var[Array[P, k]](asarray[I, P, C](values, budget, modulus=rebind[Modulus](ctx).value))
    else:
        var original = _prepare[I, P, C](values, budget)
        ctx = _data_context[k](original.modulus(), 0, budget)
        p = _promote[k](original, ctx, budget)
    var c = _wrap[k](_convert[k](scalar, ctx, budget))
    comptime if op == 2:
        return Array[P, k](p._core[].scale(c, budget), budget)
    elif op == 3:
        return Array[P, k](p._core[].scale(rebind_var[_Ring[k]](rebind[downcast[_Ring[k], CoefficientField]](c).inverse(budget)), budget), budget)
    else:
        var q = SparsePoly[_Ring[k]].constant(c, p._core[].order, budget)
        comptime if op == 0:
            return Array[P, k](p._core[].add(q, budget), budget)
        elif reverse:
            return Array[P, k](q.sub(p._core[], budget), budget)
        else:
            return Array[P, k](p._core[].sub(q, budget), budget)


def _numeric_scalar_operation[op: Int, reverse: Bool, P: Copyable & Deinitable, D: NumericDomain, S: Copyable & Deinitable](values: NumericArray[P, D], scalar: S, mut budget: Budget, *, context: D.Context) raises PolyError -> NumericArray[P, D]:
    _num._context[D](context, budget)
    var c = _num._value[D](scalar, context, budget)
    comptime if op == 2 or op == 3:
        return NumericArray[P, D](values._core[].scale(c, context, budget, divide=op == 3), budget)
    else:
        _allocation[NumericTerm[D]](1, budget)
        var q = NumericSparsePoly[D].from_terms([NumericTerm[D](Monomial(), c^)], values._core[].order, context, budget)
        comptime if op == 0:
            return NumericArray[P, D](values._core[].add(q, context, budget), budget)
        elif reverse:
            return NumericArray[P, D](q.sub(values._core[], context, budget), budget)
        else:
            return NumericArray[P, D](values._core[].sub(q, context, budget), budget)


def add[I: Iterable, S: Copyable & Deinitable, P: Copyable & Deinitable, C: Copyable & Deinitable](values: I, scalar: S, mut budget: Budget) raises PolyError -> Array[P, _Join[_Kind[C], _Kind[S]]] where (_Element[I] == Tuple[P, C] and _Kind[C] >= 0 and _Kind[S] >= 0):
    """Add a scalar constant to a polynomial.

    Exact domains promote together. Modular inputs must have the same
    prime. Inputs remain unchanged.

    Parameters:
        I: The inferred polynomial iterable.
        S: The scalar operand type.
        P: The retained sparse power shape.
        C: The input coefficient type.

    Args:
        values: Sparse terms or a prepared array.
        scalar: The scalar constant.
        budget: The shared work allowance, including conversion and storage.

    Returns:
        A new polynomial in the common exact domain.

    Raises:
        PolyError: DOMAIN for incompatible scalars; LIMIT/CAPACITY on resource limits.
    """
    return _scalar_operation[0, False, I, S, P, C](values, scalar, budget)


def add[I: Iterable, S: Copyable & Deinitable, P: Copyable & Deinitable, C: Copyable & Deinitable](values: I, scalar: S, *, max_steps: UInt64 = UInt64.MAX) raises PolyError -> Array[P, _Join[_Kind[C], _Kind[S]]] where (_Element[I] == Tuple[P, C] and _Kind[C] >= 0 and _Kind[S] >= 0):
    """Add a scalar constant to a polynomial.

    Exact domains promote together. Modular inputs must have the same
    prime. Inputs remain unchanged.

    Parameters:
        I: The inferred polynomial iterable.
        S: The scalar operand type.
        P: The retained sparse power shape.
        C: The input coefficient type.

    Args:
        values: Sparse terms or a prepared array.
        scalar: The scalar constant.
        max_steps: The complete call allowance.

    Returns:
        A new polynomial in the common exact domain.

    Raises:
        PolyError: DOMAIN for incompatible scalars; LIMIT/CAPACITY on resource limits.
    """
    var budget = Budget(max_steps)
    return _scalar_operation[0, False, I, S, P, C](values, scalar, budget)


def add[I: Iterable, S: Copyable & Deinitable, P: Copyable & Deinitable, C: Copyable & Deinitable](scalar: S, values: I, mut budget: Budget) raises PolyError -> Array[P, _Join[_Kind[C], _Kind[S]]] where (_Element[I] == Tuple[P, C] and _Kind[C] >= 0 and _Kind[S] >= 0):
    """Add a scalar constant to a polynomial.

    Exact domains promote together. Modular inputs must have the same
    prime. Inputs remain unchanged.

    Parameters:
        I: The inferred polynomial iterable.
        S: The scalar operand type.
        P: The retained sparse power shape.
        C: The input coefficient type.

    Args:
        scalar: The scalar constant.
        values: Sparse terms or a prepared array.
        budget: The shared work allowance, including conversion and storage.

    Returns:
        A new polynomial in the common exact domain.

    Raises:
        PolyError: DOMAIN for incompatible scalars; LIMIT/CAPACITY on resource limits.
    """
    return _scalar_operation[0, True, I, S, P, C](values, scalar, budget)


def add[I: Iterable, S: Copyable & Deinitable, P: Copyable & Deinitable, C: Copyable & Deinitable](scalar: S, values: I, *, max_steps: UInt64 = UInt64.MAX) raises PolyError -> Array[P, _Join[_Kind[C], _Kind[S]]] where (_Element[I] == Tuple[P, C] and _Kind[C] >= 0 and _Kind[S] >= 0):
    """Add a scalar constant to a polynomial.

    Exact domains promote together. Modular inputs must have the same
    prime. Inputs remain unchanged.

    Parameters:
        I: The inferred polynomial iterable.
        S: The scalar operand type.
        P: The retained sparse power shape.
        C: The input coefficient type.

    Args:
        scalar: The scalar constant.
        values: Sparse terms or a prepared array.
        max_steps: The complete call allowance.

    Returns:
        A new polynomial in the common exact domain.

    Raises:
        PolyError: DOMAIN for incompatible scalars; LIMIT/CAPACITY on resource limits.
    """
    var budget = Budget(max_steps)
    return _scalar_operation[0, True, I, S, P, C](values, scalar, budget)


def subtract[I: Iterable, S: Copyable & Deinitable, P: Copyable & Deinitable, C: Copyable & Deinitable](values: I, scalar: S, mut budget: Budget) raises PolyError -> Array[P, _Join[_Kind[C], _Kind[S]]] where (_Element[I] == Tuple[P, C] and _Kind[C] >= 0 and _Kind[S] >= 0):
    """Subtract a scalar constant or a polynomial in operand order.

    Exact domains promote together. Modular inputs must have the same
    prime. Inputs remain unchanged.

    Parameters:
        I: The inferred polynomial iterable.
        S: The scalar operand type.
        P: The retained sparse power shape.
        C: The input coefficient type.

    Args:
        values: Sparse terms or a prepared array.
        scalar: The scalar constant.
        budget: The shared work allowance, including conversion and storage.

    Returns:
        A new polynomial in the common exact domain.

    Raises:
        PolyError: DOMAIN for incompatible scalars; LIMIT/CAPACITY on resource limits.
    """
    return _scalar_operation[1, False, I, S, P, C](values, scalar, budget)


def subtract[I: Iterable, S: Copyable & Deinitable, P: Copyable & Deinitable, C: Copyable & Deinitable](values: I, scalar: S, *, max_steps: UInt64 = UInt64.MAX) raises PolyError -> Array[P, _Join[_Kind[C], _Kind[S]]] where (_Element[I] == Tuple[P, C] and _Kind[C] >= 0 and _Kind[S] >= 0):
    """Subtract a scalar constant or a polynomial in operand order.

    Exact domains promote together. Modular inputs must have the same
    prime. Inputs remain unchanged.

    Parameters:
        I: The inferred polynomial iterable.
        S: The scalar operand type.
        P: The retained sparse power shape.
        C: The input coefficient type.

    Args:
        values: Sparse terms or a prepared array.
        scalar: The scalar constant.
        max_steps: The complete call allowance.

    Returns:
        A new polynomial in the common exact domain.

    Raises:
        PolyError: DOMAIN for incompatible scalars; LIMIT/CAPACITY on resource limits.
    """
    var budget = Budget(max_steps)
    return _scalar_operation[1, False, I, S, P, C](values, scalar, budget)


def subtract[I: Iterable, S: Copyable & Deinitable, P: Copyable & Deinitable, C: Copyable & Deinitable](scalar: S, values: I, mut budget: Budget) raises PolyError -> Array[P, _Join[_Kind[C], _Kind[S]]] where (_Element[I] == Tuple[P, C] and _Kind[C] >= 0 and _Kind[S] >= 0):
    """Subtract a scalar constant or a polynomial in operand order.

    Exact domains promote together. Modular inputs must have the same
    prime. Inputs remain unchanged.

    Parameters:
        I: The inferred polynomial iterable.
        S: The scalar operand type.
        P: The retained sparse power shape.
        C: The input coefficient type.

    Args:
        scalar: The scalar constant.
        values: Sparse terms or a prepared array.
        budget: The shared work allowance, including conversion and storage.

    Returns:
        A new polynomial in the common exact domain.

    Raises:
        PolyError: DOMAIN for incompatible scalars; LIMIT/CAPACITY on resource limits.
    """
    return _scalar_operation[1, True, I, S, P, C](values, scalar, budget)


def subtract[I: Iterable, S: Copyable & Deinitable, P: Copyable & Deinitable, C: Copyable & Deinitable](scalar: S, values: I, *, max_steps: UInt64 = UInt64.MAX) raises PolyError -> Array[P, _Join[_Kind[C], _Kind[S]]] where (_Element[I] == Tuple[P, C] and _Kind[C] >= 0 and _Kind[S] >= 0):
    """Subtract a scalar constant or a polynomial in operand order.

    Exact domains promote together. Modular inputs must have the same
    prime. Inputs remain unchanged.

    Parameters:
        I: The inferred polynomial iterable.
        S: The scalar operand type.
        P: The retained sparse power shape.
        C: The input coefficient type.

    Args:
        scalar: The scalar constant.
        values: Sparse terms or a prepared array.
        max_steps: The complete call allowance.

    Returns:
        A new polynomial in the common exact domain.

    Raises:
        PolyError: DOMAIN for incompatible scalars; LIMIT/CAPACITY on resource limits.
    """
    var budget = Budget(max_steps)
    return _scalar_operation[1, True, I, S, P, C](values, scalar, budget)


def multiply[I: Iterable, S: Copyable & Deinitable, P: Copyable & Deinitable, C: Copyable & Deinitable](values: I, scalar: S, mut budget: Budget) raises PolyError -> Array[P, _Join[_Kind[C], _Kind[S]]] where (_Element[I] == Tuple[P, C] and _Kind[C] >= 0 and _Kind[S] >= 0):
    """Multiply every coefficient by a scalar.

    Exact domains promote together. Modular inputs must have the same
    prime. Inputs remain unchanged.

    Parameters:
        I: The inferred polynomial iterable.
        S: The scalar operand type.
        P: The retained sparse power shape.
        C: The input coefficient type.

    Args:
        values: Sparse terms or a prepared array.
        scalar: The scalar constant.
        budget: The shared work allowance, including conversion and storage.

    Returns:
        A new polynomial in the common exact domain.

    Raises:
        PolyError: DOMAIN for incompatible scalars; LIMIT/CAPACITY on resource limits.
    """
    return _scalar_operation[2, False, I, S, P, C](values, scalar, budget)


def multiply[I: Iterable, S: Copyable & Deinitable, P: Copyable & Deinitable, C: Copyable & Deinitable](values: I, scalar: S, *, max_steps: UInt64 = UInt64.MAX) raises PolyError -> Array[P, _Join[_Kind[C], _Kind[S]]] where (_Element[I] == Tuple[P, C] and _Kind[C] >= 0 and _Kind[S] >= 0):
    """Multiply every coefficient by a scalar.

    Exact domains promote together. Modular inputs must have the same
    prime. Inputs remain unchanged.

    Parameters:
        I: The inferred polynomial iterable.
        S: The scalar operand type.
        P: The retained sparse power shape.
        C: The input coefficient type.

    Args:
        values: Sparse terms or a prepared array.
        scalar: The scalar constant.
        max_steps: The complete call allowance.

    Returns:
        A new polynomial in the common exact domain.

    Raises:
        PolyError: DOMAIN for incompatible scalars; LIMIT/CAPACITY on resource limits.
    """
    var budget = Budget(max_steps)
    return _scalar_operation[2, False, I, S, P, C](values, scalar, budget)


def multiply[I: Iterable, S: Copyable & Deinitable, P: Copyable & Deinitable, C: Copyable & Deinitable](scalar: S, values: I, mut budget: Budget) raises PolyError -> Array[P, _Join[_Kind[C], _Kind[S]]] where (_Element[I] == Tuple[P, C] and _Kind[C] >= 0 and _Kind[S] >= 0):
    """Multiply every coefficient by a scalar.

    Exact domains promote together. Modular inputs must have the same
    prime. Inputs remain unchanged.

    Parameters:
        I: The inferred polynomial iterable.
        S: The scalar operand type.
        P: The retained sparse power shape.
        C: The input coefficient type.

    Args:
        scalar: The scalar constant.
        values: Sparse terms or a prepared array.
        budget: The shared work allowance, including conversion and storage.

    Returns:
        A new polynomial in the common exact domain.

    Raises:
        PolyError: DOMAIN for incompatible scalars; LIMIT/CAPACITY on resource limits.
    """
    return _scalar_operation[2, True, I, S, P, C](values, scalar, budget)


def multiply[I: Iterable, S: Copyable & Deinitable, P: Copyable & Deinitable, C: Copyable & Deinitable](scalar: S, values: I, *, max_steps: UInt64 = UInt64.MAX) raises PolyError -> Array[P, _Join[_Kind[C], _Kind[S]]] where (_Element[I] == Tuple[P, C] and _Kind[C] >= 0 and _Kind[S] >= 0):
    """Multiply every coefficient by a scalar.

    Exact domains promote together. Modular inputs must have the same
    prime. Inputs remain unchanged.

    Parameters:
        I: The inferred polynomial iterable.
        S: The scalar operand type.
        P: The retained sparse power shape.
        C: The input coefficient type.

    Args:
        scalar: The scalar constant.
        values: Sparse terms or a prepared array.
        max_steps: The complete call allowance.

    Returns:
        A new polynomial in the common exact domain.

    Raises:
        PolyError: DOMAIN for incompatible scalars; LIMIT/CAPACITY on resource limits.
    """
    var budget = Budget(max_steps)
    return _scalar_operation[2, True, I, S, P, C](values, scalar, budget)


def divide[I: Iterable, S: Copyable & Deinitable, P: Copyable & Deinitable, C: Copyable & Deinitable](values: I, scalar: S, mut budget: Budget) raises PolyError -> Array[P, _FieldKind[_Join[_Kind[C], _Kind[S]]]] where (_Element[I] == Tuple[P, C] and _Kind[C] >= 0 and _Kind[S] >= 0):
    """Divide every coefficient by a nonzero scalar.

    Exact domains promote together; integer division returns rationals.
    Modular inputs must have the same prime. Inputs remain unchanged.

    Parameters:
        I: The inferred polynomial iterable.
        S: The scalar operand type.
        P: The retained sparse power shape.
        C: The input coefficient type.

    Args:
        values: Sparse terms or a prepared array.
        scalar: The scalar constant; division requires a nonzero value.
        budget: The shared work allowance, including conversion and storage.

    Returns:
        A new polynomial in the common exact domain.

    Raises:
        PolyError: DOMAIN for incompatible scalars or zero divisors; LIMIT/CAPACITY on resource limits.
    """
    return _scalar_operation[3, False, I, S, P, C](values, scalar, budget)


def divide[I: Iterable, S: Copyable & Deinitable, P: Copyable & Deinitable, C: Copyable & Deinitable](values: I, scalar: S, *, max_steps: UInt64 = UInt64.MAX) raises PolyError -> Array[P, _FieldKind[_Join[_Kind[C], _Kind[S]]]] where (_Element[I] == Tuple[P, C] and _Kind[C] >= 0 and _Kind[S] >= 0):
    """Divide every coefficient by a nonzero scalar.

    Exact domains promote together; integer division returns rationals.
    Modular inputs must have the same prime. Inputs remain unchanged.

    Parameters:
        I: The inferred polynomial iterable.
        S: The scalar operand type.
        P: The retained sparse power shape.
        C: The input coefficient type.

    Args:
        values: Sparse terms or a prepared array.
        scalar: The scalar constant; division requires a nonzero value.
        max_steps: The complete call allowance.

    Returns:
        A new polynomial in the common exact domain.

    Raises:
        PolyError: DOMAIN for incompatible scalars or zero divisors; LIMIT/CAPACITY on resource limits.
    """
    var budget = Budget(max_steps)
    return _scalar_operation[3, False, I, S, P, C](values, scalar, budget)


def add[P: Copyable & Deinitable, D: NumericDomain, S: Copyable & Deinitable](values: NumericArray[P, D], scalar: S, mut budget: Budget, *, context: D.Context) raises PolyError -> NumericArray[P, D] where (_Kind[S] >= 0 or _num._IsNumeric[S]):
    """Add a scalar constant to a polynomial.

    Use the stored numerical domain and the explicit precision context.
    Inputs remain unchanged.

    Parameters:
        P: The retained sparse power shape.
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
    return _numeric_scalar_operation[0, False, P, D, S](values, scalar, budget, context=context)


def add[P: Copyable & Deinitable, D: NumericDomain, S: Copyable & Deinitable](values: NumericArray[P, D], scalar: S, *, context: D.Context, max_steps: UInt64 = UInt64.MAX) raises PolyError -> NumericArray[P, D] where (_Kind[S] >= 0 or _num._IsNumeric[S]):
    """Add a scalar constant to a polynomial.

    Use the stored numerical domain and the explicit precision context.
    Inputs remain unchanged.

    Parameters:
        P: The retained sparse power shape.
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
    return _numeric_scalar_operation[0, False, P, D, S](values, scalar, budget, context=context)


def add[P: Copyable & Deinitable, D: NumericDomain, S: Copyable & Deinitable](scalar: S, values: NumericArray[P, D], mut budget: Budget, *, context: D.Context) raises PolyError -> NumericArray[P, D] where (_Kind[S] >= 0 or _num._IsNumeric[S]):
    """Add a scalar constant to a polynomial.

    Use the stored numerical domain and the explicit precision context.
    Inputs remain unchanged.

    Parameters:
        P: The retained sparse power shape.
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
    return _numeric_scalar_operation[0, True, P, D, S](values, scalar, budget, context=context)


def add[P: Copyable & Deinitable, D: NumericDomain, S: Copyable & Deinitable](scalar: S, values: NumericArray[P, D], *, context: D.Context, max_steps: UInt64 = UInt64.MAX) raises PolyError -> NumericArray[P, D] where (_Kind[S] >= 0 or _num._IsNumeric[S]):
    """Add a scalar constant to a polynomial.

    Use the stored numerical domain and the explicit precision context.
    Inputs remain unchanged.

    Parameters:
        P: The retained sparse power shape.
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
    return _numeric_scalar_operation[0, True, P, D, S](values, scalar, budget, context=context)


def subtract[P: Copyable & Deinitable, D: NumericDomain, S: Copyable & Deinitable](values: NumericArray[P, D], scalar: S, mut budget: Budget, *, context: D.Context) raises PolyError -> NumericArray[P, D] where (_Kind[S] >= 0 or _num._IsNumeric[S]):
    """Subtract a scalar constant or a polynomial in operand order.

    Use the stored numerical domain and the explicit precision context.
    Inputs remain unchanged.

    Parameters:
        P: The retained sparse power shape.
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
    return _numeric_scalar_operation[1, False, P, D, S](values, scalar, budget, context=context)


def subtract[P: Copyable & Deinitable, D: NumericDomain, S: Copyable & Deinitable](values: NumericArray[P, D], scalar: S, *, context: D.Context, max_steps: UInt64 = UInt64.MAX) raises PolyError -> NumericArray[P, D] where (_Kind[S] >= 0 or _num._IsNumeric[S]):
    """Subtract a scalar constant or a polynomial in operand order.

    Use the stored numerical domain and the explicit precision context.
    Inputs remain unchanged.

    Parameters:
        P: The retained sparse power shape.
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
    return _numeric_scalar_operation[1, False, P, D, S](values, scalar, budget, context=context)


def subtract[P: Copyable & Deinitable, D: NumericDomain, S: Copyable & Deinitable](scalar: S, values: NumericArray[P, D], mut budget: Budget, *, context: D.Context) raises PolyError -> NumericArray[P, D] where (_Kind[S] >= 0 or _num._IsNumeric[S]):
    """Subtract a scalar constant or a polynomial in operand order.

    Use the stored numerical domain and the explicit precision context.
    Inputs remain unchanged.

    Parameters:
        P: The retained sparse power shape.
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
    return _numeric_scalar_operation[1, True, P, D, S](values, scalar, budget, context=context)


def subtract[P: Copyable & Deinitable, D: NumericDomain, S: Copyable & Deinitable](scalar: S, values: NumericArray[P, D], *, context: D.Context, max_steps: UInt64 = UInt64.MAX) raises PolyError -> NumericArray[P, D] where (_Kind[S] >= 0 or _num._IsNumeric[S]):
    """Subtract a scalar constant or a polynomial in operand order.

    Use the stored numerical domain and the explicit precision context.
    Inputs remain unchanged.

    Parameters:
        P: The retained sparse power shape.
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
    return _numeric_scalar_operation[1, True, P, D, S](values, scalar, budget, context=context)


def multiply[P: Copyable & Deinitable, D: NumericDomain, S: Copyable & Deinitable](values: NumericArray[P, D], scalar: S, mut budget: Budget, *, context: D.Context) raises PolyError -> NumericArray[P, D] where (_Kind[S] >= 0 or _num._IsNumeric[S]):
    """Multiply every coefficient by a scalar.

    Use the stored numerical domain and the explicit precision context.
    Inputs remain unchanged.

    Parameters:
        P: The retained sparse power shape.
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
    return _numeric_scalar_operation[2, False, P, D, S](values, scalar, budget, context=context)


def multiply[P: Copyable & Deinitable, D: NumericDomain, S: Copyable & Deinitable](values: NumericArray[P, D], scalar: S, *, context: D.Context, max_steps: UInt64 = UInt64.MAX) raises PolyError -> NumericArray[P, D] where (_Kind[S] >= 0 or _num._IsNumeric[S]):
    """Multiply every coefficient by a scalar.

    Use the stored numerical domain and the explicit precision context.
    Inputs remain unchanged.

    Parameters:
        P: The retained sparse power shape.
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
    return _numeric_scalar_operation[2, False, P, D, S](values, scalar, budget, context=context)


def multiply[P: Copyable & Deinitable, D: NumericDomain, S: Copyable & Deinitable](scalar: S, values: NumericArray[P, D], mut budget: Budget, *, context: D.Context) raises PolyError -> NumericArray[P, D] where (_Kind[S] >= 0 or _num._IsNumeric[S]):
    """Multiply every coefficient by a scalar.

    Use the stored numerical domain and the explicit precision context.
    Inputs remain unchanged.

    Parameters:
        P: The retained sparse power shape.
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
    return _numeric_scalar_operation[2, True, P, D, S](values, scalar, budget, context=context)


def multiply[P: Copyable & Deinitable, D: NumericDomain, S: Copyable & Deinitable](scalar: S, values: NumericArray[P, D], *, context: D.Context, max_steps: UInt64 = UInt64.MAX) raises PolyError -> NumericArray[P, D] where (_Kind[S] >= 0 or _num._IsNumeric[S]):
    """Multiply every coefficient by a scalar.

    Use the stored numerical domain and the explicit precision context.
    Inputs remain unchanged.

    Parameters:
        P: The retained sparse power shape.
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
    return _numeric_scalar_operation[2, True, P, D, S](values, scalar, budget, context=context)


def divide[P: Copyable & Deinitable, D: NumericDomain, S: Copyable & Deinitable](values: NumericArray[P, D], scalar: S, mut budget: Budget, *, context: D.Context) raises PolyError -> NumericArray[P, D] where (_Kind[S] >= 0 or _num._IsNumeric[S]):
    """Divide every coefficient by a nonzero scalar.

    Scale only stored terms under the explicit context. A ball divisor
    must exclude zero; inputs remain unchanged.

    Parameters:
        P: The retained sparse power shape.
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
    return _numeric_scalar_operation[3, False, P, D, S](values, scalar, budget, context=context)


def divide[P: Copyable & Deinitable, D: NumericDomain, S: Copyable & Deinitable](values: NumericArray[P, D], scalar: S, *, context: D.Context, max_steps: UInt64 = UInt64.MAX) raises PolyError -> NumericArray[P, D] where (_Kind[S] >= 0 or _num._IsNumeric[S]):
    """Divide every coefficient by a nonzero scalar.

    Scale only stored terms under the explicit context. A ball divisor
    must exclude zero; inputs remain unchanged.

    Parameters:
        P: The retained sparse power shape.
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
    return _numeric_scalar_operation[3, False, P, D, S](values, scalar, budget, context=context)

from polynomials import to_kernel_bytes as _kernel_encode, from_kernel_bytes as _kernel_decode
from . import _display


def to_kernel_bytes[I: Iterable, P: Copyable & Deinitable, C: Copyable & Deinitable](values: I, mut budget: Budget, *, variables: List[Int64] = List[Int64]()) raises PolyError -> List[UInt8] where (_Element[I] == Tuple[P, C] and _Kind[C] >= 0 and _Kind[C] <= 1):
    """Encode integer or rational coefficients as a canonical kernel literal.

    Zero and one use separate kernel atoms and cannot be encoded here.
    For application archives, use poly.io instead.

    Parameters:
        I: The inferred input iterable.
        P: The scalar or tuple power shape.
        C: The inferred coefficient type.

    Args:
        values: Exact integer or rational polynomial input.
        budget: The shared work allowance.
        variables: Core IDs in array-axis order; empty selects 0, 1, and so on.

    Returns:
        Canonical little-endian kernel bytes, at most 1 MiB.

    Raises:
        PolyError: ENCODING for zero or one, DOMAIN for invalid maps,
            LIMIT on exhaustion, or CAPACITY beyond the kernel size ceiling.
    """
    var p = _promote[1](_prepare[I, P, C](values, budget), NoContext(), budget)
    var core = to_core[Array[P, 1], P, _Scalar[1]](p, budget, variables=variables)
    return _kernel_encode(core, budget)


def to_kernel_bytes[I: Iterable, P: Copyable & Deinitable, C: Copyable & Deinitable](values: I, *, max_steps: UInt64 = UInt64.MAX, variables: List[Int64] = List[Int64]()) raises PolyError -> List[UInt8] where (_Element[I] == Tuple[P, C] and _Kind[C] >= 0 and _Kind[C] <= 1):
    """Encode integer or rational coefficients as a canonical kernel literal.

    Zero and one use separate kernel atoms and cannot be encoded here.
    For application archives, use poly.io instead.

    Parameters:
        I: The inferred input iterable.
        P: The scalar or tuple power shape.
        C: The inferred coefficient type.

    Args:
        values: Exact integer or rational polynomial input.
        max_steps: The complete work allowance.
        variables: Core IDs in array-axis order; empty selects 0, 1, and so on.

    Returns:
        Canonical little-endian kernel bytes, at most 1 MiB.

    Raises:
        PolyError: ENCODING for zero or one, DOMAIN for invalid maps,
            LIMIT on exhaustion, or CAPACITY beyond the kernel size ceiling.
    """
    var budget = Budget(max_steps)
    return to_kernel_bytes[I, P, C](values, budget, variables=variables)


def from_kernel_bytes[*, ndim: Int = 1](data: Span[UInt8, _], mut budget: Budget, *, variables: List[Int64] = List[Int64]()) raises PolyError -> Array[_Shape[ndim], 1]:
    """Decode and validate a kernel literal into rational coefficient storage.

    Malformed or noncanonical bytes are rejected, never silently repaired.
    The variable map supplies axis metadata absent from the wire format.

    Parameters:
        ndim: The number of output axes.

    Args:
        data: The kernel literal payload.
        budget: The shared work allowance.
        variables: Core IDs in array-axis order; empty selects 0, 1, and so on.

    Returns:
        A canonical polynomial over QQ with array axes starting at zero.

    Raises:
        PolyError: ENCODING for malformed bytes, DOMAIN for unmapped variables,
            LIMIT on exhaustion, or CAPACITY for excessive input or output size.
    """
    var core = _kernel_decode(data, budget)
    return from_core[QQ, ndim=ndim](core, budget, variables=variables)


def from_kernel_bytes[*, ndim: Int = 1](data: Span[UInt8, _], *, max_steps: UInt64 = UInt64.MAX, variables: List[Int64] = List[Int64]()) raises PolyError -> Array[_Shape[ndim], 1]:
    """Decode and validate a kernel literal into rational coefficient storage.

    Malformed or noncanonical bytes are rejected, never silently repaired.
    The variable map supplies axis metadata absent from the wire format.

    Parameters:
        ndim: The number of output axes.

    Args:
        data: The kernel literal payload.
        max_steps: The complete work allowance.
        variables: Core IDs in array-axis order; empty selects 0, 1, and so on.

    Returns:
        A canonical polynomial over QQ with array axes starting at zero.

    Raises:
        PolyError: ENCODING for malformed bytes, DOMAIN for unmapped variables,
            LIMIT on exhaustion, or CAPACITY for excessive input or output size.
    """
    var budget = Budget(max_steps)
    return from_kernel_bytes[ndim=ndim](data, budget, variables=variables)


def format[I: Iterable, P: Copyable & Deinitable, C: Copyable & Deinitable](values: I, mut budget: Budget, *, variables: List[String] = List[String]()) raises PolyError -> String where (_Element[I] == Tuple[P, C] and _Kind[C] >= 0 and _Kind[C] <= 3):
    """Display an exact polynomial with readable variable names.

    Supports ZZ, QQ, QQi, and prime fields. Coefficients remain exact;
    terms appear in decreasing lexicographic order. This is display text,
    not an archive carrying domain or axis metadata.

    Parameters:
        I: The inferred input iterable.
        P: The scalar or tuple power shape.
        C: The inferred coefficient type.

    Args:
        values: Polynomial coefficients, terms, or a prepared exact array.
        budget: The shared work allowance.
        variables: One ASCII identifier per axis; defaults to x or x0, x1, and so on.

    Returns:
        A named-variable expression, or 0 for the zero polynomial.

    Raises:
        PolyError: DOMAIN for invalid or duplicate names (i is reserved over QQi),
            LIMIT on exhaustion, or CAPACITY for excessive sizes.
    """
    var p = _prepare[I, P, C](values, budget)
    return _display._format(p._core[], _width[P](), variables, budget)


def format[I: Iterable, P: Copyable & Deinitable, C: Copyable & Deinitable](values: I, *, max_steps: UInt64 = UInt64.MAX, variables: List[String] = List[String]()) raises PolyError -> String where (_Element[I] == Tuple[P, C] and _Kind[C] >= 0 and _Kind[C] <= 3):
    """Display an exact polynomial with readable variable names.

    Supports ZZ, QQ, QQi, and prime fields. Coefficients remain exact;
    terms appear in decreasing lexicographic order. This is display text,
    not an archive carrying domain or axis metadata.

    Parameters:
        I: The inferred input iterable.
        P: The scalar or tuple power shape.
        C: The inferred coefficient type.

    Args:
        values: Polynomial coefficients, terms, or a prepared exact array.
        max_steps: The complete work allowance.
        variables: One ASCII identifier per axis; defaults to x or x0, x1, and so on.

    Returns:
        A named-variable expression, or 0 for the zero polynomial.

    Raises:
        PolyError: DOMAIN for invalid or duplicate names (i is reserved over QQi),
            LIMIT on exhaustion, or CAPACITY for excessive sizes.
    """
    var budget = Budget(max_steps)
    return format[I, P, C](values, budget, variables=variables)
