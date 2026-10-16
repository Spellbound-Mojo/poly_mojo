"""Canonical sparse arithmetic by merging ordered exact terms."""
from std.sys import size_of
from .errors import Budget, PolyError, PolyErrorKind, _sum, _product, _charge_size, _allocation
from .coefficients import CoefficientRing
from .monomial import Monomial, MonomialOrder
from ._ordering import _IndexedOrder, _stable_indices, _sift_min

@fieldwise_init
struct Term[C: CoefficientRing](Copyable, Movable, Equatable, Writable):
    """One monomial and its coefficient.

    Parameters:
        C: The coefficient ring type.
    """
    var monomial: Monomial
    """The canonical monomial."""
    var coefficient: Self.C
    """The coefficient in the polynomial's ring."""

    def __eq__(self, other: Self) -> Bool:
        """Compare the monomial and coefficient.

        Args:
            other: The other term.

        Returns:
            Whether both components agree.
        """
        return self.monomial == other.monomial and self.coefficient == other.coefficient

    def _copy(self, mut budget: Budget) raises PolyError -> Self:
        _charge_size(_sum(len(self.monomial.pairs), self.coefficient.size()), budget)
        return self.copy()

struct SparsePoly[C: CoefficientRing](Copyable, Movable, Equatable, Writable):
    """A canonical polynomial whose nonzero terms increase in its order.

    Parameters:
        C: The coefficient ring type.
    """
    var order: MonomialOrder
    """The explicit monomial order."""
    var ring: Self.C.Context
    """The coefficient ring context, including for the zero polynomial."""
    var terms: List[Term[Self.C]]
    """The increasing nonzero terms; callers must preserve canonical form."""

    def __init__(out self, var order: MonomialOrder, var ring: Self.C.Context):
        """Take ownership of a validated order and context to construct zero.

        Args:
            order: The owned order (no input-sized copy occurs here).
            ring: The owned coefficient context.
        """
        self.order = order^
        self.ring = ring^
        self.terms = List[Term[Self.C]]()

    @staticmethod
    def zero(order: MonomialOrder, ring: Self.C.Context, mut budget: Budget) raises PolyError -> Self:
        """Construct zero while charging the copied order.

        Args:
            order: The monomial order.
            ring: The coefficient context.
            budget: The shared work allowance.

        Returns:
            The zero polynomial.

        Raises:
            PolyError: LIMIT on exhaustion.
        """
        _charge_size(len(order.variables), budget)
        return Self(order.copy(), ring.copy())

    @staticmethod
    def constant(c: Self.C, order: MonomialOrder, mut budget: Budget) raises PolyError -> Self:
        """Construct a constant with the coefficient's context.

        Args:
            c: The constant coefficient.
            order: The monomial order.
            budget: The shared work allowance.

        Returns:
            The canonical constant polynomial.

        Raises:
            PolyError: LIMIT on exhaustion.
        """
        var result = Self.zero(order, c.context(), budget)
        _charge_size(c.size(), budget)
        if not c.is_zero():
            result.terms.append(Term[Self.C](Monomial(), c.copy()))
        return result^

    @staticmethod
    def variable(index: Int64, order: MonomialOrder, ring: Self.C.Context, mut budget: Budget) raises PolyError -> Self:
        """Construct a variable in the specified ring.

        Args:
            index: The variable index.
            order: The monomial order.
            ring: The coefficient context.
            budget: The shared work allowance.

        Returns:
            The variable polynomial.

        Raises:
            PolyError: DOMAIN for an unknown variable or LIMIT on exhaustion.
        """
        var result = Self.zero(order, ring, budget)
        var pairs: List[Tuple[Int64, UInt32]] = [(index, UInt32(1))]
        var monomial = Monomial(pairs^, budget)
        order.validate(monomial, budget)
        result.terms.append(Term[Self.C](monomial^, Self.C.one(ring)))
        return result^

    @staticmethod
    def from_terms(var terms: List[Term[Self.C]], order: MonomialOrder, ring: Self.C.Context, mut budget: Budget) raises PolyError -> Self:
        """Validate, sort, combine equal monomials, and remove zero coefficients.

        Args:
            terms: The owned unsorted terms.
            order: The target order.
            ring: The coefficient context.
            budget: The shared work allowance.

        Returns:
            The normalized polynomial.

        Raises:
            PolyError: DOMAIN for mixed rings or invalid monomials, LIMIT or CAPACITY on work limits.
        """
        var result = Self.zero(order, ring, budget)
        var indices = _sorted_indices[validate=True](terms, order, ring, budget)
        # Validated monomials use only the order's variables, so an identity
        # order compares them all by the merge pass `_compare` would choose.
        var identity = order._identity()
        for index in indices:
            budget.charge(1)
            # Sorting is finished and each owned slot is visited once. Move its
            # buffers into the result instead of copying every monomial again.
            var t = Term[Self.C](Monomial(), Self.C.zero(ring))
            swap(t, terms[index])
            if t.coefficient.is_zero():
                continue
            if len(result.terms) > 0:
                var last = len(result.terms) - 1
                var same: Bool
                if identity:
                    same = order._compare_identity(result.terms[last].monomial, t.monomial, budget) == 0
                else:
                    same = order._compare(result.terms[last].monomial, t.monomial, budget) == 0
                if same:
                    var sum = result.terms[last].coefficient.add(t.coefficient, budget)
                    if sum.is_zero():
                        _ = result.terms.pop()
                    else:
                        result.terms[last].coefficient = sum^
                    continue
            result.terms.append(t^)
        return result^

    def __eq__(self, other: Self) -> Bool:
        """Compare representations, including ring and monomial order.

        Args:
            other: The other polynomial.

        Returns:
            Whether all canonical components agree.
        """
        return self.order == other.order and self.ring == other.ring and self.terms == other.terms

    def is_zero(self) -> Bool:
        """Test for the empty canonical term list.

        Returns:
            Whether the polynomial is zero.
        """
        return len(self.terms) == 0

    def _same(self, other: Self, mut budget: Budget) raises PolyError:
        _charge_size(_sum(len(self.order.variables), len(other.order.variables)), budget)
        if self.order != other.order or self.ring != other.ring:
            raise PolyError(PolyErrorKind.DOMAIN, "different polynomial rings or orders")

    def _copy(self, mut budget: Budget) raises PolyError -> Self:
        var result = Self.zero(self.order, self.ring, budget)
        for t in self.terms:
            budget.charge(1)
            result.terms.append(t._copy(budget))
        return result^

    def _add(self, other: Self, subtract: Bool, mut budget: Budget) raises PolyError -> Self:
        self._same(other, budget)
        var result = Self.zero(self.order, self.ring, budget)
        var capacity = _sum(len(self.terms), len(other.terms))
        _allocation[Term[Self.C]](capacity, budget)
        result.terms = List[Term[Self.C]](capacity=capacity)
        var i = 0
        var j = 0
        while i < len(self.terms) or j < len(other.terms):
            budget.charge(1)
            var comparison: Int
            if i == len(self.terms):
                comparison = 1
            elif j == len(other.terms):
                comparison = -1
            else:
                comparison = self.order._compare(self.terms[i].monomial, other.terms[j].monomial, budget)
            if comparison < 0:
                result.terms.append(self.terms[i]._copy(budget))
                i += 1
            elif comparison > 0:
                var t = other.terms[j]._copy(budget)
                if subtract:
                    t.coefficient = t.coefficient.neg(budget)
                result.terms.append(t^)
                j += 1
            else:
                var coefficient: Self.C
                if subtract:
                    coefficient = self.terms[i].coefficient.sub(other.terms[j].coefficient, budget)
                else:
                    coefficient = self.terms[i].coefficient.add(other.terms[j].coefficient, budget)
                if not coefficient.is_zero():
                    _charge_size(len(self.terms[i].monomial.pairs), budget)
                    result.terms.append(Term[Self.C](self.terms[i].monomial.copy(), coefficient^))
                i += 1
                j += 1
        return result^

    def add(self, other: Self, mut budget: Budget) raises PolyError -> Self:
        """Add by a linear merge of canonical terms.

        Args:
            other: The other polynomial.
            budget: The shared work allowance.

        Returns:
            The canonical sum.

        Raises:
            PolyError: DOMAIN for incompatible operands, LIMIT or CAPACITY on work limits.
        """
        return self._add(other, False, budget)

    def sub(self, other: Self, mut budget: Budget) raises PolyError -> Self:
        """Subtract by a linear merge of canonical terms.

        Args:
            other: The other polynomial.
            budget: The shared work allowance.

        Returns:
            The canonical difference.

        Raises:
            PolyError: DOMAIN for incompatible operands, LIMIT or CAPACITY on work limits.
        """
        return self._add(other, True, budget)

    def neg(self, mut budget: Budget) raises PolyError -> Self:
        """Negate all coefficients without re-sorting.

        Args:
            budget: The shared work allowance.

        Returns:
            The additive inverse.

        Raises:
            PolyError: LIMIT or CAPACITY on work limits.
        """
        var result = Self.zero(self.order, self.ring, budget)
        for t in self.terms:
            budget.charge(1)
            _charge_size(len(t.monomial.pairs), budget)
            result.terms.append(Term[Self.C](t.monomial.copy(), t.coefficient.neg(budget)))
        return result^

    def mul(self, other: Self, mut budget: Budget) raises PolyError -> Self:
        """Multiply exact terms using sorted streams for admissible orders.

        Args:
            other: The other polynomial.
            budget: The shared work allowance.

        Returns:
            The canonical product.

        Raises:
            PolyError: DOMAIN for incompatible operands, LIMIT or CAPACITY on work limits.
        """
        self._same(other, budget)
        if self.is_zero() or other.is_zero():
            return Self.zero(self.order, self.ring, budget)
        if len(self.terms) == 1 and self.order.kind != MonomialOrder.KERNEL:
            return other._mul_term(self.terms[0], budget)
        if len(other.terms) == 1 and self.order.kind != MonomialOrder.KERNEL:
            return self._mul_term(other.terms[0], budget)
        var count = _product(len(self.terms), len(other.terms))
        if self.order.kind == MonomialOrder.KERNEL and count >= 256:
            var variables = self.variables(budget)
            var others = other.variables(budget)
            # In one variable KERNEL already is a multiplicative exponent
            # order. No copies or order conversion are needed for these rows.
            if len(variables) <= 1 and len(others) <= 1 and (not len(variables) or not len(others) or variables[0] == others[0]):
                if len(self.terms) <= len(other.terms):
                    return _heap_product(self, other, budget)
                return _heap_product(other, self, budget)
            var overlap = False
            var i = 0
            var j = 0
            while i < len(variables) and j < len(others):
                budget.charge(1)
                if variables[i] == others[j]:
                    overlap = True
                    break
                if variables[i] < others[j]:
                    i += 1
                else:
                    j += 1
            # Disjoint supports have no product collisions: the final output
            # already needs the Cartesian number of terms. Avoid two sorts.
            if overlap and _uniform_support(self, budget) and _uniform_support(other, budget):
                # Fixed support turns KERNEL comparison into lexicographic
                # exponent comparison. Translation inserts only fixed entries,
                # so every row stays sorted without an internal conversion.
                if len(self.terms) <= len(other.terms):
                    return _heap_product(self, other, budget)
                return _heap_product(other, self, budget)
            if overlap and count >= 16384:
                _extend_variables(variables, other, budget)
                var order = MonomialOrder(MonomialOrder.LEX, variables^, budget)
                var left = self.reorder(order, budget)
                var right = other.reorder(order, budget)
                var result = _heap_product[Self.C, True](left, right, budget) if len(left.terms) <= len(right.terms) else _heap_product[Self.C, True](right, left, budget)
                return result.reorder(self.order, budget)
        if self.order.kind != MonomialOrder.KERNEL and count >= 64:
            if len(self.terms) <= len(other.terms):
                return _heap_product(self, other, budget)
            return _heap_product(other, self, budget)
        _allocation[Term[Self.C]](count, budget)
        var terms = List[Term[Self.C]](capacity=count)
        for a in self.terms:
            for b in other.terms:
                var coefficient = a.coefficient.mul(b.coefficient, budget)
                if not coefficient.is_zero():
                    terms.append(Term[Self.C](a.monomial.mul(b.monomial, budget), coefficient^))
        return Self.from_terms(terms^, self.order, self.ring, budget)

    def _mul_term(self, term: Term[Self.C], mut budget: Budget) raises PolyError -> Self:
        # Multiplication preserves admissible monomial orders. KERNEL does
        # not have this property and must use the sorting path above.
        var result = Self.zero(self.order, self.ring, budget)
        _allocation[Term[Self.C]](len(self.terms), budget)
        result.terms = List[Term[Self.C]](capacity=len(self.terms))
        for t in self.terms:
            budget.charge(1)
            var coefficient = t.coefficient.mul(term.coefficient, budget)
            if not coefficient.is_zero():
                result.terms.append(Term[Self.C](t.monomial.mul(term.monomial, budget), coefficient^))
        return result^

    def scale(self, c: Self.C, mut budget: Budget) raises PolyError -> Self:
        """Multiply every coefficient by a scalar in the same ring.

        Args:
            c: The scalar.
            budget: The shared work allowance.

        Returns:
            The scaled canonical polynomial.

        Raises:
            PolyError: DOMAIN for a different coefficient ring, LIMIT or CAPACITY on work limits.
        """
        if c.context() != self.ring:
            raise PolyError(PolyErrorKind.DOMAIN, "scalar in another ring")
        var result = Self.zero(self.order, self.ring, budget)
        for t in self.terms:
            budget.charge(1)
            var coefficient = t.coefficient.mul(c, budget)
            if not coefficient.is_zero():
                _charge_size(len(t.monomial.pairs), budget)
                result.terms.append(Term[Self.C](t.monomial.copy(), coefficient^))
        return result^

    def pow(self, n: UInt64, mut budget: Budget) raises PolyError -> Self:
        """Raise to a natural power by repeated squaring, with zero power equal to one.

        Args:
            n: The exponent.
            budget: The shared work allowance.

        Returns:
            The canonical power in the same ring and order.

        Raises:
            PolyError: LIMIT or CAPACITY on work limits.
        """
        var result = Self.constant(Self.C.one(self.ring), self.order, budget)
        if n == 0:
            return result^
        var base = self._copy(budget)
        var exponent = n
        while exponent:
            budget.charge(1)
            if exponent & 1:
                result = result.mul(base, budget)
            exponent >>= 1
            if exponent:
                base = base.mul(base, budget)
        return result^

    def leading(self, mut budget: Budget) raises PolyError -> Term[Self.C]:
        """Copy the greatest term.

        Args:
            budget: The shared work allowance.

        Returns:
            The leading term.

        Raises:
            PolyError: DOMAIN for zero or LIMIT on exhaustion.
        """
        if self.is_zero():
            raise PolyError(PolyErrorKind.DOMAIN, "zero has no leading term")
        return self.terms[len(self.terms) - 1]._copy(budget)

    def total_degree(self, mut budget: Budget) raises PolyError -> Int:
        """Find the greatest total degree, or minus one for zero.

        Args:
            budget: The shared work allowance.

        Returns:
            The total degree.

        Raises:
            PolyError: LIMIT on exhaustion or CAPACITY if the degree cannot fit Int.
        """
        var result = -1
        for t in self.terms:
            budget.charge(1)
            var degree = t.monomial.degree(budget)
            if degree > UInt64(Int.MAX):
                raise PolyError(PolyErrorKind.CAPACITY, "degree exceeds Int")
            result = max(result, Int(degree))
        return result

    def degree_in(self, index: Int64, mut budget: Budget) raises PolyError -> Int:
        """Find the degree in one variable, or minus one for zero.

        Args:
            index: The variable index.
            budget: The shared work allowance.

        Returns:
            The greatest exponent of that variable.

        Raises:
            PolyError: LIMIT on exhaustion.
        """
        var result = -1
        for t in self.terms:
            budget.charge(1)
            result = max(result, Int(UInt64(t.monomial.exponent(index, budget))))
        return result

    def variables(self, mut budget: Budget) raises PolyError -> List[Int64]:
        """Collect occurring variable indices in increasing order.

        Args:
            budget: The shared work allowance.

        Returns:
            The sorted distinct indices.

        Raises:
            PolyError: LIMIT on exhaustion.
        """
        var result = List[Int64]()
        for t in self.terms:
            for pair in t.monomial.pairs:
                budget.charge(1)
                var pos = 0
                while pos < len(result) and result[pos] < pair[0]:
                    budget.charge(1)
                    pos += 1
                if pos == len(result) or result[pos] != pair[0]:
                    _charge_size(len(result) - pos + 1, budget)
                    result.insert(pos, pair[0])
        return result^

    def reorder(self, order: MonomialOrder, mut budget: Budget) raises PolyError -> Self:
        """Normalize under a new order.

        Args:
            order: The target monomial order.
            budget: The shared work allowance.

        Returns:
            The same polynomial in that order.

        Raises:
            PolyError: DOMAIN for absent variables, LIMIT or CAPACITY on work limits.
        """
        _charge_size(_sum(len(self.order.variables), len(order.variables)), budget)
        if self.order == order:
            return self._copy(budget)
        var terms = List[Term[Self.C]]()
        for t in self.terms:
            budget.charge(1)
            terms.append(t._copy(budget))
        return Self.from_terms(terms^, order, self.ring, budget)

    def check_invariants(self, mut budget: Budget) raises PolyError:
        """Check the ring, monomials, coefficients, and strict term order.

        Args:
            budget: The shared work allowance.

        Raises:
            PolyError: DOMAIN for a broken invariant or LIMIT on exhaustion.
        """
        for i in range(len(self.terms)):
            budget.charge(1)
            self.order.validate(self.terms[i].monomial, budget)
            if self.terms[i].coefficient.is_zero() or self.terms[i].coefficient.context() != self.ring:
                raise PolyError(PolyErrorKind.DOMAIN, "invalid sparse coefficient")
            if i > 0 and self.order._compare(self.terms[i - 1].monomial, self.terms[i].monomial, budget) >= 0:
                raise PolyError(PolyErrorKind.DOMAIN, "sparse terms are not strictly increasing")


struct _ProductCursor[C: CoefficientRing](Copyable, Movable):
    var row: Int
    var column: Int
    var term: Term[Self.C]

    def __init__(out self, row: Int, ring: Self.C.Context):
        self.row = row
        self.column = -1
        self.term = Term[Self.C](Monomial(), Self.C.zero(ring))


def _uniform_support[C: CoefficientRing](poly: SparsePoly[C], mut budget: Budget) raises PolyError -> Bool:
    ref support = poly.terms[0].monomial.pairs
    for term in poly.terms:
        budget.charge(1)
        if len(term.monomial.pairs) != len(support):
            return False
        for i in range(len(support)):
            budget.charge(1)
            if term.monomial.pairs[i][0] != support[i][0]:
                return False
    return True


def _extend_variables[C: CoefficientRing](mut variables: List[Int64], poly: SparsePoly[C], mut budget: Budget) raises PolyError:
    var additions = poly.variables(budget)
    for identifier in additions:
        var position = 0
        while position < len(variables) and variables[position] < identifier:
            budget.charge(1)
            position += 1
        budget.charge(1)
        if position == len(variables) or variables[position] != identifier:
            _allocation[Int64](_sum(len(variables), 1), budget)
            variables.insert(position, identifier)


def _advance_product[C: CoefficientRing](mut cursor: _ProductCursor[C], rows: SparsePoly[C], columns: SparsePoly[C], mut budget: Budget) raises PolyError -> Bool:
    while cursor.column < len(columns.terms) - 1:
        budget.charge(1)
        cursor.column += 1
        ref a = rows.terms[cursor.row]
        ref b = columns.terms[cursor.column]
        var coefficient = a.coefficient.mul(b.coefficient, budget)
        if not coefficient.is_zero():
            cursor.term = Term[C](a.monomial.mul(b.monomial, budget), coefficient^)
            return True
    return False


struct _ProductOrder[C: CoefficientRing, sorted_lex: Bool = False](_IndexedOrder):
    comptime Item = _ProductCursor[Self.C]

    @staticmethod
    @always_inline
    def compare(items: List[Self.Item], a: Int, b: Int, order: MonomialOrder, mut budget: Budget) raises PolyError -> Int:
        var relation = 0
        comptime if Self.sorted_lex:
            # Internal LEX uses increasing variable IDs. The first differing
            # pair decides without repeated exponent lookups through the order.
            ref left = items[a].term.monomial.pairs
            ref right = items[b].term.monomial.pairs
            for i in range(min(len(left), len(right))):
                budget.charge(1)
                if left[i][0] != right[i][0]:
                    relation = 1 if left[i][0] < right[i][0] else -1
                    break
                if left[i][1] != right[i][1]:
                    relation = -1 if left[i][1] < right[i][1] else 1
                    break
            if not relation:
                relation = Int(len(left) > len(right)) - Int(len(left) < len(right))
        else:
            relation = order._compare(items[a].term.monomial, items[b].term.monomial, budget)
        if relation:
            return relation
        return Int(items[a].row > items[b].row) - Int(items[a].row < items[b].row)


def _product_rows[C: CoefficientRing, sorted_lex: Bool = False](rows: SparsePoly[C], columns: SparsePoly[C], mut budget: Budget) raises PolyError -> Tuple[List[_ProductCursor[C]], List[Int]]:
    _allocation[_ProductCursor[C]](len(rows.terms), budget)
    var cursors = List[_ProductCursor[C]](capacity=len(rows.terms))
    _allocation[Int](len(rows.terms), budget)
    var heap = List[Int](capacity=len(rows.terms))
    for i in range(len(rows.terms)):
        budget.charge(1)
        var cursor = _ProductCursor[C](i, rows.ring)
        if _advance_product(cursor, rows, columns, budget):
            heap.append(len(cursors))
            cursors.append(cursor^)
    for i in range(len(heap) // 2 - 1, -1, -1):
        budget.charge(1)
        _sift_min[_ProductOrder[C, sorted_lex]](heap, cursors, i, rows.order, budget)
    return (cursors^, heap^)


def _heap_product[C: CoefficientRing, sorted_lex: Bool = False](rows: SparsePoly[C], columns: SparsePoly[C], mut budget: Budget) raises PolyError -> SparsePoly[C]:
    # Each row is sorted only for a multiplicative monomial order. Keep one
    # pending product per row, combine equal terms, and emit canonical output.
    var prepared = _product_rows[C, sorted_lex](rows, columns, budget)
    var cursors = List[_ProductCursor[C]]()
    var heap = List[Int]()
    swap(cursors, prepared[0])
    swap(heap, prepared[1])
    var result = SparsePoly[C].zero(rows.order, rows.ring, budget)
    while len(heap):
        budget.charge(1)
        var term = Term[C](Monomial(), C.zero(rows.ring))
        var cursor = heap[0]
        swap(term, cursors[cursor].term)
        if not _advance_product(cursors[cursor], rows, columns, budget):
            var last = heap.pop()
            if len(heap):
                heap[0] = last
        if len(heap):
            _sift_min[_ProductOrder[C, sorted_lex]](heap, cursors, 0, rows.order, budget)
        if len(result.terms):
            var last = len(result.terms) - 1
            _charge_size(_sum(len(result.terms[last].monomial.pairs), len(term.monomial.pairs)), budget)
            if result.terms[last].monomial == term.monomial:
                result.terms[last].coefficient = result.terms[last].coefficient.add(term.coefficient, budget)
                if result.terms[last].coefficient.is_zero():
                    _ = result.terms.pop()
                continue
        _ = _product(_sum(len(result.terms), 1), size_of[Term[C]]())
        _allocation[Term[C]](1, budget)
        result.terms.append(term^)
    return result^


struct _ExactTermOrder[C: CoefficientRing](_IndexedOrder):
    comptime Item = Term[Self.C]

    @staticmethod
    @always_inline
    def compare(items: List[Self.Item], a: Int, b: Int, order: MonomialOrder, mut budget: Budget) raises PolyError -> Int:
        return order._compare(items[a].monomial, items[b].monomial, budget)


struct _IdentityTermOrder[C: CoefficientRing](_IndexedOrder):
    """`_ExactTermOrder` for an identity order whose terms all lie within it."""
    comptime Item = Term[Self.C]

    @staticmethod
    @always_inline
    def compare(items: List[Self.Item], a: Int, b: Int, order: MonomialOrder, mut budget: Budget) raises PolyError -> Int:
        return order._compare_identity(items.unsafe_get(a).monomial, items.unsafe_get(b).monomial, budget)


def _sorted_indices[C: CoefficientRing, validate: Bool = False](terms: List[Term[C]], order: MonomialOrder, ring: C.Context, mut budget: Budget) raises PolyError -> List[Int]:
    # `_compare` checks the order and both monomials on every call; check once.
    var identity = order._identity()
    comptime if validate:
        for term in terms:
            if term.coefficient.context() != ring:
                raise PolyError(PolyErrorKind.DOMAIN, "coefficient in another ring")
            if identity:
                order._validate_identity(term.monomial, budget)
            else:
                order.validate(term.monomial, budget)
    else:
        for term in terms:
            if identity and not order._within(term.monomial):
                identity = False
    if identity:
        return _stable_indices[_IdentityTermOrder[C]](terms, order, budget)
    return _stable_indices[_ExactTermOrder[C]](terms, order, budget)
