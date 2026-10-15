"""Canonical sparse monomials and explicit deterministic orders."""
from std.hashlib import Hasher
from .errors import Budget, PolyError, PolyErrorKind, _sum, _allocation

struct Monomial(Copyable, Movable, Equatable, Hashable, Writable):
    """A product of variables with increasing indices and positive exponents."""
    var pairs: List[Tuple[Int64, UInt32]]
    """The canonical pairs; callers must preserve their invariant."""

    def __init__(out self):
        """Construct the unit monomial."""
        self.pairs = List[Tuple[Int64, UInt32]]()

    def __init__(out self, var pairs: List[Tuple[Int64, UInt32]], mut budget: Budget) raises PolyError:
        """Validate and take ownership of canonical pairs.

        Args:
            pairs: Increasing indices with positive exponents.
            budget: The shared work allowance.

        Raises:
            PolyError: DOMAIN for invalid pairs or LIMIT on exhaustion.
        """
        self.pairs = pairs^
        self.check_invariants(budget)

    def __eq__(self, other: Self) -> Bool:
        """Compare canonical pairs (a protocol exception to explicit budgets).

        Args:
            other: The other monomial.

        Returns:
            Whether the pairs agree.
        """
        return self.pairs == other.pairs

    def __hash__[H: Hasher](self, mut hasher: H):
        """Hash the canonical pairs without exposing iteration order.

        Parameters:
            H: The hasher type.

        Args:
            hasher: The accumulating hasher.
        """
        len(self.pairs).__hash__(hasher)
        for pair in self.pairs:
            pair[0].__hash__(hasher)
            pair[1].__hash__(hasher)

    def check_invariants(self, mut budget: Budget) raises PolyError:
        """Check increasing indices and positive exponents.

        Args:
            budget: The shared work allowance.

        Raises:
            PolyError: DOMAIN for malformed pairs or LIMIT on exhaustion.
        """
        for i in range(len(self.pairs)):
            budget.charge(1)
            if self.pairs[i][1] == 0 or (i > 0 and self.pairs[i - 1][0] >= self.pairs[i][0]):
                raise PolyError(PolyErrorKind.DOMAIN, "noncanonical monomial")

    def degree(self, mut budget: Budget) raises PolyError -> UInt64:
        """Sum the exponents with overflow checks.

        Args:
            budget: The shared work allowance.

        Returns:
            The total degree.

        Raises:
            PolyError: CAPACITY on overflow or LIMIT on exhaustion.
        """
        var result = UInt64(0)
        for pair in self.pairs:
            budget.charge(1)
            if UInt64.MAX - result < UInt64(pair[1]):
                raise PolyError(PolyErrorKind.CAPACITY, "total degree overflow")
            result += UInt64(pair[1])
        return result

    def exponent(self, index: Int64, mut budget: Budget) raises PolyError -> UInt32:
        """Find a variable's exponent by binary search.

        Args:
            index: The variable index.
            budget: The shared work allowance.

        Returns:
            Its exponent, or zero if absent.

        Raises:
            PolyError: LIMIT on exhaustion.
        """
        var lo = 0
        var hi = len(self.pairs)
        while lo < hi:
            budget.charge(1)
            var mid = lo + (hi - lo) // 2
            if self.pairs[mid][0] < index:
                lo = mid + 1
            else:
                hi = mid
        if lo < len(self.pairs) and self.pairs[lo][0] == index:
            return self.pairs[lo][1]
        return 0

    def mul(self, other: Self, mut budget: Budget) raises PolyError -> Self:
        """Multiply by merging exponent lists.

        Args:
            other: The other monomial.
            budget: The shared work allowance.

        Returns:
            The canonical product.

        Raises:
            PolyError: CAPACITY on exponent overflow or LIMIT on exhaustion.
        """
        return self._merge(other, False, budget)

    def lcm(self, other: Self, mut budget: Budget) raises PolyError -> Self:
        """Take componentwise maximum exponents.

        Args:
            other: The other monomial.
            budget: The shared work allowance.

        Returns:
            The least common multiple.

        Raises:
            PolyError: LIMIT or CAPACITY on work limits.
        """
        return self._merge(other, True, budget)

    def _merge(self, other: Self, maximum: Bool, mut budget: Budget) raises PolyError -> Self:
        var count = _sum(len(self.pairs), len(other.pairs))
        _allocation[Tuple[Int64, UInt32]](count, budget)
        var result = Self()
        result.pairs.reserve(count)
        var i = 0
        var j = 0
        while i < len(self.pairs) or j < len(other.pairs):
            if j == len(other.pairs) or (i < len(self.pairs) and self.pairs[i][0] < other.pairs[j][0]):
                result.pairs.append(self.pairs[i])
                i += 1
            elif i == len(self.pairs) or other.pairs[j][0] < self.pairs[i][0]:
                result.pairs.append(other.pairs[j])
                j += 1
            else:
                var a = self.pairs[i][1]
                var b = other.pairs[j][1]
                var e = max(a, b)
                if not maximum:
                    if UInt32.MAX - a < b:
                        raise PolyError(PolyErrorKind.CAPACITY, "monomial exponent overflow")
                    e = a + b
                result.pairs.append((self.pairs[i][0], e))
                i += 1
                j += 1
        return result^

    def divides(self, other: Self, mut budget: Budget) raises PolyError -> Bool:
        """Test componentwise exponent inclusion.

        Args:
            other: The proposed multiple.
            budget: The shared work allowance.

        Returns:
            Whether this monomial divides the other.

        Raises:
            PolyError: LIMIT on exhaustion.
        """
        # One merge pass over both increasing pair lists, charged as one visit per pair.
        budget.charge(UInt64(_sum(len(self.pairs), len(other.pairs))))
        var j = 0
        var n = len(other.pairs)
        for i in range(len(self.pairs)):
            ref pair = self.pairs.unsafe_get(i)
            while j < n and other.pairs.unsafe_get(j)[0] < pair[0]:
                j += 1
            if j == n or other.pairs.unsafe_get(j)[0] != pair[0] or other.pairs.unsafe_get(j)[1] < pair[1]:
                return False
            j += 1
        return True

    def div(self, other: Self, mut budget: Budget) raises PolyError -> Self:
        """Divide by a monomial exactly.

        Args:
            other: The proposed divisor.
            budget: The shared work allowance.

        Returns:
            The canonical quotient.

        Raises:
            PolyError: DOMAIN if indivisible or LIMIT on exhaustion.
        """
        if not other.divides(self, budget):
            raise PolyError(PolyErrorKind.DOMAIN, "monomial is not divisible")
        _allocation[Tuple[Int64, UInt32]](len(self.pairs), budget)
        var result = Self()
        result.pairs.reserve(len(self.pairs))
        # The divisor's variables are a subset of ours, in the same increasing order.
        var j = 0
        for i in range(len(self.pairs)):
            ref pair = self.pairs.unsafe_get(i)
            var e = pair[1]
            if j < len(other.pairs) and other.pairs.unsafe_get(j)[0] == pair[0]:
                e -= other.pairs.unsafe_get(j)[1]
                j += 1
            if e:
                result.pairs.append((pair[0], e))
        return result^

struct MonomialOrder(Copyable, Movable, Equatable, Writable):
    """An explicit variable order, or the kernel's canonical storage order."""
    var kind: UInt8
    """One of KERNEL, LEX, GRLEX, or GREVLEX."""
    var variables: List[Int64]
    """Variables from greatest to least; empty for KERNEL."""
    comptime KERNEL = UInt8(0)
    """Lexicographic pairs, with a proper prefix first."""
    comptime LEX = UInt8(1)
    """Lexicographic exponent order."""
    comptime GRLEX = UInt8(2)
    """Total degree followed by lexicographic order."""
    comptime GREVLEX = UInt8(3)
    """Total degree followed by reversed last differing exponent."""

    def __init__(out self):
        """Construct the kernel storage order."""
        self.kind = Self.KERNEL
        self.variables = List[Int64]()

    def __init__(out self, kind: UInt8, var variables: List[Int64], mut budget: Budget) raises PolyError:
        """Validate and construct an explicit order.

        Args:
            kind: The order kind.
            variables: The variable priority list.
            budget: The shared work allowance.

        Raises:
            PolyError: DOMAIN for invalid kind or repeated variables, LIMIT on exhaustion.
        """
        self.kind = kind
        self.variables = variables^
        if kind > Self.GREVLEX or (kind == Self.KERNEL and len(self.variables) != 0):
            raise PolyError(PolyErrorKind.DOMAIN, "invalid monomial order")
        for i in range(len(self.variables)):
            budget.charge(1)
            for j in range(i):
                budget.charge(1)
                if self.variables[i] == self.variables[j]:
                    raise PolyError(PolyErrorKind.DOMAIN, "repeated order variable")

    def __eq__(self, other: Self) -> Bool:
        """Compare kinds and priority lists (a protocol budget exception).

        Args:
            other: The other order.

        Returns:
            Whether the orders agree.
        """
        return self.kind == other.kind and self.variables == other.variables

    def validate(self, monomial: Monomial, mut budget: Budget) raises PolyError:
        """Check that a canonical monomial belongs to this variable domain.

        Args:
            monomial: The monomial to validate.
            budget: The shared work allowance.

        Raises:
            PolyError: DOMAIN for unknown variables or LIMIT on exhaustion.
        """
        monomial.check_invariants(budget)
        if self.kind == Self.KERNEL:
            return
        for pair in monomial.pairs:
            budget.charge(1)
            var found = False
            for variable in self.variables:
                budget.charge(1)
                if variable == pair[0]:
                    found = True
                    break
            if not found:
                raise PolyError(PolyErrorKind.DOMAIN, "variable absent from order")

    def compare(self, a: Monomial, b: Monomial, mut budget: Budget) raises PolyError -> Int:
        """Compare monomials under this order after domain validation.

        Args:
            a: The left monomial.
            b: The right monomial.
            budget: The shared work allowance.

        Returns:
            Minus one, zero, or one.

        Raises:
            PolyError: DOMAIN for unknown variables, LIMIT or CAPACITY for work limits.
        """
        self.validate(a, budget)
        self.validate(b, budget)
        return self._compare(a, b, budget)

    def _compare(self, a: Monomial, b: Monomial, mut budget: Budget) raises PolyError -> Int:
        if self.kind != Self.KERNEL and self._covers(a) and self._covers(b):
            return self._compare_identity(a, b, budget)
        if self.kind == Self.KERNEL:
            for i in range(min(len(a.pairs), len(b.pairs))):
                budget.charge(1)
                if a.pairs[i][0] != b.pairs[i][0]:
                    return -1 if a.pairs[i][0] < b.pairs[i][0] else 1
                if a.pairs[i][1] != b.pairs[i][1]:
                    return -1 if a.pairs[i][1] < b.pairs[i][1] else 1
            return Int(len(a.pairs) > len(b.pairs)) - Int(len(a.pairs) < len(b.pairs))
        if self.kind != Self.LEX:
            var ad = a.degree(budget)
            var bd = b.degree(budget)
            if ad != bd:
                return -1 if ad < bd else 1
        for i in range(len(self.variables)):
            budget.charge(1)
            var j = len(self.variables) - 1 - i if self.kind == Self.GREVLEX else i
            var ae = a.exponent(self.variables[j], budget)
            var be = b.exponent(self.variables[j], budget)
            if ae != be:
                var result = -1 if ae < be else 1
                return -result if self.kind == Self.GREVLEX else result
        return 0

    def _covers(self, m: Monomial) -> Bool:
        """Whether the order lists variables 0..n-1 in priority order and m uses only those.

        Pair indices increase, so checking the first and last pairs bounds them all.
        """
        var n = len(self.variables)
        if len(m.pairs) and (m.pairs.unsafe_get(0)[0] < 0 or m.pairs.unsafe_get(len(m.pairs) - 1)[0] >= Int64(n)):
            return False
        for i in range(n):
            if self.variables.unsafe_get(i) != Int64(i):
                return False
        return True

    def _compare_identity(self, a: Monomial, b: Monomial, mut budget: Budget) raises PolyError -> Int:
        """Compare by one merge pass when variable index order is priority order.

        Equivalent to the per-variable comparison below for monomials that
        `_covers` accepts, and charged as one visit per pair.
        """
        var na = len(a.pairs)
        var nb = len(b.pairs)
        budget.charge(UInt64(_sum(_sum(na, nb), 1)))
        if self.kind != Self.LEX:
            var ad = UInt64(0)
            var bd = UInt64(0)
            for i in range(na):
                ad += UInt64(a.pairs.unsafe_get(i)[1])
            for j in range(nb):
                bd += UInt64(b.pairs.unsafe_get(j)[1])
            if ad != bd:
                return -1 if ad < bd else 1
        if self.kind == Self.GREVLEX:
            # The last differing variable decides, and the smaller exponent there is greater.
            var i = na - 1
            var j = nb - 1
            while i >= 0 and j >= 0:
                ref p = a.pairs.unsafe_get(i)
                ref q = b.pairs.unsafe_get(j)
                if p[0] != q[0]:
                    return -1 if p[0] > q[0] else 1
                if p[1] != q[1]:
                    return -1 if p[1] > q[1] else 1
                i -= 1
                j -= 1
            return 0 if i < 0 and j < 0 else (1 if i < 0 else -1)
        # LEX and the tie-break of GRLEX: the first differing variable decides.
        var i = 0
        var j = 0
        while i < na and j < nb:
            ref p = a.pairs.unsafe_get(i)
            ref q = b.pairs.unsafe_get(j)
            if p[0] != q[0]:
                return 1 if p[0] < q[0] else -1
            if p[1] != q[1]:
                return 1 if p[1] > q[1] else -1
            i += 1
            j += 1
        return 0 if i == na and j == nb else (-1 if i == na else 1)
