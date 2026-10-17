"""Dense univariate arithmetic with iterative Karatsuba multiplication."""
from .coefficient_buffer import CoefficientBuffer, _CoefficientView, _view
from .errors import Budget, PolyError, PolyErrorKind, _sum, _product, _charge_size, _allocation
from .coefficients import CoefficientRing, ModInt, ZZ
from .monomial import Monomial, MonomialOrder
from .sparse import Term, SparsePoly
from ._ntt import _ntt_product
from ._nmod import _Field, _field, _to, _from, _mul as _residue_mul

comptime KARATSUBA_THRESHOLD = 32
"""The measured Karatsuba threshold for arbitrary-precision coefficients."""

comptime _NTT_THRESHOLD = 32
"""The shorter operand length from which ZZ and GF(p) products use multi-modular transforms."""


comptime _RESIDUE_THRESHOLD = 16
"""The shorter operand length from which odd prime-field products run on native Montgomery residues."""


def _residue_product[C: CoefficientRing](a: _CoefficientView[C, _], b: _CoefficientView[C, _], square: Bool, mut budget: Budget) raises PolyError -> Optional[List[C]]:
    """The product over an odd prime field by the native residue kernels (SIMD schoolbook, Karatsuba, transforms), or None for p = 2."""
    ref lead = rebind[ModInt](a[0])
    if lead.modulus % 2 == 0:
        return None
    var f = _field(lead.modulus)
    _allocation[UInt64](_sum(len(a), len(b)), budget)
    var x = List[UInt64](capacity=len(a))
    for i in range(len(a)):
        x.append(_to(rebind[ModInt](a[i]).value, f))
    if square:
        # One list for both operands lets the kernels take their square paths.
        return _residues[C](lead, _residue_mul(x, x, f, budget), f, budget)
    var y = List[UInt64](capacity=len(b))
    for i in range(len(b)):
        y.append(_to(rebind[ModInt](b[i]).value, f))
    return _residues[C](lead, _residue_mul(x, y, f, budget), f, budget)


def _residues[C: CoefficientRing](lead: ModInt, values: List[UInt64], f: _Field, mut budget: Budget) raises PolyError -> List[C]:
    _allocation[C](len(values), budget)
    var result = List[C](capacity=len(values))
    for v in values:
        result.append(rebind_var[C](lead._with_residue(_from(v, f))))
    return result^


def _threshold[C: CoefficientRing]() -> Int:
    comptime if C == ModInt:
        return 64
    else:
        return KARATSUBA_THRESHOLD

def _trim[C: CoefficientRing](mut values: List[C], mut budget: Budget) raises PolyError:
    while len(values):
        budget.charge(1)
        if not values[len(values) - 1].is_zero():
            break
        _ = values.pop()


def _trim[C: CoefficientRing](mut values: CoefficientBuffer[C], mut budget: Budget) raises PolyError:
    while len(values):
        budget.charge(1)
        if not values[len(values) - 1].is_zero():
            break
        _ = values.pop()


def _slice[C: CoefficientRing](values: _CoefficientView[C, _], lo: Int, hi: Int, mut budget: Budget) raises PolyError -> List[C]:
    _allocation[C](hi - lo, budget)
    var result = List[C](capacity=hi - lo)
    var i = lo
    while i < hi:
        var run = values._run(i)
        var count = min(len(run), hi - i)
        for j in range(count):
            _charge_size(run[j].size(), budget)
            result.append(run[j].copy())
        i += count
    return result^

def _add[C: CoefficientRing](a: _CoefficientView[C, _], b: _CoefficientView[C, _], subtract: Bool, mut budget: Budget) raises PolyError -> List[C]:
    var n = max(len(a), len(b))
    _allocation[C](n, budget)
    var result = List[C](capacity=n)
    var i = 0
    var common = min(len(a), len(b))
    while i < common:
        var left = a._run(i)
        var right = b._run(i)
        var count = min(len(left), min(len(right), common - i))
        for j in range(count):
            result.append(left[j].sub(right[j], budget) if subtract else left[j].add(right[j], budget))
        i += count
    while i < len(a):
        var run = a._run(i)
        for value in run:
            _charge_size(value.size(), budget)
            result.append(value.copy())
        i += len(run)
    while i < len(b):
        var run = b._run(i)
        for value in run:
            _charge_size(value.size(), budget)
            result.append(value.neg(budget) if subtract else value.copy())
        i += len(run)
    _trim(result, budget)
    return result^

def _schoolbook[C: CoefficientRing](a: _CoefficientView[C, _], b: _CoefficientView[C, _], ctx: C.Context, mut budget: Budget) raises PolyError -> List[C]:
    if len(a) == 0 or len(b) == 0:
        return List[C]()
    var n = _sum(len(a), len(b)) - 1
    _allocation[C](n, budget)
    _charge_size(_product(len(a), len(b)), budget)
    var result = List[C](length=n, fill=C.zero(ctx))
    for i in range(len(a)):
        for j in range(len(b)):
            var value = a[i].mul(b[j], budget)
            result[i + j] = result[i + j].add(value, budget)
    _trim(result, budget)
    return result^

@fieldwise_init
struct _Task[C: CoefficientRing](Movable):
    var a: List[Self.C]
    var b: List[Self.C]
    var split: Int

def _karatsuba[C: CoefficientRing](a: _CoefficientView[C, _], b: _CoefficientView[C, _], ctx: C.Context, mut budget: Budget) raises PolyError -> List[C]:
    var tasks = List[_Task[C]]()
    var answers = List[List[C]]()
    tasks.append(_Task[C](_slice(_view(a), 0, len(a), budget), _slice(_view(b), 0, len(b), budget), 0))
    while len(tasks):
        budget.charge(1)
        var task = tasks.pop()
        if task.split:
            var middle = answers.pop()
            var high = answers.pop()
            var low = answers.pop()
            var updated_middle_1 = _add(_view(middle), _view(low), True, budget)
            middle = updated_middle_1^
            var updated_middle_2 = _add(_view(middle), _view(high), True, budget)
            middle = updated_middle_2^
            var n = max(len(low), max(_sum(task.split, len(middle)), _sum(_product(2, task.split), len(high))))
            _allocation[C](n, budget)
            var result = List[C](length=n, fill=C.zero(ctx))
            for i in range(len(low)):
                budget.charge(1)
                _charge_size(low[i].size(), budget)
                result[i] = low[i].copy()
            for i in range(len(middle)):
                budget.charge(1)
                result[i + task.split] = result[i + task.split].add(middle[i], budget)
            for i in range(len(high)):
                budget.charge(1)
                result[i + 2 * task.split] = result[i + 2 * task.split].add(high[i], budget)
            _trim(result, budget)
            answers.append(result^)
            continue
        var n = max(len(task.a), len(task.b))
        var shorter = min(len(task.a), len(task.b))
        if shorter < _threshold[C]() or shorter < n // 2:
            answers.append(_schoolbook(_view(task.a), _view(task.b), ctx, budget))
            continue
        var k = n // 2
        var a0 = _slice(_view(task.a), 0, min(k, len(task.a)), budget)
        var a1 = _slice(_view(task.a), min(k, len(task.a)), len(task.a), budget)
        var b0 = _slice(_view(task.b), 0, min(k, len(task.b)), budget)
        var b1 = _slice(_view(task.b), min(k, len(task.b)), len(task.b), budget)
        var sa = _add(_view(a0), _view(a1), False, budget)
        var sb = _add(_view(b0), _view(b1), False, budget)
        tasks.append(_Task[C](List[C](), List[C](), k))
        tasks.append(_Task[C](sa^, sb^, 0))
        tasks.append(_Task[C](a1^, b1^, 0))
        tasks.append(_Task[C](a0^, b0^, 0))
    return answers.pop()

struct DensePoly[C: CoefficientRing](Copyable, Movable, Equatable, Writable):
    """A canonical univariate polynomial with coefficients in ascending degree.

    Parameters:
        C: The coefficient ring type.
    """
    var variable: Int64
    """The variable index, retained even for constants and zero."""
    var ring: Self.C.Context
    """The coefficient ring context."""
    var coefficients: CoefficientBuffer[Self.C]
    """Owned contiguous or chunked coefficients, empty for zero and otherwise ending in a nonzero value."""

    def __init__(out self, variable: Int64, var ring: Self.C.Context):
        """Construct zero by taking ownership of its context.

        Args:
            variable: The retained variable index.
            ring: The owned ring context.
        """
        self.variable = variable
        self.ring = ring^
        self.coefficients = List[Self.C]()

    @staticmethod
    def from_coefficients(variable: Int64, ring: Self.C.Context, var coefficients: List[Self.C], mut budget: Budget) raises PolyError -> Self:
        """Validate the ring and trim trailing zero coefficients.

        Args:
            variable: The variable index.
            ring: The coefficient context.
            coefficients: The owned ascending coefficient vector.
            budget: The shared work allowance.

        Returns:
            The canonical dense polynomial.

        Raises:
            PolyError: DOMAIN for mixed contexts or LIMIT on exhaustion.
        """
        # Validate and trim while the input is still a list. Keeping this
        # contiguous path explicit avoids storage dispatch in existing callers.
        for c in coefficients:
            budget.charge(1)
            if c.context() != ring:
                raise PolyError(PolyErrorKind.DOMAIN, "dense coefficient in another ring")
        _trim(coefficients, budget)
        var result = Self(variable, ring.copy())
        result.coefficients = coefficients^
        return result^

    @staticmethod
    def from_coefficients(variable: Int64, ring: Self.C.Context, var coefficients: CoefficientBuffer[Self.C], mut budget: Budget) raises PolyError -> Self:
        """Validate the ring and trim trailing zero coefficients.

        Args:
            variable: The variable index.
            ring: The coefficient context.
            coefficients: The owned ascending coefficient vector.
            budget: The shared work allowance.

        Returns:
            The canonical dense polynomial.

        Raises:
            PolyError: DOMAIN for mixed contexts or LIMIT on exhaustion.
        """
        var result = Self(variable, ring.copy())
        result.coefficients = coefficients^
        for coefficient_index in range(len(result.coefficients)):
            ref c = result.coefficients[coefficient_index]
            budget.charge(1)
            if c.context() != ring:
                raise PolyError(PolyErrorKind.DOMAIN, "dense coefficient in another ring")
        _trim(result.coefficients, budget)
        return result^

    @staticmethod
    def _from_canonical(variable: Int64, ring: Self.C.Context, var coefficients: List[Self.C]) -> Self:
        # Arithmetic helpers already establish the ring and trim their output.
        var result = Self(variable, ring.copy())
        result.coefficients = coefficients^
        return result^

    def __eq__(self, other: Self) -> Bool:
        """Compare variable, ring, and canonical coefficients.

        Args:
            other: The other polynomial.

        Returns:
            Whether their representations agree.
        """
        return self.variable == other.variable and self.ring == other.ring and self.coefficients == other.coefficients

    @staticmethod
    def karatsuba_threshold() -> Int:
        """Report the measured crossover for this coefficient type.

        Returns:
            64 coefficients for ModInt, otherwise 32.
        """
        return _threshold[Self.C]()

    def degree(self) -> Int:
        """Return the stored degree, or minus one for zero.

        Returns:
            The degree in constant time.
        """
        return len(self.coefficients) - 1

    def is_zero(self) -> Bool:
        """Test whether the coefficient vector is empty.

        Returns:
            Whether the polynomial is zero.
        """
        return len(self.coefficients) == 0

    def _same(self, other: Self) raises PolyError:
        if self.variable != other.variable or self.ring != other.ring:
            raise PolyError(PolyErrorKind.DOMAIN, "different dense variables or rings")

    def add(self, other: Self, mut budget: Budget) raises PolyError -> Self:
        """Add coefficient vectors in the same ring and variable.

        Args:
            other: The other polynomial.
            budget: The shared work allowance.

        Returns:
            The canonical sum.

        Raises:
            PolyError: DOMAIN for incompatible operands, LIMIT or CAPACITY on work limits.
        """
        self._same(other)
        return Self._from_canonical(self.variable, self.ring, _add(_view(self.coefficients), _view(other.coefficients), False, budget))

    def sub(self, other: Self, mut budget: Budget) raises PolyError -> Self:
        """Subtract coefficient vectors in the same ring and variable.

        Args:
            other: The other polynomial.
            budget: The shared work allowance.

        Returns:
            The canonical difference.

        Raises:
            PolyError: DOMAIN for incompatible operands, LIMIT or CAPACITY on work limits.
        """
        self._same(other)
        return Self._from_canonical(self.variable, self.ring, _add(_view(self.coefficients), _view(other.coefficients), True, budget))

    def neg(self, mut budget: Budget) raises PolyError -> Self:
        """Negate the coefficient vector.

        Args:
            budget: The shared work allowance.

        Returns:
            The additive inverse.

        Raises:
            PolyError: LIMIT or CAPACITY on work limits.
        """
        _allocation[Self.C](len(self.coefficients), budget)
        var values = List[Self.C](capacity=len(self.coefficients))
        for coefficient_index in range(len(self.coefficients)):
            ref c = self.coefficients[coefficient_index]
            budget.charge(1)
            values.append(c.neg(budget))
        return Self._from_canonical(self.variable, self.ring, values^)

    def scale(self, c: Self.C, mut budget: Budget) raises PolyError -> Self:
        """Multiply all coefficients by a scalar.

        Args:
            c: The scalar in the same ring.
            budget: The shared work allowance.

        Returns:
            The scaled polynomial.

        Raises:
            PolyError: DOMAIN for a mixed ring, LIMIT or CAPACITY on work limits.
        """
        if c.context() != self.ring:
            raise PolyError(PolyErrorKind.DOMAIN, "scalar in another ring")
        _allocation[Self.C](len(self.coefficients), budget)
        var values = List[Self.C](capacity=len(self.coefficients))
        for coefficient_index in range(len(self.coefficients)):
            ref a = self.coefficients[coefficient_index]
            budget.charge(1)
            values.append(a.mul(c, budget))
        _trim(values, budget)
        return Self._from_canonical(self.variable, self.ring, values^)

    def mul_schoolbook(self, other: Self, mut budget: Budget) raises PolyError -> Self:
        """Multiply by direct convolution for testing and measurements.

        Args:
            other: The other polynomial.
            budget: The shared work allowance.

        Returns:
            The canonical product.

        Raises:
            PolyError: DOMAIN for incompatible operands, LIMIT or CAPACITY on work limits.
        """
        self._same(other)
        return Self._from_canonical(self.variable, self.ring, _schoolbook(_view(self.coefficients), _view(other.coefficients), self.ring, budget))

    def mul(self, other: Self, mut budget: Budget) raises PolyError -> Self:
        """Multiply with schoolbook or an explicit-stack Karatsuba traversal.

        Args:
            other: The other polynomial.
            budget: The shared work allowance.

        Returns:
            The canonical product.

        Raises:
            PolyError: DOMAIN for incompatible operands, LIMIT or CAPACITY on work limits.
        """
        self._same(other)
        var shorter = min(len(self.coefficients), len(other.coefficients))
        comptime if Self.C == ModInt:
            if shorter >= _RESIDUE_THRESHOLD:
                var product = _residue_product(_view(self.coefficients), _view(other.coefficients), self.coefficients == other.coefficients, budget)
                if product:
                    return Self._from_canonical(self.variable, self.ring, product.take())
        comptime if Self.C == ZZ or Self.C == ModInt:
            if shorter >= _NTT_THRESHOLD:
                # Equal operands share their transform.
                var square = self.coefficients == other.coefficients
                var product = _ntt_product(_view(self.coefficients), _view(other.coefficients), square, budget)
                if product:
                    return Self._from_canonical(self.variable, self.ring, product.take())
        if shorter < _threshold[Self.C]():
            return self.mul_schoolbook(other, budget)
        return Self._from_canonical(self.variable, self.ring, _karatsuba(_view(self.coefficients), _view(other.coefficients), self.ring, budget))

    def pow(self, n: UInt64, mut budget: Budget) raises PolyError -> Self:
        """Raise to a natural power by repeated squaring.

        Args:
            n: The exponent.
            budget: The shared work allowance.

        Returns:
            The power; exponent zero gives one in the same ring and variable.

        Raises:
            PolyError: LIMIT or CAPACITY on work limits.
        """
        var values = List[Self.C]()
        values.append(Self.C.one(self.ring))
        var result = Self.from_coefficients(self.variable, self.ring, values^, budget)
        if n == 0:
            return result^
        var base = Self._from_canonical(self.variable, self.ring, _slice(_view(self.coefficients), 0, len(self.coefficients), budget))
        var exponent = n
        while exponent:
            budget.charge(1)
            if exponent & 1:
                result = result.mul(base, budget)
            exponent >>= 1
            if exponent:
                base = base.mul(base, budget)
        return result^

    def to_sparse(self, order: MonomialOrder, mut budget: Budget) raises PolyError -> SparsePoly[Self.C]:
        """Convert to canonical sparse form under an explicit order.

        Args:
            order: The sparse monomial order.
            budget: The shared work allowance.

        Returns:
            The sparse polynomial in the same coefficient ring.

        Raises:
            PolyError: DOMAIN for an unknown variable, CAPACITY for exponent overflow, LIMIT on exhaustion.
        """
        # Widen both operands explicitly before checking sparse exponent capacity.
        if UInt64(max(0, self.degree())) > UInt64(UInt32.MAX):
            raise PolyError(PolyErrorKind.CAPACITY, "dense degree exceeds sparse exponent width")
        var result = SparsePoly[Self.C].zero(order, self.ring, budget)
        if self.degree() > 0:
            var variable = Monomial([(self.variable, UInt32(1))], budget)
            order.validate(variable, budget)
        # Powers of one variable increase in all four supported orders.
        # Input canonicality already establishes the coefficient contexts.
        for i in range(len(self.coefficients)):
            budget.charge(1)
            if self.coefficients[i].is_zero():
                continue
            var monomial = Monomial()
            if i:
                monomial.pairs.append((self.variable, UInt32(i)))
            _charge_size(self.coefficients[i].size(), budget)
            result.terms.append(Term[Self.C](monomial^, self.coefficients[i].copy()))
        return result^

    @staticmethod
    def from_sparse(p: SparsePoly[Self.C], mut budget: Budget, *, variable: Optional[Int64] = None) raises PolyError -> Self:
        """Convert a univariate sparse polynomial, optionally selecting its variable.

        Args:
            p: The sparse polynomial.
            budget: The shared work allowance.
            variable: The variable to retain; inferred from nonconstant terms, otherwise zero.

        Returns:
            The dense polynomial in the same coefficient ring.

        Raises:
            PolyError: DOMAIN for another variable, LIMIT or CAPACITY on work limits.
        """
        var index = Int64(0)
        var selected = Bool(variable)
        if variable:
            index = variable.value()
        var degree = -1
        # Find the variable and extent together, without collecting/sorting
        # all variables or binary-searching every single-variable monomial.
        for term in p.terms:
            budget.charge(1)
            if len(term.monomial.pairs) > 1:
                raise PolyError(PolyErrorKind.DOMAIN, "multivariate polynomial is not dense univariate")
            if len(term.monomial.pairs):
                var pair = term.monomial.pairs[0]
                if not selected:
                    index = pair[0]
                    selected = True
                elif pair[0] != index:
                    raise PolyError(PolyErrorKind.DOMAIN, "sparse polynomial has another variable")
                degree = max(degree, Int(UInt64(pair[1])))
            else:
                degree = max(degree, 0)
        # Sparse exponents fit UInt32; adding one fits the native Int.
        var n = degree + 1
        _allocation[Self.C](n, budget)
        var values = List[Self.C](length=n, fill=Self.C.zero(p.ring))
        for term in p.terms:
            budget.charge(1)
            var exponent = Int(UInt64(term.monomial.pairs[0][1])) if len(term.monomial.pairs) else 0
            _charge_size(term.coefficient.size(), budget)
            values[exponent] = term.coefficient.copy()
        return Self._from_canonical(index, p.ring, values^)

    def check_invariants(self, mut budget: Budget) raises PolyError:
        """Check ring consistency and the nonzero leading coefficient.

        Args:
            budget: The shared work allowance.

        Raises:
            PolyError: DOMAIN for an invalid representation or LIMIT on exhaustion.
        """
        for coefficient_index in range(len(self.coefficients)):
            ref c = self.coefficients[coefficient_index]
            budget.charge(1)
            if c.context() != self.ring:
                raise PolyError(PolyErrorKind.DOMAIN, "mixed dense coefficient contexts")
        if len(self.coefficients) and self.coefficients[len(self.coefficients) - 1].is_zero():
            raise PolyError(PolyErrorKind.DOMAIN, "zero dense leading coefficient")
