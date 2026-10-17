"""Formal truncated series with explicit precision and domain conditions."""
from .coefficients import CoefficientField
from .dense import DensePoly
from ._toolkit_exact import _ExactOps, _use_newton
from .coefficient_buffer import _view
from .errors import Budget, PolyError, PolyErrorKind, _sum
from ._toolkit_ops import _values, _add_values, _mul_values, _divide_values, _compose_values, _derivative_values, _integral_values
from ._series_exact import _exact_log, _exact_exp
from ._series_ops import _newton_divide, _series_shape, _series_same_order, _series_truncation, _series_composition, _revert_values


@fieldwise_init
struct TruncatedSeries[C: CoefficientField](Copyable, Movable):
    """Store coefficients known modulo an explicit power of x.

    Parameters:
        C: The exact coefficient field.
    """
    var polynomial: DensePoly[Self.C]
    """The canonical polynomial containing known coefficients."""
    var order: Int
    """The nonnegative exponent of the unknown remainder O(x^order)."""

    @staticmethod
    def from_polynomial(poly: DensePoly[Self.C], order: Int, mut budget: Budget) raises PolyError -> Self:
        """Truncate a polynomial to a specified formal precision.

        Args:
            poly: The polynomial supplying known coefficients.
            order: The nonnegative number of known coefficients.
            budget: The shared work allowance.

        Returns:
            A formal series with zeros filled from the polynomial below the order.

        Raises:
            PolyError: DOMAIN for invalid inputs, LIMIT or CAPACITY on work limits.
        """
        if order < 0:
            raise PolyError(PolyErrorKind.DOMAIN, "negative series order")
        poly.check_invariants(budget)
        var values = _values[_ExactOps[Self.C]](_view(poly.coefficients), min(order, len(poly.coefficients)), poly.ring, budget)
        return Self(DensePoly[Self.C].from_coefficients(poly.variable, poly.ring, values^, budget), order)

    def _validate(self, mut budget: Budget) raises PolyError:
        self.polynomial.check_invariants(budget)
        _series_shape(self.order, len(self.polynomial.coefficients), budget)

    def _same(self, other: Self, mut budget: Budget) raises PolyError:
        self._validate(budget)
        other._validate(budget)
        self.polynomial._same(other.polynomial)
        _series_same_order(self.order, other.order)

    def truncate(self, order: Int, mut budget: Budget) raises PolyError -> Self:
        """Reduce precision without inventing unknown coefficients.

        Args:
            order: The requested lower precision.
            budget: The shared work allowance.

        Returns:
            A series at the requested order.

        Raises:
            PolyError: DOMAIN for incompatible inputs or unavailable divisions, LIMIT or CAPACITY on work limits.
        """
        self._validate(budget)
        _series_truncation(self.order, order)
        return Self.from_polynomial(self.polynomial, order, budget)

    def add(self, other: Self, mut budget: Budget) raises PolyError -> Self:
        """Add two series at equal precision.

        Args:
            other: The second series in the same variable, domain and order.
            budget: The shared work allowance.

        Returns:
            The truncated sum.

        Raises:
            PolyError: DOMAIN for incompatible inputs or unavailable divisions, LIMIT or CAPACITY on work limits.
        """
        self._same(other, budget)
        var values = _add_values[_ExactOps[Self.C]](_view(self.polynomial.coefficients), _view(other.polynomial.coefficients), self.order, False, self.polynomial.ring, budget)
        var poly = DensePoly[Self.C].from_coefficients(self.polynomial.variable, self.polynomial.ring, values^, budget)
        return Self(poly^, self.order)

    def sub(self, other: Self, mut budget: Budget) raises PolyError -> Self:
        """Subtract two series at equal precision.

        Args:
            other: The second series in the same variable, domain and order.
            budget: The shared work allowance.

        Returns:
            The truncated difference.

        Raises:
            PolyError: DOMAIN for incompatible inputs or unavailable divisions, LIMIT or CAPACITY on work limits.
        """
        self._same(other, budget)
        var values = _add_values[_ExactOps[Self.C]](_view(self.polynomial.coefficients), _view(other.polynomial.coefficients), self.order, True, self.polynomial.ring, budget)
        var poly = DensePoly[Self.C].from_coefficients(self.polynomial.variable, self.polynomial.ring, values^, budget)
        return Self(poly^, self.order)

    def mul(self, other: Self, mut budget: Budget) raises PolyError -> Self:
        """Multiply modulo the common truncation order.

        Args:
            other: The second series in the same variable, domain and order.
            budget: The shared work allowance.

        Returns:
            The truncated product.

        Raises:
            PolyError: DOMAIN for incompatible inputs or unavailable divisions, LIMIT or CAPACITY on work limits.
        """
        self._same(other, budget)
        var values = _mul_values[_ExactOps[Self.C]](_view(self.polynomial.coefficients), _view(other.polynomial.coefficients), self.order, self.polynomial.ring, budget)
        var poly = DensePoly[Self.C].from_coefficients(self.polynomial.variable, self.polynomial.ring, values^, budget)
        return Self(poly^, self.order)

    def divide(self, other: Self, mut budget: Budget) raises PolyError -> Self:
        """Divide by a series with invertible constant coefficient.

        Args:
            other: The second series in the same variable, domain and order.
            budget: The shared work allowance.

        Returns:
            The quotient modulo the common order.

        Raises:
            PolyError: DOMAIN for incompatible inputs or unavailable divisions, LIMIT or CAPACITY on work limits.
        """
        self._same(other, budget)
        var values = _newton_divide[_ExactOps[Self.C]](_view(self.polynomial.coefficients), _view(other.polynomial.coefficients), self.order, self.polynomial.ring, budget) if _use_newton[Self.C](self.order, len(other.polynomial.coefficients)) else _divide_values[_ExactOps[Self.C]](_view(self.polynomial.coefficients), _view(other.polynomial.coefficients), self.order, self.polynomial.ring, budget)
        var poly = DensePoly[Self.C].from_coefficients(self.polynomial.variable, self.polynomial.ring, values^, budget)
        return Self(poly^, self.order)

    def inverse(self, mut budget: Budget) raises PolyError -> Self:
        """Invert a series with invertible constant coefficient.

        Args:
            budget: The shared work allowance.

        Returns:
            The multiplicative inverse at the original precision.

        Raises:
            PolyError: DOMAIN for incompatible inputs or unavailable divisions, LIMIT or CAPACITY on work limits.
        """
        self._validate(budget)
        var values: List[Self.C]
        if _use_newton[Self.C](self.order, len(self.polynomial.coefficients)):
            var numerator: List[Self.C] = [_ExactOps[Self.C].integer(1, self.polynomial.ring, budget)]
            values = _newton_divide[_ExactOps[Self.C]](_view(numerator), _view(self.polynomial.coefficients), self.order, self.polynomial.ring, budget)
        else:
            values = _divide_values[_ExactOps[Self.C], True](_view(List[Self.C]()), _view(self.polynomial.coefficients), self.order, self.polynomial.ring, budget)
        var poly = DensePoly[Self.C].from_coefficients(self.polynomial.variable, self.polynomial.ring, values^, budget)
        return Self(poly^, self.order)

    def compose(self, other: Self, mut budget: Budget) raises PolyError -> Self:
        """Compose with a series whose constant is exactly zero.

        Args:
            other: The second series in the same variable, domain and order.
            budget: The shared work allowance.

        Returns:
            The composition at the common precision.

        Raises:
            PolyError: DOMAIN for incompatible inputs or unavailable divisions, LIMIT or CAPACITY on work limits.
        """
        self._same(other, budget)
        _series_composition[_ExactOps[Self.C]](_view(other.polynomial.coefficients), self.order, self.polynomial.ring, budget)
        var values = _compose_values[_ExactOps[Self.C]](_view(self.polynomial.coefficients), _view(other.polynomial.coefficients), self.order, self.polynomial.ring, budget)
        var poly = DensePoly[Self.C].from_coefficients(self.polynomial.variable, self.polynomial.ring, values^, budget)
        return Self(poly^, self.order)

    def derivative(self, mut budget: Budget) raises PolyError -> Self:
        """Differentiate and decrease known precision by one.

        Args:
            budget: The shared work allowance.

        Returns:
            The formal derivative, with order max(0, order-1).

        Raises:
            PolyError: DOMAIN for incompatible inputs or unavailable divisions, LIMIT or CAPACITY on work limits.
        """
        self._validate(budget)
        var values = _derivative_values[_ExactOps[Self.C]](_view(self.polynomial.coefficients), self.polynomial.ring, budget)
        var poly = DensePoly[Self.C].from_coefficients(self.polynomial.variable, self.polynomial.ring, values^, budget)
        return Self(poly^, max(0, self.order - 1))

    def integrate(self, mut budget: Budget) raises PolyError -> Self:
        """Integrate with zero constant and increase precision by one.

        Args:
            budget: The shared work allowance.

        Returns:
            The antiderivative when required coefficient divisions exist.

        Raises:
            PolyError: DOMAIN for incompatible inputs or unavailable divisions, LIMIT or CAPACITY on work limits.
        """
        self._validate(budget)
        var values = _integral_values[_ExactOps[Self.C]](_view(self.polynomial.coefficients), self.polynomial.ring, budget)
        var poly = DensePoly[Self.C].from_coefficients(self.polynomial.variable, self.polynomial.ring, values^, budget)
        return Self(poly^, _sum(self.order, 1))

    def log(self, mut budget: Budget) raises PolyError -> Self:
        """Compute a formal logarithm with constant coefficient one.

        Args:
            budget: The shared work allowance.

        Returns:
            The zero-constant logarithm at the original precision.

        Raises:
            PolyError: DOMAIN for incompatible inputs or unavailable divisions, LIMIT or CAPACITY on work limits.
        """
        self._validate(budget)
        var values = _exact_log(_view(self.polynomial.coefficients), self.order, self.polynomial.ring, budget)
        var poly = DensePoly[Self.C].from_coefficients(self.polynomial.variable, self.polynomial.ring, values^, budget)
        return Self(poly^, self.order)

    def exp(self, mut budget: Budget) raises PolyError -> Self:
        """Compute a formal exponential with constant coefficient zero.

        Args:
            budget: The shared work allowance.

        Returns:
            The unit-constant exponential at the original precision.

        Raises:
            PolyError: DOMAIN for incompatible inputs or unavailable divisions, LIMIT or CAPACITY on work limits.
        """
        self._validate(budget)
        var values = _exact_exp(_view(self.polynomial.coefficients), self.order, self.polynomial.ring, budget)
        var poly = DensePoly[Self.C].from_coefficients(self.polynomial.variable, self.polynomial.ring, values^, budget)
        return Self(poly^, self.order)

    def revert(self, mut budget: Budget) raises PolyError -> Self:
        """Invert composition for zero constant and invertible linear term.

        Args:
            budget: The shared work allowance.

        Returns:
            The reversion at the original precision, requiring order at least two.

        Raises:
            PolyError: DOMAIN for incompatible inputs or unavailable divisions, LIMIT or CAPACITY on work limits.
        """
        self._validate(budget)
        var values = _revert_values[_ExactOps[Self.C]](_view(self.polynomial.coefficients), self.order, self.polynomial.ring, budget)
        var poly = DensePoly[Self.C].from_coefficients(self.polynomial.variable, self.polynomial.ring, values^, budget)
        return Self(poly^, self.order)
