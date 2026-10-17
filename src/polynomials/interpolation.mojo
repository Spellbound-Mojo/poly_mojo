"""Reusable product trees and independently checked exact interpolation."""
from .coefficients import CoefficientField, ModInt, Modulus
from .dense import DensePoly
from .coefficient_buffer import _view
from .errors import Budget, PolyError, PolyErrorKind, _allocation, _charge_size, _sum, _product
from .evaluate import evaluate_dense, _derivative_dense, _natural
from .calculus import jet_evaluate
from ._coefficient_ops import _copy
from ._dense_ops import _remainder
from ._toolkit_exact import _ExactOps
from ._toolkit_ops import _values, _hermite_values
from ._nmod import _Field, _field, _to, _from
from ._multipoint import _Tree, _evaluate as _tree_evaluate, _interpolate as _tree_interpolate, _inverse_weights


def _validate[C: CoefficientField](values: List[C], ring: C.Context, mut budget: Budget) raises PolyError:
    for value in values:
        _charge_size(value.size(), budget)
        if value.context() != ring:
            raise PolyError(PolyErrorKind.DOMAIN, "interpolation coefficient in another field")


def _distinct[C: CoefficientField](points: List[C], mut budget: Budget) raises PolyError -> Bool:
    for i in range(len(points)):
        for j in range(i):
            _charge_size(_sum(points[i].size(), points[j].size()), budget)
            if points[i] == points[j]:
                return False
    return True


@fieldwise_init
struct MultipointPlan[C: CoefficientField](Copyable, Movable):
    """Reuse a balanced product tree for exact evaluation and interpolation.

    Parameters:
        C: The exact coefficient field.
    """
    var _variable: Int64
    var _ring: Self.C.Context
    var _points: List[Self.C]
    var _products: List[DensePoly[Self.C]]
    var _left: List[Int]
    var _right: List[Int]
    var _inverse_weights: List[Self.C]
    var _tree: Optional[_Tree]
    """Odd prime fields keep a native residue tree instead of the generic products."""

    @staticmethod
    def prepare( variable: Int64, ring: Self.C.Context, points: List[Self.C], mut budget: Budget) raises PolyError -> Self:
        """Prepare immutable product factors for an ordered point list.

        Args:
            variable: The retained polynomial variable.
            ring: The coefficient field context.
            points: Evaluation points; repetitions are allowed for evaluation.
            budget: The shared work allowance.

        Returns:
            A reusable product tree with privately stored nodes.

        Raises:
            PolyError: DOMAIN for invalid points or variable, LIMIT or CAPACITY on work limits.
        """
        _validate(points, ring, budget)
        var prepared_variable = variable
        var prepared_ring = ring.copy()
        var prepared_points = _values[_ExactOps[Self.C]](_view(points), len(points), ring, budget)
        comptime if Self.C == ModInt:
            ref field = rebind[Modulus](ring)
            if _native(field) and len(points) > 1:
                var f = _field(field.value)
                var tree = _Tree(_residues(rebind[List[ModInt]](points), f, budget), f, budget)
                return Self(prepared_variable, prepared_ring^, prepared_points^, List[DensePoly[Self.C]](), List[Int](), List[Int](), List[Self.C](), Optional(tree^))
        var capacity = _product(len(points), 2)
        _allocation[DensePoly[Self.C]](capacity, budget)
        _allocation[Int](_product(capacity, 2), budget)
        var prepared_products = List[DensePoly[Self.C]](capacity=capacity)
        var prepared_left = List[Int](capacity=capacity)
        var prepared_right = List[Int](capacity=capacity)
        _allocation[Int](len(points), budget)
        var level = List[Int](capacity=len(points))
        for i in range(len(points)):
            _allocation[Self.C](2, budget)
            prepared_products.append(DensePoly[Self.C].from_coefficients(variable, ring, [points[i].neg(budget), Self.C.one(ring)], budget))
            prepared_left.append(-1)
            prepared_right.append(-1)
            level.append(i)
        while len(level) > 1:
            _allocation[Int]((len(level) + 1) // 2, budget)
            var next = List[Int](capacity=(len(level) + 1) // 2)
            for i in range(0, len(level), 2):
                budget.charge(1)
                if i + 1 == len(level):
                    next.append(level[i])
                else:
                    var left = level[i]
                    var right = level[i + 1]
                    var product = prepared_products[left].mul(prepared_products[right], budget)
                    next.append(len(prepared_products))
                    prepared_products.append(product^)
                    prepared_left.append(left)
                    prepared_right.append(right)
            level = next^
        return Self(prepared_variable, prepared_ring^, prepared_points^, prepared_products^, prepared_left^, prepared_right^, List[Self.C](), None)

    @staticmethod
    def prepare_interpolation(variable: Int64, ring: Self.C.Context, points: List[Self.C], mut budget: Budget) raises PolyError -> Self:
        """Prepare a product tree and immutable inverse interpolation weights.

        Args:
            variable: The retained polynomial variable.
            ring: The coefficient field context.
            points: Distinct evaluation and interpolation nodes.
            budget: The shared work allowance, including weight preparation.

        Returns:
            A reusable plan whose interpolation calls reuse inverse derivative weights.

        Raises:
            PolyError: DOMAIN for repeated or invalid points, LIMIT or CAPACITY on work limits.
        """
        var plan = Self.prepare(variable, ring, points, budget)
        plan._inverse_weights = plan._weights(budget)
        return plan^

    def _weights(self, mut budget: Budget) raises PolyError -> List[Self.C]:
        if not len(self._points):
            return List[Self.C]()
        comptime if Self.C == ModInt:
            if self._tree:
                ref field = rebind[Modulus](self._ring)
                var f = _field(field.value)
                var native = _inverse_weights(self._tree.value(), f, budget)
                return rebind_var[List[Self.C]](_modints(native, field, f, budget))
        var weights = self.evaluate(_derivative_dense(self._products[len(self._products) - 1], budget), budget)
        for i in range(len(weights)):
            weights[i] = weights[i].inverse(budget)
        return weights^

    def point_count(self) -> Int:
        """Return the number of prepared points.

        Returns:
            The point count, including repetitions.
        """
        return len(self._points)

    def evaluate(self, poly: DensePoly[Self.C], mut budget: Budget) raises PolyError -> List[Self.C]:
        """Evaluate by propagating remainders down the prepared tree.

        Args:
            poly: The polynomial in this plan's field and variable.
            budget: The shared work allowance.

        Returns:
            Values in the original point order.

        Raises:
            PolyError: DOMAIN for incompatible input, LIMIT or CAPACITY on work limits.
        """
        poly.check_invariants(budget)
        if poly.variable != self._variable or poly.ring != self._ring:
            raise PolyError(PolyErrorKind.DOMAIN, "multipoint plan and polynomial disagree")
        var result = List[Self.C]()
        if not len(self._points):
            return result^
        comptime if Self.C == ModInt:
            if self._tree:
                ref field = rebind[Modulus](self._ring)
                var f = _field(field.value)
                var coefficients = _residues(rebind[List[ModInt]](poly.coefficients.to_list(budget)), f, budget)
                var values = _tree_evaluate(self._tree.value(), coefficients, f, budget)
                return rebind_var[List[Self.C]](_modints(values, field, f, budget))
        var count = len(self._products)
        _allocation[DensePoly[Self.C]](count, budget)
        var remainders = List[DensePoly[Self.C]](length=count, fill=DensePoly[Self.C](self._variable, self._ring.copy()))
        remainders[count - 1] = _remainder(poly, self._products[count - 1], budget)
        for i in range(count - 1, len(self._points) - 1, -1):
            budget.charge(1)
            var left = self._left[i]
            var right = self._right[i]
            remainders[left] = _remainder(remainders[i], self._products[left], budget)
            remainders[right] = _remainder(remainders[i], self._products[right], budget)
            # Both children now own their remainder. Release this level's
            # coefficient payload instead of retaining the complete trace.
            comptime if Self.C != ModInt:
                if len(self._points) >= 32:
                    remainders[i].coefficients = List[Self.C]()
        _allocation[Self.C](len(self._points), budget)
        for i in range(len(self._points)):
            budget.charge(1)
            result.append(Self.C.zero(self._ring) if remainders[i].is_zero() else _copy(remainders[i].coefficients[0], budget))
        return result^

    def interpolate(self, values: List[Self.C], mut budget: Budget) raises PolyError -> DensePoly[Self.C]:
        """Interpolate values using derivative weights and the product tree.

        Args:
            values: One value per prepared point.
            budget: The shared work allowance.

        Returns:
            The unique polynomial of degree less than the point count.

        Raises:
            PolyError: DOMAIN for duplicate points or incompatible values, LIMIT or CAPACITY on work limits.
        """
        _validate(values, self._ring, budget)
        if len(values) != len(self._points):
            raise PolyError(PolyErrorKind.DOMAIN, "interpolation value count mismatch")
        if not len(values):
            return DensePoly[Self.C](self._variable, self._ring.copy())
        if len(self._inverse_weights):
            return self._interpolate(values, self._inverse_weights, budget)
        var weights = self._weights(budget)
        return self._interpolate(values, weights, budget)

    def _interpolate(self, values: List[Self.C], weights: List[Self.C], mut budget: Budget) raises PolyError -> DensePoly[Self.C]:
        comptime if Self.C == ModInt:
            if self._tree:
                ref field = rebind[Modulus](self._ring)
                var f = _field(field.value)
                var native = _tree_interpolate(self._tree.value(), _residues(rebind[List[ModInt]](values), f, budget), _residues(rebind[List[ModInt]](weights), f, budget), f, budget)
                var coefficients = _modints(native, field, f, budget)
                return rebind_var[DensePoly[Self.C]](DensePoly[ModInt].from_coefficients(self._variable, field, coefficients^, budget))
        var count = len(self._products)
        _allocation[DensePoly[Self.C]](count, budget)
        var parts = List[DensePoly[Self.C]](capacity=count)
        for i in range(len(values)):
            var coefficient = values[i].mul(weights[i], budget)
            _allocation[Self.C](1, budget)
            parts.append(DensePoly[Self.C].from_coefficients(self._variable, self._ring, [coefficient^], budget))
        for i in range(len(values), count):
            var left = self._left[i]
            var right = self._right[i]
            var a = parts[left].mul(self._products[right], budget)
            var b = parts[right].mul(self._products[left], budget)
            comptime if Self.C != ModInt:
                if len(values) >= 32:
                    parts[left].coefficients = List[Self.C]()
                    parts[right].coefficients = List[Self.C]()
            parts.append(a.add(b, budget))
        var result = DensePoly[Self.C](self._variable, self._ring.copy())
        swap(result, parts[count - 1])
        return result^


def _residues(values: List[ModInt], f: _Field, mut budget: Budget) raises PolyError -> List[UInt64]:
    _allocation[UInt64](len(values), budget)
    var result = List[UInt64](capacity=len(values))
    for v in values:
        result.append(_to(v.value, f))
    return result^


def _modints(values: List[UInt64], ring: Modulus, f: _Field, mut budget: Budget) raises PolyError -> List[ModInt]:
    _allocation[ModInt](len(values), budget)
    var result = List[ModInt](capacity=len(values))
    for v in values:
        result.append(ModInt(_from(v, f), ring))
    return result^


def _native(ring: Modulus) -> Bool:
    """Whether a word prime field has native residue trees (odd primes)."""
    return ring.value > 2


def interpolate[C: CoefficientField](variable: Int64, ring: C.Context, points: List[C], values: List[C], mut budget: Budget) raises PolyError -> DensePoly[C]:
    """Interpolate distinct points over an exact field.

    Parameters:
        C: The exact coefficient field.

    Args:
        variable: The output variable.
        ring: The coefficient field context.
        points: Distinct interpolation nodes.
        values: Corresponding function values.
        budget: The shared work allowance.

    Returns:
        The degree-bounded interpolant, or zero for empty data.

    Raises:
        PolyError: DOMAIN for invalid data, LIMIT or CAPACITY on work limits.
    """
    var plan = MultipointPlan[C].prepare(variable, ring, points, budget)
    return plan.interpolate(values, budget)


def hermite_interpolate[C: CoefficientField](variable: Int64, ring: C.Context, points: List[C], jets: List[List[C]], mut budget: Budget, *, derivatives: Bool = True) raises PolyError -> DensePoly[C]:
    """Interpolate value and derivative constraints over an exact field.

    Parameters:
        C: The exact coefficient field.

    Args:
        variable: The output variable.
        ring: The coefficient field context.
        points: Distinct interpolation nodes.
        jets: Nonempty consecutive derivative lists beginning with the value.
        budget: The shared work allowance.
        derivatives: Interpret jets as raw derivatives; false selects Taylor coefficients.

    Returns:
        The unique polynomial of degree less than the number of constraints.

    Raises:
        PolyError: DOMAIN for invalid data or noninvertible factorials, LIMIT or CAPACITY on work limits.
    """
    _validate(points, ring, budget)
    for jet in jets:
        _validate(jet, ring, budget)
    var values = _hermite_values[_ExactOps[C]](_view(points), jets, derivatives, ring, budget)
    return DensePoly[C].from_coefficients(variable, ring, values^, budget)


def check_interpolation[C: CoefficientField](poly: DensePoly[C], points: List[C], values: List[C], mut budget: Budget) raises PolyError -> Bool:
    """Check degree, distinct nodes and sample identities independently.

    Parameters:
        C: The exact coefficient field.

    Args:
        poly: The proposed interpolant.
        points: Interpolation nodes.
        values: Claimed sample values.
        budget: The shared work allowance.

    Returns:
        Whether the constraints uniquely identify this polynomial.

    Raises:
        PolyError: DOMAIN for malformed coefficients, LIMIT or CAPACITY on work limits.
    """
    poly.check_invariants(budget)
    _validate(points, poly.ring, budget)
    _validate(values, poly.ring, budget)
    if len(points) != len(values) or poly.degree() >= len(points) or not _distinct(points, budget):
        return False
    for i in range(len(points)):
        var actual = evaluate_dense(poly, points[i], budget)
        _charge_size(_sum(actual.size(), values[i].size()), budget)
        if actual != values[i]:
            return False
    return True


def check_hermite_interpolation[C: CoefficientField](poly: DensePoly[C], points: List[C], jets: List[List[C]], mut budget: Budget, *, derivatives: Bool = True) raises PolyError -> Bool:
    """Check Hermite constraints by Taylor evaluation and a degree bound.

    Parameters:
        C: The exact coefficient field.

    Args:
        poly: The proposed interpolant.
        points: Distinct interpolation nodes.
        jets: Claimed consecutive constraints beginning with the value.
        budget: The shared work allowance.
        derivatives: Whether constraints are raw derivatives instead of Taylor coefficients.

    Returns:
        Whether all constraints uniquely identify the polynomial.

    Raises:
        PolyError: DOMAIN for malformed coefficients, LIMIT or CAPACITY on work limits.
    """
    poly.check_invariants(budget)
    _validate(points, poly.ring, budget)
    if len(points) != len(jets) or not _distinct(points, budget):
        return False
    var total = 0
    for i in range(len(points)):
        _validate(jets[i], poly.ring, budget)
        if not len(jets[i]):
            return False
        total = _sum(total, len(jets[i]))
        var actual = jet_evaluate(poly, points[i], len(jets[i]), budget)
        var factorial = C.one(poly.ring)
        for j in range(len(actual)):
            if derivatives and j:
                factorial = factorial.mul(_natural[C](UInt64(j), poly.ring, budget), budget)
                _charge_size(factorial.size(), budget)
                if factorial.is_zero():
                    return False
                actual[j] = actual[j].mul(factorial, budget)
            _charge_size(_sum(actual[j].size(), jets[i][j].size()), budget)
            if actual[j] != jets[i][j]:
                return False
    return poly.degree() < total
