"""Exact sparse multivariate factorization by evaluation and Hensel lifting."""
from .errors import Budget, PolyError, PolyErrorKind, _allocation, _charge_size, _sum
from .coefficients import CoefficientRing, QQ, ZZ, ModInt
from .exact_complex import QQi
from .sparse import SparsePoly, Term
from .monomial import Monomial, MonomialOrder
from .division import divide_exact
from .certificates import _equal
from ._gcd import _primitive_zz
from ._images import _rational_image, _integer_image
from ._multivariate_factor import _atoms, _normalize
from ._multivariate_gcd import _minimum_degrees
from ._coefficient_ops import _copy as _copy_coefficient
from ._power_roots import _imul, _ipow, _power_hint, _power_root, _primitive_ordered


@fieldwise_init
struct MultivariateFactorization[C: CoefficientRing](Copyable, Movable, Writable):
    """A sparse factorization whose product is independently checkable.

    Parameters:
        C: The coefficient ring.
    """
    var unit: Self.C
    """The scalar unit or content, including zero for zero input."""
    var factors: List[Tuple[SparsePoly[Self.C], Int]]
    """Distinct normalized irreducible factors with positive multiplicities."""


def _copy_factorization[C: CoefficientRing](proof: MultivariateFactorization[C], mut budget: Budget) raises PolyError -> MultivariateFactorization[C]:
    _allocation[Tuple[SparsePoly[C], Int]](len(proof.factors), budget)
    var factors = List[Tuple[SparsePoly[C], Int]](capacity=len(proof.factors))
    for entry in proof.factors:
        budget.charge(1)
        factors.append((entry[0]._copy(budget), entry[1]))
    return MultivariateFactorization[C](_copy_coefficient(proof.unit, budget), factors^)


def _less[C: CoefficientRing](a: SparsePoly[C], b: SparsePoly[C], mut budget: Budget) raises PolyError -> Bool:
    var da = a.total_degree(budget)
    var db = b.total_degree(budget)
    if da != db:
        return da < db
    for offset in range(min(len(a.terms), len(b.terms))):
        budget.charge(1)
        ref left = a.terms[len(a.terms) - 1 - offset]
        ref right = b.terms[len(b.terms) - 1 - offset]
        var order = a.order.compare(left.monomial, right.monomial, budget)
        if order != 0:
            return order < 0
        var delta = left.coefficient.sub(right.coefficient, budget)
        comptime if C == QQ:
            if not delta.is_zero():
                return rebind[QQ](delta).value.sign() < 0
        elif C == QQi:
            ref z = rebind[QQi](delta)
            if z.value.real().sign() != 0:
                return z.value.real().sign() < 0
            if z.value.imag().sign() != 0:
                return z.value.imag().sign() < 0
        elif C == ModInt:
            if not delta.is_zero():
                return rebind[ModInt](left.coefficient).value < rebind[ModInt](right.coefficient).value
        else:
            if not delta.is_zero():
                return rebind[ZZ](delta).value.sign() < 0
    return len(a.terms) < len(b.terms)


def _sort[C: CoefficientRing](mut factors: List[Tuple[SparsePoly[C], Int]], mut budget: Budget) raises PolyError:
    for i in range(1, len(factors)):
        budget.charge(1)
        var j = i
        while j > 0 and _less(factors[j][0], factors[j - 1][0], budget):
            budget.charge(1)
            var temporary = (factors[j][0]._copy(budget), factors[j][1])
            factors[j] = (factors[j - 1][0]._copy(budget), factors[j - 1][1])
            factors[j - 1] = temporary^
            j -= 1


def _unit[C: CoefficientRing](f: SparsePoly[C], mut budget: Budget) raises PolyError -> C:
    if f.is_zero():
        return C.zero(f.ring)
    if len(f.terms) != 1 or len(f.terms[0].monomial.pairs) != 0:
        raise PolyError(PolyErrorKind.DOMAIN, "factorization left a nonconstant cofactor")
    _charge_size(f.terms[0].coefficient.size(), budget)
    return f.terms[0].coefficient.copy()


def _extract_monomial[C: CoefficientRing](mut f: SparsePoly[C], mut factors: List[Tuple[SparsePoly[C], Int]], mut budget: Budget) raises PolyError:
    """Remove coordinate factors before squarefree reduction and Hensel lifting."""
    if f.is_zero():
        return
    var variables = f.variables(budget)
    _allocation[Int](len(variables), budget)
    var tops = List[Int](length=len(variables), fill=Int(UInt32.MAX))
    var minimum = _minimum_degrees(f, variables, tops, budget)
    _allocation[Tuple[Int64, UInt32]](len(variables), budget)
    var pairs = List[Tuple[Int64, UInt32]](capacity=len(variables))
    for i in range(len(variables)):
        budget.charge(1)
        if minimum[i]:
            pairs.append((variables[i], UInt32(minimum[i])))
    if len(pairs) == 0:
        return
    var common = Monomial(pairs^, budget)
    _allocation[Tuple[SparsePoly[C], Int]](len(common.pairs), budget)
    for pair in common.pairs:
        budget.charge(1)
        factors.append((SparsePoly[C].variable(pair[0], f.order, f.ring, budget), Int(pair[1])))
    for ref term in f.terms:
        budget.charge(1)
        term.monomial = term.monomial.div(common, budget)
    # KERNEL orders pair lists, so removing a variable can change term order.
    if f.order.kind == MonomialOrder.KERNEL:
        var terms = List[Term[C]]()
        swap(terms, f.terms)
        f = SparsePoly[C].from_terms(terms^, f.order, f.ring, budget)


def factor_multivariate(f: SparsePoly[QQ], mut budget: Budget) raises PolyError -> MultivariateFactorization[QQ]:
    """Factor a rational multivariate polynomial by monic transformation and lifting.

    Args:
        f: The input polynomial in any stored order, including zero and constants.
        budget: The shared work allowance.

    Returns:
        The scalar and distinct monic irreducible factors with multiplicities, sorted deterministically.

    Raises:
        PolyError: DOMAIN for malformed input, LIMIT or CAPACITY on work limits.
    """
    f.check_invariants(budget)
    var factors = List[Tuple[SparsePoly[QQ], Int]]()
    var remaining = f._copy(budget)
    _extract_monomial(remaining, factors, budget)
    if not f.is_zero():
        var atoms = _atoms(remaining.reorder(MonomialOrder(), budget), budget)
        for atom in atoms:
            budget.charge(1)
            var normalized = _normalize(atom.reorder(f.order, budget), budget)
            var multiplicity = 0
            while True:
                budget.charge(1)
                var quotient = divide_exact(remaining, normalized, budget)
                if not quotient:
                    break
                remaining = quotient.take()
                multiplicity = _sum(multiplicity, 1)
            if not multiplicity:
                raise PolyError(PolyErrorKind.DOMAIN, "lifted factor does not divide the original input")
            _allocation[Tuple[SparsePoly[QQ], Int]](1, budget)
            factors.append((normalized^, multiplicity))
    _sort(factors, budget)
    return MultivariateFactorization[QQ](_unit(remaining, budget), factors^)


def _quotient_zz(a: ZZ, b: ZZ, mut budget: Budget) raises PolyError -> ZZ:
    _charge_size(a.value.magnitude_bit_length() // 64 + 1, budget)
    try:
        return ZZ(a.value // b.value)
    except err:
        raise PolyError(PolyErrorKind.CAPACITY, String(err))


def factor_multivariate_integer(f: SparsePoly[ZZ], mut budget: Budget) raises PolyError -> MultivariateFactorization[ZZ]:
    """Factor an integer multivariate polynomial into primitive irreducible factors.

    Args:
        f: The input polynomial, including zero and constants.
        budget: The shared work allowance.

    Returns:
        The integer content and primitive factors with positive leading coefficients and multiplicities.

    Raises:
        PolyError: DOMAIN for malformed input, LIMIT or CAPACITY on work limits.
    """
    f.check_invariants(budget)
    var remaining = f._copy(budget)
    var factors = List[Tuple[SparsePoly[ZZ], Int]]()
    _extract_monomial(remaining, factors, budget)
    # A perfect power h^e factors as h with multiplicities times e; the
    # squarefree gcd and every division by a repeated factor are skipped.
    if not f.is_zero():
        var variables = remaining.variables(budget)
        if len(variables) >= 2:
            var primitive = _primitive_ordered(remaining, budget)
            var e = _power_hint(primitive, variables[len(variables) - 1], budget)
            if e >= 2:
                var root = _power_root(primitive, e, budget)
                if root:
                    var inner = factor_multivariate_integer(root.value(), budget)
                    var scale = _quotient_zz(remaining.terms[0].coefficient, primitive.terms[0].coefficient, budget)
                    var unit = ZZ(_imul(scale.value, _ipow(inner.unit.value, e, budget), budget))
                    _allocation[Tuple[SparsePoly[ZZ], Int]](len(inner.factors), budget)
                    for entry in inner.factors:
                        budget.charge(1)
                        factors.append((entry[0]._copy(budget), entry[1] * e))
                    _sort(factors, budget)
                    return MultivariateFactorization[ZZ](unit^, factors^)
    # Multiplicities are counted by exact division over ZZ directly; the
    # rational route divided twice, once with Rational arithmetic.
    if not f.is_zero():
        var rational = _rational_image(remaining, budget)
        var atoms = _atoms(rational.reorder(MonomialOrder(), budget), budget)
        _allocation[Tuple[SparsePoly[ZZ], Int]](len(atoms), budget)
        for atom in atoms:
            budget.charge(1)
            var primitive = _primitive_zz(_integer_image(_normalize(atom.reorder(rational.order, budget), budget), budget), budget)
            var multiplicity = 0
            while True:
                budget.charge(1)
                var quotient = divide_exact(remaining, primitive, budget)
                if not quotient:
                    break
                remaining = quotient.take()
                multiplicity = _sum(multiplicity, 1)
            if not multiplicity:
                raise PolyError(PolyErrorKind.DOMAIN, "integer factor reconstruction is inexact")
            factors.append((primitive^, multiplicity))
    _sort(factors, budget)
    return MultivariateFactorization[ZZ](_unit(remaining, budget), factors^)


def check_multivariate_factorization[C: CoefficientRing](f: SparsePoly[C], certificate: MultivariateFactorization[C], mut budget: Budget) raises PolyError -> Bool:
    """Verify the sparse factor product without asserting irreducibility.

    Parameters:
        C: The coefficient ring.

    Args:
        f: The original polynomial.
        certificate: The scalar, sparse factors and multiplicities.
        budget: The shared work allowance.

    Returns:
        Whether the factors with positive multiplicities multiply to the input.

    Raises:
        PolyError: DOMAIN for incompatible inputs, LIMIT or CAPACITY on work limits.
    """
    var product = SparsePoly[C].constant(certificate.unit, f.order, budget)
    for entry in certificate.factors:
        budget.charge(1)
        if entry[1] <= 0:
            return False
        product = product.mul(entry[0].pow(UInt64(entry[1]), budget), budget)
    return _equal(product, f, budget)
