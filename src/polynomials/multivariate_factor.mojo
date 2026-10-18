"""Exact sparse multivariate factorization by evaluation and Hensel lifting."""
from .errors import Budget, PolyError, PolyErrorKind, _allocation, _charge_size, _sum
from .coefficients import CoefficientRing, QQ, ZZ, ModInt
from .exact_complex import QQi
from .sparse import SparsePoly
from .monomial import MonomialOrder
from .division import divide_exact
from .certificates import _equal
from ._gcd import _primitive_zz
from ._images import _rational_image, _integer_image
from ._multivariate_factor import _atoms, _normalize
from ._coefficient_ops import _copy as _copy_coefficient
from apn_mojo import Integer, Rational
from .coefficients import NoContext
from .dense import DensePoly
from .squarefree import squarefree
from ._views import _join
from ._grouping import _without
from ._coefficient_ops import _gcd_coefficient, _exact
from .sparse import Term


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
    if not f.is_zero():
        var atoms = _atoms(f.reorder(MonomialOrder(), budget), budget)
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


def _imul(a: Integer, b: Integer, mut budget: Budget) raises PolyError -> Integer:
    _charge_size(a.magnitude_bit_length() // 64 + b.magnitude_bit_length() // 64 + 1, budget)
    try:
        return a * b
    except err:
        raise PolyError(PolyErrorKind.CAPACITY, String(err))


def _iadd(a: Integer, b: Integer, mut budget: Budget) raises PolyError -> Integer:
    _charge_size(max(a.magnitude_bit_length(), b.magnitude_bit_length()) // 64 + 1, budget)
    try:
        return a + b
    except err:
        raise PolyError(PolyErrorKind.CAPACITY, String(err))


def _ipow(a: Integer, e: Int, mut budget: Budget) raises PolyError -> Integer:
    var result = Integer(1)
    for _ in range(e):
        budget.charge(1)
        result = _imul(result, a, budget)
    return result^


def _integer_root(a: Integer, e: Int, mut budget: Budget) raises PolyError -> Optional[Integer]:
    """The integer r with r^e = a, if one exists (r > 0 for even e)."""
    var negative = a.sign() < 0
    if negative and e % 2 == 0:
        return None
    var magnitude = a.copy()
    if negative:
        magnitude = -magnitude
    var lo = Integer(0)
    var hi: Integer
    try:
        hi = Integer(1) << (magnitude.magnitude_bit_length() // e + 1)
    except err:
        raise PolyError(PolyErrorKind.CAPACITY, String(err))
    while lo < hi:
        budget.charge(1)
        var mid: Integer
        try:
            mid = (lo + hi + Integer(1)) >> 1
        except err:
            raise PolyError(PolyErrorKind.CAPACITY, String(err))
        if _ipow(mid, e, budget) > magnitude:
            try:
                hi = mid - Integer(1)
            except err:
                raise PolyError(PolyErrorKind.CAPACITY, String(err))
        else:
            lo = mid^
    if not (_ipow(lo, e, budget) == magnitude):
        return None
    if negative:
        return -lo
    return lo^


def _power_hint(f: SparsePoly[ZZ], main: Int64, mut budget: Budget) raises PolyError -> Int:
    """The gcd of the multiplicities of f at fixed small points for every
    variable but main, or 1 when that image loses degree."""
    var degree = f.degree_in(main, budget)
    _allocation[Integer](_sum(degree, 1), budget)
    var values = List[Integer](length=degree + 1, fill=Integer(0))
    # Distinct small points per variable index: 2, 3, 4, ...
    var powers = List[List[Integer]]()
    for _ in range(61):
        var row = List[Integer]()
        row.append(Integer(1))
        powers.append(row^)
    for term in f.terms:
        budget.charge(1)
        var value = term.coefficient.value.copy()
        var k = 0
        for pair in term.monomial.pairs:
            budget.charge(1)
            if pair[0] == main:
                k = Int(pair[1])
            else:
                var v = Int(pair[0] % 61)
                while len(powers[v]) <= Int(pair[1]):
                    powers[v].append(_imul(powers[v][len(powers[v]) - 1], Integer(v + 2), budget))
                value = _imul(value, powers[v][Int(pair[1])], budget)
        values[k] = _iadd(values[k], value, budget)
    if values[degree].sign() == 0:
        return 1
    var coefficients = List[QQ]()
    for v in values:
        coefficients.append(QQ(Rational(v.copy())))
    var image = DensePoly[QQ].from_coefficients(main, NoContext(), coefficients^, budget)
    var blocks = squarefree(image, budget)
    var e = 0
    for entry in blocks.factors:
        budget.charge(1)
        var a = e
        var b = entry[1]
        while b:
            var t = a % b
            a = b
            b = t
        e = a
    return max(e, 1)


def _primitive_ordered(f: SparsePoly[ZZ], mut budget: Budget) raises PolyError -> SparsePoly[ZZ]:
    """_primitive_zz without re-sorting: the content stops at one, and
    dividing every coefficient by the same scalar keeps the term order."""
    var content = ZZ.zero(NoContext())
    for term in f.terms:
        budget.charge(1)
        content = _gcd_coefficient(content, term.coefficient, budget)
        if content.value == Integer(1):
            break
    if f.terms[len(f.terms) - 1].coefficient.value.sign() < 0:
        content = content.neg(budget)
    if content.value == Integer(1):
        return f._copy(budget)
    var result = SparsePoly[ZZ](f.order.copy(), NoContext())
    _allocation[Term[ZZ]](len(f.terms), budget)
    result.terms = List[Term[ZZ]](capacity=len(f.terms))
    for term in f.terms:
        budget.charge(1)
        _charge_size(len(term.monomial.pairs), budget)
        result.terms.append(Term[ZZ](term.monomial.copy(), _exact(term.coefficient, content, budget)))
    return result^


def _top_coefficients(f: SparsePoly[ZZ], main: Int64, low: Int, mut budget: Budget) raises PolyError -> List[SparsePoly[ZZ]]:
    """The coefficients of main^low .. main^deg in f, in that order."""
    var top = f.degree_in(main, budget)
    var buckets = List[List[Term[ZZ]]]()
    for _ in range(low, top + 1):
        buckets.append(List[Term[ZZ]]())
    for term in f.terms:
        budget.charge(1)
        var k = Int(term.monomial.exponent(main, budget))
        if k < low:
            continue
        _allocation[Term[ZZ]](1, budget)
        buckets[k - low].append(Term[ZZ](_without(term.monomial, main, budget), term.coefficient.copy()))
    var result = List[SparsePoly[ZZ]]()
    for i in range(len(buckets)):
        budget.charge(1)
        var terms = List[Term[ZZ]]()
        swap(terms, buckets[i])
        result.append(SparsePoly[ZZ].from_terms(terms^, f.order, NoContext(), budget))
    return result^


def _power_root(f: SparsePoly[ZZ], e: Int, mut budget: Budget) raises PolyError -> Optional[SparsePoly[ZZ]]:
    """h with h^e = f, if one exists.

    In the main variable, with reversed coefficient sequences g of f and a
    of h, h = f^(1/e) gives h' f = (1/e) h f' and so Miller's recurrence
    k e g_0 a_k = sum_(j=1..k) (j - e (k - j)) g_j a_(k-j); every division is
    exact when the root exists, and the candidate is verified by its power."""
    var variables = f.variables(budget)
    if len(variables) == 0:
        if f.is_zero():
            return None
        var r = _integer_root(f.terms[0].coefficient.value, e, budget)
        if not r:
            return None
        return SparsePoly[ZZ].constant(ZZ(r.take()), f.order, budget)
    var main = variables[len(variables) - 1]
    var n = f.degree_in(main, budget)
    if n % e != 0:
        return None
    var d = n // e
    # g[i] is the coefficient of main^(n - d + i); only the top d + 1 enter.
    var top = _top_coefficients(f, main, n - d, budget)
    var lead = _power_root(top[d], e, budget)
    if not lead:
        return None
    var a = List[SparsePoly[ZZ]]()
    a.append(lead.take())
    for k in range(1, d + 1):
        budget.charge(1)
        var total = SparsePoly[ZZ](f.order.copy(), NoContext())
        for j in range(1, min(k, n) + 1):
            budget.charge(1)
            var weight = j - e * (k - j)
            if weight == 0 or top[d - j].is_zero():
                continue
            total = total.add(top[d - j].mul(a[k - j], budget).scale(ZZ(Integer(weight)), budget), budget)
        var quotient = divide_exact(total, top[d].scale(ZZ(Integer(k * e)), budget), budget)
        if not quotient:
            return None
        a.append(quotient.take())
    var coefficients = List[SparsePoly[ZZ]]()
    for i in range(d + 1):
        coefficients.append(a[d - i]._copy(budget))
    var h = _join(coefficients, main, f, budget)
    if not _equal(h.pow(UInt64(e), budget), f, budget):
        return None
    return h^


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
    # A perfect power h^e factors as h with multiplicities times e; the
    # squarefree gcd and every division by a repeated factor are skipped.
    if not f.is_zero():
        var variables = f.variables(budget)
        if len(variables) >= 2:
            var primitive = _primitive_ordered(f, budget)
            var e = _power_hint(primitive, variables[len(variables) - 1], budget)
            if e >= 2:
                var root = _power_root(primitive, e, budget)
                if root:
                    var inner = factor_multivariate_integer(root.value(), budget)
                    var scale = _quotient_zz(f.terms[0].coefficient, primitive.terms[0].coefficient, budget)
                    var unit = ZZ(_imul(scale.value, _ipow(inner.unit.value, e, budget), budget))
                    var powered = List[Tuple[SparsePoly[ZZ], Int]]()
                    for entry in inner.factors:
                        budget.charge(1)
                        powered.append((entry[0]._copy(budget), entry[1] * e))
                    _sort(powered, budget)
                    return MultivariateFactorization[ZZ](unit^, powered^)
    # Multiplicities are counted by exact division over ZZ directly; the
    # rational route divided twice, once with Rational arithmetic.
    var remaining = f._copy(budget)
    var factors = List[Tuple[SparsePoly[ZZ], Int]]()
    if not f.is_zero():
        var rational = _rational_image(f, budget)
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
