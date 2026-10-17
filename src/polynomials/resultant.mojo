"""Resultants and the complete indexed subresultant family."""
from .errors import Budget, PolyError, PolyErrorKind, _allocation
from .coefficients import CoefficientRing, ZZ, ModInt
from .sparse import SparsePoly
from .dense import DensePoly
from ._views import _variables, _constant
from ._nmod import _Field, _resultant_words
from ._univariate_modular import _modular_resultant
from .certificates import ResultantResult
from .division import divide_exact
from ._tower import _zero, _lc, _exact_poly
from ._prs import _prs


def subresultants[C: CoefficientRing](f: SparsePoly[C], g: SparsePoly[C], variable: Int64, mut budget: Budget) raises PolyError -> List[SparsePoly[C]]:
    """Compute S_j for every index below the smaller degree, including zeros.

    Parameters:
        C: ZZ or a coefficient field.

    Args:
        f: The first polynomial.
        g: The second polynomial in the same ring and order.
        variable: The elimination variable.
        budget: The shared work allowance.

    Returns:
        The indexed subresultants S_0 through S_(min(deg(f),deg(g))-1).

    Raises:
        PolyError: DOMAIN for incompatible inputs, LIMIT or CAPACITY on work limits.
    """
    f._same(g, budget)
    var n = f.degree_in(variable, budget)
    var m = g.degree_in(variable, budget)
    var count = max(min(n, m), 0)
    _allocation[SparsePoly[C]](count, budget)
    var result = List[SparsePoly[C]](length=count, fill=_zero(f, budget))
    if not count:
        return result^
    var sequence = _prs(f, g, variable, False, budget)
    for entry in sequence:
        budget.charge(1)
        var k = entry.polynomial.degree_in(variable, budget)
        result[entry.index] = entry.polynomial._copy(budget)
        if k != entry.index:
            var leading = _lc(entry.polynomial, variable, budget)
            var multiplier = divide_exact(entry.principal, leading, budget)
            if multiplier:
                result[k] = entry.polynomial.mul(multiplier.value(), budget)
            else:
                # A defective PRS scale can be a rational function. The full
                # scaled subresultant is polynomial even when the scale is not.
                result[k] = _exact_poly(entry.polynomial.mul(entry.principal, budget), leading, budget)
    if n < m:
        for j in range(count):
            budget.charge(1)
            if ((n - j) % 2) and ((m - j) % 2):
                result[j] = result[j].neg(budget)
    return result^


def resultant[C: CoefficientRing](f: SparsePoly[C], g: SparsePoly[C], variable: Int64, mut budget: Budget) raises PolyError -> ResultantResult[C]:
    """Compute the resultant and multipliers proving its ideal membership.

    Parameters:
        C: ZZ or a coefficient field.

    Args:
        f: The first polynomial.
        g: The second polynomial in the same ring and order.
        variable: The elimination variable.
        budget: The shared work allowance.

    Returns:
        The Sylvester-convention resultant and its cofactor identity.

    Raises:
        PolyError: DOMAIN for incompatible inputs or two nonzero constants in the variable, LIMIT or CAPACITY on work limits.
    """
    f._same(g, budget)
    var zero = _zero(f, budget)
    if f.is_zero() or g.is_zero():
        return ResultantResult[C](zero._copy(budget), (zero._copy(budget), zero^))
    var n = f.degree_in(variable, budget)
    var m = g.degree_in(variable, budget)
    if n == 0 and m == 0:
        # E-1 assumes positive degrees. For two constants the empty
        # determinant is 1, which need not lie in their ideal over ZZ.
        raise PolyError(PolyErrorKind.DOMAIN, "resultant identity requires a positive degree")
    if n == 0:
        var u = f.pow(UInt64(m - 1), budget)
        return ResultantResult[C](u.mul(f, budget), (u^, zero^))
    if m == 0:
        var v = g.pow(UInt64(n - 1), budget)
        return ResultantResult[C](v.mul(g, budget), (zero^, v^))
    var sequence = _prs(f, g, variable, True, budget, history=False)
    if not len(sequence) or sequence[len(sequence) - 1].polynomial.degree_in(variable, budget) != 0:
        return ResultantResult[C](zero._copy(budget), (zero._copy(budget), zero^))
    ref last = sequence[len(sequence) - 1]
    var multiplier = divide_exact(last.principal, last.polynomial, budget)
    var u = _zero(f, budget)
    var v = _zero(f, budget)
    if multiplier:
        u = last.u.mul(multiplier.value(), budget)
        v = last.v.mul(multiplier.value(), budget)
    else:
        # Divide only after multiplying: last.principal / last.polynomial
        # need not be polynomial, while both scaled Bezout cofactors are.
        u = _exact_poly(last.u.mul(last.principal, budget), last.polynomial, budget)
        v = _exact_poly(last.v.mul(last.principal, budget), last.polynomial, budget)
    var value = last.principal._copy(budget)
    if n < m and (n % 2) and (m % 2):
        value = value.neg(budget)
        u = u.neg(budget)
        v = v.neg(budget)
    return ResultantResult[C](value^, (u^, v^))


def _word_resultant(f: DensePoly[ModInt], g: DensePoly[ModInt], mut budget: Budget) raises PolyError -> ModInt:
    var field = _Field.of(f.ring.value)
    _allocation[UInt64](len(f.coefficients) + len(g.coefficients), budget)
    var a = List[UInt64](capacity=len(f.coefficients))
    for i in range(len(f.coefficients)):
        a.append(field.enter(f.coefficients[i].value))
    var b = List[UInt64](capacity=len(g.coefficients))
    for i in range(len(g.coefficients)):
        b.append(field.enter(g.coefficients[i].value))
    return ModInt(field.leave(_resultant_words(a^, b^, field, budget)), f.ring)


def resultant_value[C: CoefficientRing](f: SparsePoly[C], g: SparsePoly[C], variable: Int64, mut budget: Budget) raises PolyError -> SparsePoly[C]:
    """Compute the resultant alone, without the multipliers of its identity.

    Univariate integer inputs use multi-modular reconstruction up to the
    Hadamard bound, univariate inputs over odd prime fields a word-size
    Euclidean recurrence, and all others the subresultant PRS of
    `resultant` without cofactor propagation.

    Parameters:
        C: ZZ or a coefficient field.

    Args:
        f: The first polynomial.
        g: The second polynomial in the same ring and order.
        variable: The elimination variable.
        budget: The shared work allowance.

    Returns:
        The Sylvester-convention resultant, equal to `resultant(f, g, variable).resultant`.

    Raises:
        PolyError: DOMAIN for incompatible inputs or two nonzero constants in the variable, LIMIT or CAPACITY on work limits.
    """
    f._same(g, budget)
    var zero = _zero(f, budget)
    if f.is_zero() or g.is_zero():
        return zero^
    var n = f.degree_in(variable, budget)
    var m = g.degree_in(variable, budget)
    if n == 0 and m == 0:
        raise PolyError(PolyErrorKind.DOMAIN, "resultant identity requires a positive degree")
    if n == 0:
        return f.pow(UInt64(m), budget)
    if m == 0:
        return g.pow(UInt64(n), budget)
    var variables = _variables(f, g, budget)
    if len(variables) == 1:
        comptime if C == ZZ:
            var fd = DensePoly[ZZ].from_sparse(rebind[SparsePoly[ZZ]](f), budget, variable=variable)
            var gd = DensePoly[ZZ].from_sparse(rebind[SparsePoly[ZZ]](g), budget, variable=variable)
            var value = ZZ(_modular_resultant(fd, gd, budget))
            if value.is_zero():
                return zero^
            return _constant(f, rebind[C](value), budget)
        elif C == ModInt:
            if rebind[SparsePoly[ModInt]](f).ring.value > 2:
                var value = _word_resultant(DensePoly[ModInt].from_sparse(rebind[SparsePoly[ModInt]](f), budget, variable=variable), DensePoly[ModInt].from_sparse(rebind[SparsePoly[ModInt]](g), budget, variable=variable), budget)
                if value.is_zero():
                    return zero^
                return _constant(f, rebind[C](value), budget)
    var sequence = _prs(f, g, variable, False, budget, history=False)
    if not len(sequence) or sequence[len(sequence) - 1].polynomial.degree_in(variable, budget) != 0:
        return zero^
    var value = sequence[len(sequence) - 1].principal._copy(budget)
    if n < m and (n % 2) and (m % 2):
        value = value.neg(budget)
    return value^
