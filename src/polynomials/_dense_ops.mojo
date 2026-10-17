"""Shared budgeted dense views and field operations."""
from .coefficients import CoefficientRing, CoefficientField, ModInt, Modulus
from .dense import DensePoly, _slice
from ._coefficient_ops import _copy as _copy_coefficient
from .coefficient_buffer import _view
from .errors import Budget, PolyError, PolyErrorKind, _allocation
from .evaluate import _derivative_dense as _derivative
from .division import _dense_divide
from ._euclidean import _extended
from ._nmod_euclid import _Field, _gcd_words


def _words(f: DensePoly[ModInt], field: _Field, mut budget: Budget) raises PolyError -> List[UInt64]:
    _allocation[UInt64](len(f.coefficients), budget)
    var out = List[UInt64](capacity=len(f.coefficients))
    for i in range(len(f.coefficients)):
        out.append(field.enter(f.coefficients[i].value))
    return out^


def _from_words(f: DensePoly[ModInt], words: List[UInt64], field: _Field, mut budget: Budget) raises PolyError -> DensePoly[ModInt]:
    _allocation[ModInt](len(words), budget)
    var values = List[ModInt](capacity=len(words))
    for w in words:
        values.append(ModInt(field.leave(w), f.ring))
    return DensePoly[ModInt]._from_canonical(f.variable, f.ring, values^)


def _word_gcd(f: DensePoly[ModInt], g: DensePoly[ModInt], mut budget: Budget) raises PolyError -> DensePoly[ModInt]:
    f._same(g)
    var field = _Field.of(f.ring.value)
    return _from_words(f, _gcd_words(_words(f, field, budget), _words(g, field, budget), field, budget), field, budget)


def _copy[C: CoefficientRing](f: DensePoly[C], mut budget: Budget) raises PolyError -> DensePoly[C]:
    return DensePoly[C]._from_canonical(f.variable, f.ring, _slice(_view(f.coefficients), 0, len(f.coefficients), budget))


def _constant[C: CoefficientRing](f: DensePoly[C], c: C, mut budget: Budget) raises PolyError -> DensePoly[C]:
    _allocation[C](1, budget)
    return DensePoly[C].from_coefficients(f.variable, f.ring, [_copy_coefficient(c, budget)], budget)


def _one[C: CoefficientRing](f: DensePoly[C], mut budget: Budget) raises PolyError -> DensePoly[C]:
    return _constant(f, C.one(f.ring), budget)


def _monic[C: CoefficientField](f: DensePoly[C], mut budget: Budget) raises PolyError -> DensePoly[C]:
    if f.is_zero():
        return _copy(f, budget)
    return f.scale(f.coefficients[f.degree()].inverse(budget), budget)


def _gcd[C: CoefficientField](f: DensePoly[C], g: DensePoly[C], mut budget: Budget) raises PolyError -> DensePoly[C]:
    comptime if C == ModInt:
        if rebind[Modulus](f.ring).value > 2:
            return rebind_var[DensePoly[C]](_word_gcd(rebind[DensePoly[ModInt]](f), rebind[DensePoly[ModInt]](g), budget))
    var result = _extended(f, g, budget, carry=False)
    var d = DensePoly[C](f.variable, f.ring.copy())
    swap(d, result[0])
    return d^


def _remainder[C: CoefficientField](f: DensePoly[C], g: DensePoly[C], mut budget: Budget) raises PolyError -> DensePoly[C]:
    var result = _dense_divide(f, g, False, budget, quotient=False)
    var r = DensePoly[C](f.variable, f.ring.copy())
    swap(r, result.remainder)
    return r^


def _exact[C: CoefficientField](f: DensePoly[C], g: DensePoly[C], mut budget: Budget) raises PolyError -> DensePoly[C]:
    var result = _dense_divide(f, g, False, budget)
    if not result.remainder.is_zero():
        raise PolyError(PolyErrorKind.DOMAIN, "inexact dense field quotient")
    var q = DensePoly[C](f.variable, f.ring.copy())
    swap(q, result.quotient)
    return q^
