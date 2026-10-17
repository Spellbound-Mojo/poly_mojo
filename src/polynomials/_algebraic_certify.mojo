"""Arithmetic producers retaining complete elimination and root witnesses."""
from std.collections import Optional
from .errors import Budget, PolyError, PolyErrorKind
from .coefficients import QQ, NoContext
from .dense import DensePoly
from .certificates import ResultantResult, RootCountCertificate
from .algebraic_types import RealAlgebraic, _check_real, _copy_sequence
from .algebraic_arithmetic import AlgebraicArithmeticCertificate
from ._algebraic import _rational, _root_cached, _NormalizationCache, _sturm_index, _refine, _sign
from ._algebraic_ops import _binary_definitions, _unary_definition, _operation_bounds, _rational_operation
from ._dense_ops import _exact
from ._root_ops import _copy as _copy_q, _variations, _sign_at
from .resultant import resultant


def _arithmetic(a: RealAlgebraic, b: RealAlgebraic, op: Int, mut budget: Budget) raises PolyError -> AlgebraicArithmeticCertificate:
    var cache = _NormalizationCache()
    return _arithmetic_cached(a, b, op, cache, budget)


def _arithmetic_cached(a: RealAlgebraic, b: RealAlgebraic, op: Int, mut cache: _NormalizationCache, mut budget: Budget) raises PolyError -> AlgebraicArithmeticCertificate:
    if not _check_real(a, budget) or (op < 3 and not _check_real(b, budget)):
        raise PolyError(PolyErrorKind.DOMAIN, "invalid algebraic operand")
    var left = _root_cached(a.polynomial, a.low, a.high, cache, budget)
    var right = _root_cached(b.polynomial, b.low, b.high, cache, budget) if op < 3 else _rational(QQ.zero(NoContext()), budget)
    var left_factor = _exact(a.polynomial, left.polynomial, budget)
    var right_factor = _exact(b.polynomial, right.polynomial, budget) if op < 3 else DensePoly[QQ](0, NoContext())
    if op == 4 and _sign(left, budget) == 0:
        raise PolyError(PolyErrorKind.DOMAIN, "zero has no algebraic inverse")
    var exact = left.rational and (op >= 3 or right.rational)
    var zero_product = op == 2 and ((left.rational and left.low.is_zero()) or (right.rational and right.low.is_zero()))
    if exact or zero_product:
        var expected = QQ.zero(NoContext())
        if exact:
            expected = _rational_operation(left.low, right.low, op, budget)
        return AlgebraicArithmeticCertificate(op, left^, right^, left_factor^, right_factor^, _rational(expected, budget), DensePoly[QQ](0, NoContext()), DensePoly[QQ](0, NoContext()), None, None)
    var elimination = Optional[ResultantResult[QQ]]()
    var h: DensePoly[QQ]
    if op < 3:
        var definitions = _binary_definitions(left, right, op, budget)
        var identity = resultant(definitions[0], definitions[1], 1, budget)
        h = DensePoly[QQ].from_sparse(identity.resultant, budget, variable=Int64(0))
        elimination = identity^
    else:
        h = _unary_definition(left, op, budget)
    if h.is_zero():
        raise PolyError(PolyErrorKind.DOMAIN, "algebraic annihilator unexpectedly vanished")
    var sequence_index = _sturm_index(h, cache.sequences, budget)
    while True:
        budget.charge(1)
        if op == 4 and left.low.value.sign() * left.high.value.sign() <= 0:
            _refine(left, budget)
            continue
        var bounds = _operation_bounds(left, right, op, budget)
        if not _sign_at(h, bounds[0], budget) == 0 and not _sign_at(h, bounds[1], budget) == 0:
            if _variations(cache.sequences[sequence_index].polynomials, bounds[0], budget) - _variations(cache.sequences[sequence_index].polynomials, bounds[1], budget) == 1:
                var value = _root_cached(h, bounds[0], bounds[1], cache, budget)
                var value_factor = _exact(h, value.polynomial, budget)
                var selection = RootCountCertificate(_copy_sequence(cache.sequences[sequence_index], budget), _copy_q(bounds[0], budget), _copy_q(bounds[1], budget), 1)
                return AlgebraicArithmeticCertificate(op, left^, right^, left_factor^, right_factor^, value^, h^, value_factor^, elimination^, selection^)
        _refine(left, budget)
        if op < 3:
            _refine(right, budget)
