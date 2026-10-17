"""Exact, pseudo, and ordered multivariate polynomial division.

The loops implement Algorithms V-1/V-4 and the scaling proof of V-2.
"""
from .coefficient_buffer import _view
from .errors import Budget, PolyError, PolyErrorKind, _allocation, _charge_size
from .coefficients import CoefficientRing, CoefficientField, _pow
from ._coefficient_ops import _quotient, _exact
from .dense import DensePoly, _slice, _trim
from .sparse import SparsePoly, Term
from .monomial import Monomial, MonomialOrder
from .certificates import DivisionResult, ListDivision
from ._packed_division import _packed_divide as _heap_divide
from ._sparse_ops import _subtract_multiple, _from_descending
from ._reduction_stream import _ReductionStream
from ._packed_products import _packed_divide
from ._ntt import _ntt_divide_exact
from .coefficients import ZZ, ModInt


def _dense_divide[C: CoefficientRing](f: DensePoly[C], g: DensePoly[C], pseudo: Bool, mut budget: Budget, quotient: Bool = True) raises PolyError -> DivisionResult[C]:
    f._same(g)
    if g.is_zero():
        raise PolyError(PolyErrorKind.DOMAIN, "division by zero polynomial")
    var count = max(0, f.degree() - g.degree() + 1)
    var quotient_count = count if quotient else 0
    _allocation[C](quotient_count, budget)
    var q = List[C](length=quotient_count, fill=C.zero(f.ring))
    var r = _slice(_view(f.coefficients), 0, len(f.coefficients), budget)
    var remaining = count
    var inverse = C.one(f.ring)
    ref lc = g.coefficients[len(g.coefficients) - 1]
    if not pseudo and count:
        inverse = _exact(inverse, lc, budget)
    while len(r) >= len(g.coefficients):
        budget.charge(1)
        var shift = len(r) - len(g.coefficients)
        _charge_size(r[len(r) - 1].size(), budget)
        var factor = r[len(r) - 1].copy()
        if pseudo:
            for i in range(len(q)):
                budget.charge(1)
                q[i] = q[i].mul(lc, budget)
            for i in range(len(r)):
                budget.charge(1)
                r[i] = r[i].mul(lc, budget)
        else:
            factor = factor.mul(inverse, budget)
        if quotient:
            q[shift] = q[shift].add(factor, budget)
        for i in range(len(g.coefficients)):
            budget.charge(1)
            r[shift + i] = r[shift + i].sub(factor.mul(g.coefficients[i], budget), budget)
        _trim(r, budget)
        remaining -= 1
    if pseudo and remaining:
        var multiplier = _pow(lc, UInt64(remaining), budget)
        for i in range(len(q)):
            budget.charge(1)
            q[i] = q[i].mul(multiplier, budget)
        for i in range(len(r)):
            budget.charge(1)
            r[i] = r[i].mul(multiplier, budget)
    _trim(q, budget)
    return DivisionResult[C](DensePoly[C]._from_canonical(f.variable, f.ring, q^), DensePoly[C]._from_canonical(f.variable, f.ring, r^))


def divmod[C: CoefficientField](f: DensePoly[C], g: DensePoly[C], mut budget: Budget) raises PolyError -> DivisionResult[C]:
    """Divide univariate polynomials over a field.

    Parameters:
        C: The coefficient field.

    Args:
        f: The dividend.
        g: The nonzero divisor in the same variable and ring.
        budget: The shared work allowance.

    Returns:
        The unique quotient and remainder of degree less than the divisor.

    Raises:
        PolyError: DOMAIN for invalid operands, LIMIT or CAPACITY on work limits.
    """
    return _dense_divide(f, g, False, budget)


def pseudo_divmod[C: CoefficientRing](f: DensePoly[C], g: DensePoly[C], mut budget: Budget) raises PolyError -> DivisionResult[C]:
    """Divide after multiplying the dividend by the standard leading-coefficient power.

    Parameters:
        C: The coefficient integral domain.

    Args:
        f: The dividend.
        g: The nonzero divisor in the same variable and ring.
        budget: The shared work allowance.

    Returns:
        Quotient and remainder for lc(g)**max(deg(f)-deg(g)+1, 0) times f.

    Raises:
        PolyError: DOMAIN for invalid operands, LIMIT or CAPACITY on work limits.
    """
    return _dense_divide(f, g, True, budget)


def _division_order[C: CoefficientRing](p: SparsePoly[C], others: List[SparsePoly[C]], mut budget: Budget) raises PolyError -> MonomialOrder:
    if p.order.kind != MonomialOrder.KERNEL:
        _charge_size(len(p.order.variables), budget)
        return p.order.copy()
    # KERNEL is a storage order, not a well-order. Use a deterministic lex
    # work order and restore storage order on return.
    var variables = p.variables(budget)
    for other in others:
        budget.charge(1)
        var additions = other.variables(budget)
        for index in additions:
            budget.charge(1)
            var found = False
            for existing in variables:
                budget.charge(1)
                if existing == index:
                    found = True
                    break
            if not found:
                variables.append(index)
    return MonomialOrder(MonomialOrder.LEX, variables^, budget)


def divide_exact[C: CoefficientRing](f: SparsePoly[C], g: SparsePoly[C], mut budget: Budget) raises PolyError -> Optional[SparsePoly[C]]:
    """Return an exact quotient over the coefficient ring, or no value.

    Parameters:
        C: ZZ or a coefficient field.

    Args:
        f: The dividend.
        g: The nonzero divisor in the same ring and order.
        budget: The shared work allowance.

    Returns:
        The quotient if g divides f, otherwise None.

    Raises:
        PolyError: DOMAIN for invalid operands, UNSUPPORTED for another ring, LIMIT or CAPACITY on work limits.
    """
    f._same(g, budget)
    if g.is_zero():
        raise PolyError(PolyErrorKind.DOMAIN, "division by zero polynomial")
    comptime if C == ZZ or C == ModInt:
        if not f.is_zero() and len(g.terms) > 1:
            var fast = _fast_divide_exact(f, g, budget)
            if fast:
                return fast.take()
    var applicable = False
    var packed = _heap_divide(f, g, applicable, budget)
    if applicable:
        return packed^
    var others: List[SparsePoly[C]] = [g._copy(budget)]
    var order = _division_order(f, others, budget)
    var pending = f.reorder(order, budget)
    var divisor = g.reorder(order, budget)
    var terms = List[Term[C]]()
    var leading = divisor.leading(budget)
    while not pending.is_zero():
        budget.charge(1)
        var last = pending.leading(budget)
        if not leading.monomial.divides(last.monomial, budget):
            return None
        var coefficient = _quotient(last.coefficient, leading.coefficient, budget)
        if not coefficient:
            return None
        var term = Term[C](last.monomial.div(leading.monomial, budget), coefficient.take())
        pending = _subtract_multiple(pending, divisor, term, budget)
        _allocation[Term[C]](1, budget)
        terms.append(term^)
    return _from_descending(terms^, divisor, budget).reorder(f.order, budget)


def _univariate[C: CoefficientRing](p: SparsePoly[C]) -> Optional[Int64]:
    """The single variable of a nonconstant univariate polynomial."""
    var variable = Optional[Int64](None)
    for term in p.terms:
        if len(term.monomial.pairs) > 1:
            return None
        if len(term.monomial.pairs):
            var v = term.monomial.pairs[0][0]
            if variable and variable.value() != v:
                return None
            variable = v
    return variable


def _fast_divide_exact[C: CoefficientRing](f: SparsePoly[C], g: SparsePoly[C], mut budget: Budget) raises PolyError -> Optional[Optional[SparsePoly[C]]]:
    """Exact ZZ or GF(p) division by dense transforms (one variable) or packed chunks (LEX), or None when neither applies."""
    var x = _univariate(f)
    var y = _univariate(g)
    if x and y and x.value() == y.value():
        var a = DensePoly[C].from_sparse(f, budget)
        var b = DensePoly[C].from_sparse(g, budget)
        if len(b.coefficients) >= 32 and len(a.coefficients) >= len(b.coefficients):
            var q = _ntt_divide_exact(_view(a.coefficients), _view(b.coefficients), budget)
            if q:
                var quotient = q.take()
                if not quotient:
                    return Optional(Optional[SparsePoly[C]](None))
                var dense = DensePoly[C]._from_canonical(a.variable, a.ring, quotient.take())
                return Optional(Optional(dense.to_sparse(f.order, budget)))
    if f.order.kind == MonomialOrder.LEX and len(f.terms) >= 256:
        return _packed_divide(f, g, budget)
    return None


def divide_by_list[C: CoefficientField](f: SparsePoly[C], divisors: List[SparsePoly[C]], mut budget: Budget) raises PolyError -> ListDivision[C]:
    """Reduce by nonzero divisors in the supplied order under a monomial order.

    Parameters:
        C: The coefficient field.

    Args:
        f: The dividend in LEX, GRLEX, or GREVLEX order.
        divisors: Nonzero divisors in the same ring and order.
        budget: The shared work allowance.

    Returns:
        Quotients and a remainder with no term divisible by a divisor's leading monomial.

    Raises:
        PolyError: DOMAIN for zero divisors, mixed rings/orders, or KERNEL order; LIMIT or CAPACITY on work limits.
    """
    _allocation[Int](len(divisors), budget)
    var indices = List[Int](capacity=len(divisors))
    for i in range(len(divisors)):
        budget.charge(1)
        indices.append(i)
    return _divide_by_indices(f, divisors, indices, True, budget)


struct _ReducerData[C: CoefficientField](Movable):
    var leads: List[Monomial]
    var inverses: List[Self.C]

    def __init__(out self):
        self.leads = List[Monomial]()
        self.inverses = List[Self.C]()

    def append(mut self, g: SparsePoly[Self.C], mut budget: Budget) raises PolyError:
        var leading = g.leading(budget)
        var inverse = leading.coefficient.inverse(budget)
        _allocation[Monomial](1, budget)
        _allocation[Self.C](1, budget)
        var monomial = Monomial()
        swap(monomial, leading.monomial)
        self.leads.append(monomial^)
        self.inverses.append(inverse^)


def _divide_by_indices[C: CoefficientField](f: SparsePoly[C], divisors: List[SparsePoly[C]], indices: List[Int], carry: Bool, mut budget: Budget) raises PolyError -> ListDivision[C]:
    if f.order.kind == MonomialOrder.KERNEL:
        raise PolyError(PolyErrorKind.DOMAIN, "list division requires a monomial order")
    var data = _ReducerData[C]()
    for g in divisors:
        budget.charge(1)
        f._same(g, budget)
        data.append(g, budget)
    return _divide_prepared(f, divisors, indices, carry, data, budget)


def _divide_prepared[C: CoefficientField](f: SparsePoly[C], divisors: List[SparsePoly[C]], indices: List[Int], carry: Bool, data: _ReducerData[C], mut budget: Budget) raises PolyError -> ListDivision[C]:
    # The public wrapper validates ring/order compatibility. The basis producer
    # keeps one metadata entry per immutable arena polynomial and reuses it.
    _allocation[List[Term[C]]](len(indices) if carry else 0, budget)
    var quotient_terms = List[List[Term[C]]]()
    if carry:
        for _ in indices:
            budget.charge(1)
            quotient_terms.append(List[Term[C]]())
    var remainder = List[Term[C]]()
    var pending = f._copy(budget)
    var steps = 0
    while not pending.is_zero():
        if steps == 2 and len(pending.terms) >= 64:
            break
        budget.charge(1)
        var last = pending.leading(budget)
        var reduced = False
        for i in range(len(indices)):
            budget.charge(1)
            if not data.leads[indices[i]].divides(last.monomial, budget):
                continue
            var t = Term[C](last.monomial.div(data.leads[indices[i]], budget), last.coefficient.mul(data.inverses[indices[i]], budget))
            pending = _subtract_multiple(pending, divisors[indices[i]], t, budget)
            if carry:
                _allocation[Term[C]](1, budget)
                quotient_terms[i].append(t^)
            steps = min(2, steps + 1)
            reduced = True
            break
        if not reduced:
            _ = pending.terms.pop()
            _allocation[Term[C]](1, budget)
            remainder.append(last^)
    if not pending.is_zero():
        var stream = _ReductionStream[C](pending^, budget)
        while True:
            var next = stream.next(divisors, budget)
            if not next:
                break
            var last = next.take()
            var reduced = False
            for i in range(len(indices)):
                budget.charge(1)
                if not data.leads[indices[i]].divides(last.monomial, budget):
                    continue
                var t = Term[C](last.monomial.div(data.leads[indices[i]], budget), last.coefficient.mul(data.inverses[indices[i]], budget))
                stream.append(indices[i], t, divisors, budget)
                if carry:
                    _allocation[Term[C]](1, budget)
                    quotient_terms[i].append(t^)
                reduced = True
                break
            if not reduced:
                _allocation[Term[C]](1, budget)
                remainder.append(last^)
    _allocation[SparsePoly[C]](len(quotient_terms), budget)
    var quotients = List[SparsePoly[C]](capacity=len(quotient_terms))
    for i in range(len(quotient_terms)):
        budget.charge(1)
        var terms = List[Term[C]]()
        swap(terms, quotient_terms[i])
        quotients.append(_from_descending(terms^, f, budget))
    return ListDivision[C](quotients^, _from_descending(remainder^, f, budget))
