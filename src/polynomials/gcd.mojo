"""Contents, normalized gcds, and explicit coprimality proofs."""
from apn_mojo import Integer, div_rem_trunc
from .errors import Budget, PolyError, PolyErrorKind, _allocation, _charge_size, _sum
from .coefficients import CoefficientRing, CoefficientField, ZZ, _work
from ._coefficient_ops import _exact, _integer_bezout
from ._modular_coprimality import _try_modular
from .sparse import SparsePoly
from .dense import DensePoly
from .monomial import MonomialOrder
from .certificates import GcdResult, ContentGcdStep, CoprimalityNode, CoprimalityCertificate
from ._gcd import _content, _gcd_value
from ._tower import _one, _zero, _constant, _split, _variables, _exact_poly
from .resultant import resultant
from ._euclidean import _extended
from ._views import _is_unit


def content[C: CoefficientRing](p: SparsePoly[C], main_variable: Int64, mut budget: Budget) raises PolyError -> SparsePoly[C]:
    """Compute the normalized gcd of the coefficients in one variable.

    Parameters:
        C: ZZ or a coefficient field.

    Args:
        p: The polynomial.
        main_variable: The variable separated from its coefficient ring.
        budget: The shared work allowance.

    Returns:
        The content in the remaining variables, or zero for zero input.

    Raises:
        PolyError: LIMIT or CAPACITY on work limits, UNSUPPORTED for another ring.
    """
    return _content(p, main_variable, budget)


def primitive_part[C: CoefficientRing](p: SparsePoly[C], main_variable: Int64, mut budget: Budget) raises PolyError -> SparsePoly[C]:
    """Divide by the content in the chosen variable.

    Parameters:
        C: ZZ or a coefficient field.

    Args:
        p: The polynomial.
        main_variable: The variable separated from its coefficient ring.
        budget: The shared work allowance.

    Returns:
        The primitive part, or zero for zero input.

    Raises:
        PolyError: LIMIT or CAPACITY on work limits, UNSUPPORTED for another ring.
    """
    if p.is_zero():
        return p._copy(budget)
    return _exact_poly(p, _content(p, main_variable, budget), budget)


def extended_gcd[C: CoefficientField](f: DensePoly[C], h: DensePoly[C], mut budget: Budget) raises PolyError -> GcdResult[C]:
    """Compute a monic univariate gcd with Bézout multipliers.

    Parameters:
        C: The coefficient field.

    Args:
        f: The first polynomial.
        h: The second polynomial in the same variable and ring.
        budget: The shared work allowance.

    Returns:
        A gcd, its cofactors, and G-C2 evidence in KERNEL storage order.

    Raises:
        PolyError: DOMAIN for incompatible inputs, LIMIT or CAPACITY on work limits.
    """
    var triple = _extended(f, h, budget)
    var order = MonomialOrder()
    var d = triple[0].to_sparse(order, budget)
    var a = _zero(d, budget)
    var b = _zero(d, budget)
    if not d.is_zero():
        a = _exact_poly(f.to_sparse(order, budget), d, budget)
        b = _exact_poly(h.to_sparse(order, budget), d, budget)
    return GcdResult[C](d^, (a^, b^), (triple[1].to_sparse(order, budget), triple[2].to_sparse(order, budget)), None)



def _append[C: CoefficientRing](mut nodes: List[CoprimalityNode[C]], var node: CoprimalityNode[C], mut budget: Budget) raises PolyError -> Int:
    var index = len(nodes)
    _ = _sum(index, 1)
    _allocation[CoprimalityNode[C]](1, budget)
    nodes.append(node^)
    return index


def _leaf[C: CoefficientRing](mut nodes: List[CoprimalityNode[C]], var u: SparsePoly[C], var v: SparsePoly[C], var s: SparsePoly[C], mut budget: Budget) raises PolyError -> Int:
    return _append(nodes, CoprimalityNode[C](0, u^, v^, s^, List[ContentGcdStep[C]](), List[ContentGcdStep[C]](), None), budget)


def _content_proof[C: CoefficientRing](p: SparsePoly[C], variable: Int64, mut nodes: List[CoprimalityNode[C]], mut budget: Budget) raises PolyError -> Tuple[SparsePoly[C], List[ContentGcdStep[C]]]:
    var values = _split(p, variable, budget)
    _allocation[ContentGcdStep[C]](len(values), budget)
    var steps = List[ContentGcdStep[C]](capacity=len(values))
    var accumulator = _zero(p, budget)
    for value in values:
        budget.charge(1)
        var common = _gcd_value(accumulator, value, budget)
        var a = _zero(p, budget)
        var b = _zero(p, budget)
        var proof: Optional[Int] = None
        if not common.is_zero():
            a = _exact_poly(accumulator, common, budget)
            b = _exact_poly(value, common, budget)
            proof = _prove(a, b, nodes, budget)
            if not proof:
                raise PolyError(PolyErrorKind.DOMAIN, "content cofactors unexpectedly share a factor")
        accumulator = common._copy(budget)
        steps.append(ContentGcdStep[C](common^, (a^, b^), proof))
    return (accumulator^, steps^)


def _prove[C: CoefficientRing](f: SparsePoly[C], h: SparsePoly[C], mut nodes: List[CoprimalityNode[C]], mut budget: Budget) raises PolyError -> Optional[Int]:
    f._same(h, budget)
    if _is_unit(f, budget):
        var u = _constant(f, _exact(C.one(f.ring), f.terms[0].coefficient, budget), budget)
        return _leaf(nodes, u^, _zero(f, budget), _one(f, budget), budget)
    if _is_unit(h, budget):
        var v = _constant(h, _exact(C.one(h.ring), h.terms[0].coefficient, budget), budget)
        return _leaf(nodes, _zero(h, budget), v^, _one(h, budget), budget)
    if f.is_zero() or h.is_zero():
        return None
    var variables = _variables(f, h, budget)
    if not len(variables):
        comptime if C == ZZ:
            var triple = _integer_bezout(rebind[ZZ](f.terms[0].coefficient), rebind[ZZ](h.terms[0].coefficient), budget)
            var s = _constant(f, rebind[C](triple[0]), budget)
            if not _is_unit(s, budget):
                return None
            return _leaf(nodes, _constant(f, rebind[C](triple[1]), budget), _constant(h, rebind[C](triple[2]), budget), s^, budget)
        else:
            return None
    comptime if conforms_to(C, CoefficientField):
        if len(variables) == 1:
            var triple = _extended(DensePoly[C].from_sparse(f, budget, variable=variables[0]), DensePoly[C].from_sparse(h, budget, variable=variables[0]), budget)
            var s = triple[0].to_sparse(f.order, budget)
            if not _is_unit(s, budget):
                return None
            return _leaf(nodes, triple[1].to_sparse(f.order, budget), triple[2].to_sparse(f.order, budget), s^, budget)
    var variable = variables[0]
    var elimination = resultant(f, h, variable, budget)
    if elimination.resultant.is_zero():
        return None
    if _is_unit(elimination.resultant, budget):
        return _leaf(nodes, elimination.cofactors[0]._copy(budget), elimination.cofactors[1]._copy(budget), elimination.resultant._copy(budget), budget)
    var left = _content_proof(f, variable, nodes, budget)
    var right = _content_proof(h, variable, nodes, budget)
    var contents = _prove(left[0], right[0], nodes, budget)
    if not contents:
        return None
    var left_steps = List[ContentGcdStep[C]]()
    var right_steps = List[ContentGcdStep[C]]()
    swap(left_steps, left[1])
    swap(right_steps, right[1])
    return _append(nodes, CoprimalityNode[C](variable, elimination.cofactors[0]._copy(budget), elimination.cofactors[1]._copy(budget), elimination.resultant._copy(budget), left_steps^, right_steps^, contents), budget)


def coprimality_certificate[C: CoefficientRing](f: SparsePoly[C], h: SparsePoly[C], mut budget: Budget) raises PolyError -> Optional[CoprimalityCertificate[C]]:
    """Prove coprimality by unit identities or elimination with content witnesses.

    Parameters:
        C: ZZ or a coefficient field.

    Args:
        f: The first polynomial.
        h: The second polynomial in the same ring and order.
        budget: The shared work allowance.

    Returns:
        A modular projection witness or a deterministic G-C3 proof arena,
        or None when the inputs share a nonunit factor.

    Raises:
        PolyError: DOMAIN for incompatible inputs, LIMIT or CAPACITY on work limits.
    """
    f._same(h, budget)
    var modular = _try_modular(f, h, budget)
    if modular:
        return CoprimalityCertificate[C](List[CoprimalityNode[C]](), -1, modular^)
    var nodes = List[CoprimalityNode[C]]()
    var root = _prove(f, h, nodes, budget)
    if not root:
        return None
    return CoprimalityCertificate[C](nodes^, root.value())


def gcd_value[C: CoefficientRing](f: SparsePoly[C], h: SparsePoly[C], mut budget: Budget) raises PolyError -> SparsePoly[C]:
    """Compute the normalized gcd alone, without cofactors or evidence.

    Parameters:
        C: ZZ or a coefficient field.

    Args:
        f: The first polynomial.
        h: The second polynomial in the same ring and order.
        budget: The shared work allowance.

    Returns:
        The positive-leading ZZ or monic field gcd, equal to `gcd(f, h).gcd`.

    Raises:
        PolyError: DOMAIN for incompatible inputs, LIMIT or CAPACITY on work limits.
    """
    return _gcd_value(f, h, budget)


def gcd[C: CoefficientRing](f: SparsePoly[C], h: SparsePoly[C], mut budget: Budget, certify_maximal: Bool = False) raises PolyError -> GcdResult[C]:
    """Compute a normalized gcd, its cofactors, and optionally maximality evidence.

    Parameters:
        C: ZZ or a coefficient field.

    Args:
        f: The first polynomial.
        h: The second polynomial in the same ring and order.
        budget: The shared work allowance.
        certify_maximal: Whether to produce a Bézout or coprimality proof.

    Returns:
        The positive-leading ZZ or monic field gcd and its certificates.

    Raises:
        PolyError: DOMAIN for incompatible inputs, LIMIT or CAPACITY on work limits.
    """
    var common = _gcd_value(f, h, budget)
    var a = _zero(f, budget)
    var b = _zero(f, budget)
    if not common.is_zero():
        a = _exact_poly(f, common, budget)
        b = _exact_poly(h, common, budget)
    var proof: Optional[CoprimalityCertificate[C]] = None
    var bezout: Optional[Tuple[SparsePoly[C], SparsePoly[C]]] = None
    if certify_maximal:
        comptime if conforms_to(C, CoefficientField):
            var variables = _variables(f, h, budget)
            if len(variables) <= 1:
                var variable = variables[0] if len(variables) else Int64(0)
                var triple = _extended(DensePoly[C].from_sparse(f, budget, variable=variable), DensePoly[C].from_sparse(h, budget, variable=variable), budget)
                bezout = (triple[1].to_sparse(f.order, budget), triple[2].to_sparse(f.order, budget))
        if not bezout and not common.is_zero():
            proof = coprimality_certificate(a, b, budget)
            if not proof:
                raise PolyError(PolyErrorKind.DOMAIN, "gcd cofactors unexpectedly share a factor")
    return GcdResult[C](common^, (a^, b^), bezout^, proof^)
