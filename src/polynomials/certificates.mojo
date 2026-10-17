"""Arithmetic certificates and independent checks of their stated identities."""
from ._coefficient_ops import _copy as _copy_coefficient
from apn_mojo import Integer, Rational, gcd, lcm
from .errors import Budget, PolyError, PolyErrorKind, _charge_size, _sum
from .coefficients import CoefficientRing
from .dense import DensePoly
from .sparse import SparsePoly
from .monomial import MonomialOrder
from ._product_check import _matches_products


@fieldwise_init
struct MembershipCertificate[C: CoefficientRing](Copyable, Movable, Writable):
    """Polynomial multipliers proving membership in the supplied ideal (B-C1).

    Parameters:
        C: The coefficient ring.
    """
    var cofactors: List[SparsePoly[Self.C]]
    """Multipliers in the original generator order."""


def check_membership[C: CoefficientRing](f: SparsePoly[C], generators: List[SparsePoly[C]], certificate: MembershipCertificate[C], mut budget: Budget) raises PolyError -> Bool:
    """Check an ideal-membership identity without constructing a Gröbner basis.

    Parameters:
        C: The coefficient ring.

    Args:
        f: The claimed member of the ideal.
        generators: The original generators in certificate order.
        certificate: One multiplier per generator.
        budget: The shared work allowance.

    Returns:
        Whether f equals the sum of multiplier times generator.

    Raises:
        PolyError: DOMAIN for malformed input or mixed rings, LIMIT or CAPACITY on work limits.
    """
    if len(generators) != len(certificate.cofactors):
        return False
    f.check_invariants(budget)
    var stream = f.order.kind != MonomialOrder.KERNEL
    var terms = 0
    for i in range(len(generators)):
        budget.charge(1)
        terms = _sum(terms, _sum(len(generators[i].terms), len(certificate.cofactors[i].terms)))
        _charge_size(_sum(len(f.order.variables), _sum(len(generators[i].order.variables), len(certificate.cofactors[i].order.variables))), budget)
        stream = stream and generators[i].order == f.order and certificate.cofactors[i].order == f.order
    if stream and terms >= 64:
        for i in range(len(generators)):
            generators[i].check_invariants(budget)
            certificate.cofactors[i].check_invariants(budget)
            f._same(generators[i], budget)
            f._same(certificate.cofactors[i], budget)
        return _matches_products(f, generators, certificate.cofactors, SparsePoly[C].zero(f.order, f.ring, budget), budget)
    var total = SparsePoly[C].zero(f.order, f.ring, budget)
    for i in range(len(generators)):
        budget.charge(1)
        generators[i].check_invariants(budget)
        certificate.cofactors[i].check_invariants(budget)
        total = total.add(generators[i].reorder(f.order, budget).mul(certificate.cofactors[i].reorder(f.order, budget), budget), budget)
    return _equal(f, total, budget)


@fieldwise_init
struct SquarefreeDecomposition[C: CoefficientRing](Copyable, Movable, Writable):
    """A scalar and monic squarefree blocks grouped by multiplicity.

    Parameters:
        C: The coefficient ring.
    """
    var unit: Self.C
    """The leading coefficient, or zero for the zero polynomial."""
    var factors: List[Tuple[DensePoly[Self.C], Int]]
    """Nonconstant blocks and positive multiplicities, ordered by multiplicity."""


@fieldwise_init
struct Factorization[C: CoefficientRing](Copyable, Movable, Writable):
    """A scalar and normalized irreducible factors with multiplicities.

    Parameters:
        C: The coefficient ring.
    """
    var unit: Self.C
    """The scalar multiplier, including the sign over the integers."""
    var factors: List[Tuple[DensePoly[Self.C], Int]]
    """Factors ordered by degree and then descending coefficient vectors."""


def _check_product[C: CoefficientRing](f: DensePoly[C], unit: C, factors: List[Tuple[DensePoly[C], Int]], mut budget: Budget) raises PolyError -> Bool:
    f.check_invariants(budget)
    var product = DensePoly[C].from_coefficients(f.variable, f.ring, [_copy_coefficient(unit, budget)], budget)
    for entry in factors:
        budget.charge(1)
        entry[0].check_invariants(budget)
        if entry[1] <= 0:
            return False
        product = product.mul(entry[0].pow(UInt64(entry[1]), budget), budget)
    return _dense_equal(f, product, budget)


def check_squarefree_product[C: CoefficientRing](f: DensePoly[C], decomposition: SquarefreeDecomposition[C], mut budget: Budget) raises PolyError -> Bool:
    """Check the squarefree product equation without claiming coprimality (Z-C1).

    Parameters:
        C: The coefficient ring.

    Args:
        f: The original polynomial.
        decomposition: The scalar and proposed multiplicity blocks.
        budget: The shared work allowance.

    Returns:
        Whether the proposed product equals f.

    Raises:
        PolyError: DOMAIN for incompatible representations, LIMIT or CAPACITY on work limits.
    """
    return _check_product(f, decomposition.unit, decomposition.factors, budget)


def check_factorization[C: CoefficientRing](f: DensePoly[C], factorization: Factorization[C], mut budget: Budget) raises PolyError -> Bool:
    """Check the factor product equation without claiming irreducibility (Z-C2).

    Parameters:
        C: The coefficient ring.

    Args:
        f: The original polynomial.
        factorization: The scalar and proposed factors with multiplicities.
        budget: The shared work allowance.

    Returns:
        Whether the proposed product equals f.

    Raises:
        PolyError: DOMAIN for incompatible representations, LIMIT or CAPACITY on work limits.
    """
    return _check_product(f, factorization.unit, factorization.factors, budget)


@fieldwise_init
struct DivisionResult[C: CoefficientRing](Copyable, Movable, Writable):
    """A dense quotient and remainder.

    Parameters:
        C: The coefficient ring.
    """
    var quotient: DensePoly[Self.C]
    """The quotient polynomial."""
    var remainder: DensePoly[Self.C]
    """The remainder polynomial."""


@fieldwise_init
struct ListDivision[C: CoefficientRing](Copyable, Movable, Writable):
    """Quotients in divisor order and the unreduced remainder.

    Parameters:
        C: The coefficient ring.
    """
    var quotients: List[SparsePoly[Self.C]]
    """One quotient for each supplied divisor."""
    var remainder: SparsePoly[Self.C]
    """The remainder after the ordered reductions."""


def _equal[C: CoefficientRing](a: SparsePoly[C], b: SparsePoly[C], mut budget: Budget) raises PolyError -> Bool:
    _charge_size(_sum(len(a.order.variables), len(b.order.variables)), budget)
    if a.order != b.order or a.ring != b.ring or len(a.terms) != len(b.terms):
        return False
    for i in range(len(a.terms)):
        budget.charge(1)
        _charge_size(_sum(len(a.terms[i].monomial.pairs), len(b.terms[i].monomial.pairs)), budget)
        _charge_size(_sum(a.terms[i].coefficient.size(), b.terms[i].coefficient.size()), budget)
        if a.terms[i] != b.terms[i]:
            return False
    return True


def _dense_equal[C: CoefficientRing](a: DensePoly[C], b: DensePoly[C], mut budget: Budget) raises PolyError -> Bool:
    if a.variable != b.variable or a.ring != b.ring or len(a.coefficients) != len(b.coefficients):
        return False
    for i in range(len(a.coefficients)):
        budget.charge(1)
        _charge_size(_sum(a.coefficients[i].size(), b.coefficients[i].size()), budget)
        if a.coefficients[i] != b.coefficients[i]:
            return False
    return True


def check_division[C: CoefficientRing](f: DensePoly[C], g: DensePoly[C], result: DivisionResult[C], mut budget: Budget) raises PolyError -> Bool:
    """Check the ordinary division identity and strict remainder degree bound.

    Parameters:
        C: The coefficient ring.

    Args:
        f: The dividend.
        g: The divisor.
        result: The proposed quotient and remainder.
        budget: The shared work allowance.

    Returns:
        Whether the data prove V-C1; pseudo-division requires a scaled dividend.

    Raises:
        PolyError: DOMAIN for incompatible representations, LIMIT or CAPACITY on work limits.
    """
    f.check_invariants(budget)
    g.check_invariants(budget)
    result.quotient.check_invariants(budget)
    result.remainder.check_invariants(budget)
    if g.is_zero() or result.remainder.degree() >= g.degree():
        return False
    var recomposed = result.quotient.mul(g, budget).add(result.remainder, budget)
    return _dense_equal(f, recomposed, budget)


def check_list_division[C: CoefficientRing](f: SparsePoly[C], divisors: List[SparsePoly[C]], result: ListDivision[C], mut budget: Budget) raises PolyError -> Bool:
    """Check the ideal-membership identity of division by a list.

    Parameters:
        C: The coefficient ring.

    Args:
        f: The dividend.
        divisors: The ordered divisor list.
        result: The proposed quotients and remainder.
        budget: The shared work allowance.

    Returns:
        Whether the data prove V-C2, without claiming a unique remainder.

    Raises:
        PolyError: DOMAIN for incompatible representations, LIMIT or CAPACITY on work limits.
    """
    if len(divisors) != len(result.quotients):
        return False
    f.check_invariants(budget)
    result.remainder.check_invariants(budget)
    _charge_size(_sum(len(f.order.variables), len(result.remainder.order.variables)), budget)
    var stream = f.order.kind != MonomialOrder.KERNEL and result.remainder.order == f.order and result.remainder.ring == f.ring
    var terms = 0
    for i in range(len(divisors)):
        budget.charge(1)
        terms = _sum(terms, _sum(len(divisors[i].terms), len(result.quotients[i].terms)))
        _charge_size(_sum(len(f.order.variables), _sum(len(divisors[i].order.variables), len(result.quotients[i].order.variables))), budget)
        stream = stream and divisors[i].order == f.order and result.quotients[i].order == f.order
    if stream and terms >= 128:
        f._same(result.remainder, budget)
        for i in range(len(divisors)):
            divisors[i].check_invariants(budget)
            result.quotients[i].check_invariants(budget)
            f._same(divisors[i], budget)
            f._same(result.quotients[i], budget)
        return _matches_products(f, divisors, result.quotients, result.remainder, budget)
    var sum = result.remainder._copy(budget)
    for i in range(len(divisors)):
        budget.charge(1)
        divisors[i].check_invariants(budget)
        result.quotients[i].check_invariants(budget)
        sum = sum.add(result.quotients[i].mul(divisors[i], budget), budget)
    return _equal(f, sum, budget)


@fieldwise_init
struct ContentGcdStep[C: CoefficientRing](Copyable, Movable, Writable):
    """A gcd fold step proved by divisibility and cofactor coprimality.

    Parameters:
        C: The coefficient ring.
    """
    var gcd: SparsePoly[Self.C]
    """The gcd of the preceding accumulator and the next coefficient."""
    var cofactors: Tuple[SparsePoly[Self.C], SparsePoly[Self.C]]
    """The two quotient witnesses."""
    var coprimality_node: Optional[Int]
    """An earlier node proving the quotient pair coprime, absent only for two zeros."""


@fieldwise_init
struct CoprimalityNode[C: CoefficientRing](Copyable, Movable, Writable):
    """A unit identity or a content-and-resultant proof node.

    Parameters:
        C: The coefficient ring.
    """
    var variable: Int64
    """The eliminated variable for a nonterminal node."""
    var u: SparsePoly[Self.C]
    """The multiplier of the left input."""
    var v: SparsePoly[Self.C]
    """The multiplier of the right input."""
    var s: SparsePoly[Self.C]
    """The nonzero combination u*f+v*h, free of the eliminated variable."""
    var left_content_steps: List[ContentGcdStep[Self.C]]
    """The coefficient gcd fold for the left input, in increasing degree."""
    var right_content_steps: List[ContentGcdStep[Self.C]]
    """The coefficient gcd fold for the right input, in increasing degree."""
    var contents_node: Optional[Int]
    """An earlier node proving the two final contents coprime."""


@fieldwise_init
struct CoprimalityCertificate[C: CoefficientRing](Copyable, Movable, Writable):
    """A finite arena of coprimality nodes in dependency order.

    Parameters:
        C: The coefficient ring.
    """
    var nodes: List[CoprimalityNode[Self.C]]
    """Nodes whose references must point strictly backwards."""
    var root: Int
    """The node proving coprimality of the supplied input pair."""


@fieldwise_init
struct GcdResult[C: CoefficientRing](Copyable, Movable, Writable):
    """A normalized gcd and optional evidence of maximality.

    Parameters:
        C: The coefficient ring.
    """
    var gcd: SparsePoly[Self.C]
    """The normalized greatest common divisor."""
    var cofactors: Tuple[SparsePoly[Self.C], SparsePoly[Self.C]]
    """The quotients of the inputs by the gcd (G-C1)."""
    var bezout: Optional[Tuple[SparsePoly[Self.C], SparsePoly[Self.C]]]
    """Bézout multipliers when available (G-C2)."""
    var coprimality: Optional[CoprimalityCertificate[Self.C]]
    """A proof that the cofactors are coprime (G-C3), when requested."""


@fieldwise_init
struct ResultantResult[C: CoefficientRing](Copyable, Movable, Writable):
    """An elimination polynomial with its ideal-membership identity (E-C1).

    Parameters:
        C: The coefficient ring.
    """
    var resultant: SparsePoly[Self.C]
    """The resultant in the remaining variables."""
    var cofactors: Tuple[SparsePoly[Self.C], SparsePoly[Self.C]]
    """Multipliers u and v satisfying u*f+v*g=resultant."""


def _identity[C: CoefficientRing](f: SparsePoly[C], h: SparsePoly[C], u: SparsePoly[C], v: SparsePoly[C], s: SparsePoly[C], mut budget: Budget) raises PolyError -> Bool:
    f.check_invariants(budget)
    h.check_invariants(budget)
    u.check_invariants(budget)
    v.check_invariants(budget)
    s.check_invariants(budget)
    return _equal(u.mul(f, budget).add(v.mul(h, budget), budget), s, budget)


def check_common_divisor[C: CoefficientRing](f: SparsePoly[C], h: SparsePoly[C], result: GcdResult[C], mut budget: Budget) raises PolyError -> Bool:
    """Check both common-divisor identities without claiming maximality.

    Parameters:
        C: The coefficient ring.

    Args:
        f: The first input.
        h: The second input.
        result: The proposed gcd and cofactors.
        budget: The shared work allowance.

    Returns:
        Whether f=gcd*a and h=gcd*b (G-C1).

    Raises:
        PolyError: DOMAIN for invalid representations, LIMIT or CAPACITY on work limits.
    """
    f.check_invariants(budget)
    h.check_invariants(budget)
    result.gcd.check_invariants(budget)
    result.cofactors[0].check_invariants(budget)
    result.cofactors[1].check_invariants(budget)
    return _equal(f, result.gcd.mul(result.cofactors[0], budget), budget) and _equal(h, result.gcd.mul(result.cofactors[1], budget), budget)


def check_bezout[C: CoefficientRing](f: SparsePoly[C], h: SparsePoly[C], result: GcdResult[C], mut budget: Budget) raises PolyError -> Bool:
    """Check common divisibility and the Bézout identity (G-C2).

    Parameters:
        C: The coefficient ring.

    Args:
        f: The first input.
        h: The second input.
        result: The proposed gcd and Bézout multipliers.
        budget: The shared work allowance.

    Returns:
        Whether the available evidence proves both identities.

    Raises:
        PolyError: DOMAIN for invalid representations, LIMIT or CAPACITY on work limits.
    """
    if not result.bezout or not check_common_divisor(f, h, result, budget):
        return False
    ref uv = result.bezout.value()
    return _identity(f, h, uv[0], uv[1], result.gcd, budget)


def check_resultant_identity[C: CoefficientRing](f: SparsePoly[C], g: SparsePoly[C], result: ResultantResult[C], mut budget: Budget) raises PolyError -> Bool:
    """Check the ideal-membership identity supplied with a resultant (E-C1).

    Parameters:
        C: The coefficient ring.

    Args:
        f: The first input.
        g: The second input.
        result: The proposed elimination polynomial and multipliers.
        budget: The shared work allowance.

    Returns:
        Whether u*f+v*g equals the proposed elimination polynomial.

    Raises:
        PolyError: DOMAIN for invalid representations, LIMIT or CAPACITY on work limits.
    """
    return _identity(f, g, result.cofactors[0], result.cofactors[1], result.resultant, budget)


from ._views import _split, _zero, _is_unit
from .errors import _allocation


@fieldwise_init
struct _ProofTask[C: CoefficientRing](Movable):
    var left: SparsePoly[Self.C]
    var right: SparsePoly[Self.C]
    var node: Int


def _enqueue[C: CoefficientRing](f: SparsePoly[C], h: SparsePoly[C], index: Optional[Int], parent: Int, mut tasks: List[_ProofTask[C]], mut budget: Budget) raises PolyError -> Bool:
    if not index or index.value() < 0 or index.value() >= parent:
        return False
    _allocation[_ProofTask[C]](1, budget)
    _ = _sum(len(tasks), 1)
    tasks.append(_ProofTask[C](f._copy(budget), h._copy(budget), index.value()))
    return True


def _check_content[C: CoefficientRing](p: SparsePoly[C], variable: Int64, steps: List[ContentGcdStep[C]], parent: Int, mut tasks: List[_ProofTask[C]], mut budget: Budget) raises PolyError -> Optional[SparsePoly[C]]:
    var coefficients = _split(p, variable, budget)
    if len(coefficients) != len(steps):
        return None
    var accumulator = _zero(p, budget)
    for i in range(len(steps)):
        budget.charge(1)
        ref step = steps[i]
        step.gcd.check_invariants(budget)
        step.cofactors[0].check_invariants(budget)
        step.cofactors[1].check_invariants(budget)
        if step.gcd.degree_in(variable, budget) > 0 or step.cofactors[0].degree_in(variable, budget) > 0 or step.cofactors[1].degree_in(variable, budget) > 0:
            return None
        if not _equal(accumulator, step.gcd.mul(step.cofactors[0], budget), budget) or not _equal(coefficients[i], step.gcd.mul(step.cofactors[1], budget), budget):
            return None
        if step.gcd.is_zero():
            if Bool(step.coprimality_node) or not step.cofactors[0].is_zero() or not step.cofactors[1].is_zero():
                return None
        elif not _enqueue(step.cofactors[0], step.cofactors[1], step.coprimality_node, parent, tasks, budget):
            return None
        accumulator = step.gcd._copy(budget)
    return accumulator^


def check_coprimality[C: CoefficientRing](f: SparsePoly[C], h: SparsePoly[C], certificate: CoprimalityCertificate[C], mut budget: Budget) raises PolyError -> Bool:
    """Check content folds and elimination identities without rerunning gcd (G-C3).

    Parameters:
        C: ZZ or a coefficient field.

    Args:
        f: The first input.
        h: The second input.
        certificate: The proposed topologically ordered proof arena.
        budget: The shared work allowance.

    Returns:
        Whether the reachable proof establishes coprimality of these inputs.

    Raises:
        PolyError: DOMAIN for invalid representations, LIMIT or CAPACITY on work limits.
    """
    budget.charge(1)
    if certificate.root < 0 or certificate.root >= len(certificate.nodes):
        return False
    # The arena format requires every reference, including unreachable ones,
    # to point backwards. Algebraic checks below visit the root's proof only.
    for i in range(len(certificate.nodes)):
        budget.charge(1)
        ref node = certificate.nodes[i]
        if node.contents_node:
            if node.contents_node.value() < 0 or node.contents_node.value() >= i:
                return False
        for step in node.left_content_steps:
            budget.charge(1)
            if step.coprimality_node:
                if step.coprimality_node.value() < 0 or step.coprimality_node.value() >= i:
                    return False
        for step in node.right_content_steps:
            budget.charge(1)
            if step.coprimality_node:
                if step.coprimality_node.value() < 0 or step.coprimality_node.value() >= i:
                    return False
    f._same(h, budget)
    var tasks = List[_ProofTask[C]]()
    if not _enqueue(f, h, certificate.root, len(certificate.nodes), tasks, budget):
        return False
    while len(tasks):
        budget.charge(1)
        var task = tasks.pop()
        ref node = certificate.nodes[task.node]
        if node.s.is_zero() or not _identity(task.left, task.right, node.u, node.v, node.s, budget):
            return False
        if _is_unit(node.s, budget):
            if Bool(node.contents_node) or len(node.left_content_steps) != 0 or len(node.right_content_steps) != 0:
                return False
            continue
        if node.s.degree_in(node.variable, budget) > 0 or max(task.left.degree_in(node.variable, budget), task.right.degree_in(node.variable, budget)) <= 0:
            return False
        var left = _check_content(task.left, node.variable, node.left_content_steps, task.node, tasks, budget)
        var right = _check_content(task.right, node.variable, node.right_content_steps, task.node, tasks, budget)
        if not left or not right or not _enqueue(left.value(), right.value(), node.contents_node, task.node, tasks, budget):
            return False
    return True


from .coefficients import QQ
from .evaluate import _derivative_dense
from ._root_ops import _compare as _root_compare, _chain_variations, _one_sided, _sign_at, _sign


@fieldwise_init
struct SturmSequence(Copyable, Movable, Writable):
    """An unnormalized signed remainder sequence with exact quotient witnesses.

    The final nonzero polynomial is retained, including for repeated roots.
    """
    var polynomials: List[DensePoly[QQ]]
    """The input, its derivative, and successive negative remainders."""
    var quotients: List[DensePoly[QQ]]
    """Quotients proving each recurrence, including the final zero remainder."""


@fieldwise_init
struct RootCountCertificate(Copyable, Movable, Writable):
    """A Sturm sequence proving a distinct-root count on an open interval (T-C1)."""
    var sequence: SturmSequence
    """The sequence and all quotient witnesses."""
    var a: QQ
    """The lower endpoint, where the input does not vanish."""
    var b: QQ
    """The upper endpoint, where the input does not vanish."""
    var count: Int
    """The claimed number of distinct roots strictly between the endpoints."""


def check_root_count(f: DensePoly[QQ], certificate: RootCountCertificate, mut budget: Budget) raises PolyError -> Bool:
    """Check all Sturm identities and endpoint variations without polynomial division.

    Args:
        f: The polynomial whose distinct roots are counted.
        certificate: The sequence, quotient witnesses, endpoints, and count.
        budget: The shared work allowance.

    Returns:
        Whether the evidence establishes the count on the open interval.

    Raises:
        PolyError: DOMAIN for incompatible representations, LIMIT or CAPACITY on work limits.
    """
    return _check_root_count_parts(f, certificate.sequence, certificate.a, certificate.b, certificate.count, budget)


def _check_root_count_parts(f: DensePoly[QQ], sequence: SturmSequence, a: QQ, b: QQ, count: Int, mut budget: Budget) raises PolyError -> Bool:
    var chain = _IntegerChain()
    return _check_root_count_chain(f, sequence, a, b, count, chain, budget)


def _check_root_count_chain(f: DensePoly[QQ], sequence: SturmSequence, a: QQ, b: QQ, count: Int, mut chain: _IntegerChain, mut budget: Budget) raises PolyError -> Bool:
    """The root-count check, leaving the verified chain's integer data in chain."""
    # Borrow every witness component; public and algebraic callers share all
    # obligations without constructing a temporary owning certificate.
    f.check_invariants(budget)
    var n = len(sequence.polynomials)
    if f.is_zero() or n == 0 or len(sequence.quotients) != n - 1 or count < 0:
        return False
    if _root_compare(a, b, budget) >= 0 or _sign_at(f, a, budget) == 0 or _sign_at(f, b, budget) == 0:
        return False
    for p in sequence.polynomials:
        budget.charge(1)
        p.check_invariants(budget)
        f._same(p)
        if p.is_zero():
            return False
    if not _dense_equal(f, sequence.polynomials[0], budget):
        return False
    if f.degree() == 0:
        return n == 1 and count == 0
    if n < 2 or not _dense_equal(_derivative_dense(f, budget), sequence.polynomials[1], budget):
        return False
    if not _chain_relations(sequence, chain, budget):
        return False
    return count == _integer_variations(chain, sequence, a, budget) - _integer_variations(chain, sequence, b, budget)


@fieldwise_init
struct CancellationCertificate(Copyable, Movable, Writable):
    """The common factor and normalized quotient witnesses for cancellation."""
    var common: SparsePoly[QQ]
    """The cancelled polynomial, including denominator scalar normalization."""
    var cofactors: Tuple[SparsePoly[QQ], SparsePoly[QQ]]
    """The resulting numerator and denominator."""


def check_cancellation(p: SparsePoly[QQ], q: SparsePoly[QQ], certificate: CancellationCertificate, mut budget: Budget) raises PolyError -> Bool:
    """Check that cancellation preserves the rational function where q is nonzero.

    Args:
        p: The original numerator.
        q: The original nonzero denominator.
        certificate: The proposed common factor and quotients.
        budget: The shared work allowance.

    Returns:
        Whether p=common*a and q=common*b with q nonzero (F-C1).

    Raises:
        PolyError: DOMAIN for invalid representations, LIMIT or CAPACITY on work limits.
    """
    p.check_invariants(budget)
    q.check_invariants(budget)
    certificate.common.check_invariants(budget)
    certificate.cofactors[0].check_invariants(budget)
    certificate.cofactors[1].check_invariants(budget)
    if q.is_zero():
        return False
    return _equal(p, certificate.common.mul(certificate.cofactors[0], budget), budget) and _equal(q, certificate.common.mul(certificate.cofactors[1], budget), budget)


def _chain_relations(sequence: SturmSequence, mut chain: _IntegerChain, mut budget: Budget) raises PolyError -> Bool:
    # p[i - 1] == q[i - 1] * p[i] - p[i + 1] for every i. With each entry
    # written as s P (P its primitive integer part, s a rational scalar) and
    # q = Q / E, a relation is P0 = alpha Q P1 - beta P2 with
    # alpha = s1 / (E s0) and beta = s2 / s0; clearing their denominators
    # with D gives the integer identity D P0 = (D alpha) Q P1 - (D beta) P2,
    # checked on the small primitive parts. Longer quotients are checked as
    # rational products. The identities are the integer chain steps.
    var n = len(sequence.polynomials)
    _allocation[List[Integer]](n, budget)
    var forms = List[Tuple[List[Integer], Rational]](capacity=n)
    for p in sequence.polynomials:
        forms.append(_scaled_form(p, budget))
    chain = _IntegerChain()
    chain.first = forms[0][0].copy()
    if len(forms[0][0]) > 1:
        chain.bounded = True
        chain.bound = _fujiwara_exponent(forms[0][0])
    if n > 1:
        chain.second = forms[1][0].copy()
    for i in range(n):
        chain.degrees.append(len(forms[i][0]) - 1)
        chain.signs.append(forms[i][1].sign())
        if n <= _SHORT:
            chain.entries.append(forms[i][0].copy())
    var none = (List[Integer](), Rational(0))
    for i in range(1, n):
        budget.charge(1)
        ref q = sequence.quotients[i - 1]
        q.check_invariants(budget)
        var quotient = _integer_form(q, budget)
        if q.degree() > 1:
            var relation = q.mul(sequence.polynomials[i], budget)
            if i + 1 < n:
                relation = relation.sub(sequence.polynomials[i + 1], budget)
            if not _dense_equal(sequence.polynomials[i - 1], relation, budget):
                return False
            if i + 1 < n:
                var step = _step_scalars(forms[i - 1][1], forms[i][1], forms[i + 1][1], quotient[1])
                _chain_step(chain, step, quotient[0], budget)
            continue
        q._same(sequence.polynomials[i])
        if sequence.polynomials[i - 1].variable != q.variable:
            return False
        if i + 1 < n:
            sequence.polynomials[i + 1]._same(q)
            var step = _step_scalars(forms[i - 1][1], forms[i][1], forms[i + 1][1], quotient[1])
            if not _linear_relation(forms[i - 1][0], forms[i][0], forms[i + 1][0], quotient[0], step, budget):
                return False
            _chain_step(chain, step, quotient[0], budget)
        else:
            var step = _step_scalars(forms[i - 1][1], forms[i][1], none[1], quotient[1])
            if not _linear_relation(forms[i - 1][0], forms[i][0], none[0], quotient[0], step, budget):
                return False
    return True


def _step_scalars(s0: Rational, s1: Rational, s2: Rational, denominator: Integer) raises PolyError -> Tuple[Integer, Integer, Integer]:
    # (D, D alpha, D beta) for alpha = s1 / (denominator s0), beta = s2 / s0.
    try:
        var alpha = s1 / (s0 * Rational(denominator))
        var beta = s2 / s0
        var d = lcm(alpha.denominator(), beta.denominator())
        return (d.copy(), alpha.numerator() * (d // alpha.denominator()), beta.numerator() * (d // beta.denominator()))
    except e:
        raise PolyError(PolyErrorKind.CAPACITY, String(e))


def _chain_step(mut chain: _IntegerChain, step: Tuple[Integer, Integer, Integer], quotient: List[Integer], mut budget: Budget) raises PolyError:
    # D P0 = (A Q) P1 + (-B) P2 is the chain step (powers, quotients, contents).
    budget.charge(UInt64(len(quotient) + 1))
    try:
        var scaled = List[Integer](capacity=len(quotient))
        for v in quotient:
            scaled.append(v * step[1])
        chain.powers.append(step[0].copy())
        chain.quotients.append(scaled^)
        chain.contents.append(-step[2])
    except e:
        raise PolyError(PolyErrorKind.CAPACITY, String(e))


def _scaled_form(p: DensePoly[QQ], mut budget: Budget) raises PolyError -> Tuple[List[Integer], Rational]:
    # p = s P with P primitive: G, the gcd of the numerators, and L, the lcm
    # of the denominators, usually settle after one or two big gcds; every
    # other coefficient only needs a divisibility test.
    _allocation[Integer](len(p.coefficients), budget)
    var size = 0
    for c in p.coefficients:
        budget.charge(1)
        size += c.size()
    _charge_size(size, budget)
    try:
        var g = Integer(0)
        var common = Integer(1)
        for c in p.coefficients:
            var v = abs(c.value.numerator())
            if not v:
                continue
            if not g:
                g = v^
            elif g != Integer(1) and v % g:
                g = gcd(g, v)
            var d = c.value.denominator()
            if d != common and common % d:
                common = lcm(common, d)
        var values = List[Integer](capacity=len(p.coefficients))
        for c in p.coefficients:
            var d = c.value.denominator()
            var v = c.value.numerator() // g if g != Integer(1) else c.value.numerator()
            values.append(v if d == common else v * (common // d))
        return (values^, Rational(g, common))
    except e:
        raise PolyError(PolyErrorKind.CAPACITY, String(e))


def _integer_form(p: DensePoly[QQ], mut budget: Budget) raises PolyError -> Tuple[List[Integer], Integer]:
    _allocation[Integer](len(p.coefficients), budget)
    var values = List[Integer](capacity=len(p.coefficients))
    var common = Integer(1)
    for c in p.coefficients:
        budget.charge(1)
        _charge_size(c.size(), budget)
    try:
        for c in p.coefficients:
            # Reduced denominators of one entry usually divide one shared
            # denominator, so after a few lcm steps only remainders are needed.
            var d = c.value.denominator()
            if d != common and common % d:
                common = lcm(common, d)
        for c in p.coefficients:
            var d = c.value.denominator()
            values.append(c.value.numerator() if d == common else c.value.numerator() * (common // d))
    except e:
        raise PolyError(PolyErrorKind.CAPACITY, String(e))
    return (values^, common^)


def _linear_relation(p0: List[Integer], p1: List[Integer], p2: List[Integer], quotient: List[Integer], step: Tuple[Integer, Integer, Integer], mut budget: Budget) raises PolyError -> Bool:
    # D P0 == A (Q1 x + Q0) P1 - B P2, coefficient by coefficient; the last
    # relation has no P2.
    var length = max(max(len(p0), len(p1) + 1), len(p2))
    var size = 0
    try:
        var a = quotient[0].copy() if len(quotient) > 0 else Integer(0)
        var b = quotient[1].copy() if len(quotient) > 1 else Integer(0)
        for j in range(length):
            var term = Integer(0)
            if j < len(p1) and a:
                term = a * p1[j]
            if j >= 1 and j - 1 < len(p1) and b:
                term = term + b * p1[j - 1]
            var rhs = term * step[1]
            if j < len(p2):
                rhs = rhs - p2[j] * step[2]
            var lhs = p0[j] * step[0] if j < len(p0) else Integer(0)
            size += (lhs.magnitude_bit_length() + rhs.magnitude_bit_length()) // 8 + 1
            if lhs != rhs:
                return False
    except e:
        raise PolyError(PolyErrorKind.CAPACITY, String(e))
    budget.charge(UInt64(length))
    _charge_size(size, budget)
    return True


struct _IntegerChain(Copyable, Movable):
    """Integer data of a Sturm chain built by _sturm_chain, for exact signs.

    Entry i is c_i P_i with P_i primitive; for i >= 1,
    powers[i - 1] P_{i-1} = quotients[i - 1] P_i + contents[i - 1] P_{i+1}.
    """
    var first: List[Integer]
    var second: List[Integer]
    var degrees: List[Int]
    var signs: List[Int]
    var powers: List[Integer]
    var quotients: List[List[Integer]]
    var contents: List[Integer]
    var bounded: Bool
    """Whether every real root lies strictly inside (-2^bound, 2^bound)."""
    var bound: Int
    var entries: List[List[Integer]]
    """Every integer entry P_i of a short chain (at most _SHORT entries), else empty."""

    def __init__(out self):
        self.bounded = False
        self.bound = 0
        self.entries = List[List[Integer]]()
        self.first = List[Integer]()
        self.second = List[Integer]()
        self.degrees = List[Int]()
        self.signs = List[Int]()
        self.powers = List[Integer]()
        self.quotients = List[List[Integer]]()
        self.contents = List[Integer]()


comptime _SHORT = 8


def _fujiwara_exponent(c: List[Integer]) -> Int:
    # Every complex root z of sum c_j x^j satisfies |z| < 2^e:
    # |z| <= 2 max_i |c_{n-i} / c_n|^(1/i) (Fujiwara), and
    # |c_{n-i} / c_n| < 2^(bits(c_{n-i}) - bits(c_n) + 1).
    var n = len(c) - 1
    var top = c[n].magnitude_bit_length()
    var k = -(1 << 30)
    for i in range(1, n + 1):
        if c[n - i]:
            var e = c[n - i].magnitude_bit_length() - top + 1
            k = max(k, -((-e) // i))
    return k + 1


def _beyond(a: QQ, exponent: Int) raises PolyError -> Bool:
    # |a| >= 2^exponent.
    try:
        var u = abs(a.value.numerator())
        var v = a.value.denominator()
        if exponent >= 0:
            return u >= (v << exponent)
        return (u << -exponent) >= v
    except e:
        raise PolyError(PolyErrorKind.CAPACITY, String(e))


def _homogeneous(c: List[Integer], degree: Int, u: Integer, v: Integer, shift: Int) raises -> Integer:
    # v^degree c(u / v); v = 2^shift when shift >= 0.
    var t = c[len(c) - 1].copy()
    var power = Integer(1)
    for j in range(len(c) - 2, -1, -1):
        if shift >= 0:
            t = t * u + (c[j] << (shift * (degree - j)))
        else:
            power = power * v
            t = t * u + c[j] * power
    if len(c) - 1 < degree:
        if shift >= 0:
            t = t << (shift * (degree - len(c) + 1))
        else:
            for _ in range(degree - len(c) + 1):
                t = t * v
    return t^


def _integer_variations(chain: _IntegerChain, sequence: SturmSequence, a: QQ, mut budget: Budget, side: Int = 0) raises PolyError -> Int:
    """Sign variations of a chain from _sturm_chain at a, as _variations would count them.

    With H_i = v^(d_i) P_i(u / v), the pseudo-division identities give
    H_{i+1} = (L H_{i-1} - v^(d_{i-1} - d_i) Q(u / v) H_i) / (g v^(d_{i-1} - d_{i+1})),
    an exact integer division, and sign(c_i P_i(a)) = sign(c_i) sign(H_i).
    """
    var n = len(chain.degrees)
    if n < 2 or n != len(sequence.polynomials):
        return _chain_variations(sequence.polynomials, sequence.quotients, a, budget, side)
    if len(chain.entries) == n:
        # A short chain signs each entry directly: certified fixed-point
        # Horner needs far fewer bits than exact values at long points.
        var previous_sign = 0
        var changes = 0
        for i in range(n):
            budget.charge(UInt64(len(chain.entries[i])))
            var sign: Int
            try:
                sign = _sign(chain.entries[i], a.value) * chain.signs[i]
            except e:
                raise PolyError(PolyErrorKind.CAPACITY, String(e))
            sign = _one_sided(sequence.polynomials[i], sign, a, side, budget)
            if sign != 0:
                if previous_sign != 0 and previous_sign != sign:
                    changes += 1
                previous_sign = sign
        return changes
    if chain.bounded and _beyond(a, chain.bound):
        # Variations change only at roots of f (Sturm), so beyond every root
        # they are those at infinity: the leading-coefficient signs, with
        # (-1)^degree on the left.
        var previous = 0
        var count = 0
        for p in sequence.polynomials:
            budget.charge(1)
            var sign = p.coefficients[p.degree()].value.sign()
            if a.value.sign() < 0 and p.degree() % 2:
                sign = -sign
            if previous != 0 and previous != sign:
                count += 1
            previous = sign
        return count
    var previous = 0
    var count = 0
    var before = Integer(0)
    var current = Integer(0)
    var size = 0
    var u = a.value.numerator()
    var v = a.value.denominator()
    var shift: Int
    try:
        shift = v.magnitude_bit_length() - 1 if (Integer(1) << (v.magnitude_bit_length() - 1)) == v else -1
    except e:
        raise PolyError(PolyErrorKind.CAPACITY, String(e))
    for i in range(n):
        budget.charge(1)
        try:
            if i == 0:
                current = _homogeneous(chain.first, chain.degrees[0], u, v, shift)
            elif i == 1:
                before = current^
                current = _homogeneous(chain.second, chain.degrees[1], u, v, shift)
            else:
                ref q = chain.quotients[i - 2]
                var lowered = chain.degrees[i - 2] - chain.degrees[i]
                var scaled = _homogeneous(q, chain.degrees[i - 2] - chain.degrees[i - 1], u, v, shift)
                var numerator = chain.powers[i - 2] * before - scaled * current
                if chain.contents[i - 2] != Integer(1):
                    numerator = numerator // chain.contents[i - 2]
                if shift >= 0:
                    numerator = numerator >> (shift * lowered)
                else:
                    for _ in range(lowered):
                        numerator = numerator // v
                before = current^
                current = numerator^
            size += current.magnitude_bit_length() // 8 + 1
        except e:
            raise PolyError(PolyErrorKind.CAPACITY, String(e))
        var sign = current.sign() * chain.signs[i]
        sign = _one_sided(sequence.polynomials[i], sign, a, side, budget)
        if sign != 0:
            if previous != 0 and previous != sign:
                count += 1
            previous = sign
    _charge_size(size, budget)
    return count
