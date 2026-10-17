"""Exact real-root multiplicities with independently checked squarefree evidence."""
from apn_mojo import Rational
from ._root_ops import _chain_variations
from .coefficients import CoefficientRing, QQ
from .dense import DensePoly
from .errors import Budget, PolyError, PolyErrorKind, _allocation, _sum, _product
from .certificates import SquarefreeDecomposition, SturmSequence, check_squarefree_product, _check_root_count_parts, _dense_equal
from .squarefree import squarefree
from .roots import sturm_sequence, sign_changes
from .evaluate import _derivative_dense
from ._euclidean import _extended
from ._dense_ops import _copy, _constant
from ._coefficient_ops import _copy as _copy_coefficient
from .numeric_options import NumericOptions
from .numeric_real_roots import RealRootResult, _check_real
from .numeric_evaluate import _exact_dense_boxes
from ._numeric_roots import _rational_polynomial


@fieldwise_init
struct RootMultiplicityCertificate(Copyable, Movable):
    """Prove per-cell multiplicities through squarefree factors and Sturm counts."""
    var decomposition: SquarefreeDecomposition[QQ]
    """A product decomposition of the exact polynomial into multiplicity blocks."""
    var squarefree_witnesses: List[Tuple[DensePoly[QQ], DensePoly[QQ]]]
    """Multipliers u and v satisfying u*g+v*g'=1 for each block g."""
    var sequences: List[SturmSequence]
    """One independently checkable Sturm sequence per block."""
    var multiplicities: List[Int]
    """Zero for excluded cover cells and the root multiplicity for each one-root cell."""


def real_root_multiplicities[C: CoefficientRing](poly: DensePoly[C], roots: RealRootResult, options: NumericOptions, mut budget: Budget) raises PolyError -> RootMultiplicityCertificate:
    """Attach exact multiplicities to a checked real-root isolation.

    Parameters:
        C: ZZ or QQ.

    Args:
        poly: The exact polynomial.
        roots: A complete result isolating one distinct root per positive cell.
        options: The options describing that result.
        budget: The shared work allowance.

    Returns:
        Product, squarefreeness and Sturm evidence for every multiplicity.

    Raises:
        PolyError: DOMAIN for invalid or nonisolating results, LIMIT or CAPACITY on work limits.
    """
    var boxes = _exact_dense_boxes(poly, budget)
    if not roots.isolated or not _check_real(boxes, roots, options, budget):
        raise PolyError(PolyErrorKind.DOMAIN, "multiplicities require a checked complete real isolation")
    var exact = _rational_polynomial(boxes, budget)
    var decomposition = squarefree(exact.value(), budget)
    _allocation[Tuple[DensePoly[QQ], DensePoly[QQ]]](len(decomposition.factors), budget)
    _allocation[SturmSequence](len(decomposition.factors), budget)
    _allocation[Int](len(roots.cells), budget)
    var witnesses = List[Tuple[DensePoly[QQ], DensePoly[QQ]]]()
    var sequences = List[SturmSequence]()
    var multiplicities = List[Int](length=len(roots.cells), fill=0)
    for entry in decomposition.factors:
        var derivative = _derivative_dense(entry[0], budget)
        var bezout = _extended(entry[0], derivative, budget)
        witnesses.append((_copy(bezout[1], budget), _copy(bezout[2], budget)))
        var sequence = sturm_sequence(entry[0], budget)
        for i in range(len(roots.cells)):
            ref cell = roots.cells[i]
            var count = _chain_variations(sequence.polynomials, sequence.quotients, cell.interval.real_low, budget) - _chain_variations(sequence.polynomials, sequence.quotients, cell.interval.real_high, budget)
            multiplicities[i] = _sum(multiplicities[i], _product(count, entry[1]))
        sequences.append(sequence^)
    return RootMultiplicityCertificate(decomposition^, witnesses^, sequences^, multiplicities^)


def check_real_root_multiplicities[C: CoefficientRing](poly: DensePoly[C], roots: RealRootResult, options: NumericOptions, certificate: RootMultiplicityCertificate, mut budget: Budget) raises PolyError -> Bool:
    """Check root multiplicities without performing squarefree decomposition or gcd.

    Parameters:
        C: ZZ or QQ.

    Args:
        poly: The exact polynomial.
        roots: The claimed complete real isolation.
        options: The options describing the isolation.
        certificate: Product, Bézout and root-count witnesses.
        budget: The shared work allowance.

    Returns:
        Whether every per-cell multiplicity is proved exactly.

    Raises:
        PolyError: DOMAIN for malformed polynomial data, LIMIT or CAPACITY on work limits.
    """
    var boxes = _exact_dense_boxes(poly, budget)
    if not roots.isolated or not _check_real(boxes, roots, options, budget):
        return False
    var exact = _rational_polynomial(boxes, budget)
    var n = len(certificate.decomposition.factors)
    if n != len(certificate.squarefree_witnesses) or n != len(certificate.sequences) or len(roots.cells) != len(certificate.multiplicities):
        return False
    if not check_squarefree_product(exact.value(), certificate.decomposition, budget):
        return False
    _allocation[Int](len(roots.cells), budget)
    var multiplicities = List[Int](length=len(roots.cells), fill=0)
    for k in range(n):
        ref factor = certificate.decomposition.factors[k][0]
        var exponent = certificate.decomposition.factors[k][1]
        if factor.degree() < 1 or exponent < 1:
            return False
        ref witness = certificate.squarefree_witnesses[k]
        witness[0].check_invariants(budget)
        witness[1].check_invariants(budget)
        var identity = factor.mul(witness[0], budget).add(_derivative_dense(factor, budget).mul(witness[1], budget), budget)
        if not _dense_equal(identity, _constant(factor, QQ(Rational(1)), budget), budget):
            return False
        ref sequence = certificate.sequences[k]
        var left = _copy_coefficient(roots.cells[0].interval.real_low, budget)
        var right = _copy_coefficient(roots.cells[len(roots.cells) - 1].interval.real_high, budget)
        var total = _chain_variations(sequence.polynomials, sequence.quotients, left, budget) - _chain_variations(sequence.polynomials, sequence.quotients, right, budget)
        if not _check_root_count_parts(factor, sequence, left, right, total, budget):
            return False
        var previous = _chain_variations(sequence.polynomials, sequence.quotients, left, budget)
        for i in range(len(roots.cells)):
            var next = _chain_variations(sequence.polynomials, sequence.quotients, roots.cells[i].interval.real_high, budget)
            var count = previous - next
            if count < 0 or count > roots.cells[i].count:
                return False
            multiplicities[i] = _sum(multiplicities[i], _product(count, exponent))
            previous = next
    for i in range(len(roots.cells)):
        budget.charge(1)
        if certificate.multiplicities[i] != multiplicities[i] or (roots.cells[i].count == 1 and multiplicities[i] == 0):
            return False
    return True
