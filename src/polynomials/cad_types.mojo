"""Certificate values for cylindrical sections, sectors, stacks and coverings."""
from .algebraic_types import RealAlgebraic, AlgebraicComparisonCertificate
from .dense import DensePoly
from .coefficients import QQ
from .algebraic_specialization import AlgebraicSpecializationCertificate, AlgebraicPolynomialEvaluation
from .algebraic_roots import AlgebraicRootsCertificate
from .lazard import LazardEvaluationCertificate
from .cad_projection import CADProjectionCertificate


@fieldwise_init
struct CADPolynomialLift(Copyable, Movable, Writable):
    """A certified specialization and complete real roots of one projection basis member."""
    var ordinary: Optional[AlgebraicSpecializationCertificate]
    """Ordinary specialization in McCallum mode."""
    var lazard: Optional[LazardEvaluationCertificate]
    """Vanishing-order evaluation in Lazard mode."""
    var roots: Optional[AlgebraicRootsCertificate]
    """All specialized roots, absent only for an allowed McCallum nullification."""


@fieldwise_init
struct CADStackCertificate(Copyable, Movable, Writable):
    """A complete ordered stack of sections and sectors above one base cell."""
    var parent: Int
    """The parent cell index in a decomposition, or the preceding path index."""
    var level: Int
    """The zero-based level of the new coordinate."""
    var lifts: List[CADPolynomialLift]
    """One complete specialization and root proof per basis polynomial."""
    var roots: List[RealAlgebraic]
    """The distinct stack boundaries at the base sample, in increasing order."""
    var sources: List[Tuple[Int, Int]]
    """For each boundary, its basis-polynomial index and specialized root index."""
    var mapping: List[List[Int]]
    """The boundary index of each root of each basis polynomial."""
    var equalities: List[AlgebraicComparisonCertificate]
    """Equalities binding every specialized root to its merged boundary."""
    var ordering: List[AlgebraicComparisonCertificate]
    """Strict comparisons of adjacent boundaries."""
    var samples: List[RealAlgebraic]
    """Alternating sector and section samples, with unbounded sectors at both ends."""
    var separations: List[AlgebraicComparisonCertificate]
    """Section equalities and sector-bound comparisons in sample traversal order."""


@fieldwise_init
struct CADSignWitness(Copyable, Movable, Writable):
    """The proof of one input's sign at a terminal sample point."""
    var kind: Int
    """Zero for the next exact evaluation, one for interval exclusion, two for a representation zero proof, three for a common-divisor zero proof."""
    var point: List[RealAlgebraic]
    """Refined witnesses of every coordinate, for kinds one and two."""
    var primitive: Int
    """For kind two, the coordinate whose field contains every other coordinate."""
    var representations: List[DensePoly[QQ]]
    """For kind two, each coordinate as a rational polynomial in the primitive one; for kind three, the monic divisor's coefficients in the primitive coordinate's field, by powers of the other irrational coordinate."""


@fieldwise_init
struct CADCell(Copyable, Movable, Writable):
    """A cylindrical cell located by its parent and section or sector position."""
    var parent: Int
    """The parent cell index; minus one for the zero-dimensional root cell."""
    var level: Int
    """The final coordinate level; minus one for the root cell."""
    var position: Int
    """The alternating stack position; even positions are sectors, odd positions sections."""
    var sample: RealAlgebraic
    """The exact last sample coordinate, with rational zero as the root-cell placeholder."""
    var evaluations: List[AlgebraicPolynomialEvaluation]
    """Certified input-polynomial values at a full-dimensional coordinate tuple."""
    var signs: List[AlgebraicComparisonCertificate]
    """Comparisons of those values with zero, giving signs constant on the entire cell."""
    var witnesses: List[CADSignWitness]
    """One sign proof per input, or empty when every sign has an exact evaluation."""


@fieldwise_init
struct CADCertificate(Copyable, Movable, Writable):
    """A sign-invariant cylindrical tree with exact witnesses for its checking scope."""
    var projection: CADProjectionCertificate
    """The complete projection closure and basis certificates."""
    var cells: List[CADCell]
    """The root and retained cylindrical cells in breadth-first order."""
    var stacks: List[CADStackCertificate]
    """One complete stack for every nonterminal cell, in cell order."""


@fieldwise_init
struct CADCellCertificate(Copyable, Movable, Writable):
    """A certified single sign-invariant cell containing an exact query point."""
    var projection: CADProjectionCertificate
    """The projection closure for the input family."""
    var stacks: List[CADStackCertificate]
    """One certified stack along the query-point path at each level."""
    var positions: List[Int]
    """The chosen section or sector at each level."""
    var evaluations: List[AlgebraicPolynomialEvaluation]
    """The input-polynomial values at the query point."""
    var signs: List[AlgebraicComparisonCertificate]
    """The constant input signs on the selected cylindrical cell."""


@fieldwise_init
struct CADCoveringCertificate(Copyable, Movable, Writable):
    """A feasibility witness or a complete covering by cells violating a conjunction."""
    var decomposition: CADCertificate
    """The sign-invariant decomposition for the producer's coordinate scope."""
    var witness_cell: Int
    """A satisfying terminal cell, or minus one when the conjunction is infeasible."""
    var violations: List[Int]
    """For infeasibility, one violated constraint index per terminal cell in traversal order."""
