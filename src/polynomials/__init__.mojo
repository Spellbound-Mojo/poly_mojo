"""Exact and validated numerical polynomial algebra with explicit work budgets."""
from .numeric_stream import StreamedEnclosure, EnclosureStream, EnclosureStreamChecker
from .errors import PolyErrorKind, PolyError, Budget
from .algebraic_types import RealAlgebraic, AlgebraicComparisonCertificate
from .algebraic import real_rational, real_root, algebraic_compare, algebraic_sign, check_real_algebraic, check_algebraic_comparison
from .coefficients import CoefficientRing, CoefficientField, NoContext, Modulus, ZZ, QQ, ModInt
from .exact_complex import QQi
from .calculus import derivative_dense, rational_dense, rational_sparse, integrate_dense, integrate_integer_dense, definite_integral, compose_dense, affine_transform, taylor_shift, jet_evaluate, integrate_sparse, integrate_integer_sparse, substitute_many
from .interpolation import MultipointPlan, interpolate, hermite_interpolate, check_interpolation, check_hermite_interpolation
from .monomial import Monomial, MonomialOrder
from .sparse import Term, SparsePoly
from .coefficient_buffer import CoefficientBuffer
from .dense import DensePoly, KARATSUBA_THRESHOLD
from .evaluate import evaluate, evaluate_dense, substitute, derivative
from .codec import to_kernel_bytes, from_kernel_bytes, MAX_KERNEL_BYTES
from .division import divmod, pseudo_divmod, divide_exact, divide_by_list
from .primes import prime, crt
from .gcd import content, primitive_part, gcd, gcd_value, extended_gcd, coprimality_certificate
from .sparse_gcd import sparse_gcd, sparse_gcd_integer
from .determinant import DeterminantStep, ProjectionResultantCertificate, projection_resultant, check_projection_resultant
from .cad_projection import CADProjectionCertificate, cad_projection, check_cad_projection
from .lazard import LazardEvaluationCertificate, lazard_evaluate, check_lazard_evaluation
from .cad_types import CADPolynomialLift, CADStackCertificate, CADCell, CADCertificate, CADCellCertificate, CADCoveringCertificate
from .cad import cad, check_cad, cad_cell, check_cad_cell
from .cad_covering import cad_covering, check_cad_covering
from .cylindrical_covering import CADConflict, CADConflictInterval, CylindricalCoveringCertificate, cylindrical_covering, check_cylindrical_covering
from .resultant import resultant, resultant_value, subresultants
from .fractions import RationalFunction
from .squarefree import squarefree
from .sparse_squarefree import SparseSquarefreeDecomposition, squarefree_multivariate, check_sparse_squarefree_product
from .field_multivariate_factor import factor_multivariate_gaussian, factor_multivariate_finite_field
from .finite_field import factor_mod_p, factor_finite_field
from .gaussian_factor import factor_gaussian
from .factor import factor, factor_integer
from .multivariate_factor import MultivariateFactorization, factor_multivariate, factor_multivariate_integer, check_multivariate_factorization
from .groebner import GroebnerBasis, groebner, reduce, membership
from .certificates import MembershipCertificate, check_membership
from .roots import RootInterval, RootIsolation, sturm_sequence, sign_changes, count_roots, isolate_real_roots, refine, sign_on_interval
from .certificates import SturmSequence, RootCountCertificate, check_root_count
from .certificates import SquarefreeDecomposition, Factorization, check_squarefree_product, check_factorization
from .certificates import DivisionResult, ListDivision, GcdResult, ResultantResult, ContentGcdStep, CoprimalityNode, CoprimalityCertificate, CancellationCertificate, check_division, check_list_division, check_common_divisor, check_bezout, check_coprimality, check_resultant_identity, check_cancellation
from .algebraic_arithmetic import AlgebraicArithmeticCertificate, check_algebraic_arithmetic
from .algebraic_evaluation import AlgebraicEvaluationCertificate, algebraic_evaluate, check_algebraic_evaluation
from .algebraic_roots import AlgebraicRootsCertificate, algebraic_roots, check_algebraic_roots
from .algebraic_specialization import AlgebraicPolynomialEvaluation, AlgebraicSpecializationCertificate, AlgebraicRootsAtCertificate, algebraic_evaluate_sparse, check_algebraic_evaluate_sparse, algebraic_specialize, check_algebraic_specialization, algebraic_roots_at, check_algebraic_roots_at
from .algebraic import algebraic_add, algebraic_subtract, algebraic_multiply, algebraic_negate, algebraic_inverse

from .numeric_domains import NumericDomain, FloatDomain, ComplexDomain, BallDomain, ComplexBallDomain
from .numeric_calculus import numeric_integrate_dense, numeric_definite_integral, numeric_compose_dense, numeric_affine_transform, numeric_jet_evaluate, numeric_taylor_shift, numeric_integrate_sparse, numeric_substitute_many
from .numeric_interpolation import numeric_multipoint_evaluate, numeric_interpolate, numeric_hermite_interpolate
from .numeric_dense import NumericDensePoly
from .numeric_sparse import NumericTerm, NumericSparsePoly
from .numeric_bounds import NumericBox, numeric_bounds, numeric_value
from .numeric_convert import convert_numeric_dense, convert_numeric_sparse, numeric_from_dense, numeric_from_sparse
from .numeric_options import NumericOutcome, NumericOptions
from .numeric_evaluate import EnclosureEvaluation, AdaptiveEvaluation, enclose_dense, check_enclose_dense, enclose_numeric, check_enclose_numeric, enclose_sparse, check_enclose_sparse, enclose_numeric_sparse, check_enclose_numeric_sparse, adaptive_enclose_dense, adaptive_enclose_sparse, check_numeric_accuracy
from .numeric_real_roots import RealRootCell, RealRootResult, real_roots_exact, real_roots_numeric, check_real_roots_exact, check_real_roots_numeric
from .numeric_complex_roots import ComplexBoundarySegment, ComplexRootRegion, ComplexRootResult, complex_roots_exact, complex_roots_numeric, check_complex_roots_exact, check_complex_roots_numeric

from .series import TruncatedSeries
from .numeric_series import NumericSeries
from .bases import BasisPolynomial
from .numeric_bases import NumericBasisPolynomial
from .rational_tools import rational_evaluate, rational_derivative, rational_substitute, rational_compose, PartialFractionTerm, PartialFractions, partial_fractions, check_partial_fractions, rational_poles, LaurentExpansion, laurent_expansion, check_laurent_expansion, rational_residue
from .builders import PolynomialRing
from .interchange import serialize_dense, deserialize_dense, serialize_sparse, deserialize_sparse
from .numeric_interchange import serialize_numeric_dense, deserialize_numeric_dense, serialize_numeric_sparse, deserialize_numeric_sparse
from .numeric_multiplicity import RootMultiplicityCertificate, real_root_multiplicities, check_real_root_multiplicities
from .numeric_diagnostics import RootDiagnostics, PolishedRootResult, root_diagnostics_exact, check_root_diagnostics_exact, polish_root_exact, check_polished_root_exact, root_diagnostics_numeric, check_root_diagnostics_numeric, polish_root_numeric, check_polished_root_numeric
from .numeric_refine import refine_real_roots_exact, refine_real_roots_numeric, refine_complex_roots_exact, refine_complex_roots_numeric
from .numeric_division import NumericDivisionStep, NumericDivisionResult, numeric_divmod, check_numeric_division

from .text_stream import PolynomialTextSource, PolynomialTextSink
from .interchange import serialize_dense_to, deserialize_dense_from, serialize_sparse_to, deserialize_sparse_from
from .numeric_interchange import serialize_numeric_dense_to, deserialize_numeric_dense_from, serialize_numeric_sparse_to, deserialize_numeric_sparse_from

from .root_stream import RootStreamReceipt
from .numeric_real_roots import RealRootSink, real_roots_exact_to, real_roots_numeric_to
from .numeric_complex_roots import ComplexRootSink, complex_roots_exact_to, complex_roots_numeric_to
from .root_stream_check import RealRootStreamChecker, ComplexRootStreamChecker
from .cad_stream import CADStreamEvent, CADStreamReceipt, CADSink, CADStreamChecker, cad_to

from .cad_fiber import CADFiber
