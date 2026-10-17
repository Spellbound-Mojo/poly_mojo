"""Certified sparse evaluation and partial specialization at algebraic points."""
from .errors import Budget, PolyError, PolyErrorKind, _allocation, _sum, _charge_size
from .coefficients import QQ, NoContext
from .sparse import SparsePoly, Term
from ._grouping import _partition
from .monomial import Monomial
from .algebraic_types import RealAlgebraic, _rational, _copy_real, _check_real, _same_root
from .algebraic_arithmetic import AlgebraicArithmeticCertificate, check_algebraic_arithmetic
from ._algebraic_certify import _arithmetic_cached
from ._algebraic import _NormalizationCache
from .algebraic_roots import AlgebraicRootsCertificate, algebraic_roots, check_algebraic_roots
from ._algebraic_ops import _is_zero_real
from ._algebraic_filter import _direct_value, _check_direct


@fieldwise_init
struct AlgebraicPolynomialEvaluation(Copyable, Movable, Writable):
    """A fixed sparse evaluation schedule with one certificate per arithmetic step."""
    var steps: List[AlgebraicArithmeticCertificate]
    """Binary powering, term multiplication and summation witnesses in traversal order."""
    var value: RealAlgebraic
    """The exact evaluation result."""
    var witness: List[RealAlgebraic]
    """For a direct proof without steps, a refined witness of the one irrational coordinate; empty otherwise."""


@fieldwise_init
struct AlgebraicSpecializationCertificate(Copyable, Movable, Writable):
    """Exact algebraic coefficients after assigning a subset of polynomial variables."""
    var monomials: List[Monomial]
    """The remaining monomials, including those whose coefficients become zero."""
    var evaluations: List[AlgebraicPolynomialEvaluation]
    """The coefficient evaluations aligned with the remaining monomials."""


@fieldwise_init
struct AlgebraicRootsAtCertificate(Copyable, Movable, Writable):
    """Complete real roots after certified specialization of all other variables."""
    var specialization: AlgebraicSpecializationCertificate
    """The exact coefficient specialization."""
    var isolation: AlgebraicRootsCertificate
    """Every real root of the specialized nonzero polynomial."""


def _point(point: List[Tuple[Int64, RealAlgebraic]], mut budget: Budget) raises PolyError:
    for i in range(len(point)):
        budget.charge(1)
        if point[i][0] < 0 or not _check_real(point[i][1], budget):
            raise PolyError(PolyErrorKind.DOMAIN, "invalid algebraic assignment")
        for j in range(i):
            budget.charge(1)
            if point[i][0] == point[j][0]:
                raise PolyError(PolyErrorKind.DOMAIN, "duplicate algebraic assignment")


@fieldwise_init
struct _PreparedPoint(Movable):
    # Call-scoped indices into an immutable point, never cached across calls.
    var coordinates: List[Tuple[Int64, Int]]

    def index(self, variable: Int64, mut budget: Budget) raises PolyError -> Int:
        var low = 0
        var high = len(self.coordinates)
        while low < high:
            budget.charge(1)
            var middle = low + (high - low) // 2
            if self.coordinates[middle][0] < variable:
                low = middle + 1
            else:
                high = middle
        if low < len(self.coordinates) and self.coordinates[low][0] == variable:
            return self.coordinates[low][1]
        return -1


def _prepare_point(point: List[Tuple[Int64, RealAlgebraic]], mut budget: Budget) raises PolyError -> _PreparedPoint:
    _point(point, budget)
    _allocation[Tuple[Int64, Int]](len(point), budget)
    var coordinates = List[Tuple[Int64, Int]](capacity=len(point))
    for i in range(len(point)):
        budget.charge(1)
        var position = len(coordinates)
        coordinates.append((point[i][0], i))
        while position > 0 and coordinates[position - 1][0] > point[i][0]:
            budget.charge(1)
            coordinates[position] = coordinates[position - 1]
            position -= 1
        coordinates[position] = (point[i][0], i)
    return _PreparedPoint(coordinates^)


def _step[checking: Bool](a: RealAlgebraic, b: RealAlgebraic, op: Int, given: List[AlgebraicArithmeticCertificate], mut generated: List[AlgebraicArithmeticCertificate], mut cursor: Int, mut cache: _NormalizationCache, mut budget: Budget) raises PolyError -> RealAlgebraic:
    comptime if checking:
        if cursor >= len(given) or given[cursor].operation != op or not check_algebraic_arithmetic(a, _copy_real(b, budget), given[cursor], budget):
            raise PolyError(PolyErrorKind.DOMAIN, "invalid algebraic evaluation step")
        var value = _copy_real(given[cursor].value, budget)
        cursor = _sum(cursor, 1)
        return value^
    else:
        var proof = _arithmetic_cached(a, b, op, cache, budget)
        var value = _copy_real(proof.value, budget)
        _allocation[AlgebraicArithmeticCertificate](1, budget)
        generated.append(proof^)
        return value^


def _evaluation[checking: Bool](f: SparsePoly[QQ], point: List[Tuple[Int64, RealAlgebraic]], prepared: _PreparedPoint, given: AlgebraicPolynomialEvaluation, mut cache: _NormalizationCache, mut budget: Budget) raises PolyError -> AlgebraicPolynomialEvaluation:
    f.check_invariants(budget)
    comptime if checking:
        if len(given.witness):
            if len(given.steps) or not _check_direct(f, point, given.value, given.witness, budget):
                raise PolyError(PolyErrorKind.DOMAIN, "invalid direct algebraic evaluation")
            return AlgebraicPolynomialEvaluation(List[AlgebraicArithmeticCertificate](), _copy_real(given.value, budget), List[RealAlgebraic]())
    else:
        # One irrational coordinate: the value is r(alpha) for r = f mod m_alpha.
        var direct = _direct_value(f, point, cache, budget)
        if direct:
            var parts = direct.take()
            return AlgebraicPolynomialEvaluation(List[AlgebraicArithmeticCertificate](), parts[0].copy(), [parts[1].copy()])
    var generated = List[AlgebraicArithmeticCertificate]()
    var cursor = 0
    var value = _rational(QQ.zero(NoContext()), budget)
    for term in f.terms:
        budget.charge(1)
        var product = _rational(term.coefficient, budget)
        for pair in term.monomial.pairs:
            budget.charge(1)
            var index = prepared.index(pair[0], budget)
            if index < 0:
                raise PolyError(PolyErrorKind.DOMAIN, "missing algebraic assignment")
            var base = _copy_real(point[index][1], budget)
            var power = _rational(QQ.one(NoContext()), budget)
            var exponent = pair[1]
            while exponent:
                budget.charge(1)
                if exponent & 1:
                    power = _step[checking](power, base, 2, given.steps, generated, cursor, cache, budget)
                exponent >>= 1
                if exponent:
                    base = _step[checking](base, base, 2, given.steps, generated, cursor, cache, budget)
            product = _step[checking](product, power, 2, given.steps, generated, cursor, cache, budget)
        value = _step[checking](value, product, 0, given.steps, generated, cursor, cache, budget)
    comptime if checking:
        if cursor != len(given.steps) or not _same_root(given.value, value, budget):
            raise PolyError(PolyErrorKind.DOMAIN, "invalid algebraic evaluation result")
    return AlgebraicPolynomialEvaluation(generated^, value^, List[RealAlgebraic]())


def algebraic_evaluate_sparse(f: SparsePoly[QQ], point: List[Tuple[Int64, RealAlgebraic]], mut budget: Budget) raises PolyError -> AlgebraicPolynomialEvaluation:
    """Evaluate a sparse polynomial at exact algebraic coordinates with arithmetic proofs.

    Args:
        f: The rational polynomial.
        point: Distinct assignments covering every variable of the polynomial.
        budget: The shared work allowance.

    Returns:
        The exact result and its complete arithmetic transcript.

    Raises:
        PolyError: DOMAIN for missing, duplicate or invalid assignments, LIMIT or CAPACITY on work limits.
    """
    var cache = _NormalizationCache()
    return _evaluate_sparse_cached(f, point, cache, budget)


def _evaluate_sparse_cached(f: SparsePoly[QQ], point: List[Tuple[Int64, RealAlgebraic]], mut cache: _NormalizationCache, mut budget: Budget) raises PolyError -> AlgebraicPolynomialEvaluation:
    var empty = AlgebraicPolynomialEvaluation(List[AlgebraicArithmeticCertificate](), _rational(QQ.zero(NoContext()), budget), List[RealAlgebraic]())
    var prepared = _prepare_point(point, budget)
    return _evaluation[False](f, point, prepared, empty, cache, budget)


def check_algebraic_evaluate_sparse(f: SparsePoly[QQ], point: List[Tuple[Int64, RealAlgebraic]], certificate: AlgebraicPolynomialEvaluation, mut budget: Budget) raises PolyError -> Bool:
    """Verify a sparse evaluation by checking its fixed arithmetic schedule.

    Args:
        f: The original rational polynomial.
        point: The original exact assignments.
        certificate: The proposed evaluation transcript.
        budget: The shared work allowance.

    Returns:
        Whether every arithmetic witness and the final value are valid.

    Raises:
        PolyError: LIMIT or CAPACITY on work limits.
    """
    try:
        var prepared = _prepare_point(point, budget)
        return _check_evaluation_prepared(f, point, prepared, certificate, budget)
    except e:
        if e.kind == PolyErrorKind.DOMAIN:
            return False
        raise e^


def _check_evaluation_prepared(f: SparsePoly[QQ], point: List[Tuple[Int64, RealAlgebraic]], prepared: _PreparedPoint, certificate: AlgebraicPolynomialEvaluation, mut budget: Budget) raises PolyError -> Bool:
    try:
        var cache = _NormalizationCache()
        _ = _evaluation[True](f, point, prepared, certificate, cache, budget)
        return True
    except e:
        if e.kind == PolyErrorKind.DOMAIN:
            return False
        raise e^


def _groups(f: SparsePoly[QQ], point: List[Tuple[Int64, RealAlgebraic]], mut budget: Budget) raises PolyError -> Tuple[List[Monomial], List[SparsePoly[QQ]]]:
    var prepared = _prepare_point(point, budget)
    return _groups_prepared(f, prepared, budget)


def _groups_prepared(f: SparsePoly[QQ], prepared: _PreparedPoint, mut budget: Budget) raises PolyError -> Tuple[List[Monomial], List[SparsePoly[QQ]]]:
    f.check_invariants(budget)
    var count = len(f.terms)
    _allocation[Term[QQ]](count, budget)
    _allocation[Monomial](count, budget)
    var remaining = List[Term[QQ]](capacity=count)
    var assigned = List[Monomial](capacity=count)
    for term in f.terms:
        budget.charge(1)
        _allocation[Tuple[Int64, UInt32]](len(term.monomial.pairs), budget)
        _allocation[Tuple[Int64, UInt32]](len(term.monomial.pairs), budget)
        var rest = List[Tuple[Int64, UInt32]]()
        var fixed = List[Tuple[Int64, UInt32]]()
        for pair in term.monomial.pairs:
            budget.charge(1)
            if prepared.index(pair[0], budget) >= 0:
                fixed.append(pair)
            else:
                rest.append(pair)
        _charge_size(term.coefficient.size(), budget)
        remaining.append(Term[QQ](Monomial(rest^, budget), term.coefficient.copy()))
        assigned.append(Monomial(fixed^, budget))
    return _partition(remaining^, assigned^, f, budget)


def algebraic_specialize(f: SparsePoly[QQ], point: List[Tuple[Int64, RealAlgebraic]], mut budget: Budget) raises PolyError -> AlgebraicSpecializationCertificate:
    """Specialize any subset of variables with exact algebraic coefficient proofs.

    Args:
        f: The rational polynomial.
        point: Distinct exact assignments for a subset of its variables.
        budget: The shared work allowance.

    Returns:
        Remaining monomials and their certified algebraic coefficients, including zeros.

    Raises:
        PolyError: DOMAIN for invalid assignments, LIMIT or CAPACITY on work limits.
    """
    var cache = _NormalizationCache()
    return _specialize_cached(f, point, cache, budget)


def _specialize_cached(f: SparsePoly[QQ], point: List[Tuple[Int64, RealAlgebraic]], mut cache: _NormalizationCache, mut budget: Budget) raises PolyError -> AlgebraicSpecializationCertificate:
    var prepared = _prepare_point(point, budget)
    var grouped = _groups_prepared(f, prepared, budget)
    _allocation[AlgebraicPolynomialEvaluation](len(grouped[0]), budget)
    var evaluations = List[AlgebraicPolynomialEvaluation]()
    var empty = AlgebraicPolynomialEvaluation(List[AlgebraicArithmeticCertificate](), _rational(QQ.zero(NoContext()), budget), List[RealAlgebraic]())
    for coefficient in grouped[1]:
        budget.charge(1)
        evaluations.append(_evaluation[False](coefficient, point, prepared, empty, cache, budget))
    var monomials = List[Monomial]()
    swap(monomials, grouped[0])
    return AlgebraicSpecializationCertificate(monomials^, evaluations^)


def check_algebraic_specialization(f: SparsePoly[QQ], point: List[Tuple[Int64, RealAlgebraic]], certificate: AlgebraicSpecializationCertificate, mut budget: Budget) raises PolyError -> Bool:
    """Verify every coefficient of a partial algebraic specialization.

    Args:
        f: The original rational polynomial.
        point: The exact assignments.
        certificate: The proposed remaining monomials and coefficient proofs.
        budget: The shared work allowance.

    Returns:
        Whether the certificate contains exactly the specialized coefficients.

    Raises:
        PolyError: DOMAIN for malformed assignments, LIMIT or CAPACITY on work limits.
    """
    var prepared = _prepare_point(point, budget)
    var grouped = _groups_prepared(f, prepared, budget)
    if len(certificate.monomials) != len(grouped[0]) or len(certificate.evaluations) != len(grouped[0]):
        return False
    for i in range(len(grouped[0])):
        budget.charge(1)
        _charge_size(_sum(len(grouped[0][i].pairs), len(certificate.monomials[i].pairs)), budget)
        if grouped[0][i] != certificate.monomials[i] or not _check_evaluation_prepared(grouped[1][i], point, prepared, certificate.evaluations[i], budget):
            return False
    return True


def _zero_specialization(value: AlgebraicSpecializationCertificate, mut budget: Budget) raises PolyError -> Bool:
    for evaluation in value.evaluations:
        budget.charge(1)
        if not _is_zero_real(evaluation.value, budget):
            return False
    return True


def _coefficients(value: AlgebraicSpecializationCertificate, variable: Int64, mut budget: Budget) raises PolyError -> List[RealAlgebraic]:
    var size = 0
    for m in value.monomials:
        budget.charge(1)
        if len(m.pairs) > 1 or (len(m.pairs) == 1 and m.pairs[0][0] != variable):
            raise PolyError(PolyErrorKind.DOMAIN, "root specialization still has another free variable")
        size = max(size, _sum(Int(UInt64(m.exponent(variable, budget))), 1))
    _allocation[RealAlgebraic](size, budget)
    var result = List[RealAlgebraic]()
    for _ in range(size):
        budget.charge(1)
        result.append(_rational(QQ.zero(NoContext()), budget))
    for i in range(len(value.monomials)):
        budget.charge(1)
        result[Int(UInt64(value.monomials[i].exponent(variable, budget)))] = _copy_real(value.evaluations[i].value, budget)
    return result^


def algebraic_roots_at(f: SparsePoly[QQ], variable: Int64, point: List[Tuple[Int64, RealAlgebraic]], mut budget: Budget) raises PolyError -> AlgebraicRootsAtCertificate:
    """Isolate every real root after assigning all variables except one.

    Args:
        f: The rational multivariate polynomial.
        variable: The unassigned root variable.
        point: Distinct assignments for every other occurring variable.
        budget: The shared work allowance.

    Returns:
        The specialization and complete root certificates.

    Raises:
        PolyError: DOMAIN for zero specialization or invalid assignments, LIMIT or CAPACITY on work limits.
    """
    for entry in point:
        budget.charge(1)
        if entry[0] == variable:
            raise PolyError(PolyErrorKind.DOMAIN, "the root variable must be unassigned")
    var specialization = algebraic_specialize(f, point, budget)
    var roots = algebraic_roots(_coefficients(specialization, variable, budget), budget)
    return AlgebraicRootsAtCertificate(specialization^, roots^)


def check_algebraic_roots_at(f: SparsePoly[QQ], variable: Int64, point: List[Tuple[Int64, RealAlgebraic]], certificate: AlgebraicRootsAtCertificate, mut budget: Budget) raises PolyError -> Bool:
    """Verify both specialization and completeness of the resulting real roots.

    Args:
        f: The original rational polynomial.
        variable: The unassigned root variable.
        point: The original exact assignments.
        certificate: The coefficient and root witnesses.
        budget: The shared work allowance.

    Returns:
        Whether the proposed list is exactly the distinct real roots at the point.

    Raises:
        PolyError: DOMAIN for malformed assignments, LIMIT or CAPACITY on work limits.
    """
    for entry in point:
        budget.charge(1)
        if entry[0] == variable:
            return False
    return check_algebraic_specialization(f, point, certificate.specialization, budget) and check_algebraic_roots(_coefficients(certificate.specialization, variable, budget), certificate.isolation, budget)
