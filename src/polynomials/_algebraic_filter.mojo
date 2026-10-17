"""Candidate filters for algebraic-coefficient roots.

A candidate root b of the coefficient annihilator is rejected when interval
evaluation of sum c_i b^i excludes zero on refined witnesses, and accepted
when every coefficient is represented as q_i(b) for rational polynomials q_i
with sum q_i(y) y^i divisible by the minimal polynomial of b. Both proofs use
polynomial identities and interval containments only; no arithmetic
annihilators are formed.
"""
from .errors import Budget, PolyError, PolyErrorKind, _allocation, _sum
from .coefficients import QQ, NoContext
from .dense import DensePoly
from .sparse import SparsePoly
from .algebraic_types import RealAlgebraic, _copy_real, _same_root, _rational, _check_real
from ._algebraic import _refine, _root_cached, _count_cached, _NormalizationCache
from ._root_ops import _sign_at
from .monomial import MonomialOrder
from .resultant import resultant
from ._dense_ops import _copy as _copy_poly, _remainder
from ._euclidean import _extended
from ._root_ops import _compare as _compare_q
from .certificates import _dense_equal


# ------------------------------------------------------------------ intervals

def _bounds(a: RealAlgebraic, mut budget: Budget) raises PolyError -> Tuple[QQ, QQ]:
    budget.charge(1)
    return (a.low.copy(), a.high.copy())


def _interval_mul(a: Tuple[QQ, QQ], b: Tuple[QQ, QQ], mut budget: Budget) raises PolyError -> Tuple[QQ, QQ]:
    var products = [a[0].mul(b[0], budget), a[0].mul(b[1], budget), a[1].mul(b[0], budget), a[1].mul(b[1], budget)]
    var low = products[0].copy()
    var high = products[0].copy()
    for i in range(1, 4):
        budget.charge(1)
        if _compare_q(products[i], low, budget) < 0:
            low = products[i].copy()
        if _compare_q(products[i], high, budget) > 0:
            high = products[i].copy()
    return (low^, high^)


def _interval_add(a: Tuple[QQ, QQ], b: Tuple[QQ, QQ], mut budget: Budget) raises PolyError -> Tuple[QQ, QQ]:
    return (a[0].add(b[0], budget), a[1].add(b[1], budget))


def _interval_value(coefficients: List[RealAlgebraic], x: RealAlgebraic, mut budget: Budget) raises PolyError -> Tuple[QQ, QQ]:
    # Horner over closed intervals; every witness interval contains its value.
    var point = _bounds(x, budget)
    var value = (QQ.zero(NoContext()), QQ.zero(NoContext()))
    for i in range(len(coefficients) - 1, -1, -1):
        budget.charge(1)
        value = _interval_add(_interval_mul(value, point, budget), _bounds(coefficients[i], budget), budget)
    return value^


def _dense_interval(p: DensePoly[QQ], x: RealAlgebraic, mut budget: Budget) raises PolyError -> Tuple[QQ, QQ]:
    var point = _bounds(x, budget)
    var value = (QQ.zero(NoContext()), QQ.zero(NoContext()))
    for i in range(len(p.coefficients) - 1, -1, -1):
        budget.charge(1)
        var c = p.coefficients[i].copy()
        value = _interval_add(_interval_mul(value, point, budget), (c.copy(), c^), budget)
    return value^


def _excludes(value: Tuple[QQ, QQ], mut budget: Budget) raises PolyError -> Bool:
    return value[0].value.sign() > 0 or value[1].value.sign() < 0


def _inside(value: Tuple[QQ, QQ], a: RealAlgebraic, mut budget: Budget) raises PolyError -> Bool:
    # Inside an isolating interval, or equal to a rational value. The interval's
    # endpoints are not roots of its definition, so a root of that definition in
    # the closed image interval lies in the open isolating interval.
    if a.rational:
        return _compare_q(value[0], a.low, budget) == 0 and _compare_q(value[1], a.low, budget) == 0
    return _compare_q(a.low, value[0], budget) <= 0 and _compare_q(value[1], a.high, budget) <= 0


# ------------------------------------------------------------------ the field Q(b) = Q[y]/(m)

def _reduce(p: DensePoly[QQ], m: DensePoly[QQ], mut budget: Budget) raises PolyError -> DensePoly[QQ]:
    if p.degree() < m.degree():
        return _copy_poly(p, budget)
    return _remainder(p, m, budget)


def _field_mul(a: DensePoly[QQ], b: DensePoly[QQ], m: DensePoly[QQ], mut budget: Budget) raises PolyError -> DensePoly[QQ]:
    return _reduce(a.mul(b, budget), m, budget)


def _field_inverse(a: DensePoly[QQ], m: DensePoly[QQ], mut budget: Budget) raises PolyError -> DensePoly[QQ]:
    var e = _extended(a, m, budget)
    if e[0].degree() != 0:
        raise PolyError(PolyErrorKind.DOMAIN, "element is not invertible modulo the minimal polynomial")
    # _extended returns a monic gcd, so s*a + t*m == 1.
    return _reduce(e[1], m, budget)


def _compose(f: DensePoly[QQ], q: DensePoly[QQ], m: DensePoly[QQ], mut budget: Budget) raises PolyError -> DensePoly[QQ]:
    # f(q(y)) modulo m(y), by Horner.
    var result = DensePoly[QQ](0, NoContext())
    for i in range(len(f.coefficients) - 1, -1, -1):
        budget.charge(1)
        var constant = DensePoly[QQ].from_coefficients(0, NoContext(), [f.coefficients[i].copy()], budget)
        result = _field_mul(result, q, m, budget).add(constant, budget)
    return result^


def _combination(representations: List[DensePoly[QQ]], m: DensePoly[QQ], mut budget: Budget) raises PolyError -> DensePoly[QQ]:
    # sum q_i(y) y^i modulo m(y).
    var y = DensePoly[QQ].from_coefficients(0, NoContext(), [QQ.zero(NoContext()), QQ.one(NoContext())], budget)
    var result = DensePoly[QQ](0, NoContext())
    for i in range(len(representations) - 1, -1, -1):
        budget.charge(1)
        result = _field_mul(result, y, m, budget).add(representations[i], budget)
    return _reduce(result, m, budget)


# ------------------------------------------------------------------ checks

def _check_exclusion(coefficients: List[RealAlgebraic], candidate: RealAlgebraic, refined: List[RealAlgebraic], refined_candidate: RealAlgebraic, mut budget: Budget) raises PolyError -> Bool:
    if len(refined) != len(coefficients) or not _same_root(refined_candidate, candidate, budget):
        return False
    for i in range(len(coefficients)):
        budget.charge(1)
        if not _same_root(refined[i], coefficients[i], budget):
            return False
    return _excludes(_interval_value(refined, refined_candidate, budget), budget)


def _check_representation(coefficients: List[RealAlgebraic], candidate: RealAlgebraic, refined: List[RealAlgebraic], refined_candidate: RealAlgebraic, representations: List[DensePoly[QQ]], mut budget: Budget) raises PolyError -> Bool:
    var n = len(coefficients)
    if len(refined) != n or len(representations) != n or not _same_root(refined_candidate, candidate, budget):
        return False
    ref m = candidate.polynomial
    for i in range(n):
        budget.charge(1)
        ref q = representations[i]
        q.check_invariants(budget)
        if q.variable != 0 or not _same_root(refined[i], coefficients[i], budget):
            return False
        if coefficients[i].rational:
            # q_i(b) equals the rational coefficient when m divides q_i - c_i.
            var constant = DensePoly[QQ].from_coefficients(0, NoContext(), [coefficients[i].low.copy()], budget)
            if not _reduce(q.sub(constant, budget), m, budget).is_zero():
                return False
        else:
            # q_i(b) is a root of the coefficient's definition inside its
            # isolating interval, hence equal to the coefficient.
            if not _compose(coefficients[i].polynomial, q, m, budget).is_zero() or not _inside(_dense_interval(q, refined_candidate, budget), refined[i], budget):
                return False
    return _combination(representations, m, budget).is_zero()


# ------------------------------------------------------------------ producers

def _try_exclusion(coefficients: List[RealAlgebraic], candidate: RealAlgebraic, rounds: Int, mut budget: Budget) raises PolyError -> Optional[Tuple[List[RealAlgebraic], RealAlgebraic]]:
    var refined = List[RealAlgebraic]()
    for c in coefficients:
        budget.charge(1)
        refined.append(_copy_real(c, budget))
    var point = _copy_real(candidate, budget)
    for _ in range(rounds):
        budget.charge(1)
        if _excludes(_interval_value(refined, point, budget), budget):
            return (refined^, point^)
        _refine(point, budget)
        for i in range(len(refined)):
            _refine(refined[i], budget)
    return None


def _try_containment(coefficients: List[RealAlgebraic], candidate: RealAlgebraic, representations: List[DensePoly[QQ]], rounds: Int, mut budget: Budget) raises PolyError -> Optional[Tuple[List[RealAlgebraic], RealAlgebraic]]:
    var refined = List[RealAlgebraic]()
    for c in coefficients:
        budget.charge(1)
        refined.append(_copy_real(c, budget))
    var point = _copy_real(candidate, budget)
    for _ in range(rounds):
        budget.charge(1)
        var inside = True
        for i in range(len(refined)):
            if not refined[i].rational and not _inside(_dense_interval(representations[i], point, budget), refined[i], budget):
                inside = False
                break
        if inside:
            return (refined^, point^)
        _refine(point, budget)
    return None


def _coefficient_polynomials(f: SparsePoly[QQ], variable: Int64, coordinate: Int64, point: List[Tuple[Int64, RealAlgebraic]], size: Int, mut budget: Budget) raises PolyError -> List[DensePoly[QQ]]:
    # The coefficient of variable^i as a dense polynomial in the one
    # irrational coordinate, after substituting every rational coordinate.
    var rows = List[List[QQ]]()
    for _ in range(size):
        rows.append(List[QQ]())
    for term in f.terms:
        budget.charge(1)
        var power = 0
        var degree = 0
        var value = term.coefficient.copy()
        for pair in term.monomial.pairs:
            budget.charge(1)
            if pair[0] == variable:
                power = Int(pair[1])
            elif pair[0] == coordinate:
                degree = Int(pair[1])
            else:
                var found = False
                for entry in point:
                    if entry[0] == pair[0]:
                        if not entry[1].rational:
                            raise PolyError(PolyErrorKind.DOMAIN, "a second irrational coordinate")
                        for _ in range(Int(pair[1])):
                            value = value.mul(entry[1].low, budget)
                        found = True
                        break
                if not found:
                    raise PolyError(PolyErrorKind.DOMAIN, "missing coordinate")
        if power >= size:
            raise PolyError(PolyErrorKind.DOMAIN, "coefficient degree mismatch")
        while len(rows[power]) <= degree:
            rows[power].append(QQ.zero(NoContext()))
        rows[power][degree] = rows[power][degree].add(value, budget)
    var result = List[DensePoly[QQ]]()
    for i in range(size):
        budget.charge(1)
        result.append(DensePoly[QQ].from_coefficients(0, NoContext(), rows[i].copy(), budget))
    return result^


def _gcd_over_field(a: List[DensePoly[QQ]], b: List[DensePoly[QQ]], m: DensePoly[QQ], mut budget: Budget) raises PolyError -> List[DensePoly[QQ]]:
    # Monic Euclid in Q(b)[x]; polynomials are coefficient lists, lowest degree first.
    var f = _trim(a, m, budget)
    var g = _trim(b, m, budget)
    while len(g):
        budget.charge(1)
        var inverse = _field_inverse(g[len(g) - 1], m, budget)
        var r = f.copy()
        while len(r) >= len(g):
            budget.charge(1)
            var factor = _field_mul(r[len(r) - 1], inverse, m, budget)
            var shift = len(r) - len(g)
            for i in range(len(g)):
                r[shift + i] = _reduce(r[shift + i].sub(_field_mul(factor, g[i], m, budget), budget), m, budget)
            r = _trim(r, m, budget)
            if len(r) == 0:
                break
        f = g^
        g = r^
    if len(f):
        var inverse = _field_inverse(f[len(f) - 1], m, budget)
        for i in range(len(f)):
            f[i] = _field_mul(f[i], inverse, m, budget)
    return f^


def _trim(p: List[DensePoly[QQ]], m: DensePoly[QQ], mut budget: Budget) raises PolyError -> List[DensePoly[QQ]]:
    var result = List[DensePoly[QQ]]()
    for c in p:
        result.append(_reduce(c, m, budget))
    while len(result) and result[len(result) - 1].is_zero():
        _ = result.pop()
    return result^


def _represent(f: SparsePoly[QQ], variable: Int64, point: List[Tuple[Int64, RealAlgebraic]], coefficients: List[RealAlgebraic], candidate: RealAlgebraic, mut budget: Budget) raises PolyError -> Optional[List[DensePoly[QQ]]]:
    """Polynomials q_i with c_i = q_i(b), when b determines the point's one irrational coordinate."""
    ref m = candidate.polynomial
    var irrational = -1
    for i in range(len(point)):
        if not point[i][1].rational:
            if irrational >= 0:
                return None
            irrational = i
    var result = List[DensePoly[QQ]]()
    if irrational < 0:
        for c in coefficients:
            result.append(DensePoly[QQ].from_coefficients(0, NoContext(), [c.low.copy()], budget))
        return result^
    var coordinate = point[irrational][0]
    var rows = _coefficient_polynomials(f, variable, coordinate, point, len(coefficients), budget)
    # F(x, b) as a polynomial in x over Q(b): coefficient of x^k is sum_i row_i[k] y^i.
    var width = 0
    for r in rows:
        width = max(width, len(r.coefficients))
    var specialized = List[DensePoly[QQ]]()
    for k in range(width):
        budget.charge(1)
        var entries = List[QQ]()
        for i in range(len(rows)):
            entries.append(rows[i].coefficients[k].copy() if k < len(rows[i].coefficients) else QQ.zero(NoContext()))
        specialized.append(_reduce(DensePoly[QQ].from_coefficients(0, NoContext(), entries^, budget), m, budget))
    var definition = List[DensePoly[QQ]]()
    ref alpha = point[irrational][1]
    for c in alpha.polynomial.coefficients:
        definition.append(DensePoly[QQ].from_coefficients(0, NoContext(), [c.copy()], budget))
    var common = _gcd_over_field(definition, specialized, m, budget)
    if len(common) != 2:
        return None
    # x = -common[0] since common is monic of degree one.
    var a = DensePoly[QQ](0, NoContext()).sub(common[0], budget)
    for i in range(len(rows)):
        budget.charge(1)
        result.append(_compose(rows[i], a, m, budget))
    if not _combination(result, m, budget).is_zero():
        return None
    return result^


# ------------------------------------------------------------------ signs at points

def _sparse_interval(f: SparsePoly[QQ], variables: List[Int64], box: List[RealAlgebraic], mut budget: Budget) raises PolyError -> Tuple[QQ, QQ]:
    var total = (QQ.zero(NoContext()), QQ.zero(NoContext()))
    for term in f.terms:
        budget.charge(1)
        var c = term.coefficient.copy()
        var value = (c.copy(), c^)
        for pair in term.monomial.pairs:
            budget.charge(1)
            var index = -1
            for i in range(len(variables)):
                if variables[i] == pair[0]:
                    index = i
                    break
            if index < 0:
                raise PolyError(PolyErrorKind.DOMAIN, "missing coordinate")
            var x = _bounds(box[index], budget)
            for _ in range(Int(pair[1])):
                value = _interval_mul(value, x, budget)
        total = _interval_add(total, value, budget)
    return total^


def _sparse_compose(f: SparsePoly[QQ], variables: List[Int64], representations: List[DensePoly[QQ]], m: DensePoly[QQ], mut budget: Budget) raises PolyError -> DensePoly[QQ]:
    # f(r_1(y), ..., r_k(y)) modulo m(y).
    var total = DensePoly[QQ](0, NoContext())
    for term in f.terms:
        budget.charge(1)
        var value = DensePoly[QQ].from_coefficients(0, NoContext(), [term.coefficient.copy()], budget)
        for pair in term.monomial.pairs:
            budget.charge(1)
            var index = -1
            for i in range(len(variables)):
                if variables[i] == pair[0]:
                    index = i
                    break
            if index < 0:
                raise PolyError(PolyErrorKind.DOMAIN, "missing coordinate")
            for _ in range(Int(pair[1])):
                value = _field_mul(value, representations[index], m, budget)
        total = total.add(value, budget)
    return _reduce(total, m, budget)


def _check_point_interval(f: SparsePoly[QQ], variables: List[Int64], point: List[RealAlgebraic], refined: List[RealAlgebraic], relation: Int, mut budget: Budget) raises PolyError -> Bool:
    if len(refined) != len(point) or relation == 0:
        return False
    for i in range(len(point)):
        budget.charge(1)
        if not _same_root(refined[i], point[i], budget):
            return False
    var value = _sparse_interval(f, variables, refined, budget)
    return (relation > 0 and value[0].value.sign() > 0) or (relation < 0 and value[1].value.sign() < 0)


def _check_point_zero(f: SparsePoly[QQ], variables: List[Int64], point: List[RealAlgebraic], refined: List[RealAlgebraic], primitive: Int, representations: List[DensePoly[QQ]], mut budget: Budget) raises PolyError -> Bool:
    var k = len(point)
    if len(refined) != k or len(representations) != k or primitive < 0 or primitive >= k or point[primitive].rational:
        return False
    ref m = point[primitive].polynomial
    var y = DensePoly[QQ].from_coefficients(0, NoContext(), [QQ.zero(NoContext()), QQ.one(NoContext())], budget)
    for j in range(k):
        budget.charge(1)
        ref r = representations[j]
        r.check_invariants(budget)
        if r.variable != 0 or not _same_root(refined[j], point[j], budget):
            return False
        if j == primitive:
            if not _dense_equal(r, y, budget):
                return False
        elif point[j].rational:
            var constant = DensePoly[QQ].from_coefficients(0, NoContext(), [point[j].low.copy()], budget)
            if not _reduce(r.sub(constant, budget), m, budget).is_zero():
                return False
        elif not _compose(point[j].polynomial, r, m, budget).is_zero() or not _inside(_dense_interval(r, refined[primitive], budget), refined[j], budget):
            return False
    return _sparse_compose(f, variables, representations, m, budget).is_zero()


def _try_point_interval(f: SparsePoly[QQ], variables: List[Int64], point: List[RealAlgebraic], rounds: Int, mut budget: Budget) raises PolyError -> Optional[Tuple[List[RealAlgebraic], Int]]:
    var refined = List[RealAlgebraic]()
    for c in point:
        refined.append(_copy_real(c, budget))
    for _ in range(rounds):
        budget.charge(1)
        var value = _sparse_interval(f, variables, refined, budget)
        if value[0].value.sign() > 0:
            return (refined^, 1)
        if value[1].value.sign() < 0:
            return (refined^, -1)
        var exact = True
        for i in range(len(refined)):
            if not refined[i].rational:
                exact = False
                _refine(refined[i], budget)
        if exact:
            return None
    return None


def _try_point_zero(f: SparsePoly[QQ], variables: List[Int64], point: List[RealAlgebraic], rounds: Int, mut budget: Budget) raises PolyError -> Optional[Tuple[List[RealAlgebraic], Int, List[DensePoly[QQ]]]]:
    # The last irrational coordinate is primitive; at most one other may be irrational.
    var primitive = -1
    var other = -1
    for i in range(len(point)):
        if not point[i].rational:
            if primitive >= 0:
                if other >= 0:
                    return None
                other = primitive
            primitive = i
    if primitive < 0:
        return None
    ref m = point[primitive].polynomial
    var representations = List[DensePoly[QQ]]()
    for i in range(len(point)):
        budget.charge(1)
        if i == primitive:
            representations.append(DensePoly[QQ].from_coefficients(0, NoContext(), [QQ.zero(NoContext()), QQ.one(NoContext())], budget))
        elif point[i].rational:
            representations.append(DensePoly[QQ].from_coefficients(0, NoContext(), [point[i].low.copy()], budget))
        else:
            representations.append(DensePoly[QQ](0, NoContext()))
    if other >= 0:
        # Rows of f as a polynomial in the other coordinate x over Q(theta): gcd with m_x.
        var assignment = List[Tuple[Int64, RealAlgebraic]]()
        for i in range(len(point)):
            if i != other and i != primitive:
                assignment.append((variables[i], _copy_real(point[i], budget)))
        var degree = Int(f.degree_in(variables[primitive], budget))
        var rows = _coefficient_polynomials(f, variables[primitive], variables[other], assignment, degree + 1, budget)
        var width = 0
        for r in rows:
            width = max(width, len(r.coefficients))
        var specialized = List[DensePoly[QQ]]()
        for k in range(width):
            budget.charge(1)
            var entries = List[QQ]()
            for i in range(len(rows)):
                entries.append(rows[i].coefficients[k].copy() if k < len(rows[i].coefficients) else QQ.zero(NoContext()))
            specialized.append(_reduce(DensePoly[QQ].from_coefficients(0, NoContext(), entries^, budget), m, budget))
        var definition = List[DensePoly[QQ]]()
        for c in point[other].polynomial.coefficients:
            definition.append(DensePoly[QQ].from_coefficients(0, NoContext(), [c.copy()], budget))
        var common = _gcd_over_field(definition, specialized, m, budget)
        if len(common) != 2:
            return None
        representations[other] = DensePoly[QQ](0, NoContext()).sub(common[0], budget)
    if not _sparse_compose(f, variables, representations, m, budget).is_zero():
        return None
    var refined = List[RealAlgebraic]()
    for c in point:
        refined.append(_copy_real(c, budget))
    for _ in range(rounds):
        budget.charge(1)
        if other < 0 or _inside(_dense_interval(representations[other], refined[primitive], budget), refined[other], budget):
            return (refined^, primitive, representations^)
        _refine(refined[primitive], budget)
    return None


# ------------------------------------------------------------------ zero proofs through a common divisor

def _divides(divisor: List[DensePoly[QQ]], dividend: List[DensePoly[QQ]], m: DensePoly[QQ], mut budget: Budget) raises PolyError -> Bool:
    # Division by a monic polynomial in Q(b)[x] leaves remainder zero.
    var r = _trim(dividend, m, budget)
    var n = len(divisor)
    while len(r) >= n:
        budget.charge(1)
        var factor = r[len(r) - 1].copy()
        var shift = len(r) - n
        for i in range(n):
            r[shift + i] = _reduce(r[shift + i].sub(_field_mul(factor, divisor[i], m, budget), budget), m, budget)
        r = _trim(r, m, budget)
    return len(r) == 0


def _divisor_value(divisor: List[DensePoly[QQ]], x: QQ, b: RealAlgebraic, mut budget: Budget) raises PolyError -> Tuple[QQ, QQ]:
    # sum [g_k(b)] x^k over intervals.
    var point = (x.copy(), x.copy())
    var value = (QQ.zero(NoContext()), QQ.zero(NoContext()))
    for k in range(len(divisor) - 1, -1, -1):
        budget.charge(1)
        value = _interval_add(_interval_mul(value, point, budget), _dense_interval(divisor[k], b, budget), budget)
    return value^


def _sign_change(divisor: List[DensePoly[QQ]], a: RealAlgebraic, b: RealAlgebraic, mut budget: Budget) raises PolyError -> Bool:
    var left = _divisor_value(divisor, a.low, b, budget)
    var right = _divisor_value(divisor, a.high, b, budget)
    return (left[0].value.sign() > 0 and right[1].value.sign() < 0) or (left[1].value.sign() < 0 and right[0].value.sign() > 0)


def _rows_over_field(f: SparsePoly[QQ], variables: List[Int64], point: List[RealAlgebraic], primitive: Int, other: Int, m: DensePoly[QQ], mut budget: Budget) raises PolyError -> List[DensePoly[QQ]]:
    # f(x, b) with every rational coordinate substituted, as coefficients in Q(b) by powers of x.
    var assignment = List[Tuple[Int64, RealAlgebraic]]()
    for i in range(len(point)):
        if i != other and i != primitive:
            if not point[i].rational:
                raise PolyError(PolyErrorKind.DOMAIN, "a third irrational coordinate")
            assignment.append((variables[i], _copy_real(point[i], budget)))
    var degree = Int(f.degree_in(variables[primitive], budget))
    var rows = _coefficient_polynomials(f, variables[primitive], variables[other], assignment, degree + 1, budget)
    var width = 0
    for r in rows:
        width = max(width, len(r.coefficients))
    var specialized = List[DensePoly[QQ]]()
    for k in range(width):
        budget.charge(1)
        var entries = List[QQ]()
        for i in range(len(rows)):
            entries.append(rows[i].coefficients[k].copy() if k < len(rows[i].coefficients) else QQ.zero(NoContext()))
        specialized.append(_reduce(DensePoly[QQ].from_coefficients(0, NoContext(), entries^, budget), m, budget))
    return specialized^


def _constants(p: DensePoly[QQ], mut budget: Budget) raises PolyError -> List[DensePoly[QQ]]:
    var result = List[DensePoly[QQ]]()
    for c in p.coefficients:
        result.append(DensePoly[QQ].from_coefficients(0, NoContext(), [c.copy()], budget))
    return result^


def _check_point_divisor(f: SparsePoly[QQ], variables: List[Int64], point: List[RealAlgebraic], refined: List[RealAlgebraic], primitive: Int, divisor: List[DensePoly[QQ]], mut budget: Budget) raises PolyError -> Bool:
    var k = len(point)
    if len(refined) != k or primitive < 0 or primitive >= k or point[primitive].rational or len(divisor) < 2:
        return False
    var other = -1
    for i in range(k):
        budget.charge(1)
        if not _same_root(refined[i], point[i], budget):
            return False
        if i != primitive and not point[i].rational:
            if other >= 0:
                return False
            other = i
    if other < 0:
        return False
    ref m = point[primitive].polynomial
    for g in divisor:
        g.check_invariants(budget)
        if g.variable != 0 or g.degree() >= m.degree():
            return False
    var one = DensePoly[QQ].from_coefficients(0, NoContext(), [QQ.one(NoContext())], budget)
    if not _dense_equal(divisor[len(divisor) - 1], one, budget):
        return False
    # The divisor's roots are roots of the other coordinate's definition and of f(x, b);
    # one of them lies in that coordinate's isolating interval, so it is the coordinate.
    if not _divides(divisor, _constants(point[other].polynomial, budget), m, budget):
        return False
    if not _divides(divisor, _rows_over_field(f, variables, point, primitive, other, m, budget), m, budget):
        return False
    return _sign_change(divisor, refined[other], refined[primitive], budget)


def _try_point_divisor(f: SparsePoly[QQ], variables: List[Int64], point: List[RealAlgebraic], rounds: Int, mut budget: Budget) raises PolyError -> Optional[Tuple[List[RealAlgebraic], Int, List[DensePoly[QQ]]]]:
    var primitive = -1
    var other = -1
    for i in range(len(point)):
        if not point[i].rational:
            if primitive >= 0:
                if other >= 0:
                    return None
                other = primitive
            primitive = i
    if primitive < 0 or other < 0:
        return None
    ref m = point[primitive].polynomial
    var specialized = _rows_over_field(f, variables, point, primitive, other, m, budget)
    var divisor = _gcd_over_field(_constants(point[other].polynomial, budget), specialized, m, budget)
    if len(divisor) < 2:
        return None
    var refined = List[RealAlgebraic]()
    for c in point:
        refined.append(_copy_real(c, budget))
    for round in range(rounds):
        budget.charge(1)
        if _sign_change(divisor, refined[other], refined[primitive], budget):
            return (refined^, primitive, divisor^)
        # The divisor's coefficients carry the primitive coordinate's interval
        # width; it must shrink faster than the other coordinate's interval.
        _refine(refined[primitive], budget)
        if round % 3 == 0:
            _refine(refined[other], budget)
    return None


# ------------------------------------------------------------------ root filters through a common divisor

def _check_root_divisor(coefficients: List[RealAlgebraic], candidate: RealAlgebraic, refined: List[RealAlgebraic], refined_candidate: RealAlgebraic, element: RealAlgebraic, representations: List[DensePoly[QQ]], mut budget: Budget) raises PolyError -> Bool:
    # c_i = r_i(e) for an algebraic e, and a monic G over Q(b) divides m_e(x) and
    # sum_i r_i(x) b^i and changes sign on e's interval: then sum_i c_i b^i = 0.
    var n = len(coefficients)
    if len(refined) != n or len(representations) < n + 2 or element.rational or not _check_real(element, budget) or not _same_root(refined_candidate, candidate, budget) or candidate.rational:
        return False
    ref me = element.polynomial
    ref mb = candidate.polynomial
    for i in range(n):
        budget.charge(1)
        ref r = representations[i]
        r.check_invariants(budget)
        if r.variable != 0 or not _same_root(refined[i], coefficients[i], budget):
            return False
        if coefficients[i].rational:
            var constant = DensePoly[QQ].from_coefficients(0, NoContext(), [coefficients[i].low.copy()], budget)
            if not _reduce(r.sub(constant, budget), me, budget).is_zero():
                return False
        elif not _compose(coefficients[i].polynomial, r, me, budget).is_zero() or not _inside(_dense_interval(r, element, budget), refined[i], budget):
            return False
    var divisor = List[DensePoly[QQ]]()
    for i in range(n, len(representations)):
        representations[i].check_invariants(budget)
        if representations[i].variable != 0:
            return False
        divisor.append(_reduce(representations[i], mb, budget))
    var one = DensePoly[QQ].from_coefficients(0, NoContext(), [QQ.one(NoContext())], budget)
    if not _dense_equal(divisor[len(divisor) - 1], one, budget):
        return False
    # sum_i r_i(x) b^i, as coefficients in Q(b) by powers of x.
    var width = 0
    for i in range(n):
        width = max(width, len(representations[i].coefficients))
    var rows = List[DensePoly[QQ]]()
    for k in range(width):
        budget.charge(1)
        var entries = List[QQ]()
        for i in range(n):
            entries.append(representations[i].coefficients[k].copy() if k < len(representations[i].coefficients) else QQ.zero(NoContext()))
        rows.append(_reduce(DensePoly[QQ].from_coefficients(0, NoContext(), entries^, budget), mb, budget))
    if not _divides(divisor, _constants(me, budget), mb, budget) or not _divides(divisor, rows, mb, budget):
        return False
    return _sign_change(divisor, element, refined_candidate, budget)


def _try_root_divisor(f: SparsePoly[QQ], variable: Int64, point: List[Tuple[Int64, RealAlgebraic]], coefficients: List[RealAlgebraic], candidate: RealAlgebraic, rounds: Int, mut budget: Budget) raises PolyError -> Optional[Tuple[List[RealAlgebraic], RealAlgebraic, RealAlgebraic, List[DensePoly[QQ]]]]:
    if candidate.rational:
        return None
    var irrational = -1
    for i in range(len(point)):
        if not point[i][1].rational:
            if irrational >= 0:
                return None
            irrational = i
    if irrational < 0:
        return None
    var element = _copy_real(point[irrational][1], budget)
    ref me = point[irrational][1].polynomial
    ref mb = candidate.polynomial
    var rows = _coefficient_polynomials(f, variable, point[irrational][0], point, len(coefficients), budget)
    var representations = List[DensePoly[QQ]]()
    for r in rows:
        representations.append(_reduce(r, me, budget))
    var width = 0
    for r in representations:
        width = max(width, len(r.coefficients))
    var specialized = List[DensePoly[QQ]]()
    for k in range(width):
        budget.charge(1)
        var entries = List[QQ]()
        for i in range(len(representations)):
            entries.append(representations[i].coefficients[k].copy() if k < len(representations[i].coefficients) else QQ.zero(NoContext()))
        specialized.append(_reduce(DensePoly[QQ].from_coefficients(0, NoContext(), entries^, budget), mb, budget))
    var divisor = _gcd_over_field(_constants(me, budget), specialized, mb, budget)
    if len(divisor) < 2:
        return None
    var refined = List[RealAlgebraic]()
    for c in coefficients:
        refined.append(_copy_real(c, budget))
    var point_b = _copy_real(candidate, budget)
    for round in range(rounds):
        budget.charge(1)
        var ready = _sign_change(divisor, element, point_b, budget)
        if ready:
            for i in range(len(coefficients)):
                if not coefficients[i].rational and not _inside(_dense_interval(representations[i], element, budget), refined[i], budget):
                    ready = False
                    break
        if ready:
            for g in divisor:
                representations.append(g.copy())
            return (refined^, point_b^, element^, representations^)
        _refine(point_b, budget)
        if round % 3 == 0:
            _refine(element, budget)
    return None


# ------------------------------------------------------------------ direct evaluation at one irrational coordinate

def _single_irrational(f: SparsePoly[QQ], point: List[Tuple[Int64, RealAlgebraic]], mut budget: Budget) raises PolyError -> Int:
    # The index of the one irrational coordinate that f uses, -1 if none, -2 if several or a variable is unassigned.
    var found = -1
    for v in f.variables(budget):
        budget.charge(1)
        var index = -1
        for i in range(len(point)):
            if point[i][0] == v:
                index = i
                break
        if index < 0:
            return -2
        if not point[index][1].rational:
            if found >= 0 and found != index:
                return -2
            found = index
    return found


def _image(f: SparsePoly[QQ], point: List[Tuple[Int64, RealAlgebraic]], index: Int, mut budget: Budget) raises PolyError -> DensePoly[QQ]:
    # f with every rational coordinate substituted, as a dense polynomial in the irrational one.
    var coordinate = point[index][0]
    var row = List[QQ]()
    for term in f.terms:
        budget.charge(1)
        var degree = 0
        var value = term.coefficient.copy()
        for pair in term.monomial.pairs:
            budget.charge(1)
            if pair[0] == coordinate:
                degree = Int(pair[1])
                continue
            for entry in point:
                if entry[0] == pair[0]:
                    for _ in range(Int(pair[1])):
                        value = value.mul(entry[1].low, budget)
                    break
        while len(row) <= degree:
            row.append(QQ.zero(NoContext()))
        row[degree] = row[degree].add(value, budget)
    return DensePoly[QQ].from_coefficients(0, NoContext(), row^, budget)


def _check_direct(f: SparsePoly[QQ], point: List[Tuple[Int64, RealAlgebraic]], value: RealAlgebraic, witness: List[RealAlgebraic], mut budget: Budget) raises PolyError -> Bool:
    var index = _single_irrational(f, point, budget)
    if index < 0 or len(witness) != 1 or not _same_root(witness[0], point[index][1], budget) or not _check_real(value, budget):
        return False
    ref m = point[index][1].polynomial
    var r = _reduce(_image(f, point, index, budget), m, budget)
    # value is a root of its definition at r(alpha); for an irrational value the
    # image interval selects it among that definition's roots.
    if not _compose(value.polynomial, r, m, budget).is_zero():
        return False
    return value.rational or _inside(_dense_interval(r, witness[0], budget), value, budget)


def _direct_value(f: SparsePoly[QQ], point: List[Tuple[Int64, RealAlgebraic]], mut cache: _NormalizationCache, mut budget: Budget) raises PolyError -> Optional[Tuple[RealAlgebraic, RealAlgebraic]]:
    """The value of f at a point with one irrational coordinate alpha, as r(alpha) for r = f mod m_alpha."""
    var index = _single_irrational(f, point, budget)
    if index < 0:
        return None
    ref alpha = point[index][1]
    ref m = alpha.polynomial
    var r = _reduce(_image(f, point, index, budget), m, budget)
    var witness = _copy_real(alpha, budget)
    if r.degree() <= 0:
        var q = r.coefficients[0].copy() if r.degree() == 0 else QQ.zero(NoContext())
        return (_rational(q, budget), witness^)
    # The minimal polynomial of r(alpha) divides Res_x(m(x), z - r(x)).
    var order = MonomialOrder()
    var defining = _embed_dense(m, 1, budget)
    var shifted = SparsePoly[QQ].variable(0, order, NoContext(), budget).sub(_embed_dense(r, 1, budget), budget)
    var h = DensePoly[QQ].from_sparse(resultant(defining, shifted, 1, budget).resultant, budget, variable=Int64(0))
    if h.is_zero():
        return None
    for _ in range(4096):
        budget.charge(1)
        var image = _dense_interval(r, witness, budget)
        if _compare_q(image[0], image[1], budget) < 0 and _sign_at(h, image[0], budget) != 0 and _sign_at(h, image[1], budget) != 0 and _count_cached(h, image[0], image[1], cache.sequences, budget) == 1:
            var value = _root_cached(h, image[0], image[1], cache, budget)
            return (value^, witness^)
        _refine(witness, budget)
    return None


def _embed_dense(p: DensePoly[QQ], variable: Int64, mut budget: Budget) raises PolyError -> SparsePoly[QQ]:
    var moved = _copy_poly(p, budget)
    moved.variable = variable
    return moved.to_sparse(MonomialOrder(), budget)


# ------------------------------------------------------------------ tower elimination

def _check_coefficient_images(coefficients: List[RealAlgebraic], element: RealAlgebraic, representations: List[DensePoly[QQ]], mut budget: Budget) raises PolyError -> Bool:
    # c_i = r_i(e) for every coefficient.
    if len(representations) != len(coefficients) or element.rational or not _check_real(element, budget):
        return False
    ref me = element.polynomial
    for i in range(len(coefficients)):
        budget.charge(1)
        ref r = representations[i]
        r.check_invariants(budget)
        if r.variable != 0:
            return False
        if coefficients[i].rational:
            var constant = DensePoly[QQ].from_coefficients(0, NoContext(), [coefficients[i].low.copy()], budget)
            if not _reduce(r.sub(constant, budget), me, budget).is_zero():
                return False
        elif not _compose(coefficients[i].polynomial, r, me, budget).is_zero() or not _inside(_dense_interval(r, element, budget), coefficients[i], budget):
            return False
    return True


def _tower_definitions(element: RealAlgebraic, representations: List[DensePoly[QQ]], mut budget: Budget) raises PolyError -> Tuple[SparsePoly[QQ], SparsePoly[QQ]]:
    # sum_i r_i(x) y^i with y variable zero and x variable one, and m_e(x).
    var order = MonomialOrder()
    var y = SparsePoly[QQ].variable(0, order, NoContext(), budget)
    var total = SparsePoly[QQ].zero(order, NoContext(), budget)
    for i in range(len(representations) - 1, -1, -1):
        budget.charge(1)
        total = total.mul(y, budget).add(_embed_dense(representations[i], 1, budget), budget)
    return (total^, _embed_dense(element.polynomial, 1, budget))


def _try_tower(f: SparsePoly[QQ], variable: Int64, point: List[Tuple[Int64, RealAlgebraic]], coefficients: List[RealAlgebraic], rounds: Int, mut budget: Budget) raises PolyError -> Optional[Tuple[RealAlgebraic, List[DensePoly[QQ]]]]:
    var irrational = -1
    for i in range(len(point)):
        if not point[i][1].rational:
            if irrational >= 0:
                return None
            irrational = i
    if irrational < 0:
        return None
    var element = _copy_real(point[irrational][1], budget)
    ref me = point[irrational][1].polynomial
    var rows = _coefficient_polynomials(f, variable, point[irrational][0], point, len(coefficients), budget)
    var representations = List[DensePoly[QQ]]()
    for r in rows:
        representations.append(_reduce(r, me, budget))
    for _ in range(rounds):
        budget.charge(1)
        if _check_coefficient_images(coefficients, element, representations, budget):
            return (element^, representations^)
        _refine(element, budget)
    return None
