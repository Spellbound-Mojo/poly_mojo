"""Conflict-driven satisfiability of sign conjunctions by cylindrical algebraic coverings.

Source: Abraham, Davenport, England, Kremer, "Deciding the consistency of
non-linear real arithmetic constraints with a conflict driven search using
cylindrical algebraic coverings", JLAMP 119 (2021), Algorithms 2-6. The
search assigns one coordinate at a time and stops at the first satisfying
point. A level whose samples all fail returns intervals, each with the
polynomials that characterize it; their Lazard projection (leading and
trailing coefficients, discriminants, and the resultants the paper selects)
gives the interval excluded one level down. No global projection is built.
"""
from std.collections import Dict
from .errors import Budget, PolyError, PolyErrorKind, _allocation
from .coefficients import QQ, NoContext
from .sparse import SparsePoly
from .monomial import MonomialOrder
from .certificates import _equal
from .algebraic_types import RealAlgebraic, AlgebraicComparisonCertificate, _rational, _copy_real
from .algebraic import algebraic_sign
from .algebraic_specialization import AlgebraicPolynomialEvaluation, _evaluate_sparse_cached, _coefficients
from .algebraic_roots import _RootsContext
from .lazard import _lazard_cached
from .evaluate import derivative
from .resultant import resultant_value
from .multivariate_factor import factor_multivariate
from .cad_projection import _level
from ._views import _lc, _coefficient, _split
from .multivariate_factor import MultivariateFactorization, _copy_factorization, check_multivariate_factorization
from .algebraic_specialization import algebraic_evaluate_sparse, check_algebraic_evaluate_sparse
from .algebraic_types import _check_comparison, _check_real
from ._algebraic_filter import _embed_dense
from ._algebraic import _NormalizationCache, _compare, _roots_by_factors, _Frame as _PointFrame
from .dense import DensePoly
from ._images import _integer_image, _rational_image
from ._dyadic import _dense_value, _of_real, _precision, _add, _mul, _zero
from ._algebraic_filter import _child_frame, _installed, _try_tower, _try_frame_tower, _tower_definitions, _try_exclusion, _try_containment, _represent, _try_root_divisor, _element_divisor, _represent_element, _irrational_count, _tower_resultant
from ._algebraic import _root_cached, _refine
from ._algebraic_filter import _sparse_compose, _dense_interval, _frame_rows, _substitutions, _interval_add, _interval_mul, _gcd_over_field, _constants, _reduce, _sign_change
from ._algebraic_ops import _embed, _norm_expression, _is_zero_real
from .algebraic_evaluation import _evaluate_cached
from ._cad_lifting import _sector, _copy_point
from ._cad_common import _masks


@fieldwise_init
struct _Bound(Copyable, Movable):
    var value: RealAlgebraic
    """The endpoint at the current prefix."""
    var polys: List[Int]
    """Pool polynomials with a root at the endpoint."""
    var indices: List[Int]
    """For each of those polynomials, the endpoint's index among its increasing real roots."""


@fieldwise_init
struct _Interval(Copyable, Movable):
    var lower: Optional[_Bound]
    """None for minus infinity."""
    var upper: Optional[_Bound]
    """None for plus infinity."""
    var lower_closed: Bool
    var upper_closed: Bool
    var main: List[Int]
    """Pool polynomials of this level whose roots delimit the interval."""
    var down: List[Int]
    """Pool polynomials of lower levels that must keep their signs."""
    var constraint: Int
    """The violated input for a direct conflict, or minus one."""
    var sample: RealAlgebraic
    """The sample at which the conflict or the child covering holds."""
    var child: Int
    """The covering node over the sample, or minus one."""


@fieldwise_init
struct _Node(Copyable, Movable):
    var parent: Int
    """The node whose interval sample extends this node's prefix, or minus one."""
    var interval: Int
    """That interval's index in the parent's intervals."""
    var level: Int
    var intervals: List[_Interval]
    """Intervals covering the line above the node's prefix, as found."""
    var cover: List[Int]
    """The selected subcover, ordered from minus to plus infinity."""


@fieldwise_init
struct _Roots(Copyable, Movable):
    var roots: List[RealAlgebraic]
    var lifting: SparsePoly[QQ]
    """The Lazard-curtailed polynomial whose specialization has these roots."""


@fieldwise_init
struct CoveringBound(Copyable, Movable, Writable):
    """An interval endpoint: one real root of a characterization polynomial at the node's prefix."""
    var polynomial: Int
    """The index of the polynomial in CADCoveringsCertificate.polynomials."""
    var root: Int
    """The root's index, in increasing order, among the real roots of the polynomial's Lazard evaluation at the prefix."""


@fieldwise_init
struct CoveringInterval(Copyable, Movable, Writable):
    """An interval of one coordinate, above a node's prefix, on which the conjunction fails."""
    var lower: Optional[CoveringBound]
    """The lower endpoint, or None for minus infinity."""
    var upper: Optional[CoveringBound]
    """The upper endpoint, or None for plus infinity."""
    var lower_closed: Bool
    """Whether the lower endpoint belongs to the interval; with upper_closed, a single section."""
    var upper_closed: Bool
    """Whether the upper endpoint belongs to the interval."""
    var sample: RealAlgebraic
    """A point of the interval at which the conflict or the child covering is established."""
    var constraint: Int
    """The input violated on the whole interval, or minus one when a child covering excludes it."""
    var child: Int
    """The node covering the next coordinate above the sample, or minus one."""
    var polynomials: List[Int]
    """The characterization: same-level polynomials delimiting the interval and lower-level polynomials whose signs it relies on."""


@fieldwise_init
struct CoveringNode(Copyable, Movable, Writable):
    """A covering of one coordinate's line above an exact prefix point."""
    var parent: Int
    """The node whose interval sample extends the prefix, or minus one for the root."""
    var interval: Int
    """That interval's index in the parent's intervals, or minus one for the root."""
    var level: Int
    """The zero-based level of the covered coordinate."""
    var intervals: List[CoveringInterval]
    """Intervals covering the whole line, in increasing order."""


@fieldwise_init
struct CADCoveringsCertificate(Copyable, Movable, Writable):
    """A satisfying point, or a conflict-driven cylindrical covering proving that none exists."""
    var variables: List[Int64]
    """Variables in base-to-top cylindrical order."""
    var polynomials: List[SparsePoly[QQ]]
    """Normalized irreducible polynomials named by bounds and characterizations."""
    var input_factors: List[MultivariateFactorization[QQ]]
    """One factorization per input, in input order."""
    var projections: List[MultivariateFactorization[QQ]]
    """Factorizations of the projection polynomials the checker recomputes, in any order."""
    var nodes: List[CoveringNode]
    """The covering tree, root first; empty when satisfiable or for a root conflict."""
    var root_conflict: Int
    """An input constant on the whole search space whose sign fails, or minus one."""
    var witness: List[RealAlgebraic]
    """A satisfying point in base-to-top order, or empty."""
    var evaluations: List[AlgebraicPolynomialEvaluation]
    """Input values at the witness."""
    var signs: List[AlgebraicComparisonCertificate]
    """Input signs at the witness."""

    def satisfiable(self) -> Bool:
        """Report whether the certificate claims a satisfying point.

        Returns:
            True for a witness, False for a covering or a root conflict.
        """
        return self.root_conflict == -1 and len(self.nodes) == 0


struct _Search(Movable):
    var inputs: List[SparsePoly[QQ]]
    var masks: List[UInt8]
    var variables: List[Int64]
    var levels: List[Int]
    var factors: List[List[Int]]
    # Normalized irreducible polynomials met so far, with their levels.
    var pool: List[SparsePoly[QQ]]
    var pool_levels: List[Int]
    var projected: List[Optional[List[Int]]]
    var resultants: Dict[Int, List[Int]]
    # The current partial sample point and, per prefix length, its frame,
    # normalization cache and roots of pool polynomials.
    var point: List[Tuple[Int64, RealAlgebraic]]
    var frames: List[_PointFrame]
    var caches: List[_NormalizationCache]
    var root_cache: List[Dict[Int, _Roots]]
    var nodes: List[_Node]
    var satisfiable: Bool
    var interval_count: Int
    var lazard: Bool
    # Factorizations of the inputs and of every projection polynomial computed.
    var input_proofs: List[MultivariateFactorization[QQ]]
    var projection_proofs: List[MultivariateFactorization[QQ]]
    var recording: Bool

    def __init__(out self, var inputs: List[SparsePoly[QQ]], var masks: List[UInt8], variables: List[Int64], lazard: Bool = True):
        self.inputs = inputs^
        self.masks = masks^
        self.variables = variables.copy()
        self.levels = List[Int]()
        self.factors = List[List[Int]]()
        self.pool = List[SparsePoly[QQ]]()
        self.pool_levels = List[Int]()
        self.projected = List[Optional[List[Int]]]()
        self.resultants = Dict[Int, List[Int]]()
        self.point = List[Tuple[Int64, RealAlgebraic]]()
        self.frames = List[_PointFrame]()
        self.caches = List[_NormalizationCache]()
        self.root_cache = List[Dict[Int, _Roots]]()
        self.nodes = List[_Node]()
        self.satisfiable = False
        self.interval_count = 0
        self.lazard = lazard
        self.input_proofs = List[MultivariateFactorization[QQ]]()
        self.projection_proofs = List[MultivariateFactorization[QQ]]()
        self.recording = False

    # ------------------------------------------------------------ the pool

    def _add(mut self, f: SparsePoly[QQ], mut result: List[Int], mut budget: Budget) raises PolyError:
        """Append the pool indices of the nonconstant irreducible factors of f."""
        if f.is_zero():
            return
        var proof = factor_multivariate(f.reorder(MonomialOrder(), budget), budget)
        if self.recording and len(proof.factors):
            _allocation[MultivariateFactorization[QQ]](1, budget)
            self.projection_proofs.append(_copy_factorization(proof, budget))
        self._register(proof, result, budget)

    def _register(mut self, proof: MultivariateFactorization[QQ], mut result: List[Int], mut budget: Budget) raises PolyError:
        """Append the pool indices of a factorization's nonconstant factors, adding new ones to the pool."""
        for entry in proof.factors:
            budget.charge(1)
            var level = _level(entry[0], self.variables, budget)
            if level < 0:
                continue
            var index = -1
            for j in range(len(self.pool)):
                budget.charge(1)
                if self.pool_levels[j] == level and _equal(entry[0], self.pool[j], budget):
                    index = j
                    break
            if index < 0:
                index = len(self.pool)
                _allocation[SparsePoly[QQ]](1, budget)
                self.pool.append(entry[0]._copy(budget))
                self.pool_levels.append(level)
                self.projected.append(None)
            var seen = False
            for k in result:
                if k == index:
                    seen = True
                    break
            if not seen:
                _allocation[Int](1, budget)
                result.append(index)

    def _projection(mut self, p: Int, mut budget: Budget) raises PolyError -> List[Int]:
        """Leading and trailing coefficient and discriminant factors of a pool polynomial."""
        if self.projected[p]:
            return self.projected[p].value().copy()
        var result = List[Int]()
        var f = self.pool[p]._copy(budget)
        var variable = self.variables[self.pool_levels[p]]
        if self.pool_levels[p] > 0:
            if self.lazard:
                self._add(_lc(f, variable, budget), result, budget)
                self._add(_coefficient(f, variable, 0, budget), result, budget)
            else:
                for coefficient in _split(f, variable, budget):
                    self._add(coefficient, result, budget)
            var differentiated = derivative(f, variable, budget)
            if f.degree_in(variable, budget) > 1:
                var r = _integer_resultant(f, differentiated, variable, budget)
                self._add(r, result, budget)
        self.projected[p] = result.copy()
        return result^

    def _resultant(mut self, p: Int, q: Int, mut budget: Budget) raises PolyError -> List[Int]:
        var key = min(p, q) * 1048576 + max(p, q)
        var known = self.resultants.get(key)
        if known:
            return known.value().copy()
        var result = List[Int]()
        if self.pool_levels[p] == self.pool_levels[q] and self.pool_levels[p] > 0:
            var variable = self.variables[self.pool_levels[p]]
            var r = _integer_resultant(self.pool[p], self.pool[q], variable, budget)
            self._add(r, result, budget)
        self.resultants[key] = result.copy()
        return result^

    # ------------------------------------------------------------ roots and signs

    def _roots(mut self, p: Int, mut budget: Budget) raises PolyError -> _Roots:
        """All real roots of a pool polynomial of the current level, by Lazard evaluation."""
        var depth = len(self.point)
        var known = self.root_cache[depth].get(p)
        if known:
            return known.value().copy()
        ref f = self.pool[p]
        var variable = self.variables[depth]
        if _rational_point(self.point):
            var h = _specialized(f, self.point, variable, budget)
            if not h.is_zero():
                var found = List[RealAlgebraic]()
                if h.degree() > 0:
                    found = _roots_by_factors(h, self.caches[depth], budget)
                var quick = _Roots(found^, f._copy(budget))
                self.root_cache[depth][p] = quick.copy()
                return quick^
        if self.caches[depth].frame:
            var frame = self.caches[depth].frame.value().copy()
            var framed = _frame_roots(f, variable, self.point, frame, self.caches[depth], budget)
            if framed:
                var quick = _Roots(framed.take(), f._copy(budget))
                self.root_cache[depth][p] = quick.copy()
                return quick^
        var evaluation = _lazard_cached(f, variable, self.point, self.caches[depth], budget)
        var lifting = f._copy(budget)
        for i in range(len(self.point)):
            if evaluation.orders[i] and not self.lazard:
                raise PolyError(PolyErrorKind.UNSUPPORTED, "McCallum nullification requires Lazard mode at this cell")
            for _ in range(evaluation.orders[i]):
                budget.charge(1)
                lifting = derivative(lifting, self.point[i][0], budget)
        var coefficients = _coefficients(evaluation.evaluations[len(evaluation.evaluations) - 1], variable, budget)
        var roots = List[RealAlgebraic]()
        if len(coefficients) > 1:
            roots = _lean_roots(coefficients, _RootsContext(lifting._copy(budget), variable, _copy_point(self.point, budget)), self.caches[depth], budget)
        var result = _Roots(roots^, lifting^)
        self.root_cache[depth][p] = result.copy()
        return result^

    def _sign(mut self, c: Int, sample: RealAlgebraic, mut budget: Budget) raises PolyError -> Int:
        var depth = len(self.point)
        _allocation[Tuple[Int64, RealAlgebraic]](1, budget)
        self.point.append((self.variables[depth], _copy_real(sample, budget)))
        if _rational_point(self.point):
            var value = _specialized(self.inputs[c], self.point, -1, budget)
            _ = self.point.pop()
            return 0 if value.is_zero() else value.coefficients[0].value.sign()
        var lean = _lean_sign(self.inputs[c], self.point, self.caches[depth], budget)
        if lean:
            _ = self.point.pop()
            return lean.value()
        var evaluation = _evaluate_sparse_cached(self.inputs[c], self.point, self.caches[depth], budget)
        _ = self.point.pop()
        return algebraic_sign(evaluation.value, budget).relation

    def _sign_here(mut self, c: Int, mut budget: Budget) raises PolyError -> Int:
        """The sign of an input at the current full prefix."""
        var depth = len(self.point)
        if _rational_point(self.point):
            var value = _specialized(self.inputs[c], self.point, -1, budget)
            return 0 if value.is_zero() else value.coefficients[0].value.sign()
        var lean = _lean_sign(self.inputs[c], self.point, self.caches[depth], budget)
        if lean:
            return lean.value()
        var evaluation = _evaluate_sparse_cached(self.inputs[c], self.point, self.caches[depth], budget)
        return algebraic_sign(evaluation.value, budget).relation

    def _push(mut self, sample: RealAlgebraic, lifting: Optional[SparsePoly[QQ]], mut budget: Budget) raises PolyError:
        var depth = len(self.point)
        var variable = self.variables[depth]
        var frame = _child_frame(self.frames[depth], variable, lifting, sample, budget, terminal=depth + 1 == len(self.variables))
        _allocation[Tuple[Int64, RealAlgebraic]](1, budget)
        self.point.append((variable, _copy_real(sample, budget)))
        var cache = _NormalizationCache()
        cache.frame = _installed(frame, self.point, budget)
        if len(self.frames) == depth + 1:
            self.frames.append(frame^)
            self.caches.append(cache^)
            self.root_cache.append(Dict[Int, _Roots]())
        else:
            self.frames[depth + 1] = frame^
            self.caches[depth + 1] = cache^
            self.root_cache[depth + 1] = Dict[Int, _Roots]()

    def _pop(mut self):
        _ = self.point.pop()

    # ------------------------------------------------------------ intervals

    def _merged(mut self, polys: List[Int], mut budget: Budget) raises PolyError -> List[_Bound]:
        """The distinct roots of several pool polynomials, in increasing order."""
        var bounds = List[_Bound]()
        for p in polys:
            budget.charge(1)
            var found = self._roots(p, budget)
            for j in range(len(found.roots)):
                ref r = found.roots[j]
                budget.charge(1)
                var low = 0
                var high = len(bounds)
                var equal = -1
                while low < high:
                    budget.charge(1)
                    var middle = (low + high) // 2
                    var relation = _compare(r, bounds[middle].value, budget)
                    if relation == 0:
                        equal = middle
                        break
                    if relation < 0:
                        high = middle
                    else:
                        low = middle + 1
                if equal >= 0:
                    bounds[equal].polys.append(p)
                    bounds[equal].indices.append(j)
                else:
                    _allocation[_Bound](1, budget)
                    bounds.insert(low, _Bound(_copy_real(r, budget), [p], [j]))
        return bounds^

    def _conflicts(mut self, level: Int, c: Int, mut intervals: List[_Interval], mut budget: Budget) raises PolyError:
        """Intervals of the current line on which a constraint of this level fails."""
        var main = List[Int]()
        var down = List[Int]()
        for f in self.factors[c]:
            if self.pool_levels[f] == level:
                main.append(f)
            else:
                down.append(f)
        if self.masks[c] == 0:
            _allocation[_Interval](1, budget)
            intervals.append(_Interval(None, None, False, False, List[Int](), List[Int](), c, _rational(QQ.zero(NoContext()), budget), -1))
            return
        var bounds = self._merged(main, budget)
        var roots = List[RealAlgebraic]()
        for b in bounds:
            roots.append(_copy_real(b.value, budget))
        var zero_allowed = self.masks[c] & 2 != 0
        for gap in range(len(bounds) + 1):
            budget.charge(1)
            var sample = _sector(roots, gap, budget)
            var sign = self._sign(c, sample, budget)
            if self.masks[c] & (UInt8(1) << UInt8(sign + 1)) == 0:
                var lower: Optional[_Bound] = None
                var upper: Optional[_Bound] = None
                if gap > 0:
                    lower = bounds[gap - 1].copy()
                if gap < len(bounds):
                    upper = bounds[gap].copy()
                _allocation[_Interval](1, budget)
                intervals.append(_Interval(lower^, upper^, False, False, main.copy(), down.copy(), c, sample^, -1))
            if gap < len(bounds) and not zero_allowed:
                _allocation[_Interval](1, budget)
                intervals.append(_Interval(bounds[gap].copy(), bounds[gap].copy(), True, True, main.copy(), down.copy(), c, _copy_real(bounds[gap].value, budget), -1))

    def _characterized(mut self, sample: RealAlgebraic, child: Int, chars: List[Int], mut budget: Budget) raises PolyError -> _Interval:
        """The largest interval around the sample on which no characterization root lies."""
        var level = len(self.point)
        var main = List[Int]()
        var down = List[Int]()
        for p in chars:
            if self.pool_levels[p] == level:
                main.append(p)
            else:
                down.append(p)
        var lower: Optional[_Bound] = None
        var upper: Optional[_Bound] = None
        var section = False
        for p in main:
            budget.charge(1)
            var found = self._roots(p, budget)
            for j in range(len(found.roots)):
                ref r = found.roots[j]
                budget.charge(1)
                var relation = _compare(r, sample, budget)
                if relation <= 0:
                    var against = _compare(r, lower.value().value, budget) if lower else 1
                    if against > 0:
                        lower = _Bound(_copy_real(r, budget), [p], [j])
                    elif against == 0:
                        lower.value().polys.append(p)
                        lower.value().indices.append(j)
                if relation >= 0:
                    var against = _compare(r, upper.value().value, budget) if upper else -1
                    if against < 0:
                        upper = _Bound(_copy_real(r, budget), [p], [j])
                    elif against == 0:
                        upper.value().polys.append(p)
                        upper.value().indices.append(j)
                if relation == 0:
                    section = True
        if not section:
            # Roots equal to the sample were the only shared bounds.
            pass
        self.interval_count += 1
        return _Interval(lower^, upper^, section, section, main^, down^, -1, _copy_real(sample, budget), child)

    # ------------------------------------------------------------ covers

    def _before(self, a: _Interval, b: _Interval, mut budget: Budget) raises PolyError -> Bool:
        """Order by lower endpoint, closed before open."""
        if not a.lower:
            return Bool(b.lower)
        if not b.lower:
            return False
        var relation = _relation(a.lower.value(), b.lower.value(), budget)
        if relation != 0:
            return relation < 0
        return a.lower_closed and not b.lower_closed

    def _cover(mut self, node: Int, mut budget: Budget) raises PolyError -> List[Int]:
        """A subcover of the node's intervals, ordered along the line (Algorithm 5)."""
        ref intervals = self.nodes[node].intervals
        var cover = List[Int]()
        # The frontier: everything below `value` is covered, and `value` itself when `closed`.
        var reached = False
        var frontier: Optional[_Bound] = None
        var closed = False
        while True:
            budget.charge(1)
            var best = -1
            for i in range(len(intervals)):
                budget.charge(1)
                ref item = intervals[i]
                var connects: Bool
                if not reached:
                    connects = not item.lower
                elif not item.lower:
                    connects = True
                else:
                    var relation = _relation(item.lower.value(), frontier.value(), budget)
                    connects = relation < 0 or (relation == 0 and (closed or item.lower_closed))
                if not connects:
                    continue
                if best < 0 or self._extends(item, intervals[best], budget):
                    best = i
            if best < 0:
                raise PolyError(PolyErrorKind.DOMAIN, "covering intervals leave a gap")
            ref chosen = intervals[best]
            if reached and not self._beyond(chosen, frontier.value(), closed, budget):
                raise PolyError(PolyErrorKind.DOMAIN, "covering intervals leave a gap")
            _allocation[Int](1, budget)
            cover.append(best)
            if not chosen.upper:
                return cover^
            reached = True
            frontier = chosen.upper.value().copy()
            closed = chosen.upper_closed

    def _extends(self, a: _Interval, b: _Interval, mut budget: Budget) raises PolyError -> Bool:
        """Whether a reaches strictly further up than b."""
        if not b.upper:
            return False
        if not a.upper:
            return True
        var relation = _relation(a.upper.value(), b.upper.value(), budget)
        if relation != 0:
            return relation > 0
        return a.upper_closed and not b.upper_closed

    def _beyond(self, a: _Interval, frontier: _Bound, closed: Bool, mut budget: Budget) raises PolyError -> Bool:
        if not a.upper:
            return True
        var relation = _relation(a.upper.value(), frontier, budget)
        return relation > 0 or (relation == 0 and a.upper_closed and not closed)

    def _characterize(mut self, node: Int, mut budget: Budget) raises PolyError -> List[Int]:
        """The polynomials of lower levels that keep the node's covering valid (Algorithm 4)."""
        var cover = self._cover(node, budget)
        self.nodes[node].cover = cover.copy()
        var result = List[Int]()
        for k in range(len(cover)):
            budget.charge(1)
            var item = self.nodes[node].intervals[cover[k]].copy()
            for p in item.down:
                _merge(result, p, budget)
            for p in item.main:
                budget.charge(1)
                for q in self._projection(p, budget):
                    _merge(result, q, budget)
                var found = self._roots(p, budget)
                if item.lower and len(found.roots) and (_contains(item.lower.value().polys, p) or _compare(found.roots[0], item.lower.value().value, budget) <= 0):
                    for q in item.lower.value().polys:
                        if q != p:
                            for r in self._resultant(p, q, budget):
                                _merge(result, r, budget)
                if item.upper and len(found.roots) and (_contains(item.upper.value().polys, p) or _compare(found.roots[len(found.roots) - 1], item.upper.value().value, budget) >= 0):
                    for q in item.upper.value().polys:
                        if q != p:
                            for r in self._resultant(p, q, budget):
                                _merge(result, r, budget)
            if k + 1 < len(cover):
                var next = self.nodes[node].intervals[cover[k + 1]].copy()
                if Bool(item.upper) and Bool(next.lower):
                    for p in item.upper.value().polys:
                        for q in next.lower.value().polys:
                            if p != q:
                                for r in self._resultant(p, q, budget):
                                    _merge(result, r, budget)
        return result^

    # ------------------------------------------------------------ sampling

    def _sample(mut self, intervals: List[_Interval], mut budget: Budget) raises PolyError -> Optional[Tuple[RealAlgebraic, Optional[SparsePoly[QQ]]]]:
        """A sample outside every interval: rational sectors first, then sections (Algorithm 3)."""
        var ends = List[_Bound]()
        for item in intervals:
            budget.charge(1)
            for side in range(2):
                var bound = item.lower.copy() if side == 0 else item.upper.copy()
                if not bound:
                    continue
                var low = 0
                var high = len(ends)
                var equal = False
                while low < high:
                    budget.charge(1)
                    var middle = (low + high) // 2
                    var relation = _relation(bound.value(), ends[middle], budget)
                    if relation == 0:
                        equal = True
                        # Keep every name of the endpoint for later identity matches.
                        for k in range(len(bound.value().polys)):
                            ends[middle].polys.append(bound.value().polys[k])
                            ends[middle].indices.append(bound.value().indices[k])
                        break
                    if relation < 0:
                        high = middle
                    else:
                        low = middle + 1
                if not equal:
                    _allocation[_Bound](1, budget)
                    ends.insert(low, bound.value().copy())
        # Alternating positions: even for open gaps, odd for endpoints.
        var size = 2 * len(ends) + 1
        _allocation[Bool](size, budget)
        var covered = List[Bool](length=size, fill=False)
        for item in intervals:
            budget.charge(1)
            var first = 0
            var last = size - 1
            if item.lower:
                var index = self._find(ends, item.lower.value(), budget)
                first = 2 * index + 1 if item.lower_closed else 2 * index + 2
            if item.upper:
                var index = self._find(ends, item.upper.value(), budget)
                last = 2 * index + 1 if item.upper_closed else 2 * index
            for i in range(first, last + 1):
                covered[i] = True
        var roots = List[RealAlgebraic]()
        for b in ends:
            roots.append(_copy_real(b.value, budget))
        var zero = _rational(QQ.zero(NoContext()), budget)
        var zero_position = 0
        for i in range(len(ends)):
            var relation = _compare(zero, ends[i].value, budget)
            if relation == 0:
                zero_position = 2 * i + 1
                break
            if relation > 0:
                zero_position = 2 * i + 2
        var order = List[Int]()
        order.append(zero_position)
        order.append(0)
        order.append(size - 1)
        for i in range(0, size, 2):
            order.append(i)
        for i in range(1, size, 2):
            if ends[i // 2].value.rational:
                order.append(i)
        for i in range(1, size, 2):
            order.append(i)
        for i in order:
            budget.charge(1)
            if covered[i]:
                continue
            if i % 2 == 0:
                var result: Tuple[RealAlgebraic, Optional[SparsePoly[QQ]]] = (_sector(roots, i // 2, budget), None)
                return result^
            ref bound = ends[i // 2]
            var lifting: Optional[SparsePoly[QQ]] = None
            if not bound.value.rational:
                lifting = self._roots(bound.polys[0], budget).lifting.copy()
            var result: Tuple[RealAlgebraic, Optional[SparsePoly[QQ]]] = (_copy_real(bound.value, budget), lifting^)
            return result^
        return None

    def _find(self, ends: List[_Bound], value: _Bound, mut budget: Budget) raises PolyError -> Int:
        var low = 0
        var high = len(ends)
        while low < high:
            budget.charge(1)
            var middle = (low + high) // 2
            var relation = _relation(value, ends[middle], budget)
            if relation == 0:
                return middle
            if relation < 0:
                high = middle
            else:
                low = middle + 1
        raise PolyError(PolyErrorKind.DOMAIN, "interval endpoint missing from the sample line")

    # ------------------------------------------------------------ search

    def search(mut self, level: Int, mut budget: Budget) raises PolyError -> Int:
        """Return a covering node of the current line, or minus one once satisfied (Algorithm 2)."""
        var intervals = List[_Interval]()
        # Constraints of this level whose conflict intervals are not yet known.
        # A constraint is delineated only once it fails at a candidate sample.
        var pending = List[Int]()
        for c in range(len(self.inputs)):
            budget.charge(1)
            if self.levels[c] == level and self.masks[c] != 7:
                _allocation[Int](1, budget)
                pending.append(c)
        while True:
            budget.charge(1)
            var pick = self._sample(intervals, budget)
            if not pick:
                break
            var chosen = pick.take()
            # Pending constraints are checked at the pushed point, whose frame
            # also serves irrational samples.
            self._push(chosen[0], chosen[1].copy(), budget)
            var failed = -1
            for k in range(len(pending)):
                budget.charge(1)
                var c = pending[k]
                var mask = self.masks[c]
                if mask == 0 or mask & (UInt8(1) << UInt8(self._sign_here(c, budget) + 1)) == 0:
                    failed = k
                    break
            if failed >= 0:
                self._pop()
                var c = pending.pop(failed)
                self._conflicts(level, c, intervals, budget)
                continue
            if level == len(self.variables) - 1:
                self.satisfiable = True
                return -1
            var child = self.search(level + 1, budget)
            if self.satisfiable:
                return -1
            var chars = self._characterize(child, budget)
            self._pop()
            _allocation[_Interval](1, budget)
            intervals.append(self._characterized(chosen[0], child, chars, budget))
        _allocation[_Node](1, budget)
        var index = len(self.nodes)
        for k in range(len(intervals)):
            var child = intervals[k].child
            if child >= 0:
                self.nodes[child].parent = index
                self.nodes[child].interval = k
        self.nodes.append(_Node(-1, -1, level, intervals^, List[Int]()))
        return index


def _frame_roots(f: SparsePoly[QQ], variable: Int64, point: List[Tuple[Int64, RealAlgebraic]], frame: _PointFrame, mut cache: _NormalizationCache, mut budget: Budget) raises PolyError -> Optional[List[RealAlgebraic]]:
    """The real roots of f at a point whose coordinates are polynomials in the frame's generator.

    Every root is a root of the norm N(y) = Res_x(F(x, y), m(x)) for F the
    specialization with the generator x. A candidate root b of N is excluded
    by intervals, or decided by g = gcd(m(x), F(x, b)) over Q(b): g = 1
    rejects it, and g changing sign on the generator's interval accepts it, as
    for the library's common-divisor root witnesses. None when the leading
    coefficient cannot be shown nonzero (a possible Lazard nullification) or
    a candidate stays undecided.
    """
    if not frame.valid or not frame.generator or len(point) > len(frame.variables):
        return None
    var variables = List[Int64]()
    for j in range(len(point)):
        if frame.variables[j] != point[j][0]:
            return None
        variables.append(point[j][0])
    var element = _copy_real(frame.generator.value(), budget)
    ref m = frame.generator.value().polynomial
    var size = f.degree_in(variable, budget) + 1
    var rows = _frame_rows(f, variable, variables, _substitutions(point, frame.representations, budget), m, size, budget)
    var top = len(rows) - 1
    while top >= 0 and rows[top].is_zero():
        top -= 1
    if top < 0:
        return None
    # The leading coefficient is nonzero at the generator: no nullification.
    var proven = False
    for _ in range(64):
        budget.charge(1)
        var precision = _precision(element.low, element.high)
        if _dense_value(rows[top], _of_real(element, precision, budget), precision, budget).sign() != 0:
            proven = True
            break
        _refine(element, budget)
    if not proven:
        return None
    if top == 0:
        return List[RealAlgebraic]()
    while len(rows) > top + 1:
        _ = rows.pop()
    var definitions = _tower_definitions(element, rows, budget)
    var norm = _integer_resultant(definitions[0], definitions[1], 1, budget)
    if norm.is_zero():
        return None
    var candidates = _roots_by_factors(DensePoly[QQ].from_sparse(norm, budget, variable=Int64(0)), cache, budget)
    var roots = List[RealAlgebraic]()
    for candidate in candidates:
        budget.charge(1)
        var beta = _copy_real(candidate, budget)
        var gamma = _copy_real(element, budget)
        var decided = False
        for round in range(24):
            budget.charge(1)
            # Dyadic enclosure of F(gamma, beta); an undecided candidate goes to the exact gcd.
            var precision = max(_precision(beta.low, beta.high), _precision(gamma.low, gamma.high))
            var x = _of_real(beta, precision, budget)
            var g = _of_real(gamma, precision, budget)
            var value = _zero()
            for k in range(top, -1, -1):
                value = _add(_mul(value, x, precision, budget), _dense_value(rows[k], g, precision, budget), precision, budget)
            if value.sign() != 0:
                decided = True
                break
            if beta.rational:
                break
            _refine(beta, budget)
            if round % 3 == 0:
                _refine(gamma, budget)
        if decided:
            continue
        ref mb = candidate.polynomial
        var width = 0
        for r in rows:
            width = max(width, len(r.coefficients))
        var specialized = List[DensePoly[QQ]]()
        for k in range(width):
            budget.charge(1)
            var entries = List[QQ]()
            for i in range(top + 1):
                entries.append(rows[i].coefficients[k].copy() if k < len(rows[i].coefficients) else QQ.zero(NoContext()))
            specialized.append(_reduce(DensePoly[QQ].from_coefficients(0, NoContext(), entries^, budget), mb, budget))
        var divisor = _gcd_over_field(_constants(m, budget), specialized, mb, budget)
        if len(divisor) < 2:
            continue
        for round in range(256):
            budget.charge(1)
            if _sign_change(divisor, gamma, beta, budget):
                decided = True
                break
            _refine(beta, budget)
            if round % 3 == 0:
                _refine(gamma, budget)
        if not decided:
            return None
        _allocation[RealAlgebraic](1, budget)
        roots.append(_copy_real(candidate, budget))
    return roots^


def _lean_roots(coefficients: List[RealAlgebraic], context: _RootsContext, mut cache: _NormalizationCache, mut budget: Budget) raises PolyError -> List[RealAlgebraic]:
    """The real roots of a polynomial with algebraic coefficients, as algebraic_roots finds them, without its certificate."""
    var normalized = List[RealAlgebraic]()
    for coefficient in coefficients:
        budget.charge(1)
        _allocation[RealAlgebraic](1, budget)
        normalized.append(_root_cached(coefficient.polynomial, coefficient.low, coefficient.high, cache, budget))
    var expression = _norm_expression(normalized, budget)
    if expression.is_zero():
        raise PolyError(PolyErrorKind.DOMAIN, "the zero polynomial has no finite root list")
    var element = _rational(QQ.zero(NoContext()), budget)
    var representations = List[DensePoly[QQ]]()
    # One elimination of the base coordinate instead of one per coefficient.
    var tower = _try_tower(context.polynomial, context.variable, context.point, coefficients, 4096, budget)
    if not tower and cache.frame:
        tower = _try_frame_tower(context.polynomial, context.variable, context.point, coefficients, cache.frame.value(), 4096, budget)
    if tower:
        var parts = tower.take()
        var fast = _tower_resultant(parts[0], parts[1], budget)
        var norm: SparsePoly[QQ]
        if fast:
            norm = fast.value().resultant._copy(budget)
        else:
            var definitions = _tower_definitions(parts[0], parts[1], budget)
            norm = resultant_value(definitions[0], definitions[1], 1, budget)
        if not norm.is_zero():
            expression = norm^
            element = parts[0].copy()
            representations = parts[1].copy()
    for i in range(len(normalized) if len(representations) == 0 else 0):
        budget.charge(1)
        if normalized[i].rational:
            continue
        var variable = Int64(i + 1)
        expression = resultant_value(expression, _embed(normalized[i].polynomial, variable, budget), variable, budget)
    var h = DensePoly[QQ].from_sparse(expression, budget, variable=Int64(0))
    if h.is_zero():
        raise PolyError(PolyErrorKind.DOMAIN, "algebraic coefficient norm vanished")
    var candidates = _roots_by_factors(h, cache, budget)
    var roots = List[RealAlgebraic]()
    for i in range(len(candidates)):
        budget.charge(1)
        # Reject by intervals when the value is nonzero; accept by a field
        # representation when the context determines one; else evaluate exactly.
        if _try_exclusion(coefficients, candidates[i], 24, budget):
            continue
        var representation = _represent(context.polynomial, context.variable, context.point, coefficients, candidates[i], budget)
        if representation and _try_containment(coefficients, candidates[i], representation.value(), 256, budget):
            _allocation[RealAlgebraic](1, budget)
            roots.append(_copy_real(candidates[i], budget))
            continue
        var divided = _try_root_divisor(context.polynomial, context.variable, context.point, coefficients, candidates[i], 256, budget)
        if not divided and len(representations) and _irrational_count(context.point, budget) >= 2:
            # Several irrational coordinates: the same witnesses through the tower element.
            var through = _represent_element(element, representations, candidates[i], budget)
            if through and _try_containment(coefficients, candidates[i], through.value(), 256, budget):
                _allocation[RealAlgebraic](1, budget)
                roots.append(_copy_real(candidates[i], budget))
                continue
            divided = _element_divisor(_copy_real(element, budget), representations.copy(), coefficients, candidates[i], 256, budget)
        if divided:
            _allocation[RealAlgebraic](1, budget)
            roots.append(_copy_real(candidates[i], budget))
            continue
        if _try_exclusion(coefficients, candidates[i], 400, budget):
            continue
        var evaluation = _evaluate_cached(coefficients, candidates[i], cache, budget)
        if _is_zero_real(evaluation.value, budget):
            _allocation[RealAlgebraic](1, budget)
            roots.append(_copy_real(candidates[i], budget))
    return roots^


def _lean_sign(f: SparsePoly[QQ], point: List[Tuple[Int64, RealAlgebraic]], cache: _NormalizationCache, mut budget: Budget) raises PolyError -> Optional[Int]:
    """The sign of f at a point whose coordinates are polynomials in the cache frame's generator, when intervals decide it."""
    if not cache.frame:
        return None
    ref frame = cache.frame.value()
    if not frame.valid or not frame.generator or len(point) > len(frame.variables) + 1:
        return None
    var variables = List[Int64]()
    var representations = List[DensePoly[QQ]]()
    for j in range(len(point)):
        budget.charge(1)
        variables.append(point[j][0])
        if point[j][1].rational:
            representations.append(DensePoly[QQ].from_coefficients(0, NoContext(), [point[j][1].low.copy()], budget))
        elif j < len(frame.variables) and frame.variables[j] == point[j][0]:
            representations.append(frame.representations[j].copy())
        else:
            return None
    ref m = frame.generator.value().polynomial
    var r = _sparse_compose(f, variables, representations, m, budget)
    if r.degree() < 0:
        return 0
    if r.degree() == 0:
        return r.coefficients[0].value.sign()
    var witness = _copy_real(frame.generator.value(), budget)
    for _ in range(64):
        budget.charge(1)
        var precision = _precision(witness.low, witness.high)
        var sign = _dense_value(r, _of_real(witness, precision, budget), precision, budget).sign()
        if sign != 0:
            return sign
        if witness.rational:
            return None
        _refine(witness, budget)
    return None


def _rational_point(point: List[Tuple[Int64, RealAlgebraic]]) -> Bool:
    for entry in point:
        if not entry[1].rational:
            return False
    return True


def _specialized(f: SparsePoly[QQ], point: List[Tuple[Int64, RealAlgebraic]], variable: Int64, mut budget: Budget) raises PolyError -> DensePoly[QQ]:
    """f at a rational point, as a univariate polynomial in the free variable (or a constant)."""
    var coefficients = List[QQ]()
    for term in f.terms:
        budget.charge(1)
        var value = term.coefficient.copy()
        var degree = 0
        for pair in term.monomial.pairs:
            budget.charge(1)
            if pair[0] == variable:
                degree = Int(pair[1])
                continue
            var found = False
            for entry in point:
                if entry[0] == pair[0]:
                    found = True
                    for _ in range(Int(pair[1])):
                        value = value.mul(entry[1].low, budget)
                    break
            if not found:
                raise PolyError(PolyErrorKind.DOMAIN, "rational specialization misses a variable")
        while len(coefficients) <= degree:
            _allocation[QQ](1, budget)
            coefficients.append(QQ.zero(NoContext()))
        coefficients[degree] = coefficients[degree].add(value, budget)
    return DensePoly[QQ].from_coefficients(0, NoContext(), coefficients^, budget)


def _integer_resultant(f: SparsePoly[QQ], g: SparsePoly[QQ], variable: Int64, mut budget: Budget) raises PolyError -> SparsePoly[QQ]:
    """The resultant, or for large bivariate inputs a rational multiple of it by the multimodular integer route."""
    if len(f.terms) + len(g.terms) < 24:
        return resultant_value(f, g, variable, budget)
    var used = f.variables(budget)
    for v in g.variables(budget):
        var known = False
        for u in used:
            if u == v:
                known = True
        if not known:
            used.append(v)
    if len(used) > 2:
        return resultant_value(f, g, variable, budget)
    return _rational_image(resultant_value(_integer_image(f, budget), _integer_image(g, budget), variable, budget), budget)


def _merge(mut result: List[Int], p: Int, mut budget: Budget) raises PolyError:
    for q in result:
        if q == p:
            return
    _allocation[Int](1, budget)
    result.append(p)


def _validate_variables(variables: List[Int64], mut budget: Budget) raises PolyError:
    for i in range(len(variables)):
        budget.charge(1)
        if variables[i] < 0:
            raise PolyError(PolyErrorKind.DOMAIN, "negative CAD variable")
        for j in range(i):
            budget.charge(1)
            if variables[i] == variables[j]:
                raise PolyError(PolyErrorKind.DOMAIN, "duplicate CAD variable")


def _ordered(inputs: List[SparsePoly[QQ]], mut budget: Budget) raises PolyError -> List[SparsePoly[QQ]]:
    _allocation[SparsePoly[QQ]](len(inputs), budget)
    var owned = List[SparsePoly[QQ]](capacity=len(inputs))
    for f in inputs:
        owned.append(f.reorder(MonomialOrder(), budget))
    return owned^


def _start(mut search: _Search, fixed: List[RealAlgebraic], mut budget: Budget) raises PolyError:
    """Install the root frame and the fixed prefix, each irrational value lifted by its own defining polynomial."""
    if len(fixed) > len(search.variables):
        raise PolyError(PolyErrorKind.DOMAIN, "CAD fixed prefix exceeds the variable count")
    search.frames.append(_PointFrame())
    search.caches.append(_NormalizationCache())
    search.root_cache.append(Dict[Int, _Roots]())
    for k in range(len(fixed)):
        budget.charge(1)
        if not _check_real(fixed[k], budget):
            raise PolyError(PolyErrorKind.DOMAIN, "invalid fixed CAD coordinate")
        # The canonical witness: an irreducible defining polynomial, or a rational.
        var value = _root_cached(fixed[k].polynomial, fixed[k].low, fixed[k].high, search.caches[k], budget) if not fixed[k].rational else _copy_real(fixed[k], budget)
        var lifting: Optional[SparsePoly[QQ]] = None
        if not value.rational:
            lifting = _embed_dense(value.polynomial, search.variables[k], budget)
        search._push(value, lifting, budget)


def _prefix_sign(f: SparsePoly[QQ], point: List[Tuple[Int64, RealAlgebraic]], mut budget: Budget) raises PolyError -> Int:
    """The exact sign of an input whose variables all lie in the point."""
    if f.is_zero():
        return 0
    if len(f.variables(budget)) == 0:
        return f.terms[0].coefficient.value.sign()
    return algebraic_sign(algebraic_evaluate_sparse(f, point, budget).value, budget).relation


def _allowed(mask: UInt8, sign: Int) -> Bool:
    return mask & (UInt8(1) << UInt8(sign + 1)) != 0


def _bound(item: Optional[_Bound]) -> Optional[CoveringBound]:
    if not item:
        return None
    return CoveringBound(item.value().polys[0], item.value().indices[0])


def _coverings(inputs: List[SparsePoly[QQ]], masks: List[UInt8], variables: List[Int64], fixed: List[RealAlgebraic], mut budget: Budget, lazard: Bool) raises PolyError -> CADCoveringsCertificate:
    _masks(inputs, masks, budget)
    _validate_variables(variables, budget)
    var search = _Search(_ordered(inputs, budget), masks.copy(), variables, lazard)
    for i in range(len(search.inputs)):
        budget.charge(1)
        search.levels.append(_level(search.inputs[i], variables, budget))
        var proof = factor_multivariate(search.inputs[i], budget)
        var found = List[Int]()
        search._register(proof, found, budget)
        search.factors.append(found^)
        _allocation[MultivariateFactorization[QQ]](1, budget)
        search.input_proofs.append(proof^)
    _start(search, fixed, budget)
    var none = List[CoveringNode]()
    var empty = List[RealAlgebraic]()
    for i in range(len(search.inputs)):
        budget.charge(1)
        if search.levels[i] < len(fixed) and not _allowed(masks[i], _prefix_sign(search.inputs[i], search.point, budget)):
            return CADCoveringsCertificate(variables.copy(), search.pool.copy(), search.input_proofs.copy(), List[MultivariateFactorization[QQ]](), none^, i, empty^, List[AlgebraicPolynomialEvaluation](), List[AlgebraicComparisonCertificate]())
    var root = -1
    if len(fixed) == len(variables):
        search.satisfiable = True
    else:
        search.recording = True
        root = search.search(len(fixed), budget)
    if search.satisfiable:
        var evaluations = List[AlgebraicPolynomialEvaluation]()
        var signs = List[AlgebraicComparisonCertificate]()
        var depth = len(search.point)
        _allocation[AlgebraicPolynomialEvaluation](len(inputs), budget)
        _allocation[AlgebraicComparisonCertificate](len(inputs), budget)
        for i in range(len(inputs)):
            budget.charge(1)
            var evaluation = _evaluate_sparse_cached(inputs[i], search.point, search.caches[depth], budget)
            var sign = algebraic_sign(evaluation.value, budget)
            if not _allowed(masks[i], sign.relation):
                raise PolyError(PolyErrorKind.DOMAIN, "coverings sample violates a constraint")
            evaluations.append(evaluation^)
            signs.append(sign^)
        var point = List[RealAlgebraic]()
        for entry in search.point:
            point.append(_copy_real(entry[1], budget))
        return CADCoveringsCertificate(variables.copy(), search.pool.copy(), search.input_proofs.copy(), List[MultivariateFactorization[QQ]](), none^, -1, point^, evaluations^, signs^)
    search.nodes[root].cover = search._cover(root, budget)
    # The reachable subcover tree, root first; parents precede children.
    var order: List[Int] = [root]
    var parents: List[Tuple[Int, Int]] = [(-1, -1)]
    var nodes = List[CoveringNode]()
    var cursor = 0
    while cursor < len(order):
        budget.charge(1)
        ref node = search.nodes[order[cursor]]
        var intervals = List[CoveringInterval]()
        for k in range(len(node.cover)):
            budget.charge(1)
            ref item = node.intervals[node.cover[k]]
            var child = -1
            if item.child >= 0:
                child = len(order)
                _allocation[Int](1, budget)
                order.append(item.child)
                parents.append((cursor, k))
            var polynomials = item.main.copy()
            for q in item.down:
                polynomials.append(q)
            _allocation[CoveringInterval](1, budget)
            intervals.append(CoveringInterval(_bound(item.lower), _bound(item.upper), item.lower_closed, item.upper_closed, _copy_real(item.sample, budget), item.constraint, child, polynomials^))
        _allocation[CoveringNode](1, budget)
        nodes.append(CoveringNode(parents[cursor][0], parents[cursor][1], node.level, intervals^))
        cursor += 1
    return CADCoveringsCertificate(variables.copy(), search.pool.copy(), search.input_proofs.copy(), search.projection_proofs.copy(), nodes^, -1, empty^, List[AlgebraicPolynomialEvaluation](), List[AlgebraicComparisonCertificate]())


def coverings_solve(inputs: List[SparsePoly[QQ]], masks: List[UInt8], variables: List[Int64], mut budget: Budget, lazard: Bool = True) raises PolyError -> CADCoveringsCertificate:
    """Decide a sign conjunction by a conflict-driven search over cylindrical algebraic coverings.

    The search assigns one coordinate at a time and stops at the first
    satisfying point. Otherwise every failed sample is generalized to an
    interval through local Lazard (or, with lazard False, McCallum)
    characterizations, and the result is a checkable covering tree.

    Args:
        inputs: The rational constraint polynomials.
        masks: Allowed sign bits per polynomial: one for negative, two for zero, four for positive.
        variables: Distinct variables in base-to-top cylindrical order, covering every input.
        budget: The shared work allowance.
        lazard: Whether to use Lazard characterizations; False selects McCallum's, which refuse nullification.

    Returns:
        A satisfying point with its input signs, or a covering proving that none exists.

    Raises:
        PolyError: DOMAIN for invalid inputs, UNSUPPORTED for McCallum nullification, LIMIT or CAPACITY on work limits.
    """
    return _coverings(inputs, masks, variables, List[RealAlgebraic](), budget, lazard)


# ------------------------------------------------------------------ checking


struct _Checker(Movable):
    """Recomputes every claim of a coverings certificate with the search's exact root and sign routines."""
    var machine: _Search
    var nodes: List[CoveringNode]
    var visited: List[Bool]
    var input_pool: List[List[Int]]
    var products: List[SparsePoly[QQ]]
    var product_pool: List[Optional[List[Int]]]
    var projections: List[MultivariateFactorization[QQ]]
    var own: Dict[Int, List[Int]]
    var pairs: Dict[Int, List[Int]]

    def __init__(out self, var machine: _Search, var nodes: List[CoveringNode]):
        self.machine = machine^
        self.nodes = nodes^
        self.visited = List[Bool](length=len(self.nodes), fill=False)
        self.input_pool = List[List[Int]]()
        self.products = List[SparsePoly[QQ]]()
        self.product_pool = List[Optional[List[Int]]]()
        self.projections = List[MultivariateFactorization[QQ]]()
        self.own = Dict[Int, List[Int]]()
        self.pairs = Dict[Int, List[Int]]()

    def _index(self, f: SparsePoly[QQ], mut budget: Budget) raises PolyError -> Int:
        for j in range(len(self.machine.pool)):
            budget.charge(1)
            if _equal(f, self.machine.pool[j], budget):
                return j
        return -1

    def _factors(mut self, f: SparsePoly[QQ], mut budget: Budget) raises PolyError -> List[Int]:
        """Pool indices of the nonconstant factors of f, through a supplied factorization of a multiple of f."""
        var result = List[Int]()
        if f.is_zero() or len(f.variables(budget)) == 0:
            return result^
        var normal = _monic(f, budget)
        var found = -1
        for i in range(len(self.products)):
            budget.charge(1)
            if _equal(normal, self.products[i], budget):
                found = i
                break
        if found < 0:
            raise PolyError(PolyErrorKind.DOMAIN, "missing projection factorization")
        if not self.product_pool[found]:
            var indices = List[Int]()
            for entry in self.projections[found].factors:
                budget.charge(1)
                var index = self._index(entry[0], budget)
                if index < 0:
                    if _level(entry[0], self.machine.variables, budget) >= 0:
                        raise PolyError(PolyErrorKind.DOMAIN, "projection factor missing from the polynomial list")
                    continue
                indices.append(index)
            self.product_pool[found] = indices^
        return self.product_pool[found].value().copy()

    def _projection(mut self, p: Int, mut budget: Budget) raises PolyError -> List[Int]:
        """Leading coefficient, trailing coefficient and discriminant factors; the discriminant must not vanish."""
        var known = self.own.get(p)
        if known:
            return known.value().copy()
        var f = self.machine.pool[p]._copy(budget)
        var variable = self.machine.variables[self.machine.pool_levels[p]]
        var result = self._factors(_lc(f, variable, budget), budget)
        for q in self._factors(_coefficient(f, variable, 0, budget), budget):
            _merge(result, q, budget)
        if f.degree_in(variable, budget) > 1:
            var discriminant = _integer_resultant(f, derivative(f, variable, budget), variable, budget)
            if discriminant.is_zero():
                raise PolyError(PolyErrorKind.DOMAIN, "characterization polynomial is not squarefree")
            for q in self._factors(discriminant, budget):
                _merge(result, q, budget)
        self.own[p] = result.copy()
        return result^

    def _resultant(mut self, p: Int, q: Int, mut budget: Budget) raises PolyError -> List[Int]:
        var key = min(p, q) * 1048576 + max(p, q)
        var known = self.pairs.get(key)
        if known:
            return known.value().copy()
        var variable = self.machine.variables[self.machine.pool_levels[p]]
        var result = self._factors(_integer_resultant(self.machine.pool[p], self.machine.pool[q], variable, budget), budget)
        self.pairs[key] = result.copy()
        return result^

    def _value(mut self, bound: CoveringBound, interval: CoveringInterval, level: Int, mut budget: Budget) raises PolyError -> RealAlgebraic:
        var p = bound.polynomial
        if p < 0 or p >= len(self.machine.pool) or self.machine.pool_levels[p] != level or not _contains(interval.polynomials, p):
            raise PolyError(PolyErrorKind.DOMAIN, "interval bound is not a root of its characterization")
        var found = self.machine._roots(p, budget)
        if bound.root < 0 or bound.root >= len(found.roots):
            raise PolyError(PolyErrorKind.DOMAIN, "interval bound root index out of range")
        return _copy_real(found.roots[bound.root], budget)

    def _characterization(mut self, node: Int, mut budget: Budget) raises PolyError -> List[Int]:
        """The polynomials one level down that keep the node's covering valid, recomputed (Algorithm 4)."""
        var level = self.nodes[node].level
        var intervals = self.nodes[node].intervals.copy()
        var result = List[Int]()
        for k in range(len(intervals)):
            budget.charge(1)
            ref item = intervals[k]
            for p in item.polynomials:
                budget.charge(1)
                if self.machine.pool_levels[p] < level:
                    _merge(result, p, budget)
                    continue
                for q in self._projection(p, budget):
                    _merge(result, q, budget)
                var found = self.machine._roots(p, budget)
                if item.lower and len(found.roots) and item.lower.value().polynomial != p:
                    var lower = self._value(item.lower.value(), item, level, budget)
                    if _compare(found.roots[0], lower, budget) <= 0:
                        for r in self._resultant(p, item.lower.value().polynomial, budget):
                            _merge(result, r, budget)
                if item.upper and len(found.roots) and item.upper.value().polynomial != p:
                    var upper = self._value(item.upper.value(), item, level, budget)
                    if _compare(found.roots[len(found.roots) - 1], upper, budget) >= 0:
                        for r in self._resultant(p, item.upper.value().polynomial, budget):
                            _merge(result, r, budget)
            if k + 1 < len(intervals):
                ref next = intervals[k + 1]
                if Bool(item.upper) and Bool(next.lower) and item.upper.value().polynomial != next.lower.value().polynomial:
                    for r in self._resultant(item.upper.value().polynomial, next.lower.value().polynomial, budget):
                        _merge(result, r, budget)
        return result^

    def check_node(mut self, node: Int, mut budget: Budget) raises PolyError -> Bool:
        if node < 0 or node >= len(self.nodes) or self.visited[node]:
            return False
        self.visited[node] = True
        var level = self.nodes[node].level
        if level != len(self.machine.point) or level >= len(self.machine.variables):
            return False
        var intervals = self.nodes[node].intervals.copy()
        if len(intervals) == 0:
            return False
        var uppers = List[Optional[RealAlgebraic]]()
        for k in range(len(intervals)):
            budget.charge(1)
            ref item = intervals[k]
            for p in item.polynomials:
                budget.charge(1)
                if p < 0 or p >= len(self.machine.pool) or self.machine.pool_levels[p] > level:
                    return False
            if not _check_real(item.sample, budget):
                return False
            var lower: Optional[RealAlgebraic] = None
            var upper: Optional[RealAlgebraic] = None
            if item.lower:
                lower = self._value(item.lower.value(), item, level, budget)
            if item.upper:
                upper = self._value(item.upper.value(), item, level, budget)
            var section = item.lower_closed or item.upper_closed
            if section:
                # A single section: both endpoints closed, equal, and the sample.
                if not item.lower_closed or not item.upper_closed or not lower or not upper:
                    return False
                if not _same_name(item.lower.value(), item.upper.value()) and _compare(lower.value(), upper.value(), budget) != 0:
                    return False
                if _compare(item.sample, lower.value(), budget) != 0:
                    return False
            else:
                if lower and _compare(lower.value(), item.sample, budget) >= 0:
                    return False
                if upper and _compare(item.sample, upper.value(), budget) >= 0:
                    return False
                # No characterization root strictly inside the open interval.
                for p in item.polynomials:
                    budget.charge(1)
                    if self.machine.pool_levels[p] != level:
                        continue
                    var found = self.machine._roots(p, budget)
                    for r in found.roots:
                        budget.charge(1)
                        if (not lower or _compare(lower.value(), r, budget) < 0) and (not upper or _compare(r, upper.value(), budget) < 0):
                            return False
            # Coverage: the line is covered from minus infinity through this interval.
            if k == 0:
                if lower:
                    return False
            else:
                ref before = intervals[k - 1]
                if not lower or not uppers[k - 1]:
                    return False
                var relation = 0 if Bool(before.upper) and _same_name(item.lower.value(), before.upper.value()) else _compare(lower.value(), uppers[k - 1].value(), budget)
                if relation > 0 or (relation == 0 and not before.upper_closed and not item.lower_closed):
                    return False
            uppers.append(upper.copy())
            if item.constraint >= 0 and item.child == -1:
                var c = item.constraint
                if c >= len(self.machine.inputs) or self.machine.levels[c] != level:
                    return False
                var mask = self.machine.masks[c]
                if mask != 0:
                    for q in self.input_pool[c]:
                        if not _contains(item.polynomials, q):
                            return False
                    if _allowed(mask, self.machine._sign(c, item.sample, budget)):
                        return False
            elif item.child >= 0 and item.constraint == -1:
                var child = item.child
                if child >= len(self.nodes) or self.nodes[child].parent != node or self.nodes[child].interval != k or self.nodes[child].level != level + 1:
                    return False
                # A section sample is lifted by its bound polynomial, which ties it
                # to the prefix; another irrational sample by its own polynomial.
                var lifting: Optional[SparsePoly[QQ]] = None
                if not item.sample.rational:
                    if section:
                        lifting = self.machine._roots(item.lower.value().polynomial, budget).lifting.copy()
                    else:
                        lifting = _embed_dense(item.sample.polynomial, self.machine.variables[level], budget)
                self.machine._push(item.sample, lifting, budget)
                if not self.check_node(child, budget):
                    return False
                var required = self._characterization(child, budget)
                self.machine._pop()
                for q in required:
                    if not _contains(item.polynomials, q):
                        return False
            else:
                return False
        return not uppers[len(uppers) - 1]


def _relation(a: _Bound, b: _Bound, mut budget: Budget) raises PolyError -> Int:
    """Compare two endpoints at one prefix; a shared root name decides equality without arithmetic."""
    for i in range(len(a.polys)):
        for j in range(len(b.polys)):
            budget.charge(1)
            if a.polys[i] == b.polys[j] and a.indices[i] == b.indices[j]:
                return 0
    return _compare(a.value, b.value, budget)


def _same_name(a: CoveringBound, b: CoveringBound) -> Bool:
    return a.polynomial == b.polynomial and a.root == b.root


def _contains(values: List[Int], value: Int) -> Bool:
    for v in values:
        if v == value:
            return True
    return False


def _monic(f: SparsePoly[QQ], mut budget: Budget) raises PolyError -> SparsePoly[QQ]:
    var ordered = f.reorder(MonomialOrder(), budget)
    return ordered.scale(ordered.terms[len(ordered.terms) - 1].coefficient.inverse(budget), budget)


def _product(proof: MultivariateFactorization[QQ], mut budget: Budget) raises PolyError -> SparsePoly[QQ]:
    var order = MonomialOrder()
    var total = SparsePoly[QQ].constant(proof.unit.copy(), order, budget)
    for entry in proof.factors:
        budget.charge(1)
        for _ in range(entry[1]):
            total = total.mul(entry[0].reorder(order, budget), budget)
    return total^


def _check_coverings(inputs: List[SparsePoly[QQ]], masks: List[UInt8], certificate: CADCoveringsCertificate, fixed: List[RealAlgebraic], mut budget: Budget) raises PolyError -> Bool:
    _masks(inputs, masks, budget)
    ref variables = certificate.variables
    _validate_variables(variables, budget)
    if len(fixed) > len(variables) or len(certificate.input_factors) != len(inputs):
        return False
    var machine = _Search(_ordered(inputs, budget), masks.copy(), variables)
    for i in range(len(machine.inputs)):
        budget.charge(1)
        machine.levels.append(_level(machine.inputs[i], variables, budget))
    for f in certificate.polynomials:
        budget.charge(1)
        f.check_invariants(budget)
        var level = _level(f, variables, budget)
        if level < 0 or f.order != MonomialOrder():
            return False
        machine.pool.append(f._copy(budget))
        machine.pool_levels.append(level)
        machine.projected.append(None)
    _start(machine, fixed, budget)
    if certificate.root_conflict >= 0:
        var c = certificate.root_conflict
        if c >= len(inputs) or len(certificate.nodes) or len(certificate.witness) or machine.levels[c] >= len(fixed):
            return False
        return not _allowed(masks[c], _prefix_sign(machine.inputs[c], machine.point, budget))
    if certificate.root_conflict != -1:
        return False
    if certificate.satisfiable():
        if len(certificate.witness) != len(variables) or len(certificate.evaluations) != len(inputs) or len(certificate.signs) != len(inputs):
            return False
        var point = List[Tuple[Int64, RealAlgebraic]]()
        for k in range(len(variables)):
            budget.charge(1)
            if not _check_real(certificate.witness[k], budget):
                return False
            if k < len(fixed) and _compare(certificate.witness[k], fixed[k], budget) != 0:
                return False
            point.append((variables[k], _copy_real(certificate.witness[k], budget)))
        var zero = _rational(QQ.zero(NoContext()), budget)
        for i in range(len(inputs)):
            budget.charge(1)
            if not check_algebraic_evaluate_sparse(inputs[i], point, certificate.evaluations[i], budget) or not _check_comparison(certificate.evaluations[i].value, zero, certificate.signs[i], budget) or not _allowed(masks[i], certificate.signs[i].relation):
                return False
        return True
    if len(certificate.witness) or len(certificate.evaluations) or len(certificate.signs):
        return False
    var checker = _Checker(machine^, certificate.nodes.copy())
    for i in range(len(inputs)):
        budget.charge(1)
        if not check_multivariate_factorization(checker.machine.inputs[i], certificate.input_factors[i], budget):
            return False
        var indices = List[Int]()
        for entry in certificate.input_factors[i].factors:
            budget.charge(1)
            var index = checker._index(entry[0], budget)
            if index < 0:
                return False
            indices.append(index)
        checker.input_pool.append(indices^)
    for proof in certificate.projections:
        budget.charge(1)
        _allocation[SparsePoly[QQ]](1, budget)
        checker.products.append(_monic(_product(proof, budget), budget))
        checker.product_pool.append(None)
        checker.projections.append(_copy_factorization(proof, budget))
    ref root = certificate.nodes[0]
    if root.parent != -1 or root.interval != -1 or root.level != len(fixed):
        return False
    return checker.check_node(0, budget)


def check_coverings(inputs: List[SparsePoly[QQ]], masks: List[UInt8], certificate: CADCoveringsCertificate, mut budget: Budget) raises PolyError -> Bool:
    """Verify a coverings certificate without searching or trusting the producer's choices.

    A witness is substituted exactly and every sign checked. A covering is
    replayed node by node: bounds are recomputed as roots at the node's
    prefix, intervals must contain their samples, cover the line, and hold no
    characterization root inside; conflicts are exact signs at the samples;
    and each child's Lazard projection is recomputed, its supplied
    factorizations checked by product, and every factor required in the
    parent interval's characterization.

    Args:
        inputs: The original polynomial constraints.
        masks: The original allowed-sign masks.
        certificate: The proposed witness or covering.
        budget: The shared work allowance.

    Returns:
        Whether the certificate proves its verdict.

    Raises:
        PolyError: DOMAIN for invalid masks, LIMIT or CAPACITY on work limits.
    """
    _masks(inputs, masks, budget)
    try:
        return _check_coverings(inputs, masks, certificate, List[RealAlgebraic](), budget)
    except e:
        if e.kind == PolyErrorKind.DOMAIN:
            return False
        raise e^
