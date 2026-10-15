"""Buchberger bases over packed exponent vectors.

This engine runs the algorithm of `groebner.groebner` step for step:
Gebauer–Möller installation, least-LCM pair selection with index tie breaks,
and reduction of every term by the first active basis element, in leading
monomial order, whose leading monomial divides it. It changes only storage.
Exponents sit in a fixed-width vector in the order's priority order, with the
total degree and a support bitmask cached beside them, so comparison,
multiplication, and divisibility take a few vector operations and no heap
allocation. Reduction merges translated basis tails through a heap, starting
S-polynomials from their two generators' tails instead of materializing them.

Over QQ the engine is fraction-free. Basis elements are primitive integer
polynomials with positive leading coefficients. Reducing a term with
coefficient c by an element with leading coefficient a scales the pending
polynomial by a / gcd(a, c) instead of dividing by a. Scaling never changes
which monomials are present, so every reduction makes the same choices as the
rational computation, each remainder is a nonzero integer multiple of the
rational remainder, and the final monic basis is identical. Integer
arithmetic avoids the gcd that normalizes every rational sum and product.
Scaling is lazy: pending cursors carry their own multipliers, and remainder
terms record how many scalings preceded them and are corrected once at the end.

`groebner` uses this engine for orders over at most `_LANES` variables when
no cofactors are tracked, and converts the basis back to sparse polynomials.
"""
from std.math import max
from apn_mojo import Integer, Rational
from .coefficients import CoefficientField, CoefficientRing, NoContext, QQ, ZZ, _work
from .errors import Budget, PolyError, PolyErrorKind, _allocation, _sum
from .monomial import Monomial, MonomialOrder
from .sparse import SparsePoly, Term
from ._coefficient_ops import _exact, _gcd_coefficient
from ._images import _denominator, _scaled_integer

comptime _LANES = 16
comptime _Exponents = SIMD[DType.uint32, _LANES]
comptime _POSITIONS = _Exponents(1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16)
comptime _BITS = _Exponents(1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096, 8192, 16384, 32768)
comptime _FRONTIER = 64
"""Integral reduction drains its heap into one base list at this many cursors, bounding rescaling work."""


@fieldwise_init
struct _Packed(ImplicitlyCopyable, Movable):
    """Exponents in priority order, their sum, and the set of positive lanes."""
    var exponents: _Exponents
    var degree: UInt64
    var support: UInt32


@always_inline
def _packed(exponents: _Exponents) -> _Packed:
    var support = UInt32(exponents.ne(_Exponents(0)).select(_BITS, _Exponents(0)).reduce_or())
    return _Packed(exponents, exponents.cast[DType.uint64]().reduce_add(), support)


@always_inline
def _mul(a: _Packed, b: _Packed) raises PolyError -> _Packed:
    var exponents = a.exponents + b.exponents
    if exponents.lt(a.exponents).reduce_or():
        raise PolyError(PolyErrorKind.CAPACITY, "monomial exponent overflow")
    return _Packed(exponents, a.degree + b.degree, a.support | b.support)


@always_inline
def _div(a: _Packed, b: _Packed) -> _Packed:
    """The quotient a / b; b must divide a."""
    return _packed(a.exponents - b.exponents)


@always_inline
def _lcm(a: _Packed, b: _Packed) -> _Packed:
    return _packed(max(a.exponents, b.exponents))


@always_inline
def _divides(a: _Packed, b: _Packed) -> Bool:
    return (a.support & ~b.support) == 0 and a.exponents.le(b.exponents).reduce_and()


@always_inline
def _equal(a: _Packed, b: _Packed) -> Bool:
    return not a.exponents.ne(b.exponents).reduce_or()


@always_inline
def _compare(kind: UInt8, a: _Packed, b: _Packed) -> Int:
    """Compare under LEX, GRLEX, or GREVLEX; lanes are in priority order."""
    if kind != MonomialOrder.LEX and a.degree != b.degree:
        return -1 if a.degree < b.degree else 1
    var differ = a.exponents.ne(b.exponents)
    if not differ.reduce_or():
        return 0
    if kind == MonomialOrder.GREVLEX:
        # The last differing lane decides, and the smaller exponent there is greater.
        var last = Int(differ.select(_POSITIONS, _Exponents(0)).reduce_max()) - 1
        return 1 if a.exponents[last] < b.exponents[last] else -1
    var first = Int(differ.select(_POSITIONS, _Exponents(_LANES + 1)).reduce_min()) - 1
    return 1 if a.exponents[first] > b.exponents[first] else -1


def _zero_monomial() -> _Packed:
    return _Packed(_Exponents(0), 0, 0)


@fieldwise_init
struct _Term[C: CoefficientRing](Copyable, Movable):
    var monomial: _Packed
    var coefficient: Self.C


@fieldwise_init
struct _Cursor[C: CoefficientRing](Copyable, Movable):
    """A translated basis tail, or the reduction base when `source` is -1.

    `unit` is 1 or -1 when the factor is that unit, so its terms are copied or
    negated instead of multiplied, and 0 for a general factor.
    """
    var source: Int
    var position: Int
    var shift: _Packed
    var factor: Self.C
    var unit: Int
    var term: _Term[Self.C]


@fieldwise_init
struct _Pair(ImplicitlyCopyable, Movable):
    var first: Int
    var second: Int
    var lcm: _Packed


def _unit[C: CoefficientRing](value: C, ring: C.Context, mut budget: Budget) raises PolyError -> Int:
    if value == C.one(ring):
        return 1
    if value == C.one(ring).neg(budget):
        return -1
    return 0


def _normalize[C: CoefficientRing, integral: Bool](mut p: List[_Term[C]], ring: C.Context, mut budget: Budget) raises PolyError:
    """Scale a nonzero polynomial, stored in increasing order, to its canonical associate.

    Over a field that is the monic polynomial. In integral mode it is the
    primitive polynomial with a positive leading coefficient.
    """
    var last = len(p) - 1
    comptime if integral:
        var content = C.zero(ring)
        for i in range(len(p)):
            budget.charge(1)
            content = _gcd_coefficient(content, p[i].coefficient, budget)
            if content == C.one(ring):
                break
        comptime if C == ZZ:
            if rebind[ZZ](p[last].coefficient).value.sign() < 0:
                content = content.neg(budget)
        if content == C.one(ring):
            return
        for i in range(len(p)):
            budget.charge(1)
            p[i].coefficient = _exact(p[i].coefficient, content, budget)
    elif conforms_to(C, CoefficientField):
        if p[last].coefficient == C.one(ring):
            return
        var inverse = p[last].coefficient.inverse(budget)
        for i in range(len(p)):
            budget.charge(1)
            p[i].coefficient = p[i].coefficient.mul(inverse, budget)
    else:
        raise PolyError(PolyErrorKind.UNSUPPORTED, "packed Groebner bases need a field or integral mode")


def _priorities(order: MonomialOrder, mut budget: Budget) raises PolyError -> List[Int]:
    """Lanes sorted by their variable index, for writing canonical monomials."""
    var n = len(order.variables)
    _allocation[Int](n, budget)
    var by_index = List[Int](capacity=n)
    for lane in range(n):
        budget.charge(1)
        var position = len(by_index)
        by_index.append(lane)
        while position > 0 and order.variables[by_index[position - 1]] > order.variables[lane]:
            by_index[position] = by_index[position - 1]
            position -= 1
        by_index[position] = lane
    return by_index^


def _pack[C: CoefficientRing](p: SparsePoly[C], order: MonomialOrder, mut budget: Budget) raises PolyError -> List[_Term[C]]:
    """Terms of p, which uses `order`, as packed terms in the same increasing order."""
    _allocation[_Term[C]](len(p.terms), budget)
    var terms = List[_Term[C]](capacity=len(p.terms))
    for t in p.terms:
        budget.charge(1)
        var exponents = _Exponents(0)
        for pair in t.monomial.pairs:
            budget.charge(1)
            var lane = -1
            for k in range(len(order.variables)):
                if order.variables[k] == pair[0]:
                    lane = k
                    break
            if lane < 0:
                raise PolyError(PolyErrorKind.DOMAIN, "variable absent from order")
            exponents[lane] = pair[1]
        terms.append(_Term[C](_packed(exponents), t.coefficient.copy()))
    return terms^


def _monomial(packed: _Packed, order: MonomialOrder, by_index: List[Int], mut budget: Budget) raises PolyError -> Monomial:
    var pairs = List[Tuple[Int64, UInt32]]()
    for lane in by_index:
        var e = packed.exponents[lane]
        if e:
            pairs.append((order.variables[lane], e))
    _allocation[Tuple[Int64, UInt32]](len(pairs), budget)
    var monomial = Monomial()
    monomial.pairs = pairs^
    return monomial^


def _unpack[C: CoefficientRing](terms: List[_Term[C]], order: MonomialOrder, ring: C.Context, by_index: List[Int], mut budget: Budget) raises PolyError -> SparsePoly[C]:
    _allocation[Term[C]](len(terms), budget)
    var result = SparsePoly[C].zero(order, ring, budget)
    result.terms.reserve(len(terms))
    for t in terms:
        budget.charge(1)
        result.terms.append(Term[C](_monomial(t.monomial, order, by_index, budget), t.coefficient.copy()))
    return result^


struct _Engine[C: CoefficientRing, integral: Bool](Movable):
    var kind: UInt8
    var ring: Self.C.Context
    var polys: List[List[_Term[Self.C]]]
    """Basis elements: terms in increasing order and normalized, leading term last."""
    var leads: List[_Packed]
    var active: List[Int]
    var pairs: List[_Pair]

    def __init__(out self, kind: UInt8, ring: Self.C.Context):
        self.kind = kind
        self.ring = ring.copy()
        self.polys = List[List[_Term[Self.C]]]()
        self.leads = List[_Packed]()
        self.active = List[Int]()
        self.pairs = List[_Pair]()

    @always_inline
    def _placeholder(self) -> _Term[Self.C]:
        return _Term[Self.C](_zero_monomial(), Self.C.zero(self.ring))

    # ------------------------------------------------------------- reduction

    @always_inline
    def _before(self, cursors: List[_Cursor[Self.C]], a: Int, b: Int) -> Bool:
        return _compare(self.kind, cursors[a].term.monomial, cursors[b].term.monomial) > 0

    def _sift_down(self, mut heap: List[Int], cursors: List[_Cursor[Self.C]], mut budget: Budget) raises PolyError:
        var position = 0
        var value = heap[0]
        while 2 * position + 1 < len(heap):
            budget.charge(1)
            var child = 2 * position + 1
            if child + 1 < len(heap) and self._before(cursors, heap[child + 1], heap[child]):
                child += 1
            if not self._before(cursors, heap[child], value):
                break
            heap[position] = heap[child]
            position = child
        heap[position] = value

    def _sift_up(self, mut heap: List[Int], cursors: List[_Cursor[Self.C]], mut budget: Budget) raises PolyError:
        var position = len(heap) - 1
        var value = heap[position]
        while position > 0:
            budget.charge(1)
            var parent = (position - 1) // 2
            if not self._before(cursors, value, heap[parent]):
                break
            heap[position] = heap[parent]
            position = parent
        heap[position] = value

    def _load(self, mut cursor: _Cursor[Self.C], mut base: List[_Term[Self.C]], mut budget: Budget) raises PolyError:
        """Compute the cursor's current term from its source position."""
        if cursor.source < 0:
            # The base is consumed once, in order: move its coefficient out.
            cursor.term.monomial = base[cursor.position].monomial
            swap(cursor.term.coefficient, base[cursor.position].coefficient)
            if cursor.unit == 0:
                cursor.term.coefficient = cursor.term.coefficient.mul(cursor.factor, budget)
            elif cursor.unit < 0:
                cursor.term.coefficient = cursor.term.coefficient.neg(budget)
            return
        ref t = self.polys[cursor.source][cursor.position]
        var monomial = _mul(t.monomial, cursor.shift)
        if cursor.unit > 0:
            cursor.term = _Term[Self.C](monomial, t.coefficient.copy())
        elif cursor.unit < 0:
            cursor.term = _Term[Self.C](monomial, t.coefficient.neg(budget))
        else:
            cursor.term = _Term[Self.C](monomial, t.coefficient.mul(cursor.factor, budget))

    def _push(self, var cursor: _Cursor[Self.C], mut heap: List[Int], mut cursors: List[_Cursor[Self.C]], mut free: List[Int], mut base: List[_Term[Self.C]], mut budget: Budget) raises PolyError:
        if cursor.position < 0:
            return
        self._load(cursor, base, budget)
        var slot: Int
        if len(free):
            slot = free.pop()
            cursors[slot] = cursor^
        else:
            _allocation[_Cursor[Self.C]](1, budget)
            slot = len(cursors)
            cursors.append(cursor^)
        heap.append(slot)
        self._sift_up(heap, cursors, budget)

    def _advance_top(self, mut heap: List[Int], mut cursors: List[_Cursor[Self.C]], mut free: List[Int], mut base: List[_Term[Self.C]], mut budget: Budget) raises PolyError:
        var slot = heap[0]
        cursors[slot].position -= 1
        if cursors[slot].position >= 0:
            self._load(cursors[slot], base, budget)
        else:
            free.append(slot)
            var last = heap.pop()
            if len(heap) == 0:
                return
            heap[0] = last
        self._sift_down(heap, cursors, budget)

    def _next(self, mut heap: List[Int], mut cursors: List[_Cursor[Self.C]], mut free: List[Int], mut base: List[_Term[Self.C]], mut budget: Budget) raises PolyError -> _Term[Self.C]:
        """Pop the greatest pending monomial with the sum of its coefficients, possibly zero."""
        budget.charge(1)
        var top = self._placeholder()
        swap(top, cursors[heap[0]].term)
        self._advance_top(heap, cursors, free, base, budget)
        while len(heap) and _equal(cursors[heap[0]].term.monomial, top.monomial):
            budget.charge(1)
            top.coefficient = top.coefficient.add(cursors[heap[0]].term.coefficient, budget)
            self._advance_top(heap, cursors, free, base, budget)
        return top^

    def _drain(self, mut heap: List[Int], mut cursors: List[_Cursor[Self.C]], mut free: List[Int], mut base: List[_Term[Self.C]], mut budget: Budget) raises PolyError -> List[_Term[Self.C]]:
        """Collect every pending term, unreduced, in increasing order, and empty the heap."""
        var drained = List[_Term[Self.C]]()
        while len(heap):
            var top = self._next(heap, cursors, free, base, budget)
            if not top.coefficient.is_zero():
                _allocation[_Term[Self.C]](1, budget)
                drained.append(top^)
        drained.reverse()
        cursors = List[_Cursor[Self.C]]()
        free = List[Int]()
        return drained^

    def _scale(self, scale: Self.C, heap: List[Int], mut cursors: List[_Cursor[Self.C]], mut budget: Budget) raises PolyError:
        """Multiply everything pending by `scale`: each live cursor's factor and current term."""
        for slot in heap:
            budget.charge(1)
            ref cursor = cursors[slot]
            if cursor.unit != 0:
                cursor.factor = scale.copy() if cursor.unit > 0 else scale.neg(budget)
                cursor.unit = 0
            else:
                cursor.factor = cursor.factor.mul(scale, budget)
            cursor.term.coefficient = cursor.term.coefficient.mul(scale, budget)

    def reduce(self, var base: List[_Term[Self.C]], var starts: List[_Cursor[Self.C]], indices: List[Int], mut budget: Budget) raises PolyError -> List[_Term[Self.C]]:
        """Fully reduce the sum of the starting cursors against `indices`, in that order.

        Returns the remainder with terms in increasing order. In integral mode
        the result is a nonzero integer multiple of the field remainder.
        """
        var cursors = List[_Cursor[Self.C]]()
        var heap = List[Int]()
        var free = List[Int]()
        for i in range(len(starts)):
            var cursor = _Cursor[Self.C](starts[i].source, starts[i].position, starts[i].shift, starts[i].factor.copy(), starts[i].unit, self._placeholder())
            self._push(cursor^, heap, cursors, free, base, budget)
        var remainder = List[_Term[Self.C]]()
        # Integral mode: the successive scalings of everything pending, and how
        # many of them preceded each remainder term.
        var scales = List[Self.C]()
        var epochs = List[Int]()
        while len(heap):
            var top = self._next(heap, cursors, free, base, budget)
            if top.coefficient.is_zero():
                continue
            var reducer = -1
            for i in indices:
                budget.charge(1)
                if _divides(self.leads[i], top.monomial):
                    reducer = i
                    break
            if reducer < 0:
                _allocation[_Term[Self.C]](1, budget)
                remainder.append(top^)
                comptime if Self.integral:
                    epochs.append(len(scales))
                continue
            var factor: Self.C
            comptime if Self.integral:
                # Scale everything pending by a / g so that a | the scaled coefficient.
                ref lead = self.polys[reducer][len(self.polys[reducer]) - 1].coefficient
                var common = _gcd_coefficient(lead, top.coefficient, budget)
                var scale = _exact(lead, common, budget)
                factor = _exact(top.coefficient, common, budget).neg(budget)
                if scale != Self.C.one(self.ring):
                    if len(heap) >= _FRONTIER:
                        var drained = self._drain(heap, cursors, free, base, budget)
                        base = drained^
                        var restart = _Cursor[Self.C](-1, len(base) - 1, _zero_monomial(), Self.C.one(self.ring), 1, self._placeholder())
                        self._push(restart^, heap, cursors, free, base, budget)
                    self._scale(scale, heap, cursors, budget)
                    _allocation[Self.C](1, budget)
                    scales.append(scale^)
            else:
                # Basis elements are monic: subtract c * (m / lead) * g.
                factor = top.coefficient.neg(budget)
            var unit = _unit(factor, self.ring, budget)
            var cursor = _Cursor[Self.C](reducer, len(self.polys[reducer]) - 2, _div(top.monomial, self.leads[reducer]), factor^, unit, self._placeholder())
            self._push(cursor^, heap, cursors, free, base, budget)
        comptime if Self.integral:
            # Remainder terms missed the scalings that came after them.
            var multiplier = Self.C.one(self.ring)
            var applied = len(scales)
            for j in range(len(remainder) - 1, -1, -1):
                budget.charge(1)
                while applied > epochs[j]:
                    multiplier = multiplier.mul(scales[applied - 1], budget)
                    applied -= 1
                if applied < len(scales):
                    remainder[j].coefficient = remainder[j].coefficient.mul(multiplier, budget)
        remainder.reverse()
        return remainder^

    def reduce_base(self, var base: List[_Term[Self.C]], indices: List[Int], mut budget: Budget) raises PolyError -> List[_Term[Self.C]]:
        var starts = List[_Cursor[Self.C]]()
        starts.append(_Cursor[Self.C](-1, len(base) - 1, _zero_monomial(), Self.C.one(self.ring), 1, self._placeholder()))
        return self.reduce(base^, starts^, indices, budget)

    def reduce_pair(self, pair: _Pair, mut budget: Budget) raises PolyError -> List[_Term[Self.C]]:
        """Reduce the S-polynomial of a pair, merging both translated tails directly."""
        var left: Self.C
        var right: Self.C
        comptime if Self.integral:
            ref a = self.polys[pair.first][len(self.polys[pair.first]) - 1].coefficient
            ref b = self.polys[pair.second][len(self.polys[pair.second]) - 1].coefficient
            var common = _gcd_coefficient(a, b, budget)
            left = _exact(b, common, budget)
            right = _exact(a, common, budget).neg(budget)
        else:
            left = Self.C.one(self.ring)
            right = left.neg(budget)
        var left_unit = _unit(left, self.ring, budget)
        var right_unit = _unit(right, self.ring, budget)
        var starts = List[_Cursor[Self.C]]()
        starts.append(_Cursor[Self.C](pair.first, len(self.polys[pair.first]) - 2, _div(pair.lcm, self.leads[pair.first]), left^, left_unit, self._placeholder()))
        starts.append(_Cursor[Self.C](pair.second, len(self.polys[pair.second]) - 2, _div(pair.lcm, self.leads[pair.second]), right^, right_unit, self._placeholder()))
        return self.reduce(List[_Term[Self.C]](), starts^, self.active, budget)

    # ------------------------------------------------------- pair bookkeeping

    def sort_active(mut self, mut budget: Budget) raises PolyError:
        for i in range(1, len(self.active)):
            budget.charge(1)
            var value = self.active[i]
            var j = i
            while j > 0 and _compare(self.kind, self.leads[value], self.leads[self.active[j - 1]]) < 0:
                self.active[j] = self.active[j - 1]
                j -= 1
            self.active[j] = value

    def install(mut self, index: Int, mut budget: Budget) raises PolyError:
        # Gebauer–Möller installation exactly as in groebner._install.
        var mh = self.leads[index]
        _allocation[_Packed](len(self.active), budget)
        var lcms = List[_Packed](capacity=len(self.active))
        for old in self.active:
            budget.charge(1)
            lcms.append(_lcm(mh, self.leads[old]))
        _allocation[Int](len(self.active), budget)
        var kept = List[Int](capacity=len(self.active))
        for i in range(len(self.active)):
            budget.charge(1)
            var product = _equal(_mul(mh, self.leads[self.active[i]]), lcms[i])
            var redundant = False
            if not product:
                for j in range(i + 1, len(self.active)):
                    budget.charge(1)
                    if _divides(lcms[j], lcms[i]):
                        redundant = True
                        break
                if not redundant:
                    for j in kept:
                        budget.charge(1)
                        if _divides(lcms[j], lcms[i]):
                            redundant = True
                            break
            if not redundant:
                kept.append(i)
        _allocation[_Pair](_sum(len(self.pairs), len(kept)), budget)
        var next_pairs = List[_Pair](capacity=_sum(len(self.pairs), len(kept)))
        for pair in self.pairs:
            budget.charge(1)
            if not _divides(mh, pair.lcm) or _equal(_lcm(mh, self.leads[pair.first]), pair.lcm) or _equal(_lcm(mh, self.leads[pair.second]), pair.lcm):
                next_pairs.append(pair)
        for i in kept:
            budget.charge(1)
            if not _equal(_mul(mh, self.leads[self.active[i]]), lcms[i]):
                next_pairs.append(_Pair(min(index, self.active[i]), max(index, self.active[i]), lcms[i]))
        self.pairs = next_pairs^
        _allocation[Int](_sum(len(self.active), 1), budget)
        var next_active = List[Int](capacity=_sum(len(self.active), 1))
        for old in self.active:
            budget.charge(1)
            if not _divides(mh, self.leads[old]):
                next_active.append(old)
        next_active.append(index)
        self.active = next_active^

    @always_inline
    def _pair_before(self, a: _Pair, b: _Pair) -> Bool:
        var comparison = _compare(self.kind, a.lcm, b.lcm)
        return comparison < 0 or (comparison == 0 and (a.first < b.first or (a.first == b.first and a.second < b.second)))

    def _sift_pairs(mut self, start: Int, mut budget: Budget) raises PolyError:
        var value = self.pairs[start]
        var position = start
        while position < len(self.pairs) // 2:
            budget.charge(1)
            var child = position * 2 + 1
            if child + 1 < len(self.pairs) and self._pair_before(self.pairs[child + 1], self.pairs[child]):
                child += 1
            if not self._pair_before(self.pairs[child], value):
                break
            self.pairs[position] = self.pairs[child]
            position = child
        self.pairs[position] = value

    def heapify_pairs(mut self, mut budget: Budget) raises PolyError:
        for i in range(len(self.pairs) // 2 - 1, -1, -1):
            budget.charge(1)
            self._sift_pairs(i, budget)

    def select(mut self, mut budget: Budget) raises PolyError -> _Pair:
        var selected = self.pairs.pop()
        if len(self.pairs):
            var root = self.pairs[0]
            self.pairs[0] = selected
            selected = root
            self._sift_pairs(0, budget)
        return selected

    def insert(mut self, var p: List[_Term[Self.C]], mut budget: Budget) raises PolyError:
        """Normalize p, add it to the basis, and install its pairs."""
        _normalize[Self.C, Self.integral](p, self.ring, budget)
        _allocation[List[_Term[Self.C]]](1, budget)
        self.leads.append(p[len(p) - 1].monomial)
        self.polys.append(p^)
        self.install(len(self.polys) - 1, budget)
        self.heapify_pairs(budget)

    def run(mut self, var generators: List[List[_Term[Self.C]]], mut budget: Budget) raises PolyError -> List[List[_Term[Self.C]]]:
        """Buchberger's loop; returns the reduced basis, normalized, in decreasing leading-monomial order."""
        for i in range(len(generators)):
            budget.charge(1)
            if len(generators[i]) == 0:
                continue
            var p = List[_Term[Self.C]]()
            swap(p, generators[i])
            var reduced = self.reduce_base(p^, self.active, budget)
            if len(reduced) == 0:
                continue
            self.insert(reduced^, budget)
        var dirty_order = True
        while len(self.pairs):
            budget.charge(1)
            var pair = self.select(budget)
            if dirty_order:
                self.sort_active(budget)
                dirty_order = False
            var reduced = self.reduce_pair(pair, budget)
            if len(reduced) == 0:
                continue
            self.insert(reduced^, budget)
            dirty_order = True
        self.sort_active(budget)
        _allocation[List[_Term[Self.C]]](len(self.active), budget)
        var basis = List[List[_Term[Self.C]]](capacity=len(self.active))
        # Active leading monomials are mutually nondividing, so reducing each tail
        # against the others keeps every leading term and yields the reduced basis.
        for position in range(len(self.active) - 1, -1, -1):
            budget.charge(1)
            var index = self.active[position]
            _allocation[Int](len(self.active) - 1, budget)
            var others = List[Int](capacity=len(self.active) - 1)
            for j in self.active:
                budget.charge(1)
                if j != index:
                    others.append(j)
            _allocation[_Term[Self.C]](len(self.polys[index]), budget)
            var copy = List[_Term[Self.C]](capacity=len(self.polys[index]))
            for t in self.polys[index]:
                copy.append(_Term[Self.C](t.monomial, t.coefficient.copy()))
            var reduced = self.reduce_base(copy^, others, budget)
            _normalize[Self.C, Self.integral](reduced, self.ring, budget)
            basis.append(reduced^)
        return basis^


def _packed_groebner[C: CoefficientField](generators: List[SparsePoly[C]], order: MonomialOrder, mut budget: Budget) raises PolyError -> List[SparsePoly[C]]:
    """The reduced monic basis, in decreasing leading-monomial order; generators share a field."""
    if len(generators) == 0:
        return List[SparsePoly[C]]()
    var ring = generators[0].ring.copy()
    _allocation[List[_Term[C]]](len(generators), budget)
    var packed = List[List[_Term[C]]](capacity=len(generators))
    for g in generators:
        budget.charge(1)
        packed.append(_pack(g.reorder(order, budget), order, budget))
    var engine = _Engine[C, False](order.kind, ring)
    var basis = engine.run(packed^, budget)
    var by_index = _priorities(order, budget)
    _allocation[SparsePoly[C]](len(basis), budget)
    var result = List[SparsePoly[C]](capacity=len(basis))
    for p in basis:
        budget.charge(1)
        result.append(_unpack(p, order, ring, by_index, budget))
    return result^


def _packed_groebner_rational(generators: List[SparsePoly[QQ]], order: MonomialOrder, mut budget: Budget) raises PolyError -> List[SparsePoly[QQ]]:
    """The reduced monic basis over QQ, computed fraction-free over ZZ."""
    if len(generators) == 0:
        return List[SparsePoly[QQ]]()
    _allocation[List[_Term[ZZ]]](len(generators), budget)
    var integral = List[List[_Term[ZZ]]](capacity=len(generators))
    for g in generators:
        budget.charge(1)
        var rational = _pack(g.reorder(order, budget), order, budget)
        # Clear denominators; the engine normalizes each input before use.
        var common = Integer(1)
        for t in rational:
            budget.charge(1)
            common = _denominator(common, t.coefficient, budget)
        _allocation[_Term[ZZ]](len(rational), budget)
        var terms = List[_Term[ZZ]](capacity=len(rational))
        for t in rational:
            budget.charge(1)
            terms.append(_Term[ZZ](t.monomial, _scaled_integer(t.coefficient, common, budget)))
        integral.append(terms^)
    var engine = _Engine[ZZ, True](order.kind, NoContext())
    var basis = engine.run(integral^, budget)
    var by_index = _priorities(order, budget)
    _allocation[SparsePoly[QQ]](len(basis), budget)
    var result = List[SparsePoly[QQ]](capacity=len(basis))
    for p in basis:
        budget.charge(1)
        # The primitive element divided by its leading coefficient is the monic one.
        ref lead = p[len(p) - 1].coefficient.value
        _allocation[Term[QQ]](len(p), budget)
        var monic = SparsePoly[QQ].zero(order, NoContext(), budget)
        monic.terms.reserve(len(p))
        for t in p:
            budget.charge(1)
            _work(t.coefficient.size(), p[len(p) - 1].coefficient.size(), True, budget)
            var value: Rational
            try:
                value = Rational(t.coefficient.value.copy(), lead.copy())
            except e:
                raise PolyError(PolyErrorKind.CAPACITY, String(e))
            monic.terms.append(Term[QQ](_monomial(t.monomial, order, by_index, budget), QQ(value^)))
        result.append(monic^)
    return result^


def _packed_supported(order: MonomialOrder) -> Bool:
    return order.kind != MonomialOrder.KERNEL and len(order.variables) <= _LANES
