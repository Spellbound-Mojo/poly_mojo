"""Buchberger bases over packed exponent vectors.

This engine runs the algorithm of `groebner.groebner` step for step:
Gebauer–Möller installation, least-LCM pair selection with index tie breaks,
and reduction of every term by the first active basis element, in leading
monomial order, whose leading monomial divides it. It changes only storage.
Exponents sit in a fixed-width vector in the order's priority order, with the
total degree and a support bitmask cached beside them, so comparison,
multiplication, and divisibility take a few vector operations and no heap
allocation. The width is 8 lanes for up to 8 variables and 16 otherwise.

The polynomial being reduced lives in geobuckets: sorted term lists whose
capacities grow by a factor of four. A reduction step adds the translated
reducer tail to the smallest bucket that can hold it and merges upward when a
bucket overflows, so every term is touched a logarithmic number of times, in
sequential merges. The leading term is the greatest of the bucket tops.

Over a prime field the reducer tail is multiplied while it is merged, so a
step allocates only the merged list. Residues are multiplied by a factor with
a precomputed quotient (Shoup's method) instead of a division, and added
without the field check of `ModInt`, since every coefficient shares one field.
Work is charged per merge and per divisor search rather than per operation.

Over QQ the engine is fraction-free. Basis elements are primitive integer
polynomials with positive leading coefficients. Reducing a term with
coefficient c by an element with leading coefficient a scales the pending
polynomial by a / gcd(a, c) instead of dividing by a. Scaling never changes
which monomials are present, so every reduction makes the same choices as the
rational computation, each remainder is a nonzero integer multiple of the
rational remainder, and the final monic basis is identical. Integer
arithmetic avoids the gcd that normalizes every rational sum and product.
Scaling is lazy: each bucket carries a multiplier that is applied when it is
next merged, and remainder terms record how many scalings preceded them and
are corrected once at the end.

`groebner` uses this engine for orders over at most 16 variables when no
cofactors are tracked, and converts the basis back to sparse polynomials.
"""
from std.bit import pop_count
from std.math import iota, max, min
from apn_mojo import Integer, Rational
from .coefficients import CoefficientField, CoefficientRing, ModInt, NoContext, QQ, ZZ, _work
from .errors import Budget, PolyError, PolyErrorKind, _allocation, _sum
from .monomial import Monomial, MonomialOrder
from .sparse import SparsePoly, Term
from ._coefficient_ops import _exact, _gcd_coefficient
from ._images import _denominator, _scaled_integer

comptime _MAX_LANES = 16


struct _Packed[W: Int](ImplicitlyCopyable, Movable):
    """Exponents in priority order, their sum, and the set of positive lanes.

    The exponents are stored as two half-width vectors: a full-width vector
    would align, and so pad, the struct to the vector's width, while a plain
    array would split vector loads across cache lines.
    """
    var low: SIMD[DType.uint32, Self.W // 2]
    var high: SIMD[DType.uint32, Self.W // 2]
    var degree: UInt64
    var support: UInt32

    @always_inline
    def __init__(out self, exponents: SIMD[DType.uint32, Self.W], degree: UInt64, support: UInt32):
        var halves = exponents.split()
        self.low = rebind[SIMD[DType.uint32, Self.W // 2]](halves[0])
        self.high = rebind[SIMD[DType.uint32, Self.W // 2]](halves[1])
        self.degree = degree
        self.support = support

    @always_inline
    def exponents(self) -> SIMD[DType.uint32, Self.W]:
        return rebind[SIMD[DType.uint32, Self.W]](self.low.join(self.high))


@always_inline
def _packed[W: Int](exponents: SIMD[DType.uint32, W]) -> _Packed[W]:
    comptime bits = SIMD[DType.uint32, W](1) << iota[DType.uint32, W]()
    var support = UInt32(exponents.ne(SIMD[DType.uint32, W](0)).select(bits, SIMD[DType.uint32, W](0)).reduce_or())
    return _Packed[W](exponents, exponents.cast[DType.uint64]().reduce_add(), support)


@always_inline
def _mul[W: Int](a: _Packed[W], b: _Packed[W]) raises PolyError -> _Packed[W]:
    var left = a.exponents()
    var exponents = left + b.exponents()
    if exponents.lt(left).reduce_or():
        raise PolyError(PolyErrorKind.CAPACITY, "monomial exponent overflow")
    return _Packed[W](exponents, a.degree + b.degree, a.support | b.support)


@always_inline
def _div[W: Int](a: _Packed[W], b: _Packed[W]) -> _Packed[W]:
    """The quotient a / b; b must divide a."""
    return _packed(a.exponents() - b.exponents())


@always_inline
def _lcm[W: Int](a: _Packed[W], b: _Packed[W]) -> _Packed[W]:
    return _packed(max(a.exponents(), b.exponents()))


@always_inline
def _divides[W: Int](a: _Packed[W], b: _Packed[W]) -> Bool:
    return (a.support & ~b.support) == 0 and a.exponents().le(b.exponents()).reduce_and()


@always_inline
def _equal[W: Int](a: _Packed[W], b: _Packed[W]) -> Bool:
    return not a.exponents().ne(b.exponents()).reduce_or()


@always_inline
def _compare[W: Int](kind: UInt8, a: _Packed[W], b: _Packed[W]) -> Int:
    """Compare under LEX, GRLEX, or GREVLEX; lanes are in priority order."""
    comptime positions = iota[DType.uint32, W]() + 1
    if kind != MonomialOrder.LEX and a.degree != b.degree:
        return -1 if a.degree < b.degree else 1
    var differ = a.exponents().ne(b.exponents())
    if not differ.reduce_or():
        return 0
    if kind == MonomialOrder.GREVLEX:
        # The last differing lane decides, and the smaller exponent there is greater.
        var last = Int(differ.select(positions, SIMD[DType.uint32, W](0)).reduce_max()) - 1
        return 1 if a.exponents()[last] < b.exponents()[last] else -1
    var first = Int(differ.select(positions, SIMD[DType.uint32, W](W + 1)).reduce_min()) - 1
    return 1 if a.exponents()[first] > b.exponents()[first] else -1


@always_inline
def _add[C: CoefficientRing](a: C, b: C, mut budget: Budget) raises PolyError -> C:
    """The sum a + b; the caller has charged for it.

    All coefficients in the engine share one ring, so residues are added
    directly, without the field check and charge of `ModInt.add`.
    """
    comptime if C == ModInt:
        ref x = rebind[ModInt](a)
        var sum = x.value + rebind[ModInt](b).value  # < 2p < 2^63; cannot overflow.
        return rebind_var[C](x._with_residue(sum - x.modulus if sum >= x.modulus else sum))
    else:
        return a.add(b, budget)


@fieldwise_init
struct _Shoup(ImplicitlyCopyable, Movable):
    """A residue factor w with floor(w * 2^64 / p), for multiplying by w without division.

    For a, w < p < 2^63, q = floor(a * quotient / 2^64) leaves a * w - q * p in [0, 2p).
    """
    var factor: UInt64
    var quotient: UInt64
    var modulus: UInt64

    @staticmethod
    def of(w: ModInt) -> _Shoup:
        return _Shoup(w.value, UInt64((UInt128(w.value) << 64) // UInt128(w.modulus)), w.modulus)

    @always_inline
    def times(self, a: UInt64) -> UInt64:
        var q = UInt64((UInt128(a) * UInt128(self.quotient)) >> 64)
        var r = a * self.factor - q * self.modulus  # Exact modulo 2^64, and below 2p.
        return r - self.modulus if r >= self.modulus else r


@fieldwise_init
struct _Term[C: CoefficientRing, W: Int](Copyable, Movable):
    var monomial: _Packed[Self.W]
    var coefficient: Self.C


@fieldwise_init
struct _Pair[W: Int](ImplicitlyCopyable, Movable):
    var first: Int
    var second: Int
    var lcm: _Packed[Self.W]


def _unit[C: CoefficientRing](value: C, ring: C.Context, mut budget: Budget) raises PolyError -> Int:
    if value == C.one(ring):
        return 1
    if value == C.one(ring).neg(budget):
        return -1
    return 0


def _normalize[C: CoefficientRing, W: Int, integral: Bool](mut p: List[_Term[C, W]], ring: C.Context, mut budget: Budget) raises PolyError:
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


def _pack[C: CoefficientRing, W: Int](p: SparsePoly[C], order: MonomialOrder, mut budget: Budget) raises PolyError -> List[_Term[C, W]]:
    """Terms of p, which uses `order`, as packed terms in the same increasing order."""
    _allocation[_Term[C, W]](len(p.terms), budget)
    var terms = List[_Term[C, W]](capacity=len(p.terms))
    for t in p.terms:
        budget.charge(1)
        var exponents = SIMD[DType.uint32, W](0)
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
        terms.append(_Term[C, W](_packed(exponents), t.coefficient.copy()))
    return terms^


def _monomial[W: Int](packed: _Packed[W], order: MonomialOrder, by_index: List[Int], mut budget: Budget) raises PolyError -> Monomial:
    var exponents = packed.exponents()
    var pairs = List[Tuple[Int64, UInt32]](capacity=Int(pop_count(packed.support)))
    for lane in by_index:
        var e = exponents[lane]
        if e:
            pairs.append((order.variables[lane], e))
    _allocation[Tuple[Int64, UInt32]](len(pairs), budget)
    var monomial = Monomial()
    monomial.pairs = pairs^
    return monomial^


def _unpack[C: CoefficientRing, W: Int](terms: List[_Term[C, W]], order: MonomialOrder, ring: C.Context, by_index: List[Int], mut budget: Budget) raises PolyError -> SparsePoly[C]:
    _allocation[Term[C]](len(terms), budget)
    var result = SparsePoly[C].zero(order, ring, budget)
    result.terms.reserve(len(terms))
    for t in terms:
        budget.charge(1)
        result.terms.append(Term[C](_monomial(t.monomial, order, by_index, budget), t.coefficient.copy()))
    return result^


@always_inline
def _capacity(level: Int) -> Int:
    """Bucket capacities 8, 32, 128, ...: each level holds four times the last."""
    return 8 << (2 * level)


struct _Buckets[C: CoefficientRing, W: Int, integral: Bool](Movable):
    """A polynomial as geobuckets: increasing term lists, leading terms last.

    In integral mode the polynomial is the sum of each bucket's terms times
    that bucket's multiplier; `units` marks multipliers equal to one.
    """
    var kind: UInt8
    var ring: Self.C.Context
    var levels: List[List[_Term[Self.C, Self.W]]]
    var multipliers: List[Self.C]
    var units: List[Bool]

    def __init__(out self, kind: UInt8, ring: Self.C.Context):
        self.kind = kind
        self.ring = ring.copy()
        self.levels = List[List[_Term[Self.C, Self.W]]]()
        self.multipliers = List[Self.C]()
        self.units = List[Bool]()

    def _merge(self, var a: List[_Term[Self.C, Self.W]], var b: List[_Term[Self.C, Self.W]], mut budget: Budget) raises PolyError -> List[_Term[Self.C, Self.W]]:
        """Merge two increasing term lists, adding equal monomials and dropping zeros."""
        var total = _sum(len(a), len(b))
        budget.charge(UInt64(total))
        _allocation[_Term[Self.C, Self.W]](total, budget)
        var result = List[_Term[Self.C, Self.W]](capacity=total)
        comptime if Self.C == ModInt:
            # Residue terms copy without allocation: merge forward, smallest first.
            var i = 0
            var j = 0
            while i < len(a) and j < len(b):
                ref x = a.unsafe_get(i)
                ref y = b.unsafe_get(j)
                var comparison = _compare(self.kind, x.monomial, y.monomial)
                if comparison < 0:
                    result.append(x.copy())
                    i += 1
                elif comparison > 0:
                    result.append(y.copy())
                    j += 1
                else:
                    var sum = _add(x.coefficient, y.coefficient, budget)
                    if not sum.is_zero():
                        result.append(_Term[Self.C, Self.W](x.monomial, sum^))
                    i += 1
                    j += 1
            while i < len(a):
                result.append(a.unsafe_get(i).copy())
                i += 1
            while j < len(b):
                result.append(b.unsafe_get(j).copy())
                j += 1
            return result^
        while len(a) and len(b):
            var comparison = _compare(self.kind, a[len(a) - 1].monomial, b[len(b) - 1].monomial)
            if comparison > 0:
                result.append(a.pop())
            elif comparison < 0:
                result.append(b.pop())
            else:
                var x = a.pop()
                var y = b.pop()
                x.coefficient = _add(x.coefficient, y.coefficient, budget)
                if not x.coefficient.is_zero():
                    result.append(x^)
        while len(a):
            result.append(a.pop())
        while len(b):
            result.append(b.pop())
        result.reverse()
        return result^

    def _apply_multiplier(mut self, level: Int, mut budget: Budget) raises PolyError:
        comptime if Self.integral:
            if self.units[level]:
                return
            for i in range(len(self.levels[level])):
                budget.charge(1)
                self.levels[level][i].coefficient = self.levels[level][i].coefficient.mul(self.multipliers[level], budget)
            self.multipliers[level] = Self.C.one(self.ring)
            self.units[level] = True

    def _level_for(mut self, length: Int, mut budget: Budget) raises PolyError -> Int:
        """The smallest level that can hold `length` terms, created if missing."""
        var level = 0
        while _capacity(level) < length:
            level += 1
        while len(self.levels) <= level:
            _allocation[List[_Term[Self.C, Self.W]]](1, budget)
            self.levels.append(List[_Term[Self.C, Self.W]]())
            self.multipliers.append(Self.C.one(self.ring))
            self.units.append(True)
        return level

    def add(mut self, var terms: List[_Term[Self.C, Self.W]], mut budget: Budget) raises PolyError:
        """Add an increasing term list to the polynomial."""
        if len(terms) == 0:
            return
        self._carry(self._level_for(len(terms), budget), terms^, budget)

    def _carry(mut self, start: Int, var terms: List[_Term[Self.C, Self.W]], mut budget: Budget) raises PolyError:
        """Merge `terms` into level `start`, moving overflowing results upward."""
        var level = start
        while True:
            if len(self.levels) <= level:
                _ = self._level_for(_capacity(level), budget)
            self._apply_multiplier(level, budget)
            var held = List[_Term[Self.C, Self.W]]()
            swap(held, self.levels[level])
            var merged = self._merge(held^, terms^, budget)
            if len(merged) <= _capacity(level):
                self.levels[level] = merged^
                return
            terms = merged^
            level += 1

    def add_multiple(mut self, source: List[_Term[Self.C, Self.W]], shift: _Packed[Self.W], factor: ModInt, mut budget: Budget) raises PolyError:
        """Add the tail of `source` times shift * factor, multiplying while merging.

        Residue products need no allocation of their own, so the multiple goes
        straight into a bucket instead of through an intermediate list.
        """
        comptime assert Self.C == ModInt and not Self.integral, "residue multiples only"
        var n = len(source) - 1
        if n <= 0:
            return
        budget.charge(UInt64(n))
        var level = self._level_for(n, budget)
        var held = List[_Term[Self.C, Self.W]]()
        swap(held, self.levels[level])
        var total = _sum(len(held), n)
        budget.charge(UInt64(total))
        _allocation[_Term[Self.C, Self.W]](total, budget)
        var result = List[_Term[Self.C, Self.W]](capacity=total)
        var shoup = _Shoup.of(factor)
        var i = 0
        for j in range(n):
            ref t = source.unsafe_get(j)
            var monomial = _mul(t.monomial, shift)
            var comparison = -1
            while i < len(held):
                comparison = _compare(self.kind, held.unsafe_get(i).monomial, monomial)
                if comparison >= 0:
                    break
                result.append(held.unsafe_get(i).copy())
                i += 1
            var value = shoup.times(rebind[ModInt](t.coefficient).value)
            if i < len(held) and comparison == 0:
                ref x = rebind[ModInt](held.unsafe_get(i).coefficient)
                var sum = x.value + value  # < 2p < 2^63; cannot overflow.
                if sum >= x.modulus:
                    sum -= x.modulus
                if sum:
                    result.append(_Term[Self.C, Self.W](monomial, rebind_var[Self.C](x._with_residue(sum))))
                i += 1
            else:
                result.append(_Term[Self.C, Self.W](monomial, rebind_var[Self.C](factor._with_residue(value))))
        while i < len(held):
            result.append(held.unsafe_get(i).copy())
            i += 1
        if len(result) <= _capacity(level):
            self.levels[level] = result^
            return
        self._carry(level + 1, result^, budget)

    def scale(mut self, factor: Self.C, mut budget: Budget) raises PolyError:
        """Multiply the polynomial by `factor`, lazily, through the bucket multipliers."""
        for level in range(len(self.levels)):
            budget.charge(1)
            if len(self.levels[level]) == 0:
                continue
            self.multipliers[level] = self.multipliers[level].mul(factor, budget)
            self.units[level] = False

    def leading(mut self, mut budget: Budget) raises PolyError -> Optional[_Term[Self.C, Self.W]]:
        """Remove and return the leading term, skipping monomials whose contributions cancel."""
        while True:
            var best = -1
            for level in range(len(self.levels)):
                budget.charge(1)
                ref bucket = self.levels[level]
                if len(bucket) == 0:
                    continue
                if best < 0 or _compare(self.kind, bucket[len(bucket) - 1].monomial, self.levels[best][len(self.levels[best]) - 1].monomial) > 0:
                    best = level
            if best < 0:
                return None
            var top = self._pop(best, budget)
            for level in range(best + 1, len(self.levels)):
                ref bucket = self.levels[level]
                if len(bucket) and _equal(bucket[len(bucket) - 1].monomial, top.monomial):
                    var other = self._pop(level, budget)
                    budget.charge(1)
                    top.coefficient = _add(top.coefficient, other.coefficient, budget)
            if not top.coefficient.is_zero():
                return top^

    def _pop(mut self, level: Int, mut budget: Budget) raises PolyError -> _Term[Self.C, Self.W]:
        var term = self.levels[level].pop()
        comptime if Self.integral:
            if not self.units[level]:
                term.coefficient = term.coefficient.mul(self.multipliers[level], budget)
        return term^


struct _Engine[C: CoefficientRing, W: Int, integral: Bool](Movable):
    var kind: UInt8
    var ring: Self.C.Context
    var polys: List[List[_Term[Self.C, Self.W]]]
    """Basis elements: terms in increasing order and normalized, leading term last."""
    var leads: List[_Packed[Self.W]]
    var active: List[Int]
    var pairs: List[_Pair[Self.W]]

    def __init__(out self, kind: UInt8, ring: Self.C.Context):
        self.kind = kind
        self.ring = ring.copy()
        self.polys = List[List[_Term[Self.C, Self.W]]]()
        self.leads = List[_Packed[Self.W]]()
        self.active = List[Int]()
        self.pairs = List[_Pair[Self.W]]()

    # ------------------------------------------------------------- reduction

    def _multiple(self, source: Int, shift: _Packed[Self.W], factor: Self.C, mut budget: Budget) raises PolyError -> List[_Term[Self.C, Self.W]]:
        """The tail of basis element `source` times shift * factor, in increasing order."""
        ref p = self.polys[source]
        var n = len(p) - 1
        budget.charge(UInt64(n))
        _allocation[_Term[Self.C, Self.W]](n, budget)
        var result = List[_Term[Self.C, Self.W]](capacity=n)
        var unit = _unit(factor, self.ring, budget)
        for i in range(n):
            ref t = p[i]
            var monomial = _mul(t.monomial, shift)
            if unit > 0:
                result.append(_Term[Self.C, Self.W](monomial, t.coefficient.copy()))
            elif unit < 0:
                result.append(_Term[Self.C, Self.W](monomial, t.coefficient.neg(budget)))
            else:
                result.append(_Term[Self.C, Self.W](monomial, t.coefficient.mul(factor, budget)))
        return result^

    def reduce(self, var pending: _Buckets[Self.C, Self.W, Self.integral], indices: List[Int], mut budget: Budget) raises PolyError -> List[_Term[Self.C, Self.W]]:
        """Fully reduce the pending polynomial against `indices`, in that order.

        Returns the remainder with terms in increasing order. In integral mode
        the result is a nonzero integer multiple of the field remainder.
        """
        var remainder = List[_Term[Self.C, Self.W]]()
        # Integral mode: the successive scalings of everything pending, and how
        # many of them preceded each remainder term.
        var scales = List[Self.C]()
        var epochs = List[Int]()
        while True:
            var next = pending.leading(budget)
            if not next:
                break
            var top = next.take()
            var reducer = -1
            var checked = 0
            for i in indices:
                checked += 1
                if _divides(self.leads[i], top.monomial):
                    reducer = i
                    break
            budget.charge(UInt64(checked))
            if reducer < 0:
                _allocation[_Term[Self.C, Self.W]](1, budget)
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
                    pending.scale(scale, budget)
                    _allocation[Self.C](1, budget)
                    scales.append(scale^)
            else:
                # Basis elements are monic: subtract c * (m / lead) * g.
                factor = top.coefficient.neg(budget)
            var shift = _div(top.monomial, self.leads[reducer])
            comptime if Self.C == ModInt:
                pending.add_multiple(self.polys[reducer], shift, rebind[ModInt](factor), budget)
            else:
                pending.add(self._multiple(reducer, shift, factor, budget), budget)
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

    def reduces_to_zero(self, var pending: _Buckets[Self.C, Self.W, Self.integral], indices: List[Int], mut budget: Budget) raises PolyError -> Bool:
        """Whether the pending polynomial reduces to zero against `indices`.

        Stops at the first term no leading monomial divides, with no remainder
        to keep. In integral mode the pending polynomial is scaled as in
        `reduce`; a nonzero multiple reduces to zero exactly when it does.
        """
        while True:
            var next = pending.leading(budget)
            if not next:
                return True
            var top = next.take()
            var reducer = -1
            var checked = 0
            for i in indices:
                checked += 1
                if _divides(self.leads[i], top.monomial):
                    reducer = i
                    break
            budget.charge(UInt64(checked))
            if reducer < 0:
                return False
            var factor: Self.C
            comptime if Self.integral:
                ref lead = self.polys[reducer][len(self.polys[reducer]) - 1].coefficient
                var common = _gcd_coefficient(lead, top.coefficient, budget)
                var scale = _exact(lead, common, budget)
                factor = _exact(top.coefficient, common, budget).neg(budget)
                if scale != Self.C.one(self.ring):
                    pending.scale(scale, budget)
            else:
                factor = top.coefficient.neg(budget)
            var shift = _div(top.monomial, self.leads[reducer])
            comptime if Self.C == ModInt:
                pending.add_multiple(self.polys[reducer], shift, rebind[ModInt](factor), budget)
            else:
                pending.add(self._multiple(reducer, shift, factor, budget), budget)

    def reduce_base(self, var base: List[_Term[Self.C, Self.W]], indices: List[Int], mut budget: Budget) raises PolyError -> List[_Term[Self.C, Self.W]]:
        var pending = _Buckets[Self.C, Self.W, Self.integral](self.kind, self.ring)
        pending.add(base^, budget)
        return self.reduce(pending^, indices, budget)

    def reduce_pair(self, pair: _Pair[Self.W], mut budget: Budget) raises PolyError -> List[_Term[Self.C, Self.W]]:
        """Reduce the S-polynomial of a pair, built from the two translated tails."""
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
        var pending = _Buckets[Self.C, Self.W, Self.integral](self.kind, self.ring)
        comptime if Self.C == ModInt:
            pending.add_multiple(self.polys[pair.first], _div(pair.lcm, self.leads[pair.first]), rebind[ModInt](left), budget)
            pending.add_multiple(self.polys[pair.second], _div(pair.lcm, self.leads[pair.second]), rebind[ModInt](right), budget)
        else:
            pending.add(self._multiple(pair.first, _div(pair.lcm, self.leads[pair.first]), left, budget), budget)
            pending.add(self._multiple(pair.second, _div(pair.lcm, self.leads[pair.second]), right, budget), budget)
        return self.reduce(pending^, self.active, budget)

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
        _allocation[_Packed[Self.W]](len(self.active), budget)
        var lcms = List[_Packed[Self.W]](capacity=len(self.active))
        # The supports and degrees apart, to rule out most divisions cheaply.
        _allocation[UInt64](len(self.active), budget)
        var keys = List[UInt64](capacity=len(self.active) + 8)
        for old in self.active:
            budget.charge(1)
            var lcm = _lcm(mh, self.leads[old])
            keys.append((lcm.degree << 32) | UInt64(lcm.support))
            lcms.append(lcm)
        # Padding no key passes: its degree exceeds every degree.
        for _ in range(8):
            keys.append(UInt64.MAX)
        _allocation[Int](len(self.active), budget)
        var kept = List[Int](capacity=len(self.active))
        var count = len(self.active)
        for i in range(count):
            budget.charge(1)
            var product = _equal(_mul(mh, self.leads[self.active[i]]), lcms[i])
            var redundant = False
            if not product:
                var key = keys.unsafe_get(i)
                var degree = key >> 32
                var outside = ~key & 0xFFFFFFFF
                var j = i + 1
                while j < count:
                    # Eight keys at a time; the first that passes and divides counts.
                    var block = keys.unsafe_ptr().unsafe_offset(j).unsafe_load[width=8]()
                    var passing = (block >> 32).le(degree) & (block & outside).eq(0)
                    if passing.reduce_or():
                        for k in range(min(8, count - j)):
                            if passing[k] and _divides(lcms.unsafe_get(j + k), lcms.unsafe_get(i)):
                                redundant = True
                                j += k
                                break
                        if redundant:
                            break
                    j += 8
                budget.charge(UInt64(min(j + 1, count) - (i + 1)))
                if not redundant:
                    for j in kept:
                        budget.charge(1)
                        if _divides(lcms[j], lcms[i]):
                            redundant = True
                            break
            if not redundant:
                kept.append(i)
        _allocation[_Pair[Self.W]](_sum(len(self.pairs), len(kept)), budget)
        var next_pairs = List[_Pair[Self.W]](capacity=_sum(len(self.pairs), len(kept)))
        for pair in self.pairs:
            budget.charge(1)
            if not _divides(mh, pair.lcm) or _equal(_lcm(mh, self.leads[pair.first]), pair.lcm) or _equal(_lcm(mh, self.leads[pair.second]), pair.lcm):
                next_pairs.append(pair)
        for i in kept:
            budget.charge(1)
            if not _equal(_mul(mh, self.leads[self.active[i]]), lcms[i]):
                next_pairs.append(_Pair[Self.W](min(index, self.active[i]), max(index, self.active[i]), lcms[i]))
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
    def _pair_before(self, a: _Pair[Self.W], b: _Pair[Self.W]) -> Bool:
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

    def select(mut self, mut budget: Budget) raises PolyError -> _Pair[Self.W]:
        var selected = self.pairs.pop()
        if len(self.pairs):
            var root = self.pairs[0]
            self.pairs[0] = selected
            selected = root
            self._sift_pairs(0, budget)
        return selected

    def insert(mut self, var p: List[_Term[Self.C, Self.W]], mut budget: Budget, heap: Bool = True) raises PolyError:
        """Normalize p, add it to the basis, and install its pairs.

        Without `heap` the pairs are left unordered, for a caller that
        inserts several elements and then calls `heapify_pairs` once.
        """
        _normalize[Self.C, Self.W, Self.integral](p, self.ring, budget)
        _allocation[List[_Term[Self.C, Self.W]]](1, budget)
        self.leads.append(p[len(p) - 1].monomial)
        self.polys.append(p^)
        self.install(len(self.polys) - 1, budget)
        if heap:
            self.heapify_pairs(budget)

    def start(mut self, var generators: List[List[_Term[Self.C, Self.W]]], mut budget: Budget) raises PolyError:
        """Reduce each generator against the basis so far and insert the nonzero ones."""
        for i in range(len(generators)):
            budget.charge(1)
            if len(generators[i]) == 0:
                continue
            var p = List[_Term[Self.C, Self.W]]()
            swap(p, generators[i])
            var reduced = self.reduce_base(p^, self.active, budget)
            if len(reduced) == 0:
                continue
            self.insert(reduced^, budget)

    def finish(mut self, mut budget: Budget) raises PolyError -> List[List[_Term[Self.C, Self.W]]]:
        """The reduced basis, normalized, in decreasing leading-monomial order."""
        self.sort_active(budget)
        _allocation[List[_Term[Self.C, Self.W]]](len(self.active), budget)
        var basis = List[List[_Term[Self.C, Self.W]]](capacity=len(self.active))
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
            _allocation[_Term[Self.C, Self.W]](len(self.polys[index]), budget)
            var copy = List[_Term[Self.C, Self.W]](capacity=len(self.polys[index]))
            for t in self.polys[index]:
                copy.append(_Term[Self.C, Self.W](t.monomial, t.coefficient.copy()))
            var reduced = self.reduce_base(copy^, others, budget)
            _normalize[Self.C, Self.W, Self.integral](reduced, self.ring, budget)
            basis.append(reduced^)
        return basis^

    def run(mut self, var generators: List[List[_Term[Self.C, Self.W]]], mut budget: Budget) raises PolyError -> List[List[_Term[Self.C, Self.W]]]:
        """Buchberger's loop; returns the reduced basis, normalized, in decreasing leading-monomial order."""
        self.start(generators^, budget)
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
        return self.finish(budget)


def _field_basis[C: CoefficientField, W: Int](generators: List[SparsePoly[C]], order: MonomialOrder, mut budget: Budget) raises PolyError -> List[SparsePoly[C]]:
    var ring = generators[0].ring.copy()
    _allocation[List[_Term[C, W]]](len(generators), budget)
    var packed = List[List[_Term[C, W]]](capacity=len(generators))
    for g in generators:
        budget.charge(1)
        packed.append(_pack[C, W](g.reorder(order, budget), order, budget))
    var engine = _Engine[C, W, False](order.kind, ring)
    var basis = engine.run(packed^, budget)
    var by_index = _priorities(order, budget)
    _allocation[SparsePoly[C]](len(basis), budget)
    var result = List[SparsePoly[C]](capacity=len(basis))
    for p in basis:
        budget.charge(1)
        result.append(_unpack(p, order, ring, by_index, budget))
    return result^


def _packed_groebner[C: CoefficientField](generators: List[SparsePoly[C]], order: MonomialOrder, mut budget: Budget) raises PolyError -> List[SparsePoly[C]]:
    """The reduced monic basis, in decreasing leading-monomial order; generators share a field."""
    if len(generators) == 0:
        return List[SparsePoly[C]]()
    if len(order.variables) <= 8:
        return _field_basis[C, 8](generators, order, budget)
    return _field_basis[C, 16](generators, order, budget)


def _rational_basis[W: Int](generators: List[SparsePoly[QQ]], order: MonomialOrder, mut budget: Budget) raises PolyError -> List[SparsePoly[QQ]]:
    _allocation[List[_Term[ZZ, W]]](len(generators), budget)
    var integral = List[List[_Term[ZZ, W]]](capacity=len(generators))
    for g in generators:
        budget.charge(1)
        var rational = _pack[QQ, W](g.reorder(order, budget), order, budget)
        # Clear denominators; the engine normalizes each input before use.
        var common = Integer(1)
        for t in rational:
            budget.charge(1)
            common = _denominator(common, t.coefficient, budget)
        _allocation[_Term[ZZ, W]](len(rational), budget)
        var terms = List[_Term[ZZ, W]](capacity=len(rational))
        for t in rational:
            budget.charge(1)
            terms.append(_Term[ZZ, W](t.monomial, _scaled_integer(t.coefficient, common, budget)))
        integral.append(terms^)
    var engine = _Engine[ZZ, W, True](order.kind, NoContext())
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


def _packed_groebner_rational(generators: List[SparsePoly[QQ]], order: MonomialOrder, mut budget: Budget) raises PolyError -> List[SparsePoly[QQ]]:
    """The reduced monic basis over QQ, computed fraction-free over ZZ."""
    if len(generators) == 0:
        return List[SparsePoly[QQ]]()
    if len(order.variables) <= 8:
        return _rational_basis[8](generators, order, budget)
    return _rational_basis[16](generators, order, budget)


def _packed_supported(order: MonomialOrder) -> Bool:
    return order.kind != MonomialOrder.KERNEL and len(order.variables) <= _MAX_LANES
