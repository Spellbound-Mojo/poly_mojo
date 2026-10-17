"""F4 over prime fields below 2^31, on packed exponent vectors.

Faugère's F4 replaces Buchberger's one-at-a-time S-polynomial reduction with
linear algebra: each round selects every pending pair whose LCM has the least
degree, writes both halves of each S-polynomial as rows, adds a reducer row
for every monomial a basis element's leading monomial divides (symbolic
preprocessing), and row-reduces the resulting sparse matrix. Rows whose
leading monomial no pivot covers are new basis elements; they are reduced by
one another too, so each round's new elements are in reduced row echelon
form, which keeps the rows they later contribute sparse. Pairs are still
pruned by the Gebauer–Möller criteria of the packed engine, which also stores
the basis and computes the final reduced basis; the reduced basis is unique,
so the result is the one Buchberger's algorithm returns.

Every row is a multiple of a basis element, so a row stores only its column
numbers, concatenated with the other rows'; its residues are the element's,
kept once. Monomials become matrix columns through a hash table; the hash is
linear in the exponents, with pseudo-random multipliers, so a product's hash
is the sum of its factors' and each basis element's term hashes are computed
once. Rows are reduced in a dense accumulator of 64-bit words, which is
reduced modulo p only when an entry is read: below 2^16 the products of
residues fit in 32 bits and plain sums cannot overflow; below 2^31 they fit in
62 bits and each entry stays below p^2 by one conditional subtraction. The
accumulator skips runs of zero words eight at a time. Rows that are not pivots
are reduced `_BLOCK` at a time, one per SIMD lane: neighbouring rows need
nearly the same pivots, so each pivot entry updates every lane in one vector
operation, and a row that leads in a new column is subtracted from the rows
after it at once, which gives each row exactly what reducing them one after
another gives. The final reduced basis is computed by one more matrix, whose
rows are the basis elements and their reducers.

A run can be recorded (`_f4_learn`) and replayed modulo another prime
(`_f4_replay`): the replay reduces only the recorded rows that gave new
elements, against the recorded pivots, with no pairs, symbolic
preprocessing, or rows that reduced to zero, and declines as soon as a row
leads elsewhere or a result leaves its recorded support. A replay can also run
modulo `_LANES` primes at once (`_f4_replay_lanes`): the recorded matrices are
the same for every prime, so each accumulator column holds a residue per
prime in one SIMD vector, and every update is one vector operation.
`_f4_replay_bases` leaves those bases as residues on the recorded supports.

`groebner` uses F4 for untracked bases over primes below 2^31 under GRLEX and
GREVLEX, over at most sixteen variables; other cases use Buchberger's
algorithm in the packed or sparse engine.
"""
from std.bit import count_leading_zeros
from std.math import iota, max, min
from std.sys.intrinsics import prefetch, PrefetchOptions
from .coefficients import CoefficientRing, ModInt, Modulus
from .errors import Budget, PolyError, PolyErrorKind, _allocation, _product, _sum
from .monomial import MonomialOrder
from .sparse import SparsePoly
from ._packed_groebner import _Engine, _Packed, _Term, _compare, _div, _divides, _equal, _mul, _pack, _packed, _priorities, _unpack

comptime _F4_PRIME_LIMIT = UInt64(1) << 31
comptime _COLUMN_LIMIT = Int(Int32.MAX)
comptime _TAG = UInt64(0xFFFFFFFF00000000)
"""The bits of a hash slot that hold the high half of the monomial's mixed hash."""
comptime _WIDE = UInt64(0x80000000)
"""The bit of a hash slot that marks a monomial with an exponent of 256 or more."""
comptime _NUMBER = UInt64(0x7FFFFFFF)
"""The bits of a hash slot that hold one more than the monomial's number."""


comptime _MULTIPLIERS = SIMD[DType.uint64, 16](
    0x09F1FD9D03F0A9B5, 0x553274161BBF8475, 0x5D5BCA4696B343B3, 0x70D29B6C7D22528D,
    0x0BF2B716F9915475, 0x5EB7F92B95387CCB, 0x296CD0F2C21D7F91, 0x1289A69805C125B1,
    0xDAA27FB8DACB9E73, 0x3ED08D59CB3F4727, 0x58A5F17B6C15C659, 0x651AC042FA7B481B,
    0x22AF6AEAA88E8DCD, 0x2D2BAE64640ABFB9, 0xAD0E83A710231B07, 0x9D30FF2169D91F13,
)
"""Odd pseudo-random multipliers, one per lane. Multipliers in arithmetic
progression would give every pair of monomials with the same degree and the
same index-weighted exponent sum, such as x0*x2 and x1^2, the same hash."""


@always_inline
def _raw_hash[W: Int](m: _Packed[W]) -> UInt64:
    """A hash linear in the exponents, so a product's is the sum of its factors'."""
    return (m.exponents().cast[DType.uint64]() * _MULTIPLIERS.slice[W]()).reduce_add()


@always_inline
def _mix(raw: UInt64) -> UInt64:
    var h = raw ^ (raw >> 31)
    h *= 0xBF58476D1CE4E5B9
    return h ^ (h >> 29)


@always_inline
def _times[W: Int](a: _Packed[W], b: _Packed[W]) -> _Packed[W]:
    """The product a * b, where no exponent overflows."""
    return _Packed[W](a.exponents() + b.exponents(), a.degree + b.degree, a.support | b.support)


struct _Store[W: Int](Movable):
    """Each basis element's term hashes, exponent bytes, and, over a prime field, residues, leading term first."""
    var hashes: List[List[UInt64]]
    var keys: List[List[SIMD[DType.uint8, Self.W]]]
    """Each term's exponents truncated to bytes, exact when its element's `tops` are below 256."""
    var values: List[List[UInt32]]
    var tops: List[_Packed[Self.W]]
    """The greatest exponent of each variable among each element's terms."""

    def __init__(out self):
        self.hashes = List[List[UInt64]]()
        self.keys = List[List[SIMD[DType.uint8, Self.W]]]()
        self.values = List[List[UInt32]]()
        self.tops = List[_Packed[Self.W]]()

    def extend[C: CoefficientRing, integral: Bool](mut self, engine: _Engine[C, Self.W, integral], mut budget: Budget) raises PolyError:
        """Add the elements inserted since the last call; residues only over a prime field."""
        for i in range(len(self.hashes), len(engine.polys)):
            ref p = engine.polys[i]
            var n = len(p)
            budget.charge(UInt64(n))
            _allocation[UInt64](n, budget)
            _allocation[SIMD[DType.uint8, Self.W]](n, budget)
            _allocation[UInt32](n, budget)
            var h = List[UInt64](capacity=n)
            var e = List[SIMD[DType.uint8, Self.W]](capacity=n)
            var v = List[UInt32](capacity=n)
            var top = SIMD[DType.uint32, Self.W](0)
            for k in range(n - 1, -1, -1):
                ref t = p[k]
                h.append(_raw_hash(t.monomial))
                e.append(t.monomial.exponents().cast[DType.uint8]())
                comptime if C == ModInt:
                    v.append(UInt32(rebind[ModInt](t.coefficient).value))
                top = max(top, t.monomial.exponents())
            self.hashes.append(h^)
            self.keys.append(e^)
            self.values.append(v^)
            self.tops.append(_packed(top))

    def release[C: CoefficientRing, integral: Bool](self, mut engine: _Engine[C, Self.W, integral]):
        """Drop the engine's term lists of stored elements whose exponents are below 256: `add_row` needs only their hashes and exponent bytes."""
        for i in range(len(self.hashes)):
            if self.tops[i].exponents().reduce_max() < 256:
                engine.polys[i] = List[_Term[C, Self.W]]()


struct _Columns[W: Int](Movable):
    """Distinct monomials, numbered in order of first appearance, with a hash index.

    A monomial whose exponents are all below 256 is narrow: its exponent
    bytes (`keys`), a sixth of its record, decide equality with another
    narrow one. The table is probed for every term of every row, and the
    keys, unlike the records, stay in cache.
    """
    var monomials: List[_Packed[Self.W]]
    var keys: List[SIMD[DType.uint8, Self.W]]
    """Each monomial's exponents truncated to bytes."""
    var covered: List[Bool]
    """Whether some row leads with the monomial."""
    var slots: List[UInt64]
    """Open addressing: 0 is empty, otherwise the high half of the monomial's
    mixed hash, over `_WIDE` unless it is narrow, over one more than its
    number."""
    var mask: Int

    def __init__(out self):
        self.monomials = List[_Packed[Self.W]]()
        self.keys = List[SIMD[DType.uint8, Self.W]]()
        self.covered = List[Bool]()
        self.slots = List[UInt64](length=1024, fill=0)
        self.mask = 1023

    def reserve(mut self, count: Int, mut budget: Budget) raises PolyError:
        """Make room for `count` more monomials, keeping the table at most half full."""
        var total = _sum(len(self.monomials), count)
        if total > _COLUMN_LIMIT:
            raise PolyError(PolyErrorKind.CAPACITY, "F4 matrix column count overflow")
        _allocation[_Packed[Self.W]](count, budget)
        _allocation[SIMD[DType.uint8, Self.W]](count, budget)
        if 2 * total <= len(self.slots):
            return
        var size = len(self.slots)
        while size < 2 * total:
            size *= 2
        _allocation[UInt64](size, budget)
        budget.charge(UInt64(len(self.monomials)))
        self.slots = List[UInt64](length=size, fill=0)
        self.mask = size - 1
        for i in range(len(self.monomials)):
            ref m = self.monomials[i]
            var mixed = _mix(_raw_hash(m))
            var h = Int(mixed & UInt64(self.mask))
            while self.slots[h] != 0:
                h = (h + 1) & self.mask
            self.slots[h] = (mixed & _TAG) | _wide(m) | UInt64(i + 1)

    @always_inline
    def find(mut self, m: _Packed[Self.W], raw: UInt64) -> Int32:
        """The number of m, whose raw hash is `raw`, added when new; `reserve` must have made room."""
        var mixed = _mix(raw)
        var tag = (mixed & _TAG) | _wide(m)
        var key = m.exponents().cast[DType.uint8]()
        var h = Int(mixed & UInt64(self.mask))
        while True:
            var slot = self.slots.unsafe_get(h)
            if slot == 0:
                return self._add(h, m, key, tag)
            if slot & ~_NUMBER == tag:
                var c = Int(slot & _NUMBER) - 1
                if tag & _WIDE == 0:
                    if not self.keys.unsafe_get(c).ne(key).reduce_or():
                        return Int32(c)
                elif _equal(self.monomials.unsafe_get(c), m):
                    return Int32(c)
            h = (h + 1) & self.mask

    @always_inline
    def find_narrow(mut self, key: SIMD[DType.uint8, Self.W], raw: UInt64) -> Int32:
        """As `find` for the narrow monomial whose exponent bytes are `key`."""
        var mixed = _mix(raw)
        var tag = mixed & _TAG
        var h = Int(mixed & UInt64(self.mask))
        while True:
            var slot = self.slots.unsafe_get(h)
            if slot == 0:
                return self._add(h, _packed(key.cast[DType.uint32]()), key, tag)
            if slot & ~_NUMBER == tag:
                var c = Int(slot & _NUMBER) - 1
                if not self.keys.unsafe_get(c).ne(key).reduce_or():
                    return Int32(c)
            h = (h + 1) & self.mask

    @always_inline
    def _add(mut self, h: Int, m: _Packed[Self.W], key: SIMD[DType.uint8, Self.W], tag: UInt64) -> Int32:
        self.monomials.append(m)
        self.keys.append(key)
        self.covered.append(False)
        self.slots.unsafe_get(h) = tag | UInt64(len(self.monomials))
        return Int32(len(self.monomials) - 1)


@always_inline
def _wide[W: Int](m: _Packed[W]) -> UInt64:
    """`_WIDE` when some exponent of m is 256 or more, else zero."""
    return UInt64(0) if m.exponents().reduce_max() < 256 else _WIDE


def _sort_descending[W: Int](kind: UInt8, monomials: List[_Packed[W]], mut budget: Budget) raises PolyError -> List[Int]:
    """Indices of `monomials` from greatest to least, by bottom-up merge sort."""
    if len(monomials) < (1 << 32):
        var keys = _keys(kind, monomials, budget)
        if keys:
            return _sort_keys(keys.take(), budget)
    var n = len(monomials)
    _allocation[Int](2 * n, budget)
    var order = List[Int](capacity=n)
    for i in range(n):
        order.append(i)
    var scratch = List[Int](length=n, fill=0)
    var width = 1
    while width < n:
        budget.charge(UInt64(n))
        var start = 0
        while start < n:
            var middle = min(start + width, n)
            var end = min(start + 2 * width, n)
            var i = start
            var j = middle
            var k = start
            while i < middle and j < end:
                if _compare(kind, monomials[order[j]], monomials[order[i]]) > 0:
                    scratch[k] = order[j]
                    j += 1
                else:
                    scratch[k] = order[i]
                    i += 1
                k += 1
            while i < middle:
                scratch[k] = order[i]
                i += 1
                k += 1
            while j < end:
                scratch[k] = order[j]
                j += 1
                k += 1
            start = end
        swap(order, scratch)
        width *= 2
    return order^


def _keys[W: Int](kind: UInt8, monomials: List[_Packed[W]], mut budget: Budget) raises PolyError -> Optional[List[UInt128]]:
    """Keys whose integer order is the monomial order, each with its index in the low 32 bits; None unless they fit in 128 bits.

    From the top: the degree (none under LEX), then a digit of b bits per
    lane that some monomial uses, in the order that decides, which under
    GREVLEX is from the last lane up, with the exponent complemented, since a
    smaller one there is greater. Lanes no monomial uses are equal
    throughout and get no digit; b and the degree's width are the fewest
    bits that hold every exponent and degree.
    """
    var n = len(monomials)
    budget.charge(UInt64(n))
    var top = SIMD[DType.uint32, W](0)
    var degree = UInt64(0)
    for i in range(n):
        ref m = monomials.unsafe_get(i)
        top = max(top, m.exponents())
        degree = max(degree, m.degree)
    var largest = top.reduce_max()
    var b = 32 - Int(count_leading_zeros(largest))
    var degree_bits = 0 if kind == MonomialOrder.LEX else 64 - Int(count_leading_zeros(degree))
    var used = 0
    comptime for j in range(W):
        if top[j] != 0:
            used += 1
    if degree_bits + used * b > 96:
        return None
    _allocation[UInt128](n, budget)
    budget.charge(UInt64(n))
    var keys = List[UInt128](capacity=n)
    var mask = UInt128((1 << b) - 1)
    for i in range(n):
        ref m = monomials.unsafe_get(i)
        var e = m.exponents()
        var key = UInt128(0) if kind == MonomialOrder.LEX else UInt128(m.degree)
        if kind == MonomialOrder.GREVLEX:
            comptime for j in range(W - 1, -1, -1):
                if top[j] != 0:
                    key = (key << UInt128(b)) | (mask - UInt128(e[j]))
        else:
            comptime for j in range(W):
                if top[j] != 0:
                    key = (key << UInt128(b)) | UInt128(e[j])
        keys.append((key << 32) | UInt128(i))
    return keys^


def _sort_keys(var keys: List[UInt128], mut budget: Budget) raises PolyError -> List[Int]:
    """The indices in the low 32 bits of distinct keys, by decreasing key.

    Long lists go by radix sort, 11 bits at a time above the index, which
    distinct keys need not be sorted by.
    """
    var n = len(keys)
    _allocation[UInt128](n, budget)
    var scratch = List[UInt128](length=n, fill=0)
    if n < 2048:
        _merge_keys(keys, scratch, budget)
    else:
        _radix_keys(keys, scratch, budget)
    _allocation[Int](n, budget)
    var order = List[Int](capacity=n)
    for k in range(n):
        order.append(Int(keys.unsafe_get(k) & UInt128(0xFFFFFFFF)))
    return order^


def _merge_keys(mut keys: List[UInt128], mut scratch: List[UInt128], mut budget: Budget) raises PolyError:
    """Sort distinct keys decreasingly, by bottom-up merge sort."""
    var n = len(keys)
    var width = 1
    while width < n:
        budget.charge(UInt64(n))
        var start = 0
        while start < n:
            var middle = min(start + width, n)
            var end = min(start + 2 * width, n)
            var i = start
            var j = middle
            var k = start
            while i < middle and j < end:
                var x = keys.unsafe_get(i)
                var y = keys.unsafe_get(j)
                if y > x:
                    scratch.unsafe_get(k) = y
                    j += 1
                else:
                    scratch.unsafe_get(k) = x
                    i += 1
                k += 1
            while i < middle:
                scratch.unsafe_get(k) = keys.unsafe_get(i)
                i += 1
                k += 1
            while j < end:
                scratch.unsafe_get(k) = keys.unsafe_get(j)
                j += 1
                k += 1
            start = end
        swap(keys, scratch)
        width *= 2


def _radix_keys(mut keys: List[UInt128], mut scratch: List[UInt128], mut budget: Budget) raises PolyError:
    """Sort distinct keys decreasingly, least significant digit first above the index; charged as the merge sort."""
    var n = len(keys)
    var width = 1
    while width < n:
        budget.charge(UInt64(n))
        width *= 2
    var top = UInt128(0)
    for k in range(n):
        top = max(top, keys.unsafe_get(k))
    var bits = 128 - Int(count_leading_zeros(top >> 32))
    comptime DIGIT = 11
    var counts = List[Int](length=1 << DIGIT, fill=0)
    var shift = 32
    while shift < 32 + bits:
        for d in range(1 << DIGIT):
            counts.unsafe_get(d) = 0
        for k in range(n):
            counts.unsafe_get(Int((keys.unsafe_get(k) >> UInt128(shift)) & UInt128((1 << DIGIT) - 1))) += 1
        # Decreasing digits first, so the pass is stable for a descending order.
        var at = 0
        for d in range((1 << DIGIT) - 1, -1, -1):
            var c = counts.unsafe_get(d)
            counts.unsafe_get(d) = at
            at += c
        for k in range(n):
            var key = keys.unsafe_get(k)
            var d = Int((key >> UInt128(shift)) & UInt128((1 << DIGIT) - 1))
            scratch.unsafe_get(counts.unsafe_get(d)) = key
            counts.unsafe_get(d) += 1
        swap(keys, scratch)
        shift += DIGIT


@always_inline
def _divisibility_mask[W: Int, B: Int](exponents: SIMD[DType.uint32, W], thresholds: List[SIMD[DType.uint32, W]]) -> UInt64:
    """Bit k * W + lane set when the exponent in the lane reaches thresholds[k] there."""
    comptime lanes = SIMD[DType.uint64, W](1) << iota[DType.uint64, W]()
    var mask = UInt64(0)
    comptime for k in range(B):
        var reached = exponents.ge(thresholds.unsafe_get(k)).select(lanes, SIMD[DType.uint64, W](0)).reduce_or()
        mask |= reached << UInt64(k * W)
    return mask


struct _Matrix[W: Int](Movable):
    """One F4 matrix: rows as multiples of basis elements, their columns concatenated."""
    var columns: _Columns[Self.W]
    var sources: List[Int]
    """The basis element of each row; the row's residues are the element's."""
    var starts: List[Int]
    """Where each row's columns start, then where the last one ends."""
    var entries: List[Int32]
    """Each row's columns, leading term first: monomial numbers, then positions after `number`."""

    def __init__(out self):
        self.columns = _Columns[Self.W]()
        self.sources = List[Int]()
        self.starts = [0]
        self.entries = List[Int32]()

    def add_row[C: CoefficientRing, integral: Bool](mut self, engine: _Engine[C, Self.W, integral], store: _Store[Self.W], source: Int, shift: _Packed[Self.W], mut budget: Budget) raises PolyError:
        """Add shift * engine.polys[source], whose term list `store.release` may have dropped."""
        ref p = engine.polys[source]
        ref h = store.hashes[source]
        var n = len(h)
        # Some product's exponent overflows exactly when the greatest exponents' does.
        var top = _mul(store.tops[source], shift)
        budget.charge(UInt64(n))
        _allocation[Int32](n, budget)
        self.columns.reserve(n, budget)
        var base = _raw_hash(shift)
        var first = len(self.entries)
        if top.exponents().reduce_max() < 256:
            # Every product is narrow: its bytes are the sum of its factors'.
            ref keys = store.keys[source]
            var offset = shift.exponents().cast[DType.uint8]()
            for k in range(n):
                self.entries.append(self.columns.find_narrow(keys.unsafe_get(k) + offset, base + h.unsafe_get(k)))
        elif store.tops[source].exponents().reduce_max() < 256:
            # The element's exponents are its bytes.
            ref keys = store.keys[source]
            for k in range(n):
                self.entries.append(self.columns.find(_times(_packed(keys.unsafe_get(k).cast[DType.uint32]()), shift), base + h.unsafe_get(k)))
        else:
            for k in range(n):
                self.entries.append(self.columns.find(_times(p.unsafe_get(n - 1 - k).monomial, shift), base + h.unsafe_get(k)))
        self.columns.covered[Int(self.entries[first])] = True
        self.sources.append(source)
        self.starts.append(len(self.entries))

    def preprocess[C: CoefficientRing, integral: Bool](mut self, engine: _Engine[C, Self.W, integral], store: _Store[Self.W], mut budget: Budget) raises PolyError:
        """Symbolic preprocessing: a reducer for each monomial some active leading monomial divides.

        The reducer is the active element with the least such leading monomial;
        `engine.active` must be sorted, and the order graded, so the search
        stops at the first leading monomial of greater degree.
        """
        var count = len(engine.active)
        _allocation[_Packed[Self.W]](count, budget)
        _allocation[UInt64](count + 8, budget)
        var leads = List[_Packed[Self.W]](capacity=count)
        var top = SIMD[DType.uint32, Self.W](0)
        for g in engine.active:
            leads.append(engine.leads[g])
            top = max(top, engine.leads[g].exponents())
        # Divisibility masks: bit k * W + lane says the exponent in the lane
        # reaches the lane's k-th threshold, the thresholds spread over the
        # leading monomials' exponents. A leading monomial divides u only if
        # its mask is inside u's, which rules out most of them 8 at a time.
        comptime B = 64 // Self.W
        var thresholds = List[SIMD[DType.uint32, Self.W]](capacity=B)
        for k in range(B):
            var t = SIMD[DType.uint32, Self.W](1) + (top * UInt32(k)) // UInt32(B)
            thresholds.append(top.eq(0).select(SIMD[DType.uint32, Self.W](UInt32.MAX), t))
        var masks = List[UInt64](capacity=count + 8)
        for i in range(count):
            masks.append(_divisibility_mask[Self.W, B](leads[i].exponents(), thresholds))
        # Padding no monomial's mask contains.
        for _ in range(8):
            masks.append(UInt64.MAX)
        # The leading monomials of degree at most `degree` are the first `limit`.
        var degree = UInt64.MAX
        var limit = 0
        var next = 0
        while next < len(self.columns.monomials):
            var c = next
            next += 1
            if self.columns.covered[c]:
                continue
            var u = self.columns.monomials[c]
            if u.degree != degree:
                degree = u.degree
                limit = 0
                while limit < count and leads[limit].degree <= degree:
                    limit += 1
            var exponents = u.exponents()
            var outside = ~_divisibility_mask[Self.W, B](exponents, thresholds)
            var found = -1
            var i = 0
            while i < limit:
                var block = masks.unsafe_ptr().unsafe_offset(i).unsafe_load[width=8]()
                var candidates = (block & outside).eq(0)
                if candidates.reduce_or():
                    for k in range(min(8, limit - i)):
                        if candidates[k] and leads.unsafe_get(i + k).exponents().le(exponents).reduce_and():
                            found = i + k
                            break
                    if found >= 0:
                        break
                i += 8
            budget.charge(UInt64((found if found >= 0 else limit) + 1))
            if found >= 0:
                self.add_row(engine, store, engine.active[found], _div(u, leads[found]), budget)

    def number(mut self, kind: UInt8, mut budget: Budget) raises PolyError -> List[Int]:
        """Number the columns from the greatest monomial down; return the monomial at each position."""
        var ncols = len(self.columns.monomials)
        var order = _sort_descending(kind, self.columns.monomials, budget)
        _allocation[Int32](ncols, budget)
        var position = List[Int32](length=ncols, fill=0)
        for i in range(ncols):
            position[order[i]] = Int32(i)
        budget.charge(UInt64(len(self.entries)))
        for k in range(len(self.entries)):
            self.entries.unsafe_get(k) = position.unsafe_get(Int(self.entries.unsafe_get(k)))
        return order^


struct _Rows(Movable):
    """Rows of residues found during reduction, concatenated."""
    var columns: List[Int32]
    var values: List[UInt32]
    var starts: List[Int]
    """Where each row starts, then where the last one ends."""

    def __init__(out self):
        self.columns = List[Int32]()
        self.values = List[UInt32]()
        self.starts = [0]


@always_inline
def _reciprocal(prime: UInt64) -> UInt64:
    """floor(2^64 / prime), for `_residue`; the prime is at least 2."""
    return UInt64((UInt128(1) << 64) // UInt128(prime))


@always_inline
def _residue(v: UInt64, prime: UInt64, reciprocal: UInt64) -> UInt64:
    """v modulo prime, by Barrett's method with reciprocal = floor(2^64 / prime).

    v * reciprocal / 2^64 exceeds v / prime - v / 2^64 > v / prime - 1, so
    the estimated quotient is floor(v / prime) or one less, and one
    conditional subtraction finishes.
    """
    var q = UInt64((UInt128(v) * UInt128(reciprocal)) >> 64)
    var r = v - q * prime
    return r - prime if r >= prime else r


@always_inline
def _axpy[small: Bool](data: Pointer[mut=True, UInt64, _], columns: Pointer[mut=False, Int32, _], values: Pointer[mut=False, UInt32, _], n: Int, factor: UInt64, square: UInt64):
    """Add factor times a row, after its leading entry, to the dense accumulator, four entries a step."""
    var k = 1
    while k + 4 <= n:
        comptime for u in range(4):
            _update[small](data, columns, values, k + u, factor, square)
        k += 4
    while k < n:
        _update[small](data, columns, values, k, factor, square)
        k += 1


@always_inline
def _update[small: Bool](data: Pointer[mut=True, UInt64, _], columns: Pointer[mut=False, Int32, _], values: Pointer[mut=False, UInt32, _], k: Int, factor: UInt64, square: UInt64):
    var j = Int(columns.unsafe_offset(k).unsafe_load())
    var x = data.unsafe_offset(j).unsafe_load() + factor * UInt64(values.unsafe_offset(k).unsafe_load())
    comptime if small:
        data.unsafe_offset(j).unsafe_store(x)
    else:
        data.unsafe_offset(j).unsafe_store(x - square if x >= square else x)


def _reduce_row[W: Int](mut dense: List[UInt64], start: Int, pivot: List[Int], matrix: _Matrix[W], values: List[List[UInt32]], mut found: _Rows, prime: UInt64, mut budget: Budget) raises PolyError:
    if prime < 65536:
        _reduce_row_in[True](dense, start, pivot, matrix, values, found, prime, budget)
    else:
        _reduce_row_in[False](dense, start, pivot, matrix, values, found, prime, budget)


def _reduce_row_in[small: Bool, W: Int](mut dense: List[UInt64], start: Int, pivot: List[Int], matrix: _Matrix[W], values: List[List[UInt32]], mut found: _Rows, prime: UInt64, mut budget: Budget) raises PolyError:
    """Reduce the row scattered in `dense` from column `start` on, appending what no pivot covers to `found`.

    A pivot below the matrix's row count is a matrix row, whose residues are
    its basis element's; a greater one is a row of `found`. For p < 2^16
    products are below 2^32, and an entry receives at most one product per
    column before it is read, so plain 64-bit sums cannot overflow. Otherwise
    entries stay below p^2: each update adds a product below p^2 < 2^62 and
    subtracts p^2 when the sum reaches it. Visited entries are cleared, so
    `dense` is all zero again afterwards. Runs of zero words are skipped eight
    at a time.
    """
    var square = prime * prime
    var ncols = len(dense)
    var rows = len(matrix.sources)
    var data = dense.unsafe_ptr()
    budget.charge(UInt64(ncols - start))
    var c = start
    while c < ncols:
        if c & 7 == 0 and c + 8 <= ncols:
            var block = data.unsafe_offset(c).unsafe_load[width=8]()
            if not block.ne(0).reduce_or():
                c += 8
                continue
        var v = data.unsafe_offset(c).unsafe_load()
        if v == 0:
            c += 1
            continue
        data.unsafe_offset(c).unsafe_store(UInt64(0))
        v %= prime
        if v == 0:
            c += 1
            continue
        var q = pivot.unsafe_get(c)
        if q >= rows:
            var r = q - rows
            var s = found.starts.unsafe_get(r)
            var n = found.starts.unsafe_get(r + 1) - s
            budget.charge(UInt64(n))
            _axpy[small](data, found.columns.unsafe_ptr().unsafe_offset(s), found.values.unsafe_ptr().unsafe_offset(s), n, prime - v, square)
        elif q >= 0:
            var s = matrix.starts.unsafe_get(q)
            var n = matrix.starts.unsafe_get(q + 1) - s
            budget.charge(UInt64(n))
            _axpy[small](data, matrix.entries.unsafe_ptr().unsafe_offset(s), values[matrix.sources.unsafe_get(q)].unsafe_ptr(), n, prime - v, square)
        else:
            found.columns.append(Int32(c))
            found.values.append(UInt32(v))
        c += 1


comptime _BLOCK = 16
"""Rows `_eliminate` reduces at once, one per SIMD lane."""

comptime _Block = SIMD[DType.uint64, _BLOCK]

comptime _AHEAD = 8
"""Entries ahead of the update that `_axpy_block` prefetches the block for."""


struct _Field(Copyable, Movable):
    """A prime with the constants that reduce modulo it, in every lane."""
    var prime: UInt64
    var reciprocal: UInt64
    var primes: _Block
    var squares: _Block
    var wraps: _Block
    """2^32 modulo the prime."""
    var inverses: SIMD[DType.float64, _BLOCK]

    def __init__(out self, prime: UInt64):
        self.prime = prime
        self.reciprocal = _reciprocal(prime)
        self.primes = _Block(prime)
        self.squares = _Block(prime * prime)
        self.wraps = _Block((UInt64(1) << 32) % prime)
        self.inverses = SIMD[DType.float64, _BLOCK](1.0) / self.primes.cast[DType.float64]()


@always_inline
def _residues(v: _Block, field: _Field) -> _Block:
    """Each lane of v modulo the prime.

    Folding the high half by 2^32 modulo the prime leaves a value below
    2^62, whose quotient estimated in floating point is off by one at most
    either way.
    """
    var a = (v >> 32) * field.wraps + (v & 0xFFFFFFFF)
    var q = (a.cast[DType.float64]() * field.inverses).cast[DType.uint64]()
    var r = a - q * field.primes
    r = (r >> 63).ne(0).select(r + field.primes, r)
    return r.ge(field.primes).select(r - field.primes, r)


@no_inline
def _axpy_block[small: Bool](data: Pointer[mut=True, UInt64, _], columns: Pointer[mut=False, Int32, _], values: Pointer[mut=False, UInt32, _], n: Int, factors: SIMD[DType.uint32, _BLOCK], square: _Block):
    """Add each lane's factor times a row, after its leading entry, to that lane of the dense block.

    Both factors widen from 32 bits, so each product is one 32 by 32 bit
    multiplication. Inlined, the widening is lost before instructions are
    selected, which then multiply all 64 bits.
    """
    var factor = factors.cast[DType.uint64]()
    var k = 1
    while k + _AHEAD < n:
        # The block is far larger than the cache, and its columns follow no
        # pattern the hardware could prefetch; the row knows them ahead.
        var ahead = data.unsafe_offset(_BLOCK * Int(columns.unsafe_offset(k + _AHEAD).unsafe_load()))
        comptime for line in range(0, _BLOCK, 8):
            prefetch[PrefetchOptions().for_write().high_locality()](ahead.unsafe_offset(line))
        _update_block[small](data, columns, values, k, factor, square)
        k += 1
    while k < n:
        _update_block[small](data, columns, values, k, factor, square)
        k += 1


@always_inline
def _update_block[small: Bool](data: Pointer[mut=True, UInt64, _], columns: Pointer[mut=False, Int32, _], values: Pointer[mut=False, UInt32, _], k: Int, factor: _Block, square: _Block):
    var at = data.unsafe_offset(_BLOCK * Int(columns.unsafe_offset(k).unsafe_load()))
    var x = at.unsafe_load[width=_BLOCK]() + factor * _Block(UInt64(values.unsafe_offset(k).unsafe_load()))
    comptime if small:
        at.unsafe_store[width=_BLOCK](x)
    else:
        at.unsafe_store[width=_BLOCK](x.ge(square).select(x - square, x))


struct _Lane(Movable):
    """The entries one lane of a block keeps: its leading entry first, then its tail."""
    var columns: List[Int32]
    var values: List[UInt32]

    def __init__(out self):
        self.columns = List[Int32]()
        self.values = List[UInt32]()


def _reduce_block[small: Bool, W: Int](mut dense: List[UInt64], rows: List[Int], first: Int, count: Int, pivot: List[Int], matrix: _Matrix[W], values: List[List[UInt32]], found: _Rows, mut lanes: List[_Lane], field: _Field, ring: Modulus, mut budget: Budget) raises PolyError:
    """Reduce rows[first : first + count] at once, row first + l in lane l, as `_reduce_row` would one after another.

    Each lane keeps in `lanes` what no pivot covers. One after another, a
    row leading in a column no pivot covers becomes a pivot for the rows
    after it; here the first lane without a leading entry that is nonzero in
    such a column leads there, and the later lanes subtract a multiple of
    it at once. Every lane is then the row reduced by the same pivots and the
    same earlier rows, with zeros in their leading columns, which fixes it.
    For p < 2^16 an entry gains at most one product below 2^32 per column
    and per lane before it is read; otherwise entries stay below p^2.
    """
    var ncols = len(pivot)
    var rows_in_matrix = len(matrix.sources)
    var data = dense.unsafe_ptr()
    var start = ncols
    for l in range(count):
        var r = rows[first + l]
        var s = matrix.starts[r]
        ref v = values[matrix.sources[r]]
        for k in range(matrix.starts[r + 1] - s):
            data.unsafe_offset(_BLOCK * Int(matrix.entries.unsafe_get(s + k)) + l).unsafe_store(UInt64(v.unsafe_get(k)))
        start = min(start, Int(matrix.entries[s]))
        lanes[l].columns.clear()
        lanes[l].values.clear()
    var led = SIMD[DType.bool, _BLOCK](fill=False)
    budget.charge(UInt64(ncols - start))
    for c in range(start, ncols):
        var at = data.unsafe_offset(_BLOCK * c)
        var v = at.unsafe_load[width=_BLOCK]()
        if not v.ne(0).reduce_or():
            continue
        at.unsafe_store[width=_BLOCK](_Block(0))
        v = _residues(v, field)
        var nonzero = v.ne(0)
        if not nonzero.reduce_or():
            continue
        var q = pivot.unsafe_get(c)
        if q >= 0:
            var factor = nonzero.select(field.primes - v, _Block(0)).cast[DType.uint32]()
            var weight = UInt64(nonzero.cast[DType.uint8]().reduce_add())
            if q >= rows_in_matrix:
                var r = q - rows_in_matrix
                var s = found.starts.unsafe_get(r)
                var n = found.starts.unsafe_get(r + 1) - s
                budget.charge(UInt64(n) * weight)
                _axpy_block[small](data, found.columns.unsafe_ptr().unsafe_offset(s), found.values.unsafe_ptr().unsafe_offset(s), n, factor, field.squares)
            else:
                var s = matrix.starts.unsafe_get(q)
                var n = matrix.starts.unsafe_get(q + 1) - s
                budget.charge(UInt64(n) * weight)
                _axpy_block[small](data, matrix.entries.unsafe_ptr().unsafe_offset(s), values[matrix.sources.unsafe_get(q)].unsafe_ptr(), n, factor, field.squares)
            continue
        var leader = -1
        for l in range(count):
            if nonzero[l] and not led[l]:
                leader = l
                break
        for l in range(count):
            if nonzero[l] and (leader < 0 or l <= leader):
                lanes[l].columns.append(Int32(c))
                lanes[l].values.append(UInt32(v[l]))
        if leader < 0:
            continue
        led[leader] = True
        # The later lanes subtract their multiple of the leader from here on.
        var inverse = ModInt(v[leader], ring).inverse(budget).value
        var factors = SIMD[DType.uint32, _BLOCK](0)
        var any = False
        for l in range(leader + 1, count):
            if nonzero[l]:
                factors[l] = UInt32(field.prime - _residue(v[l] * inverse, field.prime, field.reciprocal))
                any = True
        if not any:
            continue
        budget.charge(UInt64(ncols - c))
        var factor = factors.cast[DType.uint64]()
        for k in range(c + 1, ncols):
            var to = data.unsafe_offset(_BLOCK * k)
            var x = to.unsafe_offset(leader).unsafe_load()
            if x == 0:
                continue
            var y = to.unsafe_load[width=_BLOCK]() + factor * _Block(UInt64(UInt32(_residue(x, field.prime, field.reciprocal))))
            comptime if small:
                to.unsafe_store[width=_BLOCK](y)
            else:
                to.unsafe_store[width=_BLOCK](y.ge(field.squares).select(y - field.squares, y))


def _scatter[W: Int](mut dense: List[UInt64], matrix: _Matrix[W], values: List[List[UInt32]], row: Int, skip: Int):
    """Write a matrix row's residues, after its first `skip` entries, into the dense accumulator."""
    var s = matrix.starts[row]
    ref v = values[matrix.sources[row]]
    for k in range(skip, matrix.starts[row + 1] - s):
        dense.unsafe_get(Int(matrix.entries.unsafe_get(s + k))) = UInt64(v.unsafe_get(k))


struct _Step[W: Int](Copyable, Movable):
    """One matrix of a recorded F4 run, which runs modulo other primes replay.

    The first `pivots` rows are pivots from the start. In a round, each later
    row is reduced in turn to a new pivot leading in `leads`, and the new
    pivots are then reduced by one another from the right; in the final
    matrix every row is a pivot and the first `basis` rows have their tails
    reduced. `supports` lists each result's columns, leading column first, in
    the order the results are inserted, which `inserted` gives as positions
    in the order they come when it is not empty; the final matrix also keeps
    the monomial of each column, which `monomial` reads through the
    supports.
    """
    var final: Bool
    var ncols: Int
    var sources: List[Int]
    var starts: List[Int]
    var entries: List[Int32]
    var pivots: Int
    var basis: Int
    var leads: List[Int32]
    var supports: List[List[Int32]]
    var inserted: List[Int]
    var columns: List[_Packed[Self.W]]

    def __init__(out self, final: Bool, ncols: Int):
        self.final = final
        self.ncols = ncols
        self.sources = List[Int]()
        self.starts = [0]
        self.entries = List[Int32]()
        self.pivots = 0
        self.basis = 0
        self.leads = List[Int32]()
        self.supports = List[List[Int32]]()
        self.inserted = List[Int]()
        self.columns = List[_Packed[Self.W]]()

    @always_inline
    def monomial(self, r: Int, k: Int) -> _Packed[Self.W]:
        """The monomial of entry k of result r of the final matrix."""
        return self.columns[Int(self.supports[r][k])]

    def keep(mut self, matrix: _Matrix[Self.W], r: Int, mut budget: Budget) raises PolyError:
        """Append matrix row r."""
        var s = matrix.starts[r]
        var e = matrix.starts[r + 1]
        _allocation[Int32](e - s, budget)
        for k in range(s, e):
            self.entries.append(matrix.entries[k])
        self.sources.append(matrix.sources[r])
        self.starts.append(len(self.entries))

    def matrix(self) -> _Matrix[Self.W]:
        """The recorded rows as a matrix, with no monomials."""
        var matrix = _Matrix[Self.W]()
        matrix.sources = self.sources.copy()
        matrix.starts = self.starts.copy()
        matrix.entries = self.entries.copy()
        return matrix^


struct _Trace[W: Int](Movable):
    """A recorded F4 run: the elements its start leaves, and its matrices."""
    var inputs: List[List[_Packed[Self.W]]]
    """Each element's monomials after the start, in increasing order."""
    var steps: List[_Step[Self.W]]

    def __init__(out self):
        self.inputs = List[List[_Packed[Self.W]]]()
        self.steps = List[_Step[Self.W]]()


def _eliminate[W: Int](matrix: _Matrix[W], mut pivot: List[Int], reduce: List[Int], values: List[List[UInt32]], prime: UInt64, ring: Modulus, mut found: _Rows, mut kept: List[Int], mut budget: Budget) raises PolyError -> List[Int]:
    """Reduce rows `reduce` in turn, each nonzero remainder becoming a monic pivot; then reduce the new pivots by one another.

    The rows are reduced `_BLOCK` at a time by `_reduce_block`, with the
    result of reducing them in turn. `kept` gets the rows that gave pivots.
    Returns the reduced new pivots, rows of `found`, by decreasing leading
    column.
    """
    var nrows = len(matrix.sources)
    var ncols = len(pivot)
    var field = _Field(prime)
    _allocation[UInt64](_product(ncols, _BLOCK), budget)
    var block = List[UInt64](length=_BLOCK * ncols, fill=0)
    var lanes = List[_Lane](capacity=_BLOCK)
    for _ in range(_BLOCK):
        lanes.append(_Lane())
    var first = 0
    while first < len(reduce):
        var count = min(_BLOCK, len(reduce) - first)
        if prime < 65536:
            _reduce_block[True](block, reduce, first, count, pivot, matrix, values, found, lanes, field, ring, budget)
        else:
            _reduce_block[False](block, reduce, first, count, pivot, matrix, values, found, lanes, field, ring, budget)
        for l in range(count):
            ref lane = lanes[l]
            if len(lane.columns) == 0:
                continue
            _allocation[UInt32](2 * len(lane.columns), budget)
            # A new pivot: monic, and used by the rows that follow.
            var inverse = ModInt(UInt64(lane.values[0]), ring).inverse(budget).value
            for k in range(len(lane.columns)):
                found.columns.append(lane.columns[k])
                found.values.append(UInt32(_residue(UInt64(lane.values[k]) * inverse, prime, field.reciprocal)))
            pivot[Int(lane.columns[0])] = nrows + len(found.starts) - 1
            found.starts.append(len(found.columns))
            kept.append(reduce[first + l])
        first += count
    _allocation[UInt64](ncols, budget)
    var dense = List[UInt64](length=ncols, fill=0)
    # The new pivots by decreasing leading column. Each is reduced by every
    # reducer already, so it only needs reducing by the new pivots right of
    # its leading column; taken from the right, those are final when it is
    # reached.
    var created = List[Int]()
    for i in range(len(found.starts) - 1):
        var j = len(created)
        created.append(i)
        while j > 0 and found.columns[found.starts[created[j - 1]]] < found.columns[found.starts[i]]:
            created[j] = created[j - 1]
            j -= 1
        created[j] = i
    var results = List[Int](capacity=len(created))
    for i in created:
        var lead = Int(found.columns[found.starts[i]])
        for k in range(found.starts[i] + 1, found.starts[i + 1]):
            dense[Int(found.columns[k])] = UInt64(found.values[k])
        var before = len(found.columns)
        found.columns.append(Int32(lead))
        found.values.append(UInt32(1))
        _reduce_row(dense, lead + 1, pivot, matrix, values, found, prime, budget)
        _allocation[UInt32](2 * (len(found.columns) - before), budget)
        pivot[lead] = nrows + len(found.starts) - 1
        results.append(len(found.starts) - 1)
        found.starts.append(len(found.columns))
    return results^


def _tails[W: Int](matrix: _Matrix[W], basis: Int, pivot: List[Int], values: List[List[UInt32]], prime: UInt64, mut found: _Rows, mut budget: Budget) raises PolyError:
    """Reduce the tails of the first `basis` rows against all rows, each a row of `found`."""
    _allocation[UInt64](len(pivot), budget)
    var dense = List[UInt64](length=len(pivot), fill=0)
    for r in range(basis):
        var first = Int(matrix.entries[matrix.starts[r]])
        _scatter(dense, matrix, values, r, 1)
        found.columns.append(Int32(first))
        found.values.append(values[matrix.sources[r]][0])
        _reduce_row(dense, first + 1, pivot, matrix, values, found, prime, budget)
        _allocation[UInt32](2 * (len(found.columns) - found.starts[len(found.starts) - 1]), budget)
        found.starts.append(len(found.columns))


def _supports(found: _Rows, rows: List[Int], mut budget: Budget) raises PolyError -> List[List[Int32]]:
    var supports = List[List[Int32]](capacity=len(rows))
    for i in rows:
        _allocation[Int32](found.starts[i + 1] - found.starts[i], budget)
        var columns = List[Int32](capacity=found.starts[i + 1] - found.starts[i])
        for k in range(found.starts[i], found.starts[i + 1]):
            columns.append(found.columns[k])
        supports.append(columns^)
    return supports^


def _insertion[W: Int](found: _Rows, results: List[Int], monomials: List[_Packed[W]], order: List[Int], mut budget: Budget) raises PolyError -> List[Int]:
    """The order to insert a round's new elements in, as positions in `results`; empty for their own order, smallest leading monomial first.

    Under an inhomogeneous run, a new element's leading monomial may be one
    that a smaller new element's divides. Such elements go first, by
    decreasing leading monomial: inserting the divisor then retires each from
    the active elements and installs their pair, which a later matrix
    reduces, so the whole run stays in its matrices.
    """
    _allocation[Bool](len(results), budget)
    var divided = List[Bool](length=len(results), fill=False)
    var some = False
    for k in range(len(results)):
        var lead = monomials[order[Int(found.columns[found.starts[results[k]]])]]
        for j in range(k):
            budget.charge(1)
            if _divides(monomials[order[Int(found.columns[found.starts[results[j]]])]], lead):
                divided[k] = True
                some = True
                break
    var inserted = List[Int]()
    if not some:
        return inserted^
    for k in range(len(results) - 1, -1, -1):
        if divided[k]:
            inserted.append(k)
    for k in range(len(results)):
        if not divided[k]:
            inserted.append(k)
    return inserted^


def _inserted(results: List[Int], inserted: List[Int]) -> List[Int]:
    """`results` in the recorded insertion order."""
    if len(inserted) == 0:
        return results.copy()
    var permuted = List[Int](capacity=len(results))
    for k in inserted:
        permuted.append(results[k])
    return permuted^


def _round[W: Int, record: Bool](mut engine: _Engine[ModInt, W, False], store: _Store[W], prime: UInt64, ring: Modulus, mut trace: _Trace[W], mut budget: Budget) raises PolyError -> List[List[_Term[ModInt, W]]]:
    """Run one F4 round on the pairs of least LCM degree; return the new elements, monic, in the order to insert them."""
    var degree = engine.pairs[0].lcm.degree
    var matrix = _Matrix[W]()
    # Both halves of every selected pair. A half is fixed by its element and
    # its leading monomial, the pair's LCM, so equal halves are added once.
    var seen = Dict[Int, Bool]()
    var stride = len(engine.polys)
    while len(engine.pairs) and engine.pairs[0].lcm.degree == degree:
        var pair = engine.select(budget)
        matrix.columns.reserve(1, budget)
        var lead = Int(matrix.columns.find(pair.lcm, _raw_hash(pair.lcm)))
        for source in [pair.first, pair.second]:
            budget.charge(1)
            var key = lead * stride + source
            if key in seen:
                continue
            seen[key] = True
            matrix.add_row(engine, store, source, _div(pair.lcm, engine.leads[source]), budget)
    var pair_rows = len(matrix.sources)
    matrix.preprocess(engine, store, budget)
    var nrows = len(matrix.sources)
    var order = matrix.number(engine.kind, budget)
    var ncols = len(order)
    # Pivots: every reducer row, then the first pair row for each leading column.
    _allocation[Int](ncols, budget)
    var pivot = List[Int](length=ncols, fill=-1)
    var pivots = List[Int]()
    for r in range(pair_rows, nrows):
        pivot[Int(matrix.entries[matrix.starts[r]])] = r
        pivots.append(r)
    var reduce = List[Int]()
    for r in range(pair_rows):
        var c = Int(matrix.entries[matrix.starts[r]])
        if pivot[c] < 0:
            pivot[c] = r
            pivots.append(r)
        else:
            reduce.append(r)
    var found = _Rows()
    var kept = List[Int]()
    var results = _eliminate(matrix, pivot, reduce, store.values, prime, ring, found, kept, budget)
    var inserted = _insertion(found, results, matrix.columns.monomials, order, budget)
    results = _inserted(results, inserted)
    comptime if record:
        # The replay keeps the pivots and the rows that gave new ones.
        var step = _Step[W](False, ncols)
        for r in pivots:
            step.keep(matrix, r, budget)
        step.pivots = len(pivots)
        for i in range(len(kept)):
            step.keep(matrix, kept[i], budget)
            step.leads.append(found.columns[found.starts[i]])
        step.supports = _supports(found, results, budget)
        step.inserted = inserted^
        trace.steps.append(step^)
    # The new elements in the order to insert them, as increasing term lists.
    var fresh = List[List[_Term[ModInt, W]]]()
    for i in results:
        var n = found.starts[i + 1] - found.starts[i]
        _allocation[_Term[ModInt, W]](n, budget)
        var terms = List[_Term[ModInt, W]](capacity=n)
        for k in range(found.starts[i + 1] - 1, found.starts[i] - 1, -1):
            terms.append(_Term[ModInt, W](matrix.columns.monomials[order[Int(found.columns[k])]], ModInt(UInt64(found.values[k]), ring)))
        fresh.append(terms^)
    return fresh^


def _interreduce[W: Int, record: Bool](mut engine: _Engine[ModInt, W, False], store: _Store[W], prime: UInt64, ring: Modulus, mut trace: _Trace[W], mut budget: Budget) raises PolyError -> List[List[_Term[ModInt, W]]]:
    """The reduced basis from the active elements, by one matrix, in decreasing leading-monomial order.

    Every active element is a row, and symbolic preprocessing adds a reducer
    for each tail monomial some leading monomial divides; active leading
    monomials are mutually nondividing, so all rows lead in distinct columns.
    Reducing each element's tail by the other rows leaves no monomial that a
    leading monomial divides: the reduced basis.
    """
    engine.sort_active(budget)
    var matrix = _Matrix[W]()
    var one = _Packed[W](SIMD[DType.uint32, W](0), 0, 0)
    for position in range(len(engine.active) - 1, -1, -1):
        matrix.add_row(engine, store, engine.active[position], one, budget)
    var basis_rows = len(matrix.sources)
    matrix.preprocess(engine, store, budget)
    var nrows = len(matrix.sources)
    var order = matrix.number(engine.kind, budget)
    var ncols = len(order)
    _allocation[Int](ncols, budget)
    var pivot = List[Int](length=ncols, fill=-1)
    for r in range(nrows):
        pivot[Int(matrix.entries[matrix.starts[r]])] = r
    var found = _Rows()
    _tails(matrix, basis_rows, pivot, store.values, prime, found, budget)
    var rows = List[Int](capacity=basis_rows)
    for r in range(basis_rows):
        rows.append(r)
    comptime if record:
        var step = _Step[W](True, ncols)
        for r in range(nrows):
            step.keep(matrix, r, budget)
        step.pivots = nrows
        step.basis = basis_rows
        step.supports = _supports(found, rows, budget)
        _allocation[_Packed[W]](ncols, budget)
        step.columns = List[_Packed[W]](capacity=ncols)
        for c in range(ncols):
            step.columns.append(matrix.columns.monomials[order[c]])
        trace.steps.append(step^)
    var basis = List[List[_Term[ModInt, W]]](capacity=basis_rows)
    for r in range(basis_rows):
        var n = found.starts[r + 1] - found.starts[r]
        _allocation[_Term[ModInt, W]](n, budget)
        var terms = List[_Term[ModInt, W]](capacity=n)
        for k in range(found.starts[r + 1] - 1, found.starts[r] - 1, -1):
            terms.append(_Term[ModInt, W](matrix.columns.monomials[order[Int(found.columns[k])]], ModInt(UInt64(found.values[k]), ring)))
        basis.append(terms^)
    return basis^


def _f4_run[W: Int, record: Bool](var generators: List[List[_Term[ModInt, W]]], kind: UInt8, ring: Modulus, mut trace: _Trace[W], mut budget: Budget) raises PolyError -> List[List[_Term[ModInt, W]]]:
    var prime = ring.value
    var engine = _Engine[ModInt, W, False](kind, ring)
    engine.start(generators^, budget)
    comptime if record:
        for p in engine.polys:
            var monomials = List[_Packed[W]](capacity=len(p))
            for t in p:
                monomials.append(t.monomial)
            trace.inputs.append(monomials^)
    var store = _Store[W]()
    while len(engine.pairs):
        budget.charge(1)
        engine.sort_active(budget)
        store.extend(engine, budget)
        store.release(engine)
        var fresh = _round[W, record](engine, store, prime, ring, trace, budget)
        for k in range(len(fresh)):
            var p = List[_Term[ModInt, W]]()
            swap(p, fresh[k])
            engine.insert(p^, budget, heap=False)
        # The pairs are ordered once the round's elements are all in.
        engine.heapify_pairs(budget)
    store.extend(engine, budget)
    store.release(engine)
    return _interreduce[W, record](engine, store, prime, ring, trace, budget)


def _f4_packed[W: Int](var generators: List[List[_Term[ModInt, W]]], kind: UInt8, ring: Modulus, mut budget: Budget) raises PolyError -> List[List[_Term[ModInt, W]]]:
    """The reduced monic basis of packed generators, in decreasing leading-monomial order.

    Generators are increasing term lists over a degree order `kind` and a
    prime below 2^31; zero generators are allowed.
    """
    var trace = _Trace[W]()
    return _f4_run[W, False](generators^, kind, ring, trace, budget)


def _f4_learn[W: Int](var generators: List[List[_Term[ModInt, W]]], kind: UInt8, ring: Modulus, mut trace: _Trace[W], mut budget: Budget) raises PolyError -> List[List[_Term[ModInt, W]]]:
    """As `_f4_packed`, recording the run in `trace` for `_f4_replay`."""
    trace = _Trace[W]()
    return _f4_run[W, True](generators^, kind, ring, trace, budget)


def _replay_rows(found: _Rows, results: List[Int], supports: List[List[Int32]], mut values: List[List[UInt32]], mut budget: Budget) raises PolyError -> Bool:
    """Append each result's residues on its recorded support; False if a result leaves it."""
    for t in range(len(results)):
        var i = results[t]
        ref support = supports[t]
        _allocation[UInt32](len(support), budget)
        var residues = List[UInt32](length=len(support), fill=0)
        var j = 0
        for k in range(found.starts[i], found.starts[i + 1]):
            budget.charge(1)
            while j < len(support) and support[j] < found.columns[k]:
                j += 1
            if j == len(support) or support[j] != found.columns[k]:
                return False
            residues[j] = found.values[k]
        if residues[0] == 0:
            return False
        values.append(residues^)
    return True


def _f4_replay[W: Int](trace: _Trace[W], var generators: List[List[_Term[ModInt, W]]], kind: UInt8, ring: Modulus, mut budget: Budget) raises PolyError -> Optional[List[List[_Term[ModInt, W]]]]:
    """The reduced basis modulo another prime by the recorded matrices, or None where this prime departs from them.

    Only the recorded rows are reduced: no pairs, symbolic preprocessing, or
    rows that reduced to zero. Every row must reduce to a pivot in its
    recorded column and every result must stay within its recorded support;
    the result is then a basis inside the ideal modulo this prime with the
    recorded leading monomials, and the reduced basis whenever this prime
    reduces no recorded nonzero to zero.
    """
    var prime = ring.value
    var engine = _Engine[ModInt, W, False](kind, ring)
    engine.start(generators^, budget)
    if len(engine.polys) != len(trace.inputs):
        return None
    var values = List[List[UInt32]]()
    for i in range(len(engine.polys)):
        ref p = engine.polys[i]
        ref monomials = trace.inputs[i]
        if len(p) != len(monomials):
            return None
        _allocation[UInt32](len(p), budget)
        var residues = List[UInt32](capacity=len(p))
        for k in range(len(p) - 1, -1, -1):
            budget.charge(1)
            if not _equal(p[k].monomial, monomials[k]):
                return None
            residues.append(UInt32(p[k].coefficient.value))
        values.append(residues^)
    for step in trace.steps:
        budget.charge(1)
        var matrix = step.matrix()
        var nrows = len(matrix.sources)
        for r in range(nrows):
            if matrix.starts[r + 1] - matrix.starts[r] != len(values[matrix.sources[r]]):
                return None
        _allocation[Int](step.ncols, budget)
        var pivot = List[Int](length=step.ncols, fill=-1)
        for r in range(step.pivots):
            pivot[Int(matrix.entries[matrix.starts[r]])] = r
        var found = _Rows()
        if not step.final:
            var reduce = List[Int]()
            for r in range(step.pivots, nrows):
                reduce.append(r)
            var kept = List[Int]()
            var results = _eliminate(matrix, pivot, reduce, values, prime, ring, found, kept, budget)
            if len(kept) != len(reduce):
                return None
            for i in range(len(kept)):
                if found.columns[found.starts[i]] != step.leads[i]:
                    return None
            if not _replay_rows(found, _inserted(results, step.inserted), step.supports, values, budget):
                return None
            continue
        _tails(matrix, step.basis, pivot, values, prime, found, budget)
        var rows = List[Int]()
        for r in range(step.basis):
            rows.append(r)
        var first = len(values)
        if not _replay_rows(found, rows, step.supports, values, budget):
            return None
        var basis = List[List[_Term[ModInt, W]]](capacity=step.basis)
        for r in range(step.basis):
            ref residues = values[first + r]
            var m = len(step.supports[r])
            var terms = List[_Term[ModInt, W]](capacity=m)
            for k in range(m - 1, -1, -1):
                if residues[k] != 0:
                    terms.append(_Term[ModInt, W](step.monomial(r, k), ModInt(UInt64(residues[k]), ring)))
            basis.append(terms^)
        return basis^
    return None


comptime _LANES = 8
"""Primes a batched replay runs at once, one per SIMD lane."""

comptime _Lanes = SIMD[DType.uint64, _LANES]


struct _LaneRows(Movable):
    """Rows found during a batched replay, concatenated: each entry has a residue per prime, `_LANES` apart."""
    var columns: List[Int32]
    var values: List[UInt32]
    var starts: List[Int]
    """Where each row starts, then where the last one ends."""

    def __init__(out self):
        self.columns = List[Int32]()
        self.values = List[UInt32]()
        self.starts = [0]


struct _Primes(Movable):
    """The primes of a batched replay, one per lane, and how many still follow the recorded run."""
    var rings: List[Modulus]
    var primes: _Lanes
    var squares: _Lanes
    var reciprocals: SIMD[DType.float64, _LANES]
    var live: Int
    """Lanes 0 to live - 1 follow the run; a lane that departs takes the later ones with it."""

    def __init__(out self, rings: List[Modulus]):
        self.rings = rings.copy()
        self.primes = _Lanes(0)
        for l in range(_LANES):
            self.primes[l] = rings[l].value
        self.squares = self.primes * self.primes
        self.reciprocals = SIMD[DType.float64, _LANES](1.0) / self.primes.cast[DType.float64]()
        self.live = _LANES

    def mask(self) -> _Lanes:
        """All ones in the lanes that follow the run, zero in the others."""
        var mask = _Lanes(0)
        for l in range(self.live):
            mask[l] = UInt64.MAX
        return mask

    def depart(mut self, lane: Int):
        self.live = min(self.live, lane)


@always_inline
def _mod_lanes(v: _Lanes, lanes: _Primes) -> _Lanes:
    """Each lane of v, below 2^62, modulo its prime.

    The quotient estimated in floating point is off by one at most either
    way, so one correction each way remains.
    """
    var q = (v.cast[DType.float64]() * lanes.reciprocals).cast[DType.uint64]()
    var r = v - q * lanes.primes
    r = (r >> 63).ne(0).select(r + lanes.primes, r)
    return r.ge(lanes.primes).select(r - lanes.primes, r)


@no_inline
def _axpy_lanes(data: Pointer[mut=True, UInt64, _], columns: Pointer[mut=False, Int32, _], values: Pointer[mut=False, UInt32, _], n: Int, factor: SIMD[DType.uint32, _LANES], squares: _Lanes):
    """Add factor times a row, after its leading entry, to every lane of the dense accumulator.

    Both factors widen from 32 bits, so each product is one 32 by 32 bit
    multiplication. Inlined, the widening is lost before instructions are
    selected, which then multiply all 64 bits (as for `_axpy_block`).
    """
    var f = factor.cast[DType.uint64]()
    for k in range(1, n):
        var at = data.unsafe_offset(_LANES * Int(columns.unsafe_offset(k).unsafe_load()))
        var x = at.unsafe_load[width=_LANES]() + f * values.unsafe_offset(_LANES * k).unsafe_load[width=_LANES]().cast[DType.uint64]()
        # Below 2^63, so the sign of x - p^2 tells, which a signed comparison
        # reads in one instruction where an unsigned one takes several.
        var y = x - squares
        at.unsafe_store[width=_LANES](y.cast[DType.int64]().lt(0).select(x, y))


def _scatter_lanes[W: Int](mut dense: List[UInt64], step: _Step[W], values: List[List[UInt32]], row: Int, skip: Int):
    """Write a recorded row's residues in every lane, after its first `skip` entries, into the dense accumulator."""
    var s = step.starts[row]
    var source = values[step.sources[row]].unsafe_ptr()
    var data = dense.unsafe_ptr()
    for k in range(skip, step.starts[row + 1] - s):
        var at = data.unsafe_offset(_LANES * Int(step.entries.unsafe_get(s + k)))
        at.unsafe_store[width=_LANES](source.unsafe_offset(_LANES * k).unsafe_load[width=_LANES]().cast[DType.uint64]())


def _reduce_lanes[W: Int](mut dense: List[UInt64], ncols: Int, start: Int, pivot: List[Int], step: _Step[W], values: List[List[UInt32]], mut found: _LaneRows, lanes: _Primes, mut budget: Budget) raises PolyError:
    """As `_reduce_row` in every lane at once, for primes below 2^31.

    A column is reduced when some lane that follows the run has a nonzero
    residue there, by its pivot, or else joins `found` with every lane's
    residue; zero lanes take a zero multiple. Lanes that departed are left
    out of every decision.
    """
    var rows = len(step.sources)
    var data = dense.unsafe_ptr()
    var live = lanes.mask()
    budget.charge(UInt64(_LANES * (ncols - start)))
    for c in range(start, ncols):
        var at = data.unsafe_offset(_LANES * c)
        var v = at.unsafe_load[width=_LANES]()
        if not v.ne(0).reduce_or():
            continue
        at.unsafe_store[width=_LANES](_Lanes(0))
        v = _mod_lanes(v, lanes) & live
        if not v.ne(0).reduce_or():
            continue
        var factor = v.eq(0).select(_Lanes(0), lanes.primes - v).cast[DType.uint32]()
        var q = pivot.unsafe_get(c)
        if q >= rows:
            var r = q - rows
            var s = found.starts.unsafe_get(r)
            var n = found.starts.unsafe_get(r + 1) - s
            budget.charge(UInt64(_LANES * n))
            _axpy_lanes(data, found.columns.unsafe_ptr().unsafe_offset(s), found.values.unsafe_ptr().unsafe_offset(_LANES * s), n, factor, lanes.squares)
        elif q >= 0:
            var s = step.starts.unsafe_get(q)
            var n = step.starts.unsafe_get(q + 1) - s
            budget.charge(UInt64(_LANES * n))
            _axpy_lanes(data, step.entries.unsafe_ptr().unsafe_offset(s), values[step.sources.unsafe_get(q)].unsafe_ptr(), n, factor, lanes.squares)
        else:
            found.columns.append(Int32(c))
            var end = len(found.values)
            found.values.resize(end + _LANES, 0)
            found.values.unsafe_ptr().unsafe_offset(end).unsafe_store[width=_LANES](v.cast[DType.uint32]())


def _eliminate_lanes[W: Int](step: _Step[W], mut dense: List[UInt64], mut pivot: List[Int], values: List[List[UInt32]], mut found: _LaneRows, mut lanes: _Primes, mut budget: Budget) raises PolyError -> List[Int]:
    """As `_eliminate` on a recorded round's rows after its pivots, in every lane, each row to a pivot in its recorded column.

    A lane whose row leads elsewhere or reduces to zero departs. Returns the
    reduced new pivots, rows of `found`, by decreasing leading column.
    """
    var nrows = len(step.sources)
    var ncols = len(pivot)
    for i in range(nrows - step.pivots):
        var r = step.pivots + i
        _scatter_lanes(dense, step, values, r, 0)
        var before = len(found.columns)
        _reduce_lanes(dense, ncols, Int(step.entries[step.starts[r]]), pivot, step, values, found, lanes, budget)
        _allocation[UInt32](_product(len(found.columns) - before, 2 * _LANES), budget)
        # Each lane that follows the run leads in the recorded column.
        var lead = step.leads[i]
        var at = before
        while at < len(found.columns) and found.columns[at] < lead:
            at += 1
        var present = at < len(found.columns) and found.columns[at] == lead
        for l in range(lanes.live):
            var leads_there = present and found.values[_LANES * at + l] != 0
            for k in range(before, at):
                if found.values[_LANES * k + l] != 0:
                    leads_there = False
            if not leads_there:
                lanes.depart(l)
                break
        if lanes.live == 0:
            return List[Int]()
        # Entries before the lead are nonzero only in departed lanes.
        if at > before:
            var n = len(found.columns) - at
            for k in range(n):
                found.columns[before + k] = found.columns[at + k]
                for l in range(_LANES):
                    found.values[_LANES * (before + k) + l] = found.values[_LANES * (at + k) + l]
            found.columns.resize(before + n, 0)
            found.values.resize(_LANES * (before + n), 0)
        # A new pivot: monic in every lane that follows the run.
        var inverse = _Lanes(0)
        for l in range(lanes.live):
            inverse[l] = ModInt(UInt64(found.values[_LANES * before + l]), lanes.rings[l]).inverse(budget).value
        var p = found.values.unsafe_ptr()
        for k in range(before, len(found.columns)):
            var x = p.unsafe_offset(_LANES * k).unsafe_load[width=_LANES]().cast[DType.uint64]()
            p.unsafe_offset(_LANES * k).unsafe_store[width=_LANES](_mod_lanes(x * inverse, lanes).cast[DType.uint32]())
        pivot[Int(lead)] = nrows + len(found.starts) - 1
        found.starts.append(len(found.columns))
    # The new pivots by decreasing leading column, each reduced by the ones
    # right of its leading column, as in `_eliminate`.
    var created = List[Int]()
    for i in range(len(found.starts) - 1):
        var j = len(created)
        created.append(i)
        while j > 0 and found.columns[found.starts[created[j - 1]]] < found.columns[found.starts[i]]:
            created[j] = created[j - 1]
            j -= 1
        created[j] = i
    var results = List[Int](capacity=len(created))
    var data = dense.unsafe_ptr()
    for i in created:
        var lead = Int(found.columns[found.starts[i]])
        for k in range(found.starts[i] + 1, found.starts[i + 1]):
            data.unsafe_offset(_LANES * Int(found.columns[k])).unsafe_store[width=_LANES](found.values.unsafe_ptr().unsafe_offset(_LANES * k).unsafe_load[width=_LANES]().cast[DType.uint64]())
        var before = len(found.columns)
        found.columns.append(Int32(lead))
        for _ in range(_LANES):
            found.values.append(UInt32(1))
        _reduce_lanes(dense, ncols, lead + 1, pivot, step, values, found, lanes, budget)
        _allocation[UInt32](_product(len(found.columns) - before, 2 * _LANES), budget)
        pivot[lead] = nrows + len(found.starts) - 1
        results.append(len(found.starts) - 1)
        found.starts.append(len(found.columns))
    return results^


def _replay_rows_lanes(found: _LaneRows, results: List[Int], supports: List[List[Int32]], mut values: List[List[UInt32]], mut lanes: _Primes, mut budget: Budget) raises PolyError:
    """As `_replay_rows` in every lane: a lane departs when its result leaves the recorded support or loses its leading entry."""
    for t in range(len(results)):
        var i = results[t]
        ref support = supports[t]
        _allocation[UInt32](_product(len(support), _LANES), budget)
        var residues = List[UInt32](length=_LANES * len(support), fill=0)
        var j = 0
        for k in range(found.starts[i], found.starts[i + 1]):
            budget.charge(UInt64(_LANES))
            while j < len(support) and support[j] < found.columns[k]:
                j += 1
            if j == len(support) or support[j] != found.columns[k]:
                for l in range(lanes.live):
                    if found.values[_LANES * k + l] != 0:
                        lanes.depart(l)
                        break
                continue
            for l in range(_LANES):
                residues[_LANES * j + l] = found.values[_LANES * k + l]
        for l in range(lanes.live):
            if residues[l] == 0:
                lanes.depart(l)
                break
        values.append(residues^)


struct _LaneBases(Movable):
    """The bases of a batched replay, over the recorded final supports.

    Element r's residue modulo lane l's prime at the k-th monomial of its
    support, by decreasing monomial, is values[r][_LANES * k + l]; lanes 0
    to live - 1 have bases.
    """
    var values: List[List[UInt32]]
    var live: Int

    def __init__(out self):
        self.values = List[List[UInt32]]()
        self.live = 0


def _lane_basis[W: Int](trace: _Trace[W], bases: _LaneBases, lane: Int, ring: Modulus, mut budget: Budget) raises PolyError -> List[List[_Term[ModInt, W]]]:
    """The basis of one lane, as `_f4_replay` returns it for the lane's prime."""
    ref step = trace.steps[len(trace.steps) - 1]
    var basis = List[List[_Term[ModInt, W]]](capacity=step.basis)
    for r in range(step.basis):
        ref residues = bases.values[r]
        var m = len(step.supports[r])
        _allocation[_Term[ModInt, W]](m, budget)
        var terms = List[_Term[ModInt, W]](capacity=m)
        for k in range(m - 1, -1, -1):
            var residue = residues[_LANES * k + lane]
            if residue != 0:
                terms.append(_Term[ModInt, W](step.monomial(r, k), ModInt(UInt64(residue), ring)))
        basis.append(terms^)
    return basis^


def _f4_replay_lanes[W: Int](trace: _Trace[W], var generators: List[List[List[_Term[ModInt, W]]]], kind: UInt8, rings: List[Modulus], mut budget: Budget) raises PolyError -> List[List[List[_Term[ModInt, W]]]]:
    """`_f4_replay` modulo `_LANES` primes below 2^31 at once, one per SIMD lane.

    Returns the bases of the primes before the first whose replay declines,
    each exactly what `_f4_replay` returns for it: lanes share the recorded
    matrices, and a lane with a zero residue where another has not takes a
    zero multiple.
    """
    var bases = _f4_replay_bases(trace, generators^, kind, rings, budget)
    var result = List[List[List[_Term[ModInt, W]]]]()
    for l in range(bases.live):
        result.append(_lane_basis(trace, bases, l, rings[l], budget))
    return result^


def _f4_replay_bases[W: Int](trace: _Trace[W], var generators: List[List[List[_Term[ModInt, W]]]], kind: UInt8, rings: List[Modulus], mut budget: Budget) raises PolyError -> _LaneBases:
    """As `_f4_replay_lanes`, with the bases as residues over the recorded supports."""
    var lanes = _Primes(rings)
    var values = List[List[UInt32]]()
    for l in range(_LANES):
        var engine = _Engine[ModInt, W, False](kind, rings[l])
        var own = List[List[_Term[ModInt, W]]]()
        swap(own, generators[l])
        engine.start(own^, budget)
        var follows = len(engine.polys) == len(trace.inputs)
        if follows and l == 0:
            for i in range(len(engine.polys)):
                _allocation[UInt32](_product(len(engine.polys[i]), _LANES), budget)
                values.append(List[UInt32](length=_LANES * len(engine.polys[i]), fill=0))
        for i in range(len(engine.polys)):
            if not follows:
                break
            ref p = engine.polys[i]
            ref monomials = trace.inputs[i]
            if len(p) != len(monomials):
                follows = False
                break
            for k in range(len(p) - 1, -1, -1):
                budget.charge(1)
                if not _equal(p[k].monomial, monomials[k]):
                    follows = False
                    break
                values[i][_LANES * (len(p) - 1 - k) + l] = UInt32(p[k].coefficient.value)
        if not follows:
            lanes.depart(l)
            break
    var bases = _LaneBases()
    if lanes.live == 0:
        return bases^
    var width = 0
    for step in trace.steps:
        width = max(width, step.ncols)
    _allocation[UInt64](_product(width, _LANES), budget)
    var dense = List[UInt64](length=_LANES * width, fill=0)
    for step in trace.steps:
        budget.charge(1)
        var nrows = len(step.sources)
        for r in range(nrows):
            if step.starts[r + 1] - step.starts[r] != len(values[step.sources[r]]) // _LANES:
                return bases^
        _allocation[Int](step.ncols, budget)
        var pivot = List[Int](length=step.ncols, fill=-1)
        for r in range(step.pivots):
            pivot[Int(step.entries[step.starts[r]])] = r
        var found = _LaneRows()
        if not step.final:
            var results = _eliminate_lanes(step, dense, pivot, values, found, lanes, budget)
            if lanes.live == 0:
                return bases^
            _replay_rows_lanes(found, _inserted(results, step.inserted), step.supports, values, lanes, budget)
            if lanes.live == 0:
                return bases^
            continue
        # The final matrix: the basis rows' tails reduced against all rows.
        for r in range(step.basis):
            var first = Int(step.entries[step.starts[r]])
            _scatter_lanes(dense, step, values, r, 1)
            found.columns.append(Int32(first))
            for l in range(_LANES):
                found.values.append(values[step.sources[r]][l])
            _reduce_lanes(dense, step.ncols, first + 1, pivot, step, values, found, lanes, budget)
            _allocation[UInt32](_product(len(found.columns) - found.starts[len(found.starts) - 1], 2 * _LANES), budget)
            found.starts.append(len(found.columns))
        var rows = List[Int](capacity=step.basis)
        for r in range(step.basis):
            rows.append(r)
        var first = len(values)
        _replay_rows_lanes(found, rows, step.supports, values, lanes, budget)
        bases.live = lanes.live
        for r in range(step.basis):
            var residues = List[UInt32]()
            swap(residues, values[first + r])
            bases.values.append(residues^)
        return bases^
    return bases^


def _f4_basis[W: Int](generators: List[SparsePoly[ModInt]], order: MonomialOrder, mut budget: Budget) raises PolyError -> List[SparsePoly[ModInt]]:
    var ring = generators[0].ring.copy()
    _allocation[List[_Term[ModInt, W]]](len(generators), budget)
    var packed = List[List[_Term[ModInt, W]]](capacity=len(generators))
    for g in generators:
        budget.charge(1)
        packed.append(_pack[ModInt, W](g.reorder(order, budget), order, budget))
    var basis = _f4_packed[W](packed^, order.kind, ring, budget)
    var by_index = _priorities(order, budget)
    _allocation[SparsePoly[ModInt]](len(basis), budget)
    var result = List[SparsePoly[ModInt]](capacity=len(basis))
    for i in range(len(basis)):
        budget.charge(1)
        # Each packed element goes as soon as it is unpacked.
        var p = List[_Term[ModInt, W]]()
        swap(p, basis[i])
        result.append(_unpack(p, order, ring, by_index, budget))
    return result^


def _f4_supported(order: MonomialOrder, prime: UInt64) -> Bool:
    """F4 here handles degree orders over primes below 2^31."""
    return order.kind != MonomialOrder.LEX and order.kind != MonomialOrder.KERNEL and len(order.variables) <= 16 and prime < _F4_PRIME_LIMIT


def _f4_groebner(generators: List[SparsePoly[ModInt]], order: MonomialOrder, mut budget: Budget) raises PolyError -> List[SparsePoly[ModInt]]:
    """The reduced monic basis by F4; generators share a field and the order is supported."""
    if len(generators) == 0:
        return List[SparsePoly[ModInt]]()
    if len(order.variables) <= 8:
        return _f4_basis[8](generators, order, budget)
    return _f4_basis[16](generators, order, budget)
