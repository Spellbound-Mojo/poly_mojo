"""F4 over prime fields below 2^31, on packed exponent vectors.

Faugère's F4 replaces Buchberger's one-at-a-time S-polynomial reduction with
linear algebra: each round selects every pending pair whose LCM has the least
degree, writes both halves of each S-polynomial as rows, adds a reducer row
for every monomial a basis element's leading monomial divides (symbolic
preprocessing), and row-reduces the resulting sparse matrix. Rows whose
leading monomial no pivot covers are new basis elements; they are reduced by
one another too, so each round's new elements are in reduced row echelon
form, which keeps the rows they later contribute sparse. Pairs are still
pruned by the Gebauer–Möller criteria of the packed engine; the reduced basis
is unique, so the result is the one Buchberger's algorithm returns. The
elements' terms are kept once, compactly: each term is the number of a
monomial in a table every element shares, and a residue.

Every row is a multiple of a basis element, so a row stores only its column
numbers, concatenated with the other rows'; its residues are the element's,
kept once. Monomials become matrix columns through a hash table; the hash is
linear in the exponents, with pseudo-random multipliers, so a product's hash
is the sum of its factors' and each basis element's term hashes are computed
once. Rows are reduced in a dense accumulator of 64-bit words, which is
reduced modulo p only when an entry is read: below 2^16 the products of
residues fit in 32 bits and plain sums cannot overflow; below 2^31 they fit in
62 bits and each entry stays below p^2 by one conditional subtraction. The
accumulator skips runs of zero words eight at a time. The final reduced basis
is computed by one more matrix, whose rows are the basis elements and their
reducers.

A run can be recorded (`_f4_learn`) and replayed modulo another prime
(`_f4_replay`): the replay reduces only the recorded rows that gave new
elements, against the recorded pivots, with no pairs, symbolic
preprocessing, or rows that reduced to zero, and declines as soon as a row
leads elsewhere or a result leaves its recorded support. A replay can also run
modulo `_LANES` primes at once (`_f4_replay_lanes`): the recorded matrices are
the same for every prime, so each accumulator column holds a residue per
prime in one SIMD vector, and every update is one vector operation.

`groebner` uses F4 for untracked bases over primes below 2^31 under GRLEX and
GREVLEX, over at most sixteen variables; other cases use Buchberger's
algorithm in the packed or sparse engine.
"""
from std.math import max, min
from .coefficients import CoefficientRing, ModInt, Modulus
from .errors import Budget, PolyError, PolyErrorKind, _allocation, _product, _sum
from .monomial import MonomialOrder
from .sparse import SparsePoly
from ._packed_groebner import _Engine, _Packed, _Term, _compare, _div, _divides, _equal, _mul, _pack, _packed, _priorities, _unpack

comptime _F4_PRIME_LIMIT = UInt64(1) << 31
comptime _COLUMN_LIMIT = Int(Int32.MAX)
comptime _TAG = UInt64(0xFFFFFFFF00000000)
"""The bits of a hash slot that hold the high half of the monomial's mixed hash."""


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
    """Each basis element's terms, leading term first, as numbers of distinct monomials, and over a prime field their residues.

    The monomials of all elements are kept once, with their hashes: elements
    share most of their monomials, so a term costs a 32-bit number and a
    32-bit residue, and F4 can drop the engine's own term lists (`release`).
    """
    var monomials: _Columns[Self.W]
    var hashes: List[UInt64]
    """The raw hash of each distinct monomial."""
    var terms: List[List[UInt32]]
    var values: List[List[UInt32]]
    var tops: List[_Packed[Self.W]]
    """The greatest exponent of each variable among each element's terms."""

    def __init__(out self):
        self.monomials = _Columns[Self.W]()
        self.hashes = List[UInt64]()
        self.terms = List[List[UInt32]]()
        self.values = List[List[UInt32]]()
        self.tops = List[_Packed[Self.W]]()

    def extend[C: CoefficientRing, integral: Bool](mut self, engine: _Engine[C, Self.W, integral], mut budget: Budget) raises PolyError:
        """Add the elements inserted since the last call; residues only over a prime field."""
        for i in range(len(self.terms), len(engine.polys)):
            ref p = engine.polys[i]
            var n = len(p)
            budget.charge(UInt64(n))
            _allocation[UInt32](2 * n, budget)
            self.monomials.reserve(n, budget)
            var numbers = List[UInt32](capacity=n)
            var v = List[UInt32](capacity=n)
            var top = SIMD[DType.uint32, Self.W](0)
            for k in range(n - 1, -1, -1):
                ref t = p[k]
                var raw = _raw_hash(t.monomial)
                var number = Int(self.monomials.find(t.monomial, raw))
                if number == len(self.hashes):
                    self.hashes.append(raw)
                numbers.append(UInt32(number))
                comptime if C == ModInt:
                    v.append(UInt32(rebind[ModInt](t.coefficient).value))
                top = max(top, t.monomial.exponents())
            self.terms.append(numbers^)
            self.values.append(v^)
            self.tops.append(_packed(top))

    def release[C: CoefficientRing, integral: Bool](self, mut engine: _Engine[C, Self.W, integral]):
        """Drop the engine's term lists of the stored elements; `restore` brings them back."""
        for i in range(len(self.terms)):
            engine.polys[i] = List[_Term[C, Self.W]]()

    def restore(self, mut engine: _Engine[ModInt, Self.W, False], indices: List[Int], mut budget: Budget) raises PolyError:
        """Rebuild the engine's term lists of the elements `indices`, in increasing order."""
        for i in indices:
            if i >= len(self.terms):
                continue  # Not stored yet, so never released.
            ref numbers = self.terms[i]
            ref v = self.values[i]
            var n = len(numbers)
            budget.charge(UInt64(n))
            _allocation[_Term[ModInt, Self.W]](n, budget)
            var p = List[_Term[ModInt, Self.W]](capacity=n)
            for k in range(n - 1, -1, -1):
                p.append(_Term[ModInt, Self.W](self.monomials.monomials[Int(numbers[k])], ModInt(UInt64(v[k]), engine.ring)))
            engine.polys[i] = p^


struct _Columns[W: Int](Movable):
    """Distinct monomials, numbered in order of first appearance, with a hash index."""
    var monomials: List[_Packed[Self.W]]
    var covered: List[Bool]
    """Whether some row leads with the monomial."""
    var slots: List[UInt64]
    """Open addressing: 0 is empty, otherwise the high half of the monomial's
    mixed hash over one more than its number."""
    var mask: Int

    def __init__(out self):
        self.monomials = List[_Packed[Self.W]]()
        self.covered = List[Bool]()
        self.slots = List[UInt64](length=1024, fill=0)
        self.mask = 1023

    def reserve(mut self, count: Int, mut budget: Budget) raises PolyError:
        """Make room for `count` more monomials, keeping the table at most half full."""
        var total = _sum(len(self.monomials), count)
        if total > _COLUMN_LIMIT:
            raise PolyError(PolyErrorKind.CAPACITY, "F4 matrix column count overflow")
        _allocation[_Packed[Self.W]](count, budget)
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
            var mixed = _mix(_raw_hash(self.monomials[i]))
            var h = Int(mixed & UInt64(self.mask))
            while self.slots[h] != 0:
                h = (h + 1) & self.mask
            self.slots[h] = (mixed & _TAG) | UInt64(i + 1)

    @always_inline
    def find(mut self, m: _Packed[Self.W], raw: UInt64) -> Int32:
        """The number of m, whose raw hash is `raw`, added when new; `reserve` must have made room."""
        var mixed = _mix(raw)
        var tag = mixed & _TAG
        var h = Int(mixed & UInt64(self.mask))
        while True:
            var slot = self.slots.unsafe_get(h)
            if slot == 0:
                self.monomials.append(m)
                self.covered.append(False)
                self.slots.unsafe_get(h) = tag | UInt64(len(self.monomials))
                return Int32(len(self.monomials) - 1)
            if slot & _TAG == tag:
                var c = Int(slot & ~_TAG) - 1
                if _equal(self.monomials.unsafe_get(c), m):
                    return Int32(c)
            h = (h + 1) & self.mask


def _sort_descending[W: Int](kind: UInt8, monomials: List[_Packed[W]], mut budget: Budget) raises PolyError -> List[Int]:
    """Indices of `monomials` from greatest to least, by bottom-up merge sort."""
    comptime if W <= 8:
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
    """Keys whose integer order is the monomial order, each with its index in the low 32 bits; None unless every exponent is below 2^8 and every degree below 2^16.

    From the top: the degree (zero under LEX), then one byte per lane in
    the order that decides, which under GREVLEX is from the last lane up,
    with the exponent complemented, since a smaller one there is greater.
    """
    comptime assert W <= 8, "one byte per lane in 64 bits"
    var n = len(monomials)
    _allocation[UInt128](n, budget)
    budget.charge(UInt64(n))
    var keys = List[UInt128](capacity=n)
    for i in range(n):
        ref m = monomials.unsafe_get(i)
        var e = m.exponents()
        if m.degree >= (1 << 16) or e.reduce_max() >= 256:
            return None
        var digits = UInt64(0)
        comptime for j in range(W):
            var lane = UInt64(e[W - 1 - j]) if kind == MonomialOrder.GREVLEX else UInt64(e[j])
            var digit = UInt64(255) - lane if kind == MonomialOrder.GREVLEX else lane
            digits |= digit << UInt64(8 * (7 - j))
        var degree = UInt128(0) if kind == MonomialOrder.LEX else UInt128(m.degree)
        keys.append((degree << 112) | (UInt128(digits) << 48) | UInt128(i))
    return keys^


def _sort_keys(var keys: List[UInt128], mut budget: Budget) raises PolyError -> List[Int]:
    """The indices in the low 32 bits of distinct keys, by decreasing key."""
    var n = len(keys)
    _allocation[UInt128](n, budget)
    var scratch = List[UInt128](length=n, fill=0)
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
    _allocation[Int](n, budget)
    var order = List[Int](capacity=n)
    for k in range(n):
        order.append(Int(keys.unsafe_get(k) & UInt128(0xFFFFFFFF)))
    return order^


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
        """Add shift * engine.polys[source], from its stored terms."""
        ref numbers = store.terms[source]
        ref monomials = store.monomials.monomials
        var n = len(numbers)
        # Some product's exponent overflows exactly when the greatest exponents' does.
        _ = _mul(store.tops[source], shift)
        budget.charge(UInt64(n))
        _allocation[Int32](n, budget)
        self.columns.reserve(n, budget)
        var base = _raw_hash(shift)
        var first = len(self.entries)
        for k in range(n):
            var number = Int(numbers.unsafe_get(k))
            self.entries.append(self.columns.find(_times(monomials.unsafe_get(number), shift), base + store.hashes.unsafe_get(number)))
        self.columns.covered[Int(self.entries[first])] = True
        self.sources.append(source)
        self.starts.append(len(self.entries))

    def preprocess[C: CoefficientRing, integral: Bool](mut self, engine: _Engine[C, Self.W, integral], store: _Store[Self.W], mut budget: Budget) raises PolyError:
        """Symbolic preprocessing: a reducer for each monomial some active leading monomial divides.

        The reducer is the active element with the least such leading monomial;
        `engine.active` must be sorted, and the order graded, so the search
        stops at the first leading monomial of greater degree.
        """
        _allocation[_Packed[Self.W]](len(engine.active), budget)
        var leads = List[_Packed[Self.W]](capacity=len(engine.active))
        for g in engine.active:
            leads.append(engine.leads[g])
        var next = 0
        while next < len(self.columns.monomials):
            var c = next
            next += 1
            if self.columns.covered[c]:
                continue
            var u = self.columns.monomials[c]
            var found = -1
            var i = 0
            while i < len(leads):
                ref lead = leads.unsafe_get(i)
                if lead.degree > u.degree:
                    break
                if _divides(lead, u):
                    found = i
                    break
                i += 1
            budget.charge(UInt64(i + 1))
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
def _axpy[small: Bool](data: Pointer[mut=True, UInt64, _], columns: Pointer[mut=False, Int32, _], values: Pointer[mut=False, UInt32, _], n: Int, factor: UInt64, square: UInt64):
    """Add factor times a row, after its leading entry, to the dense accumulator."""
    for k in range(1, n):
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
    the order the results come; the final matrix also keeps the monomial of
    each column.
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
        self.columns = List[_Packed[Self.W]]()

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
    var usable: Bool
    """False when the run inserted an element outside its matrices."""

    def __init__(out self):
        self.inputs = List[List[_Packed[Self.W]]]()
        self.steps = List[_Step[Self.W]]()
        self.usable = True


def _eliminate[W: Int](matrix: _Matrix[W], mut pivot: List[Int], reduce: List[Int], values: List[List[UInt32]], prime: UInt64, ring: Modulus, mut found: _Rows, mut kept: List[Int], mut budget: Budget) raises PolyError -> List[Int]:
    """Reduce rows `reduce` in turn, each nonzero remainder becoming a monic pivot; then reduce the new pivots by one another.

    `kept` gets the rows that gave pivots. Returns the reduced new pivots,
    rows of `found`, by decreasing leading column.
    """
    var nrows = len(matrix.sources)
    var ncols = len(pivot)
    _allocation[UInt64](ncols, budget)
    var dense = List[UInt64](length=ncols, fill=0)
    for r in reduce:
        _scatter(dense, matrix, values, r, 0)
        var before = len(found.columns)
        _reduce_row(dense, Int(matrix.entries[matrix.starts[r]]), pivot, matrix, values, found, prime, budget)
        if len(found.columns) == before:
            continue
        _allocation[UInt32](2 * (len(found.columns) - before), budget)
        # A new pivot: monic, and used by the rows that follow.
        var inverse = ModInt(UInt64(found.values[before]), ring).inverse(budget).value
        for k in range(before, len(found.values)):
            found.values[k] = UInt32((UInt64(found.values[k]) * inverse) % prime)
        pivot[Int(found.columns[before])] = nrows + len(found.starts) - 1
        found.starts.append(len(found.columns))
        kept.append(r)
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


def _round[W: Int, record: Bool](mut engine: _Engine[ModInt, W, False], store: _Store[W], prime: UInt64, ring: Modulus, mut trace: _Trace[W], mut budget: Budget) raises PolyError -> List[List[_Term[ModInt, W]]]:
    """Run one F4 round on the pairs of least LCM degree; return the new elements, monic."""
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
        trace.steps.append(step^)
    # The new elements, smallest leading monomial first, as increasing term lists.
    var fresh = List[List[_Term[ModInt, W]]]()
    for i in results:
        var n = found.starts[i + 1] - found.starts[i]
        _allocation[_Term[ModInt, W]](n, budget)
        var terms = List[_Term[ModInt, W]](capacity=n)
        for k in range(found.starts[i + 1] - 1, found.starts[i] - 1, -1):
            terms.append(_Term[ModInt, W](matrix.columns.monomials[order[Int(found.columns[k])]], ModInt(UInt64(found.values[k]), ring)))
        fresh.append(terms^)
    return fresh^


def _interreduce[W: Int, record: Bool](mut engine: _Engine[ModInt, W, False], store: _Store[W], prime: UInt64, ring: Modulus, mut trace: _Trace[W], mut budget: Budget) raises PolyError -> _Final[W]:
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
    var final = _Final[W](ring)
    swap(final.found, found)
    swap(final.monomials, matrix.columns.monomials)
    final.order = order^
    return final^


struct _Final[W: Int](Movable):
    """The reduced basis as the final matrix leaves it: one row of `found` per element, in decreasing leading-monomial order."""
    var found: _Rows
    var monomials: List[_Packed[Self.W]]
    """The matrix's monomials, in order of first appearance."""
    var order: List[Int]
    """The monomial at each column."""
    var ring: Modulus

    def __init__(out self, ring: Modulus):
        self.found = _Rows()
        self.monomials = List[_Packed[Self.W]]()
        self.order = List[Int]()
        self.ring = ring

    def packed(self, mut budget: Budget) raises PolyError -> List[List[_Term[ModInt, Self.W]]]:
        """The elements as increasing term lists."""
        var basis = List[List[_Term[ModInt, Self.W]]](capacity=len(self.found.starts) - 1)
        for r in range(len(self.found.starts) - 1):
            var n = self.found.starts[r + 1] - self.found.starts[r]
            _allocation[_Term[ModInt, Self.W]](n, budget)
            var terms = List[_Term[ModInt, Self.W]](capacity=n)
            for k in range(self.found.starts[r + 1] - 1, self.found.starts[r] - 1, -1):
                terms.append(_Term[ModInt, Self.W](self.monomials[self.order[Int(self.found.columns[k])]], ModInt(UInt64(self.found.values[k]), self.ring)))
            basis.append(terms^)
        return basis^


def _f4_run[W: Int, record: Bool](var generators: List[List[_Term[ModInt, W]]], kind: UInt8, ring: Modulus, mut trace: _Trace[W], mut budget: Budget) raises PolyError -> _Final[W]:
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
        # The released term lists come back once a round, when the first element needs them.
        var restored = False
        for k in range(len(fresh)):
            var p = List[_Term[ModInt, W]]()
            swap(p, fresh[k])
            # An element found earlier in this round may divide this one's leading monomial.
            var divided = False
            for g in engine.active:
                budget.charge(1)
                if _divides(engine.leads[g], p[len(p) - 1].monomial):
                    divided = True
                    break
            if divided:
                # Reduced outside the matrices, so a replay could not follow.
                trace.usable = False
                engine.sort_active(budget)
                if not restored:
                    store.restore(engine, engine.active.copy(), budget)
                    restored = True
                p = engine.reduce_base(p^, engine.active, budget)
                if len(p) == 0:
                    continue
            engine.insert(p^, budget)
    store.extend(engine, budget)
    store.release(engine)
    return _interreduce[W, record](engine, store, prime, ring, trace, budget)


def _f4_packed[W: Int](var generators: List[List[_Term[ModInt, W]]], kind: UInt8, ring: Modulus, mut budget: Budget) raises PolyError -> List[List[_Term[ModInt, W]]]:
    """The reduced monic basis of packed generators, in decreasing leading-monomial order.

    Generators are increasing term lists over a degree order `kind` and a
    prime below 2^31; zero generators are allowed.
    """
    var trace = _Trace[W]()
    return _f4_run[W, False](generators^, kind, ring, trace, budget).packed(budget)


def _f4_learn[W: Int](var generators: List[List[_Term[ModInt, W]]], kind: UInt8, ring: Modulus, mut trace: _Trace[W], mut budget: Budget) raises PolyError -> List[List[_Term[ModInt, W]]]:
    """As `_f4_packed`, recording the run in `trace` for `_f4_replay`."""
    trace = _Trace[W]()
    return _f4_run[W, True](generators^, kind, ring, trace, budget).packed(budget)


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
            if not _replay_rows(found, results, step.supports, values, budget):
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
            ref support = step.supports[r]
            var terms = List[_Term[ModInt, W]](capacity=len(support))
            for k in range(len(support) - 1, -1, -1):
                if residues[k] != 0:
                    terms.append(_Term[ModInt, W](step.columns[Int(support[k])], ModInt(UInt64(residues[k]), ring)))
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


@always_inline
def _axpy_lanes(data: Pointer[mut=True, UInt64, _], columns: Pointer[mut=False, Int32, _], values: Pointer[mut=False, UInt32, _], n: Int, factor: SIMD[DType.uint32, _LANES], squares: _Lanes):
    """Add factor times a row, after its leading entry, to every lane of the dense accumulator.

    Both factors widen from 32 bits, so each product is one 32 by 32 bit
    multiplication.
    """
    var f = factor.cast[DType.uint64]()
    for k in range(1, n):
        var at = data.unsafe_offset(_LANES * Int(columns.unsafe_offset(k).unsafe_load()))
        var x = at.unsafe_load[width=_LANES]() + f * values.unsafe_offset(_LANES * k).unsafe_load[width=_LANES]().cast[DType.uint64]()
        at.unsafe_store[width=_LANES](x.ge(squares).select(x - squares, x))


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
            for l in range(_LANES):
                found.values.append(UInt32(v[l]))


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
    """The reduced bases a batched replay found, as residues on the recorded final supports: `_LANES` per entry, one per prime.

    Kept this way, a basis costs four bytes a term until `basis` writes it out.
    """
    var residues: List[List[UInt32]]
    """Each basis element's residues, `_LANES` apart, on its support in the recorded final matrix."""
    var rings: List[Modulus]
    var count: Int
    """The lanes 0 to count - 1 hold bases."""

    def __init__(out self):
        self.residues = List[List[UInt32]]()
        self.rings = List[Modulus]()
        self.count = 0

    def basis[W: Int](self, l: Int, trace: _Trace[W]) -> List[List[_Term[ModInt, W]]]:
        """The basis of lane l, from the run `trace` that the replay followed."""
        ref step = trace.steps[len(trace.steps) - 1]
        var basis = List[List[_Term[ModInt, W]]](capacity=len(self.residues))
        for r in range(len(self.residues)):
            ref residues = self.residues[r]
            ref support = step.supports[r]
            var terms = List[_Term[ModInt, W]](capacity=len(support))
            for k in range(len(support) - 1, -1, -1):
                var residue = residues[_LANES * k + l]
                if residue != 0:
                    terms.append(_Term[ModInt, W](step.columns[Int(support[k])], ModInt(UInt64(residue), self.rings[l])))
            basis.append(terms^)
        return basis^


def _f4_replay_lanes[W: Int](trace: _Trace[W], var generators: List[List[List[_Term[ModInt, W]]]], kind: UInt8, rings: List[Modulus], mut budget: Budget) raises PolyError -> _LaneBases:
    """`_f4_replay` modulo `_LANES` primes below 2^31 at once, one per SIMD lane.

    Returns the bases of the primes before the first whose replay declines,
    each exactly what `_f4_replay` returns for it: lanes share the recorded
    matrices, and a lane with a zero residue where another has not takes a
    zero multiple.
    """
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
            _replay_rows_lanes(found, results, step.supports, values, lanes, budget)
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
        for r in range(step.basis):
            var residues = List[UInt32]()
            swap(residues, values[first + r])
            bases.residues.append(residues^)
        bases.rings = rings.copy()
        bases.count = lanes.live
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
