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
accumulator skips runs of zero words eight at a time. The final reduced basis
is computed by one more matrix, whose rows are the basis elements and their
reducers.

A run can be recorded (`_f4_learn`) and replayed modulo another prime
(`_f4_replay`): the replay reduces only the recorded rows that gave new
elements, against the recorded pivots, with no pairs, symbolic
preprocessing, or rows that reduced to zero, and declines as soon as a row
leads elsewhere or a result leaves its recorded support.

`groebner` uses F4 for untracked bases over primes below 2^31 under GRLEX and
GREVLEX, over at most sixteen variables; other cases use Buchberger's
algorithm in the packed or sparse engine.
"""
from std.math import max, min
from .coefficients import CoefficientRing, ModInt, Modulus
from .errors import Budget, PolyError, PolyErrorKind, _allocation, _sum
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
    """Each basis element's term hashes and, over a prime field, residues, leading term first."""
    var hashes: List[List[UInt64]]
    var values: List[List[UInt32]]
    var tops: List[_Packed[Self.W]]
    """The greatest exponent of each variable among each element's terms."""

    def __init__(out self):
        self.hashes = List[List[UInt64]]()
        self.values = List[List[UInt32]]()
        self.tops = List[_Packed[Self.W]]()

    def extend[C: CoefficientRing, integral: Bool](mut self, engine: _Engine[C, Self.W, integral], mut budget: Budget) raises PolyError:
        """Add the elements inserted since the last call; residues only over a prime field."""
        for i in range(len(self.hashes), len(engine.polys)):
            ref p = engine.polys[i]
            var n = len(p)
            budget.charge(UInt64(n))
            _allocation[UInt64](n, budget)
            _allocation[UInt32](n, budget)
            var h = List[UInt64](capacity=n)
            var v = List[UInt32](capacity=n)
            var top = SIMD[DType.uint32, Self.W](0)
            for k in range(n - 1, -1, -1):
                ref t = p[k]
                h.append(_raw_hash(t.monomial))
                comptime if C == ModInt:
                    v.append(UInt32(rebind[ModInt](t.coefficient).value))
                top = max(top, t.monomial.exponents())
            self.hashes.append(h^)
            self.values.append(v^)
            self.tops.append(_packed(top))


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
        """Add shift * engine.polys[source]."""
        ref p = engine.polys[source]
        ref h = store.hashes[source]
        var n = len(p)
        # Some product's exponent overflows exactly when the greatest exponents' does.
        _ = _mul(store.tops[source], shift)
        budget.charge(UInt64(n))
        _allocation[Int32](n, budget)
        self.columns.reserve(n, budget)
        var base = _raw_hash(shift)
        var first = len(self.entries)
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
    the order the results come; the final matrix also keeps their monomials.
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
    var monomials: List[List[_Packed[Self.W]]]

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
        self.monomials = List[List[_Packed[Self.W]]]()

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
        for r in range(basis_rows):
            var monomials = List[_Packed[W]]()
            for k in range(found.starts[r], found.starts[r + 1]):
                monomials.append(matrix.columns.monomials[order[Int(found.columns[k])]])
            step.monomials.append(monomials^)
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
        var fresh = _round[W, record](engine, store, prime, ring, trace, budget)
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
                p = engine.reduce_base(p^, engine.active, budget)
                if len(p) == 0:
                    continue
            engine.insert(p^, budget)
    store.extend(engine, budget)
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
            ref monomials = step.monomials[r]
            var terms = List[_Term[ModInt, W]](capacity=len(monomials))
            for k in range(len(monomials) - 1, -1, -1):
                if residues[k] != 0:
                    terms.append(_Term[ModInt, W](monomials[k], ModInt(UInt64(residues[k]), ring)))
            basis.append(terms^)
        return basis^
    return None


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
    for p in basis:
        budget.charge(1)
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
