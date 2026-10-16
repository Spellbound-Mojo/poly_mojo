"""F4 over prime fields below 2^31, on packed exponent vectors.

Faugère's F4 replaces Buchberger's one-at-a-time S-polynomial reduction with
linear algebra: each round selects every pending pair whose LCM has the least
degree, writes both halves of each S-polynomial as rows, adds a reducer row
for every monomial a basis element's leading monomial divides (symbolic
preprocessing), and row-reduces the resulting sparse matrix. Rows whose
leading monomial no pivot covers are new basis elements. Pairs are still
pruned by the Gebauer–Möller criteria of the packed engine, which also stores
the basis and computes the final reduced basis; the reduced basis is unique,
so the result is the one Buchberger's algorithm returns.

Monomials become matrix columns through a hash table; the hash is linear in
the exponents, so a product's hash is the sum of its factors' and each basis
element's term hashes are computed once. Rows store 32-bit column numbers and
residues and are reduced in a dense accumulator of 64-bit words, which is
reduced modulo p only when an entry is read: below 2^16 the products of
residues fit in 32 bits and plain sums cannot overflow; below 2^31 they fit in
62 bits and each entry stays below p^2 by one conditional subtraction. The
accumulator skips runs of zero words eight at a time. The final reduced basis
is computed by one more matrix, whose rows are the basis elements and their
reducers.

`groebner` uses F4 for untracked bases over primes below 2^31 under GRLEX and
GREVLEX, over at most sixteen variables; other cases use Buchberger's
algorithm in the packed or sparse engine.
"""
from std.math import iota, min
from .coefficients import ModInt, Modulus
from .errors import Budget, PolyError, _allocation
from .monomial import MonomialOrder
from .sparse import SparsePoly
from ._packed_groebner import _Engine, _Packed, _Term, _compare, _div, _divides, _equal, _mul, _pack, _priorities, _unpack

comptime _F4_PRIME_LIMIT = UInt64(1) << 31


@always_inline
def _raw_hash[W: Int](m: _Packed[W]) -> UInt64:
    """A hash linear in the exponents, so a product's is the sum of its factors'."""
    comptime multipliers = (iota[DType.uint64, W]() * 0x9E3779B97F4A7C15 + 0xC2B2AE3D27D4EB4F) | 1
    return (m.exponents().cast[DType.uint64]() * multipliers).reduce_add()


@always_inline
def _mix(raw: UInt64) -> UInt64:
    var h = raw ^ (raw >> 31)
    h *= 0xBF58476D1CE4E5B9
    return h ^ (h >> 29)


struct _Columns[W: Int](Movable):
    """Distinct monomials, numbered in order of first appearance, with a hash index."""
    var monomials: List[_Packed[Self.W]]
    var hashes: List[UInt64]
    """Each monomial's raw hash, for rehashing."""
    var slots: List[Int]
    """Open addressing: 0 is empty, otherwise one more than a monomial's number."""
    var mask: Int

    def __init__(out self):
        self.monomials = List[_Packed[Self.W]]()
        self.hashes = List[UInt64]()
        self.slots = List[Int](length=1024, fill=0)
        self.mask = 1023

    def index(mut self, m: _Packed[Self.W], raw: UInt64, mut added: Bool, mut budget: Budget) raises PolyError -> Int:
        """The number of m, whose raw hash is `raw`, added when new."""
        if 2 * (len(self.monomials) + 1) > len(self.slots):
            self._grow(budget)
        var h = Int(_mix(raw) & UInt64(self.mask))
        while True:
            var slot = self.slots.unsafe_get(h)
            if slot == 0:
                _allocation[_Packed[Self.W]](1, budget)
                self.monomials.append(m)
                self.hashes.append(raw)
                self.slots[h] = len(self.monomials)
                added = True
                return len(self.monomials) - 1
            if self.hashes.unsafe_get(slot - 1) == raw and _equal(self.monomials.unsafe_get(slot - 1), m):
                added = False
                return slot - 1
            h = (h + 1) & self.mask

    def _grow(mut self, mut budget: Budget) raises PolyError:
        var size = len(self.slots) * 2
        _allocation[Int](size, budget)
        self.slots = List[Int](length=size, fill=0)
        self.mask = size - 1
        for i in range(len(self.monomials)):
            var h = Int(_mix(self.hashes[i]) & UInt64(self.mask))
            while self.slots[h] != 0:
                h = (h + 1) & self.mask
            self.slots[h] = i + 1


def _sort_descending[W: Int](kind: UInt8, monomials: List[_Packed[W]], mut budget: Budget) raises PolyError -> List[Int]:
    """Indices of `monomials` from greatest to least, by bottom-up merge sort."""
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


struct _Matrix[W: Int](Movable):
    """One F4 round: rows as multiples of basis elements, then as sparse residue rows."""
    var columns: _Columns[Self.W]
    var sources: List[Int]
    """The basis element of each row."""
    var shifts: List[_Packed[Self.W]]
    """The monomial each row's basis element is multiplied by."""
    var entries: List[List[Int]]
    """Each row's column numbers, leading term first."""
    var covered: List[Bool]
    """Whether some row leads with the column's monomial."""

    def __init__(out self):
        self.columns = _Columns[Self.W]()
        self.sources = List[Int]()
        self.shifts = List[_Packed[Self.W]]()
        self.entries = List[List[Int]]()
        self.covered = List[Bool]()

    def column(mut self, m: _Packed[Self.W], raw: UInt64, mut todo: List[Int], mut budget: Budget) raises PolyError -> Int:
        """The column of m, created and queued for preprocessing when new."""
        var added = False
        var c = self.columns.index(m, raw, added, budget)
        if added:
            self.covered.append(False)
            todo.append(c)
        return c

    def add_row(mut self, engine: _Engine[ModInt, Self.W, False], hashes: List[List[UInt64]], source: Int, shift: _Packed[Self.W], mut todo: List[Int], mut budget: Budget) raises PolyError:
        """Add shift * engine.polys[source]; `hashes` holds each element's term hashes."""
        ref p = engine.polys[source]
        ref h = hashes[source]
        var base = _raw_hash(shift)
        budget.charge(UInt64(len(p)))
        _allocation[Int](len(p), budget)
        var columns = List[Int](capacity=len(p))
        for k in range(len(p) - 1, -1, -1):
            columns.append(self.column(_mul(p[k].monomial, shift), base + h[k], todo, budget))
        self.covered[columns[0]] = True
        self.sources.append(source)
        self.shifts.append(shift)
        self.entries.append(columns^)


def _reduce_row(mut dense: List[UInt64], start: Int, pivot: List[Int], cols: List[List[Int32]], vals: List[List[UInt32]], prime: UInt64, mut out_cols: List[Int32], mut out_vals: List[UInt32], mut budget: Budget) raises PolyError:
    if prime < 65536:
        _reduce_row_in[True](dense, start, pivot, cols, vals, prime, out_cols, out_vals, budget)
    else:
        _reduce_row_in[False](dense, start, pivot, cols, vals, prime, out_cols, out_vals, budget)


def _reduce_row_in[small: Bool](mut dense: List[UInt64], start: Int, pivot: List[Int], cols: List[List[Int32]], vals: List[List[UInt32]], prime: UInt64, mut out_cols: List[Int32], mut out_vals: List[UInt32], mut budget: Budget) raises PolyError:
    """Reduce the row scattered in `dense` from column `start` on, appending what no pivot covers.

    For p < 2^16 products are below 2^32, and an entry receives at most one
    product per column before it is read, so plain 64-bit sums cannot
    overflow. Otherwise entries stay below p^2: each update adds a product
    below p^2 < 2^62 and subtracts p^2 when the sum reaches it. Visited entries
    are cleared, so `dense` is all zero again afterwards. Runs of zero words
    are skipped eight at a time.
    """
    var square = prime * prime
    var ncols = len(dense)
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
        if q >= 0:
            var factor = prime - v
            ref qc = cols[q]
            ref qv = vals[q]
            budget.charge(UInt64(len(qc)))
            for k in range(1, len(qc)):
                var j = Int(qc.unsafe_get(k))
                var x = data.unsafe_offset(j).unsafe_load() + factor * UInt64(qv.unsafe_get(k))
                comptime if small:
                    data.unsafe_offset(j).unsafe_store(x)
                else:
                    data.unsafe_offset(j).unsafe_store(x - square if x >= square else x)
        else:
            out_cols.append(Int32(c))
            out_vals.append(UInt32(v))
        c += 1


def _round[W: Int](mut engine: _Engine[ModInt, W, False], hashes: List[List[UInt64]], prime: UInt64, ring: Modulus, mut budget: Budget) raises PolyError -> List[List[_Term[ModInt, W]]]:
    """Run one F4 round on the pairs of least LCM degree; return the new elements, monic."""
    var degree = engine.pairs[0].lcm.degree
    var matrix = _Matrix[W]()
    var todo = List[Int]()
    # Both halves of every selected pair. A half is fixed by its element and
    # its leading monomial, the pair's LCM, so equal halves are added once.
    var seen = Dict[Int, Bool]()
    var stride = len(engine.polys)
    while len(engine.pairs) and engine.pairs[0].lcm.degree == degree:
        var pair = engine.select(budget)
        var lead = matrix.column(pair.lcm, _raw_hash(pair.lcm), todo, budget)
        for source in [pair.first, pair.second]:
            budget.charge(1)
            var key = lead * stride + source
            if key in seen:
                continue
            seen[key] = True
            matrix.add_row(engine, hashes, source, _div(pair.lcm, engine.leads[source]), todo, budget)
    var pair_rows = len(matrix.entries)
    # Symbolic preprocessing: one reducer per monomial some leading monomial divides.
    var next = 0
    while next < len(todo):
        var c = todo[next]
        next += 1
        if matrix.covered[c]:
            continue
        var u = matrix.columns.monomials[c]
        for g in engine.active:
            budget.charge(1)
            if _divides(engine.leads[g], u):
                matrix.add_row(engine, hashes, g, _div(u, engine.leads[g]), todo, budget)
                break
    # Number columns from the greatest monomial down.
    var ncols = len(matrix.columns.monomials)
    var order = _sort_descending(engine.kind, matrix.columns.monomials, budget)
    _allocation[Int](ncols, budget)
    var position = List[Int](length=ncols, fill=0)
    for i in range(ncols):
        position[order[i]] = i
    # Sparse rows of residues; every row is a multiple of a monic element.
    var nrows = len(matrix.entries)
    _allocation[List[Int]](nrows, budget)
    var cols = List[List[Int32]](capacity=nrows)
    var vals = List[List[UInt32]](capacity=nrows)
    for r in range(nrows):
        ref p = engine.polys[matrix.sources[r]]
        ref e = matrix.entries[r]
        budget.charge(UInt64(len(e)))
        _allocation[UInt32](2 * len(e), budget)
        var rc = List[Int32](capacity=len(e))
        var rv = List[UInt32](capacity=len(e))
        for k in range(len(e)):
            rc.append(Int32(position[e[k]]))
            rv.append(UInt32(p[len(p) - 1 - k].coefficient.value))
        cols.append(rc^)
        vals.append(rv^)
    # Pivots: every reducer row, then the first pair row for each leading column.
    _allocation[Int](ncols, budget)
    var pivot = List[Int](length=ncols, fill=-1)
    for r in range(pair_rows, nrows):
        pivot[Int(cols[r][0])] = r
    var reduce = List[Int]()
    for r in range(pair_rows):
        if pivot[Int(cols[r][0])] < 0:
            pivot[Int(cols[r][0])] = r
        else:
            reduce.append(r)
    # Reduce the remaining rows, in order, against every pivot so far.
    _allocation[UInt64](ncols, budget)
    var dense = List[UInt64](length=ncols, fill=0)
    var created = List[Int]()
    for r in reduce:
        var first = Int(cols[r][0])
        for k in range(len(cols[r])):
            dense[Int(cols[r][k])] = UInt64(vals[r][k])
        var out_cols = List[Int32]()
        var out_vals = List[UInt32]()
        _reduce_row(dense, first, pivot, cols, vals, prime, out_cols, out_vals, budget)
        if len(out_cols) == 0:
            continue
        # A new pivot: monic, and used by the rows that follow.
        var inverse = ModInt(UInt64(out_vals[0]), ring).inverse(budget).value
        for k in range(len(out_vals)):
            out_vals[k] = UInt32((UInt64(out_vals[k]) * inverse) % prime)
        pivot[Int(out_cols[0])] = len(cols)
        created.append(len(cols))
        cols.append(out_cols^)
        vals.append(out_vals^)
    # New elements, smallest leading monomial (greatest column) first, as
    # increasing term lists.
    for i in range(1, len(created)):
        var value = created[i]
        var j = i
        while j > 0 and cols[created[j - 1]][0] < cols[value][0]:
            created[j] = created[j - 1]
            j -= 1
        created[j] = value
    var fresh = List[List[_Term[ModInt, W]]]()
    for i in range(len(created)):
        ref rc = cols[created[i]]
        ref rv = vals[created[i]]
        _allocation[_Term[ModInt, W]](len(rc), budget)
        var terms = List[_Term[ModInt, W]](capacity=len(rc))
        for k in range(len(rc) - 1, -1, -1):
            terms.append(_Term[ModInt, W](matrix.columns.monomials[order[Int(rc[k])]], ModInt(UInt64(rv[k]), ring)))
        fresh.append(terms^)
    return fresh^


def _interreduce[W: Int](mut engine: _Engine[ModInt, W, False], hashes: List[List[UInt64]], prime: UInt64, ring: Modulus, mut budget: Budget) raises PolyError -> List[List[_Term[ModInt, W]]]:
    """The reduced basis from the active elements, by one matrix, in decreasing leading-monomial order.

    Every active element is a row, and symbolic preprocessing adds a reducer
    for each tail monomial some leading monomial divides; active leading
    monomials are mutually nondividing, so all rows lead in distinct columns.
    Reducing each element's tail by the other rows leaves no monomial that a
    leading monomial divides: the reduced basis.
    """
    engine.sort_active(budget)
    var matrix = _Matrix[W]()
    var todo = List[Int]()
    var one = _Packed[W](SIMD[DType.uint32, W](0), 0, 0)
    for position in range(len(engine.active) - 1, -1, -1):
        matrix.add_row(engine, hashes, engine.active[position], one, todo, budget)
    var basis_rows = len(matrix.entries)
    var next = 0
    while next < len(todo):
        var c = todo[next]
        next += 1
        if matrix.covered[c]:
            continue
        var u = matrix.columns.monomials[c]
        for g in engine.active:
            budget.charge(1)
            if _divides(engine.leads[g], u):
                matrix.add_row(engine, hashes, g, _div(u, engine.leads[g]), todo, budget)
                break
    var ncols = len(matrix.columns.monomials)
    var order = _sort_descending(engine.kind, matrix.columns.monomials, budget)
    _allocation[Int](2 * ncols, budget)
    var position = List[Int](length=ncols, fill=0)
    for i in range(ncols):
        position[order[i]] = i
    var nrows = len(matrix.entries)
    var cols = List[List[Int32]](capacity=nrows)
    var vals = List[List[UInt32]](capacity=nrows)
    var pivot = List[Int](length=ncols, fill=-1)
    for r in range(nrows):
        ref p = engine.polys[matrix.sources[r]]
        ref e = matrix.entries[r]
        budget.charge(UInt64(len(e)))
        _allocation[UInt32](2 * len(e), budget)
        var rc = List[Int32](capacity=len(e))
        var rv = List[UInt32](capacity=len(e))
        for k in range(len(e)):
            rc.append(Int32(position[e[k]]))
            rv.append(UInt32(p[len(p) - 1 - k].coefficient.value))
        pivot[Int(rc[0])] = r
        cols.append(rc^)
        vals.append(rv^)
    _allocation[UInt64](ncols, budget)
    var dense = List[UInt64](length=ncols, fill=0)
    var basis = List[List[_Term[ModInt, W]]](capacity=basis_rows)
    for r in range(basis_rows):
        var first = Int(cols[r][0])
        for k in range(1, len(cols[r])):
            dense[Int(cols[r][k])] = UInt64(vals[r][k])
        var out_cols: List[Int32] = [Int32(first)]
        var out_vals: List[UInt32] = [vals[r][0]]
        _reduce_row(dense, first + 1, pivot, cols, vals, prime, out_cols, out_vals, budget)
        _allocation[_Term[ModInt, W]](len(out_cols), budget)
        var terms = List[_Term[ModInt, W]](capacity=len(out_cols))
        for k in range(len(out_cols) - 1, -1, -1):
            terms.append(_Term[ModInt, W](matrix.columns.monomials[order[Int(out_cols[k])]], ModInt(UInt64(out_vals[k]), ring)))
        basis.append(terms^)
    return basis^


def _extend_hashes[W: Int](engine: _Engine[ModInt, W, False], mut hashes: List[List[UInt64]], mut budget: Budget) raises PolyError:
    """Add the raw term hashes of basis elements inserted since the last call."""
    for i in range(len(hashes), len(engine.polys)):
        ref p = engine.polys[i]
        budget.charge(UInt64(len(p)))
        _allocation[UInt64](len(p), budget)
        var h = List[UInt64](capacity=len(p))
        for t in p:
            h.append(_raw_hash(t.monomial))
        hashes.append(h^)


def _f4_basis[W: Int](generators: List[SparsePoly[ModInt]], order: MonomialOrder, mut budget: Budget) raises PolyError -> List[SparsePoly[ModInt]]:
    var ring = generators[0].ring.copy()
    var prime = ring.value
    _allocation[List[_Term[ModInt, W]]](len(generators), budget)
    var packed = List[List[_Term[ModInt, W]]](capacity=len(generators))
    for g in generators:
        budget.charge(1)
        packed.append(_pack[ModInt, W](g.reorder(order, budget), order, budget))
    var engine = _Engine[ModInt, W, False](order.kind, ring)
    engine.start(packed^, budget)
    var hashes = List[List[UInt64]]()
    while len(engine.pairs):
        budget.charge(1)
        engine.sort_active(budget)
        _extend_hashes(engine, hashes, budget)
        var fresh = _round(engine, hashes, prime, ring, budget)
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
                engine.sort_active(budget)
                p = engine.reduce_base(p^, engine.active, budget)
                if len(p) == 0:
                    continue
            engine.insert(p^, budget)
    _extend_hashes(engine, hashes, budget)
    var basis = _interreduce(engine, hashes, prime, ring, budget)
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
