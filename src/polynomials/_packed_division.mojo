"""Exact sparse division over packed monomial keys with a quotient heap.

The exact quotient does not depend on the monomial order used to compute it,
so the division runs in LEX order over the variables of both operands, each
exponent in a bit field wide enough for the dividend's degree in that
variable. Johnson's algorithm keeps one heap entry per quotient term, the
next product q_i g_j still to subtract, so no intermediate remainder is ever
materialized. A quotient term whose exponent exceeds deg f - deg g in some
variable cannot belong to an exact quotient, which bounds every product's
fields and rejects inexact inputs early.
"""
from .errors import Budget, PolyError, _allocation, _charge_size, _sum, _product
from .coefficients import CoefficientRing, ModInt
from ._nmod_euclid import _Field
from .sparse import SparsePoly, Term
from .monomial import Monomial
from ._coefficient_ops import _quotient


struct _Packing(Movable):
    """Bit fields of a LEX key: variables[0] is the most significant field."""
    var variables: List[Int64]
    var shifts: List[Int]
    var masks: List[UInt128]

    def __init__(out self):
        self.variables = List[Int64]()
        self.shifts = List[Int]()
        self.masks = List[UInt128]()

    def key(self, m: Monomial, mut budget: Budget) raises PolyError -> UInt128:
        _charge_size(len(m.pairs), budget)
        var key = UInt128(0)
        var position = 0
        for pair in m.pairs:
            while self.variables[position] != pair[0]:
                position += 1
            key |= UInt128(pair[1]) << UInt128(self.shifts[position])
        return key

    def field(self, key: UInt128, position: Int) -> Int:
        return Int((key >> UInt128(self.shifts[position])) & self.masks[position])

    def monomial(self, key: UInt128, mut budget: Budget) raises PolyError -> Monomial:
        var pairs = List[Tuple[Int64, UInt32]]()
        for position in range(len(self.variables)):
            var e = self.field(key, position)
            if e:
                pairs.append((self.variables[position], UInt32(e)))
        return Monomial(pairs^, budget)


def _bit_length(value: Int) -> Int:
    var bits = 0
    while (value >> bits) != 0:
        bits += 1
    return bits


# Exponent boxes up to this many cells divide on dense arrays instead of a heap.
comptime _DENSE_CELLS = 1 << 22


def _box_index(m: Monomial, variables: List[Int64], strides: List[Int]) -> Int:
    var index = 0
    var position = 0
    for pair in m.pairs:
        while variables[position] != pair[0]:
            position += 1
        index += Int(pair[1]) * strides[position]
    return index


def _box_divide[C: CoefficientRing](f: SparsePoly[C], g: SparsePoly[C], variables: List[Int64], bounds: List[Int], mut budget: Budget) raises PolyError -> Optional[SparsePoly[C]]:
    """Exact division on a dense mixed-radix array over f's exponent box.

    Indices are LEX keys with radix deg_v(f) + 1 per variable (variables[0]
    most significant), so a descending scan visits the remainder's leading
    terms in order, and adding a quotient index to a divisor index never
    carries because every field stays within deg_v(f).
    """
    var n = len(variables)
    var radices = List[Int](capacity=n)
    for v in variables:
        radices.append(f.degree_in(v, budget) + 1)
    var strides = List[Int](length=n, fill=1)
    for position in range(n - 2, -1, -1):
        strides[position] = strides[position + 1] * radices[position + 1]
    var cells = strides[0] * radices[0]
    _charge_size(cells, budget)
    var g_index = List[Int](capacity=len(g.terms))
    var lead = 0
    for i in range(len(g.terms)):
        g_index.append(_box_index(g.terms[i].monomial, variables, strides))
        if g_index[i] > g_index[lead]:
            lead = i
    var lead_index = g_index[lead]
    var lead_fields = List[Int](capacity=n)
    for position in range(n):
        lead_fields.append((lead_index // strides[position]) % radices[position])
    var q_index = List[Int]()
    var q_coefficients = List[C]()
    var q_words = List[UInt64]()
    var words = False
    comptime if C == ModInt:
        words = rebind[ModInt](f.terms[0].coefficient).modulus > 2
    if words:
        comptime if C == ModInt:
            var field = _Field.of(rebind[ModInt](f.terms[0].coefficient).modulus)
            _allocation[UInt64](cells, budget)
            var r = List[UInt64](length=cells, fill=0)
            for t in f.terms:
                r[_box_index(t.monomial, variables, strides)] = field.enter(rebind[ModInt](t.coefficient).value)
            var gw = List[UInt64](capacity=len(g.terms))
            for t in g.terms:
                gw.append(field.enter(rebind[ModInt](t.coefficient).value))
            var inverse = field.inverse(gw[lead])
            for position in range(cells - 1, lead_index - 1, -1):
                if r[position] == 0:
                    continue
                budget.charge(1)
                for axis in range(n):
                    var e = (position // strides[axis]) % radices[axis] - lead_fields[axis]
                    if e < 0 or e > bounds[axis]:
                        return None
                var c = field.mul(r[position], inverse)
                var base = position - lead_index
                _charge_size(len(g.terms), budget)
                for j in range(len(g.terms)):
                    if j != lead:
                        r[base + g_index[j]] = field.sub(r[base + g_index[j]], field.mul(c, gw[j]))
                r[position] = 0
                q_index.append(base)
                q_words.append(field.leave(c))
            for position in range(lead_index):
                if r[position] != 0:
                    return None
            _allocation[Term[C]](len(q_index), budget)
            var terms = List[Term[C]](capacity=len(q_index))
            var context = rebind[ModInt](f.terms[0].coefficient).context()
            for i in range(len(q_index)):
                terms.append(Term[C](_box_monomial(q_index[i], variables, strides, radices, budget), rebind_var[C](ModInt(q_words[i], context))))
            return SparsePoly[C].from_terms(terms^, f.order, f.ring, budget)
    _allocation[C](cells, budget)
    var r = List[C](length=cells, fill=C.zero(f.ring))
    for t in f.terms:
        r[_box_index(t.monomial, variables, strides)] = t.coefficient.copy()
    ref lc = g.terms[lead].coefficient
    for position in range(cells - 1, lead_index - 1, -1):
        if r[position].is_zero():
            continue
        budget.charge(1)
        for axis in range(n):
            var e = (position // strides[axis]) % radices[axis] - lead_fields[axis]
            if e < 0 or e > bounds[axis]:
                return None
        var q = _quotient(r[position], lc, budget)
        if not q:
            return None
        ref c = q.value()
        var base = position - lead_index
        _charge_size(len(g.terms), budget)
        for j in range(len(g.terms)):
            if j != lead:
                r[base + g_index[j]] = r[base + g_index[j]].sub(c.mul(g.terms[j].coefficient, budget), budget)
        r[position] = C.zero(f.ring)
        q_index.append(base)
        q_coefficients.append(c.copy())
    for position in range(lead_index):
        if not r[position].is_zero():
            return None
    _allocation[Term[C]](len(q_index), budget)
    var terms = List[Term[C]](capacity=len(q_index))
    for i in range(len(q_index)):
        terms.append(Term[C](_box_monomial(q_index[i], variables, strides, radices, budget), q_coefficients[i].copy()))
    return SparsePoly[C].from_terms(terms^, f.order, f.ring, budget)


def _box_monomial(index: Int, variables: List[Int64], strides: List[Int], radices: List[Int], mut budget: Budget) raises PolyError -> Monomial:
    var pairs = List[Tuple[Int64, UInt32]]()
    for position in range(len(variables)):
        var e = (index // strides[position]) % radices[position]
        if e:
            pairs.append((variables[position], UInt32(e)))
    return Monomial(pairs^, budget)


@fieldwise_init
struct _Entry(ImplicitlyCopyable, Movable):
    var key: UInt128
    var row: Int
    var column: Int


def _push(mut heap: List[_Entry], entry: _Entry):
    heap.append(entry)
    var child = len(heap) - 1
    while child > 0:
        var parent = (child - 1) // 2
        if heap[parent].key >= heap[child].key:
            break
        var t = heap[parent]
        heap[parent] = heap[child]
        heap[child] = t
        child = parent


def _pop(mut heap: List[_Entry]) -> _Entry:
    var top = heap[0]
    var last = heap.pop()
    if len(heap):
        heap[0] = last
        var parent = 0
        var n = len(heap)
        while True:
            var child = 2 * parent + 1
            if child >= n:
                break
            if child + 1 < n and heap[child + 1].key > heap[child].key:
                child += 1
            if heap[parent].key >= heap[child].key:
                break
            var t = heap[parent]
            heap[parent] = heap[child]
            heap[child] = t
            parent = child
    return top


def _packed_divide[C: CoefficientRing](f: SparsePoly[C], g: SparsePoly[C], mut applicable: Bool, mut budget: Budget) raises PolyError -> Optional[SparsePoly[C]]:
    """Divide exactly when every exponent fits a 128-bit key; set applicable to False otherwise."""
    applicable = False
    if f.is_zero() or g.is_zero():
        return None
    var variables = f.variables(budget)
    for v in g.variables(budget):
        budget.charge(1)
        var found = False
        for w in variables:
            if w == v:
                found = True
                break
        if not found:
            # g uses a variable f lacks, so no exact quotient exists.
            applicable = True
            return None
    var packing = _Packing()
    var bounds = List[Int]()
    var total = 0
    for v in variables:
        budget.charge(1)
        var df = f.degree_in(v, budget)
        var dg = g.degree_in(v, budget)
        if dg > df:
            applicable = True
            return None
        var bits = max(_bit_length(df), 1)
        total = _sum(total, bits)
        packing.variables.append(v)
        packing.masks.append((UInt128(1) << UInt128(bits)) - 1)
        packing.shifts.append(bits)
        bounds.append(df - dg)
    var cells = 1
    for v in variables:
        cells = _product(cells, f.degree_in(v, budget) + 1)
        if cells > _DENSE_CELLS:
            break
    if len(variables) > 0 and cells <= _DENSE_CELLS and cells <= _product(32, len(f.terms)):
        applicable = True
        return _box_divide(f, g, packing.variables, bounds, budget)
    if total > 128:
        return None
    applicable = True
    # Turn widths into shifts, variables[0] in the highest field.
    var shift = total
    for position in range(len(packing.variables)):
        shift -= packing.shifts[position]
        packing.shifts[position] = shift
    _allocation[UInt128](_sum(len(f.terms), len(g.terms)), budget)
    var f_keys = List[UInt128](capacity=len(f.terms))
    for t in f.terms:
        f_keys.append(packing.key(t.monomial, budget))
    var g_keys = List[UInt128](capacity=len(g.terms))
    for t in g.terms:
        g_keys.append(packing.key(t.monomial, budget))
    # Stored orders differ from LEX on these fields; sort term indices by key, descending.
    var f_order = _descending(f_keys, budget)
    var g_order = _descending(g_keys, budget)
    var lead = g_order[0]
    var lead_key = g_keys[lead]
    ref lead_coefficient = g.terms[lead].coefficient
    var lead_fields = List[Int](capacity=len(packing.variables))
    for position in range(len(packing.variables)):
        lead_fields.append(packing.field(lead_key, position))
    var q_keys = List[UInt128]()
    var q_coefficients = List[C]()
    # Odd prime fields run on Montgomery words: one inverse of lc(g), no 128-bit remainders.
    var words = False
    var field = _Field.of(3)
    var f_words = List[UInt64]()
    var g_words = List[UInt64]()
    var q_words = List[UInt64]()
    var lead_inverse = UInt64(0)
    comptime if C == ModInt:
        var p = rebind[ModInt](f.terms[0].coefficient).modulus
        if p > 2:
            words = True
            field = _Field.of(p)
            _allocation[UInt64](_sum(len(f.terms), len(g.terms)), budget)
            for t in f.terms:
                f_words.append(field.enter(rebind[ModInt](t.coefficient).value))
            for t in g.terms:
                g_words.append(field.enter(rebind[ModInt](t.coefficient).value))
            lead_inverse = field.inverse(g_words[lead])
    var heap = List[_Entry]()
    var next_f = 0
    while next_f < len(f_order) or len(heap):
        budget.charge(1)
        var key: UInt128
        if not len(heap):
            key = f_keys[f_order[next_f]]
        elif next_f == len(f_order):
            key = heap[0].key
        else:
            key = max(heap[0].key, f_keys[f_order[next_f]])
        var accumulated = C.zero(f.ring)
        var word = UInt64(0)
        if next_f < len(f_order) and f_keys[f_order[next_f]] == key:
            if words:
                word = f_words[f_order[next_f]]
            else:
                accumulated = f.terms[f_order[next_f]].coefficient.copy()
            next_f += 1
        while len(heap) and heap[0].key == key:
            budget.charge(1)
            var entry = _pop(heap)
            var index = g_order[entry.column]
            if words:
                word = field.sub(word, field.mul(q_words[entry.row], g_words[index]))
            else:
                accumulated = accumulated.sub(q_coefficients[entry.row].mul(g.terms[index].coefficient, budget), budget)
            var column = entry.column + 1
            if column < len(g_order):
                _push(heap, _Entry(q_keys[entry.row] + g_keys[g_order[column]], entry.row, column))
        if (words and word == 0) or (not words and accumulated.is_zero()):
            continue
        # The remainder's leading term must be a multiple of g's within the degree bounds.
        for position in range(len(packing.variables)):
            var e = packing.field(key, position) - lead_fields[position]
            if e < 0 or e > bounds[position]:
                return None
        var row = len(q_keys)
        _ = _sum(row, 1)
        _allocation[Term[C]](1, budget)
        if words:
            q_words.append(field.mul(word, lead_inverse))
        else:
            var coefficient = _quotient(accumulated, lead_coefficient, budget)
            if not coefficient:
                return None
            q_coefficients.append(coefficient.take())
        q_keys.append(key - lead_key)
        if len(g_order) > 1:
            _push(heap, _Entry(q_keys[row] + g_keys[g_order[1]], row, 1))
    _allocation[Term[C]](len(q_keys), budget)
    var terms = List[Term[C]](capacity=len(q_keys))
    for i in range(len(q_keys)):
        budget.charge(1)
        comptime if C == ModInt:
            if words:
                terms.append(Term[C](packing.monomial(q_keys[i], budget), rebind_var[C](ModInt(field.leave(q_words[i]), rebind[ModInt](f.terms[0].coefficient).context()))))
                continue
        terms.append(Term[C](packing.monomial(q_keys[i], budget), q_coefficients[i].copy()))
    return SparsePoly[C].from_terms(terms^, f.order, f.ring, budget)


def _descending(keys: List[UInt128], mut budget: Budget) raises PolyError -> List[Int]:
    """Indices of distinct keys in decreasing key order, by heap sort."""
    _allocation[_Entry](len(keys), budget)
    var heap = List[_Entry](capacity=len(keys))
    for i in range(len(keys)):
        budget.charge(1)
        _push(heap, _Entry(keys[i], i, 0))
    var order = List[Int](capacity=len(keys))
    while len(heap):
        budget.charge(1)
        order.append(_pop(heap).row)
    return order^
