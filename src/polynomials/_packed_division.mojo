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
from .errors import Budget, PolyError, _allocation, _charge_size, _sum
from .coefficients import CoefficientRing
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
        if next_f < len(f_order) and f_keys[f_order[next_f]] == key:
            accumulated = f.terms[f_order[next_f]].coefficient.copy()
            next_f += 1
        while len(heap) and heap[0].key == key:
            budget.charge(1)
            var entry = _pop(heap)
            var index = g_order[entry.column]
            accumulated = accumulated.sub(q_coefficients[entry.row].mul(g.terms[index].coefficient, budget), budget)
            var column = entry.column + 1
            if column < len(g_order):
                _push(heap, _Entry(q_keys[entry.row] + g_keys[g_order[column]], entry.row, column))
        if accumulated.is_zero():
            continue
        # The remainder's leading term must be a multiple of g's within the degree bounds.
        for position in range(len(packing.variables)):
            var e = packing.field(key, position) - lead_fields[position]
            if e < 0 or e > bounds[position]:
                return None
        var coefficient = _quotient(accumulated, lead_coefficient, budget)
        if not coefficient:
            return None
        var row = len(q_keys)
        _ = _sum(row, 1)
        _allocation[Term[C]](1, budget)
        q_keys.append(key - lead_key)
        q_coefficients.append(coefficient.take())
        if len(g_order) > 1:
            _push(heap, _Entry(q_keys[row] + g_keys[g_order[1]], row, 1))
    _allocation[Term[C]](len(q_keys), budget)
    var terms = List[Term[C]](capacity=len(q_keys))
    for i in range(len(q_keys)):
        budget.charge(1)
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
