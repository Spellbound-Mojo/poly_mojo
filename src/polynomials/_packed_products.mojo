"""Packed-exponent products and exact quotients of sparse ZZ and GF(p) polynomials in LEX order.

A monomial over variables 0..n-1 becomes one machine word by Kronecker
substitution with mixed radices: radix_i exceeds the largest exponent of
variable i that the result can hold, and variable 0 is the most significant
digit. Within those bounds the map is additive (monomial products are key
sums, with no carries) and increasing (LEX comparison is integer comparison).

Products split the key into a prefix of the first L variables and a low part
of the rest, with L the smallest count whose low range fits a dense window.
Each output prefix collects the pairs of operand groups whose prefixes sum to
it, accumulates their products in the dense window, and emits the window's
touched slots in increasing order, so the output arrives sorted without a
heap or a sort of the terms. ZZ coefficients of at most 63 bits accumulate in
192-bit two's complement words; GF(p) residues accumulate in 128-bit words.

Exact quotients use the same chunks from the top prefix down: with h the
divisor's top prefix, the dividend chunk at prefix t minus the known products
of earlier quotient chunks equals the quotient chunk at t - h times the
divisor's top chunk. When that top chunk is a single term, each quotient
chunk follows term by term.

Every choice depends on sizes and exponents only, never on time.
"""
from apn_mojo import Integer
from .coefficients import CoefficientRing, ZZ, ModInt, _mod_mul
from .errors import Budget, PolyError, PolyErrorKind, _allocation, _charge_size, _product, _sum
from .monomial import Monomial, MonomialOrder
from .sparse import SparsePoly, Term
from std.collections import Dict
from std.math import log2

comptime _WINDOW = 1 << 18
"""The largest dense accumulation window, in slots."""
comptime _POWER_GATE = 1
"""The power recurrence runs when its heap steps stay below this many times the products of the last square."""
comptime _POWER_SPREAD = UInt64(2)
"""The largest base exponent for which the power recurrence runs."""
comptime _KEY_LIMIT = UInt64(1) << 62
"""Keys stay below this, so prefix and window arithmetic never wraps."""


struct _Packing(Copyable, Movable):
    """Mixed radices over variables 0..n-1 and the prefix/window split."""
    var n: Int
    var radix: List[UInt64]
    var weight: List[UInt64]
    """weight[i] = radix[i+1] * ... * radix[n-1]: the place value of variable i."""
    var prefix_count: Int
    """L, the number of leading variables in the prefix."""
    var window: UInt64
    """The low range: radix[L] * ... * radix[n-1]."""

    def __init__(out self, var radix: List[UInt64], limit: Int = _WINDOW):
        self.n = len(radix)
        self.weight = List[UInt64](length=self.n, fill=1)
        var i = self.n - 2
        while i >= 0:
            self.weight[i] = self.weight[i + 1] * radix[i + 1]
            i -= 1
        self.prefix_count = 0
        self.window = (self.weight[0] * radix[0]) if self.n else 1
        while self.prefix_count < self.n and self.window > UInt64(limit):
            self.window = self.weight[self.prefix_count]
            self.prefix_count += 1
        self.radix = radix^

    def split(mut self, prefix_count: Int):
        """Use the first prefix_count variables as the prefix (at least the current count)."""
        while self.prefix_count < prefix_count and self.prefix_count < self.n:
            self.window = self.weight[self.prefix_count]
            self.prefix_count += 1

    def key(self, m: Monomial) -> UInt64:
        var k = UInt64(0)
        for pair in m.pairs:
            k += UInt64(pair[1]) * self.weight[Int(pair[0])]
        return k

    def monomial(self, key: UInt64, mut budget: Budget) raises PolyError -> Monomial:
        var count = 0
        var rest = key
        for i in range(self.n):
            var e = rest // self.weight[i]
            rest -= e * self.weight[i]
            count += Int(e != 0)
        _allocation[Tuple[Int64, UInt32]](count, budget)
        var pairs = List[Tuple[Int64, UInt32]](capacity=count)
        rest = key
        for i in range(self.n):
            var e = rest // self.weight[i]
            rest -= e * self.weight[i]
            if e:
                pairs.append((Int64(i), UInt32(e)))
        var result = Monomial()
        result.pairs = pairs^
        return result^

    def exponent(self, key: UInt64, i: Int) -> UInt64:
        return (key // self.weight[i]) % self.radix[i]


def _lex_identity[C: CoefficientRing](p: SparsePoly[C]) -> Bool:
    """Whether p is in LEX over variables 0..n-1 in priority order, using only those."""
    if p.order.kind != MonomialOrder.LEX or not p.order._identity():
        return False
    for term in p.terms:
        if not p.order._within(term.monomial):
            return False
    return True


def _maxima[C: CoefficientRing](p: SparsePoly[C], n: Int) -> List[UInt64]:
    var result = List[UInt64](length=n, fill=0)
    for term in p.terms:
        for pair in term.monomial.pairs:
            result[Int(pair[0])] = max(result[Int(pair[0])], UInt64(pair[1]))
    return result^


def _radices(a: List[UInt64], b: List[UInt64]) -> Optional[List[UInt64]]:
    """radix_i = a_i + b_i + 1, or None when the key range reaches _KEY_LIMIT."""
    var radix = List[UInt64](capacity=len(a))
    var total = UInt128(1)
    for i in range(len(a)):
        var r = a[i] + b[i] + 1
        total *= UInt128(r)
        if total >= UInt128(_KEY_LIMIT):
            return None
        radix.append(r)
    return radix^


# ----------------------------------------------------------- coefficients

@always_inline
def _small[C: CoefficientRing](c: C) -> Bool:
    comptime if C == ZZ:
        return rebind[ZZ](c).value.magnitude_bit_length() <= 63
    else:
        return True


def _signed[C: CoefficientRing](c: C) -> Int64:
    """A ZZ coefficient of at most 63 bits, or a residue (as its bits)."""
    comptime if C == ZZ:
        try:
            return rebind[ZZ](c).value.to_native_exact[DType.int64]()
        except:
            return 0
    elif C == ModInt:
        return Int64(rebind[ModInt](c).value)
    else:
        return 0


struct _Accumulator(Movable):
    """Dense window slots.

    ZZ slots hold two's complement sums: 128 bits in `lows`, extended to 192
    bits by `highs` when the coefficient bound needs it (`wide`). GF(p)
    slots hold unreduced 128-bit sums. Tracking records the touched slots
    of sparse prefixes; dense prefixes scan the window instead.
    """
    var lows: List[UInt128]
    var highs: List[UInt64]
    var touched_flag: List[UInt8]
    var touched: List[Int]

    def __init__(out self, slots: Int, wide: Bool):
        self.lows = List[UInt128](length=slots, fill=0)
        self.highs = List[UInt64](length=slots if wide else 0, fill=0)
        self.touched_flag = List[UInt8](length=slots, fill=0)
        self.touched = List[Int]()

    @always_inline
    def touch(mut self, slot: Int):
        if not self.touched_flag.unsafe_get(slot):
            self.touched_flag.unsafe_get(slot) = 1
            self.touched.append(slot)

    @always_inline
    def add_signed[wide: Bool, track: Bool](mut self, slot: Int, a: Int64, b: Int64):
        """Add a * b for |a|, |b| < 2^63."""
        comptime if track:
            self.touch(slot)
        var product = Int128(a) * Int128(b)
        self._add[wide](slot, UInt128(product), UInt64(0) - UInt64(Int(product < 0)))

    @always_inline
    def _add[wide: Bool](mut self, slot: Int, value: UInt128, extension: UInt64):
        """Add the two's complement value whose bits above 128 are all `extension`."""
        var old = self.lows.unsafe_get(slot)
        var new = old + value
        self.lows.unsafe_get(slot) = new
        comptime if wide:
            self.highs.unsafe_get(slot) += extension + UInt64(Int(new < old))

    def add_integer[wide: Bool](mut self, slot: Int, value: Integer) raises PolyError:
        """Add a ZZ coefficient below 2^127 in magnitude, or below 2^190 in a wide slot."""
        self.touch(slot)
        var bits = value.magnitude_bit_length()
        if bits <= 63:
            var word: Int64
            try:
                word = value.to_native_exact[DType.int64]()
            except e:
                raise PolyError(PolyErrorKind.CAPACITY, String(e))
            self._add[wide](slot, UInt128(Int128(word)), UInt64(0) - UInt64(Int(word < 0)))
            return
        var bytes = value.to_bytes()
        if len(bytes) > (24 if wide else 16):
            raise PolyError(PolyErrorKind.CAPACITY, "packed accumulator coefficient overflow")
        var low = UInt128(0)
        var high = UInt64(0)
        for i in range(len(bytes)):
            if i < 16:
                low |= UInt128(bytes[i]) << UInt128(8 * i)
            else:
                high |= UInt64(bytes[i]) << UInt64(8 * (i - 16))
        if value.sign() < 0:
            # 192-bit two's complement negation.
            low = ~low + 1
            high = ~high + UInt64(Int(low == 0))
        self._add[wide](slot, low, high)

    @always_inline
    def add_modular[track: Bool](mut self, slot: Int, a: UInt64, b: UInt64, p: UInt64):
        """Add a * b for residues a, b < p < 2^62, reducing before the sum could overflow."""
        comptime if track:
            self.touch(slot)
        var acc = self.lows.unsafe_get(slot)
        if acc >= UInt128(1) << 127:
            acc %= UInt128(p)
        self.lows.unsafe_get(slot) = acc + UInt128(a) * UInt128(b)

    def modular(self, slot: Int, p: UInt64) -> UInt64:
        return UInt64(self.lows.unsafe_get(slot) % UInt128(p))

    def signed_words(self, slot: Int) -> Tuple[UInt64, UInt64, UInt64]:
        var low = self.lows.unsafe_get(slot)
        var hi = UInt64(low >> 64)
        var top = self.highs.unsafe_get(slot) if len(self.highs) else UInt64(0) - (hi >> 63)
        return (UInt64(low), hi, top)

    @always_inline
    def empty(self, slot: Int) -> Bool:
        """Whether the slot's sum is zero (before any modular reduction)."""
        return self.lows.unsafe_get(slot) == 0 and (not len(self.highs) or self.highs.unsafe_get(slot) == 0)

    def clear(mut self, slot: Int):
        self.lows.unsafe_get(slot) = 0
        if len(self.highs):
            self.highs.unsafe_get(slot) = 0
        self.touched_flag.unsafe_get(slot) = 0

    def sorted_touched(mut self) -> List[Int]:
        var result = List[Int]()
        swap(result, self.touched)
        sort(result)
        return result^


def _is_zero(words: Tuple[UInt64, UInt64, UInt64]) -> Bool:
    return words[0] == 0 and words[1] == 0 and words[2] == 0


def _integer(words: Tuple[UInt64, UInt64, UInt64]) -> Integer:
    """The value of 192-bit two's complement words."""
    var negative = (words[2] >> 63) == 1
    var w0 = words[0]
    var w1 = words[1]
    var w2 = words[2]
    if negative:
        # Negate: invert and add one.
        w0 = ~w0
        w1 = ~w1
        w2 = ~w2
        w0 += 1
        if w0 == 0:
            w1 += 1
            if w1 == 0:
                w2 += 1
    if w1 == 0 and w2 == 0 and w0 <= UInt64(Int64.MAX):
        var v = Int64(w0)
        return Integer(-v if negative else v)
    var bytes = List[UInt8](length=24, fill=0)
    for i in range(8):
        bytes[i] = UInt8((w0 >> UInt64(8 * i)) & 0xFF)
        bytes[8 + i] = UInt8((w1 >> UInt64(8 * i)) & 0xFF)
        bytes[16 + i] = UInt8((w2 >> UInt64(8 * i)) & 0xFF)
    return Integer.from_bytes(bytes, negative=negative)


def _coefficient[C: CoefficientRing](acc: _Accumulator, slot: Int, template: C) -> C:
    comptime if C == ZZ:
        return rebind_var[C](ZZ(_integer(acc.signed_words(slot))))
    elif C == ModInt:
        ref t = rebind[ModInt](template)
        return rebind_var[C](t._with_residue(acc.modular(slot, t.modulus)))
    else:
        return template.copy()


def _slot_zero[C: CoefficientRing](acc: _Accumulator, slot: Int, template: C) -> Bool:
    comptime if C == ZZ:
        return _is_zero(acc.signed_words(slot))
    elif C == ModInt:
        return acc.modular(slot, rebind[ModInt](template).modulus) == 0
    else:
        return True


# ---------------------------------------------------------------- groups

@fieldwise_init
struct _Packed(Movable):
    """Terms as increasing keys with word coefficients, and their groups by prefix."""
    var keys: List[UInt64]
    var lows: List[Int]
    """Each key's window part."""
    var values: List[Int64]
    var group_prefix: List[UInt64]
    var group_start: List[Int]
    """Group g holds terms group_start[g] ..< group_start[g + 1]."""


def _pack[C: CoefficientRing](p: SparsePoly[C], packing: _Packing, mut budget: Budget) raises PolyError -> _Packed:
    var count = len(p.terms)
    _allocation[UInt64](_product(3, count), budget)
    var keys = List[UInt64](capacity=count)
    var lows = List[Int](capacity=count)
    var values = List[Int64](capacity=count)
    var group_prefix = List[UInt64]()
    var group_start = List[Int]()
    for i in range(count):
        budget.charge(1)
        ref term = p.terms[i]
        var key = packing.key(term.monomial)
        var prefix = key // packing.window
        if not len(group_prefix) or group_prefix[len(group_prefix) - 1] != prefix:
            group_prefix.append(prefix)
            group_start.append(i)
        keys.append(key)
        lows.append(Int(key - prefix * packing.window))
        values.append(_signed(term.coefficient))
    group_start.append(count)
    return _Packed(keys^, lows^, values^, group_prefix^, group_start^)


def _usable[C: CoefficientRing](a: SparsePoly[C], b: SparsePoly[C]) -> Bool:
    comptime if not (C == ZZ or C == ModInt):
        return False
    if not len(a.order.variables):
        return False
    if not _lex_identity(a) or not _lex_identity(b) or a.order != b.order:
        return False
    for term in a.terms:
        if not _small(term.coefficient):
            return False
    for term in b.terms:
        if not _small(term.coefficient):
            return False
    return True


def _packed_product[C: CoefficientRing](a: SparsePoly[C], b: SparsePoly[C], mut budget: Budget) raises PolyError -> Optional[SparsePoly[C]]:
    """The canonical product, or None when the operands do not fit the packed kernel.

    Both operands are nonzero, in the same ring and order.
    """
    if not _usable(a, b):
        return None
    var n = len(a.order.variables)
    var radix = _radices(_maxima(a, n), _maxima(b, n))
    if not radix:
        return None
    # A window larger than eight slots per term pair would cost more to clear than to use.
    var packing = _Packing(radix.take(), min(_WINDOW, max(1024, 8 * len(a.terms) * len(b.terms))))
    var left = _pack(a, packing, budget)
    var right = _pack(b, packing, budget)
    var groups_a = len(left.group_prefix)
    var groups_b = len(right.group_prefix)
    var pair_count = _product(groups_a, groups_b)
    # Fragmented supports would spend more on group pairs than on products.
    if pair_count > _product(len(a.terms), len(b.terms)) // 4 + 16:
        return None
    _allocation[UInt64](pair_count, budget)
    var pairs = List[UInt64](capacity=pair_count)
    var shift = 0
    while (1 << shift) < pair_count:
        shift += 1
    # Sort (output prefix, pair index) by packing both into one word when they fit.
    var prefix_bits = 0
    var prefix_range = left.group_prefix[groups_a - 1] + right.group_prefix[groups_b - 1] + 1
    while (UInt64(1) << UInt64(prefix_bits)) < prefix_range:
        prefix_bits += 1
    if prefix_bits + shift > 63:
        return None
    # Squares visit each unordered pair of terms once, doubling the off-diagonal products.
    var square = a == b
    comptime if C == ZZ:
        for term in a.terms:
            if rebind[ZZ](term.coefficient).value.magnitude_bit_length() > 62:
                square = False
                break
    for i in range(groups_a):
        for j in range(i if square else 0, groups_b):
            budget.charge(1)
            var prefix = left.group_prefix[i] + right.group_prefix[j]
            pairs.append((prefix << UInt64(shift)) | UInt64(i * groups_b + j))
    pair_count = len(pairs)
    _charge_size(pair_count, budget)
    sort(pairs)
    # Sums need 192 bits only when the coefficient bound reaches 2^127.
    var wide = False
    comptime if C == ZZ:
        var bits = _bits(a) + _bits(b) + _bit_length(min(len(a.terms), len(b.terms))) + 1
        wide = bits >= 127
    var window = Int(packing.window)
    _allocation[UInt64](_product(4, window), budget)
    var acc = _Accumulator(window, wide)
    var ring = a.ring.copy()
    var template = a.terms[0].coefficient.copy()
    var p = UInt64(0)
    comptime if C == ModInt:
        p = rebind[ModInt](template).modulus
    var result = SparsePoly[C].zero(a.order, ring, budget)
    var mask = (UInt64(1) << UInt64(shift)) - 1
    var position = 0
    while position < pair_count:
        var prefix = pairs[position] >> UInt64(shift)
        var end = position
        var work = 0
        while end < pair_count and (pairs[end] >> UInt64(shift)) == prefix:
            var index = Int(pairs[end] & mask)
            work += (left.group_start[index // groups_b + 1] - left.group_start[index // groups_b]) * (right.group_start[index % groups_b + 1] - right.group_start[index % groups_b])
            end += 1
        _charge_size(work, budget)
        # A prefix with work comparable to the window scans it instead of tracking slots.
        var dense = 4 * work >= window
        while position < end:
            var index = Int(pairs[position] & mask)
            position += 1
            var i = index // groups_b
            var j = index % groups_b
            var a0 = left.group_start[i]
            var a1 = left.group_start[i + 1]
            var b0 = right.group_start[j]
            var b1 = right.group_start[j + 1]
            var diagonal = square and i == j
            var doubled = square and i != j
            if dense:
                if wide:
                    _accumulate[C, True, False](acc, left, right, a0, a1, b0, b1, p, diagonal, doubled)
                else:
                    _accumulate[C, False, False](acc, left, right, a0, a1, b0, b1, p, diagonal, doubled)
            elif wide:
                _accumulate[C, True, True](acc, left, right, a0, a1, b0, b1, p, diagonal, doubled)
            else:
                _accumulate[C, False, True](acc, left, right, a0, a1, b0, b1, p, diagonal, doubled)
        if dense:
            _emit_window(acc, packing, prefix, template, result, budget)
        else:
            _emit(acc, packing, prefix, template, result, budget)
    return result^


def _bits[C: CoefficientRing](p: SparsePoly[C]) -> Int:
    var bits = 0
    for term in p.terms:
        bits = max(bits, rebind[ZZ](term.coefficient).value.magnitude_bit_length())
    return bits


def _bit_length(n: Int) -> Int:
    var bits = 0
    while (1 << bits) <= n:
        bits += 1
    return bits


@always_inline
def _twice[C: CoefficientRing](v: Int64, p: UInt64) -> Int64:
    comptime if C == ZZ:
        return 2 * v
    else:
        var t = 2 * UInt64(v)
        return Int64(t - p if t >= p else t)


def _accumulate[C: CoefficientRing, wide: Bool, track: Bool](mut acc: _Accumulator, left: _Packed, right: _Packed, a0: Int, a1: Int, b0: Int, b1: Int, p: UInt64, diagonal: Bool, doubled: Bool):
    """Add the products of terms a0 ..< a1 and b0 ..< b1; for a diagonal group of a square, each unordered pair once."""
    for x in range(a0, a1):
        var ka = left.lows.unsafe_get(x)
        var va = left.values.unsafe_get(x)
        var start = b0
        if diagonal:
            comptime if C == ZZ:
                acc.add_signed[wide, track](ka + ka, va, va)
            else:
                acc.add_modular[track](ka + ka, UInt64(va), UInt64(va), p)
            start = x + 1
            va = _twice[C](va, p)
        elif doubled:
            va = _twice[C](va, p)
        for y in range(start, b1):
            var slot = ka + right.lows.unsafe_get(y)
            comptime if C == ZZ:
                acc.add_signed[wide, track](slot, va, right.values.unsafe_get(y))
            else:
                acc.add_modular[track](slot, UInt64(va), UInt64(right.values.unsafe_get(y)), p)


def _emit[C: CoefficientRing](mut acc: _Accumulator, packing: _Packing, prefix: UInt64, template: C, mut result: SparsePoly[C], mut budget: Budget) raises PolyError:
    """Append the window's touched nonzero slots in increasing order and clear them."""
    var touched = acc.sorted_touched()
    _charge_size(len(touched), budget)
    _allocation[Term[C]](len(touched), budget)
    for slot in touched:
        if not _slot_zero(acc, slot, template):
            var key = prefix * packing.window + UInt64(slot)
            result.terms.append(Term[C](packing.monomial(key, budget), _coefficient(acc, slot, template)))
        acc.clear(slot)


def _emit_window[C: CoefficientRing](mut acc: _Accumulator, packing: _Packing, prefix: UInt64, template: C, mut result: SparsePoly[C], mut budget: Budget) raises PolyError:
    """Append every nonzero slot of the window in increasing order and clear them."""
    var window = Int(packing.window)
    _charge_size(window, budget)
    for slot in range(window):
        if acc.empty(slot):
            continue
        if not _slot_zero(acc, slot, template):
            _allocation[Term[C]](1, budget)
            var key = prefix * packing.window + UInt64(slot)
            result.terms.append(Term[C](packing.monomial(key, budget), _coefficient(acc, slot, template)))
        acc.clear(slot)


# --------------------------------------------------------------- division

comptime _EXACT = 0
comptime _INEXACT = 1
"""The divisor does not divide the dividend."""
comptime _OVERFLOW = 2
"""A quotient coefficient needs more than 63 bits: the general path decides."""


def _divide_word(words: Tuple[UInt64, UInt64, UInt64], divisor: Int64, mut quotient: Int64) -> Int:
    """Divide a 192-bit two's complement value by a nonzero word: _EXACT, _INEXACT, or _OVERFLOW."""
    var value = _integer(words)
    try:
        var d = Integer(divisor)
        var q = value // d
        if q * d != value:
            return _INEXACT
        if q.magnitude_bit_length() > 63:
            return _OVERFLOW
        quotient = q.to_native_exact[DType.int64]()
        return _EXACT
    except:
        return _OVERFLOW


def _packed_divide[C: CoefficientRing](f: SparsePoly[C], g: SparsePoly[C], mut budget: Budget) raises PolyError -> Optional[Optional[SparsePoly[C]]]:
    """The exact quotient f / g (inner None when g does not divide f), or None when the kernel does not apply.

    Both operands are nonzero, in the same ring and order.
    """
    comptime if not (C == ZZ or C == ModInt):
        return None
    if not len(f.order.variables):
        return None
    if not _lex_identity(f) or not _lex_identity(g) or f.order != g.order:
        return None
    for term in g.terms:
        if not _small(term.coefficient):
            return None
    for term in f.terms:
        comptime if C == ZZ:
            if rebind[ZZ](term.coefficient).value.magnitude_bit_length() > 189:
                return None
    var n = len(f.order.variables)
    var top_f = _maxima(f, n)
    var top_g = _maxima(g, n)
    for i in range(n):
        if top_g[i] > top_f[i]:
            return Optional(Optional[SparsePoly[C]](None))
    # Quotient and divisor exponents both stay within the dividend's.
    var zeros = List[UInt64](length=n, fill=0)
    var radix = _radices(top_f, zeros)
    if not radix:
        return None
    var packing = _Packing(radix.take())
    # Deepen the prefix until the divisor's leading chunk is its leading term
    # alone; with every variable in the prefix each chunk is a single term.
    var lead_key = packing.key(g.terms[len(g.terms) - 1].monomial)
    var depth = max(packing.prefix_count, 1)
    while True:
        packing.split(depth)
        var lead_prefix = lead_key // packing.window
        var count = 0
        var i = len(g.terms) - 1
        while i >= 0 and count < 2:
            budget.charge(1)
            if packing.key(g.terms[i].monomial) // packing.window != lead_prefix:
                break
            count += 1
            i -= 1
        if count == 1 or depth >= n:
            break
        depth += 1
    var divisor = _pack(g, packing, budget)
    var top = len(divisor.group_prefix) - 1
    var lead_value = divisor.values[len(divisor.values) - 1]
    var h = divisor.group_prefix[top]
    var template = g.terms[0].coefficient.copy()
    var p = UInt64(0)
    var lead_inverse = UInt64(0)
    comptime if C == ModInt:
        ref t = rebind[ModInt](template)
        p = t.modulus
        lead_inverse = rebind[ModInt](g.terms[len(g.terms) - 1].coefficient).inverse(budget).value
    # The dividend's chunks, by prefix.
    var dividend_prefix = List[UInt64]()
    var dividend_start = List[Int]()
    for i in range(len(f.terms)):
        budget.charge(1)
        var prefix = packing.key(f.terms[i].monomial) // packing.window
        if not len(dividend_prefix) or dividend_prefix[len(dividend_prefix) - 1] != prefix:
            dividend_prefix.append(prefix)
            dividend_start.append(i)
    dividend_start.append(len(f.terms))
    # Every dividend prefix visits every divisor group. When that exceeds the
    # dividend's terms, chunks collide too little to pay; a heap division wins.
    if _product(len(dividend_prefix), len(divisor.group_prefix)) > 8 * len(f.terms):
        return None
    var window = Int(packing.window)
    _allocation[UInt64](_product(4, window), budget)
    # Each remainder slot sums one dividend coefficient and at most one quotient
    # product (of at most 63 bits) per divisor term.
    var wide = True
    comptime if C == ZZ:
        var dividend_bits = 0
        for term in f.terms:
            dividend_bits = max(dividend_bits, rebind[ZZ](term.coefficient).value.magnitude_bit_length())
        wide = max(dividend_bits, 63 + _bits(g) + _bit_length(len(g.terms))) + 1 >= 127
    var acc = _Accumulator(window, wide)
    # Quotient chunks in the order computed (decreasing prefix), as packed terms.
    var q_prefix = List[UInt64]()
    var q_keys = List[List[UInt64]]()
    var q_values = List[List[Int64]]()
    var q_index = Dict[UInt64, Int]()
    # Pending prefixes, processed largest first; duplicates are skipped.
    var pending = List[UInt64]()
    for prefix in dividend_prefix:
        pending.append(prefix)
    var next_dividend = len(dividend_prefix) - 1
    var last = UInt64.MAX
    var heap = _MaxHeap(pending^)
    while heap.size():
        var t = heap.pop()
        if t == last:
            continue
        last = t
        budget.charge(1)
        # The dividend's chunk at t, if any.
        while next_dividend >= 0 and dividend_prefix[next_dividend] > t:
            next_dividend -= 1
        if next_dividend >= 0 and dividend_prefix[next_dividend] == t:
            for i in range(dividend_start[next_dividend], dividend_start[next_dividend + 1]):
                ref term = f.terms[i]
                var slot = Int(packing.key(term.monomial) % packing.window)
                comptime if C == ZZ:
                    if wide:
                        acc.add_integer[True](slot, rebind[ZZ](term.coefficient).value)
                    else:
                        acc.add_integer[False](slot, rebind[ZZ](term.coefficient).value)
                else:
                    acc.add_modular[True](slot, rebind[ModInt](term.coefficient).value, 1, p)
        # Minus the known products: quotient chunks at t - e for divisor prefixes e below h.
        for e_index in range(top):
            var e = divisor.group_prefix[e_index]
            if e > t:
                break
            var d = t - e
            var found = q_index.get(d)
            if not found:
                continue
            var qi = found.value()
            ref qk = q_keys[qi]
            ref qv = q_values[qi]
            var g0 = divisor.group_start[e_index]
            var g1 = divisor.group_start[e_index + 1]
            _charge_size(_product(len(qk), g1 - g0), budget)
            for x in range(len(qk)):
                var kq = Int(qk.unsafe_get(x) % packing.window)
                var vq = qv.unsafe_get(x)
                for y in range(g0, g1):
                    var slot = kq + divisor.lows.unsafe_get(y)
                    comptime if C == ZZ:
                        if wide:
                            acc.add_signed[True, True](slot, -vq, divisor.values.unsafe_get(y))
                        else:
                            acc.add_signed[False, True](slot, -vq, divisor.values.unsafe_get(y))
                    else:
                        acc.add_modular[True](slot, UInt64(vq), p - UInt64(divisor.values.unsafe_get(y)), p)
        # The remainder chunk must be the next quotient chunk times the lead term.
        var touched = acc.sorted_touched()
        _charge_size(len(touched), budget)
        var keys = List[UInt64]()
        var values = List[Int64]()
        var status = _EXACT
        for slot in touched:
            if status != _EXACT or _slot_zero(acc, slot, template):
                acc.clear(slot)
                continue
            var full = t * packing.window + UInt64(slot)
            if t < h:
                status = _INEXACT
            else:
                # Exponentwise divisibility, and room for the divisor's exponents.
                for i in range(n):
                    var e_full = packing.exponent(full, i)
                    var e_lead = packing.exponent(lead_key, i)
                    if e_full < e_lead or e_full - e_lead + top_g[i] > top_f[i]:
                        status = _INEXACT
                        break
                if status == _EXACT:
                    comptime if C == ZZ:
                        var value = Int64(0)
                        status = _divide_word(acc.signed_words(slot), lead_value, value)
                        if status == _EXACT:
                            keys.append(full - lead_key)
                            values.append(value)
                    else:
                        keys.append(full - lead_key)
                        values.append(Int64(_mod_mul(acc.modular(slot, p), lead_inverse, p)))
            acc.clear(slot)
        if status == _OVERFLOW:
            return None
        if status == _INEXACT:
            return Optional(Optional[SparsePoly[C]](None))
        if len(keys):
            var d = t - h
            q_index[d] = len(q_prefix)
            q_prefix.append(d)
            for e_index in range(top):
                var e = divisor.group_prefix[e_index]
                heap.push(d + e)
            q_keys.append(keys^)
            q_values.append(values^)
    # Chunks were found from the top down; emit them in increasing order.
    var result = SparsePoly[C].zero(f.order, f.ring, budget)
    var c = len(q_prefix) - 1
    while c >= 0:
        ref keys = q_keys[c]
        ref values = q_values[c]
        _allocation[Term[C]](len(keys), budget)
        for x in range(len(keys)):
            comptime if C == ZZ:
                result.terms.append(Term[C](packing.monomial(keys[x], budget), rebind_var[C](ZZ(Integer(values[x])))))
            else:
                result.terms.append(Term[C](packing.monomial(keys[x], budget), rebind_var[C](rebind[ModInt](template)._with_residue(UInt64(values[x])))))
        c -= 1
    return Optional(Optional(result^))


struct _MaxHeap(Movable):
    var items: List[UInt64]

    def __init__(out self, var items: List[UInt64]):
        self.items = items^
        var i = len(self.items) // 2 - 1
        while i >= 0:
            self._down(i)
            i -= 1

    def size(self) -> Int:
        return len(self.items)

    def push(mut self, value: UInt64):
        self.items.append(value)
        var i = len(self.items) - 1
        while i > 0:
            var parent = (i - 1) // 2
            if self.items[parent] >= self.items[i]:
                break
            var held = self.items[parent]
            self.items[parent] = self.items[i]
            self.items[i] = held
            i = parent

    def pop(mut self) -> UInt64:
        var top = self.items[0]
        var last = self.items.pop()
        if len(self.items):
            self.items[0] = last
            self._down(0)
        return top

    def _down(mut self, start: Int):
        var i = start
        var n = len(self.items)
        while True:
            var largest = i
            var l = 2 * i + 1
            var r = l + 1
            if l < n and self.items[l] > self.items[largest]:
                largest = l
            if r < n and self.items[r] > self.items[largest]:
                largest = r
            if largest == i:
                return
            var held = self.items[largest]
            self.items[largest] = self.items[i]
            self.items[i] = held
            i = largest


# ----------------------------------------------------------------- powers

def _exponent(m: Monomial, v: Int) -> Int:
    for pair in m.pairs:
        if Int(pair[0]) == v:
            return Int(pair[1])
    return 0


def _grading[C: CoefficientRing](f: SparsePoly[C], n: Int) -> Int:
    """A variable whose exponent is strictly largest at f's leading term, or -1."""
    ref lead = f.terms[len(f.terms) - 1].monomial
    for v in range(n):
        var top = _exponent(lead, v)
        var unique = top > 0
        for i in range(len(f.terms) - 1):
            if _exponent(f.terms[i].monomial, v) >= top:
                unique = False
                break
        if unique:
            return v
    return -1


def _term_estimate(t: Int, j: Int, top: List[UInt64]) -> Float64:
    """Terms of f^j for t terms, at most C(t + j - 1, j) and the exponent box (j top_i + 1)."""
    var choose = Float64(1)
    for i in range(1, t):
        choose = choose * Float64(j + i) / Float64(i)
    var box = Float64(1)
    for e in top:
        box *= Float64(j) * Float64(e) + 1
    return min(choose, box)


def _packed_power[C: CoefficientRing](f: SparsePoly[C], k: Int, mut budget: Budget) raises PolyError -> Optional[SparsePoly[C]]:
    """f^k by the power recurrence, or None when repeated squaring is expected to be faster or the kernel does not apply.

    The recurrence takes about (terms of f - 1) * (terms of f^k) heap steps and
    the last square of repeated squaring about (terms of f^(k/2))^2 / 2 products;
    both counts are estimated from the exponents alone.

    With D the derivation multiplying a monomial by its exponent of a variable v,
    g = f^k satisfies f D(g) = k D(f) g. If f's leading term f_0 has the
    strictly largest exponent of v, the coefficient of f_0 g_j in that identity
    gives g_j from the larger terms of g:
        g_j (d_j - k e_0) f_0 = - sum over i > 0, f_i g_l = f_0 g_j of f_i g_l (d_l - k e_i),
    where e_i and d_l are exponents of v. A heap merges the products f_i g as
    g grows, from the top down (Monagan and Pearce), so the work is about
    (terms of f - 1) * (terms of g) instead of the products of the last square.
    """
    comptime if not (C == ZZ):
        return None
    var t = len(f.terms)
    if t < 2 or k < 3 or not _usable(f, f):
        return None
    var n = len(f.order.variables)
    var top = _maxima(f, n)
    # Bases with a wide exponent spread (Monagan and Pearce's u^5) give sparse
    # windows that repeated squaring fills cheaply; the recurrence measured
    # faster only for exponents of at most _POWER_SPREAD.
    for e in top:
        if e > _POWER_SPREAD:
            return None
    if Float64(t - 1) * _term_estimate(t, k, top) >= Float64(_POWER_GATE) * _term_estimate(t, k // 2, top) ** 2 / 2:
        return None
    return _power_recurrence(f, k, budget)


def _power_recurrence[C: CoefficientRing](f: SparsePoly[C], k: Int, mut budget: Budget) raises PolyError -> Optional[SparsePoly[C]]:
    """f^k by the power recurrence for any k >= 2, or None when the kernel does not apply."""
    comptime if not (C == ZZ):
        return None
    var t = len(f.terms)
    if t < 2 or k < 2 or not _usable(f, f):
        return None
    var n = len(f.order.variables)
    var v = _grading(f, n)
    if v < 0:
        return None
    var top = _maxima(f, n)
    # Products f_i g_l have exponents up to (k + 1) top_i: keys carry no digit.
    var scaled = List[UInt64](capacity=n)
    var zeros = List[UInt64](length=n, fill=0)
    for i in range(n):
        scaled.append(UInt64(k + 1) * top[i])
    var radix = _radices(scaled, zeros)
    if not radix:
        return None
    var packing = _Packing(radix.take())
    # |g| <= |f|_1^k; each recurrence sum adds t - 1 products of at most
    # max|f_i| * (k + 1) top_v * |g| and must stay below 2^127.
    var norm = Float64(0)
    var largest = Float64(1)
    for term in f.terms:
        var c = abs(Float64(_signed(term.coefficient)))
        norm += c
        largest = max(largest, c)
    var bits = Float64(k) * log2(norm) + log2(Float64(t) * largest * Float64(k + 1) * (Float64(top[v]) + 1)) + 2
    if bits > 124:
        return None
    var key_bits = _bit_length(Int(packing.weight[0] * packing.radix[0]))
    var stream_bits = _bit_length(t - 1)
    if key_bits + stream_bits > 63:
        return None
    # f's terms from the leading one down.
    var fk = List[UInt64](capacity=t)
    var fc = List[Int128](capacity=t)
    var fd = List[Int](capacity=t)
    var fe = List[Int](capacity=t * n)
    for x in range(t):
        ref term = f.terms[t - 1 - x]
        budget.charge(1)
        fk.append(packing.key(term.monomial))
        fc.append(Int128(_signed(term.coefficient)))
        fd.append(_exponent(term.monomial, v))
        for i in range(n):
            fe.append(_exponent(term.monomial, i))
    _allocation[UInt64](_product(n + 3, t + 1), budget)
    var expected = Int(min(_term_estimate(t, k, top), Float64(1 << 20)))
    var gk = List[UInt64](capacity=expected)
    var gc = List[Int128](capacity=expected)
    var gd = List[Int](capacity=expected)
    var ge = List[Int](capacity=expected * n)
    var lead = Int128(1)
    for _ in range(k):
        lead *= fc[0]
    gk.append(UInt64(k) * fk[0])
    gc.append(lead)
    gd.append(k * fd[0])
    for i in range(n):
        ge.append(k * fe[i])
    var shift = UInt64(stream_bits)
    var mask = (UInt64(1) << shift) - 1
    var entries = List[UInt64](capacity=t - 1)
    for x in range(1, t):
        entries.append(((fk[x] + gk[0]) << shift) | UInt64(x))
    var heap = _StreamHeap(entries^)
    var position = List[Int](length=t, fill=0)
    var stalled = List[Int](capacity=t)
    var exponents = List[Int](length=n, fill=0)
    while heap.size:
        var key = heap.top() >> shift
        var sum = Int128(0)
        var x = 0
        var l = 0
        while heap.size and (heap.top() >> shift) == key:
            budget.charge(1)
            x = Int(heap.top() & mask)
            l = position[x]
            sum += fc[x] * Int128(gd[l] - k * fd[x]) * gc[l]
            position[x] = l + 1
            if l + 1 < len(gk):
                heap.replace_top(((fk[x] + gk[l + 1]) << shift) | UInt64(x))
            else:
                heap.pop()
                stalled.append(x)
        if sum == 0:
            continue
        # The new term is (f_x g_l) / f_0, which the identity makes exact.
        for i in range(n):
            exponents[i] = fe[x * n + i] + ge[l * n + i] - fe[i]
            if exponents[i] < 0:
                return None
        var d = fd[x] + gd[l] - fd[0]
        var denominator = fc[0] * Int128(d - k * fd[0])
        var quotient: Int128
        # Most sums fit a word, where division is a machine instruction.
        if Int128(Int64.MIN) < sum and sum <= Int128(Int64.MAX) and Int128(Int64.MIN) < denominator and denominator <= Int128(Int64.MAX):
            var word = Int64(sum)
            var by = Int64(denominator)
            if word % by != 0:
                return None
            quotient = Int128(word // by)
        else:
            quotient = sum // denominator
            if quotient * denominator != sum:
                return None
        _allocation[UInt64](n + 3, budget)
        gk.append(key - fk[0])
        gc.append(-quotient)
        gd.append(d)
        for i in range(n):
            ge.append(exponents[i])
        for s in stalled:
            heap.push(((fk[s] + gk[position[s]]) << shift) | UInt64(s))
        stalled.clear()
    var result = SparsePoly[C].zero(f.order, f.ring, budget)
    var count = len(gk)
    _allocation[Term[C]](count, budget)
    result.terms.reserve(count)
    var j = count - 1
    while j >= 0:
        budget.charge(1)
        var used = 0
        for i in range(n):
            used += Int(ge[j * n + i] != 0)
        _allocation[Tuple[Int64, UInt32]](used, budget)
        var monomial = Monomial()
        monomial.pairs.reserve(used)
        for i in range(n):
            if ge[j * n + i]:
                monomial.pairs.append((Int64(i), UInt32(ge[j * n + i])))
        var c = gc[j]
        var words = UInt128(c)
        result.terms.append(Term[C](monomial^, rebind_var[C](ZZ(_integer((UInt64(words), UInt64(words >> 64), UInt64(0) - UInt64(Int(c < 0))))))))
        j -= 1
    return result^


struct _StreamHeap(Movable):
    """A max-heap of at most its initial number of words, without reallocation."""
    var items: List[UInt64]
    var size: Int

    def __init__(out self, var items: List[UInt64]):
        self.size = len(items)
        self.items = items^
        var i = self.size // 2 - 1
        while i >= 0:
            self._down(i, self.items.unsafe_get(i))
            i -= 1

    @always_inline
    def top(self) -> UInt64:
        return self.items.unsafe_get(0)

    @always_inline
    def replace_top(mut self, value: UInt64):
        self._down(0, value)

    @always_inline
    def pop(mut self):
        self.size -= 1
        if self.size:
            self._down(0, self.items.unsafe_get(self.size))

    def push(mut self, value: UInt64):
        var i = self.size
        self.size += 1
        while i > 0:
            var parent = (i - 1) // 2
            var above = self.items.unsafe_get(parent)
            if above >= value:
                break
            self.items.unsafe_get(i) = above
            i = parent
        self.items.unsafe_get(i) = value

    @always_inline
    def _down(mut self, start: Int, value: UInt64):
        """Place value at start and sift it down."""
        var i = start
        while True:
            var child = 2 * i + 1
            if child >= self.size:
                break
            var c = self.items.unsafe_get(child)
            if child + 1 < self.size:
                var other = self.items.unsafe_get(child + 1)
                if other > c:
                    child += 1
                    c = other
            if c <= value:
                break
            self.items.unsafe_get(i) = c
            i = child
        self.items.unsafe_get(i) = value
