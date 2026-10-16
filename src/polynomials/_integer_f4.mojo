"""Exact reduction by F4 matrices over the integers: zero-reduction checks and tails.

Certifying a reconstructed basis G (see `_rational_groebner`) needs every
S-pair the Gebauer–Möller criteria keep to reduce to zero modulo G, exactly.
The pairs of one LCM degree share a matrix, built as F4 builds one: both
halves of every S-polynomial and, from symbolic preprocessing, a reducer m*g
for every monomial some leading monomial divides. Every row is a multiple of
an element of G, so every row leading in a column can reduce it.

Each S-polynomial is reduced alone in a dense row, fraction-free over the
integers: a reducer with leading coefficient d meets an entry v by scaling
the row by d / gcd(d, v) and subtracting v / gcd(d, v) times the reducer. The
scale is almost always one. Any S-polynomial that a nonzero multiple of
reduces to zero reduces to zero itself, and a nonzero entry in a column that
no leading monomial divides is a nonzero remainder, since later reducers
touch only later columns. Reducing to zero by some choice of reducers gives a
standard representation, which is all Buchberger's criterion needs.

The same rows reduce the tails of a Gröbner basis by one another, for the
reduced basis of the dehomogenized ideal: there an entry in a column no
leading monomial divides is part of the result.

Row entries are fixed-width two's complement integers in 64-bit limbs,
widened when a bound on their size requires it, so a reduction step is an
in-place multiply-subtract with no allocation.
"""
from std.bit import count_leading_zeros
from std.math import max, min
from apn_mojo import Integer, div_rem_trunc, gcd as integer_gcd
from .coefficients import ZZ
from .errors import Budget, PolyError, PolyErrorKind, _allocation, _product
from ._f4 import _Matrix, _Store
from ._packed_groebner import _Engine, _Packed, _Term, _div

comptime _SLACK = 16
"""Bits of growth a widened row leaves room for before it is measured again."""


def _magnitude(value: Integer, mut limbs: List[UInt64]):
    """Append the magnitude of value in 64-bit limbs, least significant first."""
    var bytes = value.to_bytes()
    var n = (len(bytes) + 7) // 8
    for l in range(n):
        var limb = UInt64(0)
        for b in range(8):
            var i = 8 * l + b
            if i < len(bytes):
                limb |= UInt64(bytes[i]) << UInt64(8 * b)
        limbs.append(limb)


def _bits(limbs: List[UInt64]) -> Int:
    var n = len(limbs)
    while n > 0 and limbs[n - 1] == 0:
        n -= 1
    if n == 0:
        return 0
    var top = limbs[n - 1]
    var bits = 64 * (n - 1)
    while top:
        bits += 1
        top >>= 1
    return bits


struct _Coefficients(Movable):
    """Each element's coefficients as magnitude limbs and signs, leading term first."""
    var limbs: List[List[UInt64]]
    var starts: List[List[Int]]
    """Where each coefficient's limbs start, then where the last one's end."""
    var negative: List[List[Bool]]
    var bits: List[Int]
    """The bit length of each element's largest coefficient."""
    var leads: List[Integer]
    var words: List[UInt64]
    """Each leading coefficient when it fits in 63 bits, otherwise zero."""

    def __init__[W: Int](out self, engine: _Engine[ZZ, W, True], mut budget: Budget) raises PolyError:
        self.limbs = List[List[UInt64]]()
        self.starts = List[List[Int]]()
        self.negative = List[List[Bool]]()
        self.bits = List[Int]()
        self.leads = List[Integer]()
        self.words = List[UInt64]()
        for p in engine.polys:
            var limbs = List[UInt64]()
            var starts = List[Int]()
            var negative = List[Bool]()
            var bits = 0
            for k in range(len(p) - 1, -1, -1):
                ref value = p[k].coefficient.value
                budget.charge(UInt64(value.magnitude_bit_length() // 64 + 1))
                starts.append(len(limbs))
                _magnitude(value, limbs)
                negative.append(value.sign() < 0)
                bits = max(bits, value.magnitude_bit_length())
            starts.append(len(limbs))
            _allocation[UInt64](len(limbs), budget)
            self.limbs.append(limbs^)
            self.starts.append(starts^)
            self.negative.append(negative^)
            self.bits.append(bits)
            ref lead = p[len(p) - 1].coefficient.value
            self.words.append(_limbs_of(lead)[0] if lead.magnitude_bit_length() <= 63 else UInt64(0))
            self.leads.append(lead.copy())


struct _Row(Movable):
    """A dense row of fixed-width two's complement integers in 64-bit limbs.

    `sizes` bounds the bit length of each entry's magnitude, and is zero for
    a zero entry; `bound` bounds them all. An entry holds 64 * width - 1 bits
    besides its sign, so no update overflows while the bound fits. A sum can
    be a bit longer than its terms, so the bounds drift upward; when the
    bound outgrows the width, the entries are measured before the row is
    widened.
    """
    var width: Int
    var bound: Int
    var ncols: Int
    var data: List[UInt64]
    var sizes: List[Int]
    var scratch: List[UInt64]

    def __init__(out self, ncols: Int):
        self.ncols = ncols
        self.bound = 0
        self.width = 0
        self.data = List[UInt64]()
        self.sizes = List[Int]()
        self.scratch = List[UInt64]()

    def prepare(mut self, bits: Int, mut budget: Budget) raises PolyError:
        """Expect entries of about `bits` bits; every entry must be zero."""
        var width = bits // 64 + 1
        if width > self.width or 2 * width < self.width:
            _allocation[UInt64](_product(self.ncols, width), budget)
            self.width = width
            self.data = List[UInt64](length=self.ncols * width, fill=0)
            self.scratch = List[UInt64](length=2 * width + 2, fill=0)
        budget.charge(UInt64(self.ncols))
        if len(self.sizes) != self.ncols:
            self.sizes = List[Int](length=self.ncols, fill=0)
        else:
            for c in range(self.ncols):
                self.sizes.unsafe_get(c) = 0
        self.bound = 0

    def room_for_sum(mut self, bits: Int, mut budget: Budget) raises PolyError:
        """Make room for adding terms of `bits` bits, one to each entry at most."""
        if max(self.bound, bits) + 1 < 64 * self.width:
            return
        self._tighten(budget)
        var needed = max(self.bound, bits) + 1
        # Widen with some slack, so that measuring stays rare.
        if needed + _SLACK >= 64 * self.width:
            self._widen(needed + _SLACK, budget)

    def room_for_scale(mut self, bits: Int, mut budget: Budget) raises PolyError:
        """Make room for multiplying every entry by a factor of `bits` bits."""
        if self.bound + bits < 64 * self.width:
            return
        self._tighten(budget)
        var needed = self.bound + bits
        if needed + _SLACK >= 64 * self.width:
            self._widen(needed + _SLACK, budget)

    def _tighten(mut self, mut budget: Budget) raises PolyError:
        """Replace the size bounds by the entries' sizes."""
        budget.charge(UInt64(len(self.data)))
        var bound = 0
        for c in range(self.ncols):
            if self.sizes.unsafe_get(c) > 0:
                self.sizes.unsafe_get(c) = self._entry_bits(c)
                bound = max(bound, self.sizes.unsafe_get(c))
        self.bound = bound

    def _entry_bits(self, c: Int) -> Int:
        var base = c * self.width
        var negative = (self.data.unsafe_get(base + self.width - 1) >> 63) != 0
        for l in range(self.width - 1, -1, -1):
            var limb = self.data.unsafe_get(base + l)
            if negative:
                limb = ~limb
            if limb != 0:
                # ~x is |x| - 1 for negative x, at most one bit shorter.
                return 64 * l + 64 - Int(count_leading_zeros(limb)) + (1 if negative else 0)
        return 1 if negative else 0

    def _widen(mut self, bound: Int, mut budget: Budget) raises PolyError:
        """Make room for entries of `bound` bits, sign-extending every entry."""
        var width = max(bound // 64 + 1, self.width + self.width // 2)
        _allocation[UInt64](_product(self.ncols, width), budget)
        budget.charge(UInt64(self.ncols * width))
        var data = List[UInt64](length=self.ncols * width, fill=0)
        for c in range(self.ncols):
            var old = c * self.width
            var fill = UInt64.MAX if (self.data.unsafe_get(old + self.width - 1) >> 63) != 0 else UInt64(0)
            for l in range(width):
                data.unsafe_get(c * width + l) = self.data.unsafe_get(old + l) if l < self.width else fill
        self.data = data^
        self.width = width
        self.scratch = List[UInt64](length=2 * width + 2, fill=0)

    def is_zero(self, c: Int) -> Bool:
        if self.sizes.unsafe_get(c) == 0:
            return True
        var base = c * self.width
        for l in range(self.width):
            if self.data.unsafe_get(base + l) != 0:
                return False
        return True

    def value(self, c: Int) -> Integer:
        """Entry c as an Integer."""
        var base = c * self.width
        var negative = (self.data.unsafe_get(base + self.width - 1) >> 63) != 0
        var used = (self._entry_bits(c) + 63) // 64
        var bytes = List[UInt8](capacity=8 * used)
        var carry = UInt64(1)
        for l in range(used):
            var limb = self.data.unsafe_get(base + l)
            if negative:
                # The magnitude of a two's complement value: invert and add one.
                limb = ~limb + carry
                carry = UInt64(1) if (carry != 0 and limb == 0) else UInt64(0)
            for b in range(8):
                bytes.append(UInt8((limb >> UInt64(8 * b)) & 0xFF))
        return Integer.from_bytes(bytes, negative=negative)

    def magnitude(self, c: Int) -> List[UInt64]:
        """The magnitude of entry c in limbs, without leading zeros."""
        var base = c * self.width
        var negative = self.negative(c)
        var used = (self._entry_bits(c) + 63) // 64
        var limbs = List[UInt64](capacity=used)
        var carry = UInt64(1)
        for l in range(used):
            var limb = self.data.unsafe_get(base + l)
            if negative:
                limb = ~limb + carry
                carry = UInt64(1) if (carry != 0 and limb == 0) else UInt64(0)
            limbs.append(limb)
        while len(limbs) and limbs[len(limbs) - 1] == 0:
            _ = limbs.pop()
        return limbs^

    def negative(self, c: Int) -> Bool:
        return (self.data.unsafe_get(c * self.width + self.width - 1) >> 63) != 0

    def set_zero(mut self, c: Int):
        self.sizes.unsafe_get(c) = 0
        var base = c * self.width
        for l in range(self.width):
            self.data.unsafe_get(base + l) = 0

    def _negate(mut self, c: Int):
        var base = c * self.width
        var carry = UInt64(1)
        for l in range(self.width):
            var sum = ~self.data.unsafe_get(base + l) + carry
            carry = UInt64(1) if (carry != 0 and sum == 0) else UInt64(0)
            self.data.unsafe_get(base + l) = sum

    @always_inline
    def _grow(mut self, c: Int, bits: Int):
        var size = max(self.sizes.unsafe_get(c), bits) + 1
        self.sizes.unsafe_get(c) = size
        self.bound = max(self.bound, size)

    def _product(mut self, factor: List[UInt64], terms: List[UInt64], start: Int, end: Int) -> Int:
        """Put factor times the magnitude terms[start:end] in the scratch limbs; return their count."""
        var n = end - start
        var out = self.scratch.unsafe_ptr()
        var b = terms.unsafe_ptr().unsafe_offset(start)
        _multiply(out, factor.unsafe_ptr(), len(factor), b, n)
        return min(len(factor) + n, self.width)

    def add_product(mut self, c: Int, factor: List[UInt64], terms: List[UInt64], start: Int, end: Int, bits: Int):
        """Add factor times the magnitude terms[start:end], of at most `bits` bits, to entry c."""
        self._grow(c, bits)
        var data = self.data.unsafe_ptr().unsafe_offset(c * self.width)
        if len(factor) == 1:
            _add_mul_1(data, self.width, factor.unsafe_get(0), terms.unsafe_ptr().unsafe_offset(start), end - start)
            return
        if end - start == 1:
            _add_mul_1(data, self.width, terms.unsafe_get(start), factor.unsafe_ptr(), len(factor))
            return
        var used = self._product(factor, terms, start, end)
        var product = self.scratch.unsafe_ptr()
        var carry = UInt64(0)
        for l in range(used):
            var e = data.unsafe_offset(l).unsafe_load()
            var p = product.unsafe_offset(l).unsafe_load()
            var sum = e + p
            var next = UInt64(1) if sum < e else UInt64(0)
            var total = sum + carry
            next += UInt64(1) if total < sum else UInt64(0)
            data.unsafe_offset(l).unsafe_store(total)
            carry = next
        # Two's complement: the carry runs on through the sign limbs.
        var l = used
        while carry != 0 and l < self.width:
            var total = data.unsafe_offset(l).unsafe_load() + carry
            carry = UInt64(1) if total == 0 else UInt64(0)
            data.unsafe_offset(l).unsafe_store(total)
            l += 1

    def subtract_product(mut self, c: Int, factor: List[UInt64], terms: List[UInt64], start: Int, end: Int, bits: Int):
        """Subtract factor times the magnitude terms[start:end], of at most `bits` bits, from entry c."""
        self._grow(c, bits)
        var data = self.data.unsafe_ptr().unsafe_offset(c * self.width)
        if len(factor) == 1:
            _sub_mul_1(data, self.width, factor.unsafe_get(0), terms.unsafe_ptr().unsafe_offset(start), end - start)
            return
        if end - start == 1:
            _sub_mul_1(data, self.width, terms.unsafe_get(start), factor.unsafe_ptr(), len(factor))
            return
        var used = self._product(factor, terms, start, end)
        var product = self.scratch.unsafe_ptr()
        var borrow = UInt64(0)
        for l in range(used):
            var e = data.unsafe_offset(l).unsafe_load()
            var p = product.unsafe_offset(l).unsafe_load()
            var difference = e - p
            var next = UInt64(1) if e < p else UInt64(0)
            var total = difference - borrow
            next += UInt64(1) if difference < borrow else UInt64(0)
            data.unsafe_offset(l).unsafe_store(total)
            borrow = next
        var l = used
        while borrow != 0 and l < self.width:
            var e = data.unsafe_offset(l).unsafe_load()
            data.unsafe_offset(l).unsafe_store(e - borrow)
            borrow = UInt64(1) if e == 0 else UInt64(0)
            l += 1

    def scale(mut self, first: Int, factor: List[UInt64], bits: Int):
        """Multiply every entry from column `first` on by the positive factor of `bits` bits; the bound must allow it."""
        self.bound += bits
        # Two's complement products modulo 2^(64 width) are exact while they fit.
        for c in range(first, self.ncols):
            if self.is_zero(c):
                continue
            self.sizes.unsafe_get(c) += bits
            var entry = self.data.unsafe_ptr().unsafe_offset(c * self.width)
            if len(factor) == 1:
                var f = UInt128(factor.unsafe_get(0))
                var carry = UInt128(0)
                for l in range(self.width):
                    var t = f * UInt128(entry.unsafe_offset(l).unsafe_load()) + carry
                    entry.unsafe_offset(l).unsafe_store(UInt64(t & UInt128(UInt64.MAX)))
                    carry = t >> 64
                continue
            _multiply(self.scratch.unsafe_ptr(), factor.unsafe_ptr(), len(factor), entry, self.width)
            for l in range(self.width):
                entry.unsafe_offset(l).unsafe_store(self.scratch.unsafe_get(l))


@always_inline
def _add_mul_1(data: Pointer[mut=True, UInt64, _], width: Int, f: UInt64, other: Pointer[mut=False, UInt64, _], n: Int):
    """data += f * other[0:n] over `width` limbs of two's complement, in one carry chain."""
    var g = UInt128(f)
    var carry = UInt128(0)
    var l = 0
    while l < n and l < width:
        var t = g * UInt128(other.unsafe_offset(l).unsafe_load()) + UInt128(data.unsafe_offset(l).unsafe_load()) + carry
        data.unsafe_offset(l).unsafe_store(UInt64(t & UInt128(UInt64.MAX)))
        carry = t >> 64
        l += 1
    while carry != 0 and l < width:
        var x = UInt128(data.unsafe_offset(l).unsafe_load()) + carry
        data.unsafe_offset(l).unsafe_store(UInt64(x & UInt128(UInt64.MAX)))
        carry = x >> 64
        l += 1


@always_inline
def _sub_mul_1(data: Pointer[mut=True, UInt64, _], width: Int, f: UInt64, other: Pointer[mut=False, UInt64, _], n: Int):
    """data -= f * other[0:n] over `width` limbs of two's complement, in one borrow chain."""
    var g = UInt128(f)
    var rest = UInt128(0)
    var l = 0
    while l < n and l < width:
        var t = g * UInt128(other.unsafe_offset(l).unsafe_load()) + rest
        var low = UInt64(t & UInt128(UInt64.MAX))
        rest = t >> 64
        var e = data.unsafe_offset(l).unsafe_load()
        data.unsafe_offset(l).unsafe_store(e - low)
        if e < low:
            rest += 1
        l += 1
    while rest != 0 and l < width:
        var e = UInt128(data.unsafe_offset(l).unsafe_load())
        var low = rest & UInt128(UInt64.MAX)
        data.unsafe_offset(l).unsafe_store(UInt64((e - low) & UInt128(UInt64.MAX)))
        rest = (rest >> 64) + (UInt128(1) if e < low else UInt128(0))
        l += 1


def _multiply(result: Pointer[mut=True, UInt64, _], a: Pointer[mut=False, UInt64, _], na: Int, b: Pointer[mut=False, UInt64, _], nb: Int):
    """result[0 : na + nb] = a[0:na] * b[0:nb], magnitudes in 64-bit limbs.

    With a short factor, either one, the product goes row by row, one row
    per limb of the short factor. Otherwise each output limb sums its column
    of products first, in a 192-bit accumulator: the products of a column are
    independent, so they do not wait on one another's carries.
    """
    if nb <= 2 and na > nb:
        _multiply(result, b, nb, a, na)
        return
    if na <= 2:
        for l in range(na + nb):
            result.unsafe_offset(l).unsafe_store(0)
        for k in range(na):
            var f = UInt128(a.unsafe_offset(k).unsafe_load())
            var carry = UInt128(0)
            var row = result.unsafe_offset(k)
            for i in range(nb):
                var t = f * UInt128(b.unsafe_offset(i).unsafe_load()) + UInt128(row.unsafe_offset(i).unsafe_load()) + carry
                row.unsafe_offset(i).unsafe_store(UInt64(t & UInt128(UInt64.MAX)))
                carry = t >> 64
            row.unsafe_offset(nb).unsafe_store(UInt64(carry))
        return
    var low = UInt128(0)
    var high = UInt64(0)
    for j in range(na + nb - 1):
        var first = max(0, j - nb + 1)
        var last = min(j, na - 1)
        for k in range(first, last + 1):
            var product = UInt128(a.unsafe_offset(k).unsafe_load()) * UInt128(b.unsafe_offset(j - k).unsafe_load())
            low += product
            high += UInt64(1) if low < product else UInt64(0)
        result.unsafe_offset(j).unsafe_store(UInt64(low & UInt128(UInt64.MAX)))
        low = (low >> 64) | (UInt128(high) << 64)
        high = 0
    result.unsafe_offset(na + nb - 1).unsafe_store(UInt64(low & UInt128(UInt64.MAX)))


def _remainder(limbs: List[UInt64], d: UInt64) -> UInt64:
    var r = UInt128(0)
    for l in range(len(limbs) - 1, -1, -1):
        r = ((r << 64) | UInt128(limbs[l])) % UInt128(d)
    return UInt64(r)


def _divide(mut limbs: List[UInt64], d: UInt64):
    """Divide the magnitude limbs by d in place, dropping leading zeros; d must divide them."""
    var r = UInt128(0)
    for l in range(len(limbs) - 1, -1, -1):
        var x = (r << 64) | UInt128(limbs[l])
        limbs[l] = UInt64(x // UInt128(d))
        r = x % UInt128(d)
    while len(limbs) and limbs[len(limbs) - 1] == 0:
        _ = limbs.pop()


def _word_gcd(var a: UInt64, var b: UInt64) -> UInt64:
    while b:
        var t = a % b
        a = b
        b = t
    return a


def _limbs_of(value: Integer) -> List[UInt64]:
    var limbs = List[UInt64]()
    _magnitude(value, limbs)
    return limbs^


def _pairs_reduce_to_zero[W: Int](mut engine: _Engine[ZZ, W, True], mut budget: Budget) raises PolyError -> Bool:
    """Whether the S-polynomial of every pending pair reduces to zero against the active elements, exactly.

    The active elements must have mutually nondividing leading monomials.
    """
    engine.sort_active(budget)
    var store = _Store[W]()
    store.extend(engine, budget)
    var coefficients = _Coefficients(engine, budget)
    while len(engine.pairs):
        var degree = engine.pairs[0].lcm.degree
        var matrix = _Matrix[W]()
        var halves = List[Int]()
        while len(engine.pairs) and engine.pairs[0].lcm.degree == degree:
            var pair = engine.select(budget)
            halves.append(len(matrix.sources))
            matrix.add_row(engine, store, pair.first, _div(pair.lcm, engine.leads[pair.first]), budget)
            matrix.add_row(engine, store, pair.second, _div(pair.lcm, engine.leads[pair.second]), budget)
        matrix.preprocess(engine, store, budget)
        var order = matrix.number(engine.kind, budget)
        var ncols = len(order)
        var nrows = len(matrix.sources)
        _allocation[Int](ncols, budget)
        var pivot = List[Int](length=ncols, fill=-1)
        for r in range(nrows - 1, -1, -1):
            pivot[Int(matrix.entries[matrix.starts[r]])] = r
        var row = _Row(ncols)
        for a in halves:
            if not _reduces(row, matrix, pivot, coefficients, a, budget):
                return False
    return True


def _reduces[W: Int](mut row: _Row, matrix: _Matrix[W], pivot: List[Int], coefficients: _Coefficients, a: Int, mut budget: Budget) raises PolyError -> Bool:
    """Whether the S-polynomial of matrix rows a and a + 1, which lead in one column, reduces to zero."""
    var b = a + 1
    var ga = matrix.sources[a]
    var gb = matrix.sources[b]
    var lead_a: Integer
    var lead_b: Integer
    try:
        var common = integer_gcd(coefficients.leads[ga], coefficients.leads[gb])
        lead_a = div_rem_trunc(coefficients.leads[gb], common)[0].copy()
        lead_b = div_rem_trunc(coefficients.leads[ga], common)[0].copy()
    except e:
        raise PolyError(PolyErrorKind.CAPACITY, String(e))
    # S = lead_a * row a - lead_b * row b, where lead_a * d_a = lead_b * d_b.
    var fa = _limbs_of(lead_a)
    var fb = _limbs_of(lead_b)
    var negative_a = lead_a.sign() < 0
    var negative_b = lead_b.sign() < 0
    # A row that reduced to zero is all zero again.
    row.prepare(max(coefficients.bits[ga] + _bits(fa), coefficients.bits[gb] + _bits(fb)) + 1, budget)
    _load(row, matrix, coefficients, a, fa, negative_a, False, budget)
    _load(row, matrix, coefficients, b, fb, negative_b, True, budget)
    var first = Int(matrix.entries[matrix.starts[a]])
    row.set_zero(first)
    for c in range(first + 1, row.ncols):
        budget.charge(UInt64(row.width))
        if row.is_zero(c):
            continue
        var q = pivot[c]
        if q < 0:
            return False
        _cancel(row, matrix, coefficients, c, q, c, budget)
    return True


def _cancel[W: Int](mut row: _Row, matrix: _Matrix[W], coefficients: _Coefficients, c: Int, q: Int, first: Int, mut budget: Budget) raises PolyError:
    """Make entry c zero with matrix row q, which leads in column c.

    The row is scaled first, from column `first` on, when the leading
    coefficient d of row q does not divide the entry v: by d / gcd(d, v),
    which is positive since leading coefficients are.
    """
    var g = matrix.sources[q]
    var d = coefficients.words[g]
    if d != 0:
        # A word-sized leading coefficient: divide in limbs.
        var negative = row.negative(c)
        var f = row.magnitude(c)
        budget.charge(UInt64(2 * len(f)))
        var r = _remainder(f, d)
        if r == 0:
            _divide(f, d)
        else:
            var common = _word_gcd(d, r)
            var s: List[UInt64] = [d // common]
            _divide(f, common)
            row.room_for_scale(_bits(s), budget)
            budget.charge(UInt64(_product(row.ncols - first, row.width)))
            row.scale(first, s, _bits(s))
        _load(row, matrix, coefficients, q, f, negative, True, budget)
        row.set_zero(c)
        return
    var v = row.value(c)
    var factor: Integer
    try:
        var qr = div_rem_trunc(v, coefficients.leads[g])
        if qr[1].sign() == 0:
            factor = qr[0].copy()
        else:
            var common = integer_gcd(coefficients.leads[g], v)
            var s = _limbs_of(div_rem_trunc(coefficients.leads[g], common)[0])
            factor = div_rem_trunc(v, common)[0].copy()
            row.room_for_scale(_bits(s), budget)
            budget.charge(UInt64(_product(row.ncols - first, row.width * len(s))))
            row.scale(first, s, _bits(s))
    except e:
        raise PolyError(PolyErrorKind.CAPACITY, String(e))
    # The entry is v * scale = factor * d, cancelled by factor times the reducer.
    _load(row, matrix, coefficients, q, _limbs_of(factor), factor.sign() < 0, True, budget)
    row.set_zero(c)


def _reduced_tails[W: Int](mut engine: _Engine[ZZ, W, True], mut budget: Budget) raises PolyError -> List[List[_Term[ZZ, W]]]:
    """The active elements with their tails reduced by one another, in decreasing leading-monomial order.

    The active elements must form a Gröbner basis with positive leading
    coefficients and mutually nondividing leading monomials, so the reduced
    tails are their normal forms. Each element is one row, a multiple of
    itself; entries in columns no leading monomial divides stay.
    """
    engine.sort_active(budget)
    var store = _Store[W]()
    store.extend(engine, budget)
    var coefficients = _Coefficients(engine, budget)
    var matrix = _Matrix[W]()
    var one = _Packed[W](SIMD[DType.uint32, W](0), 0, 0)
    for position in range(len(engine.active) - 1, -1, -1):
        matrix.add_row(engine, store, engine.active[position], one, budget)
    var basis_rows = len(matrix.sources)
    matrix.preprocess(engine, store, budget)
    var order = matrix.number(engine.kind, budget)
    var ncols = len(order)
    var nrows = len(matrix.sources)
    _allocation[Int](ncols, budget)
    var pivot = List[Int](length=ncols, fill=-1)
    for r in range(nrows - 1, -1, -1):
        pivot[Int(matrix.entries[matrix.starts[r]])] = r
    var row = _Row(ncols)
    var unit: List[UInt64] = [1]
    var result = List[List[_Term[ZZ, W]]](capacity=basis_rows)
    for r in range(basis_rows):
        row.prepare(coefficients.bits[matrix.sources[r]] + 1, budget)
        _load(row, matrix, coefficients, r, unit, False, False, budget)
        var first = Int(matrix.entries[matrix.starts[r]])
        for c in range(first + 1, ncols):
            budget.charge(UInt64(row.width))
            if row.is_zero(c) or pivot[c] < 0:
                continue
            _cancel(row, matrix, coefficients, c, pivot[c], first, budget)
        # The remaining entries, as an increasing term list; the row is zero again after.
        var terms = List[_Term[ZZ, W]]()
        for c in range(ncols - 1, first - 1, -1):
            if row.is_zero(c):
                continue
            _allocation[_Term[ZZ, W]](1, budget)
            terms.append(_Term[ZZ, W](matrix.columns.monomials[order[c]], ZZ(row.value(c))))
            row.set_zero(c)
        result.append(terms^)
    return result^


def _load[W: Int](mut row: _Row, matrix: _Matrix[W], coefficients: _Coefficients, r: Int, factor: List[UInt64], negative: Bool, subtract: Bool, mut budget: Budget) raises PolyError:
    """Add, or subtract, factor (negative if `negative`) times matrix row r to the dense row."""
    var g = matrix.sources[r]
    var bits = coefficients.bits[g] + _bits(factor)
    row.room_for_sum(bits, budget)
    ref limbs = coefficients.limbs[g]
    ref starts = coefficients.starts[g]
    ref signs = coefficients.negative[g]
    var s = matrix.starts[r]
    var n = matrix.starts[r + 1] - s
    budget.charge(UInt64(_product(n, len(factor) * (coefficients.bits[g] // 64 + 1) + row.width)))
    for k in range(n):
        var c = Int(matrix.entries.unsafe_get(s + k))
        # The term's sign, times the factor's, decides between adding and subtracting.
        if subtract != (negative != signs.unsafe_get(k)):
            row.subtract_product(c, factor, limbs, starts.unsafe_get(k), starts.unsafe_get(k + 1), bits)
        else:
            row.add_product(c, factor, limbs, starts.unsafe_get(k), starts.unsafe_get(k + 1), bits)
