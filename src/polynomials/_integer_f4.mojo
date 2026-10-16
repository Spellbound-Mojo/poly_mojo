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
in-place multiply-subtract with no allocation. The entry divides by the
reducer's leading coefficient from the low end (Hensel division), which also
tells whether the division is exact. Products of long factors go through
52-bit digits and AVX-512 IFMA where the target has it.
"""
from std.bit import count_leading_zeros, count_trailing_zeros
from std.math import max, min
from std.sys import CompilationTarget, llvm_intrinsic
from std.time import perf_counter_ns
from apn_mojo import Integer, div_rem_trunc, gcd as integer_gcd
from .coefficients import Modulus, ZZ, _prime
from .errors import Budget, PolyError, PolyErrorKind, _allocation, _product
from ._f4 import _LANES, _Lanes, _Matrix, _Primes, _Store, _mod_lanes
from ._packed_groebner import _Engine, _Packed, _Term, _div

comptime _SLACK = 16
"""Bits of growth a widened row leaves room for before it is measured again."""

comptime _COMBA = 24
"""Products whose factors are both at least this many limbs long go into an entry a column at a time."""

comptime _IFMA = CompilationTarget._has_feature["avx512ifma"]()
"""Whether the target multiplies 52-bit digits eight at a time (AVX-512 IFMA)."""

comptime _IFMA_MIN = 12
"""With IFMA, products whose factors are both at least this many limbs long go through 52-bit digits."""

comptime _PAD = 32
"""Zero digits on each side of a digit string, for the IFMA loads that run past its ends."""


def _magnitude(value: Integer, mut limbs: List[UInt64]):
    """Append the magnitude of value in 64-bit limbs, least significant first."""
    var bytes = value.to_bytes()
    var count = len(bytes)
    var full = count // 8
    for l in range(full):
        var limb = UInt64(0)
        comptime for b in range(8):
            limb |= UInt64(bytes.unsafe_get(8 * l + b)) << UInt64(8 * b)
        limbs.append(limb)
    if full * 8 < count:
        var limb = UInt64(0)
        for i in range(full * 8, count):
            limb |= UInt64(bytes.unsafe_get(i)) << UInt64(8 * (i - 8 * full))
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
    var by_sign: List[List[Int]]
    """Each element's term indices, the positive coefficients' first."""
    var positives: List[Int]
    """How many of each element's coefficients are positive."""
    var bits: List[Int]
    """The bit length of each element's largest coefficient."""
    var leads: List[Integer]
    var words: List[UInt64]
    """Each leading coefficient when it fits in 63 bits, otherwise zero."""
    var odd: List[List[UInt64]]
    """The odd part of each leading coefficient, in limbs."""
    var twos: List[Int]
    """The power of two in each leading coefficient."""
    var inverses: List[UInt64]
    """The inverse of each odd part's lowest limb modulo 2^64."""
    var digits: List[List[UInt64]]
    """With IFMA, each long element's coefficients as 52-bit digit strings, `_PAD` zeros apart."""
    var digit_starts: List[List[Int]]
    var digit_counts: List[List[Int]]

    def __init__[W: Int](out self, engine: _Engine[ZZ, W, True], mut budget: Budget) raises PolyError:
        self.limbs = List[List[UInt64]]()
        self.starts = List[List[Int]]()
        self.negative = List[List[Bool]]()
        self.by_sign = List[List[Int]]()
        self.positives = List[Int]()
        self.bits = List[Int]()
        self.leads = List[Integer]()
        self.words = List[UInt64]()
        self.odd = List[List[UInt64]]()
        self.twos = List[Int]()
        self.inverses = List[UInt64]()
        self.digits = List[List[UInt64]]()
        self.digit_starts = List[List[Int]]()
        self.digit_counts = List[List[Int]]()
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
            _allocation[Int](len(negative), budget)
            var by_sign = List[Int](capacity=len(negative))
            for k in range(len(negative)):
                if not negative[k]:
                    by_sign.append(k)
            self.positives.append(len(by_sign))
            for k in range(len(negative)):
                if negative[k]:
                    by_sign.append(k)
            self.by_sign.append(by_sign^)
            var digits = List[UInt64]()
            var digit_starts = List[Int]()
            var digit_counts = List[Int]()
            comptime if _IFMA:
                if bits >= 64 * _IFMA_MIN:
                    _allocation[UInt64](_product(len(starts), 2 * _PAD) + 2 * len(limbs), budget)
                    budget.charge(UInt64(2 * len(limbs)))
                    digits = List[UInt64](length=_PAD, fill=0)
                    for k in range(len(starts) - 1):
                        digit_starts.append(len(digits))
                        _append_digits(limbs.unsafe_ptr().unsafe_offset(starts[k]), starts[k + 1] - starts[k], digits)
                        digit_counts.append(len(digits) - digit_starts[k])
                        for _ in range(_PAD):
                            digits.append(0)
            self.digits.append(digits^)
            self.digit_starts.append(digit_starts^)
            self.digit_counts.append(digit_counts^)
            self.limbs.append(limbs^)
            self.starts.append(starts^)
            self.negative.append(negative^)
            self.bits.append(bits)
            ref lead = p[len(p) - 1].coefficient.value
            var odd = _limbs_of(lead)
            self.words.append(odd[0] if lead.magnitude_bit_length() <= 63 else UInt64(0))
            var twos = 0
            while odd[twos // 64] == 0:
                twos += 64
            twos += Int(count_trailing_zeros(odd[twos // 64]))
            _ = _shift_out(odd, twos)
            # Newton's iteration doubles the correct low bits; x^2 = 1 mod 8 for odd x.
            var inverse = odd[0]
            for _ in range(5):
                inverse *= 2 - odd[0] * inverse
            self.odd.append(odd^)
            self.twos.append(twos)
            self.inverses.append(inverse)
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
    var marks: List[UInt64]
    """A bit per column, set whenever the entry is written, so that scans skip
    untouched columns 64 at a time; every entry with a nonzero size is marked."""
    var scratch: List[UInt64]
    var factor_digits: List[UInt64]
    """With IFMA, the factor of the current load as a padded digit string."""
    var entry_digits: List[UInt64]
    """With IFMA, an entry being scaled, as a padded digit string."""
    var low: List[UInt64]
    var high: List[UInt64]
    """With IFMA, a product's column sums."""

    def __init__(out self, ncols: Int):
        self.ncols = ncols
        self.bound = 0
        self.width = 0
        self.data = List[UInt64]()
        self.sizes = List[Int]()
        self.marks = List[UInt64]()
        self.scratch = List[UInt64]()
        self.factor_digits = List[UInt64]()
        self.entry_digits = List[UInt64]()
        self.low = List[UInt64]()
        self.high = List[UInt64]()

    def prepare(mut self, bits: Int, mut budget: Budget) raises PolyError:
        """Expect entries of about `bits` bits; every entry must be zero."""
        var width = bits // 64 + 1
        if width > self.width or 2 * width < self.width:
            _allocation[UInt64](_product(self.ncols, width), budget)
            self.width = width
            self.data = List[UInt64](length=self.ncols * width, fill=0)
            self.scratch = List[UInt64](length=2 * width + 2, fill=0)
        var words = self.ncols // 64 + 1
        budget.charge(UInt64(words))
        if len(self.sizes) != self.ncols:
            self.sizes = List[Int](length=self.ncols, fill=0)
            self.marks = List[UInt64](length=words, fill=0)
        else:
            # Only marked entries can have nonzero sizes.
            for w in range(words):
                var word = self.marks.unsafe_get(w)
                while word != 0:
                    var c = 64 * w + Int(count_trailing_zeros(word))
                    budget.charge(1)
                    self.sizes.unsafe_get(c) = 0
                    word &= word - 1
                self.marks.unsafe_get(w) = 0
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
        var c = self.next_marked(0)
        while c < self.ncols:
            if self.sizes.unsafe_get(c) > 0:
                self.sizes.unsafe_get(c) = self._entry_bits(c)
                bound = max(bound, self.sizes.unsafe_get(c))
            c = self.next_marked(c + 1)
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
        var bytes = List[UInt8](length=8 * used, fill=0)
        var carry = UInt64(1)
        for l in range(used):
            var limb = self.data.unsafe_get(base + l)
            if negative:
                # The magnitude of a two's complement value: invert and add one.
                limb = ~limb + carry
                carry = UInt64(1) if (carry != 0 and limb == 0) else UInt64(0)
            comptime for b in range(8):
                bytes.unsafe_get(8 * l + b) = UInt8((limb >> UInt64(8 * b)) & 0xFF)
        return Integer.from_bytes(bytes, negative=negative)

    def magnitude_into(self, c: Int, mut limbs: List[UInt64]):
        """Set limbs to the magnitude of entry c, without leading zeros."""
        var base = c * self.width
        var negative = self.negative(c)
        var used = (self._entry_bits(c) + 63) // 64
        limbs.clear()
        var carry = UInt64(1)
        for l in range(used):
            var limb = self.data.unsafe_get(base + l)
            if negative:
                limb = ~limb + carry
                carry = UInt64(1) if (carry != 0 and limb == 0) else UInt64(0)
            limbs.append(limb)
        while len(limbs) and limbs[len(limbs) - 1] == 0:
            _ = limbs.pop()

    def negative(self, c: Int) -> Bool:
        return (self.data.unsafe_get(c * self.width + self.width - 1) >> 63) != 0

    def next_marked(self, c: Int) -> Int:
        """The least marked column at or after c, or `ncols` if none is."""
        if c >= self.ncols:
            return self.ncols
        var w = c // 64
        var word = self.marks.unsafe_get(w) & (UInt64.MAX << UInt64(c % 64))
        while word == 0:
            w += 1
            if w >= len(self.marks):
                return self.ncols
            word = self.marks.unsafe_get(w)
        return min(64 * w + Int(count_trailing_zeros(word)), self.ncols)

    def unmark(mut self, c: Int):
        """Forget a zero entry."""
        self.sizes.unsafe_get(c) = 0
        self.marks.unsafe_get(c // 64) &= ~(UInt64(1) << UInt64(c % 64))

    def set_zero(mut self, c: Int):
        self.marks.unsafe_get(c // 64) &= ~(UInt64(1) << UInt64(c % 64))
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
        self.marks.unsafe_get(c // 64) |= UInt64(1) << UInt64(c % 64)

    def add_product(mut self, c: Int, factor: List[UInt64], terms: List[UInt64], start: Int, end: Int, bits: Int):
        """Add factor times the magnitude terms[start:end], of at most `bits` bits, to entry c."""
        self._grow(c, bits)
        var data = self.data.unsafe_ptr().unsafe_offset(c * self.width)
        _accumulate[False](data, self.width, factor.unsafe_ptr(), len(factor), terms.unsafe_ptr().unsafe_offset(start), end - start)

    def subtract_product(mut self, c: Int, factor: List[UInt64], terms: List[UInt64], start: Int, end: Int, bits: Int):
        """Subtract factor times the magnitude terms[start:end], of at most `bits` bits, from entry c."""
        self._grow(c, bits)
        var data = self.data.unsafe_ptr().unsafe_offset(c * self.width)
        _accumulate[True](data, self.width, factor.unsafe_ptr(), len(factor), terms.unsafe_ptr().unsafe_offset(start), end - start)

    @always_inline
    def word_product[subtract: Bool](mut self, c: Int, factor: Pointer[mut=False, UInt64, _], n: Int, term: UInt64, bits: Int):
        """Add, or subtract, the word term times the magnitude factor[0:n], of at most `bits` bits, to entry c."""
        self._grow(c, bits)
        var data = self.data.unsafe_ptr().unsafe_offset(c * self.width)
        comptime if subtract:
            _sub_mul_1(data, self.width, term, factor, n)
        else:
            _add_mul_1(data, self.width, term, factor, n)

    def set_factor_digits(mut self, factor: List[UInt64]):
        """Keep the factor as a padded digit string for `digit_product`."""
        self.factor_digits.clear()
        for _ in range(_PAD):
            self.factor_digits.append(0)
        _append_digits(factor.unsafe_ptr(), len(factor), self.factor_digits)
        for _ in range(_PAD):
            self.factor_digits.append(0)

    def digit_product[subtract: Bool](mut self, c: Int, digits: List[UInt64], start: Int, count: Int, bits: Int):
        """Add, or subtract, the factor digits times the padded digit string digits[start : start + count] to entry c."""
        self._grow(c, bits)
        var nf = len(self.factor_digits) - 2 * _PAD
        var room = nf + count + _PAD
        if len(self.low) < room:
            self.low.resize(room, 0)
            self.high.resize(room, 0)
        var data = self.data.unsafe_ptr().unsafe_offset(c * self.width)
        var f = self.factor_digits.unsafe_ptr().unsafe_offset(_PAD)
        var t = digits.unsafe_ptr().unsafe_offset(start)
        if nf <= count:
            _ifma[subtract](data, self.width, f, nf, t, count, self.low.unsafe_ptr(), self.high.unsafe_ptr())
        else:
            _ifma[subtract](data, self.width, t, count, f, nf, self.low.unsafe_ptr(), self.high.unsafe_ptr())

    def scale(mut self, first: Int, factor: List[UInt64], bits: Int):
        """Multiply every entry from column `first` on by the positive factor of `bits` bits; the bound must allow it."""
        self.bound += bits
        var digits = False
        comptime if _IFMA:
            if len(factor) >= _IFMA_MIN:
                self.set_factor_digits(factor)
                digits = True
        var scratch = self.scratch.unsafe_ptr()
        var c = self.next_marked(first)
        while c < self.ncols:
            var next = self.next_marked(c + 1)
            if self.is_zero(c):
                c = next
                continue
            # The low u limbs hold the entry X - sign B^u, and the product
            # X s - sign s B^u fits in n limbs before its sign repeats.
            var u = min(self.width, (self.sizes.unsafe_get(c) + 64) // 64)
            var n = min(u + len(factor), self.width)
            self.sizes.unsafe_get(c) += bits
            var entry = self.data.unsafe_ptr().unsafe_offset(c * self.width)
            var negative = (entry.unsafe_offset(self.width - 1).unsafe_load() >> 63) != 0
            for l in range(n):
                scratch.unsafe_offset(l).unsafe_store(0)
            var done = False
            comptime if _IFMA:
                if digits and u >= _IFMA_MIN:
                    self.entry_digits.clear()
                    for _ in range(_PAD):
                        self.entry_digits.append(0)
                    _append_digits(entry, u, self.entry_digits)
                    for _ in range(_PAD):
                        self.entry_digits.append(0)
                    var nf = len(self.factor_digits) - 2 * _PAD
                    var ne = len(self.entry_digits) - 2 * _PAD
                    if len(self.low) < nf + ne + _PAD:
                        self.low.resize(nf + ne + _PAD, 0)
                        self.high.resize(nf + ne + _PAD, 0)
                    var f = self.factor_digits.unsafe_ptr().unsafe_offset(_PAD)
                    var e = self.entry_digits.unsafe_ptr().unsafe_offset(_PAD)
                    if nf <= ne:
                        _ifma[False](scratch, n, f, nf, e, ne, self.low.unsafe_ptr(), self.high.unsafe_ptr())
                    else:
                        _ifma[False](scratch, n, e, ne, f, nf, self.low.unsafe_ptr(), self.high.unsafe_ptr())
                    done = True
            if not done:
                _accumulate[False](scratch, n, factor.unsafe_ptr(), len(factor), entry, u)
            if negative and n > u:
                _ = _subtract_limbs(scratch.unsafe_offset(u), n - u, factor.unsafe_ptr(), min(len(factor), n - u))
            for l in range(n):
                entry.unsafe_offset(l).unsafe_store(scratch.unsafe_offset(l).unsafe_load())
            var fill = UInt64.MAX if negative else UInt64(0)
            for l in range(n, self.width):
                entry.unsafe_offset(l).unsafe_store(fill)
            c = next


def _accumulate[subtract: Bool](data: Pointer[mut=True, UInt64, _], width: Int, a: Pointer[mut=False, UInt64, _], na: Int, b: Pointer[mut=False, UInt64, _], nb: Int):
    """data += a[0:na] * b[0:nb], or -= when `subtract`, over `width` limbs of two's complement.

    Products past the width are dropped, which is exact modulo 2^(64 width).
    A short factor goes in a limb pair at a time, each pair in one carry
    chain along the longer one; two long ones go a column at a time.
    """
    if na > nb:
        _accumulate[subtract](data, width, b, nb, a, na)
        return
    if na >= _COMBA:
        _comba[subtract](data, width, a, na, b, nb)
        return
    var i = 0
    while i + 1 < na and i < width:
        comptime if subtract:
            _sub_mul_2(data.unsafe_offset(i), width - i, a.unsafe_offset(i).unsafe_load(), a.unsafe_offset(i + 1).unsafe_load(), b, nb)
        else:
            _add_mul_2(data.unsafe_offset(i), width - i, a.unsafe_offset(i).unsafe_load(), a.unsafe_offset(i + 1).unsafe_load(), b, nb)
        i += 2
    if i < na and i < width:
        comptime if subtract:
            _sub_mul_1(data.unsafe_offset(i), width - i, a.unsafe_offset(i).unsafe_load(), b, nb)
        else:
            _add_mul_1(data.unsafe_offset(i), width - i, a.unsafe_offset(i).unsafe_load(), b, nb)


@always_inline
def _add_mul_1[whole: Bool = False](data: Pointer[mut=True, UInt64, _], width: Int, f: UInt64, other: Pointer[mut=False, UInt64, _], n: Int):
    """data += f * other[0:n] over `width` limbs of two's complement, in one carry chain."""
    var g = UInt128(f)
    var carry = UInt64(0)
    var m = min(n, width)
    var l = 0
    while l < m:
        var p = g * UInt128(other.unsafe_offset(l).unsafe_load())
        var low = UInt64(p & UInt128(UInt64.MAX))
        var high = UInt64(p >> 64)
        var e = data.unsafe_offset(l).unsafe_load()
        low += e
        high += UInt64(1) if low < e else UInt64(0)
        low += carry
        high += UInt64(1) if low < carry else UInt64(0)
        data.unsafe_offset(l).unsafe_store(low)
        carry = high
        l += 1
    _carry_word[whole](data, width, l, carry)


@always_inline
def _sub_mul_1[whole: Bool = False](data: Pointer[mut=True, UInt64, _], width: Int, f: UInt64, other: Pointer[mut=False, UInt64, _], n: Int):
    """data -= f * other[0:n] over `width` limbs of two's complement, in one borrow chain."""
    var g = UInt128(f)
    var borrow = UInt64(0)
    var m = min(n, width)
    var l = 0
    while l < m:
        var p = g * UInt128(other.unsafe_offset(l).unsafe_load())
        var low = UInt64(p & UInt128(UInt64.MAX))
        var high = UInt64(p >> 64)
        low += borrow
        high += UInt64(1) if low < borrow else UInt64(0)
        var e = data.unsafe_offset(l).unsafe_load()
        data.unsafe_offset(l).unsafe_store(e - low)
        borrow = high + (UInt64(1) if e < low else UInt64(0))
        l += 1
    _borrow_word[whole](data, width, l, borrow)


@always_inline
def _add_mul_2[whole: Bool = False](data: Pointer[mut=True, UInt64, _], width: Int, f0: UInt64, f1: UInt64, b: Pointer[mut=False, UInt64, _], n: Int):
    """data += (f0 + f1 2^64) * b[0:n] over `width` limbs, both limbs in one carry chain.

    Limb l receives the low words of f0 b[l] and f1 b[l - 1], data[l] and
    the carry c0 + c1 2^64, where c1 is at most two; the high words, the
    overflows and c1 make the next carry.
    """
    var m = min(n, width)
    var c0 = UInt64(0)
    var c1 = UInt64(0)
    var previous = UInt64(0)
    var l = 0
    while l < m:
        var bl = b.unsafe_offset(l).unsafe_load()
        var x = UInt128(f0) * UInt128(bl)
        var y = UInt128(f1) * UInt128(previous)
        var x0 = UInt64(x & UInt128(UInt64.MAX))
        var y0 = UInt64(y & UInt128(UInt64.MAX))
        var e = data.unsafe_offset(l).unsafe_load()
        var s = x0 + y0
        var k = UInt64(1) if s < x0 else UInt64(0)
        s += e
        k += UInt64(1) if s < e else UInt64(0)
        s += c0
        k += UInt64(1) if s < c0 else UInt64(0)
        data.unsafe_offset(l).unsafe_store(s)
        var x1 = UInt64(x >> 64)
        var t = x1 + UInt64(y >> 64)
        var o = UInt64(1) if t < x1 else UInt64(0)
        var kc = k + c1
        t += kc
        c1 = o + (UInt64(1) if t < kc else UInt64(0))
        c0 = t
        previous = bl
        l += 1
    if l == n and l < width:
        # The second limb's last product.
        var t = UInt128(f1) * UInt128(previous) + UInt128(c0)
        var t3 = t + UInt128(data.unsafe_offset(l).unsafe_load())
        var over = UInt128(1) if t3 < t else UInt128(0)
        data.unsafe_offset(l).unsafe_store(UInt64(t3 & UInt128(UInt64.MAX)))
        _carry[whole](data, width, l + 1, (t3 >> 64) + (over << 64) + UInt128(c1))


@always_inline
def _sub_mul_2[whole: Bool = False](data: Pointer[mut=True, UInt64, _], width: Int, f0: UInt64, f1: UInt64, b: Pointer[mut=False, UInt64, _], n: Int):
    """data -= (f0 + f1 2^64) * b[0:n] over `width` limbs, both limbs in one borrow chain."""
    var m = min(n, width)
    var c0 = UInt64(0)
    var c1 = UInt64(0)
    var previous = UInt64(0)
    var l = 0
    while l < m:
        var bl = b.unsafe_offset(l).unsafe_load()
        var x = UInt128(f0) * UInt128(bl)
        var y = UInt128(f1) * UInt128(previous)
        var x0 = UInt64(x & UInt128(UInt64.MAX))
        var y0 = UInt64(y & UInt128(UInt64.MAX))
        var s = x0 + y0
        var k = UInt64(1) if s < x0 else UInt64(0)
        s += c0
        k += UInt64(1) if s < c0 else UInt64(0)
        var e = data.unsafe_offset(l).unsafe_load()
        data.unsafe_offset(l).unsafe_store(e - s)
        k += UInt64(1) if e < s else UInt64(0)
        var x1 = UInt64(x >> 64)
        var t = x1 + UInt64(y >> 64)
        var o = UInt64(1) if t < x1 else UInt64(0)
        var kc = k + c1
        t += kc
        c1 = o + (UInt64(1) if t < kc else UInt64(0))
        c0 = t
        previous = bl
        l += 1
    if l == n and l < width:
        var t = UInt128(f1) * UInt128(previous) + UInt128(c0)
        var low = UInt64(t & UInt128(UInt64.MAX))
        var e = data.unsafe_offset(l).unsafe_load()
        data.unsafe_offset(l).unsafe_store(e - low)
        _borrow[whole](data, width, l + 1, (t >> 64) + (UInt128(1) if e < low else UInt128(0)) + UInt128(c1))


def _comba[subtract: Bool](data: Pointer[mut=True, UInt64, _], width: Int, a: Pointer[mut=False, UInt64, _], na: Int, b: Pointer[mut=False, UInt64, _], nb: Int):
    """data += a[0:na] * b[0:nb], or -=, a column at a time for na <= nb.

    Each column's products alternate between two 192-bit accumulators, so
    neighbouring products' additions do not wait on each other.
    """
    var carry = UInt128(0)
    var columns = min(na + nb - 1, width)
    for j in range(columns):
        var first = max(0, j - nb + 1)
        var last = min(j, na - 1)
        var l0 = UInt128(0)
        var h0 = UInt64(0)
        var l1 = UInt128(0)
        var h1 = UInt64(0)
        var k = first
        while k < last:
            var p0 = UInt128(a.unsafe_offset(k).unsafe_load()) * UInt128(b.unsafe_offset(j - k).unsafe_load())
            var p1 = UInt128(a.unsafe_offset(k + 1).unsafe_load()) * UInt128(b.unsafe_offset(j - k - 1).unsafe_load())
            l0 += p0
            h0 += UInt64(1) if l0 < p0 else UInt64(0)
            l1 += p1
            h1 += UInt64(1) if l1 < p1 else UInt64(0)
            k += 2
        if k == last:
            var p0 = UInt128(a.unsafe_offset(k).unsafe_load()) * UInt128(b.unsafe_offset(j - k).unsafe_load())
            l0 += p0
            h0 += UInt64(1) if l0 < p0 else UInt64(0)
        l0 += l1
        h0 += h1 + (UInt64(1) if l0 < l1 else UInt64(0))
        l0 += carry
        h0 += UInt64(1) if l0 < carry else UInt64(0)
        comptime if subtract:
            var low = UInt64(l0 & UInt128(UInt64.MAX))
            var e = data.unsafe_offset(j).unsafe_load()
            data.unsafe_offset(j).unsafe_store(e - low)
            carry = ((l0 >> 64) | (UInt128(h0) << 64)) + (UInt128(1) if e < low else UInt128(0))
        else:
            var e = UInt128(data.unsafe_offset(j).unsafe_load())
            l0 += e
            h0 += UInt64(1) if l0 < e else UInt64(0)
            data.unsafe_offset(j).unsafe_store(UInt64(l0 & UInt128(UInt64.MAX)))
            carry = (l0 >> 64) | (UInt128(h0) << 64)
    comptime if subtract:
        _borrow(data, width, columns, carry)
    else:
        _carry(data, width, columns, carry)


@always_inline
def _carry_word[whole: Bool = False](data: Pointer[mut=True, UInt64, _], width: Int, start: Int, var carry: UInt64):
    """Add the word carry to data[start:width], two's complement.

    With `whole`, the carry goes through every limb even once it is zero, in
    a loop whose length does not depend on the data.
    """
    var l = start
    while (whole or carry != 0) and l < width:
        var x = data.unsafe_offset(l).unsafe_load() + carry
        data.unsafe_offset(l).unsafe_store(x)
        carry = UInt64(1) if x < carry else UInt64(0)
        l += 1


@always_inline
def _borrow_word[whole: Bool = False](data: Pointer[mut=True, UInt64, _], width: Int, start: Int, var borrow: UInt64):
    """Subtract the word borrow from data[start:width], two's complement; `whole` as for `_carry_word`."""
    var l = start
    while (whole or borrow != 0) and l < width:
        var e = data.unsafe_offset(l).unsafe_load()
        data.unsafe_offset(l).unsafe_store(e - borrow)
        borrow = UInt64(1) if e < borrow else UInt64(0)
        l += 1


@always_inline
def _carry[whole: Bool = False](data: Pointer[mut=True, UInt64, _], width: Int, start: Int, var carry: UInt128):
    """Add carry to data[start:width], two's complement; `whole` as for `_carry_word`."""
    var l = start
    while (whole or carry != 0) and l < width:
        var x = UInt128(data.unsafe_offset(l).unsafe_load()) + (carry & UInt128(UInt64.MAX))
        data.unsafe_offset(l).unsafe_store(UInt64(x & UInt128(UInt64.MAX)))
        carry = (carry >> 64) + (x >> 64)
        l += 1


@always_inline
def _borrow[whole: Bool = False](data: Pointer[mut=True, UInt64, _], width: Int, start: Int, var borrow: UInt128):
    """Subtract borrow from data[start:width], two's complement; `whole` as for `_carry_word`."""
    var l = start
    while (whole or borrow != 0) and l < width:
        var e = UInt128(data.unsafe_offset(l).unsafe_load())
        var low = borrow & UInt128(UInt64.MAX)
        data.unsafe_offset(l).unsafe_store(UInt64((e - low) & UInt128(UInt64.MAX)))
        borrow = (borrow >> 64) + (UInt128(1) if e < low else UInt128(0))
        l += 1


comptime _Digits = SIMD[DType.uint64, 8]

comptime _DIGIT = (UInt64(1) << 52) - 1
"""The mask of one 52-bit digit."""


@always_inline
def _madd_low(acc: _Digits, a: _Digits, b: _Digits) -> _Digits:
    """acc plus the low 52 bits of each lane's 52-bit product (AVX-512 IFMA)."""
    return llvm_intrinsic["llvm.x86.avx512.vpmadd52l.uq.512", _Digits](acc, a, b)


@always_inline
def _madd_high(acc: _Digits, a: _Digits, b: _Digits) -> _Digits:
    """acc plus the high 52 bits of each lane's 104-bit product (AVX-512 IFMA)."""
    return llvm_intrinsic["llvm.x86.avx512.vpmadd52h.uq.512", _Digits](acc, a, b)


def _append_digits(limbs: Pointer[mut=False, UInt64, _], n: Int, mut digits: List[UInt64]):
    """Append the magnitude limbs[0:n] as 52-bit digits, least significant first."""
    var buffer = UInt128(0)
    var bits = 0
    for l in range(n):
        buffer |= UInt128(limbs.unsafe_offset(l).unsafe_load()) << UInt128(bits)
        bits += 64
        while bits >= 52:
            digits.append(UInt64(buffer & UInt128(_DIGIT)))
            buffer >>= 52
            bits -= 52
    if bits > 0:
        digits.append(UInt64(buffer & UInt128(_DIGIT)))


def _ifma[subtract: Bool](data: Pointer[mut=True, UInt64, _], width: Int, a: Pointer[mut=False, UInt64, _], da: Int, b: Pointer[mut=False, UInt64, _], db: Int, low: Pointer[mut=True, UInt64, _], high: Pointer[mut=True, UInt64, _]):
    """data += A * B, or -=, over `width` limbs for digit strings a[0:da] and b[0:db], da <= db.

    b must have `_PAD` zero digits on each side. Each block of eight output
    columns accumulates the low and the high halves of its 52-bit products in
    64-bit lanes, which hold 4096 of them; long products take four blocks per
    pass for independent accumulators. The columns are then carried into
    52-bit digits, packed into limbs, and added to the entry.
    """
    var columns = da + db
    if columns < 96:
        for j0 in range(0, columns, 8):
            var l0 = _Digits(0)
            var h0 = _Digits(0)
            for k in range(max(0, j0 - db + 1), min(da - 1, j0 + 7) + 1):
                var x = _Digits(a.unsafe_offset(k).unsafe_load())
                var y = b.unsafe_offset(j0 - k).unsafe_load[width=8]()
                l0 = _madd_low(l0, x, y)
                h0 = _madd_high(h0, x, y)
            low.unsafe_offset(j0).unsafe_store[width=8](l0)
            high.unsafe_offset(j0).unsafe_store[width=8](h0)
    else:
        for j0 in range(0, columns, 32):
            var l0 = _Digits(0)
            var h0 = _Digits(0)
            var l1 = _Digits(0)
            var h1 = _Digits(0)
            var l2 = _Digits(0)
            var h2 = _Digits(0)
            var l3 = _Digits(0)
            var h3 = _Digits(0)
            for k in range(max(0, j0 - db + 1), min(da - 1, j0 + 31) + 1):
                var x = _Digits(a.unsafe_offset(k).unsafe_load())
                var base = b.unsafe_offset(j0 - k)
                var y0 = base.unsafe_load[width=8]()
                var y1 = base.unsafe_offset(8).unsafe_load[width=8]()
                var y2 = base.unsafe_offset(16).unsafe_load[width=8]()
                var y3 = base.unsafe_offset(24).unsafe_load[width=8]()
                l0 = _madd_low(l0, x, y0)
                h0 = _madd_high(h0, x, y0)
                l1 = _madd_low(l1, x, y1)
                h1 = _madd_high(h1, x, y1)
                l2 = _madd_low(l2, x, y2)
                h2 = _madd_high(h2, x, y2)
                l3 = _madd_low(l3, x, y3)
                h3 = _madd_high(h3, x, y3)
            low.unsafe_offset(j0).unsafe_store[width=8](l0)
            high.unsafe_offset(j0).unsafe_store[width=8](h0)
            low.unsafe_offset(j0 + 8).unsafe_store[width=8](l1)
            high.unsafe_offset(j0 + 8).unsafe_store[width=8](h1)
            low.unsafe_offset(j0 + 16).unsafe_store[width=8](l2)
            high.unsafe_offset(j0 + 16).unsafe_store[width=8](h2)
            low.unsafe_offset(j0 + 24).unsafe_store[width=8](l3)
            high.unsafe_offset(j0 + 24).unsafe_store[width=8](h3)
    # Column j holds low[j] + high[j - 1] in units of 2^(52 j); the product
    # fits in `columns` digits, so nothing carries past the last column.
    var carry = UInt128(0)
    var buffer = UInt128(0)
    var bits = 0
    var limb = 0
    var chain = UInt64(0)
    var previous = UInt64(0)
    for j in range(columns + 1):
        if j < columns:
            var t = UInt128(low.unsafe_offset(j).unsafe_load()) + UInt128(previous) + carry
            previous = high.unsafe_offset(j).unsafe_load()
            carry = t >> 52
            buffer |= (t & UInt128(_DIGIT)) << UInt128(bits)
            bits += 52
            if bits < 64:
                continue
        elif bits == 0:
            break
        # A whole limb of the product, or the last partial one.
        if limb < width:
            var e = data.unsafe_offset(limb).unsafe_load()
            var p = UInt64(buffer & UInt128(UInt64.MAX))
            comptime if subtract:
                var d = e - p
                var next = UInt64(1) if e < p else UInt64(0)
                var total = d - chain
                next += UInt64(1) if d < chain else UInt64(0)
                data.unsafe_offset(limb).unsafe_store(total)
                chain = next
            else:
                var sum = e + p
                var next = UInt64(1) if sum < e else UInt64(0)
                var total = sum + chain
                next += UInt64(1) if total < sum else UInt64(0)
                data.unsafe_offset(limb).unsafe_store(total)
                chain = next
        limb += 1
        buffer >>= 64
        bits = max(bits - 64, 0)
    comptime if subtract:
        _borrow(data, width, limb, UInt128(chain))
    else:
        _carry(data, width, limb, UInt128(chain))


def _subtract_limbs(x: Pointer[mut=True, UInt64, _], nx: Int, y: Pointer[mut=False, UInt64, _], ny: Int) -> UInt64:
    """x[0:nx] -= y[0:ny] for ny <= nx; return the borrow out."""
    var borrow = UInt64(0)
    for i in range(ny):
        var e = x.unsafe_offset(i).unsafe_load()
        var p = y.unsafe_offset(i).unsafe_load()
        var difference = e - p
        var next = UInt64(1) if e < p else UInt64(0)
        var total = difference - borrow
        next += UInt64(1) if difference < borrow else UInt64(0)
        x.unsafe_offset(i).unsafe_store(total)
        borrow = next
    var i = ny
    while borrow != 0 and i < nx:
        var e = x.unsafe_offset(i).unsafe_load()
        x.unsafe_offset(i).unsafe_store(e - borrow)
        borrow = UInt64(1) if e == 0 else UInt64(0)
        i += 1
    return borrow


def _remainder_limbs(u: Pointer[mut=True, UInt64, _], length: Int, d: Pointer[mut=False, UInt64, _], n: Int):
    """Reduce u[0:length] modulo d[0:n] in place, leaving the remainder in u[0:n].

    Schoolbook division (Knuth's algorithm D) by a normalized divisor: the
    top limb of d has its high bit set. Needs length >= n >= 1 and a zero
    limb at u[length]. Each quotient limb is estimated from two limbs over
    one, refined against the divisor's second limb, and corrected at most
    once more after the subtraction.
    """
    var top = UInt128(d.unsafe_offset(n - 1).unsafe_load())
    var second = UInt128(d.unsafe_offset(n - 2).unsafe_load()) if n >= 2 else UInt128(0)
    var j = length - n
    while j >= 0:
        var window = u.unsafe_offset(j)
        var numerator = (UInt128(window.unsafe_offset(n).unsafe_load()) << 64) | UInt128(window.unsafe_offset(n - 1).unsafe_load())
        var q = numerator // top
        if q > UInt128(UInt64.MAX):
            q = UInt128(UInt64.MAX)
        var r = numerator - q * top
        if n >= 2:
            while r <= UInt128(UInt64.MAX) and q * second > ((r << 64) | UInt128(window.unsafe_offset(n - 2).unsafe_load())):
                q -= 1
                r += top
        if q != 0:
            _sub_mul_1(window, n + 1, UInt64(q), d, n)
            if window.unsafe_offset(n).unsafe_load() != 0:
                # One too many: the window went negative, and adding d back clears its top limb.
                _add_mul_1(window, n + 1, 1, d, n)
        j -= 1


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


def _divide_exact(mut limbs: List[UInt64], odd: UInt64, twos: Int, inverse: UInt64) -> Bool:
    """Divide the magnitude limbs by odd * 2^twos in place if it divides them; return whether it does.

    Hensel division from the low end: each quotient limb is the running
    difference times the inverse of odd modulo 2^64, and odd divides exactly
    when no borrow is left at the top. On False the limbs hold garbage.
    """
    var n = len(limbs)
    if twos > 0:
        if limbs[0] & ((UInt64(1) << UInt64(twos)) - 1) != 0:
            return False
        for l in range(n):
            var high = limbs.unsafe_get(l + 1) << UInt64(64 - twos) if l + 1 < n else UInt64(0)
            limbs.unsafe_get(l) = (limbs.unsafe_get(l) >> UInt64(twos)) | high
    var borrow = UInt64(0)
    for l in range(n):
        var limb = limbs.unsafe_get(l)
        var x = limb - borrow
        var below = UInt64(1) if x > limb else UInt64(0)
        var q = x * inverse
        limbs.unsafe_get(l) = q
        borrow = UInt64((UInt128(q) * UInt128(odd)) >> 64) + below
    if borrow != 0:
        return False
    while len(limbs) and limbs[len(limbs) - 1] == 0:
        _ = limbs.pop()
    return True


def _shift_out(mut limbs: List[UInt64], twos: Int) -> Bool:
    """Shift the magnitude limbs right by `twos` bits if those bits are zero; return whether they are."""
    var words = twos // 64
    var bits = twos % 64
    if words >= len(limbs):
        return False
    for l in range(words):
        if limbs[l] != 0:
            return False
    if bits > 0 and limbs[words] & ((UInt64(1) << UInt64(bits)) - 1) != 0:
        return False
    var n = len(limbs) - words
    for l in range(n):
        var low = limbs.unsafe_get(l + words) >> UInt64(bits) if bits > 0 else limbs.unsafe_get(l + words)
        var high = limbs.unsafe_get(l + words + 1) << UInt64(64 - bits) if bits > 0 and l + 1 < n else UInt64(0)
        limbs.unsafe_get(l) = low | high
    while len(limbs) > n:
        _ = limbs.pop()
    while len(limbs) and limbs[len(limbs) - 1] == 0:
        _ = limbs.pop()
    return True


def _divide_exact_limbs(mut limbs: List[UInt64], odd: List[UInt64], twos: Int, inverse: UInt64) -> Bool:
    """Divide the magnitude limbs by odd * 2^twos in place if it divides them; return whether it does.

    Hensel division from the low end, a quotient limb at a time: each makes
    the lowest remaining limb zero, and the division is exact when nothing
    is left above the quotient, with a guard limb catching a final borrow.
    On False the limbs hold garbage.
    """
    if not _shift_out(limbs, twos):
        return False
    var m = len(odd)
    var n = len(limbs)
    if n < m:
        return False
    limbs.append(0)
    var k = n - m + 1
    var w = limbs.unsafe_ptr()
    for i in range(k):
        var q = w.unsafe_offset(i).unsafe_load() * inverse
        _sub_mul_1(w.unsafe_offset(i), n + 1 - i, q, odd.unsafe_ptr(), m)
        w.unsafe_offset(i).unsafe_store(q)
    for j in range(k, n + 1):
        if w.unsafe_offset(j).unsafe_load() != 0:
            return False
    while len(limbs) > k:
        _ = limbs.pop()
    while len(limbs) and limbs[len(limbs) - 1] == 0:
        _ = limbs.pop()
    return True


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
    var routes = _pair_routes(engine, budget, _PAIR_PRIMES)
    comptime if _CERT_STATS:
        print("CERT pass_ms", routes.counts[0] // 1000000, "prove_ms", routes.counts[1] // 1000000, "attempts", routes.counts[2], "fractions", routes.counts[3], "slots combined", routes.counts[4], "fraction_ms", routes.counts[5] // 1000000)
        print("CERT modular units", routes.counts[6], "ns", routes.counts[7], "exact units", routes.counts[8], "ns", routes.counts[9])
        print("CERT pairs", routes.modular + routes.exact, "modular", routes.modular, "exact", routes.exact, "primes/modular pair", Float64(routes.primes) / Float64(max(routes.modular, 1)))
    return routes.zero


@fieldwise_init
struct _Routes(Copyable, Movable):
    """How `_pair_routes` decided: whether every pair reduced to zero, and how many pairs each route proved."""
    var zero: Bool
    var modular: Int
    var exact: Int
    var primes: Int
    """Primes the modularly proved pairs used, in all."""
    var counts: List[Int]


def _pair_routes[W: Int](mut engine: _Engine[ZZ, W, True], mut budget: Budget, primes: Int) raises PolyError -> _Routes:
    """As `_pairs_reduce_to_zero`, which it decides, with up to `primes` primes per pair.

    Each pair first tries a standard representation found modulo up to
    `primes` primes (`_modular_pair`); a pair it does not prove, and every
    pair when `primes` is below `_LANES`, is reduced exactly over the
    integers. Stops at the first pair that does not reduce to zero.
    """
    engine.sort_active(budget)
    var store = _Store[W]()
    store.extend(engine, budget)
    var coefficients = _Coefficients(engine, budget)
    var images = _PairPrimes(coefficients, primes, budget)
    var counts = List[Int](length=10, fill=0)
    # With `_CERT_STATS`: nanoseconds in passes and in proofs, attempts, fractions, slots combined.
    var quotient = List[UInt64]()
    var modular = 0
    var exact = 0
    var used = 0
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
        var lanes = _LaneRow(ncols, budget)
        # Costs of this degree's long pairs, those reaching `_LONG` primes, by
        # the cost models `_modular_cost` and `_exact_cost`, which count
        # operations, never time: a few, and then one in `_EVERY`, are also checked
        # exactly, which compares the routes on the same pairs. A modular
        # attempt stops once it costs as much as an average exact check; the
        # degree turns to the exact check alone once most attempts fail, or
        # once the sampled pairs cost more than `_RATIO` percent modularly,
        # counting the exact checks of those the modular route left.
        var tried = 0
        var failed = 0
        var sampled = 0
        var sample_modular = 0
        var sample_exact = 0
        var hint = 0
        for a in halves:
            var cheaper = sampled < _TIMED or 100 * sample_modular <= _RATIO * sample_exact
            var exactly = True
            var attempted = False
            var spent = 0
            var k = 0
            if images.limit > 0 and cheaper and (failed < _GIVE_UP or 2 * failed <= tried):
                tried += 1
                attempted = True
                var allowance = 0
                if sampled > 0:
                    allowance = sample_exact // sampled
                var t0 = _clock()
                var cost = 0
                # The primes the last pair needed: attempts start a batch below.
                k = _modular_pair(lanes, matrix, pivot, coefficients, images, a, max(_FIRST_PRIMES, hint - _LANES), allowance, cost, counts, budget)
                spent = cost
                counts[6] += cost
                counts[7] += _clock() - t0
                if k > 0:
                    modular += 1
                    used += k
                    hint = k
                    exactly = False
                else:
                    failed += 1
            # Past the first samples, only a close comparison needs more.
            var close = 100 * sample_modular > _CLEAR * sample_exact
            var sample = attempted and (k == 0 or k >= _LONG) and (sampled < _TIMED or (close and tried % _EVERY == 0))
            if not exactly and not sample:
                continue
            if exactly:
                exact += 1
            var before = budget.remaining()
            var terms = 0
            var t = _clock()
            if not _reduces(row, matrix, pivot, coefficients, a, quotient, terms, budget):
                return _Routes(False, modular, exact, used, counts.copy())
            var e = _exact_cost(Int(before - budget.remaining()), terms, ncols - Int(matrix.entries[matrix.starts[a]]))
            counts[8] += e
            counts[9] += _clock() - t
            if sample:
                sampled += 1
                sample_exact += e
                # The modular route's cost: its attempt, and the exact check after a failure.
                sample_modular += spent + (e if exactly else 0)
    return _Routes(True, modular, exact, used, counts.copy())


def _reduces[W: Int](mut row: _Row, matrix: _Matrix[W], pivot: List[Int], coefficients: _Coefficients, a: Int, mut quotient: List[UInt64], mut terms: Int, mut budget: Budget) raises PolyError -> Bool:
    """Whether the S-polynomial of matrix rows a and a + 1, which lead in one column, reduces to zero.

    Adds the number of row terms it loads to `terms`, for `_exact_cost`.
    """
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
    terms += matrix.starts[b + 1] - matrix.starts[a]
    var first = Int(matrix.entries[matrix.starts[a]])
    row.set_zero(first)
    var c = row.next_marked(first + 1)
    while c < row.ncols:
        budget.charge(UInt64(row.width))
        if row.is_zero(c):
            row.unmark(c)
        else:
            var q = pivot[c]
            if q < 0:
                return False
            terms += matrix.starts[q + 1] - matrix.starts[q]
            _cancel(row, matrix, coefficients, c, q, c, quotient, budget)
        c = row.next_marked(c + 1)
    return True


def _cancel[W: Int](mut row: _Row, matrix: _Matrix[W], coefficients: _Coefficients, c: Int, q: Int, first: Int, mut quotient: List[UInt64], mut budget: Budget) raises PolyError:
    """Make entry c zero with matrix row q, which leads in column c.

    The row is scaled first, from column `first` on, when the leading
    coefficient d of row q does not divide the entry v: by d / gcd(d, v),
    which is positive since leading coefficients are.
    """
    var g = matrix.sources[q]
    var d = coefficients.words[g]
    if d != 0:
        # A word-sized leading coefficient: divide in limbs, into `quotient`.
        var negative = row.negative(c)
        row.magnitude_into(c, quotient)
        budget.charge(UInt64(2 * len(quotient)))
        if not _divide_exact(quotient, coefficients.odd[g][0], coefficients.twos[g], coefficients.inverses[g]):
            row.magnitude_into(c, quotient)
            var common = _word_gcd(d, _remainder(quotient, d))
            var s: List[UInt64] = [d // common]
            _divide(quotient, common)
            row.room_for_scale(_bits(s), budget)
            budget.charge(UInt64(_product(row.ncols - first, row.width)))
            row.scale(first, s, _bits(s))
        _load(row, matrix, coefficients, q, quotient, negative, True, budget)
        row.set_zero(c)
        return
    # Most entries are multiples of d: divide in limbs, into `quotient`.
    var negative = row.negative(c)
    row.magnitude_into(c, quotient)
    budget.charge(UInt64(_product(len(quotient), len(coefficients.odd[g]))))
    if _divide_exact_limbs(quotient, coefficients.odd[g], coefficients.twos[g], coefficients.inverses[g]):
        _load(row, matrix, coefficients, q, quotient, negative, True, budget)
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
    var quotient = List[UInt64]()
    var result = List[List[_Term[ZZ, W]]](capacity=basis_rows)
    for r in range(basis_rows):
        # A row with no tail column that some row leads is already reduced.
        var reducible = False
        budget.charge(UInt64(matrix.starts[r + 1] - matrix.starts[r]))
        for k in range(matrix.starts[r] + 1, matrix.starts[r + 1]):
            if pivot[Int(matrix.entries[k])] >= 0:
                reducible = True
                break
        if not reducible:
            ref p = engine.polys[matrix.sources[r]]
            _allocation[_Term[ZZ, W]](len(p), budget)
            var terms = List[_Term[ZZ, W]](capacity=len(p))
            for t in p:
                terms.append(_Term[ZZ, W](t.monomial, t.coefficient.copy()))
            result.append(terms^)
            continue
        row.prepare(coefficients.bits[matrix.sources[r]] + 1, budget)
        _load(row, matrix, coefficients, r, unit, False, False, budget)
        var first = Int(matrix.entries[matrix.starts[r]])
        var c = row.next_marked(first + 1)
        while c < ncols:
            budget.charge(UInt64(row.width))
            if not row.is_zero(c) and pivot[c] >= 0:
                _cancel(row, matrix, coefficients, c, pivot[c], first, quotient, budget)
            c = row.next_marked(c + 1)
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
    var s = matrix.starts[r]
    var n = matrix.starts[r + 1] - s
    budget.charge(UInt64(_product(n, len(factor) * (coefficients.bits[g] // 64 + 1) + row.width)))
    ref by_sign = coefficients.by_sign[g]
    var positives = coefficients.positives[g]
    # Each column takes one term, so the terms go in any order: those to add,
    # then those to subtract, with no branch on each term's sign.
    var plus_first = subtract == negative
    if coefficients.bits[g] <= 64:
        # Word coefficients, the common case: one carry chain along the factor per term.
        if plus_first:
            _word_terms[minus=False](row, matrix, s, by_sign, 0, positives, limbs, factor, bits)
            _word_terms[minus=True](row, matrix, s, by_sign, positives, n, limbs, factor, bits)
        else:
            _word_terms[minus=True](row, matrix, s, by_sign, 0, positives, limbs, factor, bits)
            _word_terms[minus=False](row, matrix, s, by_sign, positives, n, limbs, factor, bits)
        return
    var digits = False
    comptime if _IFMA:
        if len(factor) >= _IFMA_MIN and len(coefficients.digits[g]) > 0:
            row.set_factor_digits(factor)
            digits = True
    if plus_first:
        _long_terms[minus=False](row, matrix, coefficients, g, s, 0, positives, factor, digits, bits)
        _long_terms[minus=True](row, matrix, coefficients, g, s, positives, n, factor, digits, bits)
    else:
        _long_terms[minus=True](row, matrix, coefficients, g, s, 0, positives, factor, digits, bits)
        _long_terms[minus=False](row, matrix, coefficients, g, s, positives, n, factor, digits, bits)


@always_inline
def _word_terms[W: Int, minus: Bool](mut row: _Row, matrix: _Matrix[W], s: Int, by_sign: List[Int], begin: Int, end: Int, limbs: List[UInt64], factor: List[UInt64], bits: Int):
    """Add, or subtract when `minus`, factor times the word terms by_sign[begin:end] of the matrix row starting at s."""
    var f = factor.unsafe_ptr()
    var nf = len(factor)
    for i in range(begin, end):
        var k = by_sign.unsafe_get(i)
        var c = Int(matrix.entries.unsafe_get(s + k))
        row.word_product[minus](c, f, nf, limbs.unsafe_get(k), bits)


def _long_terms[W: Int, minus: Bool](mut row: _Row, matrix: _Matrix[W], coefficients: _Coefficients, g: Int, s: Int, begin: Int, end: Int, factor: List[UInt64], digits: Bool, bits: Int):
    """Add, or subtract when `minus`, factor times the terms by_sign[begin:end] of element g's matrix row starting at s."""
    ref limbs = coefficients.limbs[g]
    ref starts = coefficients.starts[g]
    ref by_sign = coefficients.by_sign[g]
    for i in range(begin, end):
        var k = by_sign.unsafe_get(i)
        var c = Int(matrix.entries.unsafe_get(s + k))
        comptime if _IFMA:
            if digits and starts.unsafe_get(k + 1) - starts.unsafe_get(k) >= _IFMA_MIN:
                row.digit_product[minus](c, coefficients.digits[g], coefficients.digit_starts[g].unsafe_get(k), coefficients.digit_counts[g].unsafe_get(k), bits)
                continue
        comptime if minus:
            row.subtract_product(c, factor, limbs, starts.unsafe_get(k), starts.unsafe_get(k + 1), bits)
        else:
            row.add_product(c, factor, limbs, starts.unsafe_get(k), starts.unsafe_get(k + 1), bits)


comptime _PAIR_PRIMES = 128
"""Primes a pair's modular standard representation may use before the pair is reduced exactly."""

comptime _FIRST_PRIMES = _LANES
"""Primes of a pair's first attempt; each later batch of `_LANES` primes makes another."""

comptime _GIVE_UP = 4
"""Pairs of a degree that must fail modularly, and be most of those tried, before the rest skip the modular attempt."""

comptime _TIMED = 3
"""Long pairs a degree samples before comparing the routes' costs."""

comptime _RATIO = 85
"""Percent of the exact cost above which a degree leaves the modular route."""

comptime _LONG = 48
"""Primes from which a pair counts as long, and may be sampled (see `_pair_routes`)."""

comptime _EVERY = 32
"""After the first `_TIMED`, one long pair in this many is sampled, while the comparison is close."""

comptime _CLEAR = 60
"""Percent of the exact cost below which the modular route wins clearly and sampling stops."""

comptime _CERT_STATS = False
"""Whether certification prints how many pairs each route proved."""


def _clock() -> Int:
    """Nanoseconds for the statistics of `_CERT_STATS`, and zero without them; nothing decides by it."""
    comptime if _CERT_STATS:
        return Int(perf_counter_ns())
    return 0


def _exact_cost(units: Int, terms: Int, columns: Int) -> Int:
    """The exact check's cost model, in hundredths of a nanosecond on the
    calibration machine: from its budget units, the row terms it loaded and
    the columns after the pair's leading one (fitted over cyclic-7/8,
    katsura-9/10, eco-10/11 and noon-8 to a few percent)."""
    return 79 * units + 1030 * terms + 165 * columns


def _modular_cost(lane_units: Int, crt_units: Int, slots: Int) -> Int:
    """The modular route's cost model, in the units of `_exact_cost`: from the
    budget units of its lane sweeps and of its proofs, and the quotient slots
    its attempts combine (fitted as `_exact_cost`, to about fifteen percent)."""
    return 38 * lane_units + 232 * crt_units + 21000 * slots


def _remainder_of(limbs: Pointer[mut=False, UInt64, _], n: Int, d: UInt64) -> UInt64:
    var r = UInt128(0)
    for l in range(n - 1, -1, -1):
        r = ((r << 64) | UInt128(limbs.unsafe_offset(l).unsafe_load())) % UInt128(d)
    return UInt64(r)


def _power(var b: UInt64, var e: UInt64, p: UInt64) -> UInt64:
    var r = UInt64(1)
    b %= p
    while e:
        if e & 1:
            r = r * b % p
        b = b * b % p
        e >>= 1
    return r


def _residue_of(value: Integer, p: UInt64) -> UInt64:
    var limbs = _limbs_of(value)
    var x = _remainder_of(limbs.unsafe_ptr(), len(limbs), p)
    if value.sign() < 0 and x != 0:
        x = p - x
    return x


struct _Basis(Movable):
    """The CRT basis of the first k primes, as `_Crt` in `_rational_groebner`: for
    product Q, Q_i = Q / p_i and c_i = Q_i^-1 modulo p_i, residues r_i give
    x = sum r_i e_i - m Q with e_i = c_i Q_i and m = floor(sum r_i c_i / p_i)."""
    var product: List[UInt64]
    var basis: List[UInt64]
    var weights: List[Float64]
    var limbs: Int
    var modulus: Integer
    var bits: Int
    """The bit length of Q."""

    def __init__(out self, primes: List[UInt64], k: Int, mut budget: Budget) raises PolyError:
        self.product = [UInt64(1)]
        for i in range(k):
            budget.charge(UInt64(len(self.product)))
            var carry = UInt128(0)
            for l in range(len(self.product)):
                var x = UInt128(self.product[l]) * UInt128(primes[i]) + carry
                self.product[l] = UInt64(x & UInt128(UInt64.MAX))
                carry = x >> 64
            if carry:
                self.product.append(UInt64(carry))
        self.limbs = len(self.product)
        self.bits = _bits(self.product)
        _allocation[UInt64](_product(k, self.limbs), budget)
        self.basis = List[UInt64](length=k * self.limbs, fill=0)
        self.weights = List[Float64](capacity=k)
        for i in range(k):
            var prime = primes[i]
            budget.charge(UInt64(3 * self.limbs))
            var cofactor = self.product.copy()
            _divide(cofactor, prime)
            var c = _power(_remainder(cofactor, prime), prime - 2, prime)
            var carry = UInt128(0)
            for l in range(self.limbs):
                var x = (UInt128(cofactor[l]) if l < len(cofactor) else UInt128(0)) * UInt128(c) + carry
                self.basis[i * self.limbs + l] = UInt64(x & UInt128(UInt64.MAX))
                carry = x >> 64
            self.weights.append(Float64(c) / Float64(prime))
        var bytes = List[UInt8](length=8 * self.limbs, fill=0)
        for l in range(self.limbs):
            comptime for shift in range(8):
                bytes[8 * l + shift] = UInt8((self.product[l] >> UInt64(8 * shift)) & 0xFF)
        self.modulus = Integer.from_bytes(bytes)

    def value(self, residues: List[UInt64], mut work: List[UInt64], mut budget: Budget) raises PolyError:
        """Set work (limbs + 2 limbs) to the number below Q with the given residues."""
        var k = len(self.weights)
        budget.charge(UInt64(_product(k, self.limbs)))
        var n = self.limbs + 2
        var data = work.unsafe_ptr()
        for l in range(n):
            data.unsafe_offset(l).unsafe_store(0)
        var estimate = Float64(0)
        for i in range(k):
            var r = residues.unsafe_get(i)
            if r == 0:
                continue
            _add_mul_1(data, n, r, self.basis.unsafe_ptr().unsafe_offset(i * self.limbs), self.limbs)
            estimate += Float64(r) * self.weights.unsafe_get(i)
        var m = UInt64(estimate)
        if m:
            _sub_mul_1(data, n, m, self.product.unsafe_ptr(), self.limbs)
        while (data.unsafe_offset(n - 1).unsafe_load() >> 63) != 0:
            _add_mul_1(data, n, 1, self.product.unsafe_ptr(), self.limbs)
        while _compare_limbs(work, self.product) >= 0:
            _sub_mul_1(data, n, 1, self.product.unsafe_ptr(), self.limbs)


def _compare_limbs(x: List[UInt64], y: List[UInt64]) -> Int:
    """The sign of x - y for nonnegative limb strings, ignoring lengths."""
    for l in range(max(len(x), len(y)) - 1, -1, -1):
        var a = x[l] if l < len(x) else UInt64(0)
        var b = y[l] if l < len(y) else UInt64(0)
        if a != b:
            return 1 if a > b else -1
    return 0


def _limbs_to_integer(limbs: List[UInt64], n: Int) -> Integer:
    var bytes = List[UInt8](length=8 * n, fill=0)
    for l in range(n):
        comptime for shift in range(8):
            bytes[8 * l + shift] = UInt8((limbs[l] >> UInt64(8 * shift)) & 0xFF)
    return Integer.from_bytes(bytes)


struct _PairPrimes(Movable):
    """Primes below 2^31 that divide no leading coefficient, `_LANES` at a time,
    with each element's coefficients modulo them made monic, and the CRT basis
    of each attempt's primes."""
    var limit: Int
    """Primes a pair may use: a multiple of `_LANES`, or zero."""
    var primes: List[UInt64]
    var batches: List[_Primes]
    var values: List[List[List[UInt32]]]
    """Per batch and element, its monic coefficients, `_LANES` residues per term."""
    var inverses: List[List[UInt64]]
    """Per batch, each element's leading coefficient inverse, `_LANES` per element."""
    var bases: List[_Basis]
    """The CRT basis of the first `_LANES` * (i + 1) primes."""

    def __init__(out self, coefficients: _Coefficients, limit: Int, mut budget: Budget) raises PolyError:
        self.limit = (limit // _LANES) * _LANES
        self.primes = List[UInt64]()
        self.batches = List[_Primes]()
        self.values = List[List[List[UInt32]]]()
        self.inverses = List[List[UInt64]]()
        self.bases = List[_Basis]()
        var candidate = UInt64(1) << 31
        while len(self.primes) < self.limit:
            candidate -= 1
            budget.charge(1)
            if not _prime(candidate, budget):
                continue
            var divides = False
            for lead in coefficients.leads:
                if _residue_of(lead, candidate) == 0:
                    divides = True
                    break
            if not divides:
                self.primes.append(candidate)

    def ensure(mut self, batch: Int, coefficients: _Coefficients, mut budget: Budget) raises PolyError:
        """Prepare the residues of batches up to `batch`."""
        if len(self.batches) > batch:
            return
        while len(self.batches) <= batch:
            var b = len(self.batches)
            var rings = List[Modulus]()
            for l in range(_LANES):
                rings.append(Modulus(_prime_value=self.primes[_LANES * b + l]))
            var lanes = _Primes(rings)
            var values = List[List[UInt32]]()
            var inverses = List[UInt64](length=_LANES * len(coefficients.limbs), fill=0)
            for g in range(len(coefficients.limbs)):
                var n = len(coefficients.starts[g]) - 1
                budget.charge(UInt64(_product(_LANES, len(coefficients.limbs[g]) + n)))
                _allocation[UInt32](_LANES * n, budget)
                var r = List[UInt32](length=_LANES * n, fill=0)
                ref limbs = coefficients.limbs[g]
                ref starts = coefficients.starts[g]
                for l in range(_LANES):
                    var p = lanes.primes[l]
                    var lead = _remainder_of(limbs.unsafe_ptr().unsafe_offset(starts[0]), starts[1] - starts[0], p)
                    var inverse = _power(lead, p - 2, p)
                    inverses[_LANES * g + l] = inverse
                    for k in range(n):
                        var x = _remainder_of(limbs.unsafe_ptr().unsafe_offset(starts[k]), starts[k + 1] - starts[k], p)
                        if coefficients.negative[g][k] and x != 0:
                            x = p - x
                        r[_LANES * k + l] = UInt32(x * inverse % p)
                values.append(r^)
            self.batches.append(lanes^)
            self.values.append(values^)
            self.inverses.append(inverses^)

    def basis(mut self, attempt: Int, mut budget: Budget) raises PolyError:
        """Prepare the CRT basis of attempt `attempt`."""
        while len(self.bases) <= attempt:
            self.bases.append(_Basis(self.primes, _LANES * (len(self.bases) + 1), budget))


struct _LaneRow(Movable):
    """A dense row with a residue per lane prime in each column, and a mark per written column."""
    var data: List[UInt64]
    var marks: List[UInt64]
    var ncols: Int
    var slot: List[Int]
    """Per column, the quotient slot of the pair being reduced, or -1."""
    var columns: List[Int]
    """Per slot, its column."""
    var residues: List[UInt32]
    """Per slot, `limit` residues of the entry the reducer met, prime by prime."""

    def __init__(out self, ncols: Int, mut budget: Budget) raises PolyError:
        _allocation[UInt64](_product(2 * _LANES + 1, ncols), budget)
        self.ncols = ncols
        self.data = List[UInt64](length=2 * _LANES * ncols, fill=0)
        self.marks = List[UInt64](length=ncols // 64 + 1, fill=0)
        self.slot = List[Int](length=ncols, fill=-1)
        self.columns = List[Int]()
        self.residues = List[UInt32]()

    @always_inline
    def mark(mut self, c: Int):
        self.marks.unsafe_get(c // 64) |= UInt64(1) << UInt64(c % 64)

    def next_marked(self, c: Int) -> Int:
        if c >= self.ncols:
            return self.ncols
        var w = c // 64
        var word = self.marks.unsafe_get(w) & (UInt64.MAX << UInt64(c % 64))
        while word == 0:
            w += 1
            if w >= len(self.marks):
                return self.ncols
            word = self.marks.unsafe_get(w)
        return min(64 * w + Int(count_trailing_zeros(word)), self.ncols)

    def clear(mut self, stride: Int):
        """Zero every marked column, `stride` lanes apart, and forget the slots."""
        for w in range(len(self.marks)):
            var word = self.marks.unsafe_get(w)
            while word != 0:
                var c = 64 * w + Int(count_trailing_zeros(word))
                for l in range(0, stride, _LANES):
                    self.data.unsafe_ptr().unsafe_offset(stride * c + l).unsafe_store[width=_LANES](_Lanes(0))
                word &= word - 1
            self.marks.unsafe_get(w) = 0
        for c in self.columns:
            self.slot.unsafe_get(c) = -1
        self.columns.clear()
        self.residues.clear()

    def add(mut self, columns: Pointer[mut=False, Int32, _], values: Pointer[mut=False, UInt32, _], n: Int, factor: _Lanes, squares: _Lanes, skip: Int):
        """Add factor times a row of residues, after its first `skip` entries; entries stay below p^2."""
        var data = self.data.unsafe_ptr()
        var marks = self.marks.unsafe_ptr()
        for k in range(skip, n):
            var c = Int(columns.unsafe_offset(k).unsafe_load())
            var at = data.unsafe_offset(_LANES * c)
            var x = at.unsafe_load[width=_LANES]() + factor * values.unsafe_offset(_LANES * k).unsafe_load[width=_LANES]().cast[DType.uint64]()
            at.unsafe_store[width=_LANES](x.ge(squares).select(x - squares, x))
            var word = marks.unsafe_offset(c >> 6)
            word.unsafe_store(word.unsafe_load() | (UInt64(1) << UInt64(c & 63)))


def _lane_pass_two[W: Int](mut lanes: _LaneRow, matrix: _Matrix[W], pivot: List[Int], values: List[List[UInt32]], others: List[List[UInt32]], primes: _Primes, more: _Primes, a: Int, batch: Int, limit: Int, mut budget: Budget) raises PolyError -> Bool:
    """As `_lane_pass` for batches `batch` and `batch` + 1 in one sweep, two `_LANES` apart in each column."""
    comptime S = 2 * _LANES
    var data = lanes.data.unsafe_ptr()
    var marks = lanes.marks.unsafe_ptr()
    var b = a + 1
    var first = Int(matrix.entries[matrix.starts[a]])
    for half in range(2):
        var r = a + half
        var s = matrix.starts[r]
        var n = matrix.starts[r + 1] - s
        var columns = matrix.entries.unsafe_ptr().unsafe_offset(s)
        var v0 = values[matrix.sources[r]].unsafe_ptr()
        var v1 = others[matrix.sources[r]].unsafe_ptr()
        var f0 = _Lanes(1) if half == 0 else primes.primes - 1
        var f1 = _Lanes(1) if half == 0 else more.primes - 1
        for k in range(n):
            var c = Int(columns.unsafe_offset(k).unsafe_load())
            var at = data.unsafe_offset(S * c)
            at.unsafe_store[width=_LANES](at.unsafe_load[width=_LANES]() + f0 * v0.unsafe_offset(_LANES * k).unsafe_load[width=_LANES]().cast[DType.uint64]())
            var at1 = at.unsafe_offset(_LANES)
            at1.unsafe_store[width=_LANES](at1.unsafe_load[width=_LANES]() + f1 * v1.unsafe_offset(_LANES * k).unsafe_load[width=_LANES]().cast[DType.uint64]())
            var word = marks.unsafe_offset(c >> 6)
            word.unsafe_store(word.unsafe_load() | (UInt64(1) << UInt64(c & 63)))
    budget.charge(UInt64(S * (matrix.starts[b + 1] - matrix.starts[a])))
    data.unsafe_offset(S * first).unsafe_store[width=_LANES](_Lanes(0))
    data.unsafe_offset(S * first + _LANES).unsafe_store[width=_LANES](_Lanes(0))
    lanes.marks.unsafe_get(first // 64) &= ~(UInt64(1) << UInt64(first % 64))
    var c = lanes.next_marked(first + 1)
    while c < lanes.ncols:
        lanes.marks.unsafe_get(c // 64) &= ~(UInt64(1) << UInt64(c % 64))
        var at = data.unsafe_offset(S * c)
        var u = _mod_lanes(at.unsafe_load[width=_LANES](), primes)
        var w = _mod_lanes(at.unsafe_offset(_LANES).unsafe_load[width=_LANES](), more)
        at.unsafe_store[width=_LANES](_Lanes(0))
        at.unsafe_offset(_LANES).unsafe_store[width=_LANES](_Lanes(0))
        if u.ne(0).reduce_or() or w.ne(0).reduce_or():
            var q = pivot.unsafe_get(c)
            if q < 0:
                lanes.clear(S)
                return False
            var slot = lanes.slot.unsafe_get(c)
            if slot < 0:
                slot = len(lanes.columns)
                lanes.slot.unsafe_get(c) = slot
                lanes.columns.append(c)
                lanes.residues.resize(len(lanes.residues) + limit, 0)
            var to = lanes.residues.unsafe_ptr().unsafe_offset(slot * limit + _LANES * batch)
            to.unsafe_store[width=_LANES](u.cast[DType.uint32]())
            to.unsafe_offset(_LANES).unsafe_store[width=_LANES](w.cast[DType.uint32]())
            var s = matrix.starts.unsafe_get(q)
            var n = matrix.starts.unsafe_get(q + 1) - s
            budget.charge(UInt64(S * n))
            var f0 = u.eq(0).select(_Lanes(0), primes.primes - u)
            var f1 = w.eq(0).select(_Lanes(0), more.primes - w)
            var columns = matrix.entries.unsafe_ptr().unsafe_offset(s)
            var g = matrix.sources.unsafe_get(q)
            var v0 = values[g].unsafe_ptr()
            var v1 = others[g].unsafe_ptr()
            for k in range(1, n):
                var e = Int(columns.unsafe_offset(k).unsafe_load())
                var to0 = data.unsafe_offset(S * e)
                var x = to0.unsafe_load[width=_LANES]() + f0 * v0.unsafe_offset(_LANES * k).unsafe_load[width=_LANES]().cast[DType.uint64]()
                to0.unsafe_store[width=_LANES](x.ge(primes.squares).select(x - primes.squares, x))
                var to1 = to0.unsafe_offset(_LANES)
                var y = to1.unsafe_load[width=_LANES]() + f1 * v1.unsafe_offset(_LANES * k).unsafe_load[width=_LANES]().cast[DType.uint64]()
                to1.unsafe_store[width=_LANES](y.ge(more.squares).select(y - more.squares, y))
                var word = marks.unsafe_offset(e >> 6)
                word.unsafe_store(word.unsafe_load() | (UInt64(1) << UInt64(e & 63)))
        c = lanes.next_marked(c + 1)
    return True


def _lane_pass[W: Int](mut lanes: _LaneRow, matrix: _Matrix[W], pivot: List[Int], values: List[List[UInt32]], primes: _Primes, a: Int, batch: Int, limit: Int, mut budget: Budget) raises PolyError -> Bool:
    """Reduce S / L, for the S-polynomial of rows a and a + 1, in every lane, recording the entries reducers meet.

    With L = la * lc(g_a) = lb * lc(g_b), S / L is the difference of the two
    monic rows. Returns False, with the row cleared, when a nonzero residue
    meets a column no row leads in: then S does not reduce to zero, and the
    exact check decides. Otherwise the row is zero again.
    """
    var data = lanes.data.unsafe_ptr()
    var b = a + 1
    var sa = matrix.starts[a]
    var sb = matrix.starts[b]
    lanes.add(matrix.entries.unsafe_ptr().unsafe_offset(sa), values[matrix.sources[a]].unsafe_ptr(), matrix.starts[a + 1] - sa, _Lanes(1), primes.squares, 0)
    lanes.add(matrix.entries.unsafe_ptr().unsafe_offset(sb), values[matrix.sources[b]].unsafe_ptr(), matrix.starts[b + 1] - sb, primes.primes - 1, primes.squares, 0)
    budget.charge(UInt64(_LANES * (matrix.starts[b + 1] - sa)))
    var first = Int(matrix.entries[sa])
    data.unsafe_offset(_LANES * first).unsafe_store[width=_LANES](_Lanes(0))
    lanes.marks.unsafe_get(first // 64) &= ~(UInt64(1) << UInt64(first % 64))
    var c = lanes.next_marked(first + 1)
    while c < lanes.ncols:
        lanes.marks.unsafe_get(c // 64) &= ~(UInt64(1) << UInt64(c % 64))
        var at = data.unsafe_offset(_LANES * c)
        var v = _mod_lanes(at.unsafe_load[width=_LANES](), primes)
        at.unsafe_store[width=_LANES](_Lanes(0))
        if v.ne(0).reduce_or():
            var q = pivot.unsafe_get(c)
            if q < 0:
                lanes.clear(_LANES)
                return False
            var slot = lanes.slot.unsafe_get(c)
            if slot < 0:
                slot = len(lanes.columns)
                lanes.slot.unsafe_get(c) = slot
                lanes.columns.append(c)
                lanes.residues.resize(len(lanes.residues) + limit, 0)
            var to = lanes.residues.unsafe_ptr().unsafe_offset(slot * limit + _LANES * batch)
            to.unsafe_store[width=_LANES](v.cast[DType.uint32]())
            var s = matrix.starts.unsafe_get(q)
            var n = matrix.starts.unsafe_get(q + 1) - s
            budget.charge(UInt64(_LANES * n))
            var factor = v.eq(0).select(_Lanes(0), primes.primes - v)
            lanes.add(matrix.entries.unsafe_ptr().unsafe_offset(s), values[matrix.sources.unsafe_get(q)].unsafe_ptr(), n, factor, primes.squares, 1)
        c = lanes.next_marked(c + 1)
    return True


def _modular_pair[W: Int](mut lanes: _LaneRow, matrix: _Matrix[W], pivot: List[Int], coefficients: _Coefficients, mut images: _PairPrimes, a: Int, first: Int, allowance: Int, mut cost: Int, mut counts: List[Int], mut budget: Budget) raises PolyError -> Int:
    """The number of primes that proved the S-polynomial of rows a and a + 1 reduces to zero, or 0 if they did not.

    Modulo each prime p the reduction gives S = sum r_c R_c, R_c the row
    leading in column c. A denominator D and integers n_c = D r_c modulo the
    product Q of the primes are found by rational reconstruction; when Q
    exceeds twice a bound on the coefficients of D S - sum n_c R_c, that
    difference, zero modulo Q, is zero, so S has the standard representation
    sum (n_c / D) R_c. Nothing else is assumed, so a wrong reconstruction can
    only fail.

    Primes come in batches of `_LANES`, the first alone and later ones two
    at a time; an attempt follows each batch from `first` primes on. Gives
    up after `images.limit` primes, or, when `allowance` is positive, after
    the attempt that brings its cost past it. Its cost, by `_modular_cost`,
    is added to `cost`; every decision follows that count, so a route never
    depends on timing.
    """
    var b = a + 1
    var ga = matrix.sources[a]
    var gb = matrix.sources[b]
    var la: Integer
    var lb: Integer
    var multiple: Integer
    try:
        var common = integer_gcd(coefficients.leads[ga], coefficients.leads[gb])
        la = div_rem_trunc(coefficients.leads[gb], common)[0].copy()
        lb = div_rem_trunc(coefficients.leads[ga], common)[0].copy()
        multiple = la * coefficients.leads[ga]
    except e:
        raise PolyError(PolyErrorKind.CAPACITY, String(e))
    # S = la R_a - lb R_b bounds its coefficients by 2^s.
    var s_bits = max(coefficients.bits[ga] + la.magnitude_bit_length(), coefficients.bits[gb] + lb.magnitude_bit_length()) + 1
    var limit = images.limit
    var batch = 0
    var proved = 0
    var own = 0
    while _LANES * batch < limit:
        # The first batch alone, which often suffices; later ones two at a time.
        var two = batch > 0 and _LANES * (batch + 2) <= limit
        images.ensure(batch + 1 if two else batch, coefficients, budget)
        var t0 = _clock()
        var units = budget.remaining()
        var passed: Bool
        if two:
            passed = _lane_pass_two(lanes, matrix, pivot, images.values[batch], images.values[batch + 1], images.batches[batch], images.batches[batch + 1], a, batch, limit, budget)
        else:
            passed = _lane_pass(lanes, matrix, pivot, images.values[batch], images.batches[batch], a, batch, limit, budget)
        counts[0] += _clock() - t0
        own += _modular_cost(Int(units - budget.remaining()), 0, 0)
        if not passed:
            cost += own
            return 0
        for _ in range(2 if two else 1):
            batch += 1
            var k = _LANES * batch
            if k < first:
                continue
            var attempt = batch - 1
            images.basis(attempt, budget)
            var t1 = _clock()
            var crt = budget.remaining()
            var proves = _proves(lanes, matrix, pivot, coefficients, images, attempt, multiple, s_bits, counts, budget)
            own += _modular_cost(0, Int(crt - budget.remaining()), len(lanes.columns))
            counts[1] += _clock() - t1
            counts[2] += 1
            if proves:
                proved = k
                break
        if proved > 0 or (allowance > 0 and own > allowance):
            break
    lanes.clear(_LANES)
    cost += own
    return proved


def _proves[W: Int](lanes: _LaneRow, matrix: _Matrix[W], pivot: List[Int], coefficients: _Coefficients, images: _PairPrimes, attempt: Int, multiple: Integer, s_bits: Int, mut counts: List[Int], mut budget: Budget) raises PolyError -> Bool:
    """Whether the recorded residues modulo the attempt's primes prove the standard representation (see `_modular_pair`)."""
    ref basis = images.bases[attempt]
    var k = len(basis.weights)
    var limit = images.limit
    var nslots = len(lanes.columns)
    # r_c = L v_c / lc(g_c) modulo p, with D folded in: D r_c.
    var scaled = List[UInt64](length=k, fill=0)
    # L D modulo each prime, `_LANES` at a time.
    var factors = List[UInt64](length=k, fill=0)
    var multiple_limbs = _limbs_of(multiple)
    for i in range(k):
        var p = images.primes[i]
        var x = _remainder_of(multiple_limbs.unsafe_ptr(), len(multiple_limbs), p)
        factors[i] = p - x if multiple.sign() < 0 and x != 0 else x
    var work = List[UInt64](length=basis.limbs + 2, fill=0)
    var other = List[UInt64](length=basis.limbs + 2, fill=0)
    var half = (basis.bits - 2) // 2
    var d = Integer(1)
    var d_bits = 1
    var worst = d_bits + s_bits
    var log = 0
    while (1 << log) < nslots + 1:
        log += 1
    # Later columns first: their denominators tend to contain the earlier ones'.
    for slot in range(nslots - 1, -1, -1):
        var g = matrix.sources[pivot[lanes.columns[slot]]]
        var from_ = lanes.residues.unsafe_ptr().unsafe_offset(slot * limit)
        for batch in range(k // _LANES):
            ref primes = images.batches[batch]
            var v = from_.unsafe_offset(_LANES * batch).unsafe_load[width=_LANES]().cast[DType.uint64]()
            var inverse = images.inverses[batch].unsafe_ptr().unsafe_offset(_LANES * g).unsafe_load[width=_LANES]()
            var x = _mod_lanes(v * factors.unsafe_ptr().unsafe_offset(_LANES * batch).unsafe_load[width=_LANES](), primes)
            scaled.unsafe_ptr().unsafe_offset(_LANES * batch).unsafe_store[width=_LANES](_mod_lanes(x * inverse, primes))
        basis.value(scaled, work, budget)
        counts[4] += 1
        # The symmetric representative: x or x - Q, whichever is smaller.
        for l in range(basis.limbs + 2):
            other[l] = basis.product[l] if l < basis.limbs else UInt64(0)
        _ = _subtract_limbs(other.unsafe_ptr(), basis.limbs + 2, work.unsafe_ptr(), basis.limbs + 2)
        var size = min(_bits(work), _bits(other))
        var n_bits: Int
        if max(worst, size + coefficients.bits[g]) + log + 1 < basis.bits - 1:
            # Small enough for the bound as it is: n_c is this value.
            n_bits = size
        else:
            # A new denominator: a / b = x modulo Q with |a|, b below 2^half.
            counts[3] += 1
            var t0 = _clock()
            budget.charge(UInt64(_product(basis.limbs, basis.limbs)))
            var found = _fraction(_limbs_to_integer(work, basis.limbs), basis.modulus, half)
            counts[5] += _clock() - t0
            if not found:
                return False
            var b = found.value()[1].copy()
            n_bits = found.value()[0].magnitude_bit_length()
            d = _times(d, b)
            d_bits = d.magnitude_bit_length()
            var b_limbs = _limbs_of(b)
            for i in range(k):
                var p = images.primes[i]
                factors[i] = factors[i] * _remainder_of(b_limbs.unsafe_ptr(), len(b_limbs), p) % p
            # Earlier n_c grow by the new factor; account for it in the bound now.
            worst += b.magnitude_bit_length()
        # n_c times D / D_now, which is below 2^(bits D - bits D_now + 1) at the end:
        # counted here by charging the later growth to `worst` as it happens.
        worst = max(worst, n_bits + coefficients.bits[g])
        if worst + log + 1 >= basis.bits - 1:
            return False
    worst = max(worst, d_bits + s_bits)
    # |D S - sum n_c R_c| <= (nslots + 1) 2^worst, and must stay below Q / 2.
    return worst + log + 1 < basis.bits - 1


def _times(x: Integer, y: Integer) raises PolyError -> Integer:
    try:
        return x * y
    except e:
        raise PolyError(PolyErrorKind.CAPACITY, String(e))


def _fraction(x: Integer, modulus: Integer, bits: Int) raises PolyError -> Optional[Tuple[Integer, Integer]]:
    """A fraction a / b = x modulo `modulus` with |a| and 0 < b below 2^bits, if the Euclidean remainders give one."""
    try:
        return _euclid(x, modulus, bits)
    except e:
        raise PolyError(PolyErrorKind.CAPACITY, String(e))


def _euclid(x: Integer, modulus: Integer, bits: Int) raises -> Optional[Tuple[Integer, Integer]]:
    """As `_fraction`, with Lehmer steps while the remainders are long (as `_reconstruct` in `_rational_groebner`)."""
    var bound = Integer(1) << Integer(bits)
    var r0 = modulus.copy()
    var r1 = x.copy()
    var t0 = Integer(0)
    var t1 = Integer(1)
    var stop = bits + 128
    while r1 >= bound:
        if r1.magnitude_bit_length() > stop:
            # The quotients of the leading 62 bits, while they are certainly
            # the true ones, as one matrix; a batch shortens r1 by less than
            # 128 bits, so every remainder it skips stays above the bound.
            var shift = Integer(r0.magnitude_bit_length() - 62)
            var u = Int(r0 >> shift)
            var w = Int(r1 >> shift)
            var a = 1
            var b = 0
            var c = 0
            var d = 1
            while w + c != 0 and w + d != 0:
                var q = (u + a) // (w + c)
                if q != (u + b) // (w + d):
                    break
                var t = a - q * c
                a = c
                c = t
                t = b - q * d
                b = d
                d = t
                t = u - q * w
                u = w
                w = t
            if b != 0:
                var next_r0 = r0 * Integer(a) + r1 * Integer(b)
                r1 = r0 * Integer(c) + r1 * Integer(d)
                r0 = next_r0^
                var next_t0 = t0 * Integer(a) + t1 * Integer(b)
                t1 = t0 * Integer(c) + t1 * Integer(d)
                t0 = next_t0^
                continue
        var qr = div_rem_trunc(r0, r1)
        var t2 = t0 - qr[0] * t1
        r0 = r1^
        r1 = qr[1].copy()
        t0 = t1^
        t1 = t2^
    if t1.sign() == 0 or t1.magnitude_bit_length() > bits:
        return None
    if t1.sign() < 0:
        return (Integer(0) - r1, Integer(0) - t1)
    return (r1^, t1^)
