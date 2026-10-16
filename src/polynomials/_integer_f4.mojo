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
from apn_mojo import Integer, div_rem_trunc, gcd as integer_gcd
from .coefficients import ZZ
from .errors import Budget, PolyError, PolyErrorKind, _allocation, _product
from ._f4 import _Matrix, _Store
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
    """A dense row of two's complement integers in 64-bit limbs, `width` limbs per entry.

    `sizes` bounds the bit length of each entry's magnitude, and is zero for
    a zero entry; `bound` bounds them all. An entry of size s lives in its
    low s / 64 + 1 limbs, the ones its sign needs, and the limbs above are
    stale, so updates, scans and clearing touch only those. An entry holds
    64 * width - 1 bits besides its sign, so no update overflows while the
    bound fits. A sum can be a bit longer than its terms, so the bounds
    drift upward; when the bound outgrows the width, the entries are
    measured before the row is widened.
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
        """Expect entries of about `bits` bits; the row becomes zero."""
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

    @always_inline
    def _limbs(self, c: Int) -> Int:
        """The limbs entry c lives in, none when it is zero."""
        var size = self.sizes.unsafe_get(c)
        return size // 64 + 1 if size > 0 else 0

    def _entry_bits(self, c: Int) -> Int:
        var u = self._limbs(c)
        if u == 0:
            return 0
        var base = c * self.width
        var negative = (self.data.unsafe_get(base + u - 1) >> 63) != 0
        for l in range(u - 1, -1, -1):
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
            for l in range(self._limbs(c)):
                data.unsafe_get(c * width + l) = self.data.unsafe_get(old + l)
        self.data = data^
        self.width = width
        self.scratch = List[UInt64](length=2 * width + 2, fill=0)

    def is_zero(self, c: Int) -> Bool:
        var base = c * self.width
        for l in range(self._limbs(c)):
            if self.data.unsafe_get(base + l) != 0:
                return False
        return True

    def value(self, c: Int) -> Integer:
        """Entry c as an Integer."""
        var base = c * self.width
        var negative = self.negative(c)
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
        var u = self._limbs(c)
        return u > 0 and (self.data.unsafe_get(c * self.width + u - 1) >> 63) != 0

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

    @always_inline
    def _grow(mut self, c: Int, bits: Int) -> Int:
        """Make entry c room for a sum with a term of `bits` bits; return its limbs.

        The limbs it gains take its sign.
        """
        var u = self._limbs(c)
        var size = max(self.sizes.unsafe_get(c), bits) + 1
        var v = size // 64 + 1
        if v > u:
            var base = c * self.width
            var fill = UInt64.MAX if u > 0 and (self.data.unsafe_get(base + u - 1) >> 63) != 0 else UInt64(0)
            for l in range(u, v):
                self.data.unsafe_get(base + l) = fill
        self.sizes.unsafe_get(c) = size
        self.bound = max(self.bound, size)
        self.marks.unsafe_get(c // 64) |= UInt64(1) << UInt64(c % 64)
        return v

    @always_inline
    def _claim(mut self, c: Int, bits: Int, mut valid: Int, mut fill: UInt64) -> Int:
        """`_grow` without the filling: return the entry's new limbs, set valid
        to its old ones and fill to the sign word the limbs above them take."""
        var u = self._limbs(c)
        var size = max(self.sizes.unsafe_get(c), bits) + 1
        var top = self.data.unsafe_get(c * self.width + max(u - 1, 0))
        # No branch on whether the entry was zero: its stale top limb is masked.
        fill = (UInt64(0) - (top >> 63)) & (UInt64(0) - UInt64(Int(u > 0)))
        valid = u
        self.sizes.unsafe_get(c) = size
        self.bound = max(self.bound, size)
        self.marks.unsafe_get(c // 64) |= UInt64(1) << UInt64(c % 64)
        return size // 64 + 1

    def add_product(mut self, c: Int, factor: List[UInt64], terms: List[UInt64], start: Int, end: Int, bits: Int):
        """Add factor times the magnitude terms[start:end], of at most `bits` bits, to entry c."""
        var u = self._grow(c, bits)
        var data = self.data.unsafe_ptr().unsafe_offset(c * self.width)
        _accumulate[False](data, u, factor.unsafe_ptr(), len(factor), terms.unsafe_ptr().unsafe_offset(start), end - start)

    def subtract_product(mut self, c: Int, factor: List[UInt64], terms: List[UInt64], start: Int, end: Int, bits: Int):
        """Subtract factor times the magnitude terms[start:end], of at most `bits` bits, from entry c."""
        var u = self._grow(c, bits)
        var data = self.data.unsafe_ptr().unsafe_offset(c * self.width)
        _accumulate[True](data, u, factor.unsafe_ptr(), len(factor), terms.unsafe_ptr().unsafe_offset(start), end - start)

    @always_inline
    def word_product[subtract: Bool](mut self, c: Int, factor: Pointer[mut=False, UInt64, _], n: Int, term: UInt64, bits: Int):
        """Add, or subtract, the word term times the magnitude factor[0:n], of at most `bits` bits, to entry c."""
        var valid = 0
        var fill = UInt64(0)
        var v = self._claim(c, bits, valid, fill)
        var data = self.data.unsafe_ptr().unsafe_offset(c * self.width)
        comptime if subtract:
            _sub_mul_1[True, True](data, v, term, factor, n, valid, fill)
        else:
            _add_mul_1[True, True](data, v, term, factor, n, valid, fill)

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
        var u = self._grow(c, bits)
        var nf = len(self.factor_digits) - 2 * _PAD
        var room = nf + count + _PAD
        if len(self.low) < room:
            self.low.resize(room, 0)
            self.high.resize(room, 0)
        var data = self.data.unsafe_ptr().unsafe_offset(c * self.width)
        var f = self.factor_digits.unsafe_ptr().unsafe_offset(_PAD)
        var t = digits.unsafe_ptr().unsafe_offset(start)
        if nf <= count:
            _ifma[subtract](data, u, f, nf, t, count, self.low.unsafe_ptr(), self.high.unsafe_ptr())
        else:
            _ifma[subtract](data, u, t, count, f, nf, self.low.unsafe_ptr(), self.high.unsafe_ptr())

    def scale(mut self, first: Int, factor: List[UInt64], bits: Int):
        """Multiply every entry from column `first` on by the positive factor of `bits` bits; the bound must allow it."""
        self.bound += bits
        var digits = False
        comptime if _IFMA:
            if len(factor) >= _IFMA_MIN:
                self.set_factor_digits(factor)
                digits = True
        if len(factor) == 1 and not digits:
            self._scale_word(first, factor[0], bits)
            return
        var scratch = self.scratch.unsafe_ptr()
        var c = self.next_marked(first)
        while c < self.ncols:
            var next = self.next_marked(c + 1)
            if self.is_zero(c):
                c = next
                continue
            # The low u limbs hold the entry X - sign B^u, and the product
            # X s - sign s B^u fits in n limbs, which cover the entry's
            # limbs at its new size.
            var u = self._limbs(c)
            var n = min(u + len(factor), self.width)
            var negative = self.negative(c)
            self.sizes.unsafe_get(c) += bits
            var entry = self.data.unsafe_ptr().unsafe_offset(c * self.width)
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
            c = next


    def _scale_word(mut self, first: Int, f: UInt64, bits: Int):
        """`scale` by the word factor f, in place: the entry, sign-extended by a limb, times f."""
        var c = self.next_marked(first)
        while c < self.ncols:
            var next = self.next_marked(c + 1)
            if self.is_zero(c):
                c = next
                continue
            var u = self._limbs(c)
            var negative = self.negative(c)
            self.sizes.unsafe_get(c) += bits
            var entry = self.data.unsafe_ptr().unsafe_offset(c * self.width)
            var carry = UInt64(0)
            for l in range(u):
                var p = UInt128(f) * UInt128(entry.unsafe_offset(l).unsafe_load()) + UInt128(carry)
                entry.unsafe_offset(l).unsafe_store(UInt64(p & UInt128(UInt64.MAX)))
                carry = UInt64(p >> 64)
            if u < self.width:
                # The sign limb B - 1 times f, plus the carry, is f B + carry - f.
                entry.unsafe_offset(u).unsafe_store(carry - (f if negative else UInt64(0)))
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
            _sub_mul_2[True](data.unsafe_offset(i), width - i, a.unsafe_offset(i).unsafe_load(), a.unsafe_offset(i + 1).unsafe_load(), b, nb)
        else:
            _add_mul_2[True](data.unsafe_offset(i), width - i, a.unsafe_offset(i).unsafe_load(), a.unsafe_offset(i + 1).unsafe_load(), b, nb)
        i += 2
    if i < na and i < width:
        comptime if subtract:
            _sub_mul_1[True](data.unsafe_offset(i), width - i, a.unsafe_offset(i).unsafe_load(), b, nb)
        else:
            _add_mul_1[True](data.unsafe_offset(i), width - i, a.unsafe_offset(i).unsafe_load(), b, nb)


@always_inline
def _add_mul_1[whole: Bool = False, extend: Bool = False](data: Pointer[mut=True, UInt64, _], width: Int, f: UInt64, other: Pointer[mut=False, UInt64, _], n: Int, valid: Int = 0, fill: UInt64 = 0):
    """data += f * other[0:n] over `width` limbs of two's complement, in one carry chain.

    With `extend`, only data[0:valid] holds the value, and the limbs above
    read as fill, its sign extension; `whole` must be set too.
    """
    var g = UInt128(f)
    var carry = UInt64(0)
    var m = min(n, width)
    var l = 0
    while l < m:
        var p = g * UInt128(other.unsafe_offset(l).unsafe_load())
        var low = UInt64(p & UInt128(UInt64.MAX))
        var high = UInt64(p >> 64)
        var e = data.unsafe_offset(l).unsafe_load()
        comptime if extend:
            e = fill if l >= valid else e
        low += e
        high += UInt64(1) if low < e else UInt64(0)
        low += carry
        high += UInt64(1) if low < carry else UInt64(0)
        data.unsafe_offset(l).unsafe_store(low)
        carry = high
        l += 1
    _carry_word[whole, extend](data, width, l, carry, valid, fill)


@always_inline
def _sub_mul_1[whole: Bool = False, extend: Bool = False](data: Pointer[mut=True, UInt64, _], width: Int, f: UInt64, other: Pointer[mut=False, UInt64, _], n: Int, valid: Int = 0, fill: UInt64 = 0):
    """data -= f * other[0:n] over `width` limbs of two's complement, in one borrow chain; `extend` as for `_add_mul_1`."""
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
        comptime if extend:
            e = fill if l >= valid else e
        data.unsafe_offset(l).unsafe_store(e - low)
        borrow = high + (UInt64(1) if e < low else UInt64(0))
        l += 1
    _borrow_word[whole, extend](data, width, l, borrow, valid, fill)


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
def _carry_word[whole: Bool = False, extend: Bool = False](data: Pointer[mut=True, UInt64, _], width: Int, start: Int, var carry: UInt64, valid: Int = 0, fill: UInt64 = 0):
    """Add the word carry to data[start:width], two's complement.

    With `whole`, the carry goes through every limb even once it is zero, in
    a loop whose length does not depend on the data.
    """
    var l = start
    while (whole or carry != 0) and l < width:
        var e = data.unsafe_offset(l).unsafe_load()
        comptime if extend:
            e = fill if l >= valid else e
        var x = e + carry
        data.unsafe_offset(l).unsafe_store(x)
        carry = UInt64(1) if x < carry else UInt64(0)
        l += 1


@always_inline
def _borrow_word[whole: Bool = False, extend: Bool = False](data: Pointer[mut=True, UInt64, _], width: Int, start: Int, var borrow: UInt64, valid: Int = 0, fill: UInt64 = 0):
    """Subtract the word borrow from data[start:width], two's complement; `whole` as for `_carry_word`."""
    var l = start
    while (whole or borrow != 0) and l < width:
        var e = data.unsafe_offset(l).unsafe_load()
        comptime if extend:
            e = fill if l >= valid else e
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
    engine.sort_active(budget)
    var store = _Store[W]()
    store.extend(engine, budget)
    var coefficients = _Coefficients(engine, budget)
    var quotient = List[UInt64]()
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
            if not _reduces(row, matrix, pivot, coefficients, a, quotient, budget):
                return False
    return True


def _reduces[W: Int](mut row: _Row, matrix: _Matrix[W], pivot: List[Int], coefficients: _Coefficients, a: Int, mut quotient: List[UInt64], mut budget: Budget) raises PolyError -> Bool:
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
    var c = row.next_marked(first + 1)
    while c < row.ncols:
        budget.charge(UInt64(row.width))
        if row.is_zero(c):
            row.unmark(c)
        else:
            var q = pivot[c]
            if q < 0:
                return False
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
    """Add, or subtract when `minus`, factor times the word terms by_sign[begin:end] of the matrix row starting at s.

    As `_Row.word_product` for each term, with the row's fields held in
    registers across the terms.
    """
    var f = factor.unsafe_ptr()
    var nf = len(factor)
    var data = row.data.unsafe_ptr()
    var width = row.width
    var sizes = row.sizes.unsafe_ptr()
    var marks = row.marks.unsafe_ptr()
    var entries = matrix.entries.unsafe_ptr().unsafe_offset(s)
    var order = by_sign.unsafe_ptr()
    var terms = limbs.unsafe_ptr()
    var bound = row.bound
    for i in range(begin, end):
        var k = order.unsafe_offset(i).unsafe_load()
        var c = Int(entries.unsafe_offset(k).unsafe_load())
        var old = sizes.unsafe_offset(c).unsafe_load()
        var size = max(old, bits) + 1
        var valid = (old // 64 + 1) * Int(old > 0)
        var entry = data.unsafe_offset(c * width)
        # The sign of the entry, with no branch on whether it was zero.
        var top = entry.unsafe_offset(max(valid - 1, 0)).unsafe_load()
        var fill = (UInt64(0) - (top >> 63)) & (UInt64(0) - UInt64(Int(valid > 0)))
        sizes.unsafe_offset(c).unsafe_store(size)
        bound = max(bound, size)
        marks.unsafe_offset(c >> 6).unsafe_store(marks.unsafe_offset(c >> 6).unsafe_load() | (UInt64(1) << UInt64(c & 63)))
        comptime if minus:
            _sub_mul_1[True, True](entry, size // 64 + 1, terms.unsafe_offset(k).unsafe_load(), f, nf, valid, fill)
        else:
            _add_mul_1[True, True](entry, size // 64 + 1, terms.unsafe_offset(k).unsafe_load(), f, nf, valid, fill)
    row.bound = bound


def _long_terms[W: Int, minus: Bool](mut row: _Row, matrix: _Matrix[W], coefficients: _Coefficients, g: Int, s: Int, begin: Int, end: Int, factor: List[UInt64], digits: Bool, bits: Int):
    """Add, or subtract when `minus`, factor times the terms by_sign[begin:end] of element g's matrix row starting at s.

    As `_Row.add_product` and `subtract_product` for each term, with the
    row's fields held in registers across the terms.
    """
    comptime if _IFMA:
        if digits:
            _digit_terms[minus](row, matrix, coefficients, g, s, begin, end, factor, bits)
            return
    var f = factor.unsafe_ptr()
    var nf = len(factor)
    var data = row.data.unsafe_ptr()
    var width = row.width
    var sizes = row.sizes.unsafe_ptr()
    var marks = row.marks.unsafe_ptr()
    var entries = matrix.entries.unsafe_ptr().unsafe_offset(s)
    var order = coefficients.by_sign[g].unsafe_ptr()
    var limbs = coefficients.limbs[g].unsafe_ptr()
    var starts = coefficients.starts[g].unsafe_ptr()
    var bound = row.bound
    for i in range(begin, end):
        var k = order.unsafe_offset(i).unsafe_load()
        var c = Int(entries.unsafe_offset(k).unsafe_load())
        var old = sizes.unsafe_offset(c).unsafe_load()
        var size = max(old, bits) + 1
        var u = (old // 64 + 1) * Int(old > 0)
        var v = size // 64 + 1
        var entry = data.unsafe_offset(c * width)
        if v > u:
            var fill = UInt64.MAX if u > 0 and (entry.unsafe_offset(u - 1).unsafe_load() >> 63) != 0 else UInt64(0)
            for l in range(u, v):
                entry.unsafe_offset(l).unsafe_store(fill)
        sizes.unsafe_offset(c).unsafe_store(size)
        bound = max(bound, size)
        marks.unsafe_offset(c >> 6).unsafe_store(marks.unsafe_offset(c >> 6).unsafe_load() | (UInt64(1) << UInt64(c & 63)))
        var start = starts.unsafe_offset(k).unsafe_load()
        var count = starts.unsafe_offset(k + 1).unsafe_load() - start
        _accumulate[minus](entry, v, f, nf, limbs.unsafe_offset(start), count)
    row.bound = bound


def _digit_terms[W: Int, //, minus: Bool](mut row: _Row, matrix: _Matrix[W], coefficients: _Coefficients, g: Int, s: Int, begin: Int, end: Int, factor: List[UInt64], bits: Int):
    """`_long_terms` with IFMA: terms of at least `_IFMA_MIN` limbs go through digit strings."""
    ref limbs = coefficients.limbs[g]
    ref starts = coefficients.starts[g]
    ref by_sign = coefficients.by_sign[g]
    for i in range(begin, end):
        var k = by_sign.unsafe_get(i)
        var c = Int(matrix.entries.unsafe_get(s + k))
        if starts.unsafe_get(k + 1) - starts.unsafe_get(k) >= _IFMA_MIN:
            row.digit_product[minus](c, coefficients.digits[g], coefficients.digit_starts[g].unsafe_get(k), coefficients.digit_counts[g].unsafe_get(k), bits)
            continue
        comptime if minus:
            row.subtract_product(c, factor, limbs, starts.unsafe_get(k), starts.unsafe_get(k + 1), bits)
        else:
            row.add_product(c, factor, limbs, starts.unsafe_get(k), starts.unsafe_get(k + 1), bits)
