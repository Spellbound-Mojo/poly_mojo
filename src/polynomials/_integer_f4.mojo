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
52-bit digits and AVX-512 IFMA where the target has it, and otherwise,
where it has ADX, through rows of mulx, adcx and adox.
"""
from std.bit import count_leading_zeros, count_trailing_zeros
from std.collections import Dict
from std.math import max, min
from std.sys import CompilationTarget, llvm_intrinsic
from std.sys._assembly import inlined_assembly
from std.time import perf_counter_ns
from apn_mojo import Integer, div_rem_trunc, gcd as integer_gcd
from .coefficients import Modulus, ZZ, _prime
from .errors import Budget, PolyError, PolyErrorKind, _allocation, _product
from ._f4 import _LANES, _Lanes, _Matrix, _Primes, _Store, _mod_lanes, _raw_hash
from ._packed_groebner import _Engine, _Packed, _Term, _div

comptime _SLACK = 16
"""Bits of growth a widened row leaves room for before it is measured again."""

comptime _COMBA = 24
"""Products whose factors are both at least this many limbs long go into an entry a column at a time."""

comptime _IFMA = CompilationTarget._has_feature["avx512ifma"]()
"""Whether the target multiplies 52-bit digits eight at a time (AVX-512 IFMA)."""

comptime _IFMA_MIN = 12
"""With IFMA, products whose factors are both at least this many limbs long go through 52-bit digits."""

comptime _ADX = CompilationTarget._has_feature["adx"]() and CompilationTarget._has_feature["bmi2"]()
"""Whether the target has mulx, adcx and adox, for multiply-add chains in two carry flags."""

comptime _ROWS = 4
"""With mulx, adcx and adox, products whose longer factor has at least this many limbs go a row at a time."""

comptime _PAD = 32
"""Zero digits on each side of a digit string, for the IFMA loads that run past its ends."""


def _magnitude(value: Integer, mut limbs: List[UInt64]):
    """Append the magnitude of value in 64-bit limbs, least significant first."""
    if value.magnitude_bit_length() <= 63:
        # Word values, the common case, without a byte string.
        try:
            var word = value.to_native_exact[DType.int64]()
            if word != 0:
                limbs.append(UInt64(word if word > 0 else -word))
            return
        except:
            pass
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
    var data = limbs.unsafe_ptr()
    var n = len(limbs)
    while n > 0 and data.unsafe_offset(n - 1).unsafe_load() == 0:
        n -= 1
    if n == 0:
        return 0
    return 64 * n - Int(count_leading_zeros(data.unsafe_offset(n - 1).unsafe_load()))


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
            # Limbs above an entry's size are never read, so need no zeros.
            self.data = List[UInt64](unsafe_uninit_length=self.ncols * width)
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
                # The measure of a negative entry can exceed its bound by a
                # bit, which could take in a limb above the ones it lives in.
                self.sizes.unsafe_get(c) = min(self.sizes.unsafe_get(c), self._entry_bits(c))
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
        var data = List[UInt64](unsafe_uninit_length=self.ncols * width)
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
        var bits = self._entry_bits(c)
        if bits == 0:
            # A zero entry's limbs are stale.
            return Integer(0)
        if bits <= 63:
            # The low limb, sign-extended, is the whole entry.
            return Integer(Int64(self.data.unsafe_get(base)))
        var used = (bits + 63) // 64
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
        var data = self.data.unsafe_ptr()
        var width = self.width
        var sizes = self.sizes.unsafe_ptr()
        var c = self.next_marked(first)
        while c < self.ncols:
            var next = self.next_marked(c + 1)
            var size = sizes.unsafe_offset(c).unsafe_load()
            var u = (size // 64 + 1) * Int(size > 0)
            var entry = data.unsafe_offset(c * width)
            var negative = u > 0 and (entry.unsafe_offset(u - 1).unsafe_load() >> 63) != 0
            var carry = UInt64(0)
            var any = UInt64(0)
            for l in range(u):
                var e = entry.unsafe_offset(l).unsafe_load()
                any |= e
                var p = UInt128(f) * UInt128(e) + UInt128(carry)
                entry.unsafe_offset(l).unsafe_store(UInt64(p & UInt128(UInt64.MAX)))
                carry = UInt64(p >> 64)
            if u < width:
                # The sign limb B - 1 times f, plus the carry, is f B + carry - f.
                entry.unsafe_offset(u).unsafe_store(carry - (f if negative else UInt64(0)))
            # A zero entry stays zero, and keeps its size.
            sizes.unsafe_offset(c).unsafe_store(size + bits * Int(any != 0))
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
    comptime if _ADX:
        if nb >= _ROWS:
            _rows[subtract](data, width, a, na, b, nb)
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
    comptime if _ADX:
        if m >= _ROWS:
            # In assembly, the value filled in first.
            l = m
            comptime if extend:
                for k in range(valid, l):
                    data.unsafe_offset(k).unsafe_store(fill)
            carry = _adx_add_mul(data, f, other, l)
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
    comptime if _ADX:
        if m >= _ROWS:
            l = m
            comptime if extend:
                for k in range(valid, l):
                    data.unsafe_offset(k).unsafe_store(fill)
            borrow = _adx_sub_mul(data, f, other, l)
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
def _adx_add_mul(data: Pointer[mut=True, UInt64, _], f: UInt64, other: Pointer[mut=False, UInt64, _], n: Int) -> UInt64:
    """data[0:n] += f * other[0:n] for n >= 1; return the carry out, below 2^64.

    The products' high words go in by adcx (the carry flag) and the data by
    adox (the overflow flag): two carry chains that do not wait on each other.
    The n mod 4 odd limbs go one at a time, the rest four at a time.
    """
    return inlined_assembly[
        """
        mov $1, %rdi
        mov $2, %rsi
        mov $3, %rcx
        mov $4, %rdx
        mov %rcx, %r11
        shr $$2, %r11
        and $$3, %rcx
        xor %r8d, %r8d
        jrcxz 3f
        1:
        mulx (%rsi), %r9, %r10
        adcx %r8, %r9
        adox (%rdi), %r9
        mov %r9, (%rdi)
        mov %r10, %r8
        lea 8(%rsi), %rsi
        lea 8(%rdi), %rdi
        lea -1(%rcx), %rcx
        jrcxz 3f
        jmp 1b
        3:
        mov %r11, %rcx
        jrcxz 4f
        2:
        mulx (%rsi), %r9, %r10
        adcx %r8, %r9
        adox (%rdi), %r9
        mov %r9, (%rdi)
        mulx 8(%rsi), %r9, %r8
        adcx %r10, %r9
        adox 8(%rdi), %r9
        mov %r9, 8(%rdi)
        mulx 16(%rsi), %r9, %r10
        adcx %r8, %r9
        adox 16(%rdi), %r9
        mov %r9, 16(%rdi)
        mulx 24(%rsi), %r9, %r8
        adcx %r10, %r9
        adox 24(%rdi), %r9
        mov %r9, 24(%rdi)
        lea 32(%rsi), %rsi
        lea 32(%rdi), %rdi
        lea -1(%rcx), %rcx
        jrcxz 4f
        jmp 2b
        4:
        mov $$0, %r9
        adcx %r9, %r8
        adox %r9, %r8
        mov %r8, $0
        """,
        UInt64,
        constraints="=&r,r,r,r,r,~{rdi},~{rsi},~{rcx},~{rdx},~{r8},~{r9},~{r10},~{r11},~{memory},~{cc}",
    ](data, other, n, f)

@always_inline
def _adx_sub_mul(data: Pointer[mut=True, UInt64, _], f: UInt64, other: Pointer[mut=False, UInt64, _], n: Int) -> UInt64:
    """data[0:n] -= f * other[0:n] for n >= 1; return the borrow out.

    As `_adx_add_mul`, adding the complement of the product with the
    overflow flag set first, so the overflow out is one minus the borrow.
    """
    return inlined_assembly[
        """
        mov $1, %rdi
        mov $2, %rsi
        mov $3, %rcx
        mov $4, %rdx
        mov %rcx, %r11
        shr $$2, %r11
        and $$3, %rcx
        mov $$0x7fffffffffffffff, %r8
        add $$1, %r8
        mov $$0, %r8
        jrcxz 3f
        1:
        mulx (%rsi), %r9, %r10
        adcx %r8, %r9
        not %r9
        adox (%rdi), %r9
        mov %r9, (%rdi)
        mov %r10, %r8
        lea 8(%rsi), %rsi
        lea 8(%rdi), %rdi
        lea -1(%rcx), %rcx
        jrcxz 3f
        jmp 1b
        3:
        mov %r11, %rcx
        jrcxz 4f
        2:
        mulx (%rsi), %r9, %r10
        adcx %r8, %r9
        not %r9
        adox (%rdi), %r9
        mov %r9, (%rdi)
        mulx 8(%rsi), %r9, %r8
        adcx %r10, %r9
        not %r9
        adox 8(%rdi), %r9
        mov %r9, 8(%rdi)
        mulx 16(%rsi), %r9, %r10
        adcx %r8, %r9
        not %r9
        adox 16(%rdi), %r9
        mov %r9, 16(%rdi)
        mulx 24(%rsi), %r9, %r8
        adcx %r10, %r9
        not %r9
        adox 24(%rdi), %r9
        mov %r9, 24(%rdi)
        lea 32(%rsi), %rsi
        lea 32(%rdi), %rdi
        lea -1(%rcx), %rcx
        jrcxz 4f
        jmp 2b
        4:
        mov $$0, %r9
        adcx %r9, %r8
        adox %r9, %r9
        lea 1(%r8), %r8
        sub %r9, %r8
        mov %r8, $0
        """,
        UInt64,
        constraints="=&r,r,r,r,r,~{rdi},~{rsi},~{rcx},~{rdx},~{r8},~{r9},~{r10},~{r11},~{memory},~{cc}",
    ](data, other, n, f)


@always_inline
def _mul_row[subtract: Bool](data: Pointer[mut=True, UInt64, _], f: UInt64, b: Pointer[mut=False, UInt64, _], n: Int) -> UInt64:
    """data[0:n] += f * b[0:n], or -= when `subtract`, for n >= 1; return the carry or borrow out, below 2^64."""
    comptime if subtract:
        return _adx_sub_mul(data, f, b, n)
    else:
        return _adx_add_mul(data, f, b, n)


def _rows[subtract: Bool](data: Pointer[mut=True, UInt64, _], width: Int, a: Pointer[mut=False, UInt64, _], na: Int, b: Pointer[mut=False, UInt64, _], nb: Int):
    """`_accumulate` with mulx, adcx and adox, a row per limb of a.

    Row i adds a[i] b at limb i and leaves its carry at limb i + nb, where a
    bit carried out of that limb waits for the next row's carry.
    """
    var pending = UInt64(0)
    var top = min(na + nb, width)
    for i in range(min(na, width)):
        var n = min(nb, width - i)
        var c = _mul_row[subtract](data.unsafe_offset(i), a.unsafe_offset(i).unsafe_load(), b, n)
        var at = i + n
        if at >= width:
            # The carry is past the width, as are the later rows' carries.
            pending = 0
            continue
        var e = data.unsafe_offset(at).unsafe_load()
        comptime if subtract:
            var t = c + pending
            var over = UInt64(1) if t < c else UInt64(0)
            data.unsafe_offset(at).unsafe_store(e - t)
            pending = over + (UInt64(1) if e < t else UInt64(0))
        else:
            var t = e + c
            var over = UInt64(1) if t < c else UInt64(0)
            var t2 = t + pending
            over += UInt64(1) if t2 < pending else UInt64(0)
            data.unsafe_offset(at).unsafe_store(t2)
            pending = over
    comptime if subtract:
        _borrow_word[True](data, width, top, pending)
    else:
        _carry_word[True](data, width, top, pending)


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


def _divide_limbs(u: Pointer[mut=True, UInt64, _], length: Int, d: Pointer[mut=False, UInt64, _], n: Int, q: Pointer[mut=True, UInt64, _]):
    """`_remainder_limbs`, also writing the length - n + 1 quotient limbs to q."""
    var top = UInt128(d.unsafe_offset(n - 1).unsafe_load())
    var second = UInt128(d.unsafe_offset(n - 2).unsafe_load()) if n >= 2 else UInt128(0)
    var j = length - n
    while j >= 0:
        var window = u.unsafe_offset(j)
        var numerator = (UInt128(window.unsafe_offset(n).unsafe_load()) << 64) | UInt128(window.unsafe_offset(n - 1).unsafe_load())
        var digit = numerator // top
        if digit > UInt128(UInt64.MAX):
            digit = UInt128(UInt64.MAX)
        var r = numerator - digit * top
        if n >= 2:
            while r <= UInt128(UInt64.MAX) and digit * second > ((r << 64) | UInt128(window.unsafe_offset(n - 2).unsafe_load())):
                digit -= 1
                r += top
        if digit != 0:
            _sub_mul_1(window, n + 1, UInt64(digit), d, n)
            if window.unsafe_offset(n).unsafe_load() != 0:
                _add_mul_1(window, n + 1, 1, d, n)
                digit -= 1
        q.unsafe_offset(j).unsafe_store(UInt64(digit))
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
        # Both halves of every pair, as rows. A half is fixed by its element
        # and its leading monomial, the pair's LCM, so equal halves share a row.
        var halves = List[Tuple[Int, Int]]()
        var seen = Dict[Int, Int]()
        var stride = len(engine.polys)
        while len(engine.pairs) and engine.pairs[0].lcm.degree == degree:
            var pair = engine.select(budget)
            matrix.columns.reserve(1, budget)
            var lead = Int(matrix.columns.find(pair.lcm, _raw_hash(pair.lcm)))
            var rows = List[Int](capacity=2)
            for source in [pair.first, pair.second]:
                var key = lead * stride + source
                var known = seen.get(key)
                if known:
                    rows.append(known.value())
                    continue
                seen[key] = len(matrix.sources)
                rows.append(len(matrix.sources))
                matrix.add_row(engine, store, source, _div(pair.lcm, engine.leads[source]), budget)
            halves.append((rows[0], rows[1]))
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
        for half in halves:
            var a = half[0]
            var b = half[1]
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
                k = _modular_pair(lanes, matrix, pivot, coefficients, images, a, b, max(_FIRST_PRIMES, hint - _LANES), allowance, cost, counts, budget)
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
            if not _reduces(row, matrix, pivot, coefficients, a, b, quotient, terms, budget):
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


def _reduces[W: Int](mut row: _Row, matrix: _Matrix[W], pivot: List[Int], coefficients: _Coefficients, a: Int, b: Int, mut quotient: List[UInt64], mut terms: Int, mut budget: Budget) raises PolyError -> Bool:
    """Whether the S-polynomial of matrix rows a and b, which lead in one column, reduces to zero.

    Adds the number of row terms it loads to `terms`, for `_exact_cost`.
    """
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
    terms += matrix.starts[a + 1] - matrix.starts[a] + matrix.starts[b + 1] - matrix.starts[b]
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
    x = sum r_i e_i - m Q with e_i = c_i Q_i and m = floor(sum r_i c_i / p_i).

    `values` forms `_LANES` values at once, one per SIMD lane, from the
    32-bit digits of the e_i: each digit's products with the residues stay
    below 2^63, and their low and high halves go into columns that carry
    once all of them are in."""
    var product: List[UInt64]
    var basis: List[UInt64]
    var digits: List[UInt64]
    """The e_i in 32-bit digits, 2 `limbs` each."""
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
        _allocation[UInt64](_product(2 * k, self.limbs), budget)
        self.digits = List[UInt64](capacity=2 * k * self.limbs)
        for limb in self.basis:
            self.digits.append(limb & 0xFFFFFFFF)
            self.digits.append(limb >> 32)
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


    def values(self, residues: List[UInt64], mut work: List[UInt64], mut sums: List[UInt64]):
        """`value` for `_LANES` residue vectors at once, uncharged: residues[i _LANES + j] is the j-th's residue modulo the i-th prime, and its value goes to work[j (limbs + 2) :], limbs + 2 limbs. `sums` is scratch of `_LANES` (2 limbs + 2)."""
        var k = len(self.weights)
        var digits = 2 * self.limbs
        var columns = sums.unsafe_ptr()
        var mask = _Lanes(0xFFFFFFFF)
        for d in range(digits + 2):
            columns.unsafe_offset(_LANES * d).unsafe_store[width=_LANES](_Lanes(0))
        var estimate = SIMD[DType.float64, _LANES](0)
        for i in range(k):
            var r = residues.unsafe_ptr().unsafe_offset(_LANES * i).unsafe_load[width=_LANES]()
            estimate += r.cast[DType.float64]() * self.weights.unsafe_get(i)
            var e = self.digits.unsafe_ptr().unsafe_offset(i * digits)
            var high = _Lanes(0)
            for d in range(digits):
                # Both factors are below 2^32, which the masks make plain.
                var x = (r & mask) * (_Lanes(e.unsafe_offset(d).unsafe_load()) & mask)
                var column = columns.unsafe_offset(_LANES * d)
                column.unsafe_store[width=_LANES](column.unsafe_load[width=_LANES]() + (x & mask) + high)
                high = x >> 32
            var column = columns.unsafe_offset(_LANES * digits)
            column.unsafe_store[width=_LANES](column.unsafe_load[width=_LANES]() + high)
        var carry = _Lanes(0)
        for d in range(digits + 2):
            var x = columns.unsafe_offset(_LANES * d).unsafe_load[width=_LANES]() + carry
            columns.unsafe_offset(_LANES * d).unsafe_store[width=_LANES](x & mask)
            carry = x >> 32
        var n = self.limbs + 2
        for lane in range(_LANES):
            var data = work.unsafe_ptr().unsafe_offset(lane * n)
            for l in range(self.limbs + 1):
                var low = columns.unsafe_offset(_LANES * 2 * l + lane).unsafe_load()
                var high = columns.unsafe_offset(_LANES * (2 * l + 1) + lane).unsafe_load()
                data.unsafe_offset(l).unsafe_store(low | (high << 32))
            data.unsafe_offset(self.limbs + 1).unsafe_store(0)
            var m = UInt64(estimate[lane])
            if m:
                _sub_mul_1(data, n, m, self.product.unsafe_ptr(), self.limbs)
            while (data.unsafe_offset(n - 1).unsafe_load() >> 63) != 0:
                _add_mul_1(data, n, 1, self.product.unsafe_ptr(), self.limbs)
            while not self._below(data):
                _sub_mul_1(data, n, 1, self.product.unsafe_ptr(), self.limbs)

    def _below(self, data: Pointer[mut=False, UInt64, _]) -> Bool:
        """Whether the nonnegative limbs + 2 limbs at data are below Q."""
        if data.unsafe_offset(self.limbs).unsafe_load() != 0 or data.unsafe_offset(self.limbs + 1).unsafe_load() != 0:
            return False
        for l in range(self.limbs - 1, -1, -1):
            var x = data.unsafe_offset(l).unsafe_load()
            var y = self.product.unsafe_get(l)
            if x != y:
                return x < y
        return False


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

    def add(mut self, columns: Pointer[mut=False, Int32, _], values: Pointer[mut=False, UInt32, _], n: Int, factor: SIMD[DType.uint32, _LANES], squares: _Lanes, skip: Int):
        """Add factor times a row of residues, after its first `skip` entries; entries stay below p^2."""
        _lanes_add[_LANES, True](self.data.unsafe_ptr(), self.marks.unsafe_ptr(), columns, values, n, factor, squares, skip)


@no_inline
def _lanes_add[S: Int, reduce: Bool](data: Pointer[mut=True, UInt64, _], marks: Pointer[mut=True, UInt64, _], columns: Pointer[mut=False, Int32, _], values: Pointer[mut=False, UInt32, _], n: Int, factors: SIMD[DType.uint32, _LANES], squares: _Lanes, skip: Int):
    """Add factors times a row of residues, after its first `skip` entries, to every lane of a dense row whose columns are S apart, and mark the columns.

    With `reduce` each entry is brought below p^2 again. Both factors widen
    from 32 bits, so each product is one 32 by 32 bit multiplication; this
    stays out of line, since inlined the widening is lost before instructions
    are selected.
    """
    var factor = factors.cast[DType.uint64]()
    for k in range(skip, n):
        var c = Int(columns.unsafe_offset(k).unsafe_load())
        var at = data.unsafe_offset(S * c)
        var x = at.unsafe_load[width=_LANES]() + factor * values.unsafe_offset(_LANES * k).unsafe_load[width=_LANES]().cast[DType.uint64]()
        comptime if reduce:
            at.unsafe_store[width=_LANES](x.ge(squares).select(x - squares, x))
        else:
            at.unsafe_store[width=_LANES](x)
        var mw = marks.unsafe_offset(c >> 6)
        mw.unsafe_store(mw.unsafe_load() | (UInt64(1) << UInt64(c & 63)))


@no_inline
def _lanes_add_two[reduce: Bool](data: Pointer[mut=True, UInt64, _], marks: Pointer[mut=True, UInt64, _], columns: Pointer[mut=False, Int32, _], values: Pointer[mut=False, UInt32, _], others: Pointer[mut=False, UInt32, _], n: Int, factors: SIMD[DType.uint32, _LANES], more: SIMD[DType.uint32, _LANES], squares: _Lanes, more_squares: _Lanes, skip: Int):
    """As `_lanes_add` for two batches, `_LANES` apart in each column."""
    comptime S = 2 * _LANES
    var f0 = factors.cast[DType.uint64]()
    var f1 = more.cast[DType.uint64]()
    for k in range(skip, n):
        var c = Int(columns.unsafe_offset(k).unsafe_load())
        var at = data.unsafe_offset(S * c)
        var x = at.unsafe_load[width=_LANES]() + f0 * values.unsafe_offset(_LANES * k).unsafe_load[width=_LANES]().cast[DType.uint64]()
        var at1 = at.unsafe_offset(_LANES)
        var y = at1.unsafe_load[width=_LANES]() + f1 * others.unsafe_offset(_LANES * k).unsafe_load[width=_LANES]().cast[DType.uint64]()
        comptime if reduce:
            at.unsafe_store[width=_LANES](x.ge(squares).select(x - squares, x))
            at1.unsafe_store[width=_LANES](y.ge(more_squares).select(y - more_squares, y))
        else:
            at.unsafe_store[width=_LANES](x)
            at1.unsafe_store[width=_LANES](y)
        var mw = marks.unsafe_offset(c >> 6)
        mw.unsafe_store(mw.unsafe_load() | (UInt64(1) << UInt64(c & 63)))


def _lane_pass_two[W: Int](mut lanes: _LaneRow, matrix: _Matrix[W], pivot: List[Int], values: List[List[UInt32]], others: List[List[UInt32]], primes: _Primes, more: _Primes, a: Int, b: Int, batch: Int, limit: Int, mut budget: Budget) raises PolyError -> Bool:
    """As `_lane_pass` for batches `batch` and `batch` + 1 in one sweep, two `_LANES` apart in each column."""
    comptime S = 2 * _LANES
    var data = lanes.data.unsafe_ptr()
    var marks = lanes.marks.unsafe_ptr()
    var first = Int(matrix.entries[matrix.starts[a]])
    for half in range(2):
        var r = a if half == 0 else b
        var s = matrix.starts[r]
        var n = matrix.starts[r + 1] - s
        var columns = matrix.entries.unsafe_ptr().unsafe_offset(s)
        var f0 = SIMD[DType.uint32, _LANES](1) if half == 0 else (primes.primes - 1).cast[DType.uint32]()
        var f1 = SIMD[DType.uint32, _LANES](1) if half == 0 else (more.primes - 1).cast[DType.uint32]()
        _lanes_add_two[False](data, marks, columns, values[matrix.sources[r]].unsafe_ptr(), others[matrix.sources[r]].unsafe_ptr(), n, f0, f1, primes.squares, more.squares, 0)
    budget.charge(UInt64(S * (matrix.starts[a + 1] - matrix.starts[a] + matrix.starts[b + 1] - matrix.starts[b])))
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
            var f0 = u.eq(0).select(_Lanes(0), primes.primes - u).cast[DType.uint32]()
            var f1 = w.eq(0).select(_Lanes(0), more.primes - w).cast[DType.uint32]()
            var g = matrix.sources.unsafe_get(q)
            _lanes_add_two[True](data, marks, matrix.entries.unsafe_ptr().unsafe_offset(s), values[g].unsafe_ptr(), others[g].unsafe_ptr(), n, f0, f1, primes.squares, more.squares, 1)
        c = lanes.next_marked(c + 1)
    return True


def _lane_pass[W: Int](mut lanes: _LaneRow, matrix: _Matrix[W], pivot: List[Int], values: List[List[UInt32]], primes: _Primes, a: Int, b: Int, batch: Int, limit: Int, mut budget: Budget) raises PolyError -> Bool:
    """Reduce S / L, for the S-polynomial of rows a and b, in every lane, recording the entries reducers meet.

    With L = la * lc(g_a) = lb * lc(g_b), S / L is the difference of the two
    monic rows. Returns False, with the row cleared, when a nonzero residue
    meets a column no row leads in: then S does not reduce to zero, and the
    exact check decides. Otherwise the row is zero again.
    """
    var data = lanes.data.unsafe_ptr()
    var sa = matrix.starts[a]
    var sb = matrix.starts[b]
    lanes.add(matrix.entries.unsafe_ptr().unsafe_offset(sa), values[matrix.sources[a]].unsafe_ptr(), matrix.starts[a + 1] - sa, SIMD[DType.uint32, _LANES](1), primes.squares, 0)
    lanes.add(matrix.entries.unsafe_ptr().unsafe_offset(sb), values[matrix.sources[b]].unsafe_ptr(), matrix.starts[b + 1] - sb, (primes.primes - 1).cast[DType.uint32](), primes.squares, 0)
    budget.charge(UInt64(_LANES * (matrix.starts[a + 1] - sa + matrix.starts[b + 1] - sb)))
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
            var factor = v.eq(0).select(_Lanes(0), primes.primes - v).cast[DType.uint32]()
            lanes.add(matrix.entries.unsafe_ptr().unsafe_offset(s), values[matrix.sources.unsafe_get(q)].unsafe_ptr(), n, factor, primes.squares, 1)
        c = lanes.next_marked(c + 1)
    return True


def _modular_pair[W: Int](mut lanes: _LaneRow, matrix: _Matrix[W], pivot: List[Int], coefficients: _Coefficients, mut images: _PairPrimes, a: Int, b: Int, first: Int, allowance: Int, mut cost: Int, mut counts: List[Int], mut budget: Budget) raises PolyError -> Int:
    """The number of primes that proved the S-polynomial of rows a and b reduces to zero, or 0 if they did not.

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
            passed = _lane_pass_two(lanes, matrix, pivot, images.values[batch], images.values[batch + 1], images.batches[batch], images.batches[batch + 1], a, b, batch, limit, budget)
        else:
            passed = _lane_pass(lanes, matrix, pivot, images.values[batch], images.batches[batch], a, b, batch, limit, budget)
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
    # r_c = L v_c / lc(g_c) modulo p, with D folded in: D r_c. The factors
    # are L D modulo each prime, `_LANES` at a time.
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
    # The values of up to `_LANES` slots at a time, slot - j in lane j, under
    # the factors of their time; a new denominator voids the rest.
    var n = basis.limbs + 2
    var block = List[UInt64](length=_LANES * k, fill=0)
    var block_values = List[UInt64](length=_LANES * n, fill=0)
    var sums = List[UInt64](length=_LANES * (2 * basis.limbs + 2), fill=0)
    var euclid = _Euclid(basis.limbs, budget)
    var half_q = List[UInt64](length=basis.limbs, fill=0)
    for l in range(basis.limbs):
        half_q[l] = (basis.product[l] >> 1) | ((basis.product[l + 1] << 63) if l + 1 < basis.limbs else UInt64(0))
    # Q shifted to a normalized divisor, for rescaling values in place.
    var shift = Int(count_leading_zeros(basis.product[basis.limbs - 1]))
    var divisor = List[UInt64](length=basis.limbs, fill=0)
    for l in range(basis.limbs):
        var low = basis.product[l] << UInt64(shift)
        var high = (basis.product[l - 1] >> UInt64(64 - shift)) if shift > 0 and l > 0 else UInt64(0)
        divisor[l] = low | high
    var scaled = List[UInt64](length=2 * basis.limbs + 4, fill=0)
    # Each slot's element, and per element the factors times its leading
    # coefficient's inverse, modulo each prime, as of `version`.
    var elements = List[Int](capacity=nslots)
    for slot in range(nslots):
        elements.append(matrix.sources.unsafe_get(pivot.unsafe_get(lanes.columns.unsafe_get(slot))))
    var ngens = len(coefficients.limbs)
    var combined = List[UInt64](length=ngens * k, fill=0)
    var stamps = List[Int](length=ngens, fill=-1)
    var version = 0
    var top = nslots
    var ready = 0
    # Later columns first: their denominators tend to contain the earlier ones'.
    for slot in range(nslots - 1, -1, -1):
        var g = elements.unsafe_get(slot)
        if top - slot >= ready:
            top = slot
            ready = min(_LANES, slot + 1)
            for j in range(ready):
                var h = elements.unsafe_get(slot - j)
                var from_ = lanes.residues.unsafe_ptr().unsafe_offset((slot - j) * limit)
                var scale = combined.unsafe_ptr().unsafe_offset(h * k)
                if stamps.unsafe_get(h) != version:
                    stamps.unsafe_get(h) = version
                    for batch in range(k // _LANES):
                        var inverse = images.inverses[batch].unsafe_ptr().unsafe_offset(_LANES * h).unsafe_load[width=_LANES]()
                        var f = factors.unsafe_ptr().unsafe_offset(_LANES * batch).unsafe_load[width=_LANES]()
                        scale.unsafe_offset(_LANES * batch).unsafe_store[width=_LANES](_mod_lanes(f * inverse, images.batches[batch]))
                for batch in range(k // _LANES):
                    ref primes = images.batches[batch]
                    var v = from_.unsafe_offset(_LANES * batch).unsafe_load[width=_LANES]().cast[DType.uint64]()
                    var y = _mod_lanes(v * scale.unsafe_offset(_LANES * batch).unsafe_load[width=_LANES](), primes)
                    comptime for l in range(_LANES):
                        block.unsafe_get(_LANES * (_LANES * batch + l) + j) = y[l]
            basis.values(block, block_values, sums)
        # Charged per slot, as one `value` each.
        budget.charge(UInt64(_product(k, basis.limbs)))
        var x = block_values.unsafe_ptr().unsafe_offset((top - slot) * n)
        comptime if _CERT_STATS:
            counts[4] += 1
        # The symmetric representative: x or x - Q, whichever is smaller; x
        # is the smaller exactly when it is at most floor(Q / 2).
        var size: Int
        if _compare_at(x, basis.limbs, half_q.unsafe_ptr()) <= 0:
            size = _bits_at(x, basis.limbs)
        else:
            for l in range(basis.limbs):
                other.unsafe_get(l) = basis.product.unsafe_get(l)
            _ = _subtract_limbs(other.unsafe_ptr(), basis.limbs, x, basis.limbs)
            size = _bits_at(other.unsafe_ptr(), basis.limbs)
        var n_bits: Int
        if max(worst, size + coefficients.bits[g]) + log + 1 < basis.bits - 1:
            # Small enough for the bound as it is: n_c is this value.
            n_bits = size
        else:
            # A new denominator: a / b = x modulo Q with |a|, b below 2^half.
            counts[3] += 1
            var t0 = _clock()
            budget.charge(UInt64(_product(basis.limbs, basis.limbs)))
            for l in range(n):
                work.unsafe_get(l) = x.unsafe_offset(l).unsafe_load()
            var found = euclid.fraction(work, basis.product, half)
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
            version += 1
            # Earlier n_c grow by the new factor; account for it in the bound now.
            worst += b.magnitude_bit_length()
            # The values formed ahead are now b times theirs modulo Q: rescale
            # them when that is cheaper than forming them again.
            var lane = top - slot
            var remaining = ready - lane - 1
            var factor = _shifted_limbs(b_limbs, shift)
            if remaining > 0 and len(factor) <= basis.limbs and remaining * (2 * len(factor) + 1) < 2 * k:
                for j in range(lane + 1, ready):
                    _rescale(block_values.unsafe_ptr().unsafe_offset(j * n), basis.limbs, factor, divisor, shift, scaled)
            else:
                ready = 0
        # n_c times D / D_now, which is below 2^(bits D - bits D_now + 1) at the end:
        # counted here by charging the later growth to `worst` as it happens.
        worst = max(worst, n_bits + coefficients.bits[g])
        if worst + log + 1 >= basis.bits - 1:
            return False
    worst = max(worst, d_bits + s_bits)
    # |D S - sum n_c R_c| <= (nslots + 1) 2^worst, and must stay below Q / 2.
    return worst + log + 1 < basis.bits - 1


def _bits_at(x: Pointer[mut=False, UInt64, _], n: Int) -> Int:
    """The bit length of the nonnegative x[0:n]."""
    var l = n - 1
    while l >= 0 and x.unsafe_offset(l).unsafe_load() == 0:
        l -= 1
    if l < 0:
        return 0
    return 64 * l + 64 - Int(count_leading_zeros(x.unsafe_offset(l).unsafe_load()))


def _shifted_limbs(limbs: List[UInt64], shift: Int) -> List[UInt64]:
    """The magnitude limbs times 2^shift, for shift below 64, without leading zeros."""
    var result = List[UInt64](capacity=len(limbs) + 1)
    var carry = UInt64(0)
    for limb in limbs:
        result.append((limb << UInt64(shift)) | carry)
        carry = (limb >> UInt64(64 - shift)) if shift > 0 else UInt64(0)
    result.append(carry)
    while len(result) and result[len(result) - 1] == 0:
        _ = result.pop()
    return result^


def _rescale(x: Pointer[mut=True, UInt64, _], n: Int, factor: List[UInt64], divisor: List[UInt64], shift: Int, mut scratch: List[UInt64]):
    """Set x[0:n], below Q, to x times b modulo Q, given factor = b 2^shift and divisor = Q 2^shift (n limbs, normalized)."""
    var length = n + len(factor)
    var w = scratch.unsafe_ptr()
    for l in range(length + 1):
        w.unsafe_offset(l).unsafe_store(0)
    for l in range(len(factor)):
        _add_mul_1(w.unsafe_offset(l), length - l, factor[l], x, n)
    _remainder_limbs(w, length, divisor.unsafe_ptr(), n)
    for l in range(n):
        var high = (w.unsafe_offset(l + 1).unsafe_load() << UInt64(64 - shift)) if shift > 0 and l + 1 < n else UInt64(0)
        x.unsafe_offset(l).unsafe_store((w.unsafe_offset(l).unsafe_load() >> UInt64(shift)) | high)


def _compare_at(x: Pointer[mut=False, UInt64, _], n: Int, y: Pointer[mut=False, UInt64, _]) -> Int:
    """The sign of x[0:n] - y[0:n]."""
    for l in range(n - 1, -1, -1):
        var a = x.unsafe_offset(l).unsafe_load()
        var b = y.unsafe_offset(l).unsafe_load()
        if a != b:
            return 1 if a > b else -1
    return 0


def _bits_window(x: Pointer[mut=False, UInt64, _], shift: Int) -> Int:
    """Bits shift to shift + 61 of the nonnegative x, which has no bit above them."""
    var w = shift // 64
    var b = shift % 64
    var low = x.unsafe_offset(w).unsafe_load() >> UInt64(b)
    var high = (x.unsafe_offset(w + 1).unsafe_load() << UInt64(64 - b)) if b > 0 and b + 62 > 64 else UInt64(0)
    return Int((low | high) & ((UInt64(1) << 62) - 1))


@always_inline
def _combine(target: Pointer[mut=True, UInt64, _], n: Int, f: Int, x: Pointer[mut=False, UInt64, _], g: Int, y: Pointer[mut=False, UInt64, _]):
    """target = f x + g y, all n-limb two's complement, modulo 2^(64 n)."""
    for l in range(n):
        target.unsafe_offset(l).unsafe_store(0)
    if f > 0:
        _add_mul_1(target, n, UInt64(f), x, n)
    elif f < 0:
        _sub_mul_1(target, n, UInt64(-f), x, n)
    if g > 0:
        _add_mul_1(target, n, UInt64(g), y, n)
    elif g < 0:
        _sub_mul_1(target, n, UInt64(-g), y, n)


struct _Euclid(Movable):
    """`_euclid` in limbs, for values below a modulus of `limbs` limbs.

    The remainders r and cofactors t live in n = limbs + 1 limbs of two's
    complement; every combination is exact modulo 2^(64 n) and the true
    values fit. The steps are `_euclid`'s: the same Lehmer matrices from the
    same leading bits while r1 is long, then one exact division at a time,
    so the remainder sequence, and where it stops, are the same.
    """
    var n: Int
    var r0: List[UInt64]
    var r1: List[UInt64]
    var t0: List[UInt64]
    var t1: List[UInt64]
    var next0: List[UInt64]
    var next1: List[UInt64]
    var dividend: List[UInt64]
    var divisor: List[UInt64]
    var quotient: List[UInt64]

    def __init__(out self, limbs: Int, mut budget: Budget) raises PolyError:
        self.n = limbs + 1
        _allocation[UInt64](_product(10, self.n + 2), budget)
        self.r0 = List[UInt64](length=self.n, fill=0)
        self.r1 = List[UInt64](length=self.n, fill=0)
        self.t0 = List[UInt64](length=self.n, fill=0)
        self.t1 = List[UInt64](length=self.n, fill=0)
        self.next0 = List[UInt64](length=self.n, fill=0)
        self.next1 = List[UInt64](length=self.n, fill=0)
        self.dividend = List[UInt64](length=self.n + 2, fill=0)
        self.divisor = List[UInt64](length=self.n, fill=0)
        self.quotient = List[UInt64](length=self.n + 1, fill=0)

    def fraction(mut self, x: List[UInt64], modulus: List[UInt64], bits: Int) -> Optional[Tuple[Integer, Integer]]:
        """As `_euclid(x, modulus, bits)`, for 0 <= x < modulus, both given in limbs."""
        var n = self.n
        for l in range(n):
            self.r0.unsafe_get(l) = modulus[l] if l < len(modulus) else UInt64(0)
            self.r1.unsafe_get(l) = x[l] if l < n - 1 else UInt64(0)
            self.t0.unsafe_get(l) = 0
            self.t1.unsafe_get(l) = 1 if l == 0 else UInt64(0)
        var stop = bits + 128
        while True:
            var length1 = _bits_at(self.r1.unsafe_ptr(), n)
            if length1 <= bits:
                break
            if length1 > stop:
                var shift = _bits_at(self.r0.unsafe_ptr(), n) - 62
                var u = _bits_window(self.r0.unsafe_ptr(), shift)
                var w = _bits_window(self.r1.unsafe_ptr(), shift)
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
                    _combine(self.next0.unsafe_ptr(), n, a, self.r0.unsafe_ptr(), b, self.r1.unsafe_ptr())
                    _combine(self.next1.unsafe_ptr(), n, c, self.r0.unsafe_ptr(), d, self.r1.unsafe_ptr())
                    swap(self.r0, self.next0)
                    swap(self.r1, self.next1)
                    _combine(self.next0.unsafe_ptr(), n, a, self.t0.unsafe_ptr(), b, self.t1.unsafe_ptr())
                    _combine(self.next1.unsafe_ptr(), n, c, self.t0.unsafe_ptr(), d, self.t1.unsafe_ptr())
                    swap(self.t0, self.next0)
                    swap(self.t1, self.next1)
                    continue
            self._step(length1)
        # r1 is below 2^bits; t1 must be nonzero and as short.
        var negative = (self.t1.unsafe_get(n - 1) >> 63) != 0
        if negative:
            for l in range(n):
                self.next1.unsafe_get(l) = 0
            _ = _subtract_limbs(self.next1.unsafe_ptr(), n, self.t1.unsafe_ptr(), n)
        else:
            for l in range(n):
                self.next1.unsafe_get(l) = self.t1.unsafe_get(l)
        var length = _bits_at(self.next1.unsafe_ptr(), n)
        if length == 0 or length > bits:
            return None
        var bytes = List[UInt8](length=8 * n, fill=0)
        for l in range(n):
            comptime for shift in range(8):
                bytes[8 * l + shift] = UInt8((self.r1.unsafe_get(l) >> UInt64(8 * shift)) & 0xFF)
        # The sign goes to the numerator, as `_euclid` gives it.
        return (Integer.from_bytes(bytes, negative=negative), _limbs_to_integer(self.next1, n))

    def _step(mut self, length1: Int):
        """One Euclidean step: (r0, r1) = (r1, r0 mod r1) and (t0, t1) = (t1, t0 - q t1)."""
        var n = self.n
        var m = (length1 + 63) // 64
        var shift = Int(count_leading_zeros(self.r1.unsafe_get(m - 1)))
        var length0 = _bits_at(self.r0.unsafe_ptr(), n)
        var size = max((length0 + shift + 63) // 64, m)
        # The normalized divisor and dividend, with a zero limb above the dividend.
        var carry = UInt64(0)
        for l in range(m):
            var limb = self.r1.unsafe_get(l)
            self.divisor.unsafe_get(l) = (limb << UInt64(shift)) | carry
            carry = limb >> UInt64(64 - shift) if shift > 0 else UInt64(0)
        carry = 0
        for l in range(size + 1):
            var limb = self.r0.unsafe_get(l) if l < n else UInt64(0)
            self.dividend.unsafe_get(l) = (limb << UInt64(shift)) | carry
            carry = limb >> UInt64(64 - shift) if shift > 0 else UInt64(0)
        self.dividend.unsafe_get(size + 1) = 0
        _divide_limbs(self.dividend.unsafe_ptr(), size, self.divisor.unsafe_ptr(), m, self.quotient.unsafe_ptr())
        # The remainder, shifted back, becomes r1; r1 becomes r0.
        for l in range(n):
            var low = self.dividend.unsafe_get(l) >> UInt64(shift) if l < m else UInt64(0)
            var high = (self.dividend.unsafe_get(l + 1) << UInt64(64 - shift)) if shift > 0 and l + 1 < m else UInt64(0)
            self.next1.unsafe_get(l) = low | high
        swap(self.r0, self.r1)
        swap(self.r1, self.next1)
        # t0 - q t1, then the rotation.
        for l in range(n):
            self.next0.unsafe_get(l) = self.t0.unsafe_get(l)
        for j in range(size - m + 1):
            var digit = self.quotient.unsafe_get(j)
            if digit != 0 and j < n:
                _sub_mul_1(self.next0.unsafe_ptr().unsafe_offset(j), n - j, digit, self.t1.unsafe_ptr(), n - j)
        swap(self.t0, self.t1)
        swap(self.t1, self.next0)


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
