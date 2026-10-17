"""Multi-modular univariate gcds and resultants over the integers.

Images come from the word-size field kernels in _nmod_euclid. Coefficients are
reconstructed incrementally in symmetric representation: a new prime leaves
a coefficient unchanged exactly when its residue already agrees, so a prime
that changes nothing marks a stable candidate. The gcd is accepted only after
exact division (G-5); the resultant stops at the Hadamard bound.
"""
from apn_mojo import Integer
from .errors import Budget, PolyError, PolyErrorKind, _allocation, _charge_size, _sum
from .coefficients import ZZ, NoContext
from ._coefficient_ops import _gcd_coefficient, _quotient, _exact
from .dense import DensePoly
from .primes import prime, _residue
from .coefficient_buffer import _view
from ._ntt import _PRIMES, _PRIME_BITS, _PRIME_COUNT, _series_inverse, _modular_product, _equal_mod, _reconstruct_zz, _bits_zz, _bit_length
from ._nmod_euclid import _Field, _gcd_words, _resultant_words, _trim_words, _inverse_mod


struct _Reconstruction(Movable):
    """Symmetric residues modulo a growing product of primes."""
    var values: List[Integer]
    var modulus: Integer

    def __init__(out self, count: Int, mut budget: Budget) raises PolyError:
        _allocation[Integer](count, budget)
        self.values = List[Integer](length=count, fill=Integer(0))
        self.modulus = Integer(1)

    def headroom(self) -> Int:
        """The bits between the largest value and half the modulus."""
        var top = 0
        for i in range(len(self.values)):
            top = max(top, self.values[i].magnitude_bit_length())
        return self.modulus.magnitude_bit_length() - 1 - top

    def merge(mut self, residues: List[UInt64], p: UInt64, mut budget: Budget) raises PolyError -> Bool:
        """Fold standard residues modulo p into the values; return whether any value changed."""
        var field = _Field.of(p)
        var m = _residue(self.modulus, p, budget)
        if m == 0:
            raise PolyError(PolyErrorKind.DOMAIN, "CRT moduli are not coprime")
        var inverse = field.inverse(field.enter(m))
        var big_p = ZZ(Integer(Int(p)))
        var next_modulus = ZZ(self.modulus.copy()).mul(big_p, budget).value
        var next_half: Integer
        try:
            next_half = next_modulus >> 1
        except e:
            raise PolyError(PolyErrorKind.CAPACITY, String(e))
        var changed = False
        for i in range(len(self.values)):
            budget.charge(1)
            var old = _residue(self.values[i], p, budget)
            var difference = field.sub(field.enter(residues[i]), field.enter(old))
            if difference == 0:
                continue
            changed = True
            var correction = field.leave(field.mul(difference, inverse))
            var value = ZZ(self.values[i].copy()).add(ZZ(self.modulus.copy()).mul(ZZ(Integer(Int(correction))), budget), budget).value
            if value > next_half:
                value = ZZ(value^).sub(ZZ(next_modulus.copy()), budget).value
            self.values[i] = value^
        self.modulus = next_modulus^
        return changed


def _residues(f: DensePoly[ZZ], p: UInt64, mut budget: Budget) raises PolyError -> List[UInt64]:
    _allocation[UInt64](len(f.coefficients), budget)
    var out = List[UInt64](capacity=len(f.coefficients))
    for i in range(len(f.coefficients)):
        ref c = f.coefficients[i].value
        var r = _residue(c, p, budget)
        out.append(r)
    return out^


def _entered(values: List[UInt64], field: _Field) -> List[UInt64]:
    var out = List[UInt64](capacity=len(values))
    for v in values:
        out.append(field.enter(v))
    return out^


struct _Words(Movable):
    """The 32-bit magnitude words of a dense integer polynomial's coefficients, flattened once for residues modulo many primes."""
    var words: List[UInt64]
    var offsets: List[Int]
    var negative: List[Bool]
    var longest: Int

    def __init__(out self, f: DensePoly[ZZ], mut budget: Budget) raises PolyError:
        var count = len(f.coefficients)
        _allocation[Int](count + 1, budget)
        self.offsets = List[Int](capacity=count + 1)
        self.negative = List[Bool](capacity=count)
        self.words = List[UInt64]()
        self.longest = 0
        self.offsets.append(0)
        for i in range(count):
            ref c = f.coefficients[i].value
            var n = c._word_count()
            _allocation[UInt64](n, budget)
            for j in range(n):
                self.words.append(UInt64(c._word(j)))
            self.offsets.append(len(self.words))
            self.negative.append(c.sign() < 0)
            self.longest = max(self.longest, n)

    def residues(self, field: _Field, mut budget: Budget, standard: Bool = False) raises PolyError -> List[UInt64]:
        """Every coefficient modulo field.p, in Montgomery form or, when standard, as plain residues.

        With W_j the Montgomery form of 2^(32 j) R, the sum of word_j W_j
        stays below 2^32 p per word, so one reduction yields value R mod p;
        W_j = 2^(32 j) R mod p yields the value itself.
        """
        _charge_size(len(self.words) + self.longest, budget)
        var powers = List[UInt64](capacity=self.longest)
        var step = field.enter(UInt64(1) << 32)
        var w = field.enter(1) if standard else field.r2
        for _ in range(self.longest):
            powers.append(w)
            w = field.mul(w, step)
        _allocation[UInt64](len(self.negative), budget)
        var out = List[UInt64](capacity=len(self.negative))
        var pw = self.words.unsafe_ptr()
        var pp = powers.unsafe_ptr()
        for i in range(len(self.negative)):
            var base = self.offsets[i]
            var count = self.offsets[i + 1] - base
            var word = pw.unsafe_offset(base)
            # Two independent sums; together still below count 2^32 p <= p 2^64.
            var even = UInt128(0)
            var odd = UInt128(0)
            var j = 0
            while j + 1 < count:
                even += UInt128(word.unsafe_offset(j).unsafe_load()) * UInt128(pp.unsafe_offset(j).unsafe_load())
                odd += UInt128(word.unsafe_offset(j + 1).unsafe_load()) * UInt128(pp.unsafe_offset(j + 1).unsafe_load())
                j += 2
            if j < count:
                even += UInt128(word.unsafe_offset(j).unsafe_load()) * UInt128(pp.unsafe_offset(j).unsafe_load())
            var r = field.reduce(even + odd)
            out.append((field.p - r if r else r) if self.negative[i] else r)
        return out^


def _gcd_images(fd: DensePoly[ZZ], hd: DensePoly[ZZ], gamma: ZZ, p: UInt64, mut budget: Budget) raises PolyError -> List[UInt64]:
    """gamma times the monic gcd of the images modulo p, in standard form."""
    var field = _Field.of(p)
    var g = _gcd_words(_entered(_residues(fd, p, budget), field), _entered(_residues(hd, p, budget), field), field, budget)
    var scale = field.enter(_residue(gamma.value, p, budget))
    for i in range(len(g)):
        g[i] = field.leave(field.mul(g[i], scale))
    return g^


def _next_gcd_candidate(fd: DensePoly[ZZ], hd: DensePoly[ZZ], mut state: _GcdSearch, mut budget: Budget) raises PolyError -> DensePoly[ZZ]:
    """Advance the prime search to the next stable candidate gamma·g/lc(g), not yet primitive.

    A constant image modulo a prime dividing neither leading coefficient
    proves the gcd constant, so the constant candidate returns at once.
    """
    while True:
        budget.charge(1)
        var p = prime(state.index, budget)
        state.index = _sum(state.index, 1)
        # Both degrees must survive reduction, as required by G-5's proof.
        if _residue(fd.coefficients[len(fd.coefficients) - 1].value, p, budget) == 0 or _residue(hd.coefficients[len(hd.coefficients) - 1].value, p, budget) == 0:
            continue
        var image = _gcd_images(fd, hd, state.gamma, p, budget)
        var degree = len(image) - 1
        if degree > state.best:
            continue
        if degree == 0:
            return DensePoly[ZZ].from_coefficients(fd.variable, NoContext(), [ZZ(Integer(1))], budget)
        if degree < state.best:
            state.best = degree
            state.values = _Reconstruction(degree + 1, budget)
            state.primes = 0
        var changed = state.values.merge(image, p, budget)
        state.primes = _sum(state.primes, 1)
        if state.primes > 1 and not changed:
            _allocation[ZZ](state.best + 1, budget)
            var coefficients = List[ZZ](capacity=state.best + 1)
            for i in range(state.best + 1):
                budget.charge(1)
                coefficients.append(ZZ(state.values.values[i].copy()))
            var dense = DensePoly[ZZ].from_coefficients(fd.variable, NoContext(), coefficients^, budget)
            if dense.degree() == state.best:
                return dense^


struct _GcdSearch(Movable):
    var gamma: ZZ
    var best: Int
    var index: Int
    var primes: Int
    var values: _Reconstruction

    def __init__(out self, var gamma: ZZ, best: Int, mut budget: Budget) raises PolyError:
        self.gamma = gamma^
        self.best = best
        self.index = 0
        self.primes = 0
        self.values = _Reconstruction(0, budget)


def _hadamard_bits(f: DensePoly[ZZ], mut budget: Budget) raises PolyError -> Int:
    """An upper bound on log2 of the Euclidean norm of the coefficient vector."""
    var top = 0
    for i in range(len(f.coefficients)):
        budget.charge(1)
        top = max(top, f.coefficients[i].value.magnitude_bit_length())
    var count_bits = 0
    while (1 << count_bits) < len(f.coefficients):
        count_bits += 1
    # ||f||_2 <= sqrt(len) max|f_i| < 2^(top + ceil(log2 len) / 2).
    return top + (count_bits + 1) // 2


comptime _SMALL_TOP = UInt64(1) << 30
"""Resultant images use primes below this bound, where the Euclidean kernel vectorizes."""
comptime _SIEVE_SPAN = 1 << 14
comptime _SMALL_RESULTANT_BITS = 2048
"""Hadamard bounds above this many bits amortize sieving the small primes."""


struct _SmallPrimes(Movable):
    """The primes between 2^29 and 2^30 in descending order, found by a segmented sieve as needed."""
    var base: List[UInt64]
    var found: List[UInt64]
    var position: Int
    var top: UInt64

    def __init__(out self):
        """An empty sequence, for callers that will not draw from it."""
        self.base = List[UInt64]()
        self.found = List[UInt64]()
        self.position = 0
        self.top = 0

    def __init__(out self, mut budget: Budget) raises PolyError:
        # Odd primes up to 2^15, enough to sieve any segment below 2^30.
        comptime limit = 1 << 15
        _charge_size(limit, budget)
        var composite = List[Bool](length=limit + 1, fill=False)
        self.base = List[UInt64]()
        for i in range(3, limit + 1, 2):
            if composite[i]:
                continue
            self.base.append(UInt64(i))
            for j in range(i * i, limit + 1, 2 * i):
                composite[j] = True
        self.found = List[UInt64]()
        self.position = 0
        self.top = _SMALL_TOP

    def next(mut self, mut budget: Budget) raises PolyError -> UInt64:
        while self.position == len(self.found):
            # Callers count 29 bits per prime, so the sequence stops at 2^29.
            if self.top <= (UInt64(1) << 29) + UInt64(_SIEVE_SPAN):
                raise PolyError(PolyErrorKind.CAPACITY, "small prime sequence exhausted")
            var low = self.top - UInt64(_SIEVE_SPAN)
            _charge_size(_SIEVE_SPAN + len(self.base), budget)
            var composite = List[Bool](length=_SIEVE_SPAN, fill=False)
            for q in self.base:
                var start = ((low + q - 1) // q) * q
                var j = Int(start - low)
                while j < _SIEVE_SPAN:
                    composite[j] = True
                    j += Int(q)
            self.found.clear()
            self.position = 0
            for j in range(_SIEVE_SPAN - 1, -1, -1):
                if not composite[j] and ((low + UInt64(j)) & 1):
                    self.found.append(low + UInt64(j))
            self.top = low
        var p = self.found[self.position]
        self.position += 1
        return p


def _modular_resultant(fd: DensePoly[ZZ], gd: DensePoly[ZZ], mut budget: Budget) raises PolyError -> Integer:
    """The resultant of two integer polynomials of positive degree, by CRT up to the Hadamard bound.

    Bounds above _SMALL_RESULTANT_BITS take images modulo primes below 2^30,
    whose Euclidean kernel vectorizes, combining pairs of images in one word
    before each big-integer merge; smaller ones use the cached 62-bit primes
    and skip the sieve.
    """
    var m = fd.degree()
    var n = gd.degree()
    # |res| <= ||f||^n ||g||^m; the symmetric range needs one more bit.
    var bits = _sum(_sum(n * _hadamard_bits(fd, budget), m * _hadamard_bits(gd, budget)), 2)
    var small = bits > _SMALL_RESULTANT_BITS
    var values = _Reconstruction(1, budget)
    var covered = 0
    var index = 0
    var primes = _SmallPrimes()
    if small:
        primes = _SmallPrimes(budget)
    var residue = List[UInt64](length=1, fill=0)
    var fw = _Words(fd, budget)
    var gw = _Words(gd, budget)
    var pending = UInt64(0)
    var pending_prime = UInt64(0)
    while covered < bits:
        budget.charge(1)
        var p: UInt64
        if small:
            p = primes.next(budget)
        else:
            p = prime(index, budget)
            index = _sum(index, 1)
        var field = _Field.of(p)
        var a = fw.residues(field, budget)
        var b = gw.residues(field, budget)
        if a[m] == 0 or b[n] == 0:
            continue
        var r = field.leave(_resultant_words(a^, b^, field, budget))
        var floor_log = 0
        while (p >> UInt64(floor_log + 1)) != 0:
            floor_log += 1
        covered = _sum(covered, floor_log)
        if not small:
            residue[0] = r
            _ = values.merge(residue, p, budget)
            continue
        if pending_prime == 0:
            pending = r
            pending_prime = p
            continue
        # x = pending + q t with t = (r - pending) / q mod p, below q p < 2^60.
        var q = pending_prime
        var t = ((r + p - pending % p) % p) * _inverse_mod(q % p, p) % p
        residue[0] = pending + q * t
        _ = values.merge(residue, q * p, budget)
        pending_prime = 0
    if pending_prime:
        residue[0] = pending
        _ = values.merge(residue, pending_prime, budget)
    return values.values[0].copy()


def _dense_content(f: DensePoly[ZZ], mut budget: Budget) raises PolyError -> ZZ:
    """The nonnegative gcd of the coefficients."""
    var content = ZZ(Integer(0))
    for i in range(len(f.coefficients)):
        budget.charge(1)
        content = _gcd_coefficient(content, f.coefficients[i], budget)
        if content.value == Integer(1):
            break
    return content^


def _divide_scalar(f: DensePoly[ZZ], c: ZZ, mut budget: Budget) raises PolyError -> DensePoly[ZZ]:
    _allocation[ZZ](len(f.coefficients), budget)
    var values = List[ZZ](capacity=len(f.coefficients))
    for i in range(len(f.coefficients)):
        budget.charge(1)
        values.append(_exact(f.coefficients[i], c, budget))
    return DensePoly[ZZ]._from_canonical(f.variable, NoContext(), values^)


def _quotient_images(words: _Words, divisor: List[UInt64], inverse: List[UInt64], field: _Field, mut budget: Budget) raises PolyError -> Optional[List[UInt64]]:
    """The quotient of the dividend by the divisor modulo field.p, or None when a remainder is left.

    inverse is the reversed divisor's series inverse to at least the quotient's length.
    """
    var q = field.p
    var a = words.residues(field, budget, standard=True)
    var m = len(a) - len(divisor) + 1
    _allocation[UInt64](2 * m, budget)
    var a_rev = List[UInt64](capacity=m)
    for i in range(m):
        a_rev.append(a[len(a) - 1 - i])
    var head = List[UInt64](capacity=m)
    for i in range(m):
        head.append(inverse[i])
    var q_rev = _modular_product(a_rev, head, m, q, False, budget)
    var quotient = List[UInt64](capacity=m)
    for i in range(m):
        quotient.append(q_rev[m - 1 - i])
    if not _equal_mod(a, quotient, divisor, q, budget):
        return None
    return quotient^


def _bounded(quotients: List[List[UInt64]], k: Int, count: Int, top_dividend: Int, top_divisor: Int, mut budget: Budget) raises PolyError -> Bool:
    """Whether the symmetric reconstruction Q of the quotient images certifies divisor Q = dividend.

    Q times the divisor agrees with the dividend modulo the product M of the
    first k transform primes; once |dividend| and |divisor| |Q|_1 both lie
    below M/2 the congruence is an identity. Every transform prime exceeds
    2^61, so M > 2^(61 k).
    """
    var candidate = _reconstruct_zz[ZZ](quotients, k, count, budget)
    var top = 0
    for i in range(len(candidate)):
        top = max(top, candidate[i].value.magnitude_bit_length())
    var room = _PRIME_BITS * k - 1
    return top_dividend + 1 <= room and top_divisor + top + _bit_length(count) <= room


def _transform_divides(f: DensePoly[ZZ], fw: _Words, h: DensePoly[ZZ], hw: _Words, g: DensePoly[ZZ], mut budget: Budget) raises PolyError -> Optional[Bool]:
    """Whether g divides both f and h, of degree at least deg g, from quotients modulo transform primes, or None when they cannot decide.

    Each prime's quotients must leave no remainder, and their
    reconstructions must pass the size bound of _bounded; no product is
    formed. Both dividends share the divisor's residues and series inverse.
    """
    var gw = _Words(g, budget)
    var primes = materialize[_PRIMES]()
    var top_f = _bits_zz(_view(f.coefficients))
    var top_h = _bits_zz(_view(h.coefficients))
    var top_g = _bits_zz(_view(g.coefficients))
    var dg = len(g.coefficients)
    var longest = max(len(f.coefficients), len(h.coefficients))
    var span = longest - dg + 1
    var k = (max(top_f, top_h) + _bit_length(longest) + 2 + _PRIME_BITS - 1) // _PRIME_BITS
    var quotients_f = List[List[UInt64]]()
    var quotients_h = List[List[UInt64]]()
    while k <= _PRIME_COUNT:
        for i in range(len(quotients_f), k):
            var field = _Field.of(primes[i])
            var b = gw.residues(field, budget, standard=True)
            if b[dg - 1] == 0:
                return None  # the divisor's degree drops modulo this prime
            var head = List[UInt64](capacity=min(span, dg))
            for j in range(min(span, dg)):
                head.append(b[dg - 1 - j])
            var inverse = _series_inverse(head, span, primes[i], budget)
            var qf = _quotient_images(fw, b, inverse, field, budget)
            if not qf:
                return Optional(False)
            var qh = _quotient_images(hw, b, inverse, field, budget)
            if not qh:
                return Optional(False)
            quotients_f.append(qf.take())
            quotients_h.append(qh.take())
        if _bounded(quotients_f, k, len(f.coefficients) - dg + 1, top_f, top_g, budget) and _bounded(quotients_h, k, len(h.coefficients) - dg + 1, top_h, top_g, budget):
            return Optional(True)
        if k == _PRIME_COUNT:
            break
        k = min(2 * k, _PRIME_COUNT)
    return None


def _divides_both(f: DensePoly[ZZ], fw: _Words, h: DensePoly[ZZ], hw: _Words, g: DensePoly[ZZ], mut budget: Budget) raises PolyError -> Bool:
    """Whether g divides both f and h, of degree at least deg g: by transform primes when they decide, else by long division."""
    if g.degree() >= 31:
        var fast = _transform_divides(f, fw, h, hw, g, budget)
        if fast:
            return fast.value()
    return _dense_divides(f, g, budget) and _dense_divides(h, g, budget)


def _dense_divides(f: DensePoly[ZZ], g: DensePoly[ZZ], mut budget: Budget) raises PolyError -> Bool:
    """Whether g divides f over the integers, by dense exact long division."""
    if f.is_zero():
        return True
    var n = g.degree()
    if f.degree() < n:
        return False
    ref lc = g.coefficients[n]
    var r = f.coefficients.to_list(budget)
    for k in range(f.degree(), n - 1, -1):
        budget.charge(1)
        if r[k].is_zero():
            continue
        var q = _quotient(r[k], lc, budget)
        if not q:
            return False
        ref digit = q.value()
        var base = k - n
        for i in range(n):
            budget.charge(1)
            if not g.coefficients[i].is_zero():
                r[base + i] = r[base + i].sub(digit.mul(g.coefficients[i], budget), budget)
    for i in range(n):
        budget.charge(1)
        if not r[i].is_zero():
            return False
    return True


def _univariate_gcd(f: DensePoly[ZZ], h: DensePoly[ZZ], mut budget: Budget) raises PolyError -> DensePoly[ZZ]:
    """The positive-leading gcd of two nonzero integer polynomials, integer content included."""
    var cf = _dense_content(f, budget)
    var ch = _dense_content(h, budget)
    var common = _gcd_coefficient(cf, ch, budget)
    var pf = _divide_scalar(f, cf, budget)
    var ph = _divide_scalar(h, ch, budget)
    var constant = DensePoly[ZZ].from_coefficients(f.variable, NoContext(), [common.copy()], budget)
    if pf.degree() == 0 or ph.degree() == 0:
        return constant^
    var gamma = _gcd_coefficient(pf.coefficients[pf.degree()], ph.coefficients[ph.degree()], budget)
    var fw = _Words(pf, budget)
    var hw = _Words(ph, budget)
    var best = min(pf.degree(), ph.degree()) + 1
    var values = _Reconstruction(0, budget)
    var used = 0
    var index = 0
    while True:
        budget.charge(1)
        var p = prime(index, budget)
        index = _sum(index, 1)
        var field = _Field.of(p)
        var a = fw.residues(field, budget)
        var b = hw.residues(field, budget)
        # Both degrees must survive reduction, as required by G-5's proof.
        if a[len(a) - 1] == 0 or b[len(b) - 1] == 0:
            continue
        var image = _gcd_words(a^, b^, field, budget)
        var degree = len(image) - 1
        if degree > best:
            continue
        if degree == 0:
            return constant^
        if degree < best:
            best = degree
            values = _Reconstruction(degree + 1, budget)
            used = 0
        var scale = field.enter(_residue(gamma.value, p, budget))
        for i in range(len(image)):
            image[i] = field.leave(field.mul(image[i], scale))
        var changed = values.merge(image, p, budget)
        used = _sum(used, 1)
        # Exact division decides; it is tried once the images agree or every
        # reconstructed coefficient sits 16 bits inside the symmetric range,
        # which an incomplete reconstruction of two or more random
        # coefficients does with probability below 2^-32.
        if (used > 1 and not changed) or values.headroom() >= 16:
            _allocation[ZZ](best + 1, budget)
            var coefficients = List[ZZ](capacity=best + 1)
            for i in range(best + 1):
                budget.charge(1)
                coefficients.append(ZZ(values.values[i].copy()))
            var candidate = DensePoly[ZZ].from_coefficients(pf.variable, NoContext(), coefficients^, budget)
            if candidate.degree() != best:
                continue
            var primitive = _divide_scalar(candidate, _dense_content(candidate, budget), budget)
            if primitive.coefficients[primitive.degree()].value.sign() < 0:
                primitive = primitive.scale(ZZ(Integer(-1)), budget)
            if _divides_both(pf, fw, ph, hw, primitive, budget):
                return primitive.scale(common, budget)
