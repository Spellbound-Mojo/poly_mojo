"""Gröbner bases over QQ under GREVLEX, through the homogenized inputs.

The inputs become primitive integer polynomials, homogenized with a new least
variable h (GREVLEX with h last) unless they are homogeneous already. The
reduced basis of their ideal J is reconstructed from modular images and
certified, and setting h = 1 then gives the basis of the input ideal.

1. Images. Modulo each prime below 2^31 that divides no leading coefficient,
   F4 computes the reduced basis of the image of J. Images whose leading
   monomials differ from the first one's are set aside.
2. Reconstruction. Each coefficient is lifted by the Chinese remainder
   theorem over the union of the images' supports and recovered as a
   fraction, through a running denominator per element; a candidate must
   also agree with the next image before it is certified.
3. Certification, exactly over the integers, for the homogeneous candidate G:
   (a) every input reduces to zero modulo G, so J is contained in <G>;
   (b) every S-pair kept by the Gebauer–Möller criteria reduces to zero, so
       G is a Gröbner basis of <G> and <G>_d has dimension c_d, the number of
       degree-d monomials its leading monomials generate; the pairs of each
       degree are reduced in one F4 matrix over the integers
       (`_integer_f4`);
   (c) G's leading monomials are those of a basis G_p computed inside the
       image J_p. Then dim (J_p)_d >= c_d, and dim (J_p)_d <= dim J_d since
       the Macaulay matrix of J_d is an integer matrix and reduction modulo p
       cannot raise its rank. So c_d <= dim J_d <= dim <G>_d = c_d for every
       d, and <G> = J;
   (d) every element is monic and no tail monomial is divisible by a leading
       monomial, so G is the reduced basis of J.
   Correctness never depends on a prime being lucky; bad primes cost time.
   If reconstruction needs more than `_PRIME_LIMIT` primes or certification
   fails `_CERTIFY_LIMIT` times, J is computed exactly instead: the packed
   engine runs fraction-free Buchberger on the homogenized inputs, degree by
   degree, which avoids most of the coefficient growth an inhomogeneous
   computation suffers.

Finish. A GREVLEX basis of J with h last dehomogenizes to a basis of the
input ideal, because the leading monomial of a homogeneous element
dehomogenizes to the leading monomial of its image. Dropping elements whose
leading monomial another's divides and reducing the tails exactly gives the
reduced basis, which is unique, so every route returns the same result.
"""
from std.math import max
from apn_mojo import Integer, Rational, div_rem_euclid, gcd as integer_gcd, inverse_mod, isqrt
from .coefficients import ModInt, Modulus, NoContext, QQ, ZZ, _prime, _work
from .errors import Budget, PolyError, PolyErrorKind, _allocation
from .monomial import MonomialOrder
from .sparse import SparsePoly, Term
from .primes import _residue
from ._images import _denominator, _scaled_integer
from ._packed_groebner import _Buckets, _Engine, _Packed, _Term, _compare, _divides, _equal, _monomial, _pack, _packed, _priorities
from ._f4 import _f4_packed
from ._integer_f4 import _pairs_reduce_to_zero

comptime _PRIME_LIMIT = 4096
"""Primes tried before giving up on reconstruction."""
comptime _CERTIFY_LIMIT = 4
"""Certification attempts before giving up."""
comptime _MISMATCH_LIMIT = 3
"""Consecutive images with other leading monomials before they replace the first."""
comptime _BATCH = 32
"""Primes whose residues are combined in word arithmetic before joining the accumulated values."""


def _next_prime(previous: UInt64, mut budget: Budget) raises PolyError -> UInt64:
    """The largest prime below `previous`, which is odd and above 3."""
    var candidate = previous - 2
    while True:
        budget.charge(1)
        if _prime(candidate, budget):
            return candidate
        candidate -= 2


def _reconstruct(value: Integer, modulus: Integer, bound: Integer, mut budget: Budget) raises PolyError -> Optional[Rational]:
    """The fraction a/b = value modulo `modulus` with |a| <= bound and 0 < b <= bound, if one exists."""
    _work(modulus.magnitude_bit_length() // 8 + 1, modulus.magnitude_bit_length() // 8 + 1, True, budget)
    try:
        var r0 = modulus.copy()
        var r1 = div_rem_euclid(value, modulus)[1].copy()
        var t0 = Integer(0)
        var t1 = Integer(1)
        var stop = bound.magnitude_bit_length() + 128
        while r1 > bound:
            if r1.magnitude_bit_length() > stop:
                # Lehmer: the quotients of the leading 62 bits, while they are
                # certainly the true ones, as one matrix [[a, b], [c, d]]. A
                # batch shortens r1 by less than 128 bits, so every remainder
                # it skips stays above the bound.
                var shift = Integer(r0.magnitude_bit_length() - 62)
                var x = Int(r0 >> shift)
                var y = Int(r1 >> shift)
                var a = 1
                var b = 0
                var c = 0
                var d = 1
                while y + c != 0 and y + d != 0:
                    var q = (x + a) // (y + c)
                    if q != (x + b) // (y + d):
                        break
                    var t = a - q * c
                    a = c
                    c = t
                    t = b - q * d
                    b = d
                    d = t
                    t = x - q * y
                    x = y
                    y = t
                if b != 0:
                    var next_r0 = r0 * Integer(a) + r1 * Integer(b)
                    r1 = r0 * Integer(c) + r1 * Integer(d)
                    r0 = next_r0^
                    var next_t0 = t0 * Integer(a) + t1 * Integer(b)
                    t1 = t0 * Integer(c) + t1 * Integer(d)
                    t0 = next_t0^
                    continue
            var qr = div_rem_euclid(r0, r1)
            var t2 = t0 - qr[0] * t1
            r0 = r1^
            r1 = qr[1].copy()
            t0 = t1^
            t1 = t2^
        if t1.sign() == 0 or abs(t1) > bound:
            return None
        var a = r1^
        var b = t1^
        if b.sign() < 0:
            a = -a
            b = -b
        if integer_gcd(a, b) != Integer(1):
            return None
        return Rational(a^, b^)
    except e:
        raise PolyError(PolyErrorKind.CAPACITY, String(e))


struct _Images[W: Int](Movable):
    """CRT accumulation of monic modular bases that share their leading monomials.

    Residues wait as words in batches of up to `_BATCH` primes. A batch is
    combined by Garner's algorithm in word arithmetic and joins the
    accumulated values in one step, so the large values are touched once per
    batch rather than once per prime.
    """
    var kind: UInt8
    var leads: List[_Packed[Self.W]]
    var monomials: List[List[_Packed[Self.W]]]
    """Each element's monomials so far, in increasing order."""
    var values: List[List[Integer]]
    """Each coefficient modulo `modulus`, in [0, modulus)."""
    var modulus: Integer
    """The product of the primes whose residues have joined `values`."""
    var batch: List[UInt64]
    """The primes whose residues still wait."""
    var residues: List[List[UInt32]]
    """Each element's waiting residues, `_BATCH` slots per coefficient."""
    var count: Int
    var probe: Tuple[Int, Int]
    """The coefficient that last failed to reconstruct, tried first next time."""

    def __init__(out self, kind: UInt8):
        self.kind = kind
        self.leads = List[_Packed[Self.W]]()
        self.monomials = List[List[_Packed[Self.W]]]()
        self.values = List[List[Integer]]()
        self.modulus = Integer(1)
        self.batch = List[UInt64]()
        self.residues = List[List[UInt32]]()
        self.count = 0
        self.probe = (0, 0)

    def matches(self, basis: List[List[_Term[ModInt, Self.W]]]) -> Bool:
        if len(basis) != len(self.leads):
            return False
        for i in range(len(basis)):
            if not _equal(basis[i][len(basis[i]) - 1].monomial, self.leads[i]):
                return False
        return True

    def reset(mut self):
        self.leads = List[_Packed[Self.W]]()
        self.monomials = List[List[_Packed[Self.W]]]()
        self.values = List[List[Integer]]()
        self.modulus = Integer(1)
        self.batch = List[UInt64]()
        self.residues = List[List[UInt32]]()
        self.count = 0
        self.probe = (0, 0)

    def _cover(mut self, e: Int, image: List[_Term[ModInt, Self.W]], mut budget: Budget) raises PolyError:
        """Give element e every monomial of the image, new ones with value and residues zero."""
        var missing = 0
        var i = 0
        for j in range(len(image)):
            budget.charge(1)
            while i < len(self.monomials[e]) and _compare(self.kind, self.monomials[e][i], image[j].monomial) < 0:
                i += 1
            if i < len(self.monomials[e]) and _equal(self.monomials[e][i], image[j].monomial):
                i += 1
            else:
                missing += 1
        if missing == 0:
            return
        var n = len(self.monomials[e]) + missing
        _allocation[Integer](n, budget)
        _allocation[UInt32](n * _BATCH, budget)
        var monomials = List[_Packed[Self.W]](capacity=n)
        var values = List[Integer](capacity=n)
        var residues = List[UInt32](capacity=n * _BATCH)
        i = 0
        var j = 0
        while i < len(self.monomials[e]) or j < len(image):
            budget.charge(1)
            var comparison: Int
            if j == len(image):
                comparison = -1
            elif i == len(self.monomials[e]):
                comparison = 1
            else:
                comparison = _compare(self.kind, self.monomials[e][i], image[j].monomial)
            if comparison <= 0:
                monomials.append(self.monomials[e][i])
                values.append(self.values[e][i].copy())
                for slot in range(_BATCH):
                    residues.append(self.residues[e][i * _BATCH + slot])
                i += 1
                if comparison == 0:
                    j += 1
            else:
                monomials.append(image[j].monomial)
                values.append(Integer(0))
                for _ in range(_BATCH):
                    residues.append(0)
                j += 1
        self.monomials[e] = monomials^
        self.values[e] = values^
        self.residues[e] = residues^

    def add(mut self, basis: List[List[_Term[ModInt, Self.W]]], p: UInt64, mut budget: Budget) raises PolyError:
        """Add one image: its residues wait in the batch, over the union of supports."""
        if self.count == 0:
            for element in basis:
                self.leads.append(element[len(element) - 1].monomial)
                self.monomials.append(List[_Packed[Self.W]]())
                self.values.append(List[Integer]())
                self.residues.append(List[UInt32]())
        var slot = len(self.batch)
        for e in range(len(basis)):
            ref image = basis[e]
            self._cover(e, image, budget)
            # The image's monomials are now among the element's; both increase.
            var i = 0
            for j in range(len(image)):
                while not _equal(self.monomials[e][i], image[j].monomial):
                    budget.charge(1)
                    i += 1
                self.residues[e][i * _BATCH + slot] = UInt32(image[j].coefficient.value)
        self.batch.append(p)
        self.count += 1
        if len(self.batch) == _BATCH:
            self._flush(budget)

    def _batch_modulus(self, mut budget: Budget) raises PolyError -> Integer:
        var q = Integer(1)
        for prime in self.batch:
            _work(q.magnitude_bit_length() // 8 + 1, 8, False, budget)
            try:
                q = q * Integer(prime)
            except e:
                raise PolyError(PolyErrorKind.CAPACITY, String(e))
        return q^

    def _garner_inverses(self, mut budget: Budget) raises PolyError -> List[UInt64]:
        """For each batch prime, the inverse modulo it of the product of the primes before it."""
        var b = len(self.batch)
        var inverses = List[UInt64](length=b, fill=1)
        for j in range(1, b):
            var prime = self.batch[j]
            var product = UInt64(1)
            for i in range(j):
                budget.charge(1)
                product = (product * (self.batch[i] % prime)) % prime
            inverses[j] = ModInt(product, Modulus(_prime_value=prime)).inverse(budget).value
        return inverses^

    def _garner(self, e: Int, k: Int, inverses: List[UInt64], mut budget: Budget) raises PolyError -> Integer:
        """The waiting residues of coefficient k of element e, combined modulo the batch's product.

        The mixed-radix digits d_j, with value d_0 + p_0 (d_1 + p_1 (d_2 + ...)),
        need only word arithmetic: every product is below 2^62.
        """
        var b = len(self.batch)
        budget.charge(UInt64(b * b))
        var digits = List[UInt64](length=b, fill=0)
        for j in range(b):
            var prime = self.batch[j]
            var known = UInt64(0)
            for i in range(j - 1, -1, -1):
                known = (known * (self.batch[i] % prime) + digits[i]) % prime
            var residue = UInt64(self.residues[e][k * _BATCH + j])
            digits[j] = ((residue + prime - known) % prime) * inverses[j] % prime
        # Horner in 64-bit limbs, least significant first.
        var limbs = List[UInt64](length=b // 2 + 2, fill=0)
        limbs[0] = digits[b - 1]
        var used = 1
        for i in range(b - 2, -1, -1):
            var carry = UInt128(digits[i])
            for l in range(used):
                var x = UInt128(limbs[l]) * UInt128(self.batch[i]) + carry
                limbs[l] = UInt64(x & UInt128(UInt64.MAX))
                carry = x >> 64
            if carry:
                limbs[used] = UInt64(carry)
                used += 1
        var bytes = List[UInt8](capacity=8 * used)
        for l in range(used):
            for shift in range(8):
                bytes.append(UInt8((limbs[l] >> UInt64(8 * shift)) & 0xFF))
        return Integer.from_bytes(bytes)

    def _joined(self, value: Integer, waiting: Integer, q: Integer, inverse: Integer, mut budget: Budget) raises PolyError -> Integer:
        """The number below modulus * q congruent to value modulo `modulus` and to waiting modulo q."""
        _work(self.modulus.magnitude_bit_length() // 8 + 1, q.magnitude_bit_length() // 8 + 1, True, budget)
        try:
            var t = div_rem_euclid((waiting - div_rem_euclid(value, q)[1]) * inverse, q)[1].copy()
            return value + self.modulus * t
        except e:
            raise PolyError(PolyErrorKind.CAPACITY, String(e))

    def _inverse(self, q: Integer) raises PolyError -> Integer:
        """The inverse of `modulus` modulo q."""
        try:
            return inverse_mod(div_rem_euclid(self.modulus, q)[1], q)
        except e:
            raise PolyError(PolyErrorKind.CAPACITY, String(e))

    def _flush(mut self, mut budget: Budget) raises PolyError:
        """Join the waiting residues to the accumulated values."""
        if len(self.batch) == 0:
            return
        var q = self._batch_modulus(budget)
        var inverses = self._garner_inverses(budget)
        var inverse = self._inverse(q)
        for e in range(len(self.values)):
            for k in range(len(self.values[e])):
                var waiting = self._garner(e, k, inverses, budget)
                self.values[e][k] = self._joined(self.values[e][k], waiting, q, inverse, budget)
            for i in range(len(self.residues[e])):
                self.residues[e][i] = 0
        try:
            self.modulus = self.modulus * q
        except e:
            raise PolyError(PolyErrorKind.CAPACITY, String(e))
        self.batch.clear()

    def _probe_ready(self, mut budget: Budget) raises PolyError -> Bool:
        """Whether the probe coefficient, with the waiting residues, has a small enough fraction."""
        var pe = self.probe[0]
        var pk = self.probe[1]
        if pe >= len(self.values) or pk >= len(self.values[pe]):
            return True
        var q = self._batch_modulus(budget)
        var value = self.values[pe][pk].copy()
        if len(self.batch):
            value = self._joined(value, self._garner(pe, pk, self._garner_inverses(budget), budget), q, self._inverse(q), budget)
        var total: Integer
        var bound: Integer
        try:
            total = self.modulus * q
            bound = isqrt(total // 2)
        except e:
            raise PolyError(PolyErrorKind.CAPACITY, String(e))
        return Bool(_reconstruct(value, total, bound, budget))

    def reconstruct(mut self, mut budget: Budget) raises PolyError -> Optional[List[List[_Term[QQ, Self.W]]]]:
        """Every coefficient as a fraction, or None when one has no small enough fraction yet.

        The coefficient that failed last time is tried first, so an attempt
        that is still too early costs one reconstruction and leaves the batch
        waiting.
        """
        if not self._probe_ready(budget):
            return None
        self._flush(budget)
        var bound: Integer
        try:
            bound = isqrt(self.modulus // 2)
        except e:
            raise PolyError(PolyErrorKind.CAPACITY, String(e))
        var half: Integer
        try:
            half = self.modulus // 2
        except e:
            raise PolyError(PolyErrorKind.CAPACITY, String(e))
        var result = List[List[_Term[QQ, Self.W]]](capacity=len(self.leads))
        for e in range(len(self.leads)):
            # A running common denominator: a coefficient whose value times it
            # is small needs no Euclidean reconstruction of its own.
            var denominator = Integer(1)
            var terms = List[_Term[QQ, Self.W]]()
            for k in range(len(self.monomials[e])):
                budget.charge(1)
                _work(self.modulus.magnitude_bit_length() // 8 + 1, denominator.magnitude_bit_length() // 8 + 1, True, budget)
                var numerator: Integer
                try:
                    numerator = div_rem_euclid(self.values[e][k] * denominator, self.modulus)[1].copy()
                    if numerator > half:
                        numerator -= self.modulus
                except err:
                    raise PolyError(PolyErrorKind.CAPACITY, String(err))
                if abs(numerator) > bound:
                    var fraction = _reconstruct(numerator, self.modulus, bound, budget)
                    if not fraction:
                        self.probe = (e, k)
                        return None
                    var f = fraction.take()
                    try:
                        denominator = denominator * f.denominator()
                    except err:
                        raise PolyError(PolyErrorKind.CAPACITY, String(err))
                    if denominator > bound:
                        self.probe = (e, k)
                        return None
                    numerator = f.numerator().copy()
                if numerator.sign() != 0:
                    var value: Rational
                    try:
                        value = Rational(numerator^, denominator.copy())
                    except err:
                        raise PolyError(PolyErrorKind.CAPACITY, String(err))
                    _allocation[_Term[QQ, Self.W]](1, budget)
                    terms.append(_Term[QQ, Self.W](self.monomials[e][k], QQ(value^)))
            result.append(terms^)
        return result^


def _agrees[W: Int](kind: UInt8, candidate: List[List[_Term[QQ, W]]], basis: List[List[_Term[ModInt, W]]], p: UInt64, mut budget: Budget) raises PolyError -> Bool:
    """Whether the candidate reduces modulo p to the image, coefficient by coefficient."""
    if len(candidate) != len(basis):
        return False
    for e in range(len(basis)):
        ref c = candidate[e]
        ref image = basis[e]
        var i = 0
        var j = 0
        while i < len(c) or j < len(image):
            budget.charge(1)
            var comparison: Int
            if i == len(c):
                comparison = 1
            elif j == len(image):
                comparison = -1
            else:
                comparison = _compare(kind, image[j].monomial, c[i].monomial)
            if comparison > 0:
                return False  # The image has a monomial the candidate lacks.
            var residue = UInt64(0)
            if comparison == 0:
                residue = image[j].coefficient.value
                j += 1
            ref fraction = c[i].coefficient.value
            var numerator = _residue(fraction.numerator(), p, budget)
            var denominator = _residue(fraction.denominator(), p, budget)
            if denominator == 0:
                return False
            if numerator != UInt64((UInt128(denominator) * UInt128(residue)) % UInt128(p)):
                return False
            i += 1
    return True


def _integral[W: Int](p: List[_Term[QQ, W]], mut budget: Budget) raises PolyError -> List[_Term[ZZ, W]]:
    """p times the least common denominator of its coefficients."""
    var common = Integer(1)
    for t in p:
        budget.charge(1)
        common = _denominator(common, t.coefficient, budget)
    _allocation[_Term[ZZ, W]](len(p), budget)
    var terms = List[_Term[ZZ, W]](capacity=len(p))
    for t in p:
        budget.charge(1)
        terms.append(_Term[ZZ, W](t.monomial, _scaled_integer(t.coefficient, common, budget)))
    return terms^


def _copy[W: Int](p: List[_Term[ZZ, W]], mut budget: Budget) raises PolyError -> List[_Term[ZZ, W]]:
    _allocation[_Term[ZZ, W]](len(p), budget)
    var terms = List[_Term[ZZ, W]](capacity=len(p))
    for t in p:
        terms.append(_Term[ZZ, W](t.monomial, t.coefficient.copy()))
    return terms^


def _certify[W: Int](kind: UInt8, inputs: List[List[_Term[ZZ, W]]], candidate: List[List[_Term[ZZ, W]]], mut budget: Budget) raises PolyError -> Bool:
    """Checks (a), (b), and (d) of the module proof; (c) holds by construction."""
    var engine = _Engine[ZZ, W, True](kind, NoContext())
    for g in candidate:
        budget.charge(1)
        if len(g) == 0:
            return False
        engine.insert(_copy(g, budget), budget)
    if len(engine.active) != len(candidate):
        return False  # Some leading monomial divides another.
    engine.sort_active(budget)
    # (d) Reduced: no tail monomial is divisible by a leading monomial.
    for g in candidate:
        for k in range(len(g) - 1):
            for i in engine.active:
                budget.charge(1)
                if _divides(engine.leads[i], g[k].monomial):
                    return False
    # (a) Every input reduces to zero.
    for f in inputs:
        budget.charge(1)
        var pending = _Buckets[ZZ, W, True](kind, NoContext())
        pending.add(_copy(f, budget), budget)
        if not engine.reduces_to_zero(pending^, engine.active, budget):
            return False
    # (b) Every remaining S-pair reduces to zero.
    return _pairs_reduce_to_zero(engine, budget)


def _monic[W: Int](p: List[_Term[ZZ, W]], order: MonomialOrder, by_index: List[Int], mut budget: Budget) raises PolyError -> SparsePoly[QQ]:
    """A primitive integer polynomial divided by its leading coefficient."""
    ref lead = p[len(p) - 1].coefficient.value
    _allocation[Term[QQ]](len(p), budget)
    var monic = SparsePoly[QQ].zero(order, NoContext(), budget)
    monic.terms.reserve(len(p))
    for t in p:
        budget.charge(1)
        _work(t.coefficient.size(), p[len(p) - 1].coefficient.size(), True, budget)
        var value: Rational
        try:
            value = Rational(t.coefficient.value.copy(), lead.copy())
        except e:
            raise PolyError(PolyErrorKind.CAPACITY, String(e))
        monic.terms.append(Term[QQ](_monomial(t.monomial, order, by_index, budget), QQ(value^)))
    return monic^


def _exact[W: Int](inputs: List[List[_Term[ZZ, W]]], kind: UInt8, mut budget: Budget) raises PolyError -> List[List[_Term[ZZ, W]]]:
    """The reduced basis by fraction-free Buchberger."""
    var engine = _Engine[ZZ, W, True](kind, NoContext())
    var copies = List[List[_Term[ZZ, W]]]()
    for f in inputs:
        copies.append(_copy(f, budget))
    engine.start(copies^, budget)
    var dirty_order = True
    while len(engine.pairs):
        budget.charge(1)
        var pair = engine.select(budget)
        if dirty_order:
            engine.sort_active(budget)
            dirty_order = False
        var reduced = engine.reduce_pair(pair, budget)
        if len(reduced) == 0:
            continue
        engine.insert(reduced^, budget)
        dirty_order = True
    return engine.finish(budget)


def _multimodular[W: Int](inputs: List[List[_Term[ZZ, W]]], kind: UInt8, mut budget: Budget) raises PolyError -> Optional[List[List[_Term[ZZ, W]]]]:
    """The certified reduced basis of homogeneous inputs, or None when reconstruction gives up."""
    # Leading coefficients, which an admissible prime must not divide.
    var leads = List[Integer]()
    for f in inputs:
        leads.append(f[len(f) - 1].coefficient.value.copy())
    var images = _Images[W](kind)
    var candidate = Optional[List[List[_Term[QQ, W]]]](None)
    var mismatches = 0
    var certifications = 0
    var attempt = 1
    var p = (UInt64(1) << 31) + 1
    for _ in range(_PRIME_LIMIT):
        budget.charge(1)
        p = _next_prime(p, budget)
        var admissible = True
        for c in leads:
            if _residue(c, p, budget) == 0:
                admissible = False
                break
        if not admissible:
            continue
        var ring = Modulus(_prime_value=p)
        var reduced = List[List[_Term[ModInt, W]]](capacity=len(inputs))
        for f in inputs:
            _allocation[_Term[ModInt, W]](len(f), budget)
            var terms = List[_Term[ModInt, W]](capacity=len(f))
            for t in f:
                budget.charge(1)
                # Euclidean residues are already in [0, p), for negative values too.
                var r = _residue(t.coefficient.value, p, budget)
                if r != 0:
                    terms.append(_Term[ModInt, W](t.monomial, ModInt(r, ring)))
            reduced.append(terms^)
        var basis = _f4_packed[W](reduced^, kind, ring, budget)
        if images.count > 0 and not images.matches(basis):
            mismatches += 1
            if mismatches < _MISMATCH_LIMIT:
                continue
            # The first images were likely the unlucky ones: start over from this one.
            images.reset()
            candidate = None
            attempt = 1
        mismatches = 0
        if candidate:
            if _agrees(kind, candidate.value(), basis, p, budget):
                certifications += 1
                var proposal = List[List[_Term[ZZ, W]]]()
                for g in candidate.value():
                    proposal.append(_integral(g, budget))
                if _certify(kind, inputs, proposal, budget):
                    return proposal^
                if certifications >= _CERTIFY_LIMIT:
                    return None
            candidate = None
        images.add(basis, p, budget)
        var count = images.count
        if count >= attempt:
            candidate = images.reconstruct(budget)
            # After 1, 2, 4, and 8 images, every 8 up to 64, then every eighth
            # more: a failed attempt costs at least one reconstruction of a
            # coefficient as large as the modulus.
            attempt = 2 * count if count < 8 else count + max(8, count // 8)
    return None




def _rational_basis[W: Int](generators: List[SparsePoly[QQ]], order: MonomialOrder, exact: Bool, mut budget: Budget) raises PolyError -> List[SparsePoly[QQ]]:
    var n = len(order.variables)
    var kind = order.kind
    # Primitive integer inputs, in the order's lanes; h, if needed, is lane n.
    var inputs = List[List[_Term[ZZ, W]]]()
    var homogeneous = True
    for g in generators:
        budget.charge(1)
        if g.is_zero():
            continue
        var rational = _pack[QQ, W](g.reorder(order, budget), order, budget)
        var integral = _integral(rational, budget)
        var degree = integral[len(integral) - 1].monomial.degree
        for t in integral:
            if t.monomial.degree != degree:
                homogeneous = False
        inputs.append(integral^)
    if len(inputs) == 0:
        return List[SparsePoly[QQ]]()
    if not homogeneous:
        # Under GREVLEX the leading term has the greatest degree, and adding h
        # keeps the order of every polynomial's terms.
        for f in range(len(inputs)):
            var degree = inputs[f][len(inputs[f]) - 1].monomial.degree
            for k in range(len(inputs[f])):
                budget.charge(1)
                var exponents = inputs[f][k].monomial.exponents()
                exponents[n] = UInt32(degree - inputs[f][k].monomial.degree)
                inputs[f][k].monomial = _packed(exponents)
    # By certified reconstruction, and exactly if that gives up.
    if not exact:
        var modular = _multimodular[W](inputs, kind, budget)
        if modular:
            return _finish(modular.take(), homogeneous, n, order, budget)
    return _finish(_exact[W](inputs, kind, budget), homogeneous, n, order, budget)


def _finish[W: Int](var basis: List[List[_Term[ZZ, W]]], homogeneous: Bool, n: Int, order: MonomialOrder, mut budget: Budget) raises PolyError -> List[SparsePoly[QQ]]:
    """The reduced basis of the input ideal from the certified basis, as monic rational polynomials."""
    var by_index = _priorities(order, budget)
    var result = List[SparsePoly[QQ]]()
    if homogeneous:
        for p in basis:
            budget.charge(1)
            result.append(_monic(p, order, by_index, budget))
        return result^
    # Set h = 1. Distinct terms of a homogeneous polynomial differ off lane n,
    # and their order is unchanged.
    for e in range(len(basis)):
        for k in range(len(basis[e])):
            budget.charge(1)
            var exponents = basis[e][k].monomial.exponents()
            exponents[n] = 0
            basis[e][k].monomial = _packed(exponents)
    # Keep the elements whose leading monomial no other one divides, then reduce tails.
    var engine = _Engine[ZZ, W, True](order.kind, NoContext())
    for e in range(len(basis)):
        budget.charge(1)
        var lead = basis[e][len(basis[e]) - 1].monomial
        var redundant = False
        for f in range(len(basis)):
            budget.charge(1)
            if f != e and _divides(basis[f][len(basis[f]) - 1].monomial, lead):
                redundant = True
                break
        if redundant:
            continue
        engine.leads.append(lead)
        engine.active.append(len(engine.polys))
        engine.polys.append(_copy(basis[e], budget))
    var reduced = engine.finish(budget)
    for p in reduced:
        budget.charge(1)
        result.append(_monic(p, order, by_index, budget))
    return result^


def _grevlex_supported(order: MonomialOrder) -> Bool:
    """GREVLEX over at most fifteen variables, leaving a lane for h."""
    return order.kind == MonomialOrder.GREVLEX and len(order.variables) + 1 <= 16


def _grevlex_groebner_rational(generators: List[SparsePoly[QQ]], order: MonomialOrder, mut budget: Budget, exact: Bool = False) raises PolyError -> List[SparsePoly[QQ]]:
    """The reduced monic basis over QQ under a supported GREVLEX order.

    By certified reconstruction unless `exact`, which tests use to exercise
    the exact computation that reconstruction falls back on.
    """
    if len(order.variables) + 1 <= 8:
        return _rational_basis[8](generators, order, exact, budget)
    return _rational_basis[16](generators, order, exact, budget)
