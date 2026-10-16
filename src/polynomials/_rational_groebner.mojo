"""Gröbner bases over QQ under GREVLEX, through the homogenized inputs.

The inputs become primitive integer polynomials, homogenized with a new least
variable h (GREVLEX with h last) unless they are homogeneous already. The
reduced basis of their ideal J is reconstructed from modular images and
certified, and setting h = 1 then gives the basis of the input ideal.

1. Images. Modulo each prime below 2^31 that divides no leading coefficient,
   F4 computes the reduced basis of the image of J. The first prime's run
   is recorded and later primes replay its matrices, `_LANES` primes at a
   time, one per SIMD lane; a prime whose replay declines is computed in
   full and recorded instead, and the primes after it replay the new run.
   Images whose leading monomials differ from the first one's are set
   aside.
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
from .errors import Budget, PolyError, PolyErrorKind, _allocation, _product
from .monomial import MonomialOrder
from .sparse import SparsePoly, Term
from .primes import _residue
from ._images import _denominator, _scaled_integer
from ._packed_groebner import _Buckets, _Engine, _Packed, _Term, _compare, _divides, _equal, _monomial, _pack, _packed, _priorities
from ._f4 import _LANES, _Matrix, _Store, _Trace, _f4_learn, _f4_replay, _f4_replay_lanes
from ._integer_f4 import _add_mul_1, _divide, _pairs_reduce_to_zero, _reduced_tails, _remainder, _sub_mul_1

comptime _PRIME_LIMIT = 4096
"""Primes tried before giving up on reconstruction."""
comptime _CERTIFY_LIMIT = 4
"""Certification attempts before giving up."""
comptime _MISMATCH_LIMIT = 3
"""Consecutive images with other leading monomials before they replace the first."""
comptime _PROBES = 16
"""Elements whose least coefficient is tried before a full reconstruction."""
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


struct _Crt(Movable):
    """A batch's CRT basis. For primes p_i with product Q, Q_i = Q / p_i and
    c_i = Q_i^-1 modulo p_i, the residues r_i give x = sum r_i e_i - k Q with
    e_i = c_i Q_i and k = floor(sum r_i c_i / p_i), so a value takes word
    multiples of the basis and one word multiple of Q, in limbs."""
    var product: List[UInt64]
    var basis: List[UInt64]
    """The e_i, `limbs` limbs each."""
    var weights: List[Float64]
    """The c_i / p_i, whose sum against the residues estimates k."""
    var limbs: Int
    var work: List[UInt64]

    def __init__(out self, primes: List[UInt64], mut budget: Budget) raises PolyError:
        var b = len(primes)
        self.product = [UInt64(1)]
        for prime in primes:
            budget.charge(UInt64(len(self.product)))
            var carry = UInt128(0)
            for l in range(len(self.product)):
                var x = UInt128(self.product[l]) * UInt128(prime) + carry
                self.product[l] = UInt64(x & UInt128(UInt64.MAX))
                carry = x >> 64
            if carry:
                self.product.append(UInt64(carry))
        self.limbs = len(self.product)
        _allocation[UInt64](_product(b, self.limbs) + self.limbs + 2, budget)
        self.basis = List[UInt64](length=b * self.limbs, fill=0)
        self.weights = List[Float64](capacity=b)
        self.work = List[UInt64](length=self.limbs + 2, fill=0)
        for i in range(b):
            var prime = primes[i]
            budget.charge(UInt64(3 * self.limbs))
            var cofactor = self.product.copy()
            _divide(cofactor, prime)
            var c = ModInt(_remainder(cofactor, prime), Modulus(_prime_value=prime)).inverse(budget).value
            var carry = UInt128(0)
            for l in range(self.limbs):
                var x = (UInt128(cofactor[l]) if l < len(cofactor) else UInt128(0)) * UInt128(c) + carry
                self.basis[i * self.limbs + l] = UInt64(x & UInt128(UInt64.MAX))
                carry = x >> 64
            self.weights.append(Float64(c) / Float64(prime))

    def value(mut self, residues: List[UInt32], start: Int, b: Int, mut budget: Budget) raises PolyError -> Integer:
        """The number below Q with the residues residues[start : start + b]."""
        budget.charge(UInt64(_product(b, self.limbs)))
        var n = self.limbs + 2
        var work = self.work.unsafe_ptr()
        for l in range(n):
            work.unsafe_offset(l).unsafe_store(0)
        var estimate = Float64(0)
        for i in range(b):
            var r = residues.unsafe_get(start + i)
            if r == 0:
                continue
            _add_mul_1(work, n, UInt64(r), self.basis.unsafe_ptr().unsafe_offset(i * self.limbs), self.limbs)
            estimate += Float64(r) * self.weights.unsafe_get(i)
        # The estimate's error is far below one, so one correction at most remains.
        var k = UInt64(estimate)
        if k:
            _sub_mul_1(work, n, k, self.product.unsafe_ptr(), self.limbs)
        while (work.unsafe_offset(n - 1).unsafe_load() >> 63) != 0:
            _add_mul_1(work, n, 1, self.product.unsafe_ptr(), self.limbs)
        while not self._below_product():
            _sub_mul_1(work, n, 1, self.product.unsafe_ptr(), self.limbs)
        var bytes = List[UInt8](length=8 * self.limbs, fill=0)
        for l in range(self.limbs):
            var limb = work.unsafe_offset(l).unsafe_load()
            comptime for shift in range(8):
                bytes.unsafe_get(8 * l + shift) = UInt8((limb >> UInt64(8 * shift)) & 0xFF)
        return Integer.from_bytes(bytes)

    def _below_product(self) -> Bool:
        """Whether the nonnegative accumulator is below Q."""
        var n = self.limbs + 2
        for l in range(n - 1, self.limbs - 1, -1):
            if self.work.unsafe_get(l) != 0:
                return False
        for l in range(self.limbs - 1, -1, -1):
            var x = self.work.unsafe_get(l)
            var y = self.product.unsafe_get(l)
            if x != y:
                return x < y
        return False


struct _Images[W: Int](Movable):
    """CRT accumulation of monic modular bases that share their leading monomials.

    Residues wait as words in batches of up to `_BATCH` primes. A batch is
    combined through its CRT basis in word multiples (`_Crt`) and joins the
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
        var crt = _Crt(self.batch, budget)
        var first = self.modulus == Integer(1)
        var inverse = Integer(1) if first else self._inverse(q)
        var b = len(self.batch)
        for e in range(len(self.values)):
            for k in range(len(self.values[e])):
                var waiting = crt.value(self.residues[e], k * _BATCH, b, budget)
                if first:
                    self.values[e][k] = waiting^
                else:
                    self.values[e][k] = self._joined(self.values[e][k], waiting, q, inverse, budget)
            for i in range(len(self.residues[e])):
                self.residues[e][i] = 0
        try:
            self.modulus = self.modulus * q
        except e:
            raise PolyError(PolyErrorKind.CAPACITY, String(e))
        self.batch.clear()

    def _probe_ready(mut self, mut budget: Budget) raises PolyError -> Bool:
        """Whether some probe coefficients, with the waiting residues, have small enough fractions.

        The probes are the coefficient that failed last time and the least
        term of a spread of elements; one that fails becomes the next probe.
        """
        var waiting = len(self.batch) > 0
        var q = self._batch_modulus(budget)
        var crt = _Crt(self.batch, budget)
        var inverse = self._inverse(q) if waiting else Integer(1)
        var total: Integer
        var bound: Integer
        try:
            total = self.modulus * q
            bound = isqrt(total // 2)
        except e:
            raise PolyError(PolyErrorKind.CAPACITY, String(e))
        var probes: List[Tuple[Int, Int]] = [self.probe]
        for e in range(0, len(self.values), max(1, len(self.values) // _PROBES)):
            probes.append((e, 0))
        for probe in probes:
            var pe = probe[0]
            var pk = probe[1]
            if pe >= len(self.values) or pk >= len(self.values[pe]):
                continue
            var value = self.values[pe][pk].copy()
            if waiting:
                value = self._joined(value, crt.value(self.residues[pe], pk * _BATCH, len(self.batch), budget), q, inverse, budget)
            if not _reconstruct(value, total, bound, budget):
                self.probe = (pe, pk)
                return False
        return True

    def reconstruct(mut self, mut budget: Budget) raises PolyError -> Optional[List[List[_Term[ZZ, Self.W]]]]:
        """Every element, as fractions, times the least common denominator of its coefficients; None when a coefficient has no small enough fraction yet.

        Probe coefficients are tried first, so an attempt that is still too
        early costs a few reconstructions and leaves the batch waiting.
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
        var result = List[List[_Term[ZZ, Self.W]]](capacity=len(self.leads))
        for e in range(len(self.leads)):
            # A running common denominator: a coefficient whose value times it
            # is small needs no Euclidean reconstruction of its own. Each
            # numerator is over the denominator of its time; `changes` marks
            # where the denominator grew, and to what.
            var denominator = Integer(1)
            var numerators = List[Integer](capacity=len(self.monomials[e]))
            var changes = List[Int]()
            var denominators = List[Integer]()
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
                    changes.append(k)
                    denominators.append(denominator.copy())
                numerators.append(numerator^)
            # Over the final denominator: numerators before a change lack the
            # factors that came later.
            _allocation[_Term[ZZ, Self.W]](len(numerators), budget)
            var terms = List[_Term[ZZ, Self.W]](capacity=len(numerators))
            var segment = -1
            var factor = Integer(1)
            for k in range(len(numerators)):
                budget.charge(1)
                if segment + 1 < len(changes) and changes[segment + 1] == k:
                    segment += 1
                    try:
                        factor = denominator // denominators[segment]
                    except err:
                        raise PolyError(PolyErrorKind.CAPACITY, String(err))
                elif segment < 0 and k == 0:
                    factor = denominator.copy()
                if numerators[k].sign() == 0:
                    continue
                var value: Integer
                try:
                    value = numerators[k] * factor
                except err:
                    raise PolyError(PolyErrorKind.CAPACITY, String(err))
                terms.append(_Term[ZZ, Self.W](self.monomials[e][k], ZZ(value^)))
            result.append(terms^)
        return result^


def _agrees[W: Int](kind: UInt8, candidate: List[List[_Term[ZZ, W]]], basis: List[List[_Term[ModInt, W]]], p: UInt64, mut budget: Budget) raises PolyError -> Bool:
    """Whether the integral candidate is, modulo p, its leading coefficient times the monic image, coefficient by coefficient."""
    if len(candidate) != len(basis):
        return False
    for e in range(len(basis)):
        ref c = candidate[e]
        ref image = basis[e]
        var lead = _residue(c[len(c) - 1].coefficient.value, p, budget)
        if lead == 0:
            return False
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
            if _residue(c[i].coefficient.value, p, budget) != UInt64((UInt128(lead) * UInt128(residue)) % UInt128(p)):
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
        engine.insert(_copy(g, budget), budget, heap=False)
    if len(engine.active) != len(candidate):
        return False  # Some leading monomial divides another.
    engine.heapify_pairs(budget)
    engine.sort_active(budget)
    # (d) Reduced: no tail monomial is divisible by a leading monomial. As
    # rows of one F4 matrix, numbering each distinct monomial once, no tail
    # column may be a leading one, and symbolic preprocessing must find no
    # reducer for any other.
    var store = _Store[W]()
    store.extend(engine, budget)
    var matrix = _Matrix[W]()
    var one = _Packed[W](SIMD[DType.uint32, W](0), 0, 0)
    for i in engine.active:
        matrix.add_row(engine, store, i, one, budget)
    var rows = len(matrix.sources)
    budget.charge(UInt64(len(matrix.entries)))
    for r in range(rows):
        for k in range(matrix.starts[r] + 1, matrix.starts[r + 1]):
            if matrix.columns.covered[Int(matrix.entries[k])]:
                return False
    matrix.preprocess(engine, store, budget)
    if len(matrix.sources) != rows:
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


def _admissible[W: Int](inputs: List[List[_Term[ZZ, W]]], p: UInt64, mut budget: Budget) raises PolyError -> Bool:
    """Whether p divides no input's leading coefficient."""
    for f in inputs:
        if _residue(f[len(f) - 1].coefficient.value, p, budget) == 0:
            return False
    return True


def _images_of[W: Int](inputs: List[List[_Term[ZZ, W]]], ring: Modulus, mut budget: Budget) raises PolyError -> List[List[_Term[ModInt, W]]]:
    """The inputs modulo the ring's prime."""
    var p = ring.value
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
    return reduced^


def _multimodular[W: Int](inputs: List[List[_Term[ZZ, W]]], kind: UInt8, certify: Bool, mut budget: Budget) raises PolyError -> Optional[List[List[_Term[ZZ, W]]]]:
    """The certified reduced basis of homogeneous inputs, or None when reconstruction gives up.

    Without `certify`, the first candidate that agrees with the next image is
    returned uncertified.
    """
    var images = _Images[W](kind)
    var candidate = Optional[List[List[_Term[ZZ, W]]]](None)
    var mismatches = 0
    var certifications = 0
    var attempt = 1
    # The first prime's F4 run is recorded, and later primes replay it; a
    # prime whose replay departs from it is computed in full and recorded.
    var trace = _Trace[W]()
    var learned = False
    # Replays run `_LANES` primes at once: the images of the primes after
    # this one wait in `ahead`, computed from the same recorded run, and are
    # dropped whenever the run is recorded anew.
    var ahead = List[List[List[_Term[ModInt, W]]]]()
    var ahead_primes = List[UInt64]()
    var p = (UInt64(1) << 31) + 1
    for _ in range(_PRIME_LIMIT):
        budget.charge(1)
        p = _next_prime(p, budget)
        if not _admissible(inputs, p, budget):
            continue
        var ring = Modulus(_prime_value=p)
        var replayed = Optional[List[List[_Term[ModInt, W]]]](None)
        if learned and trace.usable:
            if len(ahead_primes) > 0 and ahead_primes[0] == p:
                replayed = ahead.pop(0)
                _ = ahead_primes.pop(0)
            else:
                # This prime and the next admissible ones, in one batch.
                var rings: List[Modulus] = [ring]
                var batch = List[List[List[_Term[ModInt, W]]]]()
                batch.append(_images_of(inputs, ring, budget))
                var q = p
                while len(rings) < _LANES:
                    q = _next_prime(q, budget)
                    if _admissible(inputs, q, budget):
                        rings.append(Modulus(_prime_value=q))
                        batch.append(_images_of(inputs, rings[len(rings) - 1], budget))
                ahead = _f4_replay_lanes[W](trace, batch^, kind, rings, budget)
                ahead_primes = List[UInt64]()
                for i in range(1, len(ahead)):
                    ahead_primes.append(rings[i].value)
                if len(ahead) > 0:
                    replayed = ahead.pop(0)
        var basis: List[List[_Term[ModInt, W]]]
        if replayed:
            basis = replayed.take()
        else:
            basis = _f4_learn[W](_images_of(inputs, ring, budget), kind, ring, trace, budget)
            learned = True
            ahead = List[List[List[_Term[ModInt, W]]]]()
            ahead_primes = List[UInt64]()
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
                if not certify or _certify(kind, inputs, candidate.value(), budget):
                    return candidate.take()
                if certifications >= _CERTIFY_LIMIT:
                    return None
                # The images may follow an unlucky recorded run: record anew,
                # so that differing leading monomials can show.
                learned = False
                ahead = List[List[List[_Term[ModInt, W]]]]()
                ahead_primes = List[UInt64]()
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




def _rational_basis[W: Int](generators: List[SparsePoly[QQ]], order: MonomialOrder, exact: Bool, certify: Bool, mut budget: Budget) raises PolyError -> List[SparsePoly[QQ]]:
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
        var modular = _multimodular[W](inputs, kind, certify, budget)
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
    var reduced = _reduced_tails(engine, budget)
    for p in reduced:
        budget.charge(1)
        result.append(_monic(p, order, by_index, budget))
    return result^


def _grevlex_supported(order: MonomialOrder) -> Bool:
    """GREVLEX over at most fifteen variables, leaving a lane for h."""
    return order.kind == MonomialOrder.GREVLEX and len(order.variables) + 1 <= 16


def _grevlex_groebner_rational(generators: List[SparsePoly[QQ]], order: MonomialOrder, mut budget: Budget, exact: Bool = False, certify: Bool = True) raises PolyError -> List[SparsePoly[QQ]]:
    """The reduced monic basis over QQ under a supported GREVLEX order.

    By certified reconstruction unless `exact`, which tests use to exercise
    the exact computation that reconstruction falls back on. Without
    `certify` the reconstruction is not certified.
    """
    if len(order.variables) + 1 <= 8:
        return _rational_basis[8](generators, order, exact, certify, budget)
    return _rational_basis[16](generators, order, exact, certify, budget)
