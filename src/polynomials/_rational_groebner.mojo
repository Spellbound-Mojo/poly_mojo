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
2. Reconstruction. The images' residues are kept over the union of their
   supports, and each attempt recovers every coefficient as a fraction
   through a running denominator d per element: the coefficient's lift by
   the Chinese remainder theorem times d must be small, or it is
   reconstructed and d grows. A small product needs only the residues of
   the coefficient times d modulo a prefix of the primes, so a full lift is
   needed only where a denominator shows. A candidate must also agree with
   the next image before it is certified.
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

Uncertified, inhomogeneous inputs are not homogenized: steps 1 and 2 run on
the input ideal itself, whose reduced basis is often many times smaller than
that of J, and the first candidate that agrees with the next image is the
result.
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
from ._f4 import _LANES, _LaneBases, _Matrix, _Store, _Trace, _f4_learn, _f4_replay_bases, _lane_basis
from ._integer_f4 import _add_mul_1, _divide, _magnitude, _pairs_reduce_to_zero, _reduced_tails, _remainder, _sub_mul_1

comptime _PRIME_LIMIT = 4096
"""Primes tried before giving up on reconstruction."""
comptime _CERTIFY_LIMIT = 4
"""Certification attempts before giving up."""
comptime _MISMATCH_LIMIT = 3
"""Consecutive images with other leading monomials before they replace the first."""
comptime _PROBES = 16
"""Elements whose least coefficient is tried before a full reconstruction."""
comptime _BATCH = 32
"""Primes in a block of residues, which combine in word arithmetic (`_Crt`)."""
comptime _TREE = 24
"""Blocks from which a CRT combines them up a product tree, whose large products are subquadratic."""


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
    """A block's CRT basis. For primes p_i with product Q, Q_i = Q / p_i and
    c_i = s Q_i^-1 modulo p_i for a scale s, the residues r_i give
    x = sum r_i e_i - k Q, the number below Q congruent to s times their CRT,
    with e_i = c_i Q_i and k = floor(sum r_i c_i / p_i): word multiples of the
    basis and one word multiple of Q, in limbs."""
    var product: List[UInt64]
    var basis: List[UInt64]
    """The e_i, `limbs` limbs each."""
    var weights: List[Float64]
    """The c_i / p_i, whose sum against the residues estimates k."""
    var limbs: Int

    def __init__(out self, primes: List[UInt64], start: Int, end: Int, scale: Integer, mut budget: Budget) raises PolyError:
        """The basis for primes[start:end]."""
        var b = end - start
        self.product = [UInt64(1)]
        for i in range(start, end):
            var prime = primes[i]
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
        var scaled = List[UInt64]()
        _magnitude(scale, scaled)
        for i in range(b):
            var prime = primes[start + i]
            budget.charge(UInt64(3 * self.limbs + len(scaled)))
            var cofactor = self.product.copy()
            _divide(cofactor, prime)
            var c = ModInt(_remainder(cofactor, prime), Modulus(_prime_value=prime)).inverse(budget).value
            c = UInt64((UInt128(c) * UInt128(_remainder(scaled, prime))) % UInt128(prime))
            var carry = UInt128(0)
            for l in range(self.limbs):
                var x = (UInt128(cofactor[l]) if l < len(cofactor) else UInt128(0)) * UInt128(c) + carry
                self.basis[i * self.limbs + l] = UInt64(x & UInt128(UInt64.MAX))
                carry = x >> 64
            self.weights.append(Float64(c) / Float64(prime))

    def value_into(self, residues: Pointer[mut=False, UInt32, _], target: Pointer[mut=True, UInt64, _]) -> Float64:
        """Write the value for the residues, `limbs` limbs, to target, which has two limbs more; return it divided by Q, approximately."""
        var n = self.limbs + 2
        for l in range(n):
            target.unsafe_offset(l).unsafe_store(0)
        var estimate = Float64(0)
        for i in range(len(self.weights)):
            var r = residues.unsafe_offset(i).unsafe_load()
            if r == 0:
                continue
            _add_mul_1(target, n, UInt64(r), self.basis.unsafe_ptr().unsafe_offset(i * self.limbs), self.limbs)
            estimate += Float64(r) * self.weights.unsafe_get(i)
        # The estimate's error is far below one, so one correction at most remains.
        var k = UInt64(estimate)
        if k:
            _sub_mul_1(target, n, k, self.product.unsafe_ptr(), self.limbs)
        var fraction = estimate - Float64(k)
        while (target.unsafe_offset(n - 1).unsafe_load() >> 63) != 0:
            _add_mul_1(target, n, 1, self.product.unsafe_ptr(), self.limbs)
            fraction += 1
        while not _below(target, n, self.product.unsafe_ptr(), self.limbs):
            _sub_mul_1(target, n, 1, self.product.unsafe_ptr(), self.limbs)
            fraction -= 1
        return fraction


def _below(x: Pointer[mut=False, UInt64, _], n: Int, y: Pointer[mut=False, UInt64, _], m: Int) -> Bool:
    """Whether the nonnegative x of n limbs is below y of m <= n limbs."""
    for l in range(n - 1, m - 1, -1):
        if x.unsafe_offset(l).unsafe_load() != 0:
            return False
    for l in range(m - 1, -1, -1):
        var a = x.unsafe_offset(l).unsafe_load()
        var b = y.unsafe_offset(l).unsafe_load()
        if a != b:
            return a < b
    return False


def _integer(limbs: Pointer[mut=False, UInt64, _], n: Int) -> Integer:
    """The nonnegative number with the n limbs, least significant first."""
    var bytes = List[UInt8](length=8 * n, fill=0)
    for l in range(n):
        var limb = limbs.unsafe_offset(l).unsafe_load()
        comptime for shift in range(8):
            bytes.unsafe_get(8 * l + shift) = UInt8((limb >> UInt64(8 * shift)) & 0xFF)
    return Integer.from_bytes(bytes)


def _end(primes: List[UInt64], b: Int) -> Int:
    """The end of block b in primes."""
    return min(len(primes), (b + 1) * _BATCH)


def _times(a: Integer, b: Integer) raises PolyError -> Integer:
    try:
        return a * b
    except e:
        raise PolyError(PolyErrorKind.CAPACITY, String(e))


struct _Lift(Movable):
    """CRT over the first blocks of `_BATCH` primes, for many values.

    For block products q_b with product M, a value is
    x = sum_b u_b M / q_b - k M, where u_b < q_b is the CRT of block b's
    residues times (M / q_b)^-1 modulo q_b, in word arithmetic (`_Crt`), and
    k = floor(sum_b u_b / q_b), which the blocks' estimates give. Below
    `_TREE` blocks the sum takes word multiples of the M / q_b; from it, it
    combines up a product tree instead: a node's value is its left value
    times its right product plus its right value times its left product.
    """
    var crts: List[_Crt]
    var factors: List[List[UInt64]]
    """The M / q_b in limbs, below `_TREE` blocks."""
    var levels: List[List[Integer]]
    """From `_TREE` blocks, the tree's products from the q_b up; an odd last node is carried up alone."""
    var modulus: Integer
    var product: List[UInt64]
    """M in limbs."""
    var primes: Int
    var digits: List[UInt64]
    var work: List[UInt64]

    def __init__(out self, primes: List[UInt64], blocks: Int, mut budget: Budget) raises PolyError:
        var products = List[Integer]()
        self.modulus = Integer(1)
        self.primes = min(len(primes), blocks * _BATCH)
        for b in range(blocks):
            var q = Integer(1)
            for i in range(b * _BATCH, _end(primes, b)):
                _work(q.magnitude_bit_length() // 8 + 1, 8, False, budget)
                q = _times(q, Integer(primes[i]))
            _work(self.modulus.magnitude_bit_length() // 8 + 1, q.magnitude_bit_length() // 8 + 1, False, budget)
            self.modulus = _times(self.modulus, q)
            products.append(q^)
        self.crts = List[_Crt]()
        self.factors = List[List[UInt64]]()
        self.product = List[UInt64]()
        _magnitude(self.modulus, self.product)
        var width = 0
        for b in range(blocks):
            _work(self.modulus.magnitude_bit_length() // 8 + 1, products[b].magnitude_bit_length() // 8 + 1, True, budget)
            var factor: Integer
            var inverse: Integer
            try:
                factor = self.modulus // products[b]
                inverse = inverse_mod(div_rem_euclid(factor, products[b])[1], products[b])
            except e:
                raise PolyError(PolyErrorKind.CAPACITY, String(e))
            self.crts.append(_Crt(primes, b * _BATCH, _end(primes, b), inverse, budget))
            width = max(width, self.crts[b].limbs)
            if blocks < _TREE:
                var limbs = List[UInt64]()
                _magnitude(factor, limbs)
                self.factors.append(limbs^)
        self.levels = [products^]
        while blocks >= _TREE and len(self.levels[len(self.levels) - 1]) > 1:
            ref below = self.levels[len(self.levels) - 1]
            var level = List[Integer]()
            for i in range(0, len(below), 2):
                if i + 1 < len(below):
                    _work(below[i].magnitude_bit_length() // 8 + 1, below[i + 1].magnitude_bit_length() // 8 + 1, False, budget)
                    level.append(_times(below[i], below[i + 1]))
                else:
                    level.append(below[i].copy())
            self.levels.append(level^)
        _allocation[UInt64](width + len(self.product) + 4, budget)
        self.digits = List[UInt64](length=width + 2, fill=0)
        self.work = List[UInt64](length=len(self.product) + 2, fill=0)

    def value(mut self, residues: List[UInt32], mut budget: Budget) raises PolyError -> Integer:
        """The number below M with the residues, block b's at residues[b * _BATCH:]."""
        if len(self.crts) >= _TREE:
            return self._tree(residues, budget)
        var limbs = len(self.product)
        budget.charge(UInt64(_product(self.primes, limbs + _BATCH)))
        var n = limbs + 2
        var work = self.work.unsafe_ptr()
        for l in range(n):
            work.unsafe_offset(l).unsafe_store(0)
        var digits = self.digits.unsafe_ptr()
        var estimate = Float64(0)
        for b in range(len(self.crts)):
            estimate += self.crts[b].value_into(residues.unsafe_ptr().unsafe_offset(b * _BATCH), digits)
            ref factor = self.factors[b]
            for l in range(self.crts[b].limbs):
                var f = digits.unsafe_offset(l).unsafe_load()
                if f != 0:
                    _add_mul_1(work.unsafe_offset(l), n - l, f, factor.unsafe_ptr(), len(factor))
        var k = UInt64(max(estimate, Float64(0)))
        if k:
            _sub_mul_1(work, n, k, self.product.unsafe_ptr(), limbs)
        while (work.unsafe_offset(n - 1).unsafe_load() >> 63) != 0:
            _add_mul_1(work, n, 1, self.product.unsafe_ptr(), limbs)
        while not _below(work, n, self.product.unsafe_ptr(), limbs):
            _sub_mul_1(work, n, 1, self.product.unsafe_ptr(), limbs)
        return _integer(work, limbs)

    def _tree(mut self, residues: List[UInt32], mut budget: Budget) raises PolyError -> Integer:
        var bytes = self.modulus.magnitude_bit_length() // 8 + 1
        _work(bytes, bytes, False, budget)
        var digits = self.digits.unsafe_ptr()
        var values = List[Integer](capacity=len(self.crts))
        var estimate = Float64(0)
        for b in range(len(self.crts)):
            budget.charge(UInt64(_product(_BATCH, self.crts[b].limbs)))
            estimate += self.crts[b].value_into(residues.unsafe_ptr().unsafe_offset(b * _BATCH), digits)
            values.append(_integer(digits, self.crts[b].limbs))
        try:
            var level = 0
            while len(values) > 1:
                ref products = self.levels[level]
                var combined = List[Integer](capacity=(len(values) + 1) // 2)
                for i in range(0, len(values), 2):
                    if i + 1 < len(values):
                        combined.append(values[i] * products[i + 1] + values[i + 1] * products[i])
                    else:
                        combined.append(values[i].copy())
                values = combined^
                level += 1
            if len(values) == 0:
                return Integer(0)
            var x = values[0] - Integer(Int(max(estimate, Float64(0)))) * self.modulus
            while x.sign() < 0:
                x += self.modulus
            while x >= self.modulus:
                x -= self.modulus
            return x^
        except e:
            raise PolyError(PolyErrorKind.CAPACITY, String(e))


struct _Check(Movable):
    """Residues of limb strings modulo a prime, through the powers of 2^64."""
    var prime: UInt64
    var powers: List[UInt64]

    def __init__(out self, prime: UInt64, limbs: Int, mut budget: Budget) raises PolyError:
        """For limb strings of at most `limbs` limbs."""
        self.prime = prime
        _allocation[UInt64](limbs, budget)
        self.powers = List[UInt64](capacity=limbs)
        var power = UInt64(1)
        var radix = UInt64((UInt128(1) << 64) % UInt128(prime))
        for _ in range(limbs):
            self.powers.append(power)
            power = UInt64((UInt128(power) * UInt128(radix)) % UInt128(prime))

    def residue(self, limbs: List[UInt64]) -> UInt64:
        # Each product is below 2^95, so the sum of fewer than 2^32 fits.
        var sum = UInt128(0)
        for l in range(len(limbs)):
            sum += UInt128(limbs.unsafe_get(l)) * UInt128(self.powers.unsafe_get(l))
        return UInt64(sum % UInt128(self.prime))


def _residues(value: Integer, primes: List[UInt64], count: Int, mut residues: List[UInt64], mut budget: Budget) raises PolyError:
    """Set residues to value modulo each of the first `count` primes, through each block's product."""
    residues.clear()
    var b = 0
    while b * _BATCH < count:
        var q = Integer(1)
        for i in range(b * _BATCH, _end(primes, b)):
            q = _times(q, Integer(primes[i]))
        _work(value.magnitude_bit_length() // 8 + 1, q.magnitude_bit_length() // 8 + 1, True, budget)
        var limbs = List[UInt64]()
        try:
            _magnitude(div_rem_euclid(value, q)[1], limbs)
        except e:
            raise PolyError(PolyErrorKind.CAPACITY, String(e))
        for i in range(b * _BATCH, _end(primes, b)):
            budget.charge(UInt64(len(limbs)))
            residues.append(_remainder(limbs, primes[i]))
        b += 1


struct _Images[W: Int](Movable):
    """Monic modular bases that share their leading monomials, and their CRT.

    Every image's residues are kept, by blocks of `_BATCH` primes, over the
    union of the images' supports. A reconstruction attempt combines them
    (`_Lift`) only for the coefficients it needs: in full for a few probes
    and wherever a denominator shows, and otherwise, for a coefficient c of
    an element whose denominator so far is d, the numerator c d alone. It is
    below the reconstruction bound, so it needs only the residues of c d
    modulo a prefix of the primes whose product exceeds twice the bound,
    checked against two primes outside the prefix.
    """
    var kind: UInt8
    var leads: List[_Packed[Self.W]]
    var monomials: List[List[_Packed[Self.W]]]
    """Each element's monomials so far, in increasing order."""
    var verified: List[Int]
    """For each element, the generation of the recorded run whose final supports are its monomials, or -1."""
    var primes: List[UInt64]
    var residues: List[List[List[UInt32]]]
    """Each element's residues, by block and then by prime: slot j of a block holds the j-th prime's, one per coefficient."""
    var count: Int
    var probe: Tuple[Int, Int]
    """The coefficient that last failed to reconstruct, tried first next time."""

    def __init__(out self, kind: UInt8):
        self.kind = kind
        self.leads = List[_Packed[Self.W]]()
        self.monomials = List[List[_Packed[Self.W]]]()
        self.verified = List[Int]()
        self.primes = List[UInt64]()
        self.residues = List[List[List[UInt32]]]()
        self.count = 0
        self.probe = (0, 0)

    def matches(self, basis: List[List[_Term[ModInt, Self.W]]]) -> Bool:
        if len(basis) != len(self.leads):
            return False
        for i in range(len(basis)):
            if not _equal(basis[i][len(basis[i]) - 1].monomial, self.leads[i]):
                return False
        return True

    def matches_supports(self, supports: List[List[_Packed[Self.W]]]) -> Bool:
        """As `matches` for a replayed basis on the supports, by decreasing monomial."""
        if len(supports) != len(self.leads):
            return False
        for i in range(len(supports)):
            if not _equal(supports[i][0], self.leads[i]):
                return False
        return True

    def reset(mut self):
        self.leads = List[_Packed[Self.W]]()
        self.monomials = List[List[_Packed[Self.W]]]()
        self.verified = List[Int]()
        self.primes = List[UInt64]()
        self.residues = List[List[List[UInt32]]]()
        self.count = 0
        self.probe = (0, 0)

    def _start(mut self, leads: List[_Packed[Self.W]]):
        for lead in leads:
            self.leads.append(lead)
            self.monomials.append(List[_Packed[Self.W]]())
            self.verified.append(-1)
            self.residues.append(List[List[UInt32]]())

    def _cover(mut self, e: Int, image: List[_Packed[Self.W]], mut budget: Budget) raises PolyError:
        """Give element e every monomial of the image, in increasing order, new ones with residues zero."""
        var missing = 0
        var i = 0
        for j in range(len(image)):
            budget.charge(1)
            while i < len(self.monomials[e]) and _compare(self.kind, self.monomials[e][i], image[j]) < 0:
                i += 1
            if i < len(self.monomials[e]) and _equal(self.monomials[e][i], image[j]):
                i += 1
            else:
                missing += 1
        if missing == 0:
            return
        self.verified[e] = -1
        var n = len(self.monomials[e]) + missing
        _allocation[UInt32](_product(n * _BATCH, len(self.residues[e])), budget)
        var monomials = List[_Packed[Self.W]](capacity=n)
        # Where each old coefficient goes.
        var places = List[Int](capacity=len(self.monomials[e]))
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
                comparison = _compare(self.kind, self.monomials[e][i], image[j])
            if comparison <= 0:
                places.append(len(monomials))
                monomials.append(self.monomials[e][i])
                i += 1
                if comparison == 0:
                    j += 1
            else:
                monomials.append(image[j])
                j += 1
        var old = len(places)
        for b in range(len(self.residues[e])):
            var residues = List[UInt32](length=n * _BATCH, fill=0)
            for slot in range(_BATCH):
                budget.charge(UInt64(old))
                for k in range(old):
                    residues[slot * n + places[k]] = self.residues[e][b][slot * old + k]
            self.residues[e][b] = residues^
        self.monomials[e] = monomials^

    def _block(mut self, e: Int, slot: Int, mut budget: Budget) raises PolyError:
        """Start a new block for element e at its first slot."""
        if slot == 0:
            var n = len(self.monomials[e])
            _allocation[UInt32](n * _BATCH, budget)
            self.residues[e].append(List[UInt32](length=n * _BATCH, fill=0))

    def add(mut self, basis: List[List[_Term[ModInt, Self.W]]], p: UInt64, mut budget: Budget) raises PolyError:
        """Add one image: its residues join their block, over the union of supports."""
        if self.count == 0:
            var leads = List[_Packed[Self.W]]()
            for element in basis:
                leads.append(element[len(element) - 1].monomial)
            self._start(leads)
        var slot = self.count % _BATCH
        for e in range(len(basis)):
            ref image = basis[e]
            # Usually the image has the element's monomials exactly.
            var same = len(image) == len(self.monomials[e])
            if same:
                budget.charge(UInt64(len(image)))
                for j in range(len(image)):
                    if not _equal(self.monomials[e][j], image[j].monomial):
                        same = False
                        break
            if not same:
                var monomials = List[_Packed[Self.W]](capacity=len(image))
                for t in image:
                    monomials.append(t.monomial)
                self._cover(e, monomials, budget)
            self._block(e, slot, budget)
            var n = len(self.monomials[e])
            ref block = self.residues[e][len(self.residues[e]) - 1]
            if same:
                for j in range(len(image)):
                    block[slot * n + j] = UInt32(image[j].coefficient.value)
                continue
            # The image's monomials are now among the element's; both increase.
            var i = 0
            for j in range(len(image)):
                while not _equal(self.monomials[e][i], image[j].monomial):
                    budget.charge(1)
                    i += 1
                block[slot * n + i] = UInt32(image[j].coefficient.value)
        self.primes.append(p)
        self.count += 1

    def add_lane(mut self, supports: List[List[_Packed[Self.W]]], generation: Int, bases: _LaneBases, lane: Int, p: UInt64, mut budget: Budget) raises PolyError:
        """Add one lane of a replayed batch, on the supports of the run of the given generation.

        An element whose monomials are found to be the supports' keeps that
        generation, so later lanes of the run take their residues directly.
        """
        if self.count == 0:
            var leads = List[_Packed[Self.W]]()
            for support in supports:
                leads.append(support[0])
            self._start(leads)
        var slot = self.count % _BATCH
        for e in range(len(supports)):
            ref support = supports[e]
            var m = len(support)
            if self.verified[e] != generation:
                var same = m == len(self.monomials[e])
                if same:
                    budget.charge(UInt64(m))
                    for k in range(m):
                        if not _equal(self.monomials[e][m - 1 - k], support[k]):
                            same = False
                            break
                if same:
                    self.verified[e] = generation
                else:
                    var monomials = List[_Packed[Self.W]](capacity=m)
                    for k in range(m - 1, -1, -1):
                        monomials.append(support[k])
                    self._cover(e, monomials, budget)
            self._block(e, slot, budget)
            var n = len(self.monomials[e])
            ref block = self.residues[e][len(self.residues[e]) - 1]
            ref values = bases.values[e]
            budget.charge(UInt64(m))
            if self.verified[e] == generation:
                for k in range(m):
                    block[slot * n + n - 1 - k] = values[_LANES * k + lane]
                continue
            # The supports' monomials are among the element's, which increase.
            var i = 0
            for k in range(m - 1, -1, -1):
                while not _equal(self.monomials[e][i], support[k]):
                    budget.charge(1)
                    i += 1
                block[slot * n + i] = values[_LANES * k + lane]
        self.primes.append(p)
        self.count += 1

    def _gather(self, e: Int, k: Int, blocks: Int, scales: List[UInt64], mut into: List[UInt32]):
        """Set into to the residues of coefficient k of element e in the first blocks, block-major, each times its scale when there are scales."""
        var n = len(self.monomials[e])
        for b in range(blocks):
            ref block = self.residues[e][b]
            var count = min(_BATCH, len(self.primes) - b * _BATCH)
            for slot in range(count):
                var r = block.unsafe_get(slot * n + k)
                if len(scales):
                    var i = b * _BATCH + slot
                    r = UInt32((UInt64(r) * scales.unsafe_get(i)) % self.primes.unsafe_get(i))
                into.unsafe_get(b * _BATCH + slot) = r

    def reconstruct(mut self, mut budget: Budget) raises PolyError -> Optional[List[List[_Term[ZZ, Self.W]]]]:
        """Every element, as fractions, times the least common denominator of its coefficients; None when a coefficient has no small enough fraction yet.

        Probe coefficients are tried first, so an attempt that is still too
        early costs a few reconstructions: the coefficient that failed last
        time and the least term of a spread of elements; one that fails
        becomes the next probe.
        """
        var blocks = (len(self.primes) + _BATCH - 1) // _BATCH
        var full = _Lift(self.primes, blocks, budget)
        var bound: Integer
        var half: Integer
        try:
            bound = isqrt(full.modulus // 2)
            half = full.modulus // 2
        except e:
            raise PolyError(PolyErrorKind.CAPACITY, String(e))
        _allocation[UInt32](blocks * _BATCH, budget)
        var gathered = List[UInt32](length=blocks * _BATCH, fill=0)
        var unscaled = List[UInt64]()
        var probes: List[Tuple[Int, Int]] = [self.probe]
        for e in range(0, len(self.monomials), max(1, len(self.monomials) // _PROBES)):
            probes.append((e, 0))
        for probe in probes:
            var pe = probe[0]
            var pk = probe[1]
            if pe >= len(self.monomials) or pk >= len(self.monomials[pe]):
                continue
            self._gather(pe, pk, blocks, unscaled, gathered)
            if not _reconstruct(full.value(gathered, budget), full.modulus, bound, budget):
                self.probe = (pe, pk)
                return None
        # The prefix for numerators, with the checking primes after it.
        var prefix_blocks = 0
        var bits = 0
        while prefix_blocks < blocks and bits < bound.magnitude_bit_length() + 66:
            # Every prime is above 2^30.
            bits += 30 * (_end(self.primes, prefix_blocks) - prefix_blocks * _BATCH)
            prefix_blocks += 1
        var use_prefix = prefix_blocks < blocks
        var prefix = _Lift(self.primes, prefix_blocks if use_prefix else 0, budget)
        var prefix_half: Integer
        try:
            prefix_half = prefix.modulus // 2
        except e:
            raise PolyError(PolyErrorKind.CAPACITY, String(e))
        var checks = List[_Check]()
        var checked = List[Int]()
        var shifts = List[UInt64]()
        var limbs = List[UInt64]()
        if use_prefix:
            _magnitude(prefix.modulus, limbs)
            for i in range(len(self.primes) - 1, max(prefix.primes, len(self.primes) - 2) - 1, -1):
                checks.append(_Check(self.primes[i], len(limbs), budget))
                checked.append(i)
                shifts.append(checks[len(checks) - 1].residue(limbs))
        var scales = List[UInt64]()
        var result = List[List[_Term[ZZ, Self.W]]](capacity=len(self.leads))
        for e in range(len(self.leads)):
            # A running common denominator: a coefficient whose value times it
            # is small needs no Euclidean reconstruction of its own. Each
            # numerator is over the denominator of its time; `changes` marks
            # where the denominator grew, and to what.
            var denominator = Integer(1)
            scales.clear()
            var numerators = List[Integer](capacity=len(self.monomials[e]))
            var changes = List[Int]()
            var denominators = List[Integer]()
            for k in range(len(self.monomials[e])):
                budget.charge(1)
                var numerator = Optional[Integer](None)
                if use_prefix:
                    # The numerator from the prefix, if it is within the bound
                    # and agrees with the checking primes.
                    self._gather(e, k, prefix_blocks, scales, gathered)
                    var candidate = prefix.value(gathered, budget)
                    var negative = candidate > prefix_half
                    limbs.clear()
                    _magnitude(candidate, limbs)
                    var agrees = True
                    for c in range(len(checks)):
                        var i = checked[c]
                        var p = self.primes[i]
                        var r = UInt64(self.residues[e][i // _BATCH][(i % _BATCH) * len(self.monomials[e]) + k])
                        if len(scales):
                            r = UInt64((UInt128(r) * UInt128(scales[i])) % UInt128(p))
                        var got = checks[c].residue(limbs)
                        if negative:
                            got = (got + p - shifts[c]) % p
                        if got != r:
                            agrees = False
                            break
                    if agrees:
                        try:
                            if negative:
                                candidate -= prefix.modulus
                        except err:
                            raise PolyError(PolyErrorKind.CAPACITY, String(err))
                        if abs(candidate) <= bound:
                            numerator = Optional(candidate^)
                if not numerator:
                    self._gather(e, k, blocks, unscaled, gathered)
                    var value = full.value(gathered, budget)
                    _work(full.modulus.magnitude_bit_length() // 8 + 1, denominator.magnitude_bit_length() // 8 + 1, True, budget)
                    var exact: Integer
                    try:
                        exact = div_rem_euclid(value * denominator, full.modulus)[1].copy()
                        if exact > half:
                            exact -= full.modulus
                    except err:
                        raise PolyError(PolyErrorKind.CAPACITY, String(err))
                    if abs(exact) > bound:
                        var fraction = _reconstruct(exact, full.modulus, bound, budget)
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
                        exact = f.numerator().copy()
                        changes.append(k)
                        denominators.append(denominator.copy())
                        if use_prefix:
                            _residues(denominator, self.primes, len(self.primes), scales, budget)
                    numerator = Optional(exact^)
                numerators.append(numerator.take())
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
    # Counts the recorded runs, so that images can tell when their supports change.
    var generation = 0
    # Replays run `_LANES` primes at once: the images of the primes after
    # this one wait in `ahead`, as residues on the recorded run's final
    # supports, and are dropped whenever the run is recorded anew.
    var ahead = _LaneBases()
    var ahead_primes = List[UInt64]()
    var p = (UInt64(1) << 31) + 1
    for _ in range(_PRIME_LIMIT):
        budget.charge(1)
        p = _next_prime(p, budget)
        if not _admissible(inputs, p, budget):
            continue
        var ring = Modulus(_prime_value=p)
        var lane = -1
        if learned:
            for l in range(ahead.live):
                if ahead_primes[l] == p:
                    lane = l
            if lane < 0:
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
                ahead = _f4_replay_bases[W](trace, batch^, kind, rings, budget)
                ahead_primes = List[UInt64]()
                for ring_l in rings:
                    ahead_primes.append(ring_l.value)
                if ahead.live > 0:
                    lane = 0
        # A replayed image stays as residues unless its terms are needed.
        var basis = List[List[_Term[ModInt, W]]]()
        if lane < 0:
            basis = _f4_learn[W](_images_of(inputs, ring, budget), kind, ring, trace, budget)
            learned = True
            generation += 1
            ahead = _LaneBases()
            ahead_primes = List[UInt64]()
        ref supports = trace.steps[len(trace.steps) - 1].monomials
        if images.count > 0 and not (images.matches_supports(supports) if lane >= 0 else images.matches(basis)):
            mismatches += 1
            if mismatches < _MISMATCH_LIMIT:
                continue
            # The first images were likely the unlucky ones: start over from this one.
            images.reset()
            candidate = None
            attempt = 1
        mismatches = 0
        if candidate:
            if lane >= 0:
                basis = _lane_basis(trace, ahead, lane, ring, budget)
                lane = -1
            if _agrees(kind, candidate.value(), basis, p, budget):
                certifications += 1
                if not certify or _certify(kind, inputs, candidate.value(), budget):
                    return candidate.take()
                if certifications >= _CERTIFY_LIMIT:
                    return None
                # The images may follow an unlucky recorded run: record anew,
                # so that differing leading monomials can show.
                learned = False
                ahead = _LaneBases()
                ahead_primes = List[UInt64]()
            candidate = None
        if lane >= 0:
            images.add_lane(supports, generation, ahead, lane, p, budget)
        else:
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
    if not homogeneous and not certify and not exact:
        # Uncertified, the affine basis is reconstructed directly: the proof
        # needs J, but the basis of J is often many times larger.
        var affine = _multimodular[W](inputs, kind, False, budget)
        if affine:
            return _finish(affine.take(), True, n, order, budget)
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
