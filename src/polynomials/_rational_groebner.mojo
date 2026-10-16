"""Gröbner bases over QQ under GREVLEX, through the homogenized inputs.

The inputs become primitive integer polynomials, homogenized with a new least
variable h (GREVLEX with h last) unless they are homogeneous already. Their
ideal J is computed in one of two ways, and setting h = 1 then gives the
basis of the input ideal.

Exactly. The packed engine runs fraction-free Buchberger on the homogenized
inputs. Processing them degree by degree avoids most of the intermediate
coefficient growth an inhomogeneous computation suffers. If a basis element's
coefficients still grow beyond `_GROWTH_BITS`, or four times the inputs',
the exact run stops in favor of:

Reconstruction, with a certificate.
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
       degree-d monomials its leading monomials generate;
   (c) G's leading monomials are those of a basis G_p computed inside the
       image J_p. Then dim (J_p)_d >= c_d, and dim (J_p)_d <= dim J_d since
       the Macaulay matrix of J_d is an integer matrix and reduction modulo p
       cannot raise its rank. So c_d <= dim J_d <= dim <G>_d = c_d for every
       d, and <G> = J;
   (d) every element is monic and no tail monomial is divisible by a leading
       monomial, so G is the reduced basis of J.
   Correctness never depends on a prime being lucky; bad primes cost time.
   If reconstruction needs more than `_PRIME_LIMIT` primes or certification
   fails `_CERTIFY_LIMIT` times, the exact run resumes without a limit.

Finish. A GREVLEX basis of J with h last dehomogenizes to a basis of the
input ideal, because the leading monomial of a homogeneous element
dehomogenizes to the leading monomial of its image. Dropping elements whose
leading monomial another's divides and reducing the tails exactly gives the
reduced basis, which is unique, so every route returns the same result.
"""
from std.math import max
from apn_mojo import Integer, Rational, div_rem_euclid, gcd as integer_gcd, isqrt
from .coefficients import ModInt, Modulus, NoContext, QQ, ZZ, _prime, _work
from .errors import Budget, PolyError, PolyErrorKind, _allocation
from .monomial import MonomialOrder
from .sparse import SparsePoly, Term
from .primes import _residue
from ._images import _denominator, _scaled_integer
from ._packed_groebner import _Buckets, _Engine, _Packed, _Term, _compare, _divides, _equal, _monomial, _pack, _packed, _priorities
from ._f4 import _f4_packed

comptime _PRIME_LIMIT = 4096
"""Primes tried before giving up on reconstruction."""
comptime _CERTIFY_LIMIT = 4
"""Certification attempts before giving up."""
comptime _GROWTH_BITS = 512
"""Coefficient size, at least, at which the exact run gives way to reconstruction."""
comptime _MISMATCH_LIMIT = 3
"""Consecutive images with other leading monomials before they replace the first."""


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
        while r1 > bound:
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
    """CRT accumulation of monic modular bases that share their leading monomials."""
    var kind: UInt8
    var leads: List[_Packed[Self.W]]
    var monomials: List[List[_Packed[Self.W]]]
    """Each element's monomials so far, in increasing order."""
    var values: List[List[Integer]]
    """Each coefficient modulo `modulus`, in [0, modulus)."""
    var modulus: Integer
    var count: Int
    var probe: Tuple[Int, Int]
    """The coefficient that last failed to reconstruct, tried first next time."""

    def __init__(out self, kind: UInt8):
        self.kind = kind
        self.leads = List[_Packed[Self.W]]()
        self.monomials = List[List[_Packed[Self.W]]]()
        self.values = List[List[Integer]]()
        self.modulus = Integer(1)
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
        self.count = 0
        self.probe = (0, 0)

    def _merge(self, value: Integer, residue: UInt64, p: UInt64, inverse: UInt64, mut budget: Budget) raises PolyError -> Integer:
        """The number below modulus * p congruent to value and to residue modulo p.

        `inverse` is the inverse of the modulus modulo p, shared by every coefficient.
        """
        var old = _residue(value, p, budget)
        var correction = UInt64((UInt128((residue + p - old) % p) * UInt128(inverse)) % UInt128(p))
        if correction == 0:
            return value.copy()
        _work(self.modulus.magnitude_bit_length() // 8 + 1, 8, True, budget)
        try:
            return value + self.modulus * Integer(correction)
        except e:
            raise PolyError(PolyErrorKind.CAPACITY, String(e))

    def add(mut self, basis: List[List[_Term[ModInt, Self.W]]], p: UInt64, mut budget: Budget) raises PolyError:
        """Merge one image: its residues join the accumulated ones over the union of supports."""
        var ring = Modulus(_prime_value=p)
        var inverse = ModInt(_residue(self.modulus, p, budget), ring).inverse(budget).value
        if self.count == 0:
            for element in basis:
                self.leads.append(element[len(element) - 1].monomial)
                self.monomials.append(List[_Packed[Self.W]]())
                self.values.append(List[Integer]())
        for e in range(len(basis)):
            ref image = basis[e]
            ref old_m = self.monomials[e]
            ref old_v = self.values[e]
            _allocation[Integer](len(old_m) + len(image), budget)
            var merged_m = List[_Packed[Self.W]](capacity=len(old_m) + len(image))
            var merged_v = List[Integer](capacity=len(old_m) + len(image))
            var i = 0
            var j = 0
            while i < len(old_m) or j < len(image):
                var comparison: Int
                if i == len(old_m):
                    comparison = 1
                elif j == len(image):
                    comparison = -1
                else:
                    comparison = _compare(self.kind, image[j].monomial, old_m[i])
                if comparison < 0:
                    merged_m.append(old_m[i])
                    merged_v.append(self._merge(old_v[i], 0, p, inverse, budget))
                    i += 1
                elif comparison > 0:
                    merged_m.append(image[j].monomial)
                    merged_v.append(self._merge(Integer(0), image[j].coefficient.value, p, inverse, budget))
                    j += 1
                else:
                    merged_m.append(old_m[i])
                    merged_v.append(self._merge(old_v[i], image[j].coefficient.value, p, inverse, budget))
                    i += 1
                    j += 1
            self.monomials[e] = merged_m^
            self.values[e] = merged_v^
        try:
            self.modulus = self.modulus * Integer(p)
        except e:
            raise PolyError(PolyErrorKind.CAPACITY, String(e))
        self.count += 1

    def reconstruct(mut self, mut budget: Budget) raises PolyError -> Optional[List[List[_Term[QQ, Self.W]]]]:
        """Every coefficient as a fraction, or None when one has no small enough fraction yet.

        The coefficient that failed last time is tried first, so an attempt
        that is still too early costs one reconstruction.
        """
        var bound: Integer
        try:
            bound = isqrt(self.modulus // 2)
        except e:
            raise PolyError(PolyErrorKind.CAPACITY, String(e))
        var pe = self.probe[0]
        var pk = self.probe[1]
        if pe < len(self.values) and pk < len(self.values[pe]):
            if not _reconstruct(self.values[pe][pk], self.modulus, bound, budget):
                return None
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
    while len(engine.pairs):
        budget.charge(1)
        var pair = engine.select(budget)
        if not engine.pair_reduces_to_zero(pair, budget):
            return False
    return True


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


def _bits[W: Int](p: List[_Term[ZZ, W]]) -> Int:
    var bits = 0
    for t in p:
        bits = max(bits, t.coefficient.value.magnitude_bit_length())
    return bits


def _exact[W: Int](inputs: List[List[_Term[ZZ, W]]], kind: UInt8, limit: Int, mut budget: Budget) raises PolyError -> Optional[List[List[_Term[ZZ, W]]]]:
    """The reduced basis by fraction-free Buchberger, or None once an element exceeds `limit` bits (0: no limit)."""
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
        if limit and _bits(engine.polys[len(engine.polys) - 1]) > limit:
            return None
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
        if count & (count - 1) == 0 or count % 8 == 0:
            candidate = images.reconstruct(budget)
    return None




def _rational_basis[W: Int](generators: List[SparsePoly[QQ]], order: MonomialOrder, growth: Int, mut budget: Budget) raises PolyError -> List[SparsePoly[QQ]]:
    var n = len(order.variables)
    var kind = order.kind
    # Primitive integer inputs, in the order's lanes; h, if needed, is lane n.
    var inputs = List[List[_Term[ZZ, W]]]()
    var homogeneous = True
    var input_bits = 0
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
        input_bits = max(input_bits, _bits(integral))
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
    # Exactly, unless coefficients grow far beyond the inputs'; then by
    # certified reconstruction; and exactly without limit if that gives up.
    if growth >= 0:
        var exact = _exact[W](inputs, kind, max(growth, 4 * input_bits), budget)
        if exact:
            return _finish(exact.take(), homogeneous, n, order, budget)
    var modular = _multimodular[W](inputs, kind, budget)
    if modular:
        return _finish(modular.take(), homogeneous, n, order, budget)
    var unlimited = _exact[W](inputs, kind, 0, budget)
    return _finish(unlimited.take(), homogeneous, n, order, budget)


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


def _grevlex_groebner_rational(generators: List[SparsePoly[QQ]], order: MonomialOrder, mut budget: Budget, growth: Int = _GROWTH_BITS) raises PolyError -> List[SparsePoly[QQ]]:
    """The reduced monic basis over QQ under a supported GREVLEX order.

    The exact run gives way to reconstruction once a basis element's
    coefficients exceed max(growth, four times the inputs') bits; a negative
    `growth` skips the exact run, which tests use to exercise reconstruction.
    """
    if len(order.variables) + 1 <= 8:
        return _rational_basis[8](generators, order, growth, budget)
    return _rational_basis[16](generators, order, growth, budget)
