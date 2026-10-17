"""Univariate integer and rational factorization by Hensel–Zassenhaus (Z-6)."""
from apn_mojo import Integer
from .coefficients import CoefficientRing, ZZ, QQ, ModInt, Modulus, NoContext, _pow, _prime
from .dense import DensePoly
from ._subsets import _Recombination
from ._coefficient_ops import _copy as _copy_coefficient
from .errors import Budget, PolyError, PolyErrorKind, _allocation, _sum, _charge_size
from .certificates import Factorization
from .squarefree import squarefree
from .finite_field import factor_mod_p
from .primes import prime, _residue, _symmetric
from ._dense_ops import _copy, _constant, _monic, _derivative, _gcd
from ._images import _integer_dense as _integer, _rational_dense as _rational, _mod_image
from ._coefficient_ops import _quotient
from ._hensel import _HenselState, _hensel, _hensel_start, _hensel_extend, _hensel_resume, _truncate, _trial_divide
from ._integer_ops import _content, _primitive, _divide_scalar
from ._lattice_factor import _van_hoeij_lifted, _lattice_precision
from ._gcd import _modular_primitive
from .monomial import MonomialOrder
from . import _nmod


def _bound(f: DensePoly[ZZ], mut budget: Budget) raises PolyError -> ZZ:
    # ||f||_2 <= ||f||_1. This exact, conservative Landau–Mignotte bound
    # avoids a square root; recombination always reconstructs the side
    # whose degree is at most half the original degree.
    var norm = ZZ.zero(NoContext())
    for coefficient_index in range(len(f.coefficients)):
        ref c = f.coefficients[coefficient_index]
        budget.charge(1)
        norm = norm.add(c.neg(budget) if c.value.sign() < 0 else _copy_coefficient(c, budget), budget)
    var power = _pow(ZZ(Integer(2)), UInt64(f.degree() // 2 + 1), budget)
    return norm.mul(power, budget).mul(f.coefficients[f.degree()], budget)


def _subset_degrees(degrees: List[Int], total: Int, mut budget: Budget) raises PolyError -> List[Bool]:
    """Which degrees 0..total are sums of a subset of the modular factor degrees."""
    _allocation[Bool](_sum(total, 1), budget)
    var reachable = List[Bool](length=total + 1, fill=False)
    reachable[0] = True
    var top = 0
    for d in degrees:
        _charge_size(_sum(top, 1), budget)
        var i = top
        while i >= 0:
            if reachable[i] and i + d <= total:
                reachable[i + d] = True
            i -= 1
        top = min(total, top + d)
    return reachable^


def _recombine(f: DensePoly[ZZ], lifted: List[DensePoly[ZZ]], modulus: ZZ, allowed: List[Bool], mut budget: Budget) raises PolyError -> List[DensePoly[ZZ]]:
    # `allowed[d]` is False for degrees that no factor of f can have, because
    # some prime's factor degrees cannot sum to d.
    var search = _Recombination(len(lifted), budget)
    var remaining = _copy(f, budget)
    var result = List[DensePoly[ZZ]]()
    var fractions = List[Float64]()
    var total = Float64(0)
    var tolerance = Float64(1)
    var fresh = False
    while search.ready():
        budget.charge(1)
        if not fresh:
            fractions = _subleading_fractions(remaining, lifted, modulus, budget)
            total = 0
            for i in range(len(search.active)):
                budget.charge(1)
                total += fractions[search.active[i]]
            tolerance = _subleading_tolerance(remaining, modulus, budget)
            fresh = True
        var degree = 0
        for i in search.selection.indices:
            budget.charge(1)
            degree = _sum(degree, lifted[search.active[i]].degree())
        var complement = degree > remaining.degree() // 2
        _allocation[Bool](len(search.active), budget)
        var chosen = List[Bool](length=len(search.active), fill=complement)
        for i in search.selection.indices:
            budget.charge(1)
            chosen[i] = not complement
        var chosen_degree = remaining.degree() - degree if complement else degree
        if chosen_degree < len(allowed) and not allowed[chosen_degree]:
            search.advance(budget)
            continue
        # The x^(k-1) coefficient of lc(q) * h is lc(f) times the sum of the
        # roots of h, so its residue lies within the tolerance of a multiple
        # of the modulus. Compare the fractional parts first.
        if tolerance < 0.5:
            var part = Float64(0)
            for i in search.selection.indices:
                budget.charge(1)
                part += fractions[search.active[i]]
            if complement:
                part = total - part
            part -= _floor(part)
            if min(part, 1 - part) > tolerance:
                search.advance(budget)
                continue
        # A true factor h with cofactor q reconstructs as lc(q) * h exactly, so
        # its constant term lc(q) * h(0) divides lc(f) * f(0). Test that first.
        var lead = _copy_coefficient(remaining.coefficients[remaining.degree()], budget)
        if not remaining.coefficients[0].is_zero():
            var trailing = _copy_coefficient(lead, budget)
            for i in range(len(search.active)):
                budget.charge(1)
                if chosen[i]:
                    trailing = ZZ(_symmetric(trailing.mul(lifted[search.active[i]].coefficients[0], budget).value, modulus.value, budget))
            var target = lead.mul(remaining.coefficients[0], budget)
            if trailing.is_zero() or not _quotient(target, trailing, budget):
                search.advance(budget)
                continue
        var candidate = _constant(remaining, lead, budget)
        for i in range(len(search.active)):
            budget.charge(1)
            if chosen[i]:
                candidate = _truncate(candidate.mul(lifted[search.active[i]], budget), modulus, budget)
        candidate = _primitive(candidate, budget)
        var quotient = Optional[DensePoly[ZZ]](None)
        if candidate.degree() > 0 and candidate.degree() < remaining.degree():
            if candidate.coefficients[0].is_zero() or Bool(_quotient(remaining.coefficients[0], candidate.coefficients[0], budget)):
                quotient = _trial_divide(remaining, candidate, budget)
        if quotient:
            _allocation[DensePoly[ZZ]](1, budget)
            if complement:
                # The selected (smaller-cardinality) side is irreducible:
                # every proper subset was tested earlier. Reconstructing
                # its lower-degree complement only supplies the quotient.
                result.append(quotient.take())
                remaining = candidate^
            else:
                result.append(candidate^)
                remaining = quotient.take()
            search.accept(budget)
            fresh = False
        else:
            search.advance(budget)
    if remaining.degree() > 0:
        _allocation[DensePoly[ZZ]](1, budget)
        result.append(remaining^)
    return result^


def _floor(x: Float64) -> Float64:
    var t = Float64(Int(x))
    return t - 1 if t > x else t


def _fraction(r: Integer, modulus: Integer) raises PolyError -> Float64:
    """r / modulus for 0 <= r < modulus, within 2^-52 of the exact ratio."""
    try:
        var shift = max(0, modulus.magnitude_bit_length() - 62)
        return Float64(Int(r >> shift)) / Float64(Int(modulus >> shift))
    except e:
        raise PolyError(PolyErrorKind.CAPACITY, String(e))


def _subleading_fractions(f: DensePoly[ZZ], lifted: List[DensePoly[ZZ]], modulus: ZZ, mut budget: Budget) raises PolyError -> List[Float64]:
    """lc(f) * (subleading coefficient of each monic lifted factor) mod the
    modulus, as a fraction of the modulus."""
    ref lead = f.coefficients[f.degree()]
    _allocation[Float64](len(lifted), budget)
    var result = List[Float64](capacity=len(lifted))
    for g in lifted:
        budget.charge(1)
        var r = _symmetric(lead.mul(g.coefficients[g.degree() - 1], budget).value, modulus.value, budget)
        if r.sign() < 0:
            r = ZZ(r).add(modulus, budget).value
        result.append(_fraction(r, modulus.value))
    return result^


def _subleading_tolerance(f: DensePoly[ZZ], modulus: ZZ, mut budget: Budget) raises PolyError -> Float64:
    """A bound on |lc(f) * (sum of the roots of any factor)| over the modulus,
    plus the rounding slack of summing fractions.

    The roots of f with |a| >= 1 have product at most M(f)/|lc(f)| <= ||f||_1
    / |lc(f)|, and numbers at least 1 sum to at most their count less one plus
    their product, so the sum of |a| over all roots is at most (d - 1) +
    ||f||_1 / |lc(f)|."""
    ref lead = f.coefficients[f.degree()]
    var bound = ZZ.zero(NoContext())
    for i in range(len(f.coefficients)):
        budget.charge(1)
        ref c = f.coefficients[i]
        bound = bound.add(c.neg(budget) if c.value.sign() < 0 else _copy_coefficient(c, budget), budget)
    var magnitude = lead.neg(budget) if lead.value.sign() < 0 else _copy_coefficient(lead, budget)
    bound = bound.add(magnitude.mul(ZZ(Integer(f.degree() - 1)), budget), budget)
    if bound.value.magnitude_bit_length() >= modulus.value.magnitude_bit_length():
        return 1
    return _fraction(bound.value, modulus.value) + Float64(2.0) ** -40


comptime _PRIME_TRIALS = 3
"""Good primes whose modular factorizations are compared before lifting."""
comptime _LATTICE_TRIALS = 10
"""Good primes compared while the fewest factors still need lattice
recombination and one of the last three primes lowered that count."""


def _next_small_prime(previous: UInt64, mut budget: Budget) raises PolyError -> UInt64:
    """The largest prime below `previous`; starting from 2^28 this walks the
    descending primes whose residue products take the SIMD path, and
    quadratic lifting makes their size irrelevant."""
    var candidate = previous - 1
    if candidate % 2 == 0:
        candidate -= 1
    while True:
        budget.charge(1)
        if candidate < 3:
            raise PolyError(PolyErrorKind.CAPACITY, "small prime sequence exhausted")
        if _prime(candidate, budget):
            return candidate
        candidate -= 2


def _squarefree_factors(f: DensePoly[ZZ], mut budget: Budget) raises PolyError -> List[DensePoly[ZZ]]:
    if f.degree() <= 1:
        _allocation[DensePoly[ZZ]](1, budget)
        return [_copy(f, budget)]
    # Factor modulo several good primes. Each one's factor degrees bound the
    # degrees of true factors; lifting uses the prime with fewest factors.
    var p = UInt64(1) << 28
    var trials = 0
    _allocation[Bool](_sum(f.degree(), 1), budget)
    var allowed = List[Bool](length=f.degree() + 1, fill=True)
    var best = List[DensePoly[ModInt]]()
    var stale = 0
    while trials < _PRIME_TRIALS or (trials < _LATTICE_TRIALS and len(best) >= 20 and stale < 3):
        budget.charge(1)
        p = _next_small_prime(p, budget)
        if _residue(f.coefficients[f.degree()].value, p, budget) == 0:
            continue
        var ctx = Modulus(_prime_value=p)
        var image = _monic(_mod_image(f, ctx, budget), budget)
        if _gcd(image, _derivative(image, budget), budget).degree() > 0:
            continue
        trials += 1
        var modular = factor_mod_p(image, budget, seed=0)
        if len(modular) == 1:
            _allocation[DensePoly[ZZ]](1, budget)
            return [_copy(f, budget)]
        _allocation[Int](len(modular), budget)
        var degrees = List[Int](capacity=len(modular))
        for g in modular:
            degrees.append(g.degree())
        var reachable = _subset_degrees(degrees, f.degree(), budget)
        var proper = False
        for d in range(f.degree() + 1):
            allowed[d] = allowed[d] and reachable[d]
            if d > 0 and d < f.degree() and allowed[d]:
                proper = True
        if not proper:
            _allocation[DensePoly[ZZ]](1, budget)
            return [_copy(f, budget)]
        if len(best) == 0 or len(modular) < len(best):
            best = modular^
            stale = 0
        else:
            stale += 1
    # Measured crossover: exact LLL loses on 8/16-way splitting but
    # wins at 20. Peel singleton groups before paying for the lattice.
    if len(best) >= 20:
        return _large_recombine(f, best, allowed, budget)
    var lifting = _hensel(f, best, _bound(f, budget), budget)
    return _recombine(f, lifting[0], lifting[1], allowed, budget)


def _large_recombine(f: DensePoly[ZZ], modular: List[DensePoly[ModInt]], mut budget: Budget) raises PolyError -> List[DensePoly[ZZ]]:
    _allocation[Bool](_sum(f.degree(), 1), budget)
    return _large_recombine(f, modular, List[Bool](length=f.degree() + 1, fill=True), budget)


def _large_recombine(f: DensePoly[ZZ], modular: List[DensePoly[ModInt]], allowed: List[Bool], mut budget: Budget) raises PolyError -> List[DensePoly[ZZ]]:
    var state = _hensel_start(modular, budget)
    # Peel and run the lattice at the lattice's own precision; factors that
    # need more are lifted further only when reconstruction asks for it.
    var bound = _bound(f, budget)
    var precision = _lattice_precision(f, len(modular), ZZ(Integer(Int(modular[0].ring.value))), budget)
    var first = _copy_coefficient(bound, budget)
    if precision and precision.value().value < bound.value:
        first = _copy_coefficient(precision.value(), budget)
    _hensel_extend(f, modular, first, state, budget)
    var lifting = (state.lifted.copy(), _copy_coefficient(state.modulus, budget))
    var remaining = _copy(f, budget)
    var result = List[DensePoly[ZZ]]()
    var active_modular = List[DensePoly[ModInt]]()
    var active_lifted = List[DensePoly[ZZ]]()
    for i in range(len(modular)):
        budget.charge(1)
        var candidate = _primitive(_truncate(lifting[0][i].scale(remaining.coefficients[remaining.degree()], budget), lifting[1], budget), budget)
        var quotient = _trial_divide(remaining, candidate, budget)
        if candidate.degree() > 0 and candidate.degree() == lifting[0][i].degree() and quotient:
            remaining = quotient.take()
            _allocation[DensePoly[ZZ]](1, budget)
            result.append(candidate^)
        else:
            _allocation[DensePoly[ModInt]](1, budget)
            _allocation[DensePoly[ZZ]](1, budget)
            active_modular.append(_copy(modular[i], budget))
            active_lifted.append(_copy(lifting[0][i], budget))
    if remaining.degree() > 0:
        var rest: List[DensePoly[ZZ]]
        if len(active_modular) >= 20:
            if len(active_modular) == len(modular):
                # Nothing peeled: keep the factor tree for further lifting.
                rest = _van_hoeij_lifted(remaining, active_modular, _bound(remaining, budget), state, budget)
            else:
                var resumed = _hensel_resume(active_lifted^, _copy_coefficient(lifting[1], budget))
                rest = _van_hoeij_lifted(remaining, active_modular, _bound(remaining, budget), resumed, budget)
        else:
            var remaining_bound = _bound(remaining, budget)
            if lifting[1].value > remaining_bound.value:
                rest = _recombine(remaining, active_lifted, lifting[1], allowed, budget)
            else:
                var full = _hensel(remaining, active_modular, remaining_bound, budget)
                rest = _recombine(remaining, full[0], full[1], allowed, budget)
        for g in rest:
            budget.charge(1)
            _allocation[DensePoly[ZZ]](1, budget)
            result.append(_copy(g, budget))
    return result^


def _less[C: CoefficientRing](a: DensePoly[C], b: DensePoly[C], mut budget: Budget) raises PolyError -> Bool:
    budget.charge(1)
    if a.degree() != b.degree():
        return a.degree() < b.degree()
    for i in range(a.degree(), -1, -1):
        budget.charge(1)
        var delta = a.coefficients[i].sub(b.coefficients[i], budget)
        if not delta.is_zero():
            comptime if C == ZZ:
                return rebind[ZZ](delta).value.sign() < 0
            elif C == QQ:
                return rebind[QQ](delta).value.sign() < 0
    return False


def _sort[C: CoefficientRing](mut factors: List[Tuple[DensePoly[C], Int]], template: DensePoly[C], mut budget: Budget) raises PolyError:
    for i in range(1, len(factors)):
        budget.charge(1)
        var current = (DensePoly[C](template.variable, template.ring.copy()), 0)
        swap(current, factors[i])
        var j = i
        while j > 0 and _less(current[0], factors[j - 1][0], budget):
            var moved = (DensePoly[C](template.variable, template.ring.copy()), 0)
            swap(moved, factors[j - 1])
            swap(moved, factors[j])
            j -= 1
        swap(current, factors[j])


def _modular_squarefree(f: DensePoly[ZZ], mut budget: Budget) raises PolyError -> Bool:
    # A prime that keeps the degree and leaves f coprime to f' proves f
    # squarefree over QQ: a repeated primitive factor would survive reduction.
    var p = UInt64(1) << 28
    for _ in range(2):
        budget.charge(1)
        p = _next_small_prime(p, budget)
        if _residue(f.coefficients[f.degree()].value, p, budget) == 0:
            continue
        var field = _nmod._field(p)
        _allocation[UInt64](len(f.coefficients), budget)
        var image = List[UInt64](capacity=len(f.coefficients))
        for i in range(len(f.coefficients)):
            image.append(_nmod._to(_residue(f.coefficients[i].value, p, budget), field))
        if len(_nmod._gcd(image, _nmod._derivative(image, field, budget), field, budget)) == 1:
            return True
    return False


def _integer_gcd(a: DensePoly[ZZ], b: DensePoly[ZZ], mut budget: Budget) raises PolyError -> DensePoly[ZZ]:
    # The primitive gcd with positive leading coefficient, by modular images.
    if b.is_zero():
        return _primitive(a, budget)
    if a.is_zero():
        return _primitive(b, budget)
    if a.degree() <= 0 or b.degree() <= 0:
        return _constant(a, ZZ.one(NoContext()), budget)
    var order = MonomialOrder()
    var g = _modular_primitive(_primitive(a, budget).to_sparse(order, budget), _primitive(b, budget).to_sparse(order, budget), a.variable, budget)
    return _primitive(DensePoly[ZZ].from_sparse(g, budget, variable=a.variable), budget)


def _exact_integer(a: DensePoly[ZZ], b: DensePoly[ZZ], mut budget: Budget) raises PolyError -> DensePoly[ZZ]:
    var quotient = _trial_divide(a, b, budget)
    if not quotient:
        raise PolyError(PolyErrorKind.DOMAIN, "inexact integer squarefree quotient")
    return quotient.take()


def _integer_squarefree(f: DensePoly[ZZ], mut budget: Budget) raises PolyError -> List[Tuple[DensePoly[ZZ], Int]]:
    """Primitive squarefree blocks of a primitive polynomial by Yun's recurrence over ZZ.

    By Gauss's lemma every quotient below is exact over ZZ, so modular gcds
    replace rational remainder sequences.
    """
    var blocks = List[Tuple[DensePoly[ZZ], Int]]()
    if f.degree() <= 0:
        return blocks^
    _allocation[Tuple[DensePoly[ZZ], Int]](1, budget)
    if _modular_squarefree(f, budget):
        blocks.append((_primitive(f, budget), 1))
        return blocks^
    var derivative = _derivative(f, budget)
    var common = _integer_gcd(f, derivative, budget)
    var b = _exact_integer(f, common, budget)
    var c = _exact_integer(derivative, common, budget)
    var multiplicity = 1
    while b.degree() > 0:
        budget.charge(1)
        # Exactly b = prod_{j>=i} a_j and c = b * sum_{j>=i} (j-i+1) a_j'/a_j;
        # b and c must share their scale, so neither is normalized.
        var d = c.sub(_derivative(b, budget), budget)
        var a = _integer_gcd(b, d, budget)
        if a.degree() > 0:
            _allocation[Tuple[DensePoly[ZZ], Int]](1, budget)
            blocks.append((_copy(a, budget), multiplicity))
        b = _exact_integer(b, a, budget)
        c = _exact_integer(d, a, budget)
        multiplicity = _sum(multiplicity, 1)
    return blocks^


def factor_integer(f: DensePoly[ZZ], mut budget: Budget) raises PolyError -> Factorization[ZZ]:
    """Factor an integer polynomial into primitive factors with positive leading coefficients.

    Args:
        f: The integer polynomial, including zero or constants.
        budget: The shared work allowance.

    Returns:
        Signed content and factors sorted by degree, then leading-to-constant coefficients.

    Raises:
        PolyError: DOMAIN for malformed input, LIMIT or CAPACITY on work limits.
    """
    f.check_invariants(budget)
    var unit = _content(f, budget)
    var factors = List[Tuple[DensePoly[ZZ], Int]]()
    if f.degree() <= 0:
        return Factorization[ZZ](unit^, factors^)
    var primitive = _divide_scalar(f, unit, budget)
    var blocks = _integer_squarefree(primitive, budget)
    for entry in blocks:
        budget.charge(1)
        var irreducibles = _squarefree_factors(entry[0], budget)
        for i in range(len(irreducibles)):
            budget.charge(1)
            _allocation[Tuple[DensePoly[ZZ], Int]](1, budget)
            var irreducible = DensePoly[ZZ](f.variable, NoContext())
            swap(irreducible, irreducibles[i])
            factors.append((irreducible^, entry[1]))
    _sort(factors, f, budget)
    return Factorization[ZZ](unit^, factors^)


def factor(f: DensePoly[QQ], mut budget: Budget) raises PolyError -> Factorization[QQ]:
    """Factor a rational polynomial into monic irreducibles with multiplicities.

    Args:
        f: The rational polynomial, including zero or constants.
        budget: The shared work allowance.

    Returns:
        The leading coefficient and factors in the deterministic coefficient order.

    Raises:
        PolyError: DOMAIN for malformed input, LIMIT or CAPACITY on work limits.
    """
    f.check_invariants(budget)
    var unit = QQ.zero(f.ring)
    if not f.is_zero():
        unit = _copy_coefficient(f.coefficients[f.degree()], budget)
    var factors = List[Tuple[DensePoly[QQ], Int]]()
    if f.degree() > 0:
        var integer_factors = factor_integer(_integer(f, budget), budget)
        for entry in integer_factors.factors:
            budget.charge(1)
            _allocation[Tuple[DensePoly[QQ], Int]](1, budget)
            factors.append((_monic(_rational(entry[0], budget), budget), entry[1]))
        _sort(factors, f, budget)
    return Factorization[QQ](unit^, factors^)
