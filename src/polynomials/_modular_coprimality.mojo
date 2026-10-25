"""Exact coprimality witnesses from degree-preserving affine lines over prime fields.

A nonconstant common divisor survives any affine projection preserving both
input total degrees. A univariate Bezout identity excludes it. Over ZZ an
integer combination of original coefficients equal to one also excludes scalar
factors. Search failures are inconclusive and leave the exact fallback intact.
"""
from apn_mojo import Integer
from .coefficients import CoefficientRing, ZZ, QQ
from .sparse import SparsePoly
from .errors import Budget, PolyError, _allocation, _charge_size, _sum, _product
from ._coefficient_ops import _integer_bezout
from ._images import _integer_image
from ._views import _variables, _is_unit
from .primes import _residue


@fieldwise_init
struct ModularCoprimalityCertificate(Copyable, Movable, Writable):
    """A degree-preserving affine projection and two exact coprimality identities.

    The modular identity excludes nonconstant factors. For integer inputs the
    coefficient identity excludes shared integer factors; rational inputs have
    empty integer witness lists. Coefficients use ordinary reduced residues.
    """
    var prime: UInt64
    """One of the fixed admitted primes below 2**30."""
    var variables: List[Int64]
    """All occurring variables, in increasing identifier order."""
    var slopes: List[UInt64]
    """The coefficient of t in each variable's affine substitution."""
    var offsets: List[UInt64]
    """The constant term in each variable's affine substitution."""
    var u: List[UInt64]
    """The left univariate Bezout multiplier, in increasing degree."""
    var v: List[UInt64]
    """The right univariate Bezout multiplier, in increasing degree."""
    var integer_indices: List[Int]
    """Increasing indices into the concatenated input coefficient lists."""
    var integer_weights: List[ZZ]
    """Nonzero integer weights whose selected coefficient sum is exactly one."""


# Bounded dense images keep the fast attempt cheap even for sparse huge degrees.
comptime _MAX_DEGREE = 256


def _prime_at(i: Int) -> UInt64:
    return UInt64(1000000007) if i == 0 else (UInt64(1000000009) if i == 1 else UInt64(998244353))


def _degree[C: CoefficientRing](f: SparsePoly[C], mut budget: Budget) raises PolyError -> Int:
    var degree = -1
    for term in f.terms:
        budget.charge(1)
        var total = 0
        for pair in term.monomial.pairs:
            budget.charge(1)
            total = _sum(total, Int(pair[1]))
        degree = max(degree, total)
    return degree


def _trim(mut a: List[UInt64], mut budget: Budget) raises PolyError:
    while len(a) and a[len(a) - 1] == 0:
        budget.charge(1)
        _ = a.pop()


def _multiply(a: List[UInt64], b: List[UInt64], p: UInt64, mut budget: Budget) raises PolyError -> List[UInt64]:
    if not len(a) or not len(b):
        return List[UInt64]()
    var size = _sum(len(a), len(b)) - 1
    _allocation[UInt64](size, budget)
    _charge_size(_product(len(a), len(b)), budget)
    var out = List[UInt64](length=size, fill=0)
    for i in range(len(a)):
        for j in range(len(b)):
            # p < 2**30: one product plus a reduced residue fits UInt64.
            out[i + j] = (out[i + j] + a[i] * b[j]) % p
    _trim(out, budget)
    return out^


def _add(mut a: List[UInt64], b: List[UInt64], p: UInt64, subtract: Bool, mut budget: Budget) raises PolyError:
    if len(a) < len(b):
        _allocation[UInt64](len(b) - len(a), budget)
        a.resize(len(b), 0)
    _charge_size(len(b), budget)
    for i in range(len(b)):
        a[i] = (a[i] + p - b[i]) % p if subtract else (a[i] + b[i]) % p
    _trim(a, budget)


def _power(a: UInt64, n: UInt64, p: UInt64, mut budget: Budget) raises PolyError -> UInt64:
    var base = a
    var exponent = n
    var result = UInt64(1)
    while exponent:
        budget.charge(1)
        if exponent & 1:
            result = result * base % p
        exponent >>= 1
        base = base * base % p
    return result


def _quotient(mut a: List[UInt64], b: List[UInt64], p: UInt64, mut budget: Budget) raises PolyError -> List[UInt64]:
    var count = max(0, len(a) - len(b) + 1)
    _allocation[UInt64](count, budget)
    var q = List[UInt64](length=count, fill=0)
    var inverse = _power(b[len(b) - 1], p - 2, p, budget)
    while len(a) >= len(b) and len(a):
        var shift = len(a) - len(b)
        var c = a[len(a) - 1] * inverse % p
        q[shift] = c
        _charge_size(len(b), budget)
        for i in range(len(b)):
            a[i + shift] = (a[i + shift] + p - c * b[i] % p) % p
        _trim(a, budget)
    _trim(q, budget)
    return q^


def _bezout(var a: List[UInt64], var b: List[UInt64], p: UInt64, mut budget: Budget) raises PolyError -> Optional[Tuple[List[UInt64], List[UInt64]]]:
    _allocation[UInt64](2, budget)
    var u: List[UInt64] = [1]
    var v = List[UInt64]()
    var next_u = List[UInt64]()
    var next_v: List[UInt64] = [1]
    while len(b):
        budget.charge(1)
        var q = _quotient(a, b, p, budget)
        _add(u, _multiply(q, next_u, p, budget), p, True, budget)
        _add(v, _multiply(q, next_v, p, budget), p, True, budget)
        swap(a, b)
        swap(u, next_u)
        swap(v, next_v)
    if len(a) != 1:
        return None
    var inverse = _power(a[0], p - 2, p, budget)
    _charge_size(_sum(len(u), len(v)), budget)
    for i in range(len(u)):
        u[i] = u[i] * inverse % p
    for i in range(len(v)):
        v[i] = v[i] * inverse % p
    return (u^, v^)


def _project(f: SparsePoly[ZZ], proof: ModularCoprimalityCertificate, mut budget: Budget) raises PolyError -> List[UInt64]:
    var p = proof.prime
    _allocation[List[List[UInt64]]](len(proof.variables), budget)
    var powers = List[List[List[UInt64]]]()
    for i in range(len(proof.variables)):
        var top = Int(f.degree_in(proof.variables[i], budget))
        _allocation[List[UInt64]](top + 1, budget)
        _allocation[UInt64](3, budget)
        var rows = List[List[UInt64]]()
        rows.append([1])
        var linear: List[UInt64] = [proof.offsets[i], proof.slopes[i]]
        for _ in range(top):
            rows.append(_multiply(rows[len(rows) - 1], linear, p, budget))
        powers.append(rows^)
    var result = List[UInt64]()
    for term in f.terms:
        _allocation[UInt64](1, budget)
        var image: List[UInt64] = [_residue(term.coefficient.value, p, budget)]
        var position = 0
        for pair in term.monomial.pairs:
            while proof.variables[position] != pair[0]:
                budget.charge(1)
                position += 1
            image = _multiply(image, powers[position][Int(pair[1])], p, budget)
        _add(result, image, p, False, budget)
    return result^


def _coefficient(f: SparsePoly[ZZ], g: SparsePoly[ZZ], i: Int) -> ref [f.terms[0].coefficient, g.terms[0].coefficient] ZZ:
    if i < len(f.terms):
        return f.terms[i].coefficient
    return g.terms[i - len(f.terms)].coefficient


def _integer_witness(f: SparsePoly[ZZ], g: SparsePoly[ZZ], mut proof: ModularCoprimalityCertificate, mut budget: Budget) raises PolyError -> Bool:
    var accumulator = ZZ(Integer(0))
    for i in range(_sum(len(f.terms), len(g.terms))):
        budget.charge(1)
        var triple = _integer_bezout(accumulator, _coefficient(f, g, i), budget)
        if triple[1].is_zero():
            proof.integer_indices.clear()
            proof.integer_weights.clear()
        else:
            for j in range(len(proof.integer_weights)):
                proof.integer_weights[j] = proof.integer_weights[j].mul(triple[1], budget)
        if not triple[2].is_zero():
            _allocation[Int](1, budget)
            _allocation[ZZ](1, budget)
            proof.integer_indices.append(i)
            var weight = ZZ(Integer(0))
            swap(weight, triple[2])
            proof.integer_weights.append(weight^)
        swap(accumulator, triple[0])
        if accumulator.value == Integer(1):
            return True
    return False


def _random(mut state: UInt64) -> UInt64:
    state ^= state << 13
    state ^= state >> 7
    state ^= state << 17
    return state


def _produce(f: SparsePoly[ZZ], g: SparsePoly[ZZ], integer: Bool, mut budget: Budget) raises PolyError -> Optional[ModularCoprimalityCertificate]:
    var df = _degree(f, budget)
    var dg = _degree(g, budget)
    if min(df, dg) < 0 or max(df, dg) == 0 or max(df, dg) > _MAX_DEGREE:
        return None
    var proof = ModularCoprimalityCertificate(0, _variables(f, g, budget), List[UInt64](), List[UInt64](), List[UInt64](), List[UInt64](), List[Int](), List[ZZ]())
    if integer and not _integer_witness(f, g, proof, budget):
        return None
    _allocation[UInt64](_product(2, len(proof.variables)), budget)
    proof.slopes.resize(len(proof.variables), 0)
    proof.offsets.resize(len(proof.variables), 0)
    var state = UInt64(42)
    for prime_index in range(3):
        proof.prime = _prime_at(prime_index)
        for _ in range(8):
            budget.charge(1)
            for i in range(len(proof.variables)):
                budget.charge(1)
                proof.slopes[i] = 1 + _random(state) % (proof.prime - 1)
                proof.offsets[i] = _random(state) % proof.prime
            var a = _project(f, proof, budget)
            var b = _project(g, proof, budget)
            if len(a) != df + 1 or len(b) != dg + 1:
                continue
            var witness = _bezout(a^, b^, proof.prime, budget)
            if witness:
                var pair = witness.take()
                swap(proof.u, pair[0])
                swap(proof.v, pair[1])
                return proof^
    return None


def _try_modular[C: CoefficientRing](f: SparsePoly[C], g: SparsePoly[C], mut budget: Budget) raises PolyError -> Optional[ModularCoprimalityCertificate]:
    # Unit and constant identities remain smaller than a modular witness.
    if _is_unit(f, budget) or _is_unit(g, budget):
        return None
    comptime if C == ZZ:
        return _produce(rebind[SparsePoly[ZZ]](f), rebind[SparsePoly[ZZ]](g), True, budget)
    elif C == QQ:
        return _produce(_integer_image(rebind[SparsePoly[QQ]](f), budget), _integer_image(rebind[SparsePoly[QQ]](g), budget), False, budget)
    else:
        return None


def _canonical(a: List[UInt64], p: UInt64, mut budget: Budget) raises PolyError -> Bool:
    if len(a) and a[len(a) - 1] == 0:
        return False
    for c in a:
        budget.charge(1)
        if c >= p:
            return False
    return True


def _check(f: SparsePoly[ZZ], g: SparsePoly[ZZ], proof: ModularCoprimalityCertificate, integer: Bool, mut budget: Budget) raises PolyError -> Bool:
    budget.charge(1)
    var p = proof.prime
    if p != _prime_at(0) and p != _prime_at(1) and p != _prime_at(2):
        return False
    var df = _degree(f, budget)
    var dg = _degree(g, budget)
    if min(df, dg) < 0 or max(df, dg) > _MAX_DEGREE:
        return False
    var variables = _variables(f, g, budget)
    if len(variables) != len(proof.variables) or len(variables) != len(proof.slopes) or len(variables) != len(proof.offsets):
        return False
    for i in range(len(variables)):
        budget.charge(1)
        if variables[i] != proof.variables[i] or proof.slopes[i] >= p or proof.offsets[i] >= p:
            return False
    if len(proof.u) > max(1, dg) or len(proof.v) > max(1, df) or not _canonical(proof.u, p, budget) or not _canonical(proof.v, p, budget):
        return False
    if len(proof.integer_indices) != len(proof.integer_weights):
        return False
    if integer:
        var total = ZZ(Integer(0))
        var previous = -1
        var count = _sum(len(f.terms), len(g.terms))
        for i in range(len(proof.integer_indices)):
            budget.charge(1)
            var index = proof.integer_indices[i]
            if index <= previous or index >= count or proof.integer_weights[i].is_zero():
                return False
            total = total.add(proof.integer_weights[i].mul(_coefficient(f, g, index), budget), budget)
            previous = index
        if total.value != Integer(1):
            return False
    elif len(proof.integer_indices):
        return False
    var a = _project(f, proof, budget)
    var b = _project(g, proof, budget)
    if len(a) != df + 1 or len(b) != dg + 1:
        return False
    # Verification uses only projection and multiplication, never Euclid/search.
    var identity = _multiply(proof.u, a, p, budget)
    _add(identity, _multiply(proof.v, b, p, budget), p, False, budget)
    return len(identity) == 1 and identity[0] == 1


def _check_modular[C: CoefficientRing](f: SparsePoly[C], g: SparsePoly[C], proof: ModularCoprimalityCertificate, mut budget: Budget) raises PolyError -> Bool:
    f.check_invariants(budget)
    g.check_invariants(budget)
    f._same(g, budget)
    comptime if C == ZZ:
        return _check(rebind[SparsePoly[ZZ]](f), rebind[SparsePoly[ZZ]](g), proof, True, budget)
    elif C == QQ:
        return _check(_integer_image(rebind[SparsePoly[QQ]](f), budget), _integer_image(rebind[SparsePoly[QQ]](g), budget), proof, False, budget)
    else:
        return False
