"""Cheap reductions ahead of multivariate integer gcds.

Deflation: when every exponent of a variable in both inputs is a multiple
of J, substituting x^J -> x is an injective ring map that preserves gcds
over a field of characteristic zero (it maps coprime pairs to coprime
pairs), so gcd(f, h) is the inflated gcd of the deflated pair.

Image test: remove each input's monomial factor in the images, then preserve
its degree in every remaining variable. Constant image gcds in all variables
exclude every nonmonomial common factor. Integer content and common monomial
exponents then give the exact gcd without recursive polynomial contents.
"""
from apn_mojo import Integer
from .errors import Budget, PolyError, _allocation, _charge_size
from .coefficients import CoefficientRing, ZZ
from .sparse import SparsePoly, Term
from .monomial import Monomial
from .primes import prime, _residue
from ._nmod_euclid import _Field, _gcd_words
from ._coefficient_ops import _gcd_coefficient


# Keep this preliminary test bounded for sparse polynomials of huge degree.
comptime _IMAGE_DEGREE_LIMIT = 4096


def _integer_gcd(a: Int, b: Int) -> Int:
    var x = a
    var y = b
    while y:
        var t = x % y
        x = y
        y = t
    return x


def _exponent_gcds[C: CoefficientRing](p: SparsePoly[C], variables: List[Int64], mut out: List[Int], mut ones: Int, mut budget: Budget) raises PolyError:
    """Fold p's exponents into the gcds in out; `ones` counts the gcds equal to one, which no exponent changes."""
    for t in p.terms:
        if ones == len(out):
            return
        budget.charge(1)
        var position = 0
        for pair in t.monomial.pairs:
            while variables[position] != pair[0]:
                position += 1
            if out[position] != 1:
                out[position] = _integer_gcd(out[position], Int(pair[1]))
                if out[position] == 1:
                    ones += 1


def _deflation[C: CoefficientRing](f: SparsePoly[C], h: SparsePoly[C], variables: List[Int64], mut budget: Budget) raises PolyError -> List[Int]:
    """The gcd of all exponents of each variable in both inputs (one for an absent variable)."""
    _allocation[Int](len(variables), budget)
    var out = List[Int](length=len(variables), fill=0)
    var ones = 0
    _exponent_gcds(f, variables, out, ones, budget)
    _exponent_gcds(h, variables, out, ones, budget)
    for i in range(len(out)):
        if out[i] == 0:
            out[i] = 1
    return out^


def _scaled[C: CoefficientRing](p: SparsePoly[C], variables: List[Int64], exponents: List[Int], inflate: Bool, mut budget: Budget) raises PolyError -> SparsePoly[C]:
    """Divide (deflate) or multiply (inflate) each variable's exponents by its factor."""
    _allocation[Term[C]](len(p.terms), budget)
    var terms = List[Term[C]](capacity=len(p.terms))
    for t in p.terms:
        budget.charge(1)
        _charge_size(len(t.monomial.pairs), budget)
        var pairs = List[Tuple[Int64, UInt32]](capacity=len(t.monomial.pairs))
        var position = 0
        for pair in t.monomial.pairs:
            while variables[position] != pair[0]:
                position += 1
            var factor = UInt32(exponents[position])
            pairs.append((pair[0], pair[1] * factor if inflate else pair[1] // factor))
        terms.append(Term[C](Monomial(pairs^, budget), t.coefficient.copy()))
    return SparsePoly[C].from_terms(terms^, p.order, p.ring, budget)


def _deflates(exponents: List[Int]) -> Bool:
    for e in exponents:
        if e > 1:
            return True
    return False


def _degrees(p: SparsePoly[ZZ], variables: List[Int64], mut out: List[Int], mut budget: Budget) raises PolyError:
    """Raise out[i] to the degree of p in variables[i]."""
    for t in p.terms:
        budget.charge(1)
        var position = 0
        for pair in t.monomial.pairs:
            while variables[position] != pair[0]:
                position += 1
            out[position] = max(out[position], Int(pair[1]))


def _residues(p: SparsePoly[ZZ], field: _Field, mut budget: Budget) raises PolyError -> List[UInt64]:
    _allocation[UInt64](len(p.terms), budget)
    var out = List[UInt64](capacity=len(p.terms))
    for t in p.terms:
        budget.charge(1)
        out.append(field.enter(_residue(t.coefficient.value, field.p, budget)))
    return out^


def _minimum_degrees(p: SparsePoly[ZZ], variables: List[Int64], tops: List[Int], mut budget: Budget) raises PolyError -> List[Int]:
    """The exponents of p's monomial content, including zero for absent axes."""
    _allocation[Int](len(variables), budget)
    var out = tops.copy()
    for term in p.terms:
        budget.charge(1)
        var position = 0
        for i in range(len(variables)):
            budget.charge(1)
            if position < len(term.monomial.pairs) and term.monomial.pairs[position][0] == variables[i]:
                out[i] = min(out[i], Int(term.monomial.pairs[position][1]))
                position += 1
            else:
                out[i] = 0
    return out^


def _univariate_image(p: SparsePoly[ZZ], residues: List[UInt64], degree: Int, at: Int, variables: List[Int64], minimum: List[Int], powers: List[List[UInt64]], field: _Field, mut budget: Budget) raises PolyError -> List[UInt64]:
    """Specialize p after removing its monomial content, without copying terms."""
    _allocation[UInt64](degree + 1, budget)
    var out = List[UInt64](length=degree + 1, fill=0)
    for i in range(len(p.terms)):
        budget.charge(1)
        ref pairs = p.terms[i].monomial.pairs
        _charge_size(len(pairs), budget)
        var value = residues[i]
        var e = 0
        var position = 0
        for pair in pairs:
            while variables[position] != pair[0]:
                position += 1
            if position == at:
                e = Int(pair[1]) - minimum[position]
            else:
                value = field.mul(value, powers[position][Int(pair[1]) - minimum[position]])
        out[e] = field.add(out[e], value)
    return out^


def _monomial_result(f: SparsePoly[ZZ], h: SparsePoly[ZZ], variables: List[Int64], minimum_f: List[Int], minimum_h: List[Int], mut budget: Budget) raises PolyError -> SparsePoly[ZZ]:
    """Combine the exact integer content with the known common monomial."""
    var content = ZZ(Integer(0))
    for term in f.terms:
        budget.charge(1)
        content = _gcd_coefficient(content, term.coefficient, budget)
        if content.value == Integer(1):
            break
    if content.value != Integer(1):
        for term in h.terms:
            budget.charge(1)
            content = _gcd_coefficient(content, term.coefficient, budget)
            if content.value == Integer(1):
                break
    _allocation[Tuple[Int64, UInt32]](len(variables), budget)
    var pairs = List[Tuple[Int64, UInt32]]()
    for i in range(len(variables)):
        budget.charge(1)
        var exponent = min(minimum_f[i], minimum_h[i])
        if exponent:
            pairs.append((variables[i], UInt32(exponent)))
    _allocation[Term[ZZ]](1, budget)
    return SparsePoly[ZZ].from_terms([Term[ZZ](Monomial(pairs^, budget), content^)], f.order, f.ring, budget)


def _try_monomial_gcd(f: SparsePoly[ZZ], h: SparsePoly[ZZ], variables: List[Int64], tops_f: List[Int], tops_h: List[Int], mut budget: Budget) raises PolyError -> Tuple[Optional[SparsePoly[ZZ]], Bool]:
    """Try an exact scalar/monomial gcd; also retain a first-axis degree-zero bound.

    Inputs are nonzero, with sorted active variables and their exact degrees.
    A failed search is inconclusive. The second result allows the caller to
    reuse a proved first-axis exclusion when another axis prevents early exit.
    """
    var minimum_f = _minimum_degrees(f, variables, tops_f, budget)
    var minimum_h = _minimum_degrees(h, variables, tops_h, budget)
    for i in range(len(variables)):
        budget.charge(1)
        if max(tops_f[i] - minimum_f[i], tops_h[i] - minimum_h[i]) > _IMAGE_DEGREE_LIMIT:
            return (None, False)
    var field = _Field.of(prime(0, budget))
    var residues_f = _residues(f, field, budget)
    var residues_h = _residues(h, field, budget)
    var first_axis_zero = False
    for attempt in range(3):
        budget.charge(1)
        # Share residues and power tables across all univariate images.
        _allocation[List[UInt64]](len(variables), budget)
        var powers = List[List[UInt64]]()
        for position in range(len(variables)):
            var top = max(tops_f[position] - minimum_f[position], tops_h[position] - minimum_h[position])
            _allocation[UInt64](top + 1, budget)
            var row = List[UInt64](capacity=top + 1)
            var point = field.enter(UInt64(2 + position + attempt * len(variables)))
            var value = field.enter(1)
            for _ in range(top + 1):
                row.append(value)
                value = field.mul(value, point)
            powers.append(row^)
        var complete = True
        for at in range(len(variables)):
            budget.charge(1)
            var df = tops_f[at] - minimum_f[at]
            var dh = tops_h[at] - minimum_h[at]
            # A variable absent from either reduced input cannot divide both.
            if min(df, dh) > 0:
                var a = _univariate_image(f, residues_f, df, at, variables, minimum_f, powers, field, budget)
                var b = _univariate_image(h, residues_h, dh, at, variables, minimum_h, powers, field, budget)
                if a[df] == 0 or b[dh] == 0:
                    complete = False
                    break
                if len(_gcd_words(a^, b^, field, budget)) != 1:
                    return (None, first_axis_zero)
            if at == 0:
                first_axis_zero = min(minimum_f[0], minimum_h[0]) == 0
        if complete:
            return (_monomial_result(f, h, variables, minimum_f, minimum_h, budget), first_axis_zero)
    return (None, first_axis_zero)
