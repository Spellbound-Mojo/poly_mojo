"""Internal content recursion and deterministic modular gcd reconstruction."""
from apn_mojo import Integer
from ._images import _integer_image, _rational_image, _mod_image
from .errors import Budget, PolyError, _allocation, _charge_size, _sum
from .coefficients import CoefficientRing, ZZ, QQ, ModInt, Modulus, NoContext
from ._coefficient_ops import _gcd_coefficient, _unit, _exact
from .sparse import SparsePoly, Term
from .dense import DensePoly
from .division import divide_exact
from ._dense_ops import _gcd as _field_gcd
from ._views import _is_unit
from ._tower import _split, _one, _zero, _constant, _variables, _exact_poly
from ._prs import _prs
from ._univariate_modular import _GcdSearch, _next_gcd_candidate, _univariate_gcd
from .monomial import MonomialOrder
from ._sparse_gcd import _sparse_gcd
from ._heuristic_gcd import _heuristic
from ._brown_gcd import _brown_gcd
from ._sparse_brown import _sparse_brown_gcd
from ._multivariate_gcd import _deflation, _deflates, _scaled, _image_coprime
from .primes import prime, _residue, _merge_residue, _symmetric


# The measured crossover between subresultant and modular gcds.
comptime _MODULAR_THRESHOLD = 8


def _normalized[C: CoefficientRing](p: SparsePoly[C], mut budget: Budget) raises PolyError -> SparsePoly[C]:
    if p.is_zero():
        return p._copy(budget)
    return p.scale(_unit(p.terms[len(p.terms) - 1].coefficient, budget), budget)


def _scalar_content[C: CoefficientRing](p: SparsePoly[C], mut budget: Budget) raises PolyError -> C:
    var content = C.zero(p.ring)
    for term in p.terms:
        budget.charge(1)
        content = _gcd_coefficient(content, term.coefficient, budget)
    return content^


def _divide_scalar[C: CoefficientRing](p: SparsePoly[C], c: C, mut budget: Budget) raises PolyError -> SparsePoly[C]:
    _allocation[Term[C]](len(p.terms), budget)
    var terms = List[Term[C]](capacity=len(p.terms))
    for term in p.terms:
        budget.charge(1)
        _charge_size(len(term.monomial.pairs), budget)
        terms.append(Term[C](term.monomial.copy(), _exact(term.coefficient, c, budget)))
    return SparsePoly[C].from_terms(terms^, p.order, p.ring, budget)


def _primitive_zz(p: SparsePoly[ZZ], mut budget: Budget) raises PolyError -> SparsePoly[ZZ]:
    if p.is_zero():
        return p._copy(budget)
    return _normalized(_divide_scalar(p, _scalar_content(p, budget), budget), budget)


def _modular_primitive(f: SparsePoly[ZZ], h: SparsePoly[ZZ], variable: Int64, mut budget: Budget) raises PolyError -> SparsePoly[ZZ]:
    var fd = DensePoly[ZZ].from_sparse(f, budget, variable=variable)
    var hd = DensePoly[ZZ].from_sparse(h, budget, variable=variable)
    var gamma = _gcd_coefficient(fd.coefficients[len(fd.coefficients) - 1], hd.coefficients[len(hd.coefficients) - 1], budget)
    var state = _GcdSearch(gamma^, min(fd.degree(), hd.degree()) + 1, budget)
    while True:
        budget.charge(1)
        var dense = _next_gcd_candidate(fd, hd, state, budget)
        if dense.degree() == 0:
            return _one(f, budget)
        var candidate = _primitive_zz(dense.to_sparse(f.order, budget), budget)
        if divide_exact(f, candidate, budget) and divide_exact(h, candidate, budget):
            return candidate^


def _content[C: CoefficientRing](p: SparsePoly[C], variable: Int64, mut budget: Budget, heuristic: Bool = True) raises PolyError -> SparsePoly[C]:
    var result = _zero(p, budget)
    for coefficient in _split(p, variable, budget):
        budget.charge(1)
        result = _gcd_value(result, coefficient, budget, heuristic)
        if _is_unit(result, budget):
            break
    return result^


def _dense_in_total_degree[C: CoefficientRing](p: SparsePoly[C], n: Int, mut budget: Budget) raises PolyError -> Bool:
    """Whether p has at least 3/5 of the C(d + n, n) monomials of degree at most its total degree d."""
    var d = 0
    for t in p.terms:
        budget.charge(1)
        var total = 0
        for pair in t.monomial.pairs:
            total += Int(pair[1])
        d = max(d, total)
    # C(d + n, n) built incrementally; stop once it exceeds 5/3 of the term count.
    var count = 1
    var limit = (5 * len(p.terms)) // 3
    for i in range(1, n + 1):
        count = count * (d + i) // i
        if count > limit:
            return False
    return True


def _gcd_value[C: CoefficientRing](f: SparsePoly[C], h: SparsePoly[C], mut budget: Budget, heuristic: Bool = True) raises PolyError -> SparsePoly[C]:
    # heuristic=False skips GCDHEU, for contents of a pair on which it already failed.
    f._same(h, budget)
    if f.is_zero():
        return _normalized(h, budget)
    if h.is_zero():
        return _normalized(f, budget)
    if _is_unit(f, budget) or _is_unit(h, budget):
        return _one(f, budget)
    var variables = _variables(f, h, budget)
    if not len(variables):
        return _constant(f, _gcd_coefficient(f.terms[0].coefficient, h.terms[0].coefficient, budget), budget)
    var variable = variables[0]
    comptime if C == QQ:
        # Clearing denominators scales each input by a unit of QQ, so the monic
        # gcd is that of the integer images; their gcd takes the integer paths.
        var integer_f = _integer_image(rebind[SparsePoly[QQ]](f), budget)
        var integer_h = _integer_image(rebind[SparsePoly[QQ]](h), budget)
        var integer_gcd = _gcd_value(integer_f, integer_h, budget)
        return rebind_var[SparsePoly[C]](_normalized(_rational_image(integer_gcd, budget), budget))
    if len(variables) == 1:
        comptime if C == ModInt:
            var result = _field_gcd(DensePoly[ModInt].from_sparse(rebind[SparsePoly[ModInt]](f), budget, variable=variable), DensePoly[ModInt].from_sparse(rebind[SparsePoly[ModInt]](h), budget, variable=variable), budget)
            return rebind_var[SparsePoly[C]](result.to_sparse(f.order, budget))
    comptime if C == ZZ:
        if len(variables) == 1 and max(f.degree_in(variable, budget), h.degree_in(variable, budget)) >= _MODULAR_THRESHOLD:
            var fd = DensePoly[ZZ].from_sparse(rebind[SparsePoly[ZZ]](f), budget, variable=variable)
            var hd = DensePoly[ZZ].from_sparse(rebind[SparsePoly[ZZ]](h), budget, variable=variable)
            return rebind_var[SparsePoly[C]](_univariate_gcd(fd, hd, budget).to_sparse(f.order, budget))
    var use_heuristic = heuristic
    comptime if C == ZZ:
        if len(variables) > 1:
            var exponents = _deflation(f, h, variables, budget)
            if _deflates(exponents):
                var deflated = _gcd_value(_scaled(f, variables, exponents, False, budget), _scaled(h, variables, exponents, False, budget), budget)
                return _normalized(_scaled(deflated, variables, exponents, True, budget), budget)
            if _image_coprime(rebind[SparsePoly[ZZ]](f), rebind[SparsePoly[ZZ]](h), variable, variables, budget):
                return _normalized(_gcd_value(_content(f, variable, budget), _content(h, variable, budget), budget), budget)
            # Sparse modular interpolation, unless both inputs fill most of their
            # total-degree box, where the subresultant PRS measures faster.
            var dense = _dense_in_total_degree(f, len(variables), budget) and _dense_in_total_degree(h, len(variables), budget)
            # Brown's dense modular gcd first for few variables of high degree,
            # where it measured faster than GCDHEU; GCDHEU first otherwise.
            var high = False
            if len(variables) <= 3:
                for v in variables:
                    if max(f.degree_in(v, budget), h.degree_in(v, budget)) >= 16:
                        high = True
            if dense and high:
                var brown = _brown_gcd(rebind[SparsePoly[ZZ]](f), rebind[SparsePoly[ZZ]](h), variables, budget)
                if brown:
                    return _normalized(rebind_var[SparsePoly[C]](brown.take()), budget)
            if not high:
                var early = _sparse_brown_gcd(rebind[SparsePoly[ZZ]](f), rebind[SparsePoly[ZZ]](h), variables, budget)
                if early:
                    return _normalized(rebind_var[SparsePoly[C]](early.take()), budget)
            if dense and heuristic:
                use_heuristic = False
                var guess = _heuristic(rebind[SparsePoly[ZZ]](f), rebind[SparsePoly[ZZ]](h), budget)
                if guess:
                    return _normalized(rebind_var[SparsePoly[C]](guess.take()), budget)
                var sparse = _sparse_brown_gcd(rebind[SparsePoly[ZZ]](f), rebind[SparsePoly[ZZ]](h), variables, budget)
                if sparse:
                    return _normalized(rebind_var[SparsePoly[C]](sparse.take()), budget)
            if not dense:
                var lex = MonomialOrder(MonomialOrder.LEX, variables.copy(), budget)
                var modular = _sparse_gcd(rebind[SparsePoly[ZZ]](f).reorder(lex, budget), rebind[SparsePoly[ZZ]](h).reorder(lex, budget), budget)
                return _normalized(rebind_var[SparsePoly[C]](modular.reorder(f.order, budget)), budget)
    var cf = _content(f, variable, budget, use_heuristic)
    var ch = _content(h, variable, budget, use_heuristic)
    var common = _gcd_value(cf, ch, budget, use_heuristic)
    var pf = _exact_poly(f, cf, budget)
    var ph = _exact_poly(h, ch, budget)
    var sequence = _prs(pf, ph, variable, False, budget, history=False)
    var last = _zero(f, budget)
    if len(sequence):
        last = sequence[len(sequence) - 1].polynomial._copy(budget)
    elif pf.degree_in(variable, budget) < ph.degree_in(variable, budget):
        last = pf^
    else:
        last = ph^
    var primitive = _exact_poly(last, _content(last, variable, budget, use_heuristic), budget)
    return _normalized(common.mul(primitive, budget), budget)
