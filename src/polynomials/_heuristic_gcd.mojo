"""Heuristic multivariate integer gcds (GCDHEU).

Follows the scheme of Char, Geddes and Gonnet as in SymPy's
dmp_zz_heu_gcd: specialize the first variable at an integer xi larger than
twice the smaller max-norm, take the gcd of the images recursively (one
variable left: the dense multi-modular univariate gcd), and rebuild the
first variable from the symmetric xi-adic digits of every coefficient. The
primitive part of that candidate is the gcd exactly when it divides both
inputs (their theorem, for xi above the bound), which divide_exact
decides. Six growing points are tried; otherwise the caller falls back.
"""
from apn_mojo import Integer, div_rem_euclid, isqrt
from .errors import Budget, PolyError, PolyErrorKind, _allocation, _charge_size
from .coefficients import ZZ, NoContext
from .sparse import SparsePoly, Term
from .dense import DensePoly
from .monomial import Monomial
from .division import divide_exact
from ._coefficient_ops import _gcd_coefficient, _exact
from ._univariate_modular import _univariate_gcd

comptime _ATTEMPTS = 6
comptime _MAX_BITS = 1 << 21
# Inputs with fewer terms than this run GCDHEU before sparse Brown (measured faster there).
comptime _SMALL_TERMS = 512


def _fail(e: Error) -> PolyError:
    return PolyError(PolyErrorKind.CAPACITY, String(e))


def _abs(value: Integer) -> Integer:
    if value.sign() < 0:
        return -value
    return value.copy()


def _mul(a: Integer, b: Integer) raises PolyError -> Integer:
    try:
        return a * b
    except e:
        raise _fail(e)


def _add(a: Integer, b: Integer) raises PolyError -> Integer:
    try:
        return a + b
    except e:
        raise _fail(e)


def _sub(a: Integer, b: Integer) raises PolyError -> Integer:
    try:
        return a - b
    except e:
        raise _fail(e)


def _floordiv(a: Integer, b: Integer) raises PolyError -> Integer:
    try:
        return a // b
    except e:
        raise _fail(e)


def _root(a: Integer) raises PolyError -> Integer:
    try:
        return isqrt(a)
    except e:
        raise _fail(e)


def _half(a: Integer) raises PolyError -> Integer:
    try:
        return a >> 1
    except e:
        raise _fail(e)


def _euclid(a: Integer, b: Integer) raises PolyError -> Tuple[Integer, Integer]:
    try:
        var qr = div_rem_euclid(a, b)
        return (qr[0].copy(), qr[1].copy())
    except e:
        raise _fail(e)


def _max_norm(p: SparsePoly[ZZ], mut budget: Budget) raises PolyError -> Integer:
    var top = Integer(0)
    for t in p.terms:
        budget.charge(1)
        var a = _abs(t.coefficient.value)
        if a > top:
            top = a^
    return top^


def _content(p: SparsePoly[ZZ], mut budget: Budget) raises PolyError -> ZZ:
    var c = ZZ(Integer(0))
    for t in p.terms:
        budget.charge(1)
        c = _gcd_coefficient(c, t.coefficient, budget)
        if c.value == Integer(1):
            break
    return c^


def _scale_down(p: SparsePoly[ZZ], c: ZZ, mut budget: Budget) raises PolyError -> SparsePoly[ZZ]:
    if c.value == Integer(1):
        return p.copy()
    _allocation[Term[ZZ]](len(p.terms), budget)
    var terms = List[Term[ZZ]](capacity=len(p.terms))
    for t in p.terms:
        budget.charge(1)
        terms.append(Term[ZZ](t.monomial.copy(), _exact(t.coefficient, c, budget)))
    var out = SparsePoly[ZZ].zero(p.order, NoContext(), budget)
    out.terms = terms^
    return out^


def _without(m: Monomial, variable: Int64, mut budget: Budget) raises PolyError -> Tuple[Int, Monomial]:
    var pairs = List[Tuple[Int64, UInt32]]()
    var e = 0
    for pair in m.pairs:
        if pair[0] == variable:
            e = Int(pair[1])
        else:
            pairs.append(pair)
    return (e, Monomial(pairs^, budget))


def _evaluate(p: SparsePoly[ZZ], variable: Int64, powers: List[ZZ], mut budget: Budget) raises PolyError -> SparsePoly[ZZ]:
    _allocation[Term[ZZ]](len(p.terms), budget)
    var terms = List[Term[ZZ]](capacity=len(p.terms))
    for t in p.terms:
        budget.charge(1)
        _charge_size(len(t.monomial.pairs), budget)
        var split = _without(t.monomial, variable, budget)
        terms.append(Term[ZZ](split[1].copy(), t.coefficient.mul(powers[split[0]], budget)))
    return SparsePoly[ZZ].from_terms(terms^, p.order, NoContext(), budget)


def _with(m: Monomial, variable: Int64, e: Int, mut budget: Budget) raises PolyError -> Monomial:
    if e == 0:
        return m.copy()
    var pairs = List[Tuple[Int64, UInt32]]()
    var placed = False
    for pair in m.pairs:
        if not placed and pair[0] > variable:
            pairs.append((variable, UInt32(e)))
            placed = True
        pairs.append(pair)
    if not placed:
        pairs.append((variable, UInt32(e)))
    return Monomial(pairs^, budget)


def _interpolate(h: SparsePoly[ZZ], variable: Int64, xi: Integer, mut budget: Budget) raises PolyError -> SparsePoly[ZZ]:
    """Rebuild `variable` from the symmetric xi-adic digits of each coefficient."""
    var half = _half(xi)
    var terms = List[Term[ZZ]]()
    for t in h.terms:
        var c = t.coefficient.value.copy()
        var e = 0
        while c != Integer(0):
            budget.charge(1)
            _charge_size(c.magnitude_bit_length() // 8 + 1, budget)
            var qr = _euclid(c, xi)
            var d = qr[1].copy()
            if d > half:
                d = _sub(d, xi)
            if d != Integer(0):
                _allocation[Term[ZZ]](1, budget)
                terms.append(Term[ZZ](_with(t.monomial, variable, e, budget), ZZ(d.copy())))
            c = _floordiv(_sub(c, d), xi)
            e += 1
    return SparsePoly[ZZ].from_terms(terms^, h.order, NoContext(), budget)


def _variables_of(f: SparsePoly[ZZ], g: SparsePoly[ZZ], mut budget: Budget) raises PolyError -> List[Int64]:
    var vs = f.variables(budget)
    for v in g.variables(budget):
        var found = False
        for w in vs:
            if w == v:
                found = True
        if not found:
            vs.append(v)
    sort(vs)
    return vs^


def _small_for_heuristic(f: SparsePoly[ZZ], g: SparsePoly[ZZ], variables: List[Int64]) -> Bool:
    """Whether to run GCDHEU before sparse Brown: three or more variables and few terms."""
    return len(variables) >= 3 and len(f.terms) + len(g.terms) < _SMALL_TERMS


def _heuristic(f: SparsePoly[ZZ], g: SparsePoly[ZZ], mut budget: Budget) raises PolyError -> Optional[SparsePoly[ZZ]]:
    """The gcd up to sign of two nonzero integer polynomials, or None when the heuristic fails."""
    var abandoned = False
    return _attempt(f, g, abandoned, budget)


def _attempt(f: SparsePoly[ZZ], g: SparsePoly[ZZ], mut abandoned: Bool, mut budget: Budget) raises PolyError -> Optional[SparsePoly[ZZ]]:
    """GCDHEU at one level; `abandoned` reports a size limit anywhere below, which ends all levels."""
    var variables = _variables_of(f, g, budget)
    if not len(variables):
        return SparsePoly[ZZ].constant(_gcd_coefficient(f.terms[0].coefficient, g.terms[0].coefficient, budget), f.order, budget)
    if len(variables) == 1:
        var fd = DensePoly[ZZ].from_sparse(f, budget, variable=variables[0])
        var gd = DensePoly[ZZ].from_sparse(g, budget, variable=variables[0])
        return _univariate_gcd(fd, gd, budget).to_sparse(f.order, budget)
    var variable = variables[0]
    var cf = _content(f, budget)
    var cg = _content(g, budget)
    var common = _gcd_coefficient(cf, cg, budget)
    var pf = _scale_down(f, cf, budget)
    var pg = _scale_down(g, cg, budget)
    var nf = _max_norm(pf, budget)
    var ng = _max_norm(pg, budget)
    var b = _add(_mul(nf.copy() if nf < ng else ng.copy(), Integer(2)), Integer(29))
    var xi = b.copy()
    var root = _mul(Integer(99), _root(b))
    if root < xi:
        xi = root^
    var lf = _floordiv(nf, _abs(pf.terms[len(pf.terms) - 1].coefficient.value))
    var lg = _floordiv(ng, _abs(pg.terms[len(pg.terms) - 1].coefficient.value))
    var floor = _add(_mul(lf.copy() if lf < lg else lg.copy(), Integer(2)), Integer(2))
    if floor > xi:
        xi = floor^
    # Each specialization multiplies coefficient sizes by about deg + 1; give up
    # before the integers at the univariate level become larger than _MAX_BITS.
    var estimate = xi.magnitude_bit_length()
    for i in range(len(variables) - 1):
        estimate *= max(pf.degree_in(variables[i], budget), pg.degree_in(variables[i], budget)) + 1
        if estimate > _MAX_BITS:
            abandoned = True
            return None
    var df = pf.degree_in(variable, budget)
    var dg = pg.degree_in(variable, budget)
    var top = max(df, dg)
    for _ in range(_ATTEMPTS):
        budget.charge(1)
        _allocation[ZZ](top + 1, budget)
        var powers = List[ZZ](capacity=top + 1)
        powers.append(ZZ(Integer(1)))
        for i in range(top):
            powers.append(powers[i].mul(ZZ(xi.copy()), budget))
        var a = _evaluate(pf, variable, powers, budget)
        var c = _evaluate(pg, variable, powers, budget)
        if not a.is_zero() and not c.is_zero():
            var image = _attempt(a, c, abandoned, budget)
            if abandoned:
                return None
            if image:
                var h = _interpolate(image.value(), variable, xi, budget)
                if not h.is_zero():
                    h = _scale_down(h, _content(h, budget), budget)
                    if divide_exact(pf, h, budget) and divide_exact(pg, h, budget):
                        return h.scale(common, budget)
        # SymPy's growth step: xi <- 73794 xi isqrt(isqrt(xi)) / 27011.
        xi = _floordiv(_mul(_mul(Integer(73794), xi), _root(_root(xi))), Integer(27011))
    return None
