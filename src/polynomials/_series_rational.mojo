"""Rational series by integer arithmetic: composition, inverses and logarithms.

Inverse and logarithm. With f = F / d and c = F_0, U(x) = F(c x) / c is an
integer series with constant term one, so G = 1 / U is integral and
(1 / f)_k = d G_k / c^(k+1). Newton steps for G run on integers through the
low and middle products of `_ntt`, and only the outputs are reduced. For
the logarithm f_0 = 1 forces c = d, and f'/f has coefficients
(F^' G)_k / c^(k+1) with the integer series F^'_j = F'_j c^j.

Composition.

With f = F / d_f and g = G / d_g for integer polynomials F and G,
f(g) = H / (d_f d_g^(m-1)) where H = sum_i F_i d_g^(m-1-i) G^i over the m
coefficients of f. H is computed with integer arithmetic only: the baby steps
G^0 ... G^k and the giant step G^k go through the transform products of
`_ntt`, the block sums are integer multiply-adds, and one division per
output coefficient reduces the fractions. No rational gcd runs inside the
loops.
"""
from apn_mojo import Integer, Rational, lcm
from .coefficient_buffer import _CoefficientView, _view
from .coefficients import ZZ, QQ
from .errors import Budget, PolyError, PolyErrorKind, _allocation, _charge_size, _product
from ._ntt import _ntt_low_product, _ntt_middle_product


def _common(values: _CoefficientView[QQ, _]) raises -> Integer:
    """The lcm of the denominators."""
    var result = Integer(1)
    for i in range(len(values)):
        var d = values[i].value.denominator()
        if d != Integer(1):
            result = lcm(result, d)
    return result^


def _scaled(values: _CoefficientView[QQ, _], scale: Integer) raises -> List[ZZ]:
    var result = List[ZZ](capacity=len(values))
    for i in range(len(values)):
        ref v = values[i].value
        result.append(ZZ(v.numerator() * (scale // v.denominator())))
    return result^


def _powers(base: Integer, count: Int) raises -> List[Integer]:
    """base^0 ... base^(count - 1)."""
    var result = List[Integer](capacity=count)
    var power = Integer(1)
    for _ in range(count):
        result.append(power)
        power = power * base
    return result^


def _fractions(values: List[ZZ], denominator: Integer, length: Int) raises -> List[QQ]:
    var result = List[QQ](capacity=length)
    for t in range(length):
        result.append(QQ(Rational(values[t].value, denominator)) if t < len(values) else QQ(Rational(0)))
    return result^


def _low(a: List[ZZ], b: List[ZZ], length: Int, mut budget: Budget) raises PolyError -> Optional[List[ZZ]]:
    return _ntt_low_product(_view(a), _view(b), length, budget)


def _compose_rational(outer: _CoefficientView[QQ, _], inner: _CoefficientView[QQ, _], length: Int, mut budget: Budget) raises PolyError -> Optional[List[QQ]]:
    """outer(inner) modulo x^length, or None when a transform product does not apply."""
    var m = len(outer)
    if m == 0 or length <= 0:
        return List[QQ]()
    var d_f: Integer
    var d_g: Integer
    var f: List[ZZ]
    var g: List[ZZ]
    var scales: List[Integer]
    try:
        d_f = _common(outer)
        d_g = _common(inner)
        f = _scaled(outer, d_f)
        g = _scaled(inner, d_g)
        scales = _powers(d_g, m) if d_g != Integer(1) else List[Integer]()
    except e:
        raise PolyError(PolyErrorKind.CAPACITY, String(e))
    if len(scales):
        # F_i d_g^(m-1-i).
        for i in range(m):
            f[i] = f[i].mul(ZZ(scales[m - 1 - i]), budget)
    var k = 1
    while k * k < m:
        k += 1
    var blocks = (m + k - 1) // k
    var valuation = len(g) == 0 or g[0].is_zero()
    _allocation[List[ZZ]](k + 1, budget)
    var powers = List[List[ZZ]](capacity=k + 1)
    powers.append([ZZ(Integer(1))])
    for i in range(1, k + 1):
        var next = _low(powers[i - 1], g, length, budget)
        if not next:
            return None
        powers.append(next.take())
    var result = List[ZZ]()
    for j in range(blocks - 1, -1, -1):
        var limit = max(0, length - j * k) if valuation else length
        _charge_size(_product(limit, k) + 1, budget)
        _allocation[ZZ](limit, budget)
        var row = List[ZZ](length=limit, fill=ZZ(Integer(0)))
        for i in range(k):
            var index = j * k + i
            if index >= m or f[index].is_zero():
                continue
            ref p = powers[i]
            for t in range(min(limit, len(p))):
                if not p[t].is_zero():
                    row[t] = row[t].add(f[index].mul(p[t], budget), budget)
        if len(result):
            var shifted = _low(result, powers[k], limit, budget)
            if not shifted:
                return None
            var low = shifted.take()
            for t in range(min(limit, len(low))):
                row[t] = row[t].add(low[t], budget)
        result = row^
    try:
        var denominator = d_f * (d_g ** (m - 1)) if len(scales) else d_f
        return _fractions(result, denominator, min(length, len(result)))
    except e:
        raise PolyError(PolyErrorKind.CAPACITY, String(e))


def _middle(a: List[ZZ], b: List[ZZ], lo: Int, hi: Int, mut budget: Budget) raises PolyError -> Optional[List[ZZ]]:
    return _ntt_middle_product(_view(a), _view(b), lo, hi, budget)


def _unit_inverse(u: List[ZZ], n: Int, mut budget: Budget) raises PolyError -> Optional[List[ZZ]]:
    """1 / u modulo x^n for an integer series with constant term one, by Newton steps."""
    var g: List[ZZ] = [ZZ(Integer(1))]
    var known = 1
    while known < n:
        budget.charge(1)
        var next = min(2 * known, n)
        var prefix = List[ZZ](capacity=min(len(u), next))
        for i in range(min(len(u), next)):
            prefix.append(u[i].copy())
        # u g = 1 + x^known e + O(x^next); the next coefficients are -g e.
        var e = _middle(prefix, g, known, next, budget)
        if not e:
            return None
        var t = _low(g, e.take(), next - known, budget)
        if not t:
            return None
        var correction = t.take()
        for i in range(next - known):
            g.append(correction[i].neg(budget) if i < len(correction) else ZZ(Integer(0)))
        known = next
    return g^


@fieldwise_init
struct _Integral(Movable):
    """f = F / d with c = F_0 and U(x) = F(c x) / c."""
    var f: List[ZZ]
    var d: Integer
    var c: Integer
    var powers: List[Integer]
    """c^0 ... c^n."""
    var u: List[ZZ]


def _integral(values: _CoefficientView[QQ, _], n: Int) raises -> _Integral:
    var d = _common(values)
    var f = _scaled(values, d)
    var c = f[0].value
    var powers = _powers(c, n + 2) if c != Integer(1) else List[Integer]()
    var u = List[ZZ](capacity=min(len(f), n))
    u.append(ZZ(Integer(1)))
    for k in range(1, min(len(f), n)):
        u.append(ZZ(f[k].value * powers[k - 1]) if len(powers) else f[k].copy())
    return _Integral(f^, d^, c^, powers^, u^)


def _ratio(value: Integer, scale: Integer, power: Integer) raises -> QQ:
    return QQ(Rational(value * scale, power))


def _inverse_rational(values: _CoefficientView[QQ, _], n: Int, mut budget: Budget) raises PolyError -> Optional[List[QQ]]:
    """1 / f modulo x^n, or None when f(0) = 0 or a product does not apply."""
    if n < 1 or len(values) == 0 or values[0].is_zero():
        return None
    _charge_size(n, budget)
    var data: _Integral
    try:
        data = _integral(values, n)
    except e:
        raise PolyError(PolyErrorKind.CAPACITY, String(e))
    var g = _unit_inverse(data.u, n, budget)
    if not g:
        return None
    var inverse = g.take()
    _allocation[QQ](n, budget)
    var result = List[QQ](capacity=n)
    try:
        for k in range(n):
            var value = inverse[k].value if k < len(inverse) else Integer(0)
            result.append(_ratio(value, data.d, data.powers[k + 1] if len(data.powers) else Integer(1)))
    except e:
        raise PolyError(PolyErrorKind.CAPACITY, String(e))
    return result^


def _log_rational(values: _CoefficientView[QQ, _], n: Int, mut budget: Budget) raises PolyError -> Optional[List[QQ]]:
    """log f modulo x^n for f(0) = 1, or None for other inputs."""
    if n < 1 or len(values) == 0 or values[0].value != Rational(1):
        return None
    _charge_size(n, budget)
    var data: _Integral
    try:
        data = _integral(values, n)
    except e:
        raise PolyError(PolyErrorKind.CAPACITY, String(e))
    var result = List[QQ](capacity=n)
    result.append(QQ(Rational(0)))
    if n == 1:
        return result^
    var g = _unit_inverse(data.u, n - 1, budget)
    if not g:
        return None
    # F^'_j = (j + 1) F_(j+1) c^j.
    var derivative = List[ZZ](capacity=min(len(data.f), n) - 1)
    for j in range(min(len(data.f), n) - 1):
        var term = data.f[j + 1].mul(ZZ(Integer(j + 1)), budget)
        derivative.append(term.mul(ZZ(data.powers[j]), budget) if len(data.powers) else term^)
    var slope = List[ZZ]()
    if len(derivative):
        var product = _low(derivative, g.take(), n - 1, budget)
        if not product:
            return None
        slope = product.take()
    _allocation[QQ](n, budget)
    try:
        for k in range(1, n):
            var value = slope[k - 1].value if k - 1 < len(slope) else Integer(0)
            var power = data.powers[k] if len(data.powers) else Integer(1)
            result.append(QQ(Rational(value, power * Integer(k))))
    except e:
        raise PolyError(PolyErrorKind.CAPACITY, String(e))
    return result^
