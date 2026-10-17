"""Rational series composition by Brent and Kung's steps over the integers.

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
from ._ntt import _ntt_low_product


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
