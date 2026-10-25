"""Internal exact quotients and UFD normalization for P2 algorithms."""
from apn_mojo import Integer, div_rem_trunc, gcd as integer_gcd
from .errors import Budget, PolyError, PolyErrorKind, _charge_size, _sum
from .coefficients import CoefficientRing, CoefficientField, ZZ, _work


def _copy[C: CoefficientRing](value: C, mut budget: Budget) raises PolyError -> C:
    _charge_size(value.size(), budget)
    return value.copy()


def _quotient[C: CoefficientRing](a: C, b: C, mut budget: Budget) raises PolyError -> Optional[C]:
    if a.context() != b.context() or b.is_zero():
        raise PolyError(PolyErrorKind.DOMAIN, "invalid coefficient divisor")
    comptime if C == ZZ:
        _work(a.size(), b.size(), True, budget)
        try:
            var qr = div_rem_trunc(rebind[ZZ](a).value, rebind[ZZ](b).value)
            if qr[1] != Integer(0):
                return None
            return rebind_var[C](ZZ(qr[0].copy()))
        except e:
            raise PolyError(PolyErrorKind.CAPACITY, String(e))
    elif conforms_to(C, CoefficientField):
        return a.mul(b.inverse(budget), budget)
    else:
        raise PolyError(PolyErrorKind.UNSUPPORTED, "exact quotient requires ZZ or a coefficient field")


def _exact[C: CoefficientRing](a: C, b: C, mut budget: Budget) raises PolyError -> C:
    var result = _quotient(a, b, budget)
    if not result:
        raise PolyError(PolyErrorKind.DOMAIN, "coefficient quotient is not exact")
    return result.take()


def _gcd_coefficient[C: CoefficientRing](a: C, b: C, mut budget: Budget) raises PolyError -> C:
    if a.context() != b.context():
        raise PolyError(PolyErrorKind.DOMAIN, "different coefficient rings")
    comptime if C == ZZ:
        _work(a.size(), b.size(), True, budget)
        try:
            return rebind_var[C](ZZ(integer_gcd(rebind[ZZ](a).value, rebind[ZZ](b).value)))
        except e:
            raise PolyError(PolyErrorKind.CAPACITY, String(e))
    elif conforms_to(C, CoefficientField):
        budget.charge(1)
        return C.zero(a.context()) if a.is_zero() and b.is_zero() else C.one(a.context())
    else:
        raise PolyError(PolyErrorKind.UNSUPPORTED, "gcd requires ZZ or a coefficient field")


def _unit[C: CoefficientRing](a: C, mut budget: Budget) raises PolyError -> C:
    if a.is_zero():
        return C.one(a.context())
    comptime if C == ZZ:
        budget.charge(1)
        return rebind_var[C](ZZ(Integer(-1 if rebind[ZZ](a).value.sign() < 0 else 1)))
    elif conforms_to(C, CoefficientField):
        return a.inverse(budget)
    else:
        raise PolyError(PolyErrorKind.UNSUPPORTED, "normalization requires ZZ or a coefficient field")


def _integer_bezout(a: ZZ, b: ZZ, mut budget: Budget) raises PolyError -> Tuple[ZZ, ZZ, ZZ]:
    _charge_size(_sum(a.size(), b.size()), budget)
    var f = a.copy()
    var h = b.copy()
    var u0 = ZZ(Integer(1))
    var v0 = ZZ(Integer(0))
    var u1 = ZZ(Integer(0))
    var v1 = ZZ(Integer(1))
    while not h.is_zero():
        budget.charge(1)
        _work(f.size(), h.size(), True, budget)
        var q: ZZ
        var r: ZZ
        try:
            var qr = div_rem_trunc(f.value, h.value)
            q = ZZ(qr[0].copy())
            r = ZZ(qr[1].copy())
        except e:
            raise PolyError(PolyErrorKind.CAPACITY, String(e))
        var u = u0.sub(q.mul(u1, budget), budget)
        var v = v0.sub(q.mul(v1, budget), budget)
        f = h^
        h = r^
        u0 = u1^
        v0 = v1^
        u1 = u^
        v1 = v^
    if f.value.sign() < 0:
        f = f.neg(budget)
        u0 = u0.neg(budget)
        v0 = v0.neg(budget)
    return (f^, u0^, v0^)
