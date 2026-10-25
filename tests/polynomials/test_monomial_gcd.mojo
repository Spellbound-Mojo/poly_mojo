"""Global modular early exits, hidden factors, monomial shifts, and unlucky images."""
from apn_mojo import Integer, Rational
from polynomials import Budget, ZZ, QQ, NoContext, SparsePoly, MonomialOrder, PolyError, PolyErrorKind, prime, gcd_value, gcd, check_common_divisor, check_coprimality
from polynomials._gcd import _occurring
from polynomials._multivariate_gcd import _degrees, _try_monomial_gcd
from std.testing import assert_true, assert_false, assert_equal


def attempt(f: SparsePoly[ZZ], g: SparsePoly[ZZ], mut work: Budget) raises PolyError -> Tuple[Optional[SparsePoly[ZZ]], Bool]:
    var variables = _occurring(f, g, work)
    var df = List[Int](length=len(variables), fill=0)
    var dg = List[Int](length=len(variables), fill=0)
    _degrees(f, variables, df, work)
    _degrees(g, variables, dg, work)
    return _try_monomial_gcd(f, g, variables, df, dg, work)


def main() raises:
    var work = Budget()
    var order = MonomialOrder()
    var x = SparsePoly[ZZ].variable(0, order, NoContext(), work)
    var y = SparsePoly[ZZ].variable(1, order, NoContext(), work)
    var z = SparsePoly[ZZ].variable(2, order, NoContext(), work)
    var one = SparsePoly[ZZ].constant(ZZ(Integer(1)), order, work)
    var two = one.scale(ZZ(Integer(2)), work)
    var three = one.scale(ZZ(Integer(3)), work)
    var a = x.add(y, work).add(one, work)
    var b = a.add(one, work)
    var f = a.mul(x.pow(4, work), work).mul(y.pow(2, work), work).scale(ZZ(Integer(-12)), work)
    var g = b.mul(x.pow(2, work), work).mul(y.pow(5, work), work).scale(ZZ(Integer(18)), work)
    var expected = x.pow(2, work).mul(y.pow(2, work), work).scale(ZZ(Integer(6)), work)
    var direct = attempt(f, g, work)
    assert_true(Bool(direct[0]))
    assert_equal(direct[0].value(), expected)
    assert_equal(gcd_value(f, g, work), expected)
    var certified = gcd(f, g, work, certify_maximal=True)
    assert_true(check_common_divisor(f, g, certified, work))
    assert_true(check_coprimality(certified.cofactors[0], certified.cofactors[1], certified.coprimality.value(), work))

    # Passing the x test must not conceal a shared factor involving only y.
    var hidden = y.add(one, work)
    f = hidden.mul(x.add(one, work), work)
    g = hidden.mul(x.add(two, work), work)
    direct = attempt(f, g, work)
    assert_false(Bool(direct[0]))
    assert_true(direct[1])
    assert_equal(gcd_value(f, g, work), hidden)
    # Dropping the leading degree at y=3 cannot certify the hidden factor away.
    hidden = y.sub(three, work).mul(x, work).add(one, work)
    f = hidden.mul(x.add(one, work), work)
    g = hidden.mul(x.add(two, work), work)
    assert_false(Bool(attempt(f, g, work)[0]))
    assert_equal(gcd_value(f, g, work), hidden)
    # The same degree loss on coprime inputs retries with another point.
    f = y.sub(three, work).mul(x, work).add(one, work)
    g = f.add(one, work)
    assert_true(Bool(attempt(f, g, work)[0]))
    assert_equal(gcd_value(f, g, work), one)
    # An accidental common image is inconclusive, with the exact fallback intact.
    f = x.add(y.sub(three, work), work)
    g = x.add(y.sub(three, work).scale(ZZ(Integer(2)), work), work)
    assert_false(Bool(attempt(f, g, work)[0]))
    assert_equal(gcd_value(f, g, work), one)

    # A coefficient prime that erases a factor's leading term is rejected.
    var p = ZZ(Integer(Int(prime(0, work))))
    hidden = x.scale(p, work).add(y, work).add(one, work)
    f = hidden.mul(x.add(one, work), work)
    g = hidden.mul(x.add(two, work), work)
    assert_false(Bool(attempt(f, g, work)[0]))
    assert_equal(gcd_value(f, g, work), hidden)
    # Entire inputs can vanish modulo the chosen prime without losing content.
    assert_equal(gcd_value(a.scale(p, work), b.scale(p, work), work), one.scale(p, work))

    # Different variable sets, constants, and large integer content.
    f = x.mul(y.add(one, work), work)
    g = z.mul(y.add(two, work), work)
    assert_true(Bool(attempt(f, g, work)[0]))
    assert_equal(gcd_value(f, g, work), one)
    var large = ZZ(Integer(1) << 200)
    f = a.scale(large.mul(ZZ(Integer(-6)), work), work)
    g = b.scale(large.mul(ZZ(Integer(9)), work), work)
    assert_equal(gcd_value(f, g, work), one.scale(large.mul(ZZ(Integer(3)), work), work))
    assert_equal(gcd_value(x.scale(ZZ(Integer(6)), work), one.scale(ZZ(Integer(9)), work), work), three)

    # Large shifts use small images; genuinely large degree ranges skip the test.
    hidden = x.pow(1000000, work).mul(y.pow(2000000, work), work)
    f = hidden.mul(a, work)
    g = hidden.mul(b, work)
    assert_equal(attempt(f, g, work)[0].value(), hidden)
    assert_equal(gcd_value(f, g, work), hidden)
    f = x.pow(4097, work).add(y, work)
    assert_false(Bool(attempt(f, a, work)[0]))

    # Exercise arbitrary identifiers and orderings with known coprime cofactors.
    for kind in [MonomialOrder.LEX, MonomialOrder.GRLEX, MonomialOrder.GREVLEX]:
        var chosen = MonomialOrder(kind, [-4, 9, 70], work)
        var u = SparsePoly[ZZ].variable(-4, chosen, NoContext(), work)
        var v = SparsePoly[ZZ].variable(9, chosen, NoContext(), work)
        var w = SparsePoly[ZZ].variable(70, chosen, NoContext(), work)
        var unit = SparsePoly[ZZ].constant(ZZ(Integer(1)), chosen, work)
        for i in range(1, 7):
            var left = u.add(v, work).add(w.scale(ZZ(Integer(i)), work), work).add(unit, work)
            var right = left.add(unit, work)
            var factor = u.pow(UInt64(i), work).mul(v.pow(UInt64(7-i), work), work)
            if i % 2 == 0:
                factor = factor.mul(v.add(unit, work), work)
            var aa = left.mul(factor, work).scale(ZZ(Integer(-10)), work)
            var bb = right.mul(factor, work).scale(ZZ(Integer(15)), work)
            assert_equal(gcd_value(aa, bb, work), factor.scale(ZZ(Integer(5)), work))

    var qx = SparsePoly[QQ].variable(0, order, NoContext(), work)
    var qy = SparsePoly[QQ].variable(1, order, NoContext(), work)
    var qone = SparsePoly[QQ].constant(QQ(Rational(1)), order, work)
    var qa = qx.mul(qy.add(qone, work), work).scale(QQ(Rational(2, 3)), work)
    var qb = qx.pow(2, work).mul(qy.add(qone.scale(QQ(Rational(2)), work), work), work).scale(QQ(Rational(-4, 7)), work)
    assert_equal(gcd_value(qa, qb, work), qx)
    var first = Budget()
    var second = Budget()
    assert_equal(gcd_value(a, b, first), gcd_value(a, b, second))
    assert_equal(first.remaining(), second.remaining())
    var limited = False
    var tiny = Budget(0)
    try:
        _ = attempt(a, b, tiny)
    except e:
        limited = e.kind == PolyErrorKind.LIMIT
    assert_true(limited)
    print("monomial gcd early-exit checks passed")
