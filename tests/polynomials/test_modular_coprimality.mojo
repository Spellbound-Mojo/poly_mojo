"""Exact affine certificates, adversarial projections, budgets, and legacy fallbacks."""
from apn_mojo import Integer, Rational
from polynomials import Budget, PolyErrorKind, ZZ, QQ, NoContext, SparsePoly, MonomialOrder, ModularCoprimalityCertificate, CoprimalityCertificate, CoprimalityNode, coprimality_certificate, check_coprimality, gcd, check_common_divisor
from polynomials._modular_coprimality import _prime_at, _try_modular
from polynomials.coefficients import _prime
from std.testing import assert_true, assert_false, assert_equal


def main() raises:
    var work = Budget()
    var order = MonomialOrder()
    var x = SparsePoly[ZZ].variable(0, order, NoContext(), work)
    var y = SparsePoly[ZZ].variable(1, order, NoContext(), work)
    var one = SparsePoly[ZZ].constant(ZZ(Integer(1)), order, work)
    var two = ZZ(Integer(2))
    for i in range(3):
        assert_true(_prime(_prime_at(i), work))
    var f = x.mul(y, work)
    var h = x.add(one, work).mul(y.add(one, work), work)
    var optional = coprimality_certificate(f, h, work)
    assert_true(Bool(optional))
    var proof = optional.take()
    assert_true(Bool(proof.modular))
    assert_true(check_coprimality(f, h, proof, work))
    var again = coprimality_certificate(f, h, work)
    assert_equal(String(proof), String(again.value()))
    var factor = x.pow(2, work).add(y, work)
    var result = gcd(f.mul(factor, work), h.mul(factor, work), work, certify_maximal=True)
    assert_true(check_common_divisor(f.mul(factor, work), h.mul(factor, work), result, work))
    assert_true(check_coprimality(result.cofactors[0], result.cofactors[1], result.coprimality.value(), work))

    var bad = proof.copy()
    bad.modular.value().u[0] = (bad.modular.value().u[0] + 1) % bad.modular.value().prime
    assert_false(check_coprimality(f, h, bad, work))
    bad = proof.copy()
    bad.modular.value().prime = 1000000008
    assert_false(check_coprimality(f, h, bad, work))
    bad = proof.copy()
    bad.modular.value().variables[0] = 9
    assert_false(check_coprimality(f, h, bad, work))
    bad = proof.copy()
    bad.modular.value().slopes[0] = bad.modular.value().prime
    assert_false(check_coprimality(f, h, bad, work))
    bad = proof.copy()
    _ = bad.modular.value().offsets.pop()
    assert_false(check_coprimality(f, h, bad, work))
    bad = proof.copy()
    bad.modular.value().u.append(0)
    assert_false(check_coprimality(f, h, bad, work))
    bad = proof.copy()
    bad.modular.value().integer_indices[0] = -1
    assert_false(check_coprimality(f, h, bad, work))
    bad = proof.copy()
    bad.modular.value().integer_indices[0] = len(f.terms) + len(h.terms)
    assert_false(check_coprimality(f, h, bad, work))
    bad = proof.copy()
    bad.modular.value().integer_weights.clear()
    assert_false(check_coprimality(f, h, bad, work))
    bad = proof.copy()
    bad.root = 0
    assert_false(check_coprimality(f, h, bad, work))

    # A shared x becomes a unit on x=1, y=t. Degree preservation must reject it.
    var hidden = ModularCoprimalityCertificate(_prime_at(0), [0, 1], [0, 1], [1, 0], [1], List[UInt64](), [0], [ZZ(Integer(1))])
    var forged = CoprimalityCertificate[ZZ](List[CoprimalityNode[ZZ]](), -1, hidden^)
    assert_false(check_coprimality(x, f, forged, work))
    assert_false(Bool(coprimality_certificate(x, f, work)))
    # x+y becomes 1 on x=t, y=1-t, even though both slopes are nonzero.
    var cancel = ModularCoprimalityCertificate(_prime_at(0), [0, 1], [1, _prime_at(0)-1], [0, 1], [1], List[UInt64](), [0], [ZZ(Integer(1))])
    assert_false(check_coprimality(x.add(y, work), y, CoprimalityCertificate[ZZ](List[CoprimalityNode[ZZ]](), -1, cancel^), work))

    # The modular Bezout identity must not conceal shared integer content 2.
    var p = _prime_at(0)
    var half = (p + 1) // 2
    var scalar = ModularCoprimalityCertificate(p, [0], [1], [0], [p-half], [half], [0], [ZZ(Integer(Int(half)))])
    var a = x.add(one, work).scale(two, work)
    var b = x.add(one.scale(two, work), work).scale(two, work)
    assert_false(check_coprimality(a, b, CoprimalityCertificate[ZZ](List[CoprimalityNode[ZZ]](), -1, scalar^), work))
    assert_false(Bool(coprimality_certificate(a, b, work)))

    # An unlucky prime is inconclusive; search must continue with another prime.
    var unlucky = x.add(one.scale(ZZ(Integer(Int(p))), work), work)
    var retry = coprimality_certificate(x, unlucky, work)
    assert_true(Bool(retry.value().modular))
    assert_equal(retry.value().modular.value().prime, _prime_at(1))
    assert_true(check_coprimality(x, unlucky, retry.value(), work))
    # All admitted primes unlucky: retain the exact fallback.
    var multiple = ZZ(Integer(1))
    for i in range(3):
        multiple = multiple.mul(ZZ(Integer(Int(_prime_at(i)))), work)
    var all_bad = x.add(one.scale(multiple, work), work)
    var fallback = coprimality_certificate(x, all_bad, work)
    assert_false(Bool(fallback.value().modular))
    assert_true(check_coprimality(x, all_bad, fallback.value(), work))
    var high = x.pow(257, work).add(one, work)
    fallback = coprimality_certificate(high, x, work)
    assert_false(Bool(fallback.value().modular))
    assert_true(check_coprimality(high, x, fallback.value(), work))

    # Rational coefficients are cleared exactly; rational scalar factors are units.
    var qx = SparsePoly[QQ].variable(-4, order, NoContext(), work)
    var qy = SparsePoly[QQ].variable(9, order, NoContext(), work)
    var qa = qx.scale(QQ(Rational(2, 3)), work)
    var qb = qy.scale(QQ(Rational(4, 7)), work)
    var rational = coprimality_certificate(qa, qb, work)
    assert_true(Bool(rational.value().modular))
    assert_equal(len(rational.value().modular.value().integer_weights), 0)
    assert_true(check_coprimality(qa, qb, rational.value(), work))
    rational.value().modular.value().integer_indices.append(0)
    rational.value().modular.value().integer_weights.append(ZZ(Integer(1)))
    assert_false(check_coprimality(qa, qb, rational.value(), work))

    var tiny = Budget(0)
    var limited = False
    try:
        _ = check_coprimality(f, h, proof, tiny)
    except e:
        limited = e.kind == PolyErrorKind.LIMIT
    assert_true(limited)
    limited = False
    try:
        _ = _try_modular(f, h, tiny)
    except e:
        limited = e.kind == PolyErrorKind.LIMIT
    assert_true(limited)
    print("modular coprimality checks passed")
