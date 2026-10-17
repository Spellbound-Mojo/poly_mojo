"""Exact integer/rational factors, Hensel identities, and corrupted products."""
from apn_mojo import Rational, Integer
from polynomials import Budget, PolyErrorKind, CoefficientRing, QQ, ZZ, NoContext, DensePoly, MonomialOrder, factor, factor_integer, check_factorization, Factorization, Modulus, factor_mod_p, prime
from polynomials.factor import _integer, _rational, _bound
from polynomials._hensel import _hensel, _truncate, _divmod_monic, _long_divmod_monic
from polynomials._dense_ops import _monic, _one
from polynomials._gcd import _mod_image
from support.corpus import read_cases, parse_polynomial, as_zz
from support.check import Checker


def boundaries[C: CoefficientRing](mut c: Checker) raises:
    var work = Budget()
    for value in range(-2, 3):
        var qq = DensePoly[QQ].from_coefficients(19, NoContext(), [QQ(Rational(value))], work)
        comptime if C == QQ:
            var got = factor(qq, work)
            c.check(check_factorization(qq, got, work) and len(got.factors) == 0, "rational constants")
        else:
            var zz = DensePoly[ZZ].from_coefficients(19, NoContext(), [ZZ(Integer(value))], work)
            var got = factor_integer(zz, work)
            c.check(check_factorization(zz, got, work) and len(got.factors) == 0, "integer constants")
    var xq = DensePoly[QQ].from_coefficients(19, NoContext(), [QQ.zero(NoContext()), QQ.one(NoContext())], work)
    var f: DensePoly[C]
    comptime if C == QQ:
        f = rebind_var[DensePoly[C]](xq.copy())
    else:
        f = rebind_var[DensePoly[C]](_integer(xq, work))
    var before = f.copy()
    var tiny = Budget(25)
    try:
        comptime if C == QQ:
            _ = factor(rebind[DensePoly[QQ]](f), tiny)
        else:
            _ = factor_integer(rebind[DensePoly[ZZ]](f), tiny)
        c.check(False, "factor budget ignored")
    except e:
        c.check(e.kind == PolyErrorKind.LIMIT and f == before, "factor budget preserves input")


def zz(values: List[Int], mut work: Budget) raises -> DensePoly[ZZ]:
    var coefficients = List[ZZ]()
    for v in values:
        coefficients.append(ZZ(Integer(v)))
    return DensePoly[ZZ].from_coefficients(0, NoContext(), coefficients^, work)


def repeated_blocks(mut c: Checker) raises:
    # Integer Yun blocks: multiplicities, content and signs survive exactly.
    var work = Budget()
    var a = zz([1, 0, 1], work)
    var b = zz([3, 2], work)
    var d = zz([7, -1, 0, 0, 0, 1], work)
    var e = zz([-1, 1], work)
    var f = a.pow(3, work).mul(b.pow(2, work), work).mul(d, work).mul(e.pow(4, work), work).scale(ZZ(Integer(-6)), work)
    var got = factor_integer(f, work)
    c.check(check_factorization(f, got, work), "repeated blocks reconstruct")
    c.check(got.unit == ZZ(Integer(-6)), "repeated blocks keep signed content")
    c.check(len(got.factors) == 4, "four distinct repeated blocks")
    for entry in got.factors:
        if entry[0] == a:
            c.check(entry[1] == 3, "cube block")
        elif entry[0] == b:
            c.check(entry[1] == 2, "square block")
        elif entry[0] == d:
            c.check(entry[1] == 1, "simple block")
        else:
            c.check(entry[0] == e and entry[1] == 4, "fourth power block")
    var high = zz([-2, 0, 1], work).pow(7, work)
    var seven = factor_integer(high, work)
    c.check(len(seven.factors) == 1 and seven.factors[0][1] == 7, "seventh power")


def main() raises:
    var work = Budget()
    var c = Checker("factor")
    repeated_blocks(c)
    var count = 0
    for record in read_cases():
        var op = record.field("op ")
        if op != "factor" and op != "factor_integer":
            continue
        var text = record.field("in f ")
        var sparse = parse_polynomial(text, MonomialOrder(), work)
        var f = DensePoly[QQ].from_sparse(sparse, work)
        var expected = List[Tuple[DensePoly[QQ], Int]]()
        for line in record.lines:
            if line.startswith("out factor "):
                var parts = line.split(" ")
                var exponent = Int(String(parts[2]))
                var factor_text = String(line[byte=12 + String(exponent).byte_length():])
                expected.append((DensePoly[QQ].from_sparse(parse_polynomial(factor_text, MonomialOrder(), work), work), exponent))
        var unit_text = record.field("out unit ")
        var expected_unit = QQ(Rational(unit_text))
        if op == "factor":
            var got = factor(f, work)
            c.check(got.unit == expected_unit and got.factors == expected, record.name)
            c.check(check_factorization(f, got, work), "rational product certificate")
            got.unit = got.unit.add(QQ.one(NoContext()), work)
            c.check(not check_factorization(f, got, work), "corrupt rational product")
        else:
            var zf = DensePoly[ZZ].from_sparse(as_zz(sparse, work), work)
            var got = factor_integer(zf, work)
            c.check(got.unit.value == expected_unit.value.to_integer_exact() and len(got.factors) == len(expected), record.name)
            for i in range(len(expected)):
                c.check(got.factors[i][1] == expected[i][1] and _rational(got.factors[i][0], work) == expected[i][0], "integer factor")
            c.check(check_factorization(zf, got, work), "integer product certificate")
            got.unit = got.unit.add(ZZ.one(NoContext()), work)
            c.check(not check_factorization(zf, got, work), "corrupt integer product")
        count += 1
    c.check(count == 21, "all twenty-one integer/rational factor cases")
    boundaries[QQ](c)
    boundaries[ZZ](c)
    # Planted primitive irreducibles: linear factors and positive quadratics.
    for n in range(1, 9):
        var a = DensePoly[ZZ].from_coefficients(-3, NoContext(), [ZZ(Integer(-n)), ZZ(Integer(2 * n + 1))], work)
        var b = DensePoly[ZZ].from_coefficients(-3, NoContext(), [ZZ(Integer(n)), ZZ(Integer(0)), ZZ(Integer(1))], work)
        var f = a.pow(2, work).mul(b.pow(UInt64(n % 3 + 1), work), work).scale(ZZ(Integer(-6)), work)
        var got = factor_integer(f, work)
        c.check(got.unit.value == Integer(-6) and len(got.factors) == 2, "planted unit and count")
        c.check(got.factors[0][0] == a and got.factors[0][1] == 2 and got.factors[1][0] == b and got.factors[1][1] == n % 3 + 1, "planted irreducibles and multiplicities")
        c.check(check_factorization(f, got, work), "planted product")
        got.factors[0][1] = 0
        c.check(not check_factorization(f, got, work), "zero exponent refused")
        got.factors[0][1] = -1
        c.check(not check_factorization(f, got, work), "negative exponent refused")
    # Force several base-p correction digits, including a nonmonic input.
    var h = DensePoly[ZZ].from_coefficients(0, NoContext(), [ZZ(Integer(35)), ZZ(Integer(31)), ZZ(Integer(6))], work)
    var ctx = Modulus(13, work)
    var fs = factor_mod_p(_monic(_mod_image(h, ctx, work), work), work, 42)
    var lifted = _hensel(h, fs, _bound(h, work), work)
    var product = DensePoly[ZZ].from_coefficients(0, NoContext(), [ZZ(Integer(6))], work)
    for g in lifted[0]:
        c.check(g.coefficients[g.degree()].value == Integer(1), "lift preserves monicity")
        product = product.mul(g, work)
    c.check(_truncate(h.sub(product, work), lifted[1], work).is_zero(), "Hensel product modulo lifted prime power")
    var first_prime = Integer(Int(prime(0, work)))
    for unlucky in range(2):
        var a = DensePoly[ZZ].from_coefficients(0, NoContext(), [ZZ(Integer(1)), ZZ(first_prime.copy() if unlucky == 0 else Integer(1))], work)
        var b = DensePoly[ZZ].from_coefficients(0, NoContext(), [ZZ(Integer(2) if unlucky == 0 else first_prime + Integer(1)), ZZ(Integer(1))], work)
        var input = a.mul(b, work)
        var got = factor_integer(input, work)
        c.check(len(got.factors) == 2 and ((got.factors[0][0] == a and got.factors[1][0] == b) or (got.factors[0][0] == b and got.factors[1][0] == a)), "skip first prime with degree drop or repeated modular factor")
        c.check(check_factorization(input, got, work), "unlucky factorization product")
        # Measure a warm deterministic call, then stop one work unit short.
        var measured = Budget()
        _ = factor_integer(input, measured)
        var late = Budget(UInt64.MAX - measured.remaining() - 1)
        var original = input.copy()
        try:
            _ = factor_integer(input, late)
            c.check(False, "late factorization budget ignored")
        except e:
            c.check(e.kind == PolyErrorKind.LIMIT and input == original, "late budget fails closed without changing input")
    # Division by a power series inverse agrees with long division modulo M.
    var division_work = Budget()
    var big_modulus = Integer(1)
    for _ in range(40):
        big_modulus = big_modulus * Integer(1000003)
    var division_modulus = ZZ(big_modulus.copy())
    var state = Integer(12345)
    var dividend_values = List[ZZ]()
    var divisor_values = List[ZZ]()
    for i in range(301):
        state = (state * Integer(6364136223) + Integer(1442695)) % big_modulus
        dividend_values.append(ZZ(state - Integer(1000003)))
        if i < 120:
            divisor_values.append(ZZ(state % Integer(998244353) - Integer(499122176)))
    divisor_values.append(ZZ(Integer(1)))
    var numerator = _truncate(DensePoly[ZZ].from_coefficients(0, NoContext(), dividend_values^, division_work), division_modulus, division_work)
    var monic_divisor = DensePoly[ZZ].from_coefficients(0, NoContext(), divisor_values^, division_work)
    var fast = _divmod_monic(numerator, monic_divisor, division_modulus, division_work)
    var slow = _long_divmod_monic(numerator, monic_divisor, division_modulus, division_work)
    c.check(fast[0] == slow[0] and fast[1] == slow[1] and fast[1].degree() < monic_divisor.degree(), "series-inverse division matches long division")
    c.finish()
