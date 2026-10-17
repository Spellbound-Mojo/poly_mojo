"""Truncated products across split boundaries and non-real exact series identities."""
from apn_mojo import Rational, ExactComplex
from polynomials import *
from support.check import Checker
from polynomials._toolkit_exact import _exact_product, _ExactOps
from polynomials._toolkit_ops import _divide_values, _convolve_values
from polynomials._series_ops import _exp_values
from polynomials._series_nmod import _native_series
from polynomials._ntt import _modular_range
from polynomials._fntt import _fconvolve, _FPRIMES, _FPRIME_COUNT
from polynomials._ntt import _transform_length, _ntt_middle_product, _ks_range, _ks_core, _Segments, _zz_range, _transform_quotient, _shoup_quotient, _PRIMES, _PRIME_COUNT
from polynomials.coefficient_buffer import _view
from apn_mojo import Integer


def value[C: CoefficientRing](ctx: C.Context, k: Int, bits: Int) raises -> C:
    """A deterministic coefficient of about `bits` bits, with signs and denominators varying."""
    var x = Integer(k * k * 7919 + 13 * k + 5)
    var magnitude = x
    while magnitude.magnitude_bit_length() < bits:
        magnitude = magnitude * x + Integer(k + 1)
    var signed = -magnitude if k % 3 == 1 else magnitude
    comptime if C == ZZ:
        return rebind_var[C](ZZ(signed))
    elif C == QQ:
        return rebind_var[C](QQ(Rational(signed, Integer(k % 7 + 1))))
    else:
        var p = rebind[Modulus](ctx).value
        var r = UInt64(k * k * 7919 + 13 * k + 5) % p
        return rebind_var[C](ModInt(p - 1 - r if k % 2 else r, rebind[Modulus](ctx)))


def transform_products[C: CoefficientRing](ctx: C.Context, bits: Int, mut check: Checker) raises:
    """Transform truncated products return the work stack's exact lists; middle products agree with the full product."""
    var work = Budget()
    for sizes in [(64, 64), (100, 70), (130, 257), (300, 300)]:
        var a = List[C]()
        var b = List[C]()
        for k in range(sizes[0]):
            a.append(value[C](ctx, k, bits))
        for k in range(sizes[1]):
            b.append(value[C](ctx, k + 1000, bits))
        var full = DensePoly[C].from_coefficients(0, ctx, a.copy(), work).mul_schoolbook(DensePoly[C].from_coefficients(0, ctx, b.copy(), work), work)
        var whole = sizes[0] + sizes[1] - 1
        for length in [64, sizes[0] - 1, max(sizes[0], sizes[1]), max(sizes[0], sizes[1]) + 5, whole, whole + 9]:
            var got = _exact_product(_view(a), _view(b), length, ctx, work)
            var na = min(length, sizes[0])
            var nb = min(length, sizes[1])
            var n = min(length, na + nb - 1)
            # The reference shape: n coefficients, or the trimmed full product truncated to n.
            var expected = List[C]()
            var head_a = List[C]()
            var head_b = List[C]()
            for i in range(na):
                head_a.append(a[i].copy())
            for i in range(nb):
                head_b.append(b[i].copy())
            var full_low = DensePoly[C].from_coefficients(0, ctx, head_a^, work).mul_schoolbook(DensePoly[C].from_coefficients(0, ctx, head_b^, work), work)
            if n <= max(na, nb):
                for i in range(n):
                    expected.append(full_low.coefficients[i].copy() if i < len(full_low.coefficients) else C.zero(ctx))
            else:
                for i in range(min(n, len(full_low.coefficients))):
                    expected.append(full_low.coefficients[i].copy())
            check.check(got == expected, String("transform truncated product ", sizes[0], "x", sizes[1], " to ", length))
        for bounds in [(0, 64), (sizes[0] - 1, sizes[0] + 60), (whole - 70, whole + 5)]:
            var middle = _ntt_middle_product(_view(a), _view(b), bounds[0], bounds[1], work)
            var valid = Bool(middle)
            if middle:
                ref m = middle.value()
                valid = len(m) == bounds[1] - bounds[0]
                for i in range(len(m)):
                    var j = bounds[0] + i
                    var e = full.coefficients[j].copy() if j < len(full.coefficients) else C.zero(ctx)
                    valid = valid and m[i] == e
            check.check(valid, String("middle product ", bounds[0], " to ", bounds[1]))


def segmented(mut check: Checker) raises:
    """Kronecker segmentation agrees with multi-modular CRT on ragged limb counts, signs, zeros and ranges."""
    var work = Budget()
    for sizes in [(1, 1), (5, 3), (40, 70), (130, 129)]:
        var a = List[ZZ]()
        var b = List[ZZ]()
        for k in range(sizes[0]):
            # Limb counts from zero to four, both signs.
            a.append(value[ZZ](NoContext(), k, [0, 1, 64, 130, 250][k % 5]) if k % 7 != 3 else ZZ(Integer(0)))
        for k in range(sizes[1]):
            b.append(value[ZZ](NoContext(), k + 500, [190, 3, 70, 128][k % 4]))
        var whole = sizes[0] + sizes[1] - 1
        for bounds in [(0, whole), (0, 1), (whole // 2, whole + 3), (whole - 1, whole)]:
            var expected = _zz_range(_view(a), _view(b), bounds[0], bounds[1], work)
            var got = _ks_range(_view(a), _view(b), bounds[0], bounds[1], False, work)
            check.check(Bool(got) and Bool(expected) and got.value() == expected.value(), String("segmented range ", sizes[0], "x", sizes[1], " ", bounds[0], "..", bounds[1]))
        # Both prime families of the segmented core agree.
        var la = sizes[0]
        var lb = sizes[1]
        var left = _Segments(_view(a), la, work)
        var right = _Segments(_view(b), lb, work)
        var stride = left.widest + right.widest - 1
        var n = _transform_length((la + lb - 1) * stride)
        var by_float = _ks_core[ZZ, True](left, right, 0, la + lb - 1, stride, n, False, work)
        var by_integer = _ks_core[ZZ, False](left, right, 0, la + lb - 1, stride, n, False, work)
        check.check(Bool(by_float) and Bool(by_integer) and by_float.value() == by_integer.value(), "segmented float and integer primes agree")
        var square = _ks_range(_view(a), _view(a), 0, 2 * sizes[0] - 1, True, work)
        check.check(Bool(square) and square.value() == _zz_range(_view(a), _view(a), 0, 2 * sizes[0] - 1, work).value(), "segmented square")


def transform_quotients(mut check: Checker):
    """The division-free Shoup quotient of the twiddle tables matches the 128-bit division for every transform prime."""
    var primes = materialize[_PRIMES]()
    var valid = True
    for i in range(_PRIME_COUNT):
        var q = primes[i]
        var reciprocal = UInt64((UInt128(1) << 125) // UInt128(q))
        var x = UInt64(i + 1)
        for k in range(200):
            x = x * 6364136223846793005 + 1442695040888963407
            var y = (x >> 2) % q
            if k < 4:
                y = [UInt64(0), UInt64(1), q - 1, q - 2][k]
            valid = valid and _transform_quotient(y, q, reciprocal) == _shoup_quotient(y, q)
    check.check(valid, "transform quotients")


def float_convolutions(mut check: Checker):
    """Double-precision transforms reproduce exact cyclic-free convolutions for every float prime, below and above the vector width."""
    var primes = materialize[_FPRIMES]()
    for index in range(_FPRIME_COUNT):
        var q = primes[index]
        var valid = True
        for la in [1, 3, 8, 9, 17, 100, 300]:
            for lb in [1, 7, 64]:
                var a = List[UInt64]()
                var b = List[UInt64]()
                var x = UInt64(la * 1000 + lb + index)
                for k in range(la):
                    x = x * 6364136223846793005 + 1442695040888963407
                    a.append(q - 1 if k % 5 == 0 else (x >> 14) % q)
                for k in range(lb):
                    x = x * 6364136223846793005 + 1442695040888963407
                    b.append(q - 1 if k % 3 == 0 else (x >> 14) % q)
                var count = la + lb - 1
                var got = _fconvolve(a, b, count, False, index, _transform_length(count))
                var square = _fconvolve(a, a, 2 * la - 1, True, index, _transform_length(2 * la - 1))
                for k in range(count):
                    var e = UInt128(0)
                    for i in range(max(0, k - lb + 1), min(k, la - 1) + 1):
                        e = (e + UInt128(a[i]) * UInt128(b[k - i])) % UInt128(q)
                    valid = valid and UInt64(e) == got[k]
                for k in range(2 * la - 1):
                    var e = UInt128(0)
                    for i in range(max(0, k - la + 1), min(k, la - 1) + 1):
                        e = (e + UInt128(a[i]) * UInt128(a[k - i])) % UInt128(q)
                    valid = valid and UInt64(e) == square[k]
        check.check(valid, String("float convolution modulo ", q))


def native_recurrences(mut check: Checker) raises:
    """Prime-field division, exponential and convolution recurrences on native words satisfy their defining identities."""
    var work = Budget()
    for p in [UInt64(101), (UInt64(1) << 62) - 57]:
        var ctx = Modulus(p, work)
        for n in [31, 32, 33, 100]:
            var a = List[ModInt]()
            var b = List[ModInt]()
            var x = UInt64(n)
            for k in range(n):
                x = x * 6364136223846793005 + 1442695040888963407
                a.append(ModInt(x >> 3, ctx))
                b.append(ModInt(UInt64(1) if k == 0 else p - 1 - (x >> 40) % p, ctx))
            # b (a / b) = a modulo x^n, by schoolbook.
            var q = _divide_values[_ExactOps[ModInt]](_view(a), _view(b), n, ctx, work)
            var back = DensePoly[ModInt].from_coefficients(0, ctx, b.copy(), work).mul_schoolbook(DensePoly[ModInt].from_coefficients(0, ctx, q.copy(), work), work)
            var valid = len(q) == n
            for k in range(n):
                var got = back.coefficients[k].value if k < len(back.coefficients) else UInt64(0)
                valid = valid and got == a[k].value
            check.check(valid, String("native series quotient modulo ", p, ", length ", n))
            # exp(f) with f(0) = 0: g' = f' g modulo x^(n-1).
            if UInt64(n) <= p:
                var f = a.copy()
                f[0] = ModInt(0, ctx)
                var g = _exp_values[_ExactOps[ModInt]](_view(f), n, ctx, work)
                var df = List[ModInt]()
                var dg = List[ModInt]()
                for k in range(1, n):
                    df.append(ModInt(UInt64((UInt128(f[k].value) * UInt128(k)) % UInt128(p)), ctx))
                    dg.append(ModInt(UInt64((UInt128(g[k].value) * UInt128(k)) % UInt128(p)), ctx))
                var rhs = DensePoly[ModInt].from_coefficients(0, ctx, df^, work).mul_schoolbook(DensePoly[ModInt].from_coefficients(0, ctx, g.copy(), work), work)
                var ok = len(g) == n and g[0].value == 1
                for k in range(n - 1):
                    var r = rhs.coefficients[k].value if k < len(rhs.coefficients) else UInt64(0)
                    ok = ok and r == dg[k].value
                check.check(ok, String("native series exponential modulo ", p, ", length ", n))
            var conv = _convolve_values[_ExactOps[ModInt]](_view(a), _view(b), n + 7, ctx, work)
            var full = DensePoly[ModInt].from_coefficients(0, ctx, a.copy(), work).mul_schoolbook(DensePoly[ModInt].from_coefficients(0, ctx, b.copy(), work), work)
            var same = len(conv) == n + 7
            for k in range(n + 7):
                var e = full.coefficients[k].value if k < len(full.coefficients) else UInt64(0)
                same = same and conv[k].value == e
            check.check(same, String("native convolution modulo ", p, ", length ", n))


def routed_series(mut check: Checker) raises:
    """Prime-field inverses and exponentials agree with their identities on both sides of the word/Newton crossovers."""
    var work = Budget()
    var p = (UInt64(1) << 62) - 57
    var ring = Modulus(p, work)
    for n in [1535, 1536, 1537, 3071, 3073]:
        var a = List[ModInt]()
        var x = UInt64(n)
        for k in range(n):
            x = x * 6364136223846793005 + 1442695040888963407
            a.append(ModInt(x >> 3, ring))
        var unit = a.copy()
        unit[0] = ModInt(1, ring)
        var g = _native_series(unit, ring, n, 0, work).value().copy()
        var bu = List[UInt64]()
        var gu = List[UInt64]()
        for k in range(n):
            bu.append(unit[k].value)
            gu.append(g[k].value)
        var product = _modular_range(bu, gu, 0, n, p, work)
        var ok = product[0] == 1
        for k in range(1, n):
            ok = ok and product[k] == 0
        check.check(ok, String("routed series inverse, order ", n))
        var zero = a.copy()
        zero[0] = ModInt(0, ring)
        var e = _native_series(zero, ring, n, 2, work).value().copy()
        var da = List[UInt64]()
        var eu = List[UInt64]()
        for k in range(n):
            eu.append(e[k].value)
            if k:
                da.append(UInt64((UInt128(zero[k].value) * UInt128(k)) % UInt128(p)))
        var rhs = _modular_range(da, eu, 0, n - 1, p, work)
        var fine = e[0].value == 1
        for k in range(n - 1):
            fine = fine and rhs[k] == UInt64((UInt128(e[k + 1].value) * UInt128(k + 1)) % UInt128(p))
        check.check(fine, String("routed series exponential, order ", n))


def main() raises:
    var check = Checker("toolkit_products")
    routed_series(check)
    native_recurrences(check)
    float_convolutions(check)
    transform_quotients(check)
    segmented(check)
    var work = Budget()
    transform_products[ZZ](NoContext(), 8, check)
    transform_products[ZZ](NoContext(), 200, check)
    # Eighteen limbs carry the residue sums past 128 bits and take 38 primes.
    transform_products[ZZ](NoContext(), 1100, check)
    # Past the 48-prime table: Kronecker segmentation.
    transform_products[ZZ](NoContext(), 1600, check)
    transform_products[QQ](NoContext(), 40, check)
    transform_products[ModInt](Modulus(65521, work), 0, check)
    transform_products[ModInt](Modulus((UInt64(1) << 62) - 57, work), 0, check)


    var ctx = Modulus(65521, work)
    for size in [63, 64, 65, 127, 128, 129, 257]:
        for short in [size, size - 3, size // 2]:
            var a = List[ModInt]()
            var b = List[ModInt]()
            for k in range(size):
                a.append(ModInt(UInt64((k * k + 3 * k + 1) % 17), ctx))
            for k in range(short):
                b.append(ModInt(UInt64((k * k + 5 * k + 2) % 19), ctx))
            var f = TruncatedSeries[ModInt].from_polynomial(DensePoly[ModInt].from_coefficients(-2, ctx, a.copy(), work), size, work)
            var g = TruncatedSeries[ModInt].from_polynomial(DensePoly[ModInt].from_coefficients(-2, ctx, b.copy(), work), size, work)
            var got = f.mul(g, work)
            # Independent native-residue oracle, with sums reduced each term.
            var valid = True
            for k in range(size):
                var expected = UInt64(0)
                for i in range(k + 1):
                    if i < len(a) and k - i < len(b):
                        expected = (expected + a[i].value * b[k - i].value) % ctx.value
                var actual = got.polynomial.coefficients[k].value if k < len(got.polynomial.coefficients) else UInt64(0)
                valid = valid and actual == expected
            check.check(valid, "truncated Karatsuba split agrees with modular oracle")
            var saved_f = f.polynomial.copy()
            var saved_g = g.polynomial.copy()
            var tiny = Budget(71)
            try:
                _ = f.mul(g, tiny)
                check.check(False, "truncated product ignored budget")
            except e:
                check.check(e.kind == PolyErrorKind.LIMIT and f.polynomial == saved_f and g.polynomial == saved_g, "product failure preserves operands")
    var imaginary = QQi(ExactComplex(0, 1))
    var long_values = List[ModInt](length=2049, fill=ModInt.one(ctx))
    var long_series = TruncatedSeries[ModInt].from_polynomial(DensePoly[ModInt].from_coefficients(0, ctx, long_values^, work), 2049, work)
    var long_inverse = long_series.inverse(work)
    var long_expected = DensePoly[ModInt].from_coefficients(0, ctx, [ModInt.one(ctx), ModInt.one(ctx).neg(work)], work)
    check.check(long_inverse.polynomial == long_expected, "large modular Newton inverse retains truncation boundary")
    var coefficients = List[QQi](length=65, fill=imaginary)
    var f = TruncatedSeries[QQi].from_polynomial(DensePoly[QQi].from_coefficients(0, NoContext(), coefficients^, work), 65, work)
    var inverse = f.inverse(work)
    var expected = DensePoly[QQi].from_coefficients(0, NoContext(), [QQi(ExactComplex(0, -1)), QQi(ExactComplex(0, 1))], work)
    check.check(inverse.polynomial == expected, "Gaussian rational inverse constant is not real")
    coefficients = List[QQi]()
    coefficients.append(QQi.zero(NoContext()))
    var power = QQi.one(NoContext())
    for _ in range(1, 65):
        coefficients.append(power.copy())
        power = power.mul(imaginary, work)
    f = TruncatedSeries[QQi].from_polynomial(DensePoly[QQi].from_coefficients(0, NoContext(), coefficients^, work), 65, work)
    var reverted = f.revert(work)
    power = QQi.one(NoContext())
    var valid = reverted.polynomial.coefficients[0].is_zero()
    for k in range(1, 65):
        valid = valid and reverted.polynomial.coefficients[k] == power
        power = power.mul(imaginary.neg(work), work)
    check.check(valid, "x/(1-i*x) reverts to x/(1+i*x)")
    check.finish()
