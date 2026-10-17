"""Number-theoretic transforms in double precision, for products that need few primes.

Residues modulo primes 2^49.99 < p < 2^50 are exact integers in a Float64, and
every operation below is exact. The bounds hold for any residues below p and
any length, so no input needs the integer kernel instead. The argument needs
IEEE double arithmetic with round-to-nearest and a correctly rounded fma
(hardware FMA, or a correctly rounded software fma; both qualify). With
u = 2^-53:

- _mulmod(a, b) for |a b| <= M p^2, M <= 2. h = fl(a b) has |a b - h| <= u M p^2
  < 2^48, and l = fma(a, b, -h) is that error exactly. fl(h fl(1/p)) is within
  3u M p < 0.375 M of a b / p, so the rounded quotient Q is within one of the
  nearest integer to a b / p and leaves |a b - Q p| <= (0.5 + 0.375 M) p. Q is
  not corrected: the result is a b - Q p, a correct residue in that wider range
  (within 1.25 p), and the stage invariants below absorb it. fma(-Q, p, h) =
  h - Q p is an integer below 2^52, so it is exact, and adding l is exact.
- _reduce(x) for |x| < 4 p: x - Q p, within p / 2 + 1, exactly by one fma.
- _float_garner's mixed-radix digits use products with M <= 2 and reductions
  of values below 3.2 p, then move each digit into [0, q_i).
- Twiddles are reduced, within p / 2 + 1.
- Forward (decimation in frequency): inputs lie in [0, p). With values within p,
  u + v is reduced and (u - v) w has M <= 1, so outputs stay within 0.875 p.
- Pointwise products of values within p have M <= 1: within 0.875 p.
- Inverse (decimation in time): t = v w has M <= 0.5, within 0.69 p, and both
  u + t and u - t (below 1.6 p) are reduced to within p / 2 + 1.
- The final scaling by 1/n < p has M <= 0.5. Every sum is of integers below
  2^52, hence exact.

Eight-lane vectors run every butterfly, the last three stages through lane
shuffles: a convolution runs 2.4-2.7 times faster than the scalar 61-bit
kernel, about twice as fast per bit of modulus. The tables follow _ntt's
layout, entry m + j holding w_2m^j or w_2m^-j.
"""
from std.math import fma

comptime _FPRIME_COUNT = 8
comptime _FPRIMES: Array[UInt64, _FPRIME_COUNT] = [
    1125844072267777, 1125818302464001, 1125809712529409, 1125629323902977,
    1125625028935681, 1125487589982209, 1125281431552001, 1125178352336897,
]
"""Primes c * 2^32 + 1 just below 2^50, largest first."""
comptime _FROOTS: Array[UInt64, _FPRIME_COUNT] = [
    786008014450235, 147641925747491, 981578757977294, 471535527357524,
    417876965932711, 458010413125077, 528161200896742, 698502836831190,
]
"""Roots of unity of order 2^32."""
comptime _FPRIME_BITS = 49
"""Each prime exceeds 2^49.99: k primes hold a symmetric range of 49 k bits."""
comptime _FMAX_LOG = 32
comptime _W = 8


def _fpower(a: UInt64, n: UInt64, q: UInt64) -> UInt64:
    var base = a % q
    var exponent = n
    var result = UInt64(1)
    while exponent:
        if exponent & 1:
            result = UInt64(UInt128(result) * UInt128(base) % UInt128(q))
        exponent >>= 1
        if exponent:
            base = UInt64(UInt128(base) * UInt128(base) % UInt128(q))
    return result


@always_inline
def _mulmod[w: Int](a: SIMD[DType.float64, w], b: SIMD[DType.float64, w], p: SIMD[DType.float64, w], inverse: SIMD[DType.float64, w]) -> SIMD[DType.float64, w]:
    """a * b mod p within (0.5 + 0.375 M) p, for |a b| <= M p^2 with M <= 2."""
    var h = a * b
    var l = fma(a, b, -h)
    var q = (h * inverse).__round__()
    return fma(-q, p, h) + l


@always_inline
def _reduce[w: Int](x: SIMD[DType.float64, w], p: SIMD[DType.float64, w], inverse: SIMD[DType.float64, w]) -> SIMD[DType.float64, w]:
    """x mod p within p / 2 + 1, for |x| < 4 p."""
    return fma(-(x * inverse).__round__(), p, x)


struct _FTables(Movable):
    """Twiddles as signed floats within p / 2: w^-j is -w^(n/2 - j)."""
    var forward: List[Float64]
    var inverse: List[Float64]

    def __init__(out self, q: UInt64, root: UInt64, n: Int):
        self.forward = List[Float64](length=n, fill=0)
        self.inverse = List[Float64](length=n, fill=0)
        if n < 2:
            return
        var half = n // 2
        var log = 0
        while (1 << log) < n:
            log += 1
        var w = _fpower(root, UInt64(1) << UInt64(_FMAX_LOG - log), q)
        var fw = self.forward.unsafe_ptr()
        var x = UInt64(1)
        for j in range(min(half, _W)):
            # Signed representatives keep every twiddle within p / 2.
            fw.unsafe_offset(half + j).unsafe_store(Float64(x) - Float64(q) if x > q // 2 else Float64(x))
            x = UInt64(UInt128(x) * UInt128(w) % UInt128(q))
        if half > _W:
            # Eight independent chains: w^(j + 8) = w^j w^8.
            var prime = Float64(q)
            var p = SIMD[DType.float64, _W](prime)
            var inv = SIMD[DType.float64, _W](1.0 / prime)
            var step = SIMD[DType.float64, _W](Float64(x))
            var j = _W
            while j < half:
                var previous = fw.unsafe_offset(half + j - _W).unsafe_load[width=_W]()
                fw.unsafe_offset(half + j).unsafe_store(_reduce[_W](_mulmod[_W](previous, step, p, inv), p, inv))
                j += _W
        var iv = self.inverse.unsafe_ptr()
        iv.unsafe_offset(half).unsafe_store(1.0)
        for j in range(1, half):
            iv.unsafe_offset(half + j).unsafe_store(-fw.unsafe_offset(n - j).unsafe_load())
        var m = half // 2
        var stride = 2
        while m >= 1:
            for j in range(m):
                fw.unsafe_offset(m + j).unsafe_store(fw.unsafe_offset(half + j * stride).unsafe_load())
                iv.unsafe_offset(m + j).unsafe_store(iv.unsafe_offset(half + j * stride).unsafe_load())
            m //= 2
            stride *= 2


def _fforward(mut a: List[Float64], t: _FTables, prime: Float64):
    """Decimation in frequency; bit-reversed output, values within 0.875 p."""
    var n = len(a)
    var ptr = a.unsafe_ptr()
    var wp = t.forward.unsafe_ptr()
    var m = n // 2
    if n >= 2 * _W:
        var p = SIMD[DType.float64, _W](prime)
        var inv = SIMD[DType.float64, _W](1.0 / prime)
        # Stages m and m / 2 together while both are vector-wide: one pass loads
        # four vectors and applies the same four butterflies in the same order.
        while m >= 2 * _W:
            var h = m // 2
            var s = 0
            while s < n:
                var j = 0
                while j < h:
                    var a0 = ptr.unsafe_offset(s + j).unsafe_load[width=_W]()
                    var a1 = ptr.unsafe_offset(s + j + h).unsafe_load[width=_W]()
                    var a2 = ptr.unsafe_offset(s + j + m).unsafe_load[width=_W]()
                    var a3 = ptr.unsafe_offset(s + j + m + h).unsafe_load[width=_W]()
                    var b0 = _reduce[_W](a0 + a2, p, inv)
                    var b2 = _mulmod[_W](a0 - a2, wp.unsafe_offset(m + j).unsafe_load[width=_W](), p, inv)
                    var b1 = _reduce[_W](a1 + a3, p, inv)
                    var b3 = _mulmod[_W](a1 - a3, wp.unsafe_offset(m + j + h).unsafe_load[width=_W](), p, inv)
                    var w = wp.unsafe_offset(h + j).unsafe_load[width=_W]()
                    ptr.unsafe_offset(s + j).unsafe_store(_reduce[_W](b0 + b1, p, inv))
                    ptr.unsafe_offset(s + j + h).unsafe_store(_mulmod[_W](b0 - b1, w, p, inv))
                    ptr.unsafe_offset(s + j + m).unsafe_store(_reduce[_W](b2 + b3, p, inv))
                    ptr.unsafe_offset(s + j + m + h).unsafe_store(_mulmod[_W](b2 - b3, w, p, inv))
                    j += _W
                s += 2 * m
            m //= 4
        while m >= _W:
            var s = 0
            while s < n:
                var j = 0
                while j < m:
                    var u = ptr.unsafe_offset(s + j).unsafe_load[width=_W]()
                    var v = ptr.unsafe_offset(s + j + m).unsafe_load[width=_W]()
                    var w = wp.unsafe_offset(m + j).unsafe_load[width=_W]()
                    ptr.unsafe_offset(s + j).unsafe_store(_reduce[_W](u + v, p, inv))
                    ptr.unsafe_offset(s + j + m).unsafe_store(_mulmod[_W](u - v, w, p, inv))
                    j += _W
                s += 2 * m
            m //= 2
        # The last three stages inside each vector of eight.
        var p4 = SIMD[DType.float64, 4](prime)
        var inv4 = SIMD[DType.float64, 4](1.0 / prime)
        var w4 = wp.unsafe_offset(4).unsafe_load[width=4]()
        var w2 = wp.unsafe_offset(2).unsafe_load[width=2]()
        var w22 = w2.join(w2)
        var s = 0
        while s < n:
            var x = ptr.unsafe_offset(s).unsafe_load[width=_W]()
            # m = 4: lanes 0-3 against 4-7.
            var u = x.slice[4, offset=0]()
            var v = x.slice[4, offset=4]()
            x = _reduce[4](u + v, p4, inv4).join(_mulmod[4](u - v, w4, p4, inv4))
            # m = 2: pairs 0-1 against 2-3 in each half.
            var y = x.shuffle[0, 1, 4, 5, 2, 3, 6, 7]()
            u = y.slice[4, offset=0]()
            v = y.slice[4, offset=4]()
            x = _reduce[4](u + v, p4, inv4).join(_mulmod[4](u - v, w22, p4, inv4)).shuffle[0, 1, 4, 5, 2, 3, 6, 7]()
            # m = 1: even lanes against odd lanes; the twiddle is one.
            y = x.shuffle[0, 2, 4, 6, 1, 3, 5, 7]()
            u = y.slice[4, offset=0]()
            v = y.slice[4, offset=4]()
            x = _reduce[4](u + v, p4, inv4).join(_reduce[4](u - v, p4, inv4)).shuffle[0, 4, 1, 5, 2, 6, 3, 7]()
            ptr.unsafe_offset(s).unsafe_store(x)
            s += _W
        return
    var p1 = SIMD[DType.float64, 1](prime)
    var inv1 = SIMD[DType.float64, 1](1.0 / prime)
    while m >= 1:
        var s = 0
        while s < n:
            for j in range(m):
                var u = ptr.unsafe_offset(s + j).unsafe_load[width=1]()
                var v = ptr.unsafe_offset(s + j + m).unsafe_load[width=1]()
                var w = wp.unsafe_offset(m + j).unsafe_load[width=1]()
                ptr.unsafe_offset(s + j).unsafe_store(_reduce[1](u + v, p1, inv1))
                ptr.unsafe_offset(s + j + m).unsafe_store(_mulmod[1](u - v, w, p1, inv1))
            s += 2 * m
        m //= 2


def _finverse(mut a: List[Float64], t: _FTables, prime: Float64):
    """Decimation in time without the 1/n factor; bit-reversed input, values within p / 2 + 1."""
    var n = len(a)
    var ptr = a.unsafe_ptr()
    var wp = t.inverse.unsafe_ptr()
    var m = 1
    if n >= 2 * _W:
        var p4 = SIMD[DType.float64, 4](prime)
        var inv4 = SIMD[DType.float64, 4](1.0 / prime)
        var w4 = wp.unsafe_offset(4).unsafe_load[width=4]()
        var w2 = wp.unsafe_offset(2).unsafe_load[width=2]()
        var w22 = w2.join(w2)
        var s = 0
        while s < n:
            var x = ptr.unsafe_offset(s).unsafe_load[width=_W]()
            # m = 1: even lanes against odd lanes; the twiddle is one.
            var y = x.shuffle[0, 2, 4, 6, 1, 3, 5, 7]()
            var u = y.slice[4, offset=0]()
            var v = y.slice[4, offset=4]()
            x = _reduce[4](u + v, p4, inv4).join(_reduce[4](u - v, p4, inv4)).shuffle[0, 4, 1, 5, 2, 6, 3, 7]()
            # m = 2.
            y = x.shuffle[0, 1, 4, 5, 2, 3, 6, 7]()
            u = y.slice[4, offset=0]()
            var tw = _mulmod[4](y.slice[4, offset=4](), w22, p4, inv4)
            x = _reduce[4](u + tw, p4, inv4).join(_reduce[4](u - tw, p4, inv4)).shuffle[0, 1, 4, 5, 2, 3, 6, 7]()
            # m = 4.
            u = x.slice[4, offset=0]()
            tw = _mulmod[4](x.slice[4, offset=4](), w4, p4, inv4)
            ptr.unsafe_offset(s).unsafe_store(_reduce[4](u + tw, p4, inv4).join(_reduce[4](u - tw, p4, inv4)))
            s += _W
        m = _W
        var p = SIMD[DType.float64, _W](prime)
        var inv = SIMD[DType.float64, _W](1.0 / prime)
        # Stages m and 2 m together: four vectors per pass, butterflies unchanged.
        while 4 * m <= n:
            var d = 2 * m
            s = 0
            while s < n:
                var j = 0
                while j < m:
                    var a0 = ptr.unsafe_offset(s + j).unsafe_load[width=_W]()
                    var a1 = ptr.unsafe_offset(s + j + m).unsafe_load[width=_W]()
                    var a2 = ptr.unsafe_offset(s + j + d).unsafe_load[width=_W]()
                    var a3 = ptr.unsafe_offset(s + j + d + m).unsafe_load[width=_W]()
                    var w = wp.unsafe_offset(m + j).unsafe_load[width=_W]()
                    var t1 = _mulmod[_W](a1, w, p, inv)
                    var b0 = _reduce[_W](a0 + t1, p, inv)
                    var b1 = _reduce[_W](a0 - t1, p, inv)
                    var t3 = _mulmod[_W](a3, w, p, inv)
                    var b2 = _reduce[_W](a2 + t3, p, inv)
                    var b3 = _reduce[_W](a2 - t3, p, inv)
                    var u2 = _mulmod[_W](b2, wp.unsafe_offset(d + j).unsafe_load[width=_W](), p, inv)
                    ptr.unsafe_offset(s + j).unsafe_store(_reduce[_W](b0 + u2, p, inv))
                    ptr.unsafe_offset(s + j + d).unsafe_store(_reduce[_W](b0 - u2, p, inv))
                    var u3 = _mulmod[_W](b3, wp.unsafe_offset(d + j + m).unsafe_load[width=_W](), p, inv)
                    ptr.unsafe_offset(s + j + m).unsafe_store(_reduce[_W](b1 + u3, p, inv))
                    ptr.unsafe_offset(s + j + d + m).unsafe_store(_reduce[_W](b1 - u3, p, inv))
                    j += _W
                s += 2 * d
            m *= 4
        while m < n:
            s = 0
            while s < n:
                var j = 0
                while j < m:
                    var u = ptr.unsafe_offset(s + j).unsafe_load[width=_W]()
                    var t1 = _mulmod[_W](ptr.unsafe_offset(s + j + m).unsafe_load[width=_W](), wp.unsafe_offset(m + j).unsafe_load[width=_W](), p, inv)
                    ptr.unsafe_offset(s + j).unsafe_store(_reduce[_W](u + t1, p, inv))
                    ptr.unsafe_offset(s + j + m).unsafe_store(_reduce[_W](u - t1, p, inv))
                    j += _W
                s += 2 * m
            m *= 2
        return
    var p1 = SIMD[DType.float64, 1](prime)
    var inv1 = SIMD[DType.float64, 1](1.0 / prime)
    while m < n:
        var s = 0
        while s < n:
            for j in range(m):
                var u = ptr.unsafe_offset(s + j).unsafe_load[width=1]()
                var t1 = _mulmod[1](ptr.unsafe_offset(s + j + m).unsafe_load[width=1](), wp.unsafe_offset(m + j).unsafe_load[width=1](), p1, inv1)
                ptr.unsafe_offset(s + j).unsafe_store(_reduce[1](u + t1, p1, inv1))
                ptr.unsafe_offset(s + j + m).unsafe_store(_reduce[1](u - t1, p1, inv1))
            s += 2 * m
        m *= 2


def _floats(values: List[UInt64], n: Int) -> List[Float64]:
    """Residues below the prime as floats, zero-padded to n."""
    var out = List[Float64](length=n, fill=0)
    var count = min(n, len(values))
    var src = values.unsafe_ptr()
    var dst = out.unsafe_ptr()
    var i = 0
    while i + _W <= count:
        dst.unsafe_offset(i).unsafe_store(src.unsafe_offset(i).unsafe_load[width=_W]().cast[DType.float64]())
        i += _W
    while i < count:
        dst.unsafe_offset(i).unsafe_store(Float64(src.unsafe_offset(i).unsafe_load()))
        i += 1
    return out^


def _ftransform(values: List[UInt64], tables: _FTables, prime: Float64, n: Int) -> List[Float64]:
    """The forward transform of residues below the prime, zero-padded to n."""
    var x = _floats(values, n)
    _fforward(x, tables, prime)
    return x^


def _fmultiply(x: List[Float64], y: List[Float64], tables: _FTables, prime: Float64, count: Int) -> List[UInt64]:
    """The first `count` cyclic convolution coefficients of two forward transforms, reduced below the prime."""
    var n = len(x)
    var z = List[Float64](length=n, fill=0)
    var px = x.unsafe_ptr()
    var py = y.unsafe_ptr()
    var pz = z.unsafe_ptr()
    var p = SIMD[DType.float64, _W](prime)
    var inv = SIMD[DType.float64, _W](1.0 / prime)
    var p1 = SIMD[DType.float64, 1](prime)
    var inv1 = SIMD[DType.float64, 1](1.0 / prime)
    var i = 0
    while i + _W <= n:
        pz.unsafe_offset(i).unsafe_store(_mulmod[_W](px.unsafe_offset(i).unsafe_load[width=_W](), py.unsafe_offset(i).unsafe_load[width=_W](), p, inv))
        i += _W
    while i < n:
        pz.unsafe_offset(i).unsafe_store(_mulmod[1](px.unsafe_offset(i).unsafe_load[width=1](), py.unsafe_offset(i).unsafe_load[width=1](), p1, inv1))
        i += 1
    _finverse(z, tables, prime)
    # Divide by n and move into [0, q).
    var q = UInt64(prime)
    var scale = Float64(_fpower(UInt64(n), q - 2, q))
    var sv = SIMD[DType.float64, _W](scale)
    var result = List[UInt64](length=count, fill=0)
    var out = result.unsafe_ptr()
    var zero = SIMD[DType.float64, _W](0)
    i = 0
    while i + _W <= count:
        var r = _reduce[_W](_mulmod[_W](pz.unsafe_offset(i).unsafe_load[width=_W](), sv, p, inv), p, inv)
        r = r.lt(zero).select(r + p, r)
        out.unsafe_offset(i).unsafe_store(r.cast[DType.uint64]())
        i += _W
    var s1 = SIMD[DType.float64, 1](scale)
    while i < count:
        var r = _reduce[1](_mulmod[1](pz.unsafe_offset(i).unsafe_load[width=1](), s1, p1, inv1), p1, inv1)[0]
        if r < 0:
            r += prime
        out.unsafe_offset(i).unsafe_store(UInt64(r))
        i += 1
    return result^


def _fconvolve(a: List[UInt64], b: List[UInt64], count: Int, square: Bool, index: Int, n: Int) -> List[UInt64]:
    """The first `count` cyclic convolution coefficients of residues below float prime `index`, reduced below it.

    The transform length n is a power of two; operands are read up to n.
    """
    var primes = materialize[_FPRIMES]()
    var roots = materialize[_FROOTS]()
    var q = primes[index]
    var prime = Float64(q)
    var tables = _FTables(q, roots[index], n)
    var x = _ftransform(a, tables, prime, n)
    if square:
        return _fmultiply(x, x, tables, prime, count)
    return _fmultiply(x, _ftransform(b, tables, prime, n), tables, prime, count)


@always_inline
def _canonical[w: Int](x: SIMD[DType.float64, w], p: SIMD[DType.float64, w], inverse: SIMD[DType.float64, w]) -> SIMD[DType.float64, w]:
    """x mod p in [0, p), for |x| < 4 p."""
    var r = _reduce[w](x, p, inverse)
    return r.lt(SIMD[DType.float64, w](0)).select(r + p, r)


@always_inline
def _garner_lanes[w: Int](r0: SIMD[DType.float64, w], r1: SIMD[DType.float64, w], r2: SIMD[DType.float64, w], q1: SIMD[DType.float64, w], i1: SIMD[DType.float64, w], q2: SIMD[DType.float64, w], i2: SIMD[DType.float64, w], c1: SIMD[DType.float64, w], c2a: SIMD[DType.float64, w], c2: SIMD[DType.float64, w]) -> Tuple[SIMD[DType.float64, w], SIMD[DType.float64, w]]:
    # v1 = (r1 - v0) / q0 mod q1, with v0 = r0 < q0 < 2 q1, so r1 - v0 > -2 q1.
    var v1 = _canonical[w](_mulmod[w](r1 - r0, c1, q1, i1), q1, i1)
    # v2 = (r2 - v0 - v1 q0) / (q0 q1) mod q2.
    var acc = _reduce[w](_mulmod[w](v1, c2a, q2, i2) + r0, q2, i2)
    var v2 = _canonical[w](_mulmod[w](r2 - acc, c2, q2, i2), q2, i2)
    return (v1, v2)


def _float_garner(residues: List[List[UInt64]], moduli: List[UInt64], mut second: List[UInt64], mut third: List[UInt64]):
    """The digits v_1 < q_1 and v_2 < q_2 of x = v_0 + q_0 v_1 + q_0 q_1 v_2, for residues modulo three float primes.

    v_0 is the first residue. Every step is a _mulmod with |a b| < 2 p^2 or a
    reduction of a value below 2^51, so all of it is exact, and each digit is
    the unique representative in [0, q_i): the same digits _digits gives.
    """
    var q0 = moduli[0]
    var q1 = moduli[1]
    var q2 = moduli[2]
    var c1 = _fpower(q0 % q1, q1 - 2, q1)
    var c2a = q0 % q2
    var c2 = _fpower(UInt64((UInt128(q0) * UInt128(q1)) % UInt128(q2)), q2 - 2, q2)
    var count = len(second)
    var a = residues[0].unsafe_ptr()
    var b = residues[1].unsafe_ptr()
    var c = residues[2].unsafe_ptr()
    var out1 = second.unsafe_ptr()
    var out2 = third.unsafe_ptr()
    var vq1 = SIMD[DType.float64, _W](Float64(q1))
    var vi1 = SIMD[DType.float64, _W](1.0 / Float64(q1))
    var vq2 = SIMD[DType.float64, _W](Float64(q2))
    var vi2 = SIMD[DType.float64, _W](1.0 / Float64(q2))
    var i = 0
    while i + _W <= count:
        var digits = _garner_lanes[_W](a.unsafe_offset(i).unsafe_load[width=_W]().cast[DType.float64](), b.unsafe_offset(i).unsafe_load[width=_W]().cast[DType.float64](), c.unsafe_offset(i).unsafe_load[width=_W]().cast[DType.float64](), vq1, vi1, vq2, vi2, SIMD[DType.float64, _W](Float64(c1)), SIMD[DType.float64, _W](Float64(c2a)), SIMD[DType.float64, _W](Float64(c2)))
        out1.unsafe_offset(i).unsafe_store(digits[0].cast[DType.uint64]())
        out2.unsafe_offset(i).unsafe_store(digits[1].cast[DType.uint64]())
        i += _W
    while i < count:
        var digits = _garner_lanes[1](Float64(a.unsafe_offset(i).unsafe_load()), Float64(b.unsafe_offset(i).unsafe_load()), Float64(c.unsafe_offset(i).unsafe_load()), Float64(q1), 1.0 / Float64(q1), Float64(q2), 1.0 / Float64(q2), Float64(c1), Float64(c2a), Float64(c2))
        out1.unsafe_offset(i).unsafe_store(UInt64(digits[0][0]))
        out2.unsafe_offset(i).unsafe_store(UInt64(digits[1][0]))
        i += 1
