"""Measurement probe for certification by reconstructed standard representations (experiment only).

`_pairs_measure` does what `_pairs_reduce_to_zero` does and, per S-pair,
prints the heights of the rational quotients q_c of its standard
representation S = sum q_c R_c, recovered from the fraction-free reduction:
at column c the entry is v, the row so far carries the scale P, and the
reducer leads with d, so q_c = v / (P d). Each matrix is also reduced
modulo one prime, timed, as the per-prime cost of the modular route.

Lines printed:
  PAIR degree steps work num den lcm lq g s width
  MAT degree pairs rows cols exact_ns mod_ns
`work` is the number of reducer terms touched (one multiply-add each per
prime), num/den the largest quotient numerator and denominator bits, lcm
the bits of the common denominator D, lq the largest bits of D q_c, g the
largest reducer coefficient bits, s the largest S coefficient bits, width
the fraction-free row width in limbs at the end.
"""
from std.math import max
from std.time import perf_counter_ns
from apn_mojo import Integer, div_rem_trunc, gcd as integer_gcd
from .coefficients import ZZ
from .errors import Budget, PolyError, PolyErrorKind, _allocation
from ._f4 import _LANES, _Lanes, _Matrix, _Primes, _Store, _axpy_lanes, _mod_lanes
from .coefficients import Modulus
from ._packed_groebner import _Engine, _div
from ._integer_f4 import _Coefficients, _Row, _bits, _cancel, _limbs_of, _load, _reduces, _remainder

comptime _P = UInt64(2147483629)


def _pow_mod(var b: UInt64, var e: UInt64, p: UInt64) -> UInt64:
    var r = UInt64(1)
    b %= p
    while e:
        if e & 1:
            r = r * b % p
        b = b * b % p
        e >>= 1
    return r


def _residue_of(value: Integer, p: UInt64) -> UInt64:
    var x = _remainder(_limbs_of(value), p)
    if value.sign() < 0 and x != 0:
        x = p - x
    return x


def _pairs_measure[W: Int](mut engine: _Engine[ZZ, W, True], mut budget: Budget) raises PolyError -> Bool:
    engine.sort_active(budget)
    var store = _Store[W]()
    store.extend(engine, budget)
    var coefficients = _Coefficients(engine, budget)
    var p = _P
    # Each element's coefficients modulo p, leading first, and its leading inverse.
    var residues = List[List[UInt64]]()
    var inverses = List[UInt64]()
    for g in range(len(coefficients.limbs)):
        var r = List[UInt64]()
        for k in range(len(coefficients.starts[g]) - 1):
            var limbs = List[UInt64]()
            for l in range(coefficients.starts[g][k], coefficients.starts[g][k + 1]):
                limbs.append(coefficients.limbs[g][l])
            var x = _remainder(limbs, p)
            if coefficients.negative[g][k] and x != 0:
                x = p - x
            r.append(x)
        inverses.append(_pow_mod(r[0], p - 2, p))
        residues.append(r^)
    var rings = List[Modulus]()
    for q in [2147483647, 2147483629, 2147483587, 2147483579, 2147483563, 2147483549, 2147483543, 2147483497]:
        rings.append(Modulus(_prime_value=UInt64(q)))
    var lanes = _Primes(rings)
    # Each element's coefficients modulo the lane primes, made monic, `_LANES` per term.
    var monic = List[List[UInt32]]()
    for g in range(len(coefficients.limbs)):
        var n = len(coefficients.starts[g]) - 1
        var r = List[UInt32](length=_LANES * n, fill=0)
        for l in range(_LANES):
            var q = lanes.primes[l]
            var values = List[UInt64]()
            for k in range(n):
                var limbs = List[UInt64]()
                for t in range(coefficients.starts[g][k], coefficients.starts[g][k + 1]):
                    limbs.append(coefficients.limbs[g][t])
                var x = _remainder(limbs, q)
                if coefficients.negative[g][k] and x != 0:
                    x = q - x
                values.append(x)
            var inv = _pow_mod(values[0], q - 2, q)
            for k in range(n):
                r[_LANES * k + l] = UInt32(values[k] * inv % q)
        monic.append(r^)
    var lane_total = 0
    var factors = List[UInt32](length=_LANES * 1000000, fill=0)
    var quotient = List[UInt64]()
    var exact_total = 0
    var mod_total = 0
    while len(engine.pairs):
        var degree = engine.pairs[0].lcm.degree
        var matrix = _Matrix[W]()
        var halves = List[Int]()
        while len(engine.pairs) and engine.pairs[0].lcm.degree == degree:
            var pair = engine.select(budget)
            halves.append(len(matrix.sources))
            matrix.add_row(engine, store, pair.first, _div(pair.lcm, engine.leads[pair.first]), budget)
            matrix.add_row(engine, store, pair.second, _div(pair.lcm, engine.leads[pair.second]), budget)
        matrix.preprocess(engine, store, budget)
        var order = matrix.number(engine.kind, budget)
        var ncols = len(order)
        var nrows = len(matrix.sources)
        _allocation[Int](ncols, budget)
        var pivot = List[Int](length=ncols, fill=-1)
        for r in range(nrows - 1, -1, -1):
            pivot[Int(matrix.entries[matrix.starts[r]])] = r
        var row = _Row(ncols)
        var t0 = perf_counter_ns()
        for a in halves:
            if not _reduces(row, matrix, pivot, coefficients, a, quotient, budget):
                print("FAIL", degree)
                return False
        var t1 = perf_counter_ns()
        var mrow = List[UInt64](length=ncols, fill=0)
        for a in halves:
            try:
                if not _reduces_mod(mrow, matrix, pivot, coefficients, residues, inverses, a, p):
                    print("MODFAIL", degree)
            except e:
                raise PolyError(PolyErrorKind.CAPACITY, String(e))
        var t2 = perf_counter_ns()
        var dense = List[UInt64](length=_LANES * ncols, fill=0)
        for a in halves:
            if not _reduces_lanes(dense, matrix, pivot, monic, a, lanes, factors):
                print("LANEFAIL", degree)
        var t3 = perf_counter_ns()
        lane_total += Int(t3 - t2)
        exact_total += Int(t1 - t0)
        mod_total += Int(t2 - t1)
        print("MAT", degree, len(halves), nrows, ncols, t1 - t0, t2 - t1, t3 - t2)
        for a in halves:
            _reduces_measure(row, matrix, pivot, coefficients, a, quotient, Int(degree), budget)
    print("TOTAL exact_ns", exact_total, "mod_ns", mod_total, "lanes8_ns", lane_total)
    return True


def _reduces_mod[W: Int](mut mrow: List[UInt64], matrix: _Matrix[W], pivot: List[Int], coefficients: _Coefficients, residues: List[List[UInt64]], inverses: List[UInt64], a: Int, p: UInt64) raises -> Bool:
    var b = a + 1
    var ga = matrix.sources[a]
    var gb = matrix.sources[b]
    var common = integer_gcd(coefficients.leads[ga], coefficients.leads[gb])
    var la = _residue_of(div_rem_trunc(coefficients.leads[gb], common)[0], p)
    var lb = _residue_of(div_rem_trunc(coefficients.leads[ga], common)[0], p)
    var first = Int(matrix.entries[matrix.starts[a]])
    for k in range(matrix.starts[a + 1] - matrix.starts[a]):
        var c = Int(matrix.entries[matrix.starts[a] + k])
        mrow[c] = (mrow[c] + la * residues[ga][k]) % p
    for k in range(matrix.starts[b + 1] - matrix.starts[b]):
        var c = Int(matrix.entries[matrix.starts[b] + k])
        mrow[c] = (mrow[c] + (p - lb) * residues[gb][k]) % p
    var ok = mrow[first] == 0
    mrow[first] = 0
    for c in range(first + 1, len(mrow)):
        var v = mrow[c]
        if v == 0:
            continue
        var q = pivot[c]
        if q < 0:
            ok = False
            mrow[c] = 0
            continue
        var g = matrix.sources[q]
        var f = p - v * inverses[g] % p
        var s = matrix.starts[q]
        ref res = residues[g]
        for k in range(matrix.starts[q + 1] - s):
            var e = Int(matrix.entries.unsafe_get(s + k))
            mrow.unsafe_get(e) = (mrow.unsafe_get(e) + f * res.unsafe_get(k)) % p
    return ok


def _reduces_lanes[W: Int](mut dense: List[UInt64], matrix: _Matrix[W], pivot: List[Int], monic: List[List[UInt32]], a: Int, lanes: _Primes, mut factors: List[UInt32]) -> Bool:
    """S / L of rows a and a + 1 reduced modulo the lane primes; records each step's factor."""
    var data = dense.unsafe_ptr()
    var b = a + 1
    var ga = matrix.sources[a]
    var gb = matrix.sources[b]
    for k in range(matrix.starts[a + 1] - matrix.starts[a]):
        var at = data.unsafe_offset(_LANES * Int(matrix.entries[matrix.starts[a] + k]))
        at.unsafe_store[width=_LANES](at.unsafe_load[width=_LANES]() + monic[ga].unsafe_ptr().unsafe_offset(_LANES * k).unsafe_load[width=_LANES]().cast[DType.uint64]())
    for k in range(matrix.starts[b + 1] - matrix.starts[b]):
        var at = data.unsafe_offset(_LANES * Int(matrix.entries[matrix.starts[b] + k]))
        at.unsafe_store[width=_LANES](at.unsafe_load[width=_LANES]() + lanes.primes - monic[gb].unsafe_ptr().unsafe_offset(_LANES * k).unsafe_load[width=_LANES]().cast[DType.uint64]())
    var first = Int(matrix.entries[matrix.starts[a]])
    data.unsafe_offset(_LANES * first).unsafe_store[width=_LANES](_Lanes(0))
    var ok = True
    var steps = 0
    var ncols = len(dense) // _LANES
    for c in range(first + 1, ncols):
        var at = data.unsafe_offset(_LANES * c)
        var v = at.unsafe_load[width=_LANES]()
        if not v.ne(0).reduce_or():
            continue
        at.unsafe_store[width=_LANES](_Lanes(0))
        v = _mod_lanes(v, lanes)
        if not v.ne(0).reduce_or():
            continue
        var factor = v.eq(0).select(_Lanes(0), lanes.primes - v).cast[DType.uint32]()
        var q = pivot.unsafe_get(c)
        if q < 0:
            ok = False
            continue
        factors.unsafe_ptr().unsafe_offset(_LANES * (steps % 1000000)).unsafe_store[width=_LANES](factor)
        steps += 1
        var s = matrix.starts.unsafe_get(q)
        var n = matrix.starts.unsafe_get(q + 1) - s
        _axpy_lanes(data, matrix.entries.unsafe_ptr().unsafe_offset(s), monic[matrix.sources.unsafe_get(q)].unsafe_ptr(), n, factor, lanes.squares)
    return ok


def _reduces_measure[W: Int](mut row: _Row, matrix: _Matrix[W], pivot: List[Int], coefficients: _Coefficients, a: Int, mut quotient: List[UInt64], degree: Int, mut budget: Budget) raises PolyError:
    var b = a + 1
    var ga = matrix.sources[a]
    var gb = matrix.sources[b]
    var lead_a: Integer
    var lead_b: Integer
    try:
        var common = integer_gcd(coefficients.leads[ga], coefficients.leads[gb])
        lead_a = div_rem_trunc(coefficients.leads[gb], common)[0].copy()
        lead_b = div_rem_trunc(coefficients.leads[ga], common)[0].copy()
    except e:
        raise PolyError(PolyErrorKind.CAPACITY, String(e))
    var fa = _limbs_of(lead_a)
    var fb = _limbs_of(lead_b)
    row.prepare(max(coefficients.bits[ga] + _bits(fa), coefficients.bits[gb] + _bits(fb)) + 1, budget)
    _load(row, matrix, coefficients, a, fa, lead_a.sign() < 0, False, budget)
    _load(row, matrix, coefficients, b, fb, lead_b.sign() < 0, True, budget)
    var first = Int(matrix.entries[matrix.starts[a]])
    row.set_zero(first)
    var sbits = 0
    var c = row.next_marked(first + 1)
    while c < row.ncols:
        if not row.is_zero(c):
            sbits = max(sbits, row.value(c).magnitude_bit_length())
        c = row.next_marked(c + 1)
    var gbits = max(coefficients.bits[ga], coefficients.bits[gb])
    var nums = List[Integer]()
    var dens = List[Integer]()
    var scale = Integer(1)
    var steps = 0
    var work = (matrix.starts[a + 1] - matrix.starts[a]) + (matrix.starts[b + 1] - matrix.starts[b])
    var numbits = 0
    var denbits = 0
    try:
        c = row.next_marked(first + 1)
        while c < row.ncols:
            if row.is_zero(c):
                row.unmark(c)
            else:
                var q = pivot[c]
                var g = matrix.sources[q]
                var v = row.value(c)
                ref d = coefficients.leads[g]
                var den = scale * d
                var h = integer_gcd(v, den)
                var num = div_rem_trunc(v, h)[0].copy()
                den = div_rem_trunc(den, h)[0].copy()
                numbits = max(numbits, num.magnitude_bit_length())
                denbits = max(denbits, den.magnitude_bit_length())
                nums.append(num^)
                dens.append(den^)
                var s = div_rem_trunc(d, integer_gcd(d, v))[0].copy()
                scale = scale * s
                steps += 1
                work += matrix.starts[q + 1] - matrix.starts[q]
                gbits = max(gbits, coefficients.bits[g])
                _cancel(row, matrix, coefficients, c, q, c, quotient, budget)
            c = row.next_marked(c + 1)
        var lcm = Integer(1)
        for i in range(len(dens)):
            var h = integer_gcd(lcm, dens[i])
            lcm = lcm * div_rem_trunc(dens[i], h)[0]
        var lq = 0
        for i in range(len(nums)):
            var x = nums[i] * div_rem_trunc(lcm, dens[i])[0]
            lq = max(lq, x.magnitude_bit_length())
        print("PAIR", degree, steps, work, numbits, denbits, lcm.magnitude_bit_length(), lq, gbits, sbits, row.width)
    except e:
        raise PolyError(PolyErrorKind.CAPACITY, String(e))
