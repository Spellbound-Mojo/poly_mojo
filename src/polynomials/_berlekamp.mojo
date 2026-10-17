"""Berlekamp factorization over tiny prime fields with byte-packed linear algebra.

For p <= 13 every residue fits a byte and a row update a + c b stays below
256, so the Berlekamp matrix Q - I is eliminated 64 bytes per vector step.
The kernel of the transposed matrix spans the polynomials g with
g^p = g mod f; its dimension is the number of irreducible factors, and
gcd(h, v - s) over s in GF(p) splits any piece h for a random kernel
element v. The factor set is unique, so it does not depend on the seed.
"""
from .errors import Budget, PolyError, _allocation, _charge_size, _product
from ._nmod import _Field, _to, _from, _gcd, _divmod_classic, _Random, _trim

comptime _BERLEKAMP_PRIME = UInt64(13)
"""The largest prime whose residues and row updates fit bytes."""
comptime _BERLEKAMP_DEGREE = 4096
"""The largest degree factored by Berlekamp; distinct-degree factorization takes over above."""
comptime _BYTES = 64
comptime _Bytes = SIMD[DType.uint8, _BYTES]


@always_inline
def _reduce_bytes(x: _Bytes, steps: List[UInt8]) -> _Bytes:
    """x mod p for x below 2 steps[0], with steps the multiples 2^k p in decreasing order down to p."""
    var y = x
    for s in steps:
        var v = _Bytes(s)
        y = y.ge(v).select(y - v, y)
    return y


def _reduction_steps(p: UInt64) -> List[UInt8]:
    """2^k p down to p, enough to reduce anything up to p - 1 + (p - 1)^2."""
    var top = (p - 1) + (p - 1) * (p - 1)
    var multiple = p
    while multiple * 2 <= top:
        multiple *= 2
    var steps = List[UInt8]()
    while multiple >= p:
        steps.append(UInt8(multiple))
        multiple //= 2
    return steps^


def _axpy(pt: Pointer[mut=True, UInt8, _], ps: Pointer[mut=False, UInt8, _], start: Int, stop: Int, c: UInt8, steps: List[UInt8], p: UInt8):
    """pt[i] = (pt[i] + c ps[i]) mod p for start <= i < stop; the rows may share a buffer but not overlap."""
    var vc = _Bytes(c)
    var i = start
    while i + _BYTES <= stop:
        var x = pt.unsafe_offset(i).unsafe_load[width=_BYTES]() + vc * ps.unsafe_offset(i).unsafe_load[width=_BYTES]()
        pt.unsafe_offset(i).unsafe_store[width=_BYTES](_reduce_bytes(x, steps))
        i += _BYTES
    while i < stop:
        var x = UInt64(pt.unsafe_offset(i).unsafe_load()) + UInt64(c) * UInt64(ps.unsafe_offset(i).unsafe_load())
        pt.unsafe_offset(i).unsafe_store(UInt8(x % UInt64(p)))
        i += 1


def _axpy_rows(base: Pointer[mut=True, UInt8, _], target: Int, source: Int, start: Int, stop: Int, c: UInt8, steps: List[UInt8], p: UInt8):
    """Row target += c row source mod p within one buffer, for start <= i < stop; the rows do not overlap."""
    var vc = _Bytes(c)
    var i = start
    while i + _BYTES <= stop:
        var x = base.unsafe_offset(target + i).unsafe_load[width=_BYTES]() + vc * base.unsafe_offset(source + i).unsafe_load[width=_BYTES]()
        base.unsafe_offset(target + i).unsafe_store[width=_BYTES](_reduce_bytes(x, steps))
        i += _BYTES
    while i < stop:
        var x = UInt64(base.unsafe_offset(target + i).unsafe_load()) + UInt64(c) * UInt64(base.unsafe_offset(source + i).unsafe_load())
        base.unsafe_offset(target + i).unsafe_store(UInt8(x % UInt64(p)))
        i += 1


def _inverse_small(a: UInt64, p: UInt64) -> UInt64:
    var result = UInt64(1)
    var base = a % p
    var e = p - 2
    while e:
        if e & 1:
            result = result * base % p
        base = base * base % p
        e >>= 1
    return result


def _berlekamp(f: List[UInt64], field: _Field, seed: UInt64, mut budget: Budget) raises PolyError -> List[List[UInt64]]:
    """The monic irreducible factors, in Montgomery form, of a monic squarefree f of degree at least 2 over GF(p), p <= 13."""
    var p = field.p
    var n = len(f) - 1
    var stride = ((n + _BYTES - 1) // _BYTES) * _BYTES
    var steps = _reduction_steps(p)
    var p8 = UInt8(p)
    _allocation[UInt8](_product(n + 2, stride), budget)
    # Plain residues of f below its leading one.
    var lower = List[UInt8](length=stride, fill=0)
    for i in range(n):
        lower[i] = UInt8(_from(f[i], field))
    # B = (Q - I)^T, where row i of Q holds x^(p i) mod f: B[j][i] = Q[i][j] - [i == j].
    _charge_size(_product(_product(n, Int(p)), stride), budget)
    var matrix = List[UInt8](length=_product(n, stride), fill=0)
    var current = List[UInt8](length=stride, fill=0)
    var shifted = List[UInt8](length=stride, fill=0)
    current[0] = 1
    for i in range(n):
        for j in range(n):
            matrix[j * stride + i] = current[j]
        matrix[i * stride + i] = UInt8((UInt64(matrix[i * stride + i]) + p - 1) % p)
        if i + 1 == n:
            break
        # current <- current x^p mod f, one factor of x at a time.
        for _ in range(Int(p)):
            var top = current[n - 1]
            shifted[0] = 0
            for j in range(1, n):
                shifted[j] = current[j - 1]
            for j in range(n, stride):
                shifted[j] = 0
            if top:
                _axpy(shifted.unsafe_ptr(), lower.unsafe_ptr(), 0, stride, UInt8(p - UInt64(top)), steps, p8)
            swap(current, shifted)
    # Row echelon form; rows below the rank are zero left of the current column.
    _charge_size(_product(_product(n, n), stride) // (2 * _BYTES) + 1, budget)
    var pivots = List[Int]()
    var free = List[Int]()
    var rank = 0
    for c in range(n):
        var r = rank
        while r < n and matrix[r * stride + c] == 0:
            r += 1
        if r == n:
            free.append(c)
            continue
        if r != rank:
            for j in range(c, stride):
                var t = matrix[r * stride + j]
                matrix[r * stride + j] = matrix[rank * stride + j]
                matrix[rank * stride + j] = t
        var inverse = _inverse_small(UInt64(matrix[rank * stride + c]), p)
        for j in range(c, n):
            matrix[rank * stride + j] = UInt8(UInt64(matrix[rank * stride + j]) * inverse % p)
        var start = (c // _BYTES) * _BYTES
        var base = matrix.unsafe_ptr()
        for i in range(rank + 1, n):
            var x = matrix[i * stride + c]
            if x:
                _axpy_rows(base, i * stride, rank * stride, start, stride, p8 - x, steps, p8)
        pivots.append(c)
        rank += 1
    var k = len(free)
    if k <= 1:
        var only = List[List[UInt64]]()
        only.append(f.copy())
        return only^
    # Kernel basis: one vector per free column, by back substitution.
    _charge_size(_product(_product(k, rank), n) + 1, budget)
    var basis = List[List[UInt8]](capacity=k)
    for fc in free:
        var v = List[UInt8](length=n, fill=0)
        v[fc] = 1
        var t = rank - 1
        while t >= 0:
            var pc = pivots[t]
            var row = t * stride
            var total = UInt64(0)
            for j in range(pc + 1, n):
                if v[j]:
                    total += UInt64(matrix[row + j]) * UInt64(v[j])
            v[pc] = UInt8((p - total % p) % p)
            t -= 1
        basis.append(v^)
    # Split with random kernel elements until there are k pieces.
    var rng = _Random(seed)
    var pieces = List[List[UInt64]]()
    pieces.append(f.copy())
    while len(pieces) < k:
        budget.charge(1)
        var v = List[UInt64](length=n, fill=0)
        for b in basis:
            var a = rng.next(budget) % p
            if a:
                for j in range(n):
                    v[j] = (v[j] + a * UInt64(b[j])) % p
        var poly = List[UInt64](capacity=n)
        for j in range(n):
            poly.append(_to(v[j], field))
        _trim(poly)
        var next = List[List[UInt64]]()
        for piece in pieces:
            if len(piece) <= 2:
                next.append(piece.copy())
                continue
            var reduced = _divmod_classic(poly, piece, False, field, budget)[1].copy()
            var found = 0
            for s in range(Int(p)):
                var shifted_poly = reduced.copy()
                if len(shifted_poly) == 0:
                    shifted_poly.append(0)
                shifted_poly[0] = _from_sub(shifted_poly[0], _to(UInt64(s), field), field)
                _trim(shifted_poly)
                var d = _gcd(piece, shifted_poly, field, budget)
                if len(d) > 1:
                    found += 1
                    next.append(d^)
            if found == 0:
                next.append(piece.copy())
        pieces = next^
    return pieces^


@always_inline
def _from_sub(a: UInt64, b: UInt64, field: _Field) -> UInt64:
    """a - b for Montgomery residues."""
    return a - b if a >= b else a + field.p - b
