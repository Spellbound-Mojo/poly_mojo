# Microbenchmark: the certificate's per-pair lane sweep against a blocked kernel,
# on a real degree matrix dumped as text:
#   MATRIX degree ncols nrows npairs
#   R element col0 col1 ...      (one line per row; col0 is the leading column)
#   H a b                        (one line per pair: its two half rows)
# Usage: blocked_bench FILE DEGREE
# Values are pseudo-random monic residues per (element, term), the same for both
# kernels; both reduce every pair modulo the same 8 primes and record the factor
# met at every pivot column, which are compared.
from std.sys import argv
from std.time import perf_counter_ns
from std.bit import count_trailing_zeros

comptime L = 8
comptime V = SIMD[DType.uint64, L]
comptime B = 16
comptime PL = 32
comptime VP = SIMD[DType.uint64, PL]


@always_inline
def vmodp(v: VP, p: VP, r: SIMD[DType.float64, PL]) -> VP:
    var q = (v.cast[DType.float64]() * r).cast[DType.uint64]()
    var x = v - q * p
    x = (x >> 63).ne(0).select(x + p, x)
    return x.ge(p).select(x - p, x)


def value(g: Int, k: Int, p: UInt64) -> UInt64:
    if k == 0:
        return 1
    var x = UInt64(g) * 0x9E3779B97F4A7C15 + UInt64(k) * 0xBF58476D1CE4E5B9
    x ^= x >> 31
    x *= 0x94D049BB133111EB
    x ^= x >> 29
    return x % p


@always_inline
def vmod(v: V, p: V, r: SIMD[DType.float64, L]) -> V:
    var q = (v.cast[DType.float64]() * r).cast[DType.uint64]()
    var x = v - q * p
    x = (x >> 63).ne(0).select(x + p, x)
    return x.ge(p).select(x - p, x)


def main() raises:
    var args = argv()
    var path = String(args[1])
    var want = Int(String(args[2]))
    var text = open(path, "r").read()
    var lines = text.split("\n")
    var ncols = 0
    var sources = List[Int]()
    var starts = List[Int]()
    var entries = List[Int]()
    var halves = List[Tuple[Int, Int]]()
    var inside = False
    starts.append(0)
    for line in lines:
        var t = line.split(" ")
        if line.byte_length() == 0 or len(t) == 0:
            continue
        if t[0] == "MATRIX":
            inside = Int(String(t[1])) == want
            if inside:
                ncols = Int(String(t[2]))
            continue
        if not inside:
            continue
        if t[0] == "R":
            sources.append(Int(String(t[1])))
            for i in range(2, len(t)):
                entries.append(Int(String(t[i])))
            starts.append(len(entries))
        elif t[0] == "H":
            halves.append((Int(String(t[1])), Int(String(t[2]))))
    var nrows = len(sources)
    var pivot = List[Int](length=ncols, fill=-1)
    for r in range(nrows - 1, -1, -1):
        pivot[entries[starts[r]]] = r
    var npairs = len(halves)
    print("degree", want, "cols", ncols, "rows", nrows, "pairs", npairs)
    var primes = V(0)
    var plist = List[UInt64]()
    var cand = UInt64(1) << 31
    while len(plist) < L:
        cand -= 1
        var ok = True
        var d = UInt64(2)
        while d * d <= cand:
            if cand % d == 0:
                ok = False
                break
            d += 1
        if ok:
            plist.append(cand)
    for l in range(L):
        primes[l] = plist[l]
    var squares = primes * primes
    var recips = SIMD[DType.float64, L](1.0) / primes.cast[DType.float64]()
    # Per-row values, 8 primes per term (kernel A), and per prime per term (kernel B).
    var vals8 = List[UInt32](length=L * len(entries), fill=0)
    for r in range(nrows):
        for k in range(starts[r + 1] - starts[r]):
            for l in range(L):
                vals8[L * (starts[r] + k) + l] = UInt32(value(sources[r], k, plist[l]))
    # ---------------- Kernel A: per pair, primes in lanes ----------------
    var factorsA = List[UInt32](length=npairs * ncols * 0 + 1, fill=0)
    var checksumA = UInt64(0)
    var useful = 0
    var row = List[UInt64](length=L * ncols, fill=0)
    var t0 = perf_counter_ns()
    for pi in range(npairs):
        var a = halves[pi][0]
        var b = halves[pi][1]
        var data = row.unsafe_ptr()
        for k in range(starts[a + 1] - starts[a]):
            var at = data.unsafe_offset(L * entries[starts[a] + k])
            at.unsafe_store[width=L](at.unsafe_load[width=L]() + vals8.unsafe_ptr().unsafe_offset(L * (starts[a] + k)).unsafe_load[width=L]().cast[DType.uint64]())
        for k in range(starts[b + 1] - starts[b]):
            var at = data.unsafe_offset(L * entries[starts[b] + k])
            at.unsafe_store[width=L](at.unsafe_load[width=L]() + primes - vals8.unsafe_ptr().unsafe_offset(L * (starts[b] + k)).unsafe_load[width=L]().cast[DType.uint64]())
        var first = entries[starts[a]]
        data.unsafe_offset(L * first).unsafe_store[width=L](V(0))
        for c in range(first + 1, ncols):
            var at = data.unsafe_offset(L * c)
            var raw = at.unsafe_load[width=L]()
            if not raw.ne(0).reduce_or():
                continue
            at.unsafe_store[width=L](V(0))
            var v = vmod(raw, primes, recips)
            if not v.ne(0).reduce_or():
                continue
            var q = pivot[c]
            if q < 0:
                continue
            checksumA += v.reduce_add()
            var f = v.eq(0).select(V(0), primes - v)
            var s = starts[q]
            var n = starts[q + 1] - s
            useful += n - 1
            for k in range(1, n):
                var e = entries.unsafe_get(s + k)
                var at2 = data.unsafe_offset(L * e)
                var x = at2.unsafe_load[width=L]() + f * vals8.unsafe_ptr().unsafe_offset(L * (s + k)).unsafe_load[width=L]().cast[DType.uint64]()
                at2.unsafe_store[width=L](x.ge(squares).select(x - squares, x))
    var tA = perf_counter_ns() - t0
    print("A per-pair: ms", tA // 1000000, "useful prime-terms", useful * L, "ns per useful prime-term", Float64(tA) / Float64(useful * L))
    # ---------------- Kernel B: 8 pairs in lanes, one prime, blocks of B pivots ----------------
    # Blocks of B consecutive pivot columns, each with its delayed entries
    # (terms of its rows outside the block's pivot columns) grouped by column.
    var t1 = perf_counter_ns()
    var pcols = List[Int]()
    for c in range(ncols):
        if pivot[c] >= 0:
            pcols.append(c)
    var nblocks = (len(pcols) + B - 1) // B
    var block_of = List[Int](length=ncols, fill=-1)
    for i in range(len(pcols)):
        block_of[pcols[i]] = i // B
    # Immediate (inside-block pivot columns) and delayed entries per block.
    var imm_start = List[Int](capacity=nblocks + 1)
    var imm_row = List[Int]()    # index i in block of the row
    var imm_col = List[Int]()
    var imm_term = List[Int]()   # global term index (for values)
    var del_start = List[Int](capacity=nblocks + 1)
    var col_start = List[Int]()  # per delayed column group: start into del entries
    var col_id = List[Int]()
    var del_row = List[Int]()
    var del_term = List[Int]()
    imm_start.append(0)
    del_start.append(0)
    col_start.append(0)
    var scratch_cols = List[Int]()
    var bucket = Dict[Int, List[Tuple[Int, Int]]]()
    for blk in range(nblocks):
        var lo = blk * B
        var hi = min(lo + B, len(pcols))
        bucket = Dict[Int, List[Tuple[Int, Int]]]()
        scratch_cols.clear()
        for i in range(lo, hi):
            var r = pivot[pcols[i]]
            for k in range(starts[r] + 1, starts[r + 1]):
                var e = entries[k]
                if block_of[e] == blk:
                    imm_row.append(i - lo)
                    imm_col.append(e)
                    imm_term.append(k)
                else:
                    if e not in bucket:
                        bucket[e] = List[Tuple[Int, Int]]()
                        scratch_cols.append(e)
                    bucket[e].append((i - lo, k))
        imm_start.append(len(imm_row))
        sort(scratch_cols)
        for e in scratch_cols:
            col_id.append(e)
            for it in bucket[e]:
                del_row.append(it[0])
                del_term.append(it[1])
            col_start.append(len(del_row))
        del_start.append(len(col_id))
    var tprep = perf_counter_ns() - t1
    # Per prime values for the immediate and delayed entries, in their orders.
    var imm_vals = List[List[UInt64]]()
    var del_vals = List[List[UInt64]]()
    var lead_rows = List[Int]()
    for i in range(len(pcols)):
        lead_rows.append(pivot[pcols[i]])
    for l in range(L):
        var iv = List[UInt64](capacity=len(imm_term))
        for t in imm_term:
            iv.append(UInt64(vals8[L * t + l]))
        imm_vals.append(iv^)
        var dv = List[UInt64](capacity=len(del_term))
        for t in del_term:
            dv.append(UInt64(vals8[L * t + l]))
        del_vals.append(dv^)
    var checksumB = UInt64(0)
    var done_entries = 0
    var rowB = List[UInt64](length=PL * ncols, fill=0)
    var f = List[VP](length=B, fill=VP(0))
    var t2 = perf_counter_ns()
    var chunk = 0
    while chunk < npairs:
        var count = min(PL, npairs - chunk)
        var lo_col = ncols
        for j in range(count):
            lo_col = min(lo_col, entries[starts[halves[chunk + j][0]]])
        for l in range(L):
            var p = plist[l]
            var pv = VP(p)
            var sq = VP(p * p)
            var rc = SIMD[DType.float64, PL](1.0 / Float64(p))
            var data = rowB.unsafe_ptr()
            for j in range(count):
                var a = halves[chunk + j][0]
                var b = halves[chunk + j][1]
                for k in range(starts[a + 1] - starts[a]):
                    var at = data.unsafe_offset(PL * entries[starts[a] + k] + j)
                    at.unsafe_store(at.unsafe_load() + UInt64(vals8[L * (starts[a] + k) + l]))
                for k in range(starts[b + 1] - starts[b]):
                    var at = data.unsafe_offset(PL * entries[starts[b] + k] + j)
                    at.unsafe_store(at.unsafe_load() + p - UInt64(vals8[L * (starts[b] + k) + l]))
                data.unsafe_offset(PL * entries[starts[a]] + j).unsafe_store(0)
            ref iv = imm_vals[l]
            ref dv = del_vals[l]
            var first_block = block_of[lo_col] if block_of[lo_col] >= 0 else 0
            for blk in range(first_block, nblocks):
                var lo = blk * B
                var hi = min(lo + B, len(pcols))
                var any = False
                var ip = imm_start[blk]
                for i in range(hi - lo):
                    var c = pcols[lo + i]
                    var at = data.unsafe_offset(PL * c)
                    var v = vmodp(at.unsafe_load[width=PL](), pv, rc)
                    at.unsafe_store[width=PL](VP(0))
                    checksumB += v.reduce_add()
                    var fi = v.eq(0).select(VP(0), pv - v)
                    f[i] = fi
                    if fi.ne(0).reduce_or():
                        any = True
                        # Immediate entries of row i, in later block pivot columns.
                        while ip < imm_start[blk + 1] and imm_row[ip] == i:
                            var at2 = data.unsafe_offset(PL * imm_col[ip])
                            var x = at2.unsafe_load[width=PL]() + fi * VP(iv[ip])
                            at2.unsafe_store[width=PL](x.ge(sq).select(x - sq, x))
                            ip += 1
                    while ip < imm_start[blk + 1] and imm_row[ip] == i:
                        ip += 1
                if not any:
                    continue
                done_entries += col_start[del_start[blk + 1]] - col_start[del_start[blk]]
                var fp = f.unsafe_ptr()
                var drp = del_row.unsafe_ptr()
                var dvp = dv.unsafe_ptr()
                for g in range(del_start[blk], del_start[blk + 1]):
                    var at3 = data.unsafe_offset(PL * col_id.unsafe_get(g))
                    var acc = at3.unsafe_load[width=PL]()
                    var e = col_start.unsafe_get(g)
                    var end = col_start.unsafe_get(g + 1)
                    # Below p^2 each; three products and the entry stay below 2^64.
                    while e + 3 <= end:
                        acc = acc.ge(sq).select(acc - sq, acc)
                        acc += fp[Int(drp.unsafe_offset(e).unsafe_load())] * VP(dvp.unsafe_offset(e).unsafe_load())
                        acc += fp[Int(drp.unsafe_offset(e + 1).unsafe_load())] * VP(dvp.unsafe_offset(e + 1).unsafe_load())
                        acc = acc.ge(sq).select(acc - sq, acc)
                        acc += fp[Int(drp.unsafe_offset(e + 2).unsafe_load())] * VP(dvp.unsafe_offset(e + 2).unsafe_load())
                        e += 3
                    while e < end:
                        acc = acc.ge(sq).select(acc - sq, acc)
                        acc += fp[Int(drp.unsafe_offset(e).unsafe_load())] * VP(dvp.unsafe_offset(e).unsafe_load())
                        e += 1
                    at3.unsafe_store[width=PL](acc.ge(sq).select(acc - sq, acc))
            # Clear what is left (non-pivot columns).
            for c in range(lo_col, ncols):
                data.unsafe_offset(PL * c).unsafe_store[width=PL](VP(0))
        chunk += PL
    var tB = perf_counter_ns() - t2
    print("B blocked: ms", tB // 1000000, "prep ms", tprep // 1000000, "ns per useful prime-term", Float64(tB) / Float64(useful * L), "speedup", Float64(tA) / Float64(tB))
    print("B entries x lanes", done_entries * PL, "vs useful", useful * L, "waste", Float64(done_entries * PL) / Float64(useful * L))
    print("checksums", checksumA, checksumB, "same" if checksumA == checksumB else "DIFFERENT")
