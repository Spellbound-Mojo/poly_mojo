"""Benchmark driver: cylindrical algebraic decomposition and sign conditions.

Build one binary per dimension with `mojo build -I build -D NVARS=n`.

Arguments: MODE INPUT RESULT ANSWER MASKS MIN_SECONDS MIN_REPS.
The input holds length-prefixed sparse QQ records, as for the Gröbner driver.
MASKS lists one allowed-sign mask per input (1 negative, 2 zero, 4 positive),
comma separated, or `-` for a full decomposition.

| Mode | Timed call | Check timed separately |
|---|---|---|
| lazard | `cad.decompose` | `cad.check` |
| mccallum | `cad.decompose(lazard=False)` | `cad.check` |
| stream | `cad.checker`, `cad.decompose_to`, `finish` (one region) | none |
| solve | `cad.solve` of the conjunction | `cad.check` |

The answer file lists, for a decomposition, one line per terminal cell with
its dimension, signs and exact sample coordinates; for `solve`, the verdict
and the exact sample point. A coordinate is `Q:<rational>` or
`A:<c0>,<c1>,...:<low>:<high>`, the root of sum c_i t^i in [low, high].
Writing the answer stays outside the timed region.
"""
from apn_mojo import Rational
from poly import algebraic, cad, sparse
from poly.algebraic import Real
from polynomials import Budget
from std.sys import argv, get_defined_int
from std.time import perf_counter_ns

comptime NVARS = get_defined_int["NVARS", 2]()


def status_kb(field: String) raises -> Int:
    var text = open("/proc/self/status", "r").read()
    var start = text.find(field + ":")
    var end = text.find("\n", start)
    var value = String(text[byte = start + field.byte_length() + 1 : end]).strip()
    return Int(String(value.removesuffix("kB").strip()))


def reset_peak() raises:
    with open("/proc/self/clear_refs", "w") as f:
        f.write("5")


def read_number(text: String, mut position: Int) raises -> Int:
    var end = text.find("\n", position)
    var value = Int(String(text[byte=position:end]))
    position = end + 1
    return value


def read_records(path: String) raises -> List[String]:
    var text = open(path, "r").read()
    var position = 0
    var count = read_number(text, position)
    var records = List[String](capacity=count)
    for _ in range(count):
        var length = read_number(text, position)
        records.append(String(text[byte = position : position + length]))
        position += length
    return records^


def coordinate(value: Real, mut out: String):
    ref w = value.witness()
    if w.rational:
        out.write("Q:", w.low.value)
        return
    out.write("A:")
    for i in range(len(w.polynomial.coefficients)):
        out.write("," if i else "", w.polynomial.coefficients[i].value)
    out.write(":", w.low.value, ":", w.high.value)


def point(sample: List[Real], mut out: String):
    for i in range(len(sample)):
        out.write(" " if i else "")
        coordinate(sample[i], out)


def json_times(times: List[Int]) -> String:
    var text = String("[")
    for i in range(len(times)):
        text.write(", " if i else "", times[i])
    text.write("]")
    return text^


def main() raises:
    var args = List[String]()
    for arg in argv():
        args.append(String(arg))
    if len(args) != 8:
        raise Error("usage: cad MODE INPUT RESULT ANSWER MASKS MIN_SECONDS MIN_REPS")
    var mode = args[1]
    var min_seconds = atof(args[6])
    var min_reps = Int(args[7])
    var records = read_records(args[2])
    var polys = List[type_of(sparse.loads[Rational, ndim=NVARS](records[0]))](capacity=len(records))
    for record in records:
        polys.append(sparse.loads[Rational, ndim=NVARS](record))
    var limit = min_seconds * 1e9
    var times = List[Int]()
    var total = 0
    var check_ns = 0
    var check_ok: Bool
    var answer = String()
    var extra = String()
    var rss_before = status_kb("VmRSS")
    reset_peak()
    var peak: Int

    if mode == "lazard" or mode == "mccallum":
        var lazard = mode == "lazard"
        var start = perf_counter_ns()
        var result = cad.decompose(polys, lazard=lazard)
        var elapsed = perf_counter_ns() - start
        peak = status_kb("VmHWM")
        times.append(elapsed)
        total += elapsed
        if Float64(elapsed) < limit:
            while len(times) < min_reps or Float64(total) < limit:
                start = perf_counter_ns()
                var again = cad.decompose(polys, lazard=lazard)
                var lap = perf_counter_ns() - start
                times.append(lap)
                total += lap
                if len(again.evidence().cells) != len(result.evidence().cells):
                    raise Error("repeated decomposition differs")
        start = perf_counter_ns()
        check_ok = cad.check(result)
        check_ns = perf_counter_ns() - start
        ref projection = result.evidence().projection
        var factors = String("[")
        for level in range(len(projection.levels)):
            factors.write(", " if level else "", len(projection.levels[level]))
        factors.write("]")
        var described = cad.cells(result)
        extra.write(', "cells": ', len(described), ', "projection_factors": ', factors,
                    ', "stacks": ', len(result.evidence().stacks))
        answer.write(len(described), "\n")
        for c in described:
            answer.write(c.dimension, " ")
            for i in range(len(c.signs)):
                answer.write("," if i else "", c.signs[i])
            answer.write(" ")
            point(c.sample, answer)
            answer.write("\n")
    elif mode == "stream":
        var start = perf_counter_ns()
        var checker = cad.checker(polys)
        var receipt = cad.decompose_to(polys, checker)
        var work = Budget()
        check_ok = checker.finish(receipt, work)
        var elapsed = perf_counter_ns() - start
        peak = status_kb("VmHWM")
        times.append(elapsed)
        extra.write(', "cells": ', receipt.cells, ', "stacks": ', receipt.stacks)
        answer.write(receipt.cells, "\n")
    elif mode == "solve":
        var masks = args[5].split(",")
        var constraints = List[cad.Constraint[type_of(polys[0])._Power]]()
        for i in range(len(polys)):
            var m = Int(masks[i])
            if m == 1:
                constraints.append(cad.negative(polys[i]))
            elif m == 2:
                constraints.append(cad.zero(polys[i]))
            elif m == 4:
                constraints.append(cad.positive(polys[i]))
            elif m == 3:
                constraints.append(cad.nonpositive(polys[i]))
            elif m == 6:
                constraints.append(cad.nonnegative(polys[i]))
            elif m == 5:
                constraints.append(cad.nonzero(polys[i]))
            else:
                raise Error("unsupported mask")
        var start = perf_counter_ns()
        var result = cad.solve(constraints)
        var elapsed = perf_counter_ns() - start
        peak = status_kb("VmHWM")
        times.append(elapsed)
        total += elapsed
        if Float64(elapsed) < limit:
            while len(times) < min_reps or Float64(total) < limit:
                start = perf_counter_ns()
                var again = cad.solve(constraints)
                var lap = perf_counter_ns() - start
                times.append(lap)
                total += lap
                if again.satisfiable() != result.satisfiable():
                    raise Error("repeated solve differs")
        start = perf_counter_ns()
        check_ok = cad.check(result)
        check_ns = perf_counter_ns() - start
        var sat = result.satisfiable()
        extra.write(', "sat": ', "true" if sat else "false")
        if sat:
            answer.write("sat\n")
            point(cad.sample(result).value(), answer)
            answer.write("\n")
        else:
            answer.write("unsat\n")
    else:
        raise Error("unknown mode " + mode)

    with open(args[4], "w") as f:
        f.write(answer)
    var result = String('{"times_ns": ', json_times(times), ', "rss_before_kb": ', rss_before, ', "peak_kb": ', peak)
    result.write(', "check_ns": ', check_ns, ', "check_ok": ', "true" if check_ok else "false", extra, "}\n")
    with open(args[3], "w") as f:
        f.write(result)
