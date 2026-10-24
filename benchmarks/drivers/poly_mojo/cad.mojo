"""Benchmark driver: cylindrical algebraic decomposition and sign conditions.

Build one binary per dimension with `mojo build -I build -D NVARS=n`.

Arguments: MODE INPUT RESULT ANSWER MASKS MIN_SECONDS MIN_REPS.
Negative MIN_SECONDS requests exactly MIN_REPS calls for decomposition/solve.
The input holds length-prefixed sparse QQ records, as for the Gröbner driver.
MASKS lists one allowed-sign mask per input (1 negative, 2 zero, 4 positive),
comma separated, or `-` for a full decomposition.

| Mode | Timed call | Check timed separately |
|---|---|---|
| construct | compact backend construction, retaining final data | complete final acceptance (not an extra recheck) |
| final | `cad.decompose` (includes mandatory acceptance) | extra `cad.check`; `cells_ns` times `cad.cells` |
| lazard | `cad.decompose(lazard=True)` (includes acceptance) | extra `cad.check` |
| mccallum | `cad.decompose(lazard=False)` | `cad.check` |
| stream | `cad.checker`, `cad.decompose_to`, `finish` (one region) | none |
| solve | `cad.solve` of the conjunction | `cad.check` |
| certificate | `cad.decompose` | extra `cad.check`; the answer is a checked archive |
| certificate-solve | `cad.solve` | `cad.check`; the answer is a checked archive |
| consumers | default accepted decomposition | extra check, materialization, descriptions, iteration and archive read/write separately |

The answer file lists, for a decomposition, one line per terminal cell with
its dimension, signs and exact sample coordinates; for `solve`, the verdict
and the exact sample point. A coordinate is `Q:<rational>` or
`A:<c0>,<c1>,...:<low>:<high>`, the root of sum c_i t^i in [low, high].
Writing the answer stays outside the timed region. For public decomposition modes,
check_ns is an extra recheck and must not be added to times_ns as a mandatory
certification cost; the public call already includes that verification.
The construct instrumentation instead records construction and acceptance in
separate timers, while following the same retry policy.
"""
from apn_mojo import Rational
from poly import algebraic, cad, sparse, io
from poly.algebraic import Real
from polynomials import Budget
from polynomials import SparsePoly, QQ, PolyErrorKind, CADFinalCertificate
from polynomials.cad_final import _CADFinalData
from polynomials._cad_tree_final import _FinalCAD, _construct_final_cad, _check_final_cad
from poly._interop import _Shape
from std.memory import ArcPointer
from std.sys import argv, get_defined_int
from std.time import perf_counter_ns

comptime NVARS = get_defined_int["NVARS", 2]()


def construction(polys: List[sparse.Array[_Shape[NVARS], 1]], mut build_ns: Int, mut verify_ns: Int) raises -> cad.Decomposition[_Shape[NVARS]]:
    """Benchmark the compact backend's construction and acceptance separately.

    Final data still serve as evidence. This is not a proof-free public API.
    Retry order matches the public default: interval, exact, plain Lazard.
    """
    var start = perf_counter_ns()
    var budget = Budget()
    var inputs = List[SparsePoly[QQ]]()
    for p in polys:
        inputs.append(p._core[].reorder(p._core[].order, budget))
    var variables = List[Int64]()
    for i in range(NVARS):
        variables.append(Int64(i))
    build_ns += perf_counter_ns() - start
    for attempt in range(3):
        var candidate = Optional[_FinalCAD]()
        start = perf_counter_ns()
        try:
            candidate = _construct_final_cad(inputs, variables, List[Int](), budget, brown=attempt != 2, interval=attempt == 0)
        except e:
            if e.kind != PolyErrorKind.DOMAIN:
                raise e^
        build_ns += perf_counter_ns() - start
        if not candidate:
            continue
        var tree = candidate.take()
        tree.retries = attempt
        start = perf_counter_ns()
        var valid = _check_final_cad(inputs, variables, List[Int](), tree, budget)
        verify_ns += perf_counter_ns() - start
        if valid:
            start = perf_counter_ns()
            var proof = CADFinalCertificate(ArcPointer(_CADFinalData(tree^, None, None, False)))
            var result = cad.Decomposition[_Shape[NVARS]](ArcPointer(cad._DecompositionData(inputs^, proof^, None, List[Tuple[Int, Real]]())))
            build_ns += perf_counter_ns() - start
            return result^
    raise Error("construction rejected by final verification")


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
    var metadata_budget = Budget()
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

    if mode == "certificate":
        var start = perf_counter_ns()
        var result = cad.decompose(polys)
        times.append(perf_counter_ns() - start)
        peak = status_kb("VmHWM")
        check_ok = cad.check(result)
        answer.write(io.dumps(result))
    elif mode == "construct" or mode == "final" or mode == "lazard" or mode == "mccallum" or mode == "consumers":
        var lazard = Optional[Bool]() if mode == "final" or mode == "consumers" else Optional(mode == "lazard")
        var start = perf_counter_ns()
        var elapsed = 0
        var result = construction(polys, elapsed, check_ns) if mode == "construct" else cad.decompose(polys, lazard=lazard)
        if mode != "construct":
            elapsed = perf_counter_ns() - start
        peak = status_kb("VmHWM")
        times.append(elapsed)
        total += elapsed
        if min_seconds < 0 or Float64(elapsed) < limit:
            while len(times) < min_reps or Float64(total) < limit:
                start = perf_counter_ns()
                var lap = 0
                var extra_verify = 0
                var again = construction(polys, lap, extra_verify) if mode == "construct" else cad.decompose(polys, lazard=lazard)
                if mode != "construct":
                    lap = perf_counter_ns() - start
                times.append(lap)
                total += lap
                if again.evidence().cell_count(metadata_budget) != result.evidence().cell_count(metadata_budget):
                    raise Error("repeated decomposition differs")
        check_ok = True
        if mode != "construct":
            start = perf_counter_ns()
            check_ok = cad.check(result)
            check_ns = perf_counter_ns() - start
        var counts = result.evidence().factor_counts(metadata_budget)
        var factors = String("[")
        for level in range(len(counts)):
            factors.write(", " if level else "", counts[level])
        factors.write("]")
        if mode == "consumers":
            start = perf_counter_ns()
            var geometry = result.evidence().cells(metadata_budget)
            var materialize_ns = perf_counter_ns() - start
            extra.write(', "absolute_materialize_ns": ', materialize_ns, ', "all_cells": ', len(geometry))
        start = perf_counter_ns()
        var described = cad.cells(result)
        var cells_ns = perf_counter_ns() - start
        extra.write(', "cells_ns": ', cells_ns, ', "cells": ', len(described), ', "projection_factors": ', factors,
                    ', "stacks": ', result.evidence().stack_count())
        if mode == "consumers":
            start = perf_counter_ns()
            var checksum = 0
            for c in described:
                checksum += c.dimension
                for sign in c.signs:
                    checksum += sign
            extra.write(', "iteration_ns": ', perf_counter_ns() - start, ', "iteration_checksum": ', checksum)
            start = perf_counter_ns()
            var archive = io.dumps(result)
            extra.write(', "archive_write_ns": ', perf_counter_ns() - start, ', "archive_bytes": ', archive.byte_length())
            start = perf_counter_ns()
            var restored = io.loads[type_of(result)](archive)
            extra.write(', "archive_read_ns": ', perf_counter_ns() - start)
            if restored.evidence().cell_count(metadata_budget) != result.evidence().cell_count(metadata_budget):
                raise Error("archive round trip changed cell count")
        start = perf_counter_ns()
        answer.write(len(described), "\n")
        for c in described:
            answer.write(c.dimension, " ")
            for i in range(len(c.signs)):
                answer.write("," if i else "", c.signs[i])
            answer.write(" ")
            point(c.sample, answer)
            answer.write("\n")
        extra.write(', "format_answer_ns": ', perf_counter_ns() - start)
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
    elif mode == "solve" or mode == "certificate-solve":
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
        if min_seconds < 0 or Float64(elapsed) < limit:
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
        if mode == "certificate-solve":
            answer.write(io.dumps(result))
        elif sat:
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
