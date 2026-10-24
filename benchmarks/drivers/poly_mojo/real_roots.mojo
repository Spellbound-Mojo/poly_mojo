"""Benchmark driver: real root isolation, refinement, exact roots, and Sturm counts.

Arguments: input, answer, result, mode, min_seconds, min_reps.
The input holds a coefficient count, one ascending integer coefficient per
line, and an exponent k such that every real root lies in (-2^k, 2^k). Reading it, and writing the answer, stay outside the
timed region. Modes:

| mode | timed call | answer |
|---|---|---|
| isolate, isolateN | `dense.real_root_cover` (Descartes) with `absolute_bits=1` or `N` | isolating intervals |
| refine53, refine1000, refineN | `roots.refine` of the isolating cover to 2^-53, 2^-1000 or 2^-N | refined intervals |
| exact | `dense.real_roots` | bounds of each exact root |
| count | `dense.count_roots` (Descartes) on (-2^k, 2^k) | the count |
| sturm | `dense.sturm_sequence`, then `roots.count_roots` on (-2^k, 2^k) | the count |

The answer lists one root per line as `low high` rationals (the count first).
All producers retain evidence. The first result's independent `roots.check`
is measured separately as `check_ns`, outside computation and formatting.
"""
from apn_mojo import Rational
from polynomials import NumericOptions
from poly import dense, roots, algebraic
from std.sys import argv
from std.time import perf_counter_ns


def status_kb(field: String) raises -> Int:
    """Return a `/proc/self/status` field in KiB, such as VmRSS or VmHWM."""
    var text = open("/proc/self/status", "r").read()
    var start = text.find(field + ":")
    if start < 0:
        raise Error("missing /proc/self/status field " + field)
    var end = text.find("\n", start)
    var value = String(text[byte = start + field.byte_length() + 1 : end]).strip()
    return Int(String(value.removesuffix("kB").strip()))


def reset_peak() raises:
    """Reset VmHWM to the current resident size (Linux 4.0 and later)."""
    with open("/proc/self/clear_refs", "w") as f:
        f.write("5")


def read_coefficients(path: String, mut bound: Int) raises -> List[Rational]:
    var lines = open(path, "r").read().splitlines()
    var count = Int(lines[0])
    var values = List[Rational](capacity=count)
    for i in range(count):
        values.append(Rational(String(String(lines[i + 1]).strip())))
    bound = Int(String(lines[count + 1]).strip())
    return values^


def options(bits: Int) -> NumericOptions:
    # Bisection-based covers need a subdivision allowance proportional to roots * bits.
    return NumericOptions(absolute_bits=bits, max_subdivisions=1 << 40)


def isolate(values: List[Rational]) raises -> type_of(dense.real_root_cover(values, options=options(1))):
    return dense.real_root_cover(values, options=options(1), complete_only=True)


def cover_answer(cells: List[Tuple[Rational, Rational, Int]]) raises -> String:
    var count = 0
    for c in cells:
        if c[2] != 1:
            raise Error("cover cell does not isolate one root")
        count += 1
    var answer = String(count, "\n")
    for c in cells:
        answer.write(c[0], " ", c[1], "\n")
    return answer^


def main() raises:
    var args = List[String]()
    for arg in argv():
        args.append(String(arg))
    if len(args) != 7:
        raise Error("usage: real_roots INPUT ANSWER RESULT MODE MIN_SECONDS MIN_REPS")
    var bound_exponent = 0
    var values = read_coefficients(args[1], bound_exponent)
    var mode = args[4]
    var min_seconds = atof(args[5])
    var min_reps = Int(args[6])
    var times = List[Int]()
    var total = 0
    var answer = String("?")
    var rss_before = status_kb("VmRSS")
    var peak = 0
    var limit = min_seconds * 1e9
    var check_ns = 0
    var check_ok = True
    if mode.startswith("refine"):
        var bits = Int(String(mode[byte=6:]))
        var cover = isolate(values)
        rss_before = status_kb("VmRSS")
        reset_peak()
        while len(times) == 0 or len(times) < min_reps or Float64(total) < limit:
            var start = perf_counter_ns()
            var result = roots.refine(cover, options(bits), complete_only=True)
            var lap = perf_counter_ns() - start
            if len(times) == 0:
                peak = status_kb("VmHWM")
                start = perf_counter_ns()
                check_ok = roots.check(result)
                check_ns = perf_counter_ns() - start
                answer = cover_answer(roots.intervals(result))
            times.append(lap)
            total += lap
            if Float64(lap) >= limit:
                break
    elif mode == "count":
        var bound = Rational(1)
        for _ in range(bound_exponent):
            bound = bound * Rational(2)
        reset_peak()
        while len(times) == 0 or len(times) < min_reps or Float64(total) < limit:
            var start = perf_counter_ns()
            var result = dense.count_roots(values, -bound, bound)
            var lap = perf_counter_ns() - start
            if len(times) == 0:
                peak = status_kb("VmHWM")
                start = perf_counter_ns()
                check_ok = roots.check(result)
                check_ns = perf_counter_ns() - start
                answer = String(result.count(), "\n")
            times.append(lap)
            total += lap
            if Float64(lap) >= limit:
                break
    elif mode == "sturm":
        var bound = Rational(1)
        for _ in range(bound_exponent):
            bound = bound * Rational(2)
        reset_peak()
        while len(times) == 0 or len(times) < min_reps or Float64(total) < limit:
            var start = perf_counter_ns()
            var plan = dense.sturm_sequence(values)
            var result = roots.count_roots(plan, -bound, bound)
            var lap = perf_counter_ns() - start
            if len(times) == 0:
                peak = status_kb("VmHWM")
                start = perf_counter_ns()
                check_ok = roots.check(result)
                check_ns = perf_counter_ns() - start
                answer = String(result.count(), "\n")
            times.append(lap)
            total += lap
            if Float64(lap) >= limit:
                break
    elif mode == "exact":
        reset_peak()
        while len(times) == 0 or len(times) < min_reps or Float64(total) < limit:
            var start = perf_counter_ns()
            var result = dense.real_roots(values)
            var lap = perf_counter_ns() - start
            if len(times) == 0:
                peak = status_kb("VmHWM")
                start = perf_counter_ns()
                check_ok = roots.check(result)
                check_ns = perf_counter_ns() - start
                answer = String(len(result), "\n")
                for r in result:
                    var bounds = algebraic.bounds(r)
                    answer.write(bounds[0], " ", bounds[1], "\n")
            times.append(lap)
            total += lap
            if Float64(lap) >= limit:
                break
    elif mode.startswith("isolate"):
        var bits = 1 if mode == "isolate" else Int(String(mode[byte=7:]))
        reset_peak()
        while len(times) == 0 or len(times) < min_reps or Float64(total) < limit:
            var start = perf_counter_ns()
            var result = dense.real_root_cover(values, options=options(bits), complete_only=True)
            var lap = perf_counter_ns() - start
            if len(times) == 0:
                peak = status_kb("VmHWM")
                start = perf_counter_ns()
                check_ok = roots.check(result)
                check_ns = perf_counter_ns() - start
                answer = cover_answer(roots.intervals(result))
            times.append(lap)
            total += lap
            if Float64(lap) >= limit:
                break
    else:
        raise Error("unknown mode " + mode)
    with open(args[2], "w") as f:
        f.write(answer)
    var result = String('{"times_ns": [')
    for i in range(len(times)):
        result.write(", " if i else "", times[i])
    result.write('], "rss_before_kb": ', rss_before, ', "peak_kb": ', peak, ', "check_ns": ', check_ns, ', "check_ok": ', "true" if check_ok else "false", "}\n")
    with open(args[3], "w") as f:
        f.write(result)
