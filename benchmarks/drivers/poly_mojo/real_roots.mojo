"""Benchmark driver: real root isolation, refinement, exact roots, and Sturm counts.

Arguments: input, answer, result, mode, min_seconds, min_reps.
The input holds a coefficient count, one ascending integer coefficient per
line, and an exponent k such that every real root lies in (-2^k, 2^k). Reading it, and writing the answer, stay outside the
timed region. Modes:

| mode | timed call | answer |
|---|---|---|
| isolate | `dense.real_root_cover` with `absolute_bits=1` | isolating intervals |
| refine53, refine1000 | `roots.refine` of the isolating cover to 2^-53 or 2^-1000 | refined intervals |
| exact | `dense.real_roots` | bounds of each exact root |
| sturm | `dense.sturm_sequence`, then `roots.count_roots` on (-2^k, 2^k) | the count |

The answer lists one root per line as `low high` rationals (the count first).
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


def run_once(values: List[Rational], mode: String, want: Bool) raises -> String:
    """Run one timed call and return its answer when `want` is set."""
    var answer = String()
    if mode == "isolate":
        var cover = isolate(values)
        if want:
            answer = cover_answer(roots.intervals(cover))
    elif mode == "refine53" or mode == "refine1000":
        raise Error("refinement is timed by run_refine")
    elif mode == "exact":
        var result = dense.real_roots(values)
        if want:
            answer = String(len(result), "\n")
            for r in result:
                var b = algebraic.bounds(r)
                answer.write(b[0], " ", b[1], "\n")
    elif mode == "sturm":
        raise Error("sturm is timed by run_sturm")
    else:
        raise Error("unknown mode " + mode)
    return answer^


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
    if mode == "refine53" or mode == "refine1000":
        var bits = 53 if mode == "refine53" else 1000
        var cover = isolate(values)
        rss_before = status_kb("VmRSS")
        reset_peak()
        while len(times) == 0 or len(times) < min_reps or Float64(total) < limit:
            var start = perf_counter_ns()
            var refined = roots.refine(cover, options(bits), complete_only=True)
            var lap = perf_counter_ns() - start
            if len(times) == 0:
                peak = status_kb("VmHWM")
                answer = cover_answer(roots.intervals(refined))
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
            var counted = roots.count_roots(plan, -bound, bound)
            var lap = perf_counter_ns() - start
            if len(times) == 0:
                peak = status_kb("VmHWM")
                answer = String(counted.count(), "\n")
            times.append(lap)
            total += lap
            if Float64(lap) >= limit:
                break
    else:
        reset_peak()
        while len(times) == 0 or len(times) < min_reps or Float64(total) < limit:
            var start = perf_counter_ns()
            var got = run_once(values, mode, len(times) == 0)
            var lap = perf_counter_ns() - start
            if len(times) == 0:
                peak = status_kb("VmHWM")
                answer = got^
            times.append(lap)
            total += lap
            if Float64(lap) >= limit:
                break
    with open(args[2], "w") as f:
        f.write(answer)
    var result = String('{"times_ns": [')
    for i in range(len(times)):
        result.write(", " if i else "", times[i])
    result.write('], "rss_before_kb": ', rss_before, ', "peak_kb": ', peak, "}\n")
    with open(args[3], "w") as f:
        f.write(result)
