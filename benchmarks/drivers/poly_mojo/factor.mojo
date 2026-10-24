"""Benchmark driver: time one exact factorization and measure its memory.

Build once with `mojo build -I build`; sparse inputs dispatch on their
variable count (2, 3, 4, 5, 6 or 8) to a compiled power shape.

Arguments: kind, input, answer, result, modulus, mode, min_seconds, min_reps, nvars.
Kind `dense` reads one coefficient per line (degree 0 first) after a count
line and calls `dense.factor` over ZZ, or over GF(modulus) when the modulus is
nonzero. Kind `sparse` reads one canonical `sparse.dumps` record over ZZ and
calls `sparse.factor`. Reading the input and writing the answer stay outside
the timed region. Mode `certified` times `factor_checked` instead of `factor`;
`exact.check` of that same result is timed separately, without refactorization. The answer holds the scalar and, per factor, its
multiplicity and its canonical `dumps` record.
"""
from apn_mojo import Integer
from poly import dense, exact, sparse
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


def read_coefficients(path: String) raises -> List[Integer]:
    var lines = open(path, "r").read().split("\n")
    var count = Int(String(lines[0]))
    var values = List[Integer](capacity=count)
    for i in range(count):
        values.append(Integer(String(lines[i + 1])))
    return values^


struct Timing(Copyable, Movable):
    var times: List[Int]
    var rss_before: Int
    var peak: Int
    var check_ns: Int
    var check_ok: Bool

    def __init__(out self):
        self.times = List[Int]()
        self.rss_before = 0
        self.peak = 0
        self.check_ns = 0
        self.check_ok = True

    def done(self, min_seconds: Float64, min_reps: Int) -> Bool:
        var total = 0
        for t in self.times:
            total += t
        # A long first call is enough; short calls repeat until both limits are met.
        if Float64(self.times[0]) >= min_seconds * 1e9:
            return True
        return len(self.times) >= min_reps and Float64(total) >= min_seconds * 1e9


def write_result(path: String, timing: Timing, count: Int) raises:
    var result = String('{"times_ns": [')
    for i in range(len(timing.times)):
        result.write(", " if i else "", timing.times[i])
    result.write('], "rss_before_kb": ', timing.rss_before, ', "peak_kb": ', timing.peak)
    result.write(', "check_ns": ', timing.check_ns, ', "check_ok": ', "true" if timing.check_ok else "false")
    result.write(', "factor_count": ', count, "}\n")
    with open(path, "w") as f:
        f.write(result)


def run_dense(args: List[String]) raises:
    var modulus = UInt64(Int(args[5]))
    var certified = args[6] == "certified"
    var min_seconds = atof(args[7])
    var min_reps = Int(args[8])
    var values = read_coefficients(args[2])
    var timing = Timing()
    var answer = String()
    var count = 0
    timing.rss_before = status_kb("VmRSS")
    if modulus:
        var p = dense.asarray(values, modulus=modulus)
        reset_peak()
        while True:
            var start = perf_counter_ns()
            var result: type_of(dense.factor(p))
            if certified:
                var checked = dense.factor_checked(p)
                timing.times.append(Int(perf_counter_ns() - start))
                if len(timing.times) == 1:
                    timing.peak = status_kb("VmHWM")
                    start = perf_counter_ns()
                    timing.check_ok = exact.check(checked)
                    timing.check_ns = Int(perf_counter_ns() - start)
                result = (exact.unit(checked), exact.factors(checked))
            else:
                result = dense.factor(p)
                timing.times.append(Int(perf_counter_ns() - start))
                if len(timing.times) == 1:
                    timing.peak = status_kb("VmHWM")
            if len(timing.times) == 1:
                count = len(result[1])
                answer = String(result[0].value, "\n", len(result[1]), "\n")
                for entry in result[1]:
                    var record = dense.dumps(entry[0])
                    answer.write(entry[1], "\n", record.byte_length(), "\n", record)
            if timing.done(min_seconds, min_reps):
                break
    else:
        var p = dense.asarray(values)
        reset_peak()
        while True:
            var start = perf_counter_ns()
            var result: type_of(dense.factor(p))
            if certified:
                var checked = dense.factor_checked(p)
                timing.times.append(Int(perf_counter_ns() - start))
                if len(timing.times) == 1:
                    timing.peak = status_kb("VmHWM")
                    start = perf_counter_ns()
                    timing.check_ok = exact.check(checked)
                    timing.check_ns = Int(perf_counter_ns() - start)
                result = (exact.unit(checked), exact.factors(checked))
            else:
                result = dense.factor(p)
                timing.times.append(Int(perf_counter_ns() - start))
                if len(timing.times) == 1:
                    timing.peak = status_kb("VmHWM")
            if len(timing.times) == 1:
                count = len(result[1])
                answer = String(result[0], "\n", len(result[1]), "\n")
                for entry in result[1]:
                    var record = dense.dumps(entry[0])
                    answer.write(entry[1], "\n", record.byte_length(), "\n", record)
            if timing.done(min_seconds, min_reps):
                break
    with open(args[3], "w") as f:
        f.write(answer)
    write_result(args[4], timing, count)


def run_sparse[n: Int](args: List[String]) raises:
    var certified = args[6] == "certified"
    var min_seconds = atof(args[7])
    var min_reps = Int(args[8])
    var p = sparse.loads[Integer, ndim=n](open(args[2], "r").read())
    var timing = Timing()
    var answer = String()
    var count = 0
    timing.rss_before = status_kb("VmRSS")
    reset_peak()
    while True:
        var start = perf_counter_ns()
        var result: type_of(sparse.factor(p))
        if certified:
            var checked = sparse.factor_checked(p)
            timing.times.append(Int(perf_counter_ns() - start))
            if len(timing.times) == 1:
                timing.peak = status_kb("VmHWM")
                start = perf_counter_ns()
                timing.check_ok = exact.check(checked)
                timing.check_ns = Int(perf_counter_ns() - start)
            result = (exact.unit(checked), exact.factors(checked))
        else:
            result = sparse.factor(p)
            timing.times.append(Int(perf_counter_ns() - start))
            if len(timing.times) == 1:
                timing.peak = status_kb("VmHWM")
        if len(timing.times) == 1:
            count = len(result[1])
            answer = String(result[0], "\n", len(result[1]), "\n")
            for entry in result[1]:
                var record = sparse.dumps(entry[0])
                answer.write(entry[1], "\n", record.byte_length(), "\n", record)
        if timing.done(min_seconds, min_reps):
            break
    with open(args[3], "w") as f:
        f.write(answer)
    write_result(args[4], timing, count)


def main() raises:
    var args = List[String]()
    for arg in argv():
        args.append(String(arg))
    if len(args) != 10:
        raise Error("usage: factor KIND INPUT ANSWER RESULT MODULUS MODE MIN_SECONDS MIN_REPS NVARS")
    if args[1] == "dense":
        run_dense(args)
        return
    var nvars = Int(args[9])
    if nvars == 2:
        run_sparse[2](args)
    elif nvars == 3:
        run_sparse[3](args)
    elif nvars == 4:
        run_sparse[4](args)
    elif nvars == 5:
        run_sparse[5](args)
    elif nvars == 6:
        run_sparse[6](args)
    elif nvars == 8:
        run_sparse[8](args)
    else:
        raise Error("unsupported variable count")
