"""Benchmark driver: time one sparse Gröbner basis and measure its memory.

Build one binary per variable count and field with
`mojo build -I build -D NVARS=n -D MODULAR=0|1`.

Arguments: input, answer, result, order, mode, modulus, min_seconds, min_reps.
The input holds a polynomial count and then, for each generator, a byte length
followed by its canonical `sparse.dumps` record. Reading it, and writing the
answer, stay outside the timed region. Mode `comparable` computes without
witnesses; mode `certified` keeps witnesses and also times `check_groebner`.
"""
from apn_mojo import Rational
from poly import sparse
from polynomials import ModInt
from std.sys import argv, get_defined_int
from std.time import perf_counter_ns

comptime NVARS = get_defined_int["NVARS", 2]()
comptime MODULAR = get_defined_int["MODULAR", 0]()


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


def run[T: Copyable & Deinitable](args: List[String]) raises:
    var modulus = UInt64(Int(args[6]))
    var min_seconds = atof(args[7])
    var min_reps = Int(args[8])
    var order = args[4]
    var certified = args[5] == "certified"
    var records = read_records(args[1])
    var generators = List[type_of(sparse.loads[T, ndim=NVARS](records[0], modulus=modulus))](capacity=len(records))
    for record in records:
        generators.append(sparse.loads[T, ndim=NVARS](record, modulus=modulus))

    var rss_before = status_kb("VmRSS")
    reset_peak()
    var start = perf_counter_ns()
    var basis = sparse.groebner(generators, order=order, witnesses=certified)
    var elapsed = perf_counter_ns() - start
    var peak = status_kb("VmHWM")
    var times: List[Int] = [elapsed]
    var total = elapsed
    # Repeat short calls with the same immutable inputs until the clock is reliable.
    var limit = min_seconds * 1e9
    if Float64(elapsed) < limit:
        while len(times) < min_reps or Float64(total) < limit:
            start = perf_counter_ns()
            var again = sparse.groebner(generators, order=order, witnesses=certified)
            var lap = perf_counter_ns() - start
            times.append(lap)
            total += lap
            if len(again) != len(basis):
                raise Error("repeated basis differs")

    var check_ns = 0
    var check_peak = 0
    var check_ok = True
    if certified:
        reset_peak()
        start = perf_counter_ns()
        check_ok = sparse.check_groebner(basis)
        check_ns = perf_counter_ns() - start
        check_peak = status_kb("VmHWM")

    var answer = String(len(basis), "\n")
    for p in basis:
        var record = sparse.dumps(p)
        answer.write(record.byte_length(), "\n", record)
    with open(args[2], "w") as f:
        f.write(answer)

    var result = String('{"times_ns": [')
    for i in range(len(times)):
        result.write(", " if i else "", times[i])
    result.write('], "rss_before_kb": ', rss_before, ', "peak_kb": ', peak)
    result.write(', "check_ns": ', check_ns, ', "check_peak_kb": ', check_peak)
    result.write(', "check_ok": ', "true" if check_ok else "false", ', "basis_length": ', len(basis), "}\n")
    with open(args[3], "w") as f:
        f.write(result)


def main() raises:
    var args = List[String]()
    for arg in argv():
        args.append(String(arg))
    if len(args) != 9:
        raise Error("usage: groebner INPUT ANSWER RESULT ORDER MODE MODULUS MIN_SECONDS MIN_REPS")
    comptime if MODULAR:
        run[ModInt](args)
    else:
        run[Rational](args)
