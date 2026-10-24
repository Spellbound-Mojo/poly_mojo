"""Benchmark driver: time one gcd, resultant, or discriminant and measure its memory.

Build one binary per variable count and coefficient domain with
`mojo build -I build -D NVARS=n -D DOMAIN=0|1` (0: ZZ, 1: GF(p)).

Arguments: input, answer, result, operation, method, axis, modulus,
min_seconds, min_reps. The input holds a polynomial count and then, for each
polynomial, a byte length followed by its canonical `sparse.dumps` record.
Append `-certified` to METHOD to time the checked producer instead; `check_ns`
then measures only `exact.check` of its first retained result.

Operations, all through the public `poly.sparse` API:
- `gcd`: `sparse.gcd(f, h, method=method)` of the first two records.
- `resultant`: `sparse.resultant(f, h, axis=axis)`.
- `discriminant`: `sparse.resultant(f, sparse.derivative(f, axis=axis))`
  divided exactly by the third record, the constant (-1)^(n(n-1)/2) lc(f);
  the library has no separate discriminant call.
Reading the input and writing the answer stay outside the timed region.
"""
from apn_mojo import Integer
from poly import sparse, exact
from polynomials import ModInt
from poly._interop import _Shape
from std.sys import argv, get_defined_int
from std.time import perf_counter_ns

comptime NVARS = get_defined_int["NVARS", 1]()
comptime DOMAIN = get_defined_int["DOMAIN", 0]()


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


comptime K = 3 if DOMAIN == 1 else 0
comptime Poly = sparse.Array[_Shape[NVARS], K]


def compute(polys: List[Poly], operation: String, method: String, axis: Int) raises -> Poly:
    if operation == "gcd":
        return rebind_var[Poly](sparse.gcd(polys[0], polys[1], method=method))
    if operation == "resultant":
        return rebind_var[Poly](sparse.resultant(polys[0], polys[1], axis=axis))
    if operation == "discriminant":
        var r = sparse.resultant(polys[0], sparse.derivative(polys[0], axis=axis), axis=axis)
        var d = sparse.divide_exact(r, polys[2])
        if not d:
            raise Error("the resultant is not divisible by the leading coefficient")
        return rebind_var[Poly](d.take())
    raise Error("unknown operation " + operation)


def checked_call(polys: List[Poly], operation: String, method: String, axis: Int, check: Bool) raises -> Tuple[Poly, Int, Int, Int, Bool]:
    """Time production and checking separately; output conversion is untimed."""
    var start = perf_counter_ns()
    if operation == "gcd":
        var proof = sparse.gcd_checked(polys[0], polys[1], method=method)
        var elapsed = perf_counter_ns() - start
        var peak = status_kb("VmHWM")
        start = perf_counter_ns()
        var ok = exact.check(proof) if check else True
        var check_ns = perf_counter_ns() - start if check else 0
        return (rebind_var[Poly](exact.value(proof)), elapsed, peak, check_ns, ok)
    var proof = sparse.resultant_checked(polys[0], rebind_var[Poly](sparse.derivative(polys[0], axis=axis)), axis=axis) if operation == "discriminant" else sparse.resultant_checked(polys[0], polys[1], axis=axis)
    var elapsed = perf_counter_ns() - start
    var value = rebind_var[Poly](exact.value(proof))
    if operation == "discriminant":
        start = perf_counter_ns()
        var divided = sparse.divide_exact(value, polys[2])
        elapsed += perf_counter_ns() - start
        if not divided:
            raise Error("the resultant is not divisible by the leading coefficient")
        value = rebind_var[Poly](divided.take())
    var peak = status_kb("VmHWM")
    start = perf_counter_ns()
    var ok = exact.check(proof) if check else True
    var check_ns = perf_counter_ns() - start if check else 0
    return (value^, elapsed, peak, check_ns, ok)


def run[T: Copyable & Deinitable](args: List[String]) raises:
    var operation = args[4]
    var method = args[5]
    var certified = method.endswith("-certified")
    if certified:
        var plain_method = String(method.removesuffix("-certified"))
        method = plain_method^
    var axis = Int(args[6])
    var modulus = UInt64(Int(args[7]))
    var min_seconds = atof(args[8])
    var min_reps = Int(args[9])
    var records = read_records(args[1])
    var polys = List[Poly](capacity=len(records))
    for record in records:
        polys.append(rebind_var[Poly](sparse.loads[T, ndim=NVARS](record, modulus=modulus)))

    var rss_before = status_kb("VmRSS")
    reset_peak()
    var start = perf_counter_ns()
    var answer_poly: Poly
    var elapsed: Int
    var peak: Int
    var check_ns = 0
    var check_ok = True
    if certified:
        var measured = checked_call(polys, operation, method, axis, True)
        answer_poly = measured[0].copy()
        elapsed = measured[1]
        peak = measured[2]
        check_ns = measured[3]
        check_ok = measured[4]
    else:
        answer_poly = compute(polys, operation, method, axis)
        elapsed = perf_counter_ns() - start
        peak = status_kb("VmHWM")
    var times: List[Int] = [elapsed]
    var total = elapsed
    var record = sparse.dumps(answer_poly)
    # Repeat short calls with the same immutable inputs until the clock is reliable.
    var limit = min_seconds * 1e9
    if Float64(elapsed) < limit:
        while len(times) < min_reps or Float64(total) < limit:
            start = perf_counter_ns()
            var again: Poly
            var lap: Int
            if certified:
                var measured = checked_call(polys, operation, method, axis, False)
                again = measured[0].copy()
                lap = measured[1]
            else:
                again = compute(polys, operation, method, axis)
                lap = perf_counter_ns() - start
            times.append(lap)
            total += lap
            if sparse.dumps(again) != record:
                raise Error("repeated answer differs")

    with open(args[2], "w") as f:
        f.write(String("1\n", record.byte_length(), "\n", record))

    var result = String('{"times_ns": [')
    for i in range(len(times)):
        result.write(", " if i else "", times[i])
    result.write('], "rss_before_kb": ', rss_before, ', "peak_kb": ', peak,
                 ', "check_ns": ', check_ns, ', "check_ok": ', "true" if check_ok else "false", "}\n")
    with open(args[3], "w") as f:
        f.write(result)


def main() raises:
    var args = List[String]()
    for arg in argv():
        args.append(String(arg))
    if len(args) != 10:
        raise Error("usage: gcd INPUT ANSWER RESULT OPERATION METHOD AXIS MODULUS MIN_SECONDS MIN_REPS")
    comptime if DOMAIN == 1:
        run[ModInt](args)
    else:
        run[Integer](args)
