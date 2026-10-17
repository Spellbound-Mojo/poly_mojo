"""Benchmark driver: time one truncated series operation, multipoint evaluation, interpolation, or evaluation at a rational.

Build one binary per coefficient domain with `mojo build -I build -D MODULAR=0|1`.

Arguments: input, answer, result, min_seconds, min_reps. The input format is
described in harness/series.py. Operands are converted to Poly Mojo arrays
before the timer starts. The answer lists the result's values, one
hexadecimal integer or `numerator/denominator` per line.

| Operation | Timed call |
|---|---|
| series mul | `series.multiply(a, b)` |
| series inv | `series.reciprocal(a)` |
| series log, exp, revert | `series.log(a)`, `series.exp(a)`, `series.revert(a)` |
| series compose | `series.compose(a, b)` |
| multipoint | `dense.evaluate_many(f, points)` |
| interp | `dense.interpolate(points, values)` |
| evalq | `dense.evaluate(f, Rational(a, b))` |
"""
from apn_mojo import Integer, Rational
from poly import dense, series
from polynomials import Budget, ModInt, Modulus
from std.sys import argv, get_defined_int
from std.time import perf_counter_ns

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


struct Input(Movable):
    var kind: String
    var op: String
    var modulus: UInt64
    var n: Int
    var exponent: Int
    var lines: List[String]
    """Each operand's lines."""
    var operands: List[List[String]]

    def __init__(out self, path: String) raises:
        var text = open(path, "r").read()
        self.lines = List[String]()
        for line in text.split("\n"):
            self.lines.append(String(line))
        var head = self.lines[1].split(" ")
        self.kind = String(head[0])
        self.op = String(head[1])
        self.modulus = UInt64(Int(String(head[2])))
        self.n = Int(String(head[3]))
        self.exponent = Int(String(head[4]))
        self.operands = List[List[String]]()
        var position = 2
        while position < len(self.lines) and self.lines[position].byte_length():
            var count = Int(self.lines[position])
            position += 1
            var rows = List[String](capacity=count)
            for i in range(count):
                rows.append(self.lines[position + i])
            position += count
            self.operands.append(rows^)


def hex_text(value: Integer) -> String:
    var bytes = value.to_bytes(big_endian=True)
    if not len(bytes):
        return "0"
    comptime digits = "0123456789abcdef"
    var out = String("-" if value.sign() < 0 else "")
    var first = True
    for b in bytes:
        var high = Int(b >> 4)
        if not (first and high == 0):
            out.write(digits[byte=high])
        out.write(digits[byte = Int(b & 15)])
        first = False
    return out^


struct Timer:
    var times: List[Int]
    var total: Int
    var start: Int
    var rss_before: Int
    var peak: Int

    def __init__(out self) raises:
        self.times = List[Int]()
        self.total = 0
        self.rss_before = status_kb("VmRSS")
        reset_peak()
        self.start = perf_counter_ns()
        self.peak = 0

    def lap(mut self) raises:
        var elapsed = perf_counter_ns() - self.start
        if not len(self.times):
            self.peak = status_kb("VmHWM")
        self.times.append(elapsed)
        self.total += elapsed

    def more(mut self, min_seconds: Float64, min_reps: Int) -> Bool:
        var limit = min_seconds * 1e9
        if Float64(self.times[0]) >= limit:
            return False
        if len(self.times) >= min_reps and Float64(self.total) >= limit:
            return False
        self.start = perf_counter_ns()
        return True

    def write(self, path: String) raises:
        var result = String('{"times_ns": [')
        for i in range(len(self.times)):
            result.write(", " if i else "", self.times[i])
        result.write('], "rss_before_kb": ', self.rss_before, ', "peak_kb": ', self.peak, "}\n")
        with open(path, "w") as f:
            f.write(result)


def integers(rows: List[String]) raises -> List[Integer]:
    var values = List[Integer](capacity=len(rows))
    for row in rows:
        values.append(Integer(row, 16))
    return values^


def residues(rows: List[String], p: UInt64) raises -> List[ModInt]:
    var values = List[ModInt](capacity=len(rows))
    var budget = Budget(UInt64.MAX)
    var ctx = Modulus(p, budget)
    for row in rows:
        var v = Integer(row, 16) % Integer(Int(p))
        values.append(ModInt(UInt64(Int(v)), ctx))
    return values^


def rational_text(v: Rational) -> String:
    var den = v.denominator()
    if den == Integer(1):
        return hex_text(v.numerator())
    return hex_text(v.numerator()) + "/" + hex_text(den)


def write_values(values: List[String], path: String) raises:
    var out = String(len(values), "\n")
    for v in values:
        out.write(v, "\n")
    with open(path, "w") as f:
        f.write(out)


# Kind 1 is QQ and kind 3 is GF(p) (poly._common).
def series_op(op: String, a: series.Array[1], b: series.Array[1]) raises -> series.Array[1]:
    if op == "mul":
        return series.multiply(a, b)
    if op == "inv":
        return series.reciprocal(a)
    if op == "log":
        return series.log(a)
    if op == "exp":
        return series.exp(a)
    if op == "compose":
        return series.compose(a, b)
    if op == "revert":
        return series.revert(a)
    raise Error("unsupported series operation " + op)


def series_op(op: String, a: series.Array[3], b: series.Array[3]) raises -> series.Array[3]:
    if op == "mul":
        return series.multiply(a, b)
    if op == "inv":
        return series.reciprocal(a)
    if op == "log":
        return series.log(a)
    if op == "exp":
        return series.exp(a)
    if op == "compose":
        return series.compose(a, b)
    if op == "revert":
        return series.revert(a)
    raise Error("unsupported series operation " + op)


def run_series_qq(input: Input, args: List[String]) raises:
    var a = series.asarray(integers(input.operands[0]), order=input.n)
    var b = series.asarray(integers(input.operands[1 if len(input.operands) > 1 else 0]), order=input.n)
    var timer = Timer()
    var r = series_op(input.op, a, b)
    timer.lap()
    while timer.more(atof(args[4]), Int(args[5])):
        _ = series_op(input.op, a, b)
        timer.lap()
    timer.write(args[3])
    var out = List[String](capacity=len(r))
    for i in range(len(r)):
        out.append(rational_text(r[i]))
    write_values(out, args[2])


def run_series_gf(input: Input, args: List[String]) raises:
    var p = input.modulus
    var a = series.asarray(residues(input.operands[0], p), order=input.n)
    var b = series.asarray(residues(input.operands[1 if len(input.operands) > 1 else 0], p), order=input.n)
    var timer = Timer()
    var r = series_op(input.op, a, b)
    timer.lap()
    while timer.more(atof(args[4]), Int(args[5])):
        _ = series_op(input.op, a, b)
        timer.lap()
    timer.write(args[3])
    var out = List[String](capacity=len(r))
    for i in range(len(r)):
        out.append(hex_text(Integer(r[i].value)))
    write_values(out, args[2])


def run_qq(input: Input, args: List[String]) raises:
    var min_seconds = atof(args[4])
    var min_reps = Int(args[5])
    var out = List[String]()
    if input.kind == "series":
        return run_series_qq(input, args)
    if input.kind == "multipoint":
        var f = dense.asarray(integers(input.operands[0]))
        var points = integers(input.operands[1])
        var timer = Timer()
        var values = dense.evaluate_many(f, points)
        timer.lap()
        while timer.more(min_seconds, min_reps):
            _ = dense.evaluate_many(f, points)
            timer.lap()
        timer.write(args[3])
        for v in values.to_list():
            out.append(hex_text(v))
    elif input.kind == "interp":
        var points = integers(input.operands[0])
        var samples = integers(input.operands[1])
        var timer = Timer()
        var f = dense.interpolate(points, samples)
        timer.lap()
        while timer.more(min_seconds, min_reps):
            _ = dense.interpolate(points, samples)
            timer.lap()
        timer.write(args[3])
        for v in f.to_list():
            out.append(rational_text(v))
    elif input.kind == "evalq":
        var f = dense.asarray(integers(input.operands[0]))
        var point = integers(input.operands[1])
        var x = Rational(point[0].copy(), point[1].copy())
        var timer = Timer()
        var value = dense.evaluate(f, x)
        timer.lap()
        while timer.more(min_seconds, min_reps):
            _ = dense.evaluate(f, x)
            timer.lap()
        timer.write(args[3])
        out.append(rational_text(value))
    else:
        raise Error("unknown case kind " + input.kind)
    write_values(out, args[2])


def run_gf(input: Input, args: List[String]) raises:
    var min_seconds = atof(args[4])
    var min_reps = Int(args[5])
    var p = input.modulus
    var out = List[String]()
    if input.kind == "series":
        return run_series_gf(input, args)
    if input.kind == "multipoint":
        var f = dense.asarray(residues(input.operands[0], p))
        var points = residues(input.operands[1], p)
        var timer = Timer()
        var values = dense.evaluate_many(f, points)
        timer.lap()
        while timer.more(min_seconds, min_reps):
            _ = dense.evaluate_many(f, points)
            timer.lap()
        timer.write(args[3])
        for v in values.to_list():
            out.append(hex_text(Integer(v.value)))
    elif input.kind == "interp":
        var points = residues(input.operands[0], p)
        var samples = residues(input.operands[1], p)
        var timer = Timer()
        var f = dense.interpolate(points, samples)
        timer.lap()
        while timer.more(min_seconds, min_reps):
            _ = dense.interpolate(points, samples)
            timer.lap()
        timer.write(args[3])
        for v in f.to_list():
            out.append(hex_text(Integer(v.value)))
    else:
        raise Error("unknown case kind " + input.kind)
    write_values(out, args[2])


def main() raises:
    var args = List[String]()
    for arg in argv():
        args.append(String(arg))
    if len(args) != 6:
        raise Error("usage: series INPUT ANSWER RESULT MIN_SECONDS MIN_REPS")
    var input = Input(args[1])
    comptime if MODULAR:
        run_gf(input, args)
    else:
        run_qq(input, args)
