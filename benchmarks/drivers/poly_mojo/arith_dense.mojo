"""Benchmark driver: time one dense univariate product, square, or exact quotient.

Build one binary per coefficient domain with `mojo build -I build -D MODULAR=0|1`.

Arguments: input, answer, result, min_seconds, min_reps. The input format is
described in harness/arith.py. The product divided in `div` is built before
the timer starts. The answer lists the result's coefficients from degree
zero, one hexadecimal value per line.

| Operation | Timed call |
|---|---|
| mul | `dense.multiply(a, b)` |
| sqr | `dense.multiply(a, a)` |
| div | `dense.divide_exact(a * b, b)` |
"""
from apn_mojo import Integer
from poly import dense
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
    var nvars: Int
    var exponent: Int
    var second: String
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
        self.nvars = Int(String(head[3]))
        self.exponent = Int(String(head[4]))
        self.second = String(head[5])
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


def coefficients(rows: List[String], modulus: UInt64) raises -> List[Integer]:
    var values = List[Integer](capacity=len(rows))
    for row in rows:
        values.append(Integer(row, 16))
    return values^




def write_coefficients(values: List[String], path: String) raises:
    var out = String(len(values), "\n")
    for v in values:
        out.write(v, "\n")
    with open(path, "w") as f:
        f.write(out)


def run_zz(input: Input, args: List[String]) raises:
    var min_seconds = atof(args[4])
    var min_reps = Int(args[5])
    var a = dense.asarray(coefficients(input.operands[0], 0))
    var b = dense.asarray(coefficients(input.operands[1], 0))
    var out = List[String]()
    if input.op == "div":
        var product = dense.multiply(a, b)
        var timer = Timer()
        var q = dense.divide_exact(product, b)
        timer.lap()
        while timer.more(min_seconds, min_reps):
            _ = dense.divide_exact(product, b)
            timer.lap()
        timer.write(args[3])
        if not q:
            raise Error("inexact quotient")
        var values = q.take().to_list()
        if values != a.to_list():
            raise Error("quotient differs from the first factor")
        for v in values:
            out.append(hex_text(v))
    else:
        if input.op == "sqr":
            b = a.copy()
        var timer = Timer()
        var product = dense.multiply(a, b)
        timer.lap()
        while timer.more(min_seconds, min_reps):
            _ = dense.multiply(a, b)
            timer.lap()
        timer.write(args[3])
        for v in product.to_list():
            out.append(hex_text(v))
    write_coefficients(out, args[2])


def run_gf(input: Input, args: List[String]) raises:
    var min_seconds = atof(args[4])
    var min_reps = Int(args[5])
    var p = input.modulus
    var a = dense.asarray(coefficients(input.operands[0], p), modulus=p)
    var b = dense.asarray(coefficients(input.operands[1], p), modulus=p)
    var out = List[String]()
    if input.op == "div":
        var product = dense.multiply(a, b)
        var timer = Timer()
        var q = dense.divide_exact(product, b)
        timer.lap()
        while timer.more(min_seconds, min_reps):
            _ = dense.divide_exact(product, b)
            timer.lap()
        timer.write(args[3])
        if not q:
            raise Error("inexact quotient")
        var values = q.take().to_list()
        var expected = a.to_list()
        if len(values) != len(expected):
            raise Error("quotient differs from the first factor")
        for i in range(len(values)):
            if values[i].value != expected[i].value:
                raise Error("quotient differs from the first factor")
            out.append(hex_text(Integer(values[i].value)))
    else:
        if input.op == "sqr":
            b = a.copy()
        var timer = Timer()
        var product = dense.multiply(a, b)
        timer.lap()
        while timer.more(min_seconds, min_reps):
            _ = dense.multiply(a, b)
            timer.lap()
        timer.write(args[3])
        for v in product.to_list():
            out.append(hex_text(Integer(v.value)))
    write_coefficients(out, args[2])


def main() raises:
    var args = List[String]()
    for arg in argv():
        args.append(String(arg))
    if len(args) != 6:
        raise Error("usage: arith_dense INPUT ANSWER RESULT MIN_SECONDS MIN_REPS")
    var input = Input(args[1])
    if input.kind != "dense":
        raise Error("the dense driver runs dense cases only")
    comptime if MODULAR:
        run_gf(input, args)
    else:
        run_zz(input, args)
