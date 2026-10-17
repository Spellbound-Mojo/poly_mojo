"""Benchmark driver: time one sparse multivariate product, power, or exact quotient.

Build one binary per variable count with `mojo build -I build -D NVARS=n`.
Coefficients are integers. (A driver generic in its coefficient type takes
the compiler tens of minutes and over 10 GiB, so each driver is concrete.)

Arguments: input, answer, result, min_seconds, min_reps. The input format is
described in harness/arith.py: operands are bases, and the driver builds
f = base^exponent and g = f + second operand (`shift`) or g = second
operand^exponent (`power`) before the timer starts, as well as the product
divided in `div`. The answer is the result's canonical `sparse.dumps` record.

| Operation | Timed call |
|---|---|
| mul | `sparse.multiply(f, g)` |
| div | `sparse.divide_exact(f * g, g)` |
| pow | `sparse.power(base, exponent)` |
"""
from apn_mojo import Integer
from poly import sparse
from std.sys import argv, get_defined_int
from std.time import perf_counter_ns

comptime NVARS = get_defined_int["NVARS", 1]()


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


def record(rows: List[String], nvars: Int, modulus: UInt64) raises -> String:
    """A canonical sparse text record of `e0 ... coefficient` rows (the loader sorts terms)."""
    var out = String("POLYNOMIALS 1\nSPARSE\n", String("Fp:", modulus) if modulus else String("ZZ"), "\n1\n", nvars, "\n")
    for i in range(nvars):
        out.write(i, "\n")
    out.write(len(rows), "\n")
    for row in rows:
        var parts = row.split(" ")
        var pairs = List[Tuple[Int, Int]]()
        for i in range(nvars):
            var e = Int(String(parts[i]))
            if e:
                pairs.append((i, e))
        out.write(len(pairs), "\n")
        for pair in pairs:
            out.write(pair[0], "\n", pair[1], "\n")
        out.write(String(Integer(String(parts[nvars]), 16)), "\n")
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




def write_sparse(text: String, path: String) raises:
    """Write a result's canonical `sparse.dumps` record; the harness reads it back."""
    with open(path, "w") as f:
        f.write(text)


def run_sparse(input: Input, args: List[String]) raises:
    var min_seconds = atof(args[4])
    var min_reps = Int(args[5])
    var p = input.modulus
    var base = sparse.loads[Integer, ndim=NVARS](record(input.operands[0], NVARS, p), modulus=p)
    var other = sparse.loads[Integer, ndim=NVARS](record(input.operands[1], NVARS, p), modulus=p)
    if input.op == "pow":
        var timer = Timer()
        var power = sparse.power(base, input.exponent)
        timer.lap()
        while timer.more(min_seconds, min_reps):
            _ = sparse.power(base, input.exponent)
            timer.lap()
        timer.write(args[3])
        write_sparse(sparse.dumps(power), args[2])
        return
    # Round-trip the operands through their canonical text (untimed), so that
    # every operand has the loader's concrete array type.
    var f = sparse.loads[Integer, ndim=NVARS](sparse.dumps(sparse.power(base, input.exponent)), modulus=p)
    var g_text = sparse.dumps(sparse.add(f, other)) if input.second == "shift" else sparse.dumps(sparse.power(other, input.exponent))
    var g = sparse.loads[Integer, ndim=NVARS](g_text, modulus=p)
    if input.op == "mul":
        var timer = Timer()
        var product = sparse.multiply(f, g)
        timer.lap()
        while timer.more(min_seconds, min_reps):
            _ = sparse.multiply(f, g)
            timer.lap()
        timer.write(args[3])
        write_sparse(sparse.dumps(product), args[2])
    else:
        var product = sparse.loads[Integer, ndim=NVARS](sparse.dumps(sparse.multiply(f, g)), modulus=p)
        var timer = Timer()
        var q = sparse.divide_exact(product, g)
        timer.lap()
        while timer.more(min_seconds, min_reps):
            _ = sparse.divide_exact(product, g)
            timer.lap()
        timer.write(args[3])
        if not q:
            raise Error("inexact quotient")
        var text = sparse.dumps(q.take())
        if text != sparse.dumps(f):
            raise Error("quotient differs from the first factor")
        write_sparse(text, args[2])


def main() raises:
    var args = List[String]()
    for arg in argv():
        args.append(String(arg))
    if len(args) != 6:
        raise Error("usage: arith_sparse INPUT ANSWER RESULT MIN_SECONDS MIN_REPS")
    var input = Input(args[1])
    if input.kind != "sparse" or input.nvars != NVARS:
        raise Error("built for another variable count")
    run_sparse(input, args)
