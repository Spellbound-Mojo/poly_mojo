"""Benchmark driver: peak memory of streaming against materialized routes.

Build with `mojo build -I build -D NVARS=n`. Arguments: KIND MODE INPUT RESULT PARAM.
The input holds length-prefixed sparse QQ records, as for the Gröbner driver.

| Kind | Mode | Work measured |
|---|---|---|
| cad | decompose | `cad.decompose` (retained decomposition, no check) |
| cad | materialized | `cad.decompose` then `cad.check` |
| cad | streaming | `cad.checker`, `cad.decompose_to`, `finish` |
| roots | materialized | `sparse.real_root_cover` then `roots.check` |
| roots | streaming | `sparse.real_root_checker`, `real_root_cover_to`, `finish` |
| dump | materialized | `sparse.dumps` of `power(first record, PARAM)`, written to a file |
| dump | streaming | `sparse.dump` of the same power into a file sink |
| load | materialized | read the file from `dump` into a string, then `sparse.loads` |
| load | streaming | `sparse.load` from a file source |

For roots, PARAM is the absolute accuracy in bits. Each mode measures the
resident-size high-water mark from just before the work to its end.
"""
from apn_mojo import Rational
from poly import cad, roots, sparse
from polynomials import Budget, NumericOptions, PolyError, PolyErrorKind, PolynomialTextSink, PolynomialTextSource
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


struct FileSink(PolynomialTextSink):
    var handle: FileHandle
    var bytes: Int

    def __init__(out self, path: String) raises:
        self.handle = open(path, "w")
        self.bytes = 0

    def write(mut self, var chunk: String, mut budget: Budget) raises PolyError:
        self.bytes += chunk.byte_length()
        try:
            self.handle.write(chunk)
        except e:
            raise PolyError(PolyErrorKind.ENCODING, String(e))


struct FileSource(PolynomialTextSource):
    var handle: FileHandle

    def __init__(out self, path: String) raises:
        self.handle = open(path, "r")

    def read(mut self, mut budget: Budget) raises PolyError -> Optional[String]:
        try:
            var chunk = self.handle.read(1 << 16)
            if chunk.byte_length() == 0:
                return None
            return chunk^
        except e:
            raise PolyError(PolyErrorKind.ENCODING, String(e))


def main() raises:
    var args = List[String]()
    for arg in argv():
        args.append(String(arg))
    if len(args) != 6:
        raise Error("usage: streaming KIND MODE INPUT RESULT PARAM")
    var kind = args[1]
    var mode = args[2]
    var param = Int(args[5])
    var records = read_records(args[3])
    var polys = List[type_of(sparse.loads[Rational, ndim=NVARS](records[0]))](capacity=len(records))
    for record in records:
        polys.append(sparse.loads[Rational, ndim=NVARS](record))

    var count = 0
    var ok = True
    var bytes = 0
    var rss_before = 0
    var start = 0
    var elapsed = 0
    if kind == "dump" or kind == "load":
        var p = sparse.power(polys[0], param)
        var path = args[4] + ".txt"
        count = len(p)
        if kind == "dump":
            rss_before = status_kb("VmRSS")
            reset_peak()
            start = perf_counter_ns()
            if mode == "materialized":
                var text = sparse.dumps(p)
                bytes = text.byte_length()
                with open(path, "w") as f:
                    f.write(text)
            else:
                var sink = FileSink(path)
                sparse.dump(p, sink)
                bytes = sink.bytes
            elapsed = perf_counter_ns() - start
        else:
            # Prepare the file with the streaming writer, then drop the polynomial.
            var sink = FileSink(path)
            sparse.dump(p, sink)
            bytes = sink.bytes
            _ = p^
            rss_before = status_kb("VmRSS")
            reset_peak()
            start = perf_counter_ns()
            if mode == "materialized":
                var text = open(path, "r").read()
                var q = sparse.loads[Rational, ndim=NVARS](text)
                ok = len(q) == count
            else:
                var q = sparse.load[Rational, FileSource, ndim=NVARS](FileSource(path))
                ok = len(q) == count
            elapsed = perf_counter_ns() - start
    elif kind == "cad":
        rss_before = status_kb("VmRSS")
        reset_peak()
        start = perf_counter_ns()
        if mode == "streaming":
            var checker = cad.checker(polys)
            var receipt = cad.decompose_to(polys, checker)
            var work = Budget()
            ok = checker.finish(receipt, work)
            count = receipt.cells
        else:
            var decomposition = cad.decompose(polys)
            if mode == "materialized":
                ok = cad.check(decomposition)
            elapsed = perf_counter_ns() - start
            # Count cells after the measured region; describing them allocates.
            var peak_so_far = status_kb("VmHWM")
            count = len(cad.cells(decomposition))
            var result = String('{"kind": "', kind, '", "mode": "', mode, '", "time_ns": ', elapsed,
                                ', "rss_before_kb": ', rss_before, ', "peak_kb": ', peak_so_far,
                                ', "count": ', count, ', "bytes": 0, "ok": ', "true" if ok else "false", "}\n")
            with open(args[4], "w") as f:
                f.write(result)
            return
        elapsed = perf_counter_ns() - start
    elif kind == "roots":
        var options = NumericOptions(absolute_bits=param)
        rss_before = status_kb("VmRSS")
        reset_peak()
        start = perf_counter_ns()
        if mode == "streaming":
            var checker = sparse.real_root_checker(polys[0], options=options)
            var receipt = sparse.real_root_cover_to(polys[0], checker, options=options, complete_only=True)
            var work = Budget()
            ok = checker.finish(receipt, work)
            count = receipt.items
        else:
            var cover = sparse.real_root_cover(polys[0], options=options, complete_only=True)
            ok = roots.check(cover)
            count = len(cover.evidence().cells)
        elapsed = perf_counter_ns() - start
    else:
        raise Error("unknown kind " + kind)

    var peak = status_kb("VmHWM")
    var result = String('{"kind": "', kind, '", "mode": "', mode, '", "time_ns": ', elapsed,
                        ', "rss_before_kb": ', rss_before, ', "peak_kb": ', peak,
                        ', "count": ', count, ', "bytes": ', bytes, ', "ok": ', "true" if ok else "false", "}\n")
    with open(args[4], "w") as f:
        f.write(result)
