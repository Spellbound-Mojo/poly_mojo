"""Benchmark driver: SymPy truncated series, multipoint evaluation, interpolation, and evaluation at a rational.

Usage: series.py INPUT ANSWER RESULT MIN_SECONDS MIN_REPS

INPUT is the series input file described in harness/series.py; set
SYMPY_GROUND_TYPES first. Operands are converted to `sympy.polys.rings`
elements before the timer starts. The timed calls:

| Operation | Call |
|---|---|
| series mul | `ring_series.rs_mul` |
| series inv, sqrt, log, exp, pow | `rs_series_inversion`, `rs_nth_root(f, 2)`, `rs_log`, `rs_exp`, `rs_pow` |
| series compose, revert | `rs_subs(f, {x: g})`, `rs_series_reversion` |
| multipoint | `f(a)` at each point (SymPy has no subproduct-tree evaluation) |
| interp | `polyfuncs.interpolate` (QQ only: SymPy has no interpolation over GF(p)) |
| evalq | `f(QQ(a, b))` |

The answer lists one value per line: a hexadecimal integer, or
`numerator/denominator` in hexadecimal.
"""
import json
import sys
import time


def status_kb(field):
    with open('/proc/self/status') as f:
        for line in f:
            if line.startswith(field + ':'):
                return int(line.split()[1])
    raise RuntimeError(field)


def reset_peak():
    with open('/proc/self/clear_refs', 'w') as f:
        f.write('5')


def read_input(path):
    lines = open(path).read().split('\n')
    header = json.loads(lines[0])
    position, operands = 2, []
    for _ in range(header['operands']):
        count = int(lines[position])
        position += 1
        operands.append([int(t, 16) for t in lines[position:position + count]])
        position += count
    return header, operands


def hexa(v):
    return f'-{-v:x}' if v < 0 else f'{v:x}'


def text(c, p):
    if p:
        return f'{int(c) % p:x}'
    num, den = int(c.numerator), int(c.denominator)
    return hexa(num) if den == 1 else f'{hexa(num)}/{den:x}'


def main():
    _, input_path, answer_path, result_path, min_seconds, min_reps = sys.argv
    min_seconds, min_reps = float(min_seconds), int(min_reps)
    header, ops = read_input(input_path)
    kind, op, p, n = header['kind'], header['op'], header['modulus'], header['n']
    from sympy.polys.domains import GF, QQ
    from sympy.polys.rings import ring
    from sympy.polys import ring_series as rs
    domain = GF(p) if p else QQ
    R, x = ring('x', domain)

    def make(c):
        return R.from_dict({(i,): domain(v) for i, v in enumerate(c) if v})

    if kind == 'series':
        a = make(ops[0])
        b = make(ops[1]) if len(ops) > 1 else None
        calls = {
            'mul': lambda: rs.rs_mul(a, b, x, n),
            'inv': lambda: rs.rs_series_inversion(a, x, n),
            'sqrt': lambda: rs.rs_nth_root(a, 2, x, n),
            'log': lambda: rs.rs_log(a, x, n),
            'exp': lambda: rs.rs_exp(a, x, n),
            'pow': lambda: rs.rs_pow(a, header['exponent'], x, n),
            'compose': lambda: rs.rs_subs(a, {x: b}, x, n),
            'revert': lambda: rs.rs_series_reversion(a, x, n, x),
        }
        call = calls[op]

        def output(r):
            return [r.get((i,), domain.zero) for i in range(n)]
    elif kind == 'multipoint':
        f = make(ops[0])
        points = [domain(v) for v in ops[1]]

        def call():
            return [f(t) for t in points]

        def output(r):
            return r
    elif kind == 'interp':
        from sympy import Symbol
        from sympy.polys.polyfuncs import interpolate
        t = Symbol('x')
        data = list(zip(ops[0], ops[1]))

        def call():
            return interpolate(data, t)

        def output(r):
            from sympy import Poly
            c = Poly(r, t, domain=QQ).all_coeffs()[::-1] if r != 0 else []
            return c + [QQ(0)] * (n - len(c))
    else:  # evalq
        f = make(ops[0])
        point = QQ(ops[1][0], ops[1][1])

        def call():
            return f(point)

        def output(r):
            return [r]

    times = []
    rss_before = status_kb('VmRSS')
    reset_peak()
    total, peak = 0, 0
    while True:
        start = time.perf_counter_ns()
        result = call()
        elapsed = time.perf_counter_ns() - start
        if not times:
            peak = status_kb('VmHWM')
        times.append(elapsed)
        total += elapsed
        if times[0] >= min_seconds * 1e9 or (len(times) >= min_reps and total >= min_seconds * 1e9):
            break
    values = output(result)
    with open(answer_path, 'w') as f:
        f.write(f'{len(values)}\n' + ''.join(text(v, p) + '\n' for v in values))
    with open(result_path, 'w') as f:
        json.dump({'times_ns': times, 'rss_before_kb': rss_before, 'peak_kb': peak}, f)


if __name__ == '__main__':
    main()
