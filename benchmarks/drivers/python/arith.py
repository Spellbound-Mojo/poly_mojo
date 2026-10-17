"""Benchmark driver: time one dense or sparse product, square, power, or exact quotient.

Usage: arith.py LIBRARY INPUT ANSWER RESULT MIN_SECONDS MIN_REPS

LIBRARY is `flint` (python-flint: fmpz_poly, nmod_poly, fmpz_mpoly, nmod_mpoly)
or `sympy` (`sympy.polys.rings` elements; set SYMPY_GROUND_TYPES first).
INPUT is the arithmetic input file described in harness/arith.py. Operands
that the timed call consumes, such as the product divided in `div`, are built
before the timer starts. The answer file lists the result in the harness's
term text: one coefficient per line from degree zero for dense results, and
`e0 e1 ... coefficient` lines for sparse results, coefficients in hexadecimal.
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
    """Return (header dict, list of operands); dense operands are coefficient lists, sparse ones term dicts."""
    lines = open(path).read().split('\n')
    header = json.loads(lines[0])
    position = 2  # the second line repeats the header for the Mojo driver
    operands = []
    for _ in range(header['operands']):
        count = int(lines[position])
        position += 1
        if header['kind'] == 'dense':
            operands.append([int(t, 16) for t in lines[position:position + count]])
        else:
            poly = {}
            for line in lines[position:position + count]:
                *exps, c = line.split()
                poly[tuple(int(e) for e in exps)] = int(c, 16)
            operands.append(poly)
        position += count
    return header, operands


class Flint:
    def __init__(self, header):
        import flint
        self.flint = flint
        self.header = header
        p = header['modulus']
        if header['kind'] == 'dense':
            self.make = (lambda c: flint.nmod_poly(c, p)) if p else flint.fmpz_poly
        else:
            names = tuple(f'x{i}' for i in range(header['nvars']))
            if p:
                self.ctx = flint.nmod_mpoly_ctx.get(names, p, 'lex')
            else:
                self.ctx = flint.fmpz_mpoly_ctx.get(names, 'lex')
            self.make = lambda d: self.ctx.from_dict(d)

    def version(self):
        return f'python-flint {self.flint.__version__}, FLINT {self.flint.__FLINT_VERSION__}'

    def divide(self, a, b):
        # Quotient only (fmpz_poly_div, fmpz_mpoly_div): far faster than divmod for
        # multivariate operands. The driver checks the quotient after timing.
        return a // b

    def terms(self, value):
        if self.header['kind'] == 'dense':
            return [int(c) for c in value.coeffs()]
        return {tuple(int(e) for e in exps): int(c) for exps, c in zip(value.monoms(), value.coeffs())}


class SymPy:
    def __init__(self, header):
        from sympy.polys.domains import GF, ZZ
        from sympy.polys.rings import ring
        from sympy.polys.orderings import lex
        p = header['modulus']
        self.header = header
        self.domain = GF(p) if p else ZZ
        n = 1 if header['kind'] == 'dense' else header['nvars']
        self.ring, *_ = ring(','.join(f'x{i}' for i in range(n)), self.domain, lex)
        if header['kind'] == 'dense':
            self.make = lambda c: self.ring.from_dict({(i,): v for i, v in enumerate(c) if v})
        else:
            self.make = lambda d: self.ring.from_dict(d)

    def version(self):
        import sympy
        import sympy.external.gmpy
        return f'{sympy.__version__} ({sympy.external.gmpy.GROUND_TYPES} ground types)'

    def divide(self, a, b):
        q, r = a.div(b)
        if r:
            raise RuntimeError('inexact quotient')
        return q

    def integer(self, c):
        p = self.header['modulus']
        return int(self.domain.to_int(c)) % p if p else int(c)

    def terms(self, value):
        if self.header['kind'] == 'dense':
            degree = max((m[0] for m in value.keys()), default=-1)
            out = [0] * (degree + 1)
            for m, c in value.items():
                out[m[0]] = self.integer(c)
            return out
        return {tuple(m): self.integer(c) for m, c in value.items()}


def main():
    library, input_path, answer_path, result_path, min_seconds, min_reps = sys.argv[1:]
    min_seconds, min_reps = float(min_seconds), int(min_reps)
    header, operands = read_input(input_path)
    lib = (Flint if library == 'flint' else SymPy)(header)
    values = [lib.make(o) for o in operands]
    op = header['op']
    if header['kind'] == 'sparse' and op != 'pow':
        # Sparse operands arrive as bases and exponents: f = base^n, g as the case defines.
        f = values[0] ** header['exponent']
        g = f + values[1] if header['second'] == 'shift' else values[1] ** header['exponent']
        values = [f, g]
    if op == 'mul':
        a, b = values
        call = lambda: a * b
    elif op == 'sqr':
        a = values[0]
        call = lambda: a * a
    elif op == 'pow':
        a = values[0]
        e = header['exponent']
        call = lambda: a ** e
    elif op == 'div':
        a, b = values
        product = a * b
        call = lambda: lib.divide(product, b)
    else:
        raise SystemExit(f'unknown operation {op}')

    clear = lambda: None
    if library == 'sympy':
        from sympy.core.cache import clear_cache
        clear = clear_cache
    clear()
    rss_before = status_kb('VmRSS')
    reset_peak()
    start = time.perf_counter_ns()
    result = call()
    elapsed = time.perf_counter_ns() - start
    peak = status_kb('VmHWM')
    times = [elapsed]
    if elapsed < min_seconds * 1e9:
        while len(times) < min_reps or sum(times) < min_seconds * 1e9:
            clear()
            start = time.perf_counter_ns()
            call()
            times.append(time.perf_counter_ns() - start)
    if op == 'div' and result != values[0]:
        raise SystemExit('quotient differs from the first factor')

    terms = lib.terms(result)
    with open(answer_path, 'w') as f:
        if header['kind'] == 'dense':
            f.write(f'{len(terms)}\n' + ''.join(f'{c:x}\n' for c in terms))
        else:
            f.write(f'{len(terms)}\n' + ''.join(' '.join(map(str, e)) + f' {c:x}\n' for e, c in terms.items()))
    json.dump({'times_ns': times, 'rss_before_kb': rss_before, 'peak_kb': peak, 'version': lib.version()},
              open(result_path, 'w'))


if __name__ == '__main__':
    main()
