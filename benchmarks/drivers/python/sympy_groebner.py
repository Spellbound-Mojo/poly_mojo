"""Benchmark driver: time one SymPy Gröbner basis and measure its memory.

Usage: sympy_groebner.py CASE ANSWER RESULT METHOD MIN_SECONDS MIN_REPS

METHOD `fglm` computes a grevlex basis by Buchberger's algorithm and converts
it to the case's order with `matrix_fglm`, for zero-dimensional ideals.

The driver builds `sympy.polys.rings` elements directly, so expression
conversion stays outside the timed region, and calls
`sympy.polys.groebnertools.groebner`, the routine `sympy.groebner` uses after
converting its arguments. Set SYMPY_GROUND_TYPES before starting the process.
"""
import json
import sys
import time
from fractions import Fraction

from sympy.core.cache import clear_cache
from sympy.polys.domains import GF, QQ
from sympy.polys.fglmtools import matrix_fglm
from sympy.polys.groebnertools import groebner
from sympy.polys.orderings import grevlex, grlex, lex
from sympy.polys.rings import ring
import sympy.external.gmpy

ORDERS = {'lex': lex, 'grlex': grlex, 'grevlex': grevlex}


def status_kb(field):
    with open('/proc/self/status') as f:
        for line in f:
            if line.startswith(field + ':'):
                return int(line.split()[1])
    raise RuntimeError(field)


def reset_peak():
    with open('/proc/self/clear_refs', 'w') as f:
        f.write('5')


def main():
    case_path, answer_path, result_path, method, min_seconds, min_reps = sys.argv[1:]
    min_seconds, min_reps = float(min_seconds), int(min_reps)
    case = json.load(open(case_path))
    p = case['field']
    domain = QQ if p is None else GF(p)
    target = ORDERS[case['order']]
    R, *_ = ring(','.join(case['variables']), domain, grevlex if method == 'fglm' else target)

    def compute(generators):
        if method == 'fglm':
            return matrix_fglm(groebner(generators, R, method='buchberger'), R, target)
        return groebner(generators, R, method=method)

    def element(text):
        value = Fraction(text)
        return domain(value.numerator) / domain(value.denominator)

    generators = [R.from_dict({tuple(e): element(c) for e, c in poly}) for poly in case['generators']]

    clear_cache()
    rss_before = status_kb('VmRSS')
    reset_peak()
    start = time.perf_counter_ns()
    basis = compute(generators)
    elapsed = time.perf_counter_ns() - start
    peak = status_kb('VmHWM')
    times = [elapsed]
    if elapsed < min_seconds * 1e9:
        while len(times) < min_reps or sum(times) < min_seconds * 1e9:
            clear_cache()
            start = time.perf_counter_ns()
            compute(generators)
            times.append(time.perf_counter_ns() - start)

    def text(c):
        if p is not None:
            return str(int(domain.to_int(c)) % p)
        return str(Fraction(int(c.numerator), int(c.denominator)))

    answer = [[[list(m), text(c)] for m, c in g.terms()] for g in basis]
    json.dump({'polys': answer}, open(answer_path, 'w'))
    json.dump({'times_ns': times, 'rss_before_kb': rss_before, 'peak_kb': peak,
               'basis_length': len(basis), 'ground_types': sympy.external.gmpy.GROUND_TYPES},
              open(result_path, 'w'))


if __name__ == '__main__':
    main()
