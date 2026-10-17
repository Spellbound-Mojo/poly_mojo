"""Benchmark driver: SymPy real root isolation, refinement, exact roots, and counts.

Arguments: input, answer, result, mode, min_seconds, min_reps.
Modes: isolate (`Poly.intervals`), refine53 and refine1000
(`Poly.intervals(eps=2^-bits)`), exact (`Poly.real_roots`, distinct roots with
their isolating intervals), count (`Poly.count_roots`, which counts with
multiplicity, so it runs on the squarefree part `Poly.sqf_part`, inside the
timed region). The answer lists the count and then `low high` per root.
"""
import json
import sys
import time
from fractions import Fraction

sys.set_int_max_str_digits(0)

import sympy
from sympy import Poly, Symbol, Rational
from sympy.core.cache import clear_cache


def status_kb(field):
    for line in open('/proc/self/status'):
        if line.startswith(field + ':'):
            return int(line.split()[1])
    raise RuntimeError(field)


def reset_peak():
    with open('/proc/self/clear_refs', 'w') as f:
        f.write('5')


def main():
    path, answer_path, result_path, mode, min_seconds, min_reps = sys.argv[1:]
    min_seconds, min_reps = float(min_seconds), int(min_reps)
    lines = open(path).read().split()
    coefficients = [int(c) for c in lines[1:1 + int(lines[0])]]
    x = Symbol('x')
    p = Poly(list(reversed(coefficients)), x, domain='ZZ')
    bits = {'refine53': 53, 'refine1000': 1000}.get(mode)

    def run():
        if mode in ('isolate', 'refine53', 'refine1000'):
            found = p.intervals(eps=Rational(1, 2 ** bits) if bits else None)
            return [(Fraction(int(a.p), int(a.q)), Fraction(int(b.p), int(b.q))) for (a, b), _ in found]
        if mode == 'exact':
            roots = []
            for r in p.real_roots(multiple=False):
                root = r[0]
                if root.is_Rational:
                    v = Fraction(int(root.p), int(root.q))
                    roots.append((v, v))
                else:
                    interval = root._get_interval()
                    a, b = interval.a, interval.b
                    roots.append((Fraction(int(a.p), int(a.q)), Fraction(int(b.p), int(b.q))))
            return roots
        if mode == 'count':
            return int(p.sqf_part().count_roots())
        raise SystemExit(f'unknown mode {mode}')

    times = []
    rss_before = status_kb('VmRSS')
    reset_peak()
    peak = 0
    answer = None
    while not times or len(times) < min_reps or sum(times) < min_seconds * 1e9:
        clear_cache()
        start = time.perf_counter_ns()
        got = run()
        lap = time.perf_counter_ns() - start
        if not times:
            peak = status_kb('VmHWM')
            answer = got
        times.append(lap)
        if lap >= min_seconds * 1e9:
            break
    with open(answer_path, 'w') as f:
        if isinstance(answer, int):
            f.write(f'{answer}\n')
        else:
            f.write(f'{len(answer)}\n' + ''.join(f'{a} {b}\n' for a, b in answer))
    from sympy.external.gmpy import GROUND_TYPES
    with open(result_path, 'w') as f:
        json.dump({'times_ns': times, 'rss_before_kb': rss_before, 'peak_kb': peak, 'ground_types': GROUND_TYPES}, f)


if __name__ == '__main__':
    main()
