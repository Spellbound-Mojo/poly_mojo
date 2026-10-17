"""Z3 adapter for CAD conjunction cases; runs in the interpreter that has `z3`.

Arguments: CASE RESULT MIN_SECONDS MIN_REPS. Times `Solver.check()` on a fresh
solver each repetition and writes the verdict and an exact model, each
coordinate as `Q:<rational>` or `A:<c0>,...:<low>:<high>` like the Poly Mojo
driver, for the harness to check independently.
"""
from fractions import Fraction
import json
import sys
import time

import z3


def status_kb(field):
    for line in open('/proc/self/status'):
        if line.startswith(field + ':'):
            return int(line.split()[1])
    return 0


def build(case):
    xs = [z3.Real(v) for v in case['variables']]
    constraints = []
    for poly, mask in zip(case['polys'], case['masks']):
        expr = z3.RealVal(0)
        for exps, c in poly:
            term = z3.RealVal(c)
            for x, k in zip(xs, exps):
                for _ in range(k):
                    term = term * x
            expr = expr + term
        constraints.append({1: expr < 0, 2: expr == 0, 4: expr > 0, 3: expr <= 0, 6: expr >= 0, 5: expr != 0}[mask])
    return xs, constraints


def coordinate(value):
    if z3.is_rational_value(value):
        return f'Q:{Fraction(value.numerator_as_long(), value.denominator_as_long())}'
    # An algebraic number: its defining polynomial and an interval of width
    # 2e-55 around a 60-digit approximation (error below 1e-60).
    text = value.approx(60).as_decimal(60).rstrip('?')
    centre = Fraction(text)
    eps = Fraction(1, 10 ** 55)
    coeffs = z3_poly_coefficients(value)
    return 'A:' + ','.join(str(c) for c in coeffs) + f':{centre - eps}:{centre + eps}'


def z3_poly_coefficients(value):
    """Coefficients c0..cd of the defining polynomial of an algebraic model value."""
    return [Fraction(c.numerator_as_long(), c.denominator_as_long()) for c in value.poly()]


def main():
    case = json.load(open(sys.argv[1]))
    min_seconds, min_reps = float(sys.argv[3]), int(sys.argv[4])
    rss_before = status_kb('VmRSS')
    times = []
    total = 0
    while True:
        xs, constraints = build(case)
        s = z3.SolverFor('QF_NRA')
        s.add(*constraints)
        start = time.perf_counter_ns()
        verdict = s.check()
        lap = time.perf_counter_ns() - start
        times.append(lap)
        total += lap
        if len(times) >= min_reps and total >= min_seconds * 1e9 or lap > min_seconds * 1e9:
            break
    if verdict == z3.unknown:
        raise SystemExit('z3 returned unknown')
    result = {'times_ns': times, 'rss_before_kb': rss_before, 'peak_kb': status_kb('VmHWM'), 'sat': verdict == z3.sat}
    if verdict == z3.sat:
        m = s.model()
        result['point'] = [coordinate(m.eval(x, model_completion=True)) for x in xs]
    json.dump(result, open(sys.argv[2], 'w'))


if __name__ == '__main__':
    main()
