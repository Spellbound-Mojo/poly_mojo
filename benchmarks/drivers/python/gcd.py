"""Benchmark driver: one gcd, resultant, or discriminant with python-flint or SymPy.

Usage: gcd.py ENGINE CASE ANSWER RESULT MIN_SECONDS MIN_REPS, ENGINE flint or sympy.

The case's polynomials are converted to the engine's objects before the timer
starts. FLINT uses fmpz_poly and nmod_poly for univariate cases and fmpz_mpoly
(lex) otherwise; SymPy uses Poly over ZZ or GF(p) with the eliminated variable
first, so `resultant` eliminates it. Short calls repeat in-process with a
cleared SymPy cache until MIN_SECONDS and MIN_REPS are reached.
"""
import json
import sys
import time
from fractions import Fraction

# Resultants routinely exceed Python's default 4300-digit conversion limit.
sys.set_int_max_str_digits(0)


def status_kb(field):
    for line in open('/proc/self/status'):
        if line.startswith(field + ':'):
            return int(line.split()[1])
    raise RuntimeError(field)


def reset_peak():
    with open('/proc/self/clear_refs', 'w') as f:
        f.write('5')


def flint_setup(case, polys):
    import flint
    field, nvars = case['field'], len(case['variables'])
    if nvars == 1:
        def dense(p):
            n = max(e[0] for e, _ in p)
            c = [0] * (n + 1)
            for e, v in p:
                c[e[0]] = v
            return flint.fmpz_poly(c) if field is None else flint.nmod_poly(c, field)
        objs = [dense(p) for p in polys]
        to_terms = lambda r: [[[i], str(int(c))] for i, c in enumerate(r.coeffs()) if int(c)]
        scalar = lambda r: [[[0], str(int(r))]] if int(r) else []
        ops = {'gcd': lambda: objs[0].gcd(objs[1]), 'resultant': lambda: objs[0].resultant(objs[1]),
               'discriminant': lambda: objs[0].discriminant()}
        out = (lambda r: scalar(r)) if case['operation'] != 'gcd' else to_terms
        return ops[case['operation']], out
    if field is not None:
        raise SystemExit('multivariate GF(p) cases are not in this family')
    ctx = flint.fmpz_mpoly_ctx.get(case['variables'], 'lex')
    objs = [ctx.from_dict({tuple(e): v for e, v in p}) for p in polys]
    v0 = case['variables'][0]
    ops = {'gcd': lambda: objs[0].gcd(objs[1]), 'resultant': lambda: objs[0].resultant(objs[1], v0),
           'discriminant': lambda: objs[0].discriminant(v0)}
    return ops[case["operation"]], lambda r: [[[int(x) for x in e], str(int(c))] for e, c in r.to_dict().items()]


def sympy_setup(case, polys):
    from sympy import Poly, symbols, GF, ZZ
    from sympy.core.cache import clear_cache
    gens = symbols(case['variables'])
    field = case['field']
    domain = ZZ if field is None else GF(field, symmetric=False)
    objs = [Poly.from_dict({tuple(e): v for e, v in p}, *gens, domain=domain) for p in polys]
    ops = {'gcd': lambda: objs[0].gcd(objs[1]), 'resultant': lambda: objs[0].resultant(objs[1]),
           'discriminant': lambda: objs[0].discriminant()}
    op = ops[case['operation']]

    def run():
        clear_cache()
        return op()

    def out(r):
        if isinstance(r, Poly):
            return [[[0] * len(gens) if not m else list(m), str(int(c))] for m, c in r.terms() if c]
        r = int(r)
        return [[[0] * len(gens), str(r)]] if r else []
    if len(gens) > 1 and case['operation'] != 'gcd':
        # The resultant lives in the remaining variables; widen it back to all of them.
        def out(r, base=out):
            if isinstance(r, Poly):
                return [[[0] + list(m), str(int(c))] for m, c in r.terms() if c]
            return base(r)
    return run, out


def main():
    engine, case_path, answer_path, result_path = sys.argv[1:5]
    min_seconds, min_reps = float(sys.argv[5]), int(sys.argv[6])
    case = json.load(open(case_path))
    polys = [[(e, int(Fraction(v))) for e, v in p] for p in case['generators']]
    call, out = (flint_setup if engine == 'flint' else sympy_setup)(case, polys)
    rss = status_kb('VmRSS')
    reset_peak()
    t = time.perf_counter_ns()
    r = call()
    times = [time.perf_counter_ns() - t]
    peak = status_kb('VmHWM')
    limit = min_seconds * 1e9
    if times[0] < limit:
        while len(times) < min_reps or sum(times) < limit:
            t = time.perf_counter_ns()
            call()
            times.append(time.perf_counter_ns() - t)
    if engine == 'sympy':
        import sympy.external.gmpy as g
        ground = g.GROUND_TYPES
    else:
        ground = None
    json.dump(out(r), open(answer_path, 'w'))
    json.dump({'times_ns': times, 'rss_before_kb': rss, 'peak_kb': peak, 'ground_types': ground}, open(result_path, 'w'))


if __name__ == '__main__':
    main()
