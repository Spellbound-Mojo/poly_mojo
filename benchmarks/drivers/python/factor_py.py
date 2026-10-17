"""Benchmark driver: time one factorization with python-flint or SymPy.

Arguments: library (flint | sympy), case, answer, result, min_seconds, min_reps.
Building the input polynomial and writing the answer stay outside the timed
region. Calls shorter than min_seconds repeat until min_reps calls and
min_seconds have elapsed. The answer is the raw scalar and factors; the harness
normalizes them.
"""
import json
import sys
import time

sys.set_int_max_str_digits(0)
VARS = ['x', 'y', 'z', 't', 'u', 'v', 'w', 's']


def status_kb(field):
    for line in open('/proc/self/status'):
        if line.startswith(field + ':'):
            return int(line.split()[1])
    raise RuntimeError(field)


def reset_peak():
    with open('/proc/self/clear_refs', 'w') as f:
        f.write('5')


def flint_call(case):
    import flint
    kind = case['kind']
    if kind == 'zz':
        f = flint.fmpz_poly([int(c) for c in case['poly']])
    elif kind == 'gf':
        f = flint.nmod_poly([int(c) for c in case['poly']], case['modulus'])
    else:
        ctx = flint.fmpz_mpoly_ctx.get(tuple(VARS[:case['nvars']]), 'lex')
        f = ctx.from_dict({tuple(e): int(c) for e, c in case['poly']})

    def call():
        return f.factor()

    def convert(result):
        unit, factors = result
        if kind == 'mzz':
            return {'unit': str(int(unit)),
                    'factors': [[[[[int(v) for v in e], str(int(c))] for e, c in g.to_dict().items()], m] for g, m in factors]}
        return {'unit': str(int(unit)), 'factors': [[[str(int(c)) for c in g.coeffs()], m] for g, m in factors]}
    return call, convert


def sympy_call(case):
    from sympy import ZZ, GF
    from sympy.polys.rings import ring
    kind = case['kind']
    if kind == 'mzz':
        R, *_ = ring(','.join(VARS[:case['nvars']]), ZZ)
        f = R({tuple(e): int(c) for e, c in case['poly']})
    else:
        domain = GF(case['modulus'], symmetric=False) if kind == 'gf' else ZZ
        R, _ = ring('x', domain)
        f = R({(i,): int(c) for i, c in enumerate(case['poly']) if int(c)})

    def call():
        return f.factor_list()

    def convert(result):
        unit, factors = result
        out = []
        for g, m in factors:
            if kind == 'mzz':
                out.append([[[list(e), str(int(c))] for e, c in g.terms()], m])
            else:
                coeffs = [0] * (g.degree() + 1)
                for (e,), c in g.terms():
                    coeffs[e] = int(c)
                out.append([[str(c) for c in coeffs], m])
        return {'unit': str(int(unit)), 'factors': out}
    return call, convert


def main():
    library, case_path, answer_path, result_path, min_seconds, min_reps = sys.argv[1:7]
    case = json.loads(open(case_path).read())
    call, convert = (flint_call if library == 'flint' else sympy_call)(case)
    min_seconds, min_reps = float(min_seconds), int(min_reps)
    rss = status_kb('VmRSS')
    reset_peak()
    start = time.perf_counter_ns()
    result = call()
    times = [time.perf_counter_ns() - start]
    peak = status_kb('VmHWM')
    if times[0] < min_seconds * 1e9:
        while len(times) < min_reps or sum(times) < min_seconds * 1e9:
            start = time.perf_counter_ns()
            call()
            times.append(time.perf_counter_ns() - start)
    open(answer_path, 'w').write(json.dumps(convert(result)))
    open(result_path, 'w').write(json.dumps({'times_ns': times, 'rss_before_kb': rss, 'peak_kb': peak}))


if __name__ == '__main__':
    main()
