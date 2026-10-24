"""Factorization family: case generation, tool adapters, runs, checks and report.

    python -m harness.factor generate
    python -m harness.factor run [--tools a,b] [--cases REGEX] [--timeout S]
    python -m harness.factor report [FOLDER]

Cases (benchmarks/README.md, "Univariate factorization" and the factorization
half of "Multivariate factorization and gcd"):

- `zz`: univariate over ZZ (Swinnerton-Dyer S4 … S7, x^N − 1, products of k
  random irreducibles, repeated factors f³g²);
- `gf`: random monic univariate polynomials over GF(p) for p = 3, 65521 and
  the 61-bit prime 2^61 − 1;
- `mzz`: multivariate over ZZ (SymPy's Wang test polynomials `w_polys` and
  `f_polys`, the dense products (1 + x + y + z)^k (2 + x + y + z)^k, and
  sparse random products in 3 … 8 variables).

Every answer is reduced to a canonical factor multiset (primitive with a
positive leading coefficient over ZZ, lex-leading term positive for
multivariate factors, monic over GF(p)) and its product is checked against the
input with FLINT, untimed. The harness keeps this family in its own module and
records; it reuses only `measure.run` and the Poly Mojo build conventions.
"""
import argparse
import datetime
import hashlib
import json
import os
from pathlib import Path
import random
import re
import shutil
import statistics
import subprocess
import sys
import tempfile
import traceback

from . import measure
from .polys import digest

sys.set_int_max_str_digits(0)

HERE = Path(__file__).resolve().parent.parent
ROOT = HERE.parent
CASES = HERE / 'cases' / 'factor'
CACHE = HERE / '.cache'
P61 = (1 << 61) - 1
VARS = ['x', 'y', 'z', 't', 'u', 'v', 'w', 's']


# ------------------------------------------------------------------ cases

def _random_poly(rng, degree, bits):
    """Random integer coefficients of up to `bits` bits; nonzero leading and constant terms."""
    bound = 1 << bits
    c = [rng.randrange(-bound + 1, bound) for _ in range(degree + 1)]
    while c[0] == 0:
        c[0] = rng.randrange(-bound + 1, bound)
    while c[-1] == 0:
        c[-1] = rng.randrange(1, bound)
    return c


def _random_irreducible(rng, degree, bits):
    import flint
    while True:
        c = _random_poly(rng, degree, bits)
        content, factors = flint.fmpz_poly(c).factor()
        if len(factors) == 1 and factors[0][1] == 1 and abs(int(content)) == 1:
            return c


def _mul(*polys):
    import flint
    p = flint.fmpz_poly([1])
    for q in polys:
        p *= flint.fmpz_poly(q)
    return [int(c) for c in p.coeffs()]


def _zz_cases():
    from sympy.polys.specialpolys import swinnerton_dyer_poly
    from sympy import Poly, Symbol
    x = Symbol('x')
    cases = []
    for n in range(4, 8):
        coeffs = [int(c) for c in reversed(Poly(swinnerton_dyer_poly(n, x), x).all_coeffs())]
        cases.append(('zz-swinnerton-dyer-%d' % n, 'swinnerton-dyer', 2 ** n, coeffs))
    for n in (360, 2520, 5040):
        cases.append((f'zz-cyclotomic-{n}', 'cyclotomic', n, [-1] + [0] * (n - 1) + [1]))
    for bits in (16, 256):
        for k in (2, 8):
            for d in (10, 25, 50, 100):
                rng = random.Random(f'factor-zz-{k}-{d}-{bits}')
                factors = [_random_irreducible(rng, d, bits) for _ in range(k)]
                cases.append((f'zz-product-k{k}-d{d}-b{bits}', f'product-k{k}-b{bits}', k * d, _mul(*factors)))
    for d in (10, 20, 40):
        rng = random.Random(f'factor-zz-repeated-{d}')
        f, g = _random_irreducible(rng, d, 16), _random_irreducible(rng, d, 16)
        cases.append((f'zz-repeated-d{d}', 'repeated', 5 * d, _mul(f, f, f, g, g)))
    return [{'id': i, 'family': 'factor', 'kind': 'zz', 'ladder': l, 'size': s, 'modulus': 0, 'nvars': 1,
             'poly': [str(c) for c in c_]} for i, l, s, c_ in cases]


def _gf_cases():
    cases = []
    for name, p in (('p3', 3), ('p65521', 65521), ('p61', P61)):
        for n in (100, 250, 500, 1000, 2000):
            rng = random.Random(f'factor-gf-{p}-{n}')
            c = [rng.randrange(p) for _ in range(n)] + [1]
            cases.append({'id': f'gf-{name}-d{n}', 'family': 'factor', 'kind': 'gf', 'ladder': f'gf-{name}',
                          'size': n, 'modulus': p, 'nvars': 1, 'poly': [str(v) for v in c]})
    return cases


def _mzz(id_, ladder, size, terms):
    nvars = len(next(iter(terms))[0]) if terms else 1
    return {'id': id_, 'family': 'factor', 'kind': 'mzz', 'ladder': ladder, 'size': size, 'modulus': 0,
            'nvars': nvars, 'poly': sorted([[int(v) for v in e], str(int(c))] for e, c in terms)}


def _mzz_cases():
    import flint
    from sympy.polys.specialpolys import w_polys, f_polys
    cases = []
    for name, polys in (('w', w_polys()), ('f', f_polys())):
        for i, p in enumerate(polys, 1):
            cases.append(_mzz(f'mzz-wang-{name}{i}', 'wang', len(p), [(e, int(c)) for e, c in p.terms()]))
    ctx = flint.fmpz_mpoly_ctx.get(tuple(VARS[:3]), 'lex')
    x, y, z = ctx.gens()
    for k in (5, 7, 10, 12, 15):
        p = (1 + x + y + z) ** k * (2 + x + y + z) ** k
        cases.append(_mzz(f'mzz-dense-k{k}', 'dense', k, [(e, int(c)) for e, c in p.to_dict().items()]))
    for n, t in ((3, 10), (3, 30), (4, 20), (5, 30), (6, 30), (8, 30), (8, 100)):
        rng = random.Random(f'factor-mzz-{n}-{t}')
        ctx = flint.fmpz_mpoly_ctx.get(tuple(VARS[:n]), 'lex')
        product = ctx.from_dict({(0,) * n: 1})
        for _ in range(2):
            while True:
                d = {}
                for _ in range(t):
                    d[tuple(rng.randrange(0, 5) for _ in range(n))] = rng.randrange(-99, 100) or 1
                d[(0,) * n] = rng.randrange(1, 100)
                f = ctx.from_dict(d)
                c, fs = f.factor()
                if len(fs) == 1 and fs[0][1] == 1:
                    break
            product *= f
        cases.append(_mzz(f'mzz-sparse-n{n}-t{t}', f'sparse-n{n}', n * 1000 + t,
                          [(e, int(c)) for e, c in product.to_dict().items()]))
    return cases


def cases():
    return _zz_cases() + _gf_cases() + _mzz_cases()


def generate():
    CASES.mkdir(parents=True, exist_ok=True)
    produced = cases()
    for case in produced:
        (CASES / f"{case['id']}.json").write_text(json.dumps(case, separators=(',', ':')) + '\n')
    return produced


def load():
    if not CASES.is_dir():
        return generate()
    return [json.loads(p.read_text()) for p in sorted(CASES.glob('*.json'))]


def case_order(case):
    return ({'zz': 0, 'gf': 1, 'mzz': 2}[case['kind']], case['ladder'], case['size'])


# --------------------------------------------------------- canonical answers

def canonical_univariate(unit, factors, modulus):
    """`factors` holds (coefficients low to high, multiplicity); normalize and sort."""
    unit = int(unit)
    rows = []
    for coeffs, e in factors:
        c = [int(v) for v in coeffs]
        while c and (c[-1] % modulus if modulus else c[-1]) == 0:
            c.pop()
        if modulus:
            c = [v % modulus for v in c]
            inv = pow(c[-1], -1, modulus)
            unit = unit * pow(c[-1], e, modulus) % modulus
            c = [v * inv % modulus for v in c]
        else:
            from math import gcd
            g = 0
            for v in c:
                g = gcd(g, v)
            if c[-1] < 0:
                g = -g
            unit *= g ** e
            c = [v // g for v in c]
        if len(c) > 1:
            rows.append([[str(v) for v in c], e])
        else:
            unit = unit * pow(c[0], e, modulus) % modulus if modulus else unit * c[0] ** e
    rows.sort(key=lambda r: (len(r[0]), [int(v) for v in reversed(r[0])], r[1]))
    return {'unit': str(unit % modulus if modulus else unit), 'factors': rows}


def canonical_multivariate(unit, factors):
    """`factors` holds ({exponents: coefficient}, multiplicity)."""
    from math import gcd
    unit = int(unit)
    rows = []
    for terms, e in factors:
        terms = {tuple(k): int(v) for k, v in terms.items() if int(v)}
        g = 0
        for v in terms.values():
            g = gcd(g, v)
        if terms[max(terms)] < 0:
            g = -g
        unit *= g ** e
        terms = {k: v // g for k, v in terms.items()}
        if len(terms) == 1 and not any(next(iter(terms))):
            unit *= next(iter(terms.values())) ** e
            continue
        rows.append([sorted([list(k), str(v)] for k, v in terms.items()), e])
    rows.sort(key=lambda r: json.dumps(r))
    return {'unit': str(unit), 'factors': rows}


def check_product(case, answer):
    """Multiply the canonical factors back with FLINT and compare with the input."""
    import flint
    if case['kind'] == 'mzz':
        ctx = flint.fmpz_mpoly_ctx.get(tuple(VARS[:case['nvars']]), 'lex')
        f = ctx.from_dict({(0,) * case['nvars']: int(answer['unit'])})
        for terms, e in answer['factors']:
            f *= ctx.from_dict({tuple(k): int(v) for k, v in terms}) ** e
        return f == ctx.from_dict({tuple(k): int(v) for k, v in case['poly']})
    if case['kind'] == 'gf':
        p = case['modulus']
        f = flint.nmod_poly([int(answer['unit'])], p)
        for c, e in answer['factors']:
            f *= flint.nmod_poly([int(v) for v in c], p) ** e
        return f == flint.nmod_poly([int(v) for v in case['poly']], p)
    f = flint.fmpz_poly([int(answer['unit'])])
    for c, e in answer['factors']:
        f *= flint.fmpz_poly([int(v) for v in c]) ** e
    return f == flint.fmpz_poly([int(v) for v in case['poly']])


# ------------------------------------------------------------------- tools

def env_python():
    return str(Path(os.environ.get('CONDA_PREFIX', '')) / 'bin' / 'python')


def git_revision():
    head = subprocess.run(['git', 'rev-parse', 'HEAD'], cwd=ROOT, capture_output=True, text=True).stdout.strip()
    dirty = subprocess.run(['git', 'status', '--porcelain', '--', 'src'], cwd=ROOT, capture_output=True, text=True).stdout.strip()
    return head[:12] + ('+dirty' if dirty else '')


def _read_dense_record(text):
    """The coefficients of a canonical `dense.dumps` record, degree 0 first."""
    lines = text.rstrip('\n').split('\n')
    assert lines[:2] == ['POLYNOMIALS 1', 'DENSE']
    count = int(lines[4])
    return lines[5:5 + count]


def _read_sparse_record(text, nvars):
    from .polys import read_record
    from fractions import Fraction
    poly = read_record(text, None)
    out = {}
    for e, c in poly.items():
        e = tuple(e) + (0,) * (nvars - len(e))
        out[e] = int(Fraction(c))
    return out


class PolyMojo:
    """The Poly Mojo factor driver; `binary` may point at any library build."""
    system = 'Poly Mojo'
    driver = HERE / 'drivers' / 'poly_mojo' / 'factor.mojo'

    def __init__(self, name='polymojo', mode='comparable', binary=None):
        self.name, self.mode, self._binary = name, mode, binary

    def version(self):
        return git_revision()

    def supports(self, case):
        return case['kind'] != 'mzz' or case['nvars'] in (2, 3, 4, 5, 6, 8)

    def binary(self):
        if self._binary:
            return Path(self._binary)
        manifest = ROOT / 'build' / 'library-build.json'
        key = hashlib.sha256(self.driver.read_bytes() + (manifest.read_bytes() if manifest.exists() else b'')).hexdigest()[:16]
        return CACHE / 'bin' / f'pm_factor_{key}'

    def build(self):
        out = self.binary()
        if out.is_file():
            return out
        from .tools import outside_environment
        out.parent.mkdir(parents=True, exist_ok=True)
        cmd = [os.environ.get('PIXI_EXE', 'pixi'), 'run', '--manifest-path', str(ROOT / 'pixi.toml'), '--locked', 'mojo', 'build',
               '-I', str(ROOT / 'build'), str(self.driver), '-o', str(out) + '.tmp']
        log = CACHE / 'logs' / f'{out.name}.build.log'
        log.parent.mkdir(parents=True, exist_ok=True)
        with open(log, 'w') as f:
            if subprocess.run(cmd, cwd=ROOT, env=outside_environment(), stdout=f, stderr=f).returncode:
                raise SystemExit(f'Poly Mojo driver build failed; see {log}')
        os.replace(str(out) + '.tmp', out)
        return out

    def prepare(self, case, work, settings):
        if case['kind'] == 'mzz':
            from .polys import record
            from fractions import Fraction
            poly = {tuple(e): Fraction(int(c)) for e, c in case['poly']}
            (work / 'input.txt').write_text(record(poly, case['nvars'], None).replace('\nQQ\n', '\nZZ\n', 1))
            kind = 'sparse'
        else:
            (work / 'input.txt').write_text('\n'.join([str(len(case['poly']))] + case['poly']) + '\n')
            kind = 'dense'
        cmd = [str(self.binary()), kind, 'input.txt', 'answer.txt', 'result.json', str(case['modulus']), self.mode,
               str(settings['min_seconds']), str(settings['min_reps']), str(case['nvars'])]
        return cmd

    def collect(self, case, work):
        result = json.loads((work / 'result.json').read_text())
        data = (work / 'answer.txt').read_bytes()
        pos = 0

        def line():
            nonlocal pos
            end = data.index(b'\n', pos)
            value = data[pos:end].decode()
            pos = end + 1
            return value

        unit, count, factors = line(), int(line()), []
        for _ in range(count):
            e, length = int(line()), int(line())
            text = data[pos:pos + length].decode()
            pos += length
            factors.append((_read_sparse_record(text, case['nvars']) if case['kind'] == 'mzz' else _read_dense_record(text), e))
        result['answer'] = (canonical_multivariate(unit, factors) if case['kind'] == 'mzz'
                            else canonical_univariate(unit, factors, case['modulus']))
        return result


class PythonTool:
    """FLINT (python-flint) and SymPy, timed in-process by drivers/python/factor_py.py."""

    def __init__(self, name, system, library):
        self.name, self.system, self.library = name, system, library

    def version(self):
        if self.library == 'flint':
            import flint
            return f'{flint.__version__} (FLINT {flint.__FLINT_VERSION__})'
        import sympy
        return f'{sympy.__version__} (gmpy ground types)'

    def supports(self, case):
        return True

    def prepare(self, case, work, settings):
        (work / 'case.json').write_text(json.dumps(case))
        return [env_python(), str(HERE / 'drivers' / 'python' / 'factor_py.py'), self.library, 'case.json',
                'answer.json', 'result.json', str(settings['min_seconds']), str(settings['min_reps'])]

    def collect(self, case, work):
        result = json.loads((work / 'result.json').read_text())
        raw = json.loads((work / 'answer.json').read_text())
        if case['kind'] == 'mzz':
            factors = [({tuple(k): v for k, v in terms}, e) for terms, e in raw['factors']]
            result['answer'] = canonical_multivariate(raw['unit'], factors)
        else:
            result['answer'] = canonical_univariate(raw['unit'], raw['factors'], case['modulus'])
        return result


SINGULAR_SCRIPT = '''\
system("--ticks-per-sec", 1000000);
ring r = {characteristic}, ({variables}), dp;
short = 0;
poly f = {poly};
int pid = system("pid");
int rc = system("sh", "grep VmRSS /proc/" + string(pid) + "/status > rss.txt; echo 5 > /proc/" + string(pid) + "/clear_refs");
int t0 = rtimer;
list L = factorize(f);
int t1 = rtimer;
rc = system("sh", "grep VmHWM /proc/" + string(pid) + "/status > hwm.txt");
int total = t1 - t0;
int reps = 1;
string times = string(total);
list H;
if (total < {min_us}) {{
  while ((reps < {min_reps}) or (total < {min_us})) {{
    t0 = rtimer;
    H = factorize(f);
    t1 = rtimer;
    total = total + (t1 - t0);
    reps = reps + 1;
    times = times + "," + string(t1 - t0);
  }}
}}
write(":w times.txt", times);
int i;
string out = "";
for (i = 1; i <= size(L[1]); i++) {{
  out = out + string(L[2][i]) + ":" + string(L[1][i]) + newline;
}}
write(":w answer.txt", out);
quit;
'''


def _infix(case):
    names = VARS[:case['nvars']]
    if case['kind'] == 'mzz':
        terms = [(e, int(c)) for e, c in case['poly']]
    else:
        terms = [((i,), int(c)) for i, c in enumerate(case['poly']) if int(c)]
    parts = []
    for e, c in terms:
        mono = '*'.join(f'{n}^{k}' for n, k in zip(names, e) if k)
        parts.append(f'({c})' + (f'*{mono}' if mono else ''))
    return '+'.join(parts) or '0'


class Singular:
    name = 'singular'
    system = 'Singular'

    def version(self):
        return '4.4.1'

    def supports(self, case):
        # Singular's prime fields stop below 2^31.
        return case['modulus'] < (1 << 31)

    def prepare(self, case, work, settings):
        script = SINGULAR_SCRIPT.format(characteristic=case['modulus'], variables=','.join(VARS[:case['nvars']]),
                                        poly=_infix(case), min_us=int(settings['min_seconds'] * 1e6),
                                        min_reps=settings['min_reps'])
        (work / 'run.sing').write_text(script)
        return ['Singular', '-q', '--no-warn', '--no-rc', 'run.sing']

    def collect(self, case, work):
        from .polys import parse
        kb = lambda name: int((work / name).read_text().split()[1])
        times = [int(t) * 1000 for t in (work / 'times.txt').read_text().strip().split(',')]
        names = VARS[:case['nvars']]
        unit, factors = 1, []
        for row in (work / 'answer.txt').read_text().split('\n'):
            if not row.strip():
                continue
            e, _, text = row.partition(':')
            poly = parse(text, names, case['modulus'] or None)
            poly = {k: int(v) for k, v in poly.items()}
            if case['kind'] == 'mzz':
                factors.append((poly, int(e)))
            else:
                coeffs = [0] * (max(k[0] for k in poly) + 1)
                for k, v in poly.items():
                    coeffs[k[0]] = v
                factors.append((coeffs, int(e)))
        answer = (canonical_multivariate(unit, factors) if case['kind'] == 'mzz'
                  else canonical_univariate(unit, factors, case['modulus']))
        return {'times_ns': times, 'rss_before_kb': kb('rss.txt'), 'peak_kb': kb('hwm.txt'), 'answer': answer}


TOOLS = {t.name: t for t in [
    PolyMojo(), PolyMojo('polymojo-certified', 'certified'),
    PythonTool('flint', 'FLINT', 'flint'), Singular(), PythonTool('sympy', 'SymPy', 'sympy'),
]}
DEFAULT_TOOLS = ['polymojo', 'flint', 'singular', 'sympy']


# ------------------------------------------------------------------ running

def run_one(tool, case, settings):
    work = Path(tempfile.mkdtemp(prefix='factor-', dir=settings['scratch']))
    try:
        cmd = tool.prepare(case, work, settings)
        env = os.environ.copy()
        if getattr(tool, 'library', None) == 'sympy':
            # SymPy delegates to python-flint when it is importable; the twin is pure SymPy.
            env['SYMPY_GROUND_TYPES'] = 'gmpy'
        process = measure.run(cmd, cwd=work, env=env, timeout_s=settings['timeout'],
                              memory_bytes=settings['memory'], cpu=settings['cpu'],
                              stdout=work / 'stdout.txt', stderr=work / 'stderr.txt')
        if process.timed_out:
            return {'outcome': 'timeout'}
        if process.oom:
            return {'outcome': 'out-of-memory'}
        if process.returncode != 0:
            tail = (work / 'stderr.txt').read_text(errors='replace')[-2000:] + (work / 'stdout.txt').read_text(errors='replace')[-1000:]
            return {'outcome': 'error', 'error': tail.strip()}
        result = tool.collect(case, work)
    except Exception:
        return {'outcome': 'error', 'error': traceback.format_exc()[-2000:]}
    finally:
        if not settings['keep']:
            shutil.rmtree(work, ignore_errors=True)
    times = result['times_ns']
    answer = result['answer']
    record = {'outcome': 'ok', 'time_s': statistics.median(times) / 1e9, 'time_min_s': min(times) / 1e9,
              'reps': len(times), 'peak_incremental_kib': result['peak_kb'] - result['rss_before_kb'],
              'factor_count': len(answer['factors']), 'answer_digest': digest(answer),
              'product_ok': check_product(case, answer)}
    if result.get('check_ns'):
        record['check_s'] = result['check_ns'] / 1e9
        record['check_ok'] = result['check_ok']
    if not record['product_ok'] or not result.get('check_ok', True):
        record['outcome'] = 'wrong'
    answers = settings['answers'] / case['id']
    answers.mkdir(parents=True, exist_ok=True)
    (answers / f'{tool.name}.json').write_text(json.dumps(answer))
    return record


def host_label():
    from .run import host_label as label
    return label()


def run(args):
    selected = [TOOLS[n] for n in (args.tools.split(',') if args.tools else DEFAULT_TOOLS)]
    if args.binary:
        for t in selected:
            if isinstance(t, PolyMojo):
                t._binary = args.binary
    all_cases = sorted((c for c in load() if re.search(args.cases, c['id'])), key=case_order)
    # An explicit --binary measures whatever build it was linked against.
    from . import tools
    libraries = {} if args.binary else tools.verify_poly_mojo(selected)
    for t in selected:
        if isinstance(t, PolyMojo):
            t.build()
    results = args.results or HERE / 'results' / (args.host or host_label()) / f'{datetime.date.today().isoformat()}-factor' / 'records.jsonl'
    results.parent.mkdir(parents=True, exist_ok=True)
    env_path = results.parent / 'environment.json'
    if not env_path.exists():
        from .run import environment
        env_path.write_text(json.dumps(environment(), indent=2) + '\n')
    tools.record_libraries(env_path, libraries)
    done = {}
    if results.exists():
        for line in results.read_text().splitlines():
            r = json.loads(line)
            done[(r['case'], r['tool'])] = r
    done = {k: r for k, r in done.items() if not (r['outcome'] in ('timeout', 'skipped') and r['timeout_s'] < args.timeout)}
    settings = {'timeout': args.timeout, 'memory': args.memory, 'cpu': args.cpu, 'min_seconds': args.min_seconds,
                'min_reps': args.min_reps, 'keep': args.keep, 'scratch': CACHE / 'work',
                'answers': CACHE / 'answers' / results.parent.name}
    settings['scratch'].mkdir(parents=True, exist_ok=True)
    stopped = {(r['tool'], r['ladder']) for r in done.values() if r['outcome'] in ('timeout', 'out-of-memory')}
    with open(results, 'a') as out:
        for case in all_cases:
            for tool in selected:
                if (case['id'], tool.name) in done:
                    continue
                base = {'case': case['id'], 'family': 'factor', 'kind': case['kind'], 'ladder': case['ladder'],
                        'size': case['size'], 'modulus': case['modulus'], 'nvars': case['nvars'],
                        'tool': tool.name, 'library': tool.system, 'version': tool.version(), 'timeout_s': args.timeout,
                        'started': datetime.datetime.now(datetime.timezone.utc).isoformat(timespec='seconds')}
                if not tool.supports(case):
                    record = {'outcome': 'unsupported'}
                elif (tool.name, case['ladder']) in stopped:
                    record = {'outcome': 'skipped', 'reason': 'a smaller instance on this ladder hit a limit'}
                else:
                    record = run_one(tool, case, settings)
                    if record['outcome'] in ('timeout', 'out-of-memory'):
                        stopped.add((tool.name, case['ladder']))
                record = base | record
                out.write(json.dumps(record) + '\n')
                out.flush()
                summary = f"{record['outcome']:>13}"
                if record['outcome'] == 'ok':
                    summary += f"  {record['time_s']:10.4f} s  {record['factor_count']:4d} factors"
                print(f"{case['id']:<30} {tool.name:<20} {summary}", flush=True)


# ------------------------------------------------------------------ report

def _fmt(r):
    if r is None:
        return ''
    if r['outcome'] != 'ok':
        return r['outcome']
    t = r['time_s']
    return f'{t * 1e3:.2f} ms' if t < 1 else f'{t:.2f} s'


def report(folder):
    records = {}
    for line in (folder / 'records.jsonl').read_text().splitlines():
        r = json.loads(line)
        records[(r['case'], r['tool'])] = r
    tools = [t for t in TOOLS if any(k[1] == t for k in records)]
    cases = sorted({k[0] for k in records}, key=lambda c: next(case_order(x) for x in load() if x['id'] == c))
    lines = ['# Factorization', '', f'Records: `{folder.name}`. Times are medians of in-process repetitions on one pinned core. '
             'Ratio is the other tool\'s time over Poly Mojo\'s (above 1: Poly Mojo is faster). '
             '"agree" means every tool that finished returned the same normalized factor multiset and its product equals the input.', '']
    others = [t for t in tools if t != 'polymojo' and t != 'polymojo-certified']
    header = ['case'] + tools + [f'{t} ratio' for t in others] + ['agree']
    lines += ['| ' + ' | '.join(header) + ' |', '|' + '---|' * len(header)]
    for c in cases:
        row = [records.get((c, t)) for t in tools]
        pm = records.get((c, 'polymojo'))
        ratios = []
        for t in others:
            r = records.get((c, t))
            if pm and r and pm['outcome'] == 'ok' and r['outcome'] == 'ok':
                ratios.append(f"{r['time_s'] / pm['time_s']:.3g}")
            else:
                ratios.append('')
        digests = {r['answer_digest'] for r in row if r and r['outcome'] == 'ok'}
        wrong = any(r and r['outcome'] == 'wrong' for r in row)
        agree = 'no' if wrong or len(digests) > 1 else ('yes' if digests else '')
        lines.append('| ' + ' | '.join([c] + [_fmt(r) for r in row] + ratios + [agree]) + ' |')
    text = '\n'.join(lines) + '\n'
    (folder / 'report.md').write_text(text)
    return text


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = parser.add_subparsers(dest='command', required=True)
    sub.add_parser('generate')
    r = sub.add_parser('run')
    r.add_argument('--tools')
    r.add_argument('--cases', default='')
    r.add_argument('--binary', help='Use this Poly Mojo factor driver binary instead of building one')
    r.add_argument('--results', type=Path)
    r.add_argument('--host')
    r.add_argument('--timeout', type=float, default=300)
    r.add_argument('--memory', type=int, default=12 << 30)
    r.add_argument('--cpu', type=int, default=(os.cpu_count() or 1) - 1)
    r.add_argument('--min-seconds', type=float, default=0.5)
    r.add_argument('--min-reps', type=int, default=3)
    r.add_argument('--keep', action='store_true')
    p = sub.add_parser('report')
    p.add_argument('folder', type=Path, nargs='?')
    args = parser.parse_args(argv)
    if args.command == 'generate':
        print(f'factor: {len(generate())} cases')
    elif args.command == 'run':
        run(args)
    else:
        folder = args.folder or max((HERE / 'results').glob('*/*-factor'), key=lambda p: p.name)
        print(report(folder))
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
