"""Gcd, resultant, and discriminant cases and the adapters that run them.

Families (README, "Univariate gcd and resultants" and the gcd and resultant
half of "Multivariate factorization and gcd"):

- `ugcd.zz.<bits>`, `ugcd.gf`: random dense f = g·a and h = g·b with a planted
  gcd g of half the degree, degree 50 … 2000, 32- to 512-bit coefficients
  over ZZ, and over GF(65521).
- `ures.*`, `udisc.*`: resultants of random dense pairs and discriminants of
  the first polynomial of each pair, degree 10 … 200.
- `mgcd.fateman-f1|f2|f3`: SymPy's Fateman–Liao gcd families, n = 2 … 8.
- `mgcd.dense`: f = A^k B^k and h = A^k C^k with A = 1 + x + y + z,
  B = 2 + x + y + z, C = 3 + x + y + z, k = 5 … 15.
- `mgcd.sparse`: f = g·a, h = g·b with random sparse factors in 3 … 8 variables.
- `mres.<n>v`: the resultant eliminating x0 from random pairs in 2 and 3
  variables of total degree 2 … 10.

Canonical answers: a gcd over ZZ has a positive leading coefficient in lex
order and keeps the integer content gcd(cont f, cont h); a gcd over GF(p) is
monic. Resultants and discriminants are exact values, so they need no
normalization. Singular's characteristic-zero gcd works over QQ, so its
answer is made primitive and multiplied by the content gcd before comparison.
"""
from fractions import Fraction
import hashlib
import json
from math import gcd as igcd
import os
from pathlib import Path
import random

from . import measure
from .polys import make, order_key, scalar_text, format_infix, parse, read_records
from .tools import CACHE, HERE, ROOT, Tool, env_python, git_revision, outside_environment

PRIME = 65521
FAMILY = 'gcd'


# ------------------------------------------------------------------ cases

def poly_mul(p, q, field):
    out = {}
    for e, a in p.items():
        for f, b in q.items():
            k = tuple(x + y for x, y in zip(e, f))
            out[k] = out.get(k, 0) + a * b
    return make(out.items(), field)


def poly_pow(p, k, field):
    result = {tuple(0 for _ in next(iter(p))): 1}
    for _ in range(k):
        result = poly_mul(result, p, field)
    return result


def dense_univariate(rng, degree, bits, field):
    """A random dense polynomial with a nonzero leading coefficient."""
    while True:
        if field is None:
            c = [rng.randint(-(1 << bits) + 1, (1 << bits) - 1) for _ in range(degree + 1)]
        else:
            c = [rng.randrange(field) for _ in range(degree + 1)]
        if c[-1]:
            return make([((i,), v) for i, v in enumerate(c)], field)


def random_sparse(rng, nvars, terms, degree, field, bits=8):
    """A random polynomial with `terms` distinct monomials of total degree ≤ degree, and a constant term."""
    monomials = {(0,) * nvars}
    while len(monomials) < terms:
        total = rng.randint(1, degree)
        e = [0] * nvars
        for _ in range(total):
            e[rng.randrange(nvars)] += 1
        monomials.add(tuple(e))
    out = []
    for e in sorted(monomials):
        c = 0
        while not c:
            c = rng.randint(-(1 << bits), 1 << bits)
        out.append((e, c))
    return make(out, field)


def random_dense_total(rng, nvars, degree, field, bits=4):
    """A random dense polynomial of total degree `degree` with small coefficients."""
    out = []

    def walk(prefix, left):
        if len(prefix) == nvars:
            out.append((tuple(prefix), rng.randint(-(1 << bits), 1 << bits)))
            return
        for e in range(left + 1):
            walk(prefix + [e], left - e)
    walk([], degree)
    p = make(out, field)
    top = tuple([0] * (nvars - 1) + [degree]) if nvars > 1 else (degree,)
    lead = tuple([degree] + [0] * (nvars - 1))
    for e in (top, lead):
        if e not in p:
            p[e] = 1
    return p


def to_json(p, field):
    return [[list(e), scalar_text(c, field)] for e, c in sorted(p.items(), reverse=True)]


def case(ident, ladder, system, size, field, nvars, operation, polys, source, expected=None):
    c = {
        'id': ident, 'family': FAMILY, 'ladder': ladder, 'system': system, 'size': size,
        'field': field, 'order': 'lex', 'operation': operation,
        'variables': [f'x{i}' for i in range(nvars)],
        'generators': [to_json(p, field) for p in polys],
        'source': source,
    }
    if expected is not None:
        c['expected'] = to_json(expected, field)
    return c


UGCD_DEGREES = [50, 100, 200, 500, 1000, 2000]
URES_DEGREES = [10, 20, 50, 100, 200]


def univariate_cases():
    for bits in (32, 128, 512):
        for n in UGCD_DEGREES:
            rng = random.Random(f'ugcd-zz-{bits}-{n}')
            half = n // 2
            g, a, b = (dense_univariate(rng, half, bits, None) for _ in range(3))
            yield case(f'ugcd-zz{bits}-{n}', f'ugcd.zz.{bits}', 'planted gcd', n, None, 1, 'gcd',
                       [poly_mul(g, a, None), poly_mul(g, b, None)], f'f = g·a, h = g·b, deg g = {half}, {bits}-bit')
    for n in UGCD_DEGREES:
        rng = random.Random(f'ugcd-gf-{n}')
        half = n // 2
        g, a, b = (dense_univariate(rng, half, 0, PRIME) for _ in range(3))
        yield case(f'ugcd-gf-{n}', 'ugcd.gf', 'planted gcd', n, PRIME, 1, 'gcd',
                   [poly_mul(g, a, PRIME), poly_mul(g, b, PRIME)], f'f = g·a, h = g·b over GF({PRIME})')
    for field, label, bits in ((None, 'zz', 32), (PRIME, 'gf', 0)):
        for n in URES_DEGREES:
            rng = random.Random(f'ures-{label}-{n}')
            f, h = dense_univariate(rng, n, bits, field), dense_univariate(rng, n, bits, field)
            yield case(f'ures-{label}-{n}', f'ures.{label}', 'random pair', n, field, 1, 'resultant', [f, h],
                       f'random dense pair of degree {n}')
            yield case(f'udisc-{label}-{n}', f'udisc.{label}', 'random', n, field, 1, 'discriminant', [f],
                       f'random dense polynomial of degree {n}')


def fateman_cases():
    from sympy import Poly
    from sympy.polys.specialpolys import fateman_poly_F_1, fateman_poly_F_2, fateman_poly_F_3
    sizes = {1: range(2, 9), 2: range(2, 9), 3: range(2, 9)}
    for which, build in ((1, fateman_poly_F_1), (2, fateman_poly_F_2), (3, fateman_poly_F_3)):
        for n in sizes[which]:
            f, h, g = build(n)
            gens = sorted(f.free_symbols | h.free_symbols, key=lambda s: (len(s.name), s.name))
            polys = [make(Poly(p, *gens).terms(), None) for p in (f, h, g)]
            yield case(f'mgcd-f{which}-{n}', f'mgcd.fateman-f{which}', f'fateman_poly_F_{which}', n, None, len(gens), 'gcd',
                       polys[:2], f'sympy.polys.specialpolys.fateman_poly_F_{which}({n})', expected=polys[2])


def multivariate_cases():
    yield from fateman_cases()
    one = lambda c: {(0, 0, 0): c, (1, 0, 0): 1, (0, 1, 0): 1, (0, 0, 1): 1}
    for k in range(5, 16, 2):
        a, b, c = (poly_pow(one(v), k, None) for v in (1, 2, 3))
        yield case(f'mgcd-dense-{k}', 'mgcd.dense', 'dense products', k, None, 3, 'gcd',
                   [poly_mul(a, b, None), poly_mul(a, c, None)], f'A^k B^k and A^k C^k, A = 1+x+y+z, k = {k}', expected=a)
    for n in (3, 4, 5, 6, 7, 8):
        rng = random.Random(f'mgcd-sparse-{n}')
        g, a, b = (random_sparse(rng, n, 20, 6, None) for _ in range(3))
        yield case(f'mgcd-sparse-{n}', 'mgcd.sparse', 'sparse products', n, None, n, 'gcd',
                   [poly_mul(g, a, None), poly_mul(g, b, None)], f'20-term factors in {n} variables, total degree ≤ 6')
    for nvars in (2, 3):
        for d in (2, 4, 6, 8, 10):
            rng = random.Random(f'mres-{nvars}-{d}')
            f, h = random_dense_total(rng, nvars, d, None), random_dense_total(rng, nvars, d, None)
            yield case(f'mres-{nvars}v-{d}', f'mres.{nvars}v', 'random pair', d, None, nvars, 'resultant', [f, h],
                       f'eliminate x0 from a random dense pair of total degree {d}')


def gcd_cases():
    yield from univariate_cases()
    yield from multivariate_cases()


def polynomials(c):
    field = c['field']
    return [make([(e, Fraction(v)) for e, v in p], field) for p in c['generators']]


# --------------------------------------------------------------- answers

def content(p):
    g = 0
    for v in p.values():
        g = igcd(g, int(v))
    return g


def leading(p):
    return p[max(p)]


def canonical(c, p):
    """Rows of the normalized answer: see the module docstring."""
    field = c['field']
    p = {tuple(e): v for e, v in p.items() if v}
    if c['operation'] == 'gcd' and p:
        if field is None:
            p = {e: Fraction(v) for e, v in p.items()}
            if leading(p) < 0:
                p = {e: -v for e, v in p.items()}
        else:
            inv = pow(int(leading(p)), -1, field)
            p = {e: (int(v) * inv) % field for e, v in p.items()}
    return sorted([list(e), scalar_text(v, field)] for e, v in p.items())


def integer_gcd_from_field(c, p):
    """Turn a QQ gcd into the ZZ gcd: primitive, positive, times gcd(cont f, cont h)."""
    if not p:
        return p
    f, h = polynomials(c)[:2]
    scale = 1
    for v in p.values():
        scale = scale * Fraction(v).denominator // igcd(scale, Fraction(v).denominator)
    q = {e: Fraction(v) * scale for e, v in p.items()}
    cont = content(q)
    common = igcd(content(f), content(h))
    sign = -1 if leading(q) < 0 else 1
    return {e: v / cont * common * sign for e, v in q.items()}


def discriminant_divisor(c):
    """(-1)^(n(n-1)/2) lc(f): the resultant of f and f' divided by it is the discriminant."""
    f = polynomials(c)[0]
    n = max(e[0] for e in f)
    lc = sum(v for e, v in f.items() if e[0] == n and not any(e[1:]))
    if any(e[0] == n and any(e[1:]) for e in f):
        raise ValueError('discriminant cases are univariate')
    sign = -1 if (n * (n - 1) // 2) % 2 else 1
    return make([((0,) * len(c['variables']), sign * lc)], c['field'])


def record(poly, nvars, field):
    domain = 'ZZ' if field is None else f'Fp:{field}'
    lines = ['POLYNOMIALS 1', 'SPARSE', domain, '1', str(nvars), *map(str, range(nvars)), str(len(poly))]
    for exps in sorted(poly):
        pairs = [(i, e) for i, e in enumerate(exps) if e]
        lines.append(str(len(pairs)))
        for i, e in pairs:
            lines += [str(i), str(e)]
        lines.append(scalar_text(poly[exps], field))
    return '\n'.join(lines) + '\n'


def write_records(polys, nvars, field):
    out = [f'{len(polys)}\n']
    for p in polys:
        r = record(p, nvars, field)
        out.append(f'{len(r.encode())}\n{r}')
    return ''.join(out)


# ---------------------------------------------------------------- tools

class GcdTool(Tool):
    def supports(self, c):
        return c['family'] == FAMILY

    def finish(self, c, result, poly):
        result['answer'] = canonical(c, poly)
        return result


class PolyMojoGcd(GcdTool):
    system = 'Poly Mojo'
    driver = HERE / 'drivers' / 'poly_mojo' / 'gcd.mojo'

    def __init__(self, method='auto', certified=False):
        self.method = method
        self.certified = certified
        self.check_allowance = 600.0 if certified else 0.0
        self.name = 'polymojo' if method == 'auto' else f'polymojo-{method}'
        if certified:
            self.name += '-certified'
        self.algorithm = {'auto': 'default dispatch', 'modular': 'sparse modular (exact reconstruction)'}[method]

    def supports(self, c):
        if c['family'] != FAMILY:
            return False
        # The modular method covers multivariate integer gcds only.
        return self.method == 'auto' or (c['operation'] == 'gcd' and c['field'] is None and len(c['variables']) > 1)

    def version(self):
        return git_revision()

    def library(self):
        return Path(os.environ.get('POLY_MOJO_LIB', ROOT / 'build'))

    def binary(self, nvars, modular):
        lib = self.library()
        manifest = (lib / 'library-build.json').read_bytes() if (lib / 'library-build.json').is_file() else \
            b''.join((lib / f).read_bytes()[:1 << 20] for f in ('polynomials.mojoc', 'poly.mojoc'))
        key = hashlib.sha256(self.driver.read_bytes() + manifest + f'{nvars}:{modular}'.encode()).hexdigest()[:16]
        return CACHE / 'bin' / f"pm_gcd_{nvars}_{'gf' if modular else 'zz'}_{key}"

    def build(self, nvars, modular):
        out = self.binary(nvars, modular)
        if out.is_file():
            return out, 0.0, None
        out.parent.mkdir(parents=True, exist_ok=True)
        cmd = [os.environ.get('PIXI_EXE', 'pixi'), 'run', '--manifest-path', str(ROOT / 'pixi.toml'), '--locked', 'mojo', 'build',
               '-I', str(self.library()), '-D', f'NVARS={nvars}', '-D', f'DOMAIN={int(modular)}',
               str(self.driver), '-o', str(out) + '.tmp']
        log = CACHE / 'logs' / f'{out.name}.build.log'
        log.parent.mkdir(parents=True, exist_ok=True)
        result = measure.run(cmd, cwd=ROOT, env=outside_environment(), timeout_s=3600, memory_bytes=None,
                             cpu=None, stdout=log, stderr=log)
        if result.returncode != 0:
            raise SystemExit(f'Poly Mojo driver build failed; see {log}')
        os.replace(str(out) + '.tmp', out)
        return out, result.wall_s, result.maxrss_kb

    def builds(self, cases):
        return sorted({(len(c['variables']), c['field'] is not None) for c in cases if self.supports(c)})

    def prepare(self, c, work, settings):
        field, nvars = c['field'], len(c['variables'])
        polys = polynomials(c)
        if c['operation'] == 'discriminant':
            polys = [polys[0], polys[0], discriminant_divisor(c)]
        (work / 'input.txt').write_text(write_records(polys, nvars, field))
        cmd = [str(self.binary(nvars, field is not None)), 'input.txt', 'answer.txt', 'result.json', c['operation'],
               self.method + ('-certified' if self.certified else ''), '0', str(field or 0), str(settings['min_seconds']), str(settings['min_reps'])]
        return cmd, os.environ.copy()

    def collect(self, c, work):
        result = json.loads((work / 'result.json').read_text())
        poly = read_records((work / 'answer.txt').read_bytes(), c['field'])[0]
        return self.finish(c, result, poly)


class PythonGcd(GcdTool):
    """FLINT through python-flint, or SymPy, in one Python driver."""
    in_process = True

    def __init__(self, engine, ground_types='gmpy'):
        self.engine, self.ground_types = engine, ground_types
        if engine == 'flint':
            self.name, self.system = 'flint', 'FLINT'
            self.algorithm = 'fmpz_poly / nmod_poly / fmpz_mpoly'
        else:
            self.name = 'sympy' + ('' if ground_types == 'gmpy' else f'-{ground_types}')
            self.system = 'SymPy'
            self.algorithm = 'Poly (heugcd, subresultants)'

    def version(self):
        if self.engine == 'flint':
            import flint
            return f'python-flint {flint.__version__}'
        import sympy
        return f'{sympy.__version__} ({self.ground_types} ground types)'

    def prepare(self, c, work, settings):
        (work / 'case.json').write_text(json.dumps(c))
        env = os.environ.copy()
        env['SYMPY_GROUND_TYPES'] = self.ground_types
        cmd = [env_python(), str(HERE / 'drivers' / 'python' / 'gcd.py'), self.engine, 'case.json', 'answer.json',
               'result.json', str(settings['min_seconds']), str(settings['min_reps'])]
        return cmd, env

    def collect(self, c, work):
        result = json.loads((work / 'result.json').read_text())
        terms = json.loads((work / 'answer.json').read_text())
        poly = make([(e, Fraction(v)) for e, v in terms], c['field'])
        return self.finish(c, result, poly)


SINGULAR_SCRIPT = '''\
system("--ticks-per-sec", 1000000);
{lib}
ring r = {characteristic}, ({variables}), lp;
short = 0;
poly f = {f};
poly h = {h};
int pid = system("pid");
int rc = system("sh", "grep VmRSS /proc/" + string(pid) + "/status > rss.txt; echo 5 > /proc/" + string(pid) + "/clear_refs");
int t0 = rtimer;
poly G = {call};
int t1 = rtimer;
rc = system("sh", "grep VmHWM /proc/" + string(pid) + "/status > hwm.txt");
int total = t1 - t0;
int reps = 1;
string times = string(total);
poly H;
if (total < {min_us}) {{
  while ((reps < {min_reps}) or (total < {min_us})) {{
    t0 = rtimer;
    H = {call};
    t1 = rtimer;
    total = total + (t1 - t0);
    reps = reps + 1;
    times = times + "," + string(t1 - t0);
  }}
}}
write(":w times.txt", times);
write(":w answer.txt", G);
quit;
'''


class SingularGcd(GcdTool):
    name = 'singular'
    system = 'Singular'
    algorithm = 'factory gcd / resultant'

    def version(self):
        return '4.4.1'

    def prepare(self, c, work, settings):
        variables, field = c['variables'], c['field']
        polys = polynomials(c)
        f = polys[0]
        h = polys[1] if len(polys) > 1 else polys[0]
        call = {'gcd': 'gcd(f, h)', 'resultant': f'resultant(f, h, {variables[0]})'}.get(c['operation'])
        if c['operation'] == 'discriminant':
            # poly.lib's discr is not on Singular's default path here; this is its definition.
            divisor = format_infix(discriminant_divisor(c), variables, field)
            call = f'resultant(f, diff(f, {variables[0]}), {variables[0]}) / ({divisor})'
        script = SINGULAR_SCRIPT.format(
            lib='',
            characteristic=field or 0, variables=','.join(variables),
            f=format_infix(f, variables, field, 'lex'), h=format_infix(h, variables, field, 'lex'),
            call=call, min_us=int(settings['min_seconds'] * 1e6), min_reps=settings['min_reps'])
        (work / 'run.sing').write_text(script)
        return ['Singular', '-q', '--no-warn', '--no-rc', 'run.sing'], os.environ.copy()

    def collect(self, c, work):
        kb = lambda name: int((work / name).read_text().split()[1])
        times = [int(t) * 1000 for t in (work / 'times.txt').read_text().strip().split(',')]
        poly = parse((work / 'answer.txt').read_text().strip(), c['variables'], c['field'])
        if c['operation'] == 'gcd' and c['field'] is None:
            poly = integer_gcd_from_field(c, poly)
        return self.finish(c, {'times_ns': times, 'rss_before_kb': kb('rss.txt'), 'peak_kb': kb('hwm.txt')}, poly)


TOOLS = {t.name: t for t in [
    PolyMojoGcd(), PolyMojoGcd('modular'), PolyMojoGcd(certified=True), PolyMojoGcd('modular', certified=True),
    PythonGcd('flint'), PythonGcd('sympy'), PythonGcd('sympy', 'flint'),
    SingularGcd(),
]}
FAMILY_TOOLS = ['polymojo', 'polymojo-modular', 'polymojo-certified', 'polymojo-modular-certified', 'flint', 'singular', 'sympy']


# ---------------------------------------------------------------- report

LABEL = {'polymojo': 'Poly Mojo (no certificate)', 'polymojo-modular': 'Poly Mojo modular (no certificate)',
         'polymojo-certified': 'Poly Mojo (certificate)', 'polymojo-modular-certified': 'Poly Mojo modular (certificate)', 'flint': 'FLINT',
         'singular': 'Singular', 'sympy': 'SymPy', 'sympy-flint': 'SymPy (flint types)'}


def report(records, env, folder):
    """Per-ladder tables of time and memory, and geometric-mean ratios against Poly Mojo."""
    from collections import defaultdict
    from .report import cell, geomean, RATIO_FLOOR_S, memory_limit
    from .proofs import table as proof_table
    present = {r['tool'] for r in records}
    order = [t for t in LABEL if t in present]
    by_ladder = defaultdict(dict)
    for r in records:
        by_ladder[r['ladder']].setdefault((r['size'], r['case']), {})[r['tool']] = r
    lines = ['# Gcd, resultant, and discriminant results', '',
             f"Host: {env['cpu']}, {env['cpus']} vCPUs. One pinned CPU per run, "
             f"{records[0]['timeout_s']:.0f} s per run. " + memory_limit(records), '',
             'Versions: ' + '; '.join(f'{LABEL[t]} {TOOLS[t].version()}' for t in order) + '.', '',
             'Cells give the median time and incremental peak memory; ✗ marks an answer that disagrees with a '
             'confirmed one, ? an answer no other library produced. Ratios are competitor time ÷ Poly Mojo time '
             f'(above 1: Poly Mojo faster) over cases both solved with a confirmed answer and at least '
             f'{RATIO_FLOOR_S * 1000:.0f} ms for the slower tool.', '',
             'Peer ratios use the value-only API, without retained certificates. GCD certificates establish maximality; '
             'resultant certificates establish the cofactor identity. Discriminants use a checked resultant followed by exact division.', '',
             '## Summary', '', '| Ladder | ' + ' | '.join(LABEL[t] for t in order if t != 'polymojo') + ' |',
             '|---|' + '---|' * (len(order) - 1)]
    for ladder in sorted(by_ladder):
        cells = []
        for t in order:
            if t == 'polymojo':
                continue
            values = []
            for row in by_ladder[ladder].values():
                a, b = row.get(t), row.get('polymojo')
                if a and b and a['outcome'] == b['outcome'] == 'ok' and a.get('agreement') == b.get('agreement') == 'confirmed' \
                        and max(a['time_s'], b['time_s']) >= RATIO_FLOOR_S:
                    values.append(max(a['time_s'], 1e-4) / max(b['time_s'], 1e-4))
            g = geomean(values)
            cells.append(f'{g:.3g} ({len(values)})' if g else '')
        lines.append(f'| {ladder} | ' + ' | '.join(cells) + ' |')
    lines += ['', '## Certificate overhead', '', *proof_table(records, [('polymojo', 'polymojo-certified'), ('polymojo-modular', 'polymojo-modular-certified')])]
    for ladder in sorted(by_ladder):
        lines += ['', f'## {ladder}', '', '| Size | ' + ' | '.join(LABEL[t] for t in order) + ' |',
                  '|---|' + '---|' * len(order)]
        for (size, case), row in sorted(by_ladder[ladder].items()):
            lines.append(f'| {size} | ' + ' | '.join(cell(row.get(t)) for t in order) + ' |')
    (folder / 'report.md').write_text('\n'.join(lines) + '\n')
    return folder / 'report.md'
