"""Cylindrical algebraic decomposition and real sign conditions.

Cases, tool adapters, independent answer checks and the report for the CAD
family of benchmarks/README.md. Run from benchmarks/:

    python -m harness.cad generate
    python -m harness.cad run [--tools a,b] [--cases REGEX] [--timeout S]
    python -m harness.cad report RESULTS_DIR

Full decompositions: Poly Mojo `cad.decompose` (Lazard and McCallum) and
`cad.decompose_to` into `cad.checker`; QEPCAD B with `full-cad`. Conjunctions:
Poly Mojo `cad.solve`; Z3 (nlsat); QEPCAD B on the existential closure.
QEPCAD B comes from a Tarski build (github.com/chriswestbrown/tarski) named by
$QEPCAD_HOME (the qesource folder); Z3 is the `z3` Python module of the
interpreter named by $Z3_PYTHON. A missing tool reports `unsupported`.

Checks: satisfiable or unsatisfiable must agree across tools. A satisfying
point is substituted exactly and every sign is checked here, independently of
the tool. For full decompositions every Poly Mojo terminal sample point is
sign-checked here as well (claimed zeros exactly through minimal polynomials),
in addition to `cad.check`. Cell and projection-factor counts depend on the
projection operator and are reported, not compared.
"""
import argparse
import datetime
from fractions import Fraction
import hashlib
import itertools
import json
import os
from pathlib import Path
import random
import re
import shutil
import statistics
import subprocess
import tempfile
import time
import traceback

from . import measure
from .polys import make, write_records

HERE = Path(__file__).resolve().parent.parent
ROOT = HERE.parent
CACHE = HERE / '.cache'
CASES = HERE / 'cases' / 'cad'
BANK = Path(__file__).resolve().parent / 'data' / 'cad_example_bank_qepcad.txt'
DRIVER = HERE / 'drivers' / 'poly_mojo' / 'cad.mojo'

# ------------------------------------------------------------------ polynomials
# A polynomial is a dict {exponent tuple: Fraction}; axis 0 is the CAD base.


def poly_from_sympy(expr, symbols):
    import sympy
    p = sympy.Poly(sympy.expand(expr), *symbols, domain='QQ')
    return make([(e, Fraction(int(c.p), int(c.q))) for e, c in p.terms()], None)


def primitive(poly):
    """Scale to coprime integer coefficients with a positive leading term (sign-invariance is kept)."""
    from math import gcd, lcm
    den = 1
    for c in poly.values():
        den = lcm(den, c.denominator)
    ints = {e: int(c * den) for e, c in poly.items()}
    g = 0
    for c in ints.values():
        g = gcd(g, c)
    lead = ints[max(ints)]
    s = -1 if lead < 0 else 1
    return {e: Fraction(s * c // g) for e, c in ints.items()}


def infix(poly, names, power='^', times=' '):
    """Integer-coefficient infix text (QEPCAD and SMT-friendly)."""
    terms = []
    for e in sorted(poly, reverse=True):
        c = poly[e]
        assert c.denominator == 1
        c = int(c)
        mono = [f'{names[i]}{power}{k}' if k > 1 else names[i] for i, k in enumerate(e) if k]
        sign = '-' if c < 0 else '+'
        a = abs(c)
        body = times.join(([str(a)] if a != 1 or not mono else []) + mono)
        terms.append((sign, body))
    text = ''
    for i, (sign, body) in enumerate(terms):
        text += (('- ' if sign == '-' else '') if i == 0 else f' {sign} ') + body
    return text or '0'


def evaluate_rational(poly, point):
    total = Fraction(0)
    for e, c in poly.items():
        term = c
        for x, k in zip(point, e):
            if k:
                term *= x ** k
        total += term
    return total


# ------------------------------------------------------------------ cases

ATOM = re.compile(r'\[([^\[\]]*?)(<=|>=|/=|=|<|>)([^\[\]]*?)\]')
MASK = {'<': 1, '=': 2, '>': 4, '<=': 3, '>=': 6, '/=': 5}


def parse_bank():
    """Examples of the CAD example bank: (title, variables, free count, atoms, formula)."""
    import sympy
    from sympy.parsing.sympy_parser import parse_expr, standard_transformations, implicit_multiplication_application
    transforms = standard_transformations + (implicit_multiplication_application,)
    text = BANK.read_text()
    examples = []
    for block in re.finditer(r'^\[([^\]\n]+)\]\s*\n\(([^)]*)\)\s*\n(\d+)\s*\n(.*?)\.\s*$', text, re.M | re.S):
        title, names, free, formula = block[1].strip(), [v.strip() for v in block[2].split(',')], int(block[3]), ' '.join(block[4].split())
        symbols = sympy.symbols(names)
        local = dict(zip(names, symbols))
        atoms = []
        for m in ATOM.finditer(formula):
            lhs, op, rhs = (s.strip().replace('^', '**') for s in m.groups())
            expr = parse_expr(lhs, local_dict=local, transformations=transforms) - parse_expr(rhs, local_dict=local, transformations=transforms)
            atoms.append((poly_from_sympy(expr, symbols), op))
        examples.append({'title': title, 'variables': names, 'free': free, 'atoms': atoms, 'formula': formula})
    return examples


def slug(text):
    return re.sub(r'[^a-z0-9]+', '-', text.lower()).strip('-')


def distinct_polys(polys):
    seen, result = set(), []
    for p in polys:
        if all(sum(e) == 0 for e in p):
            continue
        p = primitive(p)
        key = tuple(sorted(p.items()))
        if key not in seen:
            seen.add(key)
            result.append(p)
    return result


def dense_random(n, d, rng):
    """All monomials of total degree <= d with coefficients in [-9, 9]."""
    terms = []
    for e in itertools.product(range(d + 1), repeat=n):
        if sum(e) <= d:
            terms.append((e, rng.randint(-9, 9)))
    lead = tuple(d if i == n - 1 else 0 for i in range(n))
    terms.append((lead, rng.choice([1, 2, 3])))  # keep the top degree in the main variable
    return make(terms, None)


def sphere(n):
    return make([(tuple(2 if j == i else 0 for j in range(n)), 1) for i in range(n)] + [((0,) * n, -1)], None)


def hyperplane(n, rng):
    nonzero = [c for c in range(-5, 6) if c]
    return make([(tuple(1 if j == i else 0 for j in range(n)), rng.choice(nonzero)) for i in range(n)] + [((0,) * n, rng.randint(-3, 3))], None)


def case(kind, system, size, ladder, names, polys, source, masks=None, expect=None):
    polys = [primitive(p) for p in polys]
    return {'id': f'{kind}-{system}', 'family': 'cad', 'kind': kind, 'system': system, 'size': size,
            'ladder': ladder, 'variables': names, 'masks': masks, 'expect': expect, 'source': source,
            'polys': [[[list(e), str(c)] for e, c in sorted(p.items())] for p in polys]}


def full_cases():
    for ex in parse_bank():
        n = len(ex['variables'])
        if not 2 <= n <= 5:
            continue
        polys = distinct_polys([p for p, _ in ex['atoms']])
        yield case('full', 'bank-' + slug(ex['title']), n, 'bank', ex['variables'], polys,
                   f"CAD example bank (Wilson 2012): {ex['title']}; all atom polynomials, all variables free")
    random_sizes = [(2, k, d) for d in (2, 3, 4, 6, 8, 10) for k in (1, 2, 3, 4)] + \
                   [(3, k, d) for d in (2, 3, 4) for k in (1, 2, 3)] + [(4, k, 2) for k in (1, 2, 3)]
    for n, k, d in random_sizes:
        rng = random.Random(f'cad-dense-{n}-{k}-{d}')
        polys = [dense_random(n, d, rng) for _ in range(k)]
        yield case('full', f'dense-n{n}-k{k}-d{d}', d * 10 + k, f'dense-n{n}-k{k}', [f'x{i}' for i in range(n)], polys,
                   f'{k} dense random polynomials of total degree {d} in {n} variables, coefficients in [-9, 9]')
    for n in range(2, 6):
        for planes in (1, 2):
            rng = random.Random(f'cad-sphere-{n}-{planes}')
            polys = [sphere(n)] + [hyperplane(n, rng) for _ in range(planes)]
            yield case('full', f'sphere-n{n}-h{planes}', n, f'sphere-h{planes}', [f'x{i}' for i in range(n)], polys,
                       f'unit {n - 1}-sphere in R^{n} with {planes} random hyperplane(s)')


def sat_cases():
    for ex in parse_bank():
        n = len(ex['variables'])
        if not 2 <= n <= 5 or re.search(r'\\/|==>|\(A ', ex['formula']):
            continue
        polys, masks = [], []
        for p, op in ex['atoms']:
            if all(sum(e) == 0 for e in p):
                continue
            polys.append(p)
            masks.append(MASK[op])
        yield case('sat', 'bank-' + slug(ex['title']), n, 'bank', ex['variables'], polys,
                   f"CAD example bank (Wilson 2012): {ex['title']}; existential closure of the conjunction", masks)
    # Paired SAT/UNSAT variants of the same constraint set.
    for n in (2, 3, 4):
        names = [f'x{i}' for i in range(n)]
        for variant, bound in (('sat', Fraction(1, 4 ** n)), ('unsat', Fraction(1))):
            p2 = make([((1,) * n, 1), ((0,) * n, -bound)], None)
            yield case('sat', f'hong-n{n}-{variant}', n, 'hong', names, [sphere(n), p2],
                       f'Hong: |x| < 1 and x0...x{n - 1} > {bound}', [1, 4], variant)
    names = ['x', 'y']
    motzkin = make([((4, 2), 1), ((2, 4), 1), ((2, 2), -3), ((0, 0), 1)], None)
    yield case('sat', 'motzkin-sat', 2, 'motzkin', names, [motzkin], 'Motzkin polynomial <= 0 (zero at |x| = |y| = 1)', [3], 'sat')
    yield case('sat', 'motzkin-unsat', 2, 'motzkin', names, [motzkin], 'Motzkin polynomial < 0 (nonnegative)', [1], 'unsat')
    for n in (2, 3, 4, 5):
        names = [f'x{i}' for i in range(n)]
        for variant, c in (('sat', 1), ('unsat', n)):
            plane = make([(tuple(1 if j == i else 0 for j in range(n)), 1) for i in range(n)] + [((0,) * n, -c)], None)
            yield case('sat', f'sphere-plane-n{n}-{variant}', n, 'sphere-plane', names, [sphere(n), plane],
                       f'unit sphere in R^{n} meets x0 + ... + x{n - 1} = {c}', [2, 2], variant)
    for d in (2, 3, 4):
        # A positive-definite form shifted down: q(x) + e < 0 with q a sum of squares.
        rng = random.Random(f'cad-sos-{d}')
        names = ['x', 'y', 'z']
        squares = []
        for _ in range(3):
            lin = dense_random(3, 1, rng)
            sq = {}
            for (e1, c1), (e2, c2) in itertools.product(lin.items(), repeat=2):
                e = tuple(a + b for a, b in zip(e1, e2))
                sq[e] = sq.get(e, 0) + c1 * c2
            squares.append(sq)
        total = make([(e, c) for sq in squares for e, c in sq.items()] + [((2 * d, 0, 0), 1), ((0, 2 * d, 0), 1), ((0, 0, 2 * d), 1)], None)
        at_origin = total.get((0, 0, 0), 0)
        for variant, shift in (('sat', -at_origin - 1), ('unsat', 1)):
            p = make(list(total.items()) + [((0, 0, 0), shift)], None)
            yield case('sat', f'sos-d{2 * d}-{variant}', 2 * d, 'sos', names, [p],
                       f'sum of squares plus x^{2 * d} + y^{2 * d} + z^{2 * d} {"- (value at 0) - 1" if shift < 0 else "+ 1"} < 0', [1], variant)


def cases():
    # Owner decision, 2026-10-23: QEPCAD also failed to complete this full
    # decomposition within 30 minutes. Preserve its bank source and historical
    # reports, but omit it from active acceptance/performance runs.
    return [c for c in list(full_cases()) + list(sat_cases())
            if c['id'] != 'full-bank-piano-mover-s-problem-davenport']


def generate():
    CASES.mkdir(parents=True, exist_ok=True)
    expected = set()
    for c in cases():
        path = CASES / f"{c['id']}.json"
        expected.add(path)
        path.write_text(json.dumps(c, separators=(',', ':')) + '\n')
    for stale in CASES.glob('*.json'):
        if stale not in expected:
            stale.unlink()
    return len(expected)


def load():
    found = [json.loads(p.read_text()) for p in sorted(CASES.glob('*.json'))
             if p.stem != 'full-bank-piano-mover-s-problem-davenport']
    return sorted(found, key=lambda c: (c['kind'], c['ladder'], c['size'], c['id']))


def polys_of(c):
    return [make([(tuple(e), Fraction(v)) for e, v in p], None) for p in c['polys']]


# ------------------------------------------------------------------ independent checks

def _sympy():
    import sympy
    return sympy


class Coordinate:
    """An exact real: rational, or the unique root of a squarefree polynomial in [low, high]."""

    def __init__(self, rational=None, coefficients=None, low=None, high=None):
        self.rational = rational
        if rational is None:
            sympy = _sympy()
            t = sympy.Symbol('t')
            p = sympy.Poly([sympy.Rational(c.numerator, c.denominator) for c in reversed(coefficients)], t, domain='QQ')
            p = sympy.Poly(sympy.quo(p, sympy.gcd(p, p.diff(t))), t, domain='QQ')
            low, high = Fraction(low), Fraction(high)
            hits = [(Fraction(int(s.p), int(s.q)), Fraction(int(u.p), int(u.q)))
                    for (s, u), _ in p.intervals()]
            # Choose the root whose isolating interval meets [low, high]; refine until unique.
            index = [i for i, (s, u) in enumerate(hits) if not (u < low or s > high)]
            while len(index) > 1:
                refined = []
                for i in index:
                    s, u = p.refine_root(hits[i][0], hits[i][1], eps=(high - low) / 64 or Fraction(1, 2 ** 64))
                    hits[i] = (Fraction(int(s.p), int(s.q)), Fraction(int(u.p), int(u.q)))
                    if not (hits[i][1] < low or hits[i][0] > high):
                        refined.append(i)
                index = refined
            if len(index) != 1:
                raise ValueError('interval does not isolate a root')
            self.poly, self.interval = p, hits[index[0]]
            if self.interval[0] == self.interval[1]:
                self.rational = self.interval[0]

    @staticmethod
    def parse(text):
        if text.startswith('Q:'):
            return Coordinate(rational=Fraction(text[2:]))
        _, coefficients, low, high = text.split(':')
        return Coordinate(coefficients=[Fraction(c) for c in coefficients.split(',')], low=low, high=high)

    def bounds(self, width):
        if self.rational is not None:
            return self.rational, self.rational
        s, u = self.interval
        if u - s > width:
            s, u = self.poly.refine_root(s, u, eps=width)
            self.interval = (Fraction(int(s.p), int(s.q)), Fraction(int(u.p), int(u.q)))
        return self.interval

    def sympy(self):
        sympy = _sympy()
        if self.rational is not None:
            return sympy.Rational(self.rational.numerator, self.rational.denominator)
        s, u = self.interval
        # Our interval isolates the root, so s is not a root: count those below it.
        index = self.poly.count_roots(None, sympy.Rational(s.numerator, s.denominator))
        return sympy.CRootOf(self.poly.as_expr(), index)


def interval_sign(poly, point, width):
    low = high = Fraction(0)
    boxes = [c.bounds(width) for c in point]
    for e, c in poly.items():
        lo = hi = Fraction(1)
        for (a, b), k in zip(boxes, e):
            if not k:
                continue
            ends = [a ** k, b ** k]
            if k % 2 == 0 and a < 0 < b:
                ends.append(Fraction(0))
            values = [lo * x for x in ends] + [hi * x for x in ends]
            lo, hi = min(values), max(values)
        if c > 0:
            low, high = low + c * lo, high + c * hi
        else:
            low, high = low + c * hi, high + c * lo
    if low > 0:
        return 1
    if high < 0:
        return -1
    return None


def exact_sign(poly, point):
    """The sign of poly at an exact algebraic point; zeros are proved by minimal polynomials."""
    width = Fraction(1, 2 ** 16)
    for _ in range(6):
        s = interval_sign(poly, point, width)
        if s is not None:
            return s
        width /= 2 ** 32
    sympy = _sympy()
    xs = sympy.symbols(f'v0:{len(point)}')
    expr = sum(sympy.Rational(c.numerator, c.denominator) * sympy.Mul(*[x ** k for x, k in zip(xs, e)]) for e, c in poly.items())
    value = expr.subs({x: c.sympy() for x, c in zip(xs, point)})
    z = sympy.Symbol('z')
    m = sympy.minimal_polynomial(value, z, domain=sympy.QQ)
    if sympy.Poly(m, z) == sympy.Poly(z, z):
        return 0
    while True:
        s = interval_sign(poly, point, width)
        if s is not None:
            return s
        width /= 2 ** 64


def check_point(polys, masks, coordinates):
    point = [Coordinate.parse(t) for t in coordinates]
    for p, m in zip(polys, masks):
        s = exact_sign(p, point)
        if not m & (1 << (s + 1)):
            return False
    return True


def check_cells(polys, answer_path, limit):
    """Sign-check the reported terminal cells; every cell when there are at most `limit`."""
    lines = Path(answer_path).read_text().splitlines()
    count = int(lines[0])
    rows = lines[1:]
    step = max(1, -(-count // limit))
    checked = 0
    for row in rows[::step]:
        parts = row.split(' ')
        signs = [int(s) for s in parts[1].split(',')] if parts[1] else []
        point = [Coordinate.parse(t) for t in parts[2:]]
        for p, claimed in zip(polys, signs):
            if exact_sign(p, point) != claimed:
                return checked, count, False
        checked += 1
    return checked, count, True


# ------------------------------------------------------------------ tools

def library_key():
    lib = PolyMojo.library()
    digest = hashlib.sha256(DRIVER.read_bytes())
    for name in ('apn_mojo.mojoc', 'polynomials.mojoc', 'poly.mojoc'):
        digest.update((lib / name).read_bytes())
    return lib, digest.hexdigest()[:16]


class PolyMojo:
    in_process = True
    system = 'Poly Mojo'

    @staticmethod
    def library():
        return Path(os.environ.get('POLYMOJO_LIB', ROOT / 'build'))

    def __init__(self, mode):
        self.mode = mode
        self.name = f'polymojo-{mode}'
        self.algorithm = {'construct': 'compact Revision 15 construction; complete final verification timed separately',
                          'final': 'cad.decompose, compact Revision 15 with mandatory final verification',
                          'lazard': 'cad.decompose(lazard=True), compact plain Lazard with mandatory final verification',
                          'mccallum': 'cad.decompose(lazard=False), checked legacy McCallum',
                          'stream': 'cad.decompose_to into cad.checker', 'solve': 'cad.solve'}[mode]

    def supports(self, c):
        return (c['kind'] == 'sat') == (self.mode == 'solve')

    def version(self):
        return subprocess.run(['git', 'rev-parse', '--short', 'HEAD'], cwd=ROOT, capture_output=True, text=True).stdout.strip()

    def binary(self, nvars):
        lib, key = library_key()
        return CACHE / 'bin' / f'pm_cad_{nvars}_{key}'

    def build(self, nvars):
        lib, _ = library_key()
        out = self.binary(nvars)
        out.parent.mkdir(parents=True, exist_ok=True)
        start = time.time()
        # Build outside this workspace's activation, as the other drivers do: its
        # conda linker predates the glibc symbols Mojo's runtime needs.
        from .tools import outside_environment
        subprocess.run([os.environ.get('PIXI_EXE', 'pixi'), 'run', '--manifest-path', str(ROOT / 'pixi.toml'), '--locked', 'mojo', 'build',
                        '-I', str(lib), '-D', f'NVARS={nvars}', str(DRIVER), '-o', str(out)],
                       cwd=ROOT, check=True, env=outside_environment())
        return out, time.time() - start

    def prepare(self, c, work, settings):
        polys = polys_of(c)
        (work / 'input.txt').write_text(write_records(polys, len(c['variables']), None))
        masks = ','.join(map(str, c['masks'])) if self.mode == 'solve' else '-'
        return [str(self.binary(len(c['variables']))), self.mode, 'input.txt', 'result.json', 'answer.txt', masks,
                str(settings['min_seconds']), str(settings['min_reps'])]

    def collect(self, c, work, settings):
        r = json.loads((work / 'result.json').read_text())
        out = {'times_ns': r['times_ns'], 'peak_kb': r['peak_kb'], 'rss_before_kb': r['rss_before_kb']}
        out['includes_mandatory_verification'] = self.mode in ('final', 'lazard', 'mccallum')
        if self.mode == 'construct':
            out['memory_note'] = 'Peak includes final verification; only the time components are separated.'
        if r.get('check_ns'):
            out['check_s'] = r['check_ns'] / 1e9
            if out['includes_mandatory_verification']:
                out['extra_recheck_s'] = r['check_ns'] / 1e9
        if 'cells_ns' in r:
            out['absolute_cell_output_s'] = r['cells_ns'] / 1e9
        out['check_ok'] = r['check_ok']
        for k in ('cells', 'projection_factors', 'stacks'):
            if k in r:
                out[k] = r[k]
        polys = polys_of(c)
        try:
            if self.mode == 'solve':
                lines = (work / 'answer.txt').read_text().split('\n')
                out['sat'] = lines[0] == 'sat'
                if out['sat']:
                    out['point_ok'] = check_point(polys, c['masks'], lines[1].split(' '))
            elif self.mode in ('construct', 'final', 'lazard', 'mccallum'):
                checked, count, ok = check_cells(polys, work / 'answer.txt', settings['cell_limit'])
                out |= {'cells_checked': checked, 'cells_ok': ok}
        except Exception:
            # A failure of the independent checker itself is recorded, not hidden.
            out['independent_check_error'] = traceback.format_exc()[-1500:]
        return out


class Qepcad:
    in_process = True
    system = 'QEPCAD B'

    def __init__(self, mode):
        self.mode = mode
        self.name = f'qepcad-{mode}'
        self.algorithm = {'fullcad': 'full-cad (McCallum-Brown projection)', 'sat': 'existential closure'}[mode]

    @staticmethod
    def home():
        return Path(os.environ.get('QEPCAD_HOME', CACHE / 'opt' / 'tarski' / 'qesource'))

    def supports(self, c):
        return (self.home() / 'bin' / 'qepcad').exists() and (c['kind'] == 'sat') == (self.mode == 'sat')

    def version(self):
        banner = self.home() / 'source/main/PRINTBANNER.c'
        match = re.search(r'static const char\* version = "([^"]+)"', banner.read_text()) if banner.is_file() else None
        version = match[1] if match else 'unknown'
        return f'QEPCAD B {version} (Tarski ' + os.environ.get('TARSKI_COMMIT', 'unknown') + ')'

    def script(self, c, trivial=False):
        names = c['variables']
        polys = polys_of(c)
        if trivial:
            polys = [make([(tuple(1 if j == i else 0 for j in range(len(names))), 1)], None) for i in range(len(names))]
        if self.mode == 'fullcad':
            atoms = ' /\\ '.join(f'[{infix(p, names)} /= 0]' for p in polys)
            return (f"[{c['id']}]\n({','.join(names)})\n{len(names)}\n[{atoms}].\n"
                    "full-cad\ngo\ngo\ngo\nd-stat\nd-proj-factors\ngo\nfinish\n")
        ops = {1: '<', 2: '=', 4: '>', 3: '<=', 6: '>=', 5: '/='}
        masks = c['masks'] if not trivial else [5] * len(polys)
        atoms = ' /\\ '.join(f'[{infix(p, names)} {ops[m]} 0]' for p, m in zip(polys, masks))
        quant = ''.join(f'(E {v})' for v in names)
        return f"[{c['id']}]\n({','.join(names)})\n0\n{quant}[{atoms}].\nfinish\n"

    overheads = {}

    def overhead(self, c, settings):
        key = (self.mode, len(c['variables']))
        if key not in self.overheads:
            values = []
            for _ in range(3):
                work = Path(tempfile.mkdtemp(prefix='cad-qe-', dir=settings['scratch']))
                cmd, env = self.prepare(c, work, settings, trivial=True)
                subprocess.run(cmd, cwd=work, env=env, check=True)
                text = (work / 'stdout.qe').read_text(errors='replace')
                values.append(int(re.search(r'System time after the initialization: (\d+) milliseconds', text)[1]) * 1000000)
                shutil.rmtree(work, ignore_errors=True)
            self.overheads[key] = min(values)
        return self.overheads[key]

    def prepare(self, c, work, settings, trivial=False):
        (work / 'input.txt').write_text(self.script(c, trivial))
        home = self.home()
        return ['sh', '-c', f'exec {home}/bin/qepcad +N100000000 < input.txt > stdout.qe 2>&1'], {**os.environ, 'qe': str(home)}

    def collect(self, c, work, settings):
        text = (work / 'stdout.qe').read_text(errors='replace')
        m = re.search(r'System time after the initialization: (\d+) milliseconds', text)
        if not m:
            raise RuntimeError('no QEPCAD timing: ' + text[-1500:])
        # QEPCAD's own clock after its memory initialization, as in-process time.
        # Its clock includes heap work proportional to +N, so the same clock on a
        # trivial problem with the same variables is subtracted.
        overhead = self.overhead(c, settings)
        out = {'times_ns': [max(int(m[1]) * 1000000 - overhead, 0)], 'peak_kb': 0, 'rss_before_kb': 0,
               'qepcad_overhead_s': overhead / 1e9}
        if self.mode == 'sat':
            m = re.search(r'An equivalent quantifier-free formula:\s*\n\s*(TRUE|FALSE)', text)
            if not m:
                raise RuntimeError('no verdict: ' + text[-1500:])
            out['sat'] = m[1] == 'TRUE'
        else:
            cells = re.search(r'^Cells((?:\s+\d+)+)\s*$', text, re.M)
            factors = re.search(r'^Proj Fact((?:\s+\d+)+)\s*$', text, re.M)
            if not cells or not factors:
                raise RuntimeError('no QEPCAD statistics: ' + text[-1500:])
            out['cells'] = int(cells[1].split()[-1])
            out['projection_factors'] = [int(v) for v in factors[1].split()[:-1]]
        return out


class Z3:
    in_process = True
    system = 'Z3'
    name = 'z3'
    algorithm = 'nlsat (QF_NRA tactic)'

    @staticmethod
    def python():
        return os.environ.get('Z3_PYTHON', str(CACHE / 'opt' / 'z3venv' / 'bin' / 'python'))

    def supports(self, c):
        return c['kind'] == 'sat' and Path(self.python()).exists()

    def version(self):
        try:
            return subprocess.run([self.python(), '-c', 'import z3; print(z3.get_version_string())'], capture_output=True, text=True).stdout.strip()
        except OSError:
            return ''

    def prepare(self, c, work, settings):
        (work / 'case.json').write_text(json.dumps(c))
        return [self.python(), '-I', str(Path(__file__).resolve().parent / 'cad_z3.py'), 'case.json', 'result.json',
                str(settings['min_seconds']), str(settings['min_reps'])]

    def collect(self, c, work, settings):
        r = json.loads((work / 'result.json').read_text())
        out = {'times_ns': r['times_ns'], 'peak_kb': r['peak_kb'], 'rss_before_kb': r['rss_before_kb'], 'sat': r['sat']}
        if r['sat']:
            try:
                out['point_ok'] = check_point(polys_of(c), c['masks'], r['point'])
            except Exception:
                out['independent_check_error'] = traceback.format_exc()[-1500:]
        return out


TOOLS = {t.name: t for t in [PolyMojo('construct'), PolyMojo('final'), PolyMojo('lazard'), PolyMojo('mccallum'), PolyMojo('stream'), PolyMojo('solve'),
                             Qepcad('fullcad'), Qepcad('sat'), Z3()]}


# ------------------------------------------------------------------ running

def run_one(tool, c, settings, baselines):
    work = Path(tempfile.mkdtemp(prefix='cad-', dir=settings['scratch']))
    try:
        cmd = tool.prepare(c, work, settings)
        env = os.environ.copy()
        if isinstance(cmd, tuple):
            cmd, env = cmd
        allowance = 600 if isinstance(tool, PolyMojo) and tool.mode != 'stream' else 0
        p = measure.run(cmd, cwd=work, env=env, timeout_s=settings['timeout'] + allowance, memory_bytes=settings['memory'],
                        cpu=settings['cpu'], stdout=work / 'stdout.txt', stderr=work / 'stderr.txt')
        if p.timed_out:
            return {'outcome': 'timeout'}
        if p.oom:
            return {'outcome': 'out-of-memory'}
        if p.returncode != 0:
            return {'outcome': 'error', 'error': ((work / 'stderr.txt').read_text(errors='replace') + (work / 'stdout.txt').read_text(errors='replace'))[-2000:]}
        r = tool.collect(c, work, settings)
        if tool.in_process:
            times = r.pop('times_ns')
            if min(times) / 1e9 > settings['timeout']:
                return {'outcome': 'timeout'}
            r['time_s'] = statistics.median(times) / 1e9
            r['peak_incremental_kib'] = r.pop('peak_kb') - r.pop('rss_before_kb')
        else:
            r['time_s'] = max(p.wall_s - baselines(tool, c), 0.0)
            r['wall_s'] = p.wall_s
        r['outcome'] = 'ok'
        if r.get('check_ok') is False or r.get('point_ok') is False or r.get('cells_ok') is False:
            r['outcome'] = 'wrong'
        if c['expect'] is not None and 'sat' in r and r['sat'] != (c['expect'] == 'sat'):
            r['outcome'] = 'wrong'
        return r
    except Exception:
        return {'outcome': 'error', 'error': traceback.format_exc()[-2000:]}
    finally:
        if not settings['keep']:
            shutil.rmtree(work, ignore_errors=True)


def main_run(args):
    selected = [TOOLS[n] for n in (args.tools.split(',') if args.tools else TOOLS)]
    generate()
    todo = [c for c in load() if re.search(args.cases, c['id'])]
    needed = sorted({len(c['variables']) for c in todo for t in selected if isinstance(t, PolyMojo) and t.supports(c)})
    from . import tools
    libraries = tools.verify_poly_mojo(selected)
    pm = TOOLS['polymojo-lazard']
    for n in needed:
        if not pm.binary(n).exists():
            out, seconds = pm.build(n)
            print(f'built {out.name} in {seconds:.0f} s', flush=True)
    results = Path(args.results or HERE / 'results' / (args.host or 'local') / f'{datetime.date.today().isoformat()}-cad' / 'records.jsonl')
    results.parent.mkdir(parents=True, exist_ok=True)
    env_path = results.parent / 'environment.json'
    if libraries and not env_path.exists():
        from .run import environment
        env_path.write_text(json.dumps(environment(), indent=2) + '\n')
    tools.record_libraries(env_path, libraries)
    settings = {'timeout': args.timeout, 'memory': 12 << 30, 'cpu': args.cpu, 'min_seconds': args.min_seconds,
                'min_reps': args.min_reps, 'keep': args.keep, 'cell_limit': args.cell_limit,
                'scratch': CACHE / 'work'}
    settings['scratch'].mkdir(parents=True, exist_ok=True)
    cache = {}

    def baseline(tool, c):
        key = (tool.name, len(c['variables']))
        if key not in cache:
            walls = []
            for _ in range(3):
                work = Path(tempfile.mkdtemp(prefix='cad-base-', dir=settings['scratch']))
                cmd, env = tool.prepare(c, work, settings, trivial=True)
                p = measure.run(cmd, cwd=work, env=env, timeout_s=60, memory_bytes=settings['memory'], cpu=settings['cpu'],
                                stdout=work / 'stdout.txt', stderr=work / 'stderr.txt')
                walls.append(p.wall_s)
                shutil.rmtree(work, ignore_errors=True)
            cache[key] = statistics.median(walls)
        return cache[key]

    done = {}
    if results.exists():
        for line in results.read_text().splitlines():
            r = json.loads(line)
            done[(r['case'], r['tool'])] = r
    stopped = set()
    with open(results, 'a') as out:
        for c in todo:
            for tool in selected:
                previous = done.get((c['id'], tool.name))
                if not tool.supports(c) or previous and previous['outcome'] != 'error' and not args.rerun:
                    continue
                base = {'case': c['id'], 'kind': c['kind'], 'ladder': c['ladder'], 'nvars': len(c['variables']),
                        'npolys': len(c['polys']), 'tool': tool.name, 'library': tool.system,
                        'algorithm': tool.algorithm, 'version': tool.version(), 'timeout_s': args.timeout,
                        'started': datetime.datetime.now(datetime.timezone.utc).isoformat(timespec='seconds')}
                from .proofs import metadata
                base.update(metadata(tool, dict(c, family='cad')))
                if (tool.name, c['ladder']) in stopped and c['ladder'] != 'bank':
                    record = {'outcome': 'skipped'}
                else:
                    record = run_one(tool, c, settings, baseline)
                    if record['outcome'] in ('timeout', 'out-of-memory'):
                        stopped.add((tool.name, c['ladder']))
                record = base | record
                out.write(json.dumps(record) + '\n')
                out.flush()
                extra = ''
                if record['outcome'] == 'ok':
                    extra = f"{record['time_s']:10.4f} s"
                    for k in ('cells', 'sat'):
                        if k in record:
                            extra += f'  {k}={record[k]}'
                print(f"{c['id']:<44} {tool.name:<18} {record['outcome']:>10} {extra}", flush=True)


# ------------------------------------------------------------------ report

def main_report(args):
    folder = Path(args.folder)
    records = {}
    for line in (folder / 'records.jsonl').read_text().splitlines():
        r = json.loads(line)
        records[(r['case'], r['tool'])] = r
    cases_ = sorted({k[0] for k in records})
    lines = ['# Cylindrical algebraic decomposition', '']
    full_tools = ['polymojo-construct', 'polymojo-final', 'polymojo-lazard', 'polymojo-mccallum', 'polymojo-stream', 'qepcad-fullcad']
    sat_tools = ['polymojo-solve', 'z3', 'qepcad-sat']

    def cell(r):
        if r is None:
            return '—'
        if r['outcome'] != 'ok':
            return r['outcome']
        return f"{r['time_s']:.3g}"

    lines += ['## Full decomposition (seconds; cells / projection factors for Poly Mojo)', '',
              'polymojo-construct measures construction separately from complete final verification, using benchmark instrumentation of the same compact backend and retries. It still retains final data that serve as evidence; it is not a proof-free public API. The PM/QEPCAD ratio uses this construction component. Public decomposition times include mandatory verification. Extra rechecks and absolute cell output are recorded separately. QEPCAD reports construction.', '',
              '| Case | ' + ' | '.join(full_tools) + ' | PM/QEPCAD | Lazard cells | McCallum cells | factors (Lazard) | QEPCAD cells / factors | sample points checked |',
              '|' + '---|' * (len(full_tools) + 7)]
    for cid in cases_:
        if not cid.startswith('full-'):
            continue
        row = [records.get((cid, t)) for t in full_tools]
        final, accepted, lz, mc, _, q = row
        ratio = f"{final['time_s'] / q['time_s']:.2f}" if final and q and final['outcome'] == q['outcome'] == 'ok' and q['time_s'] > 0 else '—'
        qcells = (q.get('cells'), q.get('projection_factors')) if q and q['outcome'] == 'ok' else None
        lines.append(f"| {cid[5:]} | " + ' | '.join(cell(r) for r in row) + f" | {ratio} | {lz.get('cells', '—') if lz else '—'} | "
                     f"{mc.get('cells', '—') if mc else '—'} | {lz.get('projection_factors', '—') if lz else '—'} | {f'{qcells[0]} / {qcells[1]}' if qcells else '—'} | "
                     f"{lz.get('cells_checked', '—') if lz else '—'} |")
    lines += ['', '## Construction and final verification', '',
              '| Case | Construction | Final verification | Sum | Public accepted call |', '|---|---:|---:|---:|---:|']
    for cid in cases_:
        r = records.get((cid, 'polymojo-construct'))
        if r and r['outcome'] == 'ok':
            check = r['check_s']
            lines.append(f"| {cid} | {r['time_s']:.3g} | {check:.3g} | {r['time_s'] + check:.3g} | {cell(records.get((cid, 'polymojo-final')))} |")
    lines += ['', '## Conjunctions (seconds; verdicts must agree)', '',
              'cad.solve retains its covering evidence; this API has no proof-free switch. Its independent cad.check call is excluded from the solve time. These are certificate-producing API comparisons.', '',
              '| Case | ' + ' | '.join(sat_tools) + ' | PM/Z3 | verdicts | agree |', '|' + '---|' * (len(sat_tools) + 4)]
    for cid in cases_:
        if not cid.startswith('sat-'):
            continue
        row = [records.get((cid, t)) for t in sat_tools]
        verdicts = [r.get('sat') for r in row if r and r['outcome'] == 'ok']
        pm, z = row[0], row[1]
        ratio = f"{pm['time_s'] / z['time_s']:.2f}" if pm and z and pm['outcome'] == z['outcome'] == 'ok' and z['time_s'] > 0 else '—'
        lines.append(f"| {cid[4:]} | " + ' | '.join(cell(r) for r in row) + f" | {ratio} | "
                     f"{'/'.join('sat' if v else 'unsat' for v in verdicts)} | {'yes' if len(set(verdicts)) <= 1 else 'NO'} |")
    lines += ['', '## Independent rechecks', '',
              'These checks run after the producer timer stops. Decomposition public calls already include mandatory acceptance; these are additional rechecks, not that acceptance cost.', '',
              '| Case | Mode | Producer | Extra check |', '|---|---|---:|---:|']
    for r in records.values():
        if r['tool'] != 'polymojo-construct' and r['outcome'] == 'ok' and 'check_s' in r:
            lines.append(f"| {r['case']} | {r['tool']} | {r['time_s']:.3g} | {r['check_s']:.3g} |")
    (folder / 'report.md').write_text('\n'.join(lines) + '\n')
    print('\n'.join(lines))


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = parser.add_subparsers(dest='command', required=True)
    sub.add_parser('generate')
    run = sub.add_parser('run')
    run.add_argument('--tools')
    run.add_argument('--cases', default='')
    run.add_argument('--results')
    run.add_argument('--host')
    run.add_argument('--timeout', type=float, default=300)
    run.add_argument('--cpu', type=int, default=1)
    run.add_argument('--min-seconds', type=float, default=0.5)
    run.add_argument('--min-reps', type=int, default=3)
    run.add_argument('--cell-limit', type=int, default=400)
    run.add_argument('--keep', action='store_true')
    run.add_argument('--rerun', action='store_true')
    report = sub.add_parser('report')
    report.add_argument('folder')
    args = parser.parse_args(argv)
    if args.command == 'generate':
        print(f'cad: {generate()} cases')
    elif args.command == 'run':
        main_run(args)
    else:
        main_report(args)


if __name__ == '__main__':
    main()
