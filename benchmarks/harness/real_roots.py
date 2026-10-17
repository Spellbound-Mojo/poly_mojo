"""Real roots family: cases, tool adapters, and the interval check.

Cases (README, "Real roots"): Mignotte x^n - 2(ax - 1)^2 with a = 100,
Wilkinson prod (x - i), Chebyshev T_n, random dense polynomials with
coefficients in {-1, 1} and of 64 and 1024 bits, and products with repeated
factors. Each polynomial runs in five modes:

| mode | Poly Mojo | FLINT 3.6 (C driver) | SymPy | msolve |
|---|---|---|---|---|
| isolate | `dense.real_root_cover` | `arb_fmpz_poly_complex_roots` on the squarefree part | `Poly.intervals` | default run |
| refine53, refine1000 | `roots.refine` of the cover | the same to width 2^-bits | `Poly.intervals(eps=...)` | `-p bits` |
| exact | `dense.real_roots` | | `Poly.real_roots` | |
| count | `dense.sturm_sequence` and `roots.count_roots` | `fmpz_poly_num_real_roots` (and `_sturm`) | `Poly.count_roots` | |

FLINT 3.6 has no `fmpz_poly_isolate_real_roots`, `arb_fmpz_poly_real_roots`,
or `arb_fmpz_poly_refine_root_arb`; `arb_fmpz_poly_complex_roots` is its
certified solver and reports the real roots exactly as real.

Check: the number of distinct real roots, and every interval containing
exactly one root of an Arb reference computed to width 2^-1100.
"""
from fractions import Fraction
import hashlib
import json
import os
from pathlib import Path
import random
import subprocess

from . import measure

HERE = Path(__file__).resolve().parent.parent
ROOT = HERE.parent
CACHE = HERE / '.cache'
MODES = ('isolate', 'refine53', 'refine1000', 'exact', 'count')
REFERENCE_BITS = 1100


# ---------------------------------------------------------------- polynomials
# Ascending integer coefficient lists.

def _mul(a, b):
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                out[i + j] += x * y
    return out


def _pow(a, k):
    out = [1]
    for _ in range(k):
        out = _mul(out, a)
    return out


def mignotte(n, a=100):
    """x^n - 2(ax - 1)^2: two real roots within about a^(-n/2 - 1) of 1/a."""
    c = [0] * (n + 1)
    c[n] += 1
    for i, v in enumerate(_pow([-1, a], 2)):
        c[i] -= 2 * v
    return c


def wilkinson(n):
    """prod (x - i) for i = 1..n."""
    c = [1]
    for i in range(1, n + 1):
        c = _mul(c, [-i, 1])
    return c


def chebyshev(n):
    """T_n: n irrational roots in (-1, 1), clustered towards the ends."""
    previous, current = [1], [0, 1]
    for _ in range(n - 1):
        shifted = [0] + [2 * x for x in current]
        previous, current = current, [s - (previous[j] if j < len(previous) else 0) for j, s in enumerate(shifted)]
    return current


def random_dense(n, bits):
    """Seeded coefficients in {-1, 1} (bits = 1) or uniform in (-2^bits, 2^bits), nonzero ends."""
    rng = random.Random(f'roots-random-{bits}-{n}')
    c = []
    for i in range(n + 1):
        if bits == 1:
            c.append(rng.choice((-1, 1)))
        else:
            v = 0
            while v == 0 and (i == 0 or i == n):
                v = rng.randrange(-(1 << bits) + 1, 1 << bits)
            c.append(v if i in (0, n) else rng.randrange(-(1 << bits) + 1, 1 << bits))
    return c


def repeated(k):
    """T_k^3 * W_k^2 * (x^2 - 2)^4: degree 5k + 8, repeated rational and irrational roots."""
    return _mul(_mul(_pow(chebyshev(k), 3), _pow(wilkinson(k), 2)), _pow([-2, 0, 1], 4))


SYSTEMS = {
    'mignotte': (mignotte, [10, 20, 50, 100, 200, 400], 'x^n - 2(100x - 1)^2; MPSolve test set'),
    'wilkinson': (wilkinson, [20, 40, 80, 160, 320, 640], 'prod (x - i); MPSolve test set'),
    'chebyshev': (chebyshev, [100, 200, 400, 700, 1000], 'Chebyshev T_n'),
    'random1': (lambda n: random_dense(n, 1), [100, 200, 500, 1000, 2000], 'random dense, coefficients ±1'),
    'random64': (lambda n: random_dense(n, 64), [100, 200, 500, 1000, 2000], 'random dense, 64-bit coefficients'),
    'random1024': (lambda n: random_dense(n, 1024), [100, 200, 500, 1000, 2000], 'random dense, 1024-bit coefficients'),
    'repeated': (repeated, [4, 8, 16, 32, 64], 'T_k^3 W_k^2 (x^2 - 2)^4, degree 5k + 8'),
}


def cases():
    for system, (build, sizes, source) in SYSTEMS.items():
        for size in sizes:
            coefficients = build(size)
            for mode in MODES:
                yield {
                    'id': f'{system}-{size}.{mode}',
                    'family': 'roots',
                    'system': system,
                    'size': size,
                    'mode': mode,
                    'ladder': f'{system}.{mode}',
                    'field': None,
                    'order': 'lex',
                    'variables': ['x'],
                    'coefficients': [str(c) for c in coefficients],
                    'source': source,
                }


def root_bound_exponent(coefficients):
    """k with every real root in (-2^k, 2^k): twice Fujiwara's bound, rounded up to a power of two."""
    c = [int(x) for x in coefficients]
    while len(c) > 1 and c[-1] == 0:
        c.pop()
    n, lead = len(c) - 1, abs(c[-1]).bit_length()
    k = 0
    for i in range(1, n + 1):
        if c[n - i]:
            k = max(k, -((lead - 1 - abs(c[n - i]).bit_length()) // i))
    return k + 2


def write_input(path, case):
    """The coefficient count, the ascending coefficients, and the root bound exponent."""
    c = case['coefficients']
    path.write_text(f'{len(c)}\n' + '\n'.join(c) + f'\n{root_bound_exponent(c)}\n')


# ---------------------------------------------------------------- reference

def flint_binary():
    """Compile the FLINT C driver against the workspace's libflint (cached by source hash)."""
    source = HERE / 'drivers' / 'flint' / 'real_roots.c'
    prefix = Path(os.environ.get('CONDA_PREFIX', HERE / '.pixi' / 'envs' / 'default'))
    key = hashlib.sha256(source.read_bytes()).hexdigest()[:16]
    out = CACHE / 'bin' / f'flint_real_roots_{key}'
    if not out.is_file():
        out.parent.mkdir(parents=True, exist_ok=True)
        subprocess.run([os.environ.get('CC_FOR_DRIVER', 'gcc'), '-O2', str(source), '-o', str(out),
                        f'-I{prefix}/include', f'-L{prefix}/lib', f'-Wl,-rpath,{prefix}/lib', '-lflint', '-lgmp', '-lmpfr'],
                       check=True)
    return out


def _dyadic(m, e):
    m, e = int(m), int(e)
    return Fraction(m * (1 << e)) if e >= 0 else Fraction(m, 1 << -e)


def read_flint_answer(text):
    lines = text.split('\n')
    count = int(lines[0])
    intervals = []
    for line in lines[1:1 + count]:
        if not line.strip():
            break
        m0, e0, m1, e1 = line.split()
        intervals.append((_dyadic(m0, e0), _dyadic(m1, e1)))
    return count, intervals


def reference(case, bits=REFERENCE_BITS):
    """Real roots of the case polynomial enclosed to width 2^-bits by Arb (cached)."""
    key = hashlib.sha256(' '.join(case['coefficients']).encode()).hexdigest()[:20]
    if bits != REFERENCE_BITS:
        key += f'-{bits}'
    path = CACHE / 'reference' / f'roots-{key}.txt'
    if not path.is_file():
        path.parent.mkdir(parents=True, exist_ok=True)
        work = path.parent / f'work-{key}'
        work.mkdir(exist_ok=True)
        write_input(work / 'input.txt', case)
        subprocess.run([str(flint_binary()), 'input.txt', 'answer.txt', 'result.json', f'bits{bits}', '0', '1'],
                       cwd=work, check=True)
        os.replace(work / 'answer.txt', path)
        for f in work.iterdir():
            f.unlink()
        work.rmdir()
    return read_flint_answer(path.read_text())


def check(case, count, intervals):
    """True when the count matches and each closed interval holds exactly one reference root.

    The reference is computed to 32 bits below the narrowest interval, so a
    root inside an interval has its whole reference ball inside it too
    (unless the interval is a point, which must then lie in the ball).
    """
    bits = REFERENCE_BITS
    for low, high in intervals or ():
        if high > low:
            width = high - low
            bits = max(bits, width.denominator.bit_length() - width.numerator.bit_length() + 32)
    expected, balls = reference(case, -(-bits // 512) * 512 if bits > REFERENCE_BITS else bits)
    if count != expected:
        return False
    if intervals is None:
        return True
    if len(intervals) != expected:
        return False
    for low, high in intervals:
        inside = outside = 0
        for a, b in balls:
            if low == high:
                inside += a <= low <= b
                outside += not (a <= low <= b)
            elif low <= a and b <= high:
                inside += 1
            elif b < low or high < a:
                outside += 1
        if inside != 1 or inside + outside != len(balls):
            return False
    return True


def width_ok(case, intervals):
    bits = {'refine53': 53, 'refine1000': 1000}.get(case['mode'])
    return bits is None or all(high - low <= Fraction(1, 1 << bits) for low, high in intervals)


# ---------------------------------------------------------------- tools

class RootsTool:
    name = system = algorithm = ''
    in_process = True
    modes = ()

    def supports(self, case):
        return case['family'] == 'roots' and case['mode'] in self.modes

    def version(self):
        return ''

    def builds(self, cases):
        return []

    def finish(self, case, result, count, intervals):
        ok = check(case, count, intervals) and (intervals is None or width_ok(case, intervals))
        result.update({'answer': [count], 'count': count, 'check_ok': ok})
        return result


class PolyMojoRoots(RootsTool):
    name = 'polymojo-roots'
    system = 'Poly Mojo'
    algorithm = 'Sturm bisection'
    modes = ('isolate', 'refine53', 'refine1000', 'exact', 'count')
    driver = HERE / 'drivers' / 'poly_mojo' / 'real_roots.mojo'

    @staticmethod
    def library():
        return Path(os.environ.get('POLYMOJO_LIB', ROOT / 'build'))

    def version(self):
        from .tools import git_revision
        return git_revision()

    def binary(self, *key):
        lib = self.library()
        digest = hashlib.sha256(self.driver.read_bytes())
        for name in ('apn_mojo', 'polynomials', 'poly'):
            digest.update((lib / f'{name}.mojoc').read_bytes())
        return CACHE / 'bin' / f'pm_real_roots_{digest.hexdigest()[:16]}'

    def builds(self, cases):
        return [('roots', False)] if any(self.supports(c) for c in cases) else []

    def build(self, *key):
        from .tools import outside_environment
        out = self.binary()
        if out.is_file():
            return out, 0.0, None
        out.parent.mkdir(parents=True, exist_ok=True)
        cmd = [os.environ.get('PIXI_EXE', 'pixi'), 'run', '--manifest-path', str(ROOT / 'pixi.toml'), '--locked', 'mojo', 'build',
               '-I', str(self.library()), str(self.driver), '-o', str(out) + '.tmp']
        log = CACHE / 'logs' / f'{out.name}.build.log'
        log.parent.mkdir(parents=True, exist_ok=True)
        result = measure.run(cmd, cwd=ROOT, env=outside_environment(), timeout_s=3600, memory_bytes=None,
                             cpu=None, stdout=log, stderr=log)
        if result.returncode != 0:
            raise SystemExit(f'Poly Mojo driver build failed; see {log}')
        os.replace(str(out) + '.tmp', out)
        return out, result.wall_s, result.maxrss_kb

    def prepare(self, case, work, settings):
        write_input(work / 'input.txt', case)
        mode = 'sturm' if case['mode'] == 'count' else case['mode']
        return [str(self.binary()), 'input.txt', 'answer.txt', 'result.json', mode,
                str(settings['min_seconds']), str(settings['min_reps'])], os.environ.copy()

    def collect(self, case, work):
        result = json.loads((work / 'result.json').read_text())
        lines = (work / 'answer.txt').read_text().split('\n')
        count = int(lines[0])
        intervals = None
        if case['mode'] != 'count':
            intervals = [tuple(Fraction(x) for x in line.split()) for line in lines[1:1 + count]]
        return self.finish(case, result, count, intervals)


class FlintRoots(RootsTool):
    system = 'FLINT'

    def __init__(self, sturm=False):
        self.sturm = sturm
        self.name = 'flint-roots-sturm' if sturm else 'flint-roots'
        self.algorithm = 'Sturm count' if sturm else 'Arb complex roots; Descartes count'
        self.modes = ('count',) if sturm else ('isolate', 'refine53', 'refine1000', 'count')

    def version(self):
        return '3.6.0 (libflint, C driver)'

    def prepare(self, case, work, settings):
        write_input(work / 'input.txt', case)
        mode = case['mode'] if case['mode'] != 'count' else ('sturm' if self.sturm else 'count')
        return [str(flint_binary()), 'input.txt', 'answer.txt', 'result.json', mode,
                str(settings['min_seconds']), str(settings['min_reps'])], os.environ.copy()

    def collect(self, case, work):
        result = json.loads((work / 'result.json').read_text())
        count, intervals = read_flint_answer((work / 'answer.txt').read_text())
        return self.finish(case, result, count, None if case['mode'] == 'count' else intervals)


class SymPyRoots(RootsTool):
    system = 'SymPy'
    algorithm = 'continued fractions'
    modes = ('isolate', 'refine53', 'refine1000', 'exact', 'count')

    def __init__(self, ground_types='gmpy'):
        self.ground_types = ground_types
        self.name = 'sympy-roots' + ('' if ground_types == 'gmpy' else f'-{ground_types}')

    def version(self):
        import sympy
        return f'{sympy.__version__} ({self.ground_types} ground types)'

    def prepare(self, case, work, settings):
        from .tools import env_python
        write_input(work / 'input.txt', case)
        env = os.environ.copy()
        env['SYMPY_GROUND_TYPES'] = self.ground_types
        return [env_python(), str(HERE / 'drivers' / 'python' / 'sympy_real_roots.py'), 'input.txt', 'answer.txt',
                'result.json', case['mode'], str(settings['min_seconds']), str(settings['min_reps'])], env

    def collect(self, case, work):
        result = json.loads((work / 'result.json').read_text())
        if result.pop('ground_types') != self.ground_types:
            raise RuntimeError('SymPy did not use the requested ground types')
        lines = (work / 'answer.txt').read_text().split('\n')
        count = int(lines[0])
        intervals = None
        if case['mode'] != 'count':
            intervals = [tuple(Fraction(x) for x in line.split()) for line in lines[1:1 + count]]
        return self.finish(case, result, count, intervals)


class MsolveRoots(RootsTool):
    name = 'msolve-roots'
    system = 'msolve'
    algorithm = 'Descartes (usolve)'
    in_process = False
    modes = ('isolate', 'refine53', 'refine1000')

    def version(self):
        from .tools import MSOLVE_VERSION
        return MSOLVE_VERSION

    def supports(self, case):
        from .tools import MSOLVE
        return super().supports(case) and MSOLVE.is_file()

    @staticmethod
    def write(path, coefficients):
        terms = ''.join(f'{"+" if int(c) > 0 else "-"}{abs(int(c))}*x^{i}' for i, c in reversed(list(enumerate(coefficients))) if int(c))
        path.write_text('x\n0\n' + terms.lstrip('+') + '\n')

    def command(self, bits):
        from .tools import MSOLVE
        return [str(MSOLVE), '-t', '1', '-p', str(bits), '-f', 'input.ms', '-o', 'answer.txt'], os.environ.copy()

    def baseline_input(self, case, work):
        self.write(work / 'input.ms', ['-1', '1'])
        return self.command(64)

    def prepare(self, case, work, settings):
        self.write(work / 'input.ms', case['coefficients'])
        return self.command({'isolate': 1, 'refine53': 53, 'refine1000': 1000}[case['mode']])

    def collect(self, case, work):
        import re
        text = (work / 'answer.txt').read_text()
        pairs = re.findall(r'\[\s*([-0-9/ ^*]+?)\s*,\s*([-0-9/ ^*]+?)\s*\]', text)
        intervals = [(_msolve_number(a), _msolve_number(b)) for a, b in pairs]
        return self.finish(case, {}, len(intervals), intervals)


def _msolve_number(text):
    text = text.replace(' ', '')
    if '/' in text:
        numerator, denominator = text.split('/', 1)
        denominator = eval(denominator.replace('^', '**'), {})
        return Fraction(int(numerator), int(denominator))
    return Fraction(int(text))


TOOLS = [PolyMojoRoots(), FlintRoots(), FlintRoots(sturm=True), SymPyRoots(), MsolveRoots()]
NAMES = [t.name for t in TOOLS]
