"""The series family: truncated power series, multipoint evaluation, interpolation, and evaluation at a rational.

Four kinds of case, each over the fields the operation needs:

- `series`: truncated products and the series inverse, square root,
  logarithm, exponential, integer power, composition, and reversion to order
  n, over QQ (n = 10², 10³, 10⁴) and GF(p) (n = 10³, 10⁴, 10⁵). Inputs have
  small seeded integer coefficients; the constant term is 1 where the
  operation needs a unit (inverse, square root, logarithm, power) and 0 where
  it needs a nilpotent (exponential, the inner series of a composition, a
  reversion, which also takes the linear coefficient 1).
- `multipoint`: a degree n − 1 polynomial at n distinct points, over ZZ
  (32-bit coefficients and points) and GF(p).
- `interp`: the polynomial of degree below n through n distinct nodes, over
  QQ (integer nodes from ±n, 16-bit values) and GF(p).
- `evalq`: a degree n integer polynomial with 64-bit coefficients at a
  rational point a/b with 64-bit a and b.

Every driver reads the same input file:

    {"kind": ..., "op": ..., "modulus": ..., "n": ..., "exponent": ..., "operands": k}   (JSON header)
    kind op modulus n exponent                                                       (the same, for Mojo and C)
    count, then count lines per operand: one hexadecimal integer each, from degree zero

and writes its answer as a count line and one value per line: a hexadecimal
integer, or a fraction `numerator/denominator` in hexadecimal. The harness
reduces answers to a canonical text (integers reduced modulo p, fractions in
lowest terms with a positive denominator) and compares digests.
"""
import hashlib
import json
import os
import random
import subprocess
from fractions import Fraction
from pathlib import Path

from . import tools

PRIME = 2 ** 62 - 57  # the largest prime below Poly Mojo's ModInt bound; nmod_poly takes it as well
SERIES_OPS = ['mul', 'inv', 'sqrt', 'log', 'exp', 'pow', 'compose', 'revert']
POWER = 5
SIZES = {
    ('series', 'QQ'): [100, 1000, 10000],
    ('series', 'GF'): [1000, 10000, 100000],
    ('multipoint', 'ZZ'): [100, 1000, 10000],
    ('multipoint', 'GF'): [1000, 10000, 100000],
    ('interp', 'QQ'): [100, 1000, 10000],
    ('interp', 'GF'): [1000, 10000, 100000],
    ('evalq', 'ZZ'): [1000, 10000, 100000],
}
NAMES = {'series': 'series', 'multipoint': 'multipoint evaluation', 'interp': 'interpolation',
         'evalq': 'evaluation at a rational'}


def cases():
    for (kind, domain), sizes in SIZES.items():
        ops = SERIES_OPS if kind == 'series' else [kind]
        field = PRIME if domain == 'GF' else None
        label = f'GF{PRIME}' if field else domain
        for op in ops:
            for n in sizes:
                name = f'{kind}-{op}' if kind == 'series' else kind
                yield {
                    'id': f'{name}-{label}-n{n}', 'family': 'series', 'kind': kind, 'op': op, 'domain': domain,
                    'system': name, 'size': n, 'ladder': f'{name}.{label}.dense', 'field': field,
                    'order': 'dense', 'variables': ['x0'], 'source': 'seeded random coefficients',
                }


def _rng(case, part):
    return random.Random(f"series-{case['id']}-{part}")


def _small(rng, bits):
    return rng.randrange(-(1 << (bits - 1)), 1 << (bits - 1))


def operands(case):
    """(operand list, header dict) for a case; operands are lists of integers."""
    kind, op, n, p = case['kind'], case['op'], case['size'], case['field']
    header = {'kind': kind, 'op': op, 'modulus': p or 0, 'n': n, 'exponent': POWER if op == 'pow' else 0}

    def coefficients(part, constant=None, linear=None):
        rng = _rng(case, part)
        c = [rng.randrange(p) if p else _small(rng, 8) for _ in range(n)]
        if constant is not None:
            c[0] = constant
        if linear is not None and n > 1:
            c[1] = linear
        return c

    def distinct(part, count, bits):
        rng = _rng(case, part)
        if p:
            return rng.sample(range(1, p), count) if count < 10 ** 6 else None
        seen, out = set(), []
        while len(out) < count:
            x = _small(rng, bits)
            if x not in seen:
                seen.add(x)
                out.append(x)
        return out

    if kind == 'series':
        if op == 'mul':
            ops = [coefficients('f'), coefficients('g')]
        elif op in ('inv', 'sqrt', 'log', 'pow'):
            ops = [coefficients('f', constant=1)]
        elif op == 'exp':
            ops = [coefficients('f', constant=0)]
        elif op == 'compose':
            ops = [coefficients('f'), coefficients('g', constant=0)]
        else:  # revert
            ops = [coefficients('g', constant=0, linear=1)]
    elif kind == 'multipoint':
        rng = _rng(case, 'f')
        f = [rng.randrange(p) if p else _small(rng, 32) for _ in range(n)]
        ops = [f, distinct('x', n, 32)]
    elif kind == 'interp':
        if p:
            xs = distinct('x', n, 0)
        else:
            xs = _rng(case, 'x').sample(range(-n, n + 1), n)
        rng = _rng(case, 'y')
        ys = [rng.randrange(p) if p else _small(rng, 16) for _ in range(n)]
        ops = [xs, ys]
    else:  # evalq: f of degree n and the point a/b
        rng = _rng(case, 'f')
        f = [_small(rng, 64) for _ in range(n + 1)]
        f[-1] = f[-1] or 1
        a = _small(rng, 64) or 1
        b = rng.randrange(2, 1 << 63)
        ops = [f, [a, b]]
    header['operands'] = len(ops)
    return ops, header


def _hex(v):
    return f'-{-v:x}' if v < 0 else f'{v:x}'


def write_input(case, path):
    ops, header = operands(case)
    lines = [json.dumps(header), ' '.join(str(header[k]) for k in ('kind', 'op', 'modulus', 'n', 'exponent'))]
    for o in ops:
        lines += [str(len(o))] + [_hex(c) for c in o]
    path.write_text('\n'.join(lines) + '\n')
    return ops, header


def _value(text):
    if '/' in text:
        num, den = text.split('/')
        return Fraction(int(num, 16), int(den, 16))
    return int(text, 16)


def answer_digest(case, path):
    """The count and SHA-256 of the canonical answer text."""
    lines = path.read_text().split('\n')
    count = int(lines[0])
    p = case['field']
    h = hashlib.sha256()
    for line in lines[1:1 + count]:
        v = _value(line.strip())
        if p:
            if isinstance(v, Fraction):
                v = v.numerator * pow(v.denominator, -1, p)
            text = f'{v % p:x}'
        else:
            v = Fraction(v)
            text = _hex(v.numerator) if v.denominator == 1 else f'{_hex(v.numerator)}/{v.denominator:x}'
        h.update(text.encode() + b'\n')
    return {'terms': count, 'sha256': h.hexdigest()}


class SeriesTool(tools.Tool):
    unsupported = set()

    def supports(self, case):
        return case['family'] == 'series' and (case['kind'], case['op'], case['domain']) not in self.unsupported

    def collect(self, case, work):
        result = json.loads((work / 'result.json').read_text())
        answer = answer_digest(case, work / 'answer.txt')
        return result | {'answer': answer, 'count': answer['terms']}


class PolyMojoSeries(SeriesTool, tools.PolyMojo):
    system = 'Poly Mojo'
    algorithm = 'poly.series, poly.dense'
    driver = tools.HERE / 'drivers' / 'poly_mojo' / 'series.mojo'
    # Series powers and square roots have no public Poly Mojo call yet.
    unsupported = {('series', 'pow', d) for d in ('QQ', 'GF')} | {('series', 'sqrt', d) for d in ('QQ', 'GF')}

    def __init__(self):
        self.mode = 'comparable'
        self.certified = False
        self.name = 'polymojo-series'

    @staticmethod
    def library():
        """The library build to compile against: POLY_MOJO_LIB, or the repository's build/."""
        return Path(os.environ.get('POLY_MOJO_LIB', tools.ROOT / 'build'))

    def binary(self, nvars, modular):
        lib = self.library()
        manifest_path = lib / 'library-build.json'
        manifest = manifest_path.read_bytes() if manifest_path.exists() else b''.join(
            f'{f.name}:{f.stat().st_size}:{f.stat().st_mtime_ns}'.encode() for f in sorted(lib.glob('*.mojoc')))
        key = hashlib.sha256(self.driver.read_bytes() + manifest + f'{modular}'.encode()).hexdigest()[:16]
        return tools.CACHE / 'bin' / f"pm_series_{'gf' if modular else 'qq'}_{key}"

    def build(self, nvars, modular):
        out = self.binary(nvars, modular)
        if out.is_file():
            return out, 0.0, None
        out.parent.mkdir(parents=True, exist_ok=True)
        cmd = [os.environ.get('PIXI_EXE', 'pixi'), 'run', '--manifest-path', str(tools.ROOT / 'pixi.toml'), '--locked', 'mojo',
               'build', '-I', str(self.library()), '-D', f'MODULAR={int(modular)}', str(self.driver), '-o', str(out) + '.tmp']
        log = tools.CACHE / 'logs' / f'{out.name}.build.log'
        log.parent.mkdir(parents=True, exist_ok=True)
        result = tools.measure.run(cmd, cwd=tools.ROOT, env=tools.outside_environment(), timeout_s=3600, memory_bytes=None,
                                   cpu=None, stdout=log, stderr=log)
        if result.returncode != 0:
            raise SystemExit(f'Poly Mojo driver build failed; see {log}')
        os.replace(str(out) + '.tmp', out)
        return out, result.wall_s, result.maxrss_kb

    def builds(self, cases):
        return sorted({(1, c['field'] is not None) for c in cases if self.supports(c)})

    def prepare(self, case, work, settings):
        write_input(case, work / 'input.txt')
        binary = self.binary(1, case['field'] is not None)
        return [str(binary), 'input.txt', 'answer.txt', 'result.json',
                str(settings['min_seconds']), str(settings['min_reps'])], os.environ.copy()


def flint_binary():
    """Compile the FLINT C driver against the workspace's libflint (cached by source hash)."""
    source = tools.HERE / 'drivers' / 'flint' / 'series.c'
    prefix = Path(os.environ.get('CONDA_PREFIX', tools.HERE / '.pixi' / 'envs' / 'default'))
    key = hashlib.sha256(source.read_bytes()).hexdigest()[:16]
    out = tools.CACHE / 'bin' / f'flint_series_{key}'
    if not out.is_file():
        out.parent.mkdir(parents=True, exist_ok=True)
        subprocess.run([os.environ.get('CC_FOR_DRIVER', 'gcc'), '-O2', str(source), '-o', str(out),
                        f'-I{prefix}/include', f'-L{prefix}/lib', f'-Wl,-rpath,{prefix}/lib', '-lflint', '-lgmp', '-lmpfr'],
                       check=True)
    return out


class FlintSeries(SeriesTool):
    name = 'flint-series'
    system = 'FLINT'
    algorithm = 'fmpq_poly / nmod_poly *_series, fast multipoint evaluation and interpolation'

    def version(self):
        prefix = Path(os.environ.get('CONDA_PREFIX', tools.HERE / '.pixi' / 'envs' / 'default'))
        text = (prefix / 'include' / 'flint' / 'flint.h').read_text()
        import re
        parts = [re.search(rf'#define __FLINT_VERSION{s}\s+(\d+)', text) for s in ('', '_MINOR', '_PATCHLEVEL')]
        return 'FLINT ' + '.'.join(m[1] for m in parts if m) + ' (C, conda-forge libflint)'

    def prepare(self, case, work, settings):
        write_input(case, work / 'input.txt')
        return [str(flint_binary()), 'input.txt', 'answer.txt', 'result.json',
                str(settings['min_seconds']), str(settings['min_reps'])], os.environ.copy()


class SympySeries(SeriesTool):
    name = 'sympy-series'
    system = 'SymPy'
    algorithm = 'sympy.polys.ring_series, ring evaluation, polyfuncs.interpolate'

    unsupported = {('interp', 'interp', 'GF')}  # polyfuncs.interpolate works over QQ only

    def __init__(self, ground_types='gmpy'):
        self.ground_types = ground_types

    def version(self):
        import sympy
        return f'{sympy.__version__} ({self.ground_types} ground types)'

    def prepare(self, case, work, settings):
        write_input(case, work / 'input.txt')
        env = os.environ.copy()
        env['SYMPY_GROUND_TYPES'] = self.ground_types
        return [tools.env_python(), str(tools.HERE / 'drivers' / 'python' / 'series.py'),
                'input.txt', 'answer.txt', 'result.json', str(settings['min_seconds']), str(settings['min_reps'])], env


TOOLS = {t.name: t for t in [PolyMojoSeries(), FlintSeries(), SympySeries()]}
FAMILY_TOOLS = list(TOOLS)


# ------------------------------------------------------------------ report

def report(records, env, folder):
    from .report import LABEL, cell, geomean
    labels = {'polymojo-series': 'Poly Mojo', 'flint-series': 'FLINT', 'sympy-series': 'SymPy'}
    LABEL.update(labels)
    present = [t for t in labels if any(r['tool'] == t for r in records)]
    by_ladder = {}
    for r in records:
        by_ladder.setdefault(r['ladder'], {}).setdefault(r['size'], {})[r['tool']] = r
    competitors = [t for t in present if t != 'polymojo-series']
    lines = ['# Series, evaluation, and interpolation results', '',
             f"Host: {env['cpu']}, {env['cpus']} vCPUs, {env['memory_kib'] / 1048576:.0f} GiB RAM. "
             f"Runs are pinned to one CPU, capped at {records[0]['memory_cap']} and {records[0]['timeout_s']:.0f} s.", '',
             'Versions: ' + '; '.join(f"{labels[t]} {env['versions'].get(t, '')}" for t in present) + '.', '',
             '## Summary', '',
             'Geometric mean of competitor time ÷ Poly Mojo time over cases both solved with a confirmed answer '
             'and where the slower took at least 10 ms (above 1 means Poly Mojo was faster).', '',
             '| Ladder | ' + ' | '.join(labels[t] for t in competitors) + ' |',
             '|---|' + '---|' * len(competitors)]
    for ladder in sorted(by_ladder):
        row = []
        for t in competitors:
            values = []
            for size, tools_ in by_ladder[ladder].items():
                a, b = tools_.get(t), tools_.get('polymojo-series')
                if (a and b and a['outcome'] == b['outcome'] == 'ok' and a.get('agreement') == b.get('agreement') == 'confirmed'
                        and max(a['time_s'], b['time_s']) >= 0.01):
                    values.append(a['time_s'] / max(b['time_s'], 1e-4))
            g = geomean(values)
            row.append(f'{g:.3g} (*n* = {len(values)})' if g else '—')
        lines.append(f'| {ladder.rsplit(".", 1)[0]} | ' + ' | '.join(row) + ' |')
    issues = [r for r in records if r.get('agreement') == 'disagreeing']
    lines += ['', '## Answer agreement', '']
    if issues:
        lines += [f"- {r['case']}: {labels[r['tool']]} `{r['answer_digest'][:12]}`" for r in issues]
    else:
        lines.append('Every answer that two or more libraries computed agrees.')
    lines += ['', '## Per-ladder results', '',
              'Each cell gives the median time per call and the incremental peak memory; `·` marks an instance '
              'skipped after a smaller one on the same ladder hit a limit; `n/a` marks an unsupported operation.', '']
    for ladder in sorted(by_ladder):
        lines += [f'### {ladder.rsplit(".", 1)[0]}', '', '| n | ' + ' | '.join(labels[t] for t in present) + ' |',
                  '|---|' + '---|' * len(present)]
        for size in sorted(by_ladder[ladder]):
            lines.append(f'| {size} | ' + ' | '.join(cell(by_ladder[ladder][size].get(t)) for t in present) + ' |')
        lines.append('')
    (folder / 'report.md').write_text('\n'.join(lines) + '\n')
    return folder / 'report.md'
