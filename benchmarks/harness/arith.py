"""The arithmetic family: dense univariate and sparse multivariate products, powers, and exact quotients.

Dense cases multiply two seeded random polynomials of degree n with
coefficients of a given size, square the first, or divide their product by
the second, over ZZ and over GF(p). Sparse cases use Fateman's
f = (1 + x + y + z + t)^n with f·(f + 1), and the Monagan–Pearce product
(1 + x + y + 2z² + 3t³ + 5u⁵)^12 · (1 + u + t + 2z² + 3y³ + 5x⁵)^12, each as a
product, an exact quotient of the product by its second factor, and the power
that builds the first factor.

Case files hold only the parameters; the adapters write the operands at
preparation time. Every driver reads the same input file:

    {"kind": ..., "op": ..., "modulus": ..., "nvars": ..., "operands": k, ...}   (JSON header)
    kind op modulus nvars exponent second                                       (the same, for Mojo)
    count, then count lines per operand

Dense operand lines hold one hexadecimal coefficient each, from degree zero.
Sparse operand lines hold `e0 ... e(n-1) coefficient`. Sparse operands are the
bases: drivers build f = base^exponent and g = f + second operand (`shift`)
or g = second operand^exponent (`power`) before the timer starts, and every
driver builds the product it divides before the timer starts. Answers use the
same line formats; the harness reduces them to a digest of the sorted terms.
"""
import hashlib
import json
import os
import random
from pathlib import Path

from . import tools
from .polys import format_infix, parse, read_record

# GF(p) primes: 8 bits, and the largest prime below 2^62 (Poly Mojo's ModInt
# bound; nmod_poly takes primes below 2^64). Singular accepts only p < 2^31.
SMALL_PRIME = 251
LARGE_PRIME = 2 ** 62 - 57
DENSE_DEGREES = [100, 1000, 10000, 100000]
DENSE_DOMAINS = [('ZZ', 8), ('ZZ', 64), ('ZZ', 1024), (f'GF{SMALL_PRIME}', 8), (f'GF{LARGE_PRIME}', 62)]
DENSE_OPS = ['mul', 'sqr', 'div']
FATEMAN = [10, 15, 20, 30]
SPARSE_OPS = ['mul', 'div', 'pow']


def dense_operands(case):
    """Two seeded random polynomials of degree n, as coefficient lists from degree zero."""
    rng = random.Random(f"dense-{case['domain']}-{case['size']}")
    p, bits, n = case['field'], case['bits'], case['size']

    def coefficient():
        if p:
            return rng.randrange(p)
        return rng.getrandbits(bits) * rng.choice((1, -1))

    out = []
    for _ in range(2):
        c = [coefficient() for _ in range(n + 1)]
        while not c[-1]:
            c[-1] = coefficient()
        out.append(c)
    return out


def fateman(n):
    """f = (1 + x + y + z + t)^n and g = f + 1, as bases."""
    base = {(0, 0, 0, 0): 1, (1, 0, 0, 0): 1, (0, 1, 0, 0): 1, (0, 0, 1, 0): 1, (0, 0, 0, 1): 1}
    return [base, {(0, 0, 0, 0): 1}], 'shift'


def monagan_pearce(n):
    """(1 + x + y + 2z^2 + 3t^3 + 5u^5)^n and (1 + u + t + 2z^2 + 3y^3 + 5x^5)^n over x, y, z, t, u."""
    f = {(0,) * 5: 1, (1, 0, 0, 0, 0): 1, (0, 1, 0, 0, 0): 1, (0, 0, 2, 0, 0): 2, (0, 0, 0, 3, 0): 3, (0, 0, 0, 0, 5): 5}
    g = {(0,) * 5: 1, (0, 0, 0, 0, 1): 1, (0, 0, 0, 1, 0): 1, (0, 0, 2, 0, 0): 2, (0, 3, 0, 0, 0): 3, (5, 0, 0, 0, 0): 5}
    return [f, g], 'power'


SPARSE = {'fateman': (fateman, FATEMAN, 4), 'mp': (monagan_pearce, [12], 5)}


def cases():
    for domain, bits in DENSE_DOMAINS:
        field = int(domain[2:]) if domain.startswith('GF') else None
        for op in DENSE_OPS:
            for n in DENSE_DEGREES:
                yield {
                    'id': f'dense-{op}-{domain}-{bits}b-n{n}' if field is None else f'dense-{op}-{domain}-n{n}',
                    'family': 'arith', 'kind': 'dense', 'op': op, 'domain': domain if field else f'ZZ{bits}',
                    'system': f'dense-{op}', 'size': n, 'bits': bits,
                    'ladder': f'dense-{op}.{domain}' + ('' if field else f'-{bits}b') + '.dense',
                    'field': field, 'order': 'dense', 'variables': ['x0'],
                    'source': 'seeded random coefficients',
                }
    for system, (build, sizes, nvars) in SPARSE.items():
        for op in SPARSE_OPS:
            for n in sizes:
                yield {
                    'id': f'{system}-{op}-n{n}', 'family': 'arith', 'kind': 'sparse', 'op': op,
                    'system': f'{system}-{op}', 'size': n, 'ladder': f'{system}-{op}.ZZ.lex',
                    'field': None, 'order': 'lex', 'variables': [f'x{i}' for i in range(nvars)],
                    'source': {'fateman': "Fateman's benchmark, f·(f + 1)",
                               'mp': 'Monagan and Pearce, sparse product of two 12th powers'}[system],
                }


def operands(case):
    """(operand list, header dict) for a case."""
    header = {'kind': case['kind'], 'op': case['op'], 'modulus': case['field'] or 0,
              'nvars': len(case['variables']), 'exponent': 0, 'second': '-'}
    if case['kind'] == 'dense':
        ops = dense_operands(case)
    else:
        build, _, _ = SPARSE[case['system'].split('-')[0]]
        ops, second = build(case['size'])
        header |= {'exponent': case['size'], 'second': second}
    header['operands'] = len(ops)
    return ops, header


def write_input(case, path):
    ops, header = operands(case)
    lines = [json.dumps(header), ' '.join(str(header[k]) for k in ('kind', 'op', 'modulus', 'nvars', 'exponent', 'second'))]
    for o in ops:
        if case['kind'] == 'dense':
            lines += [str(len(o))] + [f'{c:x}' for c in o]
        else:
            lines += [str(len(o))] + [' '.join(map(str, e)) + f' {c:x}' for e, c in sorted(o.items())]
    path.write_text('\n'.join(lines) + '\n')
    return ops, header


def answer_digest(case, terms):
    """A digest of the canonical answer: dense coefficient lists, or sparse terms sorted by exponent."""
    h = hashlib.sha256()
    if case['kind'] == 'dense':
        while terms and not terms[-1]:
            terms.pop()
        for c in terms:
            h.update(f'{c:x}\n'.encode())
        count = len(terms)
    else:
        items = sorted((e, c) for e, c in terms.items() if c)
        for e, c in items:
            h.update((' '.join(map(str, e)) + f' {c:x}\n').encode())
        count = len(items)
    return {'terms': count, 'sha256': h.hexdigest()}


def read_answer(case, path):
    """Parse a driver's answer file into dense coefficients or a sparse term dict, reduced into the field."""
    lines = path.read_text().split('\n')
    count = int(lines[0])
    p = case['field']
    if case['kind'] == 'dense':
        values = [int(t, 16) for t in lines[1:1 + count]]
        return [v % p for v in values] if p else values
    terms = {}
    for line in lines[1:1 + count]:
        *exps, c = line.split()
        terms[tuple(int(e) for e in exps)] = int(c, 16) % p if p else int(c, 16)
    return terms


class ArithTool(tools.Tool):
    def supports(self, case):
        return case['family'] == 'arith'

    def collect(self, case, work):
        result = json.loads((work / 'result.json').read_text())
        answer = answer_digest(case, read_answer(case, work / 'answer.txt'))
        return result | {'answer': answer, 'count': answer['terms']}


class PolyMojoArith(ArithTool, tools.PolyMojo):
    system = 'Poly Mojo'
    # Dense cases have one variable; sparse cases have four or five.
    drivers = {'dense': tools.HERE / 'drivers' / 'poly_mojo' / 'arith_dense.mojo',
               'sparse': tools.HERE / 'drivers' / 'poly_mojo' / 'arith_sparse.mojo'}

    def driver_for(self, nvars):
        return self.drivers['dense' if nvars == 1 else 'sparse']

    def __init__(self):
        self.mode = 'comparable'
        self.certified = False
        self.name = 'polymojo-arith'

    algorithm = 'Karatsuba (dense), heap (sparse)'

    @staticmethod
    def library():
        """The library build to compile against: POLY_MOJO_LIB, or the repository's build/."""
        return Path(os.environ.get('POLY_MOJO_LIB', tools.ROOT / 'build'))

    def binary(self, nvars, modular):
        lib = self.library()
        manifest_path = lib / 'library-build.json'
        manifest = manifest_path.read_bytes() if manifest_path.exists() else b''.join(
            f'{f.name}:{f.stat().st_size}:{f.stat().st_mtime_ns}'.encode() for f in sorted(lib.glob('*.mojoc')))
        key = hashlib.sha256(self.driver_for(nvars).read_bytes() + manifest + f'{nvars}:{modular}'.encode()).hexdigest()[:16]
        return tools.CACHE / 'bin' / f"pm_arith_{nvars}_{'gf' if modular else 'zz'}_{key}"

    def build(self, nvars, modular):
        out = self.binary(nvars, modular)
        if out.is_file():
            return out, 0.0, None
        out.parent.mkdir(parents=True, exist_ok=True)
        cmd = [os.environ.get('PIXI_EXE', 'pixi'), 'run', '--manifest-path', str(tools.ROOT / 'pixi.toml'), '--locked', 'mojo',
               'build', '-I', str(self.library()), '-D', f'NVARS={nvars}', '-D', f'MODULAR={int(modular)}',
               str(self.driver_for(nvars)), '-o', str(out) + '.tmp']
        log = tools.CACHE / 'logs' / f'{out.name}.build.log'
        log.parent.mkdir(parents=True, exist_ok=True)
        result = tools.measure.run(cmd, cwd=tools.ROOT, env=tools.outside_environment(), timeout_s=3600, memory_bytes=None,
                                   cpu=None, stdout=log, stderr=log)
        if result.returncode != 0:
            raise SystemExit(f'Poly Mojo driver build failed; see {log}')
        os.replace(str(out) + '.tmp', out)
        return out, result.wall_s, result.maxrss_kb

    def builds(self, cases):
        return sorted({(len(c['variables']), c['field'] is not None) for c in cases if self.supports(c)})

    def collect(self, case, work):
        if case['kind'] == 'dense':
            return super().collect(case, work)
        # Sparse answers are the canonical `sparse.dumps` record.
        result = json.loads((work / 'result.json').read_text())
        poly = read_record((work / 'answer.txt').read_text(), case['field'])
        answer = answer_digest(case, {e: int(c) for e, c in poly.items()})
        return result | {'answer': answer, 'count': answer['terms']}

    def prepare(self, case, work, settings):
        write_input(case, work / 'input.txt')
        binary = self.binary(len(case['variables']), case['field'] is not None)
        return [str(binary), 'input.txt', 'answer.txt', 'result.json',
                str(settings['min_seconds']), str(settings['min_reps'])], os.environ.copy()


class PythonArith(ArithTool):
    def __init__(self, library, ground_types='gmpy'):
        self.library = library
        self.ground_types = ground_types
        self.name = 'flint-arith' if library == 'flint' else 'sympy-arith'
        self.system = 'FLINT' if library == 'flint' else 'SymPy'
        self.algorithm = ('fmpz_poly / nmod_poly / fmpz_mpoly' if library == 'flint'
                          else 'sympy.polys.rings (dup/dmp)')

    def version(self):
        if self.library == 'flint':
            import flint
            return f'python-flint {flint.__version__}, FLINT {flint.__FLINT_VERSION__}'
        import sympy
        return f'{sympy.__version__} ({self.ground_types} ground types)'

    def prepare(self, case, work, settings):
        write_input(case, work / 'input.txt')
        env = os.environ.copy()
        env['SYMPY_GROUND_TYPES'] = self.ground_types
        return [tools.env_python(), str(tools.HERE / 'drivers' / 'python' / 'arith.py'), self.library,
                'input.txt', 'answer.txt', 'result.json', str(settings['min_seconds']), str(settings['min_reps'])], env


SINGULAR_ARITH = '''\
system("--ticks-per-sec", 1000000);
ring r = {characteristic}, ({variables}), lp;
short = 0;
{operands}
{setup}
int pid = system("pid");
int rc = system("sh", "grep VmRSS /proc/" + string(pid) + "/status > rss.txt; echo 5 > /proc/" + string(pid) + "/clear_refs");
int t0 = rtimer;
poly R = {call};
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
{check}
write(":w answer.txt", R);
quit;
'''


class SingularArith(ArithTool):
    name = 'singular-arith'
    system = 'Singular'
    algorithm = 'Singular polynomial arithmetic'

    def supports(self, case):
        return case['family'] == 'arith' and (case['field'] is None or case['field'] < 2 ** 31)

    def version(self):
        return '4.4.1'

    def prepare(self, case, work, settings):
        ops, header = operands(case)
        variables = case['variables']
        p = case['field']
        if case['kind'] == 'dense':
            ops = [{(i,): c for i, c in enumerate(o) if c} for o in ops]
        text = [f'poly A = {format_infix(ops[0], variables, p, "lex")};',
                f'poly B = {format_infix(ops[1], variables, p, "lex")};']
        setup, check = '', ''
        op = case['op']
        if case['kind'] == 'sparse':
            n = case['size']
            setup = f'poly F = A^{n};\npoly G = ' + ('F + B;' if header['second'] == 'shift' else f'B^{n};')
            first, second = ('F', 'G')
        else:
            first, second = ('A', 'B')
        if op == 'pow':
            call = f'A^{case["size"]}'
        elif op == 'sqr':
            call = 'A*A'
        elif op == 'mul':
            call = f'{first}*{second}'
        else:
            setup += f'\npoly P = {first}*{second};'
            call = f'P/{second}'
            check = f'if (R != {first}) {{ ERROR("quotient differs from the first factor"); }}'
        script = SINGULAR_ARITH.format(characteristic=p or 0, variables=','.join(variables), operands='\n'.join(text),
                                       setup=setup, call=call, check=check,
                                       min_us=int(settings['min_seconds'] * 1e6), min_reps=settings['min_reps'])
        (work / 'run.sing').write_text(script)
        return ['Singular', '-q', '--no-warn', '--no-rc', 'run.sing'], os.environ.copy()

    def collect(self, case, work):
        kb = lambda name: int((work / name).read_text().split()[1])
        times = [int(t) * 1000 for t in (work / 'times.txt').read_text().strip().split(',')]
        poly = parse((work / 'answer.txt').read_text(), case['variables'], case['field'])
        poly = {e: int(c) for e, c in poly.items()}
        if case['kind'] == 'dense':
            degree = max((e[0] for e in poly), default=-1)
            terms = [0] * (degree + 1)
            for e, c in poly.items():
                terms[e[0]] = c
        else:
            terms = poly
        answer = answer_digest(case, terms)
        return {'times_ns': times, 'rss_before_kb': kb('rss.txt'), 'peak_kb': kb('hwm.txt'),
                'answer': answer, 'count': answer['terms']}


TOOLS = {t.name: t for t in [PolyMojoArith(), PythonArith('flint'), PythonArith('sympy'), SingularArith()]}
FAMILY_TOOLS = list(TOOLS)


# ------------------------------------------------------------------ report

def report(records, env, folder):
    from .report import LABEL, cell, fmt_time, geomean, memory_limit
    labels = {'polymojo-arith': 'Poly Mojo', 'flint-arith': 'FLINT', 'sympy-arith': 'SymPy', 'singular-arith': 'Singular'}
    LABEL.update(labels)
    present = [t for t in labels if any(r['tool'] == t for r in records)]
    index = {(r['case'], r['tool']): r for r in records}
    by_ladder = {}
    for r in records:
        by_ladder.setdefault(r['ladder'], {}).setdefault(r['size'], {})[r['tool']] = r
    competitors = [t for t in present if t != 'polymojo-arith']
    lines = ['# Arithmetic results', '',
             f"Host: {env['cpu']}, {env['cpus']} vCPUs, {env['memory_kib'] / 1048576:.0f} GiB RAM. "
             f"Runs are pinned to one CPU with a {records[0]['timeout_s']:.0f} s time limit. "
             + memory_limit(records), '',
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
                a, b = tools_.get(t), tools_.get('polymojo-arith')
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
              'skipped after a smaller one on the same ladder hit a limit; `n/a` marks an unsupported field.', '']
    for ladder in sorted(by_ladder):
        lines += [f'### {ladder.rsplit(".", 1)[0]}', '', '| n | ' + ' | '.join(labels[t] for t in present) + ' |',
                  '|---|' + '---|' * len(present)]
        for size in sorted(by_ladder[ladder]):
            lines.append(f'| {size} | ' + ' | '.join(cell(by_ladder[ladder][size].get(t)) for t in present) + ' |')
        lines.append('')
    (folder / 'report.md').write_text('\n'.join(lines) + '\n')
    return folder / 'report.md'
