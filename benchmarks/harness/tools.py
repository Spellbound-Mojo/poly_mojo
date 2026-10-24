"""Adapters that turn a case into a command for each benchmarked tool.

Each tool writes its inputs into a fresh work directory, names the command to
run, and afterwards reads the driver's timings and the computed basis back.
In-process tools (Poly Mojo, SymPy, Singular) time the call and measure its
incremental peak themselves; msolve is timed as a whole process, and its
baseline cost on a trivial system with the same variables is subtracted.
"""
from concurrent.futures import ThreadPoolExecutor, as_completed
from fractions import Fraction
import hashlib
import json
from math import lcm
import os
from pathlib import Path
import re
import subprocess

from . import measure
from .generate import generators
from .polys import format_infix, make, parse, read_records, write_records

HERE = Path(__file__).resolve().parent.parent
ROOT = HERE.parent
CACHE = HERE / '.cache'
MSOLVE = CACHE / 'opt' / 'msolve' / 'bin' / 'msolve'
MSOLVE_VERSION = '0.11.0'


def env_python():
    return str(Path(os.environ.get('CONDA_PREFIX', '')) / 'bin' / 'python')


def outside_environment():
    """The caller's environment without this workspace's activation.

    The Mojo toolchain must not see this environment's compilers and linker
    (conda-forge's sysroot predates the glibc symbols Mojo's runtime needs).
    """
    prefix = os.environ.get('CONDA_PREFIX', '')
    env = {k: v for k, v in os.environ.items()
           if not k.startswith(('CONDA_', 'PIXI_PROJECT', 'PIXI_ENVIRONMENT', 'PIXI_IN_SHELL'))
           and k not in ('CC', 'CXX', 'LD', 'AR', 'NM', 'RANLIB', 'CFLAGS', 'CXXFLAGS', 'CPPFLAGS', 'LDFLAGS',
                         'HOST', 'BUILD', 'build_alias', 'host_alias', 'CMAKE_ARGS', 'MESON_ARGS', 'PKG_CONFIG_PATH')}
    if prefix:
        env['PATH'] = os.pathsep.join(p for p in env.get('PATH', '').split(os.pathsep) if not p.startswith(prefix))
    return env


def library_dir(tool):
    """The library directory a Poly Mojo tool links: its own `library()` when it has one, else build/."""
    library = getattr(tool, 'library', None)
    return Path(library()).resolve() if library else (ROOT / 'build').resolve()


def verify_library(path):
    """The build_id of a library directory whose manifest matches the current src/; exits otherwise.

    Drivers link prebuilt packages, and records are labelled with the checked-out
    revision, so a library built from other sources would be measured under the
    wrong name. scripts/build_state.py's own check compares the manifest's input
    hashes with src/ and its artifact hashes with the packages.
    """
    import sys
    sys.path.insert(0, str(ROOT / 'scripts'))
    from build_state import validate
    saved = os.environ.get('PATH', '')
    # Its compiler check runs `mojo --version`, which lives in the workspace environment.
    os.environ['PATH'] = os.pathsep.join([str(ROOT / '.pixi' / 'envs' / 'default' / 'bin'), saved])
    try:
        return validate(Path(path).resolve()).identity
    except SystemExit as error:
        raise SystemExit(f'Poly Mojo library {path} does not match the checked-out sources ({error}). Rebuild it with '
                         '`pixi run --locked build`, or `python scripts/build.py --output DIR` for POLYMOJO_LIB, '
                         'before benchmarking.') from None
    finally:
        os.environ['PATH'] = saved


def verify_poly_mojo(selected):
    """Check every library the selected Poly Mojo tools link; return {directory: build_id}."""
    libraries = {}
    for tool in selected:
        if getattr(tool, 'system', '') == 'Poly Mojo':
            path = library_dir(tool)
            if str(path) not in libraries:
                libraries[str(path)] = verify_library(path)
    return libraries


def record_libraries(env_path, libraries):
    """Store the library builds in a results directory's environment.json, refusing to mix builds."""
    if not libraries:
        return
    env = json.loads(env_path.read_text())
    previous = env.get('poly_mojo_libraries')
    if previous and previous != libraries:
        raise SystemExit(f'{env_path.parent} holds results measured with library builds {previous}; this run links '
                         f'{libraries}. Use a new results directory.')
    env['poly_mojo_libraries'] = libraries
    env_path.write_text(json.dumps(env, indent=2) + '\n')


def zero_dimensional_lex(case):
    """Whether FGLM applies: a LEX case whose ideal is zero-dimensional.

    Cyclic-n is positive-dimensional when n has a square factor (4, 8, 9 on
    the ladders); FGLM tools then hang or return a wrong basis.
    """
    if case['order'] != 'lex':
        return False
    return not (case['system'] == 'cyclic' and case['size'] in (4, 8, 9, 12))


class Tool:
    name = system = algorithm = ''
    in_process = True

    def supports(self, case):
        return case['family'] == 'groebner'

    def version(self):
        return ''

    def prepare(self, case, work, settings):
        raise NotImplementedError

    def collect(self, case, work):
        """Return a dict with times_ns, peak and RSS figures, and the basis polynomials."""
        raise NotImplementedError

    def builds(self, cases):
        return []


# ---------------------------------------------------------------- Poly Mojo

def git_revision():
    head = subprocess.run(['git', 'rev-parse', 'HEAD'], cwd=ROOT, capture_output=True, text=True).stdout.strip()
    dirty = subprocess.run(['git', 'status', '--porcelain', '--', 'src'], cwd=ROOT, capture_output=True, text=True).stdout.strip()
    return head[:12] + ('+dirty' if dirty else '')


CHECK_ALLOWANCE = 600.0
"""Seconds certified Poly Mojo's check_groebner may take beyond the computation's time limit."""


class PolyMojo(Tool):
    system = 'Poly Mojo'
    algorithm = 'Buchberger'
    driver = HERE / 'drivers' / 'poly_mojo' / 'groebner.mojo'

    def __init__(self, certified=False, mode=None):
        # Modes: comparable (no witnesses), certified (witnesses and check),
        # uncertified (no witnesses, rational bases not certified).
        self.mode = mode or ('certified' if certified else 'comparable')
        self.certified = self.mode == 'certified'
        self.name = {'comparable': 'polymojo', 'certified': 'polymojo-certified',
                     'uncertified': 'polymojo-uncertified'}[self.mode]
        # The time limit covers the computation, which proves its own result
        # in certified mode; the independent check_groebner after it runs
        # under its own allowance, must pass, and is recorded as check_s.
        self.check_allowance = CHECK_ALLOWANCE if self.certified else 0.0

    def version(self):
        return git_revision()

    def binary(self, nvars, modular):
        manifest = (ROOT / 'build' / 'library-build.json').read_bytes()
        key = hashlib.sha256(self.driver.read_bytes() + manifest + f'{nvars}:{modular}'.encode()).hexdigest()[:16]
        return CACHE / 'bin' / f"pm_groebner_{nvars}_{'gf' if modular else 'qq'}_{key}"

    def build(self, nvars, modular):
        out = self.binary(nvars, modular)
        if out.is_file():
            return out, 0.0, None
        out.parent.mkdir(parents=True, exist_ok=True)
        cmd = [os.environ.get('PIXI_EXE', 'pixi'), 'run', '--manifest-path', str(ROOT / 'pixi.toml'), '--locked', 'mojo', 'build',
               '-I', str(ROOT / 'build'), '-D', f'NVARS={nvars}', '-D', f'MODULAR={int(modular)}',
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

    def prepare(self, case, work, settings):
        field = case['field']
        polys = generators(case)
        (work / 'input.txt').write_text(write_records(polys, len(case['variables']), field))
        binary = self.binary(len(case['variables']), field is not None)
        cmd = [str(binary), 'input.txt', 'answer.txt', 'result.json', case['order'],
               self.mode, str(field or 0),
               str(settings['min_seconds']), str(settings['min_reps'])]
        return cmd, os.environ.copy()

    def collect(self, case, work):
        result = json.loads((work / 'result.json').read_text())
        result['polys'] = read_records((work / 'answer.txt').read_bytes(), case['field'])
        return result


# -------------------------------------------------------------------- SymPy

class SymPy(Tool):
    system = 'SymPy'

    def __init__(self, method, ground_types):
        self.method, self.ground_types = method, ground_types
        self.algorithm = {'buchberger': 'Buchberger', 'f5b': 'F5B (signatures)', 'fglm': 'Buchberger (grevlex) + FGLM'}[method]
        self.name = f'sympy-{method}' + ('' if ground_types == 'gmpy' else f'-{ground_types}')

    def supports(self, case):
        return case['family'] == 'groebner' and (self.method != 'fglm' or zero_dimensional_lex(case))

    def version(self):
        import sympy
        return f'{sympy.__version__} ({self.ground_types} ground types)'

    def prepare(self, case, work, settings):
        (work / 'case.json').write_text(json.dumps(case))
        env = os.environ.copy()
        env['SYMPY_GROUND_TYPES'] = self.ground_types
        cmd = [env_python(), str(HERE / 'drivers' / 'python' / 'sympy_groebner.py'), 'case.json',
               'answer.json', 'result.json', self.method, str(settings['min_seconds']), str(settings['min_reps'])]
        return cmd, env

    def collect(self, case, work):
        result = json.loads((work / 'result.json').read_text())
        if result.pop('ground_types') != self.ground_types:
            raise RuntimeError('SymPy did not use the requested ground types')
        polys = json.loads((work / 'answer.json').read_text())['polys']
        result['polys'] = [make([(e, Fraction(c)) for e, c in p], case['field']) for p in polys]
        return result


# ----------------------------------------------------------------- Singular

SINGULAR_SCRIPT = '''\
system("--ticks-per-sec", 1000000);
{lib}
ring r = {characteristic}, ({variables}), {order};
option(redSB); option(redTail);
short = 0;
ideal I = {generators};
int pid = system("pid");
int rc = system("sh", "grep VmRSS /proc/" + string(pid) + "/status > rss.txt; echo 5 > /proc/" + string(pid) + "/clear_refs");
int t0 = rtimer;
ideal G = {call}(I);
int t1 = rtimer;
rc = system("sh", "grep VmHWM /proc/" + string(pid) + "/status > hwm.txt");
int total = t1 - t0;
int reps = 1;
string times = string(total);
ideal H;
if (total < {min_us}) {{
  while ((reps < {min_reps}) or (total < {min_us})) {{
    t0 = rtimer;
    H = {call}(I);
    t1 = rtimer;
    total = total + (t1 - t0);
    reps = reps + 1;
    times = times + "," + string(t1 - t0);
  }}
}}
write(":w times.txt", times);
G = interred(G);
write(":w answer.txt", G);
quit;
'''


class Singular(Tool):
    system = 'Singular'

    def __init__(self, call):
        self.call = call
        self.algorithm = {'std': 'Buchberger (std)', 'slimgb': 'slimgb', 'modStd': 'multimodular (modStd)', 'stdfglm': 'std (dp) + FGLM'}[call]
        self.name = f'singular-{call.lower()}'

    def supports(self, case):
        if self.call == 'stdfglm' and not zero_dimensional_lex(case):
            return False
        return case['family'] == 'groebner' and not (self.call == 'modStd' and case['field'] is not None)

    def version(self):
        return '4.4.1'

    def prepare(self, case, work, settings):
        variables = case['variables']
        polys = generators(case)
        script = SINGULAR_SCRIPT.format(
            lib='LIB "modstd.lib";' if self.call == 'modStd' else '',
            characteristic=case['field'] or 0, variables=','.join(variables),
            order={'grevlex': 'dp', 'lex': 'lp', 'grlex': 'Dp'}[case['order']],
            generators=', '.join(format_infix(p, variables, case['field'], case['order']) for p in polys),
            call=self.call, min_us=int(settings['min_seconds'] * 1e6), min_reps=settings['min_reps'])
        (work / 'run.sing').write_text(script)
        return ['Singular', '-q', '--no-warn', '--no-rc', 'run.sing'], os.environ.copy()

    def collect(self, case, work):
        kb = lambda name: int((work / name).read_text().split()[1])
        times = [int(t) * 1000 for t in (work / 'times.txt').read_text().strip().split(',')]
        text = (work / 'answer.txt').read_text()
        polys = [parse(p, case['variables'], case['field']) for p in text.split(',') if p.strip()]
        return {'times_ns': times, 'rss_before_kb': kb('rss.txt'), 'peak_kb': kb('hwm.txt'),
                'basis_length': len(polys), 'polys': polys}


# ------------------------------------------------------------------- msolve

class Msolve(Tool):
    name = 'msolve'
    system = 'msolve'
    algorithm = 'F4'
    in_process = False

    def supports(self, case):
        # msolve's orders are grevlex and two-block elimination orders; it has no lex order.
        return case['family'] == 'groebner' and case['order'] == 'grevlex'

    def version(self):
        return MSOLVE_VERSION

    @staticmethod
    def write_input(path, variables, polys, field):
        rows = []
        for p in polys:
            if field is None:
                scale = lcm(*(Fraction(c).denominator for c in p.values()))
                p = {e: c * scale for e, c in p.items()}
            rows.append(format_infix(p, variables, field, power='^'))
        path.write_text(','.join(variables) + '\n' + str(field or 0) + '\n' + ',\n'.join(rows) + '\n')

    def baseline_input(self, case, work):
        """A trivial system with the same variables and field: x_i - 1."""
        n = len(case['variables'])
        polys = [{tuple(int(i == j) for j in range(n)): 1, (0,) * n: -1} for i in range(n)]
        self.write_input(work / 'input.ms', case['variables'], [make(p.items(), case['field']) for p in polys], case['field'])
        return [str(MSOLVE), '-g', '2', '-t', '1', '-f', 'input.ms', '-o', 'answer.txt'], os.environ.copy()

    def prepare(self, case, work, settings):
        self.write_input(work / 'input.ms', case['variables'], generators(case), case['field'])
        return [str(MSOLVE), '-g', '2', '-t', '1', '-f', 'input.ms', '-o', 'answer.txt'], os.environ.copy()

    def collect(self, case, work):
        text = '\n'.join(line for line in (work / 'answer.txt').read_text().splitlines() if not line.startswith('#'))
        text = text.strip().rstrip(':').strip().lstrip('[').rstrip(']')
        polys = [parse(p, case['variables'], case['field']) for p in text.split(',') if p.strip()]
        return {'basis_length': len(polys), 'polys': polys}


class PolyMojoStream(PolyMojo):
    """Poly Mojo's streaming study: one mode of materialized or incremental output."""
    algorithm = 'Poly Mojo internal study'
    driver = HERE / 'drivers' / 'poly_mojo' / 'streaming.mojo'

    def __init__(self, mode):
        self.mode = mode
        self.name = f'polymojo-{mode}'
        self.algorithm = {'decompose': 'retained decomposition, unchecked',
                          'materialized': 'materialized result, then checked',
                          'streaming': 'streamed into an incremental checker'}[mode]

    def supports(self, case):
        return case['family'] == 'streaming' and (self.mode != 'decompose' or case['kind'] == 'cad')

    def binary(self, nvars, modular=False):
        manifest = (ROOT / 'build' / 'library-build.json').read_bytes()
        key = hashlib.sha256(self.driver.read_bytes() + manifest + f'{nvars}'.encode()).hexdigest()[:16]
        return CACHE / 'bin' / f'pm_streaming_{nvars}_{key}'

    def builds(self, cases):
        return sorted({(len(c['variables']), False) for c in cases if self.supports(c)})

    def prepare(self, case, work, settings):
        (work / 'input.txt').write_text(write_records(generators(case), len(case['variables']), None))
        cmd = [str(self.binary(len(case['variables']))), case['kind'], self.mode, 'input.txt', 'result.json',
               str(case['param'])]
        return cmd, os.environ.copy()

    def collect(self, case, work):
        result = json.loads((work / 'result.json').read_text())
        if not result['ok']:
            raise RuntimeError('the streaming driver reported a failed check')
        answer = {'count': result['count']}
        if case['kind'] == 'dump':
            answer['bytes'] = result['bytes']
        return {'times_ns': [result['time_ns']], 'rss_before_kb': result['rss_before_kb'],
                'peak_kb': result['peak_kb'], 'answer': answer, 'count': result['count'], 'bytes': result['bytes']}


TOOLS = {t.name: t for t in [
    PolyMojo(), PolyMojo(certified=True), PolyMojo(mode='uncertified'),
    PolyMojoStream('decompose'), PolyMojoStream('materialized'), PolyMojoStream('streaming'),
    SymPy('buchberger', 'gmpy'), SymPy('f5b', 'gmpy'), SymPy('buchberger', 'flint'), SymPy('fglm', 'gmpy'),
    Singular('std'), Singular('slimgb'), Singular('modStd'), Singular('stdfglm'),
    Msolve(),
]}
from . import real_roots as _real_roots  # noqa: E402 (the family module imports helpers above)
TOOLS |= {t.name: t for t in _real_roots.TOOLS}


def prebuild(tools, cases, jobs):
    """Compile every Poly Mojo driver the cases need before any timing starts."""
    pending = {}
    for tool in tools:
        for key in tool.builds(cases):
            # Tools sharing a driver binary build it once.
            pending.setdefault(tool.binary(*key), (tool, key))
    work = [(tool, key) for tool, key in pending.values() if not tool.binary(*key).is_file()]
    if not work:
        return []
    print(f'Building {len(work)} Poly Mojo drivers with {jobs} jobs', flush=True)
    results = [None] * len(work)
    with ThreadPoolExecutor(jobs) as pool:
        pending = {pool.submit(tool.build, *key): (i, key) for i, (tool, key) in enumerate(work)}
        for future in as_completed(pending):
            i, key = pending[future]
            result = future.result()
            results[i] = (key, result)
            path, seconds, rss = result
            print(f'  built {path.name} in {seconds:.0f} s', flush=True)
    return [{'nvars': k[0], 'modular': k[1], 'seconds': r[1], 'maxrss_kb': r[2]} for k, r in results]
