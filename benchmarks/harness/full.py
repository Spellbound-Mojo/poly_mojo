"""Run all implemented benchmark families against one already prepared library.

Prepare packages once with the repository's `pixi run --locked build`. This
runner never builds packages. It locks and validates that build, compiles all
distinct drivers before measurement, and records compiler commands separately.
"""
import argparse
from contextlib import redirect_stderr, redirect_stdout
import datetime
import json
import os
from pathlib import Path
import subprocess
import sys

from . import cad, factor, generate, measure, real_roots, report, run, tools

FAMILIES = ('arith', 'gcd', 'series', 'factor', 'roots', 'cad', 'streaming', 'groebner')


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--results', type=Path, required=True, help='Directory for this complete run')
    parser.add_argument('--logs', type=Path, help='Log directory (default: results/logs)')
    parser.add_argument('--build-jobs', type=int, default=2)
    parser.add_argument('--cpu', type=int, default=max(os.sched_getaffinity(0)))
    parser.add_argument('--timeout', type=float, default=600)
    parser.add_argument('--allow-missing-memory', action='store_true')
    parser.add_argument('--prepare-only', action='store_true')
    args = parser.parse_args(argv)
    args.results = args.results.resolve()
    logs = (args.logs or args.results / 'logs').resolve()
    args.results.mkdir(parents=True, exist_ok=True)
    logs.mkdir(parents=True, exist_ok=True)
    phases = {}
    selected, all_cases = [], []
    for family, names in run.FAMILY_TOOLS.items():
        generate.main(['--family', family])
        registry = run.gcd_family.TOOLS if family == 'gcd' else tools.TOOLS
        selected.extend(registry[name] for name in names)
        cases = generate.load(family)
        all_cases.extend(cases)
        phases[family] = {'cases': len(cases), 'tools': names}
    factor.generate()
    cad.generate()
    factor_tools = list(factor.TOOLS.values())
    cad_tools = list(cad.TOOLS.values())
    selected.extend(factor_tools + cad_tools)
    phases['factor'] = {'cases': len(factor.load()), 'tools': list(factor.TOOLS)}
    phases['cad'] = {'cases': len(cad.load()), 'tools': list(cad.TOOLS)}
    libraries = tools.verify_poly_mojo(selected)
    if set(libraries) != {str((tools.ROOT / 'build').resolve())}:
        raise SystemExit('Full runs require every Poly Mojo adapter to use the shared build/ directory.')

    from build_state import build_lock
    commands = []
    measuring = False

    def audit(event, details):
        if event != 'subprocess.Popen':
            return
        executable, command, cwd, _ = details
        if not isinstance(command, (list, tuple)):
            return
        command = list(map(str, command))
        if 'precompile' in command or any(Path(a).name in ('build.py', 'deps.py') for a in command):
            raise RuntimeError('Package compilation is forbidden during a full benchmark run.')
        compiling = ('mojo' in command and 'build' in command) or Path(str(executable)).name in ('gcc', 'cc', 'clang')
        if compiling:
            if measuring:
                raise RuntimeError('A driver was not prepared before benchmark timing.')
            commands.append({'command': command, 'cwd': str(cwd),
                             'started': datetime.datetime.now(datetime.timezone.utc).isoformat()})

    sys.addaudithook(audit)
    manifest_path = args.results / 'suite.json'
    previous = json.loads(manifest_path.read_text()) if manifest_path.exists() else None
    if previous and previous['libraries'] != libraries:
        raise SystemExit('This results directory belongs to another library build.')
    manifest = previous or {'revision': tools.git_revision(), 'libraries': libraries,
                            'families': phases, 'driver_builds': [], 'completed': []}
    revision = tools.git_revision()
    if manifest.get('measurements_started') and manifest['revision'] != revision:
        raise SystemExit('This results directory contains measurements from another revision.')
    manifest['revision'] = revision
    group = measure.Cgroup.create(12 << 30)
    manifest['memory_limit_enforced'] = group is not None
    if group:
        group.remove()
    else:
        manifest['memory_note'] = 'No writable memory cgroup: the requested per-process 12 GiB cap is not enforced; whole-process memory figures are unavailable.'
    manifest['settings'] = {'cpu': args.cpu, 'timeout_s': args.timeout, 'min_seconds': 0.5,
                            'min_reps': 3, 'processes': 3, 'single_above_s': 1,
                            'allow_missing_memory': args.allow_missing_memory}

    def save():
        manifest_path.write_text(json.dumps(manifest, indent=2) + '\n')

    with build_lock(tools.ROOT / 'build'):
        assert tools.verify_poly_mojo(selected) == libraries
        save()
        generic = [t for t in selected if t not in factor_tools and t not in cad_tools]
        manifest['driver_builds'].extend(tools.prebuild(generic, all_cases, args.build_jobs))
        factor.TOOLS['polymojo'].build()
        pm = cad.TOOLS['polymojo-final']
        for n in sorted({len(c['variables']) for c in cad.load()}):
            if not pm.binary(n).is_file():
                path, seconds = pm.build(n)
                print(f'  built {path.name} in {seconds:.0f} s', flush=True)
        real_roots.flint_binary()
        manifest.setdefault('driver_compile_commands', []).extend(commands)
        manifest['package_compile_commands'] = 0
        assert tools.verify_poly_mojo(selected) == libraries
        save()
        print('All drivers ready; one unchanged shared library; no package compilation.', flush=True)
        if args.prepare_only:
            return 0

        measuring = True
        manifest['measurements_started'] = True
        save()
        for family in FAMILIES:
            folder = args.results / f'{args.results.name}-{family}'
            folder.mkdir(exist_ok=True)
            records = folder / 'records.jsonl'
            common = ['--results', str(records), '--timeout', str(args.timeout),
                      '--cpu', str(args.cpu), '--min-seconds', '0.5', '--min-reps', '3']
            print(f'Starting {family}; progress: {logs / (family + ".log")}', flush=True)
            with (logs / (family + '.log')).open('a', buffering=1) as log, redirect_stdout(log), redirect_stderr(log):
                if family == 'factor':
                    factor.main(['run', '--tools', ','.join(factor.TOOLS), *common])
                    factor.main(['report', str(folder)])
                elif family == 'cad':
                    cad.main(['run', *common])
                    cad.main(['report', str(folder)])
                else:
                    sys.argv = ['harness.run', '--family', family, *common,
                                '--processes', '3', '--single-above', '1', '--build-jobs', str(args.build_jobs)]
                    if args.allow_missing_memory:
                        sys.argv.append('--allow-missing-memory')
                    run.main()
                    sys.argv = ['harness.report', str(folder)]
                    report.main()
            assert tools.verify_poly_mojo(selected) == libraries
            if family not in manifest['completed']:
                manifest['completed'].append(family)
            save()
            print(f'Completed {family}', flush=True)
        manifest['complete'] = True
        assert tools.verify_poly_mojo(selected) == libraries
        save()
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
