"""Build and run the runtime suite in four sequential, cached batches.

Each test runs in its own process for failure isolation. Path filters select
execution only, so reruns reuse the same batch executables. Compiler-rejection
checks live in check_rejections.py and never run implicitly here.
"""
import argparse
from concurrent.futures import ThreadPoolExecutor, as_completed
import json
import os
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
from build_state import prepared_build
from packages import ROOT
from test_executable import prepare, CompilationFailed, source_inputs

VARIANTS = {}


def _first_line(path, prefix):
    lines = path.read_text().splitlines()
    return lines[0][len(prefix):].strip() if lines and lines[0].startswith(prefix) else None


def jobs(variant=None):
    """Return runtime cases: (label, source, expected stdout or None, defines)."""
    if variant is not None:
        if variant not in VARIANTS:
            raise SystemExit(f'unknown variant {variant!r}; known: {", ".join(sorted(VARIANTS))}')
        return [(f'{p} [{variant}]', ROOT / p, None, ('-D', f'TEST_VARIANT={variant}'))
                for p in sorted(VARIANTS[variant])]
    programs = [p for p in sorted(ROOT.glob('tests/**/test_*.mojo')) if p.parent.name != 'crosscheck']
    result = [(str(p.relative_to(ROOT)), p, None, ()) for p in programs]
    for path in sorted((ROOT / 'tests/compile').glob('*.mojo')):
        expected = _first_line(path, '# output:')
        if expected is None:
            raise ValueError(f'{path}: first line must be "# output: ..."')
        result.append((str(path.relative_to(ROOT)), path, expected, ()))
    for name in sorted(VARIANTS):
        result.extend(jobs(name))
    return result


def _run(job, executable, timeout):
    label, path, expected, _ = job
    result = executable.execute(path, ROOT, timeout)
    passed = result['returncode'] == 0
    detail = (result['stdout'] + result['stderr']).strip() if not passed else ''
    if passed and expected is not None and result['stdout'].strip() != expected:
        passed = False
        detail = f'printed {result["stdout"].strip()!r}, expected {expected!r}'
    return dict(name=label, passed=passed, detail=detail, seconds=result['seconds'])


def batches(inventory, count):
    """Spread neighboring tests across batches before applying execution filters."""
    if count < 1:
        raise ValueError('batch count must be positive')
    result = []
    for flags in sorted({job[3] for job in inventory}):
        group = sorted((job for job in inventory if job[3] == flags), key=lambda job: (job[1], job[0]))
        total = min(count, len(group))
        # Archive and CAD tests cluster by name and instantiate large generic
        # APIs. Interleave them instead of putting a whole family in one build.
        for index in range(total):
            result.append((flags, group[index::total]))
    return result


def _report(path, snapshot, records, *, complete, total, executables=(), compile_error=None):
    path.parent.mkdir(parents=True, exist_ok=True)
    record = dict(library_build=snapshot.report(), complete=complete, total=total,
                  passed=(not compile_error and len(records) == total and all(r['passed'] for r in records)) if complete else None,
                  executables=list(executables), records=records)
    if compile_error:
        record['compile_error'] = compile_error
    temporary = path.with_suffix('.tmp')
    temporary.write_text(json.dumps(record, indent=2) + '\n')
    temporary.replace(path)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--variant')
    parser.add_argument('--no-build', action='store_true', help=argparse.SUPPRESS)
    parser.add_argument('--build', default='build', help='Prepared library directory; never rebuilt by tests')
    parser.add_argument('--report', type=Path, default=ROOT / '.cache/tests/report.json')
    scope = parser.add_mutually_exclusive_group()
    scope.add_argument('--library-only', action='store_true', help='Exclude the optional kernel suite in tests/kernel/')
    scope.add_argument('--kernel-only', action='store_true', help='Compile only the optional kernel suite')
    parser.add_argument('--batches', type=int, default=4, help='Sequential builds per compiler configuration (default: 4)')
    parser.add_argument('--jobs', type=int, default=min(4, os.cpu_count() or 1), help='Test processes run at once within the current batch')
    parser.add_argument('--timeout', type=float, default=1800, help='Runtime timeout per test, in seconds (the Gröbner corpus takes about 10 minutes at O0)')
    parser.add_argument('--optimization', type=int, choices=(0, 1, 2, 3), default=0, help='Runtime suite optimization level (default: 0)')
    parser.add_argument('--compiler-threads', type=int, default=1, help='Threads in the single compiler process (default: 1, to limit peak memory)')
    parser.add_argument('--compile-timeout', type=float, help='Optional timeout for each batch compilation')
    parser.add_argument('pattern', nargs='?', help='Run matching cases from their cached batch executables')
    args = parser.parse_args()
    if args.batches < 1:
        parser.error('--batches must be positive')
    inventory = [j for j in jobs(args.variant)
                 if not (args.library_only and j[1].is_relative_to(ROOT / 'tests/kernel'))
                 and not (args.kernel_only and not j[1].is_relative_to(ROOT / 'tests/kernel'))]
    selected = [j for j in inventory if args.pattern is None or args.pattern in j[0]]
    if not selected:
        parser.error('No runtime tests match; use check_rejections.py for compiler-rejection cases')
    kernel = any(j[1].is_relative_to(ROOT / 'tests/kernel') for j in inventory)
    groups = batches(inventory, args.batches)
    records, reports, executables = [], [], []
    with prepared_build(args.build, kernel=kernel) as snapshot:
        print(f'Using library build {snapshot.identity}: {snapshot.path}', flush=True)
        _report(args.report, snapshot, records, complete=False, total=len(selected))
        for index, (flags, group) in enumerate(groups, start=1):
            active = [job for job in group if args.pattern is None or args.pattern in job[0]]
            if not active:
                continue
            print(f'Batch {index}/{len(groups)}: {len(group)} programs, {len(active)} selected', flush=True)
            try:
                executable = prepare([j[1] for j in group], snapshot, ROOT,
                                     flags=(*flags, f'-O{args.optimization}'), kernel=kernel,
                                     timeout=args.compile_timeout, compiler_threads=args.compiler_threads)
            except CompilationFailed as error:
                _report(args.report, snapshot, records, complete=True, total=len(selected),
                        executables=reports, compile_error=error.record)
                print(error, file=sys.stderr)
                return 1
            executables.append(executable)
            reports.append(executable.report())
            print('Reusing' if executable.reused else 'Built', executable.binary, flush=True)
            _report(args.report, snapshot, records, complete=False, total=len(selected), executables=reports)
            with ThreadPoolExecutor(max_workers=max(1, args.jobs)) as pool:
                pending = {pool.submit(_run, job, executable, args.timeout): job[0] for job in active}
                for future in as_completed(pending):
                    try:
                        record = future.result()
                    except Exception as error:
                        record = dict(name=pending[future], passed=False, detail=str(error), seconds=None)
                    records.append(record)
                    print(f"{'PASS' if record['passed'] else 'FAIL'} {record['name']} ({record['seconds']}s) [{len(records)}/{len(selected)}]", flush=True)
                    if not record['passed']:
                        print('\n'.join(line[:1000] for line in record['detail'].splitlines()[-40:]), flush=True)
                    _report(args.report, snapshot, records, complete=False, total=len(selected), executables=reports)
        for executable in executables:
            if source_inputs(ROOT, executable.programs) != executable.record['inputs']['sources']:
                raise RuntimeError('Test sources changed during execution; report remains incomplete')
    _report(args.report, snapshot, records, complete=True, total=len(selected), executables=reports)
    failed = sum(not r['passed'] for r in records)
    print(f'{len(records) - failed} passed, {failed} failed', flush=True)
    return bool(failed)


if __name__ == '__main__':
    raise SystemExit(main())
