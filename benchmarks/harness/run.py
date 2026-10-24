"""Run benchmark cases and append one JSON record per (case, tool) to a results file.

Cases run in ladder order (increasing size). When a tool times out or runs out
of memory on a ladder, its larger instances on that ladder are recorded as
`skipped` rather than run, which bounds the cost of slow tools without hiding
where they stop. Existing records in the results file are kept, so an
interrupted run resumes where it stopped.

Repetition: the driver repeats calls under `--min-seconds` in-process until
`--min-reps` runs and `--min-seconds` have elapsed. Each case then runs in up
to `--processes` fresh processes; calls longer than `--single-above` seconds
run in one process only. Tools timed as whole processes (msolve) run short
cases in `--min-reps` processes instead. The record keeps the median of the
process medians.
"""
import argparse
import datetime
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import shutil
import socket
import statistics
import subprocess
import sys
import tempfile
import time
import traceback

from . import arith, generate, measure, tools
from . import gcd as gcd_family
from . import series as series_family
from .polys import canonical_basis, digest

HERE = Path(__file__).resolve().parent.parent
tools.TOOLS |= arith.TOOLS  # the arithmetic family's adapters live in their own module
tools.TOOLS |= series_family.TOOLS
FAMILY_TOOLS = {
    'groebner': ['polymojo', 'polymojo-certified', 'polymojo-uncertified', 'sympy-buchberger', 'sympy-f5b', 'sympy-buchberger-flint', 'sympy-fglm',
                 'singular-std', 'singular-slimgb', 'singular-modstd', 'singular-stdfglm', 'msolve'],
    'streaming': ['polymojo-decompose', 'polymojo-materialized', 'polymojo-streaming'],
    'roots': ['polymojo-roots', 'polymojo-roots-sturm', 'flint-roots', 'flint-roots-sturm', 'sympy-roots', 'msolve-roots',
              'polymojo-roots@flint-roots', 'polymojo-roots@msolve-roots'],
    'gcd': gcd_family.FAMILY_TOOLS,
    'arith': ['polymojo-arith', 'flint-arith', 'singular-arith', 'sympy-arith'],
    'series': series_family.FAMILY_TOOLS,
}


def environment():
    def read(cmd):
        try:
            return subprocess.run(cmd, capture_output=True, text=True, timeout=30).stdout.strip()
        except OSError:
            return ''
    lscpu = read(['lscpu'])
    model = re.search(r'Model name:\s*(.*)', lscpu)
    meminfo = Path('/proc/meminfo').read_text()
    os_release = dict(line.split('=', 1) for line in Path('/etc/os-release').read_text().splitlines() if '=' in line)
    return {
        'host': socket.gethostname(),
        'cpu': model[1] if model else platform.processor(),
        'cpus': os.cpu_count(),
        'memory_kib': int(re.search(r'MemTotal:\s*(\d+)', meminfo)[1]),
        'kernel': platform.release(),
        'os': os_release.get('PRETTY_NAME', '').strip('"'),
        'hypervisor': (re.search(r'Hypervisor vendor:\s*(.*)', lscpu) or [None, None])[1],
        'python': sys.version.split()[0],
        'versions': {name: tool.version() for name, tool in tools.TOOLS.items()},
        'lscpu': lscpu,
    }


def host_label():
    """A stable folder name for the machine, such as xeon-2.10ghz-4vcpu-kvm."""
    env = environment()
    cpu = re.sub(r'\((r|tm)\)|processor|cpu|intel|amd|@', ' ', env['cpu'].lower())
    parts = cpu.split() + [f"{env['cpus']}vcpu"] + ([env['hypervisor'].lower()] if env['hypervisor'] else [])
    return re.sub(r'[^a-z0-9.]+', '-', '-'.join(parts)).strip('-')


def case_hash(case):
    return hashlib.sha256(json.dumps(case, separators=(',', ':'), sort_keys=True).encode()).hexdigest()


def outcome_of(process):
    if process.timed_out:
        return 'timeout'
    if process.oom:
        return 'out-of-memory'
    if process.returncode != 0:
        return 'error'
    return 'ok'


def run_case(tool, case, settings, baseline):
    """Run a case in up to `processes` fresh processes and summarize."""
    medians, mins, reps, first = [], [], 0, None
    index = 0
    while index < settings['processes'] or (not tool.in_process and medians and index < settings['min_reps']
                                             and statistics.median(medians) < settings['min_seconds']):
        index += 1
        work = Path(tempfile.mkdtemp(prefix='bench-', dir=settings['scratch']))
        try:
            cmd, env = tool.prepare(case, work, settings)
            # A tool whose check follows its computation gets the check's
            # allowance on top; the computation alone must fit the limit.
            process = measure.run(cmd, cwd=work, env=env, timeout_s=settings['timeout'] + getattr(tool, 'check_allowance', 0.0),
                                  memory_bytes=settings['memory'], cpu=settings['cpu'],
                                  stdout=work / 'stdout.txt', stderr=work / 'stderr.txt')
            outcome = outcome_of(process)
            record = {'outcome': outcome, 'process': process.as_dict()}
            if outcome != 'ok':
                tail = (work / 'stderr.txt').read_text(errors='replace')[-2000:] + (work / 'stdout.txt').read_text(errors='replace')[-1000:]
                record['error'] = tail.strip()
                return record
            result = tool.collect(case, work)
            if tool.in_process and min(result['times_ns']) / 1e9 > settings['timeout']:
                return {'outcome': 'timeout', 'process': process.as_dict()}
        except Exception:
            return {'outcome': 'error', 'error': traceback.format_exc()[-2000:]}
        finally:
            if not settings['keep']:
                shutil.rmtree(work, ignore_errors=True)
        if tool.in_process:
            times = result['times_ns']
            per_call = statistics.median(times) / 1e9
            mins.append(min(times) / 1e9)
            reps += len(times)
        else:
            per_call = max(process.wall_s - baseline['wall_s'], 0.0)
            mins.append(per_call)
            reps += 1
        medians.append(per_call)
        if first is None:
            first = (process, result)
        # Long calls need no repetition; short external calls repeat as processes.
        if per_call > settings['single_above']:
            break
    process, result = first
    record = {
        'outcome': 'ok',
        'time_s': statistics.median(medians),
        'time_min_s': min(mins),
        'reps': reps,
        'processes': len(medians),
        # ru_maxrss from wait4 inherits the forked harness's high-water mark, so
        # total peaks come from the driver's own VmHWM or from the run's cgroup.
        'peak_total_kib': result['peak_kb'] if tool.in_process else process.cgroup_peak_kb,
        'cgroup_peak_kib': process.cgroup_peak_kb,
        'process': process.as_dict(),
    }
    if 'polys' in result:
        rows = canonical_basis(result['polys'], case['order'], case['field'])
        record |= {'basis_length': len(rows), 'basis_terms': sum(len(r) for r in rows)}
    else:
        rows = result['answer']
        record |= {k: result[k] for k in ('count', 'bytes', 'widths', 'matched_bits') if k in result}
        if result.get('check_ok') is False:
            record['outcome'] = 'wrong'
    record['answer_digest'] = digest(rows)
    if tool.in_process:
        record['peak_incremental_kib'] = result['peak_kb'] - result['rss_before_kb']
    else:
        peak, base_peak = process.cgroup_peak_kb, baseline['cgroup_peak_kb']
        record['peak_incremental_kib'] = max(peak - base_peak, 0) if peak is not None and base_peak is not None else None
        if record['peak_incremental_kib'] is None:
            record['memory_note'] = 'Whole-process peak unavailable: no writable memory cgroup.'
        record['baseline'] = baseline
    if 'check_ns' in result and result.get('check_ns'):
        record['check_s'] = result['check_ns'] / 1e9
        if 'check_peak_kb' in result:
            record['check_peak_incremental_kib'] = result['check_peak_kb'] - result['rss_before_kb']
        record['check_ok'] = result['check_ok']
        if not result['check_ok']:
            record['outcome'] = 'wrong'
    answer = settings['answers'] / case['id'] / f'{tool.name}.json'
    answer.parent.mkdir(parents=True, exist_ok=True)
    answer.write_text(json.dumps(rows))
    return record


def baseline_for(tool, case, settings, cache):
    """Whole-process cost of an external tool on a trivial system with the same shape."""
    if tool.in_process:
        return None
    key = (tool.name, len(case['variables']), case['field'])
    if key not in cache:
        samples = []
        for _ in range(3):
            work = Path(tempfile.mkdtemp(prefix='bench-base-', dir=settings['scratch']))
            cmd, env = tool.baseline_input(case, work)
            p = measure.run(cmd, cwd=work, env=env, timeout_s=60, memory_bytes=settings['memory'],
                            cpu=settings['cpu'], stdout=work / 'stdout.txt', stderr=work / 'stderr.txt')
            samples.append(p)
            shutil.rmtree(work, ignore_errors=True)
        missing = any(p.cgroup_peak_kb is None for p in samples)
        if missing and not settings.get('allow_missing_memory', False):
            raise SystemExit('Measuring a whole-process tool needs a writable memory cgroup. '
                             'Use --allow-missing-memory to retain timings with unavailable memory figures.')
        cache[key] = {'wall_s': statistics.median(p.wall_s for p in samples),
                      'cgroup_peak_kb': None if missing else int(statistics.median(p.cgroup_peak_kb for p in samples))}
    return cache[key]


def parse_size(text):
    units = {'K': 10, 'M': 20, 'G': 30}
    return int(float(text[:-1]) * (1 << units[text[-1].upper()])) if text[-1].upper() in units else int(text)


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('--family', default='groebner', choices=sorted(FAMILY_TOOLS))
    parser.add_argument('--tools', help='Comma-separated tool names (default: every tool for the family)')
    parser.add_argument('--cases', default='', help='Regular expression on case ids')
    parser.add_argument('--results', type=Path, help='Results JSONL file (default results/<host>/<date>-<family>/records.jsonl)')
    parser.add_argument('--host', help='Folder name for the host (default: derived from the CPU)')
    parser.add_argument('--timeout', type=float, default=600)
    parser.add_argument('--memory', default='12G', help='Per-run memory cap')
    parser.add_argument('--allow-missing-memory', action='store_true',
                        help='Allow whole-process timings without cgroups; memory figures remain unavailable')
    parser.add_argument('--cpu', type=int, default=(os.cpu_count() or 1) - 1, help='CPU to pin runs to')
    parser.add_argument('--min-seconds', type=float, default=1.0)
    parser.add_argument('--min-reps', type=int, default=5)
    parser.add_argument('--processes', type=int, default=3)
    parser.add_argument('--single-above', type=float, default=60.0, help='Calls longer than this run in one process')
    parser.add_argument('--build-jobs', type=int, default=3)
    parser.add_argument('--build-only', action='store_true')
    parser.add_argument('--keep', action='store_true', help='Keep work directories')
    args = parser.parse_args()

    registry = gcd_family.TOOLS if args.family == 'gcd' else tools.TOOLS
    selected = [registry[name] for name in (args.tools.split(',') if args.tools else FAMILY_TOOLS[args.family])]
    generate.main(['--family', args.family])
    cases = [c for c in generate.load(args.family) if re.search(args.cases, c['id'])]
    libraries = tools.verify_poly_mojo(selected)
    builds = tools.prebuild(selected, cases, args.build_jobs)
    if args.build_only:
        return 0

    results = args.results or HERE / 'results' / (args.host or host_label()) / f'{datetime.date.today().isoformat()}-{args.family}' / 'records.jsonl'
    results.parent.mkdir(parents=True, exist_ok=True)
    env_path = results.parent / 'environment.json'
    if not env_path.exists():
        env_path.write_text(json.dumps(environment(), indent=2) + '\n')
    tools.record_libraries(env_path, libraries)
    if builds:
        with open(results.parent / 'builds.jsonl', 'a') as f:
            for b in builds:
                f.write(json.dumps(b) + '\n')
    # The file is append-only and the last record for a (case, tool) wins. A timeout or
    # skip recorded under a shorter limit is not final: rerunning with a longer
    # --timeout retries exactly those instances and continues their ladders.
    done = {}
    if results.exists():
        for line in results.read_text().splitlines():
            r = json.loads(line)
            done[(r['case'], r['tool'])] = r
    done = {k: r for k, r in done.items()
            if not (r['outcome'] in ('timeout', 'skipped') and r['timeout_s'] < args.timeout)}

    settings = {
        'timeout': args.timeout, 'memory': parse_size(args.memory), 'cpu': args.cpu,
        'min_seconds': args.min_seconds, 'min_reps': args.min_reps, 'processes': args.processes,
        'single_above': args.single_above, 'keep': args.keep,
        'allow_missing_memory': args.allow_missing_memory,
        'scratch': HERE / '.cache' / 'work', 'answers': HERE / '.cache' / 'answers' / results.parent.name,
    }
    settings['scratch'].mkdir(parents=True, exist_ok=True)
    for tool in selected:
        if hasattr(tool, 'bind_results'):
            tool.bind_results(results)
    stopped = {(r['tool'], r['ladder']) for r in done.values() if r['outcome'] in ('timeout', 'out-of-memory')}
    baselines = {}
    with open(results, 'a') as out:
        for case in cases:
            for tool in selected:
                key = (case['id'], tool.name)
                if key in done:
                    continue
                base = {'case': case['id'], 'case_sha256': case_hash(case), 'family': case['family'],
                        'ladder': case['ladder'], 'system': case['system'],
                        'size': case['size'], 'field': case['field'], 'order': case['order'],
                        'nvars': len(case['variables']), 'tool': tool.name, 'library': tool.system,
                        'algorithm': tool.algorithm, 'version': tool.version(),
                        'timeout_s': args.timeout, 'memory_cap': args.memory,
                        'started': datetime.datetime.now(datetime.timezone.utc).isoformat(timespec='seconds')}
                from .proofs import metadata
                base.update(metadata(tool, case))
                if not tool.supports(case):
                    record = {'outcome': 'unsupported'}
                elif (tool.name, case['ladder']) in stopped:
                    record = {'outcome': 'skipped', 'reason': 'a smaller instance on this ladder hit a limit'}
                else:
                    record = run_case(tool, case, settings, baseline_for(tool, case, settings, baselines))
                    if record['outcome'] in ('timeout', 'out-of-memory'):
                        stopped.add((tool.name, case['ladder']))
                record = base | record
                out.write(json.dumps(record) + '\n')
                out.flush()
                summary = f"{record['outcome']:>13}"
                if record['outcome'] == 'ok':
                    peak = record['peak_incremental_kib']
                    memory = f'{peak / 1024:9.1f} MiB' if peak is not None else 'memory unavailable'
                    summary += f"  {record['time_s']:10.4f} s  {memory}"
                print(f"{case['id']:<34} {tool.name:<24} {summary}", flush=True)
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
