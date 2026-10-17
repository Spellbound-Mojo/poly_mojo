"""Check answers across tools and write the Markdown report and plots for a result set.

Usage: python -m harness.report [RESULTS_DIR]  (default: the newest results/<host>/<date>)

Agreement: within each case, every successful answer is reduced to a canonical
digest. A digest returned by two or more different libraries is *confirmed*;
a record whose digest differs from a confirmed one is *disagreeing*; a record
no other library could check is *unverified*. Summary ratios use only cases
where both tools agree on a confirmed answer.
"""
import argparse
from collections import Counter, defaultdict
import json
import math
from pathlib import Path
import statistics

HERE = Path(__file__).resolve().parent.parent
BASE = 'polymojo'
RATIO_FLOOR_S = 0.01      # a ratio needs the slower tool to take at least this long
MEMORY_FLOOR_KIB = 1024   # and, for memory, at least this much incremental peak

TOOL_ORDER = ['polymojo', 'polymojo-certified', 'polymojo-uncertified', 'sympy-buchberger', 'sympy-f5b', 'sympy-buchberger-flint',
              'sympy-fglm', 'singular-std', 'singular-slimgb', 'singular-modstd', 'singular-stdfglm', 'msolve']
LABEL = {
    'polymojo': 'Poly Mojo', 'polymojo-certified': 'Poly Mojo (certified)',
    'polymojo-uncertified': 'Poly Mojo (uncertified)',
    'sympy-buchberger': 'SymPy Buchberger', 'sympy-f5b': 'SymPy F5B',
    'sympy-buchberger-flint': 'SymPy Buchberger (flint types)', 'sympy-fglm': 'SymPy FGLM',
    'singular-std': 'Singular std', 'singular-slimgb': 'Singular slimgb',
    'singular-modstd': 'Singular modStd', 'singular-stdfglm': 'Singular stdfglm', 'msolve': 'msolve',
}
SHORT = {'timeout': 'timeout', 'out-of-memory': 'OOM', 'error': 'error', 'skipped': '·',
         'unsupported': 'n/a', 'wrong': 'wrong'}


def load(folder):
    latest = {}
    for line in (folder / 'records.jsonl').read_text().splitlines():
        if line.strip():
            r = json.loads(line)
            latest[(r['case'], r['tool'])] = r   # a later record supersedes an earlier one
    records = list(latest.values())
    env = json.loads((folder / 'environment.json').read_text())
    return records, env


def agreement(records):
    """Mark each ok record as confirmed, disagreeing, or unverified."""
    by_case = defaultdict(list)
    for r in records:
        if r['outcome'] == 'ok':
            by_case[r['case']].append(r)
    issues = []
    for case, rows in by_case.items():
        libraries = defaultdict(set)
        for r in rows:
            libraries[r['answer_digest']].add(r['library'])
        confirmed = {d for d, libs in libraries.items() if len(libs) >= 2}
        for r in rows:
            if r['answer_digest'] in confirmed:
                r['agreement'] = 'confirmed'
            elif confirmed:
                r['agreement'] = 'disagreeing'
                issues.append(r)
            else:
                r['agreement'] = 'unverified'
    return issues


def fmt_time(seconds):
    if seconds < 1e-3:
        return '< 1 ms'
    if seconds < 1:
        return f'{seconds * 1e3:.3g} ms'
    if seconds < 100:
        return f'{seconds:.3g} s'
    return f'{seconds:.0f} s'


def fmt_mem(kib):
    if kib is None:
        return ''
    if kib < 1024:
        return '< 1 MiB'
    mib = kib / 1024
    return f'{mib:.3g} MiB' if mib < 1024 else f'{mib / 1024:.3g} GiB'


def cell(r, memory=True):
    if r is None:
        return ''
    if r['outcome'] != 'ok':
        return SHORT.get(r['outcome'], r['outcome'])
    text = fmt_time(r['time_s'])
    if memory:
        text += f"<br>{fmt_mem(r['peak_incremental_kib'])}"
    if r.get('agreement') == 'disagreeing':
        text += ' ✗'
    elif r.get('agreement') == 'unverified':
        text += ' ?'
    return text


def geomean(values):
    return math.exp(statistics.fmean(math.log(v) for v in values)) if values else None


def ratios(records, tools, floor_key, floor):
    """Geometric-mean ratio competitor / Poly Mojo per (field, order) group and tool."""
    index = {(r['case'], r['tool']): r for r in records}
    groups = defaultdict(lambda: defaultdict(list))
    solved = defaultdict(Counter)
    cases = defaultdict(set)
    for r in records:
        group = ('QQ' if r['field'] is None else f"GF({r['field']})", r['order'])
        cases[group].add(r['case'])
        if r['outcome'] == 'ok' and r.get('agreement') != 'disagreeing':
            solved[group][r['tool']] += 1
        elif r['outcome'] != 'unsupported':
            solved[group][r['tool']] += 0
        if r['tool'] == BASE or r['outcome'] != 'ok' or r.get('agreement') != 'confirmed':
            continue
        base = index.get((r['case'], BASE))
        if not base or base['outcome'] != 'ok' or base.get('agreement') != 'confirmed':
            continue
        a, b = r[floor_key], base[floor_key]
        if max(a, b) < floor:
            continue
        groups[group][r['tool']].append(max(a, floor / 100) / max(b, floor / 100))
    return groups, solved, Counter({g: len(c) for g, c in cases.items()})


def summary_table(records, tools, key, floor, title):
    groups, solved, totals = ratios(records, tools, key, floor)
    competitors = [t for t in tools if t not in (BASE, 'polymojo-certified', 'polymojo-uncertified')]
    lines = [f'**{title}** (geometric mean of competitor ÷ Poly Mojo; above 1 means Poly Mojo used less; *n* = cases compared)', '',
             '| Field, order | ' + ' | '.join(LABEL[t] for t in competitors) + ' |',
             '|---|' + '---|' * len(competitors)]
    for group in sorted(totals):
        row = []
        for t in competitors:
            values = groups[group].get(t, [])
            g = geomean(values)
            row.append(f'{g:.3g} (*n* = {len(values)})' if g else '—')
        lines.append(f'| {group[0]}, {group[1]} | ' + ' | '.join(row) + ' |')
    return lines, solved, totals


def solved_table(solved, totals, tools):
    lines = ['| Field, order | ' + ' | '.join(LABEL[t] for t in tools) + ' |',
             '|---|' + '---|' * len(tools)]
    for group in sorted(totals):
        lines.append(f'| {group[0]}, {group[1]} | ' + ' | '.join(
            f'{solved[group][t]}/{totals[group]}' if t in solved[group] else 'n/a' for t in tools) + ' |')
    return lines


def ladder_tables(records, tools):
    by_ladder = defaultdict(lambda: defaultdict(dict))
    for r in records:
        by_ladder[r['ladder']][r['size']][r['tool']] = r
    out = []
    for ladder in sorted(by_ladder, key=lambda l: (l.split('.')[2], l.split('.')[1], l.split('.')[0])):
        system, field, order = ladder.split('.')
        rows = by_ladder[ladder]
        out += [f'#### {system}-n over {field.replace("GF", "GF(") + (")" if field.startswith("GF") else "")}, {order}', '',
                '| n | vars | ' + ' | '.join(LABEL[t] for t in tools) + ' |',
                '|---|---|' + '---|' * len(tools)]
        for size in sorted(rows):
            any_row = next(iter(rows[size].values()))
            out.append(f"| {size} | {any_row['nvars']} | " + ' | '.join(cell(rows[size].get(t)) for t in tools) + ' |')
        out.append('')
    return out


def certification(records):
    index = {(r['case'], r['tool']): r for r in records}
    lines = ['| Case | Comparable | Certified compute | Check | Certified peak ÷ comparable peak |',
             '|---|---|---|---|---|']
    count = 0
    for r in records:
        if r['tool'] != 'polymojo-certified' or r['outcome'] != 'ok':
            continue
        base = index.get((r['case'], BASE))
        if not base or base['outcome'] != 'ok' or max(r['time_s'], base['time_s']) < RATIO_FLOOR_S:
            continue
        mem = (r['peak_incremental_kib'] / base['peak_incremental_kib']) if base['peak_incremental_kib'] >= MEMORY_FLOOR_KIB else None
        lines.append(f"| {r['case']} | {fmt_time(base['time_s'])} | {fmt_time(r['time_s'])} | {fmt_time(r.get('check_s', 0))} | "
                     f"{f'{mem:.3g}' if mem else '—'} |")
        count += 1
    return lines if count else ['No case took long enough for a meaningful certification comparison.']


def plots(records, tools, folder):
    import matplotlib
    matplotlib.use('Agg')
    import matplotlib.pyplot as plt
    by_ladder = defaultdict(lambda: defaultdict(list))
    for r in records:
        if r['outcome'] == 'ok' and r.get('agreement') != 'disagreeing':
            by_ladder[r['ladder']][r['tool']].append(r)
    names = []
    for ladder, per_tool in sorted(by_ladder.items()):
        fig, (left, right) = plt.subplots(1, 2, figsize=(11, 4))
        for t in tools:
            rows = sorted(per_tool.get(t, []), key=lambda r: r['size'])
            if not rows:
                continue
            sizes = [r['size'] for r in rows]
            left.plot(sizes, [max(r['time_s'], 1e-5) for r in rows], marker='o', label=LABEL[t])
            right.plot(sizes, [max(r['peak_incremental_kib'] / 1024, 0.01) for r in rows], marker='o', label=LABEL[t])
        for ax, ylabel in ((left, 'time (s)'), (right, 'incremental peak memory (MiB)')):
            ax.set_yscale('log')
            ax.set_xlabel('n')
            ax.set_ylabel(ylabel)
            ax.grid(True, which='both', alpha=0.3)
        left.set_title(ladder)
        right.legend(fontsize=7, loc='upper left')
        fig.tight_layout()
        name = f'plot-{ladder}.svg'
        fig.savefig(folder / name)
        plt.close(fig)
        names.append(name)
    return names


def write_report(folder):
    records, env = load(folder)
    issues = agreement(records)
    if records and records[0].get('family') == 'streaming':
        return streaming_report(records, env, folder)
    present = {r['tool'] for r in records}
    tools = [t for t in TOOL_ORDER if t in present]
    time_lines, solved, totals = summary_table(records, tools, 'time_s', RATIO_FLOOR_S, 'Time')
    for r in records:
        r.setdefault('peak_incremental_kib', 0)
    memory_lines, _, _ = summary_table(records, tools, 'peak_incremental_kib', MEMORY_FLOOR_KIB, 'Incremental peak memory')
    outcomes = Counter(r['outcome'] for r in records)
    lines = [
        '# Gröbner basis pilot results', '',
        f"Host: {env['cpu']}, {env['cpus']} vCPUs ({env.get('hypervisor') or 'bare metal'}), "
        f"{env['memory_kib'] / 1048576:.0f} GiB RAM, {env['os']}, Linux {env['kernel']}. "
        'Every run is pinned to one CPU and single-threaded, capped at '
        f"{records[0]['memory_cap']} of memory and {records[0]['timeout_s']:.0f} s.", '',
        'Versions: ' + '; '.join(f"{LABEL[t]} {env['versions'][t]}" for t in tools) + '.', '',
        f"Records: {len(records)} ({', '.join(f'{v} {k}' for k, v in sorted(outcomes.items()))}).", '',
        '## Summary', '',
        f'Ratios cover cases that both tools solved with a confirmed answer and on which the slower of the two took '
        f'at least {RATIO_FLOOR_S * 1000:.0f} ms (memory: at least {MEMORY_FLOOR_KIB // 1024} MiB). '
        'Poly Mojo runs in comparable mode (no witnesses).', '',
        *time_lines, '', *memory_lines, '',
        '**Solved cases** (finished within the limits with an answer no other library contradicts):', '',
        *solved_table(solved, totals, tools), '',
        '## Answer agreement', '',
    ]
    if issues:
        lines += ['| Case | Tool | Digest |', '|---|---|---|']
        lines += [f"| {r['case']} | {LABEL[r['tool']]} | `{r['answer_digest'][:12]}` |" for r in issues]
    else:
        lines.append('Every answer that two or more libraries computed agrees.')
    unverified = sorted({r['case'] for r in records if r.get('agreement') == 'unverified'})
    if unverified:
        lines += ['', 'Answers computed by only one library (marked ? in the tables): ' + ', '.join(unverified) + '.']
    lines += ['', '## Certification overhead', '',
              'Comparable mode computes without witnesses. Certified mode retains cofactor rows and runs '
              '`sparse.check_groebner`, which verifies both ideal containments and the Buchberger criterion.', '',
              *certification(records), '',
              '## Per-ladder results', '',
              'Each cell gives the median time per call and the incremental peak memory. `·` marks an instance '
              'skipped after a smaller one on the same ladder hit a limit; `n/a` marks an unsupported order or field.', '',
              *ladder_tables(records, tools)]
    names = plots(records, tools, folder)
    lines += ['## Plots', ''] + [f'![{n}]({n})' for n in names]
    (folder / 'report.md').write_text('\n'.join(lines) + '\n')
    return folder / 'report.md'


STREAM_MODES = ['polymojo-decompose', 'polymojo-materialized', 'polymojo-streaming']
STREAM_LABEL = {'polymojo-decompose': 'Retained, unchecked', 'polymojo-materialized': 'Retained, then checked',
                'polymojo-streaming': 'Streamed into checker'}
STREAM_UNIT = {'cad': 'cells', 'roots': 'roots', 'dump': 'terms', 'load': 'terms'}
STREAM_TITLE = {
    'cad.lines': 'CAD of k random lines (`cad.decompose` + `cad.check` against `cad.decompose_to` + `cad.checker`)',
    'cad.circles': 'CAD of k random circles',
    'cad.planes': 'CAD of k random planes in three variables',
    'roots.wilkinson': 'Real roots of the Wilkinson polynomial of degree n to 64 bits (`real_root_cover` + `roots.check` against `real_root_cover_to` + checker)',
    'roots.chebyshev': 'Real roots of the Chebyshev polynomial T_n to 64 bits',
    'dump.fateman': 'Write (1 + x + y + z + t)^n as text (`sparse.dumps` to a file against `sparse.dump` into a file sink)',
    'load.fateman': 'Read (1 + x + y + z + t)^n back (`sparse.loads` of the whole file against `sparse.load` from a file source)',
}


def streaming_report(records, env, folder):
    by_ladder = defaultdict(lambda: defaultdict(dict))
    for r in records:
        # All modes are Poly Mojo; agreement here means equal counts, shown in the count column.
        r.pop('agreement', None)
        by_ladder[r['ladder']][r['size']][r['tool']] = r
    lines = ['# Streaming study', '',
             f"Host: {env['cpu']}, {env['cpus']} vCPUs, {env['memory_kib'] / 1048576:.0f} GiB RAM. "
             f"Runs are pinned to one CPU, capped at {records[0]['memory_cap']} and {records[0]['timeout_s']:.0f} s. "
             f"Poly Mojo {env['versions'].get('polymojo', '')}.", '',
             'Each cell gives wall time and the incremental peak resident memory of the measured work: the '
             'high-water mark from just before the call to its end, minus the resident size before it. Both '
             'checked routes establish the same claim; the streamed route never holds the complete output.', '']
    for ladder in sorted(by_ladder, key=lambda l: list(STREAM_TITLE).index(l) if l in STREAM_TITLE else 99):
        kind = ladder.split('.')[0]
        modes = [m for m in STREAM_MODES if any(m in row for row in by_ladder[ladder].values())]
        lines += [f'### {STREAM_TITLE.get(ladder, ladder)}', '',
                  f'| size | {STREAM_UNIT[kind]} | ' + ' | '.join(STREAM_LABEL[m] for m in modes) + ' | checked peak ÷ streamed peak |',
                  '|---|---|' + '---|' * (len(modes) + 1)]
        for size, row in sorted(by_ladder[ladder].items()):
            counts = {r.get('count') for r in row.values() if r['outcome'] == 'ok'}
            count = '; '.join(f'{c:,}' for c in sorted(counts)) if counts else ''
            if len(counts) > 1:
                count += ' ✗'
            cells = [cell(row.get(m)) for m in modes]
            a, b = row.get('polymojo-materialized'), row.get('polymojo-streaming')
            ratio = ''
            if a and b and a['outcome'] == b['outcome'] == 'ok' and b['peak_incremental_kib'] > 0:
                ratio = f"{a['peak_incremental_kib'] / b['peak_incremental_kib']:.3g}×"
            elif a and b and b['outcome'] == 'ok' and a['outcome'] != 'ok':
                ratio = f"checked route: {SHORT.get(a['outcome'], a['outcome'])}"
            lines.append(f'| {size} | {count} | ' + ' | '.join(cells) + f' | {ratio} |')
        lines.append('')
    import matplotlib
    matplotlib.use('Agg')
    import matplotlib.pyplot as plt
    ladders = sorted(by_ladder)
    fig, axes = plt.subplots(1, len(ladders), figsize=(4 * len(ladders), 3.6), squeeze=False)
    for ax, ladder in zip(axes[0], ladders):
        for m in STREAM_MODES:
            pts = sorted((r['count'], r['peak_incremental_kib'] / 1024) for row in by_ladder[ladder].values()
                         for t, r in row.items() if t == m and r['outcome'] == 'ok' and r.get('count'))
            if pts:
                ax.plot([p[0] for p in pts], [max(p[1], 0.1) for p in pts], marker='o', label=STREAM_LABEL[m])
        ax.set_xscale('log')
        ax.set_yscale('log')
        ax.set_title(ladder, fontsize=9)
        ax.set_xlabel(STREAM_UNIT[ladder.split('.')[0]])
        ax.set_ylabel('incremental peak (MiB)')
        ax.grid(True, which='both', alpha=0.3)
    axes[0][0].legend(fontsize=7)
    fig.tight_layout()
    fig.savefig(folder / 'plot-streaming.svg')
    plt.close(fig)
    lines += ['![Peak memory against output size](plot-streaming.svg)', '']
    (folder / 'report.md').write_text('\n'.join(lines) + '\n')
    return folder / 'report.md'


def newest():
    folders = sorted(p.parent for p in (HERE / 'results').glob('*/*/records.jsonl'))
    return folders[-1]


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('folder', nargs='?', type=Path)
    args = parser.parse_args()
    print(write_report(args.folder or newest()))


if __name__ == '__main__':
    main()
