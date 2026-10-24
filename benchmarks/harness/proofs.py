"""Describe proof work independently of the operation's measured time."""


def metadata(tool, case):
    if tool.system != 'Poly Mojo':
        return {'proof_mode': 'none', 'proof_note': 'No proof certificate requested by this driver.'}
    family = case.get('family', 'cad' if 'masks' in case else 'factor')
    if family == 'groebner':
        mode = {'uncertified': 'none', 'comparable': 'internal-certification',
                'certified': 'retained'}[tool.mode]
        note = {'none': 'witnesses=False, certify=False; answer agreement checked outside timing.',
                'internal-certification': 'No retained witnesses; rational-basis certification remains timed.',
                'retained': 'Retained cofactor witnesses and rational-basis certification; independent check timed separately.'}[mode]
    elif family in ('factor', 'gcd'):
        mode = 'retained' if getattr(tool, 'certified', False) or getattr(tool, 'mode', '') == 'certified' else 'none'
        note = 'Checked producer timed; independent check of the same result timed separately.' if mode == 'retained' else 'Value-only API; no retained proof certificate requested.'
    elif family in ('arith', 'series'):
        mode, note = 'none', 'Value-only arithmetic; no proof certificate is produced.'
    elif family == 'cad' and tool.mode == 'construct':
        mode, note = 'final-data', 'Construction timed separately from final verification; compact final data are still retained. Benchmark instrumentation, not a proof-free public API.'
    else:
        mode, note = 'always-retained', 'This API retains or emits evidence; a proof-free mode is unavailable. Do not label this timing as proof-free.'
    return {'proof_mode': mode, 'proof_note': note}


def table(records, pairs):
    """Compare producer calls and keep independent checking in its own column."""
    from .report import fmt_time, cell
    index = {(r['case'], r['tool']): r for r in records}
    lines = ['| Case / mode | Without certificate | With certificate | Check only | With certificate + check |',
             '|---|---:|---:|---:|---:|']
    for plain, certified in pairs:
        for r in records:
            if r['tool'] != certified or r['outcome'] == 'unsupported':
                continue
            base = index.get((r['case'], plain))
            check = fmt_time(r['check_s']) if r.get('check_s') is not None else '—'
            total = fmt_time(r['time_s'] + r['check_s']) if r['outcome'] == 'ok' and r.get('check_s') is not None else '—'
            lines.append(f"| {r['case']} / {plain} | {cell(base, memory=False)} | {cell(r, memory=False)} | {check} | {total} |")
    return lines if len(lines) > 2 else ['No paired certificate measurements are available.']
