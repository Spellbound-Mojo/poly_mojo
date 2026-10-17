"""Refit the certification routing cost models (`_exact_cost`, `_modular_cost` in
src/polynomials/_integer_f4.mojo) on this machine and the current kernels.

Usage, from the repository root:

  python3 experiments/cert_reconstruct/calibrate_routes.py patch src /tmp/cal
      Copies src to /tmp/cal/src with a calibration change in `_pair_routes`:
      every pair goes through both routes (the modular attempt without an
      allowance, then the exact check), and one line per pair is printed:
      PAIRCAL3 degree primes modular_ns exact_ns lane_units proof_units slots
               exact_units terms columns
  Build a library from /tmp/cal/src and a driver per variable count as usual
  (mklib, then `mojo build ... groebner.mojo`), run each case certified, and
  save stdout as CASE.cal.

  python3 experiments/cert_reconstruct/calibrate_routes.py fit A.cal B.cal ...
      Fits nonnegative weights, every case weighted equally, and prints them
      in the integer form the two functions use (hundredths of a nanosecond),
      with each case's predicted and measured modular/exact time ratio.
      `_modular_cost` keeps a safety factor (default 1.2, --safety).

The weights depend on the machine and on the kernels of both routes: refit
after changing the exact row kernels, the lane sweeps or the CRT.
"""
import shutil
import sys
from pathlib import Path

import numpy as np

F4 = 'polynomials/_integer_f4.mojo'


def patch(src, out):
    out = Path(out)
    if out.exists():
        shutil.rmtree(out)
    shutil.copytree(src, out / 'src')
    path = out / 'src' / F4
    s = path.read_text()
    edits = [
        ('comptime _CERT_STATS = False', 'comptime _CERT_STATS = True'),
        ('var counts = List[Int](length=10, fill=0)', 'var counts = List[Int](length=16, fill=0)'),
        ('        own += _modular_cost(Int(units - budget.remaining()), 0, 0)',
         '        own += _modular_cost(Int(units - budget.remaining()), 0, 0)\n'
         '        counts[10] += Int(units - budget.remaining())'),
        ('            own += _modular_cost(0, Int(crt - budget.remaining()), len(lanes.columns))',
         '            own += _modular_cost(0, Int(crt - budget.remaining()), len(lanes.columns))\n'
         '            counts[11] += Int(crt - budget.remaining())\n'
         '            counts[12] += len(lanes.columns)'),
        ('''            var a = half[0]
            var b = half[1]
''', '''            var a = half[0]
            var b = half[1]
            if True:
                var mc = 0
                var c10 = counts[10]
                var c11 = counts[11]
                var c12 = counts[12]
                var t0 = Int(perf_counter_ns())
                var kk = _modular_pair(lanes, matrix, pivot, coefficients, images, a, b, _FIRST_PRIMES, 0, False, mc, counts, budget)
                var mt = Int(perf_counter_ns()) - t0
                var b1 = budget.remaining()
                var tt = 0
                var t1 = Int(perf_counter_ns())
                _ = _reduces(row, matrix, pivot, coefficients, a, b, quotient, tt, budget)
                var et = Int(perf_counter_ns()) - t1
                print("PAIRCAL3", degree, kk, mt, et, counts[10] - c10, counts[11] - c11, counts[12] - c12, Int(b1 - budget.remaining()), tt, ncols - Int(matrix.entries[matrix.starts[a]]))
                continue
'''),
    ]
    for old, new in edits:
        if s.count(old) != 1:
            sys.exit(f'patch: expected one occurrence of:\n{old}')
        s = s.replace(old, new)
    path.write_text(s)
    print(out / 'src')


def nnls(x, y):
    active = list(range(x.shape[1]))
    while True:
        c = np.linalg.lstsq(x[:, active], y, rcond=None)[0]
        if (c >= 0).all():
            full = np.zeros(x.shape[1])
            full[active] = c
            return full
        active.pop(int(np.argmin(c)))


def fit(files, safety):
    cases = {}
    for f in files:
        rows = [list(map(float, line.split()[1:])) for line in open(f) if line.startswith('PAIRCAL3')]
        if rows:
            cases[Path(f).stem] = np.array(rows)
    # columns: 0 degree 1 primes 2 modular_ns 3 exact_ns 4 lane 5 proof 6 slots 7 units 8 terms 9 columns
    a = np.vstack(list(cases.values()))
    wm = np.concatenate([np.full(len(c), 1 / c[:, 2].sum()) for c in cases.values()])
    we = np.concatenate([np.full(len(c), 1 / c[:, 3].sum()) for c in cases.values()])
    cm = nnls(a[:, 4:7] * wm[:, None], a[:, 2] * wm) * safety
    ce = nnls(a[:, 7:10] * we[:, None], a[:, 3] * we)
    print('_exact_cost:   %d * units + %d * terms + %d * columns' % tuple(round(100 * x) for x in ce))
    print('_modular_cost: %d * lane_units + %d * crt_units + %d * slots' % tuple(round(100 * x) for x in cm))
    for name, c in cases.items():
        pm, pe = (c[:, 4:7] @ cm).sum(), (c[:, 7:10] @ ce).sum()
        print(f'{name:12s} pairs {len(c):6d}  modular/exact predicted {pm / pe:.2f}  measured {c[:, 2].sum() / c[:, 3].sum():.2f}'
              f'  (exact model/measured {pe / c[:, 3].sum():.2f})')


if __name__ == '__main__':
    if len(sys.argv) >= 4 and sys.argv[1] == 'patch':
        patch(sys.argv[2], sys.argv[3])
    elif len(sys.argv) >= 3 and sys.argv[1] == 'fit':
        args = sys.argv[2:]
        safety = 1.2
        if '--safety' in args:
            i = args.index('--safety')
            safety = float(args[i + 1])
            del args[i:i + 2]
        fit(args, safety)
    else:
        sys.exit(__doc__)
