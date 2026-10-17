# Certification by reconstructed standard representations: measurements

`_certify_probe.mojo` is a measurement copy of `_pairs_reduce_to_zero`. To use it,
copy it into a scratch copy of `src/polynomials/` and make `_rational_groebner.mojo`
call `_pairs_measure` in place of `_pairs_reduce_to_zero`. It prints one `PAIR`
line per S-pair (heights of the exact quotients q_c = v / (P d)) and one `MAT`
line per degree (exact time, one-prime scalar modular time, one 8-lane pass time).

`analyze_heights.py CASE...` and `estimate_cost.py CASE...` read `CASE.meas`
(and `CASE.m2` for the 8-lane timings).

Finding: the bits needed to prove the identity track the fraction-free row
widths (work-weighted 0.86–1.22x), so the modular route wins only through word
arithmetic; per-quotient CRT is quadratic in the prime count and erodes the
gain at cyclic-8 heights.

## Refitting the routing cost models

`_pair_routes` chooses between the modular and the exact route by two cost
models counted in operations (`_exact_cost`, `_modular_cost`), so routes are
deterministic. Their weights are fitted to nanoseconds on one machine and
depend on the kernels of both routes; refit after changing either:

    python3 experiments/cert_reconstruct/calibrate_routes.py patch src /tmp/cal
    # build a library from /tmp/cal/src and certified drivers, run cases such as
    # cyclic-7/8, katsura-9/10, eco-10/11, noon-8, saving stdout as CASE.cal
    python3 experiments/cert_reconstruct/calibrate_routes.py fit /tmp/cal/*.cal

and copy the printed weights into the two functions.

## Blocked per-degree kernel (measured, not adopted)

`blocked_bench.mojo` compares the certificate's per-pair lane sweep (8 primes
in lanes) with a blocked kernel (P pairs in lanes, one prime, blocks of 16
consecutive pivots whose terms outside the block are accumulated per column
in registers), on a degree matrix dumped from a certified run (format in the
file's header). On katsura-10's degrees 8 and 9 the blocked kernel reaches
1.03-1.20x with 32 pairs per chunk (0.99x with 16, 0.69x with 8): pairs'
quotient supports overlap enough (useful work / blocked work 0.70-0.73 at
32 pairs) but each delayed entry still costs ~3.5 cycles per 8 lanes.
