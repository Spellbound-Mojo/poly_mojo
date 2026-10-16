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
