# Series, evaluation, and interpolation results

Host: Intel(R) Xeon(R) Processor @ 2.80GHz, 4 vCPUs, 16 GiB RAM. Runs are pinned to one CPU, capped at 12G and 60 s.

Versions: Poly Mojo 4019559fc554; FLINT FLINT 3.3.1 (C, conda-forge libflint); SymPy 1.14.0 (gmpy ground types).

## Summary

Geometric mean of competitor time ÷ Poly Mojo time over cases both solved with a confirmed answer and where the slower took at least 10 ms (above 1 means Poly Mojo was faster).

| Ladder | FLINT | SymPy |
|---|---|---|
| evalq.ZZ | 0.651 (*n* = 2) | 92.4 (*n* = 1) |
| interp.GF4611686018427387847 | 0.0549 (*n* = 2) | — |
| interp.QQ | 0.0149 (*n* = 1) | — |
| multipoint.GF4611686018427387847 | 0.0723 (*n* = 2) | 210 (*n* = 1) |
| multipoint.ZZ | 0.14 (*n* = 1) | 16.9 (*n* = 1) |
| series-compose.GF4611686018427387847 | 0.00343 (*n* = 1) | — |
| series-compose.QQ | 0.0081 (*n* = 1) | 0.499 (*n* = 1) |
| series-exp.GF4611686018427387847 | 0.0148 (*n* = 3) | 108 (*n* = 1) |
| series-exp.QQ | 0.00363 (*n* = 2) | 2.16 (*n* = 1) |
| series-inv.GF4611686018427387847 | 0.0167 (*n* = 2) | 316 (*n* = 1) |
| series-inv.QQ | 0.0522 (*n* = 1) | 1.84 (*n* = 1) |
| series-log.GF4611686018427387847 | 0.0143 (*n* = 2) | 361 (*n* = 1) |
| series-log.QQ | 0.0687 (*n* = 1) | 1.92 (*n* = 1) |
| series-mul.GF4611686018427387847 | 0.0161 (*n* = 2) | 127 (*n* = 1) |
| series-mul.QQ | 0.00223 (*n* = 2) | 15.7 (*n* = 2) |
| series-pow.GF4611686018427387847 | — | — |
| series-pow.QQ | — | — |
| series-revert.GF4611686018427387847 | 0.00398 (*n* = 1) | — |
| series-revert.QQ | 0.0261 (*n* = 1) | 12.8 (*n* = 1) |
| series-sqrt.GF4611686018427387847 | — | — |
| series-sqrt.QQ | — | — |

## Answer agreement

Every answer that two or more libraries computed agrees.

## Per-ladder results

Each cell gives the median time per call and the incremental peak memory; `·` marks an instance skipped after a smaller one on the same ladder hit a limit; `n/a` marks an unsupported operation.

### evalq.ZZ

| n | Poly Mojo | FLINT | SymPy |
|---|---|---|---|
| 1000 | 9.31 ms<br>< 1 MiB | 13 ms<br>< 1 MiB | 860 ms<br>< 1 MiB |
| 10000 | 942 ms<br>< 1 MiB | 286 ms<br>8.59 MiB | timeout |
| 100000 | timeout | 6.86 s<br>96.6 MiB ? | · |

### interp.GF4611686018427387847

| n | Poly Mojo | FLINT | SymPy |
|---|---|---|---|
| 1000 | 32.3 ms<br>1.25 MiB | 2.52 ms<br>1.43 MiB | n/a |
| 10000 | 2.57 s<br>12.5 MiB | 99.6 ms<br>3.42 MiB | n/a |
| 100000 | timeout | 2.22 s<br>31.9 MiB ? | n/a |

### interp.QQ

| n | Poly Mojo | FLINT | SymPy |
|---|---|---|---|
| 100 | 76.4 ms<br>< 1 MiB | 1.14 ms<br>1.18 MiB | timeout |
| 1000 | timeout | 4.34 s<br>6.68 MiB ? | · |
| 10000 | · | timeout | · |

### multipoint.GF4611686018427387847

| n | Poly Mojo | FLINT | SymPy |
|---|---|---|---|
| 1000 | 12.2 ms<br>< 1 MiB | 1.43 ms<br>1.29 MiB | 2.55 s<br>< 1 MiB |
| 10000 | 1.33 s<br>< 1 MiB | 59.3 ms<br>2.93 MiB | timeout |
| 100000 | timeout | 1.52 s<br>30.1 MiB ? | · |

### multipoint.ZZ

| n | Poly Mojo | FLINT | SymPy |
|---|---|---|---|
| 100 | 1.21 ms<br>< 1 MiB | < 1 ms<br>< 1 MiB | 7.16 ms<br>< 1 MiB |
| 1000 | 577 ms<br>3.71 MiB | 80.9 ms<br>4.45 MiB | 9.75 s<br>3.94 MiB |
| 10000 | timeout | 26.6 s<br>362 MiB ? | timeout |

### series-compose.GF4611686018427387847

| n | Poly Mojo | FLINT | SymPy |
|---|---|---|---|
| 1000 | 6.25 s<br>< 1 MiB | 21.4 ms<br>1.89 MiB | timeout |
| 10000 | timeout | 1.45 s<br>24.4 MiB ? | · |
| 100000 | · | timeout | · |

### series-compose.QQ

| n | Poly Mojo | FLINT | SymPy |
|---|---|---|---|
| 100 | 127 ms<br>< 1 MiB | 1.03 ms<br>1.08 MiB | 63.3 ms<br>< 1 MiB |
| 1000 | timeout | 299 ms<br>9.91 MiB ? | timeout |
| 10000 | · | timeout | · |

### series-exp.GF4611686018427387847

| n | Poly Mojo | FLINT | SymPy |
|---|---|---|---|
| 1000 | 17.9 ms<br>< 1 MiB | < 1 ms<br>< 1 MiB | 1.93 s<br>< 1 MiB |
| 10000 | 1.11 s<br>3.89 MiB | 21.1 ms<br>2.89 MiB | timeout |
| 100000 | 35.5 s<br>16.9 MiB | 363 ms<br>22.1 MiB | · |

### series-exp.QQ

| n | Poly Mojo | FLINT | SymPy |
|---|---|---|---|
| 100 | 10.6 ms<br>< 1 MiB | < 1 ms<br>< 1 MiB | 22.9 ms<br>< 1 MiB |
| 1000 | 46.1 s<br>5.84 MiB | 72 ms<br>1.55 MiB | timeout |
| 10000 | timeout | 27.2 s<br>1.35 GiB ? | · |

### series-inv.GF4611686018427387847

| n | Poly Mojo | FLINT | SymPy |
|---|---|---|---|
| 1000 | 3.7 ms<br>< 1 MiB | < 1 ms<br>< 1 MiB | 1.17 s<br>< 1 MiB |
| 10000 | 433 ms<br>2.59 MiB | 11.8 ms<br>2.58 MiB | timeout |
| 100000 | 16.5 s<br>13.5 MiB | 169 ms<br>20.3 MiB | · |

### series-inv.QQ

| n | Poly Mojo | FLINT | SymPy |
|---|---|---|---|
| 100 | 1.69 ms<br>< 1 MiB | < 1 ms<br>< 1 MiB | 3.29 ms<br>< 1 MiB |
| 1000 | 334 ms<br>2.08 MiB | 17.4 ms<br>3.35 MiB | 614 ms<br>1.49 MiB |
| 10000 | timeout | 2.32 s<br>308 MiB ? | timeout |

### series-log.GF4611686018427387847

| n | Poly Mojo | FLINT | SymPy |
|---|---|---|---|
| 1000 | 5.99 ms<br>< 1 MiB | < 1 ms<br>< 1 MiB | 2.16 s<br>< 1 MiB |
| 10000 | 730 ms<br>3.07 MiB | 14.6 ms<br>2.68 MiB | timeout |
| 100000 | 25.7 s<br>18.8 MiB | 264 ms<br>22.1 MiB | · |

### series-log.QQ

| n | Poly Mojo | FLINT | SymPy |
|---|---|---|---|
| 100 | 1.68 ms<br>< 1 MiB | < 1 ms<br>< 1 MiB | 5.47 ms<br>< 1 MiB |
| 1000 | 510 ms<br>2.66 MiB | 35 ms<br>6.81 MiB | 980 ms<br>1.81 MiB |
| 10000 | timeout | 13.8 s<br>1.15 GiB ? | timeout |

### series-mul.GF4611686018427387847

| n | Poly Mojo | FLINT | SymPy |
|---|---|---|---|
| 1000 | 5.87 ms<br>< 1 MiB | < 1 ms<br>< 1 MiB | 746 ms<br>< 1 MiB |
| 10000 | 214 ms<br>1.34 MiB | 6.62 ms<br>2.18 MiB | timeout |
| 100000 | 9.15 s<br>13 MiB | 76.9 ms<br>23.6 MiB | · |

### series-mul.QQ

| n | Poly Mojo | FLINT | SymPy |
|---|---|---|---|
| 100 | < 1 ms<br>< 1 MiB | < 1 ms<br>< 1 MiB | 1.73 ms<br>< 1 MiB |
| 1000 | 24.5 ms<br>< 1 MiB | < 1 ms<br>< 1 MiB | 220 ms<br>< 1 MiB |
| 10000 | 877 ms<br>4.35 MiB | 2.06 ms<br>< 1 MiB | 24.2 s<br>2.95 MiB |

### series-pow.GF4611686018427387847

| n | Poly Mojo | FLINT | SymPy |
|---|---|---|---|
| 1000 | n/a | < 1 ms<br>< 1 MiB | 1.9 s<br>< 1 MiB |
| 10000 | n/a | 15.2 ms<br>2.33 MiB ? | timeout |
| 100000 | n/a | 174 ms<br>25.3 MiB ? | · |

### series-pow.QQ

| n | Poly Mojo | FLINT | SymPy |
|---|---|---|---|
| 100 | n/a | < 1 ms<br>< 1 MiB | 4.38 ms<br>< 1 MiB |
| 1000 | n/a | < 1 ms<br>< 1 MiB | 664 ms<br>< 1 MiB |
| 10000 | n/a | 6.42 ms<br>1.62 MiB ? |  |

### series-revert.GF4611686018427387847

| n | Poly Mojo | FLINT | SymPy |
|---|---|---|---|
| 1000 | 7.19 s<br>< 1 MiB | 28.6 ms<br>1.32 MiB | timeout |
| 10000 | timeout | 1.51 s<br>10.6 MiB ? | · |
| 100000 | · | timeout | · |

### series-revert.QQ

| n | Poly Mojo | FLINT | SymPy |
|---|---|---|---|
| 100 | 191 ms<br>< 1 MiB | 4.98 ms<br>1.42 MiB | 2.45 s<br>< 1 MiB |
| 1000 | timeout | 3.75 s<br>66.1 MiB ? | timeout |
| 10000 | · | timeout | · |

### series-sqrt.GF4611686018427387847

| n | Poly Mojo | FLINT | SymPy |
|---|---|---|---|
| 1000 | n/a | < 1 ms<br>< 1 MiB | 3.64 s<br>1.05 MiB |
| 10000 | n/a | 14 ms<br>< 1 MiB ? | timeout |
| 100000 | n/a | 345 ms<br>17.1 MiB ? | · |

### series-sqrt.QQ

| n | Poly Mojo | FLINT | SymPy |
|---|---|---|---|
| 100 | n/a | < 1 ms<br>1.08 MiB | 13.4 ms<br>< 1 MiB |
| 1000 | n/a | 188 ms<br>16.3 MiB | 5.05 s<br>3.61 MiB |
| 10000 | n/a | 29.5 s<br>1.31 GiB ? | timeout |

