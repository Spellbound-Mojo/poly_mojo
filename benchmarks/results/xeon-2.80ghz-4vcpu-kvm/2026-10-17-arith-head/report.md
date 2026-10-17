# Arithmetic results

Host: Intel(R) Xeon(R) Processor @ 2.80GHz, 4 vCPUs, 16 GiB RAM. Runs are pinned to one CPU, capped at 12G and 120 s.

Versions: Poly Mojo 210703122325+dirty; FLINT python-flint 0.9.0, FLINT 3.6.0; SymPy 1.14.0 (gmpy ground types); Singular 4.4.1.

## Summary

Geometric mean of competitor time ÷ Poly Mojo time over cases both solved with a confirmed answer and where the slower took at least 10 ms (above 1 means Poly Mojo was faster).

| Ladder | FLINT | SymPy | Singular |
|---|---|---|---|
| dense-div.GF251 | 0.496 (*n* = 1) | 680 (*n* = 2) | 0.724 (*n* = 1) |
| dense-div.GF4611686018427387847 | 0.834 (*n* = 2) | 353 (*n* = 2) | — |
| dense-div.ZZ-1024b | 0.93 (*n* = 3) | 32.8 (*n* = 2) | 13.7 (*n* = 2) |
| dense-div.ZZ-64b | 2.01 (*n* = 2) | 350 (*n* = 2) | 41.8 (*n* = 2) |
| dense-div.ZZ-8b | 0.849 (*n* = 2) | 1.01e+03 (*n* = 2) | 192 (*n* = 2) |
| dense-mul.GF251 | 0.741 (*n* = 1) | 1.61e+03 (*n* = 2) | 1.36 (*n* = 1) |
| dense-mul.GF4611686018427387847 | 0.85 (*n* = 1) | 755 (*n* = 2) | — |
| dense-mul.ZZ-1024b | 0.474 (*n* = 3) | 81.7 (*n* = 2) | 0.541 (*n* = 3) |
| dense-mul.ZZ-64b | 0.633 (*n* = 2) | 957 (*n* = 2) | 1.02 (*n* = 2) |
| dense-mul.ZZ-8b | 0.909 (*n* = 1) | 4.56e+03 (*n* = 2) | 1.64 (*n* = 1) |
| dense-sqr.GF251 | 0.571 (*n* = 1) | 1.33e+03 (*n* = 2) | 1.71 (*n* = 1) |
| dense-sqr.GF4611686018427387847 | 0.649 (*n* = 1) | 748 (*n* = 2) | — |
| dense-sqr.ZZ-1024b | 0.366 (*n* = 3) | 106 (*n* = 2) | 0.64 (*n* = 3) |
| dense-sqr.ZZ-64b | 0.808 (*n* = 1) | 1.21e+03 (*n* = 2) | 1.24 (*n* = 2) |
| dense-sqr.ZZ-8b | 0.708 (*n* = 1) | 6.6e+03 (*n* = 2) | 2.65 (*n* = 1) |
| fateman-div.ZZ | 2.95 (*n* = 3) | 232 (*n* = 2) | 3.05 (*n* = 3) |
| fateman-mul.ZZ | 0.883 (*n* = 3) | 268 (*n* = 3) | 1.02 (*n* = 3) |
| fateman-pow.ZZ | 0.423 (*n* = 1) | 12.5 (*n* = 3) | 4.67 (*n* = 1) |
| mp-div.ZZ | 1.25 (*n* = 1) | — | 2.07 (*n* = 1) |
| mp-mul.ZZ | 0.711 (*n* = 1) | 30.5 (*n* = 1) | 1.12 (*n* = 1) |
| mp-pow.ZZ | — | 67.9 (*n* = 1) | — |

## Answer agreement

Every answer that two or more libraries computed agrees.

## Per-ladder results

Each cell gives the median time per call and the incremental peak memory; `·` marks an instance skipped after a smaller one on the same ladder hit a limit; `n/a` marks an unsupported field.

### dense-div.GF251

| n | Poly Mojo | FLINT | SymPy | Singular |
|---|---|---|---|---|
| 100 | < 1 ms<br>< 1 MiB | < 1 ms<br>< 1 MiB | 15.2 ms<br>< 1 MiB | < 1 ms<br>< 1 MiB |
| 1000 | < 1 ms<br>< 1 MiB | < 1 ms<br>< 1 MiB | 1.68 s<br>< 1 MiB | < 1 ms<br>< 1 MiB |
| 10000 | 9.24 ms<br>4.88 MiB | 3.15 ms<br>< 1 MiB | timeout | 4.93 ms<br>1.91 MiB |
| 100000 | 108 ms<br>34.4 MiB | 53.5 ms<br>7.22 MiB | · | 78.2 ms<br>11.9 MiB |

### dense-div.GF4611686018427387847

| n | Poly Mojo | FLINT | SymPy | Singular |
|---|---|---|---|---|
| 100 | < 1 ms<br>< 1 MiB | < 1 ms<br>< 1 MiB | 16.2 ms<br>< 1 MiB | n/a |
| 1000 | 1.44 ms<br>< 1 MiB | < 1 ms<br>< 1 MiB | 1.57 s<br>< 1 MiB | n/a |
| 10000 | 28.3 ms<br>7.98 MiB | 19.5 ms<br>1.86 MiB | timeout | n/a |
| 100000 | 251 ms<br>41.4 MiB | 254 ms<br>26 MiB | · | n/a |

### dense-div.ZZ-1024b

| n | Poly Mojo | FLINT | SymPy | Singular |
|---|---|---|---|---|
| 100 | 5.12 ms<br>< 1 MiB | 1.19 ms<br>< 1 MiB | 5.59 ms<br>< 1 MiB | 2.46 ms<br>< 1 MiB |
| 1000 | 48.6 ms<br>2.19 MiB | 24.8 ms<br>2.71 MiB | 558 ms<br>< 1 MiB | 238 ms<br>1.12 MiB |
| 10000 | 614 ms<br>22.4 MiB | 626 ms<br>41.6 MiB | 57.8 s<br>7.4 MiB | 23.6 s<br>6.49 MiB |
| 100000 | 7.04 s<br>169 MiB | 10.9 s<br>384 MiB | timeout | timeout |

### dense-div.ZZ-64b

| n | Poly Mojo | FLINT | SymPy | Singular |
|---|---|---|---|---|
| 100 | < 1 ms<br>< 1 MiB | < 1 ms<br>< 1 MiB | 3.21 ms<br>< 1 MiB | < 1 ms<br>< 1 MiB |
| 1000 | 2.48 ms<br>1.06 MiB | 2.98 ms<br>< 1 MiB | 333 ms<br>< 1 MiB | 40 ms<br>< 1 MiB |
| 10000 | 38.4 ms<br>7.96 MiB | 62.8 ms<br>4.2 MiB | 35.1 s<br>3.09 MiB | 4.16 s<br>2.45 MiB |
| 100000 | 422 ms<br>58.4 MiB | 1.04 s<br>44.6 MiB | timeout | timeout |

### dense-div.ZZ-8b

| n | Poly Mojo | FLINT | SymPy | Singular |
|---|---|---|---|---|
| 100 | < 1 ms<br>< 1 MiB | < 1 ms<br>< 1 MiB | 3.24 ms<br>< 1 MiB | < 1 ms<br>< 1 MiB |
| 1000 | < 1 ms<br>< 1 MiB | < 1 ms<br>< 1 MiB | 337 ms<br>< 1 MiB | 8.68 ms<br>< 1 MiB |
| 10000 | 13.4 ms<br>5.11 MiB | 9.28 ms<br>< 1 MiB | 36.6 s<br>2.96 MiB | 839 ms<br>1.46 MiB |
| 100000 | 161 ms<br>32.4 MiB | 167 ms<br>4.28 MiB | timeout | 94.7 s<br>14.4 MiB |

### dense-mul.GF251

| n | Poly Mojo | FLINT | SymPy | Singular |
|---|---|---|---|---|
| 100 | < 1 ms<br>< 1 MiB | < 1 ms<br>< 1 MiB | 14.8 ms<br>< 1 MiB | < 1 ms<br>1.11 MiB |
| 1000 | < 1 ms<br>< 1 MiB | < 1 ms<br>< 1 MiB | 1.74 s<br>< 1 MiB | < 1 ms<br>1.46 MiB |
| 10000 | 1.95 ms<br>1.8 MiB | < 1 ms<br>< 1 MiB | timeout | 2.19 ms<br>2.71 MiB |
| 100000 | 21.6 ms<br>10.8 MiB | 16 ms<br>5.16 MiB | · | 29.4 ms<br>16.3 MiB |

### dense-mul.GF4611686018427387847

| n | Poly Mojo | FLINT | SymPy | Singular |
|---|---|---|---|---|
| 100 | < 1 ms<br>< 1 MiB | < 1 ms<br>< 1 MiB | 14.1 ms<br>< 1 MiB | n/a |
| 1000 | < 1 ms<br>< 1 MiB | < 1 ms<br>< 1 MiB | 1.6 s<br>< 1 MiB | n/a |
| 10000 | 6.93 ms<br>1.69 MiB | 4.68 ms<br>1.66 MiB | timeout | n/a |
| 100000 | 79.1 ms<br>10.1 MiB | 67.3 ms<br>13.7 MiB | · | n/a |

### dense-mul.ZZ-1024b

| n | Poly Mojo | FLINT | SymPy | Singular |
|---|---|---|---|---|
| 100 | 1.88 ms<br>< 1 MiB | < 1 ms<br>< 1 MiB | 4.56 ms<br>< 1 MiB | < 1 ms<br>1.61 MiB |
| 1000 | 19 ms<br>1.5 MiB | 4.69 ms<br>2.26 MiB | 515 ms<br>1.1 MiB | 5.72 ms<br>3.68 MiB |
| 10000 | 226 ms<br>15.1 MiB | 151 ms<br>34.5 MiB | 55.7 s<br>11.3 MiB | 179 ms<br>39.3 MiB |
| 100000 | 2.5 s<br>144 MiB | 1.61 s<br>357 MiB | timeout | 1.67 s<br>396 MiB |

### dense-mul.ZZ-64b

| n | Poly Mojo | FLINT | SymPy | Singular |
|---|---|---|---|---|
| 100 | < 1 ms<br>< 1 MiB | < 1 ms<br>< 1 MiB | 2.57 ms<br>< 1 MiB | < 1 ms<br>1.42 MiB |
| 1000 | < 1 ms<br>< 1 MiB | < 1 ms<br>< 1 MiB | 296 ms<br>< 1 MiB | < 1 ms<br>1.71 MiB |
| 10000 | 12.1 ms<br>4.33 MiB | 6.78 ms<br>1.96 MiB | 29.4 s<br>5.62 MiB | 10.9 ms<br>5.36 MiB |
| 100000 | 128 ms<br>31.2 MiB | 91 ms<br>23.9 MiB | timeout | 147 ms<br>42 MiB |

### dense-mul.ZZ-8b

| n | Poly Mojo | FLINT | SymPy | Singular |
|---|---|---|---|---|
| 100 | < 1 ms<br>< 1 MiB | < 1 ms<br>< 1 MiB | 2.35 ms<br>< 1 MiB | < 1 ms<br>1.23 MiB |
| 1000 | < 1 ms<br>< 1 MiB | < 1 ms<br>< 1 MiB | 276 ms<br>< 1 MiB | < 1 ms<br>1.57 MiB |
| 10000 | 2.48 ms<br>1.47 MiB | 1.59 ms<br>1.19 MiB | 29.3 s<br>5.25 MiB | 3.23 ms<br>2.8 MiB |
| 100000 | 26.6 ms<br>10.8 MiB | 24.1 ms<br>6.43 MiB | timeout | 43.5 ms<br>14.7 MiB |

### dense-sqr.GF251

| n | Poly Mojo | FLINT | SymPy | Singular |
|---|---|---|---|---|
| 100 | < 1 ms<br>< 1 MiB | < 1 ms<br>< 1 MiB | 14 ms<br>< 1 MiB | < 1 ms<br>1.12 MiB |
| 1000 | < 1 ms<br>< 1 MiB | < 1 ms<br>< 1 MiB | 1.35 s<br>< 1 MiB | < 1 ms<br>1.5 MiB |
| 10000 | 1.83 ms<br>1.49 MiB | < 1 ms<br>1 MiB | timeout | 2.36 ms<br>3.02 MiB |
| 100000 | 19.6 ms<br>7 MiB | 11.2 ms<br>5 MiB | · | 33.6 ms<br>19.5 MiB |

### dense-sqr.GF4611686018427387847

| n | Poly Mojo | FLINT | SymPy | Singular |
|---|---|---|---|---|
| 100 | < 1 ms<br>< 1 MiB | < 1 ms<br>< 1 MiB | 13.2 ms<br>< 1 MiB | n/a |
| 1000 | < 1 ms<br>< 1 MiB | < 1 ms<br>< 1 MiB | 1.54 s<br>< 1 MiB | n/a |
| 10000 | 5.89 ms<br>1.96 MiB | 3.26 ms<br>1.54 MiB | timeout | n/a |
| 100000 | 67.4 ms<br>6.06 MiB | 43.7 ms<br>11.6 MiB | · | n/a |

### dense-sqr.ZZ-1024b

| n | Poly Mojo | FLINT | SymPy | Singular |
|---|---|---|---|---|
| 100 | 1.6 ms<br>< 1 MiB | < 1 ms<br>< 1 MiB | 4.69 ms<br>< 1 MiB | < 1 ms<br>1.7 MiB |
| 1000 | 15.7 ms<br>< 1 MiB | 2.9 ms<br>1.53 MiB | 548 ms<br>1.09 MiB | 5.59 ms<br>3.93 MiB |
| 10000 | 185 ms<br>10.2 MiB | 89.1 ms<br>19.7 MiB | 59.1 s<br>11.3 MiB | 150 ms<br>41.2 MiB |
| 100000 | 2.03 s<br>94.3 MiB | 1.11 s<br>203 MiB | timeout | 1.83 s<br>416 MiB |

### dense-sqr.ZZ-64b

| n | Poly Mojo | FLINT | SymPy | Singular |
|---|---|---|---|---|
| 100 | < 1 ms<br>< 1 MiB | < 1 ms<br>< 1 MiB | 2.48 ms<br>< 1 MiB | < 1 ms<br>1.49 MiB |
| 1000 | < 1 ms<br>< 1 MiB | < 1 ms<br>< 1 MiB | 300 ms<br>< 1 MiB | < 1 ms<br>1.77 MiB |
| 10000 | 9.98 ms<br>3.21 MiB | 5.47 ms<br>1.63 MiB | 33.5 s<br>5.62 MiB | 11.3 ms<br>6.12 MiB |
| 100000 | 110 ms<br>19.7 MiB | 88.6 ms<br>16.5 MiB | timeout | 151 ms<br>49.7 MiB |

### dense-sqr.ZZ-8b

| n | Poly Mojo | FLINT | SymPy | Singular |
|---|---|---|---|---|
| 100 | < 1 ms<br>< 1 MiB | < 1 ms<br>< 1 MiB | 2.38 ms<br>< 1 MiB | < 1 ms<br>1.23 MiB |
| 1000 | < 1 ms<br>< 1 MiB | < 1 ms<br>< 1 MiB | 349 ms<br>< 1 MiB | < 1 ms<br>1.63 MiB |
| 10000 | 2.05 ms<br>1.42 MiB | 1.49 ms<br>1.03 MiB | 32 s<br>5.27 MiB | 3.4 ms<br>3.05 MiB |
| 100000 | 22.9 ms<br>7.48 MiB | 16.2 ms<br>3.9 MiB | timeout | 60.7 ms<br>17.8 MiB |

### fateman-div.ZZ

| n | Poly Mojo | FLINT | SymPy | Singular |
|---|---|---|---|---|
| 10 | 3.79 ms<br>< 1 MiB | 8.75 ms<br>< 1 MiB | 665 ms<br>< 1 MiB | 9.89 ms<br>< 1 MiB |
| 15 | 46.5 ms<br>< 1 MiB | 129 ms<br>< 1 MiB | 14.3 s<br>6.48 MiB | 141 ms<br>1.3 MiB |
| 20 | 356 ms<br>< 1 MiB | 1.1 s<br>< 1 MiB | timeout | 1.12 s<br>7.38 MiB |
| 30 | 8.01 s<br>< 1 MiB | 23.9 s<br>2.75 MiB | · | 23.7 s<br>27.8 MiB |

### fateman-mul.ZZ

| n | Poly Mojo | FLINT | SymPy | Singular |
|---|---|---|---|---|
| 10 | 2.66 ms<br>4.71 MiB | 1.06 ms<br>< 1 MiB | 330 ms<br>2.51 MiB | 1.78 ms<br>1.72 MiB |
| 15 | 24.3 ms<br>6.08 MiB | 13.5 ms<br>1.68 MiB | 7.33 s<br>12.5 MiB | 17.9 ms<br>5.36 MiB |
| 20 | 200 ms<br>26.6 MiB | 123 ms<br>7.62 MiB | 103 s<br>34.6 MiB | 142 ms<br>18.1 MiB |
| 30 | 4.64 s<br>137 MiB | 9.35 s<br>1.46 GiB | timeout | 9.29 s<br>1.46 GiB |

### fateman-pow.ZZ

| n | Poly Mojo | FLINT | SymPy | Singular |
|---|---|---|---|---|
| 10 | < 1 ms<br>< 1 MiB | < 1 ms<br>< 1 MiB | 2.37 ms<br>< 1 MiB | < 1 ms<br>< 1 MiB |
| 15 | < 1 ms<br>3.05 MiB | < 1 ms<br>< 1 MiB | 10.7 ms<br>1.31 MiB | < 1 ms<br>< 1 MiB |
| 20 | 2.04 ms<br>5.67 MiB | 1.43 ms<br>1.27 MiB | 29.7 ms<br>3.29 MiB | 4.2 ms<br>1.35 MiB |
| 30 | 16.6 ms<br>8.84 MiB | 7.02 ms<br>2.61 MiB | 197 ms<br>18 MiB | 77.5 ms<br>6.64 MiB |

### mp-div.ZZ

| n | Poly Mojo | FLINT | SymPy | Singular |
|---|---|---|---|---|
| 12 | 842 ms<br>< 1 MiB | 1.06 s<br>< 1 MiB | timeout | 1.74 s<br>140 MiB |

### mp-mul.ZZ

| n | Poly Mojo | FLINT | SymPy | Singular |
|---|---|---|---|---|
| 12 | 1.53 s<br>819 MiB | 1.08 s<br>188 MiB | 46.5 s<br>1.57 GiB | 1.71 s<br>679 MiB |

### mp-pow.ZZ

| n | Poly Mojo | FLINT | SymPy | Singular |
|---|---|---|---|---|
| 12 | < 1 ms<br>2.18 MiB | < 1 ms<br>1.09 MiB | 65 ms<br>2 MiB | 1.52 ms<br>< 1 MiB |

