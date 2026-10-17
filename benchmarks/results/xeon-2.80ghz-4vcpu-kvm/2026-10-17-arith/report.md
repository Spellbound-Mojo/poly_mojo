# Arithmetic results

Host: Intel(R) Xeon(R) Processor @ 2.80GHz, 4 vCPUs, 16 GiB RAM. Runs are pinned to one CPU, capped at 12G and 120 s.

Versions: Poly Mojo 428ba91c86a5+dirty; FLINT python-flint 0.9.0, FLINT 3.6.0; SymPy 1.14.0 (gmpy ground types); Singular 4.4.1.

## Summary

Geometric mean of competitor time ÷ Poly Mojo time over cases both solved with a confirmed answer and where the slower took at least 10 ms (above 1 means Poly Mojo was faster).

| Ladder | FLINT | SymPy | Singular |
|---|---|---|---|
| dense-div.GF251 | 0.0004 (*n* = 2) | 15.4 (*n* = 2) | 0.00101 (*n* = 2) |
| dense-div.GF4611686018427387847 | 0.00172 (*n* = 2) | 14.9 (*n* = 2) | — |
| dense-div.ZZ-1024b | 0.0155 (*n* = 2) | 0.881 (*n* = 2) | 0.368 (*n* = 2) |
| dense-div.ZZ-64b | 0.00326 (*n* = 2) | 1.05 (*n* = 2) | 0.125 (*n* = 2) |
| dense-div.ZZ-8b | 0.00118 (*n* = 2) | 2.45 (*n* = 2) | 0.0596 (*n* = 2) |
| dense-mul.GF251 | 0.00266 (*n* = 2) | 171 (*n* = 2) | 0.00592 (*n* = 2) |
| dense-mul.GF4611686018427387847 | 0.0131 (*n* = 2) | 166 (*n* = 2) | — |
| dense-mul.ZZ-1024b | 0.0445 (*n* = 2) | 8.95 (*n* = 2) | 0.0534 (*n* = 2) |
| dense-mul.ZZ-64b | 0.00495 (*n* = 3) | 13.8 (*n* = 2) | 0.00814 (*n* = 3) |
| dense-mul.ZZ-8b | 0.00274 (*n* = 2) | 51.1 (*n* = 2) | 0.00525 (*n* = 2) |
| dense-sqr.GF251 | 0.00195 (*n* = 2) | 152 (*n* = 2) | 0.00662 (*n* = 2) |
| dense-sqr.GF4611686018427387847 | 0.00872 (*n* = 2) | 157 (*n* = 2) | — |
| dense-sqr.ZZ-1024b | 0.0271 (*n* = 2) | 9.59 (*n* = 2) | 0.0488 (*n* = 2) |
| dense-sqr.ZZ-64b | 0.00393 (*n* = 3) | 15 (*n* = 2) | 0.00818 (*n* = 3) |
| dense-sqr.ZZ-8b | 0.00221 (*n* = 2) | 59.8 (*n* = 2) | 0.00644 (*n* = 2) |
| fateman-div.ZZ | 0.00736 (*n* = 2) | 0.674 (*n* = 2) | 0.00817 (*n* = 2) |
| fateman-mul.ZZ | 0.00143 (*n* = 3) | 0.748 (*n* = 3) | 0.00197 (*n* = 3) |
| fateman-pow.ZZ | 0.00262 (*n* = 3) | 0.0653 (*n* = 3) | 0.00952 (*n* = 3) |
| mp-div.ZZ | — | — | — |
| mp-mul.ZZ | 0.0344 (*n* = 1) | 1.47 (*n* = 1) | 0.0543 (*n* = 1) |
| mp-pow.ZZ | 0.0085 (*n* = 1) | 0.784 (*n* = 1) | 0.0184 (*n* = 1) |

## Answer agreement

Every answer that two or more libraries computed agrees.

## Per-ladder results

Each cell gives the median time per call and the incremental peak memory; `·` marks an instance skipped after a smaller one on the same ladder hit a limit; `n/a` marks an unsupported field.

### dense-div.GF251

| n | Poly Mojo | FLINT | SymPy | Singular |
|---|---|---|---|---|
| 100 | 1.05 ms<br>< 1 MiB | < 1 ms<br>< 1 MiB | 15.2 ms<br>< 1 MiB | < 1 ms<br>< 1 MiB |
| 1000 | 102 ms<br>1.39 MiB | < 1 ms<br>< 1 MiB | 1.68 s<br>< 1 MiB | < 1 ms<br>< 1 MiB |
| 10000 | 11.3 s<br>6.98 MiB | 2.42 ms<br>< 1 MiB | timeout | 4.93 ms<br>1.91 MiB |
| 100000 | timeout | 38.1 ms<br>6.48 MiB | · | 78.2 ms<br>11.9 MiB |

### dense-div.GF4611686018427387847

| n | Poly Mojo | FLINT | SymPy | Singular |
|---|---|---|---|---|
| 100 | 1.11 ms<br>< 1 MiB | < 1 ms<br>< 1 MiB | 16.2 ms<br>< 1 MiB | n/a |
| 1000 | 103 ms<br>1.07 MiB | < 1 ms<br>< 1 MiB | 1.57 s<br>< 1 MiB | n/a |
| 10000 | 11.7 s<br>6.21 MiB | 12.8 ms<br>1.55 MiB | timeout | n/a |
| 100000 | timeout | 186 ms<br>20.9 MiB ? | · | n/a |

### dense-div.ZZ-1024b

| n | Poly Mojo | FLINT | SymPy | Singular |
|---|---|---|---|---|
| 100 | 5.9 ms<br>< 1 MiB | < 1 ms<br>< 1 MiB | 5.59 ms<br>< 1 MiB | 2.46 ms<br>< 1 MiB |
| 1000 | 587 ms<br>< 1 MiB | 19.9 ms<br>1.62 MiB | 558 ms<br>< 1 MiB | 238 ms<br>1.12 MiB |
| 10000 | 70.8 s<br>4.93 MiB | 502 ms<br>26.6 MiB | 57.8 s<br>7.4 MiB | 23.6 s<br>6.49 MiB |
| 100000 | timeout | 8.59 s<br>247 MiB ? | timeout | timeout |

### dense-div.ZZ-64b

| n | Poly Mojo | FLINT | SymPy | Singular |
|---|---|---|---|---|
| 100 | 2.75 ms<br>< 1 MiB | < 1 ms<br>< 1 MiB | 3.21 ms<br>< 1 MiB | < 1 ms<br>< 1 MiB |
| 1000 | 280 ms<br>1.1 MiB | 2.38 ms<br>< 1 MiB | 333 ms<br>< 1 MiB | 40 ms<br>< 1 MiB |
| 10000 | 38 s<br>6.44 MiB | 47.5 ms<br>2.31 MiB | 35.1 s<br>3.09 MiB | 4.16 s<br>2.45 MiB |
| 100000 | timeout | 850 ms<br>24.1 MiB ? | timeout | timeout |

### dense-div.ZZ-8b

| n | Poly Mojo | FLINT | SymPy | Singular |
|---|---|---|---|---|
| 100 | 1.43 ms<br>< 1 MiB | < 1 ms<br>< 1 MiB | 3.24 ms<br>< 1 MiB | < 1 ms<br>< 1 MiB |
| 1000 | 132 ms<br>1.46 MiB | < 1 ms<br>< 1 MiB | 337 ms<br>< 1 MiB | 8.68 ms<br>< 1 MiB |
| 10000 | 15.5 s<br>6.72 MiB | 7.99 ms<br>< 1 MiB | 36.6 s<br>2.96 MiB | 839 ms<br>1.46 MiB |
| 100000 | timeout | 159 ms<br>2.77 MiB | timeout | 94.7 s<br>14.4 MiB |

### dense-mul.GF251

| n | Poly Mojo | FLINT | SymPy | Singular |
|---|---|---|---|---|
| 100 | < 1 ms<br>< 1 MiB | < 1 ms<br>< 1 MiB | 14.8 ms<br>< 1 MiB | < 1 ms<br>1.11 MiB |
| 1000 | 6.61 ms<br>< 1 MiB | < 1 ms<br>< 1 MiB | 1.74 s<br>< 1 MiB | < 1 ms<br>1.46 MiB |
| 10000 | 210 ms<br>2.16 MiB | < 1 ms<br>< 1 MiB | timeout | 2.19 ms<br>2.71 MiB |
| 100000 | 8.73 s<br>12.5 MiB | 16 ms<br>5.16 MiB | · | 29.4 ms<br>16.3 MiB |

### dense-mul.GF4611686018427387847

| n | Poly Mojo | FLINT | SymPy | Singular |
|---|---|---|---|---|
| 100 | < 1 ms<br>< 1 MiB | < 1 ms<br>< 1 MiB | 14.1 ms<br>< 1 MiB | n/a |
| 1000 | 6.22 ms<br>< 1 MiB | < 1 ms<br>< 1 MiB | 1.6 s<br>< 1 MiB | n/a |
| 10000 | 209 ms<br>1.04 MiB | 4.68 ms<br>1.66 MiB | timeout | n/a |
| 100000 | 8.82 s<br>7.77 MiB | 67.3 ms<br>13.7 MiB | · | n/a |

### dense-mul.ZZ-1024b

| n | Poly Mojo | FLINT | SymPy | Singular |
|---|---|---|---|---|
| 100 | 2.29 ms<br>< 1 MiB | < 1 ms<br>< 1 MiB | 4.56 ms<br>< 1 MiB | < 1 ms<br>1.61 MiB |
| 1000 | 94 ms<br>1.33 MiB | 4.69 ms<br>2.26 MiB | 515 ms<br>1.1 MiB | 5.72 ms<br>3.68 MiB |
| 10000 | 3.81 s<br>13.2 MiB | 151 ms<br>34.5 MiB | 55.7 s<br>11.3 MiB | 179 ms<br>39.3 MiB |
| 100000 | timeout | 1.61 s<br>357 MiB | timeout | 1.67 s<br>396 MiB |

### dense-mul.ZZ-64b

| n | Poly Mojo | FLINT | SymPy | Singular |
|---|---|---|---|---|
| 100 | < 1 ms<br>< 1 MiB | < 1 ms<br>< 1 MiB | 2.57 ms<br>< 1 MiB | < 1 ms<br>1.42 MiB |
| 1000 | 32.1 ms<br>< 1 MiB | < 1 ms<br>< 1 MiB | 296 ms<br>< 1 MiB | < 1 ms<br>1.71 MiB |
| 10000 | 1.43 s<br>5.48 MiB | 6.78 ms<br>1.96 MiB | 29.4 s<br>5.62 MiB | 10.9 ms<br>5.36 MiB |
| 100000 | 60.1 s<br>47 MiB | 91 ms<br>23.9 MiB | timeout | 147 ms<br>42 MiB |

### dense-mul.ZZ-8b

| n | Poly Mojo | FLINT | SymPy | Singular |
|---|---|---|---|---|
| 100 | < 1 ms<br>< 1 MiB | < 1 ms<br>< 1 MiB | 2.35 ms<br>< 1 MiB | < 1 ms<br>1.23 MiB |
| 1000 | 8.93 ms<br>< 1 MiB | < 1 ms<br>< 1 MiB | 276 ms<br>< 1 MiB | < 1 ms<br>1.57 MiB |
| 10000 | 346 ms<br>1.84 MiB | 1.59 ms<br>1.19 MiB | 29.3 s<br>5.25 MiB | 3.23 ms<br>2.8 MiB |
| 100000 | 14.8 s<br>12.4 MiB | 24.1 ms<br>6.43 MiB | timeout | 43.5 ms<br>14.7 MiB |

### dense-sqr.GF251

| n | Poly Mojo | FLINT | SymPy | Singular |
|---|---|---|---|---|
| 100 | < 1 ms<br>< 1 MiB | < 1 ms<br>< 1 MiB | 14 ms<br>< 1 MiB | < 1 ms<br>1.12 MiB |
| 1000 | 6.18 ms<br>< 1 MiB | < 1 ms<br>< 1 MiB | 1.35 s<br>< 1 MiB | < 1 ms<br>1.5 MiB |
| 10000 | 207 ms<br>1.81 MiB | < 1 ms<br>1 MiB | timeout | 2.36 ms<br>3.02 MiB |
| 100000 | 8.75 s<br>11 MiB | 11.2 ms<br>5 MiB | · | 33.6 ms<br>19.5 MiB |

### dense-sqr.GF4611686018427387847

| n | Poly Mojo | FLINT | SymPy | Singular |
|---|---|---|---|---|
| 100 | < 1 ms<br>< 1 MiB | < 1 ms<br>< 1 MiB | 13.2 ms<br>< 1 MiB | n/a |
| 1000 | 6.19 ms<br>< 1 MiB | < 1 ms<br>< 1 MiB | 1.54 s<br>< 1 MiB | n/a |
| 10000 | 209 ms<br>1.12 MiB | 3.26 ms<br>1.54 MiB | timeout | n/a |
| 100000 | 8.97 s<br>7.36 MiB | 43.7 ms<br>11.6 MiB | · | n/a |

### dense-sqr.ZZ-1024b

| n | Poly Mojo | FLINT | SymPy | Singular |
|---|---|---|---|---|
| 100 | 2.37 ms<br>< 1 MiB | < 1 ms<br>< 1 MiB | 4.69 ms<br>< 1 MiB | < 1 ms<br>1.7 MiB |
| 1000 | 94.6 ms<br>1.25 MiB | 2.9 ms<br>1.53 MiB | 548 ms<br>1.09 MiB | 5.59 ms<br>3.93 MiB |
| 10000 | 3.73 s<br>12.5 MiB | 89.1 ms<br>19.7 MiB | 59.1 s<br>11.3 MiB | 150 ms<br>41.2 MiB |
| 100000 | timeout | 1.11 s<br>203 MiB | timeout | 1.83 s<br>416 MiB |

### dense-sqr.ZZ-64b

| n | Poly Mojo | FLINT | SymPy | Singular |
|---|---|---|---|---|
| 100 | < 1 ms<br>< 1 MiB | < 1 ms<br>< 1 MiB | 2.48 ms<br>< 1 MiB | < 1 ms<br>1.49 MiB |
| 1000 | 32 ms<br>< 1 MiB | < 1 ms<br>< 1 MiB | 300 ms<br>< 1 MiB | < 1 ms<br>1.77 MiB |
| 10000 | 1.39 s<br>4.56 MiB | 5.47 ms<br>1.63 MiB | 33.5 s<br>5.62 MiB | 11.3 ms<br>6.12 MiB |
| 100000 | 62.8 s<br>42.8 MiB | 88.6 ms<br>16.5 MiB | timeout | 151 ms<br>49.7 MiB |

### dense-sqr.ZZ-8b

| n | Poly Mojo | FLINT | SymPy | Singular |
|---|---|---|---|---|
| 100 | < 1 ms<br>< 1 MiB | < 1 ms<br>< 1 MiB | 2.38 ms<br>< 1 MiB | < 1 ms<br>1.23 MiB |
| 1000 | 9.26 ms<br>< 1 MiB | < 1 ms<br>< 1 MiB | 349 ms<br>< 1 MiB | < 1 ms<br>1.63 MiB |
| 10000 | 338 ms<br>1.82 MiB | 1.49 ms<br>1.03 MiB | 32 s<br>5.27 MiB | 3.4 ms<br>3.05 MiB |
| 100000 | 14.7 s<br>9.97 MiB | 16.2 ms<br>3.9 MiB | timeout | 60.7 ms<br>17.8 MiB |

### fateman-div.ZZ

| n | Poly Mojo | FLINT | SymPy | Singular |
|---|---|---|---|---|
| 10 | 857 ms<br>2.83 MiB | 8.75 ms<br>< 1 MiB | 665 ms<br>< 1 MiB | 9.89 ms<br>< 1 MiB |
| 15 | 24.4 s<br>6.51 MiB | 129 ms<br>< 1 MiB | 14.3 s<br>6.48 MiB | 141 ms<br>1.3 MiB |
| 20 | timeout | 1.1 s<br>< 1 MiB | timeout | 1.12 s<br>7.38 MiB |
| 30 | · | 23.9 s<br>2.75 MiB | · | 23.7 s<br>27.8 MiB |

### fateman-mul.ZZ

| n | Poly Mojo | FLINT | SymPy | Singular |
|---|---|---|---|---|
| 10 | 583 ms<br>2.07 MiB | 1.06 ms<br>< 1 MiB | 330 ms<br>2.51 MiB | 1.78 ms<br>1.72 MiB |
| 15 | 9.79 s<br>7.52 MiB | 13.5 ms<br>1.68 MiB | 7.33 s<br>12.5 MiB | 17.9 ms<br>5.36 MiB |
| 20 | 104 s<br>28.5 MiB | 123 ms<br>7.62 MiB | 103 s<br>34.6 MiB | 142 ms<br>18.1 MiB |
| 30 | timeout | 9.35 s<br>1.46 GiB | timeout | 9.29 s<br>1.46 GiB |

### fateman-pow.ZZ

| n | Poly Mojo | FLINT | SymPy | Singular |
|---|---|---|---|---|
| 10 | 4.22 ms<br>< 1 MiB | < 1 ms<br>< 1 MiB | 2.37 ms<br>< 1 MiB | < 1 ms<br>< 1 MiB |
| 15 | 84.5 ms<br>1.15 MiB | < 1 ms<br>< 1 MiB | 10.7 ms<br>1.31 MiB | < 1 ms<br>< 1 MiB |
| 20 | 261 ms<br>2.75 MiB | 1.43 ms<br>1.27 MiB | 29.7 ms<br>3.29 MiB | 4.2 ms<br>1.35 MiB |
| 30 | 10.2 s<br>9.26 MiB | 7.02 ms<br>2.61 MiB | 197 ms<br>18 MiB | 77.5 ms<br>6.64 MiB |

### mp-div.ZZ

| n | Poly Mojo | FLINT | SymPy | Singular |
|---|---|---|---|---|
| 12 | timeout | 1.06 s<br>< 1 MiB | timeout | 1.74 s<br>140 MiB |

### mp-mul.ZZ

| n | Poly Mojo | FLINT | SymPy | Singular |
|---|---|---|---|---|
| 12 | 31.6 s<br>1.01e+03 MiB | 1.08 s<br>188 MiB | 46.5 s<br>1.57 GiB | 1.71 s<br>679 MiB |

### mp-pow.ZZ

| n | Poly Mojo | FLINT | SymPy | Singular |
|---|---|---|---|---|
| 12 | 82.9 ms<br>1.57 MiB | < 1 ms<br>1.09 MiB | 65 ms<br>2 MiB | 1.52 ms<br>< 1 MiB |

