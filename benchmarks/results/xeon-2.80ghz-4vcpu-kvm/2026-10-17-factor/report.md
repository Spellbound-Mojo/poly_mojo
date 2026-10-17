# Factorization

Poly Mojo at 5157988 (records.jsonl; the base commit 181c723 is in records-base-181c723.jsonl). Competitors: python-flint 0.9.0 (FLINT 3.6.0), Singular 4.4.1, SymPy 1.14.0. The SymPy rows for zz-* cases ran before the harness pinned SYMPY_GROUND_TYPES=gmpy and delegate to python-flint (their times match FLINT's); the other SymPy rows are pure SymPy.

Records: `2026-10-17-factor`. Times are medians of in-process repetitions on one pinned core. Ratio is the other tool's time over Poly Mojo's (above 1: Poly Mojo is faster). "agree" means every tool that finished returned the same normalized factor multiset and its product equals the input.

| case | polymojo | flint | singular | sympy | flint ratio | singular ratio | sympy ratio | agree |
|---|---|---|---|---|---|---|---|---|
| zz-cyclotomic-360 | 1.92 s | 87.66 ms | 3.65 s | 98.81 ms | 0.0456 | 1.9 | 0.0514 | yes |
| zz-cyclotomic-2520 | timeout | 52.49 s | timeout | 53.09 s |  |  |  | yes |
| zz-cyclotomic-5040 | skipped | timeout | skipped | timeout |  |  |  |  |
| zz-product-k2-d10-b16 | 1.69 ms | 0.35 ms | 0.44 ms | 0.40 ms | 0.209 | 0.259 | 0.235 | yes |
| zz-product-k2-d25-b16 | 8.00 ms | 0.87 ms | 1.05 ms | 0.96 ms | 0.109 | 0.131 | 0.12 | yes |
| zz-product-k2-d50-b16 | 47.40 ms | 2.51 ms | 3.08 ms | 2.68 ms | 0.0529 | 0.0651 | 0.0566 | yes |
| zz-product-k2-d100-b16 | 183.17 ms | 14.45 ms | 15.99 ms | 14.57 ms | 0.0789 | 0.0873 | 0.0795 | yes |
| zz-product-k2-d10-b256 | 6.54 ms | 1.35 ms | 1.32 ms | 1.38 ms | 0.206 | 0.202 | 0.212 | yes |
| zz-product-k2-d25-b256 | 26.83 ms | 3.73 ms | 3.78 ms | 3.88 ms | 0.139 | 0.141 | 0.145 | yes |
| zz-product-k2-d50-b256 | 128.28 ms | 9.41 ms | 8.54 ms | 8.76 ms | 0.0734 | 0.0666 | 0.0683 | yes |
| zz-product-k2-d100-b256 | 452.73 ms | 37.92 ms | 39.46 ms | 39.05 ms | 0.0838 | 0.0872 | 0.0863 | yes |
| zz-product-k8-d10-b16 | 52.11 ms | 6.07 ms | 6.67 ms | 6.53 ms | 0.116 | 0.128 | 0.125 | yes |
| zz-product-k8-d25-b16 | 539.10 ms | 18.01 ms | 24.69 ms | 18.63 ms | 0.0334 | 0.0458 | 0.0346 | yes |
| zz-product-k8-d50-b16 | 2.09 s | 54.57 ms | 66.74 ms | 55.27 ms | 0.0261 | 0.0319 | 0.0264 | yes |
| zz-product-k8-d100-b16 | 8.39 s | 127.13 ms | 194.48 ms | 127.10 ms | 0.0151 | 0.0232 | 0.0151 | yes |
| zz-product-k8-d10-b256 | 321.17 ms | 22.11 ms | 22.00 ms | 23.55 ms | 0.0689 | 0.0685 | 0.0733 | yes |
| zz-product-k8-d25-b256 | 1.53 s | 81.08 ms | 86.45 ms | 83.54 ms | 0.053 | 0.0566 | 0.0547 | yes |
| zz-product-k8-d50-b256 | 21.32 s | 225.33 ms | 261.55 ms | 220.04 ms | 0.0106 | 0.0123 | 0.0103 | yes |
| zz-product-k8-d100-b256 | 75.15 s | 589.14 ms | 587.32 ms | 598.58 ms | 0.00784 | 0.00782 | 0.00797 | yes |
| zz-repeated-d10 | 1.82 ms | 0.17 ms | 0.21 ms | 0.23 ms | 0.0927 | 0.115 | 0.124 | yes |
| zz-repeated-d20 | 4.78 ms | 0.41 ms | 0.54 ms | 0.48 ms | 0.0865 | 0.114 | 0.102 | yes |
| zz-repeated-d40 | 17.22 ms | 1.59 ms | 1.85 ms | 1.74 ms | 0.0924 | 0.108 | 0.101 | yes |
| zz-swinnerton-dyer-4 | 4.65 ms | 0.41 ms | 0.49 ms | 0.46 ms | 0.0887 | 0.105 | 0.0994 | yes |
| zz-swinnerton-dyer-5 | 175.75 ms | 2.08 ms | 2.54 ms | 2.22 ms | 0.0118 | 0.0145 | 0.0126 | yes |
| zz-swinnerton-dyer-6 | 97.76 ms | 8.98 ms | 11.77 ms | 9.61 ms | 0.0919 | 0.12 | 0.0983 | yes |
| zz-swinnerton-dyer-7 | 1.91 s | 73.91 ms | 194.50 ms | 67.86 ms | 0.0386 | 0.102 | 0.0355 | yes |
| gf-p3-d100 | 2.66 ms | 0.33 ms | 0.52 ms | 111.92 ms | 0.126 | 0.195 | 42.1 | yes |
| gf-p3-d250 | 12.48 ms | 1.79 ms | 2.69 ms | 954.30 ms | 0.143 | 0.216 | 76.4 | yes |
| gf-p3-d500 | 99.57 ms | 16.17 ms | 26.48 ms | 21.01 s | 0.162 | 0.266 | 211 | yes |
| gf-p3-d1000 | 371.94 ms | 38.23 ms | 74.94 ms | 63.33 s | 0.103 | 0.201 | 170 | yes |
| gf-p3-d2000 | 2.55 s | 237.58 ms | 288.27 ms | timeout | 0.0932 | 0.113 |  | yes |
| gf-p61-d100 | 7.49 ms | 4.48 ms | unsupported | 2.43 s | 0.598 |  | 324 | yes |
| gf-p61-d250 | 75.02 ms | 66.50 ms | unsupported | 38.47 s | 0.886 |  | 513 | yes |
| gf-p61-d500 | 325.45 ms | 230.96 ms | unsupported | timeout | 0.71 |  |  | yes |
| gf-p61-d1000 | 1.67 s | 983.86 ms | unsupported | skipped | 0.59 |  |  | yes |
| gf-p61-d2000 | 14.04 s | 5.63 s | unsupported | skipped | 0.401 |  |  | yes |
| gf-p65521-d100 | 3.34 ms | 1.39 ms | 1.61 ms | 1.24 s | 0.415 | 0.481 | 370 | yes |
| gf-p65521-d250 | 27.18 ms | 11.90 ms | 12.52 ms | 25.04 s | 0.438 | 0.461 | 921 | yes |
| gf-p65521-d500 | 133.94 ms | 60.46 ms | 57.38 ms | 202.51 s | 0.451 | 0.428 | 1.51e+03 | yes |
| gf-p65521-d1000 | 670.51 ms | 239.83 ms | 248.46 ms | timeout | 0.358 | 0.371 |  | yes |
| gf-p65521-d2000 | 4.88 s | 1.44 s | 1.09 s | skipped | 0.294 | 0.224 |  | yes |
| mzz-dense-k5 | 63.68 ms | 0.49 ms | 0.77 ms | 14.95 ms | 0.0077 | 0.0121 | 0.235 | yes |
| mzz-dense-k7 | 178.71 ms | 0.86 ms | 1.43 ms | 36.38 ms | 0.00483 | 0.00801 | 0.204 | yes |
| mzz-dense-k10 | 1.14 s | 1.27 ms | 2.73 ms | 139.64 ms | 0.00111 | 0.00239 | 0.122 | yes |
| mzz-dense-k12 | 3.75 s | 1.91 ms | 4.42 ms | 299.92 ms | 0.000509 | 0.00118 | 0.0799 | yes |
| mzz-dense-k15 | 12.18 s | 3.20 ms | 8.34 ms | 867.28 ms | 0.000263 | 0.000685 | 0.0712 | yes |
| mzz-sparse-n3-t10 | 16.60 ms | 1.84 ms | 1.82 ms | 42.26 ms | 0.111 | 0.11 | 2.55 | yes |
| mzz-sparse-n3-t30 | 25.46 ms | 2.50 ms | 2.95 ms | 61.15 ms | 0.0984 | 0.116 | 2.4 | yes |
| mzz-sparse-n4-t20 | 536.30 ms | 4.83 ms | 5.73 ms | 280.32 ms | 0.00901 | 0.0107 | 0.523 | yes |
| mzz-sparse-n5-t30 | 510.39 ms | 36.31 ms | 15.39 ms | 1.85 s | 0.0712 | 0.0302 | 3.63 | yes |
| mzz-sparse-n6-t30 | 957.93 ms | 157.30 ms | 74.05 ms | 8.41 s | 0.164 | 0.0773 | 8.78 | yes |
| mzz-sparse-n8-t30 | 7.99 s | 742.73 ms | 463.82 ms | 88.01 s | 0.0929 | 0.058 | 11 | yes |
| mzz-sparse-n8-t100 | 5.09 s | 46.13 s | 7.75 s | 128.42 s | 9.07 | 1.52 | 25.3 | yes |
| mzz-wang-f6 | 0.42 ms | 0.02 ms | 0.03 ms | 1.27 ms | 0.0506 | 0.0736 | 3.01 | yes |
| mzz-wang-f1 | 1.81 ms | 0.03 ms | 0.06 ms | 1.65 ms | 0.0173 | 0.0326 | 0.913 | yes |
| mzz-wang-f7 | 7.64 ms | 0.42 ms | 0.71 ms | 10.74 ms | 0.0551 | 0.0925 | 1.41 | yes |
| mzz-wang-f4 | 4.19 ms | 1.23 ms | 1.27 ms | 8.10 ms | 0.295 | 0.304 | 1.94 | yes |
| mzz-wang-f3 | 2.99 ms | 0.43 ms | 0.52 ms | 7.02 ms | 0.144 | 0.174 | 2.35 | yes |
| mzz-wang-w2 | 8.64 ms | 0.46 ms | 0.48 ms | 11.14 ms | 0.0528 | 0.056 | 1.29 | yes |
| mzz-wang-f2 | 3.71 ms | 0.42 ms | 0.46 ms | 5.59 ms | 0.113 | 0.123 | 1.51 | yes |
| mzz-wang-f5 | 9.53 ms | 1.33 ms | 1.55 ms | 82.30 ms | 0.139 | 0.162 | 8.64 | yes |
| mzz-wang-w1 | 11.25 ms | 1.44 ms | 1.58 ms | 23.32 ms | 0.128 | 0.14 | 2.07 | yes |
