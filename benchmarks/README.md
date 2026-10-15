# Benchmark design

This directory will hold the suite that compares Poly Mojo with open-source
polynomial software. For each workload it measures wall-clock time and peak
memory, checks that every library returned the same mathematical answer, and
publishes the outcome for every case, including the cases Poly Mojo loses.
This page fixes the design before the harness is written: which features are
measured, which libraries they are measured against, which inputs are used,
and how runs are timed, checked, and reported.

## What a reader should learn

Someone choosing a polynomial library usually asks three questions, and the
published results answer them in this order:

1. **Can it do my task for my coefficients?** The
   [feature matrix](#features-and-the-libraries-they-are-compared-with) states,
   for each feature and coefficient domain, which libraries are compared.
2. **How fast is it?** Per-feature tables give the median time for each case
   and a summary ratio against each competitor.
3. **Will it fit in memory?** The same tables give the peak memory used by the
   computation itself.

Poly Mojo also produces certificates that the other libraries do not. A fourth
table reports what certification costs, so readers can separate the price of
the algorithm from the price of the evidence.

## Ground rules

- **Same input, same answer.** Every library solves the identical input, and
  its answer is reduced to a canonical form and compared with the others before
  its time counts. A disagreement removes the case from the summary ratios
  until it is explained.
- **Comparable work.** Poly Mojo runs each case twice: in *comparable mode*
  (no retained witnesses, no checking, for example `witnesses=False` for
  Gröbner bases) and in *certified mode* (default evidence plus the matching
  `check`). Ratios against competitors use comparable mode.
- **One thread.** All libraries run single-threaded on a pinned core. A
  separate multi-threaded track can follow later; it is never mixed into the
  single-thread tables.
- **Exclude one-time costs from the measured call.** Mojo compilation, Python
  imports, CAS start-up, and input parsing are excluded from the timed region
  and reported once in their own table, because users who script short
  calculations do pay them.
- **No work limits.** Poly Mojo runs with the default `max_steps`
  (`UInt64.MAX`); competitors run without their own step or degree caps. Only
  the harness's wall-clock and memory limits apply.
- **Pinned and recorded.** Every result records the library version, Poly Mojo
  commit, host CPU, memory, operating system, and the case file's hash.
- **Everything is published.** Losses, timeouts, out-of-memory results, and
  errors stay in the tables. The suite includes cases chosen to be hard for
  Poly Mojo's algorithms, not only cases that suit them.

## Libraries

Only open-source software is in scope. SageMath is not a separate column: it
mostly delegates to Singular, FLINT, PARI, Giac, and msolve, which are measured
directly. Where Singular or Macaulay2 delegate a task to FLINT or factory, the
matrix compares the engine once rather than through each front end.

| Library | Version found (Oct 2026) | Language | License | Role | Driver |
|---|---|---|---|---|---|
| [SymPy](https://www.sympy.org) | 1.14.0 | Python | BSD-3-Clause | Peer | Python, `sympy.polys` objects |
| [python-flint](https://github.com/flintlib/python-flint) / [FLINT](https://flintlib.org) | 0.8.0 (conda) / FLINT 3.5.0 | C, Python bindings | MIT / LGPL-3.0+ | Reference | Python; a small C driver for functions the bindings do not expose |
| [PARI/GP](https://pari.math.u-bordeaux.fr) | 2.17.3 | C | GPL-2.0+ | Reference | `gp` script |
| [NTL](https://libntl.org) | 11.6.0 | C++ | LGPL-2.1+ | Reference | C++ driver |
| [Singular](https://www.singular.uni-kl.de) | 4.4.1 | C/C++ | GPL-2.0+ | Reference | Singular script |
| [Macaulay2](https://macaulay2.com) | pin at first run | C++, M2 | GPL | Reference | M2 script |
| [Giac](https://www-fourier.ujf-grenoble.fr/~parisse/giac.html) | 2.0.0 | C++ | GPL-3.0+ | Reference | `giac` script |
| [Maxima](https://maxima.sourceforge.io) | 5.49.0 | Common Lisp | GPL-2.0+ | Peer | Maxima batch file |
| [msolve](https://msolve.lip6.fr) | pin at first run | C | GPL-2.0+ | Reference | command line |
| [QEPCAD B](https://www.usna.edu/Users/cs/wcbrown/qepcad/B/QEPCAD.html), [Tarski](https://github.com/chriswestbrown/tarski) | pin at first run | C++ | see note | Specialist | batch input |
| [Redlog](https://www.redlog.eu) (REDUCE) | pin at first run | Lisp | BSD | Specialist | REDUCE script |
| [Z3](https://github.com/Z3Prover/z3), [cvc5](https://cvc5.github.io), [SMT-RAT](https://github.com/ths-rwth/smtrat), [Yices 2](https://yices.csl.sri.com) | pin at first run | C/C++ | MIT, BSD, MIT, GPL-3.0 | Specialist | SMT-LIB 2 files |
| [MPSolve](https://numpi.dm.unipi.it/software/mpsolve) | pin at first run | C | GPL-3.0 | Specialist | command line |
| [mpmath](https://mpmath.org), NumPy | 1.4.1, pin | Python | BSD | Context | Python |

Roles say how to read a comparison:

- **Peer** systems are general-purpose and use algorithm families close to
  Poly Mojo's. They give the most like-for-like comparison.
- **Reference** engines are the strongest open-source implementations of a
  task. They show the distance to the state of the art, which often uses a
  different algorithm class (FFT multiplication, F4 Gröbner bases).
- **Specialist** tools solve one problem class, such as CAD or nonlinear real
  satisfiability.
- **Context** tools are uncertified numerical solvers. Their times appear for
  orientation and never in a ratio, because they do not establish the same
  claim.

Some comparisons pit Poly Mojo against the implementation it follows, which
separates the cost of the language and data structures from the choice of
algorithm. These *algorithmic twins* get their own line in the report:

| Poly Mojo module | Follows | Twin comparison |
|---|---|---|
| Buchberger pair handling (`groebner`) | SymPy `groebnertools._buchberger` | SymPy `groebner(method="buchberger")` |
| Multivariate factorization (`_multivariate_factor`) | SymPy `factortools.dmp_zz_wang` | SymPy `factor_list` |
| Finite-field factorization, squarefree, PRS | SymPy `galoistools`, `sqfreetools`, `euclidtools` | SymPy with `modulus=`, `sqf_list`, `resultant` |
| CAD projection, lifting, coverings | SMT-RAT (McCallum, Lazard, coveringng), QEPCAD B | SMT-RAT, QEPCAD B |
| Lazard evaluation | CArL | none (CArL is used through SMT-RAT) |
| Real algebraic numbers, sparse modular gcd | Z3 `algebraic_numbers.cpp`, `polynomial.cpp` | Z3 (nlsat) on the CAD conjunctions |

## Features and the libraries they are compared with

● compared directly (same task, same domain). ◐ compared with a stated
difference in domain, output, or algorithm (see the family notes). A blank cell
means the comparison is not part of the suite, because the library lacks the
feature or another column already measures the same engine.

| Feature | Domains | SymPy | FLINT | PARI | NTL | Singular | M2 | Giac | Maxima | msolve | Specialists |
|---|---|---|---|---|---|---|---|---|---|---|---|
| Dense univariate multiplication and exact division | ZZ, GF(p) | ● | ● | ● | ● | | | ● | ● | | |
| Sparse multivariate multiplication and exact division | ZZ, QQ | ● | ● | | | ● | ● | ● | ● | | |
| Univariate gcd, resultant, discriminant | ZZ, QQ, GF(p) | ● | ● | ● | ● | ● | | ● | ● | | |
| Multivariate gcd and resultant | ZZ, QQ | ● | ● | ◐ | | ● | ● | ● | ● | | |
| Univariate factorization | ZZ, QQ | ● | ● | ● | ● | ● | | ● | ● | | |
| Univariate factorization | GF(p) | ● | ● | ● | ● | ● | | ● | ● | | |
| Factorization over extensions | QQi, AA, QQbar | ● | ◐ | ● | | ● | | ◐ | ● | | |
| Multivariate factorization | QQ, GF(p) | ● | ● | | | ● | | ● | ● | | |
| Gröbner basis, grevlex | GF(p) | ● | | | | ● | ● | ● | ◐ | ● | CoCoA 5 (optional) |
| Gröbner basis, grevlex | QQ | ● | ◐ | | | ● | ● | ● | ● | ● | CoCoA 5 (optional) |
| Gröbner basis, lex and elimination | QQ, GF(p) | ● | | | | ● | ● | ● | ● | ◐ | |
| Gröbner basis over extensions | QQi, AA | ● | | | | ● | ● | | | | |
| Ideal membership with cofactors | QQ, GF(p) | ◐ | | | | ● | ● | ◐ | ◐ | | |
| Real root isolation and refinement | ZZ, QQ | ● | ◐ | ◐ | | | ● | ● | ◐ | ● | |
| Exact complex roots with multiplicities | ZZ, QQ, QQi | ● | ● | | | | | | | | |
| Validated numerical complex roots | ZZ, QQ, balls | ◐ | ● | ◐ | | | | | | | MPSolve; mpmath, NumPy as context |
| Real and complex algebraic number arithmetic | AA, QQbar | ● | ● | ◐ | | ◐ | ◐ | | | | |
| Full cylindrical algebraic decomposition | ZZ, QQ | | | | | | ◐ | | | | QEPCAD B, Tarski, Redlog |
| Satisfiability of sign conditions | ZZ, QQ | | | | | | | | | | Z3, cvc5, SMT-RAT, Yices 2; QEPCAD B, Tarski, Redlog via ∃ |
| Formal power series | QQ, GF(p) | ● | ● | ● | | | | ◐ | ◐ | | |
| Interpolation and multipoint evaluation | QQ, GF(p) | ● | ● | ● | ● | | | | | | |
| Rational functions and partial fractions | QQ, QQi | ● | ◐ | | | | | ● | ● | | |
| Enclosure (ball) evaluation | QQ, balls | | ● | | | | | | | | mpmath as context |

Two kinds of measurement have no competitor and run as internal studies:
certification overhead (comparable mode, certified mode, and checker time),
and streaming against materialized output (peak memory of `cad.decompose_to`
against `cad.decompose`, root streams against covers, and chunked text against
whole strings). Alternative bases and batch broadcasting are measured for
scaling only.

## Workload families

Each family lists the Poly Mojo calls, the cases, the competitor calls, and how
answers are compared. Cases span easy to hard, so that each table includes the
region where a competitor's algorithm class wins. Parametric families are
generated with fixed seeds; curated instances name their source.

### Gröbner bases and ideal membership

Poly Mojo: `sparse.groebner` with `order="grevlex"` or `"lex"`, comparable mode
`witnesses=False`; certified mode keeps witnesses and adds
`sparse.check_groebner`. Membership: `sparse.reduce` and `sparse.contains` on a
prepared basis, then `sparse.membership` plus `sparse.check_membership` for
cofactors.

| Case | Parameters | Source |
|---|---|---|
| cyclic-n | n = 5, 6, 7 | SymbolicData; msolve examples |
| katsura-n | n = 5 … 9 | SymbolicData |
| eco-n, noon-n, reimer-n | eco 6 … 9, noon 4 … 7, reimer 4, 5 | SymbolicData |
| Dense random quadratics | k equations in k variables, k = 4 … 7 | generated |
| Implicitization (lex) | parametric curves and surfaces of degree 2 … 6 | generated |
| Small lex systems | katsura-4, katsura-5, cyclic-5 | SymbolicData |
| Gaussian and algebraic coefficients | katsura-n with coefficients in QQi or QQ(√2), n = 4 … 6 | generated |
| Membership | 1000 reductions of ideal members and nonmembers against a prepared basis | generated |

Fields: QQ, and GF(65521), a prime every compared tool accepts. Competitors:
SymPy `groebner(..., order=..., method="buchberger")` and `method="f5b"`
(`modulus=p` for GF(p)); Singular `std` and the best of `slimgb`/`modStd`;
Macaulay2 `gb` and its F4 strategy; msolve; Giac `gbasis`; Maxima
`poly_reduced_grobner`; optionally CoCoA 5 `ReducedGBasis`. Membership with
cofactors compares with Singular `lift` and Macaulay2 `//`. SymPy, Giac, and
Maxima only return normal forms, hence ◐.

Check: the reduced, monic basis in canonical order, compared by digest. A tool
that returns a non-reduced basis is interreduced by the harness, untimed.
Report the algorithm class next to each time: Buchberger with pair criteria
(Poly Mojo, SymPy `buchberger`, Singular `std`, Maxima) or F4/F5-style
linear algebra (msolve, Giac, Macaulay2 F4, SymPy `f5b`).

### Cylindrical algebraic decomposition and real constraints

Poly Mojo: `cad.decompose` (Lazard default, and `lazard=False` for McCallum),
`cad.decompose_to` with `cad.checker` for streaming, `cad.solve` and
`cad.sample` for conjunctions, and `fixed=` slices.

| Case | Parameters | Source |
|---|---|---|
| Classic CAD problems | 2–5 variables, e.g. Collins–Johnson, Davenport–Heintz, Solotareff, x-axis ellipse | Wilson–Bradford–Davenport CAD example repository |
| Random dense families | n = 2: k ≤ 4 polynomials of degree 2 … 10; n = 3: degree 2 … 4; n = 4: degree 2 | generated |
| Sphere and hyperplane | unit n-sphere with one or two hyperplanes, n = 2 … 5 | generated |
| Variable-order study | every variable order for n ≤ 4 | generated |
| Conjunctions | SMT-LIB QF_NRA instances with at most 6 variables that are pure conjunctions of sign conditions | SMT-LIB benchmark library |
| Paired SAT/UNSAT | the same constraint set with a satisfiable and an unsatisfiable variant | generated |

Competitors for full decomposition: QEPCAD B with `full-cad`, Tarski, Redlog
`rlcad`, and the Macaulay2 CAD package (◐ where it builds open cells only).
Competitors for satisfiability: Z3 (nlsat), cvc5 (cylindrical algebraic
coverings), SMT-RAT, Yices 2 (MCSAT with libpoly), and the CAD tools through
existential quantifier elimination. `cad.solve` accepts a conjunction, so
SMT-LIB instances with Boolean structure stay out of the suite.

Check: satisfiable or unsatisfiable must agree; a satisfying point is
substituted exactly and its signs checked independently. For full CAD, every
tool's sample points are sign-checked and its cell count is reported. Cell
counts depend on the projection operator, so they are reported, not compared.
Also report the number of projection factors and the peak memory of the
streaming route against the materialized one.

### Univariate factorization

Poly Mojo: `dense.factor`; certified mode adds the product check.

| Case | Parameters | Source |
|---|---|---|
| Swinnerton-Dyer polynomials | S4 … S7 (degree 16 … 128) | `sympy.polys.specialpolys` |
| Cyclotomic products | x^N − 1 for N = 360, 2520, 5040 | generated |
| Products of random irreducibles | k ∈ {2, 8} factors of degree 10 … 100, 16- and 256-bit coefficients | generated |
| Hard recombination | van Hoeij's and Zimmermann's test polynomials | published test sets |
| Repeated factors | f³g² with random f, g | generated |
| Finite fields | random degree 100 … 2000 over p = 3, 65521, and a 61-bit prime | generated |
| Extensions | x^n ± 2 and cyclotomic polynomials over QQi, QQ(√2), and QQbar | generated |

Competitors: FLINT (`fmpz_poly.factor`, `nmod_poly.factor`), NTL, PARI
(`factor`, `factormod`, `nffactor`), Singular `factorize` (extensions through a
`minpoly`), Giac `factor`/`cfactor`, Maxima `factor`/`gfactor`, SymPy
`factor_list` with `modulus=`, `gaussian=True`, or `extension=`. Over QQbar,
FLINT's `qqbar` roots give the linear factors, hence ◐.

Check: the product identity and the factor multiset after normalization
(primitive with positive leading coefficient over ZZ, monic over fields).

### Multivariate factorization and gcd

Poly Mojo: `sparse.factor`, `sparse.gcd`, `sparse.resultant`.

| Case | Parameters | Source |
|---|---|---|
| Fateman–Liao gcd families | `fateman_poly_F_1`, `F_2`, `F_3`, n = 2 … 8 | `sympy.polys.specialpolys` |
| Wang's examples | the Wang (1978) test polynomials | SymPy factorization tests |
| Dense products | (1 + x + y + z)^k · (2 + x + y + z)^k, k = 5 … 15 | generated |
| Sparse random products | 3 … 8 variables, 10 … 100 terms per factor | generated |
| Resultants | eliminate one variable from random pairs in 2–3 variables, degree ≤ 10 | generated, CAD projection sizes |

Competitors: FLINT (`fmpz_mpoly` / `fmpq_mpoly` `factor`, `gcd`, `resultant`),
Singular, Macaulay2, Giac, Maxima, SymPy. PARI computes multivariate gcds and
resultants in its recursive representation, hence ◐.

### Arithmetic

Dense univariate over ZZ and GF(p): degree n = 10², 10³, 10⁴, 10⁵ and
coefficient sizes 8, 64, and 1024 bits; products, squares, and exact division
of the product by one factor. Sparse multivariate: Fateman's
f = (1 + x + y + z + t)^n, f·(f + 1) for n = 10, 15, 20, 30, and the
Monagan–Pearce sparse product
(1 + x + y + 2z² + 3t³ + 5u⁵)^12 · (1 + u + t + 2z² + 3y³ + 5x⁵)^12.

Poly Mojo uses Karatsuba for dense products; FLINT, NTL, and PARI switch to
FFT-based methods at large degrees. The scaling plot should make that crossover
visible rather than hide it in an average.

### Univariate gcd and resultants

Random dense f = g·a and h = g·b with a planted gcd g, degree 50 … 2000 and 32-
to 512-bit coefficients, over ZZ and GF(p); resultants of random pairs of
degree 10 … 200; discriminants of the same polynomials. Competitors: FLINT,
NTL, PARI (`gcd`, `polresultant`, `poldisc`), Singular, Giac, Maxima, SymPy.

### Real roots

Poly Mojo: `dense.real_roots` (exact algebraic values), `dense.real_root_cover`
with `roots.refine` (validated intervals), and `dense.count_roots` with a
prepared `dense.sturm_sequence`.

| Case | Parameters | Source |
|---|---|---|
| Mignotte | x^n − 2(ax − 1)², n = 10 … 400, a = 100 | classic |
| Wilkinson | ∏(x − i) for i = 1 … n, n = 20 … 640 | classic |
| Chebyshev | T_n, n = 100 … 1000 | generated |
| Random dense | ±1 and 64-, 1024-bit coefficients, n = 100 … 2000 | generated |
| Squarefree-free | products with repeated factors | generated |
| Refinement | refine every root to 2⁻⁵³ and 2⁻¹⁰⁰⁰ | all of the above |

Competitors: SymPy `Poly.intervals` and `real_roots`, msolve (univariate
input), Giac `realroot`, Macaulay2 `RealRoots`, FLINT
`arb_fmpz_poly_complex_roots` filtered to real roots (◐: complex search),
PARI `polrootsreal` (◐: approximations, not intervals), Maxima `realroots`
(◐: rational approximations).

Check: the number of distinct real roots, and each interval containing exactly
one root of a high-precision FLINT/Arb reference.

### Complex roots and algebraic numbers

Poly Mojo: `dense.complex_roots` (exact values with multiplicities),
`dense.complex_root_cover` (validated rectangles), and arithmetic on
`algebraic.Real` and `algebraic.Complex`.

Cases: the real-root families above, Mandelbrot polynomials of degree
2^k − 1 (k = 6 … 10) from the MPSolve test set, and powers f^k for multiplicity
handling. Algebraic numbers: minimal polynomials of √2 + √3 + … + √p_k for
k = 2 … 5, sums and products of roots of random quintics, and signs of
polynomials at algebraic points chosen to cause heavy cancellation.

Competitors: exact roots with SymPy `Poly.all_roots` and FLINT
`qqbar_roots_fmpz_poly`; validated covers with FLINT
`arb_fmpz_poly_complex_roots` and MPSolve; PARI `polroots` (◐); mpmath
`polyroots` and NumPy `roots` as context. Algebraic arithmetic with FLINT
`qqbar`, SymPy `minimal_polynomial` and algebraic fields, and PARI number
fields (◐).

Check: counts with multiplicity, disjoint enclosures, and each enclosure
containing a reference root.

### Series, interpolation, rational functions, and evaluation

- **Formal series:** reciprocal, exponential, and composition truncated at
  order 10², 10³, 10⁴ over QQ and GF(p). FLINT `*_inv_series`, `*_exp_series`,
  `*_compose_series`; PARI series with `O(x^n)`; SymPy `ring_series`; Giac and
  Maxima `taylor` (◐: expression-level series).
- **Interpolation and multipoint evaluation:** 10² … 10⁴ points over QQ and
  GF(p). FLINT, PARI `polinterpolate`, NTL, SymPy `interpolate`.
- **Rational functions:** normalization of large quotients and partial
  fractions of 1/((x − 1)^k · ∏(x² + i)). SymPy `cancel`/`apart`, Giac and
  Maxima `partfrac`; FLINT `fmpz_poly_q` for normalization only (◐).
- **Enclosure evaluation:** degree 10³ … 10⁵ at many points at 64, 256, and
  1024 bits, including points near roots. FLINT `arb_poly`/`acb_poly`
  evaluation; mpmath `polyval` as context.

## Measurement

### Process model

Each run starts a fresh process for one library and one case. The driver
reads the case, builds the library's objects, and only then starts the timer
around the single call under test. It writes one JSON record with the outcome,
times, memory, and the canonical answer. Python drivers construct `sympy.polys`
and python-flint objects directly, so expression parsing stays out of the
timed region; SymPy runs with an explicit `SYMPY_GROUND_TYPES` (gmpy2) and
clears its cache between repetitions. Poly Mojo drivers are compiled once with
`mojo build`, and the build time is recorded separately.

CAS scripts use each system's own clock (`rtimer` in Singular, `getabstime` in
GP, `elapsedTime` in Macaulay2, `time` in Giac, `elapsed_real_time` in Maxima).
Command-line tools without an internal clock (msolve, QEPCAD B, SMT solvers,
MPSolve) are timed as a whole process; a baseline run with a trivial input of
the same shape is subtracted and both values are kept.

### Time

- Wall-clock time from a monotonic clock, with CPU time recorded alongside.
  CPU time well above wall time reveals a hidden thread pool.
- Calls under one second repeat in-process with fresh input copies until at
  least one second and five runs have elapsed. The reported value is the median
  of three processes' medians; the minimum is kept for reference.
- Calls over one second run once per process, three processes per case; calls
  over a minute run once.
- Single thread everywhere: `taskset` to one isolated core,
  `OMP_NUM_THREADS=1`, FLINT's thread count set to one, msolve `-t 1`, and the
  equivalent settings elsewhere.

### Memory

The primary memory figure is the computation's *incremental peak*: the highest
resident set size during the call minus the resident size just before it.
On Linux, in-process drivers (Mojo, Python, C) record `VmRSS`, write `5` to
`/proc/self/clear_refs` to reset the high-water mark, run the call, and read
`VmHWM`. External tools report the whole-process peak from `wait4`, minus the
baseline run that loads the input and skips the call. Both the incremental
and the total peak are stored; total peak includes interpreter and runtime
overhead, which users also pay.

Systems that reserve memory up front need generous settings so that a
configured ceiling is not mistaken for the algorithm's need: PARI `parisizemax`,
SBCL's dynamic space for Maxima, and similar options are set to the harness
memory limit.

### Limits and outcomes

The default limits are 600 seconds and 16 GiB per run, with a 3600-second tier
for hard cases. Memory is capped with a cgroup (`systemd-run --scope -p
MemoryMax=…`) rather than `RLIMIT_AS`, because garbage-collected runtimes
reserve large virtual ranges. Each run ends with one outcome: `ok`, `timeout`,
`out-of-memory`, `error`, `unsupported`, or `wrong`.

### Host

The primary host is a Linux x86-64 machine with the performance governor,
turbo boost disabled, and no other load. A second run on Apple silicon covers
Poly Mojo's other supported platform; there, memory comes from `wait4` only.
Each result set records `lscpu`, memory size, kernel, and all versions.

## Correctness

Each family defines a canonical answer: a sorted reduced basis, a normalized
factor multiset, a root count with verified enclosures, a satisfiability
verdict with a checked point, and so on. The harness hashes it, and a case
enters the summary only when Poly Mojo agrees with at least one reference
engine. Disagreements are listed in the report with both answers. In certified
mode, the Poly Mojo checker's verdict is recorded as well; a failed check is a
`wrong` outcome even if the answer matches.

## Reporting

- **Per-feature tables.** One row per case, one column per library, showing
  median time and incremental peak memory, with outcomes in place of numbers
  where a run did not finish.
- **Summary ratios.** For each feature and competitor: the geometric mean of
  competitor time ÷ Poly Mojo time over cases both solved (above 1 means Poly
  Mojo was faster), the same ratio for memory, and the solved count `k/N` for
  each library. Ratios always name the cases they cover.
- **Scaling plots.** Log–log time and memory against the family parameter
  (degree, variables, coefficient size), which shows crossovers such as
  Karatsuba against FFT or Buchberger against F4.
- **Solved-count plots** for CAD and satisfiability: instances solved within a
  given time, the usual presentation for those communities.
- **Certification overhead.** Comparable mode, certified mode, and checker time
  per family.
- **One-time costs.** Driver build time, process start-up, and import time per
  library.

The published summary goes to a documentation page, with the raw records
committed under `results/`. The page states the host and versions and does not
claim that one host establishes a general speed advantage.

## Harness layout

```text
benchmarks/
  README.md                 this design; later, how to run the suite
  cases/<family>/*.json     case definitions, one file per case
  generators/               deterministic generators for parametric families
  convert/                  writers for each system's input syntax
  drivers/
    poly_mojo/              one Mojo program per family, built with `mojo build`
    python/                 SymPy, python-flint, mpmath, NumPy drivers
    native/                 C and C++ drivers for FLINT, NTL
    scripts/                Singular, GP, Macaulay2, Giac, Maxima, REDUCE templates
  run.py                    isolation, limits, timing, memory, outcomes
  check.py                  canonical answers and cross-library agreement
  report.py                 tables, ratios, plots, documentation page
  results/<host>/<date>/    raw JSON records and the environment description
```

A case file holds an identifier, family, coefficient domain (with the modulus
or the defining polynomial and isolating interval for algebraic coefficients),
variable names, monomial order or variable order, the polynomials as exponent
tuples with exact coefficients, generator parameters and seed, and a tier.
The converters write each system's syntax from it; Poly Mojo receives the
canonical versioned polynomial text that `sparse.loads` and `dense.loads` read,
outside the timed region.

SymPy, python-flint, mpmath, PARI, Singular, Giac, Maxima, NTL, and Z3 are
available from conda-forge and belong in a `bench` pixi environment beside the
existing Mojo toolchain; cvc5 is on PyPI. Macaulay2, msolve, QEPCAD B, Tarski,
REDUCE, SMT-RAT, Yices 2, and MPSolve are not on conda-forge and go into a
pinned container image built from tagged sources.

## Rollout

1. **Pilot:** the harness, case format, and correctness check for Gröbner
   bases against SymPy, Singular, and msolve, end to end through a draft
   report.
2. **First public release:** Gröbner bases, CAD and satisfiability,
   univariate and multivariate factorization, real roots, and arithmetic,
   against SymPy, FLINT, PARI, Singular, msolve, QEPCAD B or Tarski, Z3, and
   cvc5.
3. **Second release:** gcds and resultants, extension fields, complex roots,
   and algebraic numbers, adding Macaulay2, Giac, Maxima, NTL, Redlog, SMT-RAT,
   Yices 2, and MPSolve.
4. **Third release:** series, interpolation, rational functions, enclosure
   evaluation, and the internal streaming and certification studies.
