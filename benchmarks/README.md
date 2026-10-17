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
| [python-flint](https://github.com/flintlib/python-flint) / [FLINT](https://flintlib.org) | 0.9.0 (PyPI), bundling FLINT 3.6.0 | C, Python bindings | MIT / LGPL-3.0+ | Reference | Python; a C driver for what the bindings do not expose (`qqbar`, real-root isolation, exact interpolation, `fmpz_poly_q`) |
| [PARI/GP](https://pari.math.u-bordeaux.fr) | 2.17.3 (conda-forge; 2.19.0 upstream) | C | GPL-2.0+ | Reference | `gp` script |
| [NTL](https://libntl.org) | 11.6.0 | C++ | LGPL-2.1+ | Reference | C++ driver |
| [Singular](https://www.singular.uni-kl.de) | 4.4.1 | C/C++ | GPL-2.0+ | Reference | Singular script |
| [Macaulay2](https://macaulay2.com) | pin at first run | C++, M2 | GPL | Reference | M2 script |
| [Giac](https://www-fourier.ujf-grenoble.fr/~parisse/giac.html) | 2.0.0 (conda-forge; 2.1.0 upstream) | C++ | GPL-3.0+ | Reference | `giac` script |
| [Maxima](https://maxima.sourceforge.io) | 5.49.0 | Common Lisp | GPL-2.0+ | Peer | Maxima batch file |
| [msolve](https://github.com/algebraic-solving/msolve) | 0.11.0 | C | GPL-2.0+ | Reference | command line |
| [Tarski](https://github.com/chriswestbrown/tarski), with QEPCAD B | 1.42, bundling QEPCAD B 1.80 | C++ | ISC-style | Specialist | batch input (`tarski`, `qepcad`) |
| [Redlog](https://www.redlog.eu) (REDUCE) | pin at first run | Lisp | BSD | Specialist | REDUCE script |
| [Z3](https://github.com/Z3Prover/z3), [cvc5](https://cvc5.github.io), [SMT-RAT](https://github.com/ths-rwth/smtrat), [Yices 2](https://yices.csl.sri.com) | pin at first run; cvc5 1.4.2, Yices 2.7.0 | C/C++ | MIT, BSD-3, MIT, GPL-3.0 | Specialist | SMT-LIB 2 files |
| [MPSolve](https://numpi.dm.unipi.it/software/mpsolve) | 3.2.x | C | GPL-3.0 | Specialist | command line |
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
| Multivariate factorization | QQ, GF(p) | ● | ● | ● | | ● | | ● | ● | | |
| Gröbner basis, grevlex | GF(p) | ● | | | | ● | ● | ● | | ● | CoCoA 5 (optional) |
| Gröbner basis, grevlex | QQ | ● | ◐ | | | ● | ● | ● | ● | ● | CoCoA 5 (optional) |
| Gröbner basis, lex and elimination | QQ, GF(p) | ● | | | | ● | ● | ● | ◐ | ◐ | |
| Gröbner basis over extensions | QQi, AA | ● | | | | ● | ● | | | | |
| Ideal membership with cofactors | QQ, GF(p) | ◐ | | | | ● | ● | ◐ | ◐ | | |
| Real root isolation and refinement | ZZ, QQ | ● | ● | ◐ | | | ● | ● | ◐ | ● | CoCoA 5 (optional) |
| Exact complex roots with multiplicities | ZZ, QQ | ● | ● | | | | | | | | |
| Validated numerical complex roots | ZZ, QQ, balls | ◐ | ● | ◐ | | | | | | | MPSolve; mpmath, NumPy as context |
| Real and complex algebraic number arithmetic | AA, QQbar | ● | ● | ◐ | | ◐ | ◐ | | | | |
| Full cylindrical algebraic decomposition | ZZ, QQ | | | | | | | | | | QEPCAD B, Tarski, Redlog |
| Satisfiability of sign conditions | ZZ, QQ | | | | | | | | | | Z3, cvc5, SMT-RAT, Yices 2; QEPCAD B, Tarski, Redlog via ∃ |
| Formal power series | QQ, GF(p) | ● | ● | ● | | | | ◐ | ◐ | | |
| Interpolation and multipoint evaluation | QQ, GF(p) | ● | ● | ● | ● | | | | | | |
| Rational functions and partial fractions | QQ | ● | ◐ | | | | | ● | ● | | |
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
| cyclic-n | n = 5, 6, 7 | SymbolicData |
| katsura-n | n = 5 … 9 | SymbolicData |
| eco-n, noon-n, reimer-n | eco 6 … 9, noon 4 … 7, reimer 4, 5 | SymbolicData |
| Dense random quadratics | k equations in k variables, k = 4 … 7 | generated |
| Implicitization (lex) | parametric curves and surfaces of degree 2 … 6 | generated |
| Small lex systems | katsura-4, katsura-5, cyclic-5 | SymbolicData |
| Gaussian and algebraic coefficients | katsura-n with coefficients in QQi or QQ(√2), n = 4 … 6 | generated |
| Membership | 1000 reductions of ideal members and nonmembers against a prepared basis | generated |

Fields: QQ, and GF(65521), a prime every compared tool accepts (msolve
requires a characteristic below 2³¹). Competitors:

- SymPy `groebner(..., order=..., method="buchberger")` and `method="f5b"`,
  with `modulus=p` for GF(p) and `domain=QQ_I` or `extension=` for extensions.
  SymPy's default order is lex, so the driver always passes `order`.
- Singular `std`, and the best of `slimgb` and `modStd`.
- Macaulay2 `gb`, plus `groebnerBasis(..., Strategy => "F4")` over GF(p) only,
  where that strategy is available (it is marked experimental).
- msolve `-g 2` for the reduced grevlex basis; over QQ it lifts modular
  bases. Its only other order is a two-block elimination order (`-e`), hence
  ◐ for lex.
- Giac `gbasis` (F4 modulo p, multimodular over QQ).
- Maxima's `grobner` package, `poly_reduced_grobner`, over QQ only (◐ for the
  lex row, which also covers GF(p)).
- FLINT `fmpz_mpoly_vec.buchberger_naive`, over ZZ only and without pair
  criteria (◐); its basis is made monic over QQ before comparison.
- Optionally CoCoA 5 `ReducedGBasis`.

Membership with cofactors compares with Singular `lift` and Macaulay2 `//`.
SymPy, Giac, and Maxima only return normal forms against the basis, hence ◐.

Check: the reduced, monic basis in canonical order, compared by digest. A tool
that returns a non-reduced basis is interreduced by the harness, untimed.
Report the algorithm class next to each time: Buchberger with pair criteria
(Poly Mojo, SymPy `buchberger`, Singular `std` and `slimgb`, Macaulay2 `gb`,
Maxima), signature-based (SymPy `f5b`), multimodular (Singular `modStd`), or
F4-style linear algebra (msolve, Giac, Macaulay2 F4).

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

Competitors for full decomposition: QEPCAD B with `full-cad`, Tarski, and
Redlog `rlcad`. SymPy has no multivariate CAD. The Macaulay2
CylindricalAlgebraicDecomposition package builds open CADs with the Lazard
projection, but it is not distributed with Macaulay2; add it as an open-cell
comparison only if a tagged release can be pinned.

Competitors for satisfiability: Z3 (nlsat), cvc5 (cylindrical algebraic
coverings, which require a LibPoly build), SMT-RAT (coverings and CAD
back ends), Yices 2 (MCSAT with libpoly, built with `--enable-mcsat`), and the
CAD tools through existential quantifier elimination. `cad.solve` accepts a
conjunction, so SMT-LIB instances with Boolean structure stay out of the suite.

Harness: `python -m harness.cad generate|run|report` (module
`harness/cad.py`, driver `drivers/poly_mojo/cad.mojo`, classic problems from
`harness/data/cad_example_bank_qepcad.txt`). QEPCAD B comes from a Tarski build
named by `$QEPCAD_HOME`, Z3 from the interpreter named by `$Z3_PYTHON`; absent
tools report `unsupported`.

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
| Hard recombination | van Hoeij's test polynomials | published test set |
| Repeated factors | f³g² with random f, g | generated |
| Finite fields | random degree 100 … 2000 over p = 3, 65521, and a 61-bit prime | generated |
| Extensions | x^n ± 2 and cyclotomic polynomials over QQi, QQ(√2), and QQbar | generated |

Competitors: FLINT (`fmpz_poly.factor`, `nmod_poly.factor`), NTL, PARI
(`factor`, `factormod`, `nffactor`), Singular `factorize` (extensions through a
`minpoly`), Giac `factor`, Maxima `factor` (with a minimal polynomial for
extensions) and `gfactor`, SymPy `factor_list` with `modulus=`,
`gaussian=True`, or `extension=`. For extensions, FLINT is compared over QQbar
only, where its `qqbar` roots give the linear factors, and Giac over QQi only,
with `cfactor`; hence ◐.

Check: the product identity and the factor multiset after normalization
(primitive with positive leading coefficient over ZZ, monic over fields).

Harness: `pixi run python -m harness.factor generate|run|report` (module
`harness/factor.py`) covers this family and the factorization half of the
next one over ZZ and GF(p), against FLINT, Singular and SymPy.

### Multivariate factorization and gcd

Poly Mojo: `sparse.factor`, `sparse.gcd`, `sparse.resultant`.

| Case | Parameters | Source |
|---|---|---|
| Fateman–Liao gcd families | `fateman_poly_F_1`, `F_2`, `F_3`, n = 2 … 8 | `sympy.polys.specialpolys` |
| Wang-algorithm test polynomials | `w_polys` and `f_polys`, the inputs of SymPy's `dmp_zz_wang` tests | `sympy.polys.specialpolys` |
| Dense products | (1 + x + y + z)^k · (2 + x + y + z)^k, k = 5 … 15 | generated |
| Sparse random products | 3 … 8 variables, 10 … 100 terms per factor | generated |
| Resultants | eliminate one variable from random pairs in 2–3 variables, degree ≤ 10 | generated, CAD projection sizes |

Competitors: FLINT (`fmpz_mpoly`, `fmpq_mpoly`, and `nmod_mpoly` `factor`,
`gcd`, `resultant`, `discriminant`), Singular, Macaulay2, Giac, Maxima, SymPy,
and PARI `factor`, which factors multivariate polynomials recursively. PARI
gcds and resultants work in that recursive representation and choose the
main variable implicitly, hence ◐ for gcds.

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
| Mignotte | x^n − 2(ax − 1)², n = 10 … 400, a = 100 | classic; MPSolve test set |
| Wilkinson | ∏(x − i) for i = 1 … n, n = 20 … 640 | classic; MPSolve test set |
| Chebyshev | T_n, n = 100 … 1000 | generated |
| Random dense | ±1 and 64-, 1024-bit coefficients, n = 100 … 2000 | generated |
| Repeated roots | products with repeated factors | generated |
| Refinement | refine every root to 2⁻⁵³ and 2⁻¹⁰⁰⁰ | all of the above |

Competitors: SymPy `Poly.intervals` and `real_roots` (continued fractions),
FLINT 3.6 `fmpz_poly_isolate_real_roots` and `arb_fmpz_poly_real_roots` with
`arb_fmpz_poly_refine_root_arb` (C driver; python-flint's `real_roots` raises
`NotImplementedError`), msolve (univariate input), Giac `realroot`, Macaulay2
`RealRoots`, optionally CoCoA 5 `RealRoots` and `RealRootRefine`. PARI
`polrootsreal` (◐) and Maxima `realroots` (◐) return guaranteed or rational
approximations rather than isolating intervals.

Check: the number of distinct real roots, and each interval containing exactly
one root of a high-precision FLINT/Arb reference.

### Complex roots and algebraic numbers

Poly Mojo: `dense.complex_roots` (exact values with multiplicities),
`dense.complex_root_cover` (validated rectangles), and arithmetic on
`algebraic.Real` and `algebraic.Complex`.

Cases: the real-root families above, Mandelbrot polynomials of degree
2^k − 1 (k = 6 … 10) and other polynomials from MPSolve's test set, and powers
f^k for multiplicity handling. Algebraic numbers: minimal polynomials of
√2 + √3 + … + √p_k for k = 2 … 5, sums and products of roots of random
quintics, and signs of polynomials at algebraic points chosen to cause heavy
cancellation.

Competitors: exact roots with SymPy `Poly.all_roots` and FLINT
`qqbar_roots_fmpz_poly` (C driver); validated covers with python-flint
`fmpz_poly.complex_roots` (disjoint Arb enclosures with multiplicities) and
MPSolve (`-G i` for isolation, with guaranteed inclusion radii); SymPy
`CRootOf` isolating rectangles refined with `eval_rational` (◐: exact
rectangles rather than balls); PARI `polroots` (◐: guaranteed relative
accuracy, but no enclosure); mpmath `polyroots` and NumPy `roots` as context.
Algebraic arithmetic with FLINT
`qqbar` (C driver), SymPy `minimal_polynomial` and algebraic fields, and PARI
number fields (◐).

Check: counts with multiplicity, disjoint enclosures, and each enclosure
containing a reference root.

### Series, interpolation, rational functions, and evaluation

- **Formal series:** reciprocal, exponential, and composition truncated at
  order 10², 10³, 10⁴ over QQ and GF(p). FLINT through python-flint's
  `fmpq_series` and `nmod_series`, or the C `*_inv_series`, `*_exp_series`,
  and `*_compose_series` functions; PARI series with `O(x^n)`; SymPy
  `ring_series` (`rs_series_inversion`, `rs_exp`, `rs_subs`); Giac and Maxima
  `taylor` (◐: expression-level series).
- **Interpolation and multipoint evaluation:** 10² … 10⁴ points over QQ and
  GF(p). FLINT (`fmpz_mod_poly.multipoint_evaluate` in python-flint, exact
  interpolation in the C driver), PARI `polinterpolate`, NTL, SymPy
  `interpolate`.
- **Rational functions:** normalization of large quotients and partial
  fractions of 1/((x − 1)^k · ∏(x² + i)). SymPy `cancel`/`apart`, Giac and
  Maxima `partfrac`; FLINT `fmpz_poly_q` (C driver) for normalization only (◐).
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
timed region. SymPy clears its cache between repetitions and always runs with
an explicit `SYMPY_GROUND_TYPES`: SymPy 1.14 switches to `flint` ground types
automatically when python-flint is installed, which hands some univariate work
to FLINT. The SymPy column uses `gmpy`; a `flint` run is reported as a separate
variant, since it is what many users get by default. Poly Mojo drivers are
compiled once with `mojo build`, and the build time is recorded separately.

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
  over a minute run once. (The pilot runs calls over one second once, see
  [the pilot](#gröbner-pilot).) Tools timed as a whole process (msolve) run
  short cases in five processes instead of repeating in-process.
- Single thread everywhere: every run is pinned to one CPU with
  `sched_setaffinity`, msolve gets `-t 1`, FLINT keeps its default of one
  thread, and the equivalent settings apply elsewhere.

### Memory

The primary memory figure is the computation's *incremental peak*: the highest
resident set size during the call minus the resident size just before it.
On Linux, in-process drivers (Mojo, Python, C) record `VmRSS`, write `5` to
`/proc/self/clear_refs` to reset the high-water mark, run the call, and read
`VmHWM`. Singular scripts do the same through `system("pid")` and a shell
command; that command costs Singular about 1.6 MiB, so Singular figures below
2 MiB are at the resolution floor. External tools report the whole-process peak
from `wait4`, minus a baseline run of a trivial system with the same variables
and field. Both the incremental and the total peak are stored; total peak
includes interpreter and runtime overhead, which users also pay.

Systems that reserve memory up front need generous settings so that a
configured ceiling is not mistaken for the algorithm's need: PARI `parisizemax`,
SBCL's dynamic space for Maxima, and similar options are set to the harness
memory limit.

### Limits and outcomes

The default limits are 600 seconds and 12 GiB per run. Memory is capped with a
child memory cgroup (v1 `memory.limit_in_bytes` or v2 `memory.max`, created per
run) rather than `RLIMIT_AS`, because garbage-collected runtimes reserve large
virtual ranges. Each run ends with one outcome: `ok`, `timeout`,
`out-of-memory`, `error`, `unsupported`, `skipped`, or `wrong`.

When a tool times out or runs out of memory on a ladder, its larger instances
on that ladder are recorded as `skipped`. A first pass can use a shorter limit;
rerunning with a longer `--timeout` retries only the instances that timed out
under the shorter one and continues their ladders. The results file is
append-only, and the last record for a case and tool wins.

### Host

Published results come from the benchmark host this suite was built on: an
Intel Xeon processor at 2.1 GHz with 4 vCPUs under KVM, 15 GiB of RAM, Ubuntu
24.04, and Linux 6.18. The process group running the harness may use about
13.4 GiB, which is why the memory cap is 12 GiB rather than the 16 GiB first
planned. A virtual machine does not expose the frequency governor or turbo
settings, and other tenants can add noise. The harness therefore pins each run
to one vCPU, keeps the other vCPUs idle during measurement, records the median
of repeated calls, and keeps the minimum and the CPU time beside it. Each
result set records `lscpu`, memory size, kernel, and all versions. A second
host, such as Apple silicon, can be added later; there, memory comes from
`wait4` only.

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
  README.md                 this design and how to run it
  pixi.toml, pixi.lock      the competitors and the harness, pinned
  harness/
    generate.py             deterministic case generators (cases/ is regenerated, not committed)
    polys.py                exact polynomials, record and infix text, canonical answers
    tools.py                one adapter per tool and mode; Poly Mojo driver builds
    measure.py              CPU pinning, cgroup memory cap, time limit, wait4 usage
    run.py                  ladders, repetitions, resume, raw records
    report.py               agreement, tables, ratios, plots
    build_msolve.py         msolve from its tagged source
    test_*.py               generator and format checks
  drivers/
    poly_mojo/              Mojo drivers, built per variable count with `mojo build -D`
    python/                 SymPy driver
  results/<host>/<date>-<family>/  raw records, environment, report, and plots
```

A case file holds an identifier, family, ladder and size, field (`null` for QQ
or a prime), monomial order, variable names, and the polynomials as exponent
tuples with exact coefficients. The generator rewrites the case files on every
run, and each record stores the SHA-256 of its case. Poly Mojo receives the
canonical versioned polynomial text that `sparse.loads` reads; Singular gets
an infix script; msolve gets its input format with denominators cleared. All
input conversion happens outside the timed region.

Poly Mojo itself is built and compiled with the repository's own workspace, so
the drivers use the toolchain the library is tested with. Mojo needs the
variable count at compile time, so the harness builds one driver binary per
variable count and field, caches it by the hash of the driver source and the
library build, and compiles everything before any measurement starts. A build
takes two to six minutes.

The `benchmarks` pixi workspace pins SymPy, gmpy2, Singular, and the msolve
build requirements from conda-forge, and python-flint 0.9.0 (bundling FLINT
3.6.0) from PyPI. Later competitors available on conda-forge (PARI, Giac,
Maxima, NTL, Z3) join the same workspace; cvc5 comes from PyPI. msolve is built
from its v0.11.0 tag by `harness/build_msolve.py`. Macaulay2, Tarski with
QEPCAD B, REDUCE, SMT-RAT, Yices 2, and MPSolve need the same treatment or a
pinned container image.

## Running the suite

```sh
cd benchmarks
pixi run poly-build      # build Poly Mojo with the repository workspace
pixi run msolve-build    # build msolve v0.11.0 into .cache/opt
pixi run test            # check the generators against SymbolicData
pixi run bench -- --family groebner --timeout 120 --single-above 1
pixi run bench -- --family groebner --timeout 600 --single-above 1   # retry the timeouts
pixi run bench -- --family streaming --processes 1
pixi run report          # or: pixi run report -- results/<host>/<date>
```

`--tools` and `--cases` (a regular expression on case identifiers) select a
subset. Each family writes to `results/<host>/<date>-<family>/records.jsonl`
unless `--results` names another file; the report chooses its layout from the
family.

## Gröbner pilot

The pilot runs the Gröbner family end to end against SymPy, Singular, and
msolve. Each ladder starts with instances every tool solves in milliseconds
and grows until only F4-class engines finish, so the scaling plots show where
each tool stops, not just who wins on small inputs.

| Ladder | Sizes | Variables | Fields and orders |
|---|---|---|---|
| katsura-n | 3 … 12 | n + 1 | QQ and GF(65521), grevlex; lex for 3 … 6 |
| cyclic-n | 4 … 9 | n | QQ and GF(65521), grevlex; lex for 4 … 6 |
| eco-n | 5 … 13 | n | QQ and GF(65521), grevlex |
| noon-n | 3 … 9 | n | QQ and GF(65521), grevlex |
| reimer-n | 3 … 6 | n | QQ and GF(65521), grevlex |
| random dense quadratics | 3 … 10 (lex 2 … 5) | n | QQ and GF(65521), grevlex and lex |

The pilot keeps calls over one second to a single process
(`--single-above 1`) and runs a first pass with a 120-second limit, then a
second pass at the full 600 seconds that retries only the instances that timed
out. SymPy's flint ground types run on the QQ grevlex ladders, where they change
the coefficient arithmetic; over GF(p), both variants share the same code path.
Results and the draft report are in [`results/`](results/).

## Streaming study

Streaming matters when the retained output, not the computation's working
set, dominates memory. The study compares, for the same verified claim, a
materialized route that keeps the whole result and then checks it with a
streamed route that feeds an incremental checker:

| Workload | Materialized route | Streamed route | Sizes |
|---|---|---|---|
| CAD of *k* random lines in the plane (O(*k*³) cells, rational samples) | `cad.decompose`, then `cad.check` | `cad.checker` and `cad.decompose_to` | *k* = 4 … 64, up to about 500,000 cells |
| CAD of *k* random circles (algebraic samples) | same | same | *k* = 2 … 16 |
| CAD of *k* random planes (three-level tower) | same | same | *k* = 2 … 8 |
| Real roots of Wilkinson polynomials, 64-bit accuracy | `real_root_cover`, then `roots.check` | `real_root_checker` and `real_root_cover_to` | degree 50 … 1600 |
| Real roots of Chebyshev T_n, 64-bit accuracy | same | same | degree 100 … 3200 |
| Write (1 + x + y + z + t)^n as text | `sparse.dumps` to a string, then a file | `sparse.dump` into a file sink | n = 10 … 80, up to about 1.9 million terms |
| Read the same polynomial back | read the file into a string, then `sparse.loads` | `sparse.load` from a file source | same |

A third CAD mode, `cad.decompose` without the check, shows what an unchecked
retained decomposition costs. Each mode runs in its own process, and the
recorded figure is the incremental peak of the measured work. The ladders run
past the point where the materialized route exceeds the 12 GiB cap, so the
results show both the memory ratio while both routes finish and the size at
which only the streamed route still does. Counts of cells, roots, and terms
must agree between modes.

## Case sources

- [SymbolicData](https://github.com/symbolicdata/data) (`XMLResources/IntPS`):
  cyclic, katsura, eco, noon, and reimer systems.
- [A Repository for CAD Examples](https://researchdata.bath.ac.uk/69/)
  (Wilson, Bradford, Davenport): problems with QEPCAD input files.
- [SMT-LIB](https://smt-lib.org) 2025 non-incremental release, `QF_NRA`.
- [MPSolve](https://github.com/robol/MPSolve) `src/tests/unisolve`: about 180
  univariate test polynomials, including Mandelbrot, Chebyshev, Wilkinson, and
  Mignotte-type families.
- `sympy.polys.specialpolys`: `swinnerton_dyer_poly`, `cyclotomic_poly`,
  `fateman_poly_F_1` … `F_3`, `w_polys`, `f_polys`, and `random_poly`.
- Fateman's and Monagan–Pearce's multiplication problems, as defined in their
  papers; there is no maintained dataset, so the generator writes them.

## Rollout

1. **Pilot (in progress):** the harness, case format, and correctness check
   for Gröbner bases against SymPy, Singular, and msolve, end to end through a
   draft report, plus the streaming study.
2. **First public release:** Gröbner bases, CAD and satisfiability,
   univariate and multivariate factorization, real roots, and arithmetic,
   against SymPy, FLINT, PARI, Singular, msolve, Tarski with QEPCAD B,
   SMT-RAT, Z3, and cvc5.
3. **Second release:** gcds and resultants, extension fields, complex roots,
   and algebraic numbers, adding Macaulay2, Giac, Maxima, NTL, Redlog, Yices 2,
   and MPSolve.
4. **Third release:** series, interpolation, rational functions, enclosure
   evaluation, and certification studies for the other families.
