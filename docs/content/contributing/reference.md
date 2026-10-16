# Source provenance and fixtures

The package is an original Mojo implementation. Some modules follow published
algorithms or permissively licensed implementations closely; this page lists
those sources, maps them to the contract groups, and describes the independent
fixtures that tests compare against.

## Adapted sources

| Source | Version | License | Used for | Notice |
|---|---|---|---|---|
| [SymPy](https://github.com/sympy/sympy/tree/sympy-1.13.3/sympy/polys) `polys` | 1.13.3 | BSD-3-Clause | gcds, subresultants and resultants, squarefree decomposition, finite-field, integer and multivariate (Wang) factorization, Buchberger's algorithm with the Gebauer–Möller criteria | `licenses/SymPy.txt` |
| [Z3](https://github.com/Z3Prover/z3) | `2d08bfc` | MIT | real algebraic number arithmetic; sparse modular gcd and interpolation | `licenses/Z3.txt` |
| [SMT-RAT](https://github.com/ths-rwth/smtrat) | `fc28c1d` | MIT | McCallum and Lazard projection, delineation, sampling, cylindrical coverings | `licenses/SMT-RAT.txt` |
| [CArL](https://github.com/ths-rwth/carl) | `8afa65d` | MIT | Lazard evaluation | `licenses/SMT-RAT.txt` |
| QEPCAD B | `796962b` of Tarski | ISC | the structure of projection and lifting; no code adapted | |
| M. van Hoeij, “Factoring Polynomials and the Knapsack Problem,” *J. Number Theory* **95**(2), 2002, [doi:10.1006/jnth.2001.2763](https://doi.org/10.1006/jnth.2001.2763) | | | trace-knapsack recombination for integer factorization | |

A source file that follows one of these implementations closely keeps the
upstream copyright notice in its header and names the functions it follows.
The package ports only from MIT, BSD, ISC or Apache-2.0 sources, never from
GPL or LGPL code, and links no foreign library (ground rule PG7). The
`licenses/` notices ship with the conda package.

## How to use the references

1. **The design decides.** Algorithms, signatures, normalizations and
   certificates follow the [contracts](../spec/index.md) and the
   [theory](../theory/index.md). Where a reference differs, follow the
   contract; the known differences are listed below.
2. **Port the ideas, then write Mojo.** No reference produces certificates,
   budgets or `PolyError` values, and each has its own representations.
   SymPy stores dense polynomials with the leading coefficient first and
   sparse polynomials as dictionaries; this package stores dense
   coefficients ascending and sparse terms increasing in their order.
3. **Expected values never come from the code under test.** They come from
   theorems, hand computation, the kernel reference vectors, or the corpus.
4. **Recursion.** SymPy recurses over variables in its `dmp_*` functions,
   which PG5 allows, but also over the factor list in `dup_zz_hensel_lift`,
   which G2 forbids: use an explicit stack.

## Map by contract group

Line numbers refer to SymPy 1.13.3's `sympy/polys/`. Contract groups without a
listed source are original to this package.

### P1 Representations and arithmetic

| Item | Reference | Notes |
|---|---|---|
| P1.3 Monomials and orders | | Definition R-2's `LEX`, `GRLEX` and `GREVLEX`, with variable 0 largest; `KERNEL` is the proof kernel's storage order. Corpus: 45 `compare` cases, including Cox, Little and O'Shea's examples |
| P1.5, P1.6 Dense polynomials, evaluation, derivatives | `densearith.py`: `dup_mul` (:735, Karatsuba above a threshold), `dup_sqr` (:835), `dup_pow` (:923) | `dup_mul` is the Karatsuba reference |

### P2 Division, gcd, resultants, rational functions

| Item | Reference | Notes |
|---|---|---|
| P2.1 Division | `densearith.py`: `dup_pdiv`, `dup_prem` (:1000, :1053), `dup_rr_div` (:1308, over a ring), `dup_ff_div` (:1410, over a field), `dmp_pdiv` (:1145) | List division moves an indivisible leading term to the remainder (Theorem V-4). Corpus: `divmod`, `pseudo_divmod` |
| P2.2 Content, primitive part, gcd | `euclidtools.py`: `dmp_content`, `dmp_primitive` (:1792, :1823), `dup_gcdex` (:102), `dup_rr_prs_gcd` (:966), `dup_zz_heu_gcd` (:1147); `modulargcd.py`: `modgcd_univariate` (:156, Algorithm G-5), `modgcd_multivariate` (:1062), `_degree_bound_univariate` (:58), `_chinese_remainder_reconstruction_univariate` (:91) | Differs: primes come from this package's fixed sequence. Corpus: 21 `gcd` cases, with cofactors |
| P2.3 Primes, CRT | `galoistools.py`: `gf_crt` (:12), `gf_crt1`, `gf_crt2` | Corpus: `primes.first_100`, each proved prime and the gaps proved prime-free by the checker |
| P2.4 Unlucky primes | `modulargcd.py`, `modgcd_univariate` (:156): the degree comparison that discards an unlucky prime | Corpus: `gcd.uni.unlucky_first_prime` |
| P2.5 Resultants, subresultants | `euclidtools.py`: `dup_inner_subresultants` (:308), `dup_prs_resultant` (:405), `dmp_inner_subresultants` (:449), `dmp_prs_resultant` (:552), `dmp_zz_modular_resultant` (:592), `dmp_zz_collins_resultant` (:670) | Corpus: 12 `resultant` cases, with the principal subresultant coefficients of the univariate ones |
| P2.6 Rational functions | `euclidtools.py`: `dup_cancel`, `dmp_cancel` (:1845, :1862) | Differs: SymPy clears denominators and returns the constants separately; Definition F-1 makes the denominator monic in the order. Corpus: 7 `normalize_fraction` cases |

### P3 Factorization

| Item | Reference | Notes |
|---|---|---|
| P3.1 Squarefree decomposition | `sqfreetools.py`: `dup_sqf_list` (:500), `dup_sqf_part` (:406) | Yun's algorithm (Theorem Z-2). Corpus: 9 `squarefree` cases |
| P3.2 Factorization over $\mathbb F_p$ | `galoistools.py`: `gf_ddf_zassenhaus` (:1833), `gf_edf_zassenhaus` (:1890), `gf_berlekamp` (:1789), `gf_factor_sqf` (:2143), `gf_pow_mod` (:992), `gf_frobenius_monomial_base` (:906) | Differs: splitting polynomials come from SplitMix64 with the caller's seed (PG4), not Python's global `random`. Corpus: 11 `factor_mod_p` cases, up to $p \approx 2^{62}$ |
| P3.3 Factorization over $\mathbb Z$, $\mathbb Q$ | `factortools.py`: `dup_zz_mignotte_bound` (:144), `dup_zz_hensel_step` (:213), `dup_zz_hensel_lift` (:270), `dup_zz_zassenhaus` (:334), `dup_zz_factor_sqf` (:610), `dup_zz_factor` (:639), `dup_trial_division` (:88) | Differs: Algorithm Z-6 takes the first suitable prime of the fixed sequence (about $2^{62}$, so few lifting steps) and Theorem Z-5's bound; Hensel lifting uses an explicit stack. Corpus: 21 cases, among them $x^4 + 1$, $x^{105} - 1$, and Swinnerton-Dyer polynomials up to degree 16 |
| Multivariate factorization | `factortools.py`: `dmp_zz_wang` and its lifting helpers | `src/polynomials/_multivariate_factor.mojo` keeps SymPy's notice |

### P4 Gröbner bases

| Item | Reference | Notes |
|---|---|---|
| P4.1 Bases and reduction | `groebnertools.py`: `_buchberger` (:50) with normal selection and the Gebauer–Möller criteria (`update`, :117), `spoly` (:262), `red_groebner` (:699), `is_groebner` (:731), `is_reduced` (:765) | Differs: ties in pair selection break by the pair's indices (G1), cofactors are tracked (Proposition B-6), and untracked bases over primes below $2^{31}$ under GRLEX and GREVLEX use F4 [Faugère 1999]. Corpus: 24 `groebner` cases (Katsura-2 to 4, cyclic-4 and 5, over $\mathbb Q$ and $\mathbb F_p$) |
| P4.2 Membership | the remainder on division by a basis | Corpus: 6 `membership` cases, including $1 \in I$ |

### P5 Real roots

| Item | Reference | Notes |
|---|---|---|
| P5.1 Sturm sequences, counts | `rootisolation.py`: `dup_sturm` (:32), `dup_count_real_roots` (:778) | Differs: `dup_sturm` takes the squarefree part first; Definition T-1 does not. Corpus: 4 `sturm` cases, 6 `count_roots` cases |
| P5.2 Isolation | `rootisolation.py`: `dup_isolate_real_roots` (:592), `dup_inner_isolate_real_roots` (:358), `dup_refine_real_root` (:323) | Algorithm T-4 bisects with Sturm counts, so every interval carries a checkable count. Corpus: 14 `isolate` cases (Wilkinson's polynomials, Chebyshev, a Mignotte polynomial with a close pair, repeated roots) |

The algebraic-number and CAD layers follow the Z3, SMT-RAT and CArL sources
above; their certificate obligations are stated in
[algebraic and CAD extensions](../theory/extensions.md).

## Kernel vectors

`tests/reference/kernel/` holds `poly_reference.py` and `literal_reference.py`,
copies of the proof kernel's reference scripts, their table `poly_vectors.txt`,
and `poly_ops.txt`: 378 vectors of the kernel's polynomial operations and byte
encodings, generated by `gen_poly_ops.py` (the format is in its docstring).
`pixi run kernel-vectors-check` confirms that the vectors match their
generator. They are the expected values for P1.4 and P1.7.

## The reference corpus

### Where the values come from

`tests/reference/gen_corpus.py` computes each case with SymPy 1.14.0 and
normalizes it to this package's conventions. It reads only the fixed cases
in `corpus_inputs.txt`, never the expected output file or the Mojo package.
`tests/reference/check_corpus.py` re-checks every case with plain Python
fractions, independently of the generator and the package. Neither script
imports the other. SymPy is needed only for regeneration; normal builds and
tests use the committed corpus and need no additional dependency.

The inputs preserve every original case, including the random samples.
Nonunique root intervals are generated using exact rational endpoints with
width below $2^{-40}$, while rational roots are reported exactly. The checker
proves:

| op | checked independently |
|---|---|
| `compare` | the orders of Definition R-2 |
| `divmod`, `pseudo_divmod` | Theorems V-1 and V-2: the identity and the degree bound |
| `gcd` | Definition G-1's normalization, both cofactor identities, coprime cofactors (so the gcd is maximal; by Euclid on specializations for several variables), the content over $\mathbb Z$ |
| `primes` | primality (deterministic Miller–Rabin), order, and that no prime is skipped |
| `resultant` | the Sylvester determinant and each principal subresultant coefficient as a minor; multivariate cases at specializations |
| `normalize_fraction` | equality, the monic denominator, coprimality (Definition F-1) |
| `squarefree` | Definition Z-1 |
| `factor_mod_p` | the product, monic factors, irreducibility by distinct-degree factorization, the sort order |
| `factor`, `factor_integer` | the product, normalization, distinct squarefree pairwise coprime factors, the sort order; irreducibility only where degree patterns modulo small primes prove it (61 of 76 factors; the others, such as Swinnerton-Dyer polynomials, rely on the SymPy generator) |
| `groebner`, `membership` | monic, reduced, sorted bases; every generator reduces to $0$; Buchberger's criterion on every pair (Theorem B-2); the remainder. Not checked: that the basis lies in the generators' ideal |
| `sturm`, `count_roots`, `isolate` | Definition T-1 recomputed; Sturm counts for the counts, each interval, and all real roots within Cauchy's bound |

The checker also rejects corrupted values: of 400 random single-digit
corruptions of output lines, it caught all but 5, and those 5 left valid
isolating intervals, which are not unique.

```text
python3 tests/reference/check_corpus.py        # or: pixi run corpus-check

# Optional regeneration environment; no changes to the package's dependencies.
python3 -m venv .cache/corpus-env
.cache/corpus-env/bin/python -m pip install sympy==1.14.0 mpmath==1.3.0
.cache/corpus-env/bin/python tests/reference/gen_corpus.py --check
.cache/corpus-env/bin/python tests/reference/test_gen_corpus.py

# Regenerate only deliberately, then run the independent checker and phase tests.
.cache/corpus-env/bin/python tests/reference/gen_corpus.py --output tests/reference/corpus.txt
pixi run corpus-check
pixi run test-library
```

The generator enforces the SymPy version and compares every byte in `--check`
mode. Fixed input data contains no `out` records; the parser rejects them.
All cases are computed before an output file is written. The generator tests
cover normalization, ordering, repeated roots and invalid input records.
Review any regenerated differences and run the checker after every regeneration.

### Format

A line-oriented text file. Lines starting with `#` are comments. Each case
is a block:

```text
case <name>
op <operation>
ring QQ | ZZ | GF <p>
var <i>                       (univariate operations)
order <lex|grlex|grevlex> <i1> <i2> ...   (multivariate operations; x_i1 > x_i2 > ...)
in <key> <value>              (repeated keys form a list, in order)
out <key> <value>
end
```

A **polynomial** is `0`, or terms joined by ` + ` or ` - ` (single
spaces), the first optionally preceded by `-`. A term is a coefficient
(`7`, `3/4`), a monomial (`x0^2*x3`), or both (`3/4*x0^2*x3`); a
coefficient $1$ is never written before a monomial, an exponent $1$ is
never written, and the variables of a monomial are in increasing index.
Coefficients are integers over `ZZ`, in $[1, p)$ over `GF p`, and reduced
fractions over `QQ`. Terms appear in **decreasing** order under the
case's order (univariate: decreasing degree), so the first term is the
leading one. Variable `x<i>` is the package's variable with index `i`.

| op | ring | in | out |
|---|---|---|---|
| `compare` | | `a`, `b` (monomials) | `compare` $\in \{-1, 0, 1\}$: the order's comparison of `a` with `b` |
| `divmod` | QQ | `f`, `g` | `quotient`, `remainder` |
| `pseudo_divmod` | ZZ | `f`, `g` | `delta` ($\max(\deg f - \deg g + 1, 0)$), `quotient`, `remainder` |
| `gcd` | QQ, ZZ | `f`, `h` | `gcd` (Definition G-1, leading coefficient in the case's order), then `cofactor_f`, `cofactor_h` unless the gcd is $0$ |
| `primes` | | | `prime` (repeated): the package's fixed sequence, from the largest prime below $2^{62}$ |
| `resultant` | QQ, ZZ | `variable`, `f`, `g` | `resultant` (Definition E-1); univariate cases also `psc <j> <value>` for $0 \le j < \min(m, n)$: the principal subresultant coefficient, the determinant of the rows $x^{n-j-1} f, \dots, f, x^{m-j-1} g, \dots, g$ on the columns $x^{m+n-j-1}, \dots, x^j$ (the coefficient of $x^j$ in $S_j$ of Theorem E-4; $j = 0$ gives the resultant) |
| `normalize_fraction` | QQ | `p`, `q` | `numerator`, `denominator` (Definition F-1) |
| `squarefree` | QQ | `f` | `unit` (the leading coefficient), `factor <i> <a_i>` for each $a_i \ne 1$, by increasing $i$ |
| `factor_mod_p` | GF p | `f` (monic, squarefree) | `factor` (repeated): the monic irreducible factors |
| `factor` | QQ | `f` | `unit`, `factor <e> <f_i>` with $f_i$ monic |
| `factor_integer` | ZZ | `f` | `unit` (the content with its sign), `factor <e> <f_i>` with $f_i$ primitive, positive leading coefficient |
| `groebner` | QQ, GF p | `generator` (repeated) | `basis` (repeated): the reduced basis, monic, by decreasing leading monomial; none for the zero ideal |
| `membership` | QQ | `generator` (repeated), `f` | `basis` (repeated), `remainder`, `member` (`true` or `false`) |
| `sturm` | QQ | `f` | `sturm` (repeated): $f_0, f_1, \dots, f_\ell$ of Definition T-1, not normalized |
| `count_roots` | QQ | `f`, `a`, `b` | `count`: distinct real roots in $(a, b)$; $f(a) f(b) \ne 0$ |
| `isolate` | QQ | `f` | `count` (distinct real roots), then per root in increasing order `root exact <r>` or `root interval <lo> <hi>` (width at most $2^{-40}$) |

Factors (`factor_mod_p`, `factor`, `factor_integer`) are sorted by degree,
then by their coefficients from the leading one down (as integers in
$[0, p)$ over $\mathbb F_p$, as rationals over $\mathbb Q$, as integers
over $\mathbb Z$): the order P3.2 and P3.3 require, so
compare factor lists exactly.

### Using it in tests

Parse the file in test support code (`tests/support/`, test-only), and for
each case of the operation under test:

- compare canonical polynomials, not strings (our `SparsePoly` keeps its
  terms in increasing order; the file lists them decreasing);
- compare results that the design makes unique exactly: gcds, cofactors,
  quotients and remainders, resultants, normalized fractions, squarefree
  decompositions, factorizations, reduced bases, Sturm sequences, counts,
  and exact rational roots;
- for `isolate`, require the same number of roots and the same exact
  roots, and that the $k$-th isolating interval of ours meets the $k$-th of
  the corpus (intervals are not unique);
- for `membership`, a `true` case must yield a certificate that
  `check_membership` accepts, a `false` case none;
- run every certificate through its `check_*` function as well.

## SymPy notice

The subresultant recurrence in `src/polynomials/_prs.mojo` follows the BSD
SymPy reference and retains this notice in both source and documentation.
The complete upstream notice is also retained in `licenses/SymPy.txt`.

```text
Copyright (c) 2006-2023 SymPy Development Team

All rights reserved.

Redistribution and use in source and binary forms, with or without
modification, are permitted provided that the following conditions are met:

  a. Redistributions of source code must retain the above copyright notice,
     this list of conditions and the following disclaimer.
  b. Redistributions in binary form must reproduce the above copyright
     notice, this list of conditions and the following disclaimer in the
     documentation and/or other materials provided with the distribution.
  c. Neither the name of SymPy nor the names of its contributors
     may be used to endorse or promote products derived from this software
     without specific prior written permission.


THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
ARE DISCLAIMED. IN NO EVENT SHALL THE REGENTS OR CONTRIBUTORS BE LIABLE FOR
ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY
OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH
DAMAGE.
```
