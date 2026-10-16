# Contracts and rules

This page states the requirements a change must preserve: engineering rules,
the exact-core contracts, and the checks that validate them. Signatures live
in the [core API reference](../reference/core-api.md); definitions and proofs
live in the [theory](../theory/index.md). Public changes must also preserve
[Contract P](../reference/contract-p.md) and the separate numerical snapshot,
or include an agreed migration.

**MUST**, **MUST NOT**, **SHOULD**, and **MAY** have their RFC 2119 meanings.
Identifiers are stable, so source comments and test names can cite a precise
requirement. Source provenance and regression cases for each contract group
are in [source provenance and fixtures](../contributing/reference.md).

## Ground rules

| Rule | Requirement |
|---|---|
| G1 | Deterministic results and certificates |
| G2 | Explicit worklists instead of recursion over input-sized structures |
| G3–G4 | Work budgets and checked capacities |
| G5 | No views retained across growth of their backing storage |
| G9 | Typed errors and unchanged borrowed inputs on failure |
| G11–G12 | Positive and negative tests with independently derived expectations |
| G13–G14 | Public docstrings and documentation updated with behavior |
| G16 | Unresolved computations cannot be reported as proved answers |
| PG1 | Every `SparsePoly` and `DensePoly` satisfies Requirement R-R1 at every public boundary; tests run `check_invariants` after every operation |
| PG2 | A certificate holds everything its `check_*` function needs; checking never calls the producing algorithm |
| PG3 | Exact algorithms use exact coefficients only; apn_mojo numerical types appear only in numerical modules, with explicit contexts and exact rational checkers |
| PG4 | Modular algorithms take primes from the fixed sequence in `primes.mojo`; randomized steps use SplitMix64 seeded by the call |
| PG5 | Recursion over variables happens at most once per variable; recursion over terms or degrees is iterative |
| PG6 | `to_kernel_bytes` and `from_kernel_bytes` follow the kernel's byte format exactly, tested against the vectors in `tests/reference/kernel/` |
| PG7 | Pure Mojo over `std` and apn_mojo: no `external_call`, dynamic loading, or C/C++ library; ported code only from MIT, BSD, ISC, or Apache-2.0 sources, with their notices (`pixi run layering` checks imports) |

Every certified result is a struct holding the result and its certificate,
with a matching `check_*` function. Every public function whose work depends
on its input takes `mut budget: Budget` and charges it before that work;
constant-time accessors and fixed-signature language protocols are the only
exceptions. Public functions raise `PolyError`, converting apn_mojo errors at
the call site. A polynomial carries its coefficient context next to its
monomial order, and results inherit both from their inputs.

## Exact-core contracts

Each `check_*` function recomputes only the relation its certificate states
and has a negative test with a corrupted certificate.

### P1 Representations and arithmetic

| ID | Contract | Required checks |
|---|---|---|
| P1.1 | Budget exhaustion raises `LIMIT` and leaves inputs unchanged | A compile-fail test shows a `raises PolyError` function cannot call apn_mojo unconverted |
| P1.2 | `ZZ`, `QQ`, `QQi`, and `ModInt` implement the ring traits; constants come from the ring context, never global state; mixing moduli raises `DOMAIN`; moduli are primes below $2^{62}$ | Ring axioms on generated values; `ModInt` against reduced `Integer` arithmetic; inverses; interleaved moduli |
| P1.3 | `LEX`, `GRLEX`, and `GREVLEX` satisfy Definition R-2; `KERNEL` is the storage order of Definition R-3 | `KERNEL` on the kernel vectors; order properties on generated monomials; Proposition R-1's counterexamples |
| P1.4 | Sparse operands share order and ring (`DOMAIN` otherwise); results satisfy R-R1; `pow(0)` is one | Ring axioms; `pow` against repeated `mul`; the `add`, `mul`, `neg`, and `pow` kernel vectors |
| P1.5 | Dense coefficients ascend with a nonzero leading entry; multiplication uses Karatsuba above 32 coefficients for `ZZ` and `QQ`, 64 for `ModInt` | Karatsuba against schoolbook up to twice the threshold; conversions round-trip |
| P1.6 | Evaluation raises `DOMAIN` for an unassigned variable | Evaluation is a ring homomorphism (Proposition R-5); the product rule |
| P1.7 | The kernel codec rejects 0 and 1 with `ENCODING` and payloads above 1 MiB with `CAPACITY`, before input-sized allocation | Kernel vectors byte for byte (Theorem R-6); every `bad` vector rejected; round trips |

### P2 Division, gcds, resultants, rational functions

| ID | Contract | Required checks |
|---|---|---|
| P2.1 | Division follows Theorems V-1, V-2, and V-4; `divide_exact` returns a quotient exactly when one exists | Division identities with their degree bounds; generated products and non-multiples; Certificate V-C2 |
| P2.2 | Gcds are normalized (Definition G-1) with G-C1 cofactors; univariate gcds over `ZZ` and `QQ` switch from subresultants to the modular algorithm above degree 8 | Planted common factors recovered; G-C1 and G-C2 hold; both algorithms agree |
| P2.3 | Primes descend below $2^{62}$ from a deterministic Miller–Rabin test; CRT returns symmetric representatives | The first primes against an independent list; CRT on generated integers |
| P2.4 | Algorithm G-5 handles unlucky primes as specified | A forced unlucky prime still gives the correct gcd |
| P2.5 | Resultants carry E-C1 cofactors; coprimality certificates reference only earlier nodes, with explicit content witnesses | Vanishing on common factors (Theorem E-2); agreement with the Sylvester determinant; coprimality accepted and refused (Theorem G-8) |
| P2.6 | Rational functions are normalized (Definition F-1) with a cancellation certificate | Unique normal forms (Proposition F-1); certificates check; field axioms |

### P3 Factorization

| ID | Contract | Required checks |
|---|---|---|
| P3.1 | Squarefree blocks by Yun's algorithm; over prime fields, inverse Frobenius roots recover multiplicities divisible by $p$ | Product identity; blocks coprime to their derivatives and each other; planted multiplicities |
| P3.2 | Distinct-degree and Cantor–Zassenhaus splitting; sorted output independent of the seed | Products of irreducibles factored back; equal output for several seeds |
| P3.3 | Algorithm Z-6 with Hensel lifting and recombination; rational factors monic, integer factors primitive with positive leading coefficient, in a fixed order | $x^4+1$, $x^{12}-1$, small Swinnerton-Dyer polynomials; planted factors; `check_factorization` on every result |

Finite-field, Gaussian, and sparse multivariate producers follow the same
result conventions. Their product checkers prove reconstruction, not
irreducibility or squarefreeness.

### P4 Gröbner bases

| ID | Contract | Required checks |
|---|---|---|
| P4.1 | Buchberger's algorithm with Gebauer–Möller criteria and least-LCM pair selection, or F4 over primes below $2^{31}$ under degree orders, returns reduced bases over `QQ`, `QQi`, and prime `ModInt`, with no approximate zero test | Buchberger's criterion recomputed for every basis; independence of generator order; cofactor identities |
| P4.2 | Membership returns the cofactors of Proposition B-6 when the remainder is zero; the checker verifies only the identity | Members found, nonmembers refused; the case $1 \in I$ |

### P5 Exact real roots

| ID | Contract | Required checks |
|---|---|---|
| P5.1 | Sturm sequences (Definition T-1) keep quotient witnesses; `count_roots` requires increasing nonroot endpoints | Planted roots, repeated roots included; corrupted relations and counts rejected |
| P5.2 | Isolation (Algorithm T-4) returns exact rational roots and sorted, disjoint dyadic intervals; `sign_on_interval` follows Theorem T-6 | One root per interval; exact rational roots; counts equal distinct real roots |

[Numerical polynomials](numerical.md), [real algebraic numbers](../reference/algebraic.md),
[multivariate factorization](../reference/advanced-factorization.md),
[CAD](../reference/cad.md), and the [toolkit](../reference/toolkit.md) state
their contracts on their reference pages.

## Validation

Validation combines algorithm tests, independent expected values, corrupted
certificates, reproducibility, compiled consumers, and compatibility snapshots.
The [maintainer guide](../contributing/handoff.md) gives current commands.

| Check | How |
|---|---|
| Independent arithmetic | P1's sums, products, negations, and powers agree with the kernel's `poly_reference.py` on `tests/reference/kernel/poly_ops.txt` |
| Determinism | Every algorithm, run twice and with input terms in different orders, gives identical results and certificates |
| Reference corpus | Every case of `tests/reference/corpus.txt` passes in its group's tests; `pixi run corpus-check` keeps the corpus consistent |
