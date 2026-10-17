# Contract P

Contract P records the supported exact source interface: exported declarations,
certificate fields, and kernel codec semantics. Revision 3 stores dense
coefficients in a `CoefficientBuffer`, so one-pass construction can retain
chunks without copying them into a contiguous list. Revision 4 adds the
value-only `gcd_value` and `resultant_value` and the `certify` option of
`groebner`. The numerical surface has its own snapshot.

The contract targets Mojo 1.1.0. It does not promise a stable native ABI or a
universal certificate wire format.

## Frozen surface

[The declaration snapshot](contract-p.json) records the 201 exact root exports,
their declaring modules, generic bounds, defaults, typed errors, public
fields, constructors, and named methods. The rendered references explain
their semantics:

| Surface | Normative reference |
|---|---|
| Coefficients, contexts, orders, sparse/dense values, arithmetic, budgets, errors, codec | [Representations](p1.md) |
| Division, gcd, elimination, fractions, coprimality proof arenas and independent checkers | [Division and elimination](p2.md) |
| Squarefree, finite-field and integer/rational/Gaussian factorization | [Factorization](p3.md) |
| Gröbner bases, reduction, tracked cofactors and ideal membership | [Gröbner bases](p4.md) |
| Sturm sequences, counts, isolation, refinement and interval signs | [Real roots](p5.md) |
| Exact algebraic values, arithmetic, evaluation and complete specialized roots | [Algebraic numbers](algebraic.md) |
| Sparse multivariate factors and modular gcds | [Further factorization](advanced-factorization.md) |
| Determinants, McCallum/Lazard projection, cells and coverings | [CAD](cad.md) |
| Calculus, interpolation, bases, series, rational utilities, text transport and incremental CAD | [Toolkit](toolkit.md) |

Import consumer code from `polynomials`. Private helpers are not part of
Contract P. Standard Mojo protocol signatures are supplied by the declared
traits; protocols with fixed signatures (`copy`, equality, hashing, `write_to`
and destruction) cannot take a budget and are exempt from charging.
Human-readable `Writable` output is diagnostic, not a serialization format.

The numerical surface contains 97 exports. Its
[declaration snapshot](contract-numeric.json) and [semantics](../spec/numerical.md)
are separate from Contract P revision 4 and do not imply kernel acceptance.
`CADFiber` provides explicitly restricted CAD coverage, reusing the existing
certificate field layouts. Its certificates require verification with the same
fixed prefix. The contract tests freeze both surfaces and reject unreviewed root exports.

## Dense coefficient storage

`DensePoly.coefficients` is a `CoefficientBuffer[C]`. Indexing, mutation,
iteration, `len`, `capacity`, `append`, `pop`, and `clear` remain available.
Iteration yields owned values; use indexing to borrow or mutate an entry. Copies
own independent storage; the `poly.dense.Array` facade still shares immutable
polynomials. `DensePoly.from_coefficients` continues to accept an owned
`List[C]`, and also accepts an owned buffer.

Code that requires a `List[C]` specifically should call
`p.coefficients.to_list(budget)`. This explicit conversion allocates and copies
coefficient handles, charging the supplied budget. To replace coefficients,
build a list and transfer it into the field; use `from_coefficients` when the
new values need validation and canonical trimming. Pointer access, `Span(list)`,
and other contiguous-list operations require that explicit list conversion.
Use `is_contiguous()` to inspect storage without changing it.

## Revision 4 additions

Revision 4 is source compatible with revision 3; no consumer code needs to
change.

- `gcd_value(f, h, budget)` returns the same polynomial as `gcd(f, h, budget).gcd`
  without computing cofactors or evidence.
- `resultant_value(f, g, variable, budget)` returns the same polynomial as
  `resultant(f, g, variable, budget).resultant` without the multipliers of its
  identity.
- `groebner` takes `certify: Bool = True` after `track_cofactors`. The default
  keeps the certified result. `certify=False` applies only to bases over
  $\mathbb Q$ computed from modular images: the result is then the reduced basis
  with high probability and is not proved. Calls that pass arguments by
  position are unaffected.


## Semantic guarantees

- Polynomials are canonical at public boundaries. Sparse terms increase in
  their stored order; zero has no terms/coefficients. Modular values carry
  their validated prime context. KERNEL is a storage order; Gröbner and
  ordered list division require an admissible order.
- Computations use exact coefficients, fixed prime sequences, and explicit
  seeds. Results and certificates are deterministic for the same ordered
  inputs and independent of the order in which input terms were supplied.
  Generator/divisor list order remains meaningful for certificate columns
  and division choices. Factor lists are sorted by degree, then by
  coefficients from the leading one down.
- Computational calls share the caller's `Budget` and raise `PolyError`.
  Work is charged before it is done; a failed charge raises `LIMIT` and leaves
  borrowed inputs unchanged.
  Charges are implementation work estimates, not a frozen cost schedule;
  prime-cache state can change work consumption without changing values.
- Certificate fields and their interpretations are frozen. Checkers verify
  precisely the relations in the references: product checkers do not prove
  irreducibility; a resultant identity does not establish its determinant;
  common-divisor and cancellation identities do not alone prove maximality.
  The coprimality arena uses backward references and explicit
  coefficient-content folds. Checkers do not rerun their producers.
- The codec uses the kernel's canonical format: little-endian term/pair counts, signed 64-bit
  variable indices, unsigned 32-bit exponents, and length-prefixed canonical
  rational coefficients. It enforces `MAX_KERNEL_BYTES`, rejects malformed
  encodings, and rejects 0/1 because the kernel has dedicated constructors.
  The independent kernel vectors pin the bytes.

## Release and change control

Run the declaration check in addition to the standard release checks:

```sh
pixi run --locked build
pixi run --locked python tests/test_contract_p.py
pixi run --locked test-library --jobs 2
pixi run --locked test-rejections --jobs 2
pixi run --locked -e docs docs-check
pixi run --locked docs-test --output .cache/release-doc-examples --jobs 2
```

The [revision-1 baseline](contract-p-v1.json) retains all 77 original exports.
The [initial revision-2 baseline](contract-p-v2-initial.json) preserves 135
exports, the [final revision-2 baseline](contract-p-v2.json) preserves 198, and
the [revision-3 baseline](contract-p-v3.json) preserves 199.
The tests compare all four against the current surface, allowing only the
reviewed coefficient-field change, the new buffer constructor overload, and
the `certify` option of `groebner`. The
check reuses the documentation declaration reader and fails on export,
signature, public-member or certificate-field drift. It has no
snapshot-update mode. The Mojo phase tests, replay test and executable
examples cover behavior and compiled consumer use; a declaration snapshot
alone cannot establish semantic compatibility.

A breaking change must be agreed with downstream users first and recorded
here with a migration note. Update the snapshot only as part of that reviewed
change.
