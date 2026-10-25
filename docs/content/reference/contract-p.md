# Source compatibility and certificates

Poly Mojo targets Mojo 1.2.0. Its compatibility contract covers public source
declarations and the mathematical meaning of their results. It does not promise
a stable native ABI or a universal certificate wire format.

Use `poly` for coefficient arrays and `polynomials` for core values and
algorithms. Private helpers are outside the supported interface. The
[core API](core-api.md) documents the exact surface, also called Contract P;
[numerical polynomials](../spec/numerical.md) have separate precision and
certificate requirements.

Standard Mojo protocols with fixed signatures, such as copying, equality,
hashing, writing, and destruction, cannot take a budget. Human-readable
`Writable` output is diagnostic; use the documented
[interchange formats](../guides/interchange.md) to persist values.

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
- Checkers verify precisely the relations in the references: product checks
  alone do not prove
  irreducibility; a resultant identity does not establish its determinant;
  common-divisor and cancellation identities do not alone prove maximality.
  The coprimality arena uses backward references and explicit
  coefficient-content folds. Checkers do not rerun their producers.
- The codec uses the kernel's canonical format: little-endian term/pair counts,
  signed 64-bit variable indices, unsigned 32-bit exponents, and length-prefixed canonical
  rational coefficients. It enforces `MAX_KERNEL_BYTES`, rejects malformed
  encodings, and rejects 0/1 because the kernel has dedicated constructors.
  The independent kernel vectors pin the bytes.

## CAD evidence and archive compatibility

`cad.decompose(...).evidence()` and `cad.cover(...).evidence()` return
`CADFinalCertificate`, with immutable shared storage. Call
`variables(budget)`, `factor_counts(budget)`, `cell_count(budget)` and
`stack_count()` for metadata. Call `cad.cells(result, budget)` for absolute
cell descriptions; `cad.sample` materializes only a satisfying path. These
conversions charge the caller's budget.

Code that inspected intermediate `.projection`, `.cells` or `.stacks` fields
must use these accessors. Compact evidence retains final factors, fields,
relative roots, maps and signs; its independent checker binds the original
inputs, variable order, fixed coordinates and query. Decomposition and full
covering verify their complete geometric claim before returning. See
[CAD](cad.md) for projection choices and restricted-coordinate behavior.

Decomposition and full-covering archives write `CHECKED-3`. The reader also
accepts `CHECKED-1` archives and checks their legacy evidence without
reconstructing the CAD. Older readers reject the new format. Compact `QCF1`
payloads undergo bounded decoding and complete verification before acceptance.
Selective `cad.solve` uses its own `Solution` evidence and `CHECKED-2` archives;
the incremental producer/checker protocol has a separate evidence layout.

Archive tags identify formats, not interchangeable proof claims. Use the
matching loader and checker described in [value serialization](array-io.md),
and handle `ENCODING` for unsupported or malformed data.
