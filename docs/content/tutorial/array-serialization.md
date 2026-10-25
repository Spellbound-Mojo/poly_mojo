# Save and restore polynomial values

Use `poly.io` to save a polynomial value and restore it with the information
that makes it useful: its coefficient domain, series order, basis nodes,
rational-function numerator and denominator, or batch shape. Exact algebraic
values retain checked root witnesses. Numerical values retain their stored
precision and enclosures.

For a series `s = series.asarray([1, 2], order=6)`, call `io.dumps(s)` to save
it and `io.loads[type_of(s)](saved)` to restore it. The result still represents
$1 + 2x + O(x^6)$.

Mojo requires the result type at compile time. `type_of(s)` is convenient when
you already have a value of that type; `io.loads[series.Array[1]](saved)` works
when you do not. A record for another domain or representation is rejected.
Raw coefficient iterables should first go through `dense.asarray`,
`series.asarray`, or the appropriate constructor, which infers their domain.

## What a value record preserves

| Value | Retained information |
|---|---|
| Dense or sparse polynomial | Exact or numerical coefficients; sparse axis count, including unused axes |
| Formal series | Order of the unknown tail and stored coefficients; numerical precision of implicit zeros |
| Newton basis | Every coefficient, including trailing zeros, and all nodes |
| Chebyshev or Bernstein basis | Basis name and full coefficient extent, including representation degree |
| Rational function | Reduced numerator and monic denominator over QQ, QQi, GF(p), AA, or QQbar |
| Algebraic scalar | Exact defining polynomial and Descartes isolating interval for each real component |
| Batch | Shape and every logical item in row-major order, including nested batches |

Supported standalone scalars are `Int`, `Integer`, `Rational`, `ExactComplex`,
`ModInt`, `algebraic.Real`, `algebraic.Complex`, `Float`, `Complex`, `Ball`,
and `ComplexBall`. A batch can contain any supported value type. Empty batches
retain their item type and shape. Prime-field values retain their modulus,
which the reader validates even when their coefficient arrays are empty.
The record supplies the prime; check the restored modulus if your calculation
requires a particular one.

<!-- example: docs/examples/array_value_serialization.mojo -->

Loading a numerical value performs no rounding and needs no arithmetic
context. The next calculation takes the same explicit `context=` argument
as usual. A saved context is not a default for future operations.

Rational-function records save the normalized fraction. Loading checks that
it is reduced with a monic denominator, rebuilds cancellation and coprimality
evidence for that fraction, and verifies the result. The restored value works
with `rational.check`; its evidence describes the saved normalized inputs.
It does not retain a previous, unreduced numerator and denominator.

Saving an algebraic scalar preserves its value and root witness. To retain the
search or calculation that produced a result, save the complete result object.
Numerical fraction records preserve both coefficient arrays without cancellation
or rounding; they do not supply a default context for future arithmetic.

## Save a checked result

The same `io.dumps` and `io.loads` calls now accept checked exact results,
root results and diagnostics, reusable Sturm plans and interval counts, CAD
results, rational decompositions, and certified
evaluations. The archive includes original operands, options, and proof fields.
Loading reconstructs those fields and runs the independent checker before
returning; it does not recompute the answer with the producing algorithm.

Integer and rational GCD results can retain compact modular coprimality
certificates. Their archive payload uses the `MODULAR-1` variant marker.
Older resultant-based coprimality archives remain readable; package versions
predating this variant reject its marker.

<!-- example: docs/examples/array_checked_serialization.mojo -->

A rejected proof raises `ENCODING`. Work or field limits still raise `LIMIT`
or `CAPACITY`, so an exhausted checker never becomes a successful load.
An incomplete root cover or unsuccessful polishing certificate cannot be saved
as a checked archive. A complete cover can be saved even if a stricter accuracy
or isolation request remains unmet; its retained flags keep that distinction.

The [IO reference](../reference/array-io.md) lists the supported result families.
They use a versioned, typed certificate layout inside `POLYNOMIALS-VALUE 1`.
Keep the package version with long-lived archives. Arithmetic histories on
standalone algebraic scalars remain outside this format, and rational-function
value records still describe the normalized saved inputs. This also applies to
a fraction retained as a decomposition’s source: its saved operand is the
normalized value, without its earlier construction history.

## Stream a complete value

`io.dump(value, sink)` and `io.load[T](source)` use the same
`PolynomialTextSink` and `PolynomialTextSource` interfaces as the coefficient
helpers below. Both string and streaming entry points write
`POLYNOMIALS-VALUE 1` records. One-byte fragments, empty chunks, and fields
split across chunk boundaries are supported.

The writer flushes at field boundaries near 4096 bytes. A single large
coefficient field can exceed that size. The reader holds the current source
chunk, current field, and decoded values; it does not collect the entire text
record. `max_field_bytes=` defaults to 16 MiB and limits each field, including
numerical JSON and algebraic witness fields. It does not bound the source's
own buffering or the memory needed for the restored object.

A broadcast batch is saved as its logical values. Loading produces an
independent contiguous batch, so a large broadcast can take more storage than
the original view. Shared object identity and strides are not part of the
format.

All nested decoding, witness validation, rational-function reconstruction,
and transport share the supplied `Budget` or `max_steps=` allowance. Malformed,
noncanonical, truncated, or mismatched records raise `ENCODING`; resource
limits remain `LIMIT` or `CAPACITY`. Writers can leave partial output on
failure. For file replacement, write to a temporary destination and replace
the old file after the write succeeds.

See the [API reference](../reference/array-io.md) for all four functions.

## Existing coefficient-array records

Use `dense.dumps`/`dense.loads` or `sparse.dumps`/`sparse.loads` to exchange
canonical coefficient data. These formats are separate from the complete-value
format: read each record with the namespace that wrote it. The array helpers
preserve the polynomial's domain and representation. You still construct new
polynomials from coefficient sequences or sparse terms.

<!-- example: docs/examples/array_serialization.mojo -->

Mojo needs the restored coefficient type at compile time. Use `loads[Integer]`,
`loads[Rational]`, `loads[ExactComplex]`, `loads[algebraic.Real]`,
`loads[algebraic.Complex]`, or `loads[ModInt]`; modular records
also require the expected `modulus=`. A mismatched domain or modulus raises
`ENCODING`. Sparse loading takes `ndim=` to retain the power-tuple width,
including unused axes.

### Keep algebraic coefficients exact

Use `loads[algebraic.Real]` for `AA` and `loads[algebraic.Complex]` for
`QQbar`. Each real component retains its defining polynomial, rational
isolating endpoints. Loading checks that the polynomial changes sign across
the interval with Descartes bound 1 before accepting the coefficient. Records
written before Descartes witnesses carried Sturm sequences and fail with
`ENCODING`; recompute those values. Complex
values carry separate real and imaginary witnesses.

<!-- example: docs/examples/array_algebraic_serialization.mojo -->

The saved record preserves the supplied witness, including a valid nonminimal
defining polynomial. Equal values can therefore have different records when
their witnesses differ. Loading rebuilds the private equality cache; it does
not restore the history of arithmetic or evaluation that produced the value.
The restored coefficient still passes `algebraic.check` as an exact value.

Algebraic arrays use their own versioned format, `POLYNOMIALS-ALGEBRAIC 1`.
Existing integer, rational, modular, and numerical records keep their original
formats. No numerical approximation is involved in an algebraic round trip.

### Preserve numerical values

The same `dumps` function accepts numerical arrays. Restore them with
`loads_numeric[Float]`, `[Complex]`, `[Ball]`, or `[ComplexBall]`. Numerical
records preserve stored precision and enclosure data exactly. Loading does
not apply a new arithmetic context or silently round coefficients; pass a
context when you next calculate with the array.

Numerical records use the core library's versioned canonical text format. Malformed,
noncanonical, truncated, and incompatible records are rejected rather than
repaired. Loading consumes a shared `Budget` or `max_steps=` allowance before
input-dependent work and allocation. The records retain coefficient data and, for algebraic coefficients, root
witnesses. They do not retain polynomial-operation certificates, formal-series
order, or basis metadata.

### Stream exact or numerical records

`dense.dump(p, sink)` and `sparse.dump(p, sink)` send bounded chunks to a
`PolynomialTextSink`. `dense.load[T](source)` and
`sparse.load[T, ndim=...](source)` consume a `PolynomialTextSource`, so your
application controls files, network transport, and other storage. The same
functions stream `AA` and `QQbar`, including their coefficient witnesses.
Algebraic writers flush between fields at a target of 4096 bytes; one rational
field can exceed that target. Readers keep the current field, source chunk, and
decoded data rather than collecting the complete text record.

For numerical arrays, use the same `dump` and restore with
`load_numeric[Float]`, `[Complex]`, `[Ball]`, or `[ComplexBall]`. Sparse loading
also takes `ndim=`. `chunk_bytes=` controls the numerical producer's target
chunk size; one header or scalar may exceed it. The consumer accepts even
single-byte fragments and preserves each coefficient's stored precision.

Source chunks may split anywhere in a record. Set `max_field_bytes=` when
loading to bound an individual text field; the default is 16 MiB. All transport
and parsing work uses the same budget. A sink can receive a partial record
before a failure, so applications that need atomic replacement should write
to temporary storage and publish it only after `dump` succeeds.

The [value serialization reference](../reference/array-io.md#polynomialtextsink)
describes the sink and source protocols. The [array API reference](../reference/array-api.md)
links the dense and sparse helper signatures.

Algebraic root covers retain their coefficient-conversion witnesses. `AA`
specializations and specialized-root results retain the original sparse input,
parameter assignments, and coefficient transcripts, including tuple-shaped
powers. Adaptive fraction archives retain the last evaluations and their
accuracy outcome; an unresolved denominator is stored without inventing a
finite quotient.

## Exchange kernel literal bytes

Use `dense.to_kernel_bytes` or `sparse.to_kernel_bytes` when integrating with
a proof kernel's literal byte protocol. These adapters accept integer and rational
coefficients and restore them over `QQ`.

<!-- example: docs/examples/array_surface_kernel.mojo -->

Dense calls take `variable=`; sparse calls take `variables=` and restore with
`from_kernel_bytes[ndim=...]`. Keep this map alongside the payload: it stores
used core IDs, but does not retain unused axes or array shape. Decoding rejects
unmapped variables, malformed fields, noncanonical terms, and trailing bytes.

Zero and one have separate kernel atoms, so the literal codec rejects them
with `ENCODING`. The payload limit is 1 MiB. Both conversion and codec work
consume the same `Budget` or `max_steps=` allowance. Dense decoding also charges
for the full coefficient extent before allocating it; use sparse decoding for
large powers.

For application archives, use `poly.io`. Kernel literals do not carry the
representation metadata, numerical formats, algebraic witnesses, or operation
certificates supported by those archives.
