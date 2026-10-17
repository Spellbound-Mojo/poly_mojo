# Formal series arrays

Construct formal series with a retained unknown-tail order. Exact integer
coefficients promote to QQ; an explicit `context=` selects numerical arithmetic.
All operations return new values.

Every computational call accepts a shared `Budget` or `max_steps=`. See the
[tutorial](../tutorial/array-series.md) for examples, domain restrictions,
and the meaning of retained metadata.

Save and restore these values with [poly.io](array-io.md).

<!-- api: src/poly/series.mojo Array -->

<!-- api: src/poly/series.mojo asarray -->

<!-- api: src/poly/series.mojo add -->

<!-- api: src/poly/series.mojo subtract -->

<!-- api: src/poly/series.mojo multiply -->

<!-- api: src/poly/series.mojo divide -->

<!-- api: src/poly/series.mojo negative -->

<!-- api: src/poly/series.mojo reciprocal -->

<!-- api: src/poly/series.mojo compose -->

<!-- api: src/poly/series.mojo derivative -->

<!-- api: src/poly/series.mojo integral -->

<!-- api: src/poly/series.mojo log -->

<!-- api: src/poly/series.mojo exp -->

<!-- api: src/poly/series.mojo revert -->

<!-- api: src/poly/series.mojo sqrt -->

<!-- api: src/poly/series.mojo power -->

<!-- api: src/poly/series.mojo truncate -->

<!-- api: src/poly/series.mojo coefficients -->

<!-- api: src/poly/series.mojo to_polynomial -->

<!-- api: src/poly/series.mojo to_core -->

<!-- api: src/poly/series.mojo from_core -->

Numerical construction uses `context=`; arithmetic keeps precision explicit on every call.
See the [numerical tutorial](../tutorial/array-numeric.md#numerical-series-and-alternative-bases).

<!-- api: src/poly/series.mojo NumericArray -->
