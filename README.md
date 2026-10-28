# Poly Mojo

Poly Mojo is a pure Mojo library for exact and arbitrary-precision polynomial
computation. It combines dense and sparse arithmetic, factorization, Gröbner
bases, exact real and complex algebraic roots, validated numerical root finding,
and cylindrical algebraic decomposition (CAD), alongside calculus,
interpolation, and formal series. Solve polynomial equations and inequalities,
keep algebraic values exact, and check numerical answers with rigorous bounds.
Streaming interfaces help keep RAM use down by processing text and certificate
data incrementally.

Built on [apn_mojo](https://github.com/Spellbound-Mojo/apn_mojo), the library
supports integer, rational, finite-field, and Gaussian rational coefficients,
alongside arbitrary-precision real, complex, and interval coefficients.
Use `poly.dense` and `poly.sparse` with coefficient arrays and inferred exact
domains. Numerical algorithms let you choose precision explicitly, and `astype`
converts coefficients to a chosen floating-point or ball type. Optional work
limits bound calculations.

![Mojo 1.2](https://img.shields.io/badge/Mojo-1.2-orange)
![License](https://img.shields.io/badge/license-Apache%202.0-green)

**Documentation:** https://spellbound-mojo.github.io/poly_mojo/

## What you can do

- **Start with coefficients.** Add, multiply, divide, integrate, and evaluate
  dense or sparse polynomials through `poly`. Compute GCDs and factors over integers,
  rationals, Gaussian rationals or prime fields, and factor dense or multivariate
  sparse polynomials over real or complex algebraic numbers. Interpolate exact samples, find roots,
  and solve polynomial systems. Domains
  are inferred from your coefficients. See [polynomial arrays](docs/content/tutorial/arrays.md)
  and [exact array algebra](docs/content/tutorial/array-exact.md).

- **Reduce memory use with streaming.** Read and write polynomial text in chunks,
  and check evaluation, root, and CAD evidence as it arrives. Consumers can
  release completed proof data instead of retaining the entire history;
  inputs, active computation, and requested outputs still determine memory use.
  See [streaming](docs/content/guides/interchange.md).
- **Solve polynomial inequalities with CAD.** Decompose real space into cells
  with constant polynomial signs, locate a point's cell, or use selective
  coverings to find a satisfying assignment or prove a conjunction impossible.
  Fix selected coordinates with `fixed=[(axis, value), ...]` to solve a slice,
  with the same streaming and checking workflows. With real algebraic
  coefficients, lifting follows only the values you supplied.
  Use `cad.project`, `cad.cell_at`, and `cad.lazard_evaluate` for targeted work.
  See [CAD workflows](docs/content/tutorial/array-cad-workflows.md).
- **Reduce polynomial systems with Gröbner bases.** Compute reduced bases over
  rationals, finite fields, or exact Gaussian rationals. Ideal membership
  returns an identity you can check independently of the basis computation.
  See [Gröbner bases and membership](docs/content/tutorial/array-systems.md).
- **Calculate with exact algebraic coefficients.** Use selected roots directly
  in dense or sparse polynomials, or combine real and imaginary algebraic parts
  for exact complex arithmetic. Domains and mixed-type promotion are inferred;
  no manual number-field setup is needed. See [algebraic coefficients](docs/content/tutorial/algebraic-coefficients.md).
- **Find exact real and complex roots.** Reuse roots such as $\sqrt{2}$ as
  coefficients, or find every complex algebraic root with its multiplicity.
  Root witnesses and polynomial reconstruction establish completeness while
  coefficients stay exact. Reuse a prepared Sturm chain for repeated rational
  interval counts. See [root workflows](docs/content/tutorial/array-roots.md).
- **Find and refine validated numerical roots.** Compute real intervals or
  complex rectangles with certified root counts, then refine checked results
  to a tighter width. Explicit completeness, accuracy, and isolation flags
  tell you what the result establishes. See [numerical root covers](docs/content/tutorial/array-roots.md#choose-the-numerical-claim-you-need).

Independent checkers verify factor products, membership identities, enclosure
bounds, and root or CAD evidence against the original inputs. The
[certificate guide](docs/content/guides/certificates.md) explains the precise
claim behind each check. Use `_checked` operations and `poly.exact` to retain
and verify exact algebra results directly from coefficient arrays; see
[checked results](docs/content/tutorial/array-checked.md). For stronger resultant
verification, `resultant_certified` retains the complete determinant proof. Exact
interval sign queries, sparse modular GCD selection, and configurable sparse
division orders are available through the same array interface.

## Install

Poly Mojo 1.0.2 targets Mojo 1.2.0 on Linux (x86-64 and ARM64) and on macOS with
Apple silicon. Install version 1.0.2 from the Modular community channel. If that
version is not yet available in the channel, build from a checkout as described
below.

Add the channels to your project's `pixi.toml`:

```toml
[workspace]
channels = ["https://conda.modular.com/max", "https://repo.prefix.dev/modular-community", "conda-forge"]
```

Then add the package, which provides the `poly` and `polynomials` modules:

```sh
pixi add "poly_mojo==1.0.2"
```

### Build from a checkout

```sh
git clone https://github.com/Spellbound-Mojo/poly_mojo.git
cd poly_mojo
pixi install --locked
pixi run --locked build
pixi run --locked mojo run -I build docs/examples/tutorial_first.mojo
```

The build fetches and precompiles the pinned apn_mojo 1.0.2 dependency, and all three
compiled packages are ready to import from `build/`. See
[installation](docs/content/start/installation.md) for details.

## A first calculation

This program expands $(x+1)^3$ and evaluates the polynomial and its derivative
at $x=3$. Both results are exact.

```mojo
"""Expand (1 + x)^3 and evaluate it and its derivative exactly."""
import poly
from apn_mojo import Integer
from std.testing import assert_equal


def main() raises:
    var polynomial = poly.dense.power([1, 1], 3)
    var value = poly.dense.evaluate(polynomial, 3)
    var slope = poly.dense.evaluate(poly.dense.derivative(polynomial), 3)
    assert_equal(value, Integer(64))
    assert_equal(slope, Integer(48))
    print("Value at 3:", value)
    print("Derivative at 3:", slope)
```

Save it as `first.mojo` and run `pixi run mojo run first.mojo`. It prints
`Value at 3: 64` and `Derivative at 3: 48`. The
[first tutorial](docs/content/tutorial/first-polynomial.md) explains coefficient order,
exact domain inference, and optional work limits.

## Roots, equations, and inequalities

Use `dense.real_roots` for exact algebraic root values and `dense.real_root_cover`
or `dense.complex_root_cover` for certified enclosures. Use
`dense.complex_roots` for exact complex algebraic values with multiplicities, or
`complex_roots_to` to check them incrementally. Covers accept algebraic
coefficients directly and retain their conversion evidence. Reuse a
`sparse.groebner` result for reduction and ideal membership, or pass readable
constraints such as `cad.negative(p)` to `cad.solve`, including polynomials with
real algebraic coefficients. Root and CAD stream
functions feed independent checkers without collecting the full witness history.

See [root workflows](docs/content/tutorial/array-roots.md) and
the [Gröbner](docs/content/tutorial/array-systems.md) and [CAD](docs/content/tutorial/array-cad.md)
tutorials for complete examples using coefficient iterables and inferred domains.

## Series, bases, and rational functions

Use `poly.series` to compute reciprocals, exponentials, and compositions to an
explicit formal order. `poly.basis` works with Newton, Chebyshev, and Bernstein
coefficients, including arithmetic and subdivision. `poly.rational` normalizes
polynomial ratios over QQ, QQi, GF(p), AA, and QQbar, with partial fractions, Laurent
expansions, and residues at exact algebraic centers. Independent checks verify
complete cancellation and the irreducibility of partial-fraction factors.
All three accept exact coefficient inputs and optional work limits.
`rational.adaptive_evaluate` increases precision to certify a requested quotient
accuracy, while keeping unresolved denominators explicit.

Start with [formal series](docs/content/tutorial/array-series.md),
[basis coefficients](docs/content/tutorial/array-bases.md), or
[rational functions](docs/content/tutorial/array-rational.md).

## Numerical arrays and batches

Numerical coefficient arrays use explicit floating-point or ball contexts.
Interpolation, transformations, formal series, and alternative bases share that
interface. Checked division retains residual bounds, and certified evaluation
can refine precision toward an explicit accuracy target.
You can also evaluate at exact algebraic points, recover real-root
multiplicities, inspect and polish numerical root candidates, save complete
polynomial values, and map budget-aware functions across broadcast batches
of polynomials. See the [numerical array tutorial](docs/content/tutorial/array-numeric.md)
and [batching tutorial](docs/content/tutorial/array-batching.md).
[Value serialization](docs/content/tutorial/array-serialization.md) preserves series
orders, basis nodes, rational functions, algebraic witnesses, and batch shapes.
Checked archives also retain exact-result certificates, root evidence, CAD trees,
and certified evaluations; loading verifies their evidence before returning.
Numerical rational functions use explicit contexts, with independently checked
quotient enclosures when you need guaranteed bounds.

## More polynomial tools

| Task | Start with |
|---|---|
| Choose coefficients and a representation | [Domains](docs/content/guides/domains.md), [polynomial arrays](docs/content/tutorial/arrays.md) |
| Divide, simplify, and factor | [Exact algebra](docs/content/tutorial/array-exact.md), [rational functions](docs/content/tutorial/array-rational.md) |
| Differentiate, integrate, or reconstruct a polynomial | [Calculus](docs/content/tutorial/arrays.md#divide-integrate-and-evaluate-at-many-points), [interpolation](docs/content/tutorial/array-exact.md#recover-coefficients-from-exact-samples) |
| Change basis or compute a local expansion | [Polynomial bases](docs/content/tutorial/array-bases.md), [formal series](docs/content/tutorial/array-series.md) |
| Find exact real and complex roots | [Roots](docs/content/tutorial/array-roots.md) |
| Evaluate with arbitrary precision or interval bounds | [Numerical coefficients](docs/content/tutorial/array-numeric.md), [certified evaluation](docs/content/tutorial/array-certified.md) |
| Handle work limits and inconclusive results | [Budgets and errors](docs/content/guides/errors.md) |

The [API reference](docs/content/reference/index.md) lists operations by topic.
[Support and limitations](docs/content/guides/status.md) explains domain and
certificate boundaries. The [architecture overview](docs/content/architecture/overview.md)
connects the public types to the algorithms and independent checkers.

## Documentation

Read the [documentation site](https://spellbound-mojo.github.io/poly_mojo/),
browse the [tutorials and examples](docs/content/examples/index.md), or run the
site locally from a checkout:

```sh
pixi run --locked -e docs docs-serve
pixi run --locked -e docs docs-check
```

The site includes runnable examples, mathematical explanations, and generated
API declarations. To contribute, follow the
[contribution guide](CONTRIBUTING.md) for build, test, and
compatibility workflows.

## License

Apache License 2.0; see [LICENSE](LICENSE). Modules adapted from SymPy, Z3,
SMT-RAT and CArL keep their upstream notices in their source headers and in
[`licenses/`](licenses/).
