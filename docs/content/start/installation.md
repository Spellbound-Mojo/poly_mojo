# Installation and first run

Poly Mojo 1.0.1 targets **Mojo 1.2.0** on Linux (x86-64 and ARM64) and on macOS with
Apple silicon. Install the `poly_mojo` package from the Modular community
channel, or build the library from a checkout.

## Install the package

These instructions require `poly_mojo` 1.0.1, which uses Mojo 1.2.0 and
apn_mojo 1.0.2. If version 1.0.1 is not yet available in the channel, build from
a checkout as described below. The older 1.0.0 package targets Mojo 1.1.0.

Add the channels to your project's `pixi.toml`:

```toml
[workspace]
channels = ["https://conda.modular.com/max", "https://repo.prefix.dev/modular-community", "conda-forge"]
```

Then add the package:

```sh
pixi add "poly_mojo==1.0.1"
```

The package provides the `poly` and `polynomials` modules and brings in
apn_mojo 1.0.2 and a matching Mojo 1.2 compiler. Programs import the modules
directly; no include path is needed.

## Run a first example

Save the program from [your first polynomial](../tutorial/first-polynomial.md)
as `first.mojo` in your project and run it:

```sh
pixi run mojo run first.mojo
```

The program prints:

```text
Value at 3: 64
Derivative at 3: 48
```

It computes $(x+1)^3$ and its derivative at $x=3$ using inferred integer coefficients.
Continue with [your first polynomial](../tutorial/first-polynomial.md) for a
walkthrough.

Import `poly` for coefficient arrays, public core types and functions from
`polynomials`, and numeric values such as `Rational` from `apn_mojo`. Use a
`main` entry point that allows errors to propagate, as the examples do.

## Build from a checkout

Install [Pixi](https://pixi.sh/), clone the repository, and build the
packages:

```sh
git clone https://github.com/Spellbound-Mojo/poly_mojo.git
cd poly_mojo
pixi install --locked
pixi run --locked build
pixi run --locked mojo run -I build docs/examples/tutorial_first.mojo
```

Run these commands from the checkout root, where `pixi.toml` lives.
`--locked` keeps the environment consistent with `pixi.lock`.

The build fetches the pinned apn_mojo source into `.cache/deps/` and produces
`build/apn_mojo.mojoc`, `build/polynomials.mojoc`, and `build/poly.mojoc`.
Python and Pixi run the development tools; polynomial arithmetic runs in Mojo.

To run your own program against the checkout, pass the build directory:

```sh
pixi run --locked mojo run -I build path/to/your_program.mojo
```

The `-I build` option makes all three compiled packages visible. For source-level
work on the library, use `-I src -I build`; source imports then use the local
library and the compiled apn_mojo dependency. Rebuild after changing the pinned
compiler or dependency version.

## Browse the documentation locally

```sh
pixi run --locked -e docs docs-serve
```

The separate `docs` environment supplies MkDocs and the rendering dependencies.
`pixi run --locked -e docs docs-check` builds the site and checks its links and
content inventory.
