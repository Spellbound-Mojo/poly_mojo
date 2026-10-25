# Contributing

Maintain the mathematical guarantees alongside the implementation. A useful
change preserves canonical representations, deterministic results, explicit
resource limits, and the precise claim each certificate checker establishes.
The public API is already implemented; this guide covers the work of keeping
it correct, usable, and compatible.

## Set up the checkout

Follow [installation](docs/content/start/installation.md), then build with the pinned
Mojo toolchain:

```sh
pixi install --locked
pixi run --locked build
```

The build prepares apn_mojo in this checkout and writes all three library packages
to `build/`. Use `pixi run --locked` for Mojo commands so the compiler and
standard-library environment agree. Dependency commits are recorded in
`scripts/deps.py`; the lockfile pins the tool environment.

## Repository map

| Path | Purpose |
|---|---|
| `src/poly/`, `tests/poly/` | User-facing coefficient arrays and their tests |
| `src/polynomials/` | Public modules and private algorithm helpers |
| `tests/polynomials/` | Algorithm, boundary, and certificate tests |
| `tests/support/` | Deterministic generators and independent checking helpers |
| `tests/reference/` | Retained independent corpus and kernel vectors |
| `tests/contracts/` | Current and historical API declaration snapshots |
| `tests/compile/`, `tests/compile_fail/` | Consumer compilation and rejected programs |
| `docs/content/` | Tutorials, references, architecture, and theory |
| `docs/examples/` | Compiled documentation programs |
| `scripts/` | Dependency, build, test, and documentation tooling |

The [architecture overview](docs/content/architecture/overview.md) maps responsibilities
to modules. The [API index](docs/content/reference/index.md) is the quickest route from
an operation to its public contract.

## Build once, then test

Prepare the library once after changing its source or build inputs:

```sh
pixi run --locked build
```

This produces the shared `apn_mojo`, `polynomials`, and `poly` packages in
`build/`. The two repository packages are each precompiled once. Their
compiler docstring diagnostics are recorded in the same pass. Every test
command below consumes these packages; none rebuilds the library or imports
it from `src/`.

The runtime suite compiles into one executable. Each test then runs in its own
process, so an assertion failure does not stop the remaining checks. The runner
caches that executable using the library build, test and helper sources, compiler
settings, and generated entry points. An unchanged rerun performs no compilation.

Select tests to execute by part of their path:

```sh
pixi run --locked python scripts/suite.py --library-only --jobs 2 test_division
```

The first runtime invocation builds the complete selected suite, even when you
filter execution. Later filters reuse that executable. The full library route
adds layering, independent fixtures, recorded docstring checks, and tooling tests:

```sh
pixi run --locked test-library --jobs 2
```

Compiler-rejection tests run separately. They require individual compiler calls
because each program must fail with its expected diagnostic:

```sh
pixi run --locked test-rejections --jobs 2
```

Run both commands for library release validation; CI has separate steps for them.
`--jobs` controls runtime test processes in the runtime suite and concurrent
compiler calls in the rejection suite. Runtime compilation uses two compiler
threads by default to limit peak memory. Set `--compiler-threads` explicitly
when the machine has enough RAM for more; this is separate from `--jobs`.
The regular correctness suite uses O0 to keep compilation work and memory down.
Use `--optimization 3` for a separate optimized suite when the machine has enough
RAM. The combined O3 harness can exceed 20 GB during compilation; more compiler
threads can increase that peak. These options do not rebuild the library.

The API and documentation matrices each build one executable per optimization
setting, O0 and O3, against the same library build. Their `--only` option defines
a smaller suite when you need a focused check:

```sh
pixi run --locked test-api --only test_boundary --output .cache/api-boundary --jobs 2
pixi run --locked docs-test --only tutorial_division --output .cache/docs-division --jobs 2
```

Omit `--only` to run a complete matrix. Use a fresh documentation report
directory. Each report identifies the library build, package hashes, executable
fingerprint, and whether the executable was reused. The main suite prints
completed results immediately and saves them after each test; an interrupted report has `complete: false` and no aggregate pass result.
Runtime reports live in `.cache/tests/library.json` for the named task and
`report.json` for direct script invocations. Rejection
results live in `.cache/tests/rejections.json`. A combined compilation failure
is recorded once and prevents execution; it never falls back to compiling tests
individually.

Tests reject a missing or stale build with instructions to prepare it explicitly.
Source, toolchain, dependency, and build-script changes require a new build;
changes confined to tests or documentation do not. Test runs hold a shared lock
so a build command cannot replace their packages while they are running.
The scripts also accept `--build <directory>` for a separately prepared build.
The old `suite.py --no-build` spelling remains accepted; it is now redundant.

The combined compilation shares generic specializations across its tests.
That first compilation can still be substantial; execution filters and unchanged
reruns reuse its result. Positive compiler examples join the runtime executable
and retain their output checks. Standalone test files remain usable; the runner
adapts their entry points only in generated files under `.cache/tests/executables/`.

Also run the declaration and documentation checks when their surfaces change:

```sh
pixi run --locked python tests/test_contract_p.py
pixi run --locked -e docs docs-check
```

Report which checks ran and distinguish failures from checks that were not
attempted.

## Preserve the contracts

The [exact contract](docs/content/reference/contract-p.md) and separate numerical snapshot
record exported declarations and certificate fields. Source compatibility does
not imply a stable native ABI. Coordinate a breaking change with consumers,
record the decision and migration, and update snapshots only within that
reviewed change.

Keep the following properties visible during review:

- Canonical dense and sparse forms at public boundaries, with explicit domain
  contexts and order conventions.
- Stable numerical operation schedules and explicit precision contexts.
- Complete evidence for the checker's actual claim; no acceptance based only
  on the producer's success flag.
- Charges before input-dependent work, checked size arithmetic, and typed
  errors that preserve borrowed inputs.
- Deterministic prime sequences, seeds, sorting, and certificate traversal.
- Runtime imports limited to `std` and apn_mojo, without foreign algebra calls.

[Contracts and rules](tests/CONTRACTS.md) provides the detailed requirements. When changing an internal algorithm, preserve
its external mathematical meaning even if work charges or performance change.

## Write tests with independent expectations

Use hand calculations, algebraic identities, the independent reference corpus,
or kernel vectors. Do not generate an expected answer by calling the function
being tested. A checker needs both accepted evidence and corrupted evidence
that violates each relevant condition.

Reuse the deterministic generators and checking helpers in `tests/support/`.
The corpus lists sparse terms in decreasing order, while the package stores
them in increasing order. Compare the mathematical data in the intended order;
do not silently change fixtures to match a representation mistake.

Keep `tests/reference/` as independent evidence. A suspected fixture defect
needs an independently justified correction and its own review. The [reference
material](tests/reference/README.md) explains provenance, formats, and known source defects.

## Review performance and ownership

Measure representative small and large cases before changing dispatch or
storage. Include certificate generation and checking separately when either
could dominate the cost. Record workload definitions, compiler settings,
raw results, and limitations with the change that relies on them.

Watch for unsigned size overflow, views kept across list growth, reversed term
orders at foreign-format boundaries, and coefficient normalization differences
between integers and fields. Numerical optimizations must preserve the rounding
schedule; an algebraic reassociation that is exact over `QQ` may change a
floating-point result.

The package uses pure Mojo and permissively licensed algorithm sources. Keep
source attribution in headers and `licenses/`; consult the [source map](tests/reference/README.md)
before adapting an external implementation.

## Keep the documentation current

Update the affected tutorial, reference explanation, or architecture page with
the code. Public declarations render from source docstrings, but the workflows
and explanations still need review. Follow [maintaining the docs](scripts/DOCUMENTATION.md)
for voice, executable examples, mathematical notation, and site checks.

The published documentation is for library users. Keep development plans,
handoff notes, logs, benchmark reports, and API test snapshots out of `docs/`.
Store temporary records under the ignored `.cache/` directory. Use independent
benchmark suites such as [polybench](https://github.com/tueda/polybench) in a
separate checkout, and retain benchmark inputs, provenance, and results there.
Report ordinary operation time, operation time with certificate construction,
and certificate verification time separately. Contributor instructions live in
this guide, `scripts/DOCUMENTATION.md`, and `tests/`.
