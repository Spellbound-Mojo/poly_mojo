# Support and limitations

Poly Mojo implements exact symbolic algebra, arbitrary-precision numerical
operations, and independently checkable certificates. It targets Mojo 1.2.0 on
Linux (x86-64 and ARM64) and macOS with Apple silicon; the
[installation guide](../start/installation.md) covers the package and a checkout.

## What is available

| Area | Supported workflows |
|---|---|
| Functional arrays | Coefficient-first dense and sparse APIs, numerical contexts, algebraic evaluation, serialization, and batch broadcasting |
| Construction and arithmetic | Dense and sparse arrays, exact and numerical domains, conversions, named display, and serialization |
| Polynomial toolkit | Calculus, transformations, multipoint evaluation, interpolation, alternative bases, formal series, rational utilities |
| Exact algebra | Division, pseudo-division, gcds, resultants, univariate and multivariate factorization |
| Multivariate ideals | Gröbner bases, reduction, and certified membership over exact fields |
| Exact complex roots | Complete algebraic values with multiplicities for characteristic-zero exact coefficients |
| Exact real geometry | Sturm isolation, algebraic numbers, specialization, CAD and selective coverings |
| Validated numerics | Real and complex enclosure evaluation, adaptive accuracy, root covers and refinement |
| Incremental transport | Text, evaluation witnesses, root covers and CAD evidence |

The [domain guide](domains.md) maps coefficient types to algorithms. The
[API index](../reference/index.md) links to complete signatures and contracts.

## Boundaries that matter in applications

- **Exact and numerical domains are separate.** Rounded coefficients do not
  enter exact gcd or Gröbner algorithms implicitly.
- **A container does not imply every algorithm supports its domain.** `AA` and
  `QQbar` support ordinary exact arithmetic, squarefree decomposition,
  Gröbner bases, and univariate and multivariate irreducible factorization.
  Algebraic serialization preserves checked root witnesses; explicit numerical
  conversion and certified evaluation retain exact-value guarantees. Streaming
  evaluation automatically refines algebraic coefficients and points and checks
  their root evidence before arithmetic. Rational
  functions support QQ, QQi, GF(p), AA, and QQbar, including algebraic expansion
  centers in characteristic zero. Numerical fractions use explicit precision
  contexts and retain coefficient uncertainty.
  CAD accepts real algebraic coefficients in retained, specialized, and streaming
  workflows. Lifting follows only the supplied coefficient values, while the
  expanded rational projection and exact root arithmetic can still be costly.
- **Numerical families can be inconclusive.** Input uncertainty may prevent
  a uniform degree or root count. More working precision cannot remove it.
- **Proof claims are specific.** A factor product check does not establish
  irreducibility, and a common-divisor check does not establish maximality.
  `exact.check` for `AA` and `QQbar` factorization additionally checks irreducibility.
  `rational.check` proves complete normalization, and partial-fraction checks
  establish irreducible factors over QQ, QQi, GF(p), AA, and QQbar. The complete
  rational irreducibility fallback can be expensive; use an explicit budget.
- **CAD cost can grow quickly.** Variable order and whether you need a full
  decomposition or only a witness affect the work substantially.
- **Resource limits are explicit.** Budget exhaustion raises; it never becomes
  a mathematical answer. Incremental APIs reduce retained data without
  promising constant memory.
- **Compatibility is at source level.** Public Mojo declarations do not imply
  a stable native ABI or a universal certificate wire format. See
  [source compatibility and certificates](../reference/contract-p.md).
