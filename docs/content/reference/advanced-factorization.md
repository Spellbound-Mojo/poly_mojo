# Multivariate factorization and sparse gcd

For the array workflow, see [exact algebra](../tutorial/array-exact.md#factor-or-group-repeated-roots).
Coefficient-array users can select this sparse GCD algorithm with
`sparse.gcd(a, b, method="modular")`, or retain its evidence through
`sparse.gcd_checked`. See [exact array choices](../tutorial/array-checked.md#exact-queries-and-algorithm-choices).

`factor_multivariate` and `factor_multivariate_integer` separate recursive
polynomial content, remove repeated factors, and use a monic transformation
followed by deterministic evaluation and exact multivariate Hensel lifting.
Repeated specializations are rejected. Three distinct deterministic good
points are compared by factor count and coefficient height. Split specialized
factors are lifted as formal series through the input's total parameter degree
and recombined by exact trial division. Rational factors are normalized
by their last stored coefficient; integer factors are primitive with positive
last stored coefficient. Results are sorted by total degree and stored
monomial/coefficient order. Multiplicities and the scalar reconstruct the
original input, including zero and constants.

`factor_multivariate_gaussian` and `factor_multivariate_finite_field` cover
`QQi` and prime fields, including repeated factors. They separate squarefree blocks before a mixed-radix
Kronecker substitution, univariate factorization and exact sparse trial
division. The dense image requires up to $\prod_j (\deg_{x_j} f + 1)$
coefficient slots per block $f$, and subset recombination can take exponential work.
The shared budget covers image storage, candidate products and divisibility
tests. These routines preserve the input's monomial order and normalize every
factor to leading coefficient one. For `KERNEL` storage order, the scalar
accounts for normalization of each factor; it need not equal the input's last
stored coefficient.

`squarefree_multivariate` groups factors by multiplicity directly in sparse
storage. It supports `QQ`, `QQi` and prime fields; the array API promotes
integer input to `QQ`. `SparseSquarefreeDecomposition` stores the normalizing
scalar and monic blocks in increasing multiplicity. Its checker verifies the
product equation, without separately certifying squarefreeness or coprimality.

`check_multivariate_factorization` verifies the complete product. Like the
existing univariate product checker, it does not prove irreducibility.

`sparse_gcd` and `sparse_gcd_integer` use a fixed prime sequence, modular support
discovery, support-based interpolation and CRT reconstruction. Interpolation
solves for projective coefficients using evaluated univariate gcds; it does
not allocate a dense parameter-degree box. Failed interpolation or changing
support triggers recursive evaluation and Newton interpolation to discover
support again. Discovered monomial supports are reused across recursive samples
and primes through finite-field sparse linear interpolation; stale or singular
supports fall back to the accumulated Newton interpolant. Univariate content
and leading coefficients fix sample scaling;
degree drops discard unlucky samples. Exact trial division verifies
reconstruction. Polynomial content groups only occurring exponents and invokes
the same sparse gcd on fewer variables. Neither multivariate content nor modular
support discovery invokes PRS. Coprimality certification first tries a compact
modular affine projection over ZZ and QQ, with the exact resultant proof as a
fallback.

The returned `GcdResult` carries divisibility and independently checked
coprimality certificates. Both nonzero results include maximality evidence; the zero/zero
case has zero gcd and zero cofactors. This is an explicit sparse algorithm
entry point, independent of the existing `gcd` dispatch policy.

Integer and rational univariate factorization also include fresh exact LLL
and van Hoeij trace-knapsack recombination. This private algorithm follows
van Hoeij's 2002 knapsack method. It retains deterministic factor sorting and the
existing product certificate interface.
Hensel factors, their modulus and complementary inverses persist between
precision increases, including the handoff from singleton peeling to the lattice.

<!-- api: src/polynomials/multivariate_factor.mojo MultivariateFactorization -->

<!-- api: src/polynomials/multivariate_factor.mojo check_multivariate_factorization -->

<!-- api: src/polynomials/multivariate_factor.mojo factor_multivariate -->

<!-- api: src/polynomials/multivariate_factor.mojo factor_multivariate_integer -->

<!-- api: src/polynomials/sparse_gcd.mojo sparse_gcd -->

<!-- api: src/polynomials/sparse_gcd.mojo sparse_gcd_integer -->


<!-- api: src/polynomials/field_multivariate_factor.mojo factor_multivariate_gaussian -->

<!-- api: src/polynomials/field_multivariate_factor.mojo factor_multivariate_finite_field -->

<!-- api: src/polynomials/sparse_squarefree.mojo SparseSquarefreeDecomposition -->

<!-- api: src/polynomials/sparse_squarefree.mojo squarefree_multivariate -->

<!-- api: src/polynomials/sparse_squarefree.mojo check_sparse_squarefree_product -->
