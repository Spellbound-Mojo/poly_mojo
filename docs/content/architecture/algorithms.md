# Exact algorithms and their evidence

Exact algorithms work over integer, rational, Gaussian rational, or prime-field
coefficients as each operation permits. The implementation chooses a useful
computational route, then verifies reconstructed candidates or returns evidence
that a separate checker can inspect.

## Division, gcds, and elimination

Field division cancels leading coefficients directly. Pseudo-division keeps
coefficients in a ring by carrying an explicit scale. Multivariate ordered
reduction uses an admissible order to make each reduction decrease.

Gcd computation combines content handling, polynomial remainder sequences,
and modular techniques. Modular reconstruction avoids carrying large rational
coefficients through every intermediate step. Unlucky primes or evaluation
points can change apparent degree or support, so reconstructed candidates are
checked by exact trial division.

The explicit sparse gcd path discovers support through recursive evaluation
and interpolation, then reconstructs coefficients across a fixed sequence of
primes. It visits occurring exponent groups and reuses support only while the
samples remain compatible. Failed support assumptions trigger renewed discovery.

Gcd evidence separates divisibility from maximality. Cofactors establish the
former; Bézout identities or coprimality certificates establish the latter.
Integer and rational coprimality proofs first try a degree-preserving modular
affine projection with a univariate Bézout identity. Integer inputs also carry
an exact coefficient identity excluding scalar factors. The fallback
coprimality arena uses backward references and explicit content-gcd folds.
The checker validates each referenced input pair rather than trusting a node
merely because another pair already used it.

Resultants follow the specified Sylvester sign convention. A generic resultant
certificate records an ideal identity. Where CAD needs the determinant itself,
its projection certificate adds determinant evidence and an independent check.
After a defective subresultant degree drop, a scaling ratio may be a rational
function in the remaining variables. The implementation multiplies it into the
subresultant or Bézout numerator before exact division when the ratio itself is
not polynomial. This preserves the cancellation required by the Sylvester
minors over polynomial coefficient rings.

## Factorization

Univariate factorization separates content and repeated factors, factors over
a suitable prime field, lifts the factors, and recombines them over the integers
or rationals. The implementation includes Hensel lifting and exact LLL with
van Hoeij trace-knapsack constraints for recombination. Lifted factors and
correction data persist between precision increases.

Multivariate factorization uses deterministic evaluation points, a monic
transformation, and multivariate Hensel lifting. A good specialization can
split an original factor further; recombination and exact division recover
the original factors without assuming the specialized factors already match.
Recursive content is handled separately.

The public product checker verifies the unit, factors, and multiplicities
multiply to the input. It deliberately does not rerun factorization to prove
irreducibility. The [factorization theory](../theory/factorization.md) supplies
the algorithmic justification for the producer's stronger result.

## Gröbner bases

Buchberger's algorithm uses Gebauer–Möller pair pruning and deterministic pair
selection by the smallest least common multiple of leading monomials, with
stable index tie breaks. The
returned basis is reduced, monic, and sorted by decreasing leading monomial.
Optional cofactor tracking expresses basis elements in terms of the original
generators.

Without cofactor tracking, orders over at most sixteen variables run the same
steps on packed exponent vectors. Each monomial is a fixed-width vector in the
order's priority order with its total degree cached, so comparison and
divisibility take a few vector operations. The polynomial being reduced is kept
in geobuckets, sorted term lists of geometrically growing capacity, so each
reduction step merges the reducer's tail into the smallest bucket that fits it.
Over prime fields residues are multiplied by precomputed quotients while they
are merged. Over primes below $2^{31}$ under GRLEX and GREVLEX the packed path
is F4 instead: each round turns every pair of least LCM degree, with the
reducers symbolic preprocessing finds, into one sparse matrix and reduces its
rows in a dense 64-bit accumulator that is reduced modulo the prime only when
read. Over `QQ` under GREVLEX the inputs are homogenized, and the basis comes
from F4 images modulo primes, where later primes replay the first prime's
recorded matrices, Chinese remaindering, rational reconstruction,
and an exact certificate that the result is the reduced basis, whose S-pairs
are reduced in F4 matrices over the integers; the packed engine computes the
basis exactly if reconstruction gives up. Over `QQ` the computation is fraction-free over the integers: each
remainder is an integer multiple of the rational one, so the monic basis is the
same. Every path returns exactly the basis of the general engine; only the work
charged to the budget differs.

Ideal membership enables tracking and returns the multipliers for a direct
polynomial identity. This keeps membership checking independent of pair
selection, pruning, or basis construction. See [Gröbner theory](../theory/groebner.md)
for the criteria and termination arguments.

## Real roots and algebraic geometry

Sturm sequences establish distinct real-root counts through sign variations.
Isolation separates exact rational roots from intervals containing irrational
roots; refinement narrows a selected interval while preserving its count.
Repeated roots require explicit multiplicity information rather than reading
multiplicity from a distinct-root count.

Real algebraic arithmetic uses elimination to produce an annihilating
polynomial, then certified interval information to select the intended root.
Specialization at algebraic values can produce extra elimination roots; the
checker also verifies the original specialized equation.

CAD builds projection bases, decomposes the base line, and lifts stacks of
sections and sectors over lower-dimensional cells. Projection and lifting
justify signs throughout a cell. Complete CAD, a single queried cell, and a
selective covering carry different coverage obligations. The [CAD tutorial](../tutorial/array-cad.md)
explains which operation to choose; the [extension theory](../theory/extensions.md)
sets out the proof requirements.

## Performance evidence

Dispatch thresholds and storage choices are implementation details constrained
by these contracts. Measure the relevant workload before changing a threshold,
and check small cases as well as the large case that motivates an
optimization.
