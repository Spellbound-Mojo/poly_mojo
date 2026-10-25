# Greatest common divisors

## Definitions and normal forms

**Definition G-1.** In an integral domain $R$, $g$ is a *greatest common
divisor* of $f$ and $h$ when $g \mid f$, $g \mid h$, and every common
divisor of $f$ and $h$ divides $g$. In a unique factorization domain a
gcd exists and is unique up to a unit factor. The package returns the
*normalized* gcd:

| Ring | Units | Normalized gcd |
|---|---|---|
| $\mathbb Q[X]$, $\mathbb F_p[X]$ | nonzero constants | leading coefficient $1$ in the polynomial's order |
| $\mathbb Z[X]$ | $\pm 1$ | positive leading coefficient |

and $\gcd(0, 0) = 0$.

**Definition G-2.** For $f \in R[x]$ with $R$ a UFD, the *content*
$\operatorname{cont}(f)$ is a gcd of its coefficients and the *primitive
part* is $\operatorname{pp}(f) = f / \operatorname{cont}(f)$; $f$ is
*primitive* when its content is a unit.

**Theorem G-1 (Gauss's lemma, cited).** Over a UFD $R$, the product of two
primitive polynomials is primitive, so
$\operatorname{cont}(fg) = \operatorname{cont}(f)\operatorname{cont}(g)$ up
to units; $R[x]$ is a UFD, and
$\gcd(f, g) = \gcd(\operatorname{cont} f, \operatorname{cont} g)\cdot \gcd(\operatorname{pp} f, \operatorname{pp} g)$
[von zur Gathen and Gerhard 2013, §6.2].

## Euclid's algorithm and Bézout coefficients

**Theorem G-2 (extended Euclidean algorithm).** Over a field $K$, for
$f, h \in K[x]$ not both zero, the remainder sequence
$r_0 = f$, $r_1 = h$, $r_{i+1} = r_{i-1} \bmod r_i$ ends with a last nonzero
$r_\ell$, a gcd of $f$ and $h$, and the extended algorithm computes
$u, v \in K[x]$ with $u f + v h = r_\ell$, $\deg u < \deg h - \deg r_\ell$,
$\deg v < \deg f - \deg r_\ell$ (when the degrees are positive).

*Proof.* Each step preserves the set of common divisors, since
$r_{i+1} = r_{i-1} - q_i r_i$; degrees decrease, so the sequence ends, and
the last nonzero remainder divides its predecessor, hence all of them. The
cofactors are maintained by the same recurrence; the degree bounds follow
by induction [von zur Gathen and Gerhard 2013, §3.2]. $\square$

## Coefficient growth: subresultants

Over $\mathbb Z$, Euclid's algorithm in $\mathbb Q[x]$ suffers
coefficient explosion. The *subresultant polynomial remainder sequence*
uses pseudo-division (Theorem V-2) and divides each pseudo-remainder by a
predictable factor:

**Theorem G-3 (subresultant PRS, cited).** For $f, h \in R[x]$, $R$ a
UFD, the subresultant PRS stays in $R[x]$, its elements are the
subresultants of $f$ and $h$ up to sign, its coefficients are bounded by
determinants of submatrices of the Sylvester matrix (so they grow only
polynomially), and its last nonzero element is an associate of
$\gcd(f, h)$ times an element of $R$ [Collins 1967; Brown and Traub 1971;
von zur Gathen and Gerhard 2013, §6.10].

The package uses it for univariate gcds over $\mathbb Z$ of moderate
degree, and for resultants ([resultants](resultants.md)).

## Modular gcd

**Theorem G-4 (modular images, cited).** Let $f, h \in \mathbb Z[x]$ be
primitive, $g = \gcd(f, h)$, and $p$ a prime dividing neither leading
coefficient. Then $\deg \gcd(f \bmod p, h \bmod p) \ge \deg g$, with
equality for all but finitely many such $p$ (the *unlucky* primes, which
divide a certain nonzero subresultant) [Brown 1971; von zur Gathen and
Gerhard 2013, §6.4].

**Algorithm G-5 (univariate modular gcd).**

1. Make $f$ and $h$ primitive; let $c = \gcd(\operatorname{cont} f, \operatorname{cont} h)$
   and $\gamma = \gcd(\operatorname{lc} f, \operatorname{lc} h)$.
2. For primes $p$ in the fixed sequence, skipping those
   dividing either leading coefficient (as required by Theorem G-4): compute $g_p = \gamma \cdot \gcd(f \bmod p, h \bmod p)$,
   normalized to leading coefficient $\gamma \bmod p$.
3. Discard images of degree larger than the smallest seen (unlucky); on a
   smaller degree, restart the combination.
4. Combine images of the smallest degree by the Chinese remainder theorem
   into $G$ with symmetric coefficients modulo $\prod p$.
5. When $\operatorname{pp}(G)$ divides both $f$ and $h$ (trial division,
   Proposition V-3), return $c \cdot \operatorname{pp}(G)$, with positive
   leading coefficient.

**Theorem G-5.** Algorithm G-5 terminates and returns $\gcd(f, h)$.

*Proof.* Correctness does not rest on the modular reasoning: in step 5,
$\operatorname{pp}(G)$ divides $f$ and $h$, so it divides
$g = \gcd(\operatorname{pp} f, \operatorname{pp} h)$; and its degree is the
smallest image degree seen, which is at least $\deg g$ by Theorem G-4, so
$\operatorname{pp}(G)$ and $g$ have the same degree and are associates;
both being primitive with positive leading coefficient, they are equal.
Termination: only finitely many primes are unlucky (G-4), and once the
product of lucky primes exceeds twice a bound on the coefficients of
$\gamma \cdot g / \operatorname{lc}(g)$ (the Landau–Mignotte bound,
Theorem Z-5), the reconstruction is exact and step 5 succeeds. $\square$

The final trial division makes the result correct even if the bound were
wrong; it is also what the certificate records.

## Multivariate gcd

**Algorithm G-6 (recursive gcd).** For $f, h \in K[x_1, \dots, x_n]$,
regard them as polynomials in the main variable $x_1$ over
$R = K[x_2, \dots, x_n]$; compute the contents (gcds of coefficients, by
recursion in $n - 1$ variables) and the gcd of the primitive parts by the
subresultant PRS in $R[x_1]$, then take its primitive part.

**Theorem G-6.** Algorithm G-6 returns a gcd of $f$ and $h$.

*Proof.* $R$ is a UFD, so Theorem G-1 applies in $R[x_1]$: the gcd is
the gcd of the contents times the gcd of the primitive parts, and the
primitive part of the last nonzero subresultant is an associate of the
latter (Theorem G-3). Recursion ends at $n = 0$, where $K$ is a field or
$\mathbb Z$. $\square$

Sparse modular methods (Zippel's algorithm) are faster on sparse inputs
and are a later optimization; they do not change the certificates.

Before recursive integer contents, the implementation tests whether the GCD
is only an integer times a monomial. It removes each input's minimum exponent
in every variable inside the modular images, without copying its terms. For
each variable, a specialization must preserve both reduced input degrees;
a constant univariate GCD then bounds the common divisor's degree in that
variable by zero. If all variables have this bound, the answer is exactly the
GCD of the integer coefficient contents times the common monomial. A variable
absent from either reduced input already has a zero bound. Degree loss or an
extra image factor is inconclusive and leaves the existing algorithms available.
The preliminary test limits dense image degree ranges to 4096; large monomial
shifts do not count toward that limit.

## Certificates

**Certificate G-C1 (common divisor, with cofactors).** Data: $g$, $f'$,
$h'$. Check: $f = g f'$ and $h = g h'$. Claim: $g$ divides $f$ and $h$.
This is all a cancellation needs (Theorem F-2).

**Theorem G-7 (Bézout certificate).** Over a field, if $f = g f'$,
$h = g h'$, and $g = u f + v h$ for some polynomials $u, v$, then $g$ is a
gcd of $f$ and $h$.

*Proof.* Every common divisor $d$ divides $uf + vh = g$; and $g$ divides
both. $\square$

**Certificate G-C2 (gcd, univariate over a field).** Data: $g$, $f'$, $h'$,
$u$, $v$. Check: $f = g f'$, $h = g h'$, $g = uf + vh$. Claim: $g$ is a gcd
(Theorem G-7). Over $\mathbb Z[x]$, where a Bézout identity with $g$ on
the right need not exist, the certificate is G-C3 applied to the
cofactors.

**Theorem G-8 (coprimality certificate).** Let
$f', h' \in K[x_1, \dots, x_n]$, $K$ a field or $\mathbb Z$. Suppose
$u f' + v h' = s$ for some polynomials $u, v$ and some nonzero $s$ that
does not involve $x_1$, and that the contents of $f'$ and $h'$ with
respect to $x_1$ are coprime. Then $f'$ and $h'$ are coprime.

*Proof.* $K[x_1, \dots, x_n]$ is a UFD. Suppose an irreducible $d$ divides
$f'$ and $h'$. Then $d$ divides $s$; since $s \neq 0$ does not involve
$x_1$, $\deg_{x_1} d = 0$, so $d \in K[x_2, \dots, x_n]$. A polynomial free
of $x_1$ that divides a polynomial divides each of its coefficients with
respect to $x_1$, hence its content. So $d$ divides both contents, which
contradicts their coprimality (if $d$ is a unit it is not irreducible).
$\square$

**Certificate G-C3 (coprimality).** Data: $u$, $v$, $s$, and a
coprimality certificate for the contents, in fewer variables (recursively;
in no variable, two coprime integers or nonzero rationals). Check:
$u f' + v h' = s$, $s \neq 0$, $s$ free of $x_1$, and the recursive
certificate. Claim: $f'$ and $h'$ are coprime (Theorem G-8). The natural
choice of $s$ is the resultant $\operatorname{res}_{x_1}(f', h')$ with its
cofactors (Theorem E-3).

**Certificate G-C3M (modular affine projection).** For nonzero integer
polynomials $F,H$, choose an admitted prime $p$ and substitute
$x_i=a_it+b_i$ modulo $p$. Check that both images retain their original
total degrees, and verify a univariate identity
$U\overline F+V\overline H=1$ in $\mathbb F_p[t]$. Also verify an exact
integer linear combination of selected coefficients of $F,H$ equal to 1.
These checks establish coprimality over $\mathbb Z$.

*Proof.* If $F=DA$, total degree is additive. Substitution and reduction
cannot increase degree, so preserving the degree of $F$ forces the images
of both $D$ and $A$ to preserve their degrees. A nonconstant common divisor
would therefore remain a positive-degree common divisor of both images,
contradicting the verified identity. The integer coefficient identity
excludes shared integer factors, which could become units modulo $p$.
For rational inputs, clear denominators exactly first; integer scalar
factors are units over $\mathbb Q$, so the scalar identity is unnecessary.
$\square$

The producer tries a bounded set of lines over three fixed primes below
$2^{30}$. Images with lost degree or a nonconstant GCD are inconclusive;
they never establish noncoprimality. Total degrees above 256, unsuccessful
searches, and unsupported coefficient domains use G-C3. Checking G-C3M
uses projection and multiplication, without repeating polynomial GCD or
constructing a resultant. This is an exact certificate, not a probabilistic
acceptance test.

**Proposition G-9 (gcd from G-C1 and G-C3).** If $f = g f'$, $h = g h'$,
and $f'$, $h'$ are coprime, then $g$ is a gcd of $f$ and $h$.

*Proof.* In a UFD, for each irreducible $\pi$ let $v_\pi$ be the exponent
of $\pi$. The exponent of $\pi$ in $\gcd(f, h)$ is
$\min(v_\pi f, v_\pi h) = v_\pi g + \min(v_\pi f', v_\pi h') = v_\pi g$,
because coprimality of $f'$ and $h'$ makes the minimum $0$. So
$\gcd(f, h) = g$ up to a unit. $\square$
