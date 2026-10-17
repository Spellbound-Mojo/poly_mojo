"""Distinct-degree and Cantor–Zassenhaus factorization with an explicit seed.

Reference: SymPy galoistools.py (distinct/equal-degree factorization).
Our loops use explicit worklists and a shared budget.

Copyright (c) 2006-2023 SymPy Development Team

All rights reserved.

Redistribution and use in source and binary forms, with or without
modification, are permitted provided that the following conditions are met:

  a. Redistributions of source code must retain the above copyright notice,
     this list of conditions and the following disclaimer.
  b. Redistributions in binary form must reproduce the above copyright
     notice, this list of conditions and the following disclaimer in the
     documentation and/or other materials provided with the distribution.
  c. Neither the name of SymPy nor the names of its contributors
     may be used to endorse or promote products derived from this software
     without specific prior written permission.


THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
ARE DISCLAIMED. IN NO EVENT SHALL THE REGENTS OR CONTRIBUTORS BE LIABLE FOR
ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY
OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH
DAMAGE.
"""
from .coefficients import ModInt
from .dense import DensePoly
from .certificates import Factorization
from .squarefree import squarefree
from ._dense_reduction import _DenseReducer, _dense_reducer
from .errors import Budget, PolyError, PolyErrorKind, _allocation, _sum
from ._dense_ops import _copy, _one, _gcd, _exact, _derivative
from . import _nmod


@fieldwise_init
struct _SplitMix64(Movable):
    var state: UInt64

    def _next(mut self, mut budget: Budget) raises PolyError -> UInt64:
        budget.charge(1)
        self.state += 0x9E3779B97F4A7C15
        var z = self.state
        z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9
        z = (z ^ (z >> 27)) * 0x94D049BB133111EB
        return z ^ (z >> 31)


def _pow_mod(f: DensePoly[ModInt], exponent: UInt64, modulus: DensePoly[ModInt], mut budget: Budget) raises PolyError -> DensePoly[ModInt]:
    var reduction = _dense_reducer(modulus, budget)
    return _pow_prepared(f, exponent, reduction, budget)


def _pow_prepared(f: DensePoly[ModInt], exponent: UInt64, reduction: _DenseReducer[ModInt], mut budget: Budget) raises PolyError -> DensePoly[ModInt]:
    var result = _one(f, budget)
    var base = reduction.remainder(_copy(f, budget), budget)
    var n = exponent
    while n:
        budget.charge(1)
        if n & 1:
            result = reduction.product(result, base, budget)
        n >>= 1
        if n:
            base = reduction.product(base, base, budget)
    return result^


def _equal_degree(f: DensePoly[ModInt], degree: Int, mut rng: _SplitMix64, mut factors: List[DensePoly[ModInt]], mut budget: Budget) raises PolyError:
    _allocation[DensePoly[ModInt]](1, budget)
    var pending: List[DensePoly[ModInt]] = [_copy(f, budget)]
    while len(pending):
        budget.charge(1)
        var g = pending.pop()
        if g.degree() == degree:
            _allocation[DensePoly[ModInt]](1, budget)
            factors.append(g^)
            continue
        var reduction = _dense_reducer(g, budget)
        var divisor = _one(g, budget)
        while divisor.degree() <= 0 or divisor.degree() == g.degree():
            budget.charge(1)
            _allocation[ModInt](g.degree(), budget)
            var values = List[ModInt](capacity=g.degree())
            for _ in range(g.degree()):
                values.append(ModInt.zero(g.ring)._with_residue(rng._next(budget) % g.ring.value))
            var a = DensePoly[ModInt].from_coefficients(g.variable, g.ring, values^, budget)
            divisor = _gcd(g, a, budget)
            if divisor.degree() > 0 and divisor.degree() < g.degree():
                break
            var h: DensePoly[ModInt]
            if g.ring.value == 2:
                var power = _copy(a, budget)
                h = _copy(a, budget)
                for _ in range(1, degree):
                    budget.charge(1)
                    power = _pow_prepared(power, 2, reduction, budget)
                    h = h.add(power, budget)
            else:
                var power = _pow_prepared(a, (g.ring.value - 1) // 2, reduction, budget)
                h = _copy(power, budget)
                for _ in range(1, degree):
                    budget.charge(1)
                    var frobenius = _pow_prepared(h, g.ring.value, reduction, budget)
                    h = reduction.product(frobenius, power, budget)
                h = h.sub(_one(g, budget), budget)
            divisor = _gcd(g, h, budget)
        _allocation[DensePoly[ModInt]](2, budget)
        pending.append(_exact(g, divisor, budget))
        pending.append(divisor^)


def _less(a: DensePoly[ModInt], b: DensePoly[ModInt], mut budget: Budget) raises PolyError -> Bool:
    budget.charge(1)
    if a.degree() != b.degree():
        return a.degree() < b.degree()
    for i in range(a.degree(), -1, -1):
        budget.charge(1)
        if a.coefficients[i].value != b.coefficients[i].value:
            return a.coefficients[i].value < b.coefficients[i].value
    return False


def factor_mod_p(f: DensePoly[ModInt], mut budget: Budget, seed: UInt64) raises PolyError -> List[DensePoly[ModInt]]:
    """Factor a monic squarefree polynomial over its explicit prime field.

    Args:
        f: The monic squarefree input; one has an empty factor list.
        budget: The shared work allowance.
        seed: The SplitMix64 seed used for equal-degree splitting.

    Returns:
        Monic irreducibles sorted by degree and coefficients from the leading one down.

    Raises:
        PolyError: DOMAIN for zero, nonmonic, nonsquarefree or malformed input, LIMIT or CAPACITY on work limits.
    """
    f.check_invariants(budget)
    if f.is_zero() or f.coefficients[f.degree()].value != 1:
        raise PolyError(PolyErrorKind.DOMAIN, "finite-field factorization requires a monic input")
    var factors = List[DensePoly[ModInt]]()
    if f.ring.value > 2:
        _native_factors(f, seed, factors, budget)
        _sort_factors(factors, f, budget)
        return factors^
    if _gcd(f, _derivative(f, budget), budget).degree() > 0:
        raise PolyError(PolyErrorKind.DOMAIN, "finite-field factorization requires a squarefree input")
    var remaining = _copy(f, budget)
    var x = DensePoly[ModInt].from_coefficients(f.variable, f.ring, [ModInt.zero(f.ring), ModInt.one(f.ring)], budget)
    var power = _copy(x, budget)
    var degree = 1
    var reduction = _dense_reducer(remaining, budget)
    var rng = _SplitMix64(seed)
    while degree <= remaining.degree() // 2:
        budget.charge(1)
        power = _pow_prepared(power, f.ring.value, reduction, budget)
        var block = _gcd(remaining, power.sub(x, budget), budget)
        if block.degree() > 0:
            _equal_degree(block, degree, rng, factors, budget)
            remaining = _exact(remaining, block, budget)
            reduction = _dense_reducer(remaining, budget)
            power = reduction.remainder(power^, budget)
        degree = _sum(degree, 1)
    if remaining.degree() > 0:
        _allocation[DensePoly[ModInt]](1, budget)
        factors.append(remaining^)
    _sort_factors(factors, f, budget)
    return factors^


def _sort_factors(mut factors: List[DensePoly[ModInt]], f: DensePoly[ModInt], mut budget: Budget) raises PolyError:
    # Stable insertion sort moves polynomial buffers instead of copying them.
    for i in range(1, len(factors)):
        budget.charge(1)
        var current = DensePoly[ModInt](f.variable, f.ring.copy())
        swap(current, factors[i])
        var j = i
        while j > 0 and _less(current, factors[j - 1], budget):
            var moved = DensePoly[ModInt](f.variable, f.ring.copy())
            swap(moved, factors[j - 1])
            swap(moved, factors[j])
            j -= 1
        swap(current, factors[j])


def _native_factors(f: DensePoly[ModInt], seed: UInt64, mut factors: List[DensePoly[ModInt]], mut budget: Budget) raises PolyError:
    # Odd primes use native Montgomery residues; the factor set is canonical,
    # so it does not depend on the splitting strategy.
    var field = _nmod._field(f.ring.value)
    _allocation[UInt64](len(f.coefficients), budget)
    var native = List[UInt64](capacity=len(f.coefficients))
    for i in range(len(f.coefficients)):
        native.append(_nmod._to(f.coefficients[i].value, field))
    if len(_nmod._gcd(native, _nmod._derivative(native, field, budget), field, budget)) > 1:
        raise PolyError(PolyErrorKind.DOMAIN, "finite-field factorization requires a squarefree input")
    var found = _nmod._distinct_degree(native, field, seed, budget)
    _allocation[DensePoly[ModInt]](len(found), budget)
    for g in found:
        _allocation[ModInt](len(g), budget)
        var values = List[ModInt](capacity=len(g))
        for v in g:
            values.append(ModInt.zero(f.ring)._with_residue(_nmod._from(v, field)))
        factors.append(DensePoly[ModInt]._from_canonical(f.variable, f.ring, values^))


def factor_finite_field(f: DensePoly[ModInt], mut budget: Budget, seed: UInt64 = 0) raises PolyError -> Factorization[ModInt]:
    """Factor any prime-field polynomial, including repeated and inseparable factors.

    Args:
        f: The input, including zero, constants and nonmonic polynomials.
        budget: The shared work allowance.
        seed: The deterministic equal-degree splitting seed; defaults to zero.

    Returns:
        The leading coefficient and monic irreducibles with positive multiplicities,
        sorted by degree and then leading-to-constant residue vectors.

    Raises:
        PolyError: DOMAIN for malformed input, LIMIT or CAPACITY on work limits.
    """
    var blocks = squarefree(f, budget)
    var factors = List[Tuple[DensePoly[ModInt], Int]]()
    for block in blocks.factors:
        budget.charge(1)
        var split = factor_mod_p(block[0], budget, seed)
        _allocation[Tuple[DensePoly[ModInt], Int]](len(split), budget)
        for i in range(len(split)):
            var item = DensePoly[ModInt](f.variable, f.ring.copy())
            swap(item, split[i])
            factors.append((item^, block[1]))
    for i in range(1, len(factors)):
        var j = i
        while j > 0 and _less(factors[j][0], factors[j - 1][0], budget):
            budget.charge(1)
            var held = (DensePoly[ModInt](f.variable, f.ring.copy()), 0)
            swap(held, factors[j])
            swap(held, factors[j - 1])
            swap(held, factors[j])
            j -= 1
    var unit = ModInt.zero(f.ring)
    swap(unit, blocks.unit)
    return Factorization[ModInt](unit^, factors^)
