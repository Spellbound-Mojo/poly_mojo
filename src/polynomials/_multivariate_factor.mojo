"""Evaluation and multivariate Hensel lifting through a monic transformation.

Guided by SymPy 1.13.3 factortools.py, dmp_zz_wang and its lifting helpers.
The exact rational implementation enumerates evaluation points deterministically.
"""
# Copyright (c) 2006-2023 SymPy Development Team
#
# All rights reserved.
#
# Redistribution and use in source and binary forms, with or without
# modification, are permitted provided that the following conditions are met:
#
#   a. Redistributions of source code must retain the above copyright notice,
#      this list of conditions and the following disclaimer.
#   b. Redistributions in binary form must reproduce the above copyright
#      notice, this list of conditions and the following disclaimer in the
#      documentation and/or other materials provided with the distribution.
#   c. Neither the name of SymPy nor the names of its contributors
#      may be used to endorse or promote products derived from this software
#      without specific prior written permission.
#
#
# THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
# AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
# IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
# ARE DISCLAIMED. IN NO EVENT SHALL THE REGENTS OR CONTRIBUTORS BE LIABLE FOR
# ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
# DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
# SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
# CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
# LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY
# OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH
# DAMAGE.
#
# --------------------------------------------------------------------------------
#
# Patches that were taken from the Diofant project (https://github.com/diofant/diofant)
# are licensed as:
#
# Copyright (c) 2006-2018 SymPy Development Team,
#               2013-2023 Sergey B Kirpichev
#
# All rights reserved.
#
# Redistribution and use in source and binary forms, with or without
# modification, are permitted provided that the following conditions are met:
#
#   a. Redistributions of source code must retain the above copyright notice,
#      this list of conditions and the following disclaimer.
#   b. Redistributions in binary form must reproduce the above copyright
#      notice, this list of conditions and the following disclaimer in the
#      documentation and/or other materials provided with the distribution.
#   c. Neither the name of Diofant or SymPy nor the names of its contributors
#      may be used to endorse or promote products derived from this software
#      without specific prior written permission.
#
#
# THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
# AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
# IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
# ARE DISCLAIMED. IN NO EVENT SHALL THE REGENTS OR CONTRIBUTORS BE LIABLE FOR
# ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
# DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
# SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
# CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
# LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY
# OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH
# DAMAGE.
#
# --------------------------------------------------------------------------------
#
# Submodules taken from the multipledispatch project (https://github.com/mrocklin/multipledispatch)
# are licensed as:
#
# Copyright (c) 2014 Matthew Rocklin
#
# All rights reserved.
#
# Redistribution and use in source and binary forms, with or without
# modification, are permitted provided that the following conditions are met:
#
#   a. Redistributions of source code must retain the above copyright notice,
#      this list of conditions and the following disclaimer.
#   b. Redistributions in binary form must reproduce the above copyright
#      notice, this list of conditions and the following disclaimer in the
#      documentation and/or other materials provided with the distribution.
#   c. Neither the name of multipledispatch nor the names of its contributors
#      may be used to endorse or promote products derived from this software
#      without specific prior written permission.
#
#
# THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
# AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
# IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
# ARE DISCLAIMED. IN NO EVENT SHALL THE REGENTS OR CONTRIBUTORS BE LIABLE FOR
# ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
# DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
# SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
# CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
# LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY
# OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH
# DAMAGE.
#
# --------------------------------------------------------------------------------
#
# The files under the directory sympy/parsing/autolev/tests/pydy-example-repo
# are directly copied from PyDy project and are licensed as:
#
# Copyright (c) 2009-2023, PyDy Authors
# All rights reserved.
#
# Redistribution and use in source and binary forms, with or without
# modification, are permitted provided that the following conditions are met:
#
# * Redistributions of source code must retain the above copyright
#   notice, this list of conditions and the following disclaimer.
# * Redistributions in binary form must reproduce the above copyright
#   notice, this list of conditions and the following disclaimer in the
#   documentation and/or other materials provided with the distribution.
# * Neither the name of this project nor the names of its contributors may be
#   used to endorse or promote products derived from this software without
#   specific prior written permission.
#
# THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND
# ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
# WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
# DISCLAIMED. IN NO EVENT SHALL PYDY AUTHORS BE LIABLE FOR ANY DIRECT,
# INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING,
# BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
# DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
# LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE
# OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF
# ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
#
# --------------------------------------------------------------------------------
#
# The files under the directory sympy/parsing/latex
# are directly copied from latex2sympy project and are licensed as:
#
# Copyright 2016, latex2sympy
#
# Permission is hereby granted, free of charge, to any person obtaining a copy
# of this software and associated documentation files (the "Software"), to deal
# in the Software without restriction, including without limitation the rights
# to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
# copies of the Software, and to permit persons to whom the Software is
# furnished to do so, subject to the following conditions:
#
# The above copyright notice and this permission notice shall be included in all
# copies or substantial portions of the Software.
#
# THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
# IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
# FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
# AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
# LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
# OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
# SOFTWARE.

from apn_mojo import Rational
from ._subsets import _Recombination
from ._bounded_products import _truncated_product
from .errors import Budget, PolyError, PolyErrorKind, _allocation, _sum, _charge_size
from .coefficients import QQ, ZZ, NoContext
from .monomial import Monomial
from .sparse import SparsePoly, Term
from .dense import DensePoly
from .evaluate import substitute, derivative, _derivative_dense
from ._gcd import _gcd_value, _content
from ._views import _one, _split, _join, _is_unit
from ._tower import _exact_poly
from ._dense_ops import _gcd, _exact, _remainder, _copy
from ._euclidean import _extended
from .factor import factor
from .division import divide_exact
from ._root_ops import _compare as _compare_q, _copy as _copy_q
from ._images import _integer_image, _rational_image
from ._gcd import _primitive_zz
from ._views import _lc
from ._wang import _wang, _LeadFactor
from .primes import prime, _residue
from .coefficients import _mod_mul, _mod_pow
from . import _nmod


def _normalize(f: SparsePoly[QQ], mut budget: Budget) raises PolyError -> SparsePoly[QQ]:
    return f.scale(f.terms[len(f.terms) - 1].coefficient.inverse(budget), budget)


def _parameter_degree(m: Monomial, main: Int64, mut budget: Budget) raises PolyError -> Int:
    var total = 0
    for pair in m.pairs:
        budget.charge(1)
        if pair[0] != main:
            total = _sum(total, Int(UInt64(pair[1])))
    return total


def _truncate(f: SparsePoly[QQ], main: Int64, degree: Int, mut budget: Budget) raises PolyError -> SparsePoly[QQ]:
    var terms = List[Term[QQ]]()
    for term in f.terms:
        budget.charge(1)
        if _parameter_degree(term.monomial, main, budget) <= degree:
            _allocation[Term[QQ]](1, budget)
            _charge_size(len(term.monomial.pairs), budget)
            _charge_size(term.coefficient.size(), budget)
            terms.append(term.copy())
    return SparsePoly[QQ].from_terms(terms^, f.order, NoContext(), budget)


def _shift(f: SparsePoly[QQ], variables: List[Int64], point: List[Int], inverse: Bool, evaluate: Bool, mut budget: Budget) raises PolyError -> SparsePoly[QQ]:
    var result = f._copy(budget)
    for i in range(len(variables)):
        budget.charge(1)
        var value = QQ(Rational(point[i]))
        if inverse:
            value = value.neg(budget)
        var replacement = SparsePoly[QQ].constant(value, f.order, budget)
        if not evaluate:
            replacement = replacement.add(SparsePoly[QQ].variable(variables[i], f.order, NoContext(), budget), budget)
        result = substitute(result, variables[i], replacement, budget)
    return result^


def _lift(f: SparsePoly[QQ], main: Int64, initial: List[DensePoly[QQ]], specialized: DensePoly[QQ], mut budget: Budget) raises PolyError -> List[SparsePoly[QQ]]:
    var degree = 0
    for term in f.terms:
        budget.charge(1)
        degree = max(degree, _parameter_degree(term.monomial, main, budget))
    _allocation[SparsePoly[QQ]](len(initial), budget)
    _allocation[DensePoly[QQ]](len(initial), budget)
    var factors = List[SparsePoly[QQ]]()
    var inverses = List[DensePoly[QQ]]()
    for g in initial:
        budget.charge(1)
        factors.append(g.to_sparse(f.order, budget))
        var complement = _exact(specialized, g, budget)
        var extended = _extended(complement, g, budget)
        inverses.append(_remainder(extended[1], g, budget))
    for d in range(1, _sum(degree, 1)):
        budget.charge(1)
        var product = _one(f, budget)
        for g in factors:
            budget.charge(1)
            product = _truncated_product(product, g, main, d, budget)
        var error = f.sub(product, budget)
        for term in error.terms:
            budget.charge(1)
            if _parameter_degree(term.monomial, main, budget) != d:
                continue
            var exponent = Int(UInt64(term.monomial.exponent(main, budget)))
            _allocation[QQ](_sum(exponent, 1), budget)
            var coefficients = List[QQ](length=exponent + 1, fill=QQ.zero(NoContext()))
            _charge_size(term.coefficient.size(), budget)
            coefficients[exponent] = term.coefficient.copy()
            var scalar = DensePoly[QQ].from_coefficients(main, NoContext(), coefficients^, budget)
            _allocation[Tuple[Int64, UInt32]](len(term.monomial.pairs), budget)
            var pairs = List[Tuple[Int64, UInt32]]()
            for pair in term.monomial.pairs:
                budget.charge(1)
                if pair[0] != main:
                    pairs.append(pair)
            _allocation[Term[QQ]](1, budget)
            var multiplier = SparsePoly[QQ].from_terms([Term[QQ](Monomial(pairs^, budget), QQ.one(NoContext()))], f.order, NoContext(), budget)
            for i in range(len(initial)):
                budget.charge(1)
                var correction = _remainder(scalar.mul(inverses[i], budget), initial[i], budget)
                factors[i] = factors[i].add(correction.to_sparse(f.order, budget).mul(multiplier, budget), budget)
    return factors^


def _recombine_lifted(f: SparsePoly[QQ], main: Int64, lifted: List[SparsePoly[QQ]], mut budget: Budget) raises PolyError -> List[SparsePoly[QQ]]:
    # Monic factors have parameter degree at most that of f. Formal Hensel
    # factors truncated at this degree therefore recover every true subset.
    var degree = 0
    for term in f.terms:
        budget.charge(1)
        degree = max(degree, _parameter_degree(term.monomial, main, budget))
    var search = _Recombination(len(lifted), budget)
    var remaining = f._copy(budget)
    var result = List[SparsePoly[QQ]]()
    while search.ready():
        budget.charge(1)
        var candidate = _one(f, budget)
        for index in search.selection.indices:
            budget.charge(1)
            candidate = _truncated_product(candidate, lifted[search.active[index]], main, degree, budget)
        var quotient = divide_exact(remaining, candidate, budget)
        if quotient:
            _allocation[SparsePoly[QQ]](1, budget)
            result.append(candidate^)
            remaining = quotient.take()
            search.accept(budget)
        else:
            search.advance(budget)
    if not _is_unit(remaining, budget):
        _allocation[SparsePoly[QQ]](1, budget)
        result.append(remaining^)
    return result^


def _next_point(mut point: List[Int], mut radius: Int, mut budget: Budget) raises PolyError:
    while True:
        budget.charge(1)
        var advanced = False
        for i in range(len(point) - 1, -1, -1):
            budget.charge(1)
            if point[i] < radius:
                point[i] += 1
                advanced = True
                break
            point[i] = 0
        if not advanced:
            radius = _sum(radius, 1)
            point[len(point) - 1] = radius
        for value in point:
            budget.charge(1)
            if value == radius:
                return


def _height(f: DensePoly[QQ], mut budget: Budget) raises PolyError -> QQ:
    var result = QQ.zero(NoContext())
    var zero = QQ.zero(NoContext())
    for coefficient_index in range(len(f.coefficients)):
        ref c = f.coefficients[coefficient_index]
        budget.charge(1)
        var magnitude = c.neg(budget) if _compare_q(c, zero, budget) < 0 else _copy_q(c, budget)
        if _compare_q(magnitude, result, budget) > 0:
            result = magnitude^
    return result^


def _monic_factors(f: SparsePoly[QQ], main: Int64, parameters: List[Int64], mut budget: Budget) raises PolyError -> List[SparsePoly[QQ]]:
    _allocation[Int](len(parameters), budget)
    var point = List[Int](length=len(parameters), fill=0)
    var radius = 0
    var configurations = 0
    var best_point = List[Int]()
    var best_initial = List[DensePoly[QQ]]()
    var best_specialized = DensePoly[QQ].from_coefficients(main, NoContext(), List[QQ](), budget)
    var best_height = QQ.zero(NoContext())
    while configurations < 3:
        budget.charge(1)
        _allocation[Int](len(point), budget)
        var assignment = List[Int]()
        for value in point:
            budget.charge(1)
            assignment.append((value + 1) // 2 if value % 2 else -(value // 2))
        var specialized = DensePoly[QQ].from_sparse(_shift(f, parameters, assignment, False, True, budget), budget, variable=main)
        if _gcd(specialized, _derivative_dense(specialized, budget), budget).degree() == 0:
            var univariate = factor(specialized, budget)
            if len(univariate.factors) == 1:
                _allocation[SparsePoly[QQ]](1, budget)
                return [f._copy(budget)]
            var height = _height(specialized, budget)
            if configurations == 0 or len(univariate.factors) < len(best_initial) or (len(univariate.factors) == len(best_initial) and _compare_q(height, best_height, budget) < 0):
                _allocation[DensePoly[QQ]](len(univariate.factors), budget)
                best_initial = List[DensePoly[QQ]]()
                for entry in univariate.factors:
                    budget.charge(1)
                    best_initial.append(_copy(entry[0], budget))
                best_point = assignment^
                best_specialized = specialized^
                best_height = height^
            configurations += 1
        _next_point(point, radius, budget)
    var shifted = _shift(f, parameters, best_point, False, False, budget)
    var lifted = _lift(shifted, main, best_initial, best_specialized, budget)
    var factors = _recombine_lifted(shifted, main, lifted, budget)
    for i in range(len(factors)):
        budget.charge(1)
        factors[i] = _shift(factors[i], parameters, best_point, True, False, budget)
    return factors^


def _squarefree_image(f: SparsePoly[QQ], main: Int64, mut budget: Budget) raises PolyError -> Bool:
    # A prime image f(x, a) mod p that keeps the degree in x and is coprime
    # to its derivative proves a primitive f squarefree: each factor of f has
    # positive degree in x and keeps it under the specialization.
    var integer = _integer_image(f, budget)
    var degree = Int(f.degree_in(main, budget))
    for trial in range(2):
        budget.charge(1)
        var p = prime(trial, budget)
        var field = _nmod._field(p)
        _allocation[UInt64](_sum(degree, 1), budget)
        var image = List[UInt64](length=degree + 1, fill=0)
        for term in integer.terms:
            budget.charge(1)
            var value = _residue(term.coefficient.value, p, budget)
            var k = 0
            for pair in term.monomial.pairs:
                budget.charge(1)
                if pair[0] == main:
                    k = Int(pair[1])
                else:
                    var point = (UInt64(pair[0]) * 0x9E3779B97F4A7C15 + UInt64(trial + 1) * 0xBF58476D1CE4E5B9) % p
                    value = _mod_mul(value, _mod_pow(point, UInt64(pair[1]), p, budget), p)
            image[k] = (image[k] + value) % p
        if image[degree] == 0:
            continue
        for i in range(len(image)):
            image[i] = _nmod._to(image[i], field)
        if len(_nmod._gcd(image, _nmod._derivative(image, field, budget), field, budget)) == 1:
            return True
    return False


def _univariate_image(f: SparsePoly[ZZ], variable: Int64, degree: Int, p: UInt64, trial: Int, field: _nmod._Field, mut budget: Budget) raises PolyError -> List[UInt64]:
    # f mod p with every variable but `variable` at seeded points, in
    # Montgomery residues of length degree + 1 (trailing zeros kept).
    _allocation[UInt64](_sum(degree, 1), budget)
    var image = List[UInt64](length=degree + 1, fill=0)
    for term in f.terms:
        budget.charge(1)
        var value = _residue(term.coefficient.value, p, budget)
        var k = 0
        for pair in term.monomial.pairs:
            budget.charge(1)
            if pair[0] == variable:
                k = Int(pair[1])
            else:
                var point = (UInt64(pair[0]) * 0x9E3779B97F4A7C15 + UInt64(trial + 1) * 0xBF58476D1CE4E5B9) % p
                value = _mod_mul(value, _mod_pow(point, UInt64(pair[1]), p, budget), p)
        image[k] = (image[k] + value) % p
    for i in range(len(image)):
        image[i] = _nmod._to(image[i], field)
    return image^


def _trivial_content(f: SparsePoly[QQ], main: Int64, mut budget: Budget) raises PolyError -> Bool:
    # The content c in the main variable is constant when, for every other
    # variable v, some prime image of the coefficients in v has gcd 1 while
    # one coefficient keeps its degree in v: lc_v(c) divides that
    # coefficient's leading coefficient, so c's image would keep its degree.
    var coefficients = _split(_integer_image(f, budget), main, budget)
    var nonzero = List[Int]()
    for i in range(len(coefficients)):
        budget.charge(1)
        if not coefficients[i].is_zero():
            nonzero.append(i)
    if len(nonzero) < 2:
        return False
    for v in f.variables(budget):
        budget.charge(1)
        if v == main:
            continue
        var proved = False
        for trial in range(2):
            budget.charge(1)
            var p = prime(trial, budget)
            var field = _nmod._field(p)
            var kept = False
            var common = List[UInt64]()
            for index in nonzero:
                budget.charge(1)
                ref g = coefficients[index]
                var degree = g.degree_in(v, budget)
                var image = _univariate_image(g, v, max(degree, 0), p, trial, field, budget)
                if image[len(image) - 1] != 0:
                    kept = True
                _nmod._trim(image)
                common = _nmod._gcd(common, image, field, budget)
                if len(common) == 1 and kept:
                    break
            if len(common) == 1 and kept:
                proved = True
                break
        if not proved:
            return False
    return True


def _atoms(f: SparsePoly[QQ], mut budget: Budget) raises PolyError -> List[SparsePoly[QQ]]:
    var variables = f.variables(budget)
    if len(variables) == 0:
        return List[SparsePoly[QQ]]()
    var main = variables[len(variables) - 1]
    if len(variables) == 1:
        var univariate = factor(DensePoly[QQ].from_sparse(f, budget, variable=main), budget)
        _allocation[SparsePoly[QQ]](len(univariate.factors), budget)
        var result = List[SparsePoly[QQ]]()
        for entry in univariate.factors:
            budget.charge(1)
            result.append(entry[0].to_sparse(f.order, budget))
        return result^
    # This recursion strictly removes the main variable (PG5).
    var result = List[SparsePoly[QQ]]()
    var primitive: SparsePoly[QQ]
    if _trivial_content(f, main, budget):
        primitive = f._copy(budget)
    else:
        var content = _content(f, main, budget)
        result = _atoms(content, budget)
        primitive = _exact_poly(f, content, budget)
    var squarefree: SparsePoly[QQ]
    if _squarefree_image(primitive, main, budget):
        squarefree = primitive._copy(budget)
    else:
        # The integer gcd takes the modular and heuristic paths; the rational
        # one would fall back to subresultant sequences.
        var integer = _integer_image(primitive, budget)
        var common = _gcd_value(integer, derivative(integer, main, budget), budget)
        var quotient = divide_exact(integer, common, budget)
        if not quotient:
            raise PolyError(PolyErrorKind.DOMAIN, "squarefree quotient is inexact")
        squarefree = _rational_image(quotient.take(), budget)
    _ = variables.pop()
    var wang = _wang_atoms(squarefree, main, variables, budget)
    if wang:
        for g in wang.value():
            budget.charge(1)
            _allocation[SparsePoly[QQ]](1, budget)
            result.append(_normalize(g.reorder(f.order, budget), budget))
        return result^
    var coefficients = _split(squarefree, main, budget)
    var degree = len(coefficients) - 1
    ref leading = coefficients[degree]
    _allocation[SparsePoly[QQ]](len(coefficients), budget)
    var transformed_coefficients = List[SparsePoly[QQ]]()
    for i in range(degree):
        budget.charge(1)
        transformed_coefficients.append(coefficients[i].mul(leading.pow(UInt64(degree - 1 - i), budget), budget))
    transformed_coefficients.append(_one(f, budget))
    var transformed = _join(transformed_coefficients, main, f, budget)
    var factors = _monic_factors(transformed, main, variables, budget)
    var replacement = leading.mul(SparsePoly[QQ].variable(main, f.order, NoContext(), budget), budget)
    for g in factors:
        budget.charge(1)
        var recovered = substitute(g, main, replacement, budget)
        recovered = _exact_poly(recovered, _content(recovered, main, budget), budget)
        _allocation[SparsePoly[QQ]](1, budget)
        result.append(_normalize(recovered, budget))
    return result^


def _wang_atoms(f: SparsePoly[QQ], main: Int64, params: List[Int64], mut budget: Budget) raises PolyError -> Optional[List[SparsePoly[QQ]]]:
    # Wang's EEZ algorithm over ZZ. The leading coefficient's irreducible
    # factors come from this same recursion, which removes the main variable.
    var integer = _primitive_zz(_integer_image(f, budget), budget)
    var lead = _lc(integer, main, budget)
    var lead_factors = List[_LeadFactor]()
    var remaining = lead._copy(budget)
    for atom in _atoms(_rational_image(lead, budget), budget):
        budget.charge(1)
        var t = _primitive_zz(_integer_image(atom, budget), budget)
        var power = 0
        while True:
            budget.charge(1)
            var quotient = divide_exact(remaining, t, budget)
            if not quotient:
                break
            remaining = quotient.take()
            power = _sum(power, 1)
        if power == 0:
            return None
        _allocation[_LeadFactor](1, budget)
        lead_factors.append(_LeadFactor(t^, power))
    if len(remaining.terms) != 1 or len(remaining.terms[0].monomial.pairs) != 0:
        return None
    var ct = remaining.terms[0].coefficient.value.copy()
    var factors = _wang(integer, main, params, lead_factors, ct, budget)
    if not factors:
        return None
    var result = List[SparsePoly[QQ]]()
    for g in factors.value():
        budget.charge(1)
        _allocation[SparsePoly[QQ]](1, budget)
        result.append(_rational_image(g, budget))
    return result^
