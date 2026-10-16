"""Deterministic Buchberger bases with Gebauer–Möller pair installation.

Pair installation follows SymPy groebnertools.py _buchberger.update.
Set iteration is replaced by stable indices; cofactor propagation is added.

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
from .coefficients import CoefficientField, ModInt, QQ
from ._product_stream import _subtract_column
from .errors import Budget, PolyError, PolyErrorKind, _allocation, _charge_size, _sum
from .monomial import Monomial, MonomialOrder
from .sparse import SparsePoly, Term
from .division import _divide_prepared, _ReducerData, divide_by_list
from .certificates import ListDivision, MembershipCertificate
from ._sparse_ops import _subtract_multiples
from ._packed_groebner import _packed_groebner, _packed_groebner_rational, _packed_supported
from ._f4 import _f4_groebner, _f4_supported
from ._rational_groebner import _grevlex_groebner_rational, _grevlex_supported


@fieldwise_init
struct GroebnerBasis[C: CoefficientField](Copyable, Movable, Writable):
    """A reduced monic basis and optional combinations of its input generators.

    Parameters:
        C: The coefficient field.
    """
    var order: MonomialOrder
    """The admissible monomial order used by the basis."""
    var basis: List[SparsePoly[Self.C]]
    """The reduced basis in decreasing leading-monomial order."""
    var cofactors: Optional[List[List[SparsePoly[Self.C]]]]
    """One row per basis element, with columns in input generator order."""


@fieldwise_init
struct _Pair(Movable):
    var first: Int
    var second: Int
    var lcm: Monomial


def _monomial_equal(a: Monomial, b: Monomial, mut budget: Budget) raises PolyError -> Bool:
    _charge_size(_sum(len(a.pairs), len(b.pairs)), budget)
    return a == b


def _sort_indices(mut indices: List[Int], leads: List[Monomial], order: MonomialOrder, mut budget: Budget) raises PolyError:
    for i in range(1, len(indices)):
        budget.charge(1)
        var value = indices[i]
        var j = i
        while j > 0 and order._compare(leads[value], leads[indices[j - 1]], budget) < 0:
            indices[j] = indices[j - 1]
            j -= 1
        indices[j] = value


def _install(leads: List[Monomial], index: Int, mut active: List[Int], mut pairs: List[_Pair], mut budget: Budget) raises PolyError:
    # Gebauer–Möller installation, Becker–Weispfenning p.230 / SymPy update.
    # Stable active order replaces unordered sets. Keep product pairs during
    # divisibility filtering; discard them only after they remove redundant
    # new pairs. Old pairs survive when either replacement has the same LCM.
    ref mh = leads[index]
    _allocation[Monomial](len(active), budget)
    var lcms = List[Monomial](capacity=len(active))
    for old in active:
        budget.charge(1)
        lcms.append(mh.lcm(leads[old], budget))
    _allocation[Int](len(active), budget)
    var kept = List[Int](capacity=len(active))
    for i in range(len(active)):
        budget.charge(1)
        var product = _monomial_equal(mh.mul(leads[active[i]], budget), lcms[i], budget)
        var redundant = False
        if not product:
            for j in range(i + 1, len(active)):
                budget.charge(1)
                if lcms[j].divides(lcms[i], budget):
                    redundant = True
                    break
            if not redundant:
                for j in kept:
                    budget.charge(1)
                    if lcms[j].divides(lcms[i], budget):
                        redundant = True
                        break
        if not redundant:
            kept.append(i)
    _allocation[_Pair](_sum(len(pairs), len(kept)), budget)
    var next_pairs = List[_Pair](capacity=_sum(len(pairs), len(kept)))
    for i in range(len(pairs)):
        budget.charge(1)
        ref pair = pairs[i]
        if not mh.divides(pair.lcm, budget) or _monomial_equal(mh.lcm(leads[pair.first], budget), pair.lcm, budget) or _monomial_equal(mh.lcm(leads[pair.second], budget), pair.lcm, budget):
            var moved = _Pair(0, 0, Monomial())
            swap(moved, pairs[i])
            next_pairs.append(moved^)
    for i in kept:
        budget.charge(1)
        if not _monomial_equal(mh.mul(leads[active[i]], budget), lcms[i], budget):
            var lcm = Monomial()
            swap(lcm, lcms[i])
            next_pairs.append(_Pair(min(index, active[i]), max(index, active[i]), lcm^))
    pairs = next_pairs^
    _allocation[Int](_sum(len(active), 1), budget)
    var next_active = List[Int](capacity=_sum(len(active), 1))
    for old in active:
        budget.charge(1)
        if not mh.divides(leads[old], budget):
            next_active.append(old)
    next_active.append(index)
    active = next_active^


def _pair_before(a: _Pair, b: _Pair, order: MonomialOrder, mut budget: Budget) raises PolyError -> Bool:
    var comparison = order._compare(a.lcm, b.lcm, budget)
    return comparison < 0 or (comparison == 0 and (a.first < b.first or (a.first == b.first and a.second < b.second)))


def _sift_pairs(mut pairs: List[_Pair], start: Int, order: MonomialOrder, mut budget: Budget) raises PolyError:
    var value = _Pair(0, 0, Monomial())
    swap(value, pairs[start])
    var position = start
    while position < len(pairs) // 2:
        budget.charge(1)
        var child = position * 2 + 1
        if child + 1 < len(pairs) and _pair_before(pairs[child + 1], pairs[child], order, budget):
            child += 1
        if not _pair_before(pairs[child], value, order, budget):
            break
        var moved = _Pair(0, 0, Monomial())
        swap(moved, pairs[child])
        swap(moved, pairs[position])
        position = child
    swap(value, pairs[position])


def _heapify_pairs(mut pairs: List[_Pair], order: MonomialOrder, mut budget: Budget) raises PolyError:
    for i in range(len(pairs) // 2 - 1, -1, -1):
        budget.charge(1)
        _sift_pairs(pairs, i, order, budget)


def _select(mut pairs: List[_Pair], order: MonomialOrder, mut budget: Budget) raises PolyError -> _Pair:
    var selected = pairs.pop()
    if len(pairs):
        swap(selected, pairs[0])
        _sift_pairs(pairs, 0, order, budget)
    return selected^


def _zero_row[C: CoefficientField](p: SparsePoly[C], size: Int, mut budget: Budget) raises PolyError -> List[SparsePoly[C]]:
    _allocation[SparsePoly[C]](size, budget)
    var row = List[SparsePoly[C]](capacity=size)
    for _ in range(size):
        budget.charge(1)
        row.append(SparsePoly[C].zero(p.order, p.ring, budget))
    return row^


def _reduce_row[C: CoefficientField](mut row: List[SparsePoly[C]], quotients: List[SparsePoly[C]], indices: List[Int], rows: List[List[SparsePoly[C]]], mut budget: Budget) raises PolyError:
    var terms = 0
    for quotient in quotients:
        budget.charge(1)
        terms = _sum(terms, len(quotient.terms))
    if terms >= 512:
        for k in range(len(row)):
            row[k] = _subtract_column(row[k], quotients, indices, rows, k, budget)
        return
    for j in range(len(indices)):
        budget.charge(1)
        if quotients[j].is_zero():
            continue
        for k in range(len(row)):
            budget.charge(1)
            if not rows[indices[j]][k].is_zero():
                row[k] = row[k].sub(quotients[j].mul(rows[indices[j]][k], budget), budget)


def _normalize[C: CoefficientField](mut p: SparsePoly[C], mut row: List[SparsePoly[C]], mut budget: Budget) raises PolyError:
    var inverse = p.terms[len(p.terms) - 1].coefficient.inverse(budget)
    p = p.scale(inverse, budget)
    for i in range(len(row)):
        budget.charge(1)
        row[i] = row[i].scale(inverse, budget)


def _insert[C: CoefficientField](var p: SparsePoly[C], var row: List[SparsePoly[C]], mut arena: List[SparsePoly[C]], mut rows: List[List[SparsePoly[C]]], mut data: _ReducerData[C], mut active: List[Int], mut pairs: List[_Pair], mut budget: Budget) raises PolyError:
    _normalize(p, row, budget)
    _allocation[SparsePoly[C]](1, budget)
    data.append(p, budget)
    arena.append(p^)
    if len(row):
        _allocation[List[SparsePoly[C]]](1, budget)
        rows.append(row^)
    _install(data.leads, len(arena) - 1, active, pairs, budget)
    _heapify_pairs(pairs, arena[len(arena) - 1].order, budget)


def groebner[C: CoefficientField](generators: List[SparsePoly[C]], order: MonomialOrder, mut budget: Budget, track_cofactors: Bool = False) raises PolyError -> GroebnerBasis[C]:
    """Compute the reduced monic basis with deterministic Gebauer–Möller pruning.

    Parameters:
        C: The coefficient field.

    Args:
        generators: Polynomials in one field; zero generators are allowed.
        order: LEX, GRLEX, or GREVLEX with every input variable listed.
        budget: The shared work allowance.
        track_cofactors: Whether to retain combinations of the original generators.

    Returns:
        The reduced basis and optional cofactor rows in generator order.

    Raises:
        PolyError: DOMAIN for KERNEL order, mixed fields or malformed input, LIMIT or CAPACITY on work limits.
    """
    if order.kind == MonomialOrder.KERNEL:
        raise PolyError(PolyErrorKind.DOMAIN, "Groebner bases require a monomial order")
    order.validate(Monomial(), budget)
    if not track_cofactors and _packed_supported(order):
        # The same result on packed exponent vectors: F4 over small prime
        # fields under degree orders, Buchberger's algorithm otherwise.
        for i in range(len(generators)):
            budget.charge(1)
            generators[i].check_invariants(budget)
            if generators[i].ring != generators[0].ring:
                raise PolyError(PolyErrorKind.DOMAIN, "Groebner generators in different fields")
        comptime if C == QQ:
            # Over QQ under GREVLEX, the homogenized computation (exact, or by
            # certified reconstruction when coefficients grow); otherwise the
            # packed engine fraction-free on integer coefficients.
            ref inputs = rebind[List[SparsePoly[QQ]]](generators)
            if _grevlex_supported(order):
                var homogenized = _grevlex_groebner_rational(inputs, order, budget)
                return GroebnerBasis[C](order.copy(), rebind_var[List[SparsePoly[C]]](homogenized^), Optional[List[List[SparsePoly[C]]]](None))
            var rational = _packed_groebner_rational(inputs, order, budget)
            return GroebnerBasis[C](order.copy(), rebind_var[List[SparsePoly[C]]](rational^), Optional[List[List[SparsePoly[C]]]](None))
        elif C == ModInt:
            ref modular = rebind[List[SparsePoly[ModInt]]](generators)
            if len(modular) and _f4_supported(order, modular[0].ring.value):
                var f4 = _f4_groebner(modular, order, budget)
                return GroebnerBasis[C](order.copy(), rebind_var[List[SparsePoly[C]]](f4^), Optional[List[List[SparsePoly[C]]]](None))
            return GroebnerBasis[C](order.copy(), _packed_groebner(generators, order, budget), Optional[List[List[SparsePoly[C]]]](None))
        else:
            return GroebnerBasis[C](order.copy(), _packed_groebner(generators, order, budget), Optional[List[List[SparsePoly[C]]]](None))
    var arena = List[SparsePoly[C]]()
    var rows = List[List[SparsePoly[C]]]()
    var data = _ReducerData[C]()
    var active = List[Int]()
    var pairs = List[_Pair]()
    for i in range(len(generators)):
        budget.charge(1)
        generators[i].check_invariants(budget)
        if generators[i].ring != generators[0].ring:
            raise PolyError(PolyErrorKind.DOMAIN, "Groebner generators in different fields")
        var p = generators[i].reorder(order, budget)
        var row = List[SparsePoly[C]]()
        if track_cofactors:
            row = _zero_row(p, len(generators), budget)
            row[i] = SparsePoly[C].constant(C.one(p.ring), order, budget)
        var reduced = _divide_prepared(p, arena, active, track_cofactors, data, budget)
        if reduced.remainder.is_zero():
            continue
        if track_cofactors:
            _reduce_row(row, reduced.quotients, active, rows, budget)
        swap(p, reduced.remainder)
        _insert(p^, row^, arena, rows, data, active, pairs, budget)
    var dirty_order = True
    while len(pairs):
        budget.charge(1)
        var pair = _select(pairs, order, budget)
        var left = Term[C](pair.lcm.div(data.leads[pair.first], budget), C.one(arena[pair.first].ring))
        var right = Term[C](pair.lcm.div(data.leads[pair.second], budget), C.one(arena[pair.second].ring))
        var s = _subtract_multiples(arena[pair.first], left, arena[pair.second], right, budget)
        if dirty_order:
            _sort_indices(active, data.leads, order, budget)
            dirty_order = False
        var reduced = _divide_prepared(s, arena, active, track_cofactors, data, budget)
        if reduced.remainder.is_zero():
            continue
        var row = List[SparsePoly[C]]()
        if track_cofactors:
            row = _zero_row(s, len(generators), budget)
            for k in range(len(generators)):
                budget.charge(1)
                row[k] = _subtract_multiples(rows[pair.first][k], left, rows[pair.second][k], right, budget)
            _reduce_row(row, reduced.quotients, active, rows, budget)
        swap(s, reduced.remainder)
        _insert(s^, row^, arena, rows, data, active, pairs, budget)
        dirty_order = True
    _sort_indices(active, data.leads, order, budget)
    _allocation[SparsePoly[C]](len(active), budget)
    var basis = List[SparsePoly[C]](capacity=len(active))
    _allocation[List[SparsePoly[C]]](len(active) if track_cofactors else 0, budget)
    var cofactors = List[List[SparsePoly[C]]]()
    # Active leading monomials are mutually nondividing after installation.
    # Reducing each tail against all the others therefore preserves every
    # leading term, including the equal-leading-monomial regression case.
    for position in range(len(active) - 1, -1, -1):
        budget.charge(1)
        var index = active[position]
        _allocation[Int](len(active) - 1, budget)
        var others = List[Int](capacity=len(active) - 1)
        for j in active:
            budget.charge(1)
            if j != index:
                others.append(j)
        var reduced = _divide_prepared(arena[index], arena, others, track_cofactors, data, budget)
        var row = List[SparsePoly[C]]()
        if track_cofactors:
            row = _zero_row(arena[index], len(generators), budget)
            for k in range(len(generators)):
                budget.charge(1)
                row[k] = rows[index][k]._copy(budget)
            _reduce_row(row, reduced.quotients, others, rows, budget)
        var p = SparsePoly[C].zero(order, arena[index].ring, budget)
        swap(p, reduced.remainder)
        _normalize(p, row, budget)
        basis.append(p^)
        if track_cofactors:
            cofactors.append(row^)
    _charge_size(len(order.variables), budget)
    var evidence = Optional[List[List[SparsePoly[C]]]](None)
    if track_cofactors:
        evidence = cofactors^
    return GroebnerBasis[C](order.copy(), basis^, evidence^)


def reduce[C: CoefficientField](f: SparsePoly[C], basis: GroebnerBasis[C], mut budget: Budget) raises PolyError -> ListDivision[C]:
    """Reduce a polynomial by a Gröbner basis in its chosen monomial order.

    Parameters:
        C: The coefficient field.

    Args:
        f: The polynomial to reduce.
        basis: The basis and its monomial order.
        budget: The shared work allowance.

    Returns:
        Quotients in basis order and the unique normal form.

    Raises:
        PolyError: DOMAIN for incompatible fields or invalid orders, LIMIT or CAPACITY on work limits.
    """
    return divide_by_list(f.reorder(basis.order, budget), basis.basis, budget)


def membership[C: CoefficientField](f: SparsePoly[C], generators: List[SparsePoly[C]], order: MonomialOrder, mut budget: Budget) raises PolyError -> Optional[MembershipCertificate[C]]:
    """Find a certificate expressing f as a combination of the given generators.

    Parameters:
        C: The coefficient field.

    Args:
        f: The proposed ideal member.
        generators: The ordered original generators.
        order: The admissible monomial order used for the computation.
        budget: The shared work allowance.

    Returns:
        Cofactors in generator order when f belongs to the ideal, otherwise None.

    Raises:
        PolyError: DOMAIN for mixed fields or invalid orders, LIMIT or CAPACITY on work limits.
    """
    f.check_invariants(budget)
    if len(generators) and f.ring != generators[0].ring:
        raise PolyError(PolyErrorKind.DOMAIN, "ideal member and generators in different fields")
    var basis = groebner(generators, order, budget, track_cofactors=True)
    var division = reduce(f, basis, budget)
    if not division.remainder.is_zero():
        return None
    var row = _zero_row(division.remainder, len(generators), budget)
    for j in range(len(basis.basis)):
        budget.charge(1)
        if division.quotients[j].is_zero():
            continue
        for k in range(len(generators)):
            budget.charge(1)
            row[k] = row[k].add(division.quotients[j].mul(basis.cofactors.value()[j][k], budget), budget)
    return MembershipCertificate[C](row^)
