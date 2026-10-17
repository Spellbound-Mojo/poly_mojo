"""Subproduct trees over word prime fields: multipoint evaluation and interpolation.

Polynomials are `List[UInt64]` Montgomery residues as in `_nmod`, lowest
degree first and trimmed. Level 0 of a tree holds the monic linear factors
x - a_i; each higher level multiplies neighbouring pairs and carries an odd
last node up unchanged, so node j of level k covers points j*2^k up to
(j+1)*2^k. Long products use the transform products of `_ntt`, and
remainders by long nodes use a Newton inverse of the reversed divisor, so
both operations cost O(M(n) log n). Every step charges the shared budget in
proportion to its coefficient work, independent of timing.
"""
from .errors import Budget, PolyError, PolyErrorKind, _allocation, _charge_size, _product
from ._nmod import _Field, _dot, _mulm, _addm, _subm, _negm, _to, _invm, _mul, _schoolbook, _trim, _reversed, _slice, _sub, _add, _divmod_classic
from ._ntt import _modular_product

comptime _TRANSFORM = 384
"""Shorter operand length from which products use transforms instead of Karatsuba."""
comptime _NEWTON = 64
"""Divisor degree and quotient length from which remainders use a Newton inverse."""
comptime _LEAF_LEVEL = 5
"""Evaluation stops descending at nodes of 2^5 points and finishes by Horner's rule."""


def _redc_all(mut values: List[UInt64], f: _Field):
    # A transform product of Montgomery residues aR and bR is abR^2; one
    # reduction returns it to Montgomery form abR.
    for i in range(len(values)):
        values[i] = _mulm(values[i], 1, f)


def _mul_fast(a: List[UInt64], b: List[UInt64], f: _Field, mut budget: Budget) raises PolyError -> List[UInt64]:
    if len(a) == 0 or len(b) == 0:
        return List[UInt64]()
    if min(len(a), len(b)) < _TRANSFORM:
        return _mul(a, b, f, budget)
    var c = _modular_product(a, b, len(a) + len(b) - 1, f.p, False, budget)
    _redc_all(c, f)
    _trim(c)
    return c^


def _mullow_fast(a: List[UInt64], b: List[UInt64], limit: Int, f: _Field, mut budget: Budget) raises PolyError -> List[UInt64]:
    """The product's coefficients below `limit`, trimmed."""
    if limit <= 0:
        return List[UInt64]()
    var x = _slice(a, 0, limit, budget)
    var y = _slice(b, 0, limit, budget)
    if len(x) == 0 or len(y) == 0:
        return List[UInt64]()
    if min(len(x), len(y)) < 32:
        return _schoolbook(x, y, limit, f, budget)
    if min(len(x), len(y)) < _TRANSFORM:
        return _slice(_mul(x, y, f, budget), 0, limit, budget)
    var c = _modular_product(x, y, min(limit, len(x) + len(y) - 1), f.p, False, budget)
    _redc_all(c, f)
    _trim(c)
    return c^


def _inverse_series(b: List[UInt64], m: Int, f: _Field, mut budget: Budget) raises PolyError -> List[UInt64]:
    """The power series inverse of b, whose constant term is a unit, modulo x^m."""
    _allocation[UInt64](m, budget)
    var g = List[UInt64](capacity=m)
    g.append(_invm(b[0], f, budget))
    var k = 1
    while k < m:
        budget.charge(1)
        var k2 = min(2 * k, m)
        # b * g = 1 + x^k d + O(x^k2); the next coefficients are -g * d.
        var e = _mullow_fast(_slice(b, 0, min(len(b), k2), budget), g, k2, f, budget)
        var d = _slice(e, k, k2, budget) if len(e) > k else List[UInt64]()
        var t = _mullow_fast(g, d, k2 - k, f, budget)
        for i in range(k2 - k):
            g.append(_negm(t[i], f) if i < len(t) else UInt64(0))
        k = k2
    return g^


def _remainder(a: List[UInt64], b: List[UInt64], f: _Field, mut budget: Budget) raises PolyError -> List[UInt64]:
    """The remainder of a by the monic divisor b."""
    var n = len(b) - 1
    if len(a) <= n:
        return a.copy()
    var m = len(a) - n
    if n < _NEWTON or m < _NEWTON:
        return _divmod_classic(a, b, False, f, budget)[1].copy()
    # rev(q) = rev(a) * rev(b)^(-1) mod x^m, and r = a - q * b mod x^n.
    var ra = _reversed(a, len(a), budget)
    var rb = _reversed(b, len(b), budget)
    var inverse = _inverse_series(_slice(rb, 0, min(m, len(rb)), budget), m, f, budget)
    var rq = _mullow_fast(_slice(ra, 0, m, budget), inverse, m, f, budget)
    var q = _reversed(rq, m, budget)
    _trim(q)
    var qb = _mullow_fast(q, b, n, f, budget)
    var r = _sub(_slice(a, 0, n, budget), qb, f, budget)
    _trim(r)
    return r^


struct _Tree(Movable):
    """Levels of node products; level 0 holds x - a_i for Montgomery points a_i."""
    var levels: List[List[List[UInt64]]]
    var points: List[UInt64]

    def __init__(out self, var points: List[UInt64], f: _Field, mut budget: Budget) raises PolyError:
        self.points = points^
        self.levels = List[List[List[UInt64]]]()
        var count = len(self.points)
        _allocation[List[UInt64]](count, budget)
        var leaves = List[List[UInt64]](capacity=count)
        for a in self.points:
            budget.charge(1)
            leaves.append([_negm(a, f), f.one])
        self.levels.append(leaves^)
        while len(self.levels[len(self.levels) - 1]) > 1:
            ref below = self.levels[len(self.levels) - 1]
            var size = (len(below) + 1) // 2
            _allocation[List[UInt64]](size, budget)
            var level = List[List[UInt64]](capacity=size)
            for j in range(size):
                budget.charge(1)
                if 2 * j + 1 < len(below):
                    level.append(_mul_fast(below[2 * j], below[2 * j + 1], f, budget))
                else:
                    level.append(below[2 * j].copy())
            self.levels.append(level^)

    def root(self) -> List[UInt64]:
        return self.levels[len(self.levels) - 1][0].copy()


def _horner(r: List[UInt64], x: UInt64, f: _Field) -> UInt64:
    var value = UInt64(0)
    for i in range(len(r) - 1, -1, -1):
        value = _addm(_mulm(value, x, f), r[i], f)
    return value


def _middle(a: List[UInt64], node: List[UInt64], skip: Int, keep: Int, f: _Field, mut budget: Budget) raises PolyError -> List[UInt64]:
    """Coefficients skip ... skip + keep - 1 of rev(node) * a, zero-padded to length keep."""
    var product = _mullow_fast(_reversed(node, len(node), budget), a, skip + keep, f, budget)
    _allocation[UInt64](keep, budget)
    var result = List[UInt64](length=keep, fill=0)
    for k in range(keep):
        if skip + k < len(product):
            result[k] = product[skip + k]
    return result^


def _evaluate(tree: _Tree, poly: List[UInt64], f: _Field, mut budget: Budget) raises PolyError -> List[UInt64]:
    """Values at every tree point by a scaled remainder tree, down to blocks of 2^_LEAF_LEVEL points.

    A node v of degree d keeps A_v, the first d coefficients in 1/x of
    (poly mod M_v) / M_v. A child u with sibling w of degree e has
    A_u[k] = sum_i M_w[i] A_v[k + i], a middle product, so each node costs one
    product and no division. At a block, poly mod M_v = M_v * A_v truncated.
    """
    var count = len(tree.points)
    var top = len(tree.levels) - 1
    var stop = min(_LEAF_LEVEL, top)
    var root = tree.root()
    var n = len(root) - 1
    var reduced = _remainder(poly, root, f, budget) if len(poly) > n else poly.copy()
    _allocation[UInt64](count, budget)
    var values = List[UInt64](capacity=count)
    if top <= stop:
        _charge_size(_product(count, len(reduced) + 1), budget)
        for i in range(count):
            values.append(_horner(reduced, tree.points[i], f))
        return values^
    # With t = 1/x, poly / M_root = t * rev(poly) / rev(M_root), as series in t.
    var inverse = _inverse_series(_slice(_reversed(root, n + 1, budget), 0, n, budget), n, f, budget)
    var first = _mullow_fast(_reversed(reduced, n, budget), inverse, n, f, budget)
    first.resize(n, 0)
    var current: List[List[UInt64]] = [first^]
    var level = top
    while level > stop:
        level -= 1
        ref nodes = tree.levels[level]
        _allocation[List[UInt64]](len(nodes), budget)
        var next = List[List[UInt64]](capacity=len(nodes))
        for j in range(len(current)):
            budget.charge(1)
            if 2 * j + 1 < len(nodes):
                var left = len(nodes[2 * j]) - 1
                var right = len(nodes[2 * j + 1]) - 1
                next.append(_middle(current[j], nodes[2 * j + 1], right, left, f, budget))
                next.append(_middle(current[j], nodes[2 * j], left, right, f, budget))
            else:
                next.append(current[j].copy())
        current = next^
    ref blocks = tree.levels[stop]
    var size = 1 << stop
    for j in range(len(current)):
        ref m = blocks[j]
        ref a = current[j]
        var d = len(m) - 1
        var end = min(count, (j + 1) * size)
        _charge_size(_product(d + end - j * size, d + 1), budget)
        # remainder[k] = sum over i of M[k + 1 + i] * A[i].
        var remainder = List[UInt64](capacity=d)
        for k in range(d):
            remainder.append(_dot(m.unsafe_ptr().unsafe_offset(k + 1), a.unsafe_ptr(), d - k, f))
        for i in range(j * size, end):
            values.append(_horner(remainder, tree.points[i], f))
    return values^


def _derivative(a: List[UInt64], f: _Field, mut budget: Budget) raises PolyError -> List[UInt64]:
    _allocation[UInt64](max(0, len(a) - 1), budget)
    var result = List[UInt64](capacity=max(0, len(a) - 1))
    var k = UInt64(0)
    for i in range(1, len(a)):
        k = _addm(k, f.one, f)
        result.append(_mulm(a[i], k, f))
    _trim(result)
    return result^


def _interpolate(tree: _Tree, values: List[UInt64], f: _Field, mut budget: Budget) raises PolyError -> List[UInt64]:
    """The polynomial of degree below the point count through (a_i, values[i]); DOMAIN for repeated points."""
    var count = len(tree.points)
    var weights = _evaluate(tree, _derivative(tree.root(), f, budget), f, budget)
    # One inversion for all weights: prefix products, then unwinding.
    _allocation[UInt64](count, budget)
    var prefix = List[UInt64](capacity=count)
    var running = f.one
    for i in range(count):
        if weights[i] == 0:
            raise PolyError(PolyErrorKind.DOMAIN, "interpolation nodes must be distinct")
        prefix.append(running)
        running = _mulm(running, weights[i], f)
    var inverse = _invm(running, f, budget)
    _allocation[List[UInt64]](count, budget)
    var parts = List[List[UInt64]](capacity=count)
    for _ in range(count):
        parts.append(List[UInt64]())
    for i in range(count - 1, -1, -1):
        budget.charge(1)
        var w = _mulm(inverse, prefix[i], f)
        inverse = _mulm(inverse, weights[i], f)
        var c = _mulm(values[i], w, f)
        if c:
            parts[i].append(c)
    for level in range(len(tree.levels) - 1):
        ref nodes = tree.levels[level]
        var size = (len(nodes) + 1) // 2
        _allocation[List[UInt64]](size, budget)
        var next = List[List[UInt64]](capacity=size)
        for j in range(size):
            budget.charge(1)
            if 2 * j + 1 < len(nodes):
                var left = _mul_fast(parts[2 * j], nodes[2 * j + 1], f, budget)
                var right = _mul_fast(parts[2 * j + 1], nodes[2 * j], f, budget)
                next.append(_add(left, right, f, budget))
            else:
                next.append(parts[2 * j].copy())
        parts = next^
    var result = parts[0].copy()
    _trim(result)
    return result^


def _compose_series(f: List[UInt64], g: List[UInt64], n: Int, field: _Field, mut budget: Budget) raises PolyError -> List[UInt64]:
    """f(g) modulo x^n by Brent and Kung's baby steps and giant steps, trimmed.

    With k about sqrt(len(f)), f splits into blocks F_j of k coefficients, so
    f(g) = sum_j F_j(g) (g^k)^j. The baby steps g^0 ... g^(k-1) form the columns
    of one matrix product that yields every F_j(g); the giant step is Horner's
    rule in g^k. When g(0) = 0, the block F_j(g) is needed only below x^(n - jk).
    """
    if len(f) == 0 or n <= 0:
        return List[UInt64]()
    var k = 1
    while k * k < len(f):
        k += 1
    var blocks = (len(f) + k - 1) // k
    var valuation = len(g) == 0 or g[0] == 0
    _allocation[List[UInt64]](k + 1, budget)
    var powers = List[List[UInt64]](capacity=k + 1)
    powers.append([field.one])
    for i in range(1, k + 1):
        powers.append(_mullow_fast(powers[i - 1], g, n, field, budget))
    # columns[t * k + i] = coefficient t of g^i, so each output coefficient is one dot product.
    _allocation[UInt64](_product(n, k), budget)
    var columns = List[UInt64](length=n * k, fill=0)
    for i in range(k):
        for t in range(len(powers[i])):
            columns[t * k + i] = powers[i][t]
    var coefficients = _slice(f, 0, len(f), budget)
    coefficients.resize(blocks * k, 0)
    var pf = coefficients.unsafe_ptr()
    var pc = columns.unsafe_ptr()
    var result = List[UInt64]()
    for j in range(blocks - 1, -1, -1):
        var limit = max(0, n - j * k) if valuation else n
        _charge_size(_product(limit, k) + 1, budget)
        var row = List[UInt64](capacity=limit)
        for t in range(limit):
            row.append(_dot(pf.unsafe_offset(j * k), pc.unsafe_offset(t * k), k, field))
        _trim(row)
        if len(result):
            result = _add(_mullow_fast(result, powers[k], limit, field, budget), row, field, budget)
        else:
            result = row^
    _trim(result)
    return result^
