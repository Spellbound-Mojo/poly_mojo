"""Brown's dense modular gcd for multivariate integer polynomials.

Modulo each prime the inputs are dense word arrays over their exponent
boxes, the last variable outermost. One level of the recursion removes the
contents in that variable y, takes gamma = gcd of the inputs' leading
coefficients (LEX over the other variables) in Z_p[y], specializes y at
points where neither leading coefficient vanishes, recurses, and keeps the
images whose leading monomial is smallest (larger ones come from unlucky
points). Images scaled by gamma(point) are interpolated in y from
deg(gamma) + d + 1 points, where d bounds deg_y of the gcd by one univariate
image in y with the other variables specialized. The primitive part of the
interpolant times the content gcd is the image gcd, made monic in LEX.

Over ZZ the images, scaled by the gcd of the inputs' LEX leading integer
coefficients, are combined by symmetric CRT until a prime changes nothing;
the primitive candidate is accepted only when divide_exact shows that it
divides both inputs. Anything unexpected returns None, and the caller uses
another algorithm.
"""
from apn_mojo import Integer
from .errors import Budget, PolyError, _allocation, _charge_size, _sum, _product
from .coefficients import ZZ, NoContext
from .sparse import SparsePoly, Term
from .monomial import Monomial
from .division import divide_exact
from .primes import prime, _residue
from ._coefficient_ops import _gcd_coefficient, _exact
from ._nmod_euclid import _Field, _gcd_words, _trim_words
from ._univariate_modular import _Reconstruction

# Exponent boxes above this many cells, or more primes than this, give up.
comptime _CELLS = 1 << 22
comptime _PRIMES = 64


struct _Grid(Copyable, Movable):
    """A dense array; extents are outermost first, the first variable innermost."""
    var data: List[UInt64]
    var extents: List[Int]

    def __init__(out self, var data: List[UInt64], var extents: List[Int]):
        self.data = data^
        self.extents = extents^


def _size(extents: List[Int], start: Int) -> Int:
    var size = 1
    for i in range(start, len(extents)):
        size *= extents[i]
    return size


def _decode(index: Int, extents: List[Int]) -> List[Int]:
    """Exponents of a cell, innermost (first) variable first."""
    var out = List[Int](capacity=len(extents))
    var rest = index
    for axis in range(len(extents) - 1, -1, -1):
        out.append(rest % extents[axis])
        rest //= extents[axis]
    return out^


def _encode(exponents: List[Int], extents: List[Int]) -> Int:
    """The cell of exponents (first variable first), or -1 outside the box."""
    var index = 0
    var n = len(extents)
    for axis in range(n):
        var e = exponents[n - 1 - axis]
        if e >= extents[axis]:
            return -1
        index = index * extents[axis] + e
    return index


def _less(a: List[Int], b: List[Int]) -> Bool:
    """LEX comparison with the first variable most significant."""
    for i in range(len(a)):
        if a[i] != b[i]:
            return a[i] < b[i]
    return False


def _vector(g: _Grid, t: Int) -> List[UInt64]:
    """The coefficients in the outermost variable at inner cell t."""
    var block = _size(g.extents, 1)
    var out = List[UInt64](capacity=g.extents[0])
    for j in range(g.extents[0]):
        out.append(g.data[j * block + t])
    _trim_words(out)
    return out^


def _evaluate(a: List[UInt64], x: UInt64, field: _Field) -> UInt64:
    var value = UInt64(0)
    for i in range(len(a) - 1, -1, -1):
        value = field.add(field.mul(value, x), a[i])
    return value


def _product_words(a: List[UInt64], b: List[UInt64], field: _Field) -> List[UInt64]:
    if not len(a) or not len(b):
        return List[UInt64]()
    var out = List[UInt64](length=len(a) + len(b) - 1, fill=0)
    for i in range(len(a)):
        for j in range(len(b)):
            out[i + j] = field.add(out[i + j], field.mul(a[i], b[j]))
    return out^


def _quotient_words(a: List[UInt64], b: List[UInt64], field: _Field) raises PolyError -> List[UInt64]:
    """a / b for b dividing a."""
    var r = a.copy()
    _trim_words(r)
    var db = len(b) - 1
    if len(r) <= db:
        return List[UInt64]()
    var inverse = field.inverse(b[db])
    var q = List[UInt64](length=len(r) - db, fill=0)
    for k in range(len(r) - 1, db - 1, -1):
        var c = field.mul(r[k], inverse)
        q[k - db] = c
        if c == 0:
            continue
        for i in range(db + 1):
            r[k - db + i] = field.sub(r[k - db + i], field.mul(c, b[i]))
    return q^


def _content(g: _Grid, field: _Field, mut budget: Budget) raises PolyError -> List[UInt64]:
    var block = _size(g.extents, 1)
    var c = List[UInt64]()
    for t in range(block):
        budget.charge(1)
        var v = _vector(g, t)
        if not len(v):
            continue
        c = _gcd_words(c^, v^, field, budget)
        if len(c) == 1:
            break
    return c^


def _divide_vectors(g: _Grid, c: List[UInt64], field: _Field, mut budget: Budget) raises PolyError -> _Grid:
    if len(c) <= 1:
        return g.copy()
    var block = _size(g.extents, 1)
    var outer = g.extents[0] - (len(c) - 1)
    _allocation[UInt64](outer * block, budget)
    var data = List[UInt64](length=outer * block, fill=0)
    for t in range(block):
        budget.charge(1)
        var q = _quotient_words(_vector(g, t), c, field)
        for j in range(len(q)):
            data[j * block + t] = q[j]
    var extents = g.extents.copy()
    extents[0] = outer
    return _Grid(data^, extents^)


def _inner_lead(g: _Grid) -> Int:
    """The inner cell of the LEX-largest nonzero coefficient vector."""
    var block = _size(g.extents, 1)
    var inner = List[Int]()
    for i in range(1, len(g.extents)):
        inner.append(g.extents[i])
    var best = -1
    var best_exponents = List[Int]()
    for t in range(block):
        var nonzero = False
        for j in range(g.extents[0]):
            if g.data[j * block + t] != 0:
                nonzero = True
                break
        if not nonzero:
            continue
        var e = _decode(t, inner)
        if best < 0 or _less(best_exponents, e):
            best = t
            best_exponents = e^
    return best


def _lead(g: _Grid) -> List[Int]:
    """Exponents of the LEX-leading cell, first variable first."""
    var best = List[Int]()
    var found = False
    for index in range(len(g.data)):
        if g.data[index] == 0:
            continue
        var e = _decode(index, g.extents)
        if not found or _less(best, e):
            best = e^
            found = True
    return best^


def _horner(g: _Grid, x: UInt64, field: _Field, mut budget: Budget) raises PolyError -> _Grid:
    """Specialize the outermost variable."""
    var block = _size(g.extents, 1)
    _charge_size(len(g.data), budget)
    _allocation[UInt64](block, budget)
    var out = List[UInt64](capacity=block)
    var top = (g.extents[0] - 1) * block
    for i in range(block):
        out.append(g.data[top + i])
    var source = g.data.unsafe_ptr()
    var target = out.unsafe_ptr()
    for k in range(g.extents[0] - 2, -1, -1):
        var row = source.unsafe_offset(k * block)
        for i in range(block):
            var cell = target.unsafe_offset(i)
            cell.unsafe_store(field.add(field.mul(cell.unsafe_load(), x), row.unsafe_offset(i).unsafe_load()))
    var extents = List[Int]()
    for i in range(1, len(g.extents)):
        extents.append(g.extents[i])
    return _Grid(out^, extents^)


def _outer_degree(g: _Grid) -> Int:
    var block = _size(g.extents, 1)
    for j in range(g.extents[0] - 1, -1, -1):
        for t in range(block):
            if g.data[j * block + t] != 0:
                return j
    return -1


def _outer_image(g: _Grid, attempt: Int, field: _Field, mut budget: Budget) raises PolyError -> List[UInt64]:
    """The univariate polynomial in the outermost variable with the others specialized.

    The inner axes collapse innermost first by Horner over contiguous runs, so
    the cost is one pass over the cells and no cell is decoded.
    """
    _charge_size(len(g.data), budget)
    var data = g.data.copy()
    for axis in range(len(g.extents) - 1, 0, -1):
        var extent = g.extents[axis]
        var point = field.enter(UInt64(3 + axis + attempt * len(g.extents)))
        var groups = len(data) // extent
        var out = List[UInt64](capacity=groups)
        for i in range(groups):
            var base = i * extent
            var value = UInt64(0)
            for k in range(extent - 1, -1, -1):
                value = field.add(field.mul(value, point), data[base + k])
            out.append(value)
        data = out^
    return data^


def _brown(a: _Grid, b: _Grid, field: _Field, mut budget: Budget) raises PolyError -> Optional[_Grid]:
    """The LEX-monic gcd of two nonzero grids over the same variables, or None."""
    budget.charge(1)
    if len(a.extents) == 1:
        var g = _gcd_words(a.data.copy(), b.data.copy(), field, budget)
        var n = len(g)
        return _Grid(g^, [n])
    var content_a = _content(a, field, budget)
    var content_b = _content(b, field, budget)
    var common = _gcd_words(content_a.copy(), content_b.copy(), field, budget)
    var pa = _divide_vectors(a, content_a, field, budget)
    var pb = _divide_vectors(b, content_b, field, budget)
    var lc_a = _vector(pa, _inner_lead(pa))
    var lc_b = _vector(pb, _inner_lead(pb))
    var gamma = _gcd_words(lc_a.copy(), lc_b.copy(), field, budget)
    # Bound deg_y gcd(pa, pb) by one image in y, or by the smaller degree.
    var da = _outer_degree(pa)
    var db = _outer_degree(pb)
    var bound = min(da, db)
    for attempt in range(3):
        var ia = _outer_image(pa, attempt, field, budget)
        var ib = _outer_image(pb, attempt, field, budget)
        if ia[da] != 0 and ib[db] != 0:
            bound = len(_gcd_words(ia^, ib^, field, budget)) - 1
            break
    var need = bound + len(gamma)
    var n = len(a.extents)
    var inner = List[Int]()
    for i in range(1, n):
        inner.append(min(pa.extents[i], pb.extents[i]))
    var block = _size(inner, 0)
    _allocation[UInt64](_product(need, block), budget)
    var values = List[UInt64](length=need * block, fill=0)
    var points = List[UInt64](length=need, fill=0)
    var best = List[Int]()
    var count = 0
    var x = 0
    while count < need:
        budget.charge(1)
        x += 1
        if UInt64(x) >= field.p or x > 4 * need + 32:
            return None
        var point = field.enter(UInt64(x))
        if _evaluate(lc_a, point, field) == 0 or _evaluate(lc_b, point, field) == 0:
            continue
        var image = _brown(_horner(pa, point, field, budget), _horner(pb, point, field, budget), field, budget)
        if not image:
            return None
        ref g = image.value()
        var lead = _lead(g)
        if count == 0 or _less(lead, best):
            best = lead^
            count = 0
        elif _less(best, lead):
            continue
        var scale = _evaluate(gamma, point, field)
        var base = count * block
        for t in range(block):
            values[base + t] = 0
        for index in range(len(g.data)):
            if g.data[index] == 0:
                continue
            var cell = _encode(_decode(index, g.extents), inner)
            if cell < 0:
                return None
            values[base + cell] = field.mul(g.data[index], scale)
        points[count] = point
        count += 1
    # Newton divided differences and expansion, all inner cells at once.
    _charge_size(_product(_product(need, need), block), budget)
    for j in range(1, need):
        for i in range(need - 1, j - 1, -1):
            var inverse = field.inverse(field.sub(points[i], points[i - j]))
            for t in range(block):
                values[i * block + t] = field.mul(field.sub(values[i * block + t], values[(i - 1) * block + t]), inverse)
    var expanded = List[UInt64](length=need * block, fill=0)
    for t in range(block):
        expanded[t] = values[(need - 1) * block + t]
    var length = 1
    for j in range(need - 2, -1, -1):
        for t in range(block):
            var carry = UInt64(0)
            for i in range(length + 1):
                var current = expanded[i * block + t] if i < length else UInt64(0)
                expanded[i * block + t] = field.sub(carry, field.mul(current, points[j]))
                carry = current
            expanded[t] = field.add(expanded[t], values[j * block + t])
        length += 1
    var extents = List[Int]()
    extents.append(need)
    for e in inner:
        extents.append(e)
    var interpolant = _Grid(expanded^, extents^)
    var primitive = _divide_vectors(interpolant, _content(interpolant, field, budget), field, budget)
    # Multiply back the content gcd in y.
    var pblock = _size(primitive.extents, 1)
    var outer = primitive.extents[0] + len(common) - 1
    var data = List[UInt64](length=outer * pblock, fill=0)
    for t in range(pblock):
        var v = _product_words(_vector(primitive, t), common, field)
        for j in range(len(v)):
            data[j * pblock + t] = v[j]
    var result_extents = primitive.extents.copy()
    result_extents[0] = outer
    var result = _Grid(data^, result_extents^)
    var top = _encode(_lead(result), result.extents)
    var inverse = field.inverse(result.data[top])
    for i in range(len(result.data)):
        result.data[i] = field.mul(result.data[i], inverse)
    return result^


def _box(p: SparsePoly[ZZ], variables: List[Int64], mut budget: Budget) raises PolyError -> List[Int]:
    """Extents outermost first: the last variable first, the first variable last."""
    var out = List[Int]()
    for i in range(len(variables) - 1, -1, -1):
        out.append(max(p.degree_in(variables[i], budget), 0) + 1)
    return out^


def _exponents(m: Monomial, variables: List[Int64]) -> List[Int]:
    var out = List[Int](length=len(variables), fill=0)
    var position = 0
    for pair in m.pairs:
        while variables[position] != pair[0]:
            position += 1
        out[position] = Int(pair[1])
    return out^


def _cells(p: SparsePoly[ZZ], variables: List[Int64], extents: List[Int], mut budget: Budget) raises PolyError -> List[Int]:
    _allocation[Int](len(p.terms), budget)
    var out = List[Int](capacity=len(p.terms))
    for t in p.terms:
        budget.charge(1)
        out.append(_encode(_exponents(t.monomial, variables), extents))
    return out^


def _image(p: SparsePoly[ZZ], cells: List[Int], extents: List[Int], field: _Field, mut budget: Budget) raises PolyError -> _Grid:
    var size = _size(extents, 0)
    _allocation[UInt64](size, budget)
    var data = List[UInt64](length=size, fill=0)
    for i in range(len(p.terms)):
        budget.charge(1)
        data[cells[i]] = field.enter(_residue(p.terms[i].coefficient.value, field.p, budget))
    return _Grid(data^, extents.copy())


def _lead_term(p: SparsePoly[ZZ], variables: List[Int64]) -> Int:
    var best = 0
    var best_exponents = _exponents(p.terms[0].monomial, variables)
    for i in range(1, len(p.terms)):
        var e = _exponents(p.terms[i].monomial, variables)
        if _less(best_exponents, e):
            best = i
            best_exponents = e^
    return best


def _primitive(p: SparsePoly[ZZ], mut budget: Budget) raises PolyError -> SparsePoly[ZZ]:
    var c = ZZ(Integer(0))
    for t in p.terms:
        c = _gcd_coefficient(c, t.coefficient, budget)
    if c.value == Integer(1):
        return p.copy()
    var terms = List[Term[ZZ]](capacity=len(p.terms))
    for t in p.terms:
        terms.append(Term[ZZ](t.monomial.copy(), _exact(t.coefficient, c, budget)))
    var out = SparsePoly[ZZ].zero(p.order, NoContext(), budget)
    out.terms = terms^
    return out^


def _brown_gcd(f: SparsePoly[ZZ], h: SparsePoly[ZZ], variables: List[Int64], mut budget: Budget) raises PolyError -> Optional[SparsePoly[ZZ]]:
    """The gcd up to sign of two nonzero integer polynomials in two or more variables, or None."""
    var ef = _box(f, variables, budget)
    var eh = _box(h, variables, budget)
    var cells_f = 1
    var cells_h = 1
    for i in range(len(ef)):
        cells_f = _product(cells_f, ef[i])
        cells_h = _product(cells_h, eh[i])
        if cells_f > _CELLS or cells_h > _CELLS:
            return None
    var cf = ZZ(Integer(0))
    for t in f.terms:
        cf = _gcd_coefficient(cf, t.coefficient, budget)
    var ch = ZZ(Integer(0))
    for t in h.terms:
        ch = _gcd_coefficient(ch, t.coefficient, budget)
    var common = _gcd_coefficient(cf, ch, budget)
    var pf = _primitive(f, budget)
    var ph = _primitive(h, budget)
    ref lf = pf.terms[_lead_term(pf, variables)].coefficient
    ref lh = ph.terms[_lead_term(ph, variables)].coefficient
    var gamma = _gcd_coefficient(lf, lh, budget)
    var where_f = _cells(pf, variables, ef, budget)
    var where_h = _cells(ph, variables, eh, budget)
    var shape = List[Int]()
    for i in range(len(ef)):
        shape.append(min(ef[i], eh[i]))
    var count = _size(shape, 0)
    var values = _Reconstruction(0, budget)
    var best = List[Int]()
    var primes = 0
    var failures = 0
    for index in range(_PRIMES):
        budget.charge(1)
        var p = prime(index, budget)
        if _residue(lf.value, p, budget) == 0 or _residue(lh.value, p, budget) == 0:
            continue
        var field = _Field.of(p)
        var image = _brown(_image(pf, where_f, ef, field, budget), _image(ph, where_h, eh, field, budget), field, budget)
        if not image:
            return None
        ref g = image.value()
        var lead = _lead(g)
        if primes == 0 or _less(lead, best):
            best = lead^
            values = _Reconstruction(count, budget)
            primes = 0
        elif _less(best, lead):
            continue
        var scale = field.enter(_residue(gamma.value, p, budget))
        var residues = List[UInt64](length=count, fill=0)
        for i in range(len(g.data)):
            if g.data[i] == 0:
                continue
            var cell = _encode(_decode(i, g.extents), shape)
            if cell < 0:
                return None
            residues[cell] = field.leave(field.mul(g.data[i], scale))
        var changed = values.merge(residues, p, budget)
        primes += 1
        # Small coefficients are exact after one prime: try the first image, then
        # only images that a further prime left unchanged.
        if primes != 1 and changed:
            continue
        var terms = List[Term[ZZ]]()
        for cell in range(count):
            if values.values[cell] == Integer(0):
                continue
            var e = _decode(cell, shape)
            var pairs = List[Tuple[Int64, UInt32]]()
            for i in range(len(e)):
                if e[i]:
                    pairs.append((variables[i], UInt32(e[i])))
            terms.append(Term[ZZ](Monomial(pairs^, budget), ZZ(values.values[cell].copy())))
        var candidate = _primitive(SparsePoly[ZZ].from_terms(terms^, f.order, NoContext(), budget), budget)
        if divide_exact(pf, candidate, budget) and divide_exact(ph, candidate, budget):
            return candidate.scale(common, budget)
        if primes == 1:
            continue
        failures += 1
        if failures >= 3:
            return None
    return None
