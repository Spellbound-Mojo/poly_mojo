"""Brown's modular gcd on sparse packed terms.

The dense recursion of _brown_gcd pays for every cell of the exponent box;
inputs in many variables of low degree (Fateman's F_2, F_3) have boxes of
millions of cells but only hundreds of terms. Here a polynomial modulo p is
a sorted list of (LEX key, Montgomery word) pairs, the key packing every
exponent with the first variable most significant. The recursion
specializes the last remaining variable y, whose field is the lowest
nonzero one, so dropping it keeps the keys sorted and equal ones adjacent.
Each level is Brown's: contents in y, gamma = gcd of the leading
coefficients, a degree bound in y from one image, images at points where
neither leading coefficient vanishes, leading-key tracking for unlucky
points, and Newton interpolation over the union of the images' supports.
Over ZZ the images are combined by symmetric CRT and the primitive
candidate is accepted only when divide_exact shows that it divides both
inputs. Anything unexpected returns None and the caller falls back.
"""
from apn_mojo import Integer
from .errors import Budget, PolyError, PolyErrorKind, _allocation, _charge_size, _sum, _product
from .coefficients import ZZ, NoContext
from .sparse import SparsePoly, Term
from .monomial import Monomial
from .division import divide_exact
from .primes import prime, _residue
from ._coefficient_ops import _gcd_coefficient
from ._nmod_euclid import _Field, _gcd_words, _trim_words
from ._brown_gcd import _primitive, _quotient_words, _product_words, _evaluate

comptime _PRIMES = 64
# Terms handled per prime before the recursion gives up (deterministic).
comptime _WORK = 1 << 24


struct _Layout(Copyable, Movable):
    """Bit fields of a LEX key; variable 0 is the most significant field."""
    var shifts: List[Int]
    var masks: List[UInt64]

    def __init__(out self):
        self.shifts = List[Int]()
        self.masks = List[UInt64]()

    def field(self, key: UInt64, i: Int) -> Int:
        return Int((key >> UInt64(self.shifts[i])) & self.masks[i])

    def strip(self, key: UInt64, i: Int) -> UInt64:
        return key & ~(self.masks[i] << UInt64(self.shifts[i]))

    def place(self, e: Int, i: Int) -> UInt64:
        return UInt64(e) << UInt64(self.shifts[i])


struct _Terms(Copyable, Movable):
    """Terms with strictly increasing keys and nonzero Montgomery values."""
    var keys: List[UInt64]
    var values: List[UInt64]

    def __init__(out self):
        self.keys = List[UInt64]()
        self.values = List[UInt64]()


def _specialize(p: _Terms, y: Int, point: UInt64, layout: _Layout, field: _Field, mut budget: Budget) raises PolyError -> _Terms:
    """Substitute the point for variable y, the lowest nonzero field."""
    _charge_size(len(p.keys), budget)
    var top = 0
    for key in p.keys:
        top = max(top, layout.field(key, y))
    var powers = List[UInt64](capacity=top + 1)
    var value = field.enter(1)
    for _ in range(top + 1):
        powers.append(value)
        value = field.mul(value, point)
    var out = _Terms()
    out.keys.reserve(len(p.keys))
    out.values.reserve(len(p.keys))
    for i in range(len(p.keys)):
        var key = layout.strip(p.keys[i], y)
        var v = field.mul(p.values[i], powers[layout.field(p.keys[i], y)])
        var n = len(out.keys)
        if n and out.keys[n - 1] == key:
            out.values[n - 1] = field.add(out.values[n - 1], v)
        else:
            out.keys.append(key)
            out.values.append(v)
    var kept = _Terms()
    kept.keys.reserve(len(out.keys))
    kept.values.reserve(len(out.keys))
    for i in range(len(out.keys)):
        if out.values[i] != 0:
            kept.keys.append(out.keys[i])
            kept.values.append(out.values[i])
    return kept^


struct _Runs(Movable):
    """Runs of equal keys outside y, as index ranges: the coefficients in y of each monomial."""
    var starts: List[Int]

    def __init__(out self, p: _Terms, y: Int, layout: _Layout):
        self.starts = List[Int]()
        var i = 0
        while i < len(p.keys):
            self.starts.append(i)
            var key = layout.strip(p.keys[i], y)
            i += 1
            while i < len(p.keys) and layout.strip(p.keys[i], y) == key:
                i += 1
        self.starts.append(len(p.keys))

    def count(self) -> Int:
        return len(self.starts) - 1

    def poly(self, p: _Terms, r: Int, y: Int, layout: _Layout) -> List[UInt64]:
        var top = 0
        for t in range(self.starts[r], self.starts[r + 1]):
            top = max(top, layout.field(p.keys[t], y))
        var out = List[UInt64](length=top + 1, fill=0)
        for t in range(self.starts[r], self.starts[r + 1]):
            out[layout.field(p.keys[t], y)] = p.values[t]
        return out^


def _content(p: _Terms, runs: _Runs, y: Int, layout: _Layout, field: _Field, mut budget: Budget) raises PolyError -> List[UInt64]:
    var c = List[UInt64]()
    for r in range(runs.count()):
        budget.charge(1)
        c = _gcd_words(c^, runs.poly(p, r, y, layout), field, budget)
        if len(c) == 1:
            break
    return c^


def _divide_runs(p: _Terms, runs: _Runs, c: List[UInt64], y: Int, layout: _Layout, field: _Field) raises PolyError -> _Terms:
    """p with the coefficient in y of every monomial divided by c (exactly)."""
    if len(c) <= 1:
        return p.copy()
    var out = _Terms()
    out.keys.reserve(len(p.keys))
    out.values.reserve(len(p.keys))
    for r in range(runs.count()):
        var key = layout.strip(p.keys[runs.starts[r]], y)
        var q = _quotient_words(runs.poly(p, r, y, layout), c, field)
        for e in range(len(q)):
            if q[e] != 0:
                out.keys.append(key | layout.place(e, y))
                out.values.append(q[e])
    return out^


def _from_groups(keys: List[UInt64], polys: List[List[UInt64]], y: Int, layout: _Layout) -> _Terms:
    var out = _Terms()
    for g in range(len(keys)):
        for e in range(len(polys[g])):
            if polys[g][e] != 0:
                out.keys.append(keys[g] | layout.place(e, y))
                out.values.append(polys[g][e])
    return out^


def _y_degree(p: _Terms, y: Int, layout: _Layout) -> Int:
    var top = 0
    for key in p.keys:
        top = max(top, layout.field(key, y))
    return top


def _y_image(p: _Terms, y: Int, attempt: Int, layout: _Layout, field: _Field, mut budget: Budget) raises PolyError -> List[UInt64]:
    """The polynomial in y with the variables before it specialized at fixed points."""
    _charge_size(_product(len(p.keys), y + 1), budget)
    var out = List[UInt64](length=_y_degree(p, y, layout) + 1, fill=0)
    for i in range(len(p.keys)):
        var w = p.values[i]
        for v in range(y):
            var e = layout.field(p.keys[i], v)
            if e:
                w = field.mul(w, field.power(field.enter(UInt64(3 + v + attempt * (y + 1))), e))
        var e_y = layout.field(p.keys[i], y)
        out[e_y] = field.add(out[e_y], w)
    return out^


def _sparse_brown(a: _Terms, b: _Terms, y: Int, layout: _Layout, field: _Field, mut work: Int, mut budget: Budget) raises PolyError -> Optional[_Terms]:
    """The gcd modulo p over variables 0 … y, monic at its largest key, or None.

    `work` counts down the terms handled; the recursion gives up when it runs
    out, since the number of points grows like a product over the levels.
    """
    budget.charge(1)
    work -= len(a.keys) + len(b.keys)
    if work < 0:
        return None
    if y == 0:
        var da = _y_degree(a, 0, layout)
        var db = _y_degree(b, 0, layout)
        var ua = List[UInt64](length=da + 1, fill=0)
        for i in range(len(a.keys)):
            ua[layout.field(a.keys[i], 0)] = a.values[i]
        var ub = List[UInt64](length=db + 1, fill=0)
        for i in range(len(b.keys)):
            ub[layout.field(b.keys[i], 0)] = b.values[i]
        var g = _gcd_words(ua^, ub^, field, budget)
        var out = _Terms()
        for e in range(len(g)):
            if g[e] != 0:
                out.keys.append(layout.place(e, 0))
                out.values.append(g[e])
        return out^
    var runs_a = _Runs(a, y, layout)
    var runs_b = _Runs(b, y, layout)
    var content_a = _content(a, runs_a, y, layout, field, budget)
    var content_b = _content(b, runs_b, y, layout, field, budget)
    var common = _gcd_words(content_a.copy(), content_b.copy(), field, budget)
    var pa = _divide_runs(a, runs_a, content_a, y, layout, field)
    var pb = _divide_runs(b, runs_b, content_b, y, layout, field)
    # The last run of each primitive part is its leading coefficient in y.
    var lead_a = _Runs(pa, y, layout)
    var lead_b = _Runs(pb, y, layout)
    var lc_a = lead_a.poly(pa, lead_a.count() - 1, y, layout)
    var lc_b = lead_b.poly(pb, lead_b.count() - 1, y, layout)
    var gamma = _gcd_words(lc_a.copy(), lc_b.copy(), field, budget)
    var da = _y_degree(pa, y, layout)
    var db = _y_degree(pb, y, layout)
    var bound = min(da, db)
    for attempt in range(3):
        var ia = _y_image(pa, y, attempt, layout, field, budget)
        var ib = _y_image(pb, y, attempt, layout, field, budget)
        if ia[da] != 0 and ib[db] != 0:
            bound = len(_gcd_words(ia^, ib^, field, budget)) - 1
            break
    var need = bound + len(gamma)
    var images = List[_Terms]()
    var points = List[UInt64]()
    var best = UInt64(0)
    var x = 0
    while len(images) < need:
        budget.charge(1)
        x += 1
        if UInt64(x) >= field.p or x > 4 * need + 32:
            return None
        var point = field.enter(UInt64(x))
        if _evaluate(lc_a, point, field) == 0 or _evaluate(lc_b, point, field) == 0:
            continue
        var image = _sparse_brown(_specialize(pa, y, point, layout, field, budget), _specialize(pb, y, point, layout, field, budget), y - 1, layout, field, work, budget)
        if not image:
            return None
        var g = image.take()
        var lead = g.keys[len(g.keys) - 1]
        if not len(images) or lead < best:
            best = lead
            images = List[_Terms]()
            points = List[UInt64]()
        elif lead > best:
            continue
        var scale = _evaluate(gamma, point, field)
        for i in range(len(g.values)):
            g.values[i] = field.mul(g.values[i], scale)
        images.append(g^)
        points.append(point)
    # Newton interpolation in y over the union of the supports.
    var inverses = List[List[UInt64]]()
    for j in range(need):
        var row = List[UInt64](length=need, fill=0)
        for i in range(j + 1, need):
            row[i] = field.inverse(field.sub(points[i], points[i - j - 1]))
        inverses.append(row^)
    var cursor = List[Int](length=need, fill=0)
    var keys = List[UInt64]()
    var polys = List[List[UInt64]]()
    _charge_size(_product(need, need), budget)
    while True:
        var next_key = UInt64.MAX
        var found = False
        for j in range(need):
            if cursor[j] < len(images[j].keys):
                var k = images[j].keys[cursor[j]]
                if not found or k < next_key:
                    next_key = k
                    found = True
        if not found:
            break
        budget.charge(1)
        var c = List[UInt64](length=need, fill=0)
        for j in range(need):
            if cursor[j] < len(images[j].keys) and images[j].keys[cursor[j]] == next_key:
                c[j] = images[j].values[cursor[j]]
                cursor[j] += 1
        for j in range(1, need):
            for i in range(need - 1, j - 1, -1):
                c[i] = field.mul(field.sub(c[i], c[i - 1]), inverses[j - 1][i])
        var poly = List[UInt64](length=need, fill=0)
        poly[0] = c[need - 1]
        var length = 1
        for j in range(need - 2, -1, -1):
            var carry = UInt64(0)
            for i in range(length + 1):
                var current = poly[i] if i < length else UInt64(0)
                poly[i] = field.sub(carry, field.mul(current, points[j]))
                carry = current
            poly[0] = field.add(poly[0], c[j])
            length += 1
        _trim_words(poly)
        if len(poly):
            keys.append(next_key)
            polys.append(poly^)
    var interpolant = _from_groups(keys, polys, y, layout)
    var runs = _Runs(interpolant, y, layout)
    var primitive = _divide_runs(interpolant, runs, _content(interpolant, runs, y, layout, field, budget), y, layout, field)
    var result: _Terms
    if len(common) <= 1:
        result = primitive^
    else:
        var prims = _Runs(primitive, y, layout)
        result = _Terms()
        for r in range(prims.count()):
            var key = layout.strip(primitive.keys[prims.starts[r]], y)
            var v = _product_words(prims.poly(primitive, r, y, layout), common, field)
            for e in range(len(v)):
                if v[e] != 0:
                    result.keys.append(key | layout.place(e, y))
                    result.values.append(v[e])
    if not len(result.keys):
        return None
    var inverse = field.inverse(result.values[len(result.values) - 1])
    for i in range(len(result.values)):
        result.values[i] = field.mul(result.values[i], inverse)
    return result^


def _packed(p: SparsePoly[ZZ], variables: List[Int64], layout: _Layout) -> Tuple[List[UInt64], List[Int]]:
    """Each term's key, and the term indices in increasing key order."""
    var keys = List[UInt64](capacity=len(p.terms))
    for t in p.terms:
        var key = UInt64(0)
        var position = 0
        for pair in t.monomial.pairs:
            while variables[position] != pair[0]:
                position += 1
            key |= layout.place(Int(pair[1]), position)
        keys.append(key)
    var order = List[Int](capacity=len(keys))
    for i in range(len(keys)):
        order.append(i)
    # Insertion runs on the stored order, which is usually close to LEX.
    for i in range(1, len(order)):
        var moving = order[i]
        var j = i
        while j > 0 and keys[order[j - 1]] > keys[moving]:
            order[j] = order[j - 1]
            j -= 1
        order[j] = moving
    return (keys^, order^)


def _image(p: SparsePoly[ZZ], keys: List[UInt64], order: List[Int], field: _Field, mut budget: Budget) raises PolyError -> _Terms:
    var out = _Terms()
    for i in order:
        budget.charge(1)
        var r = _residue(p.terms[i].coefficient.value, field.p, budget)
        if r != 0:
            out.keys.append(keys[i])
            out.values.append(field.enter(r))
    return out^


def _sparse_brown_gcd(f: SparsePoly[ZZ], h: SparsePoly[ZZ], variables: List[Int64], mut budget: Budget) raises PolyError -> Optional[SparsePoly[ZZ]]:
    """The gcd up to sign of two nonzero integer polynomials in two or more variables, or None."""
    var layout = _Layout()
    var widths = List[Int]()
    var total = 0
    for v in variables:
        var d = max(max(f.degree_in(v, budget), h.degree_in(v, budget)), 1)
        var bits = 0
        while (d >> bits) != 0:
            bits += 1
        widths.append(bits)
        total += bits
    if total > 64:
        return None
    var shift = total
    for i in range(len(variables)):
        shift -= widths[i]
        layout.shifts.append(shift)
        layout.masks.append((UInt64(1) << UInt64(widths[i])) - 1)
    var cf = ZZ(Integer(0))
    for t in f.terms:
        cf = _gcd_coefficient(cf, t.coefficient, budget)
    var ch = ZZ(Integer(0))
    for t in h.terms:
        ch = _gcd_coefficient(ch, t.coefficient, budget)
    var common = _gcd_coefficient(cf, ch, budget)
    var pf = _primitive(f, budget)
    var ph = _primitive(h, budget)
    var packed_f = _packed(pf, variables, layout)
    var packed_h = _packed(ph, variables, layout)
    ref lf = pf.terms[packed_f[1][len(packed_f[1]) - 1]].coefficient
    ref lh = ph.terms[packed_h[1][len(packed_h[1]) - 1]].coefficient
    var gamma = _gcd_coefficient(lf, lh, budget)
    var y = len(variables) - 1
    var keys = List[UInt64]()
    var values = List[Integer]()
    var modulus = Integer(1)
    var best = UInt64(0)
    var primes = 0
    var failures = 0
    for index in range(_PRIMES):
        budget.charge(1)
        var p = prime(index, budget)
        if _residue(lf.value, p, budget) == 0 or _residue(lh.value, p, budget) == 0:
            continue
        var field = _Field.of(p)
        var work = _WORK
        var image = _sparse_brown(_image(pf, packed_f[0], packed_f[1], field, budget), _image(ph, packed_h[0], packed_h[1], field, budget), y, layout, field, work, budget)
        if not image:
            return None
        ref g = image.value()
        var lead = g.keys[len(g.keys) - 1]
        if primes == 0 or lead < best:
            best = lead
            keys = List[UInt64]()
            values = List[Integer]()
            modulus = Integer(1)
            primes = 0
        elif lead > best:
            continue
        # Symmetric CRT over the union of supports; a missing key is a zero residue.
        var scale = field.enter(_residue(gamma.value, p, budget))
        var inverse = field.inverse(field.enter(_residue(modulus, p, budget)))
        var next_modulus = ZZ(modulus.copy()).mul(ZZ(Integer(Int(p))), budget).value
        var half: Integer
        try:
            half = next_modulus >> 1
        except e:
            raise PolyError(PolyErrorKind.CAPACITY, String(e))
        var merged_keys = List[UInt64]()
        var merged = List[Integer]()
        var changed = False
        var i = 0
        var j = 0
        while i < len(keys) or j < len(g.keys):
            budget.charge(1)
            var key: UInt64
            var old = Integer(0)
            var residue = UInt64(0)
            if j >= len(g.keys) or (i < len(keys) and keys[i] < g.keys[j]):
                key = keys[i]
                old = values[i].copy()
                i += 1
            elif i >= len(keys) or g.keys[j] < keys[i]:
                key = g.keys[j]
                residue = field.leave(field.mul(g.values[j], scale))
                j += 1
            else:
                key = keys[i]
                old = values[i].copy()
                residue = field.leave(field.mul(g.values[j], scale))
                i += 1
                j += 1
            var difference = field.sub(field.enter(residue), field.enter(_residue(old, p, budget)))
            if difference != 0:
                changed = True
                var correction = field.leave(field.mul(difference, inverse))
                old = ZZ(old^).add(ZZ(modulus.copy()).mul(ZZ(Integer(Int(correction))), budget), budget).value
                if old > half:
                    old = ZZ(old^).sub(ZZ(next_modulus.copy()), budget).value
            if old != Integer(0):
                merged_keys.append(key)
                merged.append(old^)
        keys = merged_keys^
        values = merged^
        modulus = next_modulus^
        primes += 1
        # The first image and images a further prime left unchanged are tried.
        if primes != 1 and changed:
            continue
        var terms = List[Term[ZZ]]()
        for t in range(len(keys)):
            var pairs = List[Tuple[Int64, UInt32]]()
            for v in range(len(variables)):
                var e = layout.field(keys[t], v)
                if e:
                    pairs.append((variables[v], UInt32(e)))
            terms.append(Term[ZZ](Monomial(pairs^, budget), ZZ(values[t].copy())))
        var candidate = _primitive(SparsePoly[ZZ].from_terms(terms^, f.order, NoContext(), budget), budget)
        if not candidate.is_zero() and divide_exact(pf, candidate, budget) and divide_exact(ph, candidate, budget):
            return candidate.scale(common, budget)
        if primes == 1:
            continue
        failures += 1
        if failures >= 3:
            return None
    return None
