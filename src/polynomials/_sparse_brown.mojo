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
    # A run that is a nonzero constant in y makes the content one.
    for r in range(runs.count()):
        if runs.starts[r + 1] - runs.starts[r] == 1 and layout.field(p.keys[runs.starts[r]], y) == 0:
            return [field.enter(1)]
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
    # powers[v][e] is the point for variable v to the e.
    var powers = List[List[UInt64]](capacity=y)
    for v in range(y):
        var top = 0
        for key in p.keys:
            top = max(top, layout.field(key, v))
        var point = field.enter(UInt64(3 + v + attempt * (y + 1)))
        var row = List[UInt64](capacity=top + 1)
        var value = field.enter(1)
        for _ in range(top + 1):
            row.append(value)
            value = field.mul(value, point)
        powers.append(row^)
    for i in range(len(p.keys)):
        var w = p.values[i]
        for v in range(y):
            var e = layout.field(p.keys[i], v)
            if e:
                w = field.mul(w, powers[v][e])
        var e_y = layout.field(p.keys[i], y)
        out[e_y] = field.add(out[e_y], w)
    return out^


def _mixed(seed: UInt64) -> UInt64:
    """SplitMix64: a fixed, well-spread word for each seed."""
    var z = seed + 0x9E3779B97F4A7C15
    z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9
    z = (z ^ (z >> 27)) * 0x94D049BB133111EB
    return z ^ (z >> 31)


def _scattered(seed: UInt64, field: _Field) -> UInt64:
    """A nonzero Montgomery residue chosen deterministically from the seed."""
    var v = _mixed(seed) % field.p
    return field.enter(v if v else 1)


def _transposed_vandermonde(z: List[UInt64], w: List[UInt64], field: _Field) raises PolyError -> List[UInt64]:
    """The c with sum_m c_m z_m^k = w_(k-1) for k = 1 … n, for distinct nonzero z."""
    var n = len(z)
    # master[i] is the coefficient of Z^i in prod (Z - z_m).
    var master = List[UInt64](length=n + 1, fill=0)
    master[0] = field.enter(1)
    for m in range(n):
        for i in range(m + 1, 0, -1):
            master[i] = field.sub(master[i - 1], field.mul(master[i], z[m]))
        master[0] = field.sub(0, field.mul(master[0], z[m]))
    var c = List[UInt64](capacity=n)
    var q = List[UInt64](length=n, fill=0)
    for m in range(n):
        # q = master / (Z - z_m) by synthetic division; d_m = <q, w> / q(z_m).
        q[n - 1] = master[n]
        for i in range(n - 1, 0, -1):
            q[i - 1] = field.add(master[i], field.mul(z[m], q[i]))
        var numerator = UInt64(0)
        var denominator = UInt64(0)
        var power = field.enter(1)
        for i in range(n):
            numerator = field.add(numerator, field.mul(q[i], w[i]))
            denominator = field.add(denominator, field.mul(q[i], power))
            power = field.mul(power, z[m])
        c.append(field.mul(numerator, field.inverse(field.mul(denominator, z[m]))))
    return c^


def _solve(mut rows: List[List[UInt64]], field: _Field) raises PolyError -> Optional[List[UInt64]]:
    """The solution of the square system rows · x = last column, or None when singular."""
    var n = len(rows)
    for col in range(n):
        var pivot = -1
        for r in range(col, n):
            if rows[r][col] != 0:
                pivot = r
                break
        if pivot < 0:
            return None
        if pivot != col:
            rows.swap_elements(pivot, col)
        var inverse = field.inverse(rows[col][col])
        for j in range(col, n + 1):
            rows[col][j] = field.mul(rows[col][j], inverse)
        for r in range(n):
            if r != col and rows[r][col] != 0:
                var factor = rows[r][col]
                for j in range(col, n + 1):
                    rows[r][j] = field.sub(rows[r][j], field.mul(factor, rows[col][j]))
    var x = List[UInt64](capacity=n)
    for r in range(n):
        x.append(rows[r][n])
    return x^


def _x0_images(p: _Terms, y: Int, point: UInt64, beta: List[List[UInt64]], count: Int, layout: _Layout, field: _Field, mut budget: Budget) raises PolyError -> Optional[List[List[UInt64]]]:
    """p at y = point and x_v = beta_v^k for 0 < v < y, k = 1 … count, as polynomials in x_0.

    None when the leading coefficient in x_0 vanishes at some k.
    """
    _charge_size(_product(len(p.keys), count + y), budget)
    var top = 0
    var y_top = 0
    for key in p.keys:
        top = max(top, layout.field(key, 0))
        y_top = max(y_top, layout.field(key, y))
    var powers = List[UInt64](capacity=y_top + 1)
    var value = field.enter(1)
    for _ in range(y_top + 1):
        powers.append(value)
        value = field.mul(value, point)
    var z = List[UInt64](capacity=len(p.keys))
    var w = List[UInt64](capacity=len(p.keys))
    var e0 = List[Int](capacity=len(p.keys))
    for i in range(len(p.keys)):
        var key = p.keys[i]
        var m = field.enter(1)
        for v in range(1, y):
            var e = layout.field(key, v)
            if e:
                m = field.mul(m, beta[v][e])
        z.append(m)
        w.append(field.mul(p.values[i], powers[layout.field(key, y)]))
        e0.append(layout.field(key, 0))
    var out = List[List[UInt64]](capacity=count)
    for _ in range(count):
        var image = List[UInt64](length=top + 1, fill=0)
        for i in range(len(z)):
            w[i] = field.mul(w[i], z[i])
            image[e0[i]] = field.add(image[e0[i]], w[i])
        if image[top] == 0:
            return None
        out.append(image^)
    return out^


def _skeleton_image(a: _Terms, b: _Terms, skeleton: _Terms, y: Int, point: UInt64, layout: _Layout, field: _Field, mut work: Int, mut budget: Budget) raises PolyError -> Optional[_Terms]:
    """The gcd of a and b at y = point, monic at its largest key, on the skeleton's support.

    Zippel's sparse interpolation: with x_1 … x_(y-1) at powers of fixed
    points, the univariate gcds in x_0 give, for each power of x_0, a
    transposed Vandermonde system in the skeleton's coefficients. The
    images are monic, so they carry the unknown scale L(beta^k), L the
    skeleton's leading coefficient in x_0; when L has several terms they are
    solved first together with the smallest other group. One extra point
    checks every equation. None when the skeleton does not fit (an unlucky
    point or a wrong support); the caller then recurses densely.
    """
    # Groups of equal x_0 exponent are contiguous in increasing key order.
    var starts = List[Int]()
    for i in range(len(skeleton.keys)):
        if not i or layout.field(skeleton.keys[i], 0) != layout.field(skeleton.keys[i - 1], 0):
            starts.append(i)
    starts.append(len(skeleton.keys))
    var groups = len(starts) - 1
    if groups < 2:
        return None
    var top_start = starts[groups - 1]
    var leading = len(skeleton.keys) - top_start
    var degree = layout.field(skeleton.keys[top_start], 0)
    # Fixed points for x_1 … x_(y-1) and their power tables.
    var tops = List[Int](length=y, fill=0)
    for key in a.keys:
        for v in range(1, y):
            tops[v] = max(tops[v], layout.field(key, v))
    for key in b.keys:
        for v in range(1, y):
            tops[v] = max(tops[v], layout.field(key, v))
    for key in skeleton.keys:
        for v in range(1, y):
            tops[v] = max(tops[v], layout.field(key, v))
    var beta = List[List[UInt64]](capacity=y)
    beta.append(List[UInt64]())
    for v in range(1, y):
        var base = _scattered(UInt64(v) << 32 | UInt64(y), field)
        var row = List[UInt64](capacity=tops[v] + 1)
        var value = field.enter(1)
        for _ in range(tops[v] + 1):
            row.append(value)
            value = field.mul(value, base)
        beta.append(row^)
    var z = List[UInt64](capacity=len(skeleton.keys))
    for key in skeleton.keys:
        var m = field.enter(1)
        for v in range(1, y):
            var e = layout.field(key, v)
            if e:
                m = field.mul(m, beta[v][e])
        z.append(m)
    # Nodes must be distinct within each group.
    var smallest = -1
    var widest = 0
    for g in range(groups):
        var sorted_z = List[UInt64](capacity=starts[g + 1] - starts[g])
        for i in range(starts[g], starts[g + 1]):
            sorted_z.append(z[i])
        sort(sorted_z)
        for i in range(1, len(sorted_z)):
            if sorted_z[i] == sorted_z[i - 1]:
                return None
        var size = starts[g + 1] - starts[g]
        if g < groups - 1:
            widest = max(widest, size)
            if smallest < 0 or size < starts[smallest + 1] - starts[smallest]:
                smallest = g
    var joint = 0
    if leading > 1:
        joint = starts[smallest + 1] - starts[smallest] + leading - 1
    var count = max(widest, joint) + 1
    work -= count * (len(a.keys) + len(b.keys))
    if work < 0:
        return None
    var images_a = _x0_images(a, y, point, beta, count, layout, field, budget)
    if not images_a:
        return None
    var images_b = _x0_images(b, y, point, beta, count, layout, field, budget)
    if not images_b:
        return None
    # u[k] is the monic gcd in x_0 at the (k+1)-th power point.
    var u = List[List[UInt64]](capacity=count)
    for k in range(count):
        budget.charge(1)
        var g = _gcd_words(images_a.value()[k].copy(), images_b.value()[k].copy(), field, budget)
        if len(g) != degree + 1:
            return None
        u.append(g^)
    # Exponents of x_0 outside the skeleton must vanish in every image.
    var present = List[Bool](length=degree + 1, fill=False)
    for g in range(groups):
        present[layout.field(skeleton.keys[starts[g]], 0)] = True
    for k in range(count):
        for e in range(degree + 1):
            if not present[e] and u[k][e] != 0:
                return None
    var c = List[UInt64](length=len(skeleton.keys), fill=0)
    c[len(skeleton.keys) - 1] = field.enter(1)
    # A leading group of several terms is solved jointly with the smallest
    # other group, its largest key fixed at one.
    if leading > 1:
        var s0 = starts[smallest]
        var s1 = starts[smallest + 1]
        var e_small = layout.field(skeleton.keys[s0], 0)
        var rows = List[List[UInt64]](capacity=joint)
        var power = List[UInt64](length=len(skeleton.keys), fill=field.enter(1))
        for k in range(joint):
            budget.charge(1)
            var row = List[UInt64](capacity=joint + 1)
            for i in range(s0, s1):
                power[i] = field.mul(power[i], z[i])
                row.append(power[i])
            var v = u[k][e_small]
            for i in range(top_start, len(skeleton.keys)):
                power[i] = field.mul(power[i], z[i])
            for i in range(top_start, len(skeleton.keys) - 1):
                row.append(field.sub(0, field.mul(v, power[i])))
            row.append(field.mul(v, power[len(skeleton.keys) - 1]))
            rows.append(row^)
        var solution = _solve(rows, field)
        if not solution:
            return None
        for i in range(s0, s1):
            c[i] = solution.value()[i - s0]
        for i in range(top_start, len(skeleton.keys) - 1):
            c[i] = solution.value()[s1 - s0 + i - top_start]
    # scale[k] = L(beta^(k+1)), the leading coefficient in x_0 at each point.
    var scale = List[UInt64](length=count, fill=0)
    var power = List[UInt64](length=leading, fill=field.enter(1))
    for k in range(count):
        var total = UInt64(0)
        for i in range(top_start, len(skeleton.keys)):
            power[i - top_start] = field.mul(power[i - top_start], z[i])
            total = field.add(total, field.mul(c[i], power[i - top_start]))
        if total == 0:
            return None
        scale[k] = total
    for g in range(groups - 1):
        if leading > 1 and g == smallest:
            continue
        budget.charge(1)
        var size = starts[g + 1] - starts[g]
        _charge_size(_product(size, size), budget)
        var e = layout.field(skeleton.keys[starts[g]], 0)
        var nodes = List[UInt64](capacity=size)
        var w = List[UInt64](capacity=size)
        for i in range(starts[g], starts[g + 1]):
            nodes.append(z[i])
        for k in range(size):
            w.append(field.mul(u[k][e], scale[k]))
        var solved = _transposed_vandermonde(nodes, w, field)
        for i in range(size):
            c[starts[g] + i] = solved[i]
    # The extra point checks every group.
    var last = count - 1
    for g in range(groups - 1):
        budget.charge(1)
        var e = layout.field(skeleton.keys[starts[g]], 0)
        var total = UInt64(0)
        for i in range(starts[g], starts[g + 1]):
            total = field.add(total, field.mul(c[i], field.power(z[i], count)))
        if total != field.mul(u[last][e], scale[last]):
            return None
    var out = _Terms()
    for i in range(len(skeleton.keys)):
        if c[i] != 0:
            out.keys.append(skeleton.keys[i])
            out.values.append(c[i])
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
    var skeleton = Optional[_Terms](None)
    var images = List[_Terms]()
    var points = List[UInt64]()
    var best = UInt64(0)
    var x = 0
    while len(images) < need:
        budget.charge(1)
        x += 1
        if x > 4 * need + 32:
            return None
        var point = _scattered(UInt64(x) << 32 | UInt64(y) << 16 | 0xB, field)
        var repeated = False
        for q in points:
            repeated = repeated or q == point
        if repeated:
            continue
        if _evaluate(lc_a, point, field) == 0 or _evaluate(lc_b, point, field) == 0:
            continue
        var image = Optional[_Terms](None)
        if skeleton:
            image = _skeleton_image(pa, pb, skeleton.value(), y, point, layout, field, work, budget)
            if not image:
                skeleton = None
        if not image:
            image = _sparse_brown(_specialize(pa, y, point, layout, field, budget), _specialize(pb, y, point, layout, field, budget), y - 1, layout, field, work, budget)
            if not image:
                return None
        var g = image.take()
        var lead = g.keys[len(g.keys) - 1]
        if not len(images) or lead < best:
            best = lead
            images = List[_Terms]()
            points = List[UInt64]()
            # Later images at this level reuse this one's support when it has
            # three or more variables; dense recursion measured faster below.
            if y >= 3:
                skeleton = g.copy()
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
