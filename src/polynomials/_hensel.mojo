"""Quadratic multifactor Hensel lifting over a binary factor tree (Z-4)."""
from apn_mojo import Integer, inverse_mod
from ._integer_ops import _primitive, _divide_scalar
from .coefficients import ZZ, ModInt, NoContext, _work, _pow
from .dense import DensePoly, _slice, _trim
from .coefficient_buffer import _view
from .errors import Budget, PolyError, PolyErrorKind, _allocation, _product, _sum
from ._coefficient_ops import _copy as _copy_coefficient
from ._coefficient_ops import _quotient
from ._dense_ops import _constant, _remainder, _exact
from ._euclidean import _extended
from ._images import _mod_image
from .primes import _symmetric


def _lift_image(f: DensePoly[ModInt], mut budget: Budget) raises PolyError -> DensePoly[ZZ]:
    _allocation[ZZ](len(f.coefficients), budget)
    var values = List[ZZ](capacity=len(f.coefficients))
    for coefficient_index in range(len(f.coefficients)):
        ref c = f.coefficients[coefficient_index]
        budget.charge(1)
        values.append(ZZ(Integer(Int(c.value))))
    return DensePoly[ZZ]._from_canonical(f.variable, NoContext(), values^)


def _truncate(f: DensePoly[ZZ], modulus: ZZ, mut budget: Budget) raises PolyError -> DensePoly[ZZ]:
    _allocation[ZZ](len(f.coefficients), budget)
    var values = List[ZZ](capacity=len(f.coefficients))
    for coefficient_index in range(len(f.coefficients)):
        ref c = f.coefficients[coefficient_index]
        budget.charge(1)
        values.append(ZZ(_symmetric(c.value, modulus.value, budget)))
    return DensePoly[ZZ].from_coefficients(f.variable, NoContext(), values^, budget)


def _trial_divide(f: DensePoly[ZZ], g: DensePoly[ZZ], mut budget: Budget) raises PolyError -> Optional[DensePoly[ZZ]]:
    f._same(g)
    if g.is_zero():
        raise PolyError(PolyErrorKind.DOMAIN, "zero integer polynomial divisor")
    var n = max(f.degree() - g.degree() + 1, 0)
    _allocation[ZZ](n, budget)
    var quotient = List[ZZ](length=n, fill=ZZ.zero(f.ring))
    var remainder = _slice(_view(f.coefficients), 0, len(f.coefficients), budget)
    while len(remainder) >= len(g.coefficients):
        budget.charge(1)
        var shift = len(remainder) - len(g.coefficients)
        var scalar = _quotient(remainder[len(remainder) - 1], g.coefficients[g.degree()], budget)
        if not scalar:
            return None
        var q = scalar.take()
        for i in range(len(g.coefficients)):
            budget.charge(1)
            remainder[shift + i] = remainder[shift + i].sub(q.mul(g.coefficients[i], budget), budget)
        quotient[shift] = q^
        _trim(remainder, budget)
    if len(remainder):
        return None
    return DensePoly[ZZ].from_coefficients(f.variable, f.ring, quotient^, budget)


@fieldwise_init
struct _HenselNode(Copyable, Movable):
    # Internal nodes hold Bezout cofactors s*left + t*right = 1 for their
    # children; leaves name their position in the lifted factor list.
    var poly: DensePoly[ZZ]
    var s: DensePoly[ZZ]
    var t: DensePoly[ZZ]
    var left: Int
    var right: Int
    var leaf: Int


@fieldwise_init
struct _HenselState(Movable):
    var lifted: List[DensePoly[ZZ]]
    var modulus: ZZ
    # modulus = p^exponent for the tree below; exponent zero means the
    # factor tree has not been built and lifting starts from the images.
    var exponent: Int
    var nodes: List[_HenselNode]


def _hensel_start(factors: List[DensePoly[ModInt]], mut budget: Budget) raises PolyError -> _HenselState:
    if len(factors) == 0:
        raise PolyError(PolyErrorKind.DOMAIN, "Hensel lifting requires modular factors")
    _allocation[DensePoly[ZZ]](len(factors), budget)
    var lifted = List[DensePoly[ZZ]](capacity=len(factors))
    for g in factors:
        budget.charge(1)
        lifted.append(_lift_image(g, budget))
    return _HenselState(lifted^, ZZ(Integer(Int(factors[0].ring.value))), 0, List[_HenselNode]())


def _hensel_resume(var lifted: List[DensePoly[ZZ]], var modulus: ZZ) -> _HenselState:
    """A state holding lifted factors without their tree; extending rebuilds it."""
    return _HenselState(lifted^, modulus^, 0, List[_HenselNode]())


def _build_tree(factors: List[DensePoly[ModInt]], mut state: _HenselState, mut budget: Budget) raises PolyError:
    # Pair adjacent nodes level by level; the root is the last node.
    var ctx = factors[0].ring
    var x = factors[0].variable
    _allocation[_HenselNode](_product(2, len(factors)), budget)
    var nodes = List[_HenselNode]()
    var images = List[DensePoly[ModInt]]()
    var level = List[Int]()
    for i in range(len(factors)):
        budget.charge(1)
        nodes.append(_HenselNode(_lift_image(factors[i], budget), DensePoly[ZZ](x, NoContext()), DensePoly[ZZ](x, NoContext()), -1, -1, i))
        images.append(factors[i].copy())
        level.append(i)
    while len(level) > 1:
        budget.charge(1)
        var next = List[Int]()
        var i = 0
        while i + 1 < len(level):
            var left = level[i]
            var right = level[i + 1]
            var egcd = _extended(images[left], images[right], budget)
            if egcd[0].degree() != 0:
                raise PolyError(PolyErrorKind.DOMAIN, "Hensel lifting requires coprime modular factors")
            var product = images[left].mul(images[right], budget)
            nodes.append(_HenselNode(_lift_image(product, budget), _lift_image(egcd[1], budget), _lift_image(egcd[2], budget), left, right, -1))
            images.append(product^)
            next.append(len(nodes) - 1)
            i += 2
        if i < len(level):
            next.append(level[i])
        level = next^
    for i in range(len(factors)):
        state.lifted[i] = nodes[i].poly.copy()
    state.nodes = nodes^
    state.modulus = ZZ(Integer(Int(ctx.value)))
    state.exponent = 1


def _divmod_monic(a: DensePoly[ZZ], h: DensePoly[ZZ], modulus: ZZ, mut budget: Budget) raises PolyError -> Tuple[DensePoly[ZZ], DensePoly[ZZ]]:
    # Long division by a monic divisor over Z/modulus.
    var n = h.degree()
    var r = _slice(_view(a.coefficients), 0, len(a.coefficients), budget)
    var length = max(len(r) - n, 0)
    _allocation[ZZ](length, budget)
    var q = List[ZZ](length=length, fill=ZZ.zero(NoContext()))
    var top = len(r) - 1
    while top >= n:
        budget.charge(1)
        var c = ZZ(_symmetric(r[top].value, modulus.value, budget))
        if not c.is_zero():
            var shift = top - n
            for i in range(n):
                budget.charge(1)
                r[shift + i] = r[shift + i].sub(c.mul(h.coefficients[i], budget), budget)
            q[shift] = c^
        r[top] = ZZ.zero(NoContext())
        top -= 1
    var quotient = _truncate(DensePoly[ZZ].from_coefficients(a.variable, NoContext(), q^, budget), modulus, budget)
    var remainder = _truncate(DensePoly[ZZ].from_coefficients(a.variable, NoContext(), r^, budget), modulus, budget)
    return (quotient^, remainder^)


def _lift_tree(f: DensePoly[ZZ], mut state: _HenselState, modulus: ZZ, mut budget: Budget) raises PolyError:
    # One quadratic step (von zur Gathen and Gerhard, Algorithm 15.10) at
    # every internal node, from the root's monic image of f downwards. The
    # new modulus divides the square of the old one.
    var inverse: Integer
    try:
        inverse = inverse_mod(f.coefficients[f.degree()].value, modulus.value)
    except e:
        raise PolyError(PolyErrorKind.DOMAIN, "leading coefficient is not invertible modulo the lifting prime")
    var target = _truncate(f.scale(ZZ(inverse^), budget), modulus, budget)
    var one = _constant(f, ZZ.one(NoContext()), budget)
    var pending: List[Tuple[Int, DensePoly[ZZ]]] = [(len(state.nodes) - 1, target^)]
    while len(pending):
        budget.charge(1)
        var item = pending.pop()
        var v = item[0]
        if state.nodes[v].leaf >= 0:
            state.nodes[v].poly = item[1].copy()
            state.lifted[state.nodes[v].leaf] = item[1].copy()
            continue
        var left = state.nodes[v].left
        var right = state.nodes[v].right
        ref g = state.nodes[left].poly
        ref h = state.nodes[right].poly
        ref s = state.nodes[v].s
        ref t = state.nodes[v].t
        var e = _truncate(item[1].sub(g.mul(h, budget), budget), modulus, budget)
        var qr = _divmod_monic(_truncate(s.mul(e, budget), modulus, budget), h, modulus, budget)
        var g2 = _truncate(g.add(t.mul(e, budget), budget).add(qr[0].mul(g, budget), budget), modulus, budget)
        var h2 = _truncate(h.add(qr[1], budget), modulus, budget)
        var b = _truncate(s.mul(g2, budget).add(t.mul(h2, budget), budget).sub(one, budget), modulus, budget)
        var cd = _divmod_monic(_truncate(s.mul(b, budget), modulus, budget), h2, modulus, budget)
        var s2 = _truncate(s.sub(cd[1], budget), modulus, budget)
        var t2 = _truncate(t.sub(t.mul(b, budget), budget).sub(cd[0].mul(g2, budget), budget), modulus, budget)
        state.nodes[v].s = s2^
        state.nodes[v].t = t2^
        state.nodes[v].poly = item[1].copy()
        pending.append((left, g2^))
        pending.append((right, h2^))


def _hensel_extend(f: DensePoly[ZZ], factors: List[DensePoly[ModInt]], bound: ZZ, mut state: _HenselState, mut budget: Budget) raises PolyError:
    # Lift the monic factors until the modulus exceeds the bound, to the
    # least such power of p, by quadratic steps over a binary factor tree.
    # The leading coefficient of f is carried separately, so every lifted
    # factor stays monic with its modular degree.
    var p = ZZ(Integer(Int(factors[0].ring.value)))
    _work(state.modulus.size(), bound.size(), False, budget)
    if state.modulus.value > bound.value:
        return
    if state.exponent == 0:
        _build_tree(factors, state, budget)
    var exponent = state.exponent
    var power = _copy_coefficient(state.modulus, budget)
    while not power.value > bound.value:
        budget.charge(1)
        _work(power.size(), bound.size(), False, budget)
        power = power.mul(p, budget)
        exponent = _sum(exponent, 1)
    var schedule = List[Int]()
    var e = exponent
    while e > state.exponent:
        budget.charge(1)
        _allocation[Int](1, budget)
        schedule.append(e)
        e = (e + 1) // 2
    var i = len(schedule) - 1
    while i >= 0:
        budget.charge(1)
        var modulus = _pow(p, UInt64(schedule[i]), budget)
        _lift_tree(f, state, modulus, budget)
        state.modulus = modulus^
        state.exponent = schedule[i]
        i -= 1


def _hensel(f: DensePoly[ZZ], factors: List[DensePoly[ModInt]], bound: ZZ, mut budget: Budget) raises PolyError -> Tuple[List[DensePoly[ZZ]], ZZ]:
    var state = _hensel_start(factors, budget)
    _hensel_extend(f, factors, bound, state, budget)
    var lifted = List[DensePoly[ZZ]]()
    var modulus = ZZ.zero(NoContext())
    swap(lifted, state.lifted)
    swap(modulus, state.modulus)
    return (lifted^, modulus^)
