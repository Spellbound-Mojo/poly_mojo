"""Van Hoeij trace-knapsack recombination with exact lattice reduction.

Fresh implementation from Mark van Hoeij (2002), sections 2.1 and 2.2,
DOI 10.1006/jnth.2001.2763. Scaled traces handle nonmonic inputs.
"""
from apn_mojo import Integer
from .coefficients import ZZ, QQ, ModInt, NoContext, _work
from .dense import DensePoly
from .errors import Budget, PolyError, PolyErrorKind, _allocation, _product, _sum
from ._coefficient_ops import _exact, _copy as _zcopy
from ._dense_ops import _copy, _constant
from ._hensel import _HenselState, _hensel_start, _hensel_extend, _truncate, _primitive, _trial_divide, _divmod_monic
from ._dense_ops import _derivative
from .primes import _symmetric
from ._lattice import _lll, _lll_knapsack, _q
from ._root_ops import _compare, _copy as _copy_q


def _greater(a: ZZ, b: ZZ, mut budget: Budget) raises PolyError -> Bool:
    _work(a.size(), b.size(), False, budget)
    return a.value > b.value


def _traces(f: DensePoly[ZZ], count: Int, modulus: ZZ, mut budget: Budget) raises PolyError -> List[ZZ]:
    # Newton sums of the roots of the monic modular factor.
    _allocation[ZZ](_sum(count, 1), budget)
    var sums: List[ZZ] = [ZZ.zero(NoContext())]
    for k in range(1, _sum(count, 1)):
        budget.charge(1)
        var total = ZZ.zero(NoContext())
        for j in range(1, min(k, _sum(f.degree(), 1))):
            budget.charge(1)
            total = total.add(f.coefficients[f.degree() - j].mul(sums[k - j], budget), budget)
            total = ZZ(_symmetric(total.value, modulus.value, budget))
        if k <= f.degree():
            total = total.add(ZZ(Integer(k)).mul(f.coefficients[f.degree() - k], budget), budget)
        sums.append(ZZ(_symmetric(total.neg(budget).value, modulus.value, budget)))
    return sums^


def _projection_rref(basis: List[List[ZZ]], rows: Int, columns: Int, mut budget: Budget) raises PolyError -> List[List[QQ]]:
    _allocation[List[QQ]](rows, budget)
    _allocation[QQ](_product(rows, columns), budget)
    var result = List[List[QQ]]()
    for i in range(rows):
        budget.charge(1)
        var row = List[QQ]()
        for j in range(columns):
            budget.charge(1)
            row.append(_q(basis[i][j], budget))
        result.append(row^)
    var rank = 0
    for column in range(columns):
        budget.charge(1)
        var pivot = rank
        while pivot < rows and result[pivot][column].is_zero():
            budget.charge(1)
            pivot += 1
        if pivot == rows:
            continue
        if pivot != rank:
            var temporary = List[QQ]()
            swap(temporary, result[pivot])
            swap(temporary, result[rank])
            swap(temporary, result[pivot])
        var inverse = result[rank][column].inverse(budget)
        for j in range(column, columns):
            budget.charge(1)
            result[rank][j] = result[rank][j].mul(inverse, budget)
        for i in range(rows):
            budget.charge(1)
            if i == rank or result[i][column].is_zero():
                continue
            var multiplier = _copy_q(result[i][column], budget)
            for j in range(column, columns):
                budget.charge(1)
                result[i][j] = result[i][j].sub(multiplier.mul(result[rank][j], budget), budget)
        rank += 1
        if rank == rows:
            break
    while len(result) > rank:
        budget.charge(1)
        _ = result.pop()
    return result^


def _partition(rows: List[List[QQ]], count: Int, mut budget: Budget) raises PolyError -> Bool:
    var one = QQ.one(NoContext())
    for j in range(count):
        budget.charge(1)
        var occurrences = 0
        for row in rows:
            budget.charge(1)
            if row[j].is_zero():
                continue
            if _compare(row[j], one, budget) != 0:
                return False
            occurrences += 1
        if occurrences != 1:
            return False
    return True


def _shifted_upper(value: Integer, shift: Int) raises PolyError -> Integer:
    """An upper bound on value * 2^shift for value >= 0."""
    try:
        if shift >= 0:
            return value << shift
        return (value >> (-shift)) + Integer(1)
    except e:
        raise PolyError(PolyErrorKind.CAPACITY, String(e))


def _cld_bound(f: DensePoly[ZZ], j: Int, mut budget: Budget) raises PolyError -> ZZ:
    """A bound on |coefficient j of f g'/g| over every factor g of f.

    f g'/g sums f/(x - a) over the roots a of g, and coefficient j of
    f/(x - a) equals sum_(i>j) f_i a^(i-j-1) = -sum_(i<=j) f_i a^(i-j-1). The
    first sum grows with |a| and the second shrinks, so for any t = 2^e the
    larger of the two at t bounds every root; deg(f) times it bounds the sum.
    The exponent e is chosen near the crossing from bit lengths.
    """
    var n = f.degree()
    var bits = List[Int](capacity=n + 1)
    for i in range(n + 1):
        bits.append(f.coefficients[i].value.magnitude_bit_length())
    var hi = 0
    for b in bits:
        hi = max(hi, b + 64)
    var lo = -hi
    # Smallest e whose estimated first sum reaches the second.
    while lo < hi:
        budget.charge(1)
        var mid = (lo + hi) // 2 if (lo + hi) >= 0 else -((-(lo + hi) + 1) // 2)
        var la = -1 << 30
        var lb = -1 << 30
        for i in range(n + 1):
            if bits[i] == 0:
                continue
            var size = bits[i] + mid * (i - j - 1)
            if i > j:
                la = max(la, size)
            else:
                lb = max(lb, size)
        if la >= lb:
            hi = mid
        else:
            lo = mid + 1
    var best = ZZ.zero(NoContext())
    var found = False
    for e in [lo - 1, lo]:
        _work(n, 1, False, budget)
        var first = Integer(0)
        var second = Integer(0)
        for i in range(n + 1):
            var magnitude = f.coefficients[i].value.copy()
            if magnitude.sign() == 0:
                continue
            if magnitude.sign() < 0:
                magnitude = -magnitude
            var term = _shifted_upper(magnitude, e * (i - j - 1))
            try:
                if i > j:
                    first = first + term
                else:
                    second = second + term
            except err:
                raise PolyError(PolyErrorKind.CAPACITY, String(err))
        var larger = ZZ(first.copy() if first > second else second.copy())
        if not found or _greater(best, larger, budget):
            best = larger^
            found = True
    return best.mul(ZZ(Integer(n)), budget)


def _reconstruct(f: DensePoly[ZZ], partition: List[List[QQ]], leading: ZZ, state: _HenselState, mut budget: Budget) raises PolyError -> Optional[List[DensePoly[ZZ]]]:
    """The factors lc(f) prod_(j in group) g_j modulo the lifted modulus,
    when every one divides f exactly with its group's degree."""
    var remaining = _copy(f, budget)
    var factors = List[DensePoly[ZZ]]()
    for row in partition:
        budget.charge(1)
        var candidate = _constant(f, leading, budget)
        var degree = 0
        for j in range(len(row)):
            budget.charge(1)
            if not row[j].is_zero():
                degree = _sum(degree, state.lifted[j].degree())
                candidate = _truncate(candidate.mul(state.lifted[j], budget), state.modulus, budget)
        candidate = _primitive(candidate, budget)
        if candidate.degree() != degree or degree < 1:
            return None
        var quotient = _trial_divide(remaining, candidate, budget)
        if not quotient:
            return None
        remaining = quotient.take()
        _allocation[DensePoly[ZZ]](1, budget)
        factors.append(candidate^)
    if remaining.degree() != 0:
        return None
    return factors^


def _lattice_precision(f: DensePoly[ZZ], count: Int, p: ZZ, mut budget: Budget) raises PolyError -> Optional[ZZ]:
    """The modulus the first CLD lattice round lifts to, or no value when the
    lattice would use traces."""
    ref lc = f.coefficients[f.degree()]
    if lc.value.magnitude_bit_length() < 1024 or f.degree() < 300:
        return None
    var padding = _zcopy(p, budget)
    while padding.value.magnitude_bit_length() < _sum(count, 20):
        budget.charge(1)
        padding = padding.mul(p, budget)
    var largest_cut = ZZ.one(NoContext())
    for index in [0, f.degree() - 1]:
        budget.charge(1)
        var bound = _cld_bound(f, index, budget).mul(ZZ(Integer(2)), budget)
        var cut = ZZ.one(NoContext())
        while not _greater(cut, bound, budget):
            budget.charge(1)
            cut = cut.mul(p, budget)
        if _greater(cut, largest_cut, budget):
            largest_cut = cut^
    return largest_cut.mul(padding, budget)


def _van_hoeij(f: DensePoly[ZZ], images: List[DensePoly[ModInt]], reconstruction_bound: ZZ, mut budget: Budget) raises PolyError -> List[DensePoly[ZZ]]:
    var state = _hensel_start(images, budget)
    return _van_hoeij_lifted(f, images, reconstruction_bound, state, budget)


def _van_hoeij_lifted(f: DensePoly[ZZ], images: List[DensePoly[ModInt]], reconstruction_bound: ZZ, mut state: _HenselState, mut budget: Budget) raises PolyError -> List[DensePoly[ZZ]]:
    var count = len(images)
    if count < 2 or f.degree() < 2:
        raise PolyError(PolyErrorKind.DOMAIN, "lattice recombination requires at least two modular factors")
    var p = ZZ(Integer(Int(images[0].ring.value)))
    var root_bound = ZZ.zero(NoContext())
    for coefficient_index in range(len(f.coefficients)):
        ref coefficient = f.coefficients[coefficient_index]
        budget.charge(1)
        var magnitude = coefficient.neg(budget) if coefficient.value.sign() < 0 else _zcopy(coefficient, budget)
        if _greater(magnitude, root_bound, budget):
            root_bound = magnitude^
    ref lc = f.coefficients[f.degree()]
    var leading = lc.neg(budget) if lc.value.sign() < 0 else _zcopy(lc, budget)
    root_bound = root_bound.add(leading, budget)
    # Power sums of the roots need precision about (|lc|+max|f_i|)^k for
    # the k-th one. With a large leading coefficient and degree, that drives
    # lifting far beyond the reconstruction bound, and coefficients of the
    # logarithmic derivative (CLD), bounded near the size of f, are cheaper.
    var monic = leading.value.magnitude_bit_length() < 1024 or f.degree() < 300
    # Gradual feeding: the reduced basis rows persist, and each round
    # appends only new trace columns, each at its own precision
    # cut_j * padding, so every new entry is about the padding in size. Rows whose exact Gram-Schmidt norm exceeds the bound
    # for true indicators are dropped, which never loses one.
    _allocation[List[ZZ]](count, budget)
    var rows = List[List[ZZ]](length=count, fill=List[ZZ](length=count, fill=ZZ.zero(NoContext())))
    for i in range(count):
        rows[i][i] = ZZ.one(NoContext())
    var done = 0
    var data_columns = 0
    var traces_count = min(f.degree(), 2)
    # CLD indices from both ends inward: 0, n-1, 1, n-2, ...
    var order = List[Int]()
    var low_index = 0
    var high_index = f.degree() - 1
    while low_index <= high_index:
        order.append(low_index)
        if high_index != low_index:
            order.append(high_index)
        low_index += 1
        high_index -= 1
    # Each column must add clearly more than about one bit per modular factor,
    # or LLL cannot push the false indicators above the bound.
    var padding = _zcopy(p, budget)
    while padding.value.magnitude_bit_length() < _sum(count, 20):
        budget.charge(1)
        padding = padding.mul(p, budget)
    while True:
        budget.charge(1)
        var fresh = traces_count - done
        _allocation[List[ZZ]](count, budget)
        var columns = List[List[ZZ]](capacity=count)
        if monic:
            # For a rational factor, lc(f)^k * Tr_k is an integer with
            # absolute value at most degree(f)*(|lc(f)|+max |f_i|)^k.
            _allocation[ZZ](traces_count, budget)
            var cuts = List[ZZ]()
            var power = ZZ.one(NoContext())
            var largest_cut = ZZ.one(NoContext())
            for _ in range(traces_count):
                budget.charge(1)
                power = power.mul(root_bound, budget)
                var bound = power.mul(ZZ(Integer(_product(2, f.degree()))), budget)
                var cut = ZZ.one(NoContext())
                while not _greater(cut, bound, budget):
                    budget.charge(1)
                    cut = cut.mul(p, budget)
                largest_cut = _zcopy(cut, budget)
                cuts.append(cut^)
            var target = largest_cut.mul(padding, budget)
            _hensel_extend(f, images, target, state, budget)
            ref lifted = state.lifted
            ref modulus = state.modulus
            # columns[i][j] = (lc^(j+1) Tr_(j+1)(g_i) mod cut_j*padding - low) / cut_j.
            for i in range(count):
                budget.charge(1)
                var sums = _traces(lifted[i], traces_count, modulus, budget)
                var scale = ZZ.one(NoContext())
                var row = List[ZZ](capacity=fresh)
                for j in range(traces_count):
                    budget.charge(1)
                    scale = ZZ(_symmetric(scale.mul(leading, budget).value, modulus.value, budget))
                    if j < done:
                        continue
                    var precision = cuts[j].mul(padding, budget)
                    var trace = ZZ(_symmetric(sums[j + 1].mul(scale, budget).value, precision.value, budget))
                    var low = ZZ(_symmetric(trace.value, cuts[j].value, budget))
                    row.append(_exact(trace.sub(low, budget), cuts[j], budget))
                columns.append(row^)
        else:
            # Data columns are coefficients of the logarithmic derivative
            # f g'/g = g' (f/g), additive over modular factors and bounded by
            # about the size of f's coefficients for every index (CLD).
            _allocation[ZZ](traces_count, budget)
            var cuts = List[ZZ]()
            var largest_cut = ZZ.one(NoContext())
            for k in range(traces_count):
                budget.charge(1)
                var bound = _cld_bound(f, order[k], budget).mul(ZZ(Integer(2)), budget)
                var cut = ZZ.one(NoContext())
                while not _greater(cut, bound, budget):
                    budget.charge(1)
                    cut = cut.mul(p, budget)
                if _greater(cut, largest_cut, budget):
                    largest_cut = _zcopy(cut, budget)
                cuts.append(cut^)
            var target = largest_cut.mul(padding, budget)
            _hensel_extend(f, images, target, state, budget)
            ref lifted = state.lifted
            ref modulus = state.modulus
            # columns[i][k] = (coefficient order[k] of g_i' f/g_i mod cut_k*padding - low) / cut_k.
            for i in range(count):
                budget.charge(1)
                var quotient = _divmod_monic(f, lifted[i], modulus, budget)[0].copy()
                var cld = _truncate(_derivative(lifted[i], budget).mul(quotient, budget), modulus, budget)
                var row = List[ZZ](capacity=fresh)
                for k in range(done, traces_count):
                    budget.charge(1)
                    var index = order[k]
                    var value = cld.coefficients[index].copy() if index < len(cld.coefficients) else ZZ.zero(NoContext())
                    var precision = cuts[k].mul(padding, budget)
                    var data = ZZ(_symmetric(value.value, precision.value, budget))
                    var low = ZZ(_symmetric(data.value, cuts[k].value, budget))
                    row.append(_exact(data.sub(low, budget), cuts[k], budget))
                columns.append(row^)
        var dimension = _sum(len(rows), fresh)
        var old = len(rows[0])
        var width = _sum(old, fresh)
        _allocation[ZZ](_product(dimension, width), budget)
        var lattice = List[List[ZZ]](length=dimension, fill=List[ZZ](length=width, fill=ZZ.zero(NoContext())))
        for a in range(len(rows)):
            budget.charge(1)
            for i in range(old):
                lattice[a][i] = rows[a][i].copy()
            for j in range(fresh):
                budget.charge(1)
                var total = ZZ.zero(NoContext())
                for i in range(count):
                    if not rows[a][i].is_zero():
                        total = total.add(rows[a][i].mul(columns[i][j], budget), budget)
                lattice[a][old + j] = ZZ(_symmetric(total.value, padding.value, budget))
        for j in range(fresh):
            budget.charge(1)
            lattice[len(rows) + j][old + j] = _zcopy(padding, budget)
        var reduced = _lll_knapsack(lattice, budget)
        # Each true factor's indicator has norm squared <= n+s*n^2/4.
        # The looser integer bound avoids rounding. Dropping only a suffix
        # of larger Gram-Schmidt norms retains every such short vector.
        data_columns = _sum(data_columns, fresh)
        var bound_squared = _q(ZZ(Integer(_sum(count, _product(data_columns, _product(count, count))))), budget)
        var retained = dimension
        while retained and _compare(reduced.norms[retained - 1], bound_squared, budget) > 0:
            budget.charge(1)
            retained -= 1
        if retained == 0:
            raise PolyError(PolyErrorKind.DOMAIN, "lattice reduction lost every factor indicator")
        _allocation[List[ZZ]](retained, budget)
        var kept = List[List[ZZ]](capacity=retained)
        for a in range(retained):
            budget.charge(1)
            kept.append(reduced.basis[a].copy())
        rows = kept^
        done = traces_count
        var partition = _projection_rref(rows, len(rows), count, budget)
        if _partition(partition, count, budget):
            # Try the lattice's precision first. A divisor of f with the
            # modular image of a group and its full degree is the unique
            # such factor, so a lower precision cannot change the answer.
            var factors = _reconstruct(f, partition, leading, state, budget)
            # Lift for the full bound only once the lattice has merged some
            # factors or holds every column; until then, feed it further.
            var settled = len(partition) < count or traces_count >= f.degree()
            if not factors and settled and _greater(reconstruction_bound, state.modulus, budget):
                _hensel_extend(f, images, reconstruction_bound, state, budget)
                factors = _reconstruct(f, partition, leading, state, budget)
            if factors:
                return factors.take()
        if traces_count < f.degree():
            traces_count = min(f.degree(), _product(2, traces_count))
        else:
            # Every trace is in; feed them again with more precision.
            padding = padding.mul(p, budget)
            done = 0
