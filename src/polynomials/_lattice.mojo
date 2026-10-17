"""Exact rational Gram-Schmidt and integer LLL for van Hoeij recombination.

Fresh implementation of the lattice step in van Hoeij (2002), section 2.1.
All Gram-Schmidt calculations are exact and fraction-free; no floating-point
decisions occur.
"""
from apn_mojo import Rational, Integer, div_rem_floor
from .coefficients import ZZ, QQ, NoContext, _work
from .errors import Budget, PolyError, PolyErrorKind, _allocation, _product, _charge_size
from ._root_ops import _compare
from ._coefficient_ops import _copy


@fieldwise_init
struct _Orthogonal(Movable):
    var mu: List[List[QQ]]
    var norms: List[QQ]


@fieldwise_init
struct _LLL(Movable):
    var basis: List[List[ZZ]]
    var transform: List[List[ZZ]]
    var mu: List[List[QQ]]
    var norms: List[QQ]


def _q(a: ZZ, mut budget: Budget) raises PolyError -> QQ:
    _charge_size(a.size(), budget)
    return QQ(Rational(a.value.copy()))


def _copy_matrix(a: List[List[ZZ]], mut budget: Budget) raises PolyError -> List[List[ZZ]]:
    _allocation[List[ZZ]](len(a), budget)
    var result = List[List[ZZ]]()
    for row in a:
        budget.charge(1)
        _allocation[ZZ](len(row), budget)
        var copied = List[ZZ]()
        for value in row:
            _charge_size(value.size(), budget)
            copied.append(value.copy())
        result.append(copied^)
    return result^


def _orthogonal(a: List[List[ZZ]], mut budget: Budget) raises PolyError -> _Orthogonal:
    var rows = len(a)
    var columns = len(a[0])
    _allocation[List[QQ]](rows, budget)
    _allocation[QQ](_product(rows, rows), budget)
    _allocation[QQ](_product(rows, columns), budget)
    _allocation[QQ](rows, budget)
    var mu = List[List[QQ]](length=rows, fill=List[QQ](length=rows, fill=QQ.zero(NoContext())))
    var orthogonal = List[List[QQ]]()
    var norms = List[QQ]()
    _allocation[QQ](rows, budget)
    var inverse_norms = List[QQ](capacity=rows)
    for i in range(rows):
        budget.charge(1)
        var vector = List[QQ]()
        for value in a[i]:
            budget.charge(1)
            vector.append(_q(value, budget))
        for j in range(i):
            budget.charge(1)
            var dot = QQ.zero(NoContext())
            for k in range(columns):
                budget.charge(1)
                dot = dot.add(_q(a[i][k], budget).mul(orthogonal[j][k], budget), budget)
            mu[i][j] = dot.mul(inverse_norms[j], budget)
            for k in range(columns):
                budget.charge(1)
                vector[k] = vector[k].sub(mu[i][j].mul(orthogonal[j][k], budget), budget)
        var norm = QQ.zero(NoContext())
        for value in vector:
            budget.charge(1)
            norm = norm.add(value.mul(value, budget), budget)
        if norm.is_zero():
            raise PolyError(PolyErrorKind.DOMAIN, "LLL requires independent nonzero rows")
        if i + 1 < rows:
            inverse_norms.append(norm.inverse(budget))
        norms.append(norm^)
        orthogonal.append(vector^)
    return _Orthogonal(mu^, norms^)


def _nearest(q: QQ, mut budget: Budget) raises PolyError -> ZZ:
    _work(q.size(), 1, True, budget)
    try:
        return ZZ(q.value.round())
    except e:
        raise PolyError(PolyErrorKind.CAPACITY, String(e))


def _swap_rows(mut a: List[List[ZZ]], i: Int, j: Int):
    var temporary = List[ZZ]()
    swap(temporary, a[i])
    swap(temporary, a[j])
    swap(temporary, a[i])


def _imul(a: Integer, b: Integer, mut budget: Budget) raises PolyError -> Integer:
    _work(a.magnitude_bit_length() // 64 + 1, b.magnitude_bit_length() // 64 + 1, True, budget)
    try:
        return a * b
    except e:
        raise PolyError(PolyErrorKind.CAPACITY, String(e))


def _iadd(a: Integer, b: Integer, subtract: Bool, mut budget: Budget) raises PolyError -> Integer:
    _work(a.magnitude_bit_length() // 64 + 1, b.magnitude_bit_length() // 64 + 1, False, budget)
    try:
        return a - b if subtract else a + b
    except e:
        raise PolyError(PolyErrorKind.CAPACITY, String(e))


def _ratio(a: Integer, b: Integer, mut budget: Budget) raises PolyError -> QQ:
    _work(a.magnitude_bit_length() // 64 + 1, b.magnitude_bit_length() // 64 + 1, True, budget)
    try:
        return QQ(Rational(a.copy(), b.copy()))
    except e:
        raise PolyError(PolyErrorKind.CAPACITY, String(e))


def _iexact(a: Integer, b: Integer, mut budget: Budget) raises PolyError -> Integer:
    """The exact quotient a / b of the fraction-free recurrences."""
    _work(a.magnitude_bit_length() // 64 + 1, b.magnitude_bit_length() // 64 + 1, True, budget)
    try:
        return div_rem_floor(a, b)[0].copy()
    except e:
        raise PolyError(PolyErrorKind.CAPACITY, String(e))


def _rounded(a: Integer, d: Integer, mut budget: Budget) raises PolyError -> Integer:
    """floor(a / d + 1/2) for d > 0."""
    _work(a.magnitude_bit_length() // 64 + 1, d.magnitude_bit_length() // 64 + 1, True, budget)
    try:
        return div_rem_floor(a + a + d, d + d)[0].copy()
    except e:
        raise PolyError(PolyErrorKind.CAPACITY, String(e))


def _row_dot(a: List[ZZ], b: List[ZZ], mut budget: Budget) raises PolyError -> Integer:
    var total = Integer(0)
    for i in range(len(a)):
        budget.charge(1)
        if a[i].value.sign() == 0 or b[i].value.sign() == 0:
            continue
        total = _iadd(total, _imul(a[i].value, b[i].value, budget), False, budget)
    return total^


def _reduce[carry: Bool](k: Int, l: Int, mut basis: List[List[ZZ]], mut transform: List[List[ZZ]], mut lam: List[List[Integer]], d: List[Integer], mut budget: Budget) raises PolyError:
    budget.charge(1)
    var twice = _iadd(lam[k][l], lam[k][l], False, budget)
    if twice.sign() < 0:
        twice = -twice
    if not (twice > d[l + 1]):
        return
    var q = _rounded(lam[k][l], d[l + 1], budget)
    var zq = ZZ(q.copy())
    for column in range(len(basis[k])):
        budget.charge(1)
        if basis[l][column].value.sign() != 0:
            basis[k][column] = basis[k][column].sub(zq.mul(basis[l][column], budget), budget)
    comptime if carry:
        for column in range(len(transform[k])):
            budget.charge(1)
            if transform[l][column].value.sign() != 0:
                transform[k][column] = transform[k][column].sub(zq.mul(transform[l][column], budget), budget)
    lam[k][l] = _iadd(lam[k][l], _imul(q, d[l + 1], budget), True, budget)
    for i in range(l):
        budget.charge(1)
        if lam[l][i].sign() != 0:
            lam[k][i] = _iadd(lam[k][i], _imul(q, lam[l][i], budget), True, budget)


def _lll[carry: Bool = True](input: List[List[ZZ]], mut budget: Budget) raises PolyError -> _LLL:
    """Integral LLL with delta 3/4 (Cohen, Algorithm 2.6.7, de Weger).

    Gram-Schmidt data stay exact as the integers d_i (leading Gram
    determinants) and lambda_kj = d_(j+1) mu_kj, so no rational gcds occur;
    every decision equals the rational algorithm's.
    """
    if len(input) == 0 or len(input) > len(input[0]):
        raise PolyError(PolyErrorKind.DOMAIN, "LLL requires a nonempty full-row-rank matrix")
    var rows = len(input)
    var columns = len(input[0])
    for row in input:
        budget.charge(1)
        if len(row) != columns:
            raise PolyError(PolyErrorKind.DOMAIN, "LLL matrix has unequal row lengths")
    var basis = _copy_matrix(input, budget)
    var transform = List[List[ZZ]]()
    comptime if carry:
        _allocation[List[ZZ]](rows, budget)
        _allocation[ZZ](_product(rows, rows), budget)
        transform = List[List[ZZ]](length=rows, fill=List[ZZ](length=rows, fill=ZZ.zero(NoContext())))
        for i in range(rows):
            budget.charge(1)
            transform[i][i] = ZZ.one(NoContext())
    _allocation[Integer](_product(rows, rows), budget)
    var lam = List[List[Integer]](length=rows, fill=List[Integer](length=rows, fill=Integer(0)))
    # d[i] is the Gram determinant of the first i rows; d[0] = 1.
    var d = List[Integer](length=rows + 1, fill=Integer(0))
    d[0] = Integer(1)

    var kmax = 0
    d[1] = _row_dot(basis[0], basis[0], budget)
    if d[1].sign() == 0:
        raise PolyError(PolyErrorKind.DOMAIN, "LLL requires independent nonzero rows")
    var k = 1
    while k < rows:
        budget.charge(1)
        if k > kmax:
            kmax = k
            for j in range(k + 1):
                budget.charge(1)
                var u = _row_dot(basis[k], basis[j], budget)
                for i in range(j):
                    u = _iexact(_iadd(_imul(d[i + 1], u, budget), _imul(lam[k][i], lam[j][i], budget), True, budget), d[i], budget)
                if j < k:
                    lam[k][j] = u^
                else:
                    if u.sign() == 0:
                        raise PolyError(PolyErrorKind.DOMAIN, "LLL requires independent nonzero rows")
                    d[k + 1] = u^
        _reduce[carry](k, k - 1, basis, transform, lam, d, budget)
        var left = _imul(_imul(Integer(4), d[k + 1], budget), d[k - 1], budget)
        var right = _iadd(_imul(_imul(Integer(3), d[k], budget), d[k], budget), _imul(_imul(Integer(4), lam[k][k - 1], budget), lam[k][k - 1], budget), True, budget)
        if left < right:
            _swap_rows(basis, k, k - 1)
            comptime if carry:
                _swap_rows(transform, k, k - 1)
            for j in range(k - 1):
                budget.charge(1)
                var t = lam[k][j].copy()
                lam[k][j] = lam[k - 1][j].copy()
                lam[k - 1][j] = t^
            var l = lam[k][k - 1].copy()
            var b = _iexact(_iadd(_imul(d[k - 1], d[k + 1], budget), _imul(l, l, budget), False, budget), d[k], budget)
            for i in range(k + 1, kmax + 1):
                budget.charge(1)
                var t = lam[i][k].copy()
                lam[i][k] = _iexact(_iadd(_imul(d[k + 1], lam[i][k - 1], budget), _imul(l, t, budget), True, budget), d[k], budget)
                lam[i][k - 1] = _iexact(_iadd(_imul(b, t, budget), _imul(l, lam[i][k], budget), False, budget), d[k + 1], budget)
            d[k] = b^
            k = max(k - 1, 1)
        else:
            var l = k - 2
            while l >= 0:
                _reduce[carry](k, l, basis, transform, lam, d, budget)
                l -= 1
            k += 1
    _allocation[QQ](_product(rows, rows), budget)
    var mu = List[List[QQ]](length=rows, fill=List[QQ](length=rows, fill=QQ.zero(NoContext())))
    var norms = List[QQ](capacity=rows)
    for i in range(rows):
        budget.charge(1)
        for j in range(i):
            mu[i][j] = _ratio(lam[i][j], d[j + 1], budget)
        norms.append(_ratio(d[i + 1], d[i], budget))
    return _LLL(basis^, transform^, mu^, norms^)


def _to_float(a: Integer) raises PolyError -> Float64:
    var bits = a.magnitude_bit_length()
    try:
        if bits <= 62:
            return Float64(Int(a))
        var shift = bits - 62
        return Float64(Int(a >> shift)) * (Float64(2.0) ** Float64(shift))
    except e:
        raise PolyError(PolyErrorKind.CAPACITY, String(e))


def _from_float(x: Float64) raises PolyError -> Integer:
    """The integer nearest x (half away from zero)."""
    var r = x + 0.5 if x >= 0 else x - 0.5
    var magnitude = r if r >= 0 else -r
    if magnitude < 4.0e18:
        return Integer(Int(r))
    var shift = 0
    while magnitude >= 4.0e18:
        magnitude *= 0.5
        shift += 1
    try:
        var value = Integer(Int(magnitude)) << shift
        return -value if r < 0 else value^
    except e:
        raise PolyError(PolyErrorKind.CAPACITY, String(e))


def _float_vector(row: List[ZZ], mut budget: Budget) raises PolyError -> List[Float64]:
    _allocation[Float64](len(row), budget)
    var result = List[Float64](capacity=len(row))
    for value in row:
        budget.charge(1)
        result.append(_to_float(value.value))
    return result^


def _float_row(k: Int, fb: List[List[Float64]], mut r: List[List[Float64]], mut mu: List[List[Float64]], mut budget: Budget) raises PolyError:
    # Floating Gram-Schmidt for row k from floating copies of the exact rows.
    var n = len(fb[k])
    _charge_size(_product(k + 1, n), budget)
    for j in range(k + 1):
        var value = Float64(0)
        for c in range(n):
            value += fb[k][c] * fb[j][c]
        for i in range(j):
            value -= mu[j][i] * r[k][i]
        r[k][j] = value
        if j < k:
            mu[k][j] = value / r[j][j] if r[j][j] != 0 else 0.0


def _exact_norms(basis: List[List[ZZ]], mut budget: Budget) raises PolyError -> List[QQ]:
    """Exact squared Gram-Schmidt norms by the fraction-free recurrence."""
    var rows = len(basis)
    _allocation[Integer](_product(rows, rows), budget)
    var lam = List[List[Integer]](length=rows, fill=List[Integer](length=rows, fill=Integer(0)))
    var d = List[Integer](length=rows + 1, fill=Integer(0))
    d[0] = Integer(1)
    var norms = List[QQ](capacity=rows)
    for k in range(rows):
        budget.charge(1)
        for j in range(k + 1):
            budget.charge(1)
            var u = _row_dot(basis[k], basis[j], budget)
            for i in range(j):
                u = _iexact(_iadd(_imul(d[i + 1], u, budget), _imul(lam[k][i], lam[j][i], budget), True, budget), d[i], budget)
            if j < k:
                lam[k][j] = u^
            else:
                if u.sign() == 0:
                    raise PolyError(PolyErrorKind.DOMAIN, "LLL requires independent nonzero rows")
                d[k + 1] = u^
        norms.append(_ratio(d[k + 1], d[k], budget))
    return norms^


def _lll_knapsack(input: List[List[ZZ]], mut budget: Budget) raises PolyError -> _LLL:
    """LLL steered by floating-point Gram-Schmidt data, with exact norms.

    Row operations are exact integer ones, so the result is always a basis
    of the input lattice; floating point only chooses them. The returned
    squared norms are recomputed exactly, so every decision a caller bases
    on them is rigorous. A deterministic iteration cap falls back to the
    exact integral algorithm when floating point stalls.
    """
    if len(input) == 0 or len(input) > len(input[0]):
        raise PolyError(PolyErrorKind.DOMAIN, "LLL requires a nonempty full-row-rank matrix")
    var rows = len(input)
    var basis = _copy_matrix(input, budget)
    _allocation[Float64](_product(2 * rows, rows), budget)
    var r = List[List[Float64]](length=rows, fill=List[Float64](length=rows, fill=0.0))
    var mu = List[List[Float64]](length=rows, fill=List[Float64](length=rows, fill=0.0))
    var fb = List[List[Float64]](capacity=rows)
    for row in basis:
        fb.append(_float_vector(row, budget))
    _float_row(0, fb, r, mu, budget)
    var k = 1
    var iterations = 0
    var cap = 10000 + 100 * rows * rows
    while k < rows:
        budget.charge(1)
        iterations += 1
        if iterations > cap:
            return _lll[False](input, budget)
        var rounds = 0
        while True:
            budget.charge(1)
            _float_row(k, fb, r, mu, budget)
            var reduced = False
            var j = k - 1
            while j >= 0:
                if mu[k][j] > 0.51 or mu[k][j] < -0.51:
                    var x = _from_float(mu[k][j])
                    var zx = ZZ(x.copy())
                    for column in range(len(basis[k])):
                        budget.charge(1)
                        if basis[j][column].value.sign() != 0:
                            basis[k][column] = basis[k][column].sub(zx.mul(basis[j][column], budget), budget)
                    var fx = _to_float(x)
                    for i in range(j):
                        mu[k][i] -= fx * mu[j][i]
                    mu[k][j] -= fx
                    reduced = True
                j -= 1
            if reduced:
                fb[k] = _float_vector(basis[k], budget)
            rounds += 1
            if not reduced or rounds > 50:
                break
        var lhs = 0.99 * r[k - 1][k - 1]
        var rhs = r[k][k] + mu[k][k - 1] * mu[k][k - 1] * r[k - 1][k - 1]
        if lhs > rhs:
            _swap_rows(basis, k, k - 1)
            var held = fb[k].copy()
            fb[k] = fb[k - 1].copy()
            fb[k - 1] = held^
            _float_row(k - 1, fb, r, mu, budget)
            k = max(k - 1, 1)
        else:
            k += 1
    var norms = _exact_norms(basis, budget)
    return _LLL(basis^, List[List[ZZ]](), List[List[QQ]](), norms^)
