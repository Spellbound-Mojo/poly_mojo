"""Multimodular interpolation through integer nodes of small size.

With nodes x_i in [-X, X] and integer values y_i (rational values are
scaled by the lcm of their denominators), the interpolant is
f = sum_i y_i M_i(x) / W_i with M_i = prod_(j != i) (x - x_j) and
W_i = prod_(j != i) (x_i - x_j). Every prime factor of W_i is at most 2X, and
v_p(W_i) = sum_e #{j != i : x_j = x_i mod p^e}, so counting nodes per
residue class gives D = lcm(W_i) exactly. H = D f is an integer polynomial
with |H_k| <= sum_i |y_i| (D / |W_i|) prod_(j != i) (1 + |x_j|), which fixes
how many word primes suffice. H mod p comes from the native subproduct
tree, Garner's mixed radix recombines the residues, and f = H / D.
"""
from apn_mojo import Integer, Rational, gcd
from std.math import log2
from .coefficients import QQ, NoContext, _prime
from .dense import DensePoly
from .errors import Budget, PolyError, PolyErrorKind, _allocation, _charge_size, _product
from ._nmod import _Field, _field, _mulm, _addm, _subm, _to, _from, _invm
from ._multipoint import _Tree, _inverse_weights, _interpolate

comptime _NODE_BITS = 19
"""Nodes of magnitude below 2^19 keep the residue counts over primes up to 2X cheap."""
comptime _SAFETY_BITS = 8
"""Slack added to the floating-point coefficient bound."""


@fieldwise_init
struct _Scaled(Movable):
    var values: List[Integer]
    var scale: Integer


def _scaled(values: List[QQ]) raises -> _Scaled:
    """Integer values and the lcm of the denominators that scales them."""
    var scale = Integer(1)
    for v in values:
        var d = v.value.denominator()
        if d != Integer(1):
            scale = scale * (d // gcd(scale, d))
    var integers = List[Integer](capacity=len(values))
    for v in values:
        integers.append(v.value.numerator() * (scale // v.value.denominator()))
    return _Scaled(integers^, scale^)


def _small(value: Integer) raises -> Int:
    return Int(value)


def _times_power(value: Integer, p: Int, e: Int) raises -> Integer:
    return value * (Integer(p) ** e)


def _residue(value: Integer, p: UInt64) raises -> UInt64:
    """value mod p in 0 ..< p."""
    return UInt64(Int(value % Integer(Int(p))))


def _product_of(moduli: List[UInt64]) raises -> Integer:
    var result = Integer(1)
    for p in moduli:
        result = result * Integer(Int(p))
    return result^


def _recombine(digits: List[UInt64], moduli: List[UInt64], modulus: Integer, half: Integer, common: Integer) raises -> QQ:
    """sum_j digits[j] q_0 ... q_(j-1), shifted to the symmetric range, over the common denominator."""
    var h = Integer(Int(digits[len(digits) - 1]))
    for j in range(len(digits) - 2, -1, -1):
        h = h * Integer(Int(moduli[j])) + Integer(Int(digits[j]))
    if h > half:
        h = h - modulus
    return QQ(Rational(h, common))


def _primes_upto(limit: Int) -> List[Int]:
    var sieve = List[Bool](length=limit + 1, fill=True)
    var primes = List[Int]()
    for i in range(2, limit + 1):
        if sieve[i]:
            primes.append(i)
            var j = i * i
            while j <= limit:
                sieve[j] = False
                j += i
    return primes^


def _word_primes(count: Int, above: UInt64, mut budget: Budget) raises PolyError -> List[UInt64]:
    """`count` primes below 2^62, from the top down, all above `above`."""
    var primes = List[UInt64](capacity=count)
    var candidate = (UInt64(1) << 62) - 1
    while len(primes) < count:
        if candidate <= above:
            raise PolyError(PolyErrorKind.CAPACITY, "not enough word primes for interpolation")
        if _prime(candidate, budget):
            primes.append(candidate)
        candidate -= 2
    return primes^


def _interpolate_integer_nodes(variable: Int64, points: List[QQ], values: List[QQ], mut budget: Budget) raises PolyError -> Optional[DensePoly[QQ]]:
    """The interpolant through distinct integer nodes of magnitude below 2^_NODE_BITS; None for other data."""
    var n = len(points)
    if n < 2 or len(values) != n:
        return None
    _allocation[Int](n, budget)
    var nodes = List[Int](capacity=n)
    var reach = 0
    var seen = Dict[Int, Int]()
    for x in points:
        budget.charge(1)
        if x.value.denominator() != Integer(1) or x.value.numerator().magnitude_bit_length() > _NODE_BITS:
            return None
        var v: Int
        try:
            v = _small(x.value.numerator())
        except e:
            raise PolyError(PolyErrorKind.CAPACITY, String(e))
        if v in seen:
            return None
        seen[v] = 1
        reach = max(reach, abs(v))
        nodes.append(v)
    # Valuations of every W_i at every prime up to 2X, through residue classes.
    var span = 2 * reach + 1
    var primes = _primes_upto(max(span, 2))
    _charge_size(_product(len(primes) + 1, n), budget)
    var log_w = List[Float64](length=n, fill=0.0)
    var denominator = Integer(1)
    var residue = List[Int](length=n, fill=0)
    var valuation = List[Int](length=n, fill=0)
    for p in primes:
        for i in range(n):
            valuation[i] = 0
        var q = p
        while True:
            var counts = Dict[Int, Int]()
            for i in range(n):
                residue[i] = nodes[i] % q
                counts[residue[i]] = counts.get(residue[i], 0) + 1
            var collided = False
            for i in range(n):
                var c = counts.get(residue[i], 1) - 1
                if c:
                    collided = True
                    valuation[i] += c
            if not collided or q > span // p:
                break
            q *= p
        var most = 0
        var lp = log2(Float64(p))
        for i in range(n):
            if valuation[i]:
                log_w[i] += Float64(valuation[i]) * lp
                most = max(most, valuation[i])
        if most:
            try:
                denominator = _times_power(denominator, p, most)
            except e:
                raise PolyError(PolyErrorKind.CAPACITY, String(e))
    var scaled: _Scaled
    try:
        scaled = _scaled(values)
    except e:
        raise PolyError(PolyErrorKind.CAPACITY, String(e))
    # |H_k| <= sum_i |y_i| (D / |W_i|) prod_(j != i) (1 + |x_j|).
    var log_nodes = 0.0
    for v in nodes:
        log_nodes += log2(1.0 + Float64(abs(v)))
    var log_d = Float64(denominator.magnitude_bit_length())
    var top = 0.0
    for i in range(n):
        if scaled.values[i].sign() == 0:
            continue
        var t = Float64(scaled.values[i].magnitude_bit_length()) + log_d - log_w[i] + log_nodes - log2(1.0 + Float64(abs(nodes[i])))
        top = max(top, t)
    var bits = Int(top + log2(Float64(n))) + _SAFETY_BITS
    var count = (bits + 1) // 61 + 2
    var moduli = _word_primes(count, UInt64(span), budget)
    # Residues of H = D f' for each prime, f' interpolating the scaled values.
    _allocation[List[UInt64]](count, budget)
    var images = List[List[UInt64]](capacity=count)
    for p in moduli:
        budget.charge(1)
        var f = _field(p)
        var xs = List[UInt64](capacity=n)
        var ys = List[UInt64](capacity=n)
        var d: UInt64
        try:
            for i in range(n):
                ys.append(_to(_residue(scaled.values[i], p), f))
            d = _to(_residue(denominator, p), f)
        except e:
            raise PolyError(PolyErrorKind.CAPACITY, String(e))
        for i in range(n):
            var x = UInt64(nodes[i]) if nodes[i] >= 0 else p - UInt64(-nodes[i])
            xs.append(_to(x, f))
        var tree = _Tree(xs^, f, budget)
        var weights = _inverse_weights(tree, f, budget)
        var image = _interpolate(tree, ys, weights, f, budget)
        var plain = List[UInt64](length=n, fill=0)
        for k in range(min(n, len(image))):
            plain[k] = _from(_mulm(image[k], d, f), f)
        images.append(plain^)
    # Garner: H_k = c_0 + c_1 q_0 + c_2 q_0 q_1 + ...; radix[j][i] = q_0 ... q_(i-1) mod q_j.
    _charge_size(_product(_product(count, count), n), budget)
    var fields = List[_Field](capacity=count)
    var radix = List[List[UInt64]](capacity=count)
    var inverses = List[UInt64](capacity=count)
    for j in range(count):
        var f = _field(moduli[j])
        var row = List[UInt64](capacity=j + 1)
        var prefix = f.one
        for i in range(j):
            row.append(prefix)
            prefix = _mulm(prefix, _to(moduli[i] % moduli[j], f), f)
        inverses.append(_invm(prefix, f, budget))
        radix.append(row^)
        fields.append(f)
    var modulus: Integer
    var half: Integer
    var common: Integer
    try:
        modulus = _product_of(moduli)
        half = modulus // Integer(2)
        common = denominator * scaled.scale
    except e:
        raise PolyError(PolyErrorKind.CAPACITY, String(e))
    _allocation[QQ](n, budget)
    var coefficients = List[QQ](capacity=n)
    var digits = List[UInt64](length=count, fill=0)
    for k in range(n):
        budget.charge(UInt64(count))
        for j in range(count):
            ref f = fields[j]
            var acc = UInt64(0)
            for i in range(j):
                acc = _addm(acc, _mulm(_to(digits[i] % moduli[j], f), radix[j][i], f), f)
            digits[j] = _from(_mulm(_subm(_to(images[j][k], f), acc, f), inverses[j], f), f)
        try:
            coefficients.append(_recombine(digits, moduli, modulus, half, common))
        except e:
            raise PolyError(PolyErrorKind.CAPACITY, String(e))
    return DensePoly[QQ].from_coefficients(variable, NoContext(), coefficients^, budget)
