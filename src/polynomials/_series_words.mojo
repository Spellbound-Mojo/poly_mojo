"""Quadratic prime-field series recurrences on native residue words.

Quotients (inverses) and exponentials of short prime-field series by their
defining recurrences, on Montgomery residues. Each coefficient's inner
product is one _series_dot: _nmod._dot for primes below 2^28 (SIMD lanes)
and short runs, otherwise one 192-bit accumulation reduced once. These are
the only quadratic recurrences for these operations: _series_nmod uses them
below the measured crossovers and as its Newton iterations' seeds, and the
generic toolkit uses them for prime fields too. Budget charges follow the
generic recurrences' operation counts.
"""
from .errors import Budget, PolyError, _charge_size, _product, _sum
from .errors import _allocation
from ._nmod import _Field, _to, _from, _redc, _mulm, _addm, _subm, _negm, _invm, _dot, _SMALL

comptime _INVERSE_WORDS = 1536
"""Orders below which series inverses run the quadratic recurrence; Newton wins above (measured)."""
comptime _EXP_WORDS = 3072
"""The same for exponentials."""


@always_inline
def _wide_mod(low: UInt128, carry: UInt64, p: UInt64, wrap: UInt64) -> UInt64:
    """(carry * 2^128 + low) mod p, given wrap = 2^128 mod p."""
    var r = UInt64(low % UInt128(p))
    if carry:
        r = UInt64((UInt128(r) + UInt128(carry) * UInt128(wrap)) % UInt128(p))
    return r


def _wrap(p: UInt64) -> UInt64:
    var r = UInt64((UInt128(1) << 64) % UInt128(p))
    return UInt64((UInt128(r) * UInt128(r)) % UInt128(p))


def _naturals(n: Int, f: _Field, mut budget: Budget) raises PolyError -> List[UInt64]:
    """Montgomery inverses of 1 ... n - 1 (index 0 unused), for n - 1 < p."""
    _allocation[UInt64](max(n, 1), budget)
    var plain = List[UInt64](length=max(n, 2), fill=0)
    plain[1] = 1
    # 1/k = -(p // k) * (1 / (p mod k)) mod p.
    for k in range(2, n):
        var q = UInt64(f.p // UInt64(k))
        plain[k] = UInt64((UInt128(f.p - q) * UInt128(plain[Int(f.p % UInt64(k))])) % UInt128(f.p))
    var result = List[UInt64](length=max(n, 1), fill=0)
    for k in range(1, n):
        result[k] = _to(plain[k], f)
    _charge_size(n, budget)
    return result^


def _series_dot(x: Pointer[mut=False, UInt64, _], y: Pointer[mut=False, UInt64, _], count: Int, f: _Field, wrap: UInt64) -> UInt64:
    """The Montgomery sum of x_i y_i for Montgomery residues x, y."""
    if f.p < _SMALL or count < 16:
        return _dot(x, y, count, f)
    var low = UInt128(0)
    var carry = UInt64(0)
    for i in range(count):
        var t = low + UInt128(x.unsafe_offset(i).unsafe_load()) * UInt128(y.unsafe_offset(i).unsafe_load())
        carry += UInt64(1) if t < low else UInt64(0)
        low = t
    # The sum of (a R)(b R) is (sum a b) R^2: one reduction modulo p, one REDC.
    return _redc(UInt128(_wide_mod(low, carry, f.p, wrap)), f)


def _recurrence_work(n: Int, width: Int, per_term: Int) raises PolyError -> Int:
    """sum over m < n of per_term * min(m, width - 1) + 2: the recurrences' operation count, charged once."""
    var w = max(0, width - 1)
    var full = max(0, n - w)
    var ramp = min(n, w)
    # m < w contributes m terms; every later m contributes w.
    return _sum(_product(per_term, _sum(ramp * (ramp - 1) // 2, _product(full, w))), _product(2, n))


def _reversed_prefix(a: List[UInt64], n: Int) -> List[UInt64]:
    """The first n coefficients of a, zero-padded, in reverse order."""
    var out = List[UInt64](length=n, fill=0)
    for i in range(min(n, len(a))):
        out.unsafe_get(n - 1 - i) = a.unsafe_get(i)
    return out^


def _word_divide(numerator: List[UInt64], b: List[UInt64], n: Int, f: _Field, mut budget: Budget) raises PolyError -> List[UInt64]:
    """numerator / b modulo x^n on Montgomery residues, for b[0] a unit: g_m = (numerator_m - sum_(j>=1) b_j g_(m-j)) / b_0."""
    var inverse = _invm(b[0], f, budget)
    # Only the 192-bit dot products need 2^128 mod p.
    var wrap = _wrap(f.p) if f.p >= _SMALL and n > 16 else UInt64(0)
    _charge_size(_recurrence_work(n, len(b), 2), budget)
    var reversed = _reversed_prefix(b, n)
    var g = List[UInt64](capacity=n)
    for m in range(n):
        # Terms j = 1 ... min(m, len(b) - 1), as reversed[n - 1 - m + i] * g[i].
        var first = max(0, m - (len(b) - 1))
        var terms = m - first
        var s = _series_dot(reversed.unsafe_ptr().unsafe_offset(n - 1 - m + first), g.unsafe_ptr().unsafe_offset(first), terms, f, wrap) if terms else UInt64(0)
        var value = numerator[m] if m < len(numerator) else UInt64(0)
        g.append(_mulm(_subm(value, s, f), inverse, f))
    return g^


def _word_exp(a: List[UInt64], n: Int, naturals: List[UInt64], f: _Field, mut budget: Budget) raises PolyError -> List[UInt64]:
    """exp(a) modulo x^n on Montgomery residues, a(0) = 0, given the Montgomery inverses of 1 ... n - 1: m g_m = sum k a_k g_(m-k)."""
    var wrap = _wrap(f.p) if f.p >= _SMALL and n > 16 else UInt64(0)
    var la = min(len(a), n)
    _charge_size(_recurrence_work(n, la, 4), budget)
    var weighted = List[UInt64](length=la, fill=0)
    var k = UInt64(0)
    for i in range(1, la):
        k = _addm(k, f.one, f)
        weighted[i] = _mulm(a[i], k, f)
    var reversed = _reversed_prefix(weighted, n)
    var g = List[UInt64](capacity=n)
    g.append(f.one)
    for m in range(1, n):
        var first = max(0, m - (la - 1))
        var terms = m - first
        var s = _series_dot(reversed.unsafe_ptr().unsafe_offset(n - 1 - m + first), g.unsafe_ptr().unsafe_offset(first), terms, f, wrap) if terms > 0 else UInt64(0)
        g.append(_mulm(s, naturals[m], f))
    return g^
