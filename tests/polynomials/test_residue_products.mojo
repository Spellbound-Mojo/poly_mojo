"""Residue products by precomputed quotients against ModInt multiplication.

The packed Gröbner engine multiplies reducer tails by a fixed residue with
Shoup's method: one 64 by 64 bit product and a correction instead of a 128 bit
division. Products must agree with `ModInt.mul` for every prime the field
accepts, so the check covers a small prime, the largest prime below 2^32, and
the largest prime below 2^62, at edge residues and at random ones.
"""
from polynomials import Budget, ModInt, Modulus
from polynomials._packed_groebner import _Shoup
from support.check import Checker
from support.rng import SplitMix64


def check_shoup(mut c: Checker, mut work: Budget) raises:
    """Precomputed-quotient products against ModInt.mul, at edge and random residues."""
    var rng = SplitMix64(29)
    for p in [UInt64(65521), UInt64(4294967291), UInt64(4611686018427387847)]:
        var ctx = Modulus(p, work)
        var edges: List[UInt64] = [0, 1, 2, p // 2, p - 2, p - 1]
        for i in range(len(edges)):
            for j in range(len(edges)):
                var a = ModInt(edges[i], ctx)
                var w = ModInt(edges[j], ctx)
                c.check(_Shoup.of(w).times(a.value) == a.mul(w, work).value, "edge product modulo " + String(p))
        for _ in range(2000):
            var a = ModInt(rng.next(), ctx)
            var w = ModInt(rng.next(), ctx)
            c.check(_Shoup.of(w).times(a.value) == a.mul(w, work).value, "random product modulo " + String(p))


def main() raises:
    var work = Budget()
    var c = Checker("residue products")
    check_shoup(c, work)
    c.finish()
