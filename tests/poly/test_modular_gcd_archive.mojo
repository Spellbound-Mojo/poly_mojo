"""Modular GCD evidence survives archives; legacy arenas remain readable."""
from poly import sparse, exact, io
from apn_mojo import Rational
from polynomials import Budget, ZZ, CoprimalityNode, CoprimalityCertificate, PolyErrorKind
from polynomials.gcd import _prove
from std.testing import assert_true, assert_false, assert_equal


def roundtrip[k: Int, P: Copyable & Deinitable, is_sparse: Bool, E: Copyable & Deinitable](value: exact.Result[k, P, is_sparse, E]) raises:
    comptime T = exact.Result[k, P, is_sparse, E]
    var text = io.dumps(value)
    assert_true(text.find("MODULAR-1") >= 0)
    var restored = io.loads[T](text)
    assert_true(exact.check(restored))
    assert_equal(io.dumps(restored), text)
    var rejected = False
    try:
        _ = io.loads[T](text.replace("MODULAR-1", "MODULAR-2"))
    except e:
        rejected = e.kind == PolyErrorKind.ENCODING
    assert_true(rejected)
    rejected = False
    try:
        _ = io.loads[T](text.replace("MODULAR-1\n1000000007\n", "MODULAR-1\n1000000008\n"))
    except e:
        rejected = e.kind == PolyErrorKind.ENCODING
    assert_true(rejected)


def main() raises:
    var f = sparse.asarray([((1, 0), 1)])
    var g = sparse.asarray([((0, 1), 1)])
    var result = sparse.gcd_checked(f, g)
    assert_true(Bool(result.evidence().coprimality.value().modular))
    roundtrip(result)
    roundtrip(sparse.gcd_checked([((1, 0), Rational(2, 3))], [((0, 1), Rational(4, 7))]))

    # Construct the pre-modular arena and serialize its unchanged wire schema.
    var work = Budget()
    var nodes = List[CoprimalityNode[ZZ]]()
    var root = _prove(sparse.to_core(f), sparse.to_core(g), nodes, work)
    assert_true(Bool(root))
    result._data[].proof.coprimality = CoprimalityCertificate[ZZ](nodes^, root.value())
    var legacy = io.dumps(result)
    assert_false(legacy.find("MODULAR-1") >= 0)
    var restored = io.loads[type_of(result)](legacy)
    assert_false(Bool(restored.evidence().coprimality.value().modular))
    assert_true(exact.check(restored))
    assert_equal(io.dumps(restored), legacy)
    print("modular gcd archive checks passed")
