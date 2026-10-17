"""Prepared exact interpolation, multipoint evaluation and Hermite witnesses."""
from apn_mojo import Rational, ExactComplex
from polynomials import Budget, PolyErrorKind, CoefficientField, QQ, QQi, ModInt, Modulus, NoContext, DensePoly, MultipointPlan, interpolate, hermite_interpolate, check_interpolation, check_hermite_interpolation, evaluate_dense
from support.check import Checker


def exact[C: CoefficientField](ctx: C.Context, zero: C, one: C, two: C, mut c: Checker, mut work: Budget) raises:
    var f = DensePoly[C].from_coefficients(0, ctx, [one.copy(), two.copy(), one.copy()], work)
    var points: List[C] = [zero.copy(), one.copy(), two.copy()]
    var values = List[C]()
    for point in points:
        values.append(evaluate_dense(f, point, work))
    var plan = MultipointPlan[C].prepare(0, ctx, points, work)
    c.check(plan.point_count() == 3 and plan.evaluate(f, work) == values, "prepared remainder tree")
    var recovered = plan.interpolate(values, work)
    c.check(recovered == f and check_interpolation(recovered, points, values, work), "prepared interpolation")
    c.check(interpolate[C](0, ctx, points, values, work) == f, "interpolation convenience API")
    var wrong = f.add(DensePoly[C].from_coefficients(0, ctx, [one.copy()], work), work)
    c.check(not check_interpolation(wrong, points, values, work), "wrong interpolant rejected")
    var repeated: List[C] = [one.copy(), one.copy()]
    var duplicate_plan = MultipointPlan[C].prepare(0, ctx, repeated, work)
    var same_values = duplicate_plan.evaluate(f, work)
    c.check(same_values[0] == same_values[1], "duplicate multipoint evaluations allowed")
    try:
        _ = duplicate_plan.interpolate(same_values, work)
        c.check(False, "duplicate interpolation nodes accepted")
    except e:
        c.check(e.kind == PolyErrorKind.DOMAIN, "nonunique interpolation rejected")
    var empty = List[C]()
    var empty_plan = MultipointPlan[C].prepare(0, ctx, empty, work)
    c.check(empty_plan.interpolate(empty, work).is_zero() and len(empty_plan.evaluate(f, work)) == 0, "empty prepared plan")
    var tiny = Budget(0)
    try:
        _ = plan.evaluate(f, tiny)
        c.check(False, "multipoint budget ignored")
    except e:
        c.check(e.kind == PolyErrorKind.LIMIT, "prepared evaluation budget")


def integer_nodes(mut c: Checker, mut work: Budget) raises:
    # The multimodular route for small integer nodes must match the generic tree.
    var small: List[Int] = [-7, 3, 0, 12, -2, 5, 9]
    for scenario in range(3):
        var points = List[QQ]()
        var values = List[QQ]()
        var count = 7 if scenario == 0 else 40
        for i in range(count):
            var node = i * 7 - 150 if scenario != 0 else small[i]
            if scenario == 2 and i == 5:
                node = 1 << 30  # beyond the residue-count bound: generic route
            points.append(QQ(Rational(node)))
            values.append(QQ(Rational(i * i * i - 5 * i + 1, i % 4 + 1)))
        var fast = interpolate[QQ](0, NoContext(), points, values, work)
        var generic = MultipointPlan[QQ].prepare(0, NoContext(), points, work).interpolate(values, work)
        c.check(fast == generic and check_interpolation(fast, points, values, work), "integer-node interpolation matches the tree")
    var repeated: List[QQ] = [QQ(Rational(3)), QQ(Rational(-1)), QQ(Rational(3))]
    var samples: List[QQ] = [QQ(Rational(1)), QQ(Rational(2)), QQ(Rational(1))]
    try:
        _ = interpolate[QQ](0, NoContext(), repeated, samples, work)
        c.check(False, "repeated integer nodes accepted")
    except e:
        c.check(e.kind == PolyErrorKind.DOMAIN, "repeated integer nodes rejected")


def main() raises:
    var c = Checker("interpolation")
    var work = Budget()
    integer_nodes(c, work)
    exact[QQ](NoContext(), QQ(Rational(0)), QQ(Rational(1)), QQ(Rational(2)), c, work)
    exact[QQi](NoContext(), QQi(ExactComplex(0)), QQi(ExactComplex(1)), QQi(ExactComplex(0, 1)), c, work)
    var prime = Modulus(101, work)
    exact[ModInt](prime, ModInt(0, prime), ModInt(1, prime), ModInt(2, prime), c, work)
    # f=x^3+2x+1 has (f(0),f'(0))=(1,2), (f(1),f'(1))=(4,5).
    var points: List[QQ] = [QQ(Rational(0)), QQ(Rational(1))]
    var jets: List[List[QQ]] = [[QQ(Rational(1)), QQ(Rational(2))], [QQ(Rational(4)), QQ(Rational(5))]]
    var expected = DensePoly[QQ].from_coefficients(0, NoContext(), [QQ(Rational(1)), QQ(Rational(2)), QQ(Rational(0)), QQ(Rational(1))], work)
    var got = hermite_interpolate[QQ](0, NoContext(), points, jets, work)
    c.check(got == expected and check_hermite_interpolation(got, points, jets, work), "hand-derived confluent interpolation")
    jets[1][1] = QQ(Rational(6))
    c.check(not check_hermite_interpolation(got, points, jets, work), "corrupt Hermite constraint rejected")
    var p3 = Modulus(3, work)
    var zero3 = ModInt(0, p3)
    var one3 = ModInt(1, p3)
    var nodes3: List[ModInt] = [zero3.copy()]
    var taylor3: List[List[ModInt]] = [[zero3.copy(), zero3.copy(), zero3.copy(), one3.copy()]]
    var cubic3 = hermite_interpolate[ModInt](0, p3, nodes3, taylor3, work, derivatives=False)
    c.check(cubic3.degree() == 3 and check_hermite_interpolation(cubic3, nodes3, taylor3, work, derivatives=False), "Taylor constraints work across characteristic")
    c.check(not check_hermite_interpolation(cubic3, nodes3, taylor3, work), "singular raw derivative constraints rejected by checker")
    try:
        _ = hermite_interpolate[ModInt](0, p3, nodes3, taylor3, work)
        c.check(False, "noninvertible Hermite factorial accepted")
    except e:
        c.check(e.kind == PolyErrorKind.DOMAIN, "noninvertible Hermite factorial rejected")
    c.finish()
