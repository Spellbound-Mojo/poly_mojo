"""Root refinement reuses certified cells and rejects stale or forged results."""
from apn_mojo import Rational, Ball
from polynomials import Budget, QQ, NoContext, DensePoly, NumericOptions, PolyErrorKind, sturm_sequence, sign_changes, real_roots_exact, complex_roots_exact, refine_real_roots_exact, refine_complex_roots_exact, check_real_roots_exact, check_complex_roots_exact, NumericDensePoly, BallDomain, real_roots_numeric, refine_real_roots_numeric, check_real_roots_numeric
from support.check import Checker


def deep_refinement(mut c: Checker) raises:
    # Single-root cells split by an enclosure of their root; every count must
    # still be the Sturm count of its cell, including repeated roots, dyadic
    # rational roots on the bisection grid, and nearly coincident roots.
    var work = Budget()
    var cases = List[List[QQ]]()
    # (x - 1/2)^3 (x^2 - 2) (x + 3)
    cases.append([QQ(Rational(3, 4)), QQ(Rational(-17, 4)), QQ(Rational(57, 8)), QQ(Rational(-7, 8)), QQ(Rational(-23, 4)), QQ(Rational(3, 2)), QQ(Rational(1))])
    # (x - 1)(x - 1 - 2^-60) (x + 5/3)
    var close = Rational(1) + Rational(1, 1 << 60)
    var p0 = Rational(5, 3) * close
    var p1 = Rational(5, 3) * (Rational(-1) - close) + close
    var p2 = Rational(5, 3) - Rational(1) - close
    cases.append([QQ(p0^), QQ(p1^), QQ(p2^), QQ(Rational(1))])
    for k in range(len(cases)):
        var f = DensePoly[QQ].from_coefficients(0, NoContext(), cases[k].copy(), work)
        var coarse = NumericOptions(absolute_bits=1, max_subdivisions=1 << 20)
        var deep = NumericOptions(absolute_bits=200, max_subdivisions=1 << 20)
        var cover = real_roots_exact(f, coarse, work)
        var refined = refine_real_roots_exact(f, cover, coarse, deep, work, complete_only=True)
        c.check(check_real_roots_exact(f, refined, deep, work), String("deep refinement checks ", k))
        var sequence = sturm_sequence(f, work)
        var counted = 0
        for cell in refined.cells:
            var count = sign_changes(sequence, cell.interval.real_low, work) - sign_changes(sequence, cell.interval.real_high, work)
            c.check(count == cell.count, String("deep refinement cell count is its Sturm count ", k))
            counted += cell.count
        c.check(counted == (4 if k == 0 else 3), String("every distinct root covered ", k))


def main() raises:
    var c = Checker("root_refinement")
    deep_refinement(c)
    var work = Budget()
    var f = DensePoly[QQ].from_coefficients(0, NoContext(), [QQ(Rational(-2)), QQ(Rational(0)), QQ(Rational(1))], work)
    var coarse = NumericOptions(absolute_bits=1, max_subdivisions=2)
    var fine = NumericOptions(absolute_bits=7, max_subdivisions=256)
    var real = real_roots_exact(f, coarse, work)
    var refined = refine_real_roots_exact(f, real, coarse, fine, work, complete_only=True)
    c.check(refined.accurate and refined.isolated and check_real_roots_exact(f, refined, fine, work), "resume complete coarse Sturm cover")
    var retained = 0
    for cell in real.cells:
        if cell.count == 0:
            for after in refined.cells:
                if after.interval == cell.interval:
                    retained += 1
    c.check(retained > 0, "excluded cells reused")
    var coarse_complex = NumericOptions(absolute_bits=1, max_subdivisions=64, require_isolation=False)
    var initial = complex_roots_exact(f, coarse_complex, work)
    var fine_complex = NumericOptions(absolute_bits=4, max_subdivisions=1024)
    var refined_complex = refine_complex_roots_exact(f, initial, coarse_complex, fine_complex, work, complete_only=True)
    c.check(check_complex_roots_exact(f, refined_complex, fine_complex, work), "resume complex contour regions")
    var family = NumericDensePoly[BallDomain].from_coefficients(0, [Ball(0, Rational(9, 10)), Ball(1)], work)
    var no_splits = NumericOptions(absolute_bits=1, max_subdivisions=0)
    var family_before = real_roots_numeric(family, no_splits, work)
    var family_after = refine_real_roots_numeric(family, family_before, no_splits, fine, work)
    c.check(family_after.complete and not family_after.accurate and check_real_roots_numeric(family, family_after, fine, work), "failed family cut retains certified parent")
    var uncertain = NumericDensePoly[BallDomain].from_coefficients(0, [Ball(-2, Rational(1, 4096)), Ball(0), Ball(1)], work)
    var unresolved = real_roots_numeric(uncertain, no_splits, work)
    var resolved = refine_real_roots_numeric(uncertain, unresolved, no_splits, fine, work, complete_only=True)
    c.check(check_real_roots_numeric(uncertain, resolved, fine, work), "resume unresolved interval-family cover")
    var forged = real.copy()
    forged.cells[0].count += 1
    try:
        _ = refine_real_roots_exact(f, forged, coarse, fine, work)
        c.check(False, "forged previous root cover accepted")
    except e:
        c.check(e.kind == PolyErrorKind.DOMAIN, "previous root cover validated before reuse")
    var tiny = Budget(0)
    try:
        _ = refine_complex_roots_exact(f, initial, coarse_complex, fine_complex, tiny)
        c.check(False, "refinement ignored budget")
    except e:
        c.check(e.kind == PolyErrorKind.LIMIT, "refinement budget preserves original")
    c.finish()
