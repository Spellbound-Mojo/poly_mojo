"""Check the text formats and canonical answers the checker relies on."""
from fractions import Fraction
import unittest

from .polys import canonical_basis, format_infix, make, parse

VARIABLES = ['x0', 'x1', 'x2']


class Text(unittest.TestCase):
    def test_infix_round_trip(self):
        for field in (None, 65521):
            p = make([((2, 0, 1), Fraction(-3, 7)), ((0, 1, 0), 1), ((0, 0, 0), 5), ((1, 1, 1), -1)], field)
            self.assertEqual(parse(format_infix(p, VARIABLES, field), VARIABLES, field), p)

    def test_msolve_and_singular_output(self):
        # Terms as msolve prints them over GF(p), and as Singular prints them over QQ.
        msolve = parse('1*x0^1+1*x1^1+1*x2^1+32760', VARIABLES, 65521)
        singular = parse('x0+x1+x2-1/2', VARIABLES, None)
        self.assertEqual(msolve, make([((1, 0, 0), 1), ((0, 1, 0), 1), ((0, 0, 1), 1), ((0, 0, 0), 32760)], 65521))
        self.assertEqual(canonical_basis([msolve], 'grevlex', 65521), canonical_basis([make(singular.items(), 65521)], 'grevlex', 65521))

    def test_canonical_basis_ignores_scale_and_order(self):
        a = make([((1, 0, 0), 2), ((0, 0, 0), -1)], None)
        b = make([((0, 2, 0), 3), ((0, 0, 1), 1)], None)
        scaled = [{e: c * 6 for e, c in b.items()}, {e: c * -4 for e, c in a.items()}]
        self.assertEqual(canonical_basis([a, b], 'grevlex', None), canonical_basis(scaled, 'grevlex', None))


if __name__ == '__main__':
    unittest.main()
