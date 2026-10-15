"""Check the generated systems against SymbolicData and the record format."""
import unittest

from .generate import cyclic, eco, katsura, noon, reimer
from .polys import make, parse, read_records, write_records

# Verbatim from SymbolicData XMLResources/IntPS (variables in the listed order).
SYMBOLICDATA = {
    'katsura-3': (katsura, 3, 'u0,u1,u2,u3', [
        'u0+2*u1+2*u2+2*u3-1', 'u1^2+2*u0*u2+2*u1*u3-u2',
        '2*u0*u1+2*u1*u2+2*u2*u3-u1', 'u0^2+2*u1^2+2*u2^2+2*u3^2-u0']),
    'cyclic-5': (cyclic, 5, 'v,w,x,y,z', [
        'v+w+x+y+z', 'v*w+w*x+x*y+v*z+y*z', 'v*w*x+w*x*y+v*w*z+v*y*z+x*y*z',
        'v*w*x*y+v*w*x*z+v*w*y*z+v*x*y*z+w*x*y*z', 'v*w*x*y*z-1']),
    'eco-6': (eco, 6, 'x1,x2,x3,x4,x5,x6', [
        'x1+x2+x3+x4+x5+1', 'x5*x6-5', 'x1*x5*x6+x4*x6-4', 'x1*x4*x6+x2*x5*x6+x3*x6-3',
        'x1*x3*x6+x2*x4*x6+x3*x5*x6+x2*x6-2', 'x1*x2*x6+x2*x3*x6+x3*x4*x6+x4*x5*x6+x1*x6-1']),
    'noon-3': (noon, 3, 'x1,x2,x3', [
        '10*x1^2*x3+10*x2^2*x3-11*x3+10', '10*x1*x2^2+10*x1*x3^2-11*x1+10',
        '10*x1^2*x2+10*x2*x3^2-11*x2+10']),
    'reimer-5': (reimer, 5, 'x,y,z,t,u', [
        '2*x^2-2*y^2+2*z^2-2*t^2+2*u^2-1', '2*x^3-2*y^3+2*z^3-2*t^3+2*u^3-1',
        '2*x^4-2*y^4+2*z^4-2*t^4+2*u^4-1', '2*x^5-2*y^5+2*z^5-2*t^5+2*u^5-1',
        '2*x^6-2*y^6+2*z^6-2*t^6+2*u^6-1']),
}


def key(poly):
    return tuple(sorted(poly.items()))


class Systems(unittest.TestCase):
    def test_symbolicdata(self):
        for name, (build, size, variables, polys) in SYMBOLICDATA.items():
            with self.subTest(name):
                _, generated = build(size)
                generated = {key(make(p, None)) for p in generated}
                reference = {key(parse(p, variables.split(','), None)) for p in polys}
                self.assertEqual(generated, reference)

    def test_records_round_trip(self):
        for field in (None, 65521):
            _, polys = katsura(4)
            polys = [make(p, field) for p in polys]
            self.assertEqual(read_records(write_records(polys, 5, field), field), polys)


if __name__ == '__main__':
    unittest.main()
