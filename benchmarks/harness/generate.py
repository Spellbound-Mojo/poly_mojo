"""Write the benchmark case files.

Each case is one JSON file under cases/<family>/. Systems are generated from
their closed-form definitions, which test_generate.py checks against the
SymbolicData (github.com/symbolicdata/data, XMLResources/IntPS) instances.
Random systems use fixed seeds, so the files are reproducible; the generator
rewrites them byte for byte.

Gröbner ladders run from instances every tool solves quickly to instances that
only F4-class engines finish, so scaling curves show where each tool stops.
"""
import argparse
from fractions import Fraction
from itertools import combinations_with_replacement
import json
from pathlib import Path
import random

from .polys import make, scalar_text

HERE = Path(__file__).resolve().parent.parent
CASES = HERE / 'cases'
PRIME = 65521


def unit(n, i, power=1):
    e = [0] * n
    e[i] = power
    return e


def add(e, f):
    return [a + b for a, b in zip(e, f)]


def katsura(n):
    """Katsura-n: n+1 unknowns u_0..u_n with u_{-l} = u_l and u_l = 0 for |l| > n."""
    v = n + 1

    def u(l):
        return abs(l) if abs(l) <= n else None

    polys = [[(unit(v, 0), 1)] + [(unit(v, l), 2) for l in range(1, n + 1)] + [([0] * v, -1)]]
    for m in range(n):
        terms = []
        for l in range(-n, n + 1):
            a, b = u(l), u(m - l)
            if a is not None and b is not None:
                terms.append((add(unit(v, a), unit(v, b)), 1))
        terms.append((unit(v, m), -1))
        polys.append(terms)
    return v, polys


def cyclic(n):
    """Cyclic-n: the elementary cyclic sums of degree 1..n-1, and x0*...*x(n-1) - 1."""
    polys = []
    for k in range(1, n):
        terms = []
        for i in range(n):
            e = [0] * n
            for j in range(k):
                e[(i + j) % n] += 1
            terms.append((e, 1))
        polys.append(terms)
    polys.append([([1] * n, 1), ([0] * n, -1)])
    return n, polys


def eco(n):
    """Eco-n (Morgan): (x_k + sum_i x_i x_{i+k}) x_n - k for k = 1..n-1, and sum x_i + 1."""
    polys = []
    for k in range(1, n):
        terms = [(add(unit(n, k - 1), unit(n, n - 1)), 1)]
        for i in range(1, n - k):
            terms.append((add(add(unit(n, i - 1), unit(n, i + k - 1)), unit(n, n - 1)), 1))
        terms.append(([0] * n, -k))
        polys.append(terms)
    polys.append([(unit(n, i), 1) for i in range(n - 1)] + [([0] * n, 1)])
    return n, polys


def noon(n):
    """Noon-n (Noonburg's neural network): 10 x_i sum_{j != i} x_j^2 - 11 x_i + 10."""
    polys = []
    for i in range(n):
        terms = [(add(unit(n, i), unit(n, j, 2)), 10) for j in range(n) if j != i]
        terms += [(unit(n, i), -11), ([0] * n, 10)]
        polys.append(terms)
    return n, polys


def reimer(n):
    """Reimer-n: sum_i (-1)^(i+1) 2 x_i^k - 1 for k = 2..n+1."""
    return n, [[(unit(n, i, k), 2 * (-1) ** i) for i in range(n)] + [([0] * n, -1)] for k in range(2, n + 2)]


def randquad(n):
    """n dense quadratic equations in n unknowns with seeded coefficients in [-99, 99] minus zero."""
    rng = random.Random(f'randquad-{n}')
    monomials = [[0] * n] + [unit(n, i) for i in range(n)]
    monomials += [add(unit(n, i), unit(n, j)) for i, j in combinations_with_replacement(range(n), 2)]
    polys = []
    for _ in range(n):
        polys.append([(e, rng.choice([c for c in range(-99, 100) if c])) for e in monomials])
    return n, polys


SYSTEMS = {
    'katsura': (katsura, 'Katsura; SymbolicData Katsura_n'),
    'cyclic': (cyclic, 'Björck–Fröberg cyclic n-roots; SymbolicData Cyclic_n'),
    'eco': (eco, 'Morgan economics model; SymbolicData Verschelde.eco_n'),
    'noon': (noon, 'Noonburg neural network; SymbolicData Verschelde.noon_n'),
    'reimer': (reimer, 'Reimer; SymbolicData Reimer_5'),
    'randquad': (randquad, 'generated, seed "randquad-n"'),
}

# Ladder sizes: system -> sizes for grevlex, and the smaller lex sizes.
GREVLEX = {
    'katsura': range(3, 13),
    'cyclic': range(4, 10),
    'eco': range(5, 14),
    'noon': range(3, 10),
    'reimer': range(3, 7),
    'randquad': range(3, 11),
}
LEX = {
    'katsura': range(3, 10),
    'cyclic': range(4, 8),
    'randquad': range(2, 8),
}


def groebner_cases():
    for order, ladders in (('grevlex', GREVLEX), ('lex', LEX)):
        for system, sizes in ladders.items():
            build, source = SYSTEMS[system]
            for field in (None, PRIME):
                for size in sizes:
                    nvars, polys = build(size)
                    polys = [make(p, field) for p in polys]
                    domain = 'QQ' if field is None else f'GF{field}'
                    yield {
                        'id': f'{system}-{size}.{domain}.{order}',
                        'family': 'groebner',
                        'system': system,
                        'size': size,
                        'ladder': f'{system}.{domain}.{order}',
                        'field': field,
                        'order': order,
                        'variables': [f'x{i}' for i in range(nvars)],
                        'generators': [[[list(e), scalar_text(c, field)] for e, c in sorted(p.items(), reverse=True)] for p in polys],
                        'source': source,
                    }


# ------------------------------------------------------------- streaming

def lines(k):
    """k random lines a x + b y + c in the plane: O(k^3) CAD cells with rational samples."""
    rng = random.Random(f'lines-{k}')
    nonzero = [c for c in range(-50, 51) if c]
    return 2, [[([1, 0], rng.choice(nonzero)), ([0, 1], rng.choice(nonzero)), ([0, 0], rng.randint(-50, 50))] for _ in range(k)]


def circles(k):
    """k random circles (x-a)^2 + (y-b)^2 - r^2: irrational intersections, algebraic samples."""
    rng = random.Random(f'circles-{k}')
    polys = []
    for _ in range(k):
        a, b, r2 = rng.randint(-20, 20), rng.randint(-20, 20), rng.randint(1, 400)
        polys.append([([2, 0], 1), ([0, 2], 1), ([1, 0], -2 * a), ([0, 1], -2 * b), ([0, 0], a * a + b * b - r2)])
    return 2, polys


def planes(k):
    """k random planes in space: a three-level CAD tower."""
    rng = random.Random(f'planes-{k}')
    nonzero = [c for c in range(-20, 21) if c]
    return 3, [[([1, 0, 0], rng.choice(nonzero)), ([0, 1, 0], rng.choice(nonzero)), ([0, 0, 1], rng.choice(nonzero)),
                ([0, 0, 0], rng.randint(-20, 20))] for _ in range(k)]


def wilkinson(n):
    """prod (x - i) for i = 1..n: n rational roots, coefficients up to n! in size."""
    coefficients = [1]
    for i in range(1, n + 1):
        coefficients = [(coefficients[j - 1] if j else 0) - i * (coefficients[j] if j < len(coefficients) else 0)
                        for j in range(len(coefficients) + 1)]
    return 1, [[([j], c) for j, c in enumerate(coefficients) if c]]


def chebyshev(n):
    """The Chebyshev polynomial T_n: n irrational roots clustered towards ±1."""
    previous, current = [1], [0, 1]
    for _ in range(n - 1):
        shifted = [0] + [2 * c for c in current]
        previous, current = current, [s - (previous[j] if j < len(previous) else 0) for j, s in enumerate(shifted)]
    return 1, [[([j], c) for j, c in enumerate(current) if c]]


def fateman_base(n):
    """1 + x + y + z + t; the driver raises it to the n-th power before dumping."""
    return 4, [[([0, 0, 0, 0], 1), ([1, 0, 0, 0], 1), ([0, 1, 0, 0], 1), ([0, 0, 1, 0], 1), ([0, 0, 0, 1], 1)]]


STREAMING = {
    # kind, system: (builder, sizes, driver parameter, description)
    ('cad', 'lines'): (lines, [4, 8, 16, 24, 32, 48, 64], 0, 'k random lines in the plane'),
    ('cad', 'circles'): (circles, [2, 4, 6, 8, 12, 16], 0, 'k random circles in the plane'),
    ('cad', 'planes'): (planes, [2, 3, 4, 5, 6, 8], 0, 'k random planes in space'),
    ('roots', 'wilkinson'): (wilkinson, [50, 100, 200, 400, 800, 1600], 64, 'prod (x - i), roots to 64 bits'),
    ('roots', 'chebyshev'): (chebyshev, [100, 200, 400, 800, 1600, 3200], 64, 'Chebyshev T_n, roots to 64 bits'),
    ('dump', 'fateman'): (fateman_base, [10, 20, 40, 60, 80], None, '(1 + x + y + z + t)^n written as text'),
    ('load', 'fateman'): (fateman_base, [10, 20, 40, 60, 80], None, '(1 + x + y + z + t)^n read back from text'),
}


def streaming_cases():
    for (kind, system), (build, sizes, param, description) in STREAMING.items():
        for size in sizes:
            nvars, polys = build(size)
            polys = [make(p, None) for p in polys]
            yield {
                'id': f'{kind}-{system}-{size}',
                'family': 'streaming',
                'kind': kind,
                'system': system,
                'size': size,
                'ladder': f'{kind}.{system}',
                'field': None,
                'order': 'lex',
                'param': size if param is None else param,
                'variables': [f'x{i}' for i in range(nvars)],
                'generators': [[[list(e), scalar_text(c, None)] for e, c in sorted(p.items(), reverse=True)] for p in polys],
                'source': description,
            }


def write(cases, family):
    folder = CASES / family
    folder.mkdir(parents=True, exist_ok=True)
    expected = set()
    for case in cases:
        path = folder / f"{case['id']}.json"
        expected.add(path)
        path.write_text(json.dumps(case, indent=None, separators=(',', ':')) + '\n')
    for stale in folder.glob('*.json'):
        if stale not in expected:
            stale.unlink()
    return len(expected)


def load(family=None):
    """Return all case dicts, sorted by ladder and size."""
    paths = sorted((CASES / family).glob('*.json') if family else CASES.glob('*/*.json'))
    cases = [json.loads(p.read_text()) for p in paths]
    return sorted(cases, key=lambda c: (c['family'], c['ladder'], c['size']))


def generators(case):
    """The case's polynomials as dicts in its field."""
    field = case['field']
    return [make([(e, Fraction(c)) for e, c in p], field) for p in case['generators']]


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.parse_args(argv)
    print(f"groebner: {write(groebner_cases(), 'groebner')} cases")
    print(f"streaming: {write(streaming_cases(), 'streaming')} cases")
    from . import real_roots
    print(f"roots: {write(real_roots.cases(), 'roots')} cases")


if __name__ == '__main__':
    main()
