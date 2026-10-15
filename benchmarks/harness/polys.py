"""Exact sparse polynomials shared by the generator, the drivers, and the checker.

A polynomial is a dict from exponent tuples to nonzero coefficients: Fraction
over QQ, int in [0, p) over GF(p). A field is None for QQ or the prime p.
This module also reads and writes the text each system exchanges with the
harness: Poly Mojo's canonical sparse records and infix strings such as
`2*x0^2*x1-1/3*x2+5`.
"""
from fractions import Fraction
import hashlib
import json
import re
import sys

# Exact coefficients routinely exceed Python's default 4300-digit conversion limit.
sys.set_int_max_str_digits(0)


def coefficient(value, field):
    """Normalize a coefficient for the field; return None for zero."""
    if field is None:
        value = Fraction(value)
        return value or None
    value = int(value) % field if not isinstance(value, Fraction) else (value.numerator * pow(value.denominator, -1, field)) % field
    return value or None


def make(terms, field):
    """Build a polynomial from (exponents, coefficient) pairs, merging duplicates."""
    poly = {}
    for exps, c in terms:
        exps = tuple(exps)
        total = coefficient(c, field)
        if total is None:
            continue
        if exps in poly:
            total = coefficient(poly[exps] + total, field)
            if total is None:
                del poly[exps]
                continue
        poly[exps] = total
    return poly


def order_key(order):
    """Sort key, larger for greater monomials, for exponent tuples (x0 is the highest variable)."""
    if order == 'lex':
        return lambda e: e
    if order == 'grlex':
        return lambda e: (sum(e), e)
    if order == 'grevlex':
        return lambda e: (sum(e), tuple(-x for x in reversed(e)))
    raise ValueError(order)


def monic(poly, order, field):
    lead = max(poly, key=order_key(order))
    c = poly[lead]
    if field is None:
        return {e: v / c for e, v in poly.items()}
    inv = pow(c, -1, field)
    return {e: (v * inv) % field for e, v in poly.items()}


def scalar_text(value, field):
    if field is None:
        value = Fraction(value)
        return str(value.numerator) if value.denominator == 1 else f'{value.numerator}/{value.denominator}'
    return str(int(value) % field)


def canonical_basis(polys, order, field):
    """A reduced Gröbner basis is unique once each element is monic; return it sorted."""
    rows = []
    for p in polys:
        if not p:
            continue
        m = monic(p, order, field)
        rows.append(sorted(([list(e), scalar_text(c, field)] for e, c in m.items()), reverse=True))
    rows.sort()
    return rows


def digest(value):
    return hashlib.sha256(json.dumps(value, separators=(',', ':')).encode()).hexdigest()


# ---------------------------------------------------------------- infix text

_TERM = re.compile(r'\s*([+-]?)\s*([^+-]+)')


def parse(text, variables, field):
    """Parse an expanded infix polynomial over `variables`.

    Accepts terms such as `-3*x0^2*x1`, `1/2*x2`, `x0`, `7`, and `+1*x0^1`.
    Exponents use `^` or `**`. Coefficients may appear anywhere in a product.
    """
    index = {name: i for i, name in enumerate(variables)}
    text = text.replace('**', '^').replace(' ', '').replace('\n', '')
    if text in ('', '0'):
        return {}
    terms = []
    # Split on + and - that are not part of an exponent such as x^-1 (never produced here).
    for sign, body in re.findall(r'([+-]?)([^+-]+)', text):
        c = Fraction(-1 if sign == '-' else 1)
        exps = [0] * len(variables)
        for factor in body.split('*'):
            if not factor:
                continue
            base, _, power = factor.partition('^')
            power = int(power) if power else 1
            if base in index:
                exps[index[base]] += power
            else:
                c *= Fraction(base) ** power
        terms.append((exps, c))
    return make(terms, field)


def format_infix(poly, variables, field, order='grevlex', power='^'):
    """Write a polynomial as infix text with explicit `*` and the given power operator."""
    if not poly:
        return '0'
    parts = []
    for exps in sorted(poly, key=order_key(order), reverse=True):
        c = poly[exps]
        if field is not None and c > field // 2:
            c -= field
        c = Fraction(c)
        sign = '-' if c < 0 else '+'
        c = abs(c)
        factors = [] if c == 1 and any(exps) else [scalar_text(c, None)]
        for name, e in zip(variables, exps):
            if e:
                factors.append(name if e == 1 else f'{name}{power}{e}')
        parts.append(sign + '*'.join(factors))
    text = ''.join(parts)
    return text[1:] if text.startswith('+') else text


# ------------------------------------------------- Poly Mojo sparse records

def record(poly, nvars, field):
    """Poly Mojo's canonical sparse record: increasing lex terms over axes 0..n-1."""
    domain = 'QQ' if field is None else f'Fp:{field}'
    lines = ['POLYNOMIALS 1', 'SPARSE', domain, '1', str(nvars), *map(str, range(nvars)), str(len(poly))]
    for exps in sorted(poly):
        pairs = [(i, e) for i, e in enumerate(exps) if e]
        lines.append(str(len(pairs)))
        for i, e in pairs:
            lines += [str(i), str(e)]
        lines.append(scalar_text(poly[exps], field))
    return '\n'.join(lines) + '\n'


def write_records(polys, nvars, field):
    """Length-prefixed records, the Poly Mojo driver's input and answer format."""
    out = [f'{len(polys)}\n']
    for p in polys:
        r = record(p, nvars, field)
        out.append(f'{len(r.encode())}\n{r}')
    return ''.join(out)


def read_record(text, field):
    lines = iter(text.split('\n'))
    assert next(lines) == 'POLYNOMIALS 1' and next(lines) == 'SPARSE'
    next(lines)  # domain
    next(lines)  # order kind
    nvars = int(next(lines))
    axes = [int(next(lines)) for _ in range(nvars)]
    terms = []
    for _ in range(int(next(lines))):
        exps = [0] * nvars
        for _ in range(int(next(lines))):
            axis = int(next(lines))
            exps[axes.index(axis)] = int(next(lines))
        terms.append((exps, Fraction(next(lines))))
    return make(terms, field)


def read_records(data, field):
    """Parse length-prefixed records; lengths count bytes."""
    data = data.encode() if isinstance(data, str) else data
    position = 0

    def number():
        nonlocal position
        end = data.index(b'\n', position)
        value = int(data[position:end])
        position = end + 1
        return value

    polys = []
    for _ in range(number()):
        length = number()
        polys.append(read_record(data[position:position + length].decode(), field))
        position += length
    return polys
