"""GF(2^16) arithmetic and interpolation (protocol/mlkem-braid.md, Erasure code).

The spec says "Reed-Solomon over GF(2^16)" and nothing more: no reduction
polynomial, no element encoding, no node mapping. The polynomial
x^16 + x^12 + x^3 + x + 1 and 2-byte big-endian elements are inferred from
gf.json (GAPS.md G-24). Interpolation is Lagrange's, which is mathematics.
"""

from typing import Sequence

from . import constants as K


class FieldError(ValueError):
    pass


def _check(a: int) -> int:
    if not isinstance(a, int) or a < 0 or a > 0xFFFF:
        raise FieldError("not a GF(2^16) element")
    return a


def add(a: int, b: int) -> int:
    return _check(a) ^ _check(b)


def mul(a: int, b: int) -> int:
    _check(a)
    _check(b)
    r = 0
    for i in range(16):
        if (b >> i) & 1:
            r ^= a << i
    for i in range(30, 15, -1):
        if (r >> i) & 1:
            r ^= K.GF_POLY << (i - 16)
    return r


def inv(a: int) -> int:
    if _check(a) == 0:
        raise FieldError("zero has no inverse")
    # a^(2^16 - 2)
    result, base, e = 1, a, 0xFFFE
    while e:
        if e & 1:
            result = mul(result, base)
        base = mul(base, base)
        e >>= 1
    return result


def interpolate(nodes: Sequence[int], values: Sequence[int], x: int) -> int:
    """Evaluate at x the unique polynomial of degree < len(nodes) through the points."""
    if len(nodes) != len(values) or not nodes:
        raise FieldError("nodes and values must be non-empty and the same length")
    if len(set(nodes)) != len(nodes):
        raise FieldError("interpolation nodes must be distinct")
    acc = 0
    for i, (xi, yi) in enumerate(zip(nodes, values)):
        num, den = 1, 1
        for j, xj in enumerate(nodes):
            if j != i:
                num = mul(num, add(x, xj))
                den = mul(den, add(xi, xj))
        acc ^= mul(_check(yi), mul(num, inv(den)))
    return acc


def element_from_bytes(b: bytes) -> int:
    if len(b) != 2:
        raise FieldError("a field element is 2 bytes")
    return int.from_bytes(b, "big")


def elements_from_bytes(b: bytes):
    if len(b) % 2:
        raise FieldError("odd-length element list")
    return [int.from_bytes(b[i:i + 2], "big") for i in range(0, len(b), 2)]
