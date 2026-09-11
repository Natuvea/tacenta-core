"""GF(2^16) arithmetic and interpolation, from mlkem-braid.md, "The erasure code".

"An element of GF(2^16) is a 16-bit value whose bit n is the coefficient of
x^n. Addition is exclusive or. Multiplication is the carry-less product of the
two polynomials reduced modulo x^16 + x^12 + x^3 + x + 1 (0x1100B). Division by
a nonzero a is multiplication by a^(2^16 - 2)."

`mul` and `inv` are those definitions, written out. `mul_fast`/`inv_fast` use
exponent and logarithm tables built from `mul` (mathematics: any primitive
element generates the multiplicative group); the erasure coder uses them for
speed, and a negative case holds them equal to the definitions.

Element byte encoding in the vectors (2 bytes, big-endian) matches the page's
chunk rule: "element j being bytes 2j and 2j + 1 read big-endian".
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


def pow_(a: int, e: int) -> int:
    result, base = 1, _check(a)
    while e:
        if e & 1:
            result = mul(result, base)
        base = mul(base, base)
        e >>= 1
    return result


def inv(a: int) -> int:
    if _check(a) == 0:
        raise FieldError("zero has no inverse")
    return pow_(a, 0xFFFE)     # a^(2^16 - 2)


# ---------------------------------------------------------------- tables

_EXP = None
_LOG = None


def _tables():
    global _EXP, _LOG
    if _EXP is not None:
        return
    order = 0xFFFF
    g = 2
    while not all(pow_(g, order // p) != 1 for p in (3, 5, 17, 257)):
        g += 1
    exp = [0] * (2 * order)
    log = [0] * 0x10000
    x = 1
    for i in range(order):
        exp[i] = x
        log[x] = i
        x = mul(x, g)
    if x != 1:
        raise FieldError("generator search failed")
    exp[order:] = exp[:order]
    _EXP, _LOG = exp, log


def mul_fast(a: int, b: int) -> int:
    if a == 0 or b == 0:
        return 0
    if _EXP is None:
        _tables()
    return _EXP[_LOG[a] + _LOG[b]]


def inv_fast(a: int) -> int:
    if a == 0:
        raise FieldError("zero has no inverse")
    if _EXP is None:
        _tables()
    return _EXP[0xFFFF - _LOG[a]]


# --------------------------------------------------------- interpolation

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
