"""X25519 (RFC 7748), Ed25519 (RFC 8032), XEdDSA (revision 1 with the
modifications tacenta-spec records in CONSTANTS.md and ADR-0002).

Pure Python, not constant time: a conformance reader, not a production
primitive.
"""

import hashlib
from typing import Optional, Tuple

P = 2 ** 255 - 19
Q = 2 ** 252 + 27742317777372353535851937790883648493  # the group order l
D = (-121665 * pow(121666, P - 2, P)) % P
SQRT_M1 = pow(2, (P - 1) // 4, P)


def _inv(x: int) -> int:
    return pow(x, P - 2, P)


# ------------------------------------------------------------------ X25519

def _decode_scalar25519(k: bytes) -> int:
    if len(k) != 32:
        raise ValueError("X25519 scalar is 32 bytes")
    b = bytearray(k)
    b[0] &= 248
    b[31] &= 127
    b[31] |= 64
    return int.from_bytes(b, "little")


def x25519(k: bytes, u: bytes) -> bytes:
    if len(u) != 32:
        raise ValueError("X25519 u-coordinate is 32 bytes")
    scalar = _decode_scalar25519(k)
    x1 = int.from_bytes(u, "little") & ((1 << 255) - 1)
    x2, z2, x3, z3 = 1, 0, x1, 1
    swap = 0
    a24 = 121665
    for t in range(254, -1, -1):
        kt = (scalar >> t) & 1
        swap ^= kt
        if swap:
            x2, x3 = x3, x2
            z2, z3 = z3, z2
        swap = kt
        A = (x2 + z2) % P
        AA = A * A % P
        B = (x2 - z2) % P
        BB = B * B % P
        E = (AA - BB) % P
        C = (x3 + z3) % P
        Dd = (x3 - z3) % P
        DA = Dd * A % P
        CB = C * B % P
        x3 = pow(DA + CB, 2, P)
        z3 = x1 * pow(DA - CB, 2, P) % P
        x2 = AA * BB % P
        z2 = E * (AA + a24 * E) % P
    if swap:
        x2, x3 = x3, x2
        z2, z3 = z3, z2
    return (x2 * pow(z2, P - 2, P) % P).to_bytes(32, "little")


def x25519_public(k: bytes) -> bytes:
    return x25519(k, (9).to_bytes(32, "little"))


class NonContributory(ValueError):
    pass


def x25519_contributory(k: bytes, u: bytes) -> bytes:
    """session-establishment.md: "Both sides refuse a Diffie-Hellman output
    that is not contributory, which a low-order public key produces." """
    out = x25519(k, u)
    if out == bytes(32):
        raise NonContributory("Diffie-Hellman output is all zero")
    return out


# ----------------------------------------------------------------- Ed25519

Point = Tuple[int, int, int, int]
IDENTITY: Point = (0, 1, 1, 0)


def _add(p1: Point, p2: Point) -> Point:
    A = (p1[1] - p1[0]) * (p2[1] - p2[0]) % P
    B = (p1[1] + p1[0]) * (p2[1] + p2[0]) % P
    C = 2 * p1[3] * p2[3] * D % P
    Dd = 2 * p1[2] * p2[2] % P
    E, F, G, H = B - A, Dd - C, Dd + C, B + A
    return (E * F % P, G * H % P, F * G % P, E * H % P)


def _mul(s: int, pt: Point) -> Point:
    q = IDENTITY
    while s > 0:
        if s & 1:
            q = _add(q, pt)
        pt = _add(pt, pt)
        s >>= 1
    return q


def _neg(pt: Point) -> Point:
    return ((-pt[0]) % P, pt[1], pt[2], (-pt[3]) % P)


def _is_identity(pt: Point) -> bool:
    return pt[0] % P == 0 and (pt[1] - pt[2]) % P == 0


def _recover_x(y: int, sign: int) -> Optional[int]:
    if y >= P:
        return None
    x2 = (y * y - 1) * _inv(D * y * y + 1) % P
    if x2 == 0:
        return None if sign else 0
    x = pow(x2, (P + 3) // 8, P)
    if (x * x - x2) % P != 0:
        x = x * SQRT_M1 % P
    if (x * x - x2) % P != 0:
        return None
    if (x & 1) != sign:
        x = P - x
    return x


_GY = 4 * _inv(5) % P
_GX = _recover_x(_GY, 0)
BASE: Point = (_GX, _GY, 1, _GX * _GY % P)


def compress(pt: Point) -> bytes:
    zi = _inv(pt[2])
    x = pt[0] * zi % P
    y = pt[1] * zi % P
    return (y | ((x & 1) << 255)).to_bytes(32, "little")


def decompress(b: bytes) -> Optional[Point]:
    if len(b) != 32:
        return None
    y = int.from_bytes(b, "little")
    sign = y >> 255
    y &= (1 << 255) - 1
    x = _recover_x(y, sign)
    if x is None:
        return None
    return (x, y, 1, x * y % P)


def _sha512_int(data: bytes) -> int:
    return int.from_bytes(hashlib.sha512(data).digest(), "little")


def ed25519_public(secret: bytes) -> bytes:
    a, _ = _expand(secret)
    return compress(_mul(a, BASE))


def _expand(secret: bytes):
    if len(secret) != 32:
        raise ValueError("Ed25519 secret is 32 bytes")
    h = hashlib.sha512(secret).digest()
    a = int.from_bytes(h[:32], "little")
    a &= (1 << 254) - 8
    a |= 1 << 254
    return a, h[32:]


def ed25519_sign(secret: bytes, msg: bytes) -> bytes:
    a, prefix = _expand(secret)
    A = compress(_mul(a, BASE))
    r = _sha512_int(prefix + msg) % Q
    R = compress(_mul(r, BASE))
    h = _sha512_int(R + A + msg) % Q
    s = (r + h * a) % Q
    return R + s.to_bytes(32, "little")


def ed25519_verify(public: bytes, msg: bytes, sig: bytes) -> bool:
    """RFC 8032 5.1.7 (cofactorless equation, byte comparison of R)."""
    if len(public) != 32 or len(sig) != 64:
        return False
    A = decompress(public)
    if A is None:
        return False
    R_bytes = sig[:32]
    if decompress(R_bytes) is None:
        return False
    s = int.from_bytes(sig[32:], "little")
    if s >= Q:
        return False
    h = _sha512_int(R_bytes + public + msg) % Q
    return compress(_add(_mul(s, BASE), _neg(_mul(h, A)))) == R_bytes


# ------------------------------------------------------------------ XEdDSA

_HASH1_PREFIX = b"\xfe" + b"\xff" * 31  # 2^256 - 1 - 1, little-endian


def xeddsa_sign(k: bytes, msg: bytes, z: bytes) -> bytes:
    """XEdDSA revision 1 xeddsa_sign. k is the X25519 private key; it is
    clamped (decodeScalar25519) before use, which the tacenta spec does not
    state (GAPS.md G-27)."""
    if len(z) != 64:
        raise ValueError("Z is 64 bytes")
    scalar = _decode_scalar25519(k)
    E = _mul(scalar, BASE)
    e_enc = compress(E)
    sign = e_enc[31] >> 7
    a_enc = e_enc[:31] + bytes([e_enc[31] & 0x7F])     # A.s = 0
    a = (-scalar) % Q if sign else scalar % Q
    r = _sha512_int(_HASH1_PREFIX + a.to_bytes(32, "little") + msg + z) % Q
    R = compress(_mul(r, BASE))
    h = _sha512_int(R + a_enc + msg) % Q
    s = (r + h * a) % Q
    return R + s.to_bytes(32, "little")


def _is_small_order(pt: Point) -> bool:
    return _is_identity(_mul(8, pt))


def xeddsa_verify(u_bytes: bytes, msg: bytes, sig: bytes) -> Optional[bytes]:
    """Verify under a Montgomery public key; return the compressed Edwards key
    it verified under, or None.

    Accepted set, as tacenta-spec states it (CONSTANTS.md "XEdDSA signature
    sign bit"; ADR-0002 Consequences): u < p; the Edwards sign is the top bit
    of signature[63]; s < l (not s < 2^253); small-order A and small-order R
    refused outright; R compared as bytes.
    """
    if len(u_bytes) != 32 or len(sig) != 64:
        return None
    u = int.from_bytes(u_bytes, "little")
    if u >= P:
        return None
    sign = sig[63] >> 7
    s = int.from_bytes(sig[32:63] + bytes([sig[63] & 0x7F]), "little")
    if s >= Q:
        return None
    if (u + 1) % P == 0:
        return None  # convert_mont divides by zero (GAPS.md G-28)
    y = (u - 1) * _inv(u + 1) % P
    a_enc = (y | (sign << 255)).to_bytes(32, "little")
    A = decompress(a_enc)
    if A is None or _is_small_order(A):
        return None
    R_bytes = sig[:32]
    R = decompress(R_bytes)
    if R is None or _is_small_order(R):
        return None
    h = _sha512_int(R_bytes + a_enc + msg) % Q
    if compress(_add(_mul(s, BASE), _neg(_mul(h, A)))) != R_bytes:
        return None
    return a_enc
