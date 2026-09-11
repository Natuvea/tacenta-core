"""HMAC-SHA256 (RFC 2104 / FIPS 180-4) and HKDF-SHA256 (RFC 5869)."""

import hashlib
import hmac as _hmac

HASH_LEN = 32


def hmac_sha256(key: bytes, data: bytes) -> bytes:
    return _hmac.new(bytes(key), bytes(data), hashlib.sha256).digest()


def hkdf_extract(salt: bytes, ikm: bytes) -> bytes:
    # RFC 5869 2.2: if salt is not provided it is HashLen zero octets.
    if salt is None or len(salt) == 0:
        salt = bytes(HASH_LEN)
    return hmac_sha256(salt, ikm)


def hkdf_expand(prk: bytes, info: bytes, length: int) -> bytes:
    if length < 0 or length > 255 * HASH_LEN:
        raise ValueError("HKDF output length out of range")
    out = bytearray()
    t = b""
    i = 1
    while len(out) < length:
        t = hmac_sha256(prk, t + bytes(info) + bytes([i]))
        out += t
        i += 1
    return bytes(out[:length])


def hkdf_sha256(salt: bytes, ikm: bytes, info: bytes, length: int) -> bytes:
    return hkdf_expand(hkdf_extract(salt, ikm), info, length)
