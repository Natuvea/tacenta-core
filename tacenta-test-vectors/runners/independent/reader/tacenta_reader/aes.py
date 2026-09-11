"""AES-256 block cipher from FIPS 197, and CBC mode over it.

Python's standard library has no AES. This module implements the cipher
(FIPS 197 sections 5.1 to 5.3, Nk = 8, Nr = 14) and its inverse. The S-box is
computed from its definition (multiplicative inverse in GF(2^8) followed by
the affine transformation, FIPS 197 5.1.1) rather than typed in, and checked
against FIPS 197's own examples at import.

CBC is the textbook chaining mode (C_i = E(P_i xor C_(i-1)), C_0 = IV).
message-format.md names "AES-256-CBC" without citing where the mode is
defined (GAPS-2.md G2-02).
"""

from typing import List

NK = 8
NR = 14
BLOCK = 16


def _xtime(a: int) -> int:
    a <<= 1
    if a & 0x100:
        a ^= 0x11B          # m(x) = x^8 + x^4 + x^3 + x + 1 (FIPS 197 4.2)
    return a


def _gmul(a: int, b: int) -> int:
    r = 0
    while b:
        if b & 1:
            r ^= a
        a = _xtime(a)
        b >>= 1
    return r


def _rotl8(x: int, s: int) -> int:
    return ((x << s) | (x >> (8 - s))) & 0xFF


def _make_sbox():
    exp = [0] * 255
    log = [0] * 256
    x = 1
    for i in range(255):           # 3 generates GF(2^8)*
        exp[i] = x
        log[x] = i
        x = _gmul(x, 3)
    sbox = [0] * 256
    for a in range(256):
        b = 0 if a == 0 else exp[(255 - log[a]) % 255]
        sbox[a] = b ^ _rotl8(b, 1) ^ _rotl8(b, 2) ^ _rotl8(b, 3) ^ _rotl8(b, 4) ^ 0x63
    inv = [0] * 256
    for a, s in enumerate(sbox):
        inv[s] = a
    return sbox, inv


SBOX, INV_SBOX = _make_sbox()
# FIPS 197 5.1.1 example and Figure 7 corner: S(0x53) = 0xed, S(0x00) = 0x63.
assert SBOX[0x53] == 0xED and SBOX[0x00] == 0x63 and INV_SBOX[0xED] == 0x53

_M2 = [_gmul(a, 2) for a in range(256)]
_M3 = [_gmul(a, 3) for a in range(256)]
_M9 = [_gmul(a, 9) for a in range(256)]
_M11 = [_gmul(a, 11) for a in range(256)]
_M13 = [_gmul(a, 13) for a in range(256)]
_M14 = [_gmul(a, 14) for a in range(256)]


def expand_key(key: bytes) -> List[List[int]]:
    """KeyExpansion (FIPS 197 5.2) for a 256-bit key: 15 round keys of 16 bytes."""
    if len(key) != 32:
        raise ValueError("AES-256 key is 32 bytes")
    w = [list(key[4 * i:4 * i + 4]) for i in range(NK)]
    rcon = 1
    for i in range(NK, 4 * (NR + 1)):
        t = list(w[i - 1])
        if i % NK == 0:
            t = t[1:] + t[:1]                      # RotWord
            t = [SBOX[b] for b in t]               # SubWord
            t[0] ^= rcon
            rcon = _xtime(rcon)
        elif i % NK == 4:
            t = [SBOX[b] for b in t]
        w.append([w[i - NK][j] ^ t[j] for j in range(4)])
    return [sum(w[4 * r:4 * r + 4], []) for r in range(NR + 1)]


# The state is kept flat in input order: index r + 4c is row r, column c.
_SHIFT = [(i % 4) + 4 * (((i // 4) + (i % 4)) % 4) for i in range(16)]
_INV_SHIFT = [(i % 4) + 4 * (((i // 4) - (i % 4)) % 4) for i in range(16)]


def _mix(s):
    out = [0] * 16
    for c in range(4):
        a0, a1, a2, a3 = s[4 * c:4 * c + 4]
        out[4 * c] = _M2[a0] ^ _M3[a1] ^ a2 ^ a3
        out[4 * c + 1] = a0 ^ _M2[a1] ^ _M3[a2] ^ a3
        out[4 * c + 2] = a0 ^ a1 ^ _M2[a2] ^ _M3[a3]
        out[4 * c + 3] = _M3[a0] ^ a1 ^ a2 ^ _M2[a3]
    return out


def _inv_mix(s):
    out = [0] * 16
    for c in range(4):
        a0, a1, a2, a3 = s[4 * c:4 * c + 4]
        out[4 * c] = _M14[a0] ^ _M11[a1] ^ _M13[a2] ^ _M9[a3]
        out[4 * c + 1] = _M9[a0] ^ _M14[a1] ^ _M11[a2] ^ _M13[a3]
        out[4 * c + 2] = _M13[a0] ^ _M9[a1] ^ _M14[a2] ^ _M11[a3]
        out[4 * c + 3] = _M11[a0] ^ _M13[a1] ^ _M9[a2] ^ _M14[a3]
    return out


def encrypt_block(round_keys, block: bytes) -> bytes:
    """Cipher (FIPS 197 5.1)."""
    s = [b ^ k for b, k in zip(block, round_keys[0])]
    for r in range(1, NR + 1):
        s = [SBOX[b] for b in s]
        s = [s[_SHIFT[i]] for i in range(16)]
        if r != NR:
            s = _mix(s)
        s = [b ^ k for b, k in zip(s, round_keys[r])]
    return bytes(s)


def decrypt_block(round_keys, block: bytes) -> bytes:
    """InvCipher (FIPS 197 5.3)."""
    s = [b ^ k for b, k in zip(block, round_keys[NR])]
    for r in range(NR - 1, -1, -1):
        s = [s[_INV_SHIFT[i]] for i in range(16)]
        s = [INV_SBOX[b] for b in s]
        s = [b ^ k for b, k in zip(s, round_keys[r])]
        if r != 0:
            s = _inv_mix(s)
    return bytes(s)


def cbc_encrypt(key: bytes, iv: bytes, data: bytes) -> bytes:
    if len(iv) != BLOCK or len(data) % BLOCK:
        raise ValueError("CBC needs a 16-byte IV and whole blocks")
    rk = expand_key(key)
    prev = bytes(iv)
    out = bytearray()
    for i in range(0, len(data), BLOCK):
        prev = encrypt_block(rk, bytes(a ^ b for a, b in zip(data[i:i + BLOCK], prev)))
        out += prev
    return bytes(out)


def cbc_decrypt(key: bytes, iv: bytes, data: bytes) -> bytes:
    if len(iv) != BLOCK or len(data) % BLOCK:
        raise ValueError("CBC needs a 16-byte IV and whole blocks")
    rk = expand_key(key)
    prev = bytes(iv)
    out = bytearray()
    for i in range(0, len(data), BLOCK):
        block = bytes(data[i:i + BLOCK])
        out += bytes(a ^ b for a, b in zip(decrypt_block(rk, block), prev))
        prev = block
    return bytes(out)
