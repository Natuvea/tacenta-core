"""A test double for the incremental ML-KEM interface the Braid uses.

THIS IS NOT ML-KEM. The reader implements no FIPS 203 key generation,
encapsulation or decapsulation (GAPS-3.md, "Not attempted"). The double keeps
what mlkem-braid.md, "The KEM split", states about the interface's shapes and
laws, so that the Braid's state machine can be driven from the page:

- `header` is `rho (32) || H(ek) (32)`, with `H` SHA3-256 over `ek_vector || rho`
  (the page's hash input order), and `ek_vector` is a valid `ByteEncode12`
  encoding, so it passes the page's validation;
- the first half of encapsulation needs only `header` and yields `ct1` (1,408)
  and `K` (32); the second half draws nothing and yields `ct2` (160) from what
  the first half kept and `ek_vector`;
- decapsulation of `ct1 || ct2` returns that `K` when `ek_vector` is the one
  the header authenticates, and a pseudorandom value, never an error, for any
  other ciphertext (implicit rejection).

The key pair and the encapsulation state are this double's own layouts,
padded to CONSTANTS.md's lengths (11,872 and 2,592 bytes) so the persisted
Braid format can be exercised. They are not the library layouts
session-persistence.md delegates to (GAPS-2.md G2-08).
"""

import hashlib

from . import constants as K


class KemFailure(Exception):
    """A KEM operation failing (mlkem-braid.md, Failure)."""


def byte_encode12(coeffs):
    """FIPS 203 ByteEncode12: 12 bits per coefficient, little-endian bit order."""
    out = bytearray()
    for i in range(0, len(coeffs), 2):
        a, b = coeffs[i], coeffs[i + 1]
        out += bytes([a & 0xFF, ((a >> 8) | (b << 4)) & 0xFF, (b >> 4) & 0xFF])
    return bytes(out)


def _shake(label, *parts, n):
    return hashlib.shake_256(label + b"".join(parts)).digest(n)


def _xor(a, b):
    return bytes(x ^ y for x, y in zip(a, b))


class ToyIncrementalKem:
    def __init__(self, seed: bytes, fail_on=()):
        self.seed = bytes(seed)
        self.fail_on = set(fail_on)
        self._draws = 0

    def _random(self, n):
        self._draws += 1
        return hashlib.shake_256(self.seed + self._draws.to_bytes(8, "big")).digest(n)

    def generate(self):
        if "generate" in self.fail_on:
            raise KemFailure("key generation failed")
        stream = self._random(2 * 1024)
        coeffs = [int.from_bytes(stream[2 * i:2 * i + 2], "little") % K.MLKEM_Q for i in range(1024)]
        ek_vector = byte_encode12(coeffs)
        rho = self._random(32)
        z = self._random(32)
        header = rho + hashlib.sha3_256(ek_vector + rho).digest()
        key_pair = (ek_vector + rho + z).ljust(K.BRAID_KEY_PAIR_LEN, b"\x00")
        return key_pair, header, ek_vector

    @staticmethod
    def ek_vector(key_pair):
        return bytes(key_pair[:K.BRAID_EK_VECTOR_LEN])

    def encaps1(self, header):
        if "encaps1" in self.fail_on:
            raise KemFailure("first half of encapsulation failed")
        m = self._random(32)
        g = hashlib.sha3_512(m + header[32:]).digest()
        k, r = g[:32], g[32:]
        ct1 = _shake(b"toy ct1", r, header[:32], n=K.BRAID_CT1_LEN)
        state = (m + bytes(header)).ljust(K.BRAID_ENCAPS_LEN, b"\x00")
        return state, ct1, k

    def encaps2(self, state, ek_vector):
        if "encaps2" in self.fail_on:
            raise KemFailure("second half of encapsulation failed")
        m, header = state[:32], state[32:96]
        r = hashlib.sha3_512(m + header[32:]).digest()[32:]
        ct1 = _shake(b"toy ct1", r, header[:32], n=K.BRAID_CT1_LEN)
        return _xor(m, _shake(b"toy pad", ek_vector, ct1, n=32)) + _shake(b"toy tag", m, ek_vector, n=128)

    def decaps(self, key_pair, ct1, ct2):
        if "decaps" in self.fail_on:
            raise KemFailure("decapsulation failed")
        ek_vector, rho, z = key_pair[:1536], key_pair[1536:1568], key_pair[1568:1600]
        m = _xor(ct2[:32], _shake(b"toy pad", ek_vector, ct1, n=32))
        g = hashlib.sha3_512(m + hashlib.sha3_256(ek_vector + rho).digest()).digest()
        k, r = g[:32], g[32:]
        if ct1 == _shake(b"toy ct1", r, rho, n=K.BRAID_CT1_LEN) and ct2[32:] == _shake(b"toy tag", m, ek_vector, n=128):
            return k
        return _shake(b"toy implicit rejection", z, ct1, ct2, n=32)
