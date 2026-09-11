"""Triple Ratchet combination and split, from protocol/triple-ratchet.md.

combine: section 7.2 parameters as the page states them -- the post-quantum
message key as salt, the classical one as IKM, COMBINE_INFO as info. Output
length "the AEAD's key length" is taken as 32 (GAPS.md G-20).

split_secret: the page says only that SK "is expanded into two by a key
derivation"; CONSTANTS.md gives SPLIT_INFO. Salt, IKM, output length and the
assignment of halves are hypotheses; salt/IKM/length confirmed by split.json
(GAPS.md G-19). Which half seeds which ratchet is not resolved.
"""

from typing import Tuple

from . import constants as K
from .kdf import hkdf_sha256


def combine(mk_ec: bytes, mk_pq: bytes) -> bytes:
    if len(mk_ec) != 32 or len(mk_pq) != 32:
        raise ValueError("both message keys are 32 bytes")
    return hkdf_sha256(mk_pq, mk_ec, K.COMBINE_INFO, 32)


def split_secret_bytes(sk: bytes) -> bytes:
    return hkdf_sha256(bytes(32), sk, K.SPLIT_INFO, 64)


def split_secret(sk: bytes) -> Tuple[bytes, bytes]:
    out = split_secret_bytes(sk)
    return out[:32], out[32:]
