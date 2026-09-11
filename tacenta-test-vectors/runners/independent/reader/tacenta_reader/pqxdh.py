"""PQXDH shared secret, from tacenta-spec/protocol/session-establishment.md.

KDF(KM) = HKDF-SHA256(salt = 32 zero bytes, ikm = F || KM, info = SK_INFO, 32)
KM = DH1 || DH2 || DH3 [|| DH4] || SS

The KEM (ML-KEM-1024) is not implemented; SS is an input.
"""

from typing import Optional

from . import constants as K
from .kdf import hkdf_sha256
from .wire import encode_ec


def kdf(km: bytes) -> bytes:
    return hkdf_sha256(bytes(32), K.PQXDH_F + bytes(km), K.SK_INFO, 32)


def shared_secret(dh1: bytes, dh2: bytes, dh3: bytes, dh4: Optional[bytes], ss: bytes) -> bytes:
    for name, v in (("dh1", dh1), ("dh2", dh2), ("dh3", dh3)) + ((("dh4", dh4),) if dh4 is not None else ()):
        if len(v) != 32:
            raise ValueError(f"{name} must be a 32-byte X25519 output")
    km = dh1 + dh2 + dh3 + (dh4 if dh4 is not None else b"") + ss
    return kdf(km)


def associated_data(ika_pub: bytes, ikb_pub: bytes) -> bytes:
    """AD = EncodeEC(IKA) || EncodeEC(IKB), fixed 66 bytes."""
    return encode_ec(ika_pub) + encode_ec(ikb_pub)


def initiator_agreements(ika_priv: bytes, eka_priv: bytes, ikb_pub: bytes,
                         spkb_pub: bytes, opkb_pub: Optional[bytes]):
    """DH1..DH4 for the initiator, refusing non-contributory outputs."""
    from .curve25519 import x25519_contributory
    dh1 = x25519_contributory(ika_priv, spkb_pub)
    dh2 = x25519_contributory(eka_priv, ikb_pub)
    dh3 = x25519_contributory(eka_priv, spkb_pub)
    dh4 = x25519_contributory(eka_priv, opkb_pub) if opkb_pub is not None else None
    return dh1, dh2, dh3, dh4


def responder_agreements(ikb_priv: bytes, spkb_priv: bytes, opkb_priv: Optional[bytes],
                         ika_pub: bytes, eka_pub: bytes):
    from .curve25519 import x25519_contributory
    dh1 = x25519_contributory(spkb_priv, ika_pub)
    dh2 = x25519_contributory(ikb_priv, eka_pub)
    dh3 = x25519_contributory(spkb_priv, eka_pub)
    dh4 = x25519_contributory(opkb_priv, eka_pub) if opkb_priv is not None else None
    return dh1, dh2, dh3, dh4
