"""PQXDH, from tacenta-spec/protocol/session-establishment.md.

KDF(KM) = HKDF-SHA256(salt = 32 zero bytes, ikm = F || KM, info = SK_INFO, 32)
KM = DH1 || DH2 || DH3 [|| DH4] || SS

A DH output is non-contributory "when all 32 of its bytes are zero" and is
refused wherever one is computed (Notation). The KEM (ML-KEM-1024) is not
implemented; SS is an input. Also here: the responder's refusal of a KEM
ciphertext of the wrong length (message-format.md, Initial message: a
refusal, not a decode failure) and the repeated-initial-message rule
(Receiving the initial message).
"""

from typing import Optional

from . import constants as K
from .kdf import hkdf_sha256
from .wire import InitialMessage, encode_ec


class KemCiphertextRefused(Exception):
    """"Decapsulation refuses a ciphertext that is not the KEM's ciphertext
    length ... The refusal is not a decode failure." """


class NotARepeatedInitial(Exception):
    pass


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


def check_kem_ciphertext(kem_ciphertext: bytes, ct_len: int = K.MLKEM1024_CT_LEN) -> None:
    """The recipient refuses the initial message at decapsulation, before any
    secret is derived, when the ciphertext is not the KEM's ciphertext length."""
    if len(kem_ciphertext) != ct_len:
        raise KemCiphertextRefused(f"KEM ciphertext is {len(kem_ciphertext)} bytes, not {ct_len}")


def accept_repeated_initial(is_responder: bool, established_ephemeral: Optional[bytes],
                            message: InitialMessage) -> None:
    """An initial message on an existing session is accepted only by a
    responder's session and only if its `ephemeral` equals
    `established_ephemeral` byte for byte; no other field is compared."""
    if not is_responder or established_ephemeral is None:
        raise NotARepeatedInitial("not a responder's session")
    if bytes(message.ephemeral) != bytes(established_ephemeral):
        raise NotARepeatedInitial("ephemeral differs from established_ephemeral")
