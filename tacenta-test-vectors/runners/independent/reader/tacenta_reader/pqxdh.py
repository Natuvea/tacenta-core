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

from dataclasses import replace
from typing import Optional

from . import constants as K
from .kdf import hkdf_sha256, hmac_sha256
from .wire import InitialMessage, decode_ec, encode_ec


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


class KemPrekeyRefused(Exception):
    """The bundle's KEM prekey fails FIPS 203 section 7.2's input checks."""


def check_kem_prekey(ek: bytes, ek_len: int = K.MLKEM1024_EK_LEN) -> None:
    """session-establishment.md, Primitives, ML-KEM-1024, Validating the
    encapsulation key: before encapsulating, the key is 1,568 bytes and
    ByteEncode12(ByteDecode12(ek[0:1536])) equals ek[0:1536]; "Alice refuses a
    bundle whose key fails either check"."""
    from .persistence import _modulus_ok
    if len(ek) != ek_len:
        raise KemPrekeyRefused(f"KEM prekey is {len(ek)} bytes, not {ek_len}")
    if not _modulus_ok(bytes(ek[:1536])):
        raise KemPrekeyRefused("KEM prekey fails the FIPS 203 modulus check")


def check_kem_ciphertext(kem_ciphertext: bytes, ct_len: int = K.MLKEM1024_CT_LEN) -> None:
    """The recipient refuses the initial message at decapsulation, before any
    secret is derived, when the ciphertext is not the KEM's ciphertext length."""
    if len(kem_ciphertext) != ct_len:
        raise KemCiphertextRefused(f"KEM ciphertext is {len(kem_ciphertext)} bytes, not {ct_len}")


# ------------------------------------------ the last-resort replay record
# session-establishment.md, Replay, and "The fingerprint"; key-deletion.md;
# session-persistence.md, Prekey store (`seen`). Closes GAPS.md G-26.

class ReplayedLastResort(Exception):
    pass


class LastResortRecordFull(Exception):
    pass


def handshake_keys(message: InitialMessage):
    """"A handshake is accepted only if DecodeEC accepts both identity and
    ephemeral". Returns (IKA, EKA) as raw keys."""
    return decode_ec(message.identity), decode_ec(message.ephemeral)


def last_resort_fingerprint(message: InitialMessage) -> bytes:
    """input = u32(33) || identity || u32(33) || ephemeral
              || u32(len(kem_ciphertext)) || kem_ciphertext
              || one_time_prekey_id (4) || kem_prekey_id (4)
    fingerprint = HMAC-SHA256(key = LAST_RESORT_HANDSHAKE_LABEL, data = input)"""
    for name, v in (("identity", message.identity), ("ephemeral", message.ephemeral)):
        if len(v) != K.ENCODED_EC_LEN:
            raise ValueError(f"{name} keeps its curve byte and is 33 bytes")

    def u32(n):
        return n.to_bytes(4, "big")

    data = (u32(33) + bytes(message.identity) + u32(33) + bytes(message.ephemeral)
            + u32(len(message.kem_ciphertext)) + bytes(message.kem_ciphertext)
            + u32(message.one_time_prekey_id) + u32(message.kem_prekey_id))
    return hmac_sha256(K.LAST_RESORT_HANDSHAKE_LABEL, data)


def on_last_resort_path(store, kem_prekey_id: int) -> bool:
    """"its kem_prekey_id names Bob's current last-resort KEM prekey or the one
    the last rotation retired"."""
    return kem_prekey_id == store.kem_id or (store.previous_kem is not None and kem_prekey_id == store.previous_kem[1])


def check_last_resort(store, message: InitialMessage) -> Optional[bytes]:
    """Before decapsulation. Refuses a fingerprint any entry holds, whatever its
    tag (ReplayedLastResort), and a new handshake naming a key whose budget is
    spent (LastResortRecordFull); changes nothing. Returns the fingerprint to
    record once the initial ciphertext authenticates, or None off the path."""
    handshake_keys(message)
    if not on_last_resort_path(store, message.kem_prekey_id):
        return None
    fp = last_resort_fingerprint(message)
    if any(f == fp for _, f in store.seen):
        raise ReplayedLastResort("a record entry holds this fingerprint")
    if sum(1 for k, _ in store.seen if k == message.kem_prekey_id) >= K.MAX_LAST_RESORT_SEEN:
        raise LastResortRecordFull("the budget of the key this handshake names is spent")
    return fp


def receive_last_resort(store, message: InitialMessage, authenticate):
    """The order the page fixes. `authenticate` stands for decapsulating,
    deriving SK and decrypting the initial ciphertext; it raises on failure.
    The entry, tagged with kem_prekey_id, is added only once it returns.
    Returns (store, authenticate's result)."""
    fp = check_last_resort(store, message)
    result = authenticate()
    if fp is None:
        return store, result
    return replace(store, seen=list(store.seen) + [(message.kem_prekey_id, fp)]), result


def accept_repeated_initial(is_responder: bool, established_ephemeral: Optional[bytes],
                            message: InitialMessage) -> None:
    """An initial message on an existing session is accepted only by a
    responder's session and only if its `ephemeral` equals
    `established_ephemeral` byte for byte; no other field is compared."""
    if not is_responder or established_ephemeral is None:
        raise NotARepeatedInitial("not a responder's session")
    if bytes(message.ephemeral) != bytes(established_ephemeral):
        raise NotARepeatedInitial("ephemeral differs from established_ephemeral")
