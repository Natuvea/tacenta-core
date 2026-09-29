"""Admitting an identity key at the two boundaries that read one off the wire
(pass 13).

From identities-and-devices.md, Identity keys, and session-establishment.md,
Sending the initial message and Receiving the initial message. Nothing here is
taken from a vector's bytes.

Each function runs the establishment steps that the page orders around the
identity-key rule, and stops where this reader runs out of specification it can
execute without ML-KEM-1024:

- `initiator_prefix`: the initiator's steps from the fetched bundle to the four
  Diffie-Hellman outputs. Encapsulation itself (`PQKEM-ENC`) is not computed;
  the two random draws it and the ephemeral key need are made, in the page's
  order, and the encapsulation is recorded as the point where this reader
  stops. So the shared secret `SK`, the initial ciphertext and the initial
  message are not produced.
- `responder_prefix`: the responder's steps from the initial message to the
  point just before it decapsulates. It finds the signed prekey and the KEM
  prekey the message names, applies the identity-key rule, looks up the
  one-time curve prekey, and checks the KEM ciphertext's length. The prekey
  store is read-only throughout (Receiving the initial message: "The prekey
  store is read-only until the ratchet message inside the initial message has
  authenticated"), and this function never reaches authentication.

Counters record the work the page says a refusal must precede: signatures
verified, random values drawn, agreements computed, encapsulations made and
private keys used. "The refusal comes before the work it protects: no random
value is drawn, no agreement computed, no private key used and no stored state
changed."
"""

import hashlib
from dataclasses import dataclass, field
from typing import List, Optional

from . import constants as K
from . import curve25519, persistence, pqxdh, wire
from .curve25519 import x25519_public


class UnknownPrekey(Exception):
    """"the recipient refuses the initial message as naming a prekey it does
    not hold, the same refusal as for any other unknown identifier"
    (message-format.md, Key identifiers)."""


class Rng:
    """A deterministic byte source that records every draw. Not random: the
    reader needs to see that a refusal drew nothing."""

    def __init__(self, seed: bytes = b"tacenta-reader admission"):
        self._seed = seed
        self._n = 0
        self.draws: List[int] = []

    def draw(self, n: int) -> bytes:
        self.draws.append(n)
        out = b""
        while len(out) < n:
            out += hashlib.sha256(self._seed + self._n.to_bytes(8, "big")).digest()
            self._n += 1
        return out[:n]


@dataclass
class Counters:
    signatures_verified: int = 0
    agreements: int = 0
    encapsulations: int = 0
    private_keys_used: int = 0
    stored_state_changes: int = 0


@dataclass
class InitiatorPrefix:
    identity_key: bytes          # the identity key the initiator admitted
    dh: tuple                    # DH1..DH4 (DH4 None without a one-time curve prekey)
    ephemeral_secret: bytes
    encapsulation_m: bytes
    stopped_at: str = "encapsulation"


def initiator_prefix(bundle, initiator_identity_secret: bytes, rng: Rng,
                     counters: Optional[Counters] = None,
                     expected_identity: Optional[bytes] = None) -> InitiatorPrefix:
    """Sending the initial message, in the page's order.

    1. The bundle decodes (a decode failure otherwise), unless it arrives
       already decoded.
    2. "She also refuses a bundle before encapsulating when its identity key is
       not the one she set out to reach (when she names one), when its one-time
       curve prekey and that prekey's identifier disagree about whether one is
       present, or when its identity key, signed prekey or one-time curve
       prekey is not the canonical encoding of a curve public key."
    3. "A bundle whose canonical `IKB` is not an identity key is refused as an
       invalid identity key. She makes that check after the presence, pinning
       and canonical checks above and before she verifies either signature,
       draws a random value or encapsulates."
    4. She verifies both signatures under `IKB` and aborts if either fails.
    5. She validates the KEM prekey (FIPS 203 section 7.2) before encapsulating.
    6. "She then generates EKA, encapsulates (CT, SS) = PQKEM-ENC(PQPKB), and
       computes" DH1 to DH4, refusing a non-contributory output. The draws are
       EKA's 32 bytes and the encapsulation's 32 (Primitives, ML-KEM-1024:
       "Encapsulation draws 32 random bytes m").
    """
    c = counters if counters is not None else Counters()
    b = wire.decode_bundle(bundle) if isinstance(bundle, (bytes, bytearray)) else bundle

    def counting_verify(u, msg, sig):
        c.signatures_verified += 1
        return curve25519.xeddsa_verify(u, msg, sig)

    wire.initiator_check_bundle(b, expected_identity, verify=counting_verify)
    pqxdh.check_kem_prekey(b.kem_prekey)
    eka = rng.draw(32)
    m = rng.draw(32)
    c.encapsulations += 0   # PQKEM-ENC is not implemented; see the module docstring
    ika = bytes(initiator_identity_secret)

    def dh(k, u):
        c.agreements += 1
        return curve25519.x25519_contributory(k, u)

    dh1 = dh(ika, b.signed_prekey)
    dh2 = dh(eka, b.identity_key)
    dh3 = dh(eka, b.signed_prekey)
    dh4 = dh(eka, b.one_time_prekey) if b.one_time_prekey is not None else None
    return InitiatorPrefix(b.identity_key, (dh1, dh2, dh3, dh4), eka, m)


@dataclass
class ResponderPrefix:
    identity_key: bytes                  # IKA, as the message carried it
    signed_prekey_id: int
    kem_prekey_id: int
    one_time_prekey_id: int
    stopped_at: str = "decapsulation"


def _find_signed_prekey(store, prekey_id: int):
    """The current signed prekey, or the one the last rotation retired
    (key-deletion.md: the retired one "is honoured by `establish_responder` for
    an initial message that still names it")."""
    if prekey_id == store.signed_prekey_id:
        return store.signed_prekey_secret
    if store.previous_signed is not None and prekey_id == store.previous_signed[1]:
        return store.previous_signed[0]
    return None


def _find_kem_prekey(store, prekey_id: int):
    """The last-resort KEM prekey, the retired one, or a one-time KEM prekey."""
    if prekey_id == store.kem_id:
        return store.kem_pair
    if store.previous_kem is not None and prekey_id == store.previous_kem[1]:
        return store.previous_kem[0]
    for i, kp, _sig in store.kem_one_time:
        if i == prekey_id:
            return kp
    return None


def responder_prefix(store, message_bytes: bytes,
                     counters: Optional[Counters] = None) -> ResponderPrefix:
    """Receiving the initial message, in the page's order.

    1. The message decodes (a decode failure otherwise; a re-spelled `identity`
       or `ephemeral` does not decode).
    2. "Bob reads IKA and EKA, uses the identifiers to load the matching
       private keys": the signed prekey and the KEM prekey the message names.
       An identifier he does not hold is refused as naming a prekey he does not
       hold.
    3. "Bob refuses the message as an invalid identity key when IKA is not an
       identity key. He makes that check once he has found the signed prekey
       and the KEM prekey the message names, and before he looks up a one-time
       prekey, decapsulates, or uses any private key on the message, so an
       unknown one-time identifier or a ciphertext of the wrong length behind
       such an IKA is still refused for the identity. The refusal changes
       nothing."
    4. The one-time curve prekey, when the message names one (identifier 0 is
       "none").
    5. Decapsulation refuses a ciphertext of any length other than 1,568 bytes,
       "before any secret is derived", and "changes nothing".

    `store` is the responder's prekey store, as stored bytes (read here) or as
    the object a caller read, so that a caller can compare it with what it read
    ("Every refusal ... leaves the whole store exactly as it was").

    The function returns where it can go no further without ML-KEM.
    """
    c = counters if counters is not None else Counters()
    if isinstance(store, (bytes, bytearray)):
        store = persistence.prekey_store_from_bytes(bytes(store))
    msg = wire.decode_initial(message_bytes)
    if _find_signed_prekey(store, msg.signed_prekey_id) is None:
        raise UnknownPrekey("the message names a signed prekey the store does not hold")
    if _find_kem_prekey(store, msg.kem_prekey_id) is None:
        raise UnknownPrekey("the message names a KEM prekey the store does not hold")
    ika = wire.decode_ec(msg.identity)
    if not curve25519.is_identity_key(ika):
        raise wire.InvalidIdentityKey("IKA is not an identity key")
    if msg.one_time_prekey_used and all(i != msg.one_time_prekey_id for i, _ in store.one_time):
        raise UnknownPrekey("the message names a one-time curve prekey the store does not hold")
    pqxdh.check_kem_ciphertext(msg.kem_ciphertext)
    return ResponderPrefix(ika, msg.signed_prekey_id, msg.kem_prekey_id, msg.one_time_prekey_id)


def responder_agreements(store, message_bytes: bytes, identity_secret: bytes):
    """The responder's four Diffie-Hellman outputs for a message that reached
    the end of `responder_prefix`: DH1 = DH(SPKB, IKA), DH2 = DH(IKB, EKA),
    DH3 = DH(SPKB, EKA), DH4 = DH(OPKB, EKA) when the message names a one-time
    curve prekey, each refused when it is not contributory.

    The page orders these after decapsulation (Receiving the initial message:
    "recovers SS ..., repeats the same DH and KDF computations"). They need no
    KEM secret, so the reader can compute them for a message it cannot open, to
    check that the store's secrets and the message's keys agree in a
    contributory way. Nothing is stored or removed."""
    msg = wire.decode_initial(message_bytes)
    spkb = _find_signed_prekey(store, msg.signed_prekey_id)
    opkb = None
    if msg.one_time_prekey_used:
        opkb = next(sec for i, sec in store.one_time if i == msg.one_time_prekey_id)
    return pqxdh.responder_agreements(bytes(identity_secret), spkb, opkb,
                                      wire.decode_ec(msg.identity), wire.decode_ec(msg.ephemeral))
