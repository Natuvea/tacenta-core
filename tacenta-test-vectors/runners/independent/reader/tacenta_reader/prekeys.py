"""Prekey store operations, from key-deletion.md, "Signed prekeys rotate, and
the retired one is kept for exactly one rotation", and session-persistence.md,
Prekey store.

Only the two rotations are modelled, and only because pass 7's new semantic
rule puts an obligation on them:

    "The consequence is an obligation on the operations instead of a check
    inside them: **every operation that signs a prekey signs under the identity
    whose public key is `identity_public`**, and an implementation whose API
    lets a caller supply some other identity refuses it rather than storing the
    result. Without that obligation an operation can build a state this reader
    would refuse, which is the one thing 'No state the operations produce is
    refused' (Stored curve public keys) undertakes cannot happen."
    (session-persistence.md, Prekey store, Semantic rules)

key-deletion.md gives the rest:

- `rotate_signed_prekey` "generates a fresh curve prekey, signs it under the
  identity whose public key the store holds as `identity_public` -- and
  refuses, changing nothing, if handed any other -- and gives it the next
  identifier; the key it replaces becomes the store's *previous* signed
  prekey, with its identifier and signature".
- "`rotate_kem` does the same for the signed last-resort KEM prekey ... The
  last-resort replay record above follows the key: entries made under the
  retired key stay while it can still decrypt ... and they are dropped when the
  next rotation wipes it".
- "both rotations take their identifier from the store's counter, the one
  `replenish` draws from, and once that counter stands at `u32::MAX` each of
  `rotate_signed_prekey` and `rotate_kem` returns without rotating, silently".
"""

import copy
from typing import Optional

from . import constants as K
from .curve25519 import x25519_public, xeddsa_sign
from .persistence import PrekeyStore
from .wire import encode_ec, encode_kem


class RotationRefused(Exception):
    """"refuses, changing nothing, if handed any other" identity."""


def _check_identity(store: PrekeyStore, identity_secret: bytes) -> None:
    if x25519_public(identity_secret) != store.identity_public:
        raise RotationRefused(
            "a rotation signs under the identity whose public key is identity_public")


def rotate_signed_prekey(store: PrekeyStore, identity_secret: bytes,
                         new_secret: bytes, z: bytes) -> PrekeyStore:
    _check_identity(store, identity_secret)
    if store.next_id >= K.U32_MAX:
        return store          # "returns without rotating, silently"
    out = copy.deepcopy(store)
    out.previous_signed = (store.signed_prekey_secret, store.signed_prekey_id,
                           store.signed_prekey_sig)
    out.signed_prekey_secret = bytes(new_secret)
    out.signed_prekey_id = store.next_id
    out.signed_prekey_sig = xeddsa_sign(identity_secret,
                                        encode_ec(x25519_public(new_secret)), z)
    out.next_id = store.next_id + 1
    return out


def rotate_kem(store: PrekeyStore, identity_secret: bytes,
               new_pair: bytes, z: bytes) -> PrekeyStore:
    _check_identity(store, identity_secret)
    if store.next_id >= K.U32_MAX:
        return store
    out = copy.deepcopy(store)
    wiped: Optional[int] = store.previous_kem[1] if store.previous_kem is not None else None
    out.previous_kem = (store.kem_pair, store.kem_id, store.kem_sig)
    out.kem_pair = bytes(new_pair)
    out.kem_id = store.next_id
    out.kem_sig = xeddsa_sign(identity_secret, encode_kem(new_pair[K.KEM_DK_LEN:]), z)
    out.next_id = store.next_id + 1
    # "a rotation drops a key's entries when it wipes the key"
    # (session-persistence.md, Prekey store, Semantic rules).
    out.seen = [e for e in store.seen if e[0] != wiped]
    return out
