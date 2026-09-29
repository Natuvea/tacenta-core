"""Identity keys and application signatures, from identities-and-devices.md.

    input     = "tacenta:application-signature:v1" || 0xFF || message
    signature = Sig(IK, input, Z)

The identity secret is 32 bytes, used as the X25519 private scalar and as the
XEdDSA private key. Prekey signatures carry no label, "so a signature made for
one is not accepted for the other".
"""

from . import constants as K
from .curve25519 import is_identity_key, x25519_public, xeddsa_sign, xeddsa_verify
from .wire import DecodeError, InvalidIdentityKey, is_canonical_curve_key


def public_key(identity_secret: bytes) -> bytes:
    if len(identity_secret) != 32:
        raise ValueError("an identity is one 32-byte secret")
    return x25519_public(identity_secret)


def application_input(message: bytes) -> bytes:
    return K.APP_SIGNATURE_PREFIX + bytes(message)


def sign_application(identity_secret: bytes, message: bytes, z: bytes) -> bytes:
    if len(identity_secret) != 32:
        raise ValueError("an identity is one 32-byte secret")
    return xeddsa_sign(identity_secret, application_input(message), z)


def verify_application(identity_public: bytes, message: bytes, signature: bytes) -> bool:
    """"A verifier rebuilds `input` from the message and verifies the signature
    under the published identity key. It first applies the identity-key rule to
    that key (Identity keys, above) and accepts no signature under a key that
    fails it." A boundary that "can only say yes or no, such as a verifier of an
    application signature, ... says no" (error-handling.md)."""
    if not is_identity_key(identity_public):
        return False
    return xeddsa_verify(identity_public, application_input(message), signature) is not None


def admit_identity_key(key: bytes, read_from_bytes: bool = True) -> bytes:
    """The rule at a boundary that admits a long-lived identity key.

    "Where a boundary reads a key from bytes, a key that is not canonical is
    still a decode failure, and the canonical rule is applied first."
    (Identity keys, A refusal.) So a non-canonical spelling is a DecodeError
    when `read_from_bytes`; a canonical key that fails the rule is
    InvalidIdentityKey. Returns the key."""
    key = bytes(key)
    if read_from_bytes and not is_canonical_curve_key(key):
        raise DecodeError("identity key is not the canonical encoding of a curve public key")
    if not is_identity_key(key):
        raise InvalidIdentityKey("not an identity key")
    return key
