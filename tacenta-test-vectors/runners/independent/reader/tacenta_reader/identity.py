"""Identity keys and application signatures, from identities-and-devices.md.

    input     = "tacenta:application-signature:v1" || 0xFF || message
    signature = Sig(IK, input, Z)

The identity secret is 32 bytes, used as the X25519 private scalar and as the
XEdDSA private key. Prekey signatures carry no label, "so a signature made for
one is not accepted for the other".
"""

from . import constants as K
from .curve25519 import x25519_public, xeddsa_sign, xeddsa_verify


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
    return xeddsa_verify(identity_public, application_input(message), signature) is not None
