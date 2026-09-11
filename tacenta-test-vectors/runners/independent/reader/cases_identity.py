"""identities-and-devices.md (identity secret, application signatures) and
session-establishment.md (repeated initial message, non-contributory
definition). No vectors."""

from _casekit import accepts, registry, rejects
from tacenta_reader import constants as K
from tacenta_reader import curve25519, identity, pqxdh, wire

CASES, case = registry()
ID = "identities-and-devices.md"
SE = "session-establishment.md"

SECRET = bytes(range(40, 72))
PUB = identity.public_key(SECRET)
Z = b"\x5a" * 64


@case("ID-01 the application label is 32 ASCII bytes, 33 with 0xFF; a signature over label || 0xFF || message verifies under the identity key",
      f"{ID} Application signatures: input = \"tacenta:application-signature:v1\" || 0xFF || message")
def _():
    assert len(K.APP_SIGNATURE_LABEL) == 32 and len(K.APP_SIGNATURE_PREFIX) == 33
    for msg in (b"", b"server challenge 1234", b"\xff" * 100):
        sig = identity.sign_application(SECRET, msg, Z)
        assert identity.verify_application(PUB, msg, sig)
        assert curve25519.xeddsa_verify(PUB, K.APP_SIGNATURE_PREFIX + msg, sig) is not None
        assert not identity.verify_application(PUB, msg + b"\x00", sig)


@case("ID-02 the label keeps the two uses apart: a prekey signature is not an application signature over the same bytes, nor the reverse",
      f"{ID} Application signatures: a signature made for one is not accepted for the other")
def _():
    spk = curve25519.x25519_public(b"\x21" * 32)
    prekey_sig = curve25519.xeddsa_sign(SECRET, wire.encode_ec(spk), Z)
    assert curve25519.xeddsa_verify(PUB, wire.encode_ec(spk), prekey_sig) is not None
    assert not identity.verify_application(PUB, wire.encode_ec(spk), prekey_sig)
    app_sig = identity.sign_application(SECRET, wire.encode_ec(spk), Z)
    assert curve25519.xeddsa_verify(PUB, wire.encode_ec(spk), app_sig) is None


@case("ID-03 one 32-byte secret, used as it is: the X25519 scalar is clamped when used, so DH under the raw and the clamped bytes agree",
      f"{ID} The identity key's secret: the X25519 private scalar, clamped when used")
def _():
    rejects(identity.public_key, SECRET[:31], exc=ValueError)
    clamped = bytearray(SECRET)
    clamped[0] &= 248
    clamped[31] = (clamped[31] & 127) | 64
    peer = curve25519.x25519_public(b"\x33" * 32)
    assert curve25519.x25519(SECRET, peer) == curve25519.x25519(bytes(clamped), peer)


@case("SE-01 a repeated initial message is accepted only by a responder's session and only if ephemeral matches established_ephemeral byte for byte",
      f"{SE} Receiving the initial message: accepts it only if it is a responder's session and the message's ephemeral field equals ... (NotARepeatedInitial)")
def _():
    eph = b"\x05" + b"\x0b" * 32
    m = wire.InitialMessage(identity=b"\x05" + b"\x0a" * 32, ephemeral=eph, kem_ciphertext=b"\x01" * 1568,
                            signed_prekey_id=1, one_time_prekey_id=2, kem_prekey_id=3, ratchet_message=b"")
    accepts(pqxdh.accept_repeated_initial, True, eph, m)
    # no other field is compared
    other = wire.InitialMessage(identity=b"\x05" + b"\x77" * 32, ephemeral=eph, kem_ciphertext=b"",
                                signed_prekey_id=9, one_time_prekey_id=0, kem_prekey_id=9, ratchet_message=b"zz")
    accepts(pqxdh.accept_repeated_initial, True, eph, other)
    rejects(pqxdh.accept_repeated_initial, True, b"\x05" + b"\x0c" * 32, m, exc=pqxdh.NotARepeatedInitial)
    rejects(pqxdh.accept_repeated_initial, False, None, m, exc=pqxdh.NotARepeatedInitial)
    rejects(pqxdh.accept_repeated_initial, False, eph, m, exc=pqxdh.NotARepeatedInitial)


@case("SE-02 non-contributory means all 32 output bytes zero; every low-order input gives it and a normal key does not",
      f"{SE} Notation: A DH output is non-contributory when all 32 of its bytes are zero")
def _():
    p = 2 ** 255 - 19
    for u in (0, 1, p - 1, p, p + 1):
        out = curve25519.x25519(SECRET, (u % 2 ** 256).to_bytes(32, "little"))
        if out == bytes(32):
            rejects(curve25519.x25519_contributory, SECRET, (u % 2 ** 256).to_bytes(32, "little"),
                    exc=curve25519.NonContributory)
    assert curve25519.x25519(SECRET, bytes(32)) == bytes(32)
    accepts(curve25519.x25519_contributory, SECRET, PUB)
