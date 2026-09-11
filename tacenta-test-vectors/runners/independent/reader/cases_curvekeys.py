"""Pass 4. message-format.md, "Curve public keys", and the repeated initial
message over a live session (session-establishment.md, Receiving the initial
message).

The three files under vectors/malformed-input/ (composite-header-decode,
prekey-bundle-decode, initial-message-decode; run as vectors) pin each key
position's refusal with bit 255 set and as 9 + p, and its acceptance at p - 1.
These cases cover what those do not:
- the boundary at exactly p, and every value from p to 2^255 - 1;
- that the refusal is a decode failure, and not a later refusal;
- which fields are held to the rule and which are not;
- the repeated initial message, which no vector pins.
"""

import hashlib
import random
from dataclasses import replace

import cases_braid as BRC
import negative_cases as NC
from _casekit import accepts, put, registry, rejects
from tacenta_reader import constants as K
from tacenta_reader import curve25519, pqxdh, triple, wire
from tacenta_reader.persistence import SessionState

CASES, case = registry()
MF = "message-format.md"
SE = "session-establishment.md"
CK = f"{MF} Curve public keys"
P = K.CURVE25519_P
NINE = (9).to_bytes(32, "little")
R = random.Random(20260911_4)


def spellings(key):
    """Every other 32-byte string X25519 reads as `key` (RFC 7748, section 5,
    masks bit 255 and reduces mod p): bit 255 set, and, when it still fits
    below 2^255, the value plus p, alone and with bit 255 set."""
    u = int.from_bytes(key, "little")
    assert u < P, "spellings() takes a canonical key"
    out = [(u | 1 << 255).to_bytes(32, "little")]
    if u + P < 2 ** 255:
        out += [(u + P).to_bytes(32, "little"), ((u + P) | 1 << 255).to_bytes(32, "little")]
    return out


# ------------------------------------------------------------- the rule itself

@case("CK-01 the rule: 32 bytes read little-endian are accepted exactly when below p; 0, 1, 9 and p - 1 are accepted; every value from p to 2^255 - 1 is refused, and so is bit 255 set on any key; X25519 reads each refused spelling as the canonical key; honest public keys are never refused",
      f"{CK}: Read the 32 bytes as a 256-bit little-endian integer: the key is accepted exactly when that value is below p ... An honest key generator produces neither ... A refused key is a decode failure")
def _():
    for v in (0, 1, 9, P - 19, P - 1, R.randrange(P)):
        accepts(wire.check_curve_key, v.to_bytes(32, "little"))
    for v in range(P, 2 ** 255):                                   # the 19 values at or above p with bit 255 clear
        rejects(wire.check_curve_key, v.to_bytes(32, "little"), exc=wire.DecodeError)
    for v in (0, 9, P - 1, R.randrange(P), 2 ** 255 - 1):
        rejects(wire.check_curve_key, (v | 1 << 255).to_bytes(32, "little"), exc=wire.DecodeError)
    secret = b"\x31" * 32
    for key in (NINE, (P - 1).to_bytes(32, "little"), R.randrange(P).to_bytes(32, "little")):
        for s in spellings(key):
            assert curve25519.x25519(secret, s) == curve25519.x25519(secret, key)
    for i in range(64):
        accepts(wire.check_curve_key, curve25519.x25519_public(hashlib.sha256(b"honest %d" % i).digest()))


# ---------------------------------------------------------------- the decoders

@case("CK-02 a ratchet message's dh: every other spelling of a key is refused by the ratchet-message and composite-header decoders as a decode failure, and CONCAT refuses such a header; the counters, codeword and ciphertext keep all their values; a live session refuses a re-spelled message as a decode failure, before its non-contributory check and authentication, and still reads the original",
      f"{MF} Ratchet message: It also rejects a dh that is not the canonical encoding of a curve public key; {CK}: a ratchet message's dh")
def _():
    for key in (b"\x0a" * 32, NINE, (P - 1).to_bytes(32, "little"), bytes(32)):
        accepts(wire.decode_ratchet_message, wire.encode_ratchet_message(NC.header(dh=key), b"\xff" * 40))
        for s in spellings(key):
            raw = wire.encode_ratchet_message(NC.header(dh=s), b"")
            rejects(wire.decode_ratchet_message, raw, exc=wire.DecodeError)
            rejects(wire.decode_composite, raw, exc=wire.DecodeError)
            rejects(wire.concat_ad, b"ad", raw, exc=wire.EncodeError)
    h = NC.header(pn=0xFFFFFFFF, n=0xFFFFFFFF, pq_epoch=K.U64_MAX, pq_n=K.U64_MAX, ag_epoch=K.U64_MAX,
                  codeword=wire.Codeword(0xFFFF, b"\xff" * 32))
    assert accepts(wire.decode_ratchet_message, wire.encode_ratchet_message(h, b"\xff" * 32)) == (h, b"\xff" * 32)
    alice, bob, ag_a, ag_b = BRC.session_pair()
    alice, msg = triple.encrypt(alice, ag_a, b"hello")
    for s in spellings(msg[2:34]):
        e = rejects(triple.decrypt, bob, ag_b, msg[:2] + s + msg[34:], BRC.fresh(), exc=Exception)
        assert isinstance(e, wire.DecodeError), f"refused as {type(e).__name__}, not as a decode failure"
    assert accepts(triple.decrypt, bob, ag_b, msg, BRC.fresh())[1] == b"hello"


@case("CK-03 a prekey bundle's identity_key, signed_prekey and present one_time_prekey: each other spelling is refused at decode, as a decode failure, even when the signature over it verifies; p - 1 in all three positions decodes; a present one-time prekey u = 0, canonical but of low order, decodes and is left to the non-contributory check; an absent one-time prekey's padding is fixed to zeros; the KEM prekey and the signatures are not held to the rule",
      f"{MF} Prekey bundle: A decoder also refuses a bundle whose identity_key, signed_prekey or present one_time_prekey is not the canonical encoding ... The padding behind an absent one-time prekey is not a key; {CK}")
def _():
    z = b"\x5c" * 64
    base = NC.signed_bundle(True)
    assert accepts(wire.decode_bundle, wire.encode_bundle(base)) == base
    for key in (NC.SPK_PUB, NINE):
        for s in spellings(key):
            b = replace(base, signed_prekey=s, signed_prekey_signature=curve25519.xeddsa_sign(NC.IK_PRIV, wire.encode_ec(s), z))
            assert curve25519.xeddsa_verify(NC.IK_PUB, wire.encode_ec(s), b.signed_prekey_signature) is not None
            # its signature does not refuse it. Pass 4 had the initiator accept it; from pass 5 she refuses it
            # herself as well (session-establishment.md, Sending the initial message; SK-07)
            rejects(wire.initiator_check_bundle, b, exc=wire.BundleRefused)
            rejects(wire.decode_bundle, wire.encode_bundle(b), exc=wire.DecodeError)
    for key in (NC.IK_PUB, NINE):
        for s in spellings(key):
            e = rejects(wire.decode_bundle, wire.encode_bundle(replace(base, identity_key=s)), exc=Exception)
            assert isinstance(e, wire.DecodeError), f"refused as {type(e).__name__}, not as a decode failure"
        rejects(wire.initiator_check_bundle, replace(base, identity_key=spellings(key)[0]), exc=wire.BundleRefused)
    for key in (NC.OPK_PUB, NINE):
        for s in spellings(key):
            rejects(wire.decode_bundle, wire.encode_bundle(replace(base, one_time_prekey=s)), exc=wire.DecodeError)
    top = (P - 1).to_bytes(32, "little")
    edge = replace(base, identity_key=top, signed_prekey=top, one_time_prekey=top)
    assert accepts(wire.decode_bundle, wire.encode_bundle(edge)) == edge
    low = accepts(wire.decode_bundle, wire.encode_bundle(replace(base, one_time_prekey=bytes(32))))
    rejects(curve25519.x25519_contributory, b"\x44" * 32, low.one_time_prekey, exc=curve25519.NonContributory)
    absent = wire.encode_bundle(NC.signed_bundle(False))
    rejects(wire.decode_bundle, put(absent, NC.OFF_OT_KEY + 31, 0x80), exc=wire.DecodeError)
    loose = replace(base, kem_prekey=b"\xff" * K.MLKEM1024_EK_LEN, signed_prekey_signature=b"\xff" * 64,
                    kem_prekey_signature=b"\xff" * 64)
    accepts(wire.decode_bundle, wire.encode_bundle(loose))


@case("CK-04 an initial message's identity and ephemeral: every other spelling of either key, curve byte unchanged, is refused as a decode failure; p - 1 decodes in both; over a sweep of byte changes to both fields, every message the decoder returns has keys DecodeEC accepts; kem_ciphertext and ratchet_message are not held to the rule",
      f"{MF} Initial message: It also refuses ... an identity or ephemeral whose thirty-two key bytes are not the canonical encoding ... every key this decoder returns is one DecodeEC accepts; {CK}: DecodeEC states the same rule, so it refuses no key this decoder returned")
def _():
    base = wire.InitialMessage(identity=b"\x05" + NC.IK_PUB, ephemeral=b"\x05" + NC.OPK_PUB, kem_ciphertext=b"\xff" * 1568,
                               signed_prekey_id=1, one_time_prekey_id=0, kem_prekey_id=2, ratchet_message=b"\xff" * 64)
    assert accepts(wire.decode_initial, wire.encode_initial(base)) == base
    for field in ("identity", "ephemeral"):
        for key in (NC.IK_PUB, NINE, (P - 1).to_bytes(32, "little")):
            m = replace(base, **{field: b"\x05" + key})
            assert accepts(wire.decode_initial, wire.encode_initial(m)) == m
            for s in spellings(key):
                rejects(wire.decode_initial, wire.encode_initial(replace(base, **{field: b"\x05" + s})), exc=wire.DecodeError)
    raw = wire.encode_initial(base)
    accepted = 0
    for off in range(2, 68):
        for x in range(1, 256, 17):
            try:
                got = wire.decode_initial(put(raw, off, raw[off] ^ x))
            except wire.DecodeError:
                continue
            accepted += 1
            accepts(wire.decode_ec, got.identity)
            accepts(wire.decode_ec, got.ephemeral)
    assert accepted > 500


@case("CK-05 why the rule: a second spelling names the same key to X25519 but is a second identity wherever bytes are the identity: a signature over EncodeEC(key) does not verify over the other spelling, and PQXDH's AD and the last-resort fingerprint differ",
      f"{CK}: A key's bytes serve as its identity in several places ... A second spelling of one key would give it a second identity in each of them")
def _():
    z = b"\x5d" * 64
    for key in (NC.SPK_PUB, NINE):
        sig = curve25519.xeddsa_sign(NC.IK_PRIV, wire.encode_ec(key), z)
        assert curve25519.xeddsa_verify(NC.IK_PUB, wire.encode_ec(key), sig) is not None
        m = wire.InitialMessage(b"\x05" + NC.IK_PUB, b"\x05" + key, b"", 1, 0, 2, b"")
        for s in spellings(key):
            assert curve25519.x25519(b"\x21" * 32, s) == curve25519.x25519(b"\x21" * 32, key)
            assert curve25519.xeddsa_verify(NC.IK_PUB, wire.encode_ec(s), sig) is None
            assert pqxdh.associated_data(s, NC.IK_PUB) != pqxdh.associated_data(key, NC.IK_PUB)
            assert pqxdh.last_resort_fingerprint(replace(m, ephemeral=b"\x05" + s)) != pqxdh.last_resort_fingerprint(m)


# ------------------------------------------- the repeated initial message, live

EKA = curve25519.x25519_public(b"\x65" * 32)


def responder_session(**kw):
    """The persisted fields the rule reads (session-persistence.md, Session):
    the role from established_ephemeral, peer_identity_public raw, and
    established_ephemeral as the EncodeEC value the establishing message
    carried. The ratchet halves are driven separately, by Live."""
    base = dict(triple=None, braid=None, ratchet_private=b"", identity_ad=BRC.AD, our_identity_public=BRC.IKB,
                peer_identity_public=BRC.IKA, established_ephemeral=wire.encode_ec(EKA))
    base.update(kw)
    return SessionState(**base)


def wrap(inner, **kw):
    base = dict(identity=wire.encode_ec(BRC.IKA), ephemeral=wire.encode_ec(EKA), kem_ciphertext=bytes(range(256)) * 6 + bytes(32),
                signed_prekey_id=1, one_time_prekey_id=7, kem_prekey_id=4, ratchet_message=inner)
    base.update(kw)
    return wire.encode_initial(wire.InitialMessage(**base))


class Live:
    """Bob's Triple Ratchet half over the Braid. A call is the session's
    ordinary receive of the inner ratchet message; the state is adopted only
    when the receive succeeds (triple-ratchet.md commit rules)."""

    def __init__(self, party, ag):
        self.party, self.ag, self.calls = party, ag, 0

    def __call__(self, ratchet_message):
        self.calls += 1
        self.party, plaintext = triple.decrypt(self.party, self.ag, ratchet_message, BRC.fresh())
        return plaintext


@case("SE-06 an initial message on an existing session must first decode: a repeat whose identity or ephemeral is re-spelled (bit 255 set, 9 + p, or both), or carries another curve byte, is refused as a decode failure, not as NotARepeatedInitial, and nothing inside is decrypted; so no spelling of a genuine repeat's fields but its own reaches the comparisons",
      f"{SE} Receiving the initial message: It must first decode, so a message whose identity or ephemeral is re-spelled is refused as a decode failure ...; Both comparisons are against canonical encodings, and a key has one")
def _():
    alice, bob, ag_a, ag_b = BRC.session_pair()
    alice, m1 = triple.encrypt(alice, ag_a, b"first")
    live = Live(bob, ag_b)
    s = responder_session()
    for field, key in (("identity", BRC.IKA), ("ephemeral", EKA)):
        for sp in spellings(key):
            e = rejects(pqxdh.receive_repeated_initial, s, wrap(m1, **{field: b"\x05" + sp}), live, exc=Exception)
            assert isinstance(e, wire.DecodeError), f"refused as {type(e).__name__}, not as a decode failure"
    raw = wrap(m1)
    for off in (2, 35):
        rejects(pqxdh.receive_repeated_initial, s, put(raw, off, 0x08), live, exc=wire.DecodeError)
    assert live.calls == 0
    inner = []
    s9 = responder_session(peer_identity_public=NINE, established_ephemeral=b"\x05" + NINE)
    genuine = dict(identity=b"\x05" + NINE, ephemeral=b"\x05" + NINE, kem_ciphertext=b"", signed_prekey_id=1,
                   one_time_prekey_id=0, kem_prekey_id=2, ratchet_message=b"inner")
    assert accepts(pqxdh.receive_repeated_initial, s9, wire.encode_initial(wire.InitialMessage(**genuine)),
                   lambda rm: inner.append(rm) or b"ok") == b"ok"
    for field in ("identity", "ephemeral"):
        for sp in spellings(NINE):
            raw9 = wire.encode_initial(wire.InitialMessage(**{**genuine, field: b"\x05" + sp}))
            rejects(pqxdh.receive_repeated_initial, s9, raw9, lambda rm: inner.append(rm), exc=wire.DecodeError)
    assert inner == [b"inner"]


@case("SE-07 over a live Triple Ratchet session: a repeat whose kem_ciphertext and identifiers differ, around a message the session has not read, yields that plaintext once, as the unaltered repeat would; a wrapper around a message already read yields nothing and changes nothing; another identity or ephemeral is refused with nothing decrypted; an initiator's session refuses every repeat; the message a refused repeat carried is still read afterwards",
      f"{SE} Receiving the initial message: It then decrypts the ratchet message inside ... Ignoring them is safe ... So a repeat whose kem_ciphertext or identifiers differ from the establishing message's ... yields that message's plaintext once")
def _():
    alice, bob, ag_a, ag_b = BRC.session_pair()
    alice, m1 = triple.encrypt(alice, ag_a, b"first")
    alice, m2 = triple.encrypt(alice, ag_a, b"second")
    alice, m3 = triple.encrypt(alice, ag_a, b"third")
    live = Live(bob, ag_b)
    assert live(m1) == b"first"                       # read when the session was established
    s = responder_session()

    def yields_nothing(raw):
        before, calls = live.party, live.calls
        e = rejects(pqxdh.receive_repeated_initial, s, raw, live, exc=Exception)
        assert not isinstance(e, (wire.DecodeError, pqxdh.NotARepeatedInitial)), f"refused as {type(e).__name__} before decrypting"
        assert live.calls == calls + 1 and live.party is before

    yields_nothing(wrap(m1))                          # the unaltered repeat, around a message already read
    altered = wrap(m2, kem_ciphertext=b"", signed_prekey_id=0, one_time_prekey_id=0, kem_prekey_id=0xFFFFFFFF)
    assert accepts(pqxdh.receive_repeated_initial, s, altered, live) == b"second"
    yields_nothing(altered)
    yields_nothing(wrap(m2))
    calls = live.calls
    other = curve25519.x25519_public(b"\x66" * 32)
    for kw in (dict(identity=wire.encode_ec(other)), dict(ephemeral=wire.encode_ec(other)),
               dict(identity=wire.encode_ec(BRC.IKB)), dict(identity=wire.encode_ec(EKA), ephemeral=wire.encode_ec(BRC.IKA))):
        rejects(pqxdh.receive_repeated_initial, s, wrap(m3, **kw), live, exc=pqxdh.NotARepeatedInitial)
    initiator = responder_session(our_identity_public=BRC.IKA, peer_identity_public=BRC.IKB, established_ephemeral=None)
    rejects(pqxdh.receive_repeated_initial, initiator, wrap(m3, identity=wire.encode_ec(BRC.IKB)), live,
            exc=pqxdh.NotARepeatedInitial)
    rejects(pqxdh.receive_repeated_initial, initiator, wrap(m3), live, exc=pqxdh.NotARepeatedInitial)
    assert live.calls == calls
    assert accepts(pqxdh.receive_repeated_initial, s, wrap(m3), live) == b"third"
