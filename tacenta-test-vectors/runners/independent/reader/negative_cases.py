"""Negative (and boundary) cases derived from the text of tacenta-spec.

Each case cites the page and the sentence it tests. A case whose rule is a
hypothesis rather than a stated rule says so and names the GAPS.md entry.
Run from run.py; each case raises AssertionError on failure.
"""

import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from tacenta_reader import constants as K  # noqa: E402
from tacenta_reader import curve25519, gf65536, ratchet, spqr, wire  # noqa: E402
from tacenta_reader.wire import BundleRefused, Codeword, CompositeHeader, DecodeError, EncodeError  # noqa: E402

CASES = []


def case(cid, cite):
    def deco(fn):
        CASES.append((cid, cite, fn))
        return fn
    return deco


def rejects(fn, *args, exc=DecodeError, **kw):
    try:
        fn(*args, **kw)
    except exc:
        return
    raise AssertionError(f"accepted; expected {exc.__name__}")


def accepts(fn, *args, **kw):
    try:
        return fn(*args, **kw)
    except Exception as e:  # noqa: BLE001
        raise AssertionError(f"refused unexpectedly: {type(e).__name__}: {e}")


def put(buf, offset, value):
    b = bytearray(buf)
    if isinstance(value, int):
        b[offset] = value
    else:
        b[offset:offset + len(value)] = value
    return bytes(b)


# ------------------------------------------------------------- fixtures

def header(**kw):
    base = dict(dh=b"\x0a" * 32, pn=7, n=9, pq_epoch=3, pq_n=11, ag_epoch=3,
                ag_type=K.AG_CT1, codeword=Codeword(5, b"\xcd" * 32))
    base.update(kw)
    return CompositeHeader(**base)


MSG = wire.encode_ratchet_message(header(), b"\xde\xad\xbe\xef")
MSG_ABSENT = wire.encode_ratchet_message(header(ag_type=K.AG_NONE, codeword=None), b"\x00")
# composite offsets
OFF_AG_TYPE, OFF_PRESENT, OFF_INDEX, OFF_CHUNK = 66, 67, 68, 70

INITIAL = wire.encode_initial(wire.InitialMessage(
    identity=b"\x05" + b"\x0a" * 32, ephemeral=b"\x05" + b"\x0b" * 32,
    kem_ciphertext=b"\xc0\xde", signed_prekey_id=3, one_time_prekey_id=4,
    kem_prekey_id=5, ratchet_message=MSG))
OFF_IDENTITY, OFF_EPHEMERAL, OFF_CT_LEN = 2, 35, 68

IK_PRIV = bytes(range(1, 33))
SPK_PRIV = bytes(range(33, 65))
OPK_PRIV = bytes(range(65, 97))
IK_PUB = curve25519.x25519_public(IK_PRIV)
SPK_PUB = curve25519.x25519_public(SPK_PRIV)
OPK_PUB = curve25519.x25519_public(OPK_PRIV)
KEM_PK = bytes((i * 7 + 3) & 0xFF for i in range(K.MLKEM1024_EK_LEN))  # opaque bytes


def signed_bundle(one_time=True, **kw):
    spk_sig = curve25519.xeddsa_sign(IK_PRIV, wire.encode_ec(SPK_PUB), b"\x11" * 64)
    kem_sig = curve25519.xeddsa_sign(IK_PRIV, wire.encode_kem(KEM_PK), b"\x22" * 64)
    base = dict(identity_key=IK_PUB, signed_prekey=SPK_PUB, signed_prekey_signature=spk_sig,
                kem_prekey=KEM_PK, kem_prekey_signature=kem_sig,
                one_time_prekey=OPK_PUB if one_time else None,
                signed_prekey_id=1, one_time_prekey_id=2 if one_time else K.ABSENT_ID,
                kem_prekey_id=3)
    base.update(kw)
    return wire.PrekeyBundle(**base)


_BUNDLE_CACHE = {}


def bundle_bytes(one_time=True):
    if one_time not in _BUNDLE_CACHE:
        _BUNDLE_CACHE[one_time] = wire.encode_bundle(signed_bundle(one_time))
    return _BUNDLE_CACHE[one_time]


OFF_KEM_LEN, OFF_OT_PRESENT, OFF_OT_KEY = 130, 1766, 1767

MF = "message-format.md"
SE = "session-establishment.md"
RM = "ratchet.md"
SP = "sparse-pq-ratchet.md"


# ======================================================= ratchet message

@case("RM-01 truncated to 101 bytes", f"{MF} Ratchet message: rejects a message shorter than its framing and header")
def _():
    rejects(wire.decode_ratchet_message, MSG[:101])


@case("RM-02 empty and 1-byte input", f"{MF} Rejection: a message too short for its fixed fields")
def _():
    rejects(wire.decode_ratchet_message, b"")
    rejects(wire.decode_ratchet_message, b"\x01")


@case("RM-03 unrecognised version 0x00, 0x02, 0xff", f"{MF} Ratchet message: rejects an unrecognised version")
def _():
    for ver in (0x00, 0x02, 0xFF):
        rejects(wire.decode_ratchet_message, put(MSG, 0, ver))


@case("RM-04 unexpected type byte 0x00, 0x02, 0x03, 0x04", f"{MF} Ratchet message: rejects ... an unexpected type byte")
def _():
    for t in (0x00, K.TYPE_INITIAL, K.TYPE_BUNDLE, 0x04):
        rejects(wire.decode_ratchet_message, put(MSG, 1, t))


@case("RM-05 ag_type 0x06 (where Ct1Ack would go) and 0xff", f"{MF}: rejects an ag_type outside the six values; Ct1Ack has no byte")
def _():
    for t in (0x06, 0x07, 0x80, 0xFF):
        rejects(wire.decode_ratchet_message, put(MSG, OFF_AG_TYPE, t))


@case("RM-06 every ag_type 0x00..0x05 decodes", f"{MF} ag_type table (six values)")
def _():
    for t in range(6):
        h, _ = accepts(wire.decode_ratchet_message, put(MSG, OFF_AG_TYPE, t))
        assert h.ag_type == t


@case("RM-07 presence byte 0x02 and 0xff", f"{MF}: rejects a presence byte other than 0x00 or 0x01")
def _():
    for p in (0x02, 0x80, 0xFF):
        rejects(wire.decode_ratchet_message, put(MSG, OFF_PRESENT, p))


@case("RM-08 absent codeword with non-zero index", f"{MF}: rejects an absent codeword whose index ... bytes are not all zero")
def _():
    rejects(wire.decode_ratchet_message, put(MSG_ABSENT, OFF_INDEX, 0x01))
    rejects(wire.decode_ratchet_message, put(MSG_ABSENT, OFF_INDEX + 1, 0x80))


@case("RM-09 absent codeword with a non-zero chunk byte (first, last)", f"{MF}: rejects an absent codeword whose ... chunk bytes are not all zero")
def _():
    rejects(wire.decode_ratchet_message, put(MSG_ABSENT, OFF_CHUNK, 0x01))
    rejects(wire.decode_ratchet_message, put(MSG_ABSENT, OFF_CHUNK + 31, 0x01))


@case("RM-10 codeword carried with ag_type none decodes", f"{MF}: A codeword carried with a type that takes none decodes")
def _():
    raw = wire.encode_ratchet_message(header(ag_type=K.AG_NONE), b"")
    h, ct = accepts(wire.decode_ratchet_message, raw)
    assert h.codeword is not None and h.ag_type == K.AG_NONE and ct == b""


@case("RM-11 classical 42-byte header (2 + 40) is not accepted", f"{MF}: The classical 40-byte header ... is not a message this decoder accepts")
def _():
    classical = bytes([K.VERSION, K.TYPE_RATCHET]) + b"\x0a" * 32 + (7).to_bytes(4, "big") + (9).to_bytes(4, "big")
    rejects(wire.decode_ratchet_message, classical)


@case("RM-12 every single-byte mutation the decoder accepts re-encodes to itself",
      f"{MF} Principles: Canonical, exactly one valid encoding; triple-ratchet.md unambiguity direction")
def _():
    for base in (MSG, MSG_ABSENT):
        for off in range(K.COMPOSITE_LEN):
            for x in (0x01, 0x80, 0xFF):
                mutated = put(base, off, base[off] ^ x)
                try:
                    h, ct = wire.decode_ratchet_message(mutated)
                except DecodeError:
                    continue
                assert wire.encode_ratchet_message(h, ct) == mutated, f"offset {off} xor {x:#x} not canonical"


@case("RM-13 a prekey bundle handed to the ratchet decoder fails on the type byte",
      f"{MF} Message type: reject a bundle ... on the type byte")
def _():
    try:
        wire.decode_ratchet_message(bundle_bytes())
    except DecodeError as e:
        assert "type" in str(e), f"rejected, but not on the type byte: {e}"
        return
    raise AssertionError("accepted")


@case("RM-14 composite header decoder rejects trailing bytes", f"{MF} Rejection: trailing bytes after a message that should have ended")
def _():
    rejects(wire.decode_composite, wire.encode_composite(header()) + b"\x00")


# ====================================================== associated data

@case("AD-01 CONCAT refuses a header that is not the whole composite header",
      f"{MF} Associated data: header here is the whole composite header")
def _():
    classical = bytes([K.VERSION, K.TYPE_RATCHET]) + b"\x0a" * 40
    rejects(wire.concat_ad, b"ad", classical, exc=EncodeError)
    rejects(wire.concat_ad, b"ad", MSG, exc=EncodeError)  # header + ciphertext


@case("AD-02 CONCAT is len(ad) 4 BE || ad || header and parses uniquely",
      f"{MF} Associated data: CONCAT(ad, header) = len(ad) (4, big-endian) || ad || composite_header")
def _():
    hdr = wire.encode_composite(header())
    ad = b"\x05" + b"\x01" * 32 + b"\x05" + b"\x02" * 32
    out = wire.concat_ad(ad, hdr)
    assert out[:4] == (66).to_bytes(4, "big") and out[4:70] == ad and out[70:] == hdr
    # Unique parse: reading the length, the ad, then exactly one composite
    # header consumes the whole string and returns the pair.
    n = int.from_bytes(out[:4], "big")
    assert out[4:4 + n] == ad and wire.decode_composite(out[4 + n:]) == header()
    # Moving the boundary (a shorter ad whose last byte would, naively
    # concatenated, sit in front of the header) yields different bytes.
    assert wire.concat_ad(ad[:-1], hdr) != out
    assert ad[:-1] + bytes([ad[-1]]) + hdr == ad + hdr  # the naive form is ambiguous


@case("AD-03 stripping the codeword changes the associated data",
      f"{MF} Associated data: an intermediary could strip the agreement's message")
def _():
    with_cw = wire.encode_composite(header())
    stripped = wire.encode_composite(header(codeword=None))
    assert wire.concat_ad(b"ad", with_cw) != wire.concat_ad(b"ad", stripped)


# ======================================================= initial message

@case("IM-01 truncated inside the fixed fields", f"{MF} Rejection: a message too short for its fixed fields")
def _():
    for n in (0, 1, 2, 34, 67, 71, 72 + 2 + 11):
        rejects(wire.decode_initial, INITIAL[:n])


@case("IM-02 unrecognised version", f"{MF} Rejection: an unrecognised version")
def _():
    rejects(wire.decode_initial, put(INITIAL, 0, 0x02))


@case("IM-03 ratchet message or bundle handed to the initial decoder", f"{MF} Message type: a receiver can tell what it is holding")
def _():
    rejects(wire.decode_initial, put(INITIAL, 1, K.TYPE_RATCHET))
    rejects(wire.decode_initial, bundle_bytes())
    rejects(wire.decode_ratchet_message, INITIAL)


@case("IM-04 kem_ciphertext_len overruns the input", f"{MF} Rejection: a length prefix that overruns the input")
def _():
    rejects(wire.decode_initial, put(INITIAL, OFF_CT_LEN, (0xFFFFFFFF).to_bytes(4, "big")))
    total = len(INITIAL)
    # a length that swallows the identifiers leaves too few bytes for them
    rejects(wire.decode_initial, put(INITIAL, OFF_CT_LEN, (total - 72 - 11).to_bytes(4, "big")))


@case("IM-05 identity or ephemeral with an unrecognised curve byte (incl. the KEM byte) is a decode failure",
      f"{MF} Initial message: It also refuses an identity or ephemeral whose first byte is not the EncodeEC curve byte")
def _():
    for b in (0x00, 0x08, 0xFF):
        rejects(wire.decode_initial, put(INITIAL, OFF_IDENTITY, b))
        rejects(wire.decode_initial, put(INITIAL, OFF_EPHEMERAL, b))


@case("IM-06 one_time_prekey_id 0 reads as 'no one-time prekey was used'", f"{MF} Key identifiers: The value 0 is reserved to mean absent")
def _():
    m = wire.decode_initial(put(INITIAL, 72 + 2 + 4, bytes(4)))
    assert m.one_time_prekey_id == K.ABSENT_ID and not m.one_time_prekey_used
    assert wire.decode_initial(INITIAL).one_time_prekey_used


@case("IM-07 the embedded ratchet message still decodes on its own", f"{MF} Initial message: so it still decodes on its own")
def _():
    m = wire.decode_initial(INITIAL)
    h, ct = wire.decode_ratchet_message(m.ratchet_message)
    assert ct == b"\xde\xad\xbe\xef"


@case("IM-08 the initial decoder does not validate ratchet_message: empty or not a ratchet message decodes; decoding it as one is refused later",
      f"{MF} Initial message: the initial-message decoder does not validate it: it may be empty, or not a ratchet message at all")
def _():
    prefix = INITIAL[:-len(MSG)]
    for tail in (b"", b"\xde\xad", put(MSG, OFF_AG_TYPE, 0x06), MSG[:50]):
        m = accepts(wire.decode_initial, prefix + tail)
        assert m.ratchet_message == tail
        if tail:
            rejects(wire.decode_ratchet_message, m.ratchet_message)
    rejects(wire.decode_ratchet_message, b"")


@case("IM-09 kem_ciphertext length is not checked at decode; decapsulation's length refusal is not a decode failure",
      f"{MF} Initial message: The decoder does not check kem_ciphertext's length either ... The refusal is not a decode failure")
def _():
    from tacenta_reader import pqxdh
    for n in (0, 2, 1567, 1568, 1569, 4000):
        raw = wire.encode_initial(wire.InitialMessage(
            identity=b"\x05" + b"\x0a" * 32, ephemeral=b"\x05" + b"\x0b" * 32,
            kem_ciphertext=b"\xc3" * n, signed_prekey_id=3, one_time_prekey_id=0,
            kem_prekey_id=5, ratchet_message=MSG))
        m = accepts(wire.decode_initial, raw)
        if n == K.MLKEM1024_CT_LEN:
            accepts(pqxdh.check_kem_ciphertext, m.kem_ciphertext)
        else:
            rejects(pqxdh.check_kem_ciphertext, m.kem_ciphertext, exc=pqxdh.KemCiphertextRefused)
            try:
                pqxdh.check_kem_ciphertext(m.kem_ciphertext)
            except DecodeError:
                raise AssertionError("length refusal reported as a decode failure")
            except pqxdh.KemCiphertextRefused:
                pass


@case("IM-10 identifier 0 decodes in every position of an initial message",
      f"{MF} Key identifiers: Neither decoder looks at an identifier's value, so 0 decodes in every position")
def _():
    base = 2 + 33 + 33 + 4 + 2   # identifiers start after the 2-byte ciphertext
    raw = put(INITIAL, base, bytes(12))
    m = accepts(wire.decode_initial, raw)
    assert (m.signed_prekey_id, m.one_time_prekey_id, m.kem_prekey_id) == (0, 0, 0)
    assert not m.one_time_prekey_used


# ========================================================= prekey bundle

@case("PB-01 bundle round trip, with and without a one-time prekey; 1,811 bytes",
      f"{MF} Prekey bundle: A bundle is 1,811 bytes with that KEM")
def _():
    for ot in (True, False):
        raw = bundle_bytes(ot)
        assert len(raw) == K.BUNDLE_LEN_MLKEM1024, len(raw)
        assert wire.decode_bundle(raw) == signed_bundle(ot)


@case("PB-02 unrecognised version; wrong type byte (a ratchet message handed as a bundle)",
      f"{MF} Message type: reject a bundle handed to it as a message on the type byte")
def _():
    rejects(wire.decode_bundle, put(bundle_bytes(), 0, 0x02))
    rejects(wire.decode_bundle, put(bundle_bytes(), 1, K.TYPE_RATCHET))
    try:
        wire.decode_bundle(MSG)
    except DecodeError as e:
        assert "type" in str(e), f"rejected, but not on the type byte: {e}"
    else:
        raise AssertionError("accepted a ratchet message as a bundle")


@case("PB-03 presence byte other than 0x00/0x01", f"{MF} Prekey bundle: a presence byte other than 0x00 or 0x01 is refused")
def _():
    for p in (0x02, 0xFF):
        rejects(wire.decode_bundle, put(bundle_bytes(), OFF_OT_PRESENT, p))


@case("PB-04 absent one-time prekey whose 32 bytes are not zero", f"{MF} Prekey bundle: the 32 bytes must be zero")
def _():
    rejects(wire.decode_bundle, put(bundle_bytes(False), OFF_OT_KEY + 31, 0x01))
    rejects(wire.decode_bundle, put(bundle_bytes(True), OFF_OT_PRESENT, 0x00))


@case("PB-05 trailing bytes", f"{MF} Prekey bundle: Trailing bytes are rejected")
def _():
    rejects(wire.decode_bundle, bundle_bytes() + b"\x00")


@case("PB-06 truncated by one byte and inside the KEM key", f"{MF} Rejection: a message too short for its fixed fields")
def _():
    rejects(wire.decode_bundle, bundle_bytes()[:-1])
    rejects(wire.decode_bundle, bundle_bytes()[:500])


@case("PB-07 kem_prekey_len overruns the input", f"{MF} Rejection: a length prefix that overruns the input")
def _():
    rejects(wire.decode_bundle, put(bundle_bytes(), OFF_KEM_LEN, (0xFFFFFFFF).to_bytes(4, "big")), kem_prekey_len=None)
    rejects(wire.decode_bundle, put(bundle_bytes(), OFF_KEM_LEN, (1568 + 200).to_bytes(4, "big")), kem_prekey_len=None)


@case("PB-08 a bundle whose kem_prekey_len is not 1,568 (1,184 and 1,569) is a decode failure under ML-KEM-1024",
      f"{MF} Prekey bundle: a decoder refuses a kem_prekey_len other than the encapsulation-key length of the KEM it expects")
def _():
    for key in (KEM_PK[:1184], KEM_PK + b"\x00"):
        b = signed_bundle(kem_prekey=key)
        raw = wire.encode_bundle(b, kem_prekey_len=None)
        rejects(wire.decode_bundle, raw)
        assert wire.decode_bundle(raw, kem_prekey_len=None).kem_prekey == key


@case("PB-15 identifier 0 in the signed and KEM prekey positions decodes, and the initiator does not refuse it",
      f"{MF} Key identifiers: an initiator does not check for it in a bundle and echoes it")
def _():
    b = signed_bundle(True, signed_prekey_id=0, kem_prekey_id=0)
    got = accepts(wire.decode_bundle, wire.encode_bundle(b))
    assert (got.signed_prekey_id, got.kem_prekey_id) == (0, 0)
    accepts(wire.initiator_check_bundle, got, expected_identity=IK_PUB)


@case("PB-09 initiator accepts a correctly signed bundle", f"{SE} Sending the initial message: Alice verifies every signature")
def _():
    for ot in (True, False):
        accepts(wire.initiator_check_bundle, wire.decode_bundle(bundle_bytes(ot)), expected_identity=IK_PUB)


@case("PB-10 initiator refuses presence/identifier disagreement (both directions)",
      f"{SE}: one-time curve prekey and that prekey's identifier disagree about whether one is present")
def _():
    rejects(wire.initiator_check_bundle, signed_bundle(True, one_time_prekey_id=K.ABSENT_ID), exc=BundleRefused)
    rejects(wire.initiator_check_bundle, signed_bundle(False, one_time_prekey_id=9), exc=BundleRefused)
    # and the decoder itself does not refuse it: "refused by the initiator" (G-07)
    raw = wire.encode_bundle(signed_bundle(False, one_time_prekey_id=9))
    accepts(wire.decode_bundle, raw)


@case("PB-11 initiator refuses an identity that is not the one it named", f"{SE}: its identity key is not the one she set out to reach")
def _():
    rejects(wire.initiator_check_bundle, signed_bundle(), expected_identity=OPK_PUB, exc=BundleRefused)


@case("PB-12 initiator refuses a forged signed prekey and a forged KEM prekey", f"{SE}: Alice verifies every signature in the bundle and aborts if any fails")
def _():
    good = signed_bundle()
    rejects(wire.initiator_check_bundle, signed_bundle(signed_prekey=OPK_PUB), exc=BundleRefused)
    forged_kem = bytes([KEM_PK[0] ^ 1]) + KEM_PK[1:]
    rejects(wire.initiator_check_bundle, signed_bundle(kem_prekey=forged_kem), exc=BundleRefused)
    bad_sig = bytes([good.signed_prekey_signature[0] ^ 1]) + good.signed_prekey_signature[1:]
    rejects(wire.initiator_check_bundle, signed_bundle(signed_prekey_signature=bad_sig), exc=BundleRefused)


@case("PB-13 a signature over the untagged key is refused (signatures are over EncodeEC / EncodeKEM)",
      f"{MF} Prekey bundle: The signatures are over the tagged forms")
def _():
    raw_sig = curve25519.xeddsa_sign(IK_PRIV, SPK_PUB, b"\x33" * 64)
    rejects(wire.initiator_check_bundle, signed_bundle(signed_prekey_signature=raw_sig), exc=BundleRefused)
    raw_kem_sig = curve25519.xeddsa_sign(IK_PRIV, KEM_PK, b"\x44" * 64)
    rejects(wire.initiator_check_bundle, signed_bundle(kem_prekey_signature=raw_kem_sig), exc=BundleRefused)


@case("PB-14 EncodeEC and EncodeKEM ranges are disjoint", f"{SE} Parameters: The ranges of the encoding functions must be pairwise disjoint")
def _():
    rejects(wire.decode_ec, wire.encode_kem(KEM_PK)[:33])
    rejects(wire.decode_kem, wire.encode_ec(SPK_PUB))


# ===================================================== session agreement

@case("DH-01 non-contributory X25519 outputs are refused (u = 0, 1, order-8 points)",
      f"{SE}: Both sides refuse a Diffie-Hellman output that is not contributory")
def _():
    low_order = [bytes(32), (1).to_bytes(32, "little"),
                 bytes.fromhex("e0eb7a7c3b41b8ae1656e3faf19fc46ada098deb9c32b1fd866205165f49b800"),
                 bytes.fromhex("5f9c95bca3508c24b1d0b1559c83ef5b04445cc4581c8e86d8224eddd09f1157")]
    for u in low_order:
        rejects(curve25519.x25519_contributory, IK_PRIV, u, exc=curve25519.NonContributory)
    accepts(curve25519.x25519_contributory, IK_PRIV, SPK_PUB)


@case("DH-02 initiator and responder compute the same DH1..DH4 and SK (SS supplied)",
      f"{SE} Receiving the initial message: repeats the same DH and KDF computations")
def _():
    from tacenta_reader import pqxdh
    ika = bytes(range(140, 172))   # Alice's identity
    eka = bytes(range(100, 132))   # Alice's ephemeral
    # Bob: identity IK_PRIV, signed prekey SPK_PRIV, one-time prekey OPK_PRIV
    ss = b"\x55" * 32
    for opk in (True, False):
        a = pqxdh.initiator_agreements(ika, eka, IK_PUB, SPK_PUB, OPK_PUB if opk else None)
        b = pqxdh.responder_agreements(IK_PRIV, SPK_PRIV, OPK_PRIV if opk else None,
                                       curve25519.x25519_public(ika), curve25519.x25519_public(eka))
        assert a == b and (a[3] is None) == (not opk)
        assert pqxdh.shared_secret(*a, ss) == pqxdh.shared_secret(*b, ss)


# ============================================================== ratchet

def _bob():
    return ratchet.init_responder(b"\x01" * 32, b"\x0b" * 32)


def _dh(tag):
    def step(header_dh):
        return bytes([tag]) * 32, bytes([tag ^ 0xF0]) * 32, bytes([tag ^ 0x0F]) * 32
    return step


K1, K2, K3 = b"\x1a" * 32, b"\x2a" * 32, b"\x3a" * 32


def _recv(state, dh, pn, n, tag):
    s, mk, _ = ratchet.receive(state, ratchet.Header(dh, pn, n), _dh(tag))
    return s, mk


@case("DR-01 MAX_SKIP boundary on the receiving chain: 1000 skips accepted, 1001 rejected",
      f"{RM} Skipped keys: A header demanding more than this is rejected (TooManySkipped)")
def _():
    bob, _ = accepts(_recv, _bob(), K1, 0, 1000, 1)
    assert len(bob.skipped) == 1000
    rejects(_recv, _bob(), K1, 0, 1001, 1, exc=ratchet.TooManySkipped)


@case("DR-02 MAX_SKIP applies to the skip to PN on its own when there is a receiving chain",
      f"{RM} The Diffie-Hellman ratchet, step 1: store its skipped message keys from Nr up to the header's PN")
def _():
    bob, _ = _recv(_bob(), K1, 0, 0, 1)
    rejects(_recv, bob, K2, 1002, 0, 2, exc=ratchet.TooManySkipped)
    bob2, _ = accepts(_recv, bob, K2, 1001, 0, 2)
    assert len(bob2.skipped) == 1000


@case("DR-03 MAX_SKIPPED_STORE: a skip that would push the store past 2000 is refused by the ratchet (SkippedStoreFull)",
      f"{RM} Skipped keys: A skip that would push the store past this bound is refused by the ratchet")
def _():
    bob, _ = _recv(_bob(), K1, 0, 1000, 1)
    bob, _ = _recv(bob, K2, 1001, 1000, 2)
    assert len(bob.skipped) == 2000
    before = bob.clone()
    rejects(_recv, bob, K3, 1001, 1, 3, exc=ratchet.SkippedStoreFull)
    assert bob.__dict__ == before.__dict__, "caller's state moved"
    accepts(_recv, bob, K3, 1001, 0, 3)


@case("DR-04 a skipped key is used once and removed", f"{RM} Sending and receiving: match a stored skipped key, use and remove it")
def _():
    bob, _ = _recv(_bob(), K1, 0, 2, 1)
    bob, _ = _recv(bob, K1, 0, 0, 1)
    assert (K1, 0) not in bob.skipped
    rejects(_recv, bob, K1, 0, 0, 1, exc=ratchet.OutOfOrder)


@case("DR-05 a responder cannot send before it has received (NoSendingChain)",
      f"{RM} Initialisation: The responder cannot send until it has received; Sending: refused ... (NoSendingChain)")
def _():
    rejects(ratchet.send, _bob(), exc=ratchet.NoSendingChain)


@case("DR-06 exact expiry: a key stored in one receive serves the next MAX_SKIPPED_AGE - 1 accepted receives and is deleted at the end of the last",
      f"{RM} Skipped keys: every stored key whose age ... is at least MAX_SKIPPED_AGE is deleted")
def _():
    bob, _ = _recv(_bob(), K1, 0, 2, 1)             # R0 stores (K1,0), (K1,1) at count 0; count -> 1
    assert bob.skipped[(K1, 0)][1] == 0 and bob.events == 1
    for n in range(3, 3 + K.MAX_SKIPPED_AGE - 2):   # R1..R998
        bob, _ = _recv(bob, K1, 0, n, 1)
    assert bob.events == K.MAX_SKIPPED_AGE - 1
    assert (K1, 0) in bob.skipped and (K1, 1) in bob.skipped, "expired too early"
    # R999, the last receive allowed to use a key stored in R0, uses (K1, 0) ...
    used, mk = accepts(_recv, bob, K1, 0, 0, 1)
    assert (K1, 0) not in used.skipped
    # ... and at its end (K1, 1) reaches age 1000 and is deleted.
    assert (K1, 1) not in used.skipped and used.events == K.MAX_SKIPPED_AGE
    # An ordinary receive in the same position deletes both.
    other, _ = _recv(bob, K1, 0, 3 + K.MAX_SKIPPED_AGE - 2, 1)
    assert not any(k[0] == K1 and k[1] in (0, 1) for k in other.skipped)


@case("DR-07 sender and receiver agree across DH steps (X25519 end to end)", f"{RM} The Diffie-Hellman ratchet; Initialisation")
def _():
    a_priv, b_priv = b"\xa1" * 32, b"\xb2" * 32
    a_pub, b_pub = curve25519.x25519_public(a_priv), curve25519.x25519_public(b_priv)
    sk = b"\x42" * 32
    keys = {a_pub: a_priv, b_pub: b_priv}
    parties = {"a": ratchet.init_initiator(sk, a_pub, b_pub, curve25519.x25519(a_priv, b_pub)),
               "b": ratchet.init_responder(sk, b_pub)}
    counter = [0]

    def real_step(state):
        def step(header_dh):
            counter[0] += 1
            new_priv = bytes([counter[0]]) * 32
            new_pub = curve25519.x25519_public(new_priv)
            keys[new_pub] = new_priv
            return (curve25519.x25519(keys[state.dhs_pub], header_dh), new_pub,
                    curve25519.x25519(new_priv, header_dh))
        return step

    for snd, rcv in (("a", "b"), ("a", "b"), ("b", "a"), ("a", "b"), ("b", "a"), ("b", "a")):
        parties[snd], h, mk = ratchet.send(parties[snd])
        parties[rcv], got, _ = ratchet.receive(parties[rcv], h, real_step(parties[rcv]))
        assert got == mk


# ======================================================== sparse ratchet

def _pair(sk=b"\x07" * 32):
    return spqr.init(sk, spqr.A2B), spqr.init(sk, spqr.B2A)


@case("SP-01 a message numbered zero is refused as out of order", f"{SP} Initialisation: a message numbered zero is refused as out of order")
def _():
    _, b = _pair()
    rejects(spqr.receive, b, 0, 0, exc=spqr.OutOfOrder)


@case("SP-02 A2b and B2a assign the chain pair oppositely and agree; same direction does not",
      f"{SP} Initialisation: The two sides then assign that pair oppositely")
def _():
    a, b = _pair()
    a, e, n, mk = spqr.send(a, 0)
    assert (e, n) == (0, 1), "a chain's first message is number one"
    b, got = spqr.receive(b, e, n)
    assert got == mk
    b, e, n, mk = spqr.send(b, 0)
    assert spqr.receive(a, e, n)[1] == mk
    a2 = spqr.init(b"\x07" * 32, spqr.A2B)
    _, e, n, mk = spqr.send(a2, 0)
    assert spqr.receive(spqr.init(b"\x07" * 32, spqr.A2B), e, n)[1] != mk


@case("SP-03 an epoch gap is refused", f"{SP} Sending: a gap is an error rather than something to accommodate")
def _():
    a, _ = _pair()
    rejects(spqr.send, a, 0, b"\x99" * 32, 2, exc=spqr.EpochGap)


@case("SP-04 advancing to epoch u64::MAX is refused as counter exhaustion", f"{SP} Sending: refuses to advance to epoch u64::MAX")
def _():
    a, _ = _pair()
    last = K.U64_MAX - 1
    a.epoch = last
    a.chains = {last: a.chains[0]}
    rejects(spqr.send, a, last, b"\x99" * 32, K.U64_MAX, exc=spqr.ChainExhausted)


@case("SP-05 MAX_SKIP: 1000 skips accepted, 1001 rejected", f"{SP} Receiving: a header demanding more than the permitted number of skips is rejected")
def _():
    _, b = _pair()
    rejects(spqr.receive, b, 0, 1002, exc=spqr.TooManySkipped)
    b2, _ = accepts(spqr.receive, b, 0, 1001)
    assert len(b2.skipped) == 1000


@case("SP-06 stored key used once; out-of-order within an epoch", f"{SP} Receiving: If a key is there it is used and removed")
def _():
    a, b = _pair()
    sent = []
    for _ in range(3):
        a, e, n, mk = spqr.send(a, 0)
        sent.append(mk)
    b, got = spqr.receive(b, 0, 3)
    assert got == sent[2]
    b, got = spqr.receive(b, 0, 1)
    assert got == sent[0]
    rejects(spqr.receive, b, 0, 1, exc=spqr.OutOfOrder)
    assert spqr.receive(b, 0, 2)[1] == sent[1]


@case("SP-07 epochs advance on both sides; retired epochs and their skipped keys are discarded (NoChain)",
      f"{SP} Retiring old epochs: keeps ... every epoch e with E < e + EPOCHS_KEPT and discards the rest")
def _():
    a, b = _pair()
    s1, s2 = b"\x31" * 32, b"\x32" * 32
    old = []
    for _ in range(2):
        a, e, n, mk = spqr.send(a, 0)
        old.append(mk)
    b, _ = spqr.receive(b, 0, 2)                                   # stores (0, 1)
    a, e, n, mk = spqr.send(a, 0, s1, 1)                            # sent on the epoch before
    assert (e, n) == (0, 3) and a.epoch == 1
    b, got = spqr.receive(b, e, n, s1, 1)
    assert got == mk
    b, e, n, mk = spqr.send(b, 1)
    a, got = spqr.receive(a, e, n)
    assert got == mk
    assert (0, 1) in b.skipped and spqr.receive(b, 0, 1)[1] == old[0]  # epoch 0 still kept
    more = []
    for _ in range(2):
        a, e, n, mk = spqr.send(a, 0)                               # numbers 4, 5
        more.append(mk)
    b, got = spqr.receive(b, 0, 5)                                  # stores (0, 4)
    assert got == more[1]
    a, e, n, mk = spqr.send(a, 1, s2, 2)
    b, got = spqr.receive(b, e, n, s2, 2)
    assert got == mk
    assert 0 not in b.chains and all(k[0] != 0 for k in b.skipped)
    rejects(spqr.receive, b, 0, 4, exc=spqr.NoChain)


# ================================================================ field

@case("GF-01 zero has no inverse; interpolation nodes must be distinct", "mlkem-braid.md Erasure code: GF(2^16) is a field")
def _():
    rejects(gf65536.inv, 0, exc=gf65536.FieldError)
    rejects(gf65536.interpolate, [1, 1], [2, 3], 5, exc=gf65536.FieldError)
    for a in (1, 2, 0x8000, 0xFFFF, 0x1234):
        assert gf65536.mul(a, gf65536.inv(a)) == 1
