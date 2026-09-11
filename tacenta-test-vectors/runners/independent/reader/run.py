#!/usr/bin/env python3
"""Run tacenta_reader against every vector file and the derived negative cases.

Prints one line per vector: PASS, FAIL (with a short diff) or SKIP (with the
reason), then per-file totals. Exit status is non-zero on any FAIL.
"""

import json
import os
import sys
from collections import OrderedDict

HERE = os.path.dirname(os.path.abspath(__file__))
CLEANROOM = os.path.dirname(HERE)
VECTORS = os.path.join(CLEANROOM, "..", "..", "vectors")
sys.path.insert(0, HERE)

import copy  # noqa: E402
import re  # noqa: E402

from tacenta_reader import aead, braid, curve25519, erasure, gf65536, persistence, pqxdh, protobuf, ratchet, spqr, triple, wire  # noqa: E402
from tacenta_reader.kdf import hkdf_sha256, hmac_sha256  # noqa: E402

bx = bytes.fromhex


def _short(h, n=48):
    return h if len(h) <= n else h[:n] + "..(%d bytes)" % (len(h) // 2)


def diff(expected_hex, got_hex, what="output"):
    if expected_hex == got_hex:
        return None
    return f"{what}: expected {_short(expected_hex)} got {_short(got_hex)}"


class Fail(Exception):
    pass


class Skip(Exception):
    pass


def check(expected_hex, got_bytes, what="output"):
    d = diff(expected_hex, got_bytes.hex(), what)
    if d:
        raise Fail(d)


# ------------------------------------------------------------ primitives

def h_hmac(v):
    i = v["inputs"]
    check(v["output"], hmac_sha256(bx(i["key"]), bx(i["data"])))


def h_hkdf(v):
    i = v["inputs"]
    check(v["output"], hkdf_sha256(bx(i["salt"]), bx(i["ikm"]), bx(i["info"]), int(i["length"], 16)))


def h_x25519(v):
    i = v["inputs"]
    check(v["output"], curve25519.x25519(bx(i["private"]), bx(i["peer_public"])))


def h_ed25519(v):
    i = v["inputs"]
    sig = curve25519.ed25519_sign(bx(i["secret"]), bx(i["message"]))
    check(v["output"], sig, "signature")
    pub = curve25519.ed25519_public(bx(i["secret"]))
    if not curve25519.ed25519_verify(pub, bx(i["message"]), sig):
        raise Fail("signature does not verify under the derived public key")


def h_xeddsa(v):
    i = v["inputs"]
    expected_valid = v.get("result", "valid") == "valid"
    if "signature" in i:
        got = curve25519.xeddsa_verify(bx(i["public"]), bx(i["message"]), bx(i["signature"]))
        if not expected_valid:
            if got is not None:
                raise Fail("verify-only vector accepted, expected invalid")
            return
        if got is None:
            raise Fail("verify-only vector rejected, expected valid")
        check(v["output"], got, "verified Edwards key")
        return
    sig = curve25519.xeddsa_sign(bx(i["secret"]), bx(i["message"]), bx(i["nonce"]))
    check(v["output"], sig, "signature")
    pub = curve25519.x25519_public(bx(i["secret"]))
    if curve25519.xeddsa_verify(pub, bx(i["message"]), sig) is None:
        raise Fail("own signature does not verify under the X25519 public key")


# ---------------------------------------------------------- wire formats

def _header_from_inputs(i):
    present = int(i["chunk_present"], 16)
    if present == 0:
        if bx(i["chunk_index"]) != bytes(2) or bx(i["chunk_data"]) != bytes(32):
            raise Fail("vector: absent codeword with non-zero inputs")
        cw = None
    else:
        cw = wire.Codeword(int(i["chunk_index"], 16), bx(i["chunk_data"]))
    return wire.CompositeHeader(
        dh=bx(i["dh"]), pn=int(i["pn"], 16), n=int(i["n"], 16),
        pq_epoch=int(i["pq_epoch"], 16), pq_n=int(i["pq_n"], 16),
        ag_epoch=int(i["ag_epoch"], 16), ag_type=int(i["ag_type"], 16), codeword=cw)


def h_composite(v):
    h = _header_from_inputs(v["inputs"])
    check(v["output"], wire.encode_composite(h), "encode")
    back = wire.decode_composite(bx(v["output"]))
    if back != h:
        raise Fail(f"decode: {back} != inputs")
    # mlkem-braid.md, Messages, On the wire: the last four fields are one Braid message
    m = braid.message_from_header(back)
    if wire.CompositeHeader(back.dh, back.pn, back.n, back.pq_epoch, back.pq_n, **braid.header_fields(m)) != h:
        raise Fail("the Braid message does not give back the header's agreement fields")
    check(v["inputs"]["ag_epoch"], braid.to_bytes(m.epoch), "ag_epoch as ToBytes(epoch)")


def h_message_encoding(v):
    i = v["inputs"]
    h = _header_from_inputs(i)
    check(v["output"], wire.encode_ratchet_message(h, bx(i["ciphertext"])), "encode")
    back, ct = wire.decode_ratchet_message(bx(v["output"]))
    if back != h or ct != bx(i["ciphertext"]):
        raise Fail("decode does not return the inputs")


def h_initial(v):
    i = v["inputs"]
    m = wire.InitialMessage(
        identity=bx(i["identity"]), ephemeral=bx(i["ephemeral"]),
        kem_ciphertext=bx(i["kem_ciphertext"]),
        signed_prekey_id=int(i["signed_prekey_id"], 16),
        one_time_prekey_id=int(i["one_time_prekey_id"], 16),
        kem_prekey_id=int(i["kem_prekey_id"], 16),
        ratchet_message=bx(i["ratchet_message"]))
    check(v["output"], wire.encode_initial(m), "encode")
    back = wire.decode_initial(bx(v["output"]))
    if back != m:
        raise Fail(f"decode: {back} != inputs")


# ------------------------------------- decoders' curve-key refusals (pass 4)
# message-format.md, Curve public keys. Each file's `source` says "an accepted
# vector's output is the re-encoding of the header [bundle, initial message]
# it decodes to". The input `encoding` is the bytes handed to the decoder
# (GAPS-4.md G4-01). An invalid vector must be refused, and "A refused key is
# a decode failure", so the refusal must be wire.DecodeError and nothing else.

def _decoder_vector(v, decode, encode, also=None):
    enc = bx(v["inputs"]["encoding"])
    if _invalid(v):
        try:
            decode(enc)
        except wire.DecodeError:
            return
        except Exception as e:  # noqa: BLE001
            raise Fail(f"refused, but not as a decode failure: {type(e).__name__}: {e}")
        raise Fail("accepted; expected a decode failure")
    got = decode(enc)
    check(v["output"], encode(got), "re-encoding")
    if also:
        also(got, enc)


def h_composite_decode(v):
    """The composite header alone, as composite.json and CONCAT use it. A
    102-byte input is also a ratchet message with an empty ciphertext, and the
    ratchet-message decoder must agree (G4-01)."""
    def agree(h, enc):
        back, ct = wire.decode_ratchet_message(enc)
        if back != h or ct != b"":
            raise Fail("the ratchet-message decoder disagrees with the header decoder")
    _decoder_vector(v, wire.decode_composite, wire.encode_composite, agree)
    if _invalid(v):
        try:
            wire.decode_ratchet_message(bx(v["inputs"]["encoding"]))
        except wire.DecodeError:
            return
        raise Fail("the ratchet-message decoder accepted what the header decoder refuses")


def h_bundle_decode(v):
    _decoder_vector(v, wire.decode_bundle, wire.encode_bundle)


def h_initial_decode(v):
    """"every key this decoder returns is one DecodeEC accepts"."""
    def decode_ec_accepts(m, enc):
        wire.decode_ec(m.identity)
        wire.decode_ec(m.ephemeral)
    _decoder_vector(v, wire.decode_initial, wire.encode_initial, decode_ec_accepts)


# --------------------------------------------------------------- ratchet

def h_double_ratchet(v):
    init = v["init"]
    parties = {
        "alice": ratchet.init_sender(bx(init["sk"]), bx(init["alice_pub"]), bx(init["bob_pub"]), bx(init["dh_ab"])),
        "bob": ratchet.init_receiver(bx(init["sk"]), bx(init["bob_pub"])),
    }
    produced = {"alice": [], "bob": []}
    for idx, st in enumerate(v["steps"]):
        who = st["actor"]
        expect = st.get("expect", "ok")
        stepped = []
        try:
            if st["op"] == "send":
                hdr, mk = ratchet.ratchet_encrypt(parties[who])
                produced[who].append(hdr)
            else:
                h = st["header"]
                hdr = ratchet.Header(bx(h["dh"]), h["pn"], h["n"])
                peer = "bob" if who == "alice" else "alice"
                if produced[peer] and hdr not in produced[peer]:
                    raise Fail(f"step {idx}: header {h} was not produced by {peer}'s sends")

                def dh_step(header_dh, st=st):
                    stepped.append(True)
                    return bx(st["dh_recv"]), bx(st["new_pub"]), bx(st["dh_send"])

                mk = ratchet.ratchet_decrypt(parties[who], hdr, dh_step)
                if bool(stepped) != (bx(st["new_pub"]) != bytes(32)):
                    raise Fail(f"step {idx}: DH step taken={bool(stepped)} but vector new_pub disagrees")
        except ratchet.RatchetError as e:
            if expect == "reject":
                continue
            raise Fail(f"step {idx} ({who} {st['op']}): rejected unexpectedly: {e}")
        if expect == "reject":
            raise Fail(f"step {idx} ({who} {st['op']}): accepted, expected reject")
        d = diff(st["mk"], mk.hex(), f"step {idx} mk")
        if d:
            raise Fail(d)
        if "message_keys" in st:
            enc, mac, iv = ratchet.expand_message_key(mk)
            for name, got in (("enc", enc), ("mac", mac), ("iv", iv)):
                d = diff(st["message_keys"][name], got.hex(), f"step {idx} {name}")
                if d:
                    raise Fail(d)


# --------------------------------------------------- session, post-quantum

def h_pqxdh(v):
    i = v["inputs"]
    dh4 = bx(i["dh4"]) if "dh4" in i else None
    check(v["output"], pqxdh.shared_secret(bx(i["dh1"]), bx(i["dh2"]), bx(i["dh3"]), dh4, bx(i["ss"])))


def h_spqr(v):
    i = v["inputs"]
    nck, mk = spqr.kdf_chain(bx(i["ck"]), int(i["n"], 16))
    check(v["output"], nck + mk, "next_ck || mk")


def h_triple(v):
    i = v["inputs"]
    check(v["output"], triple.combine(bx(i["mk_ec"]), bx(i["mk_pq"])))


def h_split(v):
    check(v["output"], triple.split_secret_bytes(bx(v["inputs"]["sk"])))


def h_braid(v):
    """mlkem-braid.md, Parameters and derivations: KDF_OK (G-22, now stated)."""
    i = v["inputs"]
    check(v["output"], braid.kdf_ok(bx(i["ss"]), int(i["epoch"], 16)))


def h_auth(v):
    """One Update from a given root_key, output root_key || mac_key; "its
    from-zero vector is Init(1, s)" (G-23, now stated)."""
    i = v["inputs"]
    root, key, epoch = bx(i["root"]), bx(i["key"]), int(i["epoch"], 16)
    rk, mac = braid.auth_update(root, key, epoch)
    check(v["output"], rk + mac, "root_key || mac_key")
    if root == bytes(32):
        a = braid.Auth.init(epoch, key)
        check(v["output"], a.root_key + a.mac_key, "Init(e, s)")


def h_gf_mul(v):
    i = v["inputs"]
    got = gf65536.mul(gf65536.element_from_bytes(bx(i["a"])), gf65536.element_from_bytes(bx(i["b"])))
    check(v["output"], got.to_bytes(2, "big"))


def h_gf_inv(v):
    got = gf65536.inv(gf65536.element_from_bytes(bx(v["inputs"]["a"])))
    check(v["output"], got.to_bytes(2, "big"))


def h_interp(v):
    i = v["inputs"]
    got = gf65536.interpolate(gf65536.elements_from_bytes(bx(i["nodes"])),
                              gf65536.elements_from_bytes(bx(i["values"])),
                              gf65536.element_from_bytes(bx(i["x"])))
    check(v["output"], got.to_bytes(2, "big"))


# ------------------------------------------------- erasure code (GAPS-3.md G3-01)
# The layouts of these files' inputs are not stated in the tree. Read as:
# `indices` a run of 16-bit big-endian indices; `codewords` a run of
# index(2) || chunk(32), the persisted decoder's `codeword` layout
# (session-persistence.md); an encode `output` the listed codewords' 32 bytes
# back to back; `size`, `issued` and `stream_length` 32-bit big-endian.

def _u16s(h):
    b = bx(h)
    if len(b) % 2:
        raise Fail("vector: indices is not a run of 16-bit values")
    return [int.from_bytes(b[k:k + 2], "big") for k in range(0, len(b), 2)]


def _codeword_run(h):
    b = bx(h)
    if len(b) % 34:
        raise Fail("vector: codewords is not a run of index(2) || chunk(32)")
    return [(int.from_bytes(b[k:k + 2], "big"), b[k + 2:k + 34]) for k in range(0, len(b), 34)]


def _invalid(v):
    return v.get("result", "valid") == "invalid"


def h_erasure_encode(v):
    """mlkem-braid.md, The erasure code: Chunks, Codewords; Encoder lifetime.
    Every issued index is checked to be the next one; with stream_length the
    stream is run until it issues nothing."""
    i = v["inputs"]
    enc = erasure.Encoder.for_value(bx(i["message"]))
    wanted = _u16s(i["indices"])
    total = int(i["stream_length"], 16) if "stream_length" in i else None
    got, issued = {}, 0
    while total is not None or issued <= max(wanted):
        cw = enc.issue()
        if cw is None:
            break
        idx, data = cw
        if idx != issued:
            raise Fail(f"the encoder issued index {idx} where {issued} was next")
        if data != enc.codeword(idx):
            raise Fail(f"issued codeword {idx} differs from the codeword definition")
        if idx in wanted:
            got[idx] = data
        issued += 1
    if total is not None:
        if issued != total:
            raise Fail(f"stream issued {issued} codewords, vector says {total}")
        if enc.issue() is not None:
            raise Fail("an exhausted encoder issued again")
    missing = [x for x in wanted if x not in got]
    if missing:
        raise Fail(f"indices never issued: {missing[:4]}")
    check(v["output"], b"".join(got[x] for x in wanted), "codewords")


def h_erasure_decode(v):
    """mlkem-braid.md, The erasure code, Decoding. The file's `source` says a
    vector with no output is a decoder that holds no value (G3-01)."""
    i = v["inputs"]
    d = erasure.Decoder(int(i["size"], 16))
    for idx, data in _codeword_run(i["codewords"]):
        d.receive(idx, data)
    value = d.value()
    if _invalid(v):
        if value is not None:
            raise Fail("decoder holds a value; the vector says it holds none")
        return
    if value is None:
        raise Fail("decoder holds no value")
    check(v["output"], value, "value")


def _state_bytes_vector(v, reader, writer):
    """A `bytes` vector: read the stored state; a valid one reads back to the
    bytes given, an invalid one is refused (session-persistence.md, Rejection)."""
    data = bx(v["inputs"]["bytes"])
    if _invalid(v):
        try:
            reader(data)
        except persistence.PersistError:
            return
        raise Fail("stored bytes accepted; expected a refusal")
    check(v["output"], writer(reader(data)), "re-encoding")


def h_encoder_state(v):
    """session-persistence.md, Erasure coder sub-formats; Semantic rules of the
    leaf formats, Erasure encoder."""
    i = v["inputs"]
    if "bytes" in i:
        return _state_bytes_vector(v, persistence.encoder_from_bytes, persistence.encoder_to_bytes)
    enc = erasure.Encoder.for_value(bx(i["message"]))
    for _ in range(int(i["issued"], 16)):
        if enc.issue() is None:
            raise Fail("encoder exhausted before the vector's issued count")
    out = persistence.encoder_to_bytes(enc)
    check(v["output"], out, "encoder bytes")
    back = persistence.encoder_from_bytes(out)
    if back != enc:
        raise Fail(f"read back {back}, wrote {enc}")
    # A zero-chunk encoder's codewords are now stated: "every codeword of an
    # encoder for zero bytes is 32 zero bytes" (mlkem-braid.md, Codewords;
    # GAPS-3.md G3-02, closed), so this comparison runs for every vector.
    nxt = copy.deepcopy(enc).issue()
    if nxt != back.issue():
        raise Fail("the read-back encoder issues a different next codeword")
    if not enc.chunks and nxt is not None and nxt[1] != bytes(32):
        raise Fail("an encoder for zero bytes issued a non-zero codeword")


def h_decoder_state(v):
    """session-persistence.md, Erasure coder sub-formats; Semantic rules of the
    leaf formats, Erasure decoder."""
    i = v["inputs"]
    if "bytes" in i:
        return _state_bytes_vector(v, persistence.decoder_from_bytes, persistence.decoder_to_bytes)
    d = erasure.Decoder(int(i["size"], 16))
    for idx, data in _codeword_run(i["codewords"]):
        d.receive(idx, data)
    out = persistence.decoder_to_bytes(d)
    check(v["output"], out, "decoder bytes")
    back = persistence.decoder_from_bytes(out)
    if back != d or back.value() != d.value():
        raise Fail("the read-back decoder differs from the one written")


# ------------------------------------------------------------ protobuf profile
# protobuf-profile.md names fields in camelCase; the vectors' `fields` use the
# same names in snake_case, which the page does not say (G3-03). The mapping
# below is mechanical; names must match exactly, so an absent prekeyId must be
# absent. Integers are four big-endian bytes (vector.schema.json, `fields`).

def _snake(name):
    return re.sub(r"([A-Z])", r"_\1", name).lower()


def _protobuf(v, parse):
    region = bx(v["inputs"]["region"])
    if _invalid(v):
        try:
            parse(region)
        except protobuf.ProtobufRefused:
            return
        raise Fail("region accepted; expected a refusal")
    got = parse(region)
    fields = {_snake(k): (val.to_bytes(4, "big").hex() if isinstance(val, int) else bytes(val).hex())
              for k, val in got.items()}
    if fields != v["fields"]:
        names = sorted(set(fields) ^ set(v["fields"]))
        wrong = sorted(k for k in set(fields) & set(v["fields"]) if fields[k] != v["fields"][k])
        raise Fail(f"fields differ: names only on one side {names}, values differ {wrong}")


def h_pb_body(v):
    _protobuf(v, protobuf.parse_ratchet_body)


def h_pb_envelope(v):
    _protobuf(v, protobuf.parse_prekey_envelope)


# ------------------------------------------------------------------------ AEAD
# message-format.md, Authenticated encryption. The input `ad` is the page's
# `AD`, the whole associated data (CONCAT(ad, header) for a session), not its
# `ad` (G3-04).

def _aead_keys(i):
    return bx(i["enc_key"]), bx(i["mac_key"]), bx(i["iv"])


def _concat_cross_check(ad_bytes):
    """When the input's comment says it is CONCAT(ad, header), check it parses so."""
    n = int.from_bytes(ad_bytes[:4], "big")
    if 4 + n + wire.K.COMPOSITE_LEN != len(ad_bytes):
        raise Fail("AD does not parse as len(ad) || ad || composite header")
    wire.decode_composite(ad_bytes[4 + n:])


def h_aead_encrypt(v):
    i = v["inputs"]
    enc, mac, iv = _aead_keys(i)
    if "CONCAT" in v.get("comment", ""):
        _concat_cross_check(bx(i["ad"]))
    out = aead.encrypt(enc, mac, iv, bx(i["ad"]), bx(i["plaintext"]))
    check(v["output"], out, "output")
    if aead.decrypt(enc, mac, iv, bx(i["ad"]), out) != bx(i["plaintext"]):
        raise Fail("the output does not decrypt to the plaintext")


def h_aead_decrypt(v):
    i = v["inputs"]
    enc, mac, iv = _aead_keys(i)
    ad, data = bx(i["ad"]), bx(i["input"])
    if "CONCAT" in v.get("comment", ""):
        _concat_cross_check(ad)
    calls = []
    real = aead._cbc_decrypt
    aead._cbc_decrypt = lambda *a: calls.append(1) or real(*a)
    try:
        try:
            got = aead.decrypt(enc, mac, iv, ad, data)
        except aead.AuthenticationFailure:
            if not _invalid(v):
                raise Fail("refused; expected the plaintext")
            tag_ok = len(data) >= 32 and hmac_sha256(mac, ad + data[:-32]) == data[-32:]
            if calls and not tag_ok:
                raise Fail("decrypted before the tag verified")
            return
    finally:
        aead._cbc_decrypt = real
    if _invalid(v):
        raise Fail("accepted; expected the one authentication failure")
    check(v["output"], got, "plaintext")


HANDLERS = {
    "hmac-sha256": h_hmac,
    "hkdf-sha256": h_hkdf,
    "x25519": h_x25519,
    "ed25519": h_ed25519,
    "xeddsa": h_xeddsa,
    "composite-header": h_composite,
    "message-encoding": h_message_encoding,
    "initial-message-encoding": h_initial,
    "double-ratchet": h_double_ratchet,
    "pqxdh-sk": h_pqxdh,
    "spqr-kdf-ck": h_spqr,
    "triple-combine": h_triple,
    "triple-split": h_split,
    "braid-kdf-ok": h_braid,
    "braid-auth-update": h_auth,
    "gf65536-mul": h_gf_mul,
    "gf65536-inv": h_gf_inv,
    "polynomial-interp": h_interp,
    "erasure-encode": h_erasure_encode,
    "erasure-decode": h_erasure_decode,
    "erasure-encoder-state": h_encoder_state,
    "erasure-decoder-state": h_decoder_state,
    "protobuf-ratchet-body": h_pb_body,
    "protobuf-prekey-envelope": h_pb_envelope,
    "aead-encrypt": h_aead_encrypt,
    "aead-decrypt": h_aead_decrypt,
    "composite-header-decode": h_composite_decode,
    "prekey-bundle-decode": h_bundle_decode,
    "initial-message-decode": h_initial_decode,
}


def _structure_ok(doc):
    return (doc.get("schema_version") == 1 and isinstance(doc.get("vectors"), list)
            and doc["vectors"] and all("id" in v for v in doc["vectors"]))


def run_vectors(totals):
    files = []
    for dirpath, _, names in os.walk(VECTORS):
        for name in names:
            if name.endswith(".json"):
                files.append(os.path.join(dirpath, name))
    for path in sorted(files):
        rel = os.path.relpath(path, VECTORS)
        counts = totals.setdefault(rel, OrderedDict(PASS=0, FAIL=0, SKIP=0))
        with open(path) as f:
            doc = json.load(f)
        if not _structure_ok(doc):
            print(f"FAIL  {rel}: file does not have the schema's top-level shape")
            counts["FAIL"] += 1
            continue
        handler = HANDLERS.get(doc.get("algorithm"))
        for v in doc["vectors"]:
            label = f"{rel} :: {v['id']}"
            if handler is None:
                print(f"SKIP  {label}: algorithm {doc.get('algorithm')!r} not implemented")
                counts["SKIP"] += 1
                continue
            try:
                handler(v)
            except Skip as e:
                print(f"SKIP  {label}: {e}")
                counts["SKIP"] += 1
            except Fail as e:
                print(f"FAIL  {label}: {e}")
                counts["FAIL"] += 1
            except Exception as e:  # an unexpected refusal is a failure
                print(f"FAIL  {label}: {type(e).__name__}: {e}")
                counts["FAIL"] += 1
            else:
                print(f"PASS  {label}")
                counts["PASS"] += 1


# Derived cases, one module per area. Each module exposes CASES as
# (id, citation, callable); none has a vector behind it unless it says so.
CASE_MODULES = [
    "negative_cases",     # wire formats, bundle, PQXDH, ratchet and sparse ratchet basics, field
    "cases_ratchet",      # Double Ratchet and sparse ratchet additions (ceilings, eviction, expiry)
    "cases_triple",       # Triple Ratchet commit rules, non-contributory check, eviction retry
    "cases_aead",         # AES-256-CBC + HMAC-SHA256 AEAD
    "cases_erasure",      # GF(2^16) erasure code
    "cases_persistence",  # session-persistence.md formats
    "cases_protobuf",     # protobuf-profile.md
    "cases_identity",     # identities-and-devices.md, repeated initial message, XEdDSA rules, DecodeEC, fingerprint
    "cases_braid",        # mlkem-braid.md: derivations, authenticator, state machine, failure, session
    "cases_curvekeys",    # message-format.md Curve public keys; the repeated initial message over a live session (pass 4)
]


def run_negative(totals):
    import importlib
    for name in CASE_MODULES:
        module = importlib.import_module(name)
        counts = totals.setdefault(f"{name}.py (derived from spec text)", OrderedDict(PASS=0, FAIL=0, SKIP=0))
        for cid, cite, fn in module.CASES:
            try:
                fn()
            except AssertionError as e:
                print(f"FAIL  negative :: {cid}: {e}  [{cite}]")
                counts["FAIL"] += 1
            except Exception as e:
                print(f"FAIL  negative :: {cid}: {type(e).__name__}: {e}  [{cite}]")
                counts["FAIL"] += 1
            else:
                print(f"PASS  negative :: {cid}")
                counts["PASS"] += 1


def main():
    totals = OrderedDict()
    run_vectors(totals)
    run_negative(totals)
    print()
    print(f"{'file':58} {'pass':>5} {'fail':>5} {'skip':>5}")
    grand = OrderedDict(PASS=0, FAIL=0, SKIP=0)
    sub = {"vectors": OrderedDict(PASS=0, FAIL=0, SKIP=0), "negative": OrderedDict(PASS=0, FAIL=0, SKIP=0)}
    for rel, c in totals.items():
        print(f"{rel:58} {c['PASS']:5} {c['FAIL']:5} {c['SKIP']:5}")
        part = sub["negative"] if rel.endswith("(derived from spec text)") else sub["vectors"]
        for k in grand:
            grand[k] += c[k]
            part[k] += c[k]
    for label, c in (("vectors subtotal", sub["vectors"]), ("derived cases subtotal", sub["negative"])):
        print(f"{label:58} {c['PASS']:5} {c['FAIL']:5} {c['SKIP']:5}")
    print(f"{'TOTAL':58} {grand['PASS']:5} {grand['FAIL']:5} {grand['SKIP']:5}")
    return 1 if grand["FAIL"] else 0


if __name__ == "__main__":
    sys.exit(main())
