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

from tacenta_reader import braid, curve25519, gf65536, pqxdh, ratchet, spqr, triple, wire  # noqa: E402
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
    i = v["inputs"]
    check(v["output"], braid.kdf_epoch_key(bx(i["ss"]), int(i["epoch"], 16)))


def h_auth(v):
    i = v["inputs"]
    rk, mac = braid.auth_update(bx(i["root"]), bx(i["key"]), int(i["epoch"], 16))
    check(v["output"], rk + mac, "root_key || mac_key")


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


def run_negative(totals):
    import negative_cases
    counts = totals.setdefault("negative_cases.py (derived from spec text)", OrderedDict(PASS=0, FAIL=0, SKIP=0))
    for cid, cite, fn in negative_cases.CASES:
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
    for rel, c in totals.items():
        print(f"{rel:58} {c['PASS']:5} {c['FAIL']:5} {c['SKIP']:5}")
        for k in grand:
            grand[k] += c[k]
    print(f"{'TOTAL':58} {grand['PASS']:5} {grand['FAIL']:5} {grand['SKIP']:5}")
    return 1 if grand["FAIL"] else 0


if __name__ == "__main__":
    sys.exit(main())
