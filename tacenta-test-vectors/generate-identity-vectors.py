#!/usr/bin/env python3
"""Write vectors/identity/initiator-expectation.json, and check the four
model-generated identity-record files against a second implementation.

    python3 tacenta-test-vectors/generate-identity-vectors.py            # rewrite
    python3 tacenta-test-vectors/generate-identity-vectors.py --check    # compare

`regenerate-vectors.sh` runs the first form after the model has written its
files, so `tooling/check-vectors-current.sh` fails when the committed
initiator file is not what this script writes.

The initiator file is not pure model output. Its bundles carry XEdDSA
signatures, and the Lean model has no signer and no X25519. So the bytes come
from this script, which has its own field and curve arithmetic, its own
XEdDSA and its own ML-KEM encapsulation-key check, and nothing is read from
the Rust implementation. Each case is built with a stated intent (the outcome
tacenta-spec/protocol/session-establishment.md, Records, expectations and
attribution and Sending the initial message, give it), and two oracles must
agree with the intent before anything is written:

- this script's own reading of those sections, in the order they fix;
- the model, `Model.InitiatorExpectation.establishInitiatorExpecting`, run by
  `lake exe genvectors initiator-expectation-verdicts`. The script gives the
  model each case's expectation, records and bundle fields, and the three
  facts the model cannot compute: whether each signature verifies, whether
  the KEM prekey passes its input checks, and which prekeys are of low
  order. The model computes the rest itself (the presence and canonical-key
  checks, the identity-key rule by `Model.IdentityKey.valid`, the
  classification and the lookup) and reports the outcome and how many random
  draws it consumed.

The script also reads the four files the model writes
(`pair-digest.json`, `verification-number.json`,
`identity-classification.json` and `identity-lookup.json`) and recomputes
every answer with its own code: SHA-256 through `hashlib`, its own unsigned
byte order and decimal rendering, its own classification and lookup. A
disagreement stops it. So each of those files has two implementations behind
it before the Rust runner reads it.

Signatures use Z = 64 zero bytes, so the output is byte-reproducible.
Identity secrets are 32 repeated bytes; the initiator's is 0x11 repeated,
the identity secret of `session-e2e.json`'s initiator.

Pure standard library, so it runs wherever `python3` does, except that the
model's verdicts need `lake` on the path and a built model.
"""
from __future__ import annotations

import hashlib
import json
import os
import struct
import subprocess
import sys
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
OUT = HERE / "vectors" / "identity"
MODEL = HERE.parent / "tacenta-model"
INITIATOR_FILE = OUT / "initiator-expectation.json"

# ---------------------------------------------------------------- constants
P = 2**255 - 19
Q = 2**252 + 27742317777372353535851937790883648493
D = (-121665 * pow(121666, P - 2, P)) % P
SQRT_M1 = pow(2, (P - 1) // 4, P)
ZERO_Z = bytes(64)
PAIR_DIGEST_LABEL = b"Tacenta:identity:pair-digest:v1\xff"
assert len(PAIR_DIGEST_LABEL) == 32
EC_TYPE = 0x05   # EncodeEC's type byte
KEM_TYPE = 0x08  # EncodeKEM's type byte
KEM_Q = 3329
KEM_EK_LEN = 1568  # ML-KEM-1024: 384 * 4 + 32
ABSENT_ID = 0


# ------------------------------------------------------- field and curve maths
def inv(x):
    return pow(x, P - 2, P)


IDENT = (0, 1, 1, 0)  # extended coordinates X, Y, Z, T


def add(a, b):
    x1, y1, z1, t1 = a
    x2, y2, z2, t2 = b
    aa = (y1 - x1) * (y2 - x2) % P
    bb = (y1 + x1) * (y2 + x2) % P
    cc = t1 * 2 * D * t2 % P
    dd = z1 * 2 * z2 % P
    e, f, g, h = bb - aa, dd - cc, dd + cc, bb + aa
    return (e * f % P, g * h % P, f * g % P, e * h % P)


def neg(a):
    x, y, z, t = a
    return ((-x) % P, y, z, (-t) % P)


def mul(k, pt):
    r = IDENT
    while k > 0:
        if k & 1:
            r = add(r, pt)
        pt = add(pt, pt)
        k >>= 1
    return r


def affine(pt):
    x, y, z, _ = pt
    zi = inv(z)
    return (x * zi % P, y * zi % P)


def is_identity(pt):
    return affine(pt) == (0, 1)


def encode_point(pt):
    x, y = affine(pt)
    return (y | ((x & 1) << 255)).to_bytes(32, "little")


def recover_x(y, sign):
    """x with x^2 = (y^2 - 1) / (d y^2 + 1) and the given low bit, or None."""
    num = (y * y - 1) % P
    den = (D * y * y + 1) % P
    x2 = num * inv(den) % P
    x = pow(x2, (P + 3) // 8, P)
    if (x * x - x2) % P != 0:
        x = x * SQRT_M1 % P
    if (x * x - x2) % P != 0:
        return None
    if (x & 1) != sign:
        x = (-x) % P
    return x


def point(x, y):
    return (x, y, 1, x * y % P)


BASE_Y = 4 * inv(5) % P
BASE = point(recover_x(BASE_Y, 0), BASE_Y)


def lift(u):
    """A point of edwards25519 whose Montgomery u-coordinate is `u`, or None."""
    if u == P - 1:
        return None
    y = (u - 1) * inv(u + 1) % P
    x = recover_x(y, 0)
    return None if x is None else point(x, y)


def montgomery_u(pt):
    _, y = affine(pt)
    return (1 + y) * inv(1 - y) % P


def small_order(pt):
    return is_identity(mul(8, pt))


def clamp(secret):
    b = bytearray(secret)
    b[0] &= 248
    b[31] &= 127
    b[31] |= 64
    return int.from_bytes(bytes(b), "little")


def sha512(*parts):
    h = hashlib.sha512()
    for part in parts:
        h.update(part)
    return h.digest()


def public_key(secret):
    """The X25519 public key of the clamped secret: k*B as a u-coordinate."""
    return montgomery_u(mul(clamp(secret) % Q, BASE)).to_bytes(32, "little")


def x25519(scalar, u_bytes):
    """RFC 7748, section 5: the Montgomery ladder, bit 255 of u masked."""
    k = clamp(scalar)
    u = int.from_bytes(u_bytes, "little") & ((1 << 255) - 1)
    x1, x2, z2, x3, z3, swap = u, 1, 0, u, 1, 0
    for t in reversed(range(255)):
        kt = (k >> t) & 1
        swap ^= kt
        if swap:
            x2, x3, z2, z3 = x3, x2, z3, z2
        swap = kt
        a, b = (x2 + z2) % P, (x2 - z2) % P
        aa, bb = a * a % P, b * b % P
        e = (aa - bb) % P
        c, d = (x3 + z3) % P, (x3 - z3) % P
        da, cb = d * a % P, c * b % P
        x3 = (da + cb) ** 2 % P
        z3 = x1 * (da - cb) ** 2 % P
        x2 = aa * bb % P
        z2 = e * (aa + 121665 * e) % P
    if swap:
        x2, z2 = x3, z3
    return (x2 * pow(z2, P - 2, P) % P).to_bytes(32, "little")


def contributory(u_bytes):
    """Whether an agreement with this public key is contributory: the X25519
    output under a clamped secret is not all zero. A clamped secret is a
    multiple of 8, so the output is zero exactly for a key of order dividing
    8, on the curve or its twist, whatever the secret is."""
    return x25519(bytes([0x5c]) * 32, u_bytes) != bytes(32)


def xeddsa_sign(secret, message, z=ZERO_Z):
    """XEdDSA as identities-and-devices.md, Signing, defines it."""
    k = clamp(secret) % Q
    enc = encode_point(mul(k, BASE))
    a_pub = bytearray(enc)
    a_pub[31] &= 0x7F
    a = k if (enc[31] >> 7) == 0 else (Q - k) % Q
    prefix = bytes([0xFE]) + b"\xff" * 31
    r = int.from_bytes(sha512(prefix, a.to_bytes(32, "little"), message, z), "little") % Q
    big_r = encode_point(mul(r, BASE))
    h = int.from_bytes(sha512(big_r, bytes(a_pub), message), "little") % Q
    s = (r + h * a) % Q
    return big_r + s.to_bytes(32, "little")


def xeddsa_verify(u_bytes, message, sig):
    """identities-and-devices.md, Verifying a signature, steps 1 to 6."""
    if len(u_bytes) != 32 or len(sig) != 64:
        return False
    u = int.from_bytes(u_bytes, "little")
    if (u >> 255) & 1 or u >= P:
        return False
    if u == P - 1:
        return False
    y = (u - 1) * inv(u + 1) % P
    x = recover_x(y, sig[63] >> 7)
    if x is None:
        return False
    a_pt = point(x, y)
    if small_order(a_pt):
        return False
    s = int.from_bytes(sig[32:], "little") & ((1 << 255) - 1)
    if s >= Q:
        return False
    big_r = sig[:32]
    enc_a = encode_point(a_pt)
    h = int.from_bytes(sha512(big_r, enc_a, message), "little") % Q
    check = add(mul(s, BASE), neg(mul(h, a_pt)))
    if encode_point(check) != big_r:
        return False
    return not small_order(check)


# --------------------------------------------------------------- key classes
def canonical(key):
    """message-format.md, Curve public keys: 32 bytes, bit 255 clear, value
    below p."""
    return len(key) == 32 and int.from_bytes(key, "little") < P


def is_identity_key(key):
    """identities-and-devices.md, Identity keys: canonical, and the
    u-coordinate of a point of the prime-order subgroup."""
    if not canonical(key):
        return False
    pt = lift(int.from_bytes(key, "little"))
    return pt is not None and is_identity(mul(Q, pt))


def key_refusal(key):
    """The refusal of a presented key, if any: the canonical encoding first
    (a decode failure), then the identity-key rule."""
    if not canonical(key):
        return "decode-failure"
    if not is_identity_key(key):
        return "invalid-identity-key"
    return None


def u_bytes(u):
    return u.to_bytes(32, "little")


ORDER8 = [
    bytes.fromhex("e0eb7a7c3b41b8ae1656e3faf19fc46ada098deb9c32b1fd866205165f49b800"),
    bytes.fromhex("5f9c95bca3508c24b1d0b1559c83ef5b04445cc4581c8e86d8224eddd09f1157"),
]


def plus_torsion(key):
    """The u-coordinate of key's point plus the order-eight point ORDER8[0]:
    canonical, on the curve, not of prime order, and agreeing with key under
    every clamped secret."""
    base = lift(int.from_bytes(key, "little"))
    t = lift(int.from_bytes(ORDER8[0], "little"))
    assert base is not None and t is not None and small_order(t)
    out = u_bytes(montgomery_u(add(base, t)))
    assert canonical(out) and not is_identity_key(out)
    assert x25519(bytes([0x42]) * 32, out) == x25519(bytes([0x42]) * 32, key)
    return out


# ------------------------------------------------------------ the KEM prekey
def kem_input_ok(ek):
    """FIPS 203's encapsulation-key checks: the length, and the ByteEncode12
    round trip (every 12-bit coefficient below q)."""
    if len(ek) != KEM_EK_LEN:
        return False
    body = ek[: 384 * 4]
    for i in range(0, len(body), 3):
        b0, b1, b2 = body[i], body[i + 1], body[i + 2]
        if (b0 | ((b1 & 0x0F) << 8)) >= KEM_Q or ((b1 >> 4) | (b2 << 4)) >= KEM_Q:
            return False
    return True


def make_kem_prekey():
    """A well-formed ML-KEM-1024 encapsulation key: 1,024 coefficients below
    q from a fixed byte stream, ByteEncode12'd, then a 32-byte seed. Any such
    string passes the input checks, and encapsulation needs nothing else."""
    stream = hashlib.shake_256(b"tacenta-test-vectors identity KEM prekey").digest(4096)
    coeffs = [int.from_bytes(stream[2 * i:2 * i + 2], "little") % KEM_Q for i in range(1024)]
    body = bytearray()
    for i in range(0, 1024, 2):
        a, b = coeffs[i], coeffs[i + 1]
        body += bytes([a & 0xFF, (a >> 8) | ((b & 0x0F) << 4), b >> 4])
    ek = bytes(body) + hashlib.sha256(b"tacenta-test-vectors identity KEM seed").digest()
    assert kem_input_ok(ek)
    return ek


# ------------------------------------------- the pair digest and the number
def bytes_le(a, b):
    """a <= b as strings of unsigned bytes, byte 0 first."""
    for x, y in zip(a, b):
        if x != y:
            return x < y
    return len(a) <= len(b)


def pair_digest(k1, k2):
    """identities-and-devices.md, The identity pair digest: (digest, None),
    or (None, the refusals allowed)."""
    refusals = sorted({r for r in (key_refusal(k1), key_refusal(k2)) if r})
    if refusals:
        return None, refusals
    lo, hi = (k1, k2) if bytes_le(k1, k2) else (k2, k1)
    return hashlib.sha256(PAIR_DIGEST_LABEL + lo + hi).digest(), None


def verification_number(digest):
    """The verification number: the digest read big-endian, mod 10^60, as 60
    ASCII digits, most significant first."""
    n = int.from_bytes(digest, "big") % 10**60
    return ("%060d" % n).encode("ascii")


# ------------------------------------------- records, classification, lookup
SAME, NEW, RETIRED = "same", "new", "retired"
CLASS_BYTE = {SAME: 0x01, NEW: 0x02, RETIRED: 0x03}
UNATTRIBUTED, CONTACT, AMBIGUOUS, RETIRED_KEY = "unattributed", "contact", "ambiguous", "retired-key"
ATTRIBUTION_BYTE = {UNATTRIBUTED: 0x00, CONTACT: 0x01, AMBIGUOUS: 0x02, RETIRED_KEY: 0x03}


class Record:
    def __init__(self, current=(), retired=()):
        self.current = list(current)
        self.retired = list(retired)

    def well_formed(self):
        return all(canonical(k) for k in self.current + self.retired)

    def holds(self):
        return bool(self.current or self.retired)


def classify(key, record):
    """session-establishment.md, Classification: (class, None) or
    (None, refusal)."""
    refusal = key_refusal(key)
    if refusal:
        return None, refusal
    if not record.well_formed():
        return None, "malformed-record"
    if key in record.retired:
        return RETIRED, None
    if key in record.current:
        return SAME, None
    return NEW, None


def lookup(key, records):
    """session-establishment.md, Lookup: (result, None) or (None, refusal).
    The result is (attribution, contact or None, retired_for, malformed)."""
    refusal = key_refusal(key)
    if refusal:
        return None, refusal
    same, retired, malformed = [], [], []
    for i, record in enumerate(records):
        cls, why = classify(key, record)
        if why == "malformed-record":
            malformed.append(i)
        elif cls == SAME:
            same.append(i)
        elif cls == RETIRED:
            retired.append(i)
    if len(same) == 1:
        return (CONTACT, same[0], retired, malformed), None
    if len(same) > 1:
        return (AMBIGUOUS, None, retired, malformed), None
    if retired:
        return (RETIRED_KEY, None, retired, malformed), None
    return (UNATTRIBUTED, None, retired, malformed), None


def encode_records(records):
    """The layout of a list of records (README, Vector layouts): a 4-byte
    count, then per record a 4-byte count of current keys, those keys, a
    4-byte count of retired keys and those keys. The n-th record is the
    record of contact n, counting from 0."""
    out = struct.pack(">I", len(records))
    for r in records:
        out += struct.pack(">I", len(r.current)) + b"".join(r.current)
        out += struct.pack(">I", len(r.retired)) + b"".join(r.retired)
    return out


def decode_records(data):
    def u32(at):
        return struct.unpack(">I", data[at:at + 4])[0], at + 4

    def keys(at):
        n, at = u32(at)
        out = [data[at + 32 * i: at + 32 * (i + 1)] for i in range(n)]
        return out, at + 32 * n

    n, at = u32(0)
    records = []
    for _ in range(n):
        cur, at = keys(at)
        ret, at = keys(at)
        records.append(Record(cur, ret))
    if at != len(data):
        raise ValueError("trailing bytes after the records")
    return records


def lookup_fields(result):
    attribution, contact, retired, malformed = result
    fields = [("attribution", "%02x" % ATTRIBUTION_BYTE[attribution])]
    if attribution == CONTACT:
        fields.append(("contact", struct.pack(">I", contact).hex()))
    fields.append(("retired_for", b"".join(struct.pack(">I", i) for i in retired).hex()))
    fields.append(("malformed", b"".join(struct.pack(">I", i) for i in malformed).hex()))
    return fields


# --------------------------------------------------------- the initiator
class Bundle:
    """A prekey bundle's fields (message-format.md, Prekey bundle)."""

    def __init__(self, identity_key, signed_prekey, spk_sig, kem_prekey, kem_sig,
                 one_time_present, one_time_prekey, spk_id, one_time_id, kem_id):
        self.identity_key = identity_key
        self.signed_prekey = signed_prekey
        self.spk_sig = spk_sig
        self.kem_prekey = kem_prekey
        self.kem_sig = kem_sig
        self.one_time_present = one_time_present
        self.one_time_prekey = one_time_prekey
        self.spk_id = spk_id
        self.one_time_id = one_time_id
        self.kem_id = kem_id

    def encode(self):
        return (bytes([0x01, 0x03]) + self.identity_key + self.signed_prekey + self.spk_sig
                + struct.pack(">I", len(self.kem_prekey)) + self.kem_prekey + self.kem_sig
                + bytes([1 if self.one_time_present else 0]) + self.one_time_prekey
                + struct.pack(">III", self.spk_id, self.one_time_id, self.kem_id))

    def decodes(self):
        """Whether the bundle decoder accepts the encoding: the curve keys
        canonical, the KEM prekey of the KEM's length, and an absent one-time
        prekey's padding zero."""
        return (canonical(self.identity_key) and canonical(self.signed_prekey)
                and len(self.kem_prekey) == KEM_EK_LEN
                and (canonical(self.one_time_prekey) if self.one_time_present
                     else self.one_time_prekey == bytes(32)))


def initiator(expectation, records, bundle):
    """The initiator's establishment, in the order session-establishment.md
    fixes (Sending the initial message; Records, expectations and
    attribution, The initiator). Returns (outcome, draws): outcome is a
    refusal name or ("session", lookup result); draws is True when the step
    draws randomness before its outcome, None where the pages leave that
    open."""
    kind, known = expectation
    # A malformed expectation, before any check of Sending the initial message.
    if kind == "known":
        record = records[known]
        if not record.well_formed() or not record.holds():
            return "malformed-record", False
    elif not all(r.well_formed() for r in records):
        return "malformed-record", False
    # The bundle's presence and canonical-key checks.
    if bundle.one_time_present != (bundle.one_time_id != ABSENT_ID):
        return "inconsistent-bundle", False
    if not (canonical(bundle.identity_key) and canonical(bundle.signed_prekey)
            and (not bundle.one_time_present or canonical(bundle.one_time_prekey))):
        return "non-canonical-key", False
    # The expectation, the identity-key rule first.
    ikb = bundle.identity_key
    if kind == "known":
        cls, refusal = classify(ikb, records[known])
        if refusal:
            return refusal, False
        if cls == RETIRED:
            return "retired-identity", False
        if cls == NEW:
            return "unexpected-identity", False
    else:
        result, refusal = lookup(ikb, records)
        if refusal:
            return refusal, False
        if result[0] in (CONTACT, AMBIGUOUS):
            return "unexpected-identity", False
        if result[0] == RETIRED_KEY:
            return "retired-identity", False
    # The rule again (it cannot fire here), then both signatures.
    if not is_identity_key(ikb):
        return "invalid-identity-key", False
    if not (xeddsa_verify(ikb, bytes([EC_TYPE]) + bundle.signed_prekey, bundle.spk_sig)
            and xeddsa_verify(ikb, bytes([KEM_TYPE]) + bundle.kem_prekey, bundle.kem_sig)):
        return "authentication-failure", False
    # The KEM prekey's input checks: before or after EKA, the pages leave open.
    if not kem_input_ok(bundle.kem_prekey):
        return "kem-input", None
    # EKA is drawn, then the agreements.
    if not contributory(bundle.signed_prekey) or (
            bundle.one_time_present and not contributory(bundle.one_time_prekey)):
        return "non-contributory", True
    result, refusal = lookup(ikb, records)
    assert refusal is None
    return ("session", result), True


# ------------------------------------------------------------------- keys
INITIATOR_SECRET = bytes([0x11]) * 32
SPK_SECRET = bytes([0x31]) * 32
OPK_SECRET = bytes([0x33]) * 32


def identity(byte):
    secret = bytes([byte]) * 32
    key = public_key(secret)
    assert is_identity_key(key)
    return secret, key


K_SECRET, K = identity(0x22)        # the expected peer: session-e2e.json's responder
KP_SECRET, KP = identity(0x23)      # another identity key, a substitute
KPP_SECRET, KPP = identity(0x24)    # a key in no record
KOLD_SECRET, KOLD = identity(0x25)  # a key a record has retired
KD_SECRET, KD = identity(0x26)      # another contact's current key
K_T = plus_torsion(K)               # K's point plus a torsion point of order 8
U0, U1, U2, PM1 = u_bytes(0), u_bytes(1), u_bytes(2), u_bytes(P - 1)
P_SPELLED = u_bytes(P)                    # u = p: not canonical
SPK = public_key(SPK_SECRET)
OPK = public_key(OPK_SECRET)
EK = make_kem_prekey()
# A full-length KEM prekey whose first coefficient is 4095: it fails the
# ByteEncode12 round trip.
EK_UNENCODABLE = bytes([0xFF, 0x0F]) + EK[2:]
assert len(EK_UNENCODABLE) == KEM_EK_LEN and not kem_input_ok(EK_UNENCODABLE)


def bit255(key):
    out = bytearray(key)
    out[31] |= 0x80
    return bytes(out)


def plus_p(key):
    return (int.from_bytes(key, "little") + P).to_bytes(32, "little")


def spoil(sig):
    """The signature with its first byte changed: R no longer matches."""
    return bytes([sig[0] ^ 0x01]) + sig[1:]


def bundle(ik, signer, spk=SPK, opk=OPK, one_time_id=2, ek=EK, spk_sig_ok=True,
           kem_sig_ok=True, one_time_present=None):
    """A bundle naming `ik`, its prekeys signed by `signer`."""
    spk_sig = xeddsa_sign(signer, bytes([EC_TYPE]) + spk)
    kem_sig = xeddsa_sign(signer, bytes([KEM_TYPE]) + ek)
    if not spk_sig_ok:
        spk_sig = spoil(spk_sig)
    if not kem_sig_ok:
        kem_sig = spoil(kem_sig)
    present = opk is not None if one_time_present is None else one_time_present
    return Bundle(ik, spk, spk_sig, ek, kem_sig, present,
                  opk if opk is not None else bytes(32), 1, one_time_id, 4)


FIRST = ("first", None)


def known(i=0):
    return ("known", i)


def expectation_hex(expectation):
    kind, i = expectation
    return "00" if kind == "first" else "01" + struct.pack(">I", i).hex()


# ------------------------------------------------------------------ the cases
class Case:
    def __init__(self, vid, comment, expectation, records, b, intent, raw=False):
        self.vid = vid
        self.comment = comment
        self.expectation = expectation
        self.records = records
        self.bundle = b
        self.intent = intent
        self.raw = raw


def cases():
    rec_k = [Record([K])]
    rec_k_old = [Record([K], [KOLD])]
    out = []

    def case(vid, comment, expectation, records, b, intent, raw=False):
        out.append(Case(vid, comment, expectation, records, b, intent, raw))

    case("known-same", "known, with K current in the record; the bundle names K",
         known(), rec_k, bundle(K, K_SECRET), "session")
    case("known-new", "known, with K current in the record; the bundle names another identity key, "
         "whose signatures verify under it: new in the record",
         known(), rec_k, bundle(KP, KP_SECRET), "unexpected-identity")
    case("known-retired", "known, with K current and K_old retired; the bundle names K_old",
         known(), rec_k_old, bundle(KOLD, KOLD_SECRET), "retired-identity")
    case("known-new-bad-signed-prekey-signature",
         "known K; another identity key whose signed-prekey signature does not verify: the expectation "
         "refuses it before the signatures are checked",
         known(), rec_k, bundle(KP, KP_SECRET, spk_sig_ok=False), "unexpected-identity")
    case("known-new-bad-kem-prekey-signature",
         "known K; another identity key whose KEM-prekey signature does not verify: the expectation "
         "refuses it before the signatures are checked",
         known(), rec_k, bundle(KP, KP_SECRET, kem_sig_ok=False), "unexpected-identity")
    case("known-same-bad-signatures",
         "known K; the bundle names K and neither signature verifies: the signatures are still checked",
         known(), rec_k, bundle(K, K_SECRET, spk_sig_ok=False, kem_sig_ok=False),
         "authentication-failure")
    case("known-new-key-without-identifier",
         "known K; another identity key, with a one-time prekey and the absent identifier: the presence "
         "check comes before the expectation",
         known(), rec_k, bundle(KP, KP_SECRET, one_time_id=ABSENT_ID), "inconsistent-bundle")
    case("known-new-identifier-without-key",
         "known K; another identity key, with no one-time prekey and an identifier: the presence check "
         "comes before the expectation",
         known(), rec_k, bundle(KP, KP_SECRET, opk=None, one_time_id=2), "inconsistent-bundle")
    case("known-new-unencodable-kem-prekey",
         "known K; another identity key, with a full-length KEM prekey that fails the ByteEncode12 round "
         "trip: the expectation comes before the KEM prekey's input checks",
         known(), rec_k, bundle(KP, KP_SECRET, ek=EK_UNENCODABLE), "unexpected-identity")
    case("known-same-unencodable-kem-prekey",
         "known K; the bundle names K, with the same KEM prekey: refused by the KEM prekey's input checks",
         known(), rec_k, bundle(K, K_SECRET, ek=EK_UNENCODABLE), "kem-input")
    case("known-new-short-kem-prekey",
         "known K; another identity key, with a KEM prekey one byte short, which the bundle decoder "
         "refuses: given as fields",
         known(), rec_k, bundle(KP, KP_SECRET, ek=EK[:-1]), "unexpected-identity", raw=True)
    case("known-same-short-kem-prekey",
         "known K; the bundle names K, with a KEM prekey one byte short, given as fields: refused by the "
         "KEM prekey's input checks",
         known(), rec_k, bundle(K, K_SECRET, ek=EK[:-1]), "kem-input", raw=True)
    case("known-same-long-kem-prekey",
         "known K; the bundle names K, with a KEM prekey one byte long, given as fields: refused by the "
         "KEM prekey's input checks",
         known(), rec_k, bundle(K, K_SECRET, ek=EK + b"\x00"), "kem-input", raw=True)
    case("known-new-low-order-one-time-prekey",
         "known K; another identity key, with a one-time prekey of order 8: the expectation comes before "
         "any agreement",
         known(), rec_k, bundle(KP, KP_SECRET, opk=ORDER8[0]), "unexpected-identity")
    case("known-same-low-order-one-time-prekey",
         "known K; the bundle names K, with a one-time prekey of order 8: a non-contributory agreement",
         known(), rec_k, bundle(K, K_SECRET, opk=ORDER8[0]), "non-contributory")
    case("known-new-low-order-signed-prekey",
         "known K; another identity key, with the signed prekey u = 0: the expectation comes before any "
         "agreement",
         known(), rec_k, bundle(KP, KP_SECRET, spk=U0), "unexpected-identity")
    case("known-same-low-order-signed-prekey",
         "known K; the bundle names K, with the signed prekey u = 0: a non-contributory agreement",
         known(), rec_k, bundle(K, K_SECRET, spk=U0), "non-contributory")
    case("known-malformed-record-bad-signature",
         "known, with a record holding K and u = p, which is not canonical; the bundle names K and its "
         "signed-prekey signature does not verify: the malformed expectation comes first",
         known(), [Record([K, P_SPELLED])], bundle(K, K_SECRET, spk_sig_ok=False), "malformed-record")
    case("known-mixed-order-identity",
         "known K; the bundle names K plus a torsion point of order 8, signed by K's secret: not an "
         "identity key",
         known(), rec_k, bundle(K_T, K_SECRET), "invalid-identity-key")
    case("first-contact-no-records-mixed-order-identity",
         "first contact with no records; the bundle names K plus a torsion point of order 8: not an "
         "identity key",
         FIRST, [], bundle(K_T, K_SECRET), "invalid-identity-key")
    case("known-respelled-identity-bit-255",
         "known K; the bundle names K with bit 255 set, given as fields since the bundle decoder refuses "
         "it: the canonical-key check comes before the expectation",
         known(), rec_k, bundle(bit255(K), K_SECRET), "non-canonical-key", raw=True)
    case("known-respelled-identity-plus-p",
         "known K; the bundle names K + p, given as fields since the bundle decoder refuses it: the "
         "canonical-key check comes before the expectation",
         known(), rec_k, bundle(plus_p(K), K_SECRET), "non-canonical-key", raw=True)
    case("first-contact-no-records",
         "first contact with no records; a valid bundle: a session, unattributed",
         FIRST, [], bundle(KPP, KPP_SECRET), "session")
    case("known-empty-record",
         "known, with a record whose two sets are both empty; a valid bundle naming K",
         known(), [Record()], bundle(K, K_SECRET), "malformed-record")
    case("known-empty-record-bad-signature",
         "known, with a record whose two sets are both empty; the bundle names K and its signed-prekey "
         "signature does not verify",
         known(), [Record()], bundle(K, K_SECRET, spk_sig_ok=False), "malformed-record")
    case("first-contact-retired-key",
         "first contact; K_old is retired for contact 0 and current for none",
         FIRST, rec_k_old, bundle(KOLD, KOLD_SECRET), "retired-identity")
    case("first-contact-recorded-contact",
         "first contact; the bundle names a key current for contact 0",
         FIRST, [Record([KD])], bundle(KD, KD_SECRET), "unexpected-identity")
    case("first-contact-current-and-retired-elsewhere",
         "first contact; K is current for contact 0 and retired for contact 1",
         FIRST, [Record([K]), Record([], [K])], bundle(K, K_SECRET), "unexpected-identity")
    case("known-same-also-current-elsewhere",
         "known, with the record of contact 0; K is current for contacts 0 and 1: a session, which the "
         "lookup finds ambiguous",
         known(0), [Record([K]), Record([K])], bundle(K, K_SECRET), "session")
    case("first-contact-malformed-record-bad-signature",
         "first contact; a record holds a key with bit 255 set; the bundle's signed-prekey signature "
         "does not verify: the malformed expectation comes first",
         FIRST, [Record([bit255(KD)])], bundle(KPP, KPP_SECRET, spk_sig_ok=False), "malformed-record")
    case("first-contact-ambiguous",
         "first contact; K is current for contacts 0 and 1",
         FIRST, [Record([K]), Record([K])], bundle(K, K_SECRET), "unexpected-identity")
    for name, ik, what in (("u-0", U0, "u = 0, of order 2"), ("u-1", U1, "u = 1, of order 4"),
                           ("u-p-minus-1", PM1, "u = p - 1"),
                           ("u-order8-a", ORDER8[0], "a u-coordinate of order 8"),
                           ("u-order8-b", ORDER8[1], "a u-coordinate of order 8"),
                           ("u-2", U2, "u = 2, on the twist")):
        case("known-non-identity-key-" + name,
             "known K; the bundle names %s, and neither signature verifies: not an identity key, "
             "whatever the signatures" % what,
             known(), rec_k, bundle(ik, K_SECRET, spk_sig_ok=False, kem_sig_ok=False),
             "invalid-identity-key")
    case("known-retired-mixed-order-identity",
         "known, with K current and K plus a torsion point retired; the bundle names the retired bytes: "
         "not an identity key, rather than a retired identity",
         known(), [Record([K], [K_T])], bundle(K_T, K_SECRET), "invalid-identity-key")
    for name, ik, what in (("u-2", U2, "u = 2, on the twist"), ("u-p-minus-1", PM1, "u = p - 1")):
        case("first-contact-no-records-non-identity-key-" + name,
             "first contact with no records; the bundle names %s: not an identity key" % what,
             FIRST, [], bundle(ik, K_SECRET), "invalid-identity-key")
    case("known-malformed-record-non-identity-key",
         "known, with a record holding K and u = p; the bundle names u = 0: the malformed expectation "
         "comes first",
         known(), [Record([K, P_SPELLED])], bundle(U0, K_SECRET), "malformed-record")
    case("known-inconsistent-presence-non-identity-key",
         "known K; the bundle names u = 0 and has a one-time prekey with the absent identifier: the "
         "presence check comes first",
         known(), rec_k, bundle(U0, K_SECRET, one_time_id=ABSENT_ID), "inconsistent-bundle")
    case("known-record-with-non-identity-member",
         "known, with K and u = 0 current: a canonical member that is not an identity key does not make "
         "the record malformed",
         known(), [Record([K, U0])], bundle(K, K_SECRET), "session")
    case("first-contact-record-of-non-identity-key",
         "first contact; the one record holds only u = 0; the bundle names a key in no record: a "
         "session, unattributed",
         FIRST, [Record([U0])], bundle(KPP, KPP_SECRET), "session")
    return out


# ------------------------------------------------------------ the model's verdict
def model_request(case):
    """One line for `genvectors initiator-expectation-verdicts`: the case's
    id, expectation, records and bundle fields, and the facts the model
    cannot compute."""
    b = case.bundle
    low = b"".join(k for k in (b.signed_prekey, b.one_time_prekey if b.one_time_present else None)
                   if k is not None and canonical(k) and not contributory(k))
    spk_ok = xeddsa_verify(b.identity_key, bytes([EC_TYPE]) + b.signed_prekey, b.spk_sig)
    kem_ok = xeddsa_verify(b.identity_key, bytes([KEM_TYPE]) + b.kem_prekey, b.kem_sig)
    dash = lambda bs: bs.hex() if bs else "-"  # noqa: E731
    return " ".join([
        case.vid, expectation_hex(case.expectation), encode_records(case.records).hex(),
        b.identity_key.hex(), b.signed_prekey.hex(), "01" if b.one_time_present else "00",
        b.one_time_prekey.hex(), "%08x" % b.one_time_id, dash(b.kem_prekey),
        "1" if spk_ok else "0", "1" if kem_ok else "0", "1" if kem_input_ok(b.kem_prekey) else "0",
        dash(low), INITIATOR_SECRET.hex(), public_key(INITIATOR_SECRET).hex()])


def model_verdicts(all_cases):
    lake = os.environ.get("LAKE", "lake")
    request = "".join(model_request(c) + "\n" for c in all_cases)
    # The requests go in through a file rather than a pipe: `lake exe` does
    # not start the program until it has finished its own build check, and a
    # pipe the size of these requests fills before then.
    with tempfile.TemporaryFile() as fh:
        fh.write(request.encode())
        fh.seek(0)
        try:
            run = subprocess.run([lake, "exe", "genvectors", "initiator-expectation-verdicts"],
                                 cwd=str(MODEL), stdin=fh, stdout=subprocess.PIPE,
                                 stderr=subprocess.PIPE, check=False)
        except OSError as e:
            raise SystemExit("generate-identity-vectors: cannot run %s: %s" % (lake, e))
    if run.returncode != 0:
        sys.stderr.write(run.stderr.decode(errors="replace"))
        raise SystemExit("generate-identity-vectors: the model's verdicts failed")
    out = {}
    for line in run.stdout.decode().splitlines():
        parts = line.split(" ")
        out[parts[0]] = parts[1:]
    return out


# ------------------------------------------------------------------ rendering
def obj(pairs):
    return "{ " + ", ".join("%s: %s" % (json.dumps(k), json.dumps(v)) for k, v in pairs) + " }"


def render_vector(case, outcome):
    b = case.bundle
    inputs = [("expectation", expectation_hex(case.expectation)),
              ("records", encode_records(case.records).hex()),
              ("bundle_fields" if case.raw else "bundle", b.encode().hex()),
              ("initiator_identity_secret", INITIATOR_SECRET.hex())]
    head = "    { %s, %s, " % ('"id": ' + json.dumps(case.vid), '"comment": ' + json.dumps(case.comment))
    if isinstance(outcome, tuple):
        fields = [("peer_identity", b.identity_key.hex())] + lookup_fields(outcome[1])
        return head + '"inputs": %s, "fields": %s }' % (obj(inputs), obj(fields))
    return head + '"result": "invalid", "refusal": %s, "inputs": %s }' % (json.dumps(outcome), obj(inputs))


SOURCE = (
    "Written by tacenta-test-vectors/generate-identity-vectors.py, not model output: the bundles carry XEdDSA "
    "signatures, which the model cannot make. The script builds each case with its own field and curve "
    "arithmetic, XEdDSA and ML-KEM encapsulation-key check, and writes it only when its own reading of "
    "session-establishment.md (Sending the initial message; Records, expectations and attribution) and the "
    "model's (Model.InitiatorExpectation.establishInitiatorExpecting, through lake exe genvectors "
    "initiator-expectation-verdicts, given the signature, KEM-input and low-order verdicts) both give the "
    "case its intended outcome. Identity secrets are 32 repeated bytes and Z is 64 zero bytes. Layout: "
    "tacenta-test-vectors/README.md, Vector layouts.")


def render_file(rows):
    return ("{\n  \"schema_version\": 1,\n  \"algorithm\": \"initiator-expectation\",\n  \"source\": "
            + json.dumps(SOURCE) + ",\n  \"vectors\": [\n" + ",\n".join(rows) + "\n  ]\n}\n")


# ---------------------------------------------------------- the model's files
def check_model_files():
    """Recompute every answer in the four model-generated files."""
    problems = []

    def load(name):
        with open(OUT / name) as fh:
            return json.load(fh)["vectors"]

    def refused(v, allowed):
        if v.get("result") != "invalid":
            return False
        if "acceptable_refusals" in v:
            return sorted(v["acceptable_refusals"]) == allowed
        return [v.get("refusal")] == allowed

    for v in load("pair-digest.json"):
        k1, k2 = bytes.fromhex(v["inputs"]["k1"]), bytes.fromhex(v["inputs"]["k2"])
        digest, allowed = pair_digest(k1, k2)
        if digest is not None:
            want = {"digest": digest.hex(), "verification_number": verification_number(digest).hex()}
            if v.get("result", "valid") != "valid" or v.get("fields") != want:
                problems.append("pair-digest.json %s" % v["id"])
        elif not refused(v, allowed):
            problems.append("pair-digest.json %s: expected a refusal in %s" % (v["id"], allowed))
    for v in load("verification-number.json"):
        number = verification_number(bytes.fromhex(v["inputs"]["digest"]))
        if v.get("output") != number.hex():
            problems.append("verification-number.json %s" % v["id"])
    for v in load("identity-classification.json"):
        ins = v["inputs"]
        record = Record(split_keys(ins["current"]), split_keys(ins["retired"]))
        cls, refusal = classify(bytes.fromhex(ins["key"]), record)
        if refusal and not refused(v, [refusal]):
            problems.append("identity-classification.json %s: expected %s" % (v["id"], refusal))
        if cls and v.get("output") != "%02x" % CLASS_BYTE[cls]:
            problems.append("identity-classification.json %s: expected %s" % (v["id"], cls))
    for v in load("identity-lookup.json"):
        ins = v["inputs"]
        result, refusal = lookup(bytes.fromhex(ins["key"]), decode_records(bytes.fromhex(ins["records"])))
        if refusal and not refused(v, [refusal]):
            problems.append("identity-lookup.json %s: expected %s" % (v["id"], refusal))
        if result and v.get("fields") != dict(lookup_fields(result)):
            problems.append("identity-lookup.json %s: expected %s" % (v["id"], dict(lookup_fields(result))))
    return problems


def split_keys(hexstr):
    data = bytes.fromhex(hexstr)
    if len(data) % 32:
        raise ValueError("a key list is not a whole number of keys")
    return [data[i:i + 32] for i in range(0, len(data), 32)]


# ----------------------------------------------------------------------- main
def build():
    all_cases = cases()
    ids = [c.vid for c in all_cases]
    if len(set(ids)) != len(ids):
        raise SystemExit("generate-identity-vectors: duplicate ids")
    verdicts = model_verdicts(all_cases)
    rows, problems = [], []
    for c in all_cases:
        if c.raw == c.bundle.decodes():
            problems.append("%s: given %s, but the decoder %s it" % (
                c.vid, "as fields" if c.raw else "whole", "accepts" if c.bundle.decodes() else "refuses"))
        outcome, draws = initiator(c.expectation, c.records, c.bundle)
        name = outcome if isinstance(outcome, str) else outcome[0]
        if name != c.intent:
            problems.append("%s: this script gives %s, the case intends %s" % (c.vid, name, c.intent))
        model = verdicts.get(c.vid)
        if model is None:
            problems.append("%s: the model gave no verdict" % c.vid)
            continue
        if model[0] != name:
            problems.append("%s: the model gives %s, this script %s" % (c.vid, model[0], name))
        # Every refusal before the signatures draws nothing; the model's count
        # of consumed draws must say so.
        if draws is False and model[1] != "0":
            problems.append("%s: the model drew %s values before refusing" % (c.vid, model[1]))
        if draws is True and model[1] == "0":
            problems.append("%s: the model drew nothing" % c.vid)
        if isinstance(outcome, tuple):
            dash = lambda s: "" if s == "-" else s  # noqa: E731
            want = dict(lookup_fields(outcome[1]))
            got = {"attribution": model[3], "retired_for": dash(model[5]), "malformed": dash(model[6])}
            if model[4] != "-":
                got["contact"] = model[4]
            if model[2] != c.bundle.identity_key.hex() or got != want:
                problems.append("%s: the model's session or lookup differs: %s" % (c.vid, model))
        rows.append(render_vector(c, outcome))
    problems += check_model_files()
    if problems:
        for p in problems:
            print("generate-identity-vectors: " + p, file=sys.stderr)
        raise SystemExit(1)
    return render_file(rows), len(rows)


def main():
    check = "--check" in sys.argv[1:]
    text, count = build()
    if check:
        if not INITIATOR_FILE.exists() or INITIATOR_FILE.read_text() != text:
            print("DIFFERS  " + INITIATOR_FILE.name)
            return 1
        print("current  %s (%d vectors); the four model files agree with this script" % (INITIATOR_FILE.name, count))
        return 0
    tmp = INITIATOR_FILE.with_suffix(".json.tmp")
    tmp.write_text(text)
    tmp.replace(INITIATOR_FILE)
    print("wrote    %s (%d vectors); the four model files agree with this script" % (INITIATOR_FILE.name, count))
    return 0


if __name__ == "__main__":
    sys.exit(main())
