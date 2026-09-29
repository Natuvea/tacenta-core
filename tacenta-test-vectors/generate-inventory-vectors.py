#!/usr/bin/env python3
"""Write the four hosted-inventory vector files under vectors/groups/.

    python3 tacenta-test-vectors/generate-inventory-vectors.py            # rewrite
    python3 tacenta-test-vectors/generate-inventory-vectors.py --check    # compare

These files are not model output. The Lean model has no inventory statement, so
the oracle is this script: a Python implementation of `tacenta-spec`, "Hosted
device-inventory statements" and "Accepting a signed statement", with its own
field and curve arithmetic and its own XEdDSA. Nothing is read at run time from
the Rust implementation or the model. Every case is built with a stated intent
(the refusal class it should hit), then run through the oracle, and the script
stops if the oracle disagrees with the intent. `tacenta-core`'s tests and the
independent reader then check the committed bytes with their own code. This is
one implementation of the page; the reader is the second reading.

Signers are fixed so the output is byte-reproducible: the issuer secret for
`acme/alice` is 32 bytes of 0x09 and for `acme/bob` 32 bytes of 0x0a, and every
signature uses Z = 64 zero bytes. Device identity keys are the X25519 public
keys of 32-byte secrets that repeat one byte.

Pure standard library, so it runs wherever `python3` does.
"""
from __future__ import annotations

import hashlib
import json
import struct
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
OUT = HERE / "vectors" / "groups"

# ---------------------------------------------------------------- constants
P = 2**255 - 19
Q = 2**252 + 27742317777372353535851937790883648493
D = (-121665 * pow(121666, P - 2, P)) % P
SQRT_M1 = pow(2, (P - 1) // 4, P)

DOMAIN = b"Tacenta Inventory Statement v1"
SIGNING_LABEL = b"Tacenta:inventory-statement:v1\xff"
COMMITMENT_LABEL = b"Tacenta:inventory-binding-commitment:v1\xff"
APPLICATION_LABEL = b"tacenta:application-signature:v1\xff"
GROUP_EPOCH_V1 = 1
MAX_ACCOUNT = 256
MAX_ACTIVE = 8
MAX_REVOKED = 8
ZERO_Z = bytes(64)


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
    """A point of edwards25519 whose Montgomery u-coordinate is `u`, or None.

    `u` must be below p. `u = p - 1` has no image (the map divides by zero).
    """
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


def xeddsa_sign_leaving_the_sign_bit(secret, message, z=ZERO_Z):
    """A signer that does not normalise: it keeps `k` and sets bit 255 of the
    signature to the sign of x, which Verifying a signature reads back as A's
    sign (identities-and-devices.md, "It is wider on the sign bit")."""
    k = clamp(secret) % Q
    enc = encode_point(mul(k, BASE))
    prefix = bytes([0xFE]) + b"\xff" * 31
    r = int.from_bytes(sha512(prefix, k.to_bytes(32, "little"), message, z), "little") % Q
    big_r = encode_point(mul(r, BASE))
    h = int.from_bytes(sha512(big_r, enc, message), "little") % Q
    s = (r + h * k) % Q | ((enc[31] >> 7) << 255)
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
    return len(key) == 32 and int.from_bytes(key, "little") < P


def is_identity_key(key):
    """Check 6: canonical, and the u-coordinate of a point of order q."""
    if not canonical(key):
        return False
    pt = lift(int.from_bytes(key, "little"))
    return pt is not None and is_identity(mul(Q, pt))


def u_bytes(u):
    return u.to_bytes(32, "little")


ORDER8 = [
    bytes.fromhex("e0eb7a7c3b41b8ae1656e3faf19fc46ada098deb9c32b1fd866205165f49b800"),
    bytes.fromhex("5f9c95bca3508c24b1d0b1559c83ef5b04445cc4581c8e86d8224eddd09f1157"),
]
LOW_ORDER = [u_bytes(0), u_bytes(1), u_bytes(P - 1)] + ORDER8


def torsion_generator():
    pt = lift(int.from_bytes(ORDER8[0], "little"))
    assert pt is not None and small_order(pt) and not is_identity(mul(4, pt))
    return pt


def spellings(key):
    """The eight u-coordinates of key + j*T for the order-eight point T."""
    base = lift(int.from_bytes(key, "little"))
    assert base is not None
    t = torsion_generator()
    out = []
    for j in range(8):
        out.append(u_bytes(montgomery_u(add(base, mul(j, t)))))
    return out


def device_key(n):
    """An honest identity key: the public half of the secret n, n, ..., n."""
    key = public_key(bytes([n]) * 32)
    assert is_identity_key(key)
    return key


# --------------------------------------------------------------- statements
class Binding:
    def __init__(self, device_id, key, capabilities=GROUP_EPOCH_V1, predecessor=None):
        self.device_id = device_id
        self.key = key
        self.capabilities = capabilities
        self.predecessor = predecessor

    def encode(self):
        out = struct.pack(">I", self.device_id) + self.key + struct.pack(">Q", self.capabilities)
        if self.predecessor is None:
            return out + b"\x00"
        return out + b"\x01" + self.predecessor

    def json(self):
        obj = {"device_id": self.device_id, "identity_hex": self.key.hex(), "capabilities": self.capabilities}
        if self.predecessor is not None:
            obj["replacement_predecessor_hex"] = self.predecessor.hex()
        return obj

    def commitment(self):
        if self.capabilities != GROUP_EPOCH_V1:
            return None
        return hashlib.sha256(COMMITMENT_LABEL + self.encode()).digest()


class Revocation:
    def __init__(self, binding, terminal):
        self.binding = binding
        self.terminal = terminal

    def encode(self):
        return self.binding.encode() + struct.pack(">Q", self.terminal)

    def json(self):
        return {"binding": self.binding.json(), "terminal_generation": self.terminal}


class Statement:
    def __init__(self, issuer, account, generation, active, floor=0, revoked=()):
        self.issuer = issuer
        self.account = account if isinstance(account, bytes) else account.encode()
        self.generation = generation
        self.active = list(active)
        self.floor = floor
        self.revoked = list(revoked)

    def encode(self, count_active=None, count_revoked=None):
        out = DOMAIN + struct.pack(">Q", self.issuer)
        out += struct.pack(">I", len(self.account)) + self.account
        out += struct.pack(">Q", self.generation)
        out += struct.pack(">I", len(self.active) if count_active is None else count_active)
        out += b"".join(b.encode() for b in self.active)
        out += struct.pack(">Q", self.floor)
        out += struct.pack(">I", len(self.revoked) if count_revoked is None else count_revoked)
        out += b"".join(r.encode() for r in self.revoked)
        return out

    def sorted(self):
        """The same statement with both lists in the specified order."""
        return Statement(
            self.issuer, self.account, self.generation,
            sorted(self.active, key=lambda b: b.encode()), self.floor,
            sorted(self.revoked, key=lambda r: r.encode()),
        )

    def json(self, case_id):
        return {
            "id": case_id,
            "issuer_key_id": self.issuer,
            "account_handle": self.account.decode(),
            "inventory_generation": self.generation,
            "active": [b.json() for b in self.active],
            "revocation_floor_generation": self.floor,
            "revoked": [r.json() for r in self.revoked],
            "unsigned_hex": self.encode().hex(),
        }


class Refuse(Exception):
    pass


def decode(data):
    """The unsigned decoder of identities-and-devices.md; raises Refuse."""
    pos = 0

    def take(n):
        nonlocal pos
        if n < 0 or pos + n > len(data):
            raise Refuse("truncated")
        chunk = data[pos:pos + n]
        pos += n
        return chunk

    def u32():
        return struct.unpack(">I", take(4))[0]

    def u64():
        return struct.unpack(">Q", take(8))[0]

    if take(len(DOMAIN)) != DOMAIN:
        raise Refuse("domain")
    issuer = u64()
    length = u32()
    if length == 0 or length > MAX_ACCOUNT:
        raise Refuse("account length")
    account = take(length)
    try:
        account.decode("utf-8")
    except UnicodeDecodeError:
        raise Refuse("account utf-8")
    generation = u64()

    def binding():
        device = u32()
        key = take(32)
        caps = u64()
        tag = take(1)[0]
        if tag == 0:
            pred = None
        elif tag == 1:
            pred = take(32)
        else:
            raise Refuse("tag")
        if caps == 0 or caps & ~GROUP_EPOCH_V1:
            raise Refuse("capabilities")
        return Binding(device, key, caps, pred)

    n_active = u32()
    if n_active > MAX_ACTIVE:
        raise Refuse("active count")
    active = [binding() for _ in range(n_active)]
    floor = u64()
    n_revoked = u32()
    if n_revoked > MAX_REVOKED:
        raise Refuse("revoked count")
    revoked = [Revocation(binding(), u64()) for _ in range(n_revoked)]
    if pos != len(data):
        raise Refuse("trailing bytes")
    if floor > generation:
        raise Refuse("floor above generation")
    for r in revoked:
        if not (floor < r.terminal <= generation):
            raise Refuse("terminal generation")
    for group in ([b.encode() for b in active], [r.encode() for r in revoked]):
        for earlier, later in zip(group, group[1:]):
            if not earlier < later:
                raise Refuse("order")
    exact = {b.encode() for b in active}
    if any(r.binding.encode() in exact for r in revoked):
        raise Refuse("binding in both lists")
    statement = Statement(issuer, account, generation, active, floor, revoked)
    if statement.encode() != data:
        raise Refuse("re-encoding differs")
    return statement


# ------------------------------------------------------------------- acceptance
class Policy:
    """The scripted policy every acceptance case names (README, Vector layouts)."""

    def __init__(self, issuers, fresh, refuse_binding=None, refuse_every_binding=False, refuse_statement=False):
        self.issuers = issuers  # list of (issuer_key_id, account bytes or None, key)
        self.fresh = fresh  # list of (account bytes, generation)
        self.refuse_binding = refuse_binding  # (key, "active"/"revoked") or None
        self.refuse_every_binding = refuse_every_binding
        self.refuse_statement = refuse_statement

    def json(self):
        return {
            "issuers": [
                {"issuer_key_id": i, "account_hex": None if a is None else a.hex(), "verification_key_hex": k.hex()}
                for i, a, k in self.issuers
            ],
            "fresh": [{"account_hex": a.hex(), "generation": g} for a, g in self.fresh],
            "refuse_binding": None if self.refuse_binding is None
            else {"identity_hex": self.refuse_binding[0].hex(), "status": self.refuse_binding[1]},
            "refuse_every_binding": self.refuse_every_binding,
            "refuse_statement": self.refuse_statement,
        }


def accept(signed, account, policy):
    """The seven checks in order. Returns (refusal class or None, hook calls)."""
    log = []
    if len(signed) < 64:
        return "decode", log
    body, sig = signed[:-64], signed[-64:]
    try:
        st = decode(body)
    except (Refuse, struct.error):
        return "decode", log
    if st.account != account:
        return "account", log
    log.append("issuer:%d:%s" % (st.issuer, st.account.hex()))
    key = None
    for issuer, acct, k in policy.issuers:
        if issuer == st.issuer and (acct is None or acct == st.account):
            key = k
            break
    if key is None:
        return "issuer", log
    if not xeddsa_verify(key, SIGNING_LABEL + body, sig):
        return "signature", log
    log.append("freshness:%s:%d" % (st.account.hex(), st.generation))
    if (st.account, st.generation) not in policy.fresh:
        return "freshness", log
    ids = [b.device_id for b in st.active]
    if len(set(ids)) != len(ids):
        return "duplicate-device", log
    entries = [(b, "A") for b in st.active] + [(r.binding, "R") for r in st.revoked]
    if not all(is_identity_key(b.key) for b, _ in entries):
        return "identity-key", log
    for b, status in entries:
        log.append("binding:%s:%d:%s:%d:%s" % (
            status, b.device_id, b.key.hex(), b.capabilities,
            "-" if b.predecessor is None else b.predecessor.hex()))
        refused = policy.refuse_every_binding or (
            policy.refuse_binding is not None
            and policy.refuse_binding[0] == b.key
            and policy.refuse_binding[1] == {"A": "active", "R": "revoked"}[status])
        if refused:
            return "binding-policy", log
    log.append("statement")
    if policy.refuse_statement:
        return "statement-policy", log
    return None, log


# ---------------------------------------------------------------- the corpus
# The one case this file held before it grew; it must not change.
ONE_ACTIVE_BINDING_HEX = (
    "546163656e746120496e76656e746f72792053746174656d656e7420763100000000000000070000000a61636d652f61"
    "6c6963650000000000000002000000010000000101010101010101010101010101010101010101010101010101010101"
    "01010101000000000000000100000000000000000000000000"
)
ALICE = b"acme/alice"
BOB = b"acme/bob"
ALICE_SECRET = bytes([9]) * 32
BOB_SECRET = bytes([10]) * 32
ALICE_PUB = public_key(ALICE_SECRET)
BOB_PUB = public_key(BOB_SECRET)


def base_policy(**kw):
    return Policy(
        issuers=[(7, ALICE, ALICE_PUB), (8, BOB, BOB_PUB)],
        fresh=[(ALICE, 2), (BOB, 5)],
        **kw,
    )


def sign_body(body, secret=ALICE_SECRET, label=SIGNING_LABEL):
    return body + xeddsa_sign(secret, label + body)


def alice(active, generation=2, floor=0, revoked=(), issuer=7, account=ALICE):
    return Statement(issuer, account, generation, active, floor, revoked)


def dk(n):
    return device_key(n)


def b(device, n, **kw):
    return Binding(device, dk(n), **kw)


class Corpus:
    """Collects cases and checks each against the oracle as it is added."""

    def __init__(self):
        self.statements = []
        self.refusals = []
        self.commitments = []
        self.acceptance = []
        self.ids = set()

    def _new(self, case_id):
        assert case_id not in self.ids, case_id
        self.ids.add(case_id)

    def statement(self, case_id, st):
        self._new(case_id)
        st = st.sorted()
        assert decode(st.encode()).encode() == st.encode()
        self.statements.append(st.json(case_id))
        return st

    def refusal(self, case_id, rule, data):
        self._new(case_id)
        try:
            decode(data)
        except (Refuse, struct.error):
            pass
        else:
            raise AssertionError("decoder accepted refusal case " + case_id)
        self.refusals.append({"id": case_id, "rule": rule, "unsigned_hex": data.hex()})

    def commitment(self, case_id, binding):
        self._new(case_id)
        c = binding.commitment()
        self.commitments.append({
            "id": case_id,
            "binding": binding.json(),
            "commitment_hex": None if c is None else c.hex(),
        })
        return c

    def accepts(self, case_id, signed, expect, account=ALICE, policy=None):
        """Add an acceptance case; `expect` is the intended refusal class or None."""
        self._new(case_id)
        policy = policy or base_policy()
        got, log = accept(signed, account, policy)
        assert got == expect, "%s: intended %r, oracle says %r" % (case_id, expect, got)
        self.acceptance.append({
            "id": case_id,
            "signed_hex": signed.hex(),
            "expected_account_hex": account.hex(),
            "policy": policy.json(),
            "refusal": got,
            "hook_calls": log,
        })


def build():
    c = Corpus()

    # ---- inventory-statements-v1: encoding and decoding round trips ---------
    one = Statement(7, "acme/alice", 2, [Binding(1, bytes([1]) * 32)], 0, [])
    assert one.json("one-active-binding")["unsigned_hex"] == ONE_ACTIVE_BINDING_HEX
    c.statement("one-active-binding", one)
    c.statement("empty-statement", Statement(0, "a", 0, [], 0, []))
    c.statement("floor-equals-generation", Statement(9, "acme/alice", 5, [], 5, []))
    c.statement("maximum-integers", Statement(
        2**64 - 1, "acme/alice", 2**64 - 1,
        [Binding(2**32 - 1, bytes([0xAA]) * 32)], 2**64 - 2,
        [Revocation(Binding(0, bytes([0xBB]) * 32), 2**64 - 1)]))
    c.statement("two-active-ascending-device-id", Statement(
        7, "acme/alice", 2, [b(1, 0x21), b(2, 0x22)], 0, []))
    c.statement("same-device-id-ascending-key", Statement(
        7, "acme/alice", 2,
        [Binding(1, bytes([0x10]) * 32), Binding(1, bytes([0x20]) * 32)], 0, []))
    c.statement("key-ascending-across-first-byte", Statement(
        7, "acme/alice", 2,
        [Binding(1, bytes([0x01]) + bytes([0xFF]) * 31), Binding(1, bytes([0x02]) + bytes(31))], 0, []))
    pred = bytes([0x44]) * 32
    c.statement("no-predecessor-sorts-before-predecessor", Statement(
        7, "acme/alice", 2,
        [Binding(1, dk(0x23)), Binding(1, dk(0x23), predecessor=pred)], 0, []))
    c.statement("predecessors-ascending", Statement(
        7, "acme/alice", 2,
        [Binding(1, dk(0x23), predecessor=bytes([0x10]) * 32),
         Binding(1, dk(0x23), predecessor=bytes([0x20]) * 32)], 0, []))
    old = b(1, 0x24)
    c.statement("replacement-with-listed-tombstone", Statement(
        7, "acme/alice", 5, [b(1, 0x25, predecessor=old.commitment())], 2,
        [Revocation(old, 4)]))
    c.statement("replacement-under-new-device-id", Statement(
        7, "acme/alice", 5, [b(2, 0x25, predecessor=old.commitment())], 2,
        [Revocation(old, 4)]))
    c.statement("replacement-marker-outlives-compacted-tombstone", Statement(
        7, "acme/alice", 5, [b(1, 0x25, predecessor=old.commitment())], 2, []))
    c.statement("revoked-ascending-device-id", Statement(
        7, "acme/alice", 5, [], 1,
        [Revocation(b(1, 0x26), 3), Revocation(b(2, 0x27), 2)]))
    c.statement("same-binding-revoked-twice-ascending-terminal", Statement(
        7, "acme/alice", 5, [], 1,
        [Revocation(b(1, 0x26), 2), Revocation(b(1, 0x26), 3)]))
    c.statement("revoked-binding-order-before-terminal-order", Statement(
        7, "acme/alice", 5, [], 1,
        [Revocation(b(1, 0x26), 4), Revocation(b(2, 0x26), 2)]))
    c.statement("terminal-just-above-floor-and-at-generation", Statement(
        7, "acme/alice", 5, [], 2,
        [Revocation(b(1, 0x26), 3), Revocation(b(2, 0x26), 5)]))
    c.statement("eight-active", Statement(
        7, "acme/alice", 2, [b(i, 0x30 + i) for i in range(1, 9)], 0, []))
    c.statement("eight-revoked", Statement(
        7, "acme/alice", 5, [], 1, [Revocation(b(i, 0x40 + i), 2 + (i % 4)) for i in range(1, 9)]))
    c.statement("eight-active-and-eight-revoked", Statement(
        7, "acme/alice", 5, [b(i, 0x30 + i) for i in range(1, 9)], 1,
        [Revocation(b(i, 0x50 + i), 2 + (i % 4)) for i in range(1, 9)]))
    c.statement("account-256-ascii-bytes", Statement(7, "a" * 256, 2, [], 0, []))
    c.statement("account-256-bytes-multibyte", Statement(7, "é" * 128, 2, [], 0, []))
    c.statement("account-four-byte-scalar", Statement(7, "acme/\U0001f600", 2, [], 0, []))
    c.statement("account-nfc-form", Statement(7, "café", 2, [], 0, []))
    c.statement("account-nfd-form", Statement(7, "café", 2, [], 0, []))
    c.statement("account-with-nul-and-bom", Statement(7, "a\x00b﻿c", 2, [], 0, []))
    c.statement("account-maximum-scalar", Statement(7, "\U0010ffff", 2, [], 0, []))
    c.statement("identity-key-bytes-are-opaque-to-the-encoding", Statement(
        7, "acme/alice", 2, [Binding(1, bytes(32)), Binding(2, bytes([0xFF]) * 32)], 0,
        [Revocation(Binding(1, u_bytes(P)), 1)]))

    # ---- inventory-decode-refusals-v1 ------------------------------------------
    good = alice(
        [b(1, 0x21), b(2, 0x22, predecessor=pred)], generation=5, floor=1,
        revoked=[Revocation(b(3, 0x23), 2), Revocation(b(4, 0x24), 3)]).sorted()
    raw = good.encode()
    c.refusal("bad-domain-first-byte", "domain", bytes([raw[0] ^ 1]) + raw[1:])
    c.refusal("bad-domain-last-byte", "domain", raw[:len(DOMAIN) - 1] + bytes([raw[len(DOMAIN) - 1] ^ 1]) + raw[len(DOMAIN):])
    c.refusal("input-shorter-than-the-domain", "domain", raw[:len(DOMAIN) - 1])
    c.refusal("empty-input", "domain", b"")
    c.refusal("truncated-by-one-byte", "truncation", raw[:-1])
    c.refusal("truncated-in-the-middle-of-a-binding", "truncation", raw[:len(raw) - 100])
    c.refusal("one-trailing-byte", "trailing bytes", raw + b"\x00")
    c.refusal("signature-sized-trailing-bytes", "trailing bytes", raw + bytes(64))
    head = DOMAIN + struct.pack(">Q", 7)

    def with_account(account_bytes, declared=None):
        length = len(account_bytes) if declared is None else declared
        rest = struct.pack(">Q", 2) + struct.pack(">I", 0) + struct.pack(">Q", 0) + struct.pack(">I", 0)
        return head + struct.pack(">I", length) + account_bytes + rest

    c.refusal("account-empty", "account handle is non-empty", with_account(b""))
    c.refusal("account-257-ascii-bytes", "account handle is at most 256 bytes", with_account(b"a" * 257))
    c.refusal("account-257-bytes-multibyte", "account handle is at most 256 bytes",
              with_account(("é" * 128).encode() + b"a"))
    c.refusal("account-length-exceeds-input", "account handle is at most 256 bytes and within the input",
              with_account(b"abc", declared=200))
    c.refusal("account-length-maximum-u32", "account handle is at most 256 bytes", with_account(b"abc", declared=0xFFFFFFFF))
    c.refusal("account-overlong-utf8", "account handle is valid UTF-8", with_account(b"a\xc0\x80"))
    c.refusal("account-surrogate", "account handle is valid UTF-8", with_account(b"a\xed\xa0\x80"))
    c.refusal("account-above-10ffff", "account handle is valid UTF-8", with_account(b"a\xf4\x90\x80\x80"))
    c.refusal("account-lone-continuation-byte", "account handle is valid UTF-8", with_account(b"a\x80"))
    c.refusal("account-truncated-sequence", "account handle is valid UTF-8", with_account(b"a\xe2\x82"))
    c.refusal("account-invalid-lead-byte", "account handle is valid UTF-8", with_account(b"a\xff"))

    nine = alice([b(i, 0x30 + i) for i in range(1, 10)]).sorted()
    c.refusal("nine-active-bindings", "active_count is at most 8", nine.encode())
    c.refusal("active-count-declared-nine-over-eight-entries", "active_count is at most 8",
              alice([b(i, 0x30 + i) for i in range(1, 9)]).sorted().encode(count_active=9))
    c.refusal("active-count-maximum-u32", "active_count is at most 8", good.encode(count_active=0xFFFFFFFF))
    c.refusal("active-count-exceeds-entries", "the input holds every declared entry", good.encode(count_active=3))
    nine_rev = alice([], generation=5, floor=1, revoked=[Revocation(b(i, 0x40 + i), 2) for i in range(1, 10)]).sorted()
    c.refusal("nine-revoked-entries", "revoked_count is at most 8", nine_rev.encode())
    c.refusal("revoked-count-maximum-u32", "revoked_count is at most 8", good.encode(count_revoked=0xFFFFFFFF))
    c.refusal("revoked-count-exceeds-entries", "the input holds every declared entry", good.encode(count_revoked=3))

    def one_active(binding_bytes, revoked_bytes=b"", generation=5, floor=1, n_active=1, n_revoked=0):
        body = head + struct.pack(">I", 1) + b"a" + struct.pack(">Q", generation)
        body += struct.pack(">I", n_active) + binding_bytes
        body += struct.pack(">Q", floor) + struct.pack(">I", n_revoked) + revoked_bytes
        return body

    key = dk(0x21)
    plain = struct.pack(">I", 1) + key + struct.pack(">Q", 1)
    c.refusal("predecessor-tag-2", "predecessor tag is 0 or 1", one_active(plain + b"\x02" + bytes(32)))
    c.refusal("predecessor-tag-255", "predecessor tag is 0 or 1", one_active(plain + b"\xff"))
    c.refusal("predecessor-tag-1-with-31-bytes", "predecessor is 32 bytes when the tag is 1",
              one_active(plain + b"\x01" + bytes(31)))
    for name, caps in (("zero", 0), ("two", 2), ("three", 3), ("high-bit", 1 << 63), ("one-and-high-bit", 1 | (1 << 63))):
        entry = struct.pack(">I", 1) + key + struct.pack(">Q", caps) + b"\x00"
        c.refusal("active-capabilities-" + name, "capability word is exactly GROUP_EPOCH_V1", one_active(entry))
        rev = entry + struct.pack(">Q", 3)
        c.refusal("revoked-capabilities-" + name, "capability word is exactly GROUP_EPOCH_V1",
                  one_active(b"", rev, generation=5, floor=1, n_active=0, n_revoked=1))

    a1, a2 = b(1, 0x21), b(2, 0x22)
    tail = struct.pack(">Q", 0) + struct.pack(">I", 0)

    def actives(entries, generation=2):
        return (head + struct.pack(">I", 1) + b"a" + struct.pack(">Q", generation)
                + struct.pack(">I", len(entries)) + b"".join(e.encode() for e in entries) + tail)

    c.refusal("active-descending-device-id", "active is strictly ascending", actives([a2, a1]))
    c.refusal("active-duplicate-entry", "active is strictly ascending", actives([a1, a1]))
    k_lo, k_hi = Binding(1, bytes([0x10]) * 32), Binding(1, bytes([0x20]) * 32)
    c.refusal("active-same-device-descending-key", "active is strictly ascending", actives([k_hi, k_lo]))
    with_pred = Binding(1, dk(0x23), predecessor=pred)
    without = Binding(1, dk(0x23))
    c.refusal("active-predecessor-before-no-predecessor", "active is strictly ascending", actives([with_pred, without]))
    lo_pred = Binding(1, dk(0x23), predecessor=bytes([0x10]) * 32)
    hi_pred = Binding(1, dk(0x23), predecessor=bytes([0x20]) * 32)
    c.refusal("active-predecessors-descending", "active is strictly ascending", actives([hi_pred, lo_pred]))
    big_first = Binding(1, bytes([0x02]) + bytes(31))
    small_first = Binding(1, bytes([0x01]) + bytes([0xFF]) * 31)
    c.refusal("active-key-order-decided-at-first-byte", "active is strictly ascending", actives([big_first, small_first]))

    def revocations(entries, generation=5, floor=1, actives_=()):
        return (head + struct.pack(">I", 1) + b"a" + struct.pack(">Q", generation)
                + struct.pack(">I", len(actives_)) + b"".join(x.encode() for x in actives_)
                + struct.pack(">Q", floor) + struct.pack(">I", len(entries)) + b"".join(e.encode() for e in entries))

    r1, r2 = Revocation(b(1, 0x26), 2), Revocation(b(2, 0x27), 3)
    c.refusal("revoked-descending-device-id", "revoked is strictly ascending", revocations([r2, r1]))
    c.refusal("revoked-duplicate-entry", "revoked is strictly ascending", revocations([r1, r1]))
    c.refusal("revoked-same-binding-descending-terminal", "revoked is strictly ascending",
              revocations([Revocation(b(1, 0x26), 3), Revocation(b(1, 0x26), 2)]))
    c.refusal("revoked-binding-order-outranks-terminal-order", "revoked is strictly ascending",
              revocations([Revocation(b(2, 0x26), 2), Revocation(b(1, 0x26), 4)]))
    c.refusal("floor-above-generation", "the floor is at most the generation",
              alice([], generation=4, floor=5).encode())
    c.refusal("terminal-generation-equals-floor", "terminal generation is above the floor",
              revocations([Revocation(b(1, 0x26), 1)]))
    c.refusal("terminal-generation-zero-with-floor-zero", "terminal generation is above the floor",
              revocations([Revocation(b(1, 0x26), 0)], generation=5, floor=0))
    c.refusal("terminal-generation-above-generation", "terminal generation is at most the generation",
              revocations([Revocation(b(1, 0x26), 6)]))
    c.refusal("binding-in-both-lists", "an exact binding is not in both lists",
              revocations([Revocation(a1, 3)], actives_=[a1]))

    # ---- inventory-binding-commitments-v1 --------------------------------------
    known = Binding(7, bytes([3]) * 32, GROUP_EPOCH_V1, bytes([4]) * 32)
    c.commitment("predecessor-present", known)
    c.commitment("no-predecessor", Binding(7, bytes([3]) * 32))
    c.commitment("device-id-differs", Binding(8, bytes([3]) * 32, GROUP_EPOCH_V1, bytes([4]) * 32))
    c.commitment("key-differs", Binding(7, bytes([5]) * 32, GROUP_EPOCH_V1, bytes([4]) * 32))
    c.commitment("predecessor-differs", Binding(7, bytes([3]) * 32, GROUP_EPOCH_V1, bytes([6]) * 32))
    c.commitment("key-need-not-be-an-identity-key", Binding(7, bytes(32)))
    for name, caps in (("zero", 0), ("two", 2), ("three", 3), ("high-bit", 1 << 63)):
        c.commitment("capabilities-" + name + "-has-no-commitment", Binding(7, bytes([3]) * 32, caps))

    # ---- inventory-acceptance-v1 ---------------------------------------------
    def signed(st, secret=ALICE_SECRET):
        return sign_body(st.sorted().encode(), secret)

    a, b2 = b(1, 0x21), b(2, 0x22)
    plain_st = alice([a, b2])
    c.accepts("accepted-two-active", signed(plain_st), None)
    c.accepts("accepted-empty-inventory", signed(alice([])), None)
    c.accepts("accepted-second-account", signed(Statement(8, BOB, 5, [b(3, 0x23)]), BOB_SECRET), None, account=BOB)
    c.accepts("accepted-eight-active-and-eight-revoked", signed(alice(
        [b(i, 0x30 + i) for i in range(1, 9)], generation=2, floor=0,
        revoked=[Revocation(b(i, 0x50 + i), 1 + (i % 2)) for i in range(1, 9)])), None)
    old = b(1, 0x24)
    c.accepts("accepted-replacement-under-the-old-device-id", signed(alice(
        [b(1, 0x25, predecessor=old.commitment())], generation=2, floor=0, revoked=[Revocation(old, 1)])), None)
    c.accepts("accepted-replacement-under-a-new-device-id", signed(alice(
        [b(2, 0x25, predecessor=old.commitment())], generation=2, floor=0, revoked=[Revocation(old, 1)])), None)
    policy5 = Policy([(7, ALICE, ALICE_PUB)], [(ALICE, 5)])
    c.accepts("accepted-marker-outlives-a-compacted-tombstone", signed(alice(
        [b(1, 0x25, predecessor=old.commitment())], generation=5, floor=2)), None, policy=policy5)
    c.accepts("accepted-marker-naming-nothing-listed", signed(alice(
        [b(1, 0x25, predecessor=bytes([0x99]) * 32)])), None)
    c.accepts("accepted-marker-equal-to-a-still-active-commitment", signed(alice(
        [a, b(2, 0x22, predecessor=a.commitment())])), None)
    retired = Binding(1, dk(0x25), predecessor=bytes([0x77]) * 32)
    c.accepts("accepted-replacement-with-the-retired-bindings-own-device-id-and-key", signed(alice(
        [Binding(1, dk(0x25), predecessor=retired.commitment())], generation=2, floor=0,
        revoked=[Revocation(retired, 1)])), None)
    unnormalised = alice([a, b2]).sorted().encode()
    assert xeddsa_sign_leaving_the_sign_bit(ALICE_SECRET, SIGNING_LABEL + unnormalised)[63] >> 7 == 1
    c.accepts("accepted-signature-with-the-sign-bit-left-set",
              unnormalised + xeddsa_sign_leaving_the_sign_bit(ALICE_SECRET, SIGNING_LABEL + unnormalised), None)
    c.accepts("accepted-one-key-on-two-devices", signed(alice(
        [Binding(1, dk(0x21)), Binding(2, dk(0x21))])), None)
    c.accepts("accepted-revoked-key-listed-again-as-active", signed(alice(
        [Binding(2, dk(0x21))], generation=2, floor=0, revoked=[Revocation(Binding(1, dk(0x21)), 1)])), None)
    c.accepts("accepted-same-device-id-active-and-revoked", signed(alice(
        [Binding(1, dk(0x22))], generation=2, floor=0, revoked=[Revocation(Binding(1, dk(0x21)), 1)])), None)
    c.accepts("accepted-same-binding-revoked-twice", signed(alice(
        [], generation=3, floor=0, revoked=[Revocation(a, 1), Revocation(a, 2)])), None,
        policy=Policy([(7, ALICE, ALICE_PUB)], [(ALICE, 3)]))
    c.accepts("accepted-multibyte-account-256-bytes", signed(Statement(
        9, ("é" * 128), 2, [a]), ALICE_SECRET), None, account=("é" * 128).encode(),
        policy=Policy([(9, None, ALICE_PUB)], [(("é" * 128).encode(), 2)]))
    nfc, nfd = "café".encode(), "café".encode()
    shared = Policy([(9, None, ALICE_PUB)], [(nfc, 2), (nfd, 2)])
    c.accepts("accepted-account-compared-as-bytes-nfc", signed(Statement(9, nfc, 2, [a])), None, account=nfc, policy=shared)
    c.accepts("refused-account-nfd-asked-for-nfc-statement", signed(Statement(9, nfc, 2, [a])), "account", account=nfd, policy=shared)

    # decode refusals reached through the acceptance path: signed, still refused
    unsorted = alice([b2, a]).encode()
    c.accepts("refused-decode-signed-unsorted-active", sign_body(unsorted), "decode")
    c.accepts("refused-decode-signed-capabilities-two", sign_body(alice(
        [Binding(1, dk(0x21), 2)]).encode()), "decode")
    c.accepts("refused-decode-signed-empty-account", sign_body(Statement(7, b"", 2, []).encode()), "decode")
    c.accepts("refused-decode-signed-tag-2", sign_body(one_active(
        struct.pack(">I", 1) + dk(0x21) + struct.pack(">Q", 1) + b"\x02" + bytes(32), generation=2, floor=0)), "decode")
    c.accepts("refused-decode-fewer-than-64-bytes", bytes(63), "decode")
    c.accepts("refused-decode-exactly-64-bytes", bytes(64), "decode")
    c.accepts("refused-decode-empty-input", b"", "decode")
    good_signed = signed(plain_st)
    c.accepts("refused-decode-truncated-before-the-signature", good_signed[:40], "decode")
    c.accepts("refused-decode-body-altered-domain", bytes([good_signed[0] ^ 1]) + good_signed[1:], "decode")
    c.accepts("refused-decode-two-signatures", good_signed + good_signed[-64:], "decode")

    # check 1: account
    for name, asked in (
        ("another-account", BOB), ("prefix-of-the-account", b"acme/"), ("suffix-of-the-account", b"/alice"),
        ("account-with-last-byte-dropped", b"acme/alic"), ("account-with-trailing-space", b"acme/alice "),
        ("empty-account", b""), ("account-with-a-longer-tail", b"acme/alice/x"), ("account-in-another-case", b"ACME/ALICE"),
    ):
        c.accepts("refused-account-asked-for-" + name, good_signed, "account", account=asked)
    one_key_for_tenant = Policy([(9, None, ALICE_PUB)], [(BOB, 5), (ALICE, 2)])
    bob_under_shared = sign_body(Statement(9, BOB, 5, [a]).encode())
    c.accepts("accepted-shared-issuer-key-for-its-own-account", bob_under_shared, None, account=BOB, policy=one_key_for_tenant)
    c.accepts("refused-account-under-a-shared-issuer-key", bob_under_shared, "account", account=ALICE, policy=one_key_for_tenant)

    # check 2: issuer
    c.accepts("refused-issuer-id-unknown", signed(alice([a], issuer=99)), "issuer")
    c.accepts("refused-issuer-bound-to-another-account", signed(alice([a], issuer=8)), "issuer")
    c.accepts("refused-issuer-id-zero-unbound", signed(alice([a], issuer=0)), "issuer")

    # check 3: signature
    sig_ok = good_signed[-64:]
    body_ok = good_signed[:-64]

    def flip(data, index, mask=1):
        out = bytearray(data)
        out[index] ^= mask
        return bytes(out)

    c.accepts("refused-signature-first-bit-flipped", body_ok + flip(sig_ok, 0), "signature")
    c.accepts("refused-signature-s-bit-flipped", body_ok + flip(sig_ok, 40), "signature")
    c.accepts("refused-signature-sign-bit-flipped", body_ok + flip(sig_ok, 63, 0x80), "signature")
    s_int = int.from_bytes(sig_ok[32:], "little")
    c.accepts("refused-signature-s-plus-q", body_ok + sig_ok[:32] + (s_int + Q).to_bytes(32, "little"), "signature")
    c.accepts("refused-signature-r-all-zero", body_ok + bytes(32) + sig_ok[32:], "signature")
    c.accepts("refused-signature-all-zero", body_ok + bytes(64), "signature")
    c.accepts("refused-signature-by-another-key", signed(plain_st, BOB_SECRET), "signature")
    c.accepts("refused-signature-body-changed-after-signing",
              alice([a, b2], generation=3).sorted().encode() + sig_ok, "signature")
    c.accepts("refused-signature-without-the-label", body_ok + xeddsa_sign(ALICE_SECRET, body_ok), "signature")
    c.accepts("refused-signature-with-the-application-label",
              body_ok + xeddsa_sign(ALICE_SECRET, APPLICATION_LABEL + body_ok), "signature")
    c.accepts("refused-signature-label-without-its-terminator",
              body_ok + xeddsa_sign(ALICE_SECRET, SIGNING_LABEL[:-1] + body_ok), "signature")
    c.accepts("refused-signature-over-the-label-twice",
              body_ok + xeddsa_sign(ALICE_SECRET, SIGNING_LABEL + SIGNING_LABEL + body_ok), "signature")
    for name, key in (("zero", u_bytes(0)), ("p-minus-one", u_bytes(P - 1)), ("not-canonical", u_bytes(P))):
        c.accepts("refused-signature-issuer-key-" + name, good_signed, "signature",
                  policy=Policy([(7, ALICE, key), (8, BOB, BOB_PUB)], [(ALICE, 2), (BOB, 5)]))

    # check 4: freshness
    c.accepts("refused-freshness-generation-ahead", signed(alice([a], generation=3)), "freshness")
    c.accepts("refused-freshness-generation-behind", signed(alice([a], generation=1)), "freshness")
    c.accepts("refused-freshness-no-generation-for-the-account", good_signed, "freshness",
              policy=Policy([(7, ALICE, ALICE_PUB)], [(BOB, 2)]))

    # check 5: duplicate device
    c.accepts("refused-duplicate-device-id", signed(alice([Binding(1, dk(0x21)), Binding(1, dk(0x22))])), "duplicate-device")
    c.accepts("refused-duplicate-device-id-outranks-a-bad-key", signed(alice(
        [Binding(1, u_bytes(0)), Binding(1, dk(0x22))])), "duplicate-device")

    # check 6: identity keys, in active and in revoked
    def with_key(key, where):
        if where == "active":
            return signed(alice([Binding(1, key)]))
        return signed(alice([b(2, 0x22)], generation=2, floor=0, revoked=[Revocation(Binding(1, key), 1)]))

    for name, key in (
        ("zero", LOW_ORDER[0]), ("one", LOW_ORDER[1]), ("p-minus-one", LOW_ORDER[2]),
        ("order-eight-first", LOW_ORDER[3]), ("order-eight-second", LOW_ORDER[4]),
    ):
        for where in ("active", "revoked"):
            c.accepts("refused-key-low-order-%s-%s" % (name, where), with_key(key, where), "identity-key")
    honest = dk(0x31)
    noncanonical = {
        "p": u_bytes(P), "p-plus-one": u_bytes(P + 1), "p-plus-nine": u_bytes(P + 9),
        "all-ones": bytes([0xFF]) * 32,
        "nine-with-bit-255": bytes([9]) + bytes(30) + bytes([0x80]),
        "zero-with-bit-255": bytes(31) + bytes([0x80]),
        "honest-key-with-bit-255": honest[:31] + bytes([honest[31] | 0x80]),
        "honest-key-plus-p": (int.from_bytes(honest, "little") + P).to_bytes(32, "little"),
    }
    for name, key in noncanonical.items():
        assert not canonical(key), name
        for where in ("active", "revoked"):
            c.accepts("refused-key-non-canonical-%s-%s" % (name, where), with_key(key, where), "identity-key")
    for n in (2, 3, 5, 6):
        u = u_bytes(n)
        if lift(n) is None:
            for where in ("active", "revoked"):
                c.accepts("refused-key-off-curve-u-%d-%s" % (n, where), with_key(u, where), "identity-key")
    sp = spellings(honest)
    assert sp[0] == honest and len(set(sp)) == 8
    c.accepts("accepted-key-honest-spelling", with_key(sp[0], "active"), None)
    for j in range(1, 8):
        for where in ("active", "revoked"):
            c.accepts("refused-key-mixed-torsion-%d-%s" % (j, where), with_key(sp[j], where), "identity-key")
    other = spellings(dk(0x32))
    c.accepts("refused-key-mixed-torsion-of-a-second-key", with_key(other[3], "active"), "identity-key")
    c.accepts("refused-key-unsound-revoked-key-with-a-sound-active-key", signed(alice(
        [b(2, 0x22)], generation=2, floor=0, revoked=[Revocation(Binding(1, sp[5]), 1)])), "identity-key")
    c.accepts("refused-key-check-6-covers-every-entry", signed(alice(
        [b(1, 0x21), b(2, 0x22), b(3, 0x23), Binding(4, sp[1])])), "identity-key")

    # check 7: policy, and the order in which its hooks run
    deny_active = Policy([(7, ALICE, ALICE_PUB), (8, BOB, BOB_PUB)], [(ALICE, 2), (BOB, 5)],
                         refuse_binding=(dk(0x22), "active"))
    deny_revoked = Policy([(7, ALICE, ALICE_PUB), (8, BOB, BOB_PUB)], [(ALICE, 2), (BOB, 5)],
                          refuse_binding=(dk(0x22), "revoked"))
    with_revoked_key = signed(alice([a], generation=2, floor=0, revoked=[Revocation(b2, 1)]))
    c.accepts("refused-binding-policy-active-entry", signed(plain_st), "binding-policy", policy=deny_active)
    c.accepts("refused-binding-policy-revoked-entry", with_revoked_key, "binding-policy", policy=deny_revoked)
    c.accepts("accepted-binding-policy-status-differs-active", with_revoked_key, None, policy=deny_active)
    c.accepts("accepted-binding-policy-status-differs-revoked", signed(plain_st), None, policy=deny_revoked)
    every = base_policy(refuse_every_binding=True)
    c.accepts("refused-binding-policy-stops-at-the-first-binding", signed(plain_st), "binding-policy", policy=every)
    c.accepts("refused-binding-policy-runs-active-before-revoked", with_revoked_key, "binding-policy", policy=every)
    c.accepts("refused-binding-policy-runs-in-encoded-order", signed(alice([b(1, 0x21), b(2, 0x22), b(3, 0x23)])), "binding-policy",
              policy=Policy([(7, ALICE, ALICE_PUB)], [(ALICE, 2)], refuse_binding=(dk(0x23), "active")))
    c.accepts("refused-statement-policy", signed(plain_st), "statement-policy", policy=base_policy(refuse_statement=True))
    c.accepts("refused-binding-policy-suppresses-the-statement-policy", signed(plain_st), "binding-policy",
              policy=Policy([(7, ALICE, ALICE_PUB)], [(ALICE, 2)], refuse_binding=(dk(0x21), "active"), refuse_statement=True))
    c.accepts("refused-key-check-runs-before-any-binding-policy", signed(alice(
        [b(1, 0x21), Binding(2, u_bytes(0))])), "identity-key",
        policy=Policy([(7, ALICE, ALICE_PUB)], [(ALICE, 2)], refuse_binding=(dk(0x21), "active")))
    c.accepts("refused-key-in-revoked-runs-before-any-binding-policy", signed(alice(
        [b(1, 0x21)], generation=2, floor=0, revoked=[Revocation(Binding(2, u_bytes(0)), 1)])), "identity-key",
        policy=Policy([(7, ALICE, ALICE_PUB)], [(ALICE, 2)], refuse_binding=(dk(0x21), "active")))

    # the first failing check wins, over subsets of failing checks
    def failing(mask):
        active_ = [b(1, 0x21)]
        if mask & 16:
            active_ = [Binding(1, dk(0x21)), Binding(1, dk(0x22))]
        if mask & 64:
            active_.append(b(4, 0x23))
        if mask & 32:
            active_.append(Binding(5, u_bytes(0)))
        st = alice(active_, generation=3 if mask & 8 else 2, issuer=99 if mask & 2 else 7)
        wire = signed(st, BOB_SECRET if mask & 4 else ALICE_SECRET)
        pol = Policy([(7, ALICE, ALICE_PUB)], [(ALICE, 2)],
                     refuse_binding=(dk(0x23), "active") if mask & 64 else None,
                     refuse_statement=bool(mask & 128))
        return wire, pol

    order = ["account", "issuer", "signature", "freshness", "duplicate-device", "identity-key",
             "binding-policy", "statement-policy"]
    for mask in (0, 1, 2, 4, 8, 16, 32, 64, 128, 3, 6, 10, 12, 20, 24, 40, 48, 96, 192, 160, 255, 254, 252, 248, 240, 224):
        wire, pol = failing(mask)
        expect = next((order[i] for i in range(8) if mask & (1 << i)), None)
        c.accepts("first-failing-check-wins-mask-%03d" % mask, wire, expect,
                  account=BOB if mask & 1 else ALICE, policy=pol)
    return c


# -------------------------------------------------------------------- output
def render_case(case):
    """One case, each field on its own line; nested values stay on one line."""
    fields = [
        "      %s: %s" % (json.dumps(key), json.dumps(value, separators=(", ", ": ")))
        for key, value in case.items()
    ]
    return "    {\n" + ",\n".join(fields) + "\n    }"


def render(schema, comment, cases):
    lines = ["{", '  "schema": %s,' % json.dumps(schema), '  "comment": %s,' % json.dumps(comment), '  "cases": [']
    lines.append(",\n".join(render_case(case) for case in cases))
    lines += ["  ]", "}", ""]
    return "\n".join(lines)


FILES = {
    "inventory-statements-v1.json": (
        "tacenta-inventory-statements-v1",
        "Canonical unsigned preimages of hosted device-inventory statements, each given as fields and as the "
        "bytes they encode to. A decoder returns the same fields from the bytes. Provenance: "
        "written by tacenta-test-vectors/generate-inventory-vectors.py. "
        "Signatures are not in this file (inventory-acceptance-v1.json has them). Identity keys are opaque here.",
        "statements",
    ),
    "inventory-decode-refusals-v1.json": (
        "tacenta-inventory-decode-refusals-v1",
        "Unsigned preimages the decoder refuses, each with one defect against the encoding rules of "
        "identities-and-devices.md, Hosted device-inventory statements; `rule` names the rule broken. Provenance: "
        "tacenta-test-vectors/generate-inventory-vectors.py.",
        "refusals",
    ),
    "inventory-binding-commitments-v1.json": (
        "tacenta-inventory-binding-commitments-v1",
        "binding_commitment of a device binding, or null where the binding has no encoding and so no commitment. "
        "Provenance: tacenta-test-vectors/generate-inventory-vectors.py.",
        "commitments",
    ),
    "inventory-acceptance-v1.json": (
        "tacenta-inventory-acceptance-v1",
        "Signed statements run through the seven checks of identities-and-devices.md, Accepting a signed "
        "statement, against a scripted policy. `refusal` is null when the statement is accepted, else the check "
        "that refused it; `hook_calls` is every call the policy received, in order. Signers: 32 bytes of 0x09 "
        "for acme/alice and 0x0a for acme/bob, Z = 64 zero bytes. Provenance: "
        "tacenta-test-vectors/generate-inventory-vectors.py.",
        "acceptance",
    ),
}


def main():
    check = "--check" in sys.argv[1:]
    corpus = build()
    bad = 0
    for name, (schema, comment, attr) in FILES.items():
        text = render(schema, comment, getattr(corpus, attr))
        path = OUT / name
        if check:
            if not path.exists() or path.read_text() != text:
                print("DIFFERS  " + name)
                bad += 1
            else:
                print("current  %s (%d cases)" % (name, len(getattr(corpus, attr))))
        else:
            path.write_text(text)
            print("wrote    %s (%d cases)" % (name, len(getattr(corpus, attr))))
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
