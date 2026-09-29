"""Pass 12. identities-and-devices.md, "Hosted device-inventory statements" and
"Accepting a signed statement": the sentences the four `vectors/groups/
inventory-*.json` files do not pin, and the ones they pin only by example.

- The preimage, both sort orders, exact bindings, the generation ranges and
  the UTF-8 handle (IV-01 to IV-04, IV-22).
- A statement built in memory, and the three refusal kinds (IV-05, IV-06).
- The issuer's duty (IV-07), which no vector can reach.
- Check 4's rule having no effect of its own, and the compare-and-advance
  (IV-08, IV-09), which no vector can reach.
- Check 6, from its definition as well as its test (IV-10 to IV-15).
- Checks 5, 7, 1 and 2, and the signature input and verifier (IV-16 to IV-19).
- `binding_commitment` and the unchecked properties (IV-20, IV-21).

Every signature here is made by this reader's own XEdDSA; nothing is taken
from a vector's bytes.
"""

import hashlib
import itertools
import random

from _casekit import accepts, registry, rejects
from tacenta_reader import inventory as INV
from tacenta_reader.curve25519 import (BASE, P, Q, _add, _decode_scalar25519, _inv, _is_identity, _mul,
                                       _recover_x, _sha512_int, compress, x25519, x25519_public, xeddsa_sign)

CASES, case = registry()
ID = "identities-and-devices.md"
HD = f"{ID} Hosted device-inventory statements"
AC = f"{ID} Accepting a signed statement"
R = random.Random(20260929_12)
DB, RV, ST = INV.DeviceBinding, INV.Revocation, INV.Statement
ISSUER = b"\x21" * 32
ISSUER_PUB = x25519_public(ISSUER)
ALICE = b"acme/alice"


def rnd(n):
    return bytes(R.randrange(256) for _ in range(n))


def honest_key():
    return x25519_public(rnd(32))


def stmt(active=(), revoked=(), gen=5, floor=1, kid=7, account=ALICE):
    return ST(kid, account, gen, tuple(active), floor, tuple(revoked))


def sign(s, secret=ISSUER):
    return INV.sign_statement(secret, s, rnd(64))


def force_sign(s, secret=ISSUER):
    """Past the issuer's duty: sign whatever encodes (or, for a statement that
    does not, the bytes given)."""
    unsigned = s if isinstance(s, bytes) else INV.encode_unsigned(s)
    return unsigned + xeddsa_sign(secret, INV.signing_input(unsigned), rnd(64))


class Rec(INV.Policy):
    """A recording policy; every part accepts unless told otherwise."""

    def __init__(self, key=ISSUER_PUB, account=ALICE, kid=7, fresh=None, binding=None, statement=None):
        self.key, self.account, self.kid = key, account, kid
        self._fresh, self._binding, self._statement = fresh, binding, statement
        self.calls, self.bindings, self.statements, self.recorded = [], [], [], []

    def issuer_key(self, issuer_key_id, account_handle):
        self.calls.append(("issuer", issuer_key_id, account_handle))
        return self.key if (issuer_key_id, account_handle) == (self.kid, self.account) else None

    def fresh(self, account_handle, generation):
        self.calls.append(("freshness", account_handle, generation))
        return True if self._fresh is None else self._fresh(account_handle, generation)

    def accept_binding(self, binding, status):
        self.calls.append(("binding", status, binding))
        self.bindings.append((status, binding))
        return True if self._binding is None else self._binding(binding, status)

    def accept_statement(self, statement):
        self.calls.append(("statement",))
        self.statements.append(statement)
        return True if self._statement is None else self._statement(statement)

    def accepted(self, statement):
        self.recorded.append(statement)


def refused(signed, check, policy=None, asked=ALICE):
    policy = policy or Rec()
    e = rejects(INV.accept, signed, asked, policy, exc=INV.InventoryRefusal)
    assert e.check == check, f"refused by {e.check}, expected {check}: {e}"
    return policy


def random_binding(pred=None, device=None):
    if pred is None:
        pred = rnd(32) if R.random() < 0.4 else None
    return DB(R.randrange(4) if device is None else device, honest_key(), 1, pred)


def canonical(bindings):
    return sorted(set(bindings), key=INV.encode_binding)


def random_statement():
    active = canonical([random_binding() for _ in range(R.randrange(0, 5))])
    floor = R.randrange(0, 3)
    gen = floor + R.randrange(1, 4)
    revoked = []
    for _ in range(R.randrange(0, 4)):
        b = random_binding()
        if INV.encode_binding(b) not in {INV.encode_binding(a) for a in active}:
            revoked.append(RV(b, R.randrange(floor + 1, gen + 1)))
    revoked = sorted(set(revoked), key=INV.encode_revocation)
    return ST(R.randrange(2 ** 64), rnd(R.randrange(1, 12)).hex().encode(), gen, tuple(active), floor, tuple(revoked))


# ================================================================ the encoding

@case("IV-01 the unsigned preimage: INVENTORY_DOMAIN (30 ASCII bytes, no terminator), then issuer_key_id u64, account_handle_length u32, the handle, inventory_generation u64, active_count u32, the bindings, revocation_floor_generation u64, revoked_count u32, the revocations, every integer big-endian; a binding is device_id u32, the 32-byte key, capabilities u64, the tag byte and, only for tag 1, the 32-byte predecessor; decoding what was encoded returns it, over random statements",
      f"{HD}: The unsigned preimage is the following concatenation, all integer fields in big-endian order ...; `DeviceBinding` is ...; `Revocation` appends `terminal_generation` (u64) to a `DeviceBinding`")
def _():
    assert INV.INVENTORY_DOMAIN == b"Tacenta Inventory Statement v1" and len(INV.INVENTORY_DOMAIN) == 30
    b0 = DB(0x01020304, bytes(range(32)), 1)
    b1 = DB(0x0a0b0c0d, bytes(range(32, 64)), 1, bytes(range(64, 96)))
    s = ST(0x1112131415161718, b"acct", 9, (b0, b1), 3, (RV(DB(5, b"\x77" * 32, 1), 7),))
    raw = INV.encode_unsigned(s)
    enc0 = bytes.fromhex("01020304") + bytes(range(32)) + (1).to_bytes(8, "big") + b"\x00"
    enc1 = bytes.fromhex("0a0b0c0d") + bytes(range(32, 64)) + (1).to_bytes(8, "big") + b"\x01" + bytes(range(64, 96))
    want = (INV.INVENTORY_DOMAIN + bytes.fromhex("1112131415161718") + (4).to_bytes(4, "big") + b"acct"
            + (9).to_bytes(8, "big") + (2).to_bytes(4, "big") + enc0 + enc1 + (3).to_bytes(8, "big")
            + (1).to_bytes(4, "big") + (5).to_bytes(4, "big") + b"\x77" * 32 + (1).to_bytes(8, "big") + b"\x00"
            + (7).to_bytes(8, "big"))
    assert raw == want
    assert len(enc0) == 45 and len(enc1) == 77
    for _ in range(150):
        s = random_statement()
        assert INV.decode_unsigned(INV.encode_unsigned(s)) == s


@case("IV-02 both lists are in strictly ascending order of their encodings as unsigned byte strings, which is ascending device_id, then key, then capabilities, then no predecessor before a predecessor, then ascending predecessor, and for revoked then ascending terminal_generation; no binding encoding is a prefix of another; of every ordering of a set of entries the decoder accepts exactly the ascending one",
      f"{HD}: Both lists are sorted in strictly ascending order of their encodings, compared as unsigned byte strings from the first byte ... No `DeviceBinding` encoding is a prefix of another, so the comparison always ends on a differing byte")
def _():
    for _ in range(40):
        bs = [random_binding(device=R.randrange(3)) for _ in range(6)]
        bs += [DB(bs[0].device_id, bs[0].identity_public_key, 1, None),
               DB(bs[0].device_id, bs[0].identity_public_key, 1, rnd(32))]
        by_bytes = sorted(set(bs), key=INV.encode_binding)
        by_fields = sorted(set(bs), key=lambda b: (b.device_id, b.identity_public_key, b.capabilities,
                                                   b.replacement_predecessor is not None,
                                                   b.replacement_predecessor or b""))
        assert by_bytes == by_fields
        for x, y in itertools.permutations(set(bs), 2):
            ex, ey = INV.encode_binding(x), INV.encode_binding(y)
            assert not ey.startswith(ex), "one binding encoding is a prefix of another"
        revs = [RV(b, t) for b in by_bytes[:3] for t in (2, 4)]
        assert sorted(revs, key=INV.encode_revocation) == sorted(
            revs, key=lambda r: (INV.encode_binding(r.binding), r.terminal_generation))
    trio = canonical([random_binding(device=d) for d in (1, 2, 3)])
    for order in itertools.permutations(trio):
        s = stmt(active=order, revoked=())
        if list(order) == trio:
            accepts(INV.encode_unsigned, s)
        else:
            rejects(INV.encode_unsigned, s, exc=INV.DecodeFailure)
    revs = [RV(DB(1, trio[0].identity_public_key, 1), t) for t in (2, 3, 4)]
    for order in itertools.permutations(revs):
        s = stmt(revoked=order)
        (accepts if list(order) == revs else lambda f, a: rejects(f, a, exc=INV.DecodeFailure))(INV.encode_unsigned, s)
    # The integers are compared as their big-endian bytes, so the order holds
    # across a byte boundary, where a little-endian comparison would reverse it
    # (added in pass 12 after fault F12-07 was missed; no vector puts two
    # entries of one list on either side of a byte boundary).
    k = honest_key()
    for lo, hi in ((255, 256), (1, 256), (0xFF, 0x10000), (0x01000000, 0x01000001), (0x00FFFFFF, 0x01000000)):
        a, b = DB(lo, k, 1), DB(hi, k, 1)
        accepts(INV.encode_unsigned, stmt(active=[a, b]))
        rejects(INV.encode_unsigned, stmt(active=[b, a]), exc=INV.DecodeFailure)
        raw = INV.encode_unsigned(stmt(active=[a, b]))
        accepts(INV.decode_unsigned, raw)
    for lo, hi in ((255, 256), (2, 0x100000000)):
        r1, r2 = RV(DB(1, k, 1), lo), RV(DB(1, k, 1), hi)
        accepts(INV.encode_unsigned, stmt(revoked=[r1, r2], gen=hi, floor=1))
        rejects(INV.encode_unsigned, stmt(revoked=[r2, r1], gen=hi, floor=1), exc=INV.DecodeFailure)


@case("IV-03 an exact binding is all four fields, predecessor tag and value included, which is its encoding; it may not be both active and revoked, whatever the revocation's terminal generation; bindings that differ only in the predecessor are different bindings and may be one active and one revoked",
      f"{HD}: Two bindings are the same exact binding when all four of their fields are equal ... that is, when their encodings are equal. A `terminal_generation` belongs to a `Revocation`, not to its binding; ... an exact binding cannot occur in both `active` and `revoked`")
def _():
    key = honest_key()
    plain, marked, other = DB(1, key, 1), DB(1, key, 1, b"\x44" * 32), DB(1, key, 1, b"\x45" * 32)
    for t in (2, 3, 5):
        rejects(INV.encode_unsigned, stmt(active=[plain], revoked=[RV(plain, t)]), exc=INV.DecodeFailure)
        rejects(INV.encode_unsigned, stmt(active=[marked], revoked=[RV(marked, t)]), exc=INV.DecodeFailure)
    accepts(INV.encode_unsigned, stmt(active=[marked], revoked=[RV(plain, 3)]))
    accepts(INV.encode_unsigned, stmt(active=[plain], revoked=[RV(marked, 3)]))
    accepts(INV.encode_unsigned, stmt(active=[marked], revoked=[RV(other, 3)]))


@case("IV-04 generation ranges: the floor is no greater than inventory_generation, and each terminal generation is above the floor and no greater than inventory_generation, both ends checked; a binding leaves revoked once the floor reaches its terminal generation; the same binding revoked twice with different terminal generations is accepted, with the same one it repeats and is refused",
      f"{HD}: The floor is no greater than `inventory_generation`; Each terminal generation is greater than `revocation_floor_generation` and no greater than `inventory_generation`; The same binding can occur in `revoked` more than once with different terminal generations ... the format does not refuse that")
def _():
    b = DB(3, honest_key(), 1)
    accepts(INV.encode_unsigned, stmt(gen=4, floor=4))
    rejects(INV.encode_unsigned, stmt(gen=4, floor=5), exc=INV.DecodeFailure)
    for floor, gen in ((0, 5), (2, 5), (4, 5), (0, 1)):
        for t in range(0, gen + 2):
            s = stmt(revoked=[RV(b, t)], gen=gen, floor=floor)
            if floor < t <= gen:
                accepts(INV.encode_unsigned, s)
            else:
                rejects(INV.encode_unsigned, s, exc=INV.DecodeFailure)
    accepts(INV.encode_unsigned, stmt(revoked=[RV(b, 2), RV(b, 3)], gen=5, floor=1))
    rejects(INV.encode_unsigned, stmt(revoked=[RV(b, 3), RV(b, 3)], gen=5, floor=1), exc=INV.DecodeFailure)
    # the floor reaching a terminal generation: the entry must go
    rejects(INV.encode_unsigned, stmt(revoked=[RV(b, 3)], gen=5, floor=3), exc=INV.DecodeFailure)
    accepts(INV.encode_unsigned, stmt(revoked=[], gen=5, floor=3))


@case("IV-22 the account handle is non-empty, at most 256 bytes, and valid UTF-8: noncharacters, NUL, a byte-order mark and U+10FFFF are valid; surrogates, overlong forms, values above U+10FFFF, stray continuation bytes and cut sequences are not; the bound is in bytes, and two normalisation forms of one name are two handles",
      f"{HD}: The account handle is non-empty and at most `MAX_ACCOUNT_BYTES` (256) bytes; invalid UTF-8 is refused; {AC}, check 1: `account_handle` equals, byte for byte, the account the verifier asked about")
def _():
    for good in ("a", "￾￿", "a\x00b", "﻿x", "\U0010ffff", "é" * 128, "a" * 256):
        accepts(INV.encode_unsigned, stmt(account=good.encode("utf-8")))
    for bad in (b"", b"a" * 257, "é".encode() * 128 + b"a", b"\xed\xa0\x80", b"\xc0\x80", b"\xe0\x80\x80",
                b"\xf4\x90\x80\x80", b"\x80", b"a\xc3", b"\xff", b"\xf8\x88\x80\x80\x80"):
        rejects(INV.encode_unsigned, stmt(account=bad), exc=INV.DecodeFailure)
    nfc, nfd = "café".encode(), "café".encode()
    signed = sign(stmt(account=nfc))
    accepts(INV.accept, signed, nfc, Rec(account=nfc))
    refused(signed, "account", Rec(account=nfc), asked=nfd)


# ============================================= built in memory; refusal kinds

@case("IV-05 a statement built in memory that breaks an encoding rule is refused as a decode failure before check 1, as bytes are: the policy receives no call, even where the account asked about also differs, so check 1 would refuse it too",
      f"{HD}: A statement that breaks an encoding rule is refused before check 1, whether it arrived as bytes or was built in memory")
def _():
    good = DB(1, honest_key(), 1)
    breaches = {
        "empty account": stmt(account=b""),
        "long account": stmt(account=b"x" * 257),
        "bad UTF-8": stmt(account=b"\xff"),
        "nine active": stmt(active=canonical([DB(i, honest_key(), 1) for i in range(9)])),
        "nine revoked": stmt(revoked=[RV(DB(i, honest_key(), 1), 3) for i in range(9)]),
        "capability zero": stmt(active=[DB(1, good.identity_public_key, 0)]),
        "capability two": stmt(active=[DB(1, good.identity_public_key, 2)]),
        "capability 1 | 2^63": stmt(active=[DB(1, good.identity_public_key, 1 | 2 ** 63)]),
        "descending": stmt(active=[DB(2, good.identity_public_key, 1), good]),
        "floor above generation": stmt(gen=1, floor=2),
        "terminal at floor": stmt(revoked=[RV(good, 1)]),
        "both lists": stmt(active=[good], revoked=[RV(good, 2)]),
        "predecessor of 31 bytes": stmt(active=[DB(1, good.identity_public_key, 1, b"\x01" * 31)]),
        "device_id past u32": stmt(active=[DB(2 ** 32, good.identity_public_key, 1)]),
        "key of 31 bytes": stmt(active=[DB(1, b"\x09" * 31, 1)]),
    }
    for name, s in breaches.items():
        for asked in (ALICE, b"acme/bob"):
            policy = Rec()
            e = rejects(INV.accept_built, s, bytes(64), asked, policy, exc=INV.InventoryRefusal)
            assert isinstance(e, INV.DecodeFailure), f"{name}: {type(e).__name__}"
            assert policy.calls == [], f"{name}: the policy was called"
        rejects(INV.encode_unsigned, s, exc=INV.DecodeFailure)
    # and the same statement, well formed, gets as far as check 1
    refused_ = rejects(INV.accept_built, stmt(active=[good]), bytes(64), b"acme/bob", Rec(), exc=INV.InventoryRefusal)
    assert refused_.check == "account"


@case("IV-06 three refusal kinds: an encoding rule is a decode failure, check 3 an authentication failure, and every other check a refusal of a well-formed, authentic statement; the three are distinct",
      f"{HD}: A refusal by an encoding rule is a decode failure, and a refusal by check 3 below is an authentication failure (error-handling.md). The other checks refuse a statement that is well formed and authentic")
def _():
    kinds = (INV.DecodeFailure, INV.AuthenticationFailure, INV.StatementRefused)
    for a, b in itertools.permutations(kinds, 2):
        assert not issubclass(a, b)
    b = DB(1, honest_key(), 1)
    signed = sign(stmt(active=[b]))
    e = rejects(INV.accept, signed[:-64] + b"\x00" + signed[-64:], ALICE, Rec(), exc=INV.InventoryRefusal)
    assert isinstance(e, INV.DecodeFailure)
    e = rejects(INV.accept, signed[:-1] + bytes([signed[-1] ^ 0x01]), ALICE, Rec(), exc=INV.InventoryRefusal)
    assert isinstance(e, INV.AuthenticationFailure) and e.check == "signature"
    for policy, check in ((Rec(), "account"), (Rec(kid=8), "issuer"), (Rec(fresh=lambda a, g: False), "freshness"),
                          (Rec(binding=lambda x, y: False), "binding-policy"),
                          (Rec(statement=lambda s: False), "statement-policy")):
        asked = b"acme/bob" if check == "account" else ALICE
        e = rejects(INV.accept, signed, asked, policy, exc=INV.InventoryRefusal)
        assert isinstance(e, INV.StatementRefused) and e.check == check, (check, e)


# ============================================================== issuer's duty

@case("IV-07 the issuer applies the encoding rules, check 5 and check 6 before it signs and signs none that fails them; what it signs passes checks 5 and 6 at every verifier; a statement forced past that duty is refused by every verifier, at decode, check 5 or check 6",
      f"{HD}: An issuer must apply the encoding rules, check 5 and check 6 below to a statement before it signs it, and must not sign one that fails any of them: every verifier refuses such a statement")
def _():
    k1, k2 = honest_key(), honest_key()
    bad_key = (int.from_bytes(k1, "little") + P).to_bytes(32, "little") if int.from_bytes(k1, "little") < 2 ** 256 - P else b"\xff" * 32
    duties = {
        "decode": stmt(active=[DB(2, k1, 1), DB(1, k2, 1)]),
        "duplicate-device": stmt(active=canonical([DB(1, k1, 1), DB(1, k2, 1)])),
        "identity-key (active)": stmt(active=[DB(1, bytes(32), 1)]),
        "identity-key (revoked)": stmt(active=[DB(1, k1, 1)], revoked=[RV(DB(1, bad_key, 1), 3)]),
        "identity-key (twist)": stmt(active=[DB(1, (2).to_bytes(32, "little"), 1)]),
    }
    for name, s in duties.items():
        rejects(INV.sign_statement, ISSUER, s, rnd(64), exc=INV.IssuerRefusal)
        check = name.split(" ")[0]
        if check == "decode":
            rejects(INV.accept_built, s, bytes(64), ALICE, Rec(), exc=INV.DecodeFailure)
        else:
            refused(force_sign(s), check)
    for _ in range(12):
        s = random_statement()
        s = ST(7, ALICE, s.inventory_generation, tuple(canonical({b.device_id: b for b in s.active}.values())),
               s.revocation_floor_generation, s.revoked)
        got = accepts(INV.accept, sign(s), ALICE, Rec())
        assert got == s


# ================================================================== check 4

class GenerationRecord:
    """A verifier's stored generation per account: advanced after check 7, by
    one compare-and-advance that never lowers it."""

    def __init__(self):
        self.stored = {}

    def compare_and_advance(self, account, generation):
        current = self.stored.get(account)
        if current is None or generation > current:
            self.stored[account] = generation
            return True
        return False


class StoredFreshness(Rec):
    def __init__(self, record, rule, **kw):
        super().__init__(**kw)
        self.record, self.rule = record, rule
        self._fresh = lambda a, g: self.rule(self.record.stored.get(a), g)

    def accepted(self, statement):
        super().accepted(statement)
        self.record.compare_and_advance(bytes(statement.account_handle), statement.inventory_generation)


def newer(stored, g):
    return stored is None or g > stored


@case("IV-08 the freshness rule runs before checks 5 to 7 and has no effect of its own: a statement refused at check 5, 6 or 7 leaves the stored generation where it was, even though check 4 accepted its generation; the generation is recorded only after check 7 accepts",
      f"{AC}, check 4: The rule runs before checks 5 to 7, which can still refuse the statement, so it must have no effect of its own: a verifier records a generation as seen, or advances a stored one, only after check 7 has accepted the statement")
def _():
    k1, k2 = honest_key(), honest_key()
    later = {
        "duplicate-device": (stmt(active=canonical([DB(1, k1, 1), DB(1, k2, 1)]), gen=9), {}),
        "identity-key": (stmt(active=[DB(1, bytes(32), 1)], gen=9), {}),
        "binding-policy": (stmt(active=[DB(1, k1, 1)], gen=9), {"binding": lambda b, s: False}),
        "statement-policy": (stmt(active=[DB(1, k1, 1)], gen=9), {"statement": lambda s: False}),
    }
    for check, (s, kw) in later.items():
        record = GenerationRecord()
        record.stored[ALICE] = 5
        policy = StoredFreshness(record, newer, **kw)
        refused(force_sign(s), check, policy)
        assert ("freshness", ALICE, 9) in policy.calls, "check 4 did not run before the later refusal"
        assert record.stored[ALICE] == 5 and policy.recorded == [], f"{check}: the record moved"
    record = GenerationRecord()
    record.stored[ALICE] = 5
    accepts(INV.accept, sign(stmt(active=[DB(1, k1, 1)], gen=9)), ALICE, StoredFreshness(record, newer))
    assert record.stored[ALICE] == 9
    # the same generation again is not newer, under this verifier's rule
    refused(sign(stmt(active=[DB(1, k1, 1)], gen=9)), "freshness", StoredFreshness(record, newer))


@case("IV-09 where statements are verified concurrently the record is advanced by one compare-and-advance and never decreases: two statements that both pass check 4 against the same stored value leave the larger generation stored in whichever order they finish, where a plain write of the later one would lower the record",
      f"{AC}, check 4: Where statements can be verified concurrently, that step is one atomic compare-and-advance against the stored value, and a stored value never decreases. Otherwise two statements can both pass this check and the later write can lower the record")
def _():
    k = honest_key()

    class PlainWrite(GenerationRecord):
        def compare_and_advance(self, account, generation):
            self.stored[account] = generation
            return True

    def race(record, first, second):
        """`first` passes check 4, then `second` runs to completion, then
        `first` finishes: both passed check 4 against the same stored value."""
        s_first, s_second = sign(stmt(active=[DB(1, k, 1)], gen=first)), sign(stmt(active=[DB(1, k, 1)], gen=second))
        inner = StoredFreshness(record, newer)

        def interleave(stored, g):
            ok = newer(stored, g)
            accepts(INV.accept, s_second, ALICE, inner)
            return ok

        accepts(INV.accept, s_first, ALICE, StoredFreshness(record, lambda st, g: interleave(st, g)))
        return record.stored[ALICE]

    for first, second in ((4, 6), (6, 4)):
        record = GenerationRecord()
        record.stored[ALICE] = 3
        assert race(record, first, second) == max(first, second)
    # the interleaving does reach the hazard the page names: with a plain
    # write, the statement finishing last lowers the record
    naive = PlainWrite()
    naive.stored[ALICE] = 3
    assert race(naive, 4, 6) == 4


# ================================================================== check 6

def u_of(pt):
    zi = _inv(pt[2])
    y = pt[1] * zi % P
    return (1 + y) * _inv(1 - y) % P


def point_of_u(u, sign=0):
    y = (u - 1) * _inv(u + 1) % P
    x = _recover_x(y, sign)
    return None if x is None else (x, y, 1, x * y % P)


def torsion_points():
    """The eight points of order dividing 8: from the order-8 point with the
    smallest u on the curve found by clearing the prime-order part."""
    for seed in range(2, 200):
        pt = point_of_u(seed)
        if pt is None:
            continue
        t = _mul(Q, pt)                              # kills the subgroup part
        if not _is_identity(_mul(4, t)):             # of order exactly 8
            return [_mul(i, t) for i in range(8)]
    raise AssertionError("no order-8 point found")


TORSION = torsion_points()
LISTED_ORDER_EIGHT = {int.from_bytes(bytes.fromhex(h), "little") for h in (
    "e0eb7a7c3b41b8ae1656e3faf19fc46ada098deb9c32b1fd866205165f49b800",
    "5f9c95bca3508c24b1d0b1559c83ef5b04445cc4581c8e86d8224eddd09f1157")}


@case("IV-10 check 6's three-step test decides its definition: the u-coordinate of every point kB passes, and every honest X25519 public key with it; the u of kB plus any of the seven non-identity low-order points fails; the two points sharing a y-coordinate give the same answer, so the sign of x does not matter",
      f"{AC}, check 6: a canonical curve public key ... whose u-coordinate belongs to a point of the prime-order subgroup of edwards25519 ... A verifier tests that in three steps ... the two points with that y-coordinate give the same answer, so the sign of x does not matter; A key an honest device publishes is the X25519 public key of a clamped secret, which is `kB`")
def _():
    for _ in range(12):
        secret = rnd(32)
        assert INV.is_identity_key(x25519_public(secret))
        kB = _mul(_decode_scalar25519(secret), BASE)
        assert u_of(kB).to_bytes(32, "little") == x25519_public(secret)
        k = R.randrange(1, Q)
        pt = _mul(k, BASE)
        assert INV.is_identity_key(u_of(pt).to_bytes(32, "little"))
        for t in TORSION[1:]:
            mixed = _add(pt, t)
            u = u_of(mixed)
            assert not INV.is_identity_key(u.to_bytes(32, "little")), "a mixed-torsion key passed"
        for u in (u_of(pt), u_of(_add(pt, TORSION[3]))):
            verdicts = {_is_identity(_mul(Q, point_of_u(u, s))) for s in (0, 1)}
            assert len(verdicts) == 1


@case("IV-11 the five low-order values the page lists: 0 (order 2) and 1 (order 4) and the two listed order-eight values are exactly the u-coordinates of the low-order points of edwards25519, the identity having none; p - 1 maps to no point and is refused by the first step; X25519 with any of the five yields the all-zero string under every private key tried; check 6 refuses all five",
      f"{AC}, check 6: the five low-order values: the u-coordinates 0, 1 and p − 1, and the two of order eight ... X25519 with any of them yields the all-zero string for every private key; `u` is not p − 1")
def _():
    us = set()
    for i, t in enumerate(TORSION):
        if _is_identity(t):
            continue
        us.add(u_of(t))
    assert us == {0, 1} | LISTED_ORDER_EIGHT, sorted(hex(u) for u in us)
    assert point_of_u(0) is not None and _is_identity(_mul(2, point_of_u(0)))
    assert point_of_u(1) is not None and _is_identity(_mul(4, point_of_u(1))) and not _is_identity(_mul(2, point_of_u(1)))
    for u in LISTED_ORDER_EIGHT:
        pt = point_of_u(u)
        assert _is_identity(_mul(8, pt)) and not _is_identity(_mul(4, pt))
    five = [0, 1, P - 1] + sorted(LISTED_ORDER_EIGHT)
    for u in five:
        raw = u.to_bytes(32, "little")
        assert not INV.is_identity_key(raw)
        for _ in range(4):
            assert x25519(rnd(32), raw) == bytes(32)


@case("IV-12 a u-coordinate that no point of the curve has is refused (u = 2 is one): the test's second step finds no point, and every canonical u it finds no point for is refused; among canonical u values that do have a point, check 6 passes exactly those whose point has order q",
      f"{AC}, check 6: a u-coordinate that no point of the curve has, because it lies on the quadratic twist (u = 2 is one); `y = (u − 1) / (u + 1) mod p` is the y-coordinate of a point `P` of edwards25519")
def _():
    assert point_of_u(2) is None and not INV.is_identity_key((2).to_bytes(32, "little"))
    twist = on_curve = 0
    for _ in range(60):
        u = R.randrange(2, P - 1)
        pt = point_of_u(u)
        verdict = INV.is_identity_key(u.to_bytes(32, "little"))
        if pt is None:
            twist += 1
            assert not verdict
        else:
            on_curve += 1
            assert verdict == _is_identity(_mul(Q, pt))
    assert twist and on_curve


@case("IV-13 a mixed-torsion key agrees exactly as the subgroup point it was built from: X25519 under a clamped secret gives the same output for all eight spellings P + T, the eight are distinct u values, and exactly one of them passes check 6",
      f"{AC}, check 6: a u-coordinate of mixed torsion: the sum of a point of the subgroup and a low-order point. It agrees exactly as the subgroup point it was built from, so one key would have eight spellings")
def _():
    for _ in range(4):
        pt = _mul(R.randrange(1, Q), BASE)
        spellings = [u_of(_add(pt, t)).to_bytes(32, "little") for t in TORSION]
        assert len(set(spellings)) == 8
        assert [INV.is_identity_key(s) for s in spellings].count(True) == 1
        secret = rnd(32)
        outs = {x25519(secret, s) for s in spellings}
        assert len(outs) == 1


@case("IV-14 exactly one spelling of a key passes: an honest key with bit 255 set, or with p added where that fits in 32 bytes, is refused, so check 7 may compare identity keys as bytes",
      f"{AC}, check 6: Besides the non-canonical spellings (message-format.md), this refuses ...; Exactly one spelling of a key passes, so check 7 can compare identity keys as bytes")
def _():
    for _ in range(20):
        key = honest_key()
        u = int.from_bytes(key, "little")
        assert INV.is_identity_key(key)
        assert not INV.is_identity_key((u | (1 << 255)).to_bytes(32, "little"))
        if u + P < 2 ** 256:
            assert not INV.is_identity_key((u + P).to_bytes(32, "little"))
    for u in (P, P + 1, P + 9, 2 ** 255 - 1, 2 ** 256 - 1):
        assert not INV.is_identity_key(u.to_bytes(32, "little"))


@case("IV-15 check 6 covers every entry, active and revoked, before check 7 is applied to any binding: one unsound key anywhere in a statement is refused as identity-key with no binding-policy and no statement-policy call",
      f"{AC}, check 7: The verifier applies check 6 to every entry, those of `active` and then those of `revoked`, each in encoded order, before it applies check 7 to any binding, so its binding and statement policies never run on a statement that carries an unsound key")
def _():
    bad_keys = [bytes(32), (1).to_bytes(32, "little"), (2).to_bytes(32, "little"), b"\xff" * 32,
                u_of(_add(_mul(5, BASE), TORSION[1])).to_bytes(32, "little")]
    for _ in range(10):
        active = [DB(i, honest_key(), 1) for i in range(1, R.randrange(2, 5))]
        revoked = [RV(DB(i, honest_key(), 1), 3) for i in range(1, R.randrange(2, 5))]
        where = R.randrange(len(active) + len(revoked))
        bad = R.choice(bad_keys)
        if where < len(active):
            active[where] = DB(active[where].device_id, bad, 1)
        else:
            j = where - len(active)
            revoked[j] = RV(DB(revoked[j].binding.device_id, bad, 1), 3)
        s = stmt(active=canonical(active), revoked=sorted(revoked, key=INV.encode_revocation))
        policy = refused(force_sign(s), "identity-key")
        assert not any(c[0] in ("binding", "statement") for c in policy.calls)


# ================================================== checks 5, 7, 1, 2 and 3

@case("IV-16 check 5 is over active alone: two revoked entries with one device_id, and an active and a revoked entry with one device_id, are accepted; two active entries with one device_id are refused, and before check 6 would refuse a bad key",
      f"{AC}, check 5: No two entries of `active` share a `device_id`. An active and a revoked binding may share one: that is a device whose key was replaced under its old id")
def _():
    k1, k2, k3 = honest_key(), honest_key(), honest_key()
    accepts(INV.accept, sign(stmt(revoked=sorted([RV(DB(4, k1, 1), 3), RV(DB(4, k2, 1), 3)], key=INV.encode_revocation))), ALICE, Rec())
    accepts(INV.accept, sign(stmt(active=[DB(4, k1, 1)], revoked=[RV(DB(4, k2, 1), 3)])), ALICE, Rec())
    refused(force_sign(stmt(active=canonical([DB(4, k1, 1), DB(4, k2, 1)]))), "duplicate-device")
    refused(force_sign(stmt(active=canonical([DB(4, k1, 1), DB(4, bytes(32), 1)]), revoked=[RV(DB(6, b"\xff" * 32, 1), 2)])),
            "duplicate-device")
    refused(force_sign(stmt(active=canonical([DB(4, k1, 1), DB(5, k3, 1, b"\x01" * 32), DB(5, k3, 1)]))), "duplicate-device")


@case("IV-17 check 7: the binding policy is told each binding and its list -- the binding alone, not a revocation's terminal generation -- active entries in encoded order and then revoked entries in encoded order, and the verifier stops at its first refusal; the statement policy runs only when every binding is accepted, once, and is given the whole statement as verified, the revoked entries' terminal generations and the floor included",
      f"{AC}, check 7: It then applies the binding policy to the entries of `active` in encoded order and then to the entries of `revoked` in encoded order, telling it the binding and which list it came from, and stops at the first refusal. The statement policy runs only when every binding has been accepted, and it is given the whole statement as verified")
def _():
    active = canonical([DB(i, honest_key(), 1) for i in (3, 1, 2)])
    revoked = sorted([RV(DB(i, honest_key(), 1), t) for i, t in ((2, 4), (1, 3), (1, 5))], key=INV.encode_revocation)
    s = stmt(active=active, revoked=revoked, gen=5, floor=2)
    signed = sign(s)
    policy = Rec()
    got = accepts(INV.accept, signed, ALICE, policy)
    assert policy.bindings == [("active", b) for b in active] + [("revoked", r.binding) for r in revoked]
    assert all(isinstance(b, INV.DeviceBinding) for _, b in policy.bindings)
    assert policy.statements == [got] and got == INV.decode_signed(signed)[0] == s
    assert [r.terminal_generation for r in policy.statements[0].revoked] == [r.terminal_generation for r in revoked]
    everything = active + [r.binding for r in revoked]
    for stop in range(len(everything)):
        target = everything[stop]
        p = Rec(binding=lambda b, st, _t=target, _i=stop: not (b == _t and st == ("active" if _i < len(active) else "revoked")))
        refused(signed, "binding-policy", p)
        assert [b for _, b in p.bindings] == everything[:stop + 1]
        assert p.statements == [] and p.recorded == []
    p = Rec(statement=lambda st: False)
    refused(signed, "statement-policy", p)
    assert len(p.bindings) == len(everything) and p.recorded == []


@case("IV-18 check 1 compares the account byte for byte before any lookup, so a statement for another account under an issuer key that serves both is refused with no issuer call; check 2 resolves the pair (issuer_key_id, account_handle), so a key bound for one account does not resolve for another",
      f"{AC}, check 1: This comes before any lookup, so a valid statement for another account, signed under an issuer key that serves several accounts, is refused; check 2: The verifier's issuer-key binding resolves `(issuer_key_id, account_handle)` to a verification key. An unbound issuer is refused")
def _():
    class Shared(Rec):
        def issuer_key(self, kid, account):
            self.calls.append(("issuer", kid, account))
            return ISSUER_PUB if kid == 7 else None

    bob = b"acme/bob"
    s_bob = sign(stmt(account=bob, active=[DB(1, honest_key(), 1)]))
    accepts(INV.accept, s_bob, bob, Shared())
    for asked in (ALICE, b"acme/bo", b"acme/bob ", b"ACME/BOB", b""):
        p = refused(s_bob, "account", Shared(), asked=asked)
        assert p.calls == []
    p = refused(s_bob, "issuer", Rec(account=ALICE), asked=bob)
    assert p.calls == [("issuer", 7, bob)]


@case("IV-19 the signature is over \"Tacenta:inventory-statement:v1\" || 0xFF || the preimage and is verified as the page's Verifying a signature states: one made over the bare preimage, over the label without its terminator, under the application-signature label, or with s + q is refused as an authentication failure; one from a signer that leaves A's sign bit set, which revision 1 of XEdDSA refuses, is accepted",
      f"{HD}: A signed statement is the unsigned preimage followed by a 64-byte XEdDSA signature over: \"Tacenta:inventory-statement:v1\" || 0xFF || unsigned_preimage; {AC}, check 3; {ID} Verifying a signature, steps 2 and 4, and: It is wider on the sign bit ... a signer that does not normalise the sign still verifies")
def _():
    assert INV.INVENTORY_SIGNING_LABEL == b"Tacenta:inventory-statement:v1\xff" and len(INV.INVENTORY_SIGNING_LABEL) == 31
    s = stmt(active=[DB(1, honest_key(), 1)])
    unsigned = INV.encode_unsigned(s)
    accepts(INV.accept, unsigned + xeddsa_sign(ISSUER, INV.signing_input(unsigned), rnd(64)), ALICE, Rec())
    for wrong in (unsigned, b"Tacenta:inventory-statement:v1" + unsigned,
                  b"tacenta:application-signature:v1\xff" + unsigned,
                  INV.INVENTORY_SIGNING_LABEL + INV.INVENTORY_SIGNING_LABEL + unsigned):
        e = rejects(INV.accept, unsigned + xeddsa_sign(ISSUER, wrong, rnd(64)), ALICE, Rec(), exc=INV.InventoryRefusal)
        assert isinstance(e, INV.AuthenticationFailure)
    sig = xeddsa_sign(ISSUER, INV.signing_input(unsigned), rnd(64))
    s_int = int.from_bytes(sig[32:], "little")
    plus_q = sig[:32] + (s_int + Q).to_bytes(32, "little")
    assert plus_q[63] & 0x80 == 0
    refused(unsigned + plus_q, "signature")
    # a signer that does not normalise: find an issuer secret whose E = kB has sign 1
    for trial in range(64):
        secret = bytes([trial + 1]) * 32
        k = _decode_scalar25519(secret)
        e_enc = compress(_mul(k, BASE))
        if e_enc[31] >> 7:
            break
    assert e_enc[31] >> 7, "no secret with an odd-signed kB found"
    msg = INV.signing_input(unsigned)
    r = _sha512_int(b"\x5a" * 32 + msg) % Q
    R_ = compress(_mul(r, BASE))
    h = _sha512_int(R_ + e_enc + msg) % Q
    sv = (r + h * k) % Q
    raw_sig = R_ + sv.to_bytes(32, "little")
    raw_sig = raw_sig[:63] + bytes([raw_sig[63] | 0x80])
    got = accepts(INV.accept, unsigned + raw_sig, ALICE, Rec(key=x25519_public(secret)))
    assert got == s


# ====================================================== commitment; unchecked

@case("IV-20 binding_commitment is SHA-256 of \"Tacenta:inventory-binding-commitment:v1\" || 0xFF || the binding's encoding; it changes with every field, the predecessor's presence and value included; it does not read the key's soundness; a revocation's terminal generation is not part of it; a binding whose capability word breaks the rule has none",
      f"{HD}: `binding_commitment(binding)` is the 32-byte SHA-256 digest of ... A binding whose capability word breaks the rule above has no encoding, so it has no commitment and the function refuses it. The commitment covers every binding field, including the predecessor")
def _():
    assert INV.BINDING_COMMITMENT_LABEL == b"Tacenta:inventory-binding-commitment:v1\xff" and len(INV.BINDING_COMMITMENT_LABEL) == 40
    key = honest_key()
    base = DB(7, key, 1, b"\x04" * 32)
    assert INV.binding_commitment(base) == hashlib.sha256(INV.BINDING_COMMITMENT_LABEL + INV.encode_binding(base)).digest()
    variants = [DB(8, key, 1, b"\x04" * 32), DB(7, honest_key(), 1, b"\x04" * 32), DB(7, key, 1, None),
                DB(7, key, 1, b"\x05" + b"\x04" * 31), DB(7, key, 1, b"\x04" * 31 + b"\x05")]
    commits = {INV.binding_commitment(v) for v in variants + [base]}
    assert len(commits) == len(variants) + 1
    accepts(INV.binding_commitment, DB(7, bytes(32), 1))
    for caps in (0, 2, 3, 2 ** 63, 1 | 2 ** 63, 2 ** 64 - 1):
        rejects(INV.binding_commitment, DB(7, key, caps), exc=INV.DecodeFailure)


@case("IV-21 what the format leaves unchecked is accepted by checks 1 to 6 and by the format: a marker naming no binding; a marker equal to the commitment of a binding still active; a replacement identical to what it replaces apart from its marker; a replacement under a new device_id; one key on two devices; a revoked key listed again as active; one binding revoked twice",
      f"{AC}, the unchecked properties: Chain of custody for a replacement ...; Uniqueness and reactivation. The same identity key on more than one binding, a revoked key listed again as active, a replacement identical to what it replaces, and the same binding listed more than once in `revoked` are all accepted by the format")
def _():
    k1, k2 = honest_key(), honest_key()
    old = DB(1, k1, 1)
    statements = {
        "orphan marker": stmt(active=[DB(1, k2, 1, rnd(32))]),
        "still-active marker": stmt(active=canonical([DB(1, k1, 1), DB(2, k2, 1, INV.binding_commitment(DB(1, k1, 1)))])),
        "identical replacement": stmt(active=[DB(1, k1, 1, INV.binding_commitment(old))], revoked=[RV(old, 3)]),
        "new device id": stmt(active=[DB(9, k2, 1, INV.binding_commitment(old))], revoked=[RV(old, 3)]),
        "one key, two devices": stmt(active=canonical([DB(1, k1, 1), DB(2, k1, 1)])),
        "revoked key relisted": stmt(active=[DB(2, k1, 1)], revoked=[RV(old, 3)]),
        "revoked twice": stmt(revoked=[RV(old, 2), RV(old, 4)]),
    }
    for name, s in statements.items():
        got = accepts(INV.accept, sign(s), ALICE, Rec())
        assert got == s, name
