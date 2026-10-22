"""Pass 14. identities-and-devices.md, The identity pair digest and The
verification number; session-establishment.md, Records, expectations and
attribution, and the place of the expectation's check in Sending the initial
message.

- the digest: its label, the order of its keys, its refusals (RC-01 to RC-03);
- the verification number (RC-04);
- records, classification and lookup (RC-05 to RC-08);
- the initiator's expectation: malformed expectations, the two forms, the
  identity-key rule applied first, the order among her checks, what a refusal
  spends, and that an expectation is required (RC-09 to RC-15);
- attribution against the records as they stand, and the responder (RC-16,
  RC-17);
- the way forward from a recorded key the rule refuses (RC-18).

Every key, record and bundle is built here; nothing is taken from a vector's
bytes. Where a case reaches a point the page leaves open, it says so and cites
the gap.
"""

import hashlib
import random

import cases_idkeys as IKC
from _casekit import accepts, registry, rejects
from tacenta_reader import admission, records, wire
from tacenta_reader import constants as K
from tacenta_reader import curve25519 as C
from tacenta_reader.curve25519 import P as PRIME, x25519_public

CASES, case = registry()
ID = "identities-and-devices.md"
PD = f"{ID}, The identity pair digest"
VN = f"{ID}, The verification number"
SE = "session-establishment.md"
REC = f"{SE}, Records, expectations and attribution"
R = random.Random(20261022_14)
Record, Known, FirstContact = records.Record, records.Known, records.FirstContact


def rnd(n):
    return bytes(R.randrange(256) for _ in range(n))


def honest():
    return x25519_public(rnd(32))


def ub(u):
    return u.to_bytes(32, "little")


NONCANON = [ub(PRIME), ub(PRIME + 1), ub(2 ** 255 - 1), bytes(31) + b"\x80", b"\xff" * 32,
            ub(int.from_bytes(IKC.HONEST, "little") | 1 << 255)]
NOT_IDENTITY = list(IKC.BAD_KEYS.values()) + IKC.MIXED


def establish(bundle, expectation):
    return IKC.establish(bundle, expectation)


def spent(rng, ctr):
    return IKC.spent(rng, ctr)


BOB = x25519_public(IKC.IKB_SECRET)
OTHER_SECRET = b"\x99" * 32
OTHER = x25519_public(OTHER_SECRET)


def bob_bundle(**kw):
    return IKC.make_bundle(**kw)


def other_bundle(**kw):
    """A bundle under another identity key, its signatures made under that key."""
    return IKC.make_bundle(identity_key=OTHER, sign_under=OTHER_SECRET, **kw)


def unencodable_ek():
    ek = bytearray(IKC.EK)
    ek[0] = 0xFF
    ek[1] |= 0x0F            # the first 12-bit coefficient is 0xFFF, at least q
    return bytes(ek)


# ======================================================== the identity pair digest

@case("RC-01 the identity pair digest is SHA-256 over the 32-byte label and the two keys sorted as strings of unsigned bytes, byte 0 first; the label is CONSTANTS.md's 31 ASCII bytes with a capital T and 0xFF; for keys whose unsigned byte order disagrees with their little-endian value order, with a signed-byte order and with a u64-limb order, the byte order decides; the digest is the same in either order, and equal keys are allowed",
      f"{PD}: (lo, hi) = (k1, k2) if k1 <= k2, else (k2, k1); return SHA-256(PAIR_DIGEST_LABEL || lo || hi) ... k1 <= k2 compares the keys as strings of unsigned bytes, byte 0 first, and the first byte that differs decides. It is not the order of the keys' values, which are little-endian ... Equal keys are allowed; CONSTANTS.md, PAIR_DIGEST_LABEL")
def _():
    assert records.PAIR_DIGEST_LABEL.hex() == "546163656e74613a6964656e746974793a706169722d6469676573743a7631ff"
    assert len(records.PAIR_DIGEST_LABEL) == 32 and records.PAIR_DIGEST_LABEL[:1] == b"T"
    found = {"value": 0, "signed": 0, "limb": 0}
    for _ in range(400):
        a, b = honest(), honest()
        d = records.identity_pair_digest(a, b)
        assert d == records.identity_pair_digest(b, a)
        lo, hi = sorted((a, b))
        assert d == hashlib.sha256(records.PAIR_DIGEST_LABEL + lo + hi).digest()
        if (a < b) != (int.from_bytes(a, "little") < int.from_bytes(b, "little")):
            found["value"] += 1
            assert d != hashlib.sha256(records.PAIR_DIGEST_LABEL + max(a, b) + min(a, b)).digest()
        signed = lambda k: [x - 256 if x > 127 else x for x in k]  # noqa: E731
        if (a < b) != (signed(a) < signed(b)):
            found["signed"] += 1
        limbs = lambda k: [int.from_bytes(k[j:j + 8], "little") for j in range(0, 32, 8)]  # noqa: E731
        if (a < b) != (limbs(a) < limbs(b)):
            found["limb"] += 1
    assert all(found.values()), found
    for _ in range(5):
        k = honest()
        assert records.identity_pair_digest(k, k) == hashlib.sha256(records.PAIR_DIGEST_LABEL + k + k).digest()


@case("RC-02 the digest applies the identity-key rule to both keys: a key with bit 255 set or a value at least p is a decode failure, a canonical key that is not an identity key (low order, off the curve, mixed order, p - 1) is an invalid identity key, in either position; it refuses nothing else (every honest key, and equal keys, give a digest); when both keys are refused with different kinds, the refusal is one of the two",
      f"{PD}: a key whose bit 255 is set, or whose value, read little-endian, is at least p = 2^255 - 19, is refused as DecodeEC refuses it: a decode failure; a canonical key that is not an identity key is refused as an invalid identity key. It refuses nothing else. When both keys would be refused, either refusal conforms")
def _():
    good = honest()
    for bad in NONCANON:
        rejects(records.identity_pair_digest, bad, good, exc=wire.DecodeError)
        rejects(records.identity_pair_digest, good, bad, exc=wire.DecodeError)
    for bad in NOT_IDENTITY:
        e = rejects(records.identity_pair_digest, bad, good, exc=Exception)
        assert type(e) is wire.InvalidIdentityKey, type(e).__name__
        e = rejects(records.identity_pair_digest, good, bad, exc=Exception)
        assert type(e) is wire.InvalidIdentityKey, type(e).__name__
        rejects(records.identity_pair_digest, bad, bad, exc=wire.InvalidIdentityKey)
    for a in NONCANON[:2]:
        for b in NOT_IDENTITY[:2]:
            for pair in ((a, b), (b, a)):
                e = rejects(records.identity_pair_digest, *pair, exc=Exception)
                assert isinstance(e, (wire.DecodeError, wire.InvalidIdentityKey)), type(e).__name__
    for _ in range(20):
        accepts(records.identity_pair_digest, honest(), honest())


@case("RC-03 a key and its torsion translate, which agree as X25519 keys, cannot give two digests: the translate is refused, so one key has one digest; two different pairs give different digests",
      f"{PD}: One spelling. An identity key has one canonical spelling (Identity keys, above), so a pair of keys has one digest; What is bound. The two keys, and nothing else")
def _():
    other = honest()
    for t in IKC.mixed_keys(IKC.HONEST):
        assert C.torsion_related(IKC.HONEST, t)
        rejects(records.identity_pair_digest, t, other, exc=wire.InvalidIdentityKey)
    d = records.identity_pair_digest(IKC.HONEST, other)
    assert d != records.identity_pair_digest(IKC.HONEST, honest())
    assert d != records.identity_pair_digest(other, other)


# ======================================================== the verification number

@case("RC-04 the verification number reads the digest as an unsigned big-endian integer, reduces it mod 10^60, and writes 60 ASCII digits, most significant first, left-padded with '0'; it is not the little-endian reading; it may be laid out in twelve groups of five, which does not change the digits",
      f"{VN}: n = digest read as an unsigned big-endian integer; return n mod 10^60, as the ASCII digits 0 to 9, most significant first, left-padded with '0' to 60 digits. The digits may be laid out in twelve groups of five; CONSTANTS.md, Verification number length")
def _():
    vn = records.verification_number
    assert vn(bytes(32)) == "0" * 60
    assert vn(bytes(30) + b"\x30\x39") == "0" * 55 + "12345"
    assert vn(b"\xff" * 32) == str((2 ** 256 - 1) % 10 ** 60).rjust(60, "0")
    seen_leading_zero = False
    for _ in range(300):
        d = rnd(32)
        n = vn(d)
        assert len(n) == 60 and n.isdigit() and n.isascii()
        assert int(n) == int.from_bytes(d, "big") % 10 ** 60
        if int.from_bytes(d, "big") % 10 ** 60 != int.from_bytes(d, "little") % 10 ** 60:
            assert n != str(int.from_bytes(d, "little") % 10 ** 60).rjust(60, "0")
        seen_leading_zero |= n[0] == "0"
        groups = records.verification_number_groups(n)
        assert len(groups) == 12 and all(len(g) == 5 for g in groups) and "".join(groups) == n
    assert seen_leading_zero
    rejects(vn, bytes(31), exc=ValueError)      # the reader's choice: a digest is 32 bytes (G14-04)


# ======================================================== records, classification

@case("RC-05 classification checks the presented key first: a non-canonical key is a decode failure and a canonical non-identity key an invalid identity key, before any member is looked at, so a malformed record does not change that refusal; a presented key whose bytes are a member is still refused when it is not an identity key",
      f"{REC}, Classification: Before anything else, k must be an identity key: if k is not the canonical encoding of a curve public key ..., the classification refuses it as DecodeEC refuses such a key (a decode failure); if k is canonical but not an identity key, the classification refuses it as an invalid identity key")
def _():
    malformed = Record.of([NONCANON[0]])
    for bad in NONCANON:
        rejects(records.classify, bad, Record.of([honest()]), exc=wire.DecodeError)
        rejects(records.classify, bad, malformed, exc=wire.DecodeError)
    for bad in NOT_IDENTITY:
        rejects(records.classify, bad, Record.of([bad]), exc=wire.InvalidIdentityKey)
        rejects(records.classify, bad, Record.of(retired=[bad]), exc=wire.InvalidIdentityKey)
        rejects(records.classify, bad, malformed, exc=wire.InvalidIdentityKey)
        rejects(records.classify, bad, Record(), exc=wire.InvalidIdentityKey)


@case("RC-06 classification checks every member of both sets after the key: a non-canonical member anywhere, current or retired, before or after a match, refuses the classification as a malformed record even when the key matches another member; a canonical member that is not an identity key is not malformed and matches no presented key",
      f"{REC}, Classification: It then checks every member of both sets. If any of them is not a canonical encoding, it refuses the classification as a malformed record (MalformedRecord), even if k matches another member; Records: A member is held to the canonical encoding only, not to the identity-key rule ...: a canonical member that is not an identity key is not malformed, and it matches no presented key")
def _():
    k = honest()
    for bad in NONCANON:
        for rec in (Record.of([k, bad]), Record.of([bad, k]), Record.of([k], [bad]), Record.of([bad], [k]),
                    Record.of(retired=[k, bad]), Record.of([bad])):
            e = rejects(records.classify, k, rec, exc=records.MalformedRecord)
            assert not isinstance(e, wire.DecodeError)
    for odd in NOT_IDENTITY:
        assert records.classify(k, Record.of([k, odd])) == records.SAME
        assert records.classify(k, Record.of([odd], [odd])) == records.NEW
        assert records.classify(k, Record.of([k], [odd])) == records.SAME


@case("RC-07 classification: retired if in the retired set, otherwise same if in the current set, otherwise new; a key in both sets is retired; membership is equality of the 32 bytes; a list with repeated members is the set of its members; an empty record classifies every identity key as new; a party holds a record exactly when either set is non-empty",
      f"{REC}, Classification: Otherwise k is: retired, if it is in the retired set; otherwise same, if it is in the current set; otherwise new. Membership is equality of the 32 bytes; Records: A party holds a record for a contact when either set is non-empty ... A list given for a set denotes the set of its members, and duplicates are ignored ... A key in both sets is retired")
def _():
    k, j, m = honest(), honest(), honest()
    assert records.classify(k, Record.of([k])) == records.SAME
    assert records.classify(k, Record.of(retired=[k])) == records.RETIRED
    assert records.classify(k, Record.of([k], [k])) == records.RETIRED
    assert records.classify(k, Record.of([j, m], [j])) == records.NEW
    assert records.classify(k, Record()) == records.NEW
    assert records.classify(k, Record.of([k, k, j])) == records.classify(k, Record.of([j, k])) == records.SAME
    assert Record.of([k, k, j]) == Record.of([j, k])
    assert not Record().holds_record and Record.of([k]).holds_record and Record.of(retired=[k]).holds_record
    flipped = bytes([k[0] ^ 1]) + k[1:]
    if C.is_identity_key(flipped):
        assert records.classify(flipped, Record.of([k])) == records.NEW


@case("RC-08 lookup across records: same for exactly one record is that contact's, for more than one ambiguous (no contact's), for none with retired for some a retired key, otherwise unattributed; the contacts the key is retired for are reported with any result, a contact's included; a malformed record is skipped and reported and attributes nothing; a presented key the classification refuses refuses the lookup whether or not any record is held",
      f"{REC}, Lookup: A key the classification refuses as a decode failure or as an invalid identity key refuses the lookup in the same way, whether or not the party holds any record, and the lookup reports no record. A record whose classification is refused as a malformed record is skipped: it attributes nothing, and it is reported. The others decide: same for exactly one contact ... more than one ... ambiguous ... same for none and retired for one or more ... a retired key ... same for none and retired for none: unattributed. Wherever a lookup finds the key retired for a contact, that is reported alongside its result")
def _():
    k, j = honest(), honest()
    bad = Record.of([k, NONCANON[0]])
    L = records.lookup
    r = L(k, [Record.of(retired=[k]), Record.of([k]), bad])
    assert (r.attribution, r.contact, r.retired_for, r.malformed) == (records.CONTACT, 1, (0,), (2,))
    r = L(k, [Record.of([k]), Record.of([k]), Record.of(retired=[k])])
    assert (r.attribution, r.contact, r.retired_for) == (records.AMBIGUOUS, None, (2,))
    r = L(k, [Record.of(retired=[k]), Record.of([j]), Record.of(retired=[k])])
    assert (r.attribution, r.contact, r.retired_for) == (records.RETIRED_KEY, None, (0, 2))
    r = L(k, [Record.of([j]), Record()])
    assert (r.attribution, r.retired_for, r.malformed) == (records.UNATTRIBUTED, (), ())
    r = L(k, [bad])
    assert (r.attribution, r.malformed) == (records.UNATTRIBUTED, (0,))
    r = L(k, [bad, Record.of([k], [k])])
    assert (r.attribution, r.retired_for, r.malformed) == (records.RETIRED_KEY, (1,), (0,))
    assert L(k, []).attribution == records.UNATTRIBUTED
    for recs in ([], [Record.of([k])], [bad]):
        rejects(L, NONCANON[0], recs, exc=wire.DecodeError)
        rejects(L, IKC.MIXED[0], recs, exc=wire.InvalidIdentityKey)
    # a record that holds no record attributes nothing, wherever it is
    assert L(k, [Record(), Record.of([k])]).contact == 1


# ======================================================== the initiator's expectation

@case("RC-09 a malformed expectation is refused as a malformed record before any check of Sending the initial message, whatever else the bundle fails: known with an empty record, known whose record holds a non-canonical key (current or retired), first contact with any record holding one; nothing is verified, drawn or computed; first contact over records that include an empty one is not malformed, and a record holding a canonical non-identity key is not malformed",
      f"{REC}, The initiator: She refuses an expectation as a malformed record (MalformedRecord), before any check of Sending the initial message, when it holds a non-canonical key, in the record under known or in any of her records under first contact, or when it is known with a record whose two sets are both empty; error-handling.md: an expectation of a known contact whose record is empty (MalformedRecord)")
def _():
    malformed = [Known(Record()), Known(Record.of([BOB, NONCANON[0]])), Known(Record.of([BOB], [NONCANON[1]])),
                 FirstContact((Record.of([honest()]), Record.of(retired=[NONCANON[2]])))]
    failing_bundles = [bob_bundle(), bob_bundle(one_time=True, one_time_id=K.ABSENT_ID),
                       bob_bundle(identity_key=IKC.MIXED[0]), bob_bundle(sigs=(bytes(64), bytes(64))),
                       bob_bundle(identity_key=NONCANON[0]), other_bundle()]
    for exp in malformed:
        for b in failing_bundles:
            _, err, rng, ctr = establish(b, exp)
            assert isinstance(err, records.MalformedRecord), (exp, type(err).__name__)
            assert spent(rng, ctr) == (0, 0, 0, 0)
    for exp in (FirstContact((Record(), Record.of([honest()]))), Known(Record.of([BOB, bytes(32)])),
                FirstContact((Record.of([ub(2)]),))):
        out, err, _, _ = establish(bob_bundle(), exp)
        assert err is None, (exp, err)


@case("RC-10 under known, the bundle's identity key is classified against that record: same goes on and establishes; new is an unexpected identity; retired is a retired identity, also when the key is in both sets; the record's other members do not matter",
      f"{REC}, The initiator: under known, by classifying it against that record. Retired is refused as a retired identity (RetiredIdentity). New is refused as an unexpected identity (UnexpectedIdentity). Same goes on")
def _():
    for rec, want in ((Record.of([BOB]), None), (Record.of([honest(), BOB], [honest()]), None),
                      (Record.of([honest()]), records.UnexpectedIdentity), (Record.of(retired=[honest()]), records.UnexpectedIdentity),
                      (Record.of([honest()], [BOB]), records.RetiredIdentity), (Record.of([BOB], [BOB]), records.RetiredIdentity)):
        out, err, rng, ctr = establish(bob_bundle(), Known(rec))
        if want is None:
            assert err is None and out.identity_key == BOB, err
            assert spent(rng, ctr)[:2] == (2, 2)
        else:
            assert type(err) is want, (want.__name__, type(err).__name__)
            assert spent(rng, ctr) == (0, 0, 0, 0)


@case("RC-11 under first contact, the bundle's identity key is looked up in all her records: a contact's key or an ambiguous one is an unexpected identity, also when it is retired for another contact; a retired key (same for no contact) is a retired identity; an unattributed key goes on, with no records or with records that do not hold it, and a malformed record cannot reach the lookup because the expectation refuses it first",
      f"{REC}, The initiator: under first contact, by looking it up in her records: a key the lookup finds a contact's, or ambiguous, is refused as an unexpected identity (UnexpectedIdentity). It is a recorded contact's key, served under another name. That holds even when it is also retired for another contact. A retired key (same for no contact) is refused as a retired identity (RetiredIdentity). An unattributed key goes on")
def _():
    x = honest()
    cases = (
        ((Record.of([BOB]),), records.UnexpectedIdentity),
        ((Record.of([x]), Record.of([BOB])), records.UnexpectedIdentity),
        ((Record.of([BOB]), Record.of([BOB])), records.UnexpectedIdentity),
        ((Record.of(retired=[BOB]), Record.of([BOB])), records.UnexpectedIdentity),
        ((Record.of([BOB]), Record.of([x], [BOB])), records.UnexpectedIdentity),
        ((Record.of(retired=[BOB]),), records.RetiredIdentity),
        ((Record.of([x], [BOB]), Record.of(retired=[BOB])), records.RetiredIdentity),
        ((Record.of([BOB], [BOB]),), records.RetiredIdentity),
        ((), None),
        ((Record.of([x], [honest()]), Record()), None),
    )
    for recs, want in cases:
        out, err, rng, ctr = establish(bob_bundle(), FirstContact(recs))
        if want is None:
            assert err is None and out.identity_key == BOB, err
        else:
            assert type(err) is want, (recs, want.__name__, type(err).__name__)
            assert spent(rng, ctr) == (0, 0, 0, 0)


@case("RC-12 the check against the expectation applies the identity-key rule to the key first: a key that is not an identity key is refused as an invalid identity key, never as a refused identity, under known whether the record holds those very bytes as current or as retired or not at all, and under first contact whatever her records say of those bytes",
      f"{REC}, The initiator: Either way the check applies the identity-key rule to the key first, so a key that is not an identity key is refused as an invalid identity key, as the rule's own check would refuse it (Sending the initial message); Malformed input is reported as such ... a key that is not an identity key as an invalid identity key, never as a refused identity")
def _():
    for bad in NOT_IDENTITY:
        for exp in (Known(Record.of([BOB])), Known(Record.of([bad])), Known(Record.of([BOB], [bad])),
                    FirstContact(()), FirstContact((Record.of([bad]),)), FirstContact((Record.of(retired=[bad]),))):
            _, err, rng, ctr = establish(bob_bundle(identity_key=bad), exp)
            assert type(err) is wire.InvalidIdentityKey, (exp, type(err).__name__)
            assert spent(rng, ctr) == (0, 0, 0, 0)


@case("RC-13 the expectation's place among the initiator's checks: after the presence check and the canonical-key checks (a bundle that fails one of those and the expectation is reported as that check's refusal), and before the identity-key rule, either signature, the KEM prekey's input checks and any draw or agreement (a bundle under a key the expectation refuses is reported as that refusal however many of those it would also fail, and nothing is verified, drawn or computed); under the expected key, the same defects give their own refusals",
      f"{SE}, Sending the initial message: She checks the bundle's identity key against her expectation (Records, expectations and attribution, below) after the bundle's presence and canonical-key checks, and before the identity-key rule, the signature checks, the KEM prekey's input checks and anything that draws randomness or computes an agreement; {REC}, The initiator: A bundle refused for its identity key is refused as such, even if a later check would also have failed. Nothing is verified, drawn, computed or sent for it")
def _():
    known_bob = Known(Record.of([BOB]))
    expect_other = Known(Record.of([honest()]))
    retire_bob = Known(Record.of([honest()], [BOB]))
    # earlier checks win over the expectation
    for exp in (expect_other, retire_bob, FirstContact((Record.of([BOB]), Record.of([BOB])))):
        _, err, _, _ = establish(bob_bundle(one_time=True, one_time_id=K.ABSENT_ID), exp)
        assert type(err) is wire.InconsistentBundle, type(err).__name__
        _, err, _, _ = establish(bob_bundle(one_time=False, one_time_id=9), exp)
        assert type(err) is wire.InconsistentBundle, type(err).__name__
        for field in ("signed_prekey", "one_time_prekey"):
            _, err, _, _ = establish(bob_bundle(**{field: NONCANON[0]}), exp)
            assert type(err) is wire.NonCanonicalBundleKey, (field, type(err).__name__)
        _, err, _, _ = establish(bob_bundle(identity_key=NONCANON[5]), exp)
        assert type(err) is wire.NonCanonicalBundleKey, type(err).__name__
    # the expectation wins over every later check
    later = {
        "signed-prekey-signature": dict(sigs=(bytes(64), C.xeddsa_sign(IKC.IKB_SECRET, wire.encode_kem(IKC.EK), rnd(64)))),
        "kem-prekey-signature": dict(sigs=(C.xeddsa_sign(IKC.IKB_SECRET, wire.encode_ec(x25519_public(IKC.SPKB_SECRET)), rnd(64)), bytes(64))),
        "kem-input": dict(sigs=(C.xeddsa_sign(IKC.IKB_SECRET, wire.encode_ec(x25519_public(IKC.SPKB_SECRET)), rnd(64)),
                                C.xeddsa_sign(IKC.IKB_SECRET, wire.encode_kem(unencodable_ek()), rnd(64)))),
        "low-order-signed-prekey": dict(signed_prekey=bytes(32)),
        "low-order-one-time-prekey": dict(one_time_prekey=ub(1)),
    }
    own = {"signed-prekey-signature": wire.BundleSignatureFails, "kem-prekey-signature": wire.BundleSignatureFails,
           "kem-input": admission.pqxdh.KemPrekeyRefused, "low-order-signed-prekey": C.NonContributory,
           "low-order-one-time-prekey": C.NonContributory}
    for name, kw in later.items():
        b = bob_bundle(**kw)
        if name == "kem-input":
            from dataclasses import replace
            b = replace(b, kem_prekey=unencodable_ek())
        for exp, want in ((expect_other, records.UnexpectedIdentity), (retire_bob, records.RetiredIdentity),
                          (FirstContact((Record.of([BOB]),)), records.UnexpectedIdentity)):
            _, err, rng, ctr = establish(b, exp)
            assert type(err) is want, (name, want.__name__, type(err).__name__)
            assert spent(rng, ctr) == (0, 0, 0, 0), (name, spent(rng, ctr))
        _, err, rng, ctr = establish(b, known_bob)
        assert type(err) is own[name], (name, own[name].__name__, type(err).__name__)
        if own[name] is wire.BundleSignatureFails:
            assert spent(rng, ctr)[1:] == (0, 0, 0), (name, spent(rng, ctr))
        if own[name] is admission.pqxdh.KemPrekeyRefused:
            # "She has then computed no agreement and sent nothing. Whether she has drawn EKA before these checks is not fixed"
            assert ctr.agreements == 0 and ctr.signatures_verified == 2, (name, spent(rng, ctr))


@case("RC-14 the order of a malformed expectation against the presence and canonical-key checks, and against a non-identity key: the malformed expectation is refused first, before the checks its refusal is ordered ahead of",
      f"{REC}, The initiator: She refuses an expectation as a malformed record (MalformedRecord), before any check of Sending the initial message; {SE}, Sending the initial message: so such a bundle is refused as an invalid identity key either way, unless her expectation is itself malformed")
def _():
    for exp in (Known(Record()), Known(Record.of([NONCANON[0]])), FirstContact((Record.of([NONCANON[3]]),))):
        for b in (bob_bundle(one_time=True, one_time_id=K.ABSENT_ID), bob_bundle(identity_key=NONCANON[0]),
                  bob_bundle(identity_key=bytes(32)), bob_bundle(identity_key=IKC.MIXED[1])):
            _, err, rng, ctr = establish(b, exp)
            assert type(err) is records.MalformedRecord, type(err).__name__


@case("RC-15 an initiator establishes only with an expectation: establishment with none, or with a named key in place of a record, is not offered (the reader refuses the call); both forms are offered, and an honest bundle establishes under each",
      f"{REC}, The initiator: establishes only with an expectation. An implementation offers initiator establishment under both forms; CHANGELOG.md [Unreleased], Changed: an implementation that offers initiator establishment without an expectation, or with a named key in place of a record, does not conform")
def _():
    for exp in (None, BOB, Record.of([BOB])):
        rng, ctr = admission.Rng(), admission.Counters()
        rejects(admission.initiator_prefix, bob_bundle(), IKC.IKA_SECRET, rng, exp, ctr, exc=TypeError)
        assert spent(rng, ctr) == (0, 0, 0, 0)
    for exp in (Known(Record.of([BOB])), FirstContact(())):
        out, err, _, _ = establish(bob_bundle(), exp)
        assert err is None and out.identity_key == BOB


@case("RC-16 a session is a contact's only when a lookup of its peer key finds it that contact's, against the records as they stand: an initiator's session under known whose key is also current for another contact is established and is no contact's (ambiguous); recording the key later attributes it; moving it to retired withdraws attribution; a first-contact session is unattributed until the key is recorded",
      f"{REC}, Attribution: A session is a contact's only when a lookup of its peer identity key finds it that contact's ... moving a key to retired withdraws attribution from every session under it ...; recording a key attributes that session's earlier plaintexts; The initiator: Under known, a key that is same in her record and also same in another contact's record goes on, and the session is ambiguous: no contact's (ASM-14); First contact, in either role, gives a session whose key is in no record: an unattributed session")
def _():
    alice_records = [Record.of([BOB]), Record.of([BOB, honest()])]
    out, err, _, _ = establish(bob_bundle(), Known(alice_records[0]))
    assert err is None
    assert records.lookup(out.identity_key, alice_records).attribution == records.AMBIGUOUS
    assert records.attributed_contact(out.identity_key, alice_records) is None
    out, err, _, _ = establish(other_bundle(), FirstContact((Record.of([BOB]),)))
    assert err is None and records.attributed_contact(out.identity_key, [Record.of([BOB])]) is None
    later = [Record.of([BOB]), Record.of([OTHER])]
    assert records.attributed_contact(out.identity_key, later) == 1
    retired = [Record.of([BOB]), Record.of([honest()], [OTHER])]
    assert records.attributed_contact(out.identity_key, retired) is None
    assert records.lookup(out.identity_key, retired).attribution == records.RETIRED_KEY


@case("RC-17 the responder's establishment adds no refusal for records: it takes no records, admits a message under any key that passes the identity-key rule, and its session is attributed only by a lookup, in which a malformed record is skipped and reported and does not refuse",
      f"{REC}, The responder: Whatever key the message carries, provided it passes the identity-key rule there, once the message authenticates ... The session is attributed only by a lookup. A malformed record is skipped and reported there; it does not refuse. This section adds no responder refusal beyond the identity-key rule of Receiving the initial message")
def _():
    import inspect
    params = inspect.signature(admission.responder_prefix).parameters
    assert not any("record" in p or "expect" in p for p in params), list(params)
    k = honest()
    recs = [Record.of([k, NONCANON[0]]), Record.of(retired=[k])]
    r = records.lookup(k, recs)
    assert (r.attribution, r.retired_for, r.malformed) == (records.RETIRED_KEY, (1,), (0,))
    assert records.attributed_contact(k, recs) is None


@case("RC-18 a contact whose recorded key the identity-key rule refuses is reached under known after she records the bundle's key and retires the refused one: the record holding the refused canonical key is not malformed, the new key is same and establishes, and the refused key stays retired and matches nothing; before the change, under known, the bundle's key is new and refused as an unexpected identity",
      f"{ID}, Identity keys, A stored key the rule refuses: If her record for the peer holds the refused key, she records the bundle's key, retires the refused one and establishes under known; {REC}, A contact she holds a record for is never a first contact ... a contact whose recorded key the identity-key rule refuses ... She records the new key, retires the refused one, and establishes under known")
def _():
    refused = IKC.MIXED[0]
    before = Known(Record.of([refused]))
    _, err, _, _ = establish(bob_bundle(), before)
    assert type(err) is records.UnexpectedIdentity, type(err).__name__
    after = Known(Record.of([BOB], [refused]))
    out, err, _, _ = establish(bob_bundle(), after)
    assert err is None and out.identity_key == BOB
    assert records.classify(BOB, after.record) == records.SAME
    rejects(records.classify, refused, after.record, exc=wire.InvalidIdentityKey)
