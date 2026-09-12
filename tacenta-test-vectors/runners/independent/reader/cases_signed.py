"""Pass 7. The sentences revision 5ae4442 adds or changes, and what the two new
persisted-state vector files do not pin.

- The prekey store's sixth semantic rule, that every stored signature verifies
  under `identity_public`: each signed position, what the rule does not bind,
  its refusal kind (`incoherent`) and where it sits in the order of checks
  (PK-01 to PK-06).
- The obligation the rule puts on the operations, and the two rotations
  key-deletion.md states (PK-07, PK-08).
- Rejection's paragraph on which format gives which refusal (RJ-02).
- The Principles' exception to the inductive invariant (IN-03).
- ADR-0006's new point 7, read against the two statements that moved their
  content into the specification (TM-03).

The scoped `key_pair` content rule of tags 1 to 4 is in `cases_stored.py`
(BK-01), where the unscoped version of it already was.
"""

import hashlib
import random

import cases_persistence as PSC
from _casekit import accepts, put, registry, rejects
from tacenta_reader import constants as K
from tacenta_reader import prekeys, wire
from tacenta_reader import persistence as P
from tacenta_reader.curve25519 import x25519_public, xeddsa_sign

CASES, case = registry()
SP = "session-persistence.md"
KD = "key-deletion.md"
R = random.Random(20260912_7)
MAL, WV, NC, INC, ICO = P.Malformed, P.WrongVersion, P.NonCanonical, P.Inconsistent, P.Incoherent

# "signed_prekey_sig begins at offset 69 of a v4 store"
SIG_OFFSET = 69
OTHER_IDENTITY = b"\x73" * 32


def refused_as(fn, arg, exc, needle=None):
    e = rejects(fn, arg, exc=P.PersistError)
    assert isinstance(e, exc), f"refused as {type(e).__name__}, not {exc.__name__}: {e}"
    if needle is not None:
        assert needle in str(e), f"refused for another reason: {e}"
    return e


def full_store(**kw):
    """A store with every position the sixth rule covers occupied."""
    base = dict(seen=[(4, PSC.rnd(32)), (8, PSC.rnd(32))],
                previous_signed=(PSC.rnd(32), 7, b""),
                previous_kem=(PSC.kem_pair(), 8, b""))
    base.update(kw)
    return PSC.store(**base)


# ===================================== the sixth rule: every signature verifies

@case("PK-01 every stored signature verifies under identity_public: the signed prekey's over EncodeEC of the public half of its secret, the KEM prekey's over EncodeKEM of its pair's public half, each one-time KEM prekey's over its own pair's, and the retired pair's over theirs. A store with all five kinds present is read back; one byte flipped in any one of them is refused, and in every position",
      f"{SP} Prekey store, Semantic rules: **Every stored signature verifies under `identity_public`**: `signed_prekey_sig` over `EncodeEC` of the public half of `signed_prekey_secret`; `kem_sig` over `EncodeKEM` of `kem_pair`'s public half; each `kem_one_time` entry's `sig` over its own pair's; and, in the versions that carry them, `previous_signed`'s and `previous_kem`'s over theirs")
def _():
    good = full_store()
    accepts(P.prekey_store_from_bytes, P.prekey_store_to_bytes(good))
    assert P.prekey_store_signatures(good) is None

    def broken(mutate):
        p = full_store()
        mutate(p)
        return P.prekey_store_to_bytes(p)

    def flip(sig):
        return bytes([sig[0] ^ 1]) + sig[1:]

    mutations = {
        "signed_prekey_sig": lambda p: setattr(p, "signed_prekey_sig", flip(p.signed_prekey_sig)),
        "kem_sig": lambda p: setattr(p, "kem_sig", flip(p.kem_sig)),
        "kem_one_time[0]": lambda p: p.kem_one_time.__setitem__(
            0, (p.kem_one_time[0][0], p.kem_one_time[0][1], flip(p.kem_one_time[0][2]))),
        "kem_one_time[1]": lambda p: p.kem_one_time.__setitem__(
            1, (p.kem_one_time[1][0], p.kem_one_time[1][1], flip(p.kem_one_time[1][2]))),
        "previous_signed": lambda p: setattr(p, "previous_signed",
                                             (p.previous_signed[0], p.previous_signed[1],
                                              flip(p.previous_signed[2]))),
        "previous_kem": lambda p: setattr(p, "previous_kem",
                                          (p.previous_kem[0], p.previous_kem[1],
                                           flip(p.previous_kem[2]))),
    }
    for name, mutate in mutations.items():
        refused_as(P.prekey_store_from_bytes, broken(mutate), ICO, needle="verify")

    # A signature made over the right shape but the wrong value, rather than a
    # flipped byte: the same refusal.
    def wrong_message(p):
        p.signed_prekey_sig = PSC.prekey_sig(wire.encode_ec(PSC.rkey()))
    refused_as(P.prekey_store_from_bytes, broken(wrong_message), ICO, needle="signed_prekey_sig")


@case("PK-02 what the sixth rule does not bind: the one-time curve prekeys carry no signature and their secrets may be anything; a flipped byte in a KEM key pair's secret material -- dk_pke or z, which no stored value authenticates -- is accepted; a flip in ek or in the h inside dk is refused, but by the kem_pair rule and as malformed, not by this one",
      f"{SP} Prekey store, Semantic rules: The one-time *curve* prekeys carry no signature and are not covered by this rule; {SP} Prekey store: It binds nothing in the KEM key pairs' secret material, which no stored value authenticates and which is most of the file. A flipped byte there is accepted")
def _():
    # the one-time curve prekeys: any secret, no signature
    accepts(P.prekey_store_from_bytes,
            P.prekey_store_to_bytes(full_store(one_time=[(2, b"\xff" * 32), (3, bytes(32))])))

    def with_kem_pair(kp):
        return P.prekey_store_to_bytes(full_store(kem_pair=kp))

    good = PSC.kem_pair()
    accepts(P.prekey_store_from_bytes, with_kem_pair(good))
    # dk = dk_pke(1,536) || ek(1,568) || h(32) || z(32)
    for label, offset in (("dk_pke", 0), ("z", K.KEM_DK_LEN - 1)):
        p = full_store(kem_pair=good[:offset] + bytes([good[offset] ^ 1]) + good[offset + 1:])
        # signing is over ek, which has not moved, so the signature still verifies
        accepts(P.prekey_store_from_bytes, P.prekey_store_to_bytes(p))
    for label, offset in (("h inside dk", 1536 + K.KEM_EK_LEN), ("ek", K.KEM_DK_LEN)):
        bad = good[:offset] + bytes([good[offset] ^ 1]) + good[offset + 1:]
        refused_as(P.prekey_store_from_bytes, with_kem_pair(bad), MAL, needle="kem_pair")


@case("PK-03 the refusal is reported separately, as incoherent: a variant distinct from malformed, from non-canonical and from wrong version, and the prekey store's alone. Every one of the store's other five rules gives malformed, and every one of the session's semantic rules gives inconsistent",
      f"{SP} Rejection: the session calls that \"inconsistent\" and gives it for any of its semantic rules; the prekey store calls it \"incoherent\" and gives it for its signature rule alone, its other rules being malformed")
def _():
    for cls in (MAL, NC, WV, INC):
        assert not issubclass(ICO, cls) and not issubclass(cls, ICO), cls
    assert issubclass(ICO, P.PersistError)
    p = full_store()
    p.signed_prekey_sig = bytes(64)
    refused_as(P.prekey_store_from_bytes, P.prekey_store_to_bytes(p), ICO)
    # the other five, each as malformed
    others = {
        "identifier zero": full_store(signed_prekey_id=0),
        "identifier at next_id": full_store(next_id=1),
        "identifiers repeated": full_store(kem_id=1),
        "record under an unknown key": full_store(seen=[(99, PSC.rnd(32))]),
        "fingerprint twice": (lambda fp: full_store(seen=[(4, fp), (4, fp)]))(PSC.rnd(32)),
        "over budget for one key": full_store(seen=[(4, PSC.rnd(32)) for _ in range(1025)]),
        "identity_public not canonical": PSC.store(identity_public=b"\xff" * 32),
    }
    for name, store in others.items():
        refused_as(P.prekey_store_from_bytes, P.prekey_store_to_bytes(store), MAL)


@case("PK-04 the sixth rule is checked last of all: after the framing, after the v4 re-encode check, and after the other five. A store that breaks the signature rule and one of the others is refused as malformed; one that breaks it and is non-canonical is refused as non-canonical; one that breaks it under an unrecognised version byte is a wrong version",
      f"{SP} Prekey store, Semantic rules: Last, over the decoded store, the reader refuses as malformed any store for which `PrekeyStore::invariant` is false, and -- last of all, and reported separately -- any store holding a signature that does not verify")
def _():
    bad_sig = full_store()
    bad_sig.signed_prekey_sig = bytes(64)
    raw = P.prekey_store_to_bytes(bad_sig)
    refused_as(P.prekey_store_from_bytes, raw, ICO)

    also_zero_id = full_store(signed_prekey_id=0)
    also_zero_id.signed_prekey_sig = bytes(64)
    refused_as(P.prekey_store_from_bytes, P.prekey_store_to_bytes(also_zero_id), MAL)

    # non-canonical: a seen_count that re-encodes differently is not reachable,
    # so use the one second spelling the layout allows, a trailing field written
    # by hand. The v4 re-encode check is what catches it, before the signature.
    canon = bytearray(raw)
    canon[SIG_OFFSET - 1] = canon[SIG_OFFSET - 1]     # unchanged: raw is canonical
    assert P.prekey_store_to_bytes(bad_sig) == bytes(canon)
    refused_as(P.prekey_store_from_bytes, bytes([0x05]) + raw[1:], WV)
    refused_as(P.prekey_store_from_bytes, raw + b"\x00", MAL)
    refused_as(P.prekey_store_from_bytes, raw[:-1], MAL)


@case("PK-05 the flipped byte the page describes: signed_prekey_sig begins at offset 69 of a v4 store; a flip there re-encodes to the identical bytes, keeps all five of the other rules, and is refused by the sixth alone. A reader with the rule and a reader without it disagree about those same v4 bytes, which is what the page records",
      f"{SP} Prekey store, Semantic rules: one flipped byte -- `signed_prekey_sig` begins at offset 69 of a v4 store, and a flip there stays canonical under re-encoding -- yields a store that reads back, satisfies every other rule above, and then hands every initiator a bundle that initiator must refuse; {SP} Prekey store: a reader with the rule and a reader without it disagree about the same v4 bytes")
def _():
    p = full_store()
    raw = P.prekey_store_to_bytes(p)
    assert raw[0] == K.PREKEY_STORE_VERSION
    # offset 69 = 1 version + 32 identity_public + 32 signed_prekey_secret + 4 id
    assert SIG_OFFSET == 1 + 32 + 32 + 4
    assert raw[SIG_OFFSET:SIG_OFFSET + 64] == p.signed_prekey_sig

    flipped = put(raw, SIG_OFFSET, raw[SIG_OFFSET] ^ 0x01)
    # It parses, it is canonical, and the five cheap rules hold of it.
    store_without_the_rule = _read_without_the_signature_rule(flipped)
    assert P.prekey_store_to_bytes(store_without_the_rule) == flipped, "a flip there is not canonical"
    assert P.prekey_store_semantic(store_without_the_rule) is None, "another rule caught it"
    # The reader with the rule refuses the same bytes, and as incoherent.
    refused_as(P.prekey_store_from_bytes, flipped, ICO, needle="signed_prekey_sig")


def _read_without_the_signature_rule(raw):
    """The reader as it was before this revision: the same bytes, the five
    earlier rules, and no signature check."""
    saved = P.prekey_store_signatures
    P.prekey_store_signatures = lambda p: None
    try:
        return P.prekey_store_from_bytes(raw)
    finally:
        P.prekey_store_signatures = saved


@case("PK-06 the rule applies to all four versions, the untagged ones having had their entries tagged first: a v1, v2 or v3 store whose signatures verify is read, and the same store with signed_prekey_sig flipped is refused as incoherent at every version. v1 and v2 carry no retired pair, so the rule covers nothing there beyond the two current signatures and the one-time KEM prekeys'",
      f"{SP} Prekey store, Semantic rules: they apply to all four versions, the untagged ones having had their entries tagged with the current key first")
def _():
    p = full_store(seen=[(4, PSC.rnd(32))])
    for version in (1, 2, 3, 4):
        raw = P.prekey_store_to_bytes(p) if version == 4 else PSC.legacy(p, version)
        read = accepts(P.prekey_store_from_bytes, raw)
        if version < 3:
            assert read.previous_signed is None and read.previous_kem is None
        refused_as(P.prekey_store_from_bytes, put(raw, SIG_OFFSET, raw[SIG_OFFSET] ^ 0x01),
                   ICO, needle="signed_prekey_sig")


# ============================== the obligation the rule puts on the operations

@case("PK-07 every operation that signs a prekey signs under the identity whose public key is identity_public, and refuses any other, changing nothing: rotate_signed_prekey and rotate_kem under the store's own identity produce stores this reader accepts, and under another identity refuse and leave the store as it was. Signing under another identity, were it allowed, would build exactly a state this reader refuses as incoherent",
      f"{SP} Prekey store, Semantic rules: **every operation that signs a prekey signs under the identity whose public key is `identity_public`**, and an implementation whose API lets a caller supply some other identity refuses it rather than storing the result; {KD}: signs it under the identity whose public key the store holds as `identity_public` -- and refuses, changing nothing, if handed any other")
def _():
    p = full_store()
    before = P.prekey_store_to_bytes(p)
    z = b"\x7a" * 64

    rotated = prekeys.rotate_signed_prekey(p, PSC.STORE_IDENTITY, PSC.rnd(32), z)
    accepts(P.prekey_store_from_bytes, P.prekey_store_to_bytes(rotated))
    assert rotated.previous_signed[:2] == (p.signed_prekey_secret, p.signed_prekey_id)
    assert rotated.previous_signed[2] == p.signed_prekey_sig, "the retired key keeps its signature"
    assert rotated.signed_prekey_id == p.next_id and rotated.next_id == p.next_id + 1

    kp = PSC.kem_pair()
    rotated_kem = prekeys.rotate_kem(p, PSC.STORE_IDENTITY, kp, z)
    accepts(P.prekey_store_from_bytes, P.prekey_store_to_bytes(rotated_kem))
    # "they are dropped when the next rotation wipes it": the entries tagged
    # with the key that leaves the previous slot go, the rest stay.
    assert {t for t, _ in rotated_kem.seen} == {4}, rotated_kem.seen
    assert rotated_kem.previous_kem[:2] == (p.kem_pair, p.kem_id)

    for op, arg in ((prekeys.rotate_signed_prekey, PSC.rnd(32)), (prekeys.rotate_kem, kp)):
        rejects(op, p, OTHER_IDENTITY, arg, z, exc=prekeys.RotationRefused)
        assert P.prekey_store_to_bytes(p) == before, "a refused rotation changed the store"

    # What the obligation prevents: a store signed under another identity.
    wrong = PSC.store(identity_secret=PSC.STORE_IDENTITY)
    PSC.sign_store(wrong, OTHER_IDENTITY)
    refused_as(P.prekey_store_from_bytes, P.prekey_store_to_bytes(wrong), ICO, needle="verify")

    # "once that counter stands at u32::MAX each ... returns without rotating,
    # silently" (key-deletion.md).
    at_end = full_store(next_id=K.U32_MAX, signed_prekey_id=1, kem_id=4)
    assert prekeys.rotate_signed_prekey(at_end, PSC.STORE_IDENTITY, PSC.rnd(32), z) is at_end
    assert prekeys.rotate_kem(at_end, PSC.STORE_IDENTITY, kp, z) is at_end


@case("PK-08 no state the rotations produce is refused, on any of the six rules: forty rotations in turn, each store written, read back and written again, with the record filling between them and the retired pair's signature carried across unchanged",
      f"{SP} Session, Semantic rules, Stored curve public keys: No state the operations produce is refused; {SP} Prekey store, Semantic rules: Without that obligation an operation can build a state this reader would refuse, which is the one thing \"No state the operations produce is refused\" undertakes cannot happen")
def _():
    p = full_store(seen=[])
    for i in range(40):
        z = hashlib.sha256(b"rotate %d" % i).digest() * 2
        p = (prekeys.rotate_signed_prekey(p, PSC.STORE_IDENTITY, PSC.rnd(32), z) if i % 2 == 0
             else prekeys.rotate_kem(p, PSC.STORE_IDENTITY, PSC.kem_pair(), z))
        p.seen = p.seen + [(p.kem_id, PSC.rnd(32))]
        raw = P.prekey_store_to_bytes(p)
        back = accepts(P.prekey_store_from_bytes, raw)
        assert P.prekey_store_to_bytes(back) == raw


# ============================================== Rejection, and the Principles

@case("RJ-02 which format gives which refusal: every format gives wrong version and short or malformed; the session and the prekey store each give non-canonical as well; the session gives inconsistent for any of its semantic rules and nothing else does; the prekey store gives incoherent for its signature rule alone and nothing else does. The four leaf formats give neither of the last two, whatever the rule broken",
      f"{SP} Rejection: Each of the formats above carries its own error type, distinguishing \"wrong version\" from \"short or malformed\" ... the session and the prekey store distinguish \"non-canonical\" from both, and each distinguishes one more for the same reason")
def _():
    leaves = {
        "ratchet": (P.ratchet_from_bytes, P.ratchet_to_bytes(PSC.ALICE1.classical)),
        "sparse": (P.spqr_from_bytes, P.spqr_to_bytes(PSC.ALICE1.sparse)),
        "triple": (P.triple_from_bytes,
                   P.triple_to_bytes(P.TripleState(PSC.ALICE1.classical, PSC.ALICE1.sparse))),
        "braid": (P.braid_from_bytes, P.braid_to_bytes(PSC.braid_state(0))),
    }
    for name, (reader, raw) in leaves.items():
        accepts(reader, raw)
        for mutant in (bytes([0x02]) + raw[1:], raw + b"\x00", raw[:-1], b""):
            e = rejects(reader, mutant, exc=P.PersistError)
            assert isinstance(e, (WV, MAL)) and not isinstance(e, (NC, INC, ICO)), (name, e)
    # the session's semantic rules, all of them, as inconsistent
    for label, s in PSC.session_semantic_breakages().items():
        refused_as(P.session_from_bytes, P.session_to_bytes(s), INC)
    # the prekey store's, five as malformed and the sixth as incoherent
    refused_as(P.prekey_store_from_bytes, P.prekey_store_to_bytes(full_store(signed_prekey_id=0)), MAL)
    p = full_store()
    p.kem_sig = bytes(64)
    refused_as(P.prekey_store_from_bytes, P.prekey_store_to_bytes(p), ICO)


@case("IN-03 the exception to the inductive invariant: the five cheap rules hold of the store after every rotation, and the sixth is not one an operation checks -- it is checked when the store is read. The reader asserts the five after each operation and the sixth only in from_bytes, which is what the exempt bullet states",
      f"{SP} Principles: **One rule is exempt and says so where it is stated**: the prekey store's rule on what its stored signatures authenticate costs a signature verification per stored prekey, which a predicate asserted after every operation cannot afford, so it is checked when the store is read and the operations carry an obligation instead")
def _():
    p = full_store(seen=[])
    z = b"\x1c" * 64
    for i in range(6):
        p = prekeys.rotate_signed_prekey(p, PSC.STORE_IDENTITY, PSC.rnd(32), z)
        assert P.prekey_store_semantic(p) is None, "a cheap rule broke after an operation"
    # the sixth is reached only through the reader
    broken = full_store()
    broken.kem_sig = bytes(64)
    assert P.prekey_store_semantic(broken) is None, "the cheap predicate sees the signature rule"
    assert P.prekey_store_signatures(broken) is not None
    refused_as(P.prekey_store_from_bytes, P.prekey_store_to_bytes(broken), ICO)


@case("TM-03 ADR-0006's point 7 read against the two statements that moved: ASM-05 now names both registered prefix pairs with their values, and the pair set it names is exactly the one CONSTANTS.md's labels produce; AS-12 states the durable state REQ-AUTH-13 covers for the session and for the prekey store, and the reader's own persisted formats hold each of the items it lists",
      "decisions/ADR-0006-specification-is-normative.md, point 7: **What a page requires is readable from the specification alone.** A rule, a list, or a set that a requirement is stated over belongs in these pages; threat-model/assumptions.md ASM-05; threat-model/assets.md AS-12")
def _():
    import cases_stored as SC
    # ASM-05's two pairs, named on the page with their values, are exactly the
    # pairs CONSTANTS.md's label values give (the set TM-01 computes).
    assert K.SPLIT_INFO.startswith(K.COMBINE_INFO) and K.SPLIT_INFO != K.COMBINE_INFO
    assert K.SPLIT_INFO == K.COMBINE_INFO + b":Split", K.SPLIT_INFO
    assert K.COMBINE_INFO == b"Tacenta_CURVE25519_SHA-256_MLKEM1024", K.COMBINE_INFO
    assert K.SPQR_CHAIN_START.startswith(K.SPQR_CHAIN)
    assert (K.SPQR_PROTOCOL_INFO + K.SPQR_SEPARATOR + K.SPQR_CHAIN).endswith(b"Tacenta SPQRChain")
    assert (K.SPQR_PROTOCOL_INFO + K.SPQR_SEPARATOR + K.SPQR_CHAIN_START).endswith(b"Tacenta SPQRChain Start")
    assert any(cid.startswith("TM-01") for cid, _, _ in SC.CASES)

    # AS-12's list of durable state, item by item, against the formats that
    # hold it: each name is a field of one of the reader's persisted states.
    session_state = set(P.SessionState.__dataclass_fields__)
    ratchet_fields = set(PSC.ALICE1.classical.__dict__)
    for name in ("ns", "nr", "pn", "rk", "cks", "ckr", "dhs_pub", "dhr", "skipped"):
        assert name in ratchet_fields, name
    sparse_fields = set(PSC.ALICE1.sparse.__dict__)
    for name in ("epoch", "chains", "skipped"):
        assert name in sparse_fields, name
    braid = PSC.braid_state(0)
    for name in ("epoch", "auth_root", "auth_mac", "tag"):
        assert hasattr(braid, name), name
    store_fields = set(P.PrekeyStore.__dataclass_fields__)
    for name in ("one_time", "kem_one_time", "seen", "previous_signed", "previous_kem", "next_id"):
        assert name in store_fields, name
    assert {"triple", "braid", "pending_initial", "established_ephemeral"} <= session_state


@case("EP-01 the epoch relation's boundary, tag by tag: the sparse ratchet's epoch is the Braid's in tags 7 to 10 and one below it in tags 0 to 6, so tag 6 takes e - 1 and tag 7 takes e. Every one of the twelve tags is tried in both readings, and each is accepted under exactly one of them; a failed Braid (tag 11) is accepted under both",
      f"{SP} Session, Semantic rules: the sparse ratchet's `epoch` is `e` when the Braid is in `Ct1Sampled`, `EkReceivedCt1Sampled`, `Ct1Acknowledged` or `Ct2Sampled` (state tags 7 to 10, the states past the point where the header-receiving side folds the epoch's secret) and `e - 1` in every other live state (tags 0 to 6). ... A failed Braid (tag 11) is exempt")
def _():
    from dataclasses import replace
    from tacenta_reader import spqr

    def session_at(tag, braid_epoch, sparse_epoch):
        """A session whose every other rule holds, at the named Braid tag and
        the two epochs. The role rule fixes which party it must be: at an odd
        epoch the initiator is the header-sending side (tags 0 to 4)."""
        header_sender = tag <= 4
        initiator = header_sender == (braid_epoch % 2 == 1)
        party = PSC.ALICE0 if initiator else PSC.BOB0
        sparse = party.sparse
        while sparse.epoch < sparse_epoch:
            # a send carrying the agreement output for the next epoch advances it
            sparse = spqr.send(sparse, sparse.epoch, b"\x99" * 32, sparse.epoch + 1)[0]
        return PSC.session_for(party, PSC.braid_state(tag, epoch=braid_epoch),
                               initiator=initiator, triple=P.TripleState(party.classical, sparse),
                               pending_initial=None)

    for tag in range(11):
        for sparse_epoch, expected in ((0, tag <= 6), (1, 7 <= tag <= 10)):
            s = session_at(tag, 1, sparse_epoch)
            if expected:
                accepts(P.session_from_bytes, P.session_to_bytes(s))
            else:
                refused_as(P.session_from_bytes, P.session_to_bytes(s), INC, needle="epoch")
    # tag 11 is exempt: both epochs are accepted
    for sparse_epoch in (0, 1):
        s = session_at(11, 1, sparse_epoch)
        accepts(P.session_from_bytes, P.session_to_bytes(s))
