"""Pass 5. The sentences revision 1dd1746 adds to session-persistence.md,
session-establishment.md and message-format.md, and what the two new
persisted-state vector files do not pin.

- Stored curve public keys: which reader refuses each, and as what (SK-01 to
  SK-06).
- The initiator's own canonical check of a bundle (SK-07).
- Rejection: the format-by-format short-buffer/unknown-version overlap,
  the empty buffer, recognised-version truncation and long enough unknown
  versions (RJ-01).
- The Braid key pair's load check in tags 1 to 4 (BK-01).
- "Being inductive": every state the operations produce, up to and at each
  counter's ceiling, is one its reader accepts (IN-01, IN-02).
- ASM-05's statement about the derivation labels (TM-01).
"""

import hashlib
import random

import cases_curvekeys as CKC
import cases_persistence as PSC
import negative_cases as NC
from _casekit import accepts, put, registry, rejects
from tacenta_reader import constants as K
from tacenta_reader import curve25519, ratchet, spqr, wire
from tacenta_reader import persistence as P
from tacenta_reader import kem_double
from tacenta_reader.kem_double import byte_encode12

CASES, case = registry()
SP = "session-persistence.md"
SE = "session-establishment.md"
SCK = f"{SP} Session, Semantic rules, Stored curve public keys"
PRIME = K.CURVE25519_P
TOP = (PRIME - 1).to_bytes(32, "little")
NINE = (9).to_bytes(32, "little")
R = random.Random(20260911_5)
MAL, WV, INC = P.Malformed, P.WrongVersion, P.Inconsistent
IKB_SECRET = b"\x62" * 32   # PSC.IKB is x25519_public of this (cases_persistence.py)


def pub(tag):
    return curve25519.x25519_public(hashlib.sha256(b"pass5 %d" % tag).digest())


def refused_as(fn, arg, exc, needle="canonical"):
    """Refused as exactly `exc`, and for the stored-key rule, not another."""
    e = rejects(fn, arg, exc=P.PersistError)
    assert isinstance(e, exc), f"refused as {type(e).__name__}, not {exc.__name__}: {e}"
    assert needle in str(e), f"refused for another reason: {e}"


# ================================================================ ratchet state

@case("SK-01 the ratchet state's dhs_pub, a present dhr_pub and each stored key's dh: every other spelling (bit 255 set, value plus p, both) is refused as malformed, and p itself; p - 1 is accepted in every position; rk, the chain keys and the stored message keys are not curve keys and are not held to the rule",
      f"{SP} Semantic rules of the leaf formats, Ratchet state: and dhs_pub, dhr_pub when present, and every stored key's dh are each the canonical encoding of a curve public key; {SCK}: Refused as malformed, by a leaf format's ... own rules")
def _():
    base = PSC.BOB1.classical.clone()
    assert base.dhr is not None and base.skipped
    first = next(iter(base.skipped))

    def with_dh(s, dh):
        c = s.clone()
        (old_dh, n), v = first, c.skipped[first]
        c.skipped = {((dh, n) if k == first else k): val for k, val in c.skipped.items()}
        return c

    positions = {
        "dhs_pub": lambda s, k: setattr(s, "dhs_pub", k) or s,
        "dhr_pub": lambda s, k: setattr(s, "dhr", k) or s,
        "skipped dh": with_dh,
    }
    for name, place in positions.items():
        for key in (base.dhs_pub, NINE, TOP):
            accepts(P.ratchet_from_bytes, P.ratchet_to_bytes(place(base.clone(), key)))
            for sp in CKC.spellings(key) + ([PRIME.to_bytes(32, "little")] if key == NINE else []):
                refused_as(P.ratchet_from_bytes, P.ratchet_to_bytes(place(base.clone(), sp)), MAL)
    loose = base.clone()
    loose.rk, loose.cks, loose.ckr = b"\xff" * 32, PRIME.to_bytes(32, "little"), (PRIME | 1 << 255).to_bytes(32, "little")
    loose.skipped = {k: (b"\xff" * 32, at) for k, (_, at) in loose.skipped.items()}
    accepts(P.ratchet_from_bytes, P.ratchet_to_bytes(loose))


@case("SK-02 why the ratchet state's rule: inside the state a second spelling is a second identity; a header under the canonical key takes a Diffie-Hellman step against a re-spelled DHr, and misses the key stored under a re-spelled dh (refused as out of order where the original state returns that key)",
      f"{SCK}: Inside the ratchet state a second spelling gives one key a second identity: a header's dh is compared with DHr byte for byte, and a skipped key is found by its dh bytes (ratchet.md), so a message under the key would take a Diffie-Hellman step it should not, or miss the key stored for it")
def _():
    k1 = pub(1)

    def dh(header_dh):
        return b"\x11" * 32, pub(2), b"\x22" * 32

    b = ratchet.init_responder(b"\x01" * 32, pub(3))
    b, _, stepped = ratchet.receive(b, ratchet.Header(k1, 0, 2), dh)          # stores (k1, 0), (k1, 1); Nr = 3
    assert stepped and b.dhr == k1 and (k1, 1) in b.skipped
    _, mk, stepped = accepts(ratchet.receive, b, ratchet.Header(k1, 0, 1), dh)
    assert not stepped and mk == b.skipped[(k1, 1)][0]
    sp = CKC.spellings(k1)[0]
    moved = b.clone()
    moved.skipped = {((sp, n) if (d, n) == (k1, 1) else (d, n)): v for (d, n), v in moved.skipped.items()}
    rejects(ratchet.receive, moved, ratchet.Header(k1, 0, 1), dh, exc=ratchet.OutOfOrder)
    respelled = b.clone()
    respelled.dhr = sp
    assert ratchet.receive(b, ratchet.Header(k1, 0, 3), dh)[2] is False
    assert ratchet.receive(respelled, ratchet.Header(k1, 0, 3), dh)[2] is True
    for s in (moved, respelled):
        rejects(P.ratchet_from_bytes, P.ratchet_to_bytes(s), exc=MAL)      # and neither state is read back


@case("SK-03 a triple ratchet state or a session holding a re-spelled classical key is refused as malformed by the triple_state's reader, before the session's rules: dhs_pub (which would otherwise break the ratchet private key rule), dhr_pub and a stored dh; none is reported as inconsistent or non-canonical",
      f"{SCK}: A session whose triple_state holds such a key is refused as malformed, because the triple_state's own reader refuses it before the session's rules are reached. That includes a re-spelled dhs_pub")
def _():
    for party, braid, initiator in ((PSC.ALICE0, PSC.braid_state(1, epoch=1), True), (PSC.BOB1, PSC.braid_state(5, epoch=1), False)):
        sess = PSC.session_for(party, braid, initiator=initiator)
        if not initiator:
            accepts(P.session_from_bytes, P.session_to_bytes(sess)) if party is PSC.BOB0 else None
        c = party.classical
        variants = [("dhs_pub", CKC.spellings(c.dhs_pub)[0])]
        if c.dhr is not None:
            variants.append(("dhr", CKC.spellings(c.dhr)[-1]))
        for field, sp in variants:
            bad = c.clone()
            setattr(bad, field, sp)
            t = P.TripleState(bad, party.sparse)
            refused_as(P.triple_from_bytes, P.triple_to_bytes(t), MAL)
            s = PSC.session_for(party, braid, initiator=initiator, triple=t)
            refused_as(P.session_from_bytes, P.session_to_bytes(s), MAL)
    alice = PSC.session_for(PSC.ALICE0, PSC.braid_state(1, epoch=1))
    accepts(P.session_from_bytes, P.session_to_bytes(alice))


# ====================================================================== session

def _responder(**kw):
    return PSC.session_for(PSC.BOB0, PSC.braid_state(5, epoch=1), initiator=False, **kw)


def _initiator(**kw):
    return PSC.session_for(PSC.ALICE0, PSC.braid_state(1, epoch=1), **kw)


@case("SK-04 the session's our_identity_public, peer_identity_public, pending_initial's ephemeral_public and established_ephemeral's key: every other spelling is refused as inconsistent (not malformed, not non-canonical), with identity_ad built from the same bytes so that no other rule refuses it; p - 1 is accepted in each; kem_ciphertext is not held to the rule; a responder whose established_ephemeral is re-spelled (pass 4's probe, GAPS-4.md G4-02) is now refused",
      f"{SP} Session, Semantic rules: Every curve public key the session stores is canonical ...; The optional fields have their shape: ... established_ephemeral is a value DecodeEC accepts: 33 bytes, the curve byte first, then the canonical encoding of a curve public key; {SCK}: Refused as inconsistent")
def _():
    def ad(initiator, responder):
        return wire.encode_ec(initiator) + wire.encode_ec(responder)

    for key in (TOP,):
        accepts(P.session_from_bytes, P.session_to_bytes(_initiator(our_identity_public=key, identity_ad=ad(key, PSC.IKB))))
        accepts(P.session_from_bytes, P.session_to_bytes(_initiator(peer_identity_public=key, identity_ad=ad(PSC.IKA, key))))
        accepts(P.session_from_bytes, P.session_to_bytes(_initiator(pending_initial=P.PendingInitial(key, b"\xff" * 1568, 1, 2, 3))))
        accepts(P.session_from_bytes, P.session_to_bytes(_responder(established_ephemeral=b"\x05" + key)))
    for sp in CKC.spellings(PSC.IKA):
        refused_as(P.session_from_bytes, P.session_to_bytes(_initiator(our_identity_public=sp, identity_ad=ad(sp, PSC.IKB))), INC)
        refused_as(P.session_from_bytes, P.session_to_bytes(_responder(peer_identity_public=sp, identity_ad=ad(sp, PSC.IKB))), INC)
    for sp in CKC.spellings(PSC.IKB):
        refused_as(P.session_from_bytes, P.session_to_bytes(_initiator(peer_identity_public=sp, identity_ad=ad(PSC.IKA, sp))), INC)
        refused_as(P.session_from_bytes, P.session_to_bytes(_responder(our_identity_public=sp, identity_ad=ad(PSC.IKA, sp))), INC)
    for sp in CKC.spellings(PSC.EKA_PUB):
        refused_as(P.session_from_bytes, P.session_to_bytes(_initiator(pending_initial=P.PendingInitial(sp, PSC.rnd(1568), 1, 2, 3))), INC)
        refused_as(P.session_from_bytes, P.session_to_bytes(_responder(established_ephemeral=b"\x05" + sp)), INC)
    refused_as(P.session_from_bytes, P.session_to_bytes(_responder(established_ephemeral=b"\x05" + PRIME.to_bytes(32, "little"))), INC)


@case("SK-05 so a genuine repeat always matches: in every session the reader accepts, established_ephemeral and EncodeEC(peer_identity_public) are canonical, so the initial message that established it, which decoded, passes both comparisons; a session whose stored ephemeral is re-spelled no longer reaches the comparison",
      f"{SE} Receiving the initial message: So are established_ephemeral and peer_identity_public, in every session establishment builds and in every session a reader accepts ... so neither field of a genuine repeat can be spelled another way and still match")
def _():
    s = accepts(P.session_from_bytes, P.session_to_bytes(_responder()))
    genuine = wire.encode_initial(wire.InitialMessage(wire.encode_ec(s.peer_identity_public), s.established_ephemeral,
                                                      b"", 1, 0, 2, b"inner"))
    assert accepts(__import__("tacenta_reader.pqxdh", fromlist=["x"]).receive_repeated_initial, s, genuine, lambda rm: b"ok") == b"ok"
    for sp in CKC.spellings(PSC.EKA_PUB):
        rejects(P.session_from_bytes, P.session_to_bytes(_responder(established_ephemeral=b"\x05" + sp)), exc=INC)


@case("SK-06 the sparse ratchet state and the Braid hold no curve public key: a root key, chain keys and stored message keys with bit 255 set or at or above p are accepted, and so are a Braid's authenticator keys",
      f"{SCK}: The sparse ratchet state and the Braid hold no curve public key ... so neither format has such a rule")
def _():
    hi = (PRIME | 1 << 255).to_bytes(32, "little")
    s = PSC.BOB1.sparse.clone()
    s.rk = hi
    for pair in s.chains.values():
        for c in pair:
            if c is not None:
                c.ck = PRIME.to_bytes(32, "little")
    s.skipped = {k: hi for k in s.skipped}
    accepts(P.spqr_from_bytes, P.spqr_to_bytes(s))
    b = PSC.braid_state(0)
    b.auth_root, b.auth_mac = hi, b"\xff" * 32
    accepts(P.braid_from_bytes, P.braid_to_bytes(b))


@case("SK-07 no state the operations produce is refused: X25519 public keys are canonical (RFC 7748 section 5); live ratchet, sparse and triple states from honest exchanges, the sessions built on them, and a prekey store under an X25519 identity key are all read back",
      f"{SCK}: No state the operations produce is refused. Every curve public key a party's own operations store is canonical: ... a key computed from a private key is X25519's output, which RFC 7748, section 5, encodes as a value below p with bit 255 clear")
def _():
    for i in range(128):
        k = curve25519.x25519_public(hashlib.sha256(b"sweep %d" % i).digest())
        assert wire.is_canonical_curve_key(k) and not k[31] & 0x80
    for party in (PSC.ALICE0, PSC.BOB0, PSC.ALICE1, PSC.BOB1):
        accepts(P.triple_from_bytes, P.triple_to_bytes(P.TripleState(party.classical, party.sparse)))
    accepts(P.session_from_bytes, P.session_to_bytes(PSC.ALICE_S))
    accepts(P.session_from_bytes, P.session_to_bytes(PSC.BOB_S))
    accepts(P.prekey_store_from_bytes, P.prekey_store_to_bytes(
        PSC.store(identity_secret=hashlib.sha256(b"pass5 9").digest())))


@case("SK-08 the prekey store's identity_public: every other spelling is refused as malformed in v1, v2, v3 and v4 (in v4 after the re-encode check, which a re-spelled key passes); the canonical key of a real identity is accepted in all four; the secrets are not held to the rule. Pass 7: the sixth rule is checked after this one, so p - 1, which this rule accepts, is refused as incoherent instead, no identity having it as a public key (G7-06)",
      f"{SP} Prekey store, Semantic rules: identity_public is canonical ... they apply to all four versions; {SCK}: Refused as malformed, by ... the prekey store's own rules")
def _():
    base = PSC.store(seen=[(4, PSC.rnd(32))], identity_secret=IKB_SECRET)
    for version in (1, 2, 3, 4):
        def raw(p):
            return P.prekey_store_to_bytes(p) if version == 4 else PSC.legacy(p, version)
        accepts(P.prekey_store_from_bytes, raw(base))
        # p - 1 keeps the fifth rule and breaks the sixth, which is checked
        # after it: identities-and-devices.md, Verifying a signature, refuses
        # u = p - 1, so no signature verifies under it.
        refused_as(P.prekey_store_from_bytes, raw(PSC.store(seen=[(4, PSC.rnd(32))], identity_public=TOP)),
                   P.Incoherent, needle="verify")
        for sp in CKC.spellings(PSC.IKB) + [PRIME.to_bytes(32, "little")]:
            refused_as(P.prekey_store_from_bytes, raw(PSC.store(seen=[(4, PSC.rnd(32))], identity_public=sp)), MAL)
    accepts(P.prekey_store_from_bytes,
            P.prekey_store_to_bytes(PSC.store(signed_prekey_secret=b"\xff" * 32)))


@case("SK-09 the initiator refuses a bundle whose identity key, signed prekey or present one-time curve prekey is not canonical, before any agreement, even when the signed prekey's signature verifies over the re-spelled key and even when she names that very spelling as the identity she means to reach; p - 1 as the signed or one-time prekey passes her check; the decoder never returns such a bundle",
      f"{SE} Sending the initial message: She also refuses a bundle before encapsulating when ... its identity key, signed prekey or one-time curve prekey is not the canonical encoding of a curve public key ... A bundle the bundle decoder returned never holds such a key. The check is for a bundle that reaches her some other way")
def _():
    from dataclasses import replace
    z = b"\x5e" * 64
    base = NC.signed_bundle(True)
    accepts(wire.initiator_check_bundle, base)
    for sp in CKC.spellings(NC.SPK_PUB):
        b = replace(base, signed_prekey=sp, signed_prekey_signature=curve25519.xeddsa_sign(NC.IK_PRIV, wire.encode_ec(sp), z))
        rejects(wire.initiator_check_bundle, b, exc=wire.BundleRefused)
    for sp in CKC.spellings(NC.IK_PUB):
        rejects(wire.initiator_check_bundle, replace(base, identity_key=sp), sp, exc=wire.BundleRefused)
    for sp in CKC.spellings(NC.OPK_PUB):
        e = rejects(wire.initiator_check_bundle, replace(base, one_time_prekey=sp), exc=wire.BundleRefused)
        assert "canonical" in str(e)
    top = replace(base, signed_prekey=TOP, signed_prekey_signature=curve25519.xeddsa_sign(NC.IK_PRIV, wire.encode_ec(TOP), z),
                  one_time_prekey=TOP)
    accepts(wire.initiator_check_bundle, top)
    for field in ("identity_key", "signed_prekey", "one_time_prekey"):
        rejects(wire.decode_bundle, wire.encode_bundle(replace(base, **{field: CKC.spellings(getattr(base, field))[0]})),
                exc=wire.DecodeError)


# ==================================================================== Rejection

def _short_unknown_formats():
    return [
        ("ratchet state", P.ratchet_from_bytes, P.ratchet_to_bytes(PSC.BOB1.classical), 185, (0x00, 0x02, 0xFF)),
        ("sparse ratchet state", P.spqr_from_bytes, P.spqr_to_bytes(PSC.BOB1.sparse), 50, (0x00, 0x02, 0xFF)),
        ("triple ratchet state", P.triple_from_bytes, P.triple_to_bytes(P.TripleState(PSC.BOB1.classical, PSC.BOB1.sparse)), 9, (0x00, 0x02)),
        ("braid", P.braid_from_bytes, P.braid_to_bytes(PSC.braid_state(0)), 2, (0x00, 0x02)),
        ("session", P.session_from_bytes, P.session_to_bytes(PSC.ALICE_S), 5, (0x00, 0x02)),
        ("prekey store", P.prekey_store_from_bytes, P.prekey_store_to_bytes(PSC.STORE), 137, (0x00, 0x05, 0xFF)),
    ]


@case("RJ-01 a buffer too short for every recognised version of a persisted format whose first byte is unknown is refused, as either wrong version or short or malformed, never accepted and never as anything else, in each tabled format; with a known version the same buffer is short or malformed; the empty buffer has no version byte and is short; a long enough buffer with an unknown version is a wrong version",
      f"{SP} Rejection: A short buffer with an unknown version may be refused as either ... The affected persisted formats are")
def _():
    for name, reader, raw, fixed, unknown in _short_unknown_formats():
        e = rejects(reader, b"", exc=P.PersistError)
        assert isinstance(e, MAL), f"{name}: the empty buffer refused as {type(e).__name__}"
        for n in sorted({1, 2, fixed // 2, fixed - 1} - {0}):
            if n >= fixed:
                continue
            rejects(reader, raw[:n], exc=MAL)
            for v in unknown:
                e = rejects(reader, put(raw[:n], 0, v), exc=P.PersistError)
                assert isinstance(e, (WV, MAL)), f"{name}: refused as {type(e).__name__}"
        for v in unknown:
            rejects(reader, put(raw, 0, v), exc=WV)


# ======================================================================= Braid

def _kp(ek_vector, header, z=None):
    return (ek_vector + header + (z or PSC.rnd(32))).ljust(K.BRAID_KEY_PAIR_LEN, b"\x00")


@case("BK-01 the Braid's key_pair content clause is scoped (pass 7): this reader has no KEM key-pair layout, so in tags 1 to 4 it checks the field's 11,872-byte length, accepts every content, and conforms; a reader inside the scope, given a layout, refuses as malformed a key_pair whose H(ek_vector || rho) differs from the header's H(ek) or whose ek_vector fails the FIPS 203 modulus check, and accepts one that passes both; nothing else in key_pair is checked either way; encaps is checked for length only; a session carrying such a Braid follows its Braid",
      f"{SP} Semantic rules of the leaf formats, Braid: In tags 1 to 4, the header and ek_vector that key_pair holds pass the validation ...; **That clause is scoped to an implementation that knows the key pair's layout.** ... Such an implementation checks the field's length, accepts it, and conforms; {SP} Principles, Validated, not only parsed: A reader outside its scope checks that field's length and accepts it, and is conforming in doing so")
def _():
    good_ek = byte_encode12([R.randrange(K.MLKEM_Q) for _ in range(1024)])
    rho = PSC.rnd(32)
    header = rho + hashlib.sha3_256(good_ek + rho).digest()
    bad_ek = byte_encode12([K.MLKEM_Q] + [R.randrange(K.MLKEM_Q) for _ in range(1023)])
    bad_header = rho + hashlib.sha3_256(bad_ek + rho).digest()
    cases_ = {
        "good": (_kp(good_ek, header), None),
        "other padding": (_kp(good_ek, header, b"\xff" * 32)[:-1] + b"\x07", None),
        "hash differs": (_kp(good_ek, rho + bytes(32)), MAL),
        "ek_vector altered": (_kp(good_ek[:-1] + bytes([good_ek[-1] ^ 1]), header), MAL),
        "modulus fails, hash matches": (_kp(bad_ek, bad_header), MAL),
        "rho altered": (_kp(good_ek, bytes([rho[0] ^ 1]) + rho[1:] + header[32:]), MAL),
    }
    def with_kp(tag, kp):
        b = PSC.braid_state(tag)
        b.fields["key_pair"] = kp
        return P.braid_to_bytes(b)

    # Outside the scope, which is this reader's position: every content is
    # accepted, including one no reader inside the scope would take. A key_pair
    # of any other length is still refused, by the length rule every
    # implementation applies.
    assert P.KEY_PAIR_VIEW is None, "this reader has no KEM key-pair layout"
    for tag in (1, 2, 3, 4):
        for label, (kp, _exc) in cases_.items():
            accepts(P.braid_from_bytes, with_kp(tag, kp))
        accepts(P.braid_from_bytes, with_kp(tag, b"\x00" * K.BRAID_KEY_PAIR_LEN))
        for wrong in (K.BRAID_KEY_PAIR_LEN - 1, K.BRAID_KEY_PAIR_LEN + 1):
            refused_as(P.braid_from_bytes, with_kp(tag, b"\x00" * wrong), MAL, needle="key_pair")

    # Inside the scope, with a layout supplied. The clause is the same one, and
    # the states it refuses are refused as malformed, the leaf formats' kind.
    P.KEY_PAIR_VIEW = kem_double.key_pair_view
    try:
        for tag in (1, 2, 3, 4):
            for label, (kp, exc) in cases_.items():
                if exc is None:
                    accepts(P.braid_from_bytes, with_kp(tag, kp))
                else:
                    refused_as(P.braid_from_bytes, with_kp(tag, kp), exc, needle="ek_vector")
        braid = PSC.braid_state(1, epoch=1)
        braid.fields["key_pair"] = cases_["modulus fails, hash matches"][0]
        raw = P.session_to_bytes(PSC.session_for(PSC.ALICE0, braid))
        refused_as(P.session_from_bytes, raw, MAL, needle="ek_vector")
    finally:
        P.KEY_PAIR_VIEW = None
    # ... and outside it again, the same session is accepted.
    accepts(P.session_from_bytes, raw)

    # encaps is checked for length only, in or out of the scope.
    for tag in (7, 8, 9):
        b = PSC.braid_state(tag)
        b.fields["encaps"] = b"\xff" * K.BRAID_ENCAPS_LEN
        accepts(P.braid_from_bytes, P.braid_to_bytes(b))


# =================================================== the operations are inductive

def _roundtrip(reader, writer, s, where):
    raw = writer(s)
    try:
        back = reader(raw)
    except P.PersistError as e:
        raise AssertionError(f"{where}: a state the operations produced is refused: {type(e).__name__}: {e}")
    assert writer(back) == raw, f"{where}: read back to another state"


@case("IN-01 the classical ratchet is inductive up to its ceilings: from a new responder and from stored states with events at u32::MAX - 3 and ns and nr at u32::MAX - 3, random sends and receives (steps, skips, stored-key receives, returns to earlier keys, and refusals) leave after every accepted operation a state its reader accepts and writes back identically; the clock stops at u32::MAX - 1 and ns and nr reach u32::MAX",
      f"{SP} Principles: Being inductive constrains the operations ... the classical ratchet's received-message clock stops at u32::MAX - 1 rather than saturating into u32::MAX; ratchet.md Sending and receiving; Skipped keys")
def _():
    peers = [pub(100 + i) for i in range(4)]

    def dh(header_dh):
        h = hashlib.sha256(header_dh + bytes([R.getrandbits(8)])).digest()
        return h, curve25519.x25519_public(h), hashlib.sha256(h).digest()

    near = PSC.BOB1.classical.clone()
    near.events, near.ns, near.nr = K.MAX_EVENTS - 3, K.U32_MAX - 3, K.U32_MAX - 3
    near = accepts(P.ratchet_from_bytes, P.ratchet_to_bytes(near))
    starts = [ratchet.init_responder(b"\x02" * 32, pub(99)), near]
    seen = {"events": 0, "ns": 0, "nr": 0}
    s = near                                   # first, the sending chain to its ceiling: sends at ns = u32::MAX - 3 .. u32::MAX - 1
    for _ in range(3):
        s = accepts(ratchet.send, s)[0]
        _roundtrip(P.ratchet_from_bytes, P.ratchet_to_bytes, s, "send toward the ceiling")
    seen["ns"] = s.ns
    rejects(ratchet.send, s, exc=ratchet.ChainExhausted)
    starts[1] = s
    for start in starts:
        s = start
        for step in range(220):
            try:
                if s.cks is not None and R.random() < 0.35:
                    s = ratchet.send(s)[0]
                else:
                    if s.dhr is not None and R.random() < 0.7:
                        hk, pn = s.dhr, 0
                        n = max(0, min(K.U32_MAX, s.nr + R.choice((-2, -1, 0, 0, 1, 2, 3))))
                    else:
                        hk = R.choice(peers)
                        pn = s.nr + R.choice((0, 1, 2)) if s.ckr is not None else R.randrange(5)
                        n = R.randrange(3)
                    if s.skipped and R.random() < 0.15:
                        hk, n = R.choice(list(s.skipped))
                    s = ratchet.receive(s, ratchet.Header(hk, min(pn, K.U32_MAX), n), dh)[0]
            except ratchet.RatchetError:
                continue
            assert s.events <= K.MAX_EVENTS
            seen["events"] = max(seen["events"], s.events)
            seen["ns"], seen["nr"] = max(seen["ns"], s.ns), max(seen["nr"], s.nr)
            _roundtrip(P.ratchet_from_bytes, P.ratchet_to_bytes, s, f"classical step {step}")
    assert seen["events"] == K.MAX_EVENTS, seen
    assert seen["ns"] == K.U32_MAX and seen["nr"] == K.U32_MAX, seen


@case("IN-02 the sparse ratchet is inductive up to its ceilings: from new states and from a stored state at epoch u64::MAX - 4 with counters at u64::MAX - 3, random sends and receives with and without the agreement's secret leave after every accepted operation a state its reader accepts; the epoch reaches u64::MAX - 1 and never u64::MAX; a counter reaches u64::MAX",
      f"{SP} Principles: the sparse ratchet refuses the agreement output that would advance it to epoch u64::MAX ... with the counter-exhaustion error it already returns for a chain at the end of its range; sparse-pq-ratchet.md Sending; Receiving; Retiring old epochs")
def _():
    top = K.U64_MAX
    near = spqr.init(b"\x03" * 32, spqr.B2A)
    near.epoch = top - 4
    pair = near.chains.pop(0)
    near.chains = {top - 5: [spqr.Chain(b"\x05" * 32, top - 3), spqr.Chain(b"\x06" * 32, top - 3)],
                   top - 4: [spqr.Chain(pair[0].ck, top - 3), spqr.Chain(pair[1].ck, top - 3)]}
    near = accepts(P.spqr_from_bytes, P.spqr_to_bytes(near))
    reached = {"epoch": 0, "n": 0}
    for s in (spqr.init(b"\x04" * 32, spqr.A2B), spqr.init(b"\x04" * 32, spqr.B2A), near):
        for step in range(260):
            secret = (hashlib.sha256(b"%d" % step).digest(), s.epoch + 1) if R.random() < 0.3 else (None, None)
            e = R.choice(list(s.chains))
            try:
                if R.random() < 0.5:
                    s = spqr.send(s, e, *secret)[0]
                else:
                    chain = s.chains[e][1]
                    n = max(0, min(top, (chain.n if chain else 0) + R.choice((-1, 0, 1, 1, 2, 3))))
                    s = spqr.receive(s, e, n, *secret)[0]
            except spqr.SpqrError:
                continue
            assert s.epoch < top
            reached["epoch"] = max(reached["epoch"], s.epoch)
            reached["n"] = max([reached["n"]] + [c.n for p in s.chains.values() for c in p if c])
            _roundtrip(P.spqr_from_bytes, P.spqr_to_bytes, s, f"sparse step {step}")
    assert reached["epoch"] == top - 1 and reached["n"] == top, reached


# ============================================================ threat model text

@case("TM-01 the derivation labels are distinct, and prefix-free apart from two pairs: of the info strings and keys CONSTANTS.md gives, exactly two are proper prefixes of another, COMBINE_INFO of SPLIT_INFO and the sparse chain step's of its initialisation's. Pass 7: ASM-05 now names both pairs with their values, so which strings are registered no longer has to be taken from outside the specification (ADR-0006, point 7)",
      "threat-model/assumptions.md ASM-05: the derivation labels are the `info` strings and HMAC keys CONSTANTS.md gives under \"Derivation labels\", which carries every value. They are distinct, and prefix-free apart from exactly two pairs, registered here rather than left to a reader to notice")
def _():
    spqr_info = lambda sfx: K.SPQR_PROTOCOL_INFO + K.SPQR_SEPARATOR + sfx   # noqa: E731
    labels = {
        "RK_INFO": K.RK_INFO, "MK_INFO": K.MK_INFO, "SK_INFO": K.SK_INFO,
        "COMBINE_INFO": K.COMBINE_INFO, "SPLIT_INFO": K.SPLIT_INFO,
        "SPQR init": spqr_info(K.SPQR_CHAIN_START), "SPQR root": spqr_info(K.SPQR_ROOT), "SPQR chain": spqr_info(K.SPQR_CHAIN),
        "Braid SCKA Key": K.BRAID_PROTOCOL_INFO + K.BRAID_SCKA_KEY,
        "Braid Authenticator Update": K.BRAID_PROTOCOL_INFO + K.BRAID_AUTH_UPDATE,
        "Braid ekheader": K.BRAID_PROTOCOL_INFO + K.BRAID_EKHEADER,
        "Braid ciphertext": K.BRAID_PROTOCOL_INFO + K.BRAID_CIPHERTEXT,
        "LAST_RESORT_HANDSHAKE_LABEL": K.LAST_RESORT_HANDSHAKE_LABEL,
        "application signature": K.APP_SIGNATURE_PREFIX,
    }
    assert len(set(labels.values())) == len(labels)
    pairs = {(a, b) for a, x in labels.items() for b, y in labels.items() if a != b and y.startswith(x)}
    assert pairs == {("COMBINE_INFO", "SPLIT_INFO"), ("SPQR chain", "SPQR init")}, sorted(pairs)


@case("TM-02 REQ-AUTH-11 read against the protocol pages: on a live Triple Ratchet session every replay of a message already read is refused, on the chain it came from and after the receiver has left that classical chain; in the second case the classical rule alone would take a Diffie-Hellman step (the header's key is no longer DHr), and it is the sparse half's out-of-order refusal, which REQ-AUTH-11 does not list, that refuses it (GAPS-5.md G5-10)",
      "security-properties/authentication.md REQ-AUTH-11: A session accepts each ratchet message at most once; ratchet.md Sending and receiving: if the header's ratchet key differs from DHr ... take a DH ratchet step; sparse-pq-ratchet.md Receiving: refused as out of order (OutOfOrder); triple-ratchet.md Sending and receiving")
def _():
    import cases_braid as BRC
    from tacenta_reader import triple
    alice, bob, ag_a, ag_b = BRC.session_pair()
    alice, m1 = triple.encrypt(alice, ag_a, b"one")
    alice, m2 = triple.encrypt(alice, ag_a, b"two")
    bob, _ = triple.decrypt(bob, ag_b, m1, BRC.fresh())
    bob, _ = triple.decrypt(bob, ag_b, m2, BRC.fresh())
    rejects(triple.decrypt, bob, ag_b, m1, BRC.fresh(), exc=Exception)
    bob, r1 = triple.encrypt(bob, ag_b, b"reply")
    alice, _ = triple.decrypt(alice, ag_a, r1, BRC.fresh())
    alice, m3 = triple.encrypt(alice, ag_a, b"three")
    bob, got = triple.decrypt(bob, ag_b, m3, BRC.fresh())
    assert got == b"three"
    for m in (m1, m2):
        h, _ = wire.decode_ratchet_message(m)
        assert h.dh != bob.classical.dhr, "the receiver has left the chain the replay came from"
        rejects(triple.decrypt, bob, ag_b, m, BRC.fresh(), exc=Exception)
        rejects(spqr.receive, bob.sparse, h.pq_epoch, h.pq_n, exc=(spqr.OutOfOrder, spqr.NoChain))
        stepped = ratchet.receive(bob.classical, ratchet.Header(h.dh, h.pn, h.n),
                                  lambda d: (b"\x01" * 32, pub(7), b"\x02" * 32))[2]
        assert stepped, "the classical half alone takes a Diffie-Hellman step for the replay"
