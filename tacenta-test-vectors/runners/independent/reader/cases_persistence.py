"""session-persistence.md formats: round trips and refusals derived from the
page. No vector exists for any persisted format, so every case here checks
this reader's reading of the text against itself."""

import hashlib
import random
from dataclasses import replace

from _casekit import accepts, put, registry, rejects
from tacenta_reader import constants as K
from tacenta_reader import erasure, ratchet, spqr, triple, wire
from tacenta_reader import persistence as P
from tacenta_reader.curve25519 import x25519_public

CASES, case = registry()
SP = "session-persistence.md"
R = random.Random(424242)
MAL, WV, INC = P.Malformed, P.WrongVersion, P.Inconsistent


def rnd(n):
    return bytes(R.getrandbits(8) for _ in range(n))


# ------------------------------------------------------------ live fixtures

IKA = x25519_public(b"\x61" * 32)
IKB = x25519_public(b"\x62" * 32)
AD = wire.encode_ec(IKA) + wire.encode_ec(IKB)
SK = bytes(range(10, 42))
SPK_PRIV = b"\x5b" * 32
SPK_PUB = x25519_public(SPK_PRIV)
A_PRIV = b"\xa0" * 32
EKA_PUB = x25519_public(b"\xee" * 32)
NULL = triple.NullAgreement()
_n = [0]


def _fresh():
    _n[0] += 1
    return (1000 + _n[0]).to_bytes(4, "big") * 8


def _start():
    return (triple.init_initiator(SK, AD, A_PRIV, SPK_PUB, None),
            triple.init_responder(SK, AD, SPK_PRIV, None))


def _exchanged():
    alice, bob = _start()
    msgs = []
    for i in range(3):
        alice, m = triple.encrypt(alice, NULL, b"a%d" % i)
        msgs.append(m)
    bob, _ = triple.decrypt(bob, NULL, msgs[2], _fresh())
    replies = []
    for i in range(3):
        bob, m = triple.encrypt(bob, NULL, b"b%d" % i)
        replies.append(m)
    alice, _ = triple.decrypt(alice, NULL, replies[2], _fresh())
    alice, m = triple.encrypt(alice, NULL, b"c")
    bob, _ = triple.decrypt(bob, NULL, m, _fresh())
    return alice, bob


ALICE0, BOB0 = _start()
ALICE1, BOB1 = _exchanged()


# ============================================================ ratchet state

@case("PS-01 ratchet state round trip: fresh initiator, fresh responder, and live states with skipped keys in store order",
      f"{SP} Ratchet state: ratchet_state = version(1) || dhs_pub(32) || ... || skipped[skipped_count]")
def _():
    for s in (ALICE0.classical, BOB0.classical, ALICE1.classical, BOB1.classical):
        raw = P.ratchet_to_bytes(s)
        assert len(raw) == 185 + 72 * len(s.skipped)
        back = accepts(P.ratchet_from_bytes, raw)
        assert back == s and list(back.skipped) == list(s.skipped) and P.ratchet_to_bytes(back) == raw
    assert BOB1.classical.skipped and ALICE1.classical.skipped


@case("PS-02 ratchet state: wrong version is its own kind; every truncation and a trailing byte are malformed",
      f"{SP} Rejection: an unrecognised version, a buffer too short for its fixed fields ..., and trailing bytes")
def _():
    raw = P.ratchet_to_bytes(BOB1.classical)
    for v in (0x00, 0x02, 0xFF):
        rejects(P.ratchet_from_bytes, put(raw, 0, v), exc=WV)
    for n in range(0, len(raw)):
        rejects(P.ratchet_from_bytes, raw[:n], exc=(MAL, WV) if n == 0 else MAL)
    rejects(P.ratchet_from_bytes, raw + b"\x00", exc=MAL)


@case("PS-03 ratchet state: presence tag outside 0x00/0x01, an absent key not zeroed, an unknown LabelSet tag",
      f"{SP} Ratchet state: a one-byte presence tag (0x00 absent, 0x01 present) followed by its full 32-byte width regardless, zeroed when absent; labels 0x00 today")
def _():
    raw = P.ratchet_to_bytes(BOB0.classical)            # dhr absent, cks absent, ckr absent
    rejects(P.ratchet_from_bytes, put(raw, 33, 0x02), exc=MAL)
    rejects(P.ratchet_from_bytes, put(raw, 40, 0x01), exc=MAL)
    rejects(P.ratchet_from_bytes, put(raw, 98, 0xFF), exc=MAL)
    rejects(P.ratchet_from_bytes, put(raw, 180, 0x01), exc=MAL)


def _rs(**kw):
    s = BOB1.classical.clone()
    for k, v in kw.items():
        setattr(s, k, v)
    return P.ratchet_to_bytes(s)


@case("PS-04 ratchet state semantic rules: store bound, events below u32::MAX, stored_at not after events, no repeated (dh, n), ckr only with cks and dhr",
      f"{SP} Semantic rules of the leaf formats: Ratchet state")
def _():
    s = BOB1.classical
    full = {(rnd(32), i): (rnd(32), 0) for i in range(K.MAX_SKIPPED_STORE)}
    accepts(P.ratchet_from_bytes, _rs(skipped=full))
    rejects(P.ratchet_from_bytes, _rs(skipped={**full, (b"\x01" * 32, 1): (b"\x00" * 32, 0)}), exc=MAL)
    accepts(P.ratchet_from_bytes, _rs(events=K.U32_MAX - 1))
    rejects(P.ratchet_from_bytes, _rs(events=K.U32_MAX), exc=MAL)
    at_events = {k: (v[0], s.events) for k, v in s.skipped.items()}
    accepts(P.ratchet_from_bytes, _rs(skipped=at_events))
    later = {k: (v[0], s.events + 1) for k, v in s.skipped.items()}
    rejects(P.ratchet_from_bytes, _rs(skipped=later), exc=MAL)
    two = dict(list(s.skipped.items())[:2])
    raw = _rs(skipped=two)
    first_dh_n = raw[185:185 + 36]
    rejects(P.ratchet_from_bytes, put(raw, 185 + 72, first_dh_n), exc=MAL)
    rejects(P.ratchet_from_bytes, _rs(cks=None), exc=MAL)
    rejects(P.ratchet_from_bytes, _rs(dhr=None), exc=MAL)


@case("PS-05 ratchet state entry order is kept as read, and eviction breaks stored_at ties by it",
      f"{SP} Ratchet state: That order is meaningful ... but the reader accepts the entries in any order and keeps the order it read")
def _():
    s = BOB1.classical.clone()
    s.skipped = {k: (v[0], 0) for k, v in s.skipped.items()}
    assert len(s.skipped) >= 2
    rev = s.clone()
    rev.skipped = dict(reversed(list(s.skipped.items())))
    raw = P.ratchet_to_bytes(rev)
    back = accepts(P.ratchet_from_bytes, raw)
    assert list(back.skipped) == list(rev.skipped) and P.ratchet_to_bytes(back) == raw
    assert list(ratchet.evict(back, 1).skipped) == list(rev.skipped)[1:]


# ===================================================== sparse ratchet state

def _sp(epoch, chains, skipped=None, direction=spqr.A2B):
    return P.spqr_to_bytes(spqr.State(rk=b"\x33" * 32, epoch=epoch, direction=direction,
                                      chains=chains, skipped=skipped or {}))


def _c(n=1):
    return spqr.Chain(b"\x44" * 32, n)


@case("PS-06 sparse ratchet state round trip, across an epoch advance with skipped keys and chains order",
      f"{SP} Sparse ratchet state: spqr_state = version(1) || rk(32) || epoch(8) || direction(1) || chains || skipped")
def _():
    a, b = spqr.init(b"\x09" * 32, spqr.A2B), spqr.init(b"\x09" * 32, spqr.B2A)
    for _ in range(3):
        a = spqr.send(a, 0)[0]
    b = spqr.receive(b, 0, 3)[0]
    a, e, n, _ = spqr.send(a, 0, b"\x77" * 32, 1)
    b = spqr.receive(b, e, n, b"\x77" * 32, 1)[0]
    for s in (a, b, BOB1.sparse, ALICE0.sparse):
        raw = P.spqr_to_bytes(s)
        back = accepts(P.spqr_from_bytes, raw)
        assert back == s and list(back.chains) == list(s.chains) and list(back.skipped) == list(s.skipped)
        assert P.spqr_to_bytes(back) == raw
    assert b.skipped and list(b.chains) == [1, 0]


@case("PS-07 sparse ratchet state framing: version, truncation, trailing, direction tag, chain presence tag, absent chain zeroed",
      f"{SP} Sparse ratchet state: direction is a one-byte tag (0x00 A2b, 0x01 B2a); chain = presence(1) || ck(32) || n(8) -- present, or zeroed if absent")
def _():
    raw = P.spqr_to_bytes(BOB1.sparse)
    rejects(P.spqr_from_bytes, put(raw, 0, 0x02), exc=WV)
    for n in range(1, len(raw)):
        rejects(P.spqr_from_bytes, raw[:n], exc=MAL)
    rejects(P.spqr_from_bytes, raw + b"\x00", exc=MAL)
    rejects(P.spqr_from_bytes, put(raw, 41, 0x02), exc=MAL)
    first_chain = 1 + 32 + 8 + 1 + 4 + 8
    rejects(P.spqr_from_bytes, put(raw, first_chain, 0x02), exc=MAL)
    absent = _sp(0, {0: [None, _c()]})
    back = accepts(P.spqr_from_bytes, absent)
    rejects(spqr.send, back, 0, exc=spqr.ChainRetired)
    rejects(P.spqr_from_bytes, put(absent, first_chain + 5, 0x01), exc=MAL)
    rejects(P.spqr_from_bytes, put(absent, first_chain + 40, 0x01), exc=MAL)


@case("PS-08 sparse ratchet state semantic rules: store bound, e <= epoch < e + EPOCHS_KEPT (saturating), distinct entry epochs, current epoch present, stored keys' epochs present, distinct (epoch, n)",
      f"{SP} Semantic rules of the leaf formats: Sparse ratchet state")
def _():
    accepts(P.spqr_from_bytes, _sp(5, {4: [_c(), _c()], 5: [_c(), _c()]}))
    rejects(P.spqr_from_bytes, _sp(5, {3: [_c(), _c()], 5: [_c(), _c()]}), exc=MAL)    # e + 2 <= epoch
    rejects(P.spqr_from_bytes, _sp(5, {5: [_c(), _c()], 6: [_c(), _c()]}), exc=MAL)    # e > epoch
    rejects(P.spqr_from_bytes, _sp(5, {4: [_c(), _c()]}), exc=MAL)                     # current epoch missing
    rejects(P.spqr_from_bytes, _sp(5, {5: [_c(), _c()]}, {(4, 1): b"\x00" * 32}), exc=MAL)
    top = K.U64_MAX
    rejects(P.spqr_from_bytes, _sp(top, {top: [_c(), _c()]}), exc=MAL)                 # saturation: covers nothing
    rejects(P.spqr_from_bytes, _sp(top, {top - 1: [_c(), _c()], top: [_c(), _c()]}), exc=MAL)
    accepts(P.spqr_from_bytes, _sp(top - 1, {top - 2: [_c(), _c()], top - 1: [_c(), _c()]}))
    full = {(5, i + 1): b"\x00" * 32 for i in range(K.MAX_SKIPPED_STORE)}
    accepts(P.spqr_from_bytes, _sp(5, {5: [_c(), _c()]}, full))
    rejects(P.spqr_from_bytes, _sp(5, {5: [_c(), _c()]}, {**full, (5, 99999): b"\x00" * 32}), exc=MAL)
    raw = _sp(5, {4: [_c(), _c()], 5: [_c(), _c()]})
    first = 1 + 32 + 8 + 1 + 4
    rejects(P.spqr_from_bytes, put(raw, first + 90, (4).to_bytes(8, "big")), exc=MAL)  # two entries share an epoch
    raw = _sp(5, {5: [_c(), _c()]}, {(5, 1): b"\x00" * 32, (5, 2): b"\x00" * 32})
    rejects(P.spqr_from_bytes, put(raw, len(raw) - 48, (5).to_bytes(8, "big") + (1).to_bytes(8, "big")), exc=MAL)


# ===================================================== triple ratchet state

@case("PS-09 triple ratchet state round trip, and the role rule while the classical ratchet shows its role",
      f"{SP} Semantic rules of the leaf formats: Triple ratchet state ... the sparse ratchet's direction is A2b exactly when that role is the sender's")
def _():
    for party in (ALICE0, BOB0, ALICE1, BOB1):
        t = P.TripleState(party.classical, party.sparse)
        raw = P.triple_to_bytes(t)
        back = accepts(P.triple_from_bytes, raw)
        assert back == t and P.triple_to_bytes(back) == raw
    flip_dir = _with_dir
    rejects(P.triple_from_bytes, P.triple_to_bytes(P.TripleState(ALICE0.classical, flip_dir(ALICE0.sparse, spqr.B2A))), exc=MAL)
    rejects(P.triple_from_bytes, P.triple_to_bytes(P.TripleState(BOB0.classical, flip_dir(BOB0.sparse, spqr.A2B))), exc=MAL)
    accepts(P.triple_from_bytes, P.triple_to_bytes(P.TripleState(ALICE1.classical, flip_dir(ALICE1.sparse, spqr.B2A))))
    raw = P.triple_to_bytes(P.TripleState(BOB1.classical, BOB1.sparse))
    rejects(P.triple_from_bytes, raw + b"\x00", exc=MAL)
    rejects(P.triple_from_bytes, put(raw, 1, (0xFFFF).to_bytes(4, "big")), exc=MAL)
    rejects(P.triple_from_bytes, put(raw, 5, 0x07), exc=WV)
    rejects(P.triple_from_bytes, put(raw, 0, 0x02), exc=WV)


def _with_dir(s, d):
    c = s.clone()
    c.direction = d
    return c


# ================================================= erasure coder sub-formats

@case("PS-10 erasure encoder sub-format: round trip; exhausted is 0x00/0x01; exhausted only when next is u16::MAX; count bound; count before entries; trailing",
      f"{SP} Erasure coder sub-formats: encoder = next(2) || exhausted(1) || count(4) || chunk(32)[count]")
def _():
    e = erasure.Encoder.for_value(rnd(192))
    e.issue()
    e.issue()
    for enc in (e, erasure.Encoder(e.chunks, K.U16_MAX, True), erasure.Encoder(e.chunks, K.U16_MAX, False), erasure.Encoder([])):
        raw = P.encoder_to_bytes(enc)
        assert accepts(P.encoder_from_bytes, raw) == enc
    raw = P.encoder_to_bytes(e)
    assert raw[:3] == b"\x00\x02\x00"
    rejects(P.encoder_from_bytes, put(raw, 2, 0x02), exc=MAL)
    rejects(P.encoder_from_bytes, put(raw, 2, 0x01), exc=MAL)                      # exhausted, next = 2
    rejects(P.encoder_from_bytes, put(raw, 3, (7).to_bytes(4, "big")), exc=MAL)     # count > buffer
    rejects(P.encoder_from_bytes, raw + b"\x00", exc=MAL)
    rejects(P.encoder_from_bytes, raw[:-1], exc=MAL)
    over = b"\x00\x00\x00" + (K.MAX_CODEWORDS + 1).to_bytes(4, "big") + bytes(32 * (K.MAX_CODEWORDS + 1))
    rejects(P.encoder_from_bytes, over, exc=MAL)


@case("PS-11 erasure decoder sub-format: round trip; needed <= 65,536 and size <= 2,097,152 before narrowing; needed = ceil(size/32); count <= needed; distinct indices; trailing",
      f"{SP} Erasure coder sub-formats: decoder = size(8) || needed(8) || count(4) || codeword[count]; Erasure decoder rules")
def _():
    d = erasure.Decoder(96)
    d.receive(7, rnd(32))
    d.receive(1, rnd(32))
    for dec in (d, erasure.Decoder(1408), erasure.Decoder(0)):
        raw = P.decoder_to_bytes(dec)
        assert accepts(P.decoder_from_bytes, raw) == dec
    top = (K.ERASURE_MAX_SIZE).to_bytes(8, "big") + (K.ERASURE_MAX_NEEDED).to_bytes(8, "big") + bytes(4)
    accepts(P.decoder_from_bytes, top)
    rejects(P.decoder_from_bytes, (K.ERASURE_MAX_SIZE + 1).to_bytes(8, "big") + (65537).to_bytes(8, "big") + bytes(4), exc=MAL)
    rejects(P.decoder_from_bytes, (K.ERASURE_MAX_SIZE).to_bytes(8, "big") + (65537).to_bytes(8, "big") + bytes(4), exc=MAL)
    rejects(P.decoder_from_bytes, (K.U64_MAX).to_bytes(8, "big") + (3).to_bytes(8, "big") + bytes(4), exc=MAL)
    # a value whose low 32 bits look harmless: 2^32 + 96 bytes
    rejects(P.decoder_from_bytes, ((1 << 32) + 96).to_bytes(8, "big") + (3).to_bytes(8, "big") + bytes(4), exc=MAL)
    raw = P.decoder_to_bytes(d)
    rejects(P.decoder_from_bytes, put(raw, 8, (4).to_bytes(8, "big")), exc=MAL)        # needed != ceil(size/32)
    assert raw[20:22] == (7).to_bytes(2, "big")
    rejects(P.decoder_from_bytes, put(raw, 20 + 34, (7).to_bytes(2, "big")), exc=MAL)  # second codeword repeats index 7
    over = P.decoder_to_bytes(erasure.Decoder(32, [(1, rnd(32))]))
    rejects(P.decoder_from_bytes, put(over, 16, (2).to_bytes(4, "big")) + (2).to_bytes(2, "big") + rnd(32), exc=MAL)
    rejects(P.decoder_from_bytes, put(raw, 16, (9).to_bytes(4, "big")), exc=MAL)
    rejects(P.decoder_from_bytes, raw + b"\x00", exc=MAL)


# =================================================================== Braid

def braid_state(tag, epoch=3):
    if tag == K.BRAID_FAILED_TAG:
        return P.BraidState(tag)
    fields = {}
    for name in P.BRAID_STATES[tag][1]:
        if name in P.RAW_FIELD_LEN:
            fields[name] = rnd(P.RAW_FIELD_LEN[name])
            continue
        n = P.CODER_VALUE_LEN[name.split("_")[0]]
        if name.endswith("_enc"):
            enc = erasure.Encoder.for_value(rnd(n))
            enc.issue()
            fields[name] = enc
        else:
            dec = erasure.Decoder(n)
            dec.receive(2, rnd(32))
            fields[name] = dec
    return P.BraidState(tag, epoch, rnd(32), rnd(32), fields)


BRAIDS = {t: braid_state(t) for t in range(12)}


@case("PS-12 Braid: every state tag 0-11 round trips with its fields in table order, each length-prefixed",
      f"{SP} Braid: braid = version(1) || state_tag(1) || fields; Every field after auth is written len(4) || bytes")
def _():
    for tag, b in BRAIDS.items():
        raw = P.braid_to_bytes(b)
        back = accepts(P.braid_from_bytes, raw)
        assert back == b and P.braid_to_bytes(back) == raw, tag
    assert P.braid_to_bytes(BRAIDS[11]) == b"\x01\x0b"
    assert len(P.braid_to_bytes(BRAIDS[0])) == 2 + 8 + 64


@case("PS-13 Braid refusals: tag above 11, stored epoch u64::MAX, trailing bytes (also after Failed), wrong version",
      f"{SP} Braid: A reader refuses a tag above 11, a stored epoch of u64::MAX, and any bytes left after the last field")
def _():
    raw0 = P.braid_to_bytes(BRAIDS[0])
    for t in (12, 0x80, 0xFF):
        rejects(P.braid_from_bytes, put(raw0, 1, t), exc=MAL)
    rejects(P.braid_from_bytes, put(raw0, 2, (K.U64_MAX).to_bytes(8, "big")), exc=MAL)
    accepts(P.braid_from_bytes, put(raw0, 2, (K.U64_MAX - 1).to_bytes(8, "big")))
    for tag in (0, 7, 11):
        rejects(P.braid_from_bytes, P.braid_to_bytes(BRAIDS[tag]) + b"\x00", exc=MAL)
    rejects(P.braid_from_bytes, put(raw0, 0, 0x02), exc=WV)
    raw7 = P.braid_to_bytes(BRAIDS[7])
    rejects(P.braid_from_bytes, put(raw7, 74, (0xFFFFFFFF).to_bytes(4, "big")), exc=MAL)


@case("PS-14 Braid semantic rules: live epoch at least 1; header/ct1/ek_vector and KEM blob lengths; each coder sized for its value (hdr 96, ek 1536, ct1 1408, ct2 192)",
      f"{SP} Semantic rules of the leaf formats: Braid")
def _():
    rejects(P.braid_from_bytes, P.braid_to_bytes(replace(BRAIDS[0], epoch=0)), exc=MAL)
    accepts(P.braid_from_bytes, P.braid_to_bytes(replace(BRAIDS[0], epoch=1)))
    bad_raw = [(1, "key_pair", 11871), (1, "key_pair", 11873), (7, "encaps", 2591), (6, "header", 65),
               (3, "ct1", 1407), (8, "ek_vector", 1535)]
    for tag, name, n in bad_raw:
        b = braid_state(tag)
        b.fields[name] = rnd(n)
        rejects(P.braid_from_bytes, P.braid_to_bytes(b), exc=MAL)
    bad_coders = [(1, "hdr_enc", erasure.Encoder.for_value(rnd(128))), (5, "hdr_dec", erasure.Decoder(95)),
                  (4, "ct2_dec", erasure.Decoder(160)), (2, "ek_enc", erasure.Encoder.for_value(rnd(1504))),
                  (10, "ct2_enc", erasure.Encoder.for_value(rnd(160))), (2, "ct1_dec", erasure.Decoder(1536))]
    for tag, name, coder in bad_coders:
        b = braid_state(tag)
        b.fields[name] = coder
        rejects(P.braid_from_bytes, P.braid_to_bytes(b), exc=MAL)
    b = braid_state(10)
    b.fields["ct2_enc"] = erasure.Encoder.for_value(rnd(190))    # ceil(190/32) = 6 chunks: sized for 192
    accepts(P.braid_from_bytes, P.braid_to_bytes(b))
    raw = P.braid_to_bytes(braid_state(10))
    rejects(P.braid_from_bytes, put(raw, 2 + 8 + 64 + 4 + 2, 0x02), exc=MAL)   # inner encoder's exhausted byte


# ================================================================= session

def session_for(party, braid, initiator=True, **kw):
    base = dict(
        triple=P.TripleState(party.classical, party.sparse), braid=braid,
        ratchet_private=party.ratchet_private, identity_ad=AD,
        our_identity_public=IKA if initiator else IKB, peer_identity_public=IKB if initiator else IKA,
        pending_initial=P.PendingInitial(EKA_PUB, rnd(1568), 1, 2, 3) if initiator else None,
        established_ephemeral=None if initiator else wire.encode_ec(EKA_PUB))
    base.update(kw)
    return P.SessionState(**base)


ALICE_S = session_for(ALICE0, braid_state(1, epoch=1))
BOB_S = session_for(BOB0, braid_state(5, epoch=1), initiator=False)


@case("PS-15 session round trip: initiator with pending_initial, responder with established_ephemeral, a responder past the header-receiving point, a failed Braid",
      f"{SP} Session: session = version(1) || len(4) || triple_state || len(4) || braid || ... established_ephemeral")
def _():
    advanced = replace(BOB0, sparse=spqr.send(BOB0.sparse, 0, b"\x99" * 32, 1)[0])
    samples = [ALICE_S, BOB_S,
               session_for(advanced, braid_state(7, epoch=1), initiator=False),
               session_for(ALICE1, P.BraidState(11), pending_initial=None),
               session_for(ALICE0, braid_state(0, epoch=1))]
    for s in samples:
        raw = P.session_to_bytes(s)
        back = accepts(P.session_from_bytes, raw)
        assert back == s and P.session_to_bytes(back) == raw
    raw = P.session_to_bytes(replace(ALICE_S, pending_initial=None))
    assert raw[-2:] == b"\x00\x00", "absent optional fields are a presence byte followed by nothing"


@case("PS-16 session framing: wrong version, presence byte other than 0/1, trailing bytes, a malformed half, a pending_initial with bytes left over",
      f"{SP} Session: a presence byte followed by a length-prefixed field when present, and nothing ... when absent; Rejection")
def _():
    raw = P.session_to_bytes(ALICE_S)
    rejects(P.session_from_bytes, put(raw, 0, 0x02), exc=WV)
    rejects(P.session_from_bytes, raw + b"\x00", exc=MAL)
    pres = len(raw) - 1
    rejects(P.session_from_bytes, put(raw, pres, 0x02), exc=MAL)
    no_pending = P.session_to_bytes(replace(ALICE_S, pending_initial=None))
    rejects(P.session_from_bytes, put(no_pending, len(no_pending) - 2, 0x02), exc=MAL)
    tb = P.triple_to_bytes(ALICE_S.triple)
    rejects(P.session_from_bytes, put(raw, 5 + len(tb), 0xFF), exc=MAL)       # the braid's length prefix overruns
    bad_triple = put(raw, 5 + 1 + 4, 0x02)                                     # ratchet_state's version byte
    rejects(P.session_from_bytes, bad_triple, exc=WV)
    pb = P._pending_bytes(ALICE_S.pending_initial)
    head = raw[:-(1 + 4 + len(pb) + 1)]
    leftover = head + b"\x01" + (len(pb) + 1).to_bytes(4, "big") + pb + b"\x00" + b"\x00"
    rejects(P.session_from_bytes, leftover, exc=MAL)                          # bytes left inside pending_initial
    rejects(P.session_from_bytes, raw[:-1], exc=MAL)


@case("PS-17 session semantic rules, each refused as inconsistent: ratchet private key, sparse epoch vs the Braid's, identity_ad orientation, Braid role, direction, pending with established, optional field shapes",
      f"{SP} Session, Semantic rules: refuses the session as inconsistent unless every one of the following holds")
def _():
    accepts(P.session_from_bytes, P.session_to_bytes(ALICE_S))
    accepts(P.session_from_bytes, P.session_to_bytes(BOB_S))
    bad = {
        "private key": replace(ALICE_S, ratchet_private=b"\xa1" * 32),
        "epoch tags 0-6": replace(ALICE_S, braid=braid_state(1, epoch=2)),
        "epoch tags 7-10": session_for(BOB0, braid_state(7, epoch=1), initiator=False),
        "identity_ad": replace(ALICE_S, identity_ad=wire.encode_ec(IKB) + wire.encode_ec(IKA)),
        "identity_ad responder": replace(BOB_S, identity_ad=wire.encode_ec(IKB) + wire.encode_ec(IKA)),
        "braid role": replace(ALICE_S, braid=braid_state(5, epoch=1)),
        "braid role even epoch": session_for(ALICE1, braid_state(6, epoch=1)),
        "direction": session_for(ALICE1, braid_state(1, epoch=1), triple=P.TripleState(ALICE1.classical, _with_dir(ALICE1.sparse, spqr.B2A))),
        "pending and established": replace(BOB_S, pending_initial=P.PendingInitial(EKA_PUB, rnd(1568), 1, 2, 3)),
        "kem_ciphertext": replace(ALICE_S, pending_initial=P.PendingInitial(EKA_PUB, rnd(1567), 1, 2, 3)),
        "established 32 bytes": replace(BOB_S, established_ephemeral=EKA_PUB),
        "established curve byte": replace(BOB_S, established_ephemeral=b"\x08" + EKA_PUB),
    }
    for label, s in bad.items():
        try:
            P.session_from_bytes(P.session_to_bytes(s))
        except P.Inconsistent:
            continue
        except P.PersistError as e:
            raise AssertionError(f"{label}: refused as {type(e).__name__}, not Inconsistent: {e}")
        raise AssertionError(f"{label}: accepted")
    # a failed Braid is exempt from the epoch relation and the Braid's half of the role rule, not the direction half
    failed = P.BraidState(11)
    accepts(P.session_from_bytes, P.session_to_bytes(replace(ALICE_S, braid=failed)))
    rejects(P.session_from_bytes, P.session_to_bytes(
        session_for(ALICE1, failed, triple=P.TripleState(ALICE1.classical, _with_dir(ALICE1.sparse, spqr.B2A)))), exc=INC)


# ============================================================ prekey store

def encode12(coeffs):
    out = bytearray()
    for i in range(0, len(coeffs), 2):
        c0, c1 = coeffs[i], coeffs[i + 1]
        out += bytes([c0 & 0xFF, (c0 >> 8) | ((c1 & 0x0F) << 4), c1 >> 4])
    return bytes(out)


def kem_pair(coeffs=None):
    coeffs = coeffs or [R.randrange(K.MLKEM_Q) for _ in range(1024)]
    ek = encode12(coeffs) + rnd(32)
    dk = rnd(1536) + ek + hashlib.sha3_256(ek).digest() + rnd(32)
    return dk + ek


def store(**kw):
    base = dict(identity_public=rnd(32), signed_prekey_secret=rnd(32), signed_prekey_id=1, signed_prekey_sig=rnd(64),
                one_time=[(2, rnd(32)), (3, rnd(32))], kem_pair=kem_pair(), kem_id=4, kem_sig=rnd(64),
                kem_one_time=[(5, kem_pair(), rnd(64)), (6, kem_pair(), rnd(64))], next_id=10,
                seen=[(4, rnd(32)), (4, rnd(32))], previous_signed=None, previous_kem=None)
    base.update(kw)
    return P.PrekeyStore(**base)


STORE = store(previous_signed=(rnd(32), 7, rnd(64)), previous_kem=(kem_pair(), 8, rnd(64)),
              seen=[(4, rnd(32)), (8, rnd(32)), (4, rnd(32))])


def legacy(p, version):
    """A v1, v2 or v3 store, laid out by the page's field list."""
    v4 = P.prekey_store_to_bytes(p)
    head_len = (1 + 32 + 32 + 4 + 64 + 4 + 36 * len(p.one_time) + 4 + len(p.kem_pair) + 4 + 64
                + 4 + sum(4 + 4 + len(kp) + 64 for _, kp, _ in p.kem_one_time) + 4)
    out = bytearray([version]) + v4[1:head_len]
    if version >= 2:
        out += len(p.seen).to_bytes(4, "big") + b"".join(fp for _, fp in p.seen)
    if version >= 3:
        out += v4[head_len + 4 + 36 * len(p.seen):]
    return bytes(out)


@case("PS-18 prekey store v4 round trip, with retired prekeys and record entries under both live keys",
      f"{SP} Prekey store: prekey_store = version(1) || ... || previous_kem_present(1) || previous_kem; The writer always emits 0x04")
def _():
    for p in (STORE, store(), store(seen=[], one_time=[], kem_one_time=[])):
        raw = P.prekey_store_to_bytes(p)
        assert raw[0] == 0x04
        back = accepts(P.prekey_store_from_bytes, raw)
        assert back == p


@case("PS-19 prekey store v1, v2 and v3 are read: v1 with nothing remembered, v2 with nothing retired, untagged entries tagged with the current kem_id; each re-encodes as v4",
      f"{SP} Prekey store: Four versions are read; one is written")
def _():
    p = store(seen=[(4, rnd(32)), (4, rnd(32))])
    v1 = accepts(P.prekey_store_from_bytes, legacy(p, 1))
    assert v1.seen == [] and v1.previous_signed is None and v1.previous_kem is None
    v2 = accepts(P.prekey_store_from_bytes, legacy(p, 2))
    assert v2.seen == p.seen and v2.previous_kem is None
    q = store(previous_signed=(rnd(32), 7, rnd(64)), previous_kem=(kem_pair(), 8, rnd(64)), seen=[(4, rnd(32))])
    v3 = accepts(P.prekey_store_from_bytes, legacy(q, 3))
    assert v3 == q
    q_untagged = replace(q, seen=[(8, q.seen[0][1])])
    assert accepts(P.prekey_store_from_bytes, legacy(q_untagged, 3)).seen == [(4, q.seen[0][1])]
    for old in (v1, v2, v3):
        assert P.prekey_store_to_bytes(old)[0] == 0x04
        accepts(P.prekey_store_from_bytes, P.prekey_store_to_bytes(old))
    rejects(P.prekey_store_from_bytes, legacy(p, 2) + b"\x00", exc=MAL)
    rejects(P.prekey_store_from_bytes, legacy(p, 1) + b"\x00", exc=MAL)


@case("PS-20 prekey store framing: unknown version, truncation, trailing bytes, previous_* presence byte other than 0/1",
      f"{SP} Prekey store: A presence byte is 0x00 or 0x01 and nothing else")
def _():
    raw = P.prekey_store_to_bytes(STORE)
    for v in (0x00, 0x05, 0xFF):
        rejects(P.prekey_store_from_bytes, put(raw, 0, v), exc=WV)
    for n in (1, 40, 200, 300, len(raw) - 1):
        rejects(P.prekey_store_from_bytes, raw[:n], exc=MAL)
    rejects(P.prekey_store_from_bytes, raw + b"\x00", exc=MAL)
    no_prev = P.prekey_store_to_bytes(store())
    rejects(P.prekey_store_from_bytes, put(no_prev, len(no_prev) - 2, 0x02), exc=MAL)
    rejects(P.prekey_store_from_bytes, put(no_prev, len(no_prev) - 1, 0x02), exc=MAL)


@case("PS-21 kem_pair checks: length 4,736; FIPS 203 modulus check on ek; FIPS 203 hash check on dk; the ek inside dk equals ek (in every position a kem_pair appears)",
      f"{SP} Prekey store: The reader refuses a kem_pair as malformed unless all four hold")
def _():
    ok = [R.randrange(K.MLKEM_Q) for _ in range(1024)]
    edge = list(ok)
    edge[0], edge[1023] = K.MLKEM_Q - 1, K.MLKEM_Q - 1
    assert P.kem_pair_problem(kem_pair(edge)) is None
    for bad_c in (K.MLKEM_Q, 4095):
        for pos in (0, 1, 1023):
            c = list(ok)
            c[pos] = bad_c
            kp = kem_pair(c)
            assert P.kem_pair_problem(kp), (bad_c, pos)
    good = kem_pair(ok)
    wrong_h = good[:3104] + bytes([good[3104] ^ 1]) + good[3105:]
    other_ek = good[:-1] + bytes([good[-1] ^ 1])                 # rho byte of the outer ek
    for kp in (good[:-1], good + b"\x00", wrong_h, other_ek):
        assert P.kem_pair_problem(kp)
    bad_kp = other_ek
    for p in (store(kem_pair=bad_kp), store(kem_one_time=[(5, bad_kp, rnd(64))]),
              store(previous_kem=(bad_kp, 8, rnd(64)))):
        rejects(P.prekey_store_from_bytes, P.prekey_store_to_bytes(p), exc=MAL)


@case("PS-22 prekey store record counts: v4 at most two budgets, v2/v3 one, refused before sizing anything; per-key bound 1024 as a rule over what was read",
      f"{SP} Prekey store: a count larger than what the version could possibly have written is refused as malformed before it sizes anything")
def _():
    two = [(4, rnd(32)) for _ in range(1024)] + [(8, rnd(32)) for _ in range(1024)]
    p = store(previous_kem=(kem_pair(), 8, rnd(64)), seen=two)
    accepts(P.prekey_store_from_bytes, P.prekey_store_to_bytes(p))
    over_key = store(previous_kem=(kem_pair(), 8, rnd(64)), seen=[(4, rnd(32)) for _ in range(1025)])
    rejects(P.prekey_store_from_bytes, P.prekey_store_to_bytes(over_key), exc=MAL)
    raw = P.prekey_store_to_bytes(store(seen=[]))
    seen_at = len(raw) - 2 - 4
    huge = put(raw, seen_at, (2049).to_bytes(4, "big"))
    rejects(P.prekey_store_from_bytes, huge, exc=MAL)
    one = store(seen=[(4, rnd(32)) for _ in range(1024)])
    accepts(P.prekey_store_from_bytes, legacy(one, 3))
    rejects(P.prekey_store_from_bytes, legacy(store(seen=[(4, rnd(32)) for _ in range(1025)]), 3), exc=MAL)


@case("PS-23 prekey store semantic rules: identifiers below next_id, none zero, pairwise distinct across kinds; entries tagged with a live key; no repeated fingerprint",
      f"{SP} Prekey store, Semantic rules: the reader refuses as malformed any store for which PrekeyStore::invariant is false")
def _():
    fp = rnd(32)
    bad = {
        "zero id": store(one_time=[(0, rnd(32)), (3, rnd(32))]),
        "id == next_id": store(next_id=6),
        "id above next_id": store(kem_one_time=[(5, kem_pair(), rnd(64)), (60, kem_pair(), rnd(64))]),
        "curve vs kem one-time": store(kem_one_time=[(2, kem_pair(), rnd(64))]),
        "retired equals live": store(previous_signed=(rnd(32), 1, rnd(64))),
        "kem one-time equals last resort": store(kem_one_time=[(4, kem_pair(), rnd(64))]),
        "unknown tag": store(seen=[(9, rnd(32))]),
        "tag of a one-time KEM key": store(seen=[(5, rnd(32))]),
        "repeated fingerprint": store(seen=[(4, fp), (4, fp)]),
        "repeated fingerprint across keys": store(previous_kem=(kem_pair(), 8, rnd(64)), seen=[(4, fp), (8, fp)]),
    }
    for label, p in bad.items():
        try:
            P.prekey_store_from_bytes(P.prekey_store_to_bytes(p))
        except P.Malformed:
            continue
        except P.PersistError as e:
            raise AssertionError(f"{label}: refused as {type(e).__name__}")
        raise AssertionError(f"{label}: accepted")
    accepts(P.prekey_store_from_bytes, P.prekey_store_to_bytes(store(next_id=7)))
