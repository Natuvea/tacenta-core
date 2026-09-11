"""ML-KEM Braid cases, from mlkem-braid.md, which now states the protocol.

The KEM is kem_double.ToyIncrementalKem, a test double with the split's shapes
and laws, not ML-KEM. braid.json and auth.json (run as vectors) pin KDF_OK and
one Update; nothing else here has a vector behind it: no MAC, no transition,
no failure path, no persisted Braid state (GAPS-3.md, vector gaps)."""

import copy
import hashlib
from dataclasses import replace

from _casekit import accepts, registry, rejects
from tacenta_reader import braid as B
from tacenta_reader import constants as K
from tacenta_reader import erasure, persistence, spqr, triple, wire
from tacenta_reader.curve25519 import x25519_public
from tacenta_reader.kdf import hkdf_sha256, hmac_sha256
from tacenta_reader.kem_double import KemFailure, ToyIncrementalKem, byte_encode12

CASES, case = registry()
MB = "mlkem-braid.md"
SK = bytes(range(32))


def kems(tag=b""):
    return ToyIncrementalKem(b"alice" + tag), ToyIncrementalKem(b"bob" + tag)


# The thirteen transitions, as (tag before, tag after, operation).
TRANSITIONS = {
    (B.KEYS_UNSAMPLED, B.KEYS_SAMPLED, "send"): 1,
    (B.KEYS_SAMPLED, B.HEADER_SENT, "recv"): 2,
    (B.HEADER_SENT, B.CT1_RECEIVED, "recv"): 3,
    (B.CT1_RECEIVED, B.EK_SENT_CT1_RECEIVED, "recv"): 4,
    (B.EK_SENT_CT1_RECEIVED, B.NO_HEADER_RECEIVED, "recv"): 5,
    (B.NO_HEADER_RECEIVED, B.HEADER_RECEIVED, "recv"): 6,
    (B.HEADER_RECEIVED, B.CT1_SAMPLED, "send"): 7,
    (B.CT1_SAMPLED, B.CT1_ACKNOWLEDGED, "recv"): 8,
    (B.CT1_SAMPLED, B.CT2_SAMPLED, "recv"): 9,
    (B.CT1_SAMPLED, B.EK_RECEIVED_CT1_SAMPLED, "recv"): 10,
    (B.CT1_ACKNOWLEDGED, B.CT2_SAMPLED, "recv"): 11,
    (B.EK_RECEIVED_CT1_SAMPLED, B.CT2_SAMPLED, "recv"): 12,
    (B.CT2_SAMPLED, B.KEYS_UNSAMPLED, "recv"): 13,
}


class Run:
    """Two Braids and a log. `step(who, deliver)` makes `who` send and, when
    `deliver` says so, the other receive."""

    def __init__(self, sk_a=SK, sk_b=SK, kem_a=None, kem_b=None):
        ka, kb = kems()
        self.kem = {"a": kem_a or ka, "b": kem_b or kb}
        self.st = {"a": B.init_initiator(sk_a), "b": B.init_responder(sk_b)}
        self.outputs = {"a": [], "b": []}
        self.seen = set()
        self.log = []          # (who, op, tag before, tag after, message or result)
        self.messages = 0

    def _note(self, who, op, before, after, extra):
        if before != after:
            self.seen.add((before, after, op))
        self.log.append((who, op, before, after, extra))

    def send(self, who):
        before = self.st[who]
        r = B.send(before, self.kem[who])
        self.st[who] = r.state
        self._note(who, "send", before.tag, r.state.tag, r)
        if r.output:
            self.outputs[who].append(("send", r.output))
        self.messages += 1
        return r

    def recv(self, who, msg):
        before = self.st[who]
        r = B.receive(before, msg, self.kem[who])
        self.st[who] = r.state
        self._note(who, "recv", before.tag, r.state.tag, r)
        if r.output:
            self.outputs[who].append(("recv", r.output))
        return r

    def step(self, who, deliver=True, mutate=None):
        r = self.send(who)
        msg = r.message
        if msg is not None and mutate is not None:
            msg = mutate(msg)
        if msg is not None and deliver:
            self.recv("b" if who == "a" else "a", msg)
        return r

    def alternate(self, rounds, deliver=lambda who, i, msg: True):
        for i in range(rounds):
            for who in ("a", "b"):
                r = self.send(who)
                if r.message is not None and deliver(who, i, r.message):
                    self.recv("b" if who == "a" else "a", r.message)

    def until_epoch(self, e, deliver=lambda who, i, msg: True, limit=2000):
        i = 0
        while min(len(self.outputs["a"]), len(self.outputs["b"])) < e and i < limit:
            for who in ("a", "b"):
                r = self.send(who)
                if r.message is not None and deliver(who, i, r.message):
                    self.recv("b" if who == "a" else "a", r.message)
            i += 1
        return i


def flip_chunk(msg, byte=0):
    idx, data = msg.codeword
    d = bytearray(data)
    d[byte] ^= 0x01
    return replace(msg, codeword=(idx, bytes(d)))


# ------------------------------------------------ Parameters and derivations

@case("BR-01 the bytes: PROTOCOL_INFO and the four suffixes are the page's hex, lengths 25, 9, 21, 9, 11; ToBytes is 8 bytes big-endian; KDF_OK and KDF_AUTH are HKDF with the stated salt, info and length",
      f"{MB} Parameters and derivations: Bytes; The two derivations")
def _():
    listed = {
        K.BRAID_PROTOCOL_INFO: "5461 63656e74615f4d4c4b454d31303234 5f5348412d323536",
        K.BRAID_SCKA_KEY: "3a53434b41204b6579",
        K.BRAID_AUTH_UPDATE: "3a41757468656e74696361746f7220557064617465",
        K.BRAID_EKHEADER: "3a656b686561646572",
        K.BRAID_CIPHERTEXT: "3a63697068657274657874",
    }
    for value, hexs in listed.items():
        assert value.hex() == hexs.replace(" ", ""), value
    assert [len(v) for v in listed] == [25, 9, 21, 9, 11]
    assert B.to_bytes(0x0102) == bytes(6) + b"\x01\x02"
    rejects(B.to_bytes, K.U64_MAX + 1, exc=ValueError)
    k, u, rk = b"\x07" * 32, b"\x08" * 32, b"\x09" * 32
    for e in (1, 2, 0x100, K.U64_MAX):
        info_ok = b"Tacenta_MLKEM1024_SHA-256:SCKA Key" + e.to_bytes(8, "big")
        assert B.kdf_ok(k, e) == hkdf_sha256(bytes(32), k, info_ok, 32)
        prk = hmac_sha256(bytes(32), k)
        assert B.kdf_ok(k, e) == hmac_sha256(prk, info_ok + b"\x01")      # L = 32: one HKDF block
        info_auth = b"Tacenta_MLKEM1024_SHA-256:Authenticator Update" + e.to_bytes(8, "big")
        assert B.kdf_auth(rk, u, e) == hkdf_sha256(rk, u, info_auth, 64) and len(B.kdf_auth(rk, u, e)) == 64


@case("BR-02 the authenticator: Init(e, s) is Update from a zero root and reads no mac_key; Update puts the first 32 bytes in root_key and the last 32 in mac_key; MacHdr and MacCt are full HMACs over PROTOCOL_INFO || suffix || ToBytes(e) || data; a mismatch in any byte, or a truncated MAC, does not verify",
      f"{MB} Parameters and derivations: The ratcheted authenticator; Verification; Where this reads the published document")
def _():
    s = b"\x33" * 32
    a = B.Auth.init(1, s)
    out = B.kdf_auth(bytes(32), s, 1)
    assert (a.root_key, a.mac_key) == (out[:32], out[32:])
    assert B.Auth(bytes(32), b"\xee" * 32).update(1, s) == a        # the old mac_key plays no part
    b2 = a.update(2, b"\x44" * 32)
    out2 = B.kdf_auth(a.root_key, b"\x44" * 32, 2)
    assert (b2.root_key, b2.mac_key) == (out2[:32], out2[32:])
    hdr, ct = bytes(range(64)), bytes(1568)
    assert b2.mac_hdr(7, hdr) == hmac_sha256(b2.mac_key, K.BRAID_PROTOCOL_INFO + b":ekheader" + (7).to_bytes(8, "big") + hdr)
    assert b2.mac_ct(7, ct) == hmac_sha256(b2.mac_key, K.BRAID_PROTOCOL_INFO + b":ciphertext" + (7).to_bytes(8, "big") + ct)
    # the published document writes the epoch bare in the MAC inputs; here it is ToBytes
    assert b2.mac_hdr(7, hdr) != hmac_sha256(b2.mac_key, K.BRAID_PROTOCOL_INFO + b":ekheader" + b"\x07" + hdr)
    assert b2.mac_hdr(7, hdr) != b2.mac_ct(7, hdr) and b2.mac_hdr(7, hdr) != b2.mac_hdr(8, hdr)
    mac = b2.mac_hdr(7, hdr)
    assert B.mac_matches(mac, mac)
    assert not B.mac_matches(mac, mac[:31]) and not B.mac_matches(mac, mac[:31] + bytes([mac[31] ^ 1]))
    rejects(B.Auth(bytes(32), b"").mac_hdr, 1, hdr, exc=ValueError)


@case("BR-03 sizes and holdings: the four values are 96, 1,536, 1,408 and 192 bytes, 3, 48, 44 and 6 codewords with no padding; each state holds what the States table lists, the same fields session-persistence.md's Braid layout writes",
      f"{MB} Parameters and derivations, Sizes; The state machine, States; session-persistence.md Braid")
def _():
    for n, k in ((B.HDR_VALUE_LEN, 3), (B.EK_VECTOR_LEN, 48), (B.CT1_LEN, 44), (B.CT2_VALUE_LEN, 6)):
        assert erasure.chunk_count(n) == k and n == 32 * k
    assert B.CT1_LEN + B.CT2_LEN == 1568
    for tag, (name, fields) in persistence.BRAID_STATES.items():
        assert B.STATE_NAMES[tag] == name
        assert B.HOLDS[tag] == fields, (name, B.HOLDS[tag], fields)


@case("BR-04 initialisation: both parties at epoch 1 with Init(1, SK), SK whole and not a split half; the initiator in KeysUnsampled, the responder in NoHeaderReceived with an empty 96-byte header decoder",
      f"{MB} The state machine, Initialisation; Parameters and derivations, Initialisation")
def _():
    a, b = B.init_initiator(SK), B.init_responder(SK)
    assert (a.name, a.epoch, b.name, b.epoch) == ("KeysUnsampled", 1, "NoHeaderReceived", 1)
    assert a.auth == b.auth == B.Auth.init(1, SK)
    assert all(a.auth != B.Auth.init(1, half) for half in triple.split_secret(SK))
    assert b.hdr_dec.size == 96 and not b.hdr_dec.held


# ------------------------------------------------------------------- Sending

SEND_TABLE = {
    B.KEYS_UNSAMPLED: K.AG_HDR, B.KEYS_SAMPLED: K.AG_HDR, B.HEADER_SENT: K.AG_EK,
    B.CT1_RECEIVED: K.AG_EK_CT1_ACK, B.EK_SENT_CT1_RECEIVED: K.AG_NONE, B.NO_HEADER_RECEIVED: K.AG_NONE,
    B.HEADER_RECEIVED: K.AG_CT1, B.CT1_SAMPLED: K.AG_CT1, B.EK_RECEIVED_CT1_SAMPLED: K.AG_CT1,
    B.CT1_ACKNOWLEDGED: K.AG_NONE, B.CT2_SAMPLED: K.AG_CT2,
}


@case("BR-05 the send table: each state's type; a codeword exactly when the table gives one, at the next index of its encoder (index 0 for a new one at (1) and (7), continuing across (2)-(3) and (10)); only (1) and (7) change state; the message is stamped with the state's epoch and the sending epoch is one less",
      f"{MB} The state machine, Sending")
def _():
    sends_from = {B.KEYS_SAMPLED: "hdr_enc", B.HEADER_SENT: "ek_enc", B.CT1_RECEIVED: "ek_enc",
                  B.CT1_SAMPLED: "ct1_enc", B.EK_RECEIVED_CT1_SAMPLED: "ct1_enc", B.CT2_SAMPLED: "ct2_enc"}
    kem = dict(zip("ab", kems()))
    st = {"a": B.init_initiator(SK), "b": B.init_responder(SK)}
    deliver = lambda who, i, m: not (who == "b" and m.type == K.AG_CT1 and m.codeword[0] != 0 and i < 70)  # noqa: E731
    tags, carried = set(), set()
    for i in range(260):
        for who, other in (("a", "b"), ("b", "a")):
            before = st[who]
            r = B.send(before, kem[who])
            m = r.message
            tags.add(before.tag)
            assert m.type == SEND_TABLE[before.tag], (before.name, m.type)
            assert m.epoch == before.epoch and r.epoch == before.epoch - 1
            assert (m.codeword is not None) == (m.type != K.AG_NONE)
            if before.tag == B.KEYS_UNSAMPLED:                       # (1)
                assert m.codeword[0] == 0 and r.state.tag == B.KEYS_SAMPLED
                assert r.state.hdr_enc.next == 1 and len(r.state.hdr_enc.chunks) == 3
            elif before.tag == B.HEADER_RECEIVED:                    # (7)
                assert m.codeword[0] == 0 and r.state.tag == B.CT1_SAMPLED
                assert r.state.ct1_enc.next == 1 and len(r.state.ct1_enc.chunks) == 44
            else:
                assert r.state.tag == before.tag, before.name        # every other send changes only its encoder
                if m.codeword is not None:
                    enc = getattr(before, sends_from[before.tag])
                    assert m.codeword == (enc.next, enc.codeword(enc.next))
                    assert getattr(r.state, sends_from[before.tag]).next == enc.next + 1
            st[who] = r.state
            if deliver(who, i, m):
                prev = st[other]
                nxt = B.receive(prev, m, kem[other]).state
                if (prev.tag, nxt.tag) == (B.KEYS_SAMPLED, B.HEADER_SENT):
                    assert nxt.ek_enc.next == 0                      # (2) starts the ek_vector encoder
                if (prev.tag, nxt.tag) == (B.HEADER_SENT, B.CT1_RECEIVED):
                    assert nxt.ek_enc == prev.ek_enc                 # Ct1Received continues its indices
                    carried.add(3)
                if (prev.tag, nxt.tag) == (B.CT1_SAMPLED, B.EK_RECEIVED_CT1_SAMPLED):
                    assert nxt.ct1_enc == prev.ct1_enc               # EkReceivedCt1Sampled continues (7)'s encoder
                    carried.add(10)
                st[other] = nxt
    assert tags == set(SEND_TABLE), sorted(B.STATE_NAMES[t] for t in set(SEND_TABLE) - tags)
    assert carried == {3, 10}
    assert B.send(B.init_initiator(SK), kems()[0]).epoch == 0


@case("BR-06 an honest run in strict alternation: each epoch's key is output once on each side with that epoch, by (7) on the encapsulating side's send and by (5) on the other's receive; the roles swap every epoch; about a hundred messages per epoch",
      f"{MB} When an epoch completes; Properties a caller must know, Healing cost")
def _():
    run = Run()
    run.until_epoch(6)
    oa, ob = run.outputs["a"], run.outputs["b"]
    for e in range(1, 7):
        enc_side, dec_side = (ob, oa) if e % 2 else (oa, ob)        # the responder encapsulates at epoch 1
        assert enc_side[e - 1][0] == "send" and dec_side[e - 1][0] == "recv"
        assert enc_side[e - 1][1] == dec_side[e - 1][1] and enc_side[e - 1][1][0] == e
    assert [x[1][0] for x in oa] == list(range(1, len(oa) + 1))
    assert all(x[1] != y[1] for x, y in zip(oa, oa[1:]))
    per_epoch = run.messages / 6
    assert 80 <= per_epoch <= 130, per_epoch
    assert all(run.st[w].tag != B.FAILED for w in "ab")


@case("BR-07 what a send and a receive return: a receive reports the epoch of the state it leaves, less one, and 0 at Failed; a receive taking (5) reports the completed epoch, its output's (ADR-0007); at (13) the two readings agree; the send taking (7) reports the epoch before its output's",
      f"{MB} What a send and a receive return; ADR-0007 decision 3")
def _():
    run = Run()
    run.until_epoch(3)
    for who, op, before, after, r in run.log:
        if op == "recv":
            assert r.epoch == (0 if after == B.FAILED else run_epoch_after(r) - 1)
            if (before, after) == (B.EK_SENT_CT1_RECEIVED, B.NO_HEADER_RECEIVED):
                assert r.output is not None and r.epoch == r.output[0]
            if (before, after) == (B.CT2_SAMPLED, B.KEYS_UNSAMPLED):
                assert r.epoch == r.state.epoch - 1 and r.output is None
        elif (before, after) == (B.HEADER_RECEIVED, B.CT1_SAMPLED):
            assert r.output is not None and r.epoch == r.output[0] - 1
    f = B.receive(B.State(B.FAILED), B.Message(1, K.AG_NONE), kems()[0])
    assert (f.epoch, f.output, f.state.tag) == (0, None, B.FAILED)


def run_epoch_after(r):
    return r.state.epoch


# --------------------------------------------------- What a receive ignores

def _states_by_tag(run):
    out = {}
    for who, op, before, after, r in run.log:
        out.setdefault(after, (r.state, run.kem[who]))
    return out


@case("BR-08 what a receive ignores: a message at another epoch, a type not awaited, an awaited type with no codeword (an EkCt1Ack in Ct1Sampled takes neither (8) nor (9)); Ct1Acknowledged ignores Ek; KeysUnsampled and HeaderReceived ignore everything; (12) reads only the type; (13) reads only the epoch",
      f"{MB} What a receive ignores; The state machine, Receiving")
def _():
    run = Run()
    run.alternate(120, deliver=lambda who, i, m: not (who == "b" and m.type == K.AG_CT1 and m.codeword[0] != 0 and i < 70))
    run.alternate(150)
    states = _states_by_tag(run)
    cw = (0, bytes(32))
    for tag, (s, kem) in states.items():
        if tag == B.FAILED:
            continue
        e = s.epoch
        for typ in sorted(K.AG_TYPES):
            for epoch in (e - 1, e + 2):
                m = B.Message(epoch, typ, cw)
                assert B.export(B.receive(s, m, kem).state) == B.export(s), (s.name, typ, epoch)
            if tag not in (B.CT2_SAMPLED, B.EK_RECEIVED_CT1_SAMPLED):
                assert B.export(B.receive(s, B.Message(e, typ, None), kem).state) == B.export(s), (s.name, typ)
        if tag in (B.KEYS_UNSAMPLED, B.HEADER_RECEIVED):
            for typ in sorted(K.AG_TYPES):
                assert B.export(B.receive(s, B.Message(e, typ, cw), kem).state) == B.export(s)
        if tag == B.CT1_ACKNOWLEDGED:
            assert B.export(B.receive(s, B.Message(e, K.AG_EK, cw), kem).state) == B.export(s)
        if tag == B.CT2_SAMPLED:
            for typ in sorted(K.AG_TYPES):
                for c in (None, cw):
                    r = B.receive(s, B.Message(e + 1, typ, c), kem)
                    assert (r.state.tag, r.state.epoch, r.state.auth) == (B.KEYS_UNSAMPLED, e + 1, s.auth)
            assert B.export(B.receive(s, B.Message(e, K.AG_CT2, cw), kem).state) == B.export(s)
        if tag == B.EK_RECEIVED_CT1_SAMPLED:
            assert B.receive(s, B.Message(e, K.AG_EK_CT1_ACK, None), kem).state.tag == B.CT2_SAMPLED
    assert B.CT1_SAMPLED in states and B.EK_RECEIVED_CT1_SAMPLED in states and B.CT2_SAMPLED in states


@case("BR-09 all thirteen transitions occur, each between the states the page names, and no other change of state occurs in honest runs with loss; every run agrees on every epoch key",
      f"{MB} The state machine, Sending and Receiving, transitions (1)-(13)")
def _():
    seen, unexpected = set(), set()
    scenarios = [
        dict(),                                                           # strict alternation
        dict(deliver=lambda who, i, m: not (who == "b" and m.type == K.AG_CT1 and i % 3)),   # ct1 late: (10), (12)
        dict(deliver=lambda who, i, m: not (who == "a" and m.type == K.AG_EK and i < 45)),    # ek late: (8), (11)
        # 47 Ek codewords held, then ct1 completes and the 48th arrives on an EkCt1Ack: (9)
        dict(deliver=lambda who, i, m: not ((who == "a" and m.type == K.AG_EK and m.codeword[0] >= 47)
                                            or (who == "b" and m.type == K.AG_CT1 and m.codeword[0] != 0 and i < 70))),
        dict(deliver=lambda who, i, m: (i * 7 + len(who)) % 3 != 0),       # a third of everything lost
    ]
    for sc in scenarios:
        run = Run()
        run.until_epoch(4, **sc)
        for (before, after, op) in run.seen:
            if after == B.FAILED or (before, after, op) not in TRANSITIONS:
                unexpected.add((B.STATE_NAMES[before], B.STATE_NAMES[after], op))
            else:
                seen.add(TRANSITIONS[(before, after, op)])
        oa, ob = run.outputs["a"], run.outputs["b"]
        n = min(len(oa), len(ob))
        assert n >= 4 and [x[1] for x in oa[:n]] == [x[1] for x in ob[:n]]
    assert not unexpected, unexpected
    assert seen == set(range(1, 14)), sorted(set(range(1, 14)) - seen)


# ------------------------------------------------------------------- Failure

def _drive_to(run, predicate, limit=400, deliver=lambda who, i, m: True):
    for i in range(limit):
        for who in ("a", "b"):
            r = run.send(who)
            if r.message is not None and deliver(who, i, r.message):
                run.recv("b" if who == "a" else "a", r.message)
            if predicate(run):
                return who
    raise AssertionError("state never reached")


@case("BR-10 MAC failures: a header whose MAC does not verify moves the receiver to Failed on the receive that completes it and not before; a completed ct2 whose MacCt does not verify moves it to Failed at (5), with no output; a corrupted ct1 is not detected until ct2 arrives",
      f"{MB} Failure; The state machine, Receiving (5) and NoHeaderReceived; Properties a caller must know: ct1 is authenticated when ct2 arrives")
def _():
    run = Run(sk_b=b"\x01" * 32)              # the responder's authenticator is keyed differently
    run.step("a")
    run.step("a")
    assert run.st["b"].tag == B.NO_HEADER_RECEIVED
    run.step("a")
    assert run.st["b"].tag == B.FAILED and not run.outputs["b"]
    # ct2's MAC: corrupt one byte of the MAC-carrying chunk of ct2 || MacCt
    run = Run()
    _drive_to(run, lambda r: r.st["a"].tag == B.EK_SENT_CT1_RECEIVED)
    while run.st["a"].tag == B.EK_SENT_CT1_RECEIVED:
        run.step("b", mutate=lambda m: flip_chunk(m, 31) if m.type == K.AG_CT2 and m.codeword[0] == 5 else m)
        run.step("a")
    assert run.st["a"].tag == B.FAILED and not run.outputs["a"]
    # ct1 corrupted in transit: (2)-(4) accept it, (5) fails
    run = Run()
    _drive_to(run, lambda r: r.st["b"].tag == B.CT1_SAMPLED)
    corrupt = lambda m: flip_chunk(m, 3) if m.type == K.AG_CT1 and m.codeword[0] == 1 else m   # noqa: E731
    for _ in range(300):
        if run.st["a"].tag in (B.NO_HEADER_RECEIVED, B.FAILED):
            break
        run.step("b", mutate=corrupt)
        assert run.st["a"].tag != B.FAILED or run.log[-1][2] == B.EK_SENT_CT1_RECEIVED
        run.step("a")
    assert run.st["a"].tag == B.FAILED and run.outputs["b"] and not run.outputs["a"]


class BadEkKem(ToyIncrementalKem):
    """Generates an ek_vector with a coefficient at q, and a header whose hash covers it."""

    def generate(self):
        key_pair, header, ek_vector = super().generate()
        coeffs = [K.MLKEM_Q] + [0] * 1023
        bad = byte_encode12(coeffs)
        rho = header[:32]
        header = rho + hashlib.sha3_256(bad + rho).digest()
        return bad + key_pair[1536:], header, bad


@case("BR-11 ek_vector validation: a completed ek_vector whose hash is not the authenticated header's, or which fails the FIPS 203 modulus check though the hash matches, moves the encapsulating party to Failed, in Ct1Sampled and in Ct1Acknowledged",
      f"{MB} The KEM split, Validation; Failure; The state machine, Receiving Ct1Sampled and Ct1Acknowledged")
def _():
    assert not B.validate_ek_vector(bytes(64), bytes(1536))
    for where in ("Ct1Sampled", "Ct1Acknowledged"):
        for how in ("hash", "modulus"):
            ka, kb = kems(how.encode())
            if how == "modulus":
                ka = BadEkKem(b"bad")
            run = Run(kem_a=ka, kem_b=kb)
            _drive_to(run, lambda r: r.st["b"].tag == B.CT1_SAMPLED)
            if where == "Ct1Acknowledged":
                # hold every Ek back, so the acknowledgement arrives with ek_vector incomplete: (8)
                _drive_to(run, lambda r: r.st["b"].tag in (B.CT1_ACKNOWLEDGED, B.FAILED),
                          deliver=lambda who, i, m: not (who == "a" and m.type == K.AG_EK))
                assert run.st["b"].tag == B.CT1_ACKNOWLEDGED
                hold_ct1 = False
            else:
                hold_ct1 = True        # ct1 held back, so every ek_vector codeword arrives as Ek, in Ct1Sampled
            mutate = (lambda m: flip_chunk(m, 0) if m.type in (K.AG_EK, K.AG_EK_CT1_ACK) and m.codeword else m) \
                if how == "hash" else None
            for _ in range(200):
                if run.st["b"].tag in (B.FAILED, B.CT2_SAMPLED, B.EK_RECEIVED_CT1_SAMPLED):
                    break
                before = run.st["b"].tag
                run.step("a", mutate=mutate)
                if run.st["b"].tag == B.FAILED:
                    assert before == {"Ct1Sampled": B.CT1_SAMPLED, "Ct1Acknowledged": B.CT1_ACKNOWLEDGED}[where], (where, how, B.STATE_NAMES[before])
                run.step("b", deliver=not hold_ct1)
            assert run.st["b"].tag == B.FAILED, (where, how, run.st["b"].name)


@case("BR-12 KEM failures and Failed: key generation failing on the send that would take (1), the first half of encapsulation on (7), decapsulation in (5), the second half in (9), (11) or (12) each move to Failed; Failed puts nothing on the wire, yields no key, reports epoch 0 and stays Failed",
      f"{MB} Failure")
def _():
    r = B.send(B.init_initiator(SK), ToyIncrementalKem(b"x", fail_on={"generate"}))
    assert (r.state.tag, r.message, r.epoch, r.output) == (B.FAILED, None, 0, None)
    run = Run()
    _drive_to(run, lambda r: r.st["b"].tag == B.HEADER_RECEIVED)
    r = B.send(run.st["b"], ToyIncrementalKem(b"x", fail_on={"encaps1"}))
    assert (r.state.tag, r.message, r.output) == (B.FAILED, None, None)
    for fail, holder, where in (("decaps", "a", B.EK_SENT_CT1_RECEIVED), ("encaps2", "b", B.CT1_SAMPLED)):
        run = Run()
        _drive_to(run, lambda r: r.st[holder].tag == where)
        run.kem[holder].fail_on.add(fail)
        _drive_to(run, lambda r: r.st[holder].tag == B.FAILED, limit=200)
    for scenario, stop in ((dict(deliver=lambda who, i, m: not (who == "b" and m.type == K.AG_CT1 and i % 3)), B.EK_RECEIVED_CT1_SAMPLED),
                           (dict(deliver=lambda who, i, m: not (who == "a" and m.type == K.AG_EK and i < 45)), B.CT1_ACKNOWLEDGED)):
        run = Run()
        _drive_to(run, lambda r: r.st["b"].tag == stop, **scenario)
        run.kem["b"].fail_on.add("encaps2")
        _drive_to(run, lambda r: r.st["b"].tag == B.FAILED, limit=200)
    failed = B.State(B.FAILED)
    for _ in range(3):
        s = B.send(failed, kems()[0])
        r = B.receive(failed, B.Message(1, K.AG_CT1, (0, bytes(32))), kems()[0])
        assert (s.state.tag, s.message, s.epoch, s.output) == (B.FAILED, None, 0, None)
        assert (r.state.tag, r.epoch, r.output) == (B.FAILED, 0, None)


@case("BR-13 the epoch ceiling at u64::MAX - 1: in EkSentCt1Received completing ct2 fails and every other message is handled as at any other epoch; in Ct2Sampled any received message fails, whatever its epoch or type",
      f"{MB} Failure: reaching the reserved epoch u64::MAX; session-persistence.md Principles")
def _():
    top = K.U64_MAX - 1
    run = Run()
    _drive_to(run, lambda r: r.st["a"].tag == B.EK_SENT_CT1_RECEIVED)
    a, kem = replace(run.st["a"], epoch=top), run.kem["a"]
    ct2s = []
    b = run.st["b"]
    while len(ct2s) < 6:
        rb = B.send(b, run.kem["b"])
        b = rb.state
        if rb.message.type == K.AG_CT2:
            ct2s.append(replace(rb.message, epoch=top))
    have = len(a.ct2_dec.held)
    for m in ct2s[have:5]:
        a = B.receive(a, m, kem).state
        assert a.tag == B.EK_SENT_CT1_RECEIVED and a.epoch == top
    assert B.receive(a, B.Message(top, K.AG_HDR, (0, bytes(32))), kem).state.tag == B.EK_SENT_CT1_RECEIVED
    assert B.receive(a, ct2s[5], kem).state.tag == B.FAILED
    _drive_to(run, lambda r: r.st["b"].tag == B.CT2_SAMPLED)
    c2 = replace(run.st["b"], epoch=top)
    for m in (B.Message(top + 1, K.AG_NONE), B.Message(top, K.AG_CT2, (0, bytes(32))), B.Message(3, K.AG_HDR)):
        assert B.receive(c2, m, run.kem["b"]).state.tag == B.FAILED
    ok = replace(run.st["b"], epoch=5)
    assert B.receive(ok, B.Message(5, K.AG_NONE), run.kem["b"]).state.tag == B.CT2_SAMPLED


@case("BR-14 encoder lifetime: a state whose encoder is exhausted sends None with no codeword, stamped with its epoch, and does not change",
      f"{MB} Properties a caller must know, Encoder lifetime; The state machine, Sending")
def _():
    run = Run()
    _drive_to(run, lambda r: r.st["a"].tag == B.KEYS_SAMPLED)
    s = copy.deepcopy(run.st["a"])
    s.hdr_enc = erasure.Encoder(s.hdr_enc.chunks, K.U16_MAX, True)
    r = B.send(s, run.kem["a"])
    assert (r.message.type, r.message.codeword, r.message.epoch) == (K.AG_NONE, None, s.epoch)
    assert B.export(r.state) == B.export(s)
    s.hdr_enc = erasure.Encoder(s.hdr_enc.chunks, K.U16_MAX, False)
    r = B.send(s, run.kem["a"])
    assert r.message.codeword[0] == K.U16_MAX and r.state.hdr_enc.exhausted
    assert B.send(r.state, run.kem["a"]).message.codeword is None


@case("BR-15 persistence: every state an honest run passes through exports, imports to the same state under the reader's rules, and goes on identically; key_pair and encaps travel as opaque bytes of their stated lengths",
      f"session-persistence.md Braid; Semantic rules of the leaf formats, Braid; {MB} States")
def _():
    run = Run()
    run.alternate(40, deliver=lambda who, i, m: not (who == "b" and m.type == K.AG_CT1 and i % 3))
    run.until_epoch(3)
    run.st["b"] = B.State(B.FAILED)
    tags = set()
    for who, op, before, after, r in run.log + [("b", "x", 0, B.FAILED, B.ReceiveResult(run.st["b"], 0, None))]:
        s = r.state
        blob = B.export(s)
        back = accepts(B.import_, blob)
        assert B.export(back) == blob
        tags.add(s.tag)
        if s.tag != B.FAILED:
            assert persistence.braid_invariant(B.to_persisted(s)) is None
            k1, k2 = copy.deepcopy(run.kem[who]), copy.deepcopy(run.kem[who])
            assert B.export(B.send(s, k1).state) == B.export(B.send(back, k2).state)
            if s.key_pair is not None:
                assert len(s.key_pair) == 11872
            if s.encaps is not None:
                assert len(s.encaps) == 2592
    assert tags == set(range(12)), sorted(set(range(12)) - tags)


@case("BR-16 the composite header carries the Braid message: ag_epoch is ToBytes(epoch), ag_type the type's byte, chunk_present 0x01 with a codeword and 0x00 with zero index and chunk without; a receive hands the Braid the message those fields describe; Ct1Ack has no byte",
      f"{MB} Messages, On the wire; message-format.md Ratchet message")
def _():
    run = Run()
    run.alternate(60)
    kinds = set()
    for who, op, before, after, r in run.log:
        if op != "send":
            continue
        m = r.message
        h = wire.CompositeHeader(dh=b"\x09" * 32, pn=0, n=0, pq_epoch=r.epoch, pq_n=1, **B.header_fields(m))
        raw = wire.encode_composite(h)
        assert raw[58:66] == B.to_bytes(m.epoch) and raw[66] == m.type
        assert raw[67] == (1 if m.codeword else 0)
        if m.codeword is None:
            assert raw[68:] == bytes(34)
        else:
            assert raw[68:70] == m.codeword[0].to_bytes(2, "big") and raw[70:] == m.codeword[1]
        assert B.message_from_header(wire.decode_composite(raw)) == m
        kinds.add(m.type)
    assert kinds == set(K.AG_TYPES) - {K.AG_EK_CT1_ACK} | ({K.AG_EK_CT1_ACK} & kinds)
    raw = bytearray(wire.encode_composite(wire.CompositeHeader(b"\x09" * 32, 0, 0, 0, 1, 1, K.AG_NONE, None)))
    raw[66] = 0x06
    rejects(wire.decode_composite, bytes(raw), exc=wire.DecodeError)


# ------------------------------------------------ with the Triple Ratchet

IKA, IKB = x25519_public(b"\x61" * 32), x25519_public(b"\x62" * 32)
AD = wire.encode_ec(IKA) + wire.encode_ec(IKB)
SPK_PRIV = b"\x5b" * 32
_fresh = [0]


def fresh():
    _fresh[0] += 1
    return hashlib.sha256(b"fresh" + _fresh[0].to_bytes(8, "big")).digest()


def session_pair(sk_braid_b=SK):
    ka, kb = kems(b"session")
    alice = triple.init_initiator(SK, AD, b"\xa0" * 32, x25519_public(SPK_PRIV), B.init_initiator(SK))
    bob = triple.init_responder(SK, AD, SPK_PRIV, B.init_responder(sk_braid_b))
    return alice, bob, B.BraidAgreement(ka), B.BraidAgreement(kb)


def persisted_relation(party, initiator):
    """session-persistence.md, Session, Semantic rules: the sparse ratchet's
    epoch follows the Braid's, and the halves agree on the role."""
    b, sp = party.agreement_state, party.sparse
    if b.tag == B.FAILED:
        return sp.direction == (spqr.A2B if initiator else spqr.B2A)
    want = b.epoch if b.tag in (7, 8, 9, 10) else b.epoch - 1
    header_side = b.tag <= 4
    return (sp.epoch == want and header_side == (initiator == (b.epoch % 2 == 1))
            and sp.direction == (spqr.A2B if initiator else spqr.B2A))


@case("BR-17 the session: encrypt runs the Braid's send first and hands the sparse ratchet the sending epoch and any output; decrypt hands it any output; over two post-quantum epochs every message decrypts, pq_epoch is the sending epoch and ag_epoch the Braid's, and after every message both parties keep session-persistence.md's epoch and role relations",
      f"{MB} What the session does with them; sparse-pq-ratchet.md Sending, Receiving; session-persistence.md Session, Semantic rules")
def _():
    alice, bob, ag_a, ag_b = session_pair()
    parties = {"a": alice, "b": bob}
    ags = {"a": ag_a, "b": ag_b}
    for i in range(125):
        for who, other in (("a", "b"), ("b", "a")):
            before = parties[who].agreement_state
            parties[who], msg = triple.encrypt(parties[who], ags[who], b"m%d" % i)
            h = wire.decode_composite(msg[:K.COMPOSITE_LEN])
            # ag_epoch is the state's epoch; pq_epoch is the sending epoch, the state's epoch less one
            assert h.ag_epoch == before.epoch and h.pq_epoch == before.epoch - 1
            parties[other], pt = accepts(triple.decrypt, parties[other], ags[other], msg, fresh())
            assert pt == b"m%d" % i
            assert persisted_relation(parties["a"], True) and persisted_relation(parties["b"], False), i
    assert parties["a"].sparse.epoch >= 2 and parties["b"].sparse.epoch >= 2


@case("BR-18 AgreementFailed: a receive whose Braid transition fails is adopted only once its message authenticates, and that message's plaintext is returned; from then on encrypt and decrypt are refused; a send that fails keeps the failed state and is refused too",
      f"{MB} Failure (last paragraph)")
def _():
    alice, bob, ag_a, ag_b = session_pair(sk_braid_b=b"\x01" * 32)
    for i in range(3):
        alice, msg = triple.encrypt(alice, ag_a, b"hdr %d" % i)
        if i == 2:
            forged = bytearray(msg)
            forged[-1] ^= 1
            rejects(triple.decrypt, bob, ag_b, bytes(forged), fresh(), exc=Exception)
            assert bob.agreement_state.tag == B.NO_HEADER_RECEIVED
        bob, pt = accepts(triple.decrypt, bob, ag_b, msg, fresh())
        assert pt == b"hdr %d" % i
    assert bob.agreement_state.tag == B.FAILED
    rejects(triple.encrypt, bob, ag_b, b"x", exc=B.AgreementFailed)
    alice, msg = triple.encrypt(alice, ag_a, b"later")
    rejects(triple.decrypt, bob, ag_b, msg, fresh(), exc=B.AgreementFailed)
    # a send that fails
    alice2, bob2, _, ag_b2 = session_pair()
    ag_a_failing = B.BraidAgreement(ToyIncrementalKem(b"x", fail_on={"generate"}))
    e = rejects(triple.encrypt, alice2, ag_a_failing, b"x", exc=B.AgreementFailed)
    assert e.state.tag == B.FAILED
    alice2 = replace(alice2, agreement_state=e.state)
    rejects(triple.encrypt, alice2, ag_a_failing, b"x", exc=B.AgreementFailed)
