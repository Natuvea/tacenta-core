"""Triple Ratchet composition cases: split halves, commit rules, the
non-contributory check, eviction retry. The Braid is replaced by test doubles
(triple.NullAgreement, triple.ScriptedAgreement); no vector covers any of this."""

from dataclasses import replace

from _casekit import accepts, flip, put, registry, rejects
from tacenta_reader import aead, ratchet, spqr, triple, wire
from tacenta_reader import constants as K
from tacenta_reader.curve25519 import NonContributory, x25519, x25519_public

CASES, case = registry()
TR = "triple-ratchet.md"
RM = "ratchet.md"

IKA = x25519_public(b"\x61" * 32)
IKB = x25519_public(b"\x62" * 32)
AD = wire.encode_ec(IKA) + wire.encode_ec(IKB)
SK = bytes(range(200, 232))
SPK_PRIV = b"\x5b" * 32
SPK_PUB = x25519_public(SPK_PRIV)
NULL = triple.NullAgreement()

_counter = [0]


def fresh():
    _counter[0] += 1
    return _counter[0].to_bytes(4, "big") * 8


def pair(agreement_state=None):
    alice = triple.init_initiator(SK, AD, b"\xa0" * 32, SPK_PUB, agreement_state)
    bob = triple.init_responder(SK, AD, SPK_PRIV, agreement_state)
    return alice, bob


def dec(party, msg, agreement=NULL, evict=False):
    fn = triple.decrypt_with_eviction if evict else triple.decrypt
    return fn(party, agreement, msg, fresh())


@case("TR-01 split: first 32 bytes initialise the Double Ratchet, last 32 the sparse ratchet (A2b initiator, B2a responder); traffic both ways decrypts",
      f"{TR} Initialisation: The first 32 initialise the Double Ratchet ... and the last 32 the sparse ratchet")
def _():
    c_half, s_half = triple.split_secret(SK)
    alice, bob = pair()
    assert alice.classical == ratchet.init_initiator(c_half, x25519_public(b"\xa0" * 32), SPK_PUB, x25519(b"\xa0" * 32, SPK_PUB))
    assert bob.classical == ratchet.init_responder(c_half, SPK_PUB)
    assert alice.sparse == spqr.init(s_half, spqr.A2B) and bob.sparse == spqr.init(s_half, spqr.B2A)
    script = [("a", b"hello"), ("a", b""), ("b", b"x" * 16), ("a", b"y" * 33), ("b", b"z"), ("b", b"w")]
    parties = {"a": alice, "b": bob}
    for who, pt in script:
        other = "b" if who == "a" else "a"
        parties[who], msg = triple.encrypt(parties[who], NULL, pt)
        parties[other], got = accepts(dec, parties[other], msg)
        assert got == pt
    # halves swapped: nothing authenticates
    bad = triple.Party(ratchet.init_responder(s_half, SPK_PUB), spqr.init(c_half, spqr.B2A), SPK_PRIV, None, AD)
    _, msg = triple.encrypt(alice, NULL, b"hello")
    rejects(dec, bad, msg, exc=aead.AuthenticationFailure)


@case("TR-02 the 32-byte combination goes through the message-key expansion; salt is the sparse key, IKM the classical key",
      f"{TR} What the combination must be: the message-key expansion turns it into the AES-256 key, the HMAC-SHA256 key and the IV")
def _():
    alice, _ = pair()
    _, hdr, mk_ec = ratchet.send(alice.classical)
    _, _, _, mk_pq = spqr.send(alice.sparse, 0)
    _, msg = triple.encrypt(alice, NULL, b"payload")
    header_bytes = msg[:K.COMPOSITE_LEN]
    combined = triple.combine(mk_ec, mk_pq)
    assert msg[K.COMPOSITE_LEN:] == aead.seal(combined, wire.concat_ad(AD, header_bytes), b"payload")
    enc, mac, iv = ratchet.expand_message_key(combined)
    rejects(aead.decrypt, combined, mac, iv, wire.concat_ad(AD, header_bytes), msg[K.COMPOSITE_LEN:],
            exc=aead.AuthenticationFailure)
    swapped = triple.combine(mk_pq, mk_ec)
    assert swapped != combined


class _BadEpoch(triple.NullAgreement):
    def send(self, state):
        return triple.AgreementSend(state, 5, K.AG_NONE, None, 5)


@case("TR-03 a send runs on a copy: a refusal from the sparse half (NoChain) changes neither half",
      f"{TR} Sending and receiving: A send runs on a copy of the state ... A refusal from either half changes neither")
def _():
    alice, _ = pair()
    snapshot = (alice.classical.clone(), alice.sparse.clone())
    rejects(triple.encrypt, alice, _BadEpoch(), b"x", exc=spqr.NoChain)
    assert (alice.classical, alice.sparse) == snapshot


@case("TR-04 a receive yields a candidate adopted only after authentication: a forged tag changes nothing, including the DH step and the private key",
      f"{TR} Sending and receiving: The candidate is adopted only once the message has authenticated under that key")
def _():
    alice, bob = pair()
    alice, m1 = triple.encrypt(alice, NULL, b"one")
    bob, _ = dec(bob, m1)
    bob, reply = triple.encrypt(bob, NULL, b"two")      # alice will take a DH step on this
    snapshot = alice
    forged = flip(reply, len(reply) - 1)
    rejects(dec, alice, forged, exc=aead.AuthenticationFailure)
    assert alice is snapshot and alice.classical == snapshot.classical and alice.ratchet_private == b"\xa0" * 32
    alice2, got = accepts(dec, alice, reply)
    assert got == b"two" and alice2.ratchet_private != alice.ratchet_private and alice2.classical.events == 1


@case("TR-05 the associated data is the whole composite header: stripping or changing the codeword fails authentication",
      f"message-format.md Associated data: an intermediary could strip the agreement's message ... Binding the full composite is what rules that out")
def _():
    class WithCodeword(triple.NullAgreement):
        def send(self, state):
            return triple.AgreementSend(state, 0, K.AG_CT1, wire.Codeword(3, b"\x77" * 32), 0)
    alice, bob = pair()
    _, msg = triple.encrypt(alice, WithCodeword(), b"pq part attached")
    h, ct = wire.decode_ratchet_message(msg)
    stripped = wire.encode_ratchet_message(replace(h, ag_type=K.AG_NONE, codeword=None), ct)
    rejects(dec, bob, stripped, exc=aead.AuthenticationFailure)
    changed = wire.encode_ratchet_message(replace(h, codeword=wire.Codeword(4, b"\x77" * 32)), ct)
    rejects(dec, bob, changed, exc=aead.AuthenticationFailure)
    accepts(dec, bob, msg)


@case("TR-06 a header ratchet key with a non-contributory output is refused before either ratchet runs and before the tag",
      f"{TR} Sending and receiving: If either is not contributory ... the message is refused and nothing changes. The check runs whether or not the message would take a step")
def _():
    alice, bob = pair()
    alice, msg = triple.encrypt(alice, NULL, b"x")
    h, ct = wire.decode_ratchet_message(msg)
    order8 = bytes.fromhex("e0eb7a7c3b41b8ae1656e3faf19fc46ada098deb9c32b1fd866205165f49b800")
    for low in (bytes(32), (1).to_bytes(32, "little"), order8):
        # with a skip demand past MAX_SKIP and a garbage tag: the contributory check must win
        bad = wire.encode_ratchet_message(replace(h, dh=low, pn=5000, n=5000), b"\x00" * 3)
        rejects(dec, bob, bad, exc=NonContributory)
    # the responder's current private key is the signed prekey's (the ratchet message in an initial message)
    bob2, _ = accepts(dec, bob, msg)
    same_key = wire.encode_ratchet_message(replace(h, dh=order8), ct)
    rejects(dec, bob2, same_key, exc=NonContributory)


def _stuff(state, count, stored_at=0, tag=0xEE):
    s = state.clone()
    for i in range(count):
        s.skipped[(bytes([tag]) * 31 + bytes([i % 256]), 100000 + i)] = (b"\x00" * 32, stored_at)
    return s


@case("TR-07 a full classical store makes room: oldest evicted on a working copy, message accepted; the evicted delayed message is lost",
      f"{RM} Skipped keys: A full store makes room rather than refusing the message ... A delayed message whose key was evicted can no longer be decrypted")
def _():
    alice, bob = pair()
    msgs = []
    for i in range(3):
        alice, m = triple.encrypt(alice, NULL, b"m%d" % i)
        msgs.append(m)
    bob, _ = dec(bob, msgs[2])                         # stores keys for m0, m1 at count 0, in that order
    full = replace(bob, classical=_stuff(bob.classical, K.MAX_SKIPPED_STORE - 2, stored_at=0))
    assert len(full.classical.skipped) == K.MAX_SKIPPED_STORE
    for i in (3, 4):
        alice, m = triple.encrypt(alice, NULL, b"m%d" % i)
        msgs.append(m)
    rejects(dec, full, msgs[4], exc=ratchet.SkippedStoreFull)          # without eviction
    forged = flip(msgs[4], len(msgs[4]) - 1)
    rejects(dec, full, forged, evict=True, exc=aead.AuthenticationFailure)   # a forged header evicts nothing
    assert len(full.classical.skipped) == K.MAX_SKIPPED_STORE
    after, got = accepts(dec, full, msgs[4], evict=True)
    assert got == b"m4" and len(after.classical.skipped) == K.MAX_SKIPPED_STORE
    rejects(dec, after, msgs[0], exc=ratchet.OutOfOrder)               # its key was the oldest: evicted
    _, got = accepts(dec, after, msgs[1])
    assert got == b"m1"


@case("TR-08 a full sparse store makes room the same way (sparse half refuses SkippedStoreFull)",
      f"sparse-pq-ratchet.md The store also has a total bound: The receiver then makes room as the Double Ratchet's does")
def _():
    alice, bob = pair()
    alice, m0 = triple.encrypt(alice, NULL, b"a")
    bob, _ = dec(bob, m0)
    s = bob.sparse.clone()
    for i in range(K.MAX_SKIPPED_STORE):
        s.skipped[(0, 10_000 + i)] = b"\x00" * 32
    full = replace(bob, sparse=s)
    alice, _ = triple.encrypt(alice, NULL, b"b")
    alice, m2 = triple.encrypt(alice, NULL, b"c")
    rejects(dec, full, m2, exc=spqr.SkippedStoreFull)
    after, got = accepts(dec, full, m2, evict=True)
    assert got == b"c" and (0, 10_000) not in after.sparse.skipped and len(after.sparse.skipped) == K.MAX_SKIPPED_STORE


@case("TR-09 an empty store that still cannot take the message is refused (no eviction possible)",
      f"{RM} Skipped keys: and refuses it if the store is already empty")
def _():
    alice, bob = pair()
    s = bob.sparse.clone()
    s.skipped = {}
    rejects(triple.decrypt_with_eviction, replace(bob, sparse=s), NULL,
            wire.encode_ratchet_message(wire.CompositeHeader(SPK_PUB, 0, 0, 0, 5000, 0, 0, None), b""),
            fresh(), exc=(spqr.TooManySkipped, ratchet.RatchetError, NonContributory, aead.AuthenticationFailure))


@case("TR-10 an agreement secret opens epoch 1 on both sides through the composition; the message carrying it is sent on epoch 0",
      f"sparse-pq-ratchet.md Sending: the message carrying the secret that opens an epoch is itself sent on the epoch before")
def _():
    ag = triple.ScriptedAgreement(b"\x5e" * 32, trigger=2)
    alice, bob = pair(agreement_state=(0, 0))
    for i in range(4):
        alice, m = triple.encrypt(alice, ag, b"%d" % i)
        h, _ = wire.decode_ratchet_message(m)
        assert h.pq_epoch == (0 if i < 2 else 1)
        bob, got = accepts(dec, bob, m, ag)
        assert got == b"%d" % i
    assert alice.sparse.epoch == bob.sparse.epoch == 1
    bob, m = triple.encrypt(bob, ag, b"back")
    alice, got = accepts(dec, alice, m, ag)
    assert got == b"back"
