"""Double Ratchet and sparse ratchet additions: counter ceilings, the stale
same-chain refusal, DH step triggers and skip checks, the store bound,
eviction order and the clock ceiling. No vector covers these except where a
case says so."""

from _casekit import accepts, registry, rejects
from tacenta_reader import constants as K
from tacenta_reader import ratchet, spqr

CASES, case = registry()
RM = "ratchet.md"
SP = "sparse-pq-ratchet.md"
SPS = "session-persistence.md"

K1, K2, K3 = b"\x1a" * 32, b"\x2a" * 32, b"\x3a" * 32
SPK = b"\x0b" * 32


def _dh(tag):
    def step(header_dh):
        return bytes([tag]) * 32, bytes([tag ^ 0xF0]) * 32, bytes([tag ^ 0x0F]) * 32
    return step


def _recv(state, dh, pn, n, tag=1):
    return ratchet.receive(state, ratchet.Header(dh, pn, n), _dh(tag))


def _bob():
    return ratchet.init_responder(b"\x01" * 32, SPK)


def _alice():
    return ratchet.init_initiator(b"\x01" * 32, K1, SPK, b"\xab" * 32)


# ================================================================ classical

@case("CR-01 Ns = u32::MAX refuses a send (ChainExhausted) before anything changes; Ns = u32::MAX - 1 is the last send",
      f"{RM} Sending and receiving: Send: refused, before anything changes, if ... Ns is u32::MAX (ChainExhausted)")
def _():
    a = _alice()
    a.ns = K.U32_MAX - 1
    a2, h, _ = accepts(ratchet.send, a)
    assert h.n == K.U32_MAX - 1 and a2.ns == K.U32_MAX and a.ns == K.U32_MAX - 1
    rejects(ratchet.send, a2, exc=ratchet.ChainExhausted)


@case("CR-02 message number u32::MAX is never used on a chain: receiving it refuses with ChainExhausted",
      f"{RM} Sending and receiving: refuse if ... Nr is now u32::MAX (ChainExhausted). So message number u32::MAX is never used")
def _():
    b, _, _ = _recv(_bob(), K1, 0, 0)
    b.nr = K.U32_MAX - 1
    b2, _, _ = accepts(_recv, b, K1, 0, K.U32_MAX - 1)
    assert b2.nr == K.U32_MAX
    rejects(_recv, b, K1, 0, K.U32_MAX, exc=ratchet.ChainExhausted)   # skip stores u32::MAX-1, then Nr = u32::MAX


@case("CR-03 the clock stops at u32::MAX - 1, after which keys no longer age",
      f"{RM} Skipped keys: The count stops at u32::MAX - 1, after which keys no longer age")
def _():
    b, _, _ = _recv(_bob(), K1, 0, 0)
    b.events = K.MAX_EVENTS - 1
    b, _, _ = _recv(b, K1, 0, 2)                  # stores (K1, 1) at count MAX_EVENTS - 1
    assert b.events == K.MAX_EVENTS
    b, _, _ = _recv(b, K1, 0, 4)                  # stores (K1, 3) at count MAX_EVENTS
    for n in range(5, 5 + K.MAX_SKIPPED_AGE + 5):
        b, _, _ = _recv(b, K1, 0, n)
        assert b.events == K.MAX_EVENTS
    assert (K1, 3) in b.skipped, "a key stored at the ceiling aged"
    assert (K1, 1) in b.skipped, "age stops at 1 once the count stops"


@case("CR-04 same chain, number below Nr, key not stored: refused (the stale same-chain refusal), caller's state unchanged, next message accepted",
      f"{RM} Sending and receiving: A message whose ratchet key equals DHr, whose number N is below Nr, and whose key is not stored is not accepted")
def _():
    b, _, _ = _recv(_bob(), K1, 0, 2)             # stores 0, 1
    b, _, _ = _recv(b, K1, 0, 0)                  # stored-key receive
    before = b.clone()
    rejects(_recv, b, K1, 0, 0, exc=ratchet.OutOfOrder)   # a duplicate after a stored-key receive
    rejects(_recv, b, K1, 0, 2, exc=ratchet.OutOfOrder)   # a duplicate after an in-order receive
    assert b.__dict__ == before.__dict__
    accepts(_recv, b, K1, 0, 3)
    accepts(_recv, b, K1, 0, 1)


@case("CR-05 a header equal to DHr with no receiving chain is refused (NoReceivingChain): the initiator before its first receive",
      f"{RM} The Diffie-Hellman ratchet: A header whose ratchet key equals DHr while there is no receiving chain is refused (NoReceivingChain)")
def _():
    rejects(_recv, _alice(), SPK, 0, 0, exc=ratchet.NoReceivingChain)


@case("CR-06 DH step triggers: DHr absent, or header key differs from DHr; a return to an earlier key steps too; a stored key is looked up first",
      f"{RM} The Diffie-Hellman ratchet: The comparison is with DHr alone, so a header returning to an earlier ratchet key steps too")
def _():
    b, _, stepped = _recv(_bob(), K1, 0, 1)
    assert stepped, "DHr absent must step"
    b, _, stepped = _recv(b, K1, 0, 2)
    assert not stepped
    b, _, stepped = _recv(b, K2, 3, 0, 2)
    assert stepped and b.dhr == K2
    b, _, stepped = _recv(b, K1, 3, 0)            # (K1, 0) is stored: used, no step
    assert not stepped and b.dhr == K2
    b, _, stepped = _recv(b, K1, 0, 5, 3)         # returning to K1 with an unstored number steps
    assert stepped and b.dhr == K1


@case("CR-07 no MAX_SKIP check on PN when there is no receiving chain (the step-1 skip exists only with a receiving chain)",
      f"{RM} The Diffie-Hellman ratchet, step 1: If there is a receiving chain, store its skipped message keys ... This skip is checked against MAX_SKIP")
def _():
    b, _, _ = accepts(_recv, _bob(), K1, K.U32_MAX, 0)
    assert not b.skipped and b.nr == 1


@case("CR-08 the skip to PN and the skip to N are checked separately: one message may store 2 * MAX_SKIP keys",
      f"{RM} Skipped keys: The skip to PN on the old chain and the skip to N on the new one are checked against it separately")
def _():
    b, _, _ = _recv(_bob(), K1, 0, 0)
    b, _, _ = accepts(_recv, b, K2, 1 + K.MAX_SKIP, K.MAX_SKIP, 2)
    assert len(b.skipped) == 2 * K.MAX_SKIP
    rejects(_recv, _recv(_bob(), K1, 0, 0)[0], K2, 2 + K.MAX_SKIP, 0, 2, exc=ratchet.TooManySkipped)


@case("CR-09 the store bound counts the resulting size: a skip that only replaces held pairs does not push the store past MAX_SKIPPED_STORE",
      f"{RM} Skipped keys: A skip that would push the store past this bound is refused; key-deletion.md: storing a key for a pair already held replaces it")
def _():
    b, _, _ = _recv(_bob(), K1, 0, 1000)          # (K1, 0..999)
    b, _, _ = _recv(b, K2, 1001, 1000, 2)         # (K2, 0..999): 2000
    assert len(b.skipped) == K.MAX_SKIPPED_STORE
    b2, _, stepped = accepts(_recv, b, K1, 1001, 1000, 3)   # new chain under K1 re-stores (K1, 0..999)
    assert stepped and len(b2.skipped) == K.MAX_SKIPPED_STORE
    rejects(_recv, b, K3, 1001, 1, 3, exc=ratchet.SkippedStoreFull)


@case("CR-10 eviction order: smallest stored count first, ties going to the key stored first",
      f"{RM} Skipped keys: Oldest here means the smallest stored count, ties going to the key stored first")
def _():
    b, _, _ = _recv(_bob(), K1, 0, 3)             # (K1,0),(K1,1),(K1,2) at count 0
    b, _, _ = _recv(b, K2, 4, 2, 2)               # (K2,0),(K2,1) at count 1
    b.skipped = dict(list(b.skipped.items())[3:] + list(b.skipped.items())[:3])   # store order: K2 keys first
    e = ratchet.evict(b, 1)
    assert (K1, 0) not in e.skipped and len(e.skipped) == 4, "smallest count must go first"
    e = ratchet.evict(b, 4)
    assert list(e.skipped) == [(K2, 1)]
    same = _recv(_bob(), K1, 0, 3)[0]
    assert list(ratchet.evict(same, 2).skipped) == [(K1, 2)], "ties go to the key stored first"


@case("CR-11 the refusal leaves the caller's state alone, and a refused receive counts for nothing",
      f"{RM} Skipped keys: A receive that is refused, or whose message does not authenticate, counts for nothing")
def _():
    b, _, _ = _recv(_bob(), K1, 0, 1)
    ev = b.events
    rejects(_recv, b, K1, 0, 5000, exc=ratchet.TooManySkipped)
    assert b.events == ev


# =================================================================== sparse

def _pair(sk=b"\x07" * 32):
    return spqr.init(sk, spqr.A2B), spqr.init(sk, spqr.B2A)


@case("CR-12 sparse send: message number u64::MAX is usable; the send after it is refused (ChainExhausted)",
      f"{SP} Sending: The counter is 64-bit: message number u64::MAX is usable, and the send after it is refused as counter exhaustion")
def _():
    a, _ = _pair()
    a.chains[0][0].n = K.U64_MAX - 1
    a2, _, n, _ = accepts(spqr.send, a, 0)
    assert n == K.U64_MAX
    rejects(spqr.send, a2, 0, exc=spqr.ChainExhausted)


@case("CR-13 sparse receive: once the counter is u64::MAX an unstored number is refused as ChainExhausted, not OutOfOrder",
      f"{SP} Receiving: refused as out of order (OutOfOrder), or as counter exhaustion (ChainExhausted) once the counter is u64::MAX")
def _():
    _, b = _pair()
    b.chains[0][1].n = K.U64_MAX
    rejects(spqr.receive, b, 0, 5, exc=spqr.ChainExhausted)
    b.chains[0][1].n = 10
    rejects(spqr.receive, b, 0, 5, exc=spqr.OutOfOrder)


@case("CR-14 sparse NoChain: a send naming an epoch without chains, a receive for an epoch never reached",
      f"{SP} Sending: A send naming an epoch the state holds no chains for is refused (NoChain); Receiving: likewise")
def _():
    a, b = _pair()
    rejects(spqr.send, a, 1, exc=spqr.NoChain)
    rejects(spqr.receive, b, 3, 1, exc=spqr.NoChain)


@case("CR-15 sparse store bound (SkippedStoreFull) and eviction: the key stored first goes first, whatever its epoch",
      f"{SP} The store also has a total bound: it evicts keys from this store, the one stored first going first whatever its epoch")
def _():
    _, b = _pair()
    b = spqr.receive(b, 0, 1001)[0]               # (0, 1..1000)
    b = spqr.receive(b, 0, 2002)[0]               # (0, 1002..2001): 2000
    assert len(b.skipped) == K.MAX_SKIPPED_STORE
    e = rejects(spqr.receive, b, 0, 2004, exc=spqr.SkippedStoreFull)
    assert e.shortfall == 1
    b.skipped = {(1, 7): b"\x01" * 32, **b.skipped}   # an epoch-1 key stored first
    ev = spqr.evict(b, 2)
    assert (1, 7) not in ev.skipped and (0, 1) not in ev.skipped and (0, 2) in ev.skipped


@case("CR-16 an absent chain is refused when an operation needs it (ChainRetired)",
      f"{SPS} Sparse ratchet state: An operation that needs an absent chain is refused (ChainRetired)")
def _():
    a, b = _pair()
    a.chains[0][0] = None
    b.chains[0][1] = None
    rejects(spqr.send, a, 0, exc=spqr.ChainRetired)
    rejects(spqr.receive, b, 0, 1, exc=spqr.ChainRetired)


@case("CR-17 sparse chains order: an advance opens an entry last; a send or a stepping receive moves its entry last",
      f"{SPS} Sparse ratchet state: written in the order their epochs' chains were last replaced, most recent last")
def _():
    a, b = _pair()
    a = spqr.send(a, 0, b"\x31" * 32, 1)[0]       # advance opens 1 last, then the send on 0 moves 0 last
    assert list(a.chains) == [1, 0]
    a = spqr.send(a, 1)[0]
    assert list(a.chains) == [0, 1]
    b = spqr.receive(b, 0, 3, b"\x31" * 32, 1)[0]
    assert list(b.chains) == [1, 0]
    b = spqr.receive(b, 0, 1)[0]                   # a stored-key receive steps no chain: order unchanged
    assert list(b.chains) == [1, 0]


@case("CR-18 sparse replacement (G2-01, closed): stepping forward deletes a key stored for the epoch under a number it is about to store, then stores the range in number order after every key already held; the replacing key is last, eviction takes the others first, and the bound counts the resulting size",
      f"{SP} Receiving: Stepping forward deletes any key stored for the epoch under a number it is about to store, then stores the keys it passes, in number order, after every key already in the store; {SPS} Semantic rules of the leaf formats (ADR-0007)")
def _():
    from tacenta_reader import persistence
    _, b = _pair()
    old3, keep9 = b"\x33" * 32, b"\x99" * 32
    b.skipped[(0, 3)] = old3
    b.skipped[(0, 9)] = keep9
    b = persistence.spqr_from_bytes(persistence.spqr_to_bytes(b))     # only a stored state holds such keys
    b2, _ = accepts(spqr.receive, b, 0, 5)
    assert list(b2.skipped) == [(0, 9), (0, 1), (0, 2), (0, 3), (0, 4)]
    assert b2.skipped[(0, 3)] != old3 and b2.skipped[(0, 9)] == keep9
    assert list(spqr.evict(b2, 1).skipped) == [(0, 1), (0, 2), (0, 3), (0, 4)]
    _, c = _pair()
    c.skipped[(0, 3)] = old3
    c.skipped[(0, 4)] = old3
    for i in range(K.MAX_SKIPPED_STORE - 5):
        c.skipped[(0, 10000 + i)] = keep9
    c2, _ = accepts(spqr.receive, c, 0, 6)                            # 5 numbers, 2 replaced: 1997 + 3
    assert len(c2.skipped) == K.MAX_SKIPPED_STORE
    c.skipped[(0, 20000)] = keep9
    e = rejects(spqr.receive, c, 0, 6, exc=spqr.SkippedStoreFull)
    assert e.shortfall == 1
