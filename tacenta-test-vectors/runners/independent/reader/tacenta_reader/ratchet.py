"""The classical Double Ratchet, from tacenta-spec/protocol/ratchet.md.

Diffie-Hellman is a boundary here, as the vectors require
(ratchet-vector.schema.json): the state holds public keys only (the session
format keeps the private key beside it, session-persistence.md), and a receive
that takes a DH step asks an injected `dh_step(header_dh)` for
(DH(DHs, header key), fresh DHs public, DH(fresh DHs, header key)).

Every operation is a pure function returning a new state. That matches the
commit rules on triple-ratchet.md ("A receive yields a candidate state along
with the key, and changes nothing itself"); ratchet.md itself only promises
that "a refused receive may already have moved the state", which a pure
function trivially satisfies by leaving the caller's state alone.

Refusal names follow the page's parentheses; error-handling.md leaves names to
an implementation.
"""

import copy
from dataclasses import dataclass, field
from typing import Callable, Dict, Optional, Tuple

from . import constants as K
from .kdf import hkdf_sha256, hmac_sha256


class RatchetError(Exception):
    """A send or receive the classical ratchet refuses."""


class NoSendingChain(RatchetError):
    pass


class NoReceivingChain(RatchetError):
    pass


class ChainExhausted(RatchetError):
    pass


class TooManySkipped(RatchetError):
    pass


class SkippedStoreFull(RatchetError):
    def __init__(self, shortfall: int):
        super().__init__(f"skip would push the store past MAX_SKIPPED_STORE by {shortfall}")
        self.shortfall = shortfall


class OutOfOrder(RatchetError):
    """Same chain, number below Nr, key not stored (ratchet.md, Sending and receiving)."""


@dataclass(frozen=True)
class Header:
    dh: bytes
    pn: int
    n: int


# ------------------------------------------------------------- derivations

def kdf_rk(rk: bytes, dh_out: bytes) -> Tuple[bytes, bytes]:
    """HKDF-SHA256(salt=rk, ikm=dh_out, info=RK_INFO) -> 64 bytes: new RK (first 32), chain key (next 32)."""
    out = hkdf_sha256(rk, dh_out, K.RK_INFO, 64)
    return out[:32], out[32:]


def kdf_ck(ck: bytes) -> Tuple[bytes, bytes]:
    """Return (next chain key, message key): HMAC(ck, 0x02), HMAC(ck, 0x01)."""
    return hmac_sha256(ck, b"\x02"), hmac_sha256(ck, b"\x01")


def expand_message_key(mk: bytes) -> Tuple[bytes, bytes, bytes]:
    """ratchet.md, Derivations: HKDF-SHA256, 32-byte zero salt, mk as IKM,
    MK_INFO, 80 bytes: AES-256 key (first 32), HMAC key (next 32), IV (last 16).
    (Formerly from the vector schema only, GAPS.md G-13; now stated.)"""
    out = hkdf_sha256(bytes(32), mk, K.MK_INFO, 80)
    return out[:32], out[32:64], out[64:80]


# ------------------------------------------------------------------ state

@dataclass
class State:
    dhs_pub: bytes
    dhr: Optional[bytes]
    rk: bytes
    cks: Optional[bytes]
    ckr: Optional[bytes]
    ns: int = 0
    nr: int = 0
    pn: int = 0
    events: int = 0
    labels: int = K.LABELS_TACENTA
    # (ratchet public key, n) -> (message key, stored_at), in store order
    skipped: Dict[Tuple[bytes, int], Tuple[bytes, int]] = field(default_factory=dict)

    def clone(self) -> "State":
        return copy.deepcopy(self)


def init_initiator(sk: bytes, dhs_pub: bytes, peer_signed_prekey: bytes, dh_out: bytes) -> State:
    """ratchet.md, Initialisation: fresh DHs, DHr = peer's signed prekey,
    (RK, CKs) = KDF_RK(SK, DH(DHs, DHr)); no receiving chain; counters zero.
    `dh_out` is DH(DHs, DHr), supplied by the caller. (GAPS.md G-11, now stated.)"""
    rk, cks = kdf_rk(sk, dh_out)
    return State(dhs_pub=bytes(dhs_pub), dhr=bytes(peer_signed_prekey), rk=rk, cks=cks, ckr=None)


def init_responder(sk: bytes, signed_prekey_pub: bytes) -> State:
    """ratchet.md, Initialisation: RK = SK, DHs = signed prekey pair, no chains, DHr absent."""
    return State(dhs_pub=bytes(signed_prekey_pub), dhr=None, rk=bytes(sk), cks=None, ckr=None)


# names used by the vector schema ("init_sender / init_receiver")
init_sender = init_initiator
init_receiver = init_responder


# ---------------------------------------------------------------- sending

def send(state: State) -> Tuple[State, Header, bytes]:
    """Send: refused, before anything changes, with no sending chain or Ns = u32::MAX."""
    if state.cks is None:
        raise NoSendingChain("no sending chain")
    if state.ns == K.U32_MAX:
        raise ChainExhausted("Ns is u32::MAX")
    s = state.clone()
    s.cks, mk = kdf_ck(s.cks)
    header = Header(s.dhs_pub, s.pn, s.ns)
    s.ns += 1
    return s, header, mk


# -------------------------------------------------------------- receiving

DhStep = Callable[[bytes], Tuple[bytes, bytes, bytes]]


def _store(s: State, dh: bytes, n: int, key: bytes) -> None:
    # "The numbers skipped keys are stored under are range-checked the same way"
    if n >= K.U32_MAX:
        raise ChainExhausted("skipped key number out of range")
    k = (dh, n)
    if k in s.skipped:
        # key-deletion.md: the store is a map and storing a key for a pair
        # already held replaces it. Whether the replacement keeps the old
        # entry's position and stored_at is not stated (GAPS-2.md G2-01);
        # this reader treats it as a new store: new stored_at, last in order.
        del s.skipped[k]
    s.skipped[k] = (key, s.events)   # stored_at = the count at the start of this receive


def _skip(s: State, until: int) -> None:
    """Store keys from Nr up to `until`, exclusive, on the receiving chain."""
    if until <= s.nr:
        return
    if until - s.nr > K.MAX_SKIP:
        raise TooManySkipped(f"header demands {until - s.nr} skips on one chain")
    fresh = sum(1 for n in range(s.nr, until) if (s.dhr, n) not in s.skipped)
    over = len(s.skipped) + fresh - K.MAX_SKIPPED_STORE
    if over > 0:
        raise SkippedStoreFull(over)
    while s.nr < until:
        s.ckr, mk = kdf_ck(s.ckr)
        _store(s, s.dhr, s.nr, mk)
        s.nr += 1


def _age(s: State) -> None:
    """ratchet.md, Skipped keys: at the end of every accepted receive, after
    the stored-key lookup, increment the count (stopping at u32::MAX - 1) and
    delete every key whose age (new count - stored_at) is at least
    MAX_SKIPPED_AGE. (Boundary was a hypothesis, GAPS.md G-16; now stated.)"""
    s.events = min(s.events + 1, K.MAX_EVENTS)
    for k in [k for k, (_, at) in s.skipped.items() if s.events - at >= K.MAX_SKIPPED_AGE]:
        del s.skipped[k]


def receive(state: State, header: Header, dh_step: DhStep) -> Tuple[State, bytes, bool]:
    """Receive a header. Returns (candidate state, message key, whether a DH step was taken).

    The caller's state is never modified; the candidate is adopted by the
    caller once the message has authenticated (triple-ratchet.md).
    """
    s = state.clone()
    hdh = bytes(header.dh)
    key = (hdh, header.n)
    # "if the header's ratchet key and message number N match a stored
    # skipped key, use and remove it."
    if key in s.skipped:
        mk, _ = s.skipped.pop(key)
        _age(s)
        return s, mk, False
    stepped = False
    if s.dhr is None or hdh != s.dhr:
        # The Diffie-Hellman ratchet, steps 1-3.
        if s.ckr is not None:
            # "If there is a receiving chain, store its skipped message keys
            # from Nr up to the header's PN, exclusive ... checked against
            # MAX_SKIP on its own, before the step."
            _skip(s, header.pn)
        dh_recv, new_pub, dh_send = dh_step(hdh)
        s.rk, s.ckr = kdf_rk(s.rk, dh_recv)
        s.dhr = hdh
        s.nr = 0
        s.pn = s.ns
        s.ns = 0
        s.dhs_pub = bytes(new_pub)
        s.rk, s.cks = kdf_rk(s.rk, dh_send)
        stepped = True
    else:
        if s.ckr is None:
            # "A header whose ratchet key equals DHr while there is no
            # receiving chain is refused (NoReceivingChain)."
            raise NoReceivingChain("header key equals DHr and there is no receiving chain")
        if header.n < s.nr:
            # "A message whose ratchet key equals DHr, whose number N is
            # below Nr, and whose key is not stored is not accepted."
            raise OutOfOrder("number below Nr on the current chain and not stored")
    _skip(s, header.n)
    if s.ckr is None:
        raise NoReceivingChain("no receiving chain")
    if s.nr == K.U32_MAX:
        raise ChainExhausted("Nr is u32::MAX")
    s.ckr, mk = kdf_ck(s.ckr)
    s.nr += 1
    _age(s)
    return s, mk, stepped


def evict(state: State, count: int) -> State:
    """Evict the `count` oldest stored keys (ratchet.md, Skipped keys): "the
    smallest stored count, ties going to the key stored first"."""
    s = state.clone()
    order = sorted(s.skipped.items(), key=lambda kv: kv[1][1])   # stable: ties keep store order
    for k, _ in order[:max(0, count)]:
        del s.skipped[k]
    return s


# ------------------------------------------------- compatibility wrappers

def ratchet_encrypt(state: State) -> Tuple[Header, bytes]:
    """Mutating send, for callers without an AEAD (the vector runner)."""
    s, header, mk = send(state)
    state.__dict__.update(s.__dict__)
    return header, mk


def ratchet_decrypt(state: State, header: Header, dh_step: DhStep) -> bytes:
    """Receive and adopt immediately, for callers without an AEAD (the vector runner)."""
    s, mk, _ = receive(state, header, dh_step)
    state.__dict__.update(s.__dict__)
    return mk
