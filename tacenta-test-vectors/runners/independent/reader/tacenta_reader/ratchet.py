"""The classical Double Ratchet, from tacenta-spec/protocol/ratchet.md.

Diffie-Hellman is a boundary: the vectors supply DH outputs and fresh public
keys as bytes (ratchet-vector.schema.json), so the state holds public keys
only and the receive path asks an injected `dh_step(header_dh)` callable for
(dh_recv, new_pub, dh_send) when it takes a DH ratchet step.

Initialisation (init_sender / init_receiver) is NOT described on ratchet.md;
it is taken from the published Double Ratchet specification the page names
as its source, as a hypothesis confirmed by double-ratchet.json (GAPS.md G-11).
"""

import copy
from dataclasses import dataclass, field
from typing import Callable, Dict, Optional, Tuple

from . import constants as K
from .kdf import hkdf_sha256, hmac_sha256


class RatchetError(Exception):
    """A receive or send the ratchet refuses."""


@dataclass(frozen=True)
class Header:
    dh: bytes
    pn: int
    n: int


# ------------------------------------------------------------- derivations

def kdf_rk(rk: bytes, dh_out: bytes) -> Tuple[bytes, bytes]:
    """HKDF-SHA256(salt=rk, ikm=dh_out, info=RK_INFO) -> 64 bytes: RK, CK."""
    out = hkdf_sha256(rk, dh_out, K.RK_INFO, 64)
    return out[:32], out[32:]


def kdf_ck(ck: bytes) -> Tuple[bytes, bytes]:
    """Return (next chain key, message key): HMAC(ck, 0x02), HMAC(ck, 0x01)."""
    return hmac_sha256(ck, b"\x02"), hmac_sha256(ck, b"\x01")


def expand_message_key(mk: bytes) -> Tuple[bytes, bytes, bytes]:
    """Message-key expansion: HKDF(zero salt, mk, MK_INFO) -> enc, mac, iv.

    ratchet.md gives the three outputs (AES-256 key, HMAC-SHA256 key, 16-byte
    IV) but not the total length or the HMAC key width; 80 bytes split
    32/32/16 comes from ratchet-vector.schema.json (GAPS.md G-13).
    """
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
    # (ratchet public key, n) -> (message key, stored_at)
    skipped: Dict[Tuple[bytes, int], Tuple[bytes, int]] = field(default_factory=dict)

    def clone(self) -> "State":
        return copy.deepcopy(self)


def init_sender(sk: bytes, own_pub: bytes, peer_pub: bytes, dh_out: bytes) -> State:
    """Alice: DHs = own pair, DHr = Bob's key, (RK, CKs) = KDF_RK(SK, DH)."""
    rk, cks = kdf_rk(sk, dh_out)
    return State(dhs_pub=bytes(own_pub), dhr=bytes(peer_pub), rk=rk, cks=cks, ckr=None)


def init_receiver(sk: bytes, own_pub: bytes) -> State:
    """Bob: DHs = his pair, DHr = none, RK = SK, no chains."""
    return State(dhs_pub=bytes(own_pub), dhr=None, rk=bytes(sk), cks=None, ckr=None)


# ---------------------------------------------------------------- sending

def ratchet_encrypt(state: State) -> Tuple[Header, bytes]:
    """Send: (CKs, mk) = KDF_CK(CKs); header (DHs, PN, Ns); Ns += 1."""
    if state.cks is None:
        # ratchet.md does not say what sending with an empty chain does
        # (GAPS.md G-15); this reader refuses.
        raise RatchetError("no sending chain yet")
    if state.ns >= K.U32_MAX:
        raise RatchetError("sending counter exhausted")
    state.cks, mk = kdf_ck(state.cks)
    header = Header(state.dhs_pub, state.pn, state.ns)
    state.ns += 1
    return header, mk


# -------------------------------------------------------------- receiving

DhStep = Callable[[bytes], Tuple[bytes, bytes, bytes]]


def _skip(s: State, until: int) -> None:
    # MAX_SKIP: "the most keys that may be skipped in a single chain. A header
    # demanding more than this is rejected."
    if until > s.nr and until - s.nr > K.MAX_SKIP:
        raise RatchetError("header demands more than MAX_SKIP skipped keys")
    if s.ckr is None or until <= s.nr:
        return
    fresh = sum(1 for n in range(s.nr, until) if (s.dhr, n) not in s.skipped)
    # MAX_SKIPPED_STORE: "A step that would push the store past this bound is
    # rejected." The store is a map (key-deletion.md), so a replacement does
    # not grow it.
    if len(s.skipped) + fresh > K.MAX_SKIPPED_STORE:
        raise RatchetError("skipping would push the store past MAX_SKIPPED_STORE")
    while s.nr < until:
        s.ckr, mk = kdf_ck(s.ckr)
        s.skipped[(s.dhr, s.nr)] = (mk, s.events)
        s.nr += 1


def _age(s: State) -> None:
    # key-deletion.md: every accepted receive ages the store and drops what
    # has expired; the clock stops at u32::MAX - 1 (session-persistence.md).
    # The exact boundary ("outlived" = strictly more than MAX_SKIPPED_AGE) is
    # a hypothesis no vector exercises (GAPS.md G-16).
    s.events = min(s.events + 1, K.U32_MAX - 1)
    expired = [k for k, (_, at) in s.skipped.items() if s.events - at > K.MAX_SKIPPED_AGE]
    for k in expired:
        del s.skipped[k]


def ratchet_decrypt(state: State, header: Header, dh_step: DhStep) -> bytes:
    """Receive a header and return the message key.

    Transactional: on RatchetError the state is left as it was.
    """
    s = state.clone()
    key = (bytes(header.dh), header.n)
    if key in s.skipped:
        mk, _ = s.skipped.pop(key)
        _age(s)
        _commit(state, s)
        return mk
    if s.dhr is None or bytes(header.dh) != s.dhr:
        # DH ratchet step (ratchet.md, The Diffie-Hellman ratchet).
        _skip(s, header.pn)
        dh_recv, new_pub, dh_send = dh_step(bytes(header.dh))
        s.pn = s.ns
        s.ns = 0
        s.nr = 0
        s.dhr = bytes(header.dh)
        s.rk, s.ckr = kdf_rk(s.rk, dh_recv)
        s.dhs_pub = bytes(new_pub)
        s.rk, s.cks = kdf_rk(s.rk, dh_send)
    elif header.n < s.nr:
        # Not a stored key and behind the chain: no key exists for it
        # (GAPS.md G-15).
        raise RatchetError("message number already consumed on this chain")
    _skip(s, header.n)
    if s.ckr is None:
        raise RatchetError("no receiving chain")
    s.ckr, mk = kdf_ck(s.ckr)
    s.nr += 1
    _age(s)
    _commit(state, s)
    return mk


def _commit(dst: State, src: State) -> None:
    dst.__dict__.update(src.__dict__)
