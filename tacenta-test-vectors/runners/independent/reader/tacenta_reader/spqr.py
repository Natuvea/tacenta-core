"""The Sparse Post-Quantum Ratchet, from protocol/sparse-pq-ratchet.md.

The agreement (ML-KEM Braid) is a boundary: callers pass the epoch it names
and, optionally, a secret with the epoch it belongs to. Derivations, counter
use, chain choice, ceilings, refusals and retention are now all stated on the
page (formerly hypotheses, GAPS.md G-17 and G-18). Only the chain step is
pinned by a vector (spqr.json).

Operations are pure functions returning a new state (see ratchet.py).
"""

import copy
from dataclasses import dataclass, field
from typing import Dict, List, Optional, Tuple

from . import constants as K
from .kdf import hkdf_sha256

A2B = K.DIRECTION_A2B
B2A = K.DIRECTION_B2A


class SpqrError(Exception):
    pass


class NoChain(SpqrError):
    pass


class ChainRetired(SpqrError):
    """session-persistence.md: an operation that needs an absent chain."""


class OutOfOrder(SpqrError):
    pass


class ChainExhausted(SpqrError):
    pass


class TooManySkipped(SpqrError):
    pass


class EpochGap(SpqrError):
    """"The specification requires the new epoch to be exactly one past the
    current one, so a gap is an error." (No name given.)"""


class SkippedStoreFull(SpqrError):
    def __init__(self, shortfall: int):
        super().__init__(f"request would exceed MAX_SKIPPED_STORE by {shortfall}")
        self.shortfall = shortfall


def _info(suffix: bytes) -> bytes:
    # "PROTOCOL_INFO immediately followed by its own suffix, with no separator"
    return K.SPQR_PROTOCOL_INFO + K.SPQR_SEPARATOR + suffix


def kdf_init(sk: bytes) -> Tuple[bytes, bytes, bytes]:
    """All-zero salt, shared secret as input, 96 bytes: root key, first chain key, second."""
    out = hkdf_sha256(bytes(32), sk, _info(K.SPQR_CHAIN_START), 96)
    return out[:32], out[32:64], out[64:]


def kdf_root(rk: bytes, secret: bytes) -> Tuple[bytes, bytes, bytes]:
    """Root key as salt, agreement secret as input, 96 bytes in the same order."""
    out = hkdf_sha256(rk, secret, _info(K.SPQR_ROOT), 96)
    return out[:32], out[32:64], out[64:]


def kdf_chain(ck: bytes, n: int) -> Tuple[bytes, bytes]:
    """Chain key as salt, n as 8 big-endian bytes, 64 bytes: next chain key, message key."""
    if n < 0 or n > K.U64_MAX:
        raise SpqrError("message number out of range")
    out = hkdf_sha256(ck, n.to_bytes(8, "big"), _info(K.SPQR_CHAIN), 64)
    return out[:32], out[32:]


@dataclass
class Chain:
    ck: bytes
    n: int = 0   # the counter: the number of the last message stepped (chains number from one)


@dataclass
class State:
    rk: bytes
    epoch: int
    direction: int
    # epoch -> [send chain or None, receive chain or None], in the order the
    # entries were last replaced, most recent last (session-persistence.md)
    chains: Dict[int, List[Optional[Chain]]] = field(default_factory=dict)
    # (epoch, n) -> key, in the order stored, oldest first
    skipped: Dict[Tuple[int, int], bytes] = field(default_factory=dict)

    def clone(self) -> "State":
        return copy.deepcopy(self)


def _assign(direction: int, ck1: bytes, ck2: bytes) -> List[Optional[Chain]]:
    # "A party in direction A2b sends on the first chain key and receives on
    # the second; a party in B2a does the reverse."
    if direction == A2B:
        return [Chain(ck1), Chain(ck2)]
    if direction == B2A:
        return [Chain(ck2), Chain(ck1)]
    raise SpqrError("unknown direction")


def init(sk: bytes, direction: int) -> State:
    rk, ck1, ck2 = kdf_init(sk)
    s = State(rk=rk, epoch=0, direction=direction)
    s.chains[0] = _assign(direction, ck1, ck2)
    return s


def _touch(s: State, epoch: int) -> None:
    entry = s.chains.pop(epoch)
    s.chains[epoch] = entry


def _advance(s: State, secret: bytes, secret_epoch: int) -> None:
    if secret_epoch != s.epoch + 1:
        raise EpochGap("new epoch is not exactly one past the current one")
    if secret_epoch == K.U64_MAX:
        raise ChainExhausted("refusing to advance to epoch u64::MAX")
    s.rk, ck1, ck2 = kdf_root(s.rk, secret)
    s.chains.pop(secret_epoch, None)
    s.chains[secret_epoch] = _assign(s.direction, ck1, ck2)
    s.epoch = secret_epoch
    # Retiring old epochs: keep every e with E < e + EPOCHS_KEPT, discard the
    # rest "including the skipped keys stored under them".
    for e in [e for e in s.chains if not (s.epoch < e + K.EPOCHS_KEPT)]:
        del s.chains[e]
    for k in [k for k in s.skipped if k[0] not in s.chains]:
        del s.skipped[k]


def send(state: State, agreement_epoch: int, secret: Optional[bytes] = None,
         secret_epoch: Optional[int] = None) -> Tuple[State, int, int, bytes]:
    """Return (candidate state, epoch, message number, message key)."""
    s = state.clone()
    if secret is not None:
        _advance(s, secret, secret_epoch)
    pair = s.chains.get(agreement_epoch)
    if pair is None:
        raise NoChain("no chains for the epoch the agreement named")
    chain = pair[0]
    if chain is None:
        raise ChainRetired("sending chain absent")
    if chain.n == K.U64_MAX:
        raise ChainExhausted("send after message number u64::MAX")
    chain.n += 1
    chain.ck, mk = kdf_chain(chain.ck, chain.n)
    _touch(s, agreement_epoch)
    return s, agreement_epoch, chain.n, mk


def receive(state: State, msg_epoch: int, n: int, secret: Optional[bytes] = None,
            secret_epoch: Optional[int] = None) -> Tuple[State, bytes]:
    """Return (candidate state, message key)."""
    s = state.clone()
    if secret is not None:
        _advance(s, secret, secret_epoch)
    key = (msg_epoch, n)
    if key in s.skipped:
        return s, s.skipped.pop(key)
    pair = s.chains.get(msg_epoch)
    if pair is None:
        raise NoChain("no chains for that epoch (never reached, or retired)")
    chain = pair[1]
    if chain is None:
        raise ChainRetired("receiving chain absent")
    if n <= chain.n:
        if chain.n == K.U64_MAX:
            raise ChainExhausted("receiving counter is u64::MAX")
        raise OutOfOrder("number not past the chain's counter and not stored")
    to_skip = n - 1 - chain.n
    if to_skip > K.MAX_SKIP:
        raise TooManySkipped(f"header demands {to_skip} skips")
    over = len(s.skipped) + to_skip - K.MAX_SKIPPED_STORE
    if over > 0:
        raise SkippedStoreFull(over)
    while chain.n + 1 < n:
        chain.n += 1
        chain.ck, skipped_mk = kdf_chain(chain.ck, chain.n)
        s.skipped[(msg_epoch, chain.n)] = skipped_mk
    chain.n += 1
    chain.ck, mk = kdf_chain(chain.ck, chain.n)
    _touch(s, msg_epoch)
    return s, mk


def evict(state: State, count: int) -> State:
    """"the one stored first going first whatever its epoch"."""
    s = state.clone()
    for k in list(s.skipped)[:max(0, count)]:
        del s.skipped[k]
    return s
