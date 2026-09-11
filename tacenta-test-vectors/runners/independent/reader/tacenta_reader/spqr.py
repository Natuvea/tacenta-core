"""The Sparse Post-Quantum Ratchet, from protocol/sparse-pq-ratchet.md.

The agreement (ML-KEM Braid) is a boundary: callers pass the epoch it names
and, optionally, a secret with its epoch. Only the chain step is pinned by a
vector (spqr.json); initialisation and the root step use the same
PROTOCOL_INFO/suffix joining, which is a hypothesis (GAPS.md G-17).
"""

import copy
from dataclasses import dataclass, field
from typing import Dict, Optional, Tuple

from . import constants as K
from .kdf import hkdf_sha256

A2B = 0x00
B2A = 0x01


class SpqrError(Exception):
    pass


class ChainExhausted(SpqrError):
    pass


def _info(suffix: bytes) -> bytes:
    return K.SPQR_PROTOCOL_INFO + K.SPQR_SEPARATOR + suffix


def kdf_init(sk: bytes) -> Tuple[bytes, bytes, bytes]:
    out = hkdf_sha256(bytes(32), sk, _info(K.SPQR_CHAIN_START), 96)
    return out[:32], out[32:64], out[64:]


def kdf_root(rk: bytes, secret: bytes) -> Tuple[bytes, bytes, bytes]:
    out = hkdf_sha256(rk, secret, _info(K.SPQR_ROOT), 96)
    return out[:32], out[32:64], out[64:]


def kdf_chain(ck: bytes, n: int) -> Tuple[bytes, bytes]:
    """(next chain key, message key) = HKDF(salt=ck, ikm=n as 8 BE bytes)."""
    if n < 0 or n > K.U64_MAX:
        raise SpqrError("message number out of range")
    out = hkdf_sha256(ck, n.to_bytes(8, "big"), _info(K.SPQR_CHAIN), 64)
    return out[:32], out[32:]


@dataclass
class Chain:
    ck: bytes
    n: int = 0  # number of the last message stepped; chains number from one


@dataclass
class State:
    rk: bytes
    epoch: int
    direction: int
    chains: Dict[int, Tuple[Chain, Chain]] = field(default_factory=dict)  # epoch -> (send, recv)
    skipped: Dict[Tuple[int, int], bytes] = field(default_factory=dict)


def _assign(direction: int, ck1: bytes, ck2: bytes) -> Tuple[Chain, Chain]:
    # "A party in direction A2b sends on the first chain key and receives on
    # the second; a party in B2a does the reverse."
    if direction == A2B:
        return Chain(ck1), Chain(ck2)
    if direction == B2A:
        return Chain(ck2), Chain(ck1)
    raise SpqrError("unknown direction")


def init(sk: bytes, direction: int) -> State:
    rk, ck1, ck2 = kdf_init(sk)
    s = State(rk=rk, epoch=0, direction=direction)
    s.chains[0] = _assign(direction, ck1, ck2)
    return s


def _advance(s: State, secret: bytes, secret_epoch: int) -> None:
    if secret_epoch != s.epoch + 1:
        raise SpqrError("new epoch is not exactly one past the current one")
    if secret_epoch == K.U64_MAX:
        raise ChainExhausted("refusing to advance to epoch u64::MAX")
    s.rk, ck1, ck2 = kdf_root(s.rk, secret)
    s.chains[secret_epoch] = _assign(s.direction, ck1, ck2)
    s.epoch = secret_epoch
    # Retire: keep EPOCHS_KEPT epochs (e <= epoch < e + EPOCHS_KEPT), and the
    # skipped keys stored under retired epochs with them.
    for e in [e for e in s.chains if not (e <= s.epoch < e + K.EPOCHS_KEPT)]:
        del s.chains[e]
    for k in [k for k in s.skipped if k[0] not in s.chains]:
        del s.skipped[k]


def send(state: State, agreement_epoch: int, secret: Optional[bytes] = None,
         secret_epoch: Optional[int] = None) -> Tuple[int, int, bytes]:
    """Return (epoch, message number, message key)."""
    s = copy.deepcopy(state)
    if secret is not None:
        _advance(s, secret, secret_epoch)
    pair = s.chains.get(agreement_epoch)
    if pair is None:
        raise SpqrError("no chains for the epoch the agreement named")
    chain = pair[0]
    if chain.n >= K.U64_MAX:
        raise ChainExhausted("sending chain exhausted")
    chain.n += 1
    chain.ck, mk = kdf_chain(chain.ck, chain.n)
    state.__dict__.update(s.__dict__)
    return agreement_epoch, chain.n, mk


def receive(state: State, msg_epoch: int, n: int, secret: Optional[bytes] = None,
            secret_epoch: Optional[int] = None) -> bytes:
    s = copy.deepcopy(state)
    if secret is not None:
        _advance(s, secret, secret_epoch)
    if n == 0:
        raise SpqrError("message number zero is refused as out of order")
    key = (msg_epoch, n)
    if key in s.skipped:
        mk = s.skipped.pop(key)
        state.__dict__.update(s.__dict__)
        return mk
    pair = s.chains.get(msg_epoch)
    if pair is None:
        raise SpqrError("no chains for that epoch (never reached, or retired)")
    chain = pair[1]
    if n <= chain.n:
        raise SpqrError("message number already consumed")
    to_skip = n - 1 - chain.n
    if to_skip > K.MAX_SKIP:
        raise SpqrError("header demands more than MAX_SKIP skips")
    if len(s.skipped) + to_skip > K.MAX_SKIPPED_STORE:
        raise SpqrError("skipping would exceed MAX_SKIPPED_STORE")
    while chain.n + 1 < n:
        chain.n += 1
        chain.ck, skipped_mk = kdf_chain(chain.ck, chain.n)
        s.skipped[(msg_epoch, chain.n)] = skipped_mk
    chain.n += 1
    chain.ck, mk = kdf_chain(chain.ck, chain.n)
    state.__dict__.update(s.__dict__)
    return mk
