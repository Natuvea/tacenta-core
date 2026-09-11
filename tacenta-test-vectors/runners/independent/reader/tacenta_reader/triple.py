"""The Triple Ratchet, from protocol/triple-ratchet.md.

- `combine`: section 7.2's parameters as the page states them: the
  post-quantum message key as salt, the classical one as IKM, COMBINE_INFO,
  32 bytes, which then goes through the message-key expansion (G-20, closed).
- `split_secret`: HKDF-SHA256, 32-byte zero salt, SK as IKM, SPLIT_INFO, 64
  bytes; first 32 to the Double Ratchet, last 32 to the sparse ratchet (A2b for
  the initiator, B2a for the responder) (G-19, closed).
- `encrypt` / `decrypt`: the commit rules. Classical half first, sparse half
  second; a send runs on a copy; a receive yields a candidate adopted only once
  the message authenticates; the non-contributory check on the header's
  ratchet key under the current and the freshly generated private key runs
  before either ratchet and before the tag.
- `decrypt_with_eviction`: ratchet.md / sparse-pq-ratchet.md, "A full store
  makes room rather than refusing the message".

The agreement (the ML-KEM Braid) is a boundary here, as it is on
sparse-pq-ratchet.md: the Braid's state machine is defined only by the
published document mlkem-braid.md defers to, which is not in the tree
(GAPS.md G-21..G-23, still open). `NullAgreement` and `ScriptedAgreement`
are test doubles for that boundary, not the Braid.
"""

from dataclasses import dataclass, replace
from typing import Any, Optional, Tuple

from . import aead, ratchet, spqr, wire
from . import constants as K
from .curve25519 import NonContributory, x25519, x25519_public
from .kdf import hkdf_sha256


# ------------------------------------------------------------ derivations

def combine(mk_ec: bytes, mk_pq: bytes) -> bytes:
    if len(mk_ec) != 32 or len(mk_pq) != 32:
        raise ValueError("both message keys are 32 bytes")
    return hkdf_sha256(mk_pq, mk_ec, K.COMBINE_INFO, 32)


def split_secret_bytes(sk: bytes) -> bytes:
    return hkdf_sha256(bytes(32), sk, K.SPLIT_INFO, 64)


def split_secret(sk: bytes) -> Tuple[bytes, bytes]:
    """(classical half, sparse half)."""
    out = split_secret_bytes(sk)
    return out[:32], out[32:]


# ------------------------------------------------------ agreement boundary

@dataclass(frozen=True)
class AgreementSend:
    state: Any
    ag_epoch: int
    ag_type: int
    codeword: Optional[wire.Codeword]
    epoch: int                          # the epoch the receiver is guaranteed to know
    secret: Optional[bytes] = None
    secret_epoch: Optional[int] = None


@dataclass(frozen=True)
class AgreementReceive:
    state: Any
    secret: Optional[bytes] = None
    secret_epoch: Optional[int] = None


class NullAgreement:
    """Test double: never yields a secret, always names epoch 0, carries no codeword."""

    def send(self, state):
        return AgreementSend(state, 0, K.AG_NONE, None, 0)

    def receive(self, state, header):
        return AgreementReceive(state)


class ScriptedAgreement:
    """Test double: state is (epoch, sends). The initiator's `trigger`-th send
    yields `secret` for epoch 1, sent on epoch 0 and marked with ag_epoch 1; a
    receive of a message marked ag_epoch == epoch + 1 yields the same secret."""

    def __init__(self, secret: bytes, trigger: int):
        self.secret = secret
        self.trigger = trigger

    def send(self, state):
        epoch, sends = state
        sends += 1
        if epoch == 0 and sends == self.trigger:
            return AgreementSend((1, sends), 1, K.AG_HDR, None, 0, self.secret, 1)
        return AgreementSend((epoch, sends), epoch, K.AG_NONE, None, epoch)

    def receive(self, state, header):
        epoch, sends = state
        if header.ag_epoch == epoch + 1:
            return AgreementReceive((epoch + 1, sends), self.secret, epoch + 1)
        return AgreementReceive(state)


# ---------------------------------------------------------------- session

@dataclass(frozen=True)
class Party:
    classical: ratchet.State
    sparse: spqr.State
    ratchet_private: bytes
    agreement_state: Any
    ad: bytes                     # AD = EncodeEC(IKA) || EncodeEC(IKB)


def init_initiator(sk: bytes, ad: bytes, fresh_ratchet_private: bytes,
                   peer_signed_prekey: bytes, agreement_state: Any) -> Party:
    c_half, s_half = split_secret(sk)
    dh = x25519(fresh_ratchet_private, peer_signed_prekey)
    if dh == bytes(32):
        # session-establishment.md, Notation: refused wherever one is computed
        raise NonContributory("initial ratchet agreement is not contributory")
    classical = ratchet.init_initiator(c_half, x25519_public(fresh_ratchet_private), peer_signed_prekey, dh)
    return Party(classical, spqr.init(s_half, spqr.A2B), bytes(fresh_ratchet_private), agreement_state, bytes(ad))


def init_responder(sk: bytes, ad: bytes, signed_prekey_private: bytes, agreement_state: Any) -> Party:
    c_half, s_half = split_secret(sk)
    classical = ratchet.init_responder(c_half, x25519_public(signed_prekey_private))
    return Party(classical, spqr.init(s_half, spqr.B2A), bytes(signed_prekey_private), agreement_state, bytes(ad))


def encrypt(party: Party, agreement, plaintext: bytes) -> Tuple[Party, bytes]:
    """A send runs on a copy and adopts it only once both halves have produced keys."""
    classical, dr_hdr, mk_ec = ratchet.send(party.classical)
    ag = agreement.send(party.agreement_state)
    sparse, epoch, pq_n, mk_pq = spqr.send(party.sparse, ag.epoch, ag.secret, ag.secret_epoch)
    header = wire.CompositeHeader(dh=dr_hdr.dh, pn=dr_hdr.pn, n=dr_hdr.n, pq_epoch=epoch, pq_n=pq_n,
                                  ag_epoch=ag.ag_epoch, ag_type=ag.ag_type, codeword=ag.codeword)
    header_bytes = wire.encode_composite(header)
    ct = aead.seal(combine(mk_ec, mk_pq), wire.concat_ad(party.ad, header_bytes), plaintext)
    return replace(party, classical=classical, sparse=sparse, agreement_state=ag.state), header_bytes + ct


def check_contributory(ratchet_private: bytes, fresh_private: bytes, header_dh: bytes) -> Tuple[bytes, bytes]:
    dh_current = x25519(ratchet_private, header_dh)
    dh_fresh = x25519(fresh_private, header_dh)
    if dh_current == bytes(32) or dh_fresh == bytes(32):
        raise NonContributory("header ratchet key gives a non-contributory output")
    return dh_current, dh_fresh


def decrypt(party: Party, agreement, message: bytes, fresh_private: bytes) -> Tuple[Party, bytes]:
    """Receive. Returns (adopted party, plaintext); on any refusal `party` is untouched."""
    header, ciphertext = wire.decode_ratchet_message(message)
    dh_current, dh_fresh = check_contributory(party.ratchet_private, fresh_private, header.dh)
    fresh_pub = x25519_public(fresh_private)
    classical, mk_ec, stepped = ratchet.receive(
        party.classical, ratchet.Header(header.dh, header.pn, header.n),
        lambda _dh: (dh_current, fresh_pub, dh_fresh))
    ag = agreement.receive(party.agreement_state, header)
    sparse, mk_pq = spqr.receive(party.sparse, header.pq_epoch, header.pq_n, ag.secret, ag.secret_epoch)
    header_bytes = bytes(message[:K.COMPOSITE_LEN])
    plaintext = aead.open_(combine(mk_ec, mk_pq), wire.concat_ad(party.ad, header_bytes), ciphertext)
    return Party(classical, sparse, bytes(fresh_private) if stepped else party.ratchet_private,
                 ag.state, party.ad), plaintext


def decrypt_with_eviction(party: Party, agreement, message: bytes, fresh_private: bytes) -> Tuple[Party, bytes]:
    """Retry on a working copy with the oldest keys evicted while the only
    refusal is a full store; refuse once that store is already empty. The batch
    (shortfall first, then doubling) is this reader's choice; the pages make it
    implementation-defined."""
    working = party
    last = {"classical": 0, "sparse": 0}
    while True:
        try:
            return decrypt(working, agreement, message, fresh_private)
        except ratchet.SkippedStoreFull as e:
            if not working.classical.skipped:
                raise
            last["classical"] = max(e.shortfall, 2 * last["classical"])
            working = replace(working, classical=ratchet.evict(working.classical, last["classical"]))
        except spqr.SkippedStoreFull as e:
            if not working.sparse.skipped:
                raise
            last["sparse"] = max(e.shortfall, 2 * last["sparse"])
            working = replace(working, sparse=spqr.evict(working.sparse, last["sparse"]))
