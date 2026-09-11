"""The ML-KEM Braid, from protocol/mlkem-braid.md.

The page now states the protocol (GAPS-3.md: G-21's Braid part, G-22 and G-23
closed). This module follows its sections:

- Parameters and derivations: `ToBytes`, `KDF_OK`, `KDF_AUTH`, the ratcheted
  authenticator (`Init`, `Update`, `MacHdr`, `MacCt`).
- The KEM split: `validate_ek_vector` (hash in the page's input order, plus the
  FIPS 203 modulus check). The KEM itself is injected (kem_double.py is a test
  double, not ML-KEM).
- Messages: `Message`, and the composite header's last four fields.
- The state machine: States (`HOLDS`), Initialisation, Sending (transitions (1)
  and (7)), Receiving ((2)-(6), (8)-(13)), completing the encapsulation, What a
  send and a receive return, What a receive ignores, Failure.
- What the session does with them: `BraidAgreement`, the Braid behind
  triple.py's agreement boundary.

Every operation is pure: it returns a new state and leaves its argument as it
was.
"""

import copy
import hashlib
import hmac as _hmac
from dataclasses import dataclass
from typing import Any, Optional, Tuple

from . import constants as K
from . import erasure, persistence, wire
from .kdf import hkdf_sha256, hmac_sha256
from .kem_double import KemFailure

# ------------------------------------------------------ Parameters and sizes

HEADER_LEN = K.BRAID_HEADER_LEN          # 64
EK_VECTOR_LEN = K.BRAID_EK_VECTOR_LEN    # 1,536
CT1_LEN = K.BRAID_CT1_LEN                # 1,408
CT2_LEN = K.BRAID_CT2_LEN                # 160
MAC_SIZE = K.BRAID_MAC_LEN               # 32
HDR_VALUE_LEN = HEADER_LEN + MAC_SIZE    # 96: header || MacHdr
CT2_VALUE_LEN = CT2_LEN + MAC_SIZE       # 192: ct2 || MacCt

# States, with state_tag (mlkem-braid.md, States; CONSTANTS.md Braid state_tag)
(KEYS_UNSAMPLED, KEYS_SAMPLED, HEADER_SENT, CT1_RECEIVED, EK_SENT_CT1_RECEIVED,
 NO_HEADER_RECEIVED, HEADER_RECEIVED, CT1_SAMPLED, EK_RECEIVED_CT1_SAMPLED,
 CT1_ACKNOWLEDGED, CT2_SAMPLED, FAILED) = range(12)

STATE_NAMES = ("KeysUnsampled", "KeysSampled", "HeaderSent", "Ct1Received", "EkSentCt1Received",
               "NoHeaderReceived", "HeaderReceived", "Ct1Sampled", "EkReceivedCt1Sampled",
               "Ct1Acknowledged", "Ct2Sampled", "Failed")

# "holds, besides epoch and authenticator", in the order the States table lists
# them. Field names are session-persistence.md's.
HOLDS = {
    KEYS_UNSAMPLED: (),
    KEYS_SAMPLED: ("key_pair", "hdr_enc"),
    HEADER_SENT: ("key_pair", "ct1_dec", "ek_enc"),
    CT1_RECEIVED: ("key_pair", "ct1", "ek_enc"),
    EK_SENT_CT1_RECEIVED: ("key_pair", "ct1", "ct2_dec"),
    NO_HEADER_RECEIVED: ("hdr_dec",),
    HEADER_RECEIVED: ("header", "ek_dec"),
    CT1_SAMPLED: ("header", "encaps", "ct1", "ct1_enc", "ek_dec"),
    EK_RECEIVED_CT1_SAMPLED: ("encaps", "ct1", "ek_vector", "ct1_enc"),
    CT1_ACKNOWLEDGED: ("header", "encaps", "ct1", "ek_dec"),
    CT2_SAMPLED: ("ct2_enc",),
    FAILED: None,
}


def to_bytes(epoch: int) -> bytes:
    """ToBytes(e): the epoch as eight bytes, big-endian."""
    if not 0 <= epoch <= K.U64_MAX:
        raise ValueError("an epoch is an unsigned 64-bit integer")
    return epoch.to_bytes(8, "big")


def kdf_ok(k: bytes, epoch: int) -> bytes:
    """KDF_OK(K, e) = HKDF-SHA256(32 zero bytes, K, PROTOCOL_INFO || ":SCKA Key" || ToBytes(e), 32)."""
    return hkdf_sha256(bytes(32), k, K.BRAID_PROTOCOL_INFO + K.BRAID_SCKA_KEY + to_bytes(epoch), 32)


kdf_epoch_key = kdf_ok   # the name the second pass used


def kdf_auth(root_key: bytes, u: bytes, epoch: int) -> bytes:
    """KDF_AUTH(rk, u, e) = HKDF-SHA256(rk, u, PROTOCOL_INFO || ":Authenticator Update" || ToBytes(e), 64)."""
    return hkdf_sha256(root_key, u, K.BRAID_PROTOCOL_INFO + K.BRAID_AUTH_UPDATE + to_bytes(epoch), 64)


@dataclass(frozen=True)
class Auth:
    """The ratcheted authenticator: a root_key and a mac_key, 32 bytes each."""
    root_key: bytes
    mac_key: bytes

    @classmethod
    def init(cls, epoch: int, s: bytes) -> "Auth":
        """Init(e, s): root_key = 32 zero bytes, then Update(e, s). "Init reads no mac_key"."""
        return cls(bytes(32), b"").update(epoch, s)

    def update(self, epoch: int, u: bytes) -> "Auth":
        out = kdf_auth(self.root_key, u, epoch)
        return Auth(out[:32], out[32:])

    def _mac(self, suffix: bytes, epoch: int, data: bytes) -> bytes:
        if len(self.mac_key) != 32:
            raise ValueError("no mac_key: the authenticator was not updated")
        return hmac_sha256(self.mac_key, K.BRAID_PROTOCOL_INFO + suffix + to_bytes(epoch) + data)

    def mac_hdr(self, epoch: int, hdr: bytes) -> bytes:
        return self._mac(K.BRAID_EKHEADER, epoch, hdr)

    def mac_ct(self, epoch: int, ct: bytes) -> bytes:
        return self._mac(K.BRAID_CIPHERTEXT, epoch, ct)


def auth_update(root_key: bytes, key: bytes, epoch: int) -> Tuple[bytes, bytes]:
    """One Update from a given root_key -> (root_key, mac_key); auth.json's shape."""
    a = Auth(bytes(root_key), b"").update(epoch, key)
    return a.root_key, a.mac_key


def mac_matches(expected: bytes, got: bytes) -> bool:
    """"compares all 32 bytes ... Nothing is truncated"; constant time."""
    return len(got) == MAC_SIZE and _hmac.compare_digest(expected, got)


# ------------------------------------------------------------- The KEM split

def validate_ek_vector(header: bytes, ek_vector: bytes) -> bool:
    """Accepted only if H(ek_vector || rho) equals the hash in the header and
    ek_vector passes ByteEncode12(ByteDecode12(ek_vector)) = ek_vector."""
    rho, digest = header[:32], header[32:64]
    return (len(ek_vector) == EK_VECTOR_LEN
            and hashlib.sha3_256(bytes(ek_vector) + rho).digest() == digest
            and persistence._modulus_ok(ek_vector))


# ------------------------------------------------------------------ Messages

@dataclass(frozen=True)
class Message:
    epoch: int
    type: int
    codeword: Optional[Tuple[int, bytes]] = None


def message_from_header(h: wire.CompositeHeader) -> Message:
    """"A receive hands the Braid the message those four fields describe"."""
    cw = None if h.codeword is None else (h.codeword.index, h.codeword.data)
    return Message(h.ag_epoch, h.ag_type, cw)


def header_fields(m: Message) -> dict:
    """The composite header's ag_epoch, ag_type and codeword for a Braid message."""
    cw = None if m.codeword is None else wire.Codeword(m.codeword[0], bytes(m.codeword[1]))
    return dict(ag_epoch=m.epoch, ag_type=m.type, codeword=cw)


# --------------------------------------------------------- The state machine

@dataclass
class State:
    tag: int
    epoch: int = 0
    auth: Optional[Auth] = None
    key_pair: Optional[bytes] = None
    header: Optional[bytes] = None
    ek_vector: Optional[bytes] = None
    ct1: Optional[bytes] = None
    encaps: Optional[bytes] = None
    hdr_enc: Optional[erasure.Encoder] = None
    ek_enc: Optional[erasure.Encoder] = None
    ct1_enc: Optional[erasure.Encoder] = None
    ct2_enc: Optional[erasure.Encoder] = None
    hdr_dec: Optional[erasure.Decoder] = None
    ek_dec: Optional[erasure.Decoder] = None
    ct1_dec: Optional[erasure.Decoder] = None
    ct2_dec: Optional[erasure.Decoder] = None

    @property
    def name(self) -> str:
        return STATE_NAMES[self.tag]


def _make(tag: int, epoch: int, auth: Auth, **fields) -> State:
    if set(fields) != set(HOLDS[tag]):
        raise AssertionError(f"{STATE_NAMES[tag]} holds {HOLDS[tag]}, given {tuple(fields)}")
    return State(tag, epoch, auth, **fields)


def _failed() -> State:
    """Failed holds "nothing, not even an epoch"."""
    return State(FAILED)


def init_initiator(sk: bytes) -> State:
    """The session's initiator starts in KeysUnsampled at epoch 1, with Init(1, SK)."""
    return _make(KEYS_UNSAMPLED, 1, Auth.init(1, sk))


def init_responder(sk: bytes) -> State:
    """The responder starts in NoHeaderReceived at epoch 1, with an empty header decoder."""
    return _make(NO_HEADER_RECEIVED, 1, Auth.init(1, sk), hdr_dec=erasure.Decoder(HDR_VALUE_LEN))


@dataclass(frozen=True)
class SendResult:
    state: State
    message: Optional[Message]          # None only from Failed ("puts nothing on the wire")
    epoch: int                          # the sending epoch
    output: Optional[Tuple[int, bytes]]


@dataclass(frozen=True)
class ReceiveResult:
    state: State
    epoch: int                          # the receiving epoch
    output: Optional[Tuple[int, bytes]]


# state -> (encoder field, type) for every send that is not (1) or (7)
_SENDS_FROM = {
    KEYS_SAMPLED: ("hdr_enc", K.AG_HDR),
    HEADER_SENT: ("ek_enc", K.AG_EK),
    CT1_RECEIVED: ("ek_enc", K.AG_EK_CT1_ACK),
    CT1_SAMPLED: ("ct1_enc", K.AG_CT1),
    EK_RECEIVED_CT1_SAMPLED: ("ct1_enc", K.AG_CT1),
    CT2_SAMPLED: ("ct2_enc", K.AG_CT2),
}


def send(state: State, kem) -> SendResult:
    if state.tag == FAILED:
        return SendResult(state, None, 0, None)
    s = copy.deepcopy(state)
    e = s.epoch
    if s.tag == KEYS_UNSAMPLED:                                     # (1)
        try:
            key_pair, header, _ek_vector = kem.generate()
        except KemFailure:
            return SendResult(_failed(), None, 0, None)
        enc = erasure.Encoder.for_value(header + s.auth.mac_hdr(e, header))
        cw = enc.issue()
        return SendResult(_make(KEYS_SAMPLED, e, s.auth, key_pair=key_pair, hdr_enc=enc),
                          Message(e, K.AG_HDR, cw), e - 1, None)
    if s.tag == HEADER_RECEIVED:                                    # (7)
        try:
            encaps, ct1, k = kem.encaps1(s.header)
        except KemFailure:
            return SendResult(_failed(), None, 0, None)
        key = kdf_ok(k, e)
        auth = s.auth.update(e, key)
        enc = erasure.Encoder.for_value(ct1)
        cw = enc.issue()
        new = _make(CT1_SAMPLED, e, auth, header=s.header, encaps=encaps, ct1=ct1, ct1_enc=enc, ek_dec=s.ek_dec)
        return SendResult(new, Message(e, K.AG_CT1, cw), e - 1, (e, key))
    if s.tag in _SENDS_FROM:
        name, typ = _SENDS_FROM[s.tag]
        cw = getattr(s, name).issue()
        if cw is None:                          # Encoder lifetime: None, no codeword, no change
            return SendResult(s, Message(e, K.AG_NONE, None), e - 1, None)
        return SendResult(s, Message(e, typ, cw), e - 1, None)
    return SendResult(s, Message(e, K.AG_NONE, None), e - 1, None)


def _complete_encapsulation(s: State, ek_vector: bytes, kem) -> State:
    """(9), (11), (12): second half, an encoder over ct2 || MacCt, Ct2Sampled;
    the authenticator is not updated."""
    try:
        ct2 = kem.encaps2(s.encaps, ek_vector)
    except KemFailure:
        return _failed()
    enc = erasure.Encoder.for_value(ct2 + s.auth.mac_ct(s.epoch, s.ct1 + ct2))
    return _make(CT2_SAMPLED, s.epoch, s.auth, ct2_enc=enc)


def receive(state: State, msg: Message, kem) -> ReceiveResult:
    if state.tag == FAILED:
        return ReceiveResult(state, 0, None)
    s = copy.deepcopy(state)
    e, t, cw, typ = s.epoch, s.tag, msg.codeword, msg.type
    at = msg.epoch == e
    out = None

    if t == CT2_SAMPLED:
        if e == K.U64_MAX - 1:                  # checks the ceiling before it looks at the message
            s = _failed()
        elif msg.epoch == e + 1:                                    # (13)
            s = _make(KEYS_UNSAMPLED, e + 1, s.auth)
    elif t == KEYS_SAMPLED:
        if at and typ == K.AG_CT1 and cw is not None:               # (2)
            dec = erasure.Decoder(CT1_LEN)
            dec.receive(*cw)
            s = _make(HEADER_SENT, e, s.auth, key_pair=s.key_pair, ct1_dec=dec,
                      ek_enc=erasure.Encoder.for_value(kem.ek_vector(s.key_pair)))
    elif t == HEADER_SENT:
        if at and typ == K.AG_CT1 and cw is not None:
            s.ct1_dec.receive(*cw)
            if s.ct1_dec.complete():                                # (3)
                s = _make(CT1_RECEIVED, e, s.auth, key_pair=s.key_pair, ct1=s.ct1_dec.value(), ek_enc=s.ek_enc)
    elif t == CT1_RECEIVED:
        if at and typ == K.AG_CT2 and cw is not None:               # (4)
            dec = erasure.Decoder(CT2_VALUE_LEN)
            dec.receive(*cw)
            s = _make(EK_SENT_CT1_RECEIVED, e, s.auth, key_pair=s.key_pair, ct1=s.ct1, ct2_dec=dec)
    elif t == EK_SENT_CT1_RECEIVED:
        if at and typ == K.AG_CT2 and cw is not None:
            s.ct2_dec.receive(*cw)
            if s.ct2_dec.complete():
                value = s.ct2_dec.value()
                # "the length check comes first, then the ceiling, and both come before decapsulation"
                if len(value) != CT2_VALUE_LEN or e == K.U64_MAX - 1:
                    s = _failed()
                else:                                               # (5)
                    ct2, mac = value[:CT2_LEN], value[CT2_LEN:]
                    try:
                        k = kem.decaps(s.key_pair, s.ct1, ct2)
                    except KemFailure:
                        k = None
                    if k is None:
                        s = _failed()
                    else:
                        key = kdf_ok(k, e)
                        auth = s.auth.update(e, key)
                        if not mac_matches(auth.mac_ct(e, s.ct1 + ct2), mac):
                            s = _failed()
                        else:
                            out = (e, key)
                            s = _make(NO_HEADER_RECEIVED, e + 1, auth, hdr_dec=erasure.Decoder(HDR_VALUE_LEN))
    elif t == NO_HEADER_RECEIVED:
        if at and typ == K.AG_HDR and cw is not None:
            s.hdr_dec.receive(*cw)
            if s.hdr_dec.complete():
                value = s.hdr_dec.value()
                if len(value) != HDR_VALUE_LEN:
                    s = _failed()
                else:
                    header, mac = value[:HEADER_LEN], value[HEADER_LEN:]
                    if not mac_matches(s.auth.mac_hdr(e, header), mac):
                        s = _failed()
                    else:                                           # (6)
                        s = _make(HEADER_RECEIVED, e, s.auth, header=header,
                                  ek_dec=erasure.Decoder(EK_VECTOR_LEN))
    elif t == CT1_SAMPLED:
        if at and typ in (K.AG_EK, K.AG_EK_CT1_ACK) and cw is not None:
            s.ek_dec.receive(*cw)
            if s.ek_dec.complete():
                ek_vector = s.ek_dec.value()
                if not validate_ek_vector(s.header, ek_vector):
                    s = _failed()
                elif typ == K.AG_EK_CT1_ACK:                        # (9)
                    s = _complete_encapsulation(s, ek_vector, kem)
                else:                                               # (10)
                    s = _make(EK_RECEIVED_CT1_SAMPLED, e, s.auth, encaps=s.encaps, ct1=s.ct1,
                              ek_vector=ek_vector, ct1_enc=s.ct1_enc)
            elif typ == K.AG_EK_CT1_ACK:                            # (8)
                s = _make(CT1_ACKNOWLEDGED, e, s.auth, header=s.header, encaps=s.encaps, ct1=s.ct1,
                          ek_dec=s.ek_dec)
    elif t == CT1_ACKNOWLEDGED:
        if at and typ == K.AG_EK_CT1_ACK and cw is not None:
            s.ek_dec.receive(*cw)
            if s.ek_dec.complete():
                ek_vector = s.ek_dec.value()
                # "it validates it, going to Failed on failure. Otherwise it
                # takes (11)" -- read as: otherwise than failing (G3-06)
                if not validate_ek_vector(s.header, ek_vector):
                    s = _failed()
                else:                                               # (11)
                    s = _complete_encapsulation(s, ek_vector, kem)
    elif t == EK_RECEIVED_CT1_SAMPLED:
        if at and typ == K.AG_EK_CT1_ACK:                           # (12): reads only the type
            s = _complete_encapsulation(s, s.ek_vector, kem)
    # KeysUnsampled and HeaderReceived ignore every message.

    if s.tag == FAILED:
        return ReceiveResult(s, 0, None)
    return ReceiveResult(s, s.epoch - 1, out)


# ------------------------------------------------------------- persistence

def to_persisted(s: State) -> "persistence.BraidState":
    if s.tag == FAILED:
        return persistence.BraidState(FAILED)
    fields = {name: copy.deepcopy(getattr(s, name)) for name in HOLDS[s.tag]}
    return persistence.BraidState(s.tag, s.epoch, s.auth.root_key, s.auth.mac_key, fields)


def from_persisted(b: "persistence.BraidState") -> State:
    if b.tag == FAILED:
        return _failed()
    return _make(b.tag, b.epoch, Auth(bytes(b.auth_root), bytes(b.auth_mac)),
                 **{name: copy.deepcopy(b.fields[name]) for name in HOLDS[b.tag]})


def export(s: State) -> bytes:
    return persistence.braid_to_bytes(to_persisted(s))


def import_(buf: bytes) -> State:
    return from_persisted(persistence.braid_from_bytes(buf))


# ----------------------------------------- What the session does with them

class AgreementFailed(Exception):
    """`Session` refuses encrypt and decrypt with AgreementFailed once the Braid
    has failed. `state` is the Braid state the session keeps: "when a send is
    what fails, it keeps the failed state and refuses that send too"."""

    def __init__(self, state: State):
        super().__init__("the agreement has failed")
        self.state = state


class BraidAgreement:
    """The Braid behind triple.py's agreement boundary: a send's sending epoch
    names the sparse ratchet's sending chain and its output is the agreement's
    secret; a receive's output goes to the sparse ratchet and its receiving
    epoch is not used."""

    def __init__(self, kem):
        self.kem = kem

    def send(self, state: State):
        from .triple import AgreementSend
        if state.tag == FAILED:
            raise AgreementFailed(state)
        r = send(state, self.kem)
        if r.state.tag == FAILED:
            raise AgreementFailed(r.state)
        f = header_fields(r.message)
        secret, secret_epoch = (r.output[1], r.output[0]) if r.output else (None, None)
        return AgreementSend(r.state, f["ag_epoch"], f["ag_type"], f["codeword"], r.epoch, secret, secret_epoch)

    def receive(self, state: State, header: wire.CompositeHeader):
        from .triple import AgreementReceive
        if state.tag == FAILED:
            raise AgreementFailed(state)
        r = receive(state, message_from_header(header), self.kem)
        secret, secret_epoch = (r.output[1], r.output[0]) if r.output else (None, None)
        return AgreementReceive(r.state, secret, secret_epoch)
