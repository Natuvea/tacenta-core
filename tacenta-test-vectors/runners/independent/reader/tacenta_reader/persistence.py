"""Storage formats, from protocol/session-persistence.md.

Readers and writers for: the ratchet state, the sparse ratchet state, the
triple ratchet state, the erasure encoder and decoder sub-formats, the Braid's
per-state layout, the session, and the prekey store; with each format's
refusals and semantic rules.

Refusal kinds (session-persistence.md, Rejection; error-handling.md):
WrongVersion, Malformed (short, overrun, trailing, a leaf format's invariant,
the prekey store's semantic rules), NonCanonical (session and prekey store
re-encode check), Inconsistent (session semantic rules).

There are no vectors for any of these formats (GAPS-2.md, vector gaps).

The Braid's `key_pair` (11,872 bytes) and `encaps` (2,592 bytes) are opaque:
"each is its underlying bytes, with no version byte and no structure this page
relies on, and each reader refuses any other length".
"""

import hashlib
from dataclasses import dataclass, field
from typing import Dict, List, Optional, Tuple

from . import constants as K
from . import erasure, ratchet, spqr
from .curve25519 import x25519_public
from .wire import encode_ec


class PersistError(Exception):
    pass


class WrongVersion(PersistError):
    pass


class Malformed(PersistError):
    pass


class NonCanonical(PersistError):
    pass


class Inconsistent(PersistError):
    pass


# ----------------------------------------------------------------- helpers

class _Reader:
    def __init__(self, buf: bytes):
        self.buf = bytes(buf)
        self.pos = 0

    def remaining(self) -> int:
        return len(self.buf) - self.pos

    def take(self, n: int, what: str) -> bytes:
        if n > self.remaining():
            raise Malformed(f"buffer too short for {what}")
        out = self.buf[self.pos:self.pos + n]
        self.pos += n
        return out

    def u(self, width: int, what: str) -> int:
        return int.from_bytes(self.take(width, what), "big")

    def prefixed(self, what: str) -> bytes:
        n = self.u(4, f"length of {what}")
        if n > self.remaining():
            raise Malformed(f"declared length of {what} overruns the input")
        return self.take(n, what)

    def count(self, min_entry: int, what: str) -> int:
        n = self.u(4, f"count of {what}")
        if n * min_entry > self.remaining():
            raise Malformed(f"count of {what} larger than the buffer could hold")
        return n

    def end(self, what: str) -> None:
        if self.remaining():
            raise Malformed(f"bytes left after {what}")


def _be(v: int, width: int) -> bytes:
    return int(v).to_bytes(width, "big")


def _version(buf: bytes, allowed, what: str) -> int:
    if len(buf) < 1:
        raise Malformed(f"{what}: empty buffer")
    if buf[0] not in allowed:
        raise WrongVersion(f"{what}: unrecognised version 0x{buf[0]:02x}")
    return buf[0]


def _presence(r: _Reader, what: str) -> bool:
    p = r.u(1, f"{what} presence")
    if p not in (K.ABSENT, K.PRESENT):
        # Stated for the prekey store; for the other formats this follows from
        # the Canonical principle (GAPS-2.md G2-06).
        raise Malformed(f"{what}: presence byte 0x{p:02x} is neither 0x00 nor 0x01")
    return p == K.PRESENT


def _opt32(r: _Reader, what: str) -> Optional[bytes]:
    present = _presence(r, what)
    data = r.take(32, what)
    if not present:
        if data != bytes(32):
            raise Malformed(f"{what}: absent but not zeroed")
        return None
    return data


def _put_opt32(v: Optional[bytes]) -> bytes:
    return bytes([K.ABSENT]) + bytes(32) if v is None else bytes([K.PRESENT]) + bytes(v)


# ============================================================ ratchet state

_RATCHET_ENTRY = 32 + 4 + 4 + 32


def ratchet_to_bytes(s: ratchet.State) -> bytes:
    out = bytearray([K.STATE_VERSION])
    out += s.dhs_pub + _put_opt32(s.dhr) + s.rk + _put_opt32(s.cks) + _put_opt32(s.ckr)
    out += _be(s.ns, 4) + _be(s.nr, 4) + _be(s.pn, 4) + _be(s.events, 4)
    out += bytes([s.labels])
    out += _be(len(s.skipped), 4)
    for (dh, n), (key, at) in s.skipped.items():
        out += dh + _be(n, 4) + _be(at, 4) + key
    return bytes(out)


def ratchet_invariant(s: ratchet.State, entries: List[Tuple[bytes, int, int]]) -> Optional[str]:
    if len(entries) > K.MAX_SKIPPED_STORE:
        return "skipped store holds more than MAX_SKIPPED_STORE keys"
    if s.events >= K.U32_MAX:
        return "events is not below u32::MAX"
    if any(at > s.events for _, _, at in entries):
        return "a stored key's stored_at is later than events"
    if len({(dh, n) for dh, n, _ in entries}) != len(entries):
        return "two stored keys share a ratchet key and message number"
    if s.ckr is not None and (s.cks is None or s.dhr is None):
        return "receiving chain key without sending chain key and peer ratchet key"
    return None


def ratchet_from_bytes(buf: bytes) -> ratchet.State:
    _version(buf, {K.STATE_VERSION}, "ratchet state")
    r = _Reader(buf)
    r.take(1, "version")
    dhs = r.take(32, "dhs_pub")
    dhr = _opt32(r, "dhr_pub")
    rk = r.take(32, "rk")
    cks = _opt32(r, "cks")
    ckr = _opt32(r, "ckr")
    ns, nr, pn, events = (r.u(4, x) for x in ("ns", "nr", "pn", "events"))
    labels = r.u(1, "labels")
    if labels != K.LABELS_TACENTA:
        raise Malformed(f"ratchet state: unknown LabelSet tag 0x{labels:02x}")
    count = r.count(_RATCHET_ENTRY, "skipped")
    entries = []
    raw = []
    for _ in range(count):
        dh = r.take(32, "skipped dh")
        n = r.u(4, "skipped n")
        at = r.u(4, "skipped stored_at")
        key = r.take(32, "skipped key")
        entries.append((dh, n, at))
        raw.append(((dh, n), (key, at)))
    r.end("ratchet state")
    s = ratchet.State(dhs_pub=dhs, dhr=dhr, rk=rk, cks=cks, ckr=ckr, ns=ns, nr=nr, pn=pn,
                      events=events, labels=labels, skipped=dict(raw))
    problem = ratchet_invariant(s, entries)
    if problem:
        raise Malformed(f"ratchet state: {problem}")
    return s


# ===================================================== sparse ratchet state

_CHAIN_LEN = 1 + 32 + 8


def _chain_bytes(c: Optional[spqr.Chain]) -> bytes:
    return bytes(_CHAIN_LEN) if c is None else bytes([K.PRESENT]) + c.ck + _be(c.n, 8)


def _read_chain(r: _Reader, what: str) -> Optional[spqr.Chain]:
    present = _presence(r, what)
    ck = r.take(32, f"{what} ck")
    n = r.u(8, f"{what} n")
    if not present:
        if ck != bytes(32) or n != 0:
            raise Malformed(f"{what}: absent chain not zeroed")
        return None
    return spqr.Chain(ck, n)


def spqr_to_bytes(s: spqr.State) -> bytes:
    out = bytearray([K.STATE_VERSION])
    out += s.rk + _be(s.epoch, 8) + bytes([s.direction])
    out += _be(len(s.chains), 4)
    for e, (send, recv) in s.chains.items():
        out += _be(e, 8) + _chain_bytes(send) + _chain_bytes(recv)
    out += _be(len(s.skipped), 4)
    for (e, n), key in s.skipped.items():
        out += _be(e, 8) + _be(n, 8) + key
    return bytes(out)


def spqr_invariant(s: spqr.State) -> Optional[str]:
    if len(s.skipped) > K.MAX_SKIPPED_STORE:
        return "skipped store holds more than MAX_SKIPPED_STORE keys"
    for e in s.chains:
        if not (e <= s.epoch < min(e + K.EPOCHS_KEPT, K.U64_MAX)):
            return f"chains entry epoch {e} outside e <= epoch < e + EPOCHS_KEPT"
    if s.epoch not in s.chains:
        return "the current epoch has no chains entry"
    if any(e not in s.chains for e, _ in s.skipped):
        return "a stored key's epoch has no chains entry"
    return None


def spqr_from_bytes(buf: bytes) -> spqr.State:
    _version(buf, {K.STATE_VERSION}, "sparse ratchet state")
    r = _Reader(buf)
    r.take(1, "version")
    rk = r.take(32, "rk")
    epoch = r.u(8, "epoch")
    direction = r.u(1, "direction")
    if direction not in (K.DIRECTION_A2B, K.DIRECTION_B2A):
        raise Malformed(f"sparse ratchet state: unknown direction tag 0x{direction:02x}")
    chains: Dict[int, list] = {}
    for _ in range(r.count(8 + 2 * _CHAIN_LEN, "chains")):
        e = r.u(8, "epoch_key")
        send = _read_chain(r, "send_chain")
        recv = _read_chain(r, "receive_chain")
        if e in chains:
            raise Malformed("sparse ratchet state: two chains entries share an epoch")
        chains[e] = [send, recv]
    skipped: Dict[Tuple[int, int], bytes] = {}
    for _ in range(r.count(8 + 8 + 32, "skipped")):
        e = r.u(8, "skipped epoch")
        n = r.u(8, "skipped n")
        key = r.take(32, "skipped key")
        if (e, n) in skipped:
            raise Malformed("sparse ratchet state: two stored keys share an epoch and message number")
        skipped[(e, n)] = key
    r.end("sparse ratchet state")
    s = spqr.State(rk=rk, epoch=epoch, direction=direction, chains=chains, skipped=skipped)
    problem = spqr_invariant(s)
    if problem:
        raise Malformed(f"sparse ratchet state: {problem}")
    return s


# ===================================================== triple ratchet state

@dataclass
class TripleState:
    classical: ratchet.State
    sparse: spqr.State


def triple_to_bytes(t: TripleState) -> bytes:
    rb = ratchet_to_bytes(t.classical)
    sb = spqr_to_bytes(t.sparse)
    return bytes([K.STATE_VERSION]) + _be(len(rb), 4) + rb + _be(len(sb), 4) + sb


def classical_role(c: ratchet.State) -> Optional[str]:
    """The role the classical ratchet still shows: a sending chain and no
    receiving chain for the sender, neither for the receiver."""
    if c.cks is not None and c.ckr is None:
        return "sender"
    if c.cks is None and c.ckr is None:
        return "receiver"
    return None


def triple_invariant(t: TripleState) -> Optional[str]:
    role = classical_role(t.classical)
    if role is not None and (t.sparse.direction == K.DIRECTION_A2B) != (role == "sender"):
        return "sparse direction disagrees with the role the classical ratchet shows"
    return None


def triple_from_bytes(buf: bytes) -> TripleState:
    _version(buf, {K.STATE_VERSION}, "triple ratchet state")
    r = _Reader(buf)
    r.take(1, "version")
    rb = r.prefixed("ratchet_state")
    sb = r.prefixed("spqr_state")
    r.end("triple ratchet state")
    t = TripleState(ratchet_from_bytes(rb), spqr_from_bytes(sb))
    problem = triple_invariant(t)
    if problem:
        raise Malformed(f"triple ratchet state: {problem}")
    return t


# ================================================= erasure coder sub-formats

def encoder_to_bytes(e: erasure.Encoder) -> bytes:
    return (_be(e.next, 2) + bytes([1 if e.exhausted else 0]) + _be(len(e.chunks), 4)
            + b"".join(e.chunks))


def encoder_from_bytes(buf: bytes) -> erasure.Encoder:
    r = _Reader(buf)
    nxt = r.u(2, "next")
    exhausted = r.u(1, "exhausted")
    if exhausted not in (0, 1):
        raise Malformed("erasure encoder: exhausted is neither 0x00 nor 0x01")
    count = r.u(4, "count")
    if count > K.MAX_CODEWORDS:
        raise Malformed("erasure encoder: more than MAX_CODEWORDS chunks")
    if count * K.CHUNK_BYTES > r.remaining():
        raise Malformed("erasure encoder: count larger than the buffer could hold")
    chunks = [r.take(K.CHUNK_BYTES, "chunk") for _ in range(count)]
    r.end("erasure encoder")
    if exhausted and nxt != K.U16_MAX:
        raise Malformed("erasure encoder: exhausted while next is not u16::MAX")
    return erasure.Encoder(chunks, nxt, bool(exhausted))


def decoder_to_bytes(d: erasure.Decoder) -> bytes:
    return (_be(d.size, 8) + _be(d.needed, 8) + _be(len(d.held), 4)
            + b"".join(_be(i, 2) + c for i, c in d.held))


def decoder_from_bytes(buf: bytes) -> erasure.Decoder:
    r = _Reader(buf)
    size = r.u(8, "size")
    needed = r.u(8, "needed")
    # "A reader refuses a needed above 65,536 or a size above 2,097,152 ...
    # before narrowing either to its own word size"
    if needed > K.ERASURE_MAX_NEEDED or size > K.ERASURE_MAX_SIZE:
        raise Malformed("erasure decoder: needed or size above its bound")
    count = r.count(2 + K.CHUNK_BYTES, "codewords")
    held = [(r.u(2, "index"), r.take(K.CHUNK_BYTES, "chunk")) for _ in range(count)]
    r.end("erasure decoder")
    if needed != erasure.chunk_count(size):
        raise Malformed("erasure decoder: needed is not ceil(size / 32)")
    if count > needed:
        raise Malformed("erasure decoder: holds more than needed codewords")
    if len({i for i, _ in held}) != count:
        raise Malformed("erasure decoder: two codewords share an index")
    return erasure.Decoder(size, held)


# =================================================================== Braid

BRAID_STATES = {
    0: ("KeysUnsampled", ()),
    1: ("KeysSampled", ("key_pair", "hdr_enc")),
    2: ("HeaderSent", ("key_pair", "ct1_dec", "ek_enc")),
    3: ("Ct1Received", ("key_pair", "ct1", "ek_enc")),
    4: ("EkSentCt1Received", ("key_pair", "ct1", "ct2_dec")),
    5: ("NoHeaderReceived", ("hdr_dec",)),
    6: ("HeaderReceived", ("header", "ek_dec")),
    7: ("Ct1Sampled", ("header", "encaps", "ct1", "ct1_enc", "ek_dec")),
    8: ("EkReceivedCt1Sampled", ("encaps", "ct1", "ek_vector", "ct1_enc")),
    9: ("Ct1Acknowledged", ("header", "encaps", "ct1", "ek_dec")),
    10: ("Ct2Sampled", ("ct2_enc",)),
    11: ("Failed", None),
}

RAW_FIELD_LEN = {
    "key_pair": K.BRAID_KEY_PAIR_LEN,
    "encaps": K.BRAID_ENCAPS_LEN,
    "header": K.BRAID_HEADER_LEN,
    "ct1": K.BRAID_CT1_LEN,
    "ek_vector": K.BRAID_EK_VECTOR_LEN,
}

CODER_VALUE_LEN = {
    "hdr": K.BRAID_HDR_VALUE_LEN,     # header and a 32-byte MAC
    "ek": K.BRAID_EK_VECTOR_LEN,
    "ct1": K.BRAID_CT1_LEN,
    "ct2": K.BRAID_CT2_VALUE_LEN,     # second ciphertext half and a MAC
}


@dataclass
class BraidState:
    tag: int
    epoch: int = 0
    auth_root: bytes = b""
    auth_mac: bytes = b""
    fields: Dict[str, object] = field(default_factory=dict)

    @property
    def failed(self) -> bool:
        return self.tag == K.BRAID_FAILED_TAG

    def is_header_sender(self) -> bool:
        """Tags 0 to 4 are the header-sending side (session-persistence.md, Semantic rules)."""
        return self.tag <= 4


def braid_to_bytes(b: BraidState) -> bytes:
    out = bytearray([K.STATE_VERSION, b.tag])
    if b.tag == K.BRAID_FAILED_TAG:
        return bytes(out)
    out += _be(b.epoch, 8) + b.auth_root + b.auth_mac
    for name in BRAID_STATES[b.tag][1]:
        v = b.fields[name]
        if name.endswith("_enc"):
            data = encoder_to_bytes(v)
        elif name.endswith("_dec"):
            data = decoder_to_bytes(v)
        else:
            data = bytes(v)
        out += _be(len(data), 4) + data
    return bytes(out)


def braid_invariant(b: BraidState) -> Optional[str]:
    if b.failed:
        return None
    if b.epoch < 1:
        return "a live state's epoch is below 1"
    for name, v in b.fields.items():
        if name in RAW_FIELD_LEN:
            if len(v) != RAW_FIELD_LEN[name]:
                return f"{name} is {len(v)} bytes, not {RAW_FIELD_LEN[name]}"
            continue
        n = CODER_VALUE_LEN[name.split("_")[0]]
        if name.endswith("_enc") and len(v.chunks) != erasure.chunk_count(n):
            return f"{name} holds {len(v.chunks)} chunks, not sized for {n} bytes"
        if name.endswith("_dec") and v.size != n:
            return f"{name} has size {v.size}, not {n}"
    return None


def braid_from_bytes(buf: bytes) -> BraidState:
    _version(buf, {K.STATE_VERSION}, "braid")
    r = _Reader(buf)
    r.take(1, "version")
    tag = r.u(1, "state_tag")
    if tag > K.BRAID_MAX_TAG:
        raise Malformed(f"braid: state tag {tag} above 11")
    if tag == K.BRAID_FAILED_TAG:
        r.end("braid (Failed)")
        return BraidState(tag)
    epoch = r.u(8, "epoch")
    if epoch == K.U64_MAX:
        raise Malformed("braid: stored epoch is u64::MAX")
    root = r.take(32, "auth root_key")
    mac = r.take(32, "auth mac_key")
    fields = {}
    for name in BRAID_STATES[tag][1]:
        data = r.prefixed(name)
        if name.endswith("_enc"):
            fields[name] = encoder_from_bytes(data)
        elif name.endswith("_dec"):
            fields[name] = decoder_from_bytes(data)
        else:
            fields[name] = data
    r.end("braid")
    b = BraidState(tag, epoch, root, mac, fields)
    problem = braid_invariant(b)
    if problem:
        raise Malformed(f"braid: {problem}")
    return b


# ================================================================= session

@dataclass
class PendingInitial:
    ephemeral_public: bytes
    kem_ciphertext: bytes
    signed_prekey_id: int
    one_time_prekey_id: int
    kem_prekey_id: int


@dataclass
class SessionState:
    triple: TripleState
    braid: BraidState
    ratchet_private: bytes
    identity_ad: bytes
    our_identity_public: bytes
    peer_identity_public: bytes
    pending_initial: Optional[PendingInitial] = None
    established_ephemeral: Optional[bytes] = None

    @property
    def is_initiator(self) -> bool:
        # "the role read from established_ephemeral, which every responder
        # carries for its whole life and no initiator ever has"
        return self.established_ephemeral is None


def _pending_bytes(p: PendingInitial) -> bytes:
    return (p.ephemeral_public + _be(len(p.kem_ciphertext), 4) + p.kem_ciphertext
            + _be(p.signed_prekey_id, 4) + _be(p.one_time_prekey_id, 4) + _be(p.kem_prekey_id, 4))


def session_to_bytes(s: SessionState) -> bytes:
    tb = triple_to_bytes(s.triple)
    bb = braid_to_bytes(s.braid)
    out = bytearray([K.SESSION_VERSION])
    out += _be(len(tb), 4) + tb + _be(len(bb), 4) + bb
    out += s.ratchet_private + _be(len(s.identity_ad), 4) + s.identity_ad
    out += s.our_identity_public + s.peer_identity_public
    if s.pending_initial is None:
        out += bytes([K.ABSENT])
    else:
        pb = _pending_bytes(s.pending_initial)
        out += bytes([K.PRESENT]) + _be(len(pb), 4) + pb
    if s.established_ephemeral is None:
        out += bytes([K.ABSENT])
    else:
        out += bytes([K.PRESENT]) + _be(len(s.established_ephemeral), 4) + s.established_ephemeral
    return bytes(out)


def session_semantic(s: SessionState) -> Optional[str]:
    t, b = s.triple, s.braid
    if x25519_public(s.ratchet_private) != t.classical.dhs_pub:
        return "ratchet_private is not the private half of dhs_pub"
    if not b.failed:
        expected = b.epoch if 7 <= b.tag <= 10 else b.epoch - 1
        if t.sparse.epoch != expected:
            return f"sparse epoch {t.sparse.epoch} does not follow the Braid's (tag {b.tag}, epoch {b.epoch})"
    initiator, responder = ((s.our_identity_public, s.peer_identity_public) if s.is_initiator
                            else (s.peer_identity_public, s.our_identity_public))
    if s.identity_ad != encode_ec(initiator) + encode_ec(responder):
        return "identity_ad is not EncodeEC(initiator) || EncodeEC(responder)"
    if not b.failed:
        # "at epoch e the session's initiator is the header-sending side
        # (tags 0 to 4) exactly when e is odd"
        braid_initiator = b.is_header_sender() == (b.epoch % 2 == 1)
        if braid_initiator != s.is_initiator:
            return "the Braid's role disagrees with the session's"
    if (t.sparse.direction == K.DIRECTION_A2B) != s.is_initiator:
        return "the sparse ratchet's direction disagrees with the session's role"
    if s.pending_initial is not None and s.established_ephemeral is not None:
        return "an unanswered initiator is also a responder"
    if s.pending_initial is not None and len(s.pending_initial.kem_ciphertext) != K.MLKEM1024_CT_LEN:
        return "pending_initial's kem_ciphertext is not one ML-KEM-1024 ciphertext"
    ee = s.established_ephemeral
    if ee is not None and (len(ee) != K.ENCODED_EC_LEN or ee[0] != K.ENCODE_EC_BYTE):
        return "established_ephemeral is not an EncodeEC value"
    for problem in (triple_invariant(t), braid_invariant(b)):
        if problem:
            return problem
    return None


def session_from_bytes(buf: bytes) -> SessionState:
    buf = bytes(buf)
    _version(buf, {K.SESSION_VERSION}, "session")
    r = _Reader(buf)
    r.take(1, "version")
    triple = triple_from_bytes(r.prefixed("triple_state"))
    braid = braid_from_bytes(r.prefixed("braid"))
    ratchet_private = r.take(32, "ratchet_private")
    identity_ad = r.prefixed("identity_ad")
    ours = r.take(32, "our_identity_public")
    peer = r.take(32, "peer_identity_public")
    pending = None
    if _presence(r, "pending_initial"):
        pr = _Reader(r.prefixed("pending_initial"))
        pending = PendingInitial(pr.take(32, "ephemeral_public"), pr.prefixed("kem_ciphertext"),
                                 pr.u(4, "signed_prekey_id"), pr.u(4, "one_time_prekey_id"),
                                 pr.u(4, "kem_prekey_id"))
        pr.end("pending_initial")
    established = r.prefixed("established_ephemeral") if _presence(r, "established_ephemeral") else None
    r.end("session")
    s = SessionState(triple, braid, ratchet_private, identity_ad, ours, peer, pending, established)
    if session_to_bytes(s) != buf:
        raise NonCanonical("session does not re-encode to its input")
    problem = session_semantic(s)
    if problem:
        raise Inconsistent(f"session: {problem}")
    return s


# ============================================================ prekey store

def _modulus_ok(t_hat: bytes) -> bool:
    """FIPS 203 7.2: ByteEncode12(ByteDecode12(x)) = x, i.e. every 12-bit
    coefficient (little-endian bit order) is below q."""
    for i in range(0, len(t_hat), 3):
        b0, b1, b2 = t_hat[i], t_hat[i + 1], t_hat[i + 2]
        if (b0 | ((b1 & 0x0F) << 8)) >= K.MLKEM_Q or ((b1 >> 4) | (b2 << 4)) >= K.MLKEM_Q:
            return False
    return True


def kem_pair_problem(kp: bytes) -> Optional[str]:
    if len(kp) != K.KEM_PAIR_LEN:
        return f"kem_pair is {len(kp)} bytes, not 4,736"
    dk, ek = kp[:K.KEM_DK_LEN], kp[K.KEM_DK_LEN:]
    if not _modulus_ok(ek[:1536]):
        return "ek fails the FIPS 203 modulus check"
    ek_in_dk = dk[1536:1536 + K.KEM_EK_LEN]
    h = dk[1536 + K.KEM_EK_LEN:1536 + K.KEM_EK_LEN + 32]
    if hashlib.sha3_256(ek_in_dk).digest() != h:
        return "dk fails the FIPS 203 hash check"
    if ek_in_dk != ek:
        return "the ek inside dk differs from ek"
    return None


@dataclass
class PrekeyStore:
    identity_public: bytes
    signed_prekey_secret: bytes
    signed_prekey_id: int
    signed_prekey_sig: bytes
    one_time: List[Tuple[int, bytes]]
    kem_pair: bytes
    kem_id: int
    kem_sig: bytes
    kem_one_time: List[Tuple[int, bytes, bytes]]
    next_id: int
    seen: List[Tuple[int, bytes]] = field(default_factory=list)
    previous_signed: Optional[Tuple[bytes, int, bytes]] = None
    previous_kem: Optional[Tuple[bytes, int, bytes]] = None


def prekey_store_to_bytes(p: PrekeyStore) -> bytes:
    out = bytearray([K.PREKEY_STORE_VERSION])
    out += p.identity_public + p.signed_prekey_secret + _be(p.signed_prekey_id, 4) + p.signed_prekey_sig
    out += _be(len(p.one_time), 4) + b"".join(_be(i, 4) + s for i, s in p.one_time)
    out += _be(len(p.kem_pair), 4) + p.kem_pair + _be(p.kem_id, 4) + p.kem_sig
    out += _be(len(p.kem_one_time), 4)
    for i, kp, sig in p.kem_one_time:
        out += _be(i, 4) + _be(len(kp), 4) + kp + sig
    out += _be(p.next_id, 4)
    out += _be(len(p.seen), 4) + b"".join(_be(k, 4) + fp for k, fp in p.seen)
    if p.previous_signed is None:
        out += bytes([K.ABSENT])
    else:
        sec, i, sig = p.previous_signed
        out += bytes([K.PRESENT]) + sec + _be(i, 4) + sig
    if p.previous_kem is None:
        out += bytes([K.ABSENT])
    else:
        kp, i, sig = p.previous_kem
        out += bytes([K.PRESENT]) + _be(len(kp), 4) + kp + _be(i, 4) + sig
    return bytes(out)


def _checked_kem_pair(r: _Reader, what: str) -> bytes:
    kp = r.prefixed(what)
    problem = kem_pair_problem(kp)
    if problem:
        raise Malformed(f"prekey store: {what}: {problem}")
    return kp


def prekey_store_semantic(p: PrekeyStore) -> Optional[str]:
    ids = [p.signed_prekey_id, p.kem_id] + [i for i, _ in p.one_time] + [i for i, _, _ in p.kem_one_time]
    if p.previous_signed is not None:
        ids.append(p.previous_signed[1])
    if p.previous_kem is not None:
        ids.append(p.previous_kem[1])
    if any(i == K.ABSENT_ID for i in ids):
        return "an identifier is zero"
    if any(i >= p.next_id for i in ids):
        return "an identifier is not below next_id"
    if len(set(ids)) != len(ids):
        return "two identifiers are equal"
    live = {p.kem_id} | ({p.previous_kem[1]} if p.previous_kem is not None else set())
    per_key: Dict[int, int] = {}
    for k, _ in p.seen:
        if k not in live:
            return "a record entry is tagged with a key that is neither kem_id nor previous_kem's"
        per_key[k] = per_key.get(k, 0) + 1
    if any(c > K.MAX_LAST_RESORT_SEEN for c in per_key.values()):
        return "a key has more than MAX_LAST_RESORT_SEEN record entries"
    if len({fp for _, fp in p.seen}) != len(p.seen):
        return "a fingerprint appears twice"
    return None


def prekey_store_from_bytes(buf: bytes) -> PrekeyStore:
    buf = bytes(buf)
    version = _version(buf, K.PREKEY_STORE_VERSIONS_READ, "prekey store")
    r = _Reader(buf)
    r.take(1, "version")
    identity = r.take(32, "identity_public")
    spk_secret = r.take(32, "signed_prekey_secret")
    spk_id = r.u(4, "signed_prekey_id")
    spk_sig = r.take(64, "signed_prekey_sig")
    one_time = [(r.u(4, "one_time id"), r.take(32, "one_time secret"))
                for _ in range(r.count(36, "one_time"))]
    kem_pair = _checked_kem_pair(r, "kem_pair")
    kem_id = r.u(4, "kem_id")
    kem_sig = r.take(64, "kem_sig")
    kem_one_time = []
    for _ in range(r.count(4 + 4 + 64, "kem_one_time")):
        i = r.u(4, "kem_one_time id")
        kp = _checked_kem_pair(r, "kem_one_time kem_pair")
        kem_one_time.append((i, kp, r.take(64, "kem_one_time sig")))
    next_id = r.u(4, "next_id")
    seen: List[Tuple[int, bytes]] = []
    if version >= 0x02:
        count = r.u(4, "seen_count")
        ceiling = 2 * K.MAX_LAST_RESORT_SEEN if version == 0x04 else K.MAX_LAST_RESORT_SEEN
        if count > ceiling:
            raise Malformed("prekey store: seen_count exceeds what this version could have written")
        entry = 36 if version == 0x04 else 32
        if count * entry > r.remaining():
            raise Malformed("prekey store: seen_count larger than the buffer could hold")
        for _ in range(count):
            if version == 0x04:
                seen.append((r.u(4, "seen kem_id"), r.take(32, "fingerprint")))
            else:
                seen.append((kem_id, r.take(32, "fingerprint")))   # read back tagged with the current key
    previous_signed = previous_kem = None
    if version >= 0x03:
        if _presence(r, "previous_signed"):
            previous_signed = (r.take(32, "previous secret"), r.u(4, "previous id"), r.take(64, "previous sig"))
        if _presence(r, "previous_kem"):
            kp = _checked_kem_pair(r, "previous_kem kem_pair")
            previous_kem = (kp, r.u(4, "previous_kem id"), r.take(64, "previous_kem sig"))
    r.end("prekey store")
    store = PrekeyStore(identity, spk_secret, spk_id, spk_sig, one_time, kem_pair, kem_id, kem_sig,
                        kem_one_time, next_id, seen, previous_signed, previous_kem)
    if version == K.PREKEY_STORE_VERSION and prekey_store_to_bytes(store) != buf:
        raise NonCanonical("prekey store does not re-encode to its input")
    problem = prekey_store_semantic(store)
    if problem:
        raise Malformed(f"prekey store: {problem}")
    return store
