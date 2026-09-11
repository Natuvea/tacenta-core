"""Wire formats, from tacenta-spec/protocol/message-format.md.

- ratchet message = composite header (102 bytes) || ciphertext
- CONCAT(ad, header) = len(ad) (4, BE) || ad || composite header
- initial (prekey) message
- prekey bundle
- EncodeEC / EncodeKEM (session-establishment.md, Parameters)

Every refusal the spec states for these decoders is implemented here; each
raise carries a short reason. Rejection is a DecodeError, distinct from any
authentication failure (message-format.md, Rejection).
"""

from dataclasses import dataclass
from typing import Callable, Optional, Tuple

from . import constants as K


class DecodeError(ValueError):
    """A decode failure (message-format.md, Rejection)."""


class EncodeError(ValueError):
    """The caller asked for an encoding of a value the format cannot hold."""


class BundleRefused(Exception):
    """The initiator refuses a decoded bundle (session-establishment.md)."""


# ----------------------------------------------------------------- helpers

def _be(value: int, width: int, name: str) -> bytes:
    if not isinstance(value, int) or value < 0 or value >= 1 << (8 * width):
        raise EncodeError(f"{name} does not fit in {width} bytes")
    return value.to_bytes(width, "big")


def _fixed(value: bytes, width: int, name: str) -> bytes:
    if not isinstance(value, (bytes, bytearray)) or len(value) != width:
        raise EncodeError(f"{name} must be exactly {width} bytes")
    return bytes(value)


class _Reader:
    def __init__(self, buf: bytes):
        self.buf = bytes(buf)
        self.pos = 0

    def remaining(self) -> int:
        return len(self.buf) - self.pos

    def take(self, n: int, what: str) -> bytes:
        if n < 0 or n > self.remaining():
            raise DecodeError(f"input too short for {what}")
        out = self.buf[self.pos:self.pos + n]
        self.pos += n
        return out

    def uint(self, width: int, what: str) -> int:
        return int.from_bytes(self.take(width, what), "big")

    def rest(self) -> bytes:
        out = self.buf[self.pos:]
        self.pos = len(self.buf)
        return out


def _check_framing(buf: bytes, expected_type: int, what: str) -> None:
    # message-format.md: every message begins with a version byte and a type
    # byte; a decoder rejects an unrecognised version or an unexpected type,
    # and should reject a wrong object "on the type byte rather than on a
    # length mismatch further in" -- so framing is checked before lengths.
    if len(buf) < 2:
        raise DecodeError(f"{what}: input too short for framing")
    if buf[0] != K.VERSION:
        raise DecodeError(f"{what}: unrecognised version 0x{buf[0]:02x}")
    if buf[1] != expected_type:
        raise DecodeError(f"{what}: unexpected type byte 0x{buf[1]:02x}")


# ---------------------------------------------------------- EncodeEC / KEM

def encode_ec(key: bytes) -> bytes:
    return bytes([K.ENCODE_EC_BYTE]) + _fixed(key, K.EC_KEY_LEN, "curve key")


def decode_ec(encoded: bytes) -> bytes:
    # session-establishment.md: "a decoder that does not recognise the
    # leading byte fails"; EncodeEC is fixed at 33 bytes.
    if len(encoded) != K.ENCODED_EC_LEN:
        raise DecodeError("EncodeEC value is not 33 bytes")
    if encoded[0] != K.ENCODE_EC_BYTE:
        raise DecodeError(f"unrecognised EncodeEC curve byte 0x{encoded[0]:02x}")
    return bytes(encoded[1:])


def encode_kem(key: bytes, key_len: int = K.MLKEM1024_EK_LEN) -> bytes:
    return bytes([K.ENCODE_KEM_BYTE]) + _fixed(key, key_len, "KEM key")


def decode_kem(encoded: bytes, key_len: int = K.MLKEM1024_EK_LEN) -> bytes:
    if len(encoded) != key_len + 1:
        raise DecodeError("EncodeKEM value has the wrong length")
    if encoded[0] != K.ENCODE_KEM_BYTE:
        raise DecodeError(f"unrecognised EncodeKEM byte 0x{encoded[0]:02x}")
    return bytes(encoded[1:])


# -------------------------------------------------------- composite header

@dataclass(frozen=True)
class Codeword:
    index: int
    data: bytes


@dataclass(frozen=True)
class CompositeHeader:
    dh: bytes
    pn: int
    n: int
    pq_epoch: int
    pq_n: int
    ag_epoch: int
    ag_type: int
    codeword: Optional[Codeword]


def encode_composite(h: CompositeHeader) -> bytes:
    if h.ag_type not in K.AG_TYPES:
        raise EncodeError("ag_type outside the six values")
    out = bytearray([K.VERSION, K.TYPE_RATCHET])
    out += _fixed(h.dh, K.EC_KEY_LEN, "dh")
    out += _be(h.pn, 4, "pn")
    out += _be(h.n, 4, "n")
    out += _be(h.pq_epoch, 8, "pq_epoch")
    out += _be(h.pq_n, 8, "pq_n")
    out += _be(h.ag_epoch, 8, "ag_epoch")
    out += bytes([h.ag_type])
    if h.codeword is None:
        # "a presence byte, then the field's full width regardless, zeroed
        # when absent"
        out += bytes([K.ABSENT]) + bytes(2 + K.CHUNK_BYTES)
    else:
        out += bytes([K.PRESENT])
        out += _be(h.codeword.index, 2, "chunk_index")
        out += _fixed(h.codeword.data, K.CHUNK_BYTES, "chunk")
    assert len(out) == K.COMPOSITE_LEN
    return bytes(out)


def decode_composite_prefix(buf: bytes) -> Tuple[CompositeHeader, bytes]:
    """Decode a composite header at the front of buf; return (header, rest)."""
    buf = bytes(buf)
    _check_framing(buf, K.TYPE_RATCHET, "ratchet message")
    if len(buf) < K.COMPOSITE_LEN:
        raise DecodeError("ratchet message shorter than its framing and header")
    r = _Reader(buf)
    r.take(2, "framing")
    dh = r.take(32, "dh")
    pn = r.uint(4, "pn")
    n = r.uint(4, "n")
    pq_epoch = r.uint(8, "pq_epoch")
    pq_n = r.uint(8, "pq_n")
    ag_epoch = r.uint(8, "ag_epoch")
    ag_type = r.uint(1, "ag_type")
    if ag_type not in K.AG_TYPES:
        raise DecodeError(f"ag_type 0x{ag_type:02x} outside the six values")
    present = r.uint(1, "chunk_present")
    index_bytes = r.take(2, "chunk_index")
    data = r.take(K.CHUNK_BYTES, "chunk")
    if present == K.ABSENT:
        if index_bytes != bytes(2) or data != bytes(K.CHUNK_BYTES):
            raise DecodeError("absent codeword with non-zero index or chunk bytes")
        codeword = None
    elif present == K.PRESENT:
        codeword = Codeword(int.from_bytes(index_bytes, "big"), data)
    else:
        raise DecodeError(f"presence byte 0x{present:02x} is neither 0x00 nor 0x01")
    header = CompositeHeader(dh, pn, n, pq_epoch, pq_n, ag_epoch, ag_type, codeword)
    return header, r.rest()


def decode_composite(buf: bytes) -> CompositeHeader:
    """Decode exactly one composite header; trailing bytes are rejected."""
    header, rest = decode_composite_prefix(buf)
    if rest:
        raise DecodeError("trailing bytes after composite header")
    return header


def encode_ratchet_message(h: CompositeHeader, ciphertext: bytes) -> bytes:
    return encode_composite(h) + bytes(ciphertext)


def decode_ratchet_message(buf: bytes) -> Tuple[CompositeHeader, bytes]:
    # The ciphertext "runs to the end of the message"; it may be empty
    # (serialization vector "empty-ciphertext").
    return decode_composite_prefix(buf)


# ---------------------------------------------------------- associated data

def concat_ad(ad: bytes, composite_header: bytes) -> bytes:
    """CONCAT(ad, header) = len(ad) (4, BE) || ad || composite_header.

    "header here is the whole composite header, not the classical part of
    it": anything that is not exactly one valid composite header is refused.
    """
    header = bytes(composite_header)
    try:
        decode_composite(header)
    except DecodeError as e:
        raise EncodeError(f"CONCAT header is not a composite header: {e}")
    return _be(len(ad), 4, "len(ad)") + bytes(ad) + header


# ----------------------------------------------------------- initial message

@dataclass(frozen=True)
class InitialMessage:
    identity: bytes            # EncodeEC form, 33 bytes
    ephemeral: bytes           # EncodeEC form, 33 bytes
    kem_ciphertext: bytes
    signed_prekey_id: int
    one_time_prekey_id: int    # ABSENT_ID means "no one-time prekey was used"
    kem_prekey_id: int
    ratchet_message: bytes

    @property
    def one_time_prekey_used(self) -> bool:
        return self.one_time_prekey_id != K.ABSENT_ID


def encode_initial(m: InitialMessage, validate_ratchet_message: bool = False) -> bytes:
    for name, v in (("identity", m.identity), ("ephemeral", m.ephemeral)):
        try:
            decode_ec(v)
        except DecodeError as e:
            raise EncodeError(f"{name}: {e}")
    if validate_ratchet_message:
        try:
            decode_ratchet_message(m.ratchet_message)
        except DecodeError as e:
            raise EncodeError(f"ratchet_message: {e}")
    out = bytearray([K.VERSION, K.TYPE_INITIAL])
    out += m.identity + m.ephemeral
    out += _be(len(m.kem_ciphertext), 4, "kem_ciphertext_len") + bytes(m.kem_ciphertext)
    out += _be(m.signed_prekey_id, 4, "signed_prekey_id")
    out += _be(m.one_time_prekey_id, 4, "one_time_prekey_id")
    out += _be(m.kem_prekey_id, 4, "kem_prekey_id")
    out += bytes(m.ratchet_message)
    return bytes(out)


def decode_initial(buf: bytes, validate_ratchet_message: bool = False) -> InitialMessage:
    """Decode an initial message.

    validate_ratchet_message=False is the default because the vectors'
    ratchet_message fields ("dead", "00") are not ratchet messages; the spec
    does not say whether the initial decoder checks them (GAPS.md G-04).
    """
    buf = bytes(buf)
    _check_framing(buf, K.TYPE_INITIAL, "initial message")
    r = _Reader(buf)
    r.take(2, "framing")
    identity = r.take(K.ENCODED_EC_LEN, "identity")
    ephemeral = r.take(K.ENCODED_EC_LEN, "ephemeral")
    # EncodeEC leading-byte refusal (session-establishment.md), GAPS.md G-05.
    decode_ec(identity)
    decode_ec(ephemeral)
    ct_len = r.uint(4, "kem_ciphertext_len")
    if ct_len > r.remaining() or r.remaining() - ct_len < 12:
        raise DecodeError("kem_ciphertext_len overruns the input")
    kem_ciphertext = r.take(ct_len, "kem_ciphertext")
    spk_id = r.uint(4, "signed_prekey_id")
    otpk_id = r.uint(4, "one_time_prekey_id")
    kem_id = r.uint(4, "kem_prekey_id")
    ratchet_message = r.rest()
    if validate_ratchet_message:
        decode_ratchet_message(ratchet_message)
    return InitialMessage(identity, ephemeral, kem_ciphertext, spk_id, otpk_id,
                          kem_id, ratchet_message)


# ------------------------------------------------------------- prekey bundle

@dataclass(frozen=True)
class PrekeyBundle:
    identity_key: bytes
    signed_prekey: bytes
    signed_prekey_signature: bytes
    kem_prekey: bytes
    kem_prekey_signature: bytes
    one_time_prekey: Optional[bytes]
    signed_prekey_id: int
    one_time_prekey_id: int
    kem_prekey_id: int


def encode_bundle(b: PrekeyBundle, kem_prekey_len: Optional[int] = K.MLKEM1024_EK_LEN) -> bytes:
    if kem_prekey_len is not None and len(b.kem_prekey) != kem_prekey_len:
        raise EncodeError("kem_prekey has the wrong length for the parameter set")
    out = bytearray([K.VERSION, K.TYPE_BUNDLE])
    out += _fixed(b.identity_key, 32, "identity_key")
    out += _fixed(b.signed_prekey, 32, "signed_prekey")
    out += _fixed(b.signed_prekey_signature, 64, "signed_prekey_signature")
    out += _be(len(b.kem_prekey), 4, "kem_prekey_len") + bytes(b.kem_prekey)
    out += _fixed(b.kem_prekey_signature, 64, "kem_prekey_signature")
    if b.one_time_prekey is None:
        out += bytes([K.ABSENT]) + bytes(32)
    else:
        out += bytes([K.PRESENT]) + _fixed(b.one_time_prekey, 32, "one_time_prekey")
    out += _be(b.signed_prekey_id, 4, "signed_prekey_id")
    out += _be(b.one_time_prekey_id, 4, "one_time_prekey_id")
    out += _be(b.kem_prekey_id, 4, "kem_prekey_id")
    return bytes(out)


def decode_bundle(buf: bytes, kem_prekey_len: Optional[int] = K.MLKEM1024_EK_LEN) -> PrekeyBundle:
    """Decode a prekey bundle.

    kem_prekey_len: the parameter set's encapsulation-key length. The spec
    says a bundle "produced under one parameter set fails to decode under
    another"; enforcing the expected length is how this reader realises that
    sentence (GAPS.md G-06). Pass None to accept any length.
    """
    buf = bytes(buf)
    _check_framing(buf, K.TYPE_BUNDLE, "prekey bundle")
    r = _Reader(buf)
    r.take(2, "framing")
    identity_key = r.take(32, "identity_key")
    signed_prekey = r.take(32, "signed_prekey")
    spk_sig = r.take(64, "signed_prekey_signature")
    kem_len = r.uint(4, "kem_prekey_len")
    if kem_len > r.remaining():
        raise DecodeError("kem_prekey_len overruns the input")
    if kem_prekey_len is not None and kem_len != kem_prekey_len:
        raise DecodeError("kem_prekey length is not this parameter set's")
    kem_prekey = r.take(kem_len, "kem_prekey")
    kem_sig = r.take(64, "kem_prekey_signature")
    present = r.uint(1, "one_time_prekey_present")
    otpk = r.take(32, "one_time_prekey")
    spk_id = r.uint(4, "signed_prekey_id")
    otpk_id = r.uint(4, "one_time_prekey_id")
    kem_id = r.uint(4, "kem_prekey_id")
    if r.remaining():
        raise DecodeError("trailing bytes after prekey bundle")
    if present == K.ABSENT:
        if otpk != bytes(32):
            raise DecodeError("absent one-time prekey with non-zero bytes")
        one_time = None
    elif present == K.PRESENT:
        one_time = otpk
    else:
        raise DecodeError(f"presence byte 0x{present:02x} is neither 0x00 nor 0x01")
    return PrekeyBundle(identity_key, signed_prekey, spk_sig, kem_prekey, kem_sig,
                        one_time, spk_id, otpk_id, kem_id)


def initiator_check_bundle(b: PrekeyBundle,
                           expected_identity: Optional[bytes] = None,
                           verify: Optional[Callable[[bytes, bytes, bytes], Optional[bytes]]] = None,
                           kem_prekey_len: int = K.MLKEM1024_EK_LEN) -> None:
    """The initiator's refusals before any agreement is computed.

    session-establishment.md, Sending the initial message: verify every
    signature (over the tagged forms, message-format.md), refuse an identity
    that is not the one named, refuse a one-time prekey / identifier presence
    disagreement.
    """
    if expected_identity is not None and bytes(expected_identity) != b.identity_key:
        raise BundleRefused("identity key is not the one the initiator set out to reach")
    has_key = b.one_time_prekey is not None
    has_id = b.one_time_prekey_id != K.ABSENT_ID
    if has_key != has_id:
        raise BundleRefused("one-time prekey and its identifier disagree about presence")
    if verify is None:
        from .curve25519 import xeddsa_verify as verify  # noqa: N813
    if verify(b.identity_key, encode_ec(b.signed_prekey), b.signed_prekey_signature) is None:
        raise BundleRefused("signed prekey signature does not verify")
    if verify(b.identity_key, encode_kem(b.kem_prekey, kem_prekey_len), b.kem_prekey_signature) is None:
        raise BundleRefused("KEM prekey signature does not verify")
