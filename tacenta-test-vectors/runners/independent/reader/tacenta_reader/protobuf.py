"""The bounded protobuf profile, from protocol/protobuf-profile.md.

Parses the protobuf region of a ratchet message body and of a prekey
envelope, refusing everything outside the profile. Categories are this
reader's own ("Which condition produces which category is
implementation-defined"); a conforming reader must refuse exactly the byte
strings the page refuses.
"""

from typing import Dict, Tuple

from . import constants as K


class ProtobufRefused(ValueError):
    def __init__(self, category: str, detail: str):
        super().__init__(f"{category}: {detail}")
        self.category = category


WIRE_VARINT = 0
WIRE_LEN = 2

# field -> (name, wire type, required)
RATCHET_BODY = {
    1: ("ratchetKey", WIRE_LEN, True),
    2: ("counter", WIRE_VARINT, True),
    3: ("previousCounter", WIRE_VARINT, True),
    4: ("ciphertext", WIRE_LEN, True),
    5: ("pq", WIRE_LEN, True),
}

PREKEY_ENVELOPE = {
    1: ("prekeyId", WIRE_VARINT, False),
    2: ("baseKey", WIRE_LEN, True),
    3: ("identityKey", WIRE_LEN, True),
    4: ("message", WIRE_LEN, True),
    5: ("registrationId", WIRE_VARINT, True),
    6: ("signedPrekeyId", WIRE_VARINT, True),
    7: ("pqPrekeyId", WIRE_VARINT, True),
    8: ("kem", WIRE_LEN, True),
}


def read_varint(buf: bytes, pos: int) -> Tuple[int, int]:
    value = 0
    for i in range(K.PB_MAX_VARINT_BYTES):
        if pos >= len(buf):
            raise ProtobufRefused("Truncated", "input ends before a varint's final byte")
        b = buf[pos]
        pos += 1
        value |= (b & 0x7F) << (7 * i)
        if value > K.PB_MAX_U32:
            raise ProtobufRefused("BadVarint", "value does not fit 32 bits")
        if not b & 0x80:
            if i > 0 and b == 0x00:
                raise ProtobufRefused("BadVarint", "not minimal (final byte 0x00)")
            return value, pos
    raise ProtobufRefused("BadVarint", "longer than five bytes")


def read_tag(buf: bytes, pos: int) -> Tuple[int, int, int]:
    value, pos = read_varint(buf, pos)
    field, wire = value >> 3, value & 7
    if field == 0 or field > K.PB_MAX_FIELD_NUMBER:
        raise ProtobufRefused("NotInProfile", f"field number {field}")
    if wire not in (WIRE_VARINT, WIRE_LEN):
        raise ProtobufRefused("NotInProfile", f"wire type {wire}")
    return field, wire, pos


def parse(region: bytes, message_type: Dict[int, Tuple[str, int, bool]]) -> Dict[str, object]:
    region = bytes(region)
    if len(region) > K.PB_MAX_MESSAGE_LEN:
        raise ProtobufRefused("TooLong", "region longer than maxMessageLen")
    pos = 0
    recorded = []
    out: Dict[str, object] = {}
    while pos < len(region):
        field, wire, pos = read_tag(region, pos)
        if field in recorded:
            raise ProtobufRefused("Duplicate", f"field {field} repeated")
        if len(recorded) >= K.PB_MAX_FIELDS:
            raise ProtobufRefused("NotInProfile", "maxFields already recorded")
        recorded.append(field)
        spec = message_type.get(field)
        if spec is None or spec[1] != wire:
            raise ProtobufRefused("NotInProfile", f"field {field} with wire type {wire}")
        if wire == WIRE_VARINT:
            value, pos = read_varint(region, pos)
        else:
            length, pos = read_varint(region, pos)
            if length > len(region) - pos:
                raise ProtobufRefused("Truncated", "length runs past the region")
            value = region[pos:pos + length]
            pos += length
        out[spec[0]] = value
    for field, (name, _, required) in message_type.items():
        if required and name not in out:
            raise ProtobufRefused("NotInProfile", f"required field {field} ({name}) missing")
    return out


def parse_ratchet_body(region: bytes) -> Dict[str, object]:
    return parse(region, RATCHET_BODY)


def parse_prekey_envelope(region: bytes) -> Dict[str, object]:
    """prekeyId absent is not the same as prekeyId 0: it is simply not in the result."""
    return parse(region, PREKEY_ENVELOPE)


# ---------------------------------------------------------------- encoding
# The model defines no encoder; these emit ascending field order and omit an
# absent prekeyId, as the page describes the implementation doing.

def encode_varint(v: int) -> bytes:
    if not 0 <= v <= K.PB_MAX_U32:
        raise ValueError("varint value out of range")
    out = bytearray()
    while True:
        b = v & 0x7F
        v >>= 7
        if v:
            out.append(b | 0x80)
        else:
            out.append(b)
            return bytes(out)


def encode_field(field: int, wire: int, value) -> bytes:
    tag = encode_varint(field << 3 | wire)
    if wire == WIRE_VARINT:
        return tag + encode_varint(value)
    return tag + encode_varint(len(value)) + bytes(value)


def encode(values: Dict[str, object], message_type: Dict[int, Tuple[str, int, bool]]) -> bytes:
    out = bytearray()
    for field in sorted(message_type):
        name, wire, _ = message_type[field]
        if values.get(name) is not None:
            out += encode_field(field, wire, values[name])
    return bytes(out)
