"""protobuf-profile.md cases. No vector exercises the profile."""

import itertools

from _casekit import accepts, registry, rejects
from tacenta_reader import constants as K
from tacenta_reader import protobuf as PB

CASES, case = registry()
PP = "protobuf-profile.md"
REF = PB.ProtobufRefused

BODY = dict(ratchetKey=b"\x05" + b"\x11" * 32, counter=7, previousCounter=3, ciphertext=b"\xca\xfe" * 20, pq=b"\x01\x02")
ENVELOPE = dict(prekeyId=9, baseKey=b"\x05" + b"\x22" * 32, identityKey=b"\x05" + b"\x33" * 32, message=b"inner",
                registrationId=12345, signedPrekeyId=1, pqPrekeyId=4, kem=b"\x08" * 10)


def body_fields(values=BODY):
    return {f: PB.encode_field(f, PB.RATCHET_BODY[f][1], values[PB.RATCHET_BODY[f][0]]) for f in PB.RATCHET_BODY}


def env_fields(values=ENVELOPE):
    return {f: PB.encode_field(f, PB.PREKEY_ENVELOPE[f][1], values[PB.PREKEY_ENVELOPE[f][0]])
            for f in PB.PREKEY_ENVELOPE if values.get(PB.PREKEY_ENVELOPE[f][0]) is not None}


def varint(bs):
    v, pos = PB.read_varint(bytes(bs), 0)
    return v, pos


@case("PF-01 varints: base-128 little-endian; minimal spellings of 0, 1, 127, 128, 300, 2^32 - 1 decode; every accepted 1- or 2-byte varint is minimal",
      f"{PP} Varints: every accepted varint is exactly the minimal encoding of the value it decodes to")
def _():
    for v, hexs in ((0, "00"), (1, "01"), (127, "7f"), (128, "8001"), (300, "ac02"), (K.U32_MAX, "ffffffff0f")):
        assert varint(bytes.fromhex(hexs)) == (v, len(hexs) // 2)
        assert PB.encode_varint(v).hex() == hexs
    for a in range(256):
        for bs in ([a], [a, 0], [a, 1], [a, 0x7F]):
            try:
                v, pos = varint(bs)
            except REF:
                continue
            assert PB.encode_varint(v) == bytes(bs[:pos]), bs


@case("PF-02 varint refusals: longer than five bytes, not minimal, above 2^32 - 1, input ends first",
      f"{PP} Varints: A varint is refused when any of the following holds")
def _():
    for hexs in ("ffffffffff01", "8080808080", "8000", "ff00", "808000", "ffffffff10", "8080808010", "ffffffff7f",
                 "", "80", "ffff"):
        rejects(varint, bytes.fromhex(hexs), exc=REF)
    for last in range(0x01, 0x10):
        assert varint(bytes([0x80, 0x80, 0x80, 0x80, last]))[0] == last << 28
    v, pos = varint(bytes.fromhex("0105ff"))
    assert (v, pos) == (1, 1), "bytes after the final byte are left for what follows"


@case("PF-03 tags: every accepted tag is one byte from 0x08 to 0x7A with field 1..15 and wire type 0 or 2; field 0, field 16+, wire 1, 3-7 and multi-byte tags are refused",
      f"{PP} Tags: every accepted tag is a single byte, from 0x08 (field 1, varint) to 0x7A (field 15, length-delimited)")
def _():
    accepted = []
    for b in range(256):
        try:
            f, w, _ = PB.read_tag(bytes([b, 0]), 0)
            accepted.append(b)
        except REF:
            pass
    expect = [b for b in range(0x80) if 1 <= b >> 3 <= 15 and b & 7 in (0, 2)]
    assert accepted == expect and min(accepted) == 0x08 and max(accepted) == 0x7A
    for hexs in ("8001", "8201", "8800", "00", "09", "0b", "0c", "0d", "0e", "0f"):
        rejects(PB.read_tag, bytes.fromhex(hexs), 0, exc=REF)


@case("PF-04 bounds: a region above maxMessageLen is refused before any byte is read; exactly 16,384 bytes is within the bound",
      f"{PP} Bounds: A region of exactly maxMessageLen bytes is within the bound")
def _():
    fields = body_fields()
    fixed = b"".join(fields[f] for f in (1, 2, 3, 5))
    pad = K.PB_MAX_MESSAGE_LEN - len(fixed) - 1 - 2     # tag + 2-byte length varint
    ct = PB.encode_field(4, PB.WIRE_LEN, b"\x00" * pad)
    region = fixed + ct
    assert len(region) == K.PB_MAX_MESSAGE_LEN
    accepts(PB.parse_ratchet_body, region)
    e = rejects(PB.parse_ratchet_body, region + b"\x00", exc=REF)
    assert e.category == "TooLong"
    rejects(PB.parse_ratchet_body, b"\xff" * (K.PB_MAX_MESSAGE_LEN + 1), exc=REF)


@case("PF-05 length-delimited: a len past the region is refused; len 0 gives an empty value",
      f"{PP} Length-delimited fields: A len greater than the number of bytes left in the region after it is refused")
def _():
    fields = body_fields()
    base = b"".join(fields[f] for f in (2, 3, 4, 5))
    rejects(PB.parse_ratchet_body, base + b"\x0a\x05abcd", exc=REF)
    rejects(PB.parse_ratchet_body, base + b"\x0a\xff\xff\xff\xff\x0f", exc=REF)
    got = accepts(PB.parse_ratchet_body, base + b"\x0a\x00")
    assert got["ratchetKey"] == b""


@case("PF-06 ratchet body: all five required; a missing field, a field 6-15, a repeated field, the wrong wire type or a leftover byte is refused; any of the 120 orders is accepted",
      f"{PP} Ratchet message body: Every field is required ... A field number of 6 to 15 ... A repeated field number is refused")
def _():
    fields = body_fields()
    whole = b"".join(fields[f] for f in sorted(fields))
    got = accepts(PB.parse_ratchet_body, whole)
    assert got == BODY
    for missing in fields:
        rejects(PB.parse_ratchet_body, b"".join(fields[f] for f in sorted(fields) if f != missing), exc=REF)
    for extra in (6, 7, 15):
        rejects(PB.parse_ratchet_body, whole + PB.encode_field(extra, PB.WIRE_VARINT, 1), exc=REF)
        rejects(PB.parse_ratchet_body, whole + PB.encode_field(extra, PB.WIRE_LEN, b""), exc=REF)
    rejects(PB.parse_ratchet_body, whole + fields[2], exc=REF)
    rejects(PB.parse_ratchet_body, whole.replace(fields[2], PB.encode_field(2, PB.WIRE_LEN, b"\x07")), exc=REF)
    rejects(PB.parse_ratchet_body, whole.replace(fields[1], PB.encode_field(1, PB.WIRE_VARINT, 5)), exc=REF)
    rejects(PB.parse_ratchet_body, whole + b"\x00", exc=REF)
    orders = 0
    for perm in itertools.permutations(sorted(fields)):
        assert PB.parse_ratchet_body(b"".join(fields[f] for f in perm)) == BODY
        orders += 1
    assert orders == 120


@case("PF-07 prekey envelope: field 1 optional and distinct from 0; fields 2-8 required; 9-15, repeats (including field 1) and wrong wire types refused",
      f"{PP} Prekey envelope: a present field 1 with the value 0 is accepted and gives the identifier 0")
def _():
    fields = env_fields()
    with_id = b"".join(fields[f] for f in sorted(fields))
    assert accepts(PB.parse_prekey_envelope, with_id) == ENVELOPE
    without = b"".join(fields[f] for f in sorted(fields) if f != 1)
    got = accepts(PB.parse_prekey_envelope, without)
    assert "prekeyId" not in got
    zero = PB.encode_field(1, PB.WIRE_VARINT, 0) + without
    assert accepts(PB.parse_prekey_envelope, zero)["prekeyId"] == 0
    assert zero != without
    rejects(PB.parse_prekey_envelope, with_id + fields[1], exc=REF)
    for missing in range(2, 9):
        rejects(PB.parse_prekey_envelope, b"".join(fields[f] for f in sorted(fields) if f != missing), exc=REF)
    for extra in (9, 12, 15):
        rejects(PB.parse_prekey_envelope, with_id + PB.encode_field(extra, PB.WIRE_VARINT, 0), exc=REF)
    rejects(PB.parse_prekey_envelope, with_id.replace(fields[5], PB.encode_field(5, PB.WIRE_LEN, b"")), exc=REF)
    rejects(PB.parse_prekey_envelope, with_id.replace(fields[8], PB.encode_field(8, PB.WIRE_VARINT, 3)), exc=REF)
    rejects(PB.parse_prekey_envelope, with_id + b"\x01", exc=REF)


@case("PF-08 nothing inside a field is validated: empty keys and kem, zero and maximum counters and identifiers",
      f"{PP} Field order and canonicality: Nothing inside a field is validated")
def _():
    body = dict(ratchetKey=b"", counter=0, previousCounter=K.U32_MAX, ciphertext=b"", pq=b"\xff" * 3)
    assert accepts(PB.parse_ratchet_body, PB.encode(body, PB.RATCHET_BODY)) == body
    env = dict(prekeyId=K.U32_MAX, baseKey=b"", identityKey=b"x", message=b"", registrationId=0,
               signedPrekeyId=0, pqPrekeyId=K.U32_MAX, kem=b"")
    assert accepts(PB.parse_prekey_envelope, PB.encode(env, PB.PREKEY_ENVELOPE)) == env


@case("PF-09 field order is free, so a parsed message re-encoded need not reproduce its bytes",
      f"{PP} Field order and canonicality: for an input whose fields are not in ascending order it does not")
def _():
    fields = body_fields()
    reordered = b"".join(fields[f] for f in (5, 4, 3, 2, 1))
    parsed = accepts(PB.parse_ratchet_body, reordered)
    assert PB.encode(parsed, PB.RATCHET_BODY) != reordered
    assert PB.encode(parsed, PB.RATCHET_BODY) == b"".join(fields[f] for f in (1, 2, 3, 4, 5))
