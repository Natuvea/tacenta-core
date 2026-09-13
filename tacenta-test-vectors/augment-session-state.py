#!/usr/bin/env python3
"""Append session vectors whose oracle is outside the Lean model.

The Lean model intentionally does not compute X25519, so it cannot decide the
session rule that ratchet_private's public half is the classical ratchet's
`dhs_pub`. This post-processor keeps the model-generated file as the base and
adds the one deterministic vector that needs the real curve operation. Both the
independent reader and tacenta-core's Rust reader check that operation.
"""
from __future__ import annotations

import json
import sys
from pathlib import Path

VECTOR_ID = "ratchet-private-does-not-match-dhs-pub"
SOURCE_NOTE = (
    "; the ratchet-private mismatch vector is appended by "
    "tacenta-test-vectors/augment-session-state.py from the responder fixture: "
    "it flips byte 7 of ratchet_private, away from X25519's clamped bits, and is "
    "checked by the Rust and independent readers because the Lean model does "
    "not compute the curve."
)


def read_u32(buf: bytes, pos: int) -> int:
    return int.from_bytes(buf[pos : pos + 4], "big")


def ratchet_private_offset(stored: bytes) -> int:
    if not stored or stored[0] != 0x01:
        raise SystemExit("session augmenter: responder vector is not a v1 session")
    pos = 1
    pos += 4 + read_u32(stored, pos)
    pos += 4 + read_u32(stored, pos)
    if pos + 32 > len(stored):
        raise SystemExit("session augmenter: responder vector ends before ratchet_private")
    return pos


def lean_style(obj: object) -> str:
    rendered = json.dumps(obj, separators=(", ", ": "))
    return rendered.replace('{"', '{ "').replace('"}', '" }')


def main(path: str) -> None:
    p = Path(path)
    text = p.read_text()
    doc = json.loads(text)
    if any(v.get("id") == VECTOR_ID for v in doc["vectors"]):
        return
    responder = next((v for v in doc["vectors"] if v.get("id") == "responder"), None)
    if responder is None:
        raise SystemExit("session augmenter: no responder vector found")
    stored = bytearray.fromhex(responder["inputs"]["bytes"])
    stored[ratchet_private_offset(stored) + 7] ^= 0x01
    vector = {
        "id": VECTOR_ID,
        "comment": (
            "ratchet_private is mutated away from the private half of the "
            "classical ratchet's dhs_pub while the stored session remains "
            "well-formed and canonical"
        ),
        "result": "invalid",
        "refusal": "inconsistent",
        "inputs": {"bytes": stored.hex()},
    }
    if SOURCE_NOTE not in doc["source"]:
        old = f'  "source": {json.dumps(doc["source"])},'
        new = f'  "source": {json.dumps(doc["source"] + SOURCE_NOTE)},'
        if old not in text:
            raise SystemExit("session augmenter: could not find source line")
        text = text.replace(old, new, 1)
    marker = "\n  ]\n}\n"
    if marker not in text:
        raise SystemExit("session augmenter: could not find vector-list ending")
    text = text.replace(marker, ",\n    " + lean_style(vector) + marker, 1)
    p.write_text(text)


if __name__ == "__main__":
    if len(sys.argv) != 2:
        raise SystemExit("usage: augment-session-state.py vectors/persistence/session-state.json")
    main(sys.argv[1])
