#!/usr/bin/env python3
"""Write the seed corpus of the `frame_size_boundary` fuzz target and its manifest.

Each seed is a short description of a frame (`frame_size_entry.rs` gives the three modes). The seeds sit at,
one below and one above both bounds of the size rule (tacenta-spec/protocol/message-format.md, Message size),
fifteen and sixteen bytes either side (one AES block of padding), on the nested cases (declared KEM lengths 0,
1,567, 1,568 and 70,000, a genuine repeat re-wrapped around a ratchet message at and over the bound), on frames
with an unknown version or type byte, and on small malformed frames.

`frame_size_seeds.txt` names, for each seed, the branch the session's decrypt and responder establishment are
expected to take; `tacenta-core/tests/fuzz_frame_size_seeds.rs` runs every seed and checks both, and that every
branch is taken. Run from anywhere:

    python3 tacenta-core/fuzz/frame_size_seeds.py
"""

import pathlib
import struct

HERE = pathlib.Path(__file__).resolve().parent
CORPUS = HERE / "corpus" / "frame_size_boundary"
MANIFEST = HERE / "frame_size_seeds.txt"

FR = 1_048_710  # MAX_RATCHET_FRAME_LEN
FI = 1_050_362  # MAX_INITIAL_FRAME_LEN

RATCHET = bytes([0x01, 0x01])


def initial_prefix(k):
    """Version, type, identity and ephemeral (curve byte 05, 32 zero bytes), kem_ciphertext_len."""
    return bytes([0x01, 0x02]) + b"\x05" + bytes(32) + b"\x05" + bytes(32) + struct.pack(">I", k)


def expanded(length, prefix, fill=0):
    return b"\x01" + struct.pack(">I", length) + bytes([fill]) + prefix


def rewrapped(kem_len, inner_len):
    return b"\x02" + struct.pack(">I", kem_len) + struct.pack(">I", inner_len)


def raw(frame):
    return b"\x00" + frame


# (name, seed, session branch, responder branch)
SEEDS = [
    # The ratchet bound, on a frame that is not an initial frame.
    ("ratchet-at-the-bound", expanded(FR, RATCHET), "at-limit-to-decoder", "at-limit-to-decoder"),
    ("ratchet-one-below", expanded(FR - 1, RATCHET), "other", "within-bounds-malformed"),
    ("ratchet-one-over", expanded(FR + 1, RATCHET), "ratchet-too-long", "ratchet-too-long"),
    ("ratchet-15-below", expanded(FR - 15, RATCHET), "other", "within-bounds-malformed"),
    ("ratchet-16-below", expanded(FR - 16, RATCHET), "other", "within-bounds-malformed"),
    ("ratchet-15-over", expanded(FR + 15, RATCHET), "ratchet-too-long", "ratchet-too-long"),
    ("ratchet-16-over", expanded(FR + 16, RATCHET), "ratchet-too-long", "ratchet-too-long"),
    ("ratchet-at-the-outer-bound", expanded(FI, RATCHET), "ratchet-too-long", "ratchet-too-long"),
    ("ratchet-one-over-the-outer-bound", expanded(FI + 1, RATCHET), "outer-too-long", "outer-too-long"),
    # The outer bound, on an initial frame with the honest KEM length.
    ("initial-at-the-bound", expanded(FI, initial_prefix(1568)), "at-limit-to-decoder", "at-limit-to-decoder"),
    ("initial-one-below", expanded(FI - 1, initial_prefix(1568)), "other", "other"),
    ("initial-one-over", expanded(FI + 1, initial_prefix(1568)), "outer-too-long", "outer-too-long"),
    ("initial-15-below", expanded(FI - 15, initial_prefix(1568)), "other", "other"),
    ("initial-16-below", expanded(FI - 16, initial_prefix(1568)), "other", "other"),
    ("initial-15-over", expanded(FI + 15, initial_prefix(1568)), "outer-too-long", "outer-too-long"),
    ("initial-16-over", expanded(FI + 16, initial_prefix(1568)), "outer-too-long", "outer-too-long"),
    # The nested bound, through the frame's own declared KEM length.
    ("nested-kem-0-at-the-bound", expanded(84 + FR, initial_prefix(0)), "at-limit-to-decoder", "at-limit-to-decoder"),
    ("nested-kem-0-one-below", expanded(84 + FR - 1, initial_prefix(0)), "other", "other"),
    ("nested-kem-0-one-over", expanded(84 + FR + 1, initial_prefix(0)), "nested-too-long", "nested-too-long"),
    ("nested-kem-0-at-the-outer-bound", expanded(FI, initial_prefix(0)), "nested-too-long", "nested-too-long"),
    ("nested-kem-1567-at-the-outer-bound", expanded(FI, initial_prefix(1567)), "nested-too-long", "nested-too-long"),
    ("nested-kem-70000-at-the-outer-bound", expanded(FI, initial_prefix(70_000)), "at-limit-to-decoder", "at-limit-to-decoder"),
    ("nested-kem-70000-one-over", expanded(FI + 1, initial_prefix(70_000)), "outer-too-long", "outer-too-long"),
    # A genuine repeat re-wrapped: declared KEM length and inner ratchet message chosen by the attacker.
    ("rewrap-kem-0-inner-at-the-bound", rewrapped(0, FR), "at-limit-to-decoder", "at-limit-to-decoder"),
    ("rewrap-kem-0-inner-one-over", rewrapped(0, FR + 1), "nested-too-long", "nested-too-long"),
    ("rewrap-kem-1568-inner-at-the-bound", rewrapped(1568, FR), "at-limit-to-decoder", "at-limit-to-decoder"),
    ("rewrap-kem-1568-inner-one-over", rewrapped(1568, FR + 1), "outer-too-long", "outer-too-long"),
    ("rewrap-kem-70000-small-inner", rewrapped(70_000, 200), "other", "other"),
    # Unknown version or type bytes: not initial frames, held to the ratchet bound.
    ("unknown-version-one-over", expanded(FR + 1, bytes([0x02, 0x01])), "ratchet-too-long", "ratchet-too-long"),
    ("unknown-version-small", expanded(100, bytes([0x02, 0x01])), "within-bounds-malformed", "within-bounds-malformed"),
    ("unknown-type-at-the-bound", expanded(FR, bytes([0x01, 0x03])), "at-limit-to-decoder", "at-limit-to-decoder"),
    ("unknown-type-one-over", expanded(FR + 1, bytes([0x01, 0x03])), "ratchet-too-long", "ratchet-too-long"),
    # Small malformed frames, under every bound.
    ("empty-frame", expanded(0, b""), "within-bounds-malformed", "within-bounds-malformed"),
    ("initial-too-short-for-its-kem-length", expanded(71, initial_prefix(0)[:71]), "within-bounds-malformed", "within-bounds-malformed"),
    ("initial-kem-length-runs-past-the-end", expanded(2000, initial_prefix(0xFFFFFFFF)), "within-bounds-malformed", "within-bounds-malformed"),
    ("raw-short-ratchet-frame", raw(RATCHET + bytes(10)), "within-bounds-malformed", "within-bounds-malformed"),
]


def main():
    CORPUS.mkdir(parents=True, exist_ok=True)
    names = {name for name, *_ in SEEDS}
    for stale in CORPUS.iterdir():
        if stale.name not in names:
            stale.unlink()
    lines = ["# seed  session-branch  responder-branch (written by frame_size_seeds.py)"]
    for name, seed, session, responder in SEEDS:
        (CORPUS / name).write_bytes(seed)
        lines.append(f"{name} {session} {responder}")
    MANIFEST.write_text("\n".join(lines) + "\n")
    print(f"frame_size_seeds: wrote {len(SEEDS)} seeds and {MANIFEST.name}")


if __name__ == "__main__":
    main()
