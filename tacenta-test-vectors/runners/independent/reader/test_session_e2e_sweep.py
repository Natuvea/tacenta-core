# PROJECT-CONTROLLED DRY RUN. NOT INDEPENDENT EVIDENCE. It does not close or reclassify the open item.
#!/usr/bin/env python3
"""PROJECT-CONTROLLED DRY RUN. NOT INDEPENDENT EVIDENCE. It does not close or reclassify the open item.

Corrupt the real-primitive session vectors byte by byte and hold the reader
to what `session_e2e.py` says it checks.

For each vector, each input and each field, this changes single bytes (the
first, the second, the last, the middle and four more spread through the value,
and the bytes either side of every documented boundary) and runs the derivation
on the result. The reader must notice every one of them, with three exceptions
that `session_e2e.py` and `reader/README.md` list as not checked:

- the inputs in `session_e2e.UNREAD_INPUTS`, which the reader never reads, so
  that changing one must not change its verdict;
- the byte ranges in `session_e2e.UNREAD_INPUT_RANGES`: the `z` half of the
  Braid's key-generation draw and of the one-time KEM draw, which no output
  shows;
- the bytes of the Braid's stored key pair inside `alice_session_after_first_send`
  (its layout is delegated to the KEM library).

The last-resort KEM key pair inside `bob_prekey_store_after_receipt` was in this
list before the dry run: its decapsulation key's first 1,536 bytes (`dk_pke`) and
its last 32 (`z`) were not reached by any check. They are computed now, from
`bob_last_resort_kem_d_z`, so every byte of the stored pair is noticed.

So "checked" and "not checked" are each demonstrated, not asserted: a byte the
README calls checked that survives corruption fails this test, and so does a byte
it calls unchecked that the reader turns out to notice.

    python3 test_session_e2e_sweep.py
"""

import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

import session_e2e  # noqa: E402
from tacenta_reader import persistence  # noqa: E402

VECTORS = os.path.join(HERE, "..", "..", "..", "vectors", "session-establishment", "session-e2e.json")
MASK = 0x10      # clear of the bits an X25519 secret's clamping discards


def positions(length, extra=()):
    spread = [length * k // 9 for k in range(1, 9, 2)]
    return sorted({p for p in [0, 1, length // 2, length - 1] + spread + list(extra)
                   if 0 <= p < length})


def flipped(hex_string, at):
    raw = bytearray(bytes.fromhex(hex_string))
    raw[at] ^= MASK
    return raw.hex()


def detects(vector):
    try:
        session_e2e.check(vector)
    except Exception:  # noqa: BLE001  any refusal is the reader noticing
        return True
    return False


def unchecked_ranges(vector):
    """{field: [(start, end)]} of the bytes the reader is documented not to
    check, found in the vector's own persisted bytes."""
    f = vector["fields"]
    out = {}
    session = bytes.fromhex(f["alice_session_after_first_send"])
    key_pair = persistence.session_from_bytes(session).braid.fields["key_pair"]
    start = session.find(bytes(key_pair))
    assert start >= 0 and session.count(bytes(key_pair)) == 1
    out["alice_session_after_first_send"] = [(start, start + len(key_pair))]
    return out


def formerly_unchecked(vector):
    """{field: [positions]} inside the last-resort key pair of the responder's
    stored prekey store, the bytes that were documented as not checked before
    the pair was computed from `bob_last_resort_kem_d_z`: the start, middle and
    end of `dk_pke` and of `z`. Each must now be noticed."""
    store = bytes.fromhex(vector["fields"]["bob_prekey_store_after_receipt"])
    kem_pair = persistence.prekey_store_from_bytes(store).kem_pair
    start = store.find(bytes(kem_pair))
    assert start >= 0 and store.count(bytes(kem_pair)) == 1
    dk_pke, z_start, dk_len = 1536, 3168 - 32, 3168
    spots = [start, start + dk_pke // 2, start + dk_pke - 1, start + z_start,
             start + z_start + 16, start + dk_len - 1]
    return {"bob_prekey_store_after_receipt": spots}


def main():
    document = json.load(open(VECTORS))
    failures = []
    checked = unchecked = 0
    for vector in document["vectors"]:
        vid = vector["id"]
        assert not detects_nothing_baseline(vector), vid
        ranges = unchecked_ranges(vector)
        must_notice = formerly_unchecked(vector)
        for group in ("inputs", "fields"):
            for name, value in vector[group].items():
                length = len(value) // 2
                extra = []
                spans = (ranges.get(name, []) if group == "fields"
                         else session_e2e.UNREAD_INPUT_RANGES.get(name, []))
                for lo, hi in spans:
                    extra += [lo - 1, lo, (lo + hi) // 2, hi - 1, hi]
                if group == "fields":
                    extra += must_notice.get(name, [])
                for at in positions(length, extra):
                    mutated = json.loads(json.dumps(vector))
                    mutated[group][name] = flipped(value, at)
                    noticed = detects(mutated)
                    documented_unchecked = (
                        (group == "inputs" and (
                            name in session_e2e.UNREAD_INPUTS
                            or any(lo <= at < hi for lo, hi in spans)))
                        or (group == "fields" and any(lo <= at < hi for lo, hi in spans)))
                    if documented_unchecked:
                        unchecked += 1
                        if noticed:
                            failures.append(f"{vid}: {group}.{name}[{at}] is documented as not "
                                            "checked, yet corrupting it was noticed")
                    else:
                        checked += 1
                        if not noticed:
                            failures.append(f"{vid}: {group}.{name}[{at}] is documented as "
                                            "checked, yet corrupting it was not noticed")
    for line in failures:
        print("FAIL", line)
    if failures:
        print(f"{len(failures)} failure(s)")
        return 1
    print(f"session-e2e sweep: {checked} corrupted bytes noticed, {unchecked} corrupted bytes in "
          "documented unchecked regions or unread inputs not noticed, as documented")
    return 0


def detects_nothing_baseline(vector):
    """The unmodified vector passes (returns True on a failure)."""
    try:
        session_e2e.check(vector)
    except Exception:  # noqa: BLE001
        return True
    return False


if __name__ == "__main__":
    sys.exit(main())
