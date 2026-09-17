# Independent reader: pass 10 record

**Date:** 2026-09-17
**Implementation revision:** `b4fdeff`

This is a maintenance run record. It does not alter the historical reports
`GAPS.md` through `GAPS-9.md`, change the independent reader, or claim a new
clean-room implementation or independent reviewer.

## Purpose

Hostile-lens finding IMP-01 identified that no vector pinned a real handshake
or session at byte level. Commit `b4fdeff` adds
`vectors/session-establishment/session-e2e.json`, which drives real X25519 and
ML-KEM-1024 from prekey creation through the first authenticated message and
responder establishment. The Rust runner checks a public lifecycle path against
a reconstruction through public leaf components and then compares all named
intermediates and resulting state with the committed known answer.

## Run

From the repository root, after `b4fdeff`, this command exited zero:

```text
python3 tacenta-test-vectors/runners/independent/reader/run.py
```

The final tally was **646 PASS, 0 FAIL, 1 SKIP**: 426 passing vector checks,
one skipped vector and 220 passing derived cases. The skip is
`session-establishment/session-e2e.json`, reported as algorithm
`session-establishment-e2e` not implemented.

## Why the skip is evidence rather than a concealed pass

The reader's recorded boundary says it does not implement ML-KEM-1024 or the
end-to-end `Session`; its Braid work uses a documented KEM test double. Adding
a handler after consulting the Rust implementation would weaken the reader's
independence. The existing runner therefore says exactly what it did not check,
while continuing to fail CI on any case it does check and disagrees with.

The Rust evidence for the new case is separate:

- the complete lifecycle and component reconstruction produce identical
  initial-message bytes;
- the committed vector pins the handshake intermediates, wire bytes, first
  message keys, authenticated plaintext, consumed prekey store and both session
  states;
- `session_end_to_end_control_rejects_wrong_associated_data` changes one
  expected field and requires the vector runner to fail on it;
- the vector schema gate requires the file to name an algorithm dispatched by
  the Rust runner.

## Conclusion and limit

The missing byte-level real-handshake vector is present and executable. Its
expected bytes are project-generated regression and composition evidence, not
an external oracle. This maintenance run confirms that the independent reader
does not silently convert its real-ML-KEM boundary into a pass; it does not
independently validate the new vector.
