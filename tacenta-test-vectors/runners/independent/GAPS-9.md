# Independent reader: pass 9 record

**Date:** 2026-09-17
**Implementation revision:** `3e2745f`

This is a new maintenance pass record. It does not alter the historical
reports `GAPS.md` through `GAPS-8.md`, and it does not claim a new clean-room
implementation or a new independent reviewer.

## Purpose

Hostile-lens finding IMP-02 identified a disagreement at the Double Ratchet's
skipped-key capacity bound. On a revisit to a ratchet key, `ratchet.md` deletes
held pairs in the re-derived range before storing their replacements. The
reader followed that order, while the model and Rust checked the old store
length first and could refuse a conforming operation near the capacity bound.

Commit `3e2745f` changes the model and Rust to check the exact resulting store.
It adds the byte-level vector `replacement-bound-counts-resulting-store`: a
1,999-key store already holds two pairs that the operation re-derives, so the
operation removes two, adds two, and remains at 1,999. A pre-replacement check
would refuse it.

## Run

From the repository root, after `3e2745f`, this command exited zero:

```text
python3 tacenta-test-vectors/runners/independent/reader/run.py
```

The final tally was **646 PASS, 0 FAIL, 0 SKIP**: 426 vector checks and 220
derived cases. The new operation vector and its read-back both passed.
`cases_ratchet.py` CR-09 also continued to pass its specification-derived rule
that the capacity bound counts the resulting store after replacement.

## Corroborating checks

The maintenance run is one part of the evidence, rather than a claim that the
reader reviewed the implementation:

- the Rust persistence runner passed all 237 fixtures, including 32 accepted
  and 32 refused Double Ratchet fixtures;
- the differential harness passed 2,864 generated operations and requires a
  classical sequence to reach the 1,999-key replacement boundary;
- the model/proof package built all 37 jobs;
- the pinned Aeneas translation was regenerated, and the translated T1/T3
  proof package built all 2,291 jobs without a new axiom or `sorry`.

## Conclusion and limit

The evidence required to close `HL-IMP-02` is present: the normative reading is
recorded, the model and Rust agree, a byte-level vector and a differential
sequence distinguish the old behavior, and the existing reader accepts the
result. This pass establishes agreement among those checked artifacts. It is
not an external audit and does not close IMP-01's separate real-handshake and
end-to-end session-vector gap.
