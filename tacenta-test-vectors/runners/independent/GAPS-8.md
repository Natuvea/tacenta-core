# Independent reader: pass 8 record

**Date:** 2026-09-16
**Source revision:** `21a0c6c` before this evidence-remediation change.

This is a new pass record. It does **not** amend `GAPS-7.md`: that file is the
historical output of pass 7 and is restored here to the exact blob committed by
`159e9a2`.

## Purpose

Four gaps which were open at the end of pass 7 were later marked `CLOSED` by
editing the pass-7 record. Their underlying specification and vector changes
are real, but a historical pass must not acquire conclusions it did not make.
This pass reruns the independent reader against the current specification and
vectors, then records those four conclusions here.

## Run

From the repository root, the following command exited zero:

```text
python3 tacenta-test-vectors/runners/independent/reader/run.py
```

Its final tally was **644 PASS, 0 FAIL, 0 SKIP**: 424 vector checks and 220
derived cases. This run reuses the existing independent reader; no claim of a
new clean-room implementation is made by this maintenance pass.

## Re-assessed gaps

| Gap | Pass 7 status | Pass 8 status | Current evidence |
|---|---|---|---|
| G4-01 — standalone composite-header trailing bytes | STILL OPEN | **CLOSED** | `message-format.md` now requires a standalone decoder to accept exactly 102 bytes, and `malformed-input/composite-header-decode.json` contains `trailing-byte`; the reader passed it. |
| G6-01 — ambiguous `sk` in persistence vectors | STILL OPEN | **CLOSED** | `tacenta-test-vectors/README.md` distinguishes the ratchets' split root secrets from the Triple Ratchet's unsplit shared secret. |
| G6-03 — Braid operation output read-back | STILL OPEN | **CLOSED** | `tacenta-test-vectors/README.md` now requires runners to read operation output back and write identical bytes; the reader's Braid cases passed. |
| G6-05 — absent Braid codeword padding | STILL OPEN | **CLOSED** | `tacenta-test-vectors/README.md` now defines all-zero index and chunk padding for an absent codeword; reader checks passed. |

The pass-7 summary of the earlier gaps was 3 closed, 11 open and 1 narrowed.
With these four separately evidenced closures, pass 8 records **7 closed, 7
open and 1 narrowed**. This is a conclusion of pass 8 only.

## Scope and limit

The command above proves that this repository's current independent reader and
committed vectors agree. It does not independently review the wording of the
four new specifications, prove the protocol, or turn the prior change to
`GAPS-7.md` into an acceptable historical record. Those limits remain visible
rather than being inferred away.
