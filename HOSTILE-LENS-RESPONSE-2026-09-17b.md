# Hostile-lens response — 2026-09-17b

This is an initial, evidence-led response to the eight hostile-lens reports.
It records verified reproductions and disposition, rather than treating an
unverified review assertion as a conclusion. It does not amend historical
reader records.

## Reproduced

- **IMP-02:** reproduced against the committed isolated reader with the supplied
  `poc_store_bound.py`. It printed `reader accepted; store 1999`. The
  discrepancy was recorded as blocking `HL-IMP-02` in `GAP-REGISTER.md`.
- **FM-01:** a temporary `set_option warn.sorry false` mutation was refused by
  `check-lean-constructs.sh`; the real tree passed after restoration.
- **SC-04:** the receipt collector depended on a skipped `sign-off` job on a
  push. Its condition now begins with `always()`.
- **SC-06:** the workflow checker previously enumerated workflow files only.
  It now scans composite actions, with passing and failing composite-action
  fixtures.

## Open work

| Finding family | Disposition | Next evidence needed |
| --- | --- | --- |
| FM-02 / FM-04 | Open proof scope | Per-headline theorem satisfiability witnesses and explicit success-path-only wording until refusal refinement exists. |
| FM-03 | Open correctness cleanup | Remove the unused perfect-correctness KEM hypothesis after the Lean proof set is rebuilt and pinned. |
| SC-05 / SC-08 / SC-09 | Open supply-chain evidence | Replace candidate-written receipt claims with an independently derived record; distinguish checksum from regeneration; pin the Lean toolchain artefact. |
| SC-01 / SC-02 / SC-03 | Open governance/process | Enforce protected `main`, record the historic exceptions, and require a named reviewer who is not the change author before claiming independent review. |
| F1 / F2 / F3 | Open fuzzing | Add accepted-bundle and responder-handshake seeds, plus assertions that fail when each guard is deleted. |
| IP-01 / IP-02 | Open provenance decision | Publish source/version and research evidence where it may safely be published, or remove/downgrade the black-box and “ours” claims. |
| HN-01 / HN-05 | Open claims correction | Align public “proven core” language with the named verified zone and remove unproved session encrypt/decrypt implications. |

## Remediated

- **IMP-01 / `HL-IMP-01`:** `b4fdeff` adds a deterministic byte-level vector
  for real X25519 and ML-KEM-1024 prekey creation, initiator establishment, the
  first encrypted message and responder establishment. It pins every named
  random draw, the handshake intermediates, wire messages, message keys,
  authenticated plaintext, consumed prekey store and both session states. The
  runner also reconstructs the initial message through the public leaf
  components and requires exact agreement with the public lifecycle. A negative
  control corrupts the expected associated data and requires the runner to
  fail. The expected bytes are project-generated regression/composition
  evidence, not an external oracle; independent-reader pass 10 records one
  explicit skip because that reader has no real ML-KEM implementation.
- **IMP-02 / `HL-IMP-02`:** `3e2745f` makes the model and Rust check
  `MAX_SKIPPED_STORE` against the store after replaceable pairs are removed.
  The Rust unit test and the byte-level
  `replacement-bound-counts-resulting-store` vector exercise the reported
  1,999-key boundary. The differential harness requires a generated sequence
  to reach it and observed model/Rust agreement across 2,864 operations. The
  regenerated Aeneas translation and T1/T3 proofs build, and independent-reader
  pass 9 records 646 PASS, 0 FAIL and 0 SKIP.

## Evidence language

The project uses automated and AI-assisted engineering tools. Project-controlled
reader runs, generated material, and automated review preparation are useful
reproducible evidence, but are not independent review. The README and
ASSURANCE.md now state this directly. Individual tool attribution is not used
as a substitute for accountable engineering review.
