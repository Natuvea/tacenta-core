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
| FM-03 | Closed | `KemAgreesFor` no longer carries the `K.Correct` conjunct: neither Braid refinement proof used it, and it asked for a decapsulation guarantee that holds of ML-KEM-1024 only up to the FIPS 203 failure bound. `toyKem_correct` remains a fact about the toy model. |
| SC-05 / SC-08 / SC-09 | Open supply-chain evidence | Replace candidate-written receipt claims with an independently derived record; distinguish checksum from regeneration; pin the Lean toolchain artefact. |
| SC-01 / SC-02 / SC-03 | Open governance/process | Enforce protected `main`, record the historic exceptions, and require a named reviewer who is not the change author before claiming independent review. |
| F1 / F2 / F3 | Closed (`HL-FUZZ-01`) | The `wire_decoders` corpus carries a 1,811-byte canonical bundle that reaches `decode_bundle` acceptance, pinned by a normal decode/re-encode test; `session_receive` overlays fuzz bytes onto a genuine initial message and its zero-mutation seed must complete an accepted responder handshake; the ratchet and sparse-ratchet decoder tests start from valid encodings, overwrite the count fields and require `Malformed`, and each fails when its bound is disabled. |
| IP-01 / IP-02 | Open provenance decision | Publish source/version and research evidence where it may safely be published, or remove/downgrade the black-box and “ours” claims. |
| HN-01 / HN-05 | Open claims correction | Align public “proven core” language with the named verified zone and remove unproved session encrypt/decrypt implications. |
| IMP-01 / `HL-IMP-01` | Open independent replay | The real-session vector is implemented, but closure still requires the independent reader to replay the exact candidate and record its limits. The current allowlist only prevents silent skip drift. |

## Implemented changes, with limits

- **IMP-01 implementation (not gap closure) / `HL-IMP-01`:** `44409c6` adds a deterministic byte-level vector
  for real X25519 and ML-KEM-1024 prekey creation, initiator establishment, the
  first encrypted message and responder establishment. It pins every named
  random draw, the handshake intermediates, wire messages, message keys,
  authenticated plaintext, consumed prekey store and both session states. The
  runner also reconstructs the initial message through the public leaf
  components and requires exact agreement with the public lifecycle. A negative
  control corrupts the expected associated data and requires the runner to
  fail. The expected bytes are project-generated regression/composition
  evidence, not an external oracle. Independent-reader pass 10 records one
  explicit skip because that reader has no real ML-KEM implementation, so the
  gap remains open until the reader replays it. The checked skip allowlist
  prevents silent drift but cannot satisfy that replay requirement.
- **IMP-02 / `HL-IMP-02`:** `3e2745f` makes the model and Rust check
  `MAX_SKIPPED_STORE` against the store after replaceable pairs are removed.
  The Rust unit test and the byte-level
  `replacement-bound-counts-resulting-store` vector exercise the reported
  1,999-key boundary. The differential harness requires a generated sequence
  to reach it and observed model/Rust agreement across 2,864 operations. The
  regenerated Aeneas translation and T1/T3 proofs build, and independent-reader
  pass 9 records 646 PASS, 0 FAIL and 0 SKIP.

- **Sparse follow-up / `HL-R1-SPARSE-TRANSLATION`:** no closure is claimed in
  this response. The sparse replacement-bound change was removed from the
  current pull request because its proof and translation were not ready to
  support the implementation. The current differential does not reach the
  replacement-only stored-state edge, no test pins the lower purge endpoint,
  and the translation checksum cannot establish that Aeneas actually ran.
  These remain open blocking evidence items for a separate verified-zone
  change.

- **Reader skip control:** `run.py` now keeps an exact allowlist for the one
  documented real-ML-KEM/session skip and exits non-zero if a skip is added,
  removed or moved. A three-case control test exercises unexpected and missing
  skips. This prevents silent drift but does not turn the skipped vector into
  an independent replay.

- **Translation checksum limit:** `attest.py --check-translation` now also
  checks that each recorded source hash matches the committed tree named by
  `generated_at_commit` (or the recorded leaf trees for assembled units). The
  negative suite covers a mismatched committed-source hash. This catches a
  hand-edited hash or a refresh on an uncommitted tree, but a checksum is still
  not a public regeneration proof.

## Evidence language

The project uses automated and AI-assisted engineering tools. Project-controlled
reader runs, generated material, and automated review preparation are useful
reproducible evidence, but are not independent review. The README and
ASSURANCE.md now state this directly. Individual tool attribution is not used
as a substitute for accountable engineering review.
