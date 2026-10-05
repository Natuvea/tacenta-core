# P6 session/prekey L2 target decision

## Decision

The session-orchestration and prekey-store component meets its recorded **L2**
target for the bounded operation surface in `SESSION-OPERATION-MODEL.md`.
This decision is based on the model and lifecycle theorem, concrete operation
checks, the committed 27-trace corpus, and Jie Sun's independently authored
v4 specification-only reader and controls.

The decision raises the component's current level from L1 to L2. It does not
claim translation, a full Rust-to-model refinement, or a cryptographic proof.

## Covered L2 surface

The evidence covers prekey creation, publication, replenishment and rotation;
initiator and responder establishment; one-time and last-resort replay
refusals; ordinary and repeated-initial receive; reordered delivery and
skipped-key recovery; export/restore continuation; terminal Braid failure and
later refusal; and malformed, signature and non-contributory-DH establishment
refusals. The clean-room reader has one or more source-linked passing traces
for each of the nine required families and five controls that fail with
source-cited diagnostics.

Its cryptographic predicates are declared fixture facts. The reader checks the
specified observable effects those facts imply; it does not verify signatures,
DH, AEAD, or Braid MACs itself. Concrete tests and the differential harness
remain the evidence for those real cryptographic paths.

## Target effect and revisit triggers

The P6 component and MU-01 are closed at L2. The result leaves the stated
untranslated and bounded exclusions in place, and does not change any public
security claim or the separate P9 ledger-review requirement.

## Reassessment at the proven-core candidate

On 2026-10-05, candidate `e7968dc4` was reassessed against the two triggers
recorded in the original decision. The `legacy_blocked` rules are now present
in the model, vectors, differential checks and reader evidence. The identity-
key refusals are likewise present in the model, vectors, concrete checks and
the current reader path. They remain explicit refusal and contract-boundary
evidence; they are not a computational cryptographic verdict and they do not
extend the covered lifecycle composition claim.

The triggers are therefore answered without raising the target: the bounded
L2 decision remains closed, while the operation corpus and reader evidence are
kept current for the changed rules. The reader's current ML-KEM/session pass
is project-controlled evidence and is not an independent review or a reason
to close `HL-IMP-01-READER`, the session-orchestration composition gap, or the
P9 ledger obligation.

Reopen this decision before raising the target above L2, adding an observable
operation/refusal to the session or prekey surface, changing a covered
persistence or failure effect, or relying on a cryptographic verdict as if the
independent reader had computed it. The reopening work must update the
operation contract, source-linked corpus, clean-room reader evidence and
concrete/model checks for the changed surface.
