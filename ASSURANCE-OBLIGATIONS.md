# Assurance obligation inventory

Current inventory for P1 of the assurance execution plan. This file makes the
remaining readiness work assessable; it is not evidence that the work is done.

Last assessed: 2026-09-14, at `c7499a9b6fedb9d211198671848c1e3acbe592af`.

## Gate classes

- **BLOCKING:** must close, or be changed by a recorded decision, before the
  second external proof-ledger engagement.
- **AMBIGUOUS:** must become closed, BLOCKING, NONBLOCKING or a recorded
  decision before gate 2 can be said to pass.
- **NONBLOCKING:** disclosed work that does not block the second engagement at
  the current recorded target.
- **DEFERRED:** outside the current completion scope only if a recorded decision
  states the target effect and revisit trigger.
- **CLOSED:** resolved in current evidence.

An open row without one of these classes is itself a gate-2 failure because the
gate cannot be assessed from prose.

## Package map

| Package | Scope | Current readiness role |
| --- | --- | --- |
| P1 | Gap classification and obligation inventory | This file and `GAP-REGISTER.md` classify known work and name the inventory still needed. |
| P2 | Requirement evidence index | BLOCKING for traceability practice 8 and gate 4's "does not report green when it cannot run" claim. |
| P3 | Contract decisions before fixture generation | BLOCKING for current ambiguity in refusal, vector and public-decoder contracts. |
| P4 | Persistence coverage fixtures | Closed for the tracked prekey-store/session fixture gaps; keep future fixture gaps in this package if P5/P7 exposes them. |
| P5 | Stored-format differential checks | BLOCKING for differential-testing phase 3 once P4 baselines and P3 decisions exist. |
| P6 | Session/prekey operation model and L2 evidence | CLOSED at the recorded bounded L2 target. Reopened for planning by the Session L4 decision records (`tacenta-model/SESSION-L4-*-DECISION.md`); the Phase 0 carve-out translates the lifecycle without changing the level, and SL4-01 below carries its exit conditions. |
| P7 | Remaining proof/vector target obligations | BLOCKING where a component remains below its target; discovery starts before P4/P5 complete. |
| P8 | Validated types and explicit phases | NONBLOCKING unless P1/P6 identifies a target deficit that requires it. |
| P9 | Reproducible gate evidence and final review pack | [P9-GATE-EVIDENCE.md](tacenta-proofs/P9-GATE-EVIDENCE.md) records the candidate-capture procedure, open gate status, mutation inventory and final independent-review record. It remains BLOCKING until that pack is populated at a final candidate. |

## Mop-up execution inventory

This is the reconciled implementation inventory for the current six-item
mop-up sequence. It records work still required at the assessed revision; it
does not turn a planned result, local run or author assertion into gate
evidence. `MU-*` identifiers are stable work-obligation identifiers rather
than security requirements.

| ID | Classification | Owner role | Target effect | Current evidence and remaining work | Revisit or completion trigger |
| --- | --- | --- | --- | --- | --- |
| MU-01 | CLOSED | Core/spec maintainer | Session/prekey orchestration can meet its recorded L2 target only for operations an isolated, specification-only reader can interpret. | The committed 27-trace corpus, allowlisted v4 packet, Jie Sun's isolated reader, clean-room record and five passing controls are recorded in `tacenta-test-vectors/runners/independent/P6-OPERATION-READER-EVIDENCE.md`. [The L2 target decision](tacenta-model/P6-L2-TARGET-DECISION.md) records the covered families, declared-crypto boundary and reopen triggers. | Reopen on any trigger in the recorded decision. |
| MU-02 | BLOCKING | Ledger reviewer | Gate 3 has an independent, claim-by-claim receipt for one frozen candidate and evidence pack. | `P9-GATE-EVIDENCE.md` now defines the receipt content, `check-ledger-review-receipt.py` validates its required provenance fields, and `validate-reviewed-evidence.py` binds it to the clean manifest and verified pack. No selected candidate, independent reviewer identity or claim dispositions exist. | Freeze a clean candidate after the other blocking work, retain its required check receipts and obtain the separate review receipt. |
| MU-03 | BLOCKING | Core/spec maintainer | Gates 1 and 2 are assessable against a complete obligation catalogue and explicit boundary-headroom disposition. | The version-2 catalogue now has checked `INV-*` records, and [the headroom target decision](tacenta-proofs/PROOF-BOUNDARY-HEADROOM-TARGET-DECISION.md) states its effect and reopen triggers. [The semantic-review brief](tacenta-spec/security-properties/INVARIANT-SEMANTIC-REVIEW-BRIEF.md) fixes the review questions and return record. Practice 5 remains BLOCKING until an independent reviewer evaluates the predicates and cited coverage. | Record the semantic review and reassess all component and gap rows against its findings. |
| MU-04 | BLOCKING | Evidence/CI implementer | CI emits an honest, versioned inventory of the selected candidate's required checks and evidence. | Receipt writers now run in each CI job; the aggregation job downloads them only after all required jobs succeed, applies push/PR conditional sign-off rules, then builds and validates a versioned manifest. Local refusal controls cover missing, skipped, falsely inapplicable, foreign-candidate, mismatched-event, duplicate and missing conditional receipts. A retained hosted candidate artifact has not yet been verified. | Run and retain the aggregation for a clean selected candidate, verify its hosted artifact and record any hosted-only control results. |
| MU-05 | BLOCKING | Release operator | The reviewed evidence is packaged, retained and externally reproducible without private inputs. | `tooling/build-evidence-pack.py` now builds/verifies a digest inventory over an allowlisted public evidence set and refuses a manifest the production validator rejects. The verifier refuses altered or escaping entries; the complete production flow and the final manifest/pack/review-receipt binding passed in disposable clean candidates. The configured private S3 Object Lock archive has seven-year Compliance retention and its delete-refusal initialization control passed. No hosted candidate artifact, review receipt or candidate publication exists yet. | Run/verify the pack on the selected clean candidate, retain its Object-Lock metadata, publish the immutable GitHub release assets, then fresh-download-verify only the reviewed candidate. |
| MU-06 | CLOSED | Model/test implementer | The L2 operation evidence includes one bounded, composed establish-to-restore lifecycle property. | `Model.SessionTrace` and `Proofs.SessionTrace` state and prove the bounded refusal/restore, replay and terminal-failure observations under the documented abstract crypto and committed-snapshot assumptions. `tacenta-core/tests/session_lifecycle_property.rs` supplies a deterministic fresh-object establishment, restore, skipped-message recovery, replay and forged-message concrete witness. | Reopen when the bounded trace contract, its assumptions, or its concrete operation surface changes. |
| SL4-01 | BLOCKING for the Session L4 programme, NONBLOCKING for the current L2 target | Core maintainer | The Phase 0 carve-out is complete on its own terms before Phase 1 work merges. | Done: shipping lifecycle in `tacenta-core/lifecycle`, primitives in `tacenta-core/boundary`, facade pinned by `tests/public_api_compat.rs`, `TacentaLifecycle.lean` generated from committed source with a coverage gate and a boundary-surface gate, attestations current. Open: the product pin is still at a pre-carve-out commit and its legacy-v1 store fixture fails against this base and against the carve-out alike (a stale product expectation, not a regression); the Windows runner has not built the carve-out; no hosted Linux regeneration of `TacentaLifecycle.lean` exists (a local regeneration with the pinned binaries is byte-identical); `tacenta_core::serialization` is duplicated inside the lifecycle crate and nothing pins the two copies together; the coverage gate inventories only the thirty `Identity`/`PrekeyStore`/`Session` and `establish_*` operations, not the thirteen further public functions the leaf translates. Since #161: the eight-leaf session unit is assembled and translated from committed source (byte-identical regeneration), with conditional T1 theorems for the five roots and conditional T3 branch lemmas (register rows E2E-01, E2E-03, E2E-04); the session-unit assembly and port checks run in the hosted `checks` job. | Product pin bumped with its fixture corrected and Windows green; the duplicate serialization module removed or pinned; the coverage inventory widened or its scope recorded; then close. |

## Component obligations

| Component or gate | Current target deficit | Gate class | Package | Closure evidence |
| --- | --- | --- | --- | --- |
| Sparse post-quantum ratchet | `P7-SPARSE-BRAID-INVENTORY.md` records the selected fixed-vector surface: initial states, epoch and chain-counter ceilings, the accepted retirement trace, and the retired-epoch `NoChain` refusal. `retired-epoch-no-chain-refused` requires both runners to reject the canonical post-retirement state with `no-chain`. Generated differential and the clean-room reader cover the remaining operation combinations and durable no-op effect. | CLOSED | P7 | Reassess the fixed-vector decision if a new externally observable sparse operation or refusal is specified. |
| ML-KEM Braid | `P7-SPARSE-BRAID-INVENTORY.md` separates stored-state coverage for tags 0 and 5--11 and `Ct2Sampled` boundaries from the delegated valid key-pair layout for tags 1--4. The differential harness drives an empty `NoHeaderReceived` state through transition (6) with a persisted-key header MAC and mutation control, drives transition (5)'s real ciphertext MAC control, and uses five deterministic real-ML-KEM schedules to exercise all thirteen state-machine transitions. The clean-room reader independently checks the abstract transition table with its specified KEM double. | CLOSED | P7 | Revisit if a portable KEM-state encoding, an independent producer for the delegated layout, or a new Braid transition/failure observable is introduced. |
| Erasure code | [ERASURE-CODEC-TARGET-DECISION.md](tacenta-proofs/ERASURE-CODEC-TARGET-DECISION.md) records L3 as the current engagement target. Field arithmetic, codec T1, vectors, the independent reader and live-path tests remain the evidence. `ERASURE-DECODER-REFINEMENT.md` records the distinct L4 programme: a concrete codec relation, barycentric equivalence, decoder/encoder preservation and a port to the Braid-and-erasure unit. | CLOSED | P7 | Reopen L4 before a full-codec refinement claim or on any trigger in the recorded decision. |
| Session orchestration and prekey store | [P6-L2-TARGET-DECISION.md](tacenta-model/P6-L2-TARGET-DECISION.md) records the bounded model/concrete/independent-reader surface, its declared-crypto boundary and reopen triggers. | CLOSED | P6 | Reopen before changing a covered operation or refusal, raising L2, or treating a reader-declared crypto fact as a computed result. |
| Persisted formats: prekey store | The shared structural stored-format domain is now driven by the differential harness over the committed P4 fixtures; stored signatures and KEM-pair arithmetic are exact exclusions pinned by vectors and crate tests. | CLOSED | P5 | Keep the prekey differential fixture set current if new shared-domain branches are added. |
| Persisted formats: session | The shared structural stored-format domain is now driven by the differential harness over the committed P4 fixtures; the ratchet private/public relation is an exact exclusion pinned by vectors and crate tests. | CLOSED | P5 | Keep the session differential fixture set current if new shared-domain branches are added. |
| Practice 5: invariants catalogue | The version-2 evidence index now carries scoped `INV-*` records linked to requirements, operations, explicit headroom and selected evidence. [The headroom decision](tacenta-proofs/PROOF-BOUNDARY-HEADROOM-TARGET-DECISION.md) records the target scope and reopen triggers, and [the review brief](tacenta-spec/security-properties/INVARIANT-SEMANTIC-REVIEW-BRIEF.md) fixes the independent semantic assessment. | BLOCKING | MU-03 | Record the semantic review; structural index validity and the scope decision alone do not close the practice. |
| Practice 8: evidence traceability | Structural ID spine is checked; proof/vector/test evidence links are checked for all 32 security-property requirements, and the gate now fails when any requirement is missing from the evidence index. | CLOSED | P2 | Keep the evidence index current when requirements, proofs, vectors or tests change. |
| Practice 9: differential testing | The prekey store's and session's shared structural stored-format domains are now driven through both sides. Braid covers stored tags, `Ct2Sampled` boundaries, authenticated-header and ciphertext-MAC controls, and every state-machine transition under seeded real-ML-KEM schedules; its delegated persisted key-pair content rule has no universal vector verdict. | CLOSED | P7 | Revisit the narrow delegated-layout decision with any portable encoding, independent producer, or new Braid observable. |
| Gate 1 | Every component must meet target or have a recorded target decision. Several rows above do not. | BLOCKING | P1/P7/P6 | Component obligation matrix closed or amended by recorded decisions. |
| Gate 2 | Gap register must have no open BLOCKING rows and no unresolved AMBIGUOUS rows. | BLOCKING | P1/P3/P6/P7 | `GAP-REGISTER.md` rows classified and closed/decided as required. |
| Gate 3 | Claims ledger must receive a final independent claim-by-claim review after its last change. | BLOCKING | P9 | [P9-GATE-EVIDENCE.md](tacenta-proofs/P9-GATE-EVIDENCE.md) names the required review record; it still needs a reviewer, frozen revision, artifacts read and findings/disposition. |
| Gate 4 | Every gate must have negative-control evidence and must fail when required inputs are absent. | BLOCKING | P9/P2/P7 | [P9-GATE-EVIDENCE.md](tacenta-proofs/P9-GATE-EVIDENCE.md) distinguishes the existing controls from missing records and cases; all need command/environment, deliberate fault and diagnostic at the final candidate. |

## Deferral decisions still needed

The current register has deferred rows, but a deferral only satisfies readiness
if it states the effect on the target and a revisit trigger. These still need a
recorded decision or a target-closing slice:

| Item | Current risk | Package |
| --- | --- | --- |
| Boundary headroom | [Recorded target decision](tacenta-proofs/PROOF-BOUNDARY-HEADROOM-TARGET-DECISION.md) keeps successor-headroom as an explicit success-refinement scope and names reopening triggers. | P7 |
| Erasure codec refinement | [Recorded L3 target decision](tacenta-proofs/ERASURE-CODEC-TARGET-DECISION.md) keeps the L4 programme deferred and disclosed. | P7 |

## Gate evidence inventory

| Gate/check | Protected property | Current negative-control evidence | Missing evidence |
| --- | --- | --- | --- |
| `tooling/check-traceability.py` | Requirement/status/assumption/reference spine does not drift. | `tooling/tests/run-check-traceability-cases.sh` runs a passing baseline and 19 refusal cases: status-table removal/title/class drift, missing requirement status/`Rests on`, both direct assumption-inverse faults, unknown `LIM`/`ADV`/`AS`/`EX` references, and evidence-index faults. | Retain its command, environment and diagnostic-free candidate result. |
| `tooling/check-workflows.sh` | Workflow files parse and obey repository security rules. | 62 case files under `tooling/tests/check-workflows-cases`. | None identified in this P1 pass. |
| `tooling/check-precondition-shapes.py` | Listed vacuous numeric precondition shapes do not enter first-party Lean. | 71 case directories under `tooling/tests/check-precondition-shapes-cases`. | None identified in this P1 pass. |
| `tooling/check-labels.sh` | Derivation labels stay registered and prefix-free except recorded pairs. | `tooling/tests/run-check-labels-cases.sh` runs a passing baseline plus unregistered-label and forbidden-prefix refusals against the production checker. | Retain its command, environment and diagnostic-free candidate result. |
| `tooling/check-vectors.py` | Vector files obey schemas. | `tooling/tests/run-check-vectors-cases.sh` runs a valid baseline, unexpected-field schema refusal, duplicate-ID refusal and unsupported-schema-keyword refusal against the production checker. | Retain its command, environment and diagnostic-free candidate result. |
| Independent reader | Specification-only reader can interpret and check committed vectors. | Reader derived cases exercise many refusals; historical GAPS reports record findings. | Mutation record showing a representative missing/incorrect vector rule fails the reader. |
| Claims/attestation | Claims and generated artifacts match checked Lean/source state. | `check-audit-negatives.sh` holds the audit to its accepted compiler-trust orphan and 11 named refusal classes. `check-attest-negatives.sh` runs four isolated production-attestation refusals for a missing theorem, missing manifest, stale source attestation and changed generated translation. | Retain their command, environment and diagnostic-free candidate result. |
| Full CI | Public/local required checks run and fail rather than skip when required. | `tooling/ci.sh` and GitHub workflow share most gates; workflow now invokes traceability. | P9 must record environments and missing-tool behavior for each required/optional gate. |

## Next P1 slices

1. Decide whether `GAP-REGISTER.md` should remain Markdown-only or gain a
   machine-readable sidecar before P2 indexes evidence against gap IDs.
2. Add target/scope decision records for any deferred item that is intended not
   to block gate 1.
