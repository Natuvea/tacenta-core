# Assurance obligation inventory

Current inventory for P1 of the assurance execution plan. This file makes the
remaining readiness work assessable; it is not evidence that the work is done.

Last assessed: 2026-09-30, at `dea57eaff4e516b6f56df08f7ced44d0ee87d024`, for the gate evidence inventory and the rows that cite it. The rest of this file was last assessed on 2026-09-14, at `c7499a9b6fedb9d211198671848c1e3acbe592af`. The Gate 2 row was re-read on 2026-09-30 against `GAP-REGISTER.md` after `SESSION-CONTRACT-VACUITY` was added, and again on 2026-10-01 after `DISPATCH-EVIDENCE-VACUITY` was added. On 2026-10-22, for identity records (ADR-0009), the Gate 2 row was re-read against `GAP-REGISTER.md` after reader pass 14, and the requirement count of the practice 8 row, the revisit triggers of the MU-01 and Session rows and the zones of the authentication-boundary row were updated, by their author with tool assistance and no independent reader.

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
| P2 | Requirement evidence index | Closed for traceability practice 8. Still BLOCKING for gate 4's "does not report green when it cannot run" claim: `tooling/check-workflows.sh`, `tooling/check-constant-time-asm.sh` and the differential harness have no case for their skip-or-fail rule (the gate evidence inventory below). |
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

<!-- One item per table row, one sentence or clause per line: tooling/reflow-shared-lists.py. -->

- **ID:**
  MU-01

  **Classification:**
  AMBIGUOUS

  **Owner role:**
  Core/spec maintainer

  **Target effect:**
  Session/prekey orchestration can meet its recorded L2 target only for operations an isolated, specification-only reader can interpret.

  **Current evidence and remaining work:**
  The committed 27-trace corpus, allowlisted v4 packet, Jie Sun's isolated reader, clean-room record and five passing controls are recorded in `tacenta-test-vectors/runners/independent/P6-OPERATION-READER-EVIDENCE.md`. [The L2 target decision](tacenta-model/P6-L2-TARGET-DECISION.md) records the covered families, declared-crypto boundary and reopen triggers.

  **Revisit or completion trigger:**
  Reopen on any trigger in the recorded decision.
  Three revisit triggers have fired since (the `legacy_blocked` rules, #202, the identity-key refusals, #205, and initiator establishment under an expectation, ADR-0009);
  the decision has not been reopened (`ASSURANCE.md`, practice 4).

- **ID:**
  MU-02

  **Classification:**
  BLOCKING

  **Owner role:**
  Ledger reviewer

  **Target effect:**
  Gate 3 has an independent, section-by-section receipt for one frozen candidate and evidence pack.

  **Current evidence and remaining work:**
  `P9-GATE-EVIDENCE.md` defines the receipt content.
  `check-ledger-review-receipt.py` (receipt schema 2) validates it:
  the pack binding, the artifacts named, one disposition for every section of the pack's `CLAIMS.md` and for its introduction, each given on the SHA-256 of the section text, and finding text wherever a limit or finding is recorded.
  `ledger-review-sections.py` writes the template and reports which sections changed since an earlier pack, receipt or `CLAIMS.md`.
  `validate-reviewed-evidence.py` binds a receipt with no finding, the pack (checked against git) and the manifest.
  `tooling/tests/run-check-ledger-review-receipt-cases.sh` holds each of these with a refusal.
  No selected candidate, independent reviewer identity or claim dispositions exist.

  **Revisit or completion trigger:**
  Freeze a clean candidate after the other blocking work, retain its required check receipts and obtain the separate review receipt.

- **ID:**
  MU-03

  **Classification:**
  BLOCKING

  **Owner role:**
  Core/spec maintainer

  **Target effect:**
  Gates 1 and 2 are assessable against a complete obligation catalogue and explicit boundary-headroom disposition.

  **Current evidence and remaining work:**
  The version-2 catalogue now has checked `INV-*` records, and [the headroom target decision](tacenta-proofs/PROOF-BOUNDARY-HEADROOM-TARGET-DECISION.md) states its effect and reopen triggers. [The semantic-review brief](tacenta-spec/security-properties/INVARIANT-SEMANTIC-REVIEW-BRIEF.md) fixes the review questions and return record.
  Practice 5 remains BLOCKING until an independent reviewer evaluates the predicates and cited coverage.

  **Revisit or completion trigger:**
  Record the semantic review and reassess all component and gap rows against its findings.

- **ID:**
  MU-04

  **Classification:**
  BLOCKING

  **Owner role:**
  Evidence/CI implementer

  **Target effect:**
  CI emits an honest, versioned inventory of the selected candidate's required checks and evidence.

  **Current evidence and remaining work:**
  Receipt writers now run in each CI job;
  the aggregation job runs even when a dependency failed (`if: always()`) and fails closed on what that leaves, applies push/PR conditional sign-off rules, then builds and validates a versioned manifest.
  Local refusal controls cover missing, skipped, falsely inapplicable, foreign-candidate, mismatched-event, duplicate and missing conditional receipts, and a receipt whose recorded command steps are not `success` for exactly the steps `tooling/required-steps.json` lists for the event.
  Those steps are checked against the expected form of the workflow that lives in the same tree as the checker;
  nothing here stops a change that edits the workflow and that file together, because the checker need not change.
  The evidence pack carries `.github/workflows/ci.yml` and the receipt action beside `tooling/required-steps.json`, so a reviewer reads the workflow the receipts came from;
  that makes the self-edit visible at the candidate and does not prevent it.
  On `main` at `dea57eaf` the hosted aggregation job collected eight receipts, recorded `sign-off` as not applicable for a push, and validated the manifest, and on five earlier `main` runs since `bba8f04` it refused (`checks` failed on twelve runs since then; on seven of them the aggregation job was skipped or cancelled before it ran on failure);
  its artifact is kept for 90 days.
  A retained hosted candidate artifact has not yet been verified, and `tooling/reproduce-evidence.py --hosted` is the check that would verify one (it rebuilds the manifest from the artifact's receipts at the candidate commit and requires the bytes to match).
  `tooling/build-assurance-manifest.py --validate` has a refusal case for each thing it checks:
  another commit or tree (with the receipts moved to it as well), an unasserted clean tree, a source digest or size that differs, a dropped, retyped or additional review requirement, a failed or missing check, a field the schema does not list, a repository or generator it did not write;
  and the builder has cases for a dirty tree.
  `tooling/mutate-evidence-gates.py` removes each of those checks in turn and requires a case runner to fail;
  each is seen by a case that accepts a wrong input.
  The aggregation job builds the evidence pack, verifies it against the commit, rebuilds it in a fresh checkout, uploads it with its hidden files and verifies the uploaded copy again (the upload had dropped the two `.github` source files the manifest requires until 2026-10-15, and the verification before the upload could not see that).

  **Revisit or completion trigger:**
  Run and retain the aggregation for a clean selected candidate, verify its hosted artifact and record any hosted-only control results.

- **ID:**
  MU-05

  **Classification:**
  BLOCKING

  **Owner role:**
  Release operator

  **Target effect:**
  The reviewed evidence is packaged, retained and externally reproducible without private inputs.

  **Current evidence and remaining work:**
  `tooling/build-evidence-pack.py` now builds/verifies a digest inventory over an allowlisted public evidence set and refuses a manifest the production validator rejects.
  The verifier refuses altered or escaping entries.
  With `--candidate-repo` it also holds the pack to git:
  the commit is in the repository, the pack's tree is its tree, and every packed source is byte-identical to that file at that commit.
  `tooling/reproduce-evidence.py` rebuilds the manifest and the pack from the receipts with the candidate commit's own builders and requires them to match byte for byte, using public inputs only.
  `publish-evidence-archive.py` refuses a pack that does not verify or does not match git before it uploads anything, and its refusals are held by cases against a stand-in for `aws`.
  The complete production flow and the final manifest/pack/review-receipt binding passed in disposable clean candidates.
  The configured private S3 Object Lock archive has seven-year Compliance retention and its delete-refusal initialization control passed.
  A publication cut short cannot be completed by a retry (the retry is refused at the first key that exists, and Compliance retention forbids deleting the rest).
  No hosted candidate artifact, review receipt or candidate publication exists yet.

  **Revisit or completion trigger:**
  Run/verify the pack on the selected clean candidate, retain its Object-Lock metadata, publish the immutable GitHub release assets, then fresh-download-verify only the reviewed candidate.

- **ID:**
  MU-06

  **Classification:**
  CLOSED

  **Owner role:**
  Model/test implementer

  **Target effect:**
  The L2 operation evidence includes one bounded, composed establish-to-restore lifecycle property.

  **Current evidence and remaining work:**
  `Model.SessionTrace` and `Proofs.SessionTrace` state and prove the bounded refusal/restore, replay and terminal-failure observations under the documented abstract crypto and committed-snapshot assumptions.
  `tacenta-core/tests/session_lifecycle_property.rs` supplies a deterministic fresh-object establishment, restore, skipped-message recovery, replay and forged-message concrete witness.

  **Revisit or completion trigger:**
  Reopen when the bounded trace contract, its assumptions, or its concrete operation surface changes.

- **ID:**
  SL4-01

  **Classification:**
  BLOCKING for the Session L4 programme, NONBLOCKING for the current L2 target

  **Owner role:**
  Core maintainer

  **Target effect:**
  The Phase 0 carve-out is complete on its own terms before Phase 1 work merges.

  **Current evidence and remaining work:**
  Done:
  shipping lifecycle in `tacenta-core/lifecycle`, primitives in `tacenta-core/boundary`, facade pinned by `tests/public_api_compat.rs`,
  `TacentaLifecycle.lean` generated from committed source with a coverage gate and a boundary-surface gate, attestations current.
  Open:
  the product pin is still at a pre-carve-out commit and its legacy-v1 store fixture fails against this base and against the carve-out alike (a stale product expectation, not a regression);
  the Windows runner has not built the carve-out;
  no hosted Linux regeneration of `TacentaLifecycle.lean` exists (a local regeneration with the pinned binaries is byte-identical);
  `tacenta_core::serialization` is duplicated inside the lifecycle crate and nothing pins the two copies together;
  the coverage gate inventories only the thirty `Identity`/`PrekeyStore`/`Session` and `establish_*` operations, not the thirteen further public functions the leaf translates.
  Since #161:
  the eight-leaf session unit is assembled and translated from committed source (byte-identical regeneration), with conditional T1 theorems for the five roots and conditional T3 branch lemmas (register rows E2E-01, E2E-03, E2E-04);
  the session-unit assembly and port checks run in the hosted `checks` job.

  **Revisit or completion trigger:**
  Product pin bumped with its fixture corrected and Windows green;
  the duplicate serialization module removed or pinned;
  the coverage inventory widened or its scope recorded;
  then close.

<!-- End of the list. -->

## Component obligations

<!-- One item per table row, one sentence or clause per line: tooling/reflow-shared-lists.py. -->

- **Component or gate:**
  Sparse post-quantum ratchet

  **Current target deficit:**
  `P7-SPARSE-BRAID-INVENTORY.md` records the selected fixed-vector surface:
  initial states, epoch and chain-counter ceilings, the accepted retirement trace, the retired-epoch `NoChain` refusal, and the accepted side of the sparse total bound (`replacement-bound-counts-resulting-store` in `sparse-ratchet-state.json` and `replacement-range-excludes-the-chain-counter`).
  `retired-epoch-no-chain-refused` requires both runners to reject the canonical post-retirement state with `no-chain`.
  Generated differential and the specification-only reader cover the remaining operation combinations and durable no-op effect.

  **Gate class:**
  CLOSED

  **Package:**
  P7

  **Closure evidence:**
  Reassess the fixed-vector decision if a new externally observable sparse operation or refusal is specified.
  Reassessed for the sparse total bound:
  the accepted side has vectors;
  the refused side has none (`tacenta-test-vectors/README.md`, Three things no vector here pins).

- **Component or gate:**
  ML-KEM Braid

  **Current target deficit:**
  Below target:
  the component reads L3 against an L4 target in the `ASSURANCE.md` Components table, because its T3 receive theorems take `ct1_bounded` as a premise and, when the row was set, no theorem showed that a send keeps it.
  Preservation theorems now exist (`CLAIMS.md`, "Proved (the ML-KEM Braid keeps the two premises its receive theorems take)"), under an assumed law about the erasure decoder (two laws on the session unit) and without an independent read, and the label has not been changed;
  no recorded decision lowers the target.
  The fixed-vector surface is separate and closed:
  `P7-SPARSE-BRAID-INVENTORY.md` separates stored-state coverage for tags 0 and 5--11 and `Ct2Sampled` boundaries from the delegated valid key-pair layout for tags 1--4.
  The differential harness drives an empty `NoHeaderReceived` state through transition (6) with a persisted-key header MAC and mutation control, drives transition (5)'s real ciphertext MAC control, and uses five deterministic real-ML-KEM schedules to exercise all thirteen state-machine transitions.
  The specification-only reader independently checks the abstract transition table with its specified KEM double.

  **Gate class:**
  BLOCKING

  **Package:**
  P7

  **Closure evidence:**
  Record the level decision against the preservation theorems after they have had an independent read, or lower the target to L3 by a recorded decision.
  Revisit the fixed-vector surface if a portable KEM-state encoding, an independent producer for the delegated layout, or a new Braid transition/failure observable is introduced.

- **Component or gate:**
  Erasure code

  **Current target deficit:**
  [ERASURE-CODEC-TARGET-DECISION.md](tacenta-proofs/ERASURE-CODEC-TARGET-DECISION.md) records L3 as the current engagement target.
  Field arithmetic, codec T1, vectors, the independent reader and live-path tests remain the evidence.
  `ERASURE-DECODER-REFINEMENT.md` records the distinct L4 programme:
  a concrete codec relation, barycentric equivalence, decoder/encoder preservation and a port to the Braid-and-erasure unit.

  **Gate class:**
  CLOSED

  **Package:**
  P7

  **Closure evidence:**
  Reopen L4 before a full-codec refinement claim or on any trigger in the recorded decision.

- **Component or gate:**
  Session orchestration and prekey store

  **Current target deficit:**
  [P6-L2-TARGET-DECISION.md](tacenta-model/P6-L2-TARGET-DECISION.md) records the bounded model/concrete/independent-reader surface, its declared-crypto boundary and reopen triggers.

  **Gate class:**
  AMBIGUOUS

  **Package:**
  P6

  **Closure evidence:**
  Reopen before changing a covered operation or refusal, raising L2, or treating a reader-declared crypto fact as a computed result.
  Three revisit triggers have fired since (the `legacy_blocked` rules, #202, the identity-key refusals, #205, and initiator establishment under an expectation, ADR-0009);
  the decision has not been reopened (`ASSURANCE.md`, practice 4).

- **Component or gate:**
  Persisted formats:
  prekey store

  **Current target deficit:**
  The shared structural stored-format domain is now driven by the differential harness over the committed P4 fixtures;
  stored signatures and KEM-pair arithmetic are exact exclusions pinned by vectors and crate tests.

  **Gate class:**
  CLOSED

  **Package:**
  P5

  **Closure evidence:**
  Keep the prekey differential fixture set current if new shared-domain branches are added.

- **Component or gate:**
  Persisted formats:
  session

  **Current target deficit:**
  The shared structural stored-format domain is now driven by the differential harness over the committed P4 fixtures;
  the ratchet private/public relation is an exact exclusion pinned by vectors and crate tests.

  **Gate class:**
  CLOSED

  **Package:**
  P5

  **Closure evidence:**
  Keep the session differential fixture set current if new shared-domain branches are added.

- **Component or gate:**
  Practice 5:
  invariants catalogue

  **Current target deficit:**
  The version-2 evidence index now carries scoped `INV-*` records linked to requirements,
  operations,
  explicit headroom and selected evidence. [The headroom decision](tacenta-proofs/PROOF-BOUNDARY-HEADROOM-TARGET-DECISION.md) records the target scope and reopen triggers,
  and [the review brief](tacenta-spec/security-properties/INVARIANT-SEMANTIC-REVIEW-BRIEF.md) fixes the independent semantic assessment.

  **Gate class:**
  BLOCKING

  **Package:**
  MU-03

  **Closure evidence:**
  Record the semantic review;
  structural index validity and the scope decision alone do not close the practice.

- **Component or gate:**
  Practice 8:
  evidence traceability

  **Current target deficit:**
  Structural ID spine is checked;
  proof/vector/test evidence links are checked for all 34 security-property requirements, and the gate now fails when any requirement is missing from the evidence index.

  **Gate class:**
  CLOSED

  **Package:**
  P2

  **Closure evidence:**
  Keep the evidence index current when requirements, proofs, vectors or tests change.

- **Component or gate:**
  Practice 9:
  differential testing

  **Current target deficit:**
  The prekey store's and session's shared structural stored-format domains are now driven through both sides.
  Braid covers stored tags,
  `Ct2Sampled` boundaries, authenticated-header and ciphertext-MAC controls, and every state-machine transition under seeded real-ML-KEM schedules;
  its delegated persisted key-pair content rule has no universal vector verdict.

  **Gate class:**
  CLOSED

  **Package:**
  P7

  **Closure evidence:**
  Revisit the narrow delegated-layout decision with any portable encoding, independent producer, or new Braid observable.
  `ASSURANCE.md` rates practice 9 Partial;
  this row is closed for the domains it lists only.

- **Component or gate:**
  Gate 1

  **Current target deficit:**
  Every component must meet target or have a recorded target decision.
  Practice 5 is BLOCKING above, and the ML-KEM Braid reads L3 against an L4 target in the `ASSURANCE.md` Components table, because its T3 receive theorems take `ct1_bounded` as a premise (preservation theorems now exist in `CLAIMS.md`, and the label has not been changed);
  no recorded decision lowers that target.

  **Gate class:**
  BLOCKING

  **Package:**
  P1/P7/P6

  **Closure evidence:**
  Component obligation matrix closed or amended by recorded decisions.

- **Component or gate:**
  Gate 2

  **Current target deficit:**
  Gap register must have no open BLOCKING rows and no unresolved AMBIGUOUS rows.
  After `E2E-07` was closed on the run at `75387aa9` and `HL-R1-SPARSE-TRANSLATION` on one Linux x86_64 regeneration of 2026-10-03 (an emulated run by the maintainer's tool-assisted session,
  not independent),
  five rows are open at BLOCKING in the register,
  two of them findings of the fourteenth reader pass (`G14-03`,
  `G14-06`),
  while `HL-R1-SPARSE-READER`,
  the reader finding that used to be carried by `HL-R1-SPARSE-TRANSLATION`,
  closed on that pass (`HL-IMP-01` was closed and `INV-01` classified NONBLOCKING by recorded decisions on 2026-10-01),
  MU-02 to MU-05 above are BLOCKING,
  and MU-01 and the Session orchestration row above are AMBIGUOUS until the P6 decision is reopened or its fired triggers are recorded as answered.

  **Gate class:**
  BLOCKING

  **Package:**
  P1/P3/P6/P7

  **Closure evidence:**
  `GAP-REGISTER.md` rows classified and closed/decided as required.

- **Component or gate:**
  Gate 3

  **Current target deficit:**
  Claims ledger must receive a final independent claim-by-claim review after its last change.

  **Gate class:**
  BLOCKING

  **Package:**
  P9

  **Closure evidence:**
  [P9-GATE-EVIDENCE.md](tacenta-proofs/P9-GATE-EVIDENCE.md) names the required review record;
  it still needs a reviewer, frozen revision, artifacts read and findings/disposition.
  Before it, a person who did not write the model runs or extends the independent reader for the ML-KEM and Braid key-generation values (`HL-IMP-01-READER`).
  Not yet requested.

- **Component or gate:**
  Gate 4

  **Current target deficit:**
  Every gate must have negative-control evidence and must fail when required inputs are absent.

  **Gate class:**
  BLOCKING

  **Package:**
  P9/P2/P7

  **Closure evidence:**
  [P9-GATE-EVIDENCE.md](tacenta-proofs/P9-GATE-EVIDENCE.md) distinguishes the existing controls from missing records and cases;
  all need command/environment, deliberate fault and diagnostic at the final candidate.
  "Where the negative controls run" below records which gates have a control that runs in CI, which run only locally and which have none.

<!-- End of the list. -->

## Deferral decisions still needed

The current register has deferred rows, but a deferral only satisfies readiness
if it states the effect on the target and a revisit trigger. These still need a
recorded decision or a target-closing slice:

| Item | Current risk | Package |
| --- | --- | --- |
| Boundary headroom | [Recorded target decision](tacenta-proofs/PROOF-BOUNDARY-HEADROOM-TARGET-DECISION.md) keeps successor-headroom as an explicit success-refinement scope and names reopening triggers. | P7 |
| Erasure codec refinement | [Recorded L3 target decision](tacenta-proofs/ERASURE-CODEC-TARGET-DECISION.md) keeps the L4 programme deferred and disclosed. | P7 |

## Gate evidence inventory

<!-- One item per table row, one sentence or clause per line: tooling/reflow-shared-lists.py. -->

- **Gate/check:**
  `tooling/check-traceability.py`

  **Protected property:**
  Requirement/status/assumption/reference spine does not drift.

  **Current negative-control evidence:**
  `tooling/tests/run-check-traceability-cases.sh` runs a passing baseline and 24 refusal cases (its last line prints 22, a fixed string that undercounts):
  status-table removal/title/class drift, missing requirement status/`Rests on`, both direct assumption-inverse faults, unknown `LIM`/`ADV`/`AS`/`EX` references, evidence-index faults and invariant-catalogue faults.

  **Missing evidence:**
  Retain its command, environment and diagnostic-free candidate result.

- **Gate/check:**
  `tooling/check-workflows.sh`

  **Protected property:**
  Workflow files parse and obey the ten rules in the checker's header (pinned actions and images, a `permissions` block, checkout credentials, no download piped to a shell, `self-hosted` only on a push to `main`, no disabled job, the receipt form and the expected form), and the required workflow equals its expected form in `tooling/required-steps.json`.
  It does not refuse a `pull_request_target` trigger or write permissions in a further workflow.

  **Current negative-control evidence:**
  `tooling/tests/run-check-workflows-cases.sh` runs the case files under `tooling/tests/check-workflows-cases` (it prints their number), then makes 31 changes to the repository's own `ci.yml`, receipt action and `tooling/required-steps.json` (it prints that number too):
  each change to a command, condition, shell, environment or position must be refused as a difference from the expected form, two manifest edits must be refused, and three relabelled steps must be accepted.
  It also requires an empty tree to be refused.

  **Missing evidence:**
  The checks run from the tree being checked, which holds the workflow, the expected form and the checker:
  a change to all three is judged by its own edit, and the tree does not route it to a reviewer.
  The rule that the checker, and its case runner, fail and do not skip in CI without python3 or PyYAML is now held by eight cases at the end of the runner (`CR1` to `CR3` in `tooling/gate-mutations.json` re-run red).

- **Gate/check:**
  `tooling/check-precondition-shapes.py`

  **Protected property:**
  Listed vacuous numeric precondition shapes do not enter first-party Lean.

  **Current negative-control evidence:**
  72 case directories (the last, an unterminated string literal, added on 2026-10-01 after a guard-removal run found no case needed that guard) under `tooling/tests/check-precondition-shapes-cases`.

  **Missing evidence:**
  None identified in this P1 pass.

- **Gate/check:**
  `tooling/check-labels.sh`

  **Protected property:**
  Derivation labels stay registered and prefix-free except recorded pairs.

  **Current negative-control evidence:**
  `tooling/tests/run-check-labels-cases.sh` runs a passing baseline plus unregistered-label, unregistered-domain, forbidden-prefix and duplicate-label refusals against the production checker (the last was added on 2026-10-01; `AL-labels-dupes` survived before it).

  **Missing evidence:**
  Retain its command, environment and diagnostic-free candidate result.

- **Gate/check:**
  `tooling/check-vectors.py`

  **Protected property:**
  Vector files obey schemas.

  **Current negative-control evidence:**
  `tooling/tests/run-check-vectors-cases.sh` runs a valid baseline and seven refusals against the production checker (an unexpected field,
  a duplicate ID,
  an unsupported schema keyword,
  and four prekey-store migration rules:
  a legacy store without its upgrade,
  an upgrade that is not a v5 store keeping the header,
  an upgrade that is not longer than its input,
  and a current-version vector carrying both answers),
  and for the hosted-inventory group files a valid baseline and four refusals (an unread field in a case,
  in its policy object and in a binding,
  and a refusal class the vectors do not name).

  **Missing evidence:**
  Retain its command, environment and diagnostic-free candidate result.

- **Gate/check:**
  Independent reader

  **Protected property:**
  Specification-only reader can interpret and check committed vectors.

  **Current negative-control evidence:**
  Reader derived cases (264, 59 of them in `negative_cases.py`) exercise refusals.
  `test_skip_allowlist.py` holds the skip gate and the documented tallies to controls.
  `test_session_e2e_sweep.py` corrupts sampled bytes (up to eight positions in each input and field, and more at the edges of the two documented unchecked regions) of the session vectors and requires the reader to notice each one it says it checks.
  `session-operation-reader.py` must fail its five control traces.
  All run in the `vectors` job.

  **Missing evidence:**
  A retained mutation record for the reader outside the session vectors.

- **Gate/check:**
  Claims/attestation

  **Protected property:**
  Claims and generated artifacts match checked Lean/source state.

  **Current negative-control evidence:**
  `tacenta-proofs/scripts/check-audit-negatives.sh` plants thirteen declarations and holds the audit to one accepted compiler-trust orphan and twelve refusals, each matched to the audit's own reason.
  `tacenta-proofs/scripts/check-attest-negatives.sh` accepts the unmodified tree and then runs isolated production-attestation cases (its runner prints their number) for the claim ledger,
  the three manifests,
  the translation record,
  a deleted required pin,
  a compiler-trust pin the script does not list,
  a pin block copied over another,
  each way a generated `axiom` can differ from the axiom allowlist,
  spellings of a declaration the text scan must read alike,
  the audit comparison,
  the allowlist writer,
  and the construct scanner `tacenta-proofs/scripts/check-lean-constructs.sh`.
  `tooling/tests/run-lean-code-differential-cases.sh` (through `run-gate-controls.sh`) compares `attest.py`'s Lean stripper (`lean_code`,
  rewritten for speed as a scan that skips ordinary code,
  with a per-run memo) with the character loop it replaced,
  kept verbatim in the test,
  and with the scanner's own copy of that loop,
  on every tracked Lean file,
  hand-written hostile inputs and seeded random ones;
  it is tested by comparison on those inputs, not proved, and shows it can fail by telling thirteen single edits of the new stripper from the old loop.
  In the public workflow the run is split over sixteen machines (the `attest-negatives-slice` matrix) and the `attest-negatives` job prints the final line only when the sixteen slices are the slices of one run of the commit under test and their 64 shards together pass the check the script makes of its shards on one machine;
  `tooling/tests/run-attest-negatives-slice-cases.sh` holds that combiner to its refusals (a slice missing,
  repeated,
  relabelled,
  of another commit or script,
  cut short,
  or with shards that do not add up) and to the case count pinned in `tacenta-proofs/scripts/attest-negatives-case-count.txt`,
  which a full walk must equal (a change that adds or removes cases changes that file;
  it catches a walk cut short or padded,
  not a case replaced by another).
  The `attest-negatives` job runs `always()` and is designed to fail at its first step unless every slice succeeded, so that a failed slice turns it red rather than skipped;
  the controls of `tooling/check-workflows.sh` confirm that shape, and a hosted run with a failed slice has not yet been observed;
  it is not a required context of branch protection on main, which is a repository setting, and until it is one a failed slice blocks a merge through the required `assurance-receipts` job.
  Each slice writes its own manifest, so a slice directory made to look right by something other than the script is not detected;
  the hosted run of the matrix and the combiner is not checked by any local control.

  **Missing evidence:**
  Retain their command, environment and diagnostic-free candidate result.

- **Gate/check:**
  `attest.py` statement-pin floor (`REQUIRED_STATEMENT_PINS`)

  **Protected property:**
  A statement or definition pin (`#guard_msgs in #check @name` or `#print name`) on the floor cannot be deleted, commented out, left without its `#guard_msgs`, given an option that compares nothing, nested under another `... in`, written inside a namespace (also one that a `mutual` block follows) or moved to a module no audit module imports, without `attest.py --check` naming the declaration;
  the verification manifest records the floor, and a floor shorter than the record is refused, as is a record that is missing, unreadable, without the list or empty, and a floor that is empty.
  The floor lists names;
  for the 89 definition pins on `REQUIRED_PRINT_FORM` it also requires the form,
  `#print name`, and refuses `#check @name`, which prints the type of a definition and not its body.
  Every live statement pin, on the floor or not, is refused when its expected message holds a `⋯` other than an omitted proof printed with its proposition,
  `(⋯ : P)`, so a pin Lean cut off at depth 50 cannot stand;
  every `set_option pp.*` in the first-party Lean trees other than `pp.deepTerms true` and `pp.proofs.withType true` is refused, so no option can bring the cut back or narrow a message without a `⋯` (`pp.oneline`).
  The docstring is found through any comment between it and the `#guard_msgs` (Lean attaches it across one), and such a comment is refused.
  A message without a cut is still not the whole elaborated statement:
  Lean does not print, among other things, instance arguments, the function behind a coercion `↑`, implicit arguments, the binder types of `∃` and `fun`, universe levels or the types behind numerals and structure instances, so a new instance, a `coe` function or a definition changed under its name can change what a pinned statement means with its pin unchanged.
  `check-lean-constructs.sh` (row below) is a textual guard against the first two in hand-written Lean, and does not see a dependency's scoped instance brought in by `open`;
  the third is a matter for review.
  The docstring is found by reading the comments between the last code and the `#guard_msgs` as Lean reads them, so a `/--` inside a line comment is not taken for it.

  **Current negative-control evidence:**
  `tacenta-proofs/scripts/check-attest-negatives.sh` runs the statement-pin cases:
  one deletion,
  five ways of putting the pin in a comment,
  a docstring or a string,
  a bare `#check`,
  a renamed declaration,
  a `#check` of an application,
  a namespace,
  a namespace followed by a `mutual` block,
  four pins nested under another `... in` (`#guard_msgs (drop error)`,
  `#guard_msgs (drop all)`,
  `set_option` and `open`),
  nine `#guard_msgs` option lists that compare nothing or that the gate does not read (each asserted with its own reason),
  five spellings that are accepted,
  a `#print` definition pin with its `#guard_msgs` removed,
  an unimported module,
  a pin cut off with `⋯` where Lean cut it before its module set `pp.deepTerms`,
  an omitted proof printed without its proposition,
  the same behind a line comment,
  behind `-- /-- fake -/` and behind `-- /--` (a docstring opener inside a line comment is part of the comment),
  a comment between a docstring and its `#guard_msgs`,
  seven pretty-printer options (at file level,
  as an `... in` prefix and in a section),
  the floor shortened with and without a hand edit of the manifest,
  and the recorded floor missing,
  unreadable,
  without the list,
  null,
  empty,
  or the script's floor emptied.
  The scanner reads text, so it does not see the elaborated environment:
  it cannot tell that a pin names the declaration the claim means, and it reads what a pin says only for a `⋯`, so a statement weakened together with its pin's expected message is accepted by this check, and only the build, which compares the text, and the diff of the pin show it;
  a pin holds the printed statement, in which a definition appears by name, so changing a definition changes no pin unless the definition has its own `#print` pin.
  It does not follow `open`, a pretty-printer option set by a macro, a `run_cmd`, the lakefile or the command line, a macro that writes `#guard_msgs`, or a header longer than 20,000 characters.
  A `macro`,
  `syntax`,
  `#exit` or `run_cmd` in front of or around a pin is refused by `check-lean-constructs.sh` (run by `no-sorry.sh` in the translation job), not by this check.
  `--statement-pin-inventory` prints the survey.
  It also plants `#check @name` for eight of the 89 definition pins on `REQUIRED_PRINT_FORM` (`braidSendDrawCount`,
  `OracleOf`,
  `AeadSealBounded`,
  `AeadSealBoundedShape`,
  `SignFillsOnce64Of`,
  `KemShape`,
  `TripleRefusalOpen`,
  `StepRefines`;
  the other 81 are read by the same code and have no case of their own) and requires the refusal on `--check`,
  and for the first two on regeneration,
  and accepts that form for `takeDraws`,
  which is not on the list.

  **Missing evidence:**
  The floor lists all 533 statement and definition pins in the Lean trees when it was last edited (`--statement-pin-inventory` prints any live pin that is not on it);
  a pin added later is not required until its name is added.
  Removing a floor name needs an edit of the script and of the manifest's `statement_pin_floor` together, and the floor can be cut to any non-empty list in those two edits;
  a diff of the generated manifest shows it, nothing routes it to a reviewer, and nothing compares the floor with the base branch.
  `attest.py --check` runs in the `checks` job (`checks_40`) and the negatives in the `attest-negatives-slice` matrix (`negatives_slice`, sixteen slices of four shards each), whose slices the `attest-negatives` job combines (`negatives_combine`).
  `REQUIRED_PINS` and `REQUIRED_PRINT_FORM` have no such record.
  Either can be shortened by editing the script alone:
  with a name removed from `REQUIRED_PRINT_FORM`, its `#print` pin can be changed to `#check @name`, and with a name removed from `REQUIRED_PINS`, its axiom pin can be deleted, and `attest.py --check` accepts both after regeneration.
  The change shows in the diff of the script and of the regenerated manifest and nowhere else.

- **Gate/check:**
  Full CI

  **Protected property:**
  Public/local required checks run and fail rather than skip when required.

  **Current negative-control evidence:**
  `tooling/ci.sh` and the GitHub workflow run most of the same gates.
  The workflow also runs the receipt and aggregation jobs and the SPQR erasure regression (`rust_spqr_erasure`), which `tooling/ci.sh` does not run;
  `tooling/required-steps.json` fixes the workflow's commands.

  **Missing evidence:**
  P9 must record environments and missing-tool behaviour for each required gate.
  The rule to skip locally and fail in CI is now held for `tooling/check-workflows.sh` and its runner (eight cases), for `tooling/check-constant-time-asm.sh` (a stubbed toolchain; `CT4`) and, as a control that is in the tree and is not yet a CI step, for the differential harness (`tooling/tests/run-differential-required-input-cases.sh`; `DF1` to `DF3`).
  `tooling/check-signoff.sh` (missing base) and the collector (missing receipts) fail everywhere, and each has a case that shows the failure.

- **Gate/check:**
  `tooling/write-assurance-receipt.py`,
  `tooling/collect-assurance-receipts.py`,
  `tooling/assurance_validation.py` (receipt writer, collector, validator)

  **Protected property:**
  A required check is recorded as passed only for the selected candidate, in one event and one workflow run, with `success` for exactly the command steps `tooling/required-steps.json` lists for that event.
  The `assurance-receipts` job fails on a missing, duplicate, foreign, failed or skipped receipt.

  **Current negative-control evidence:**
  `tooling/tests/run-collect-assurance-receipts-cases.sh` (45 cases: an honest push set and an honest pull-request set collected, then single changes refused by the writer and the collector) and `tooling/tests/run-build-assurance-manifest-cases.sh`, both in the `checks` job.
  On `main` at `dea57eaf` the hosted job passed;
  on five earlier `main` runs since `bba8f04` it refused (MU-04 above has the detail).

  **Missing evidence:**
  Retain the hosted run and a mutation record at the candidate (`tooling/mutate-evidence-gates.py` makes the record).
  The per-receipt and document-level commit and tree comparisons each have a case.

- **Gate/check:**
  `tooling/build-assurance-manifest.py` (build and `--validate`)

  **Protected property:**
  The manifest names the selected commit and tree, asserts a clean tree, carries the digest of every repository-owned source, holds a passing receipt set and keeps the independent review requirement pending.

  **Current negative-control evidence:**
  `tooling/tests/run-build-assurance-manifest-cases.sh`:
  a pass case and 64 refusals:
  through the builder (the receipt set, one change at a time, and a dirty tree in a candidate checkout made for the runner), and through `--validate` (each field of a valid manifest changed once).
  It also holds the committed schema to the validator's field names.

  **Missing evidence:**
  The manifest's check set is validated by the shared receipt validator, so its refusals are in the rows above.
  Whether the digests of the repository-owned sources are the candidate's is not shown by this gate alone:
  `build-evidence-pack.py --verify --candidate-repo` shows it.

- **Gate/check:**
  `tooling/build-evidence-pack.py`,
  `tooling/check-ledger-review-receipt.py`,
  `tooling/validate-reviewed-evidence.py`

  **Protected property:**
  A pack's files match its manifest digests, its manifest and receipts name one clean candidate and agree, and a review receipt binds that pack.
  None of them shows that a receipt came from a real run or that a reviewer was independent.

  **Current negative-control evidence:**
  `tooling/tests/run-build-evidence-pack-cases.sh` (115 cases: the pack's structure and documents, a pack made by the production tools and held to git, the rebuild of a candidate, and the archive publisher against a stand-in for `aws`) and `tooling/tests/run-check-ledger-review-receipt-cases.sh` (79 cases: the receipt, the section tool and the reviewed-evidence check), both in the `checks` job.

  **Missing evidence:**
  No pack has been built from a hosted run and no review receipt exists.
  The rebuild runs Python from the candidate commit.
  Receipts are an input to every one of these:
  none shows that a workflow run wrote them.

- **Gate/check:**
  `tooling/check-signoff.sh` (DCO; `sign-off` job, and `checks_39` for a push to main)

  **Protected property:**
  Every commit a change adds is signed off by its author.

  **Current negative-control evidence:**
  `tooling/tests/run-check-signoff-cases.sh`:
  a pass case,
  12 refusals (missing base,
  unsigned commit,
  unsigned merge,
  an unsigned commit below and above a signed one,
  another person as signer,
  a trailer with a suffix and with a prefix,
  a sign-off outside the trailer block,
  another kind of trailer that carries the author's string,
  a committer who is not the author,
  and a signed merge of an unsigned commit) and one more acceptance,
  in the `checks` job.

  **Missing evidence:**
  An unsigned commit below a signed tip, a trailer that names another person and trailers that only contain the author's string (a suffix, a prefix, a sign-off outside the trailer block) are now cases (`S1` to `S8` re-run red).
  The push-mode step (`checks_39`) has no control beyond the script's own cases.

- **Gate/check:**
  `tooling/check-actionlint.sh`,
  `tooling/install-actionlint.sh`

  **Protected property:**
  Workflow expressions and schema are valid under the pinned actionlint, whose digest the installer checks.

  **Current negative-control evidence:**
  `tooling/tests/run-check-actionlint-cases.sh` (a pass control, a malformed expression, an unknown top-level key), run in the `checks` job after the installer.
  Without the tool the runner exits 1.

  **Missing evidence:**
  The installer's digest check now has a refusal case (`tooling/tests/run-install-script-cases.sh`; `AL1`, `AL2`), a control in the tree that is not yet a CI step.
  The controls were not run locally for the earlier assessment (actionlint was not installed).
  They run in the hosted `checks` job (`checks_06`);
  the run for `dea57eaf` passed them.

- **Gate/check:**
  `tooling/check-lifecycle-boundary-surface.py`,
  `tooling/check-session-operation-traces.py`

  **Protected property:**
  The set of opaque primitive calls reachable from the five Session roots stays classified;
  the committed operation-trace corpus keeps its required families and controls.

  **Current negative-control evidence:**
  `tooling/tests/run-check-lifecycle-boundary-surface-cases.sh` (9 refusals and 2 acceptances, and since 2026-10-01 a refusal of a missing Session root, which the guard-removal run showed no case needed) and `tooling/tests/run-check-session-operation-traces-cases.sh` (a pass case and 3 refusals), in the `checks` job.

  **Missing evidence:**
  The first pins the set of operations, not their call sites (its docstring says so).

- **Gate/check:**
  `tooling/check-constant-time-asm.sh`

  **Protected property:**
  The two hand-written constant-time functions compile to straight-line code:
  no conditional branch beyond `mac_eq`'s public length compare, no callee off the name allow-list.

  **Current negative-control evidence:**
  `tooling/tests/run-check-constant-time-asm-cases.sh`:
  3 controls, all on the callee allow-list.

  **Missing evidence:**
  The branch counter on x86_64 and aarch64, indirect jumps and calls, the refusal of `subtle` and `conditional_` callees, the one allowed length compare, the rules `main` applies to what the reader found and the rule that CI fails with no Linux target (a stubbed toolchain) are held by 86 further cases (`CT1` to `CT16` re-run red):
  every x86_64 conditional mnemonic, every aarch64 condition, the pair, unscaled, halfword and plain aarch64 loads,
  `lea` before the length compare and a listed `subtle::black_box`.

- **Gate/check:**
  `tacenta-proofs/scripts/check-lifecycle-translation-coverage.py`,
  `check-session-satisfiability-negatives.sh`,
  `check-initial-dispatch-negatives.py`,
  `check-port-negatives.sh` (the `translation-part` jobs through `no-sorry.sh`, combined by the `translation` job)

  **Protected property:**
  Every public lifecycle operation is generated;
  the Session contract coverage depends on each named witness;
  the initial dispatcher keeps its matching-key guards;
  the Session Braid port scripts refuse a source whose anchor moved.

  **Current negative-control evidence:**
  `check-lifecycle-translation-coverage-negatives.sh` (one missing-root mutation),
  `check-session-satisfiability-negatives.sh` (203 cases,
  18 of them acceptances;
  every Session witness removed in turn,
  the joint model,
  its bridges and the record proofs broken one change at a time,
  the classification audit refused on seven mutations and two wrong inputs,
  for the joint decision of `OracleOf`,
  each witness removed,
  nine primitives and the private-key view of its model changed one at a time and one field of a bridge or a record changed,
  and,
  for `DecryptOracleOf` from four laws,
  its proof moved onto the real constants (refused by its axiom pin alone) or routed through `oracleOf_of_laws` (refused by both pins),
  two interpretation fields and its view law changed,
  and each of the five equalities of the model frame lemma's helper swapped,
  each refused because the proof fails,
  and,
  for the Session unit's two sparse agreements from five laws,
  each law removed from the bundle or weakened where the derivation takes it,
  the shape the two models satisfy with a field dropped or the pop law weakened,
  and the model witness removed,
  each refused,
  and,
  for the decrypt hypotheses together at one witness,
  each of the fifteen laws removed from the bundle,
  the agreements moved to another oracle's KEM model (refused by the link to the refinement and,
  with the link removed,
  by the statement pin alone),
  the oracle built at `toyKem`,
  the model witness removed,
  and the shipped-size model's `CT1_LEN` or its KEM's first-ciphertext size set to the toy size,
  each refused,
  and,
  for the KEM model read off the `tacenta_kem` wrapper,
  each of its eight laws and each of the three fields that replace the joint bundle's agreements removed,
  each refusing arm of the model made to answer `some`,
  its hash given a 32-byte fallback,
  its first-ciphertext size set to the toy size,
  the corollary restated at `toyKem` (refused by its statement pin alone) and the model witness removed,
  each refused,
  and,
  for the decrypt hypotheses at a Braid holding a key pair,
  the held vector,
  private part and header hash each altered in one byte,
  the joint statement moved to `toyKem`,
  the refutation at `toyKem` moved to `wrapperKem`,
  the added law removed,
  the chunk altered in one byte or given another index,
  and the held-value predicate without its held bytes (refused by its `#print` pin alone),
  each refused),
  `check-initial-dispatch-negatives.py` (47 proof mutations, each refused by Lean for its stated premise) and `check-port-negatives.sh` (ten broken anchors: seven refused naming a unit edit and three, for the preservation port, refused for a substitution count, for the pin-section marker and for a declaration after the pins).

  **Missing evidence:**
  None identified beyond the number of mutations each holds.

- **Gate/check:**
  `tacenta-proofs/scripts/check-lifecycle-translation-coverage.py`,
  `check-session-satisfiability-negatives.sh`,
  `check-initial-dispatch-negatives.py`,
  `check-port-negatives.sh`,
  `check-braid-agreement-negatives.sh` (the `translation-part` jobs through `no-sorry.sh`, combined by the `translation` job)

  **Protected property:**
  Every public lifecycle operation is generated;
  the Session contract coverage depends on each named witness;
  the initial dispatcher keeps its matching-key guards;
  the Session Braid port scripts refuse a source whose anchor moved;
  the witnesses for the Braid refinement agreements, the erasure halves, the state hypotheses, the entry points and the Reed-Solomon proof of `ErasureAgrees` refuse a changed shape, model field, witness, definition or pinned statement.

  **Current negative-control evidence:**
  `check-lifecycle-translation-coverage-negatives.sh` (one missing-root mutation),
  `check-session-satisfiability-negatives.sh` (203 cases,
  18 of them acceptances;
  every Session witness removed in turn,
  the joint model,
  its bridges and the record proofs broken one change at a time,
  the classification audit refused on seven mutations and two wrong inputs,
  for the joint decision of `OracleOf`,
  each witness removed,
  nine primitives and the private-key view of its model changed one at a time and one field of a bridge or a record changed,
  and,
  for `DecryptOracleOf` from four laws,
  its proof moved onto the real constants (refused by its axiom pin alone) or routed through `oracleOf_of_laws` (refused by both pins),
  two interpretation fields and its view law changed,
  and each of the five equalities of the model frame lemma's helper swapped,
  each refused because the proof fails,
  and,
  for the Session unit's two sparse agreements from five laws,
  each law removed from the bundle or weakened where the derivation takes it,
  the shape the two models satisfy with a field dropped or the pop law weakened,
  and the model witness removed,
  each refused,
  and,
  for the decrypt hypotheses together at one witness,
  each of the fifteen laws removed from the bundle,
  the agreements moved to another oracle's KEM model (refused by the link to the refinement and,
  with the link removed,
  by the statement pin alone),
  the oracle built at `toyKem`,
  the model witness removed,
  and the shipped-size model's `CT1_LEN` or its KEM's first-ciphertext size set to the toy size,
  each refused,
  and,
  for the KEM model read off the `tacenta_kem` wrapper,
  each of its eight laws and each of the three fields that replace the joint bundle's agreements removed,
  each refusing arm of the model made to answer `some`,
  its hash given a 32-byte fallback,
  its first-ciphertext size set to the toy size,
  the corollary restated at `toyKem` (refused by its statement pin alone) and the model witness removed,
  each refused,
  and,
  for the decrypt hypotheses at a Braid holding a key pair,
  the held vector,
  private part and header hash each altered in one byte,
  the joint statement moved to `toyKem`,
  the refutation at `toyKem` moved to `wrapperKem`,
  the added law removed,
  the chunk altered in one byte or given another index,
  and the held-value predicate without its held bytes (refused by its `#print` pin alone),
  each refused),
  `check-initial-dispatch-negatives.py` (47 proof mutations, each refused by Lean for its stated premise),
  `check-port-negatives.sh` (ten broken anchors:
  seven refused naming a unit edit and three,
  for the preservation port,
  refused for a substitution count,
  for the pin-section marker and for a declaration after the pins) and `check-braid-agreement-negatives.sh` (53 cases,
  6 of them acceptances;
  each bridge of an agreement,
  a model field,
  a width fact,
  a state witness,
  a definition the state theorems are stated through,
  a specification function of the Reed-Solomon proof,
  a statement of its plan,
  the decoder invariant and a pinned statement changed one at a time,
  each refused inside the theorem it names or by its pin;
  a refusal by a resource limit counts as a failure of the gate).

  **Missing evidence:**
  None identified beyond the number of mutations each holds.

- **Gate/check:**
  `tacenta-proofs/scripts/check-lifecycle-translation-coverage.py`,
  `check-refuted-records.sh`,
  `check-session-satisfiability-negatives.sh`,
  `check-initial-dispatch-negatives.py`,
  `check-initiator-second-message-negatives.py`,
  `check-atomicity-negatives.py`,
  `check-repair-negatives.py`,
  `check-responder-establish-replay-negatives.py`,
  `check-send-refusal-negatives.py`,
  `check-sparse-skip-kind-negatives.py`,
  `check-sparse-store-full-negatives.py`,
  `check-tampered-reply-negatives.py`,
  `check-decrypt-ratchet-negatives.py`,
  `check-established-negatives.py`,
  `check-restored-negatives.py`,
  `check-encrypt-negatives.py`,
  `check-responder-negatives.py`,
  `check-responder-frame-negatives.py`,
  `check-responder-receipt-negatives.py`,
  `check-responder-repeated-frame-negatives.py`,
  `check-responder-successor-negatives.py`,
  `check-responder-reply-negatives.py`,
  `check-responder-reply-receipt-negatives.py`,
  `check-responder-second-receipt-negatives.py`,
  `check-responder-second-send-negatives.py`,
  `check-send-preservation-negatives.py`,
  `check-discharge-native-decide-negatives.py`,
  `check-initiator-second-send-negatives.py`,
  `check-receive-preservation-negatives.py`,
  `check-port-negatives.sh` (the `translation-part` jobs through `no-sorry.sh`, combined by the `translation` job)

  **Protected property:**
  Every public lifecycle operation is generated;
  the Session contract coverage depends on each named witness;
  the initial dispatcher keeps its matching-key guards;
  the frame proofs of the four lifecycle bodies keep refusing a write on a refusal path;
  the restated-record results keep refusing a changed statement;
  the refuted evidence records stay untaken (`check-refuted-records.sh` runs `Model.AxiomAudit.takersReport` as an executable over each translation audit module's closure and compares its printed block; the controls show the walk reports and refuses a planted taker, and the script refuses a walk that refuses, prints other lines or skips a closure);
  the composed Triple send keeps the leaf's complete refusal result;
  the sparse skip's store-full conjunct keeps naming `skippedStoreFull` and keeps reading the survivor bound;
  the `decrypt_ratchet` refinement, its retry-loop induction and its refusal closure keep the facts they rest on, and its open disjunct stays a Triple refusal that is not a full store;
  the per-run bounds derivation keeps its counter ceilings and the parked state's exclusion;
  the non-fresh session states keep the invariant clauses and ceilings they are built to meet;
  the public `decrypt` refinement on frames that are not initial messages keeps the facts it rests on;
  the invariant, the counter ceilings and the model relation at a successful `establish_initiator_for` output keep the laws, the `verify_bundle` inversion and the generated values they rest on;
  the invariant at an accepted `Session::import`, the counter-ceiling check, the restored relation and the round trip of an established initiator session keep the refusal, the clauses, the scope, the laws and the encodings they rest on;
  the public `encrypt` at a successful `establish_initiator_for` output, its two outcomes and the session a successful send leaves keep the bounds, the laws, the draw count and the computed model step they rest on;
  the `establish_responder` outcomes, their store and random-source effects, the success commit's effects and the intermediate session's invariant, ceilings and relation keep the laws, checks and generated values they rest on;
  `establish_responder` on the frame the initiator's first `encrypt` emits keeps the agreement law, the per-run KEM premise, the store's distinctness, the refusals' causes and the initiator's values it rests on;
  `establish_responder` accepting that frame keeps the model's first message on both sides, the two boundary laws, the bridges from the two runs and the attributed chunk it rests on, and its composition keeps the plaintext, the key and the bytes it names;
  the invariant and the four ceilings at the session that call returns keep the received Triple's counters, the clock, the keys' canonicity, the ratchet key's bytes, the agreement's epoch, the decoder's one chunk and the two walks they rest on, and their composing proof uses the sent bytes;
  `Triple::invariant` read on the model keeps its roles clause,
  and the invariant and the counter budget after an `encrypt` at an agreement state that takes no draw keep the no-draw premise,
  the key-pair clone record,
  the budget's unit and the walks they rest on,
  and their composition on the run uses the reply's call and relation (the invariant and the relation it places at the returned session are conjuncts of called theorems,
  placed unchanged);
  the Session unit's refinement constants, kernel proofs since 2026-10-21, keep deciding the bytes and bounds they state, the live pin of a constant refuses `native_decide` restored under it, and `export_message_fits` states exactly the type of the compiler-trust axiom `export` carries;
  the initiator's second `encrypt` at the session its receipt of the reply returns keeps the no-draw walk at `KeysSampled`, the second frame's chunk and key, the providers' no-draw premise and the model step it rests on, and its composing proof uses the receipt's session, the source it left and its relation;
  `check-receive-preservation-negatives.py`: the in-order receive step keeps its decoder scope, the key-pair clone record, the budget it spends, its dependence on the relation after the call, the canonical-key law and the oracle's public-key clause, the public step keeps its scope and budget, and on the reply's run the budget and the fresh-key premise are the ones the proof composes;
  `check-initiator-second-message-negatives.py`:
  the initiator's second message keeps the budget after the send, the fresh-key premise and the second plaintext's bound it composes, and places the ceilings at the session the receipt returns, and its reach keeps the plaintext bound and the law that chooses the responder's source (the receipt's call and the relations after the send are conjuncts of called theorems, placed unchanged);
  `check-responder-second-receipt-negatives.py`:
  the responder's receipt of the initiator's second message keeps the draw,
  the plaintext,
  the stale arm's refusal and the two-chunk decoder it composes,
  its success headline keeps the fresh-key premise and the budget after the receipt,
  and its run and reaches keep the responder's further bytes, the law that chooses the responder's and the initiator's further bytes and the stale run's key equation (the initiator's second send and its receipt of the reply are conjuncts of called theorems,
  placed unchanged);
  `establish_responder` on the initiator's first frame delivered again, at the store its first success committed, keeps the last-resort path, the commit's single record entry, the fingerprint of the secret read back and the committed store it returns, and its composition keeps the bundle's last-resort key and absent one-time curve key;
  `Session::decrypt` of the initiator's first frame delivered again, at the responder's session after its first receipt, keeps the one draw, the model's out-of-order refusal, the second source and the oracle that holds its draw, and its composition keeps the second source, the sent bytes and the header source's chunk;
  the initiator's refusal of a reply frame whose ciphertext was replaced keeps the frame layout, the premise's associated data, the freshness premise, the uniqueness law, the draw and the `Aead` refusal it rests on, the law and the premise are held by their pins, and the toy and lenient models keep separating the law from the round trip;
  the Session unit's sparse skip, related to the model's detailed skip, keeps the refusal's kind from `spqr_skip_refusal_refines` (a mapping that swaps `TooManySkipped` and `SkippedStoreFull`, and every refusal claimed store-full, are refused in the composing proof), the success conjunct of the leaf refinement, and an injective error mapping;
  `check-responder-second-send-negatives.py`:
  the responder's `encrypt` at the session its receipt of the initiator's second message returned keeps the source the receipt left,
  the session it is called at, the Triple-only write, the frame's ratchet key and sending chain, the relation after the send and the budget after it,
  and its reach keeps the responder's further bytes, the law that chooses the initiator's further bytes and the plaintext bound (the receipt's plaintext and the run's call are conjuncts of called theorems,
  placed unchanged);
  the Session Braid port scripts refuse a source whose anchor moved.

  **Current negative-control evidence:**
  `check-lifecycle-translation-coverage-negatives.sh` (one missing-root mutation),
  `run-check-refuted-records-cases.sh` (8 cases with a stand-in walk: the recorded blocks accepted over five closures each asked once with the recorded roots, records and names; a refusal, a missing line, an extra line, a moved record and a dropped closure refused),
  `check-refuted-records-negatives.sh` (23 cases:
  each record taken directly,
  sixteen further takers by spelling,
  visibility,
  route and module,
  honest code clean,
  every record absent when unimported,
  an expected name that takes nothing,
  an empty record list and a record outside the first-party prefixes refused;
  the built executable over a compiled module with a planted taker,
  a forging initializer and a notation on its name reports the taker alone),
  `check-session-satisfiability-negatives.sh` (203 cases,
  18 of them acceptances;
  every Session witness removed in turn,
  the joint model,
  its bridges and the record proofs broken one change at a time,
  the classification audit refused on seven mutations and two wrong inputs,
  for the joint decision of `OracleOf`,
  each witness removed,
  nine primitives and the private-key view of its model changed one at a time and one field of a bridge or a record changed,
  and,
  for `DecryptOracleOf` from four laws,
  its proof moved onto the real constants (refused by its axiom pin alone) or routed through `oracleOf_of_laws` (refused by both pins),
  two interpretation fields and its view law changed,
  and each of the five equalities of the model frame lemma's helper swapped,
  each refused because the proof fails,
  and,
  for the Session unit's two sparse agreements from five laws,
  each law removed from the bundle or weakened where the derivation takes it,
  the shape the two models satisfy with a field dropped or the pop law weakened,
  and the model witness removed,
  each refused,
  and,
  for the decrypt hypotheses together at one witness,
  each of the fifteen laws removed from the bundle,
  the agreements moved to another oracle's KEM model (refused by the link to the refinement and,
  with the link removed,
  by the statement pin alone),
  the oracle built at `toyKem`,
  the model witness removed,
  and the shipped-size model's `CT1_LEN` or its KEM's first-ciphertext size set to the toy size,
  each refused,
  and,
  for the KEM model read off the `tacenta_kem` wrapper,
  each of its eight laws and each of the three fields that replace the joint bundle's agreements removed,
  each refusing arm of the model made to answer `some`,
  its hash given a 32-byte fallback,
  its first-ciphertext size set to the toy size,
  the corollary restated at `toyKem` (refused by its statement pin alone) and the model witness removed,
  each refused,
  and,
  for the decrypt hypotheses at a Braid holding a key pair,
  the held vector,
  private part and header hash each altered in one byte,
  the joint statement moved to `toyKem`,
  the refutation at `toyKem` moved to `wrapperKem`,
  the added law removed,
  the chunk altered in one byte or given another index,
  and the held-value predicate without its held bytes (refused by its `#print` pin alone),
  each refused),
  `check-initial-dispatch-negatives.py` (47 proof mutations, each refused by Lean for its stated premise),
  `check-atomicity-negatives.py` (four unmodified bodies accepted and twelve planted changes refused, each on a refused goal that shows the planted field),
  `check-receive-preservation-negatives.py` (two unmodified copies accepted and 23 changes refused: 12 inside the four composing proofs, 2 projections, 7 on leaf lemmas, one statement-shape check and one definition held by its pin),
  `check-repair-negatives.py` (two unmodified inputs accepted, five changes refused),
  `check-send-refusal-negatives.py` (one unmodified proof accepted, two changes refused),
  `check-sparse-skip-kind-negatives.py` (two unmodified copies accepted and four changes refused:
  the refusal's kind under a mapping that swaps `TooManySkipped` and `SkippedStoreFull`,
  every refusal claimed `skippedStoreFull`,
  a success claimed to keep the state,
  each in the composing proof and accepted there with that proof emptied,
  and the mapping claimed injective with `TooManySkipped` sent to `skippedStoreFull`),
  `check-sparse-store-full-negatives.py` (one unmodified proof accepted, two changes refused; a harmless rewrite of the branch that moves one of its anchors makes it fail closed, naming the anchor),
  `check-decrypt-ratchet-negatives.py` (fourteen unmodified copies accepted and forty-two changes refused,
  each at a named declaration or pin:
  four in the loop correspondence,
  two that widen the open disjunct,
  two in the run record,
  one that widens the conclusion,
  one that empties the stores of the run record,
  one that widens the disjunct with the pins kept,
  four in the Triple refusal refinement,
  one in the closure's bridge,
  one that puts the disjunct back into the complete statement with its pins kept,
  one in the closure's screen,
  five in the per-run bounds derivation and one that weakens its Braid epoch ceiling with the pins kept,
  nine in the invariant-passing states that are not fresh (three in the stored-key Triple's invariant,
  the stored clock at the park,
  the sparse epoch and the Braid epoch each breaking one clause of `Session::invariant`,
  the responder's sparse direction,
  the pending ciphertext's length and the established ephemeral's curve byte),
  five planted in a renamed copy of the generated `decrypt` and refused in the copied pass-through step lemma,
  three in the public `decrypt` join (its target without the dispatch,
  its scope premise deleted,
  its inner step on the first form) and one that drops the `draws` conjunct from the join's recorded statement with its pins kept),
  `check-established-negatives.py` (three unmodified copies accepted and thirteen changes refused,
  each at a named declaration or pin:
  the walk's Triple with a clock other than the generated zero,
  the structural invariant without each of its two laws and without the `verify_bundle` inversion,
  a law without its prime-order clause once without and once with its pins,
  the ceilings asked at the parked clock and at the last Braid epoch,
  the relation asked of two wrong model states,
  the success case without the key's self-equality,
  and the joint model with the decrypt model's public key),
  `check-restored-negatives.py` (four unmodified copies accepted and twelve changes refused,
  each at a named declaration or pin with a message that names the fact removed:
  the invariant inversion against an `import` without its `Inconsistent` refusal,
  the ceiling check without its sparse-epoch clause,
  the scope widened to a sampled Braid,
  the round trip concluding an altered session and without the `as_slice` law,
  the ratchet encoding with two counters swapped,
  the Braid epoch reader without its bound,
  the `Option::branch` law weakened to allow a break,
  the established shape without the ciphertext bound,
  the joint model at an interpretation whose public-key reader drops the key,
  that bound's law weakened with its pins kept,
  and the joint model of the composed premise list at two interpretations with its pins kept),
  `check-encrypt-negatives.py` (two unmodified copies accepted and sixteen changes refused,
  each change refused at a named declaration or pin,
  eleven with a message that names the fact removed (an omega counterexample,
  an unsolved goal or a mismatch naming it;
  the outcome theorem with its refusal arm replaced by `False` is refused with `False` unsolved and the model's key generation refusing in context),
  three by an unsolved `False` goal at the named place (the first Triple send claimed to refuse,
  its sparse message number claimed to be 0,
  the successor's counters claimed uncounted),
  one by a proof error at the named place (the joint model's key generation leaving the source) and one by its pin's text,
  by design:
  the headroom lemma without the ciphertext bound and one byte short,
  the Triple store facts at the established session with its sparse epoch moved to the last value,
  the draw record with one draw consumed,
  the key-generation law weakened to some randomness,
  the outcome theorem with its key-generation refusal arm replaced by `False`,
  the first Triple send claimed to refuse and its sparse message number claimed to be 0,
  the wire claimed to be the bare ratchet frame,
  the successor's encoder restated before its first chunk,
  the successor's chain counters claimed uncounted,
  the sent Triple's classical counter at 0,
  the successor invariant without `ValidateEkAgrees` and without the seed length,
  the joint model's key generation leaving the source,
  and the key-generation answer without its refusing arm with its pins kept),
  `check-responder-negatives.py` (two unmodified copies accepted and nineteen changes refused,
  each at a named declaration or pin and against a message naming the change:
  the intermediate session's structural invariant without our identity law,
  the initiator's identity check or the ephemeral decode check,
  the session without its established ephemeral,
  the decoder sized without the MAC,
  without its chunk bound and without the `HEADER_LEN` bound,
  the ceilings at the parked clock,
  the model's Braid as the initiator's and its associated data empty,
  `ReplayedLastResort` dropped from the refusals,
  the success commit without its removals,
  an inner refusal returning the given source,
  the commit leaving the replay record unchanged and the one-time KEM prekeys unchanged on the one-time path,
  an inner success giving a draw back,
  a model success keeping the oracle,
  the joint model at the zero base point,
  and the commit recording key identifier 0 in the replay record with its pins kept;
  four of them,
  the three structural-invariant edits and the `HEADER_LEN` bound,
  are proof-dependency controls that leave the statement unchanged),
  `check-responder-establish-replay-negatives.py` (two unmodified copies accepted and twelve changes refused,
  each at a named declaration or pin and against a message naming the change,
  every one a change to a statement and a proof-breakage check there,
  not a proof that the changed statement is false:
  six labelled inside the composing proofs `establish_responder_again_refused` and `initiator_first_send_responder_replay_refused` and one a projection of a called theorem's conjunct,
  the labels checked once at start-up against a syntactic form of the projection standard read off the module,
  and at run time only that each change is refused at its labelled place,
  each inside control also run with that proof replaced by `sorry` and required to be accepted there,
  which verifies attribution only (that the syntactic form is the right standard is by reading) (inside:
  the second call claimed on the one-time path,
  the commit claimed on the one-time path,
  the fingerprint claimed of the secret before it is read back,
  the second call claimed to return the store before the commit,
  and the bundle claimed to name another KEM key or a one-time curve key;
  the projection: the record claimed to gain the one-time identifier);
  two statement-shape checks on the reach (the record claimed empty after the first call and the second call claimed to take a draw, still refused with the headline's proof emptied),
  two on the leaf lemmas (the replay check claimed without the entry and the commit claimed with a one-time curve key),
  and the replay check's statement with a variable renamed and its pins kept;
  an error that is not a refusal voids a run, matched without regard to case;
  a timeout never counts as the named refusal;
  none shows that the model refuses the same delivery),
  `check-responder-frame-negatives.py` (two unmodified copies accepted and twenty changes refused,
  each at a named declaration or pin and against a message naming the change,
  every one a change to a statement or a definition and a proof-breakage check there,
  not a proof that the changed statement is false:
  the agreement law weakened to agree with itself,
  the joint model's agreement returning the private key and its public key the zero key,
  the per-run KEM premise saying nothing of what decapsulation returns,
  the store's distinctness kept for its first two identifiers only (once for repeat-freedom,
  once for `ABSENT_ID`),
  the legacy refusal claimed without the marker,
  the full-record refusal at an empty record and below the bound,
  the parts' shared secret claimed the ratchet agreement,
  their peer identity key the initiator's ephemeral key and the last-resort flag inverted,
  the decoded KEM identifier claimed the signed prekey's,
  `publish` claimed to name the first one-time KEM entry,
  the one-time KEM lookup without its first-occurrence premise,
  the initiator's ratchet agreement claimed with its identity key,
  the reach's store with a legacy marker,
  the composed frame claimed for the empty plaintext,
  the responder fed the plaintext instead of the sent bytes,
  and the agreement law weakened with its pins kept),
  `check-responder-receipt-negatives.py` (two unmodified copies accepted and twenty changes refused,
  each at a named declaration or pin and against a message naming the change,
  every one a change to a statement or a definition and a proof-breakage check there,
  not a proof that the changed statement is false:
  the receiver's sparse chains not swapped,
  the first receive without its root relation and the first header's sparse number 2,
  the decoder round trip without its codeword-length condition,
  the model's success keeping the oracle and the ratchet key always the draw,
  the AEAD law weakened to opening returns and the contributory law to the agreement not returning `none`,
  the associated data with the keys in the other order,
  the responder's root claimed the derived root,
  the attributed source without its MAC,
  the non-contributory refusal claimed when the agreement returns,
  the composed success claimed for a caller-chosen plaintext,
  a frame sealed under a caller-chosen key,
  the responder fed the plaintext instead of the sent bytes,
  the store claimed unchanged on the one-time path,
  the responder's draws claimed untouched,
  the header source without its MAC,
  the joint model with the empty seal,
  and the contributory law without its premise with its pins kept;
  the two on the composition chain (plaintext,
  bytes) show the composed proof uses the plaintext and bytes it names,
  the other-key control sits on the model step the composition rests on,
  no control covers the chain's own key step,
  and none shows that the responder refuses other inputs),
  `check-responder-second-receipt-negatives.py` (two unmodified copies accepted and nineteen changes refused: eleven inside the five composing proofs, two projections, four on leaf lemmas and two definitions held by their pins),
  `check-responder-second-send-negatives.py` (two unmodified copies accepted and nineteen changes refused: ten inside the two composing proofs, two projections, five on leaf lemmas and two definitions held by their pins),
  `check-responder-successor-negatives.py` (two unmodified copies accepted and seventeen changes refused,
  each at a named declaration or pin and against a message naming the change,
  every one a change to a statement or a definition and a proof-breakage check there,
  not a proof that the changed statement is false:
  one inside a composing proof and two projections of called theorems' conjuncts,
  the labels checked once at start-up against the two composing theorems and a syntactic form of the projection standard read off the module,
  and at run time only that each change is refused in the declaration it is labelled with (a refusal where the proof places a conjunct of a called theorem's conclusion unchanged is a projection),
  the inside control also run with that proof replaced by `sorry` and required to be accepted there,
  which verifies attribution only (that the syntactic form is the right standard is by reading) (inside:
  the composed call taken on the plaintext,
  in `initiator_first_send_responder_successor_hypotheses`;
  projections:
  the composed invariant claimed of the initiator's session,
  a conjunct of `responder_first_frame_successor`,
  and the returned session's relation claimed to the prepared model,
  a conjunct of `responder_first_frame_inner_succeeds`),
  ten on the leaf lemmas (the received Triple claimed to have received nothing and its sparse receiving counter claimed 0,
  the clock claimed parked at the last value,
  the Triple's invariant without the sending key's canonicity,
  the structural invariant without the ratchet key's bytes being the sending key,
  the agreement claimed at epoch 2,
  the decoder lemma for two chunks and without its chunk-count premise,
  `Braid::receive` claimed to keep the decoder or return nothing else (refused only at the branch that adds the chunk),
  `decrypt_ratchet` claimed never to replace the ratchet key),
  three statement-shape checks on the headline's corollaries (the invariant claimed of the initiator's session,
  the call taken on the plaintext and the reach's invariant claimed of the initiator's session,
  each run again with the headline's proof emptied and still refused),
  and the session definition without its ratchet key with its pins kept;
  a timeout never counts as the named refusal;
  only the one inside the composing proof shows the composed proof uses what it names (the sent bytes),
  the two projections only that the composed conclusions place the called theorems' conjuncts unchanged and the three statement-shape checks only that the corollaries and the reach project its statement,
  and none shows that another session fails the invariant),
  `check-responder-repeated-frame-negatives.py` (two unmodified copies accepted and seventeen changes refused,
  each at a named declaration or pin and against a message naming the change,
  every one a change to a statement and a proof-breakage check there,
  not a proof that the changed statement is false:
  eight labelled inside the composing proofs `responder_first_frame_repeat_refused` and `initiator_first_send_responder_repeat_refused` and two projections of called theorems' conjuncts,
  the labels checked once at start-up against a syntactic form of the projection standard read off the module,
  and at run time only that each change is refused at its labelled place,
  each inside control also run with that proof replaced by `sorry` and required to be accepted there,
  which verifies attribution only (that the syntactic form is the right standard is by reading) (inside:
  the refusal claimed to take no draw,
  the model's step claimed to keep the draw,
  the refusal claimed to be `NotARepeatedInitial`,
  the second draw claimed of the first source in either composing proof,
  the model's step claimed at the first receipt's oracle,
  the first call claimed on the plaintext,
  and the model session claimed at chunk index 1;
  projections: the composed call claimed from the first source and the key generation claimed at swapped draws);
  two statement-shape checks on the reach (claimed from the seed and claimed refused as not a repeat, still refused with the headline's proof emptied),
  four on the leaf lemmas (the model's receive claimed to refuse for no receiving chain, the draw's agreement claimed refused, the model's refusal claimed to keep the oracle, and the ephemeral comparison claimed on the identity key),
  and the model receive's statement with a variable renamed and its pins kept;
  an error that is not a refusal voids a run, matched without regard to case;
  a timeout never counts as the named refusal;
  none shows that another delivery is refused),
  `check-responder-reply-negatives.py` (two unmodified copies accepted and sixteen changes refused,
  each at a named declaration or pin and against a message naming the change,
  every one a change to a statement or a definition and a proof-breakage check there,
  not a proof that the changed statement is false:
  seven labelled inside composing proofs and none a projection,
  the labels checked once at start-up against the three composing theorems and a syntactic form of the projection standard read off the module,
  and at run time only that each change is refused in the declaration it is labelled with,
  each also run with that proof replaced by `sorry` and required to be accepted there,
  which attributes the refusal to that proof but cannot tell a composing step from a projection (that classification is by reading) (the call claimed to return the source `establish_responder` left,
  the reply claimed wrapped as an initial message,
  sealed on the sparse chain the responder receives on,
  or under the responder's prepared ratchet key,
  and its relation claimed with the Triple unchanged,
  in `initiator_first_send_responder_replies`;
  the root-key equation claimed with the sparse root,
  in `responder_first_frame_successor_keys`;
  the receipt's call taken on the plaintext,
  in `initiator_first_send_responder_successor_keys`),
  seven on the leaf lemmas (the agreement's send at `NoHeaderReceived` claimed to emit a header message,
  the counted draw record claimed at a model state that draws,
  the reply header claimed with sparse number 0,
  the model's agreement send at `noHeaderReceived` claimed to output an epoch key,
  the headroom record claimed without its header room,
  the composite claimed with agreement type `hdr`,
  the model step claimed without its pending premise),
  one statement-shape check (the reach's call claimed to leave the byte-stream source,
  refused whatever the headline's proof does,
  which the script checks by refusing it again with that proof emptied),
  and the frame definition without its associated data with its pins kept;
  a timeout never counts as the named refusal;
  none shows that the initiator accepts the reply or that `encrypt` refuses anything),
  `check-responder-reply-receipt-negatives.py` (two unmodified copies accepted and twenty-one changes refused,
  each at a named declaration or pin and against a message naming the change,
  every one a change to a statement or a definition and a proof-breakage check there,
  not a proof that the changed statement is false:
  seven labelled inside composing proofs and four projections of called theorems' conjuncts,
  the labels checked once at start-up against the three composing theorems and a syntactic form of the projection standard read off the module,
  and at run time only that each change is refused in the declaration it is labelled with (a refusal where the proof places a conjunct of a called theorem's conclusion unchanged is a projection),
  each inside control also run with that proof replaced by `sorry` and required to be accepted there,
  which verifies attribution only (that the syntactic form is the right standard is by reading) (inside:
  the reply's bytes claimed to carry the peer key,
  the stale-key refusal claimed as `Aead`,
  the success claimed to keep the pending initial message,
  and the call claimed to take no draw,
  in `initiator_receives_reply_outcomes`;
  the plaintext claimed to be the initiator's first plaintext,
  and the named agreement claimed of the responder's draw,
  in `initiator_receives_reply_two_outcomes`;
  the freshness premise claimed against the initiator's own ratchet key,
  in `initiator_receives_reply`;
  projections:
  the decrypt claimed from the source before the first send and the stale-key arm claimed on a fresh key,
  in `initiator_receives_reply_outcomes`,
  the stale-key arm claimed on a fresh key,
  in `initiator_receives_reply_two_outcomes`,
  and the success claimed to take no draw,
  in `initiator_receives_reply`),
  eight on the leaf lemmas (the model's fresh-key receive under a premise about the sender's own key,
  the stale-key receive claimed to refuse `outOfOrder`,
  the Triple after the receipt with previous chain length 0,
  the joint model's public key made constant again,
  the fresh private key claimed read as its public key's bytes,
  the first agreement claimed with the peer key,
  the model's stale-key outcome claimed as `aead`,
  the first send's model session claimed at agreement epoch 0),
  one statement-shape check (the reach's decrypt claimed at the responder's session,
  run again with the reach run's proof emptied and still refused),
  and the receipt's model session keeping the pending initial message with its pins kept;
  a timeout never counts as the named refusal;
  none shows that `decrypt` refuses other inputs,
  a tampered reply frame included,
  or that a second message is received),
  `check-send-preservation-negatives.py` (three unmodified copies accepted,
  the bridge without and with its pins and the preservation module without them,
  and eighteen changes refused,
  each at a named declaration or pin and against a message naming the change,
  every one a change to a statement or a definition and a proof-breakage check there,
  not a proof that the changed statement is false:
  seven labelled inside composing proofs and two projections of called theorems' conjuncts,
  the labels checked once at start-up against the three composing theorems and a syntactic form of the projection standard read off the module,
  and at run time only that each change is refused in the declaration it is labelled with (a refusal where the proof places a conjunct of a called theorem's conclusion unchanged is a projection;
  every control refused in a composing proof must carry one of the two labels),
  each inside control also run with that proof replaced by `sorry` and required to be accepted there,
  which verifies attribution only (that the syntactic form is the right standard is by reading) (the no-draw premise weakened,
  the key-pair clone record swapped for the erasure one,
  the budget claimed unspent,
  and the relation after the call claimed to the model before it,
  a true statement that shows only that the proof uses the step's relation,
  in `encrypt_keeps_invariant_no_draw`;
  the budget after the reply claimed for `j + 1 < u32::MAX` and for `j + 2` further operations,
  both false,
  in `initiator_first_send_responder_reply_successor`;
  the establishment's law `DhPublicValid` swapped,
  in `established_encrypt_triple_invariant_via_preservation`),
  two labelled projections (the reply's call claimed from the source before the receipt and the session after the reply claimed to refine the model before the send,
  refused where the headline forwards the reply theorem's conjuncts),
  seven on the leaf lemmas (the sparse send's frame claimed with an agreement output,
  the budget claimed kept with no unit to spend,
  `next_chunk` claimed to change the codewords,
  the key-generation state claimed to send without a draw,
  the structural clauses claimed blind to the sparse epoch,
  `ModelTripleInv` without its roles clause,
  which shows the definition is used literally,
  and the sparse window claimed as a plain sum),
  one statement-shape check (the reply's corollary claimed at the initiator's session,
  run again with the headline's proof emptied and still refused),
  and `ModelTripleInv` regrouped with the bridge's pins kept;
  a timeout never counts as the named refusal;
  none shows that `encrypt` keeps the invariant at a state whose send draws,
  that a receive keeps it,
  or anything about a refused call),
  `check-discharge-native-decide-negatives.py` (twelve changes:
  each of the six labels with one byte changed,
  the three bounds and the `(1 : u64)` step claimed wrong,
  the export panic message claimed to fit 42 bytes,
  each refused at its own declaration,
  and `native_decide` restored under a constant's live pin,
  refused at the pin;
  plus the type comparison of `export_message_fits` with the axiom,
  held and refused with a word of the message dropped;
  start-up self-tests on both spellings of an unresolved name and on a heartbeat timeout;
  the zero-array step of `split_secret_refines`,
  unused by its proof,
  is removed),
  `check-initiator-second-message-negatives.py` (two unmodified copies accepted and eleven changes refused: seven inside the two composing proofs, three projections and one definition held by its pin),
  `check-tampered-reply-negatives.py` (two unmodified copies accepted and fifteen changes refused,
  each at a named declaration or pin and against a message naming the change,
  every one a change to a statement or a definition and a proof-breakage check there,
  seven inside the composing proof `initiator_refuses_tampered_reply` (the frame's header claimed 101 bytes,
  the reply's ciphertext claimed after 101 bytes, the premise claimed under the peer key's associated data,
  the freshness premise claimed against the initiator's own key, the uniqueness law replaced by the round trip,
  the refusal claimed to take no draw, the refusal claimed as the stale-key refusal),
  each also accepted there with that proof replaced by `sorry`;
  six on the leaf lemmas and two definitions held by their pins;
  start-up self-tests on the guard's spellings, on a heartbeat timeout and on the labels),
  `check-initiator-second-send-negatives.py` (two unmodified copies accepted and sixteen changes refused,
  each at a named declaration or pin and against a message naming the change,
  every one a change to a statement or a definition and a proof-breakage check there,
  not a proof that the changed statement is false:
  six labelled inside the composing proof `initiator_second_send_after_reply` and one a projection of a called theorem's conjunct,
  the labels checked once at start-up against a syntactic form of the projection standard read off the module,
  and at run time only that each change is refused at its labelled place (a refusal where the proof places a conjunct of a called theorem's conclusion unchanged is a projection;
  every control refused in the composing proof must carry one of the two labels),
  each inside control also run with that proof replaced by `sorry` and required to be accepted there,
  which verifies attribution only (that the syntactic form is the right standard is by reading) (inside:
  the model's second step claimed to take a draw,
  the call claimed to leave the source before the receipt,
  the second frame claimed at chunk index 0 or sealed on the sparse chain the initiator receives on,
  the relation after the call claimed with the receipt's Triple or with the header encoder not advanced;
  the projection:
  the session after the call claimed to keep the first send's pending initial message,
  refused where the pending conjunct of `initiator_receives_reply` is placed unchanged against the goal the walk's frame equation rewrote,
  a structural refusal),
  eight on the leaf lemmas (the agreement's send at `KeysSampled` claimed to change the source or to keep the encoder,
  the providers claimed at a model agreement whose send draws,
  the counted draw record claimed with an exhausted encoder,
  the second header claimed with previous chain length 0 or sparse number 1,
  the model's second step claimed to keep the encoder,
  the first send's model encoder claimed at position 0),
  no statement-shape check (no reach),
  and the second frame without its associated data with its pins kept;
  a timeout never counts as the named refusal;
  none shows that `Session::invariant` or the ceilings hold at the session the receipt returns,
  that the responder receives the frame,
  or that `encrypt` refuses elsewhere) and `check-port-negatives.sh` (ten broken anchors,
  as in the row above).
  The number of controls of each class (inside, projection, statement-shape, pin, leaf) and of baseline copies in each lifecycle negatives script that carries the shared `check_labels` (`check-responder-successor-negatives.py`,
  `check-responder-reply-negatives.py`,
  `check-responder-reply-receipt-negatives.py`,
  `check-send-preservation-negatives.py`,
  `check-initiator-second-send-negatives.py` and the scripts added after them,
  all of which the record must list) is recorded in `tacenta-proofs/scripts/negatives-control-counts.json` and compared by `check-negatives-control-counts.py` (`checks_43`),
  which also holds their copies of the shared helpers to one text,
  so a control deleted with its label is refused unless the record is edited in the same change;
  their label check refuses a projection any place of whose refusal is not a composing theorem.
  `run-check-negatives-control-counts-cases.sh` holds both:
  twelve planted record and script changes refused, the same deletion with the record edited accepted, and the projection-place fault refused in each script whose record counts a projection (the runner names the scripts it copies and refuses a list that differs from the record's).
  Each script's `main` calls the shared `check_complete`,
  which refuses a run that refused fewer controls than `MUTANTS` holds,
  accepted other baselines,
  skipped an emptied-proof run or a projection's record,
  or whose Lean runs,
  recorded by `run_lean` alone in `RUNS`,
  do not number one per baseline,
  control and emptied-proof run,
  at least one accepting per baseline and one refusing per control and statement-shape check;
  the gate requires that call as a statement of `main`, no `return` or exit in `main`, the run ended by `sys.exit(main())`, each shared helper bound once at the top level (compared from its decorators; any other binding, `global`, import, parameter or use of `globals`, `setattr`, `exec` and the like refused), and any script that defines, imports or reads `check_labels` in the record.
  Its cases add seven ways around the one-text check, three spellings of one more script, six `main` shapes that skip the completeness check, and the completeness check itself on whole and incomplete runs of each script.
  The gate holds the scaffold's negatives template (`tacenta-proofs/scripts/templates/lifecycle-negatives.py.in`) to the same shared text and reads its `main` by the same rules, without counting it;
  its cases refuse a template helper changed, a template `main` without the completeness call or the projection record, a template that rebinds a name through `globals()`, and the template missing (97 cases in all, the completeness check run on simulated results with no Lean).
  The gate also refuses a second binding of `main`,
  `MUTANTS`,
  `INSIDE`,
  `PROJECTION`,
  `STATEMENT_SHAPE`,
  `COMPOSING` or `PROJECTED`, any `global` or `nonlocal`, a `raise` in `main` other than `SystemExit(<a message>)`, an assignment or `del` through an attribute or subscript of a module-level name, an in-place method call on one, and a `main` that does not record `inside`,
  `projection_of` and `projects`.
  Anywhere in a script it refuses a `SystemExit` not raised directly with one argument written as a message (a string, an f-string or a `+` with one; how the argument is written is read, not its value),
  and any use, import under any name or binding of `exit`,
  `quit`,
  `_exit`,
  `abort`,
  `kill`,
  `killpg`,
  the `exec*`,
  `spawn*` and `posix_spawn*` calls,
  `fork` or `forkpty` other than the texts `sys.exit(main())` and `os.killpg(process.pid, signal.SIGTERM)`, accepted wherever they are written;
  `main` must bind `sources` once and only read it.
  Seven cases hold these: an arithmetic `SystemExit` argument, `exit` imported under another name, a helper that raises or calls an exit, an exit reached through `ctypes`, a baseline skipped with `sources` narrowed to match, and a baseline deleted from `sources`.
  The rules on the scripts' text are a tripwire for the spellings listed, not a check of what a run does; they stop accidents and the edits listed, not a deliberate edit.
  Not seen, by class: a decorator or wrapper around `main` or a helper that catches `SystemExit` and returns, so that a refused control or `check_complete`'s refusal ends the run with status 0;
  a key written twice in the `sources` literal, which the gate counts twice and the run once;
  operator overloading and other dunder methods (an operand whose `__radd__` turns the message into a number);
  reflection through names not listed (`operator.attrgetter`, `__getattribute__`, `__subclasses__`);
  another module the script imports;
  any other way of ending the run with status 0;
  the same change to every copy of a shared helper, which is one text;
  and a `main` that runs Lean the expected number of times on other files and reports refusals it did not see.

  **Missing evidence:**
  None identified beyond the number of mutations each holds;
  for the refuted records, a theorem added to the gate's recorded block is caught by review of the diff, not by a gate, and a restatement of the `def` record's body is not a mention.

- **Gate/check:**
  `tacenta-proofs/scripts/check-lean-constructs.sh`,
  `check-audit-reach.sh`,
  `check-translation-coverage.sh`, the `sorry` scan in `no-sorry.sh`,
  `verify.sh`

  **Protected property:**
  Hand-written Lean declares no axiom, opaque,
  `implemented_by`,
  `extern`,
  `partial` or `unsafe` name, and no elaboration-time code outside the seven audit invocations, each exact and standing alone, with nothing in the invoking modules but imports, pins and the invocation, one per line, and none of the text found at review to redirect, wrap, forge or hide around them;
  a textual guard on instances and coercions, since Lean prints neither the instance behind a notation nor the function behind a coercion in a statement pin:
  an `instance` declaration whose whole text (to the next blank line or line at column 0) is not one of those listed for its file and namespace (fourteen today: eleven `instance` and three `deriving instance`,
  each exactly once,
  so a copy elsewhere or a changed continuation line is refused,
  while lines may move),
  a `deriving instance` for a type whose name, as written, the file does not give one of its own declarations (compared as written, with no namespace resolution, so another file's type written by a short name the file also declares is accepted),
  an attribute list `@[...]` or `attribute [...]`,
  read on the whole file so a list split over lines is one,
  naming `instance`,
  `default_instance` or `coe`, and the `coe` and `default_instance` tokens anywhere in code;
  it does not see a dependency's scoped instance brought in by `open`, a `deriving` clause of a `structure`, `inductive` or `def`, or a class whose parent is a notation class;
  every first-party module is in the audit's import closure;
  every translation module built;
  no incomplete declaration.

  **Current negative-control evidence:**
  `tooling/tests/run-lean-constructs-cases.sh` (93 cases on a copy of the audit modules:
  instance declarations,
  `local`,
  `scoped`,
  after `open … in` and with a priority,
  instance,
  `default_instance` and `coe` attributes on one line and split over two,
  the bare tokens,
  a derived instance for another file's type and the coercion counterexample from review in the held-encoder module,
  refused;
  a derived instance of a type the file declares accepted;
  an allow-listed instance changed on its first or a continuation line,
  copied into another namespace,
  copied twice,
  moved to another namespace or with a changed default,
  refused,
  and one moved down a line accepted;
  a wrapper before an invocation,
  an indented invocation,
  a continuation,
  declaration or pin after one,
  narrowed prefixes,
  a deleted invocation,
  a notation on the audit's name,
  the `Lean` namespace by `_root_` and in guillemets,
  a `namespace`,
  `open`,
  declaration or second command on a line in an audit module,
  the audit's log tag in a string,
  a printed string,
  `#reduce`,
  `dbg_trace`,
  an interpolated string,
  an interpolating message head,
  a bang macro,
  a changed lakefile,
  in the audit a string literal holding a brace,
  spellings the stripper once misread (`/--/`,
  `/--` inside a comment,
  `/-/- -/`,
  a char literal or raw string after `!` or `λ`) hiding code,
  a literal straight after a token refused as ambiguous,
  and a literal or comment opener after a non-space refused as adjacent,
  each refused),
  `check-lean-constructs.sh` has 5 refusals and 2 acceptances inside `check-attest-negatives.sh` (run in CI as sixteen slices, `negatives_slice`, and combined by `negatives_combine`).
  `check-audit-reach.sh` now has `check-audit-reach-negatives.sh` (an orphan module in each source directory, a dropped import, a deleted audit module and five wrong audit calls; `AR-*` re-run red), and `check-translation-coverage.sh`, the log scan, the no-audit-lines guard, the kernel-replay verdict,
  `verify.sh` and the call of every control script from `no-sorry.sh` are held by `tooling/tests/run-proof-script-cases.sh` (116 cases with a stubbed `lake`; `NS-*`, `VF-*`, `TC-*` re-run red).
  `check-pin-negatives.sh` shows Lean refusing a changed `#guard_msgs` pin.
  The first and the last run in CI through `no-sorry.sh`;
  the runners run in CI from `tooling/tests/run-gate-controls.sh` (`checks_41`).
  In the public workflow `no-sorry.sh` runs in parts (`translation-part`,
  one part of `tacenta-proofs/scripts/no-sorry-parts.txt` per job,
  each running the three package builds and scans and its own phases) and the `translation` job prints the script's final line only when the parts are exactly those of the partition,
  of the commit under test,
  script and parts file,
  from a clean checkout,
  on one toolchain and one restored build cache,
  all passed,
  and together run every phase once and every control of `check-initial-dispatch-negatives.py`,
  split eight ways,
  once;
  a phase the script gains and the parts file does not assign fails every part and the combiner.
  `tooling/tests/run-no-sorry-parts-cases.sh` (`checks_41`) holds that combiner to its refusals on stubbed phases (a part missing,
  repeated,
  relabelled,
  of another partition,
  commit,
  tree,
  script,
  parts file,
  cache,
  toolchain or checkout,
  failed,
  cut short or with a failure line,
  a dispatcher slice that selected or recorded other controls,
  a phase in no part or two,
  a test seam) and resolves every committed part against the real script;
  `NP-*`,
  `DS-slice` and the part-mode `NS-*` edits are its mutations.
  The `translation` job runs `always()` and is designed to fail at its first step unless every part succeeded;
  the workflow checker's controls confirm that shape, and the matrix has not yet run on GitHub.
  Each part writes its own manifest and log;
  the combiner checks the log for consistency with the manifest (its closing lines and statuses, no `::error::` or `WRONG` line), not that it is that run's log, so a part directory made to look right by something other than the script is not detected;
  the hosted run of the matrix and the combiner is not checked by any local control.
  The `translation` receipt records the guard and the combiner only:
  the elan install, the Mathlib fetch and the self-hosted clone from local mirrors run in each part and are in no receipt or manifest;
  a failed one fails its part, which the guard refuses.
  `no-sorry.sh` refuses, in every mode, the test seams of its phases' scripts (`REFUTED_RECORDS_BIN`, `BRAIDNEG_FILTER`, `HYPWIT_ROOT`).

  **Missing evidence:**
  The construct scan reads text with a stripper, not Lean's lexer:
  eighteen hostile reads each found a spelling it misread, each now a case;
  the remaining defence is that a literal or comment opener must follow whitespace, an opening bracket or a comma, that a `'`/`r"` reading may not depend on the character before it, and that no scanned or pinned file holds a carriage return or a NUL (both stripper copies refuse one before reading).
  `tooling/check-precondition-shapes.py` carries a third stripper copy without these rules (it guards a tripwire that disclaims completeness).

- **Gate/check:**
  `assemble-triple-unit.sh`,
  `assemble-braid-unit.sh`,
  `assemble-session-unit.sh` and nine `port-*.sh` scripts, each with `--check` (steps `checks_14` to `checks_24`)

  **Protected property:**
  A generated unit crate, and its ported proofs, are what their sources produce.

  **Current negative-control evidence:**
  None retained.
  `translation-attestation.json` pins the hash of the three assemble scripts, so `attest.py --check` refuses an edit to one;
  the nine port scripts are not pinned.
  A hand edit to a triple unit file, to a session unit file and to `UnitT1.lean` was each refused.

  **Missing evidence:**
  A case for each of the twelve `--check` modes.

- **Gate/check:**
  `tacenta-proofs/scripts/check-hypothesis-witnesses.sh` (run by `no-sorry.sh`)

  **Protected property:**
  Every closed hypothesis of a claimed T1 or T3 theorem of the leaf crates and the three-leaf unit is connected to a bridge to a satisfiable shape, to a derivation the ledger names, or to `True`;
  no such theorem takes a closed hypothesis that names no predicate or quantifies over a variable only hypotheses mention;
  at least 109 leaf and 31 unit theorems are selected.

  **Current negative-control evidence:**
  `tacenta-proofs/scripts/check-hypothesis-witnesses-negatives.sh`:
  a control and seven cases in a copy of the package:
  one case adds six dead hypotheses to claimed theorems (one that names no predicate,
  an orphan variable,
  a predicate bridged to itself,
  one whose shape no function satisfies,
  two predicates bridged to each other,
  one behind an alias of a defined function),
  then a deleted bridge,
  a deleted law bridge,
  a deleted existence theorem,
  a derivation with a dead hypothesis,
  removed ledger entries and a reworded section heading.
  Run by hand;
  no workflow runs it.

  **Missing evidence:**
  Retained evidence of a run in CI.
  Joint satisfiability of the hypotheses of one theorem;
  that an existence theorem proves satisfiability (it is recognised by its shape);
  the Session unit;
  a dead hypothesis with a free variable that mentions real state.

- **Gate/check:**
  `assemble-triple-unit.sh`,
  `assemble-braid-unit.sh`,
  `assemble-session-unit.sh` and eight `port-*.sh` scripts, each with `--check` (steps `checks_14` to `checks_24`)

  **Protected property:**
  A generated unit crate, and its ported proofs, are what their sources produce.

  **Current negative-control evidence:**
  `tacenta-proofs/scripts/check-generation-negatives.sh` (132 cases):
  a hand edit to every tracked file of the three units, an extra and a missing unit file, a stale source and, for the port scripts, a rewrite target written once more, for all eleven `--check` modes;
  and at write time an unknown argument, a rewrite target counted wrongly, a leaf the triple and braid assemblers cannot read and a lifecycle root without its re-export (`GN-*`, `GA-*` re-run red).
  The assemblers' comparison of the stripped copy with the leaf and their check of where the inserted `use` landed are held by no case (`GA-*-diffq`, `GA-*-late`).
  It is in the tree and is not yet a CI step.
  `translation-attestation.json` pins the hash of the three assemble scripts, so `attest.py --check` refuses an edit to one;
  the eight port scripts are not pinned.
  The cases found that eight port scripts never printed their summary line after a difference (a `diff | head` under `pipefail` ended the script first);
  fixed.

  **Missing evidence:**
  A CI step for the control.

- **Gate/check:**
  `tooling/check_authentication_boundary.py`,
  `tooling/check-proof-hygiene.sh`,
  `tooling/check-conflict-markers.sh` (steps `checks_29`, `checks_08`, `checks_09`)

  **Protected property:**
  Every receive path is registered under its signature, in six zones,
  `tacenta-core/src/sessions` among them since identity records;
  no hand-written proof names a generated `_proof_<n>` constant;
  no tracked file holds a conflict marker.

  **Current negative-control evidence:**
  `tooling/tests/run-source-gate-cases.sh` (26 cases):
  each marker kind, a marker in a new file and the three shapes the gate lets through;
  a planted `_proof_<n>` name in code, before a comment, in a new hand-written file, and the exempt comment and generated file;
  and for the registry a new receive path,
  `const fn`, a private method, code after a test module, a `#[cfg(test)]` in a comment, shape drift, a stale and a removed and a doubled row, unbalanced braces and a doubly declared function (`CM*`, `PH*`, `AB*` re-run red).
  It is in the tree and is not yet a CI step.

  **Missing evidence:**
  A CI step for the runner.

- **Gate/check:**
  Vector currency (`proofs_vectors`, inline in `ci.yml`) and the differential harness's required-input rule (`differential.rs:4817`)

  **Protected property:**
  The committed vectors equal the model's output, and the four hosted-inventory files equal what their own generator produces;
  the harness fails, and does not skip, in CI when the model binary is missing.

  **Current negative-control evidence:**
  `tooling/check-vectors-current.sh` is the workflow's inline step as a script,
  with `tooling/tests/run-check-vectors-current-cases.sh` (a committed vector,
  a changed initiator vector and a changed inventory vector,
  each by one hex digit,
  are refused,
  naming their file;
  `VC1` to `VC6` re-run red),
  and `tooling/tests/run-differential-required-input-cases.sh` shows the harness failing with the model executable missing when the variable or `GITHUB_ACTIONS` requires it and skipping otherwise (`DF1` to `DF3`).
  Neither is a CI step yet, and the workflow's step does not yet call the script.
  A committed vector that the model no longer generates stays in the tree, because the regeneration overwrites and never deletes.

  **Missing evidence:**
  The CI wiring;
  a case that the harness ran at least once.

- **Gate/check:**
  `rust_spqr_erasure` (`ci.yml:98-100`)

  **Protected property:**
  The SPQR secret-erasure regression runs through the public Session API.

  **Current negative-control evidence:**
  The test file holds a built-in mutation-sensitivity test (`direct_spqr_retirement_wipe_is_mutation_sensitive`).
  With the feature it runs 3 tests (53 s; 62 s on a loaded machine).

  **Missing evidence:**
  `tacenta-core/tests/spqr_erasure_public.rs` is `#![cfg(feature = "private-erasure-review")]` and the test has no `required-features`, so `cargo test --test spqr_erasure_public` without `--features` prints "running 0 tests ...
  ok".
  Only `tooling/required-steps.json` keeps the flag in the command.

- **Gate/check:**
  `tooling/mutate-inventory.py`

  **Protected property:**
  The hosted-inventory acceptance boundary (`tacenta-core/src/groups/inventory.rs`) is held by its tests, one edit at a time.

  **Current negative-control evidence:**
  124 mutants, of which 8 are claimed equivalent.
  Its docstring (line 24) says "Nothing here runs in CI".
  It passes locally:
  116 killed, 8 survived as claimed, 0 unexpected (141 s).

  **Missing evidence:**
  It is a local control.
  Run it, or record why it is not run, at the candidate.

- **Gate/check:**
  `tacenta-proofs/scripts/check-precondition-witnesses.sh` (the `translation-part` jobs through `no-sorry.sh`, combined by the `translation` job)

  **Protected property:**
  The numeric-precondition witnesses (`Translation/NumericWitness*.lean`) and discharge theorems (`Translation/*DecodedStateDischarge.lean`) state their theorems' own premises:
  a premise added to or changed in a witnessed theorem is refused until it is classified, and an `*_at_witness` theorem left at a function type (what a premise added after the last argument of a discharge theorem leaves) or missing from the script's list is refused.

  **Current negative-control evidence:**
  36 cases in the script, run 2026-10-01 after the review round:
  the three witness modules,
  the two discharge modules,
  the two lists of `*_at_witness` theorems and three toy theorems accepted,
  then 26 single changes refused for the stated reason (a weakened statement,
  a deleted witness,
  a witness that proves `True`,
  a statement or a row removed,
  a premise unclassified,
  listed as outside or invented,
  a discharge theorem's conclusion or given premise changed,
  a toy theorem that gains a numeric or a non-numeric premise,
  an `*_at_witness` theorem at a function type or not listed,
  a `sat_` theorem no row accounts for).

  **Missing evidence:**
  A hypothesis is classified as numeric by its propositional skeleton or by a list of state predicate names, so a numeric bound behind a definition whose name is not on that list is classified by hand.
  It does not check that a `boundary` or `unwitnessed` classification is right, that a witness state is reachable, or that a theorem outside the table is witnessed;
  it does not tie the state a `sat_` proof uses to the state the invariant theorems are about.
  The statements of the 61 shape theorems (`NumericShapeWitness.lean`) are held by `#guard_msgs in #check` pins in the build;
  `attest.py` requires each pin to exist (`REQUIRED_STATEMENT_PINS`) and reads what it says only to refuse a cut-off `⋯`.
  No hosted run is recorded.

<!-- End of the list. -->

### Where the negative controls run (2026-09-30, at `dea57eaf`)

This records evidence for gate 4. It is not a verdict that gate 4 passes or fails. The grouping is by script or by group of CI steps with one purpose; "partial" means the control exists and a single edit to the gate survived it in a mutation run made for this assessment (59 single edits across the gates; the record is [GATE-MUTATION-RECORD.md](tacenta-proofs/GATE-MUTATION-RECORD.md)).

**Gates whose negative control runs in CI (nineteen groups).**

1. `check-workflows.sh` and `required-steps.json`: `run-check-workflows-cases.sh`. Partial: the rule that CI fails when PyYAML is missing has no case.
2. `check-actionlint.sh`: `run-check-actionlint-cases.sh`, which was not run locally for this assessment and passed in the hosted `checks` job (`checks_06`) for `dea57eaf`.
3. `check-constant-time-asm.sh`: `run-check-constant-time-asm-cases.sh`. Partial: three cases on the callee allow-list only; five edits to the rest survived.
4. `check-lifecycle-boundary-surface.py`, 5. `check-precondition-shapes.py`, 6. `check-labels.sh`, 7. `check-traceability.py`, 8. `check-vectors.py`, 9. `check-session-operation-traces.py`: each has a case runner in the `checks` job.
10. The receipt writer, collector and validator. Each commit and tree comparison, per receipt and per document, has a case of its own.
11. `build-assurance-manifest.py`. Each check of `--validate` and the dirty-tree refusals have cases.
12. `check-signoff.sh`. Partial: three of five single edits survived, and the push-mode step has no control.
13. `build-evidence-pack.py` (with its git authentication and `publish-evidence-archive.py`, `reproduce-evidence.py`), 14. `check-ledger-review-receipt.py` (with `ledger-review-sections.py` and `validate-reviewed-evidence.py`), 15. `attest.py --check`, 16. `check-lean-constructs.sh`, 17. `Model.AxiomAudit`, 18. the lifecycle translation coverage, Session witness coverage and initial-dispatch guards, and 19. the independent reader's skip gate, sweep and operation controls.

**A control that runs only locally.** `tooling/mutate-inventory.py`, for `tacenta-core/src/groups/inventory.rs` (124 mutants). Its own docstring says nothing in it runs in CI. The three calibration controls of the timing harness (`control_the_harness_detects_*` in `tacenta-core/tests/timing.rs`) are `#[ignore]`d and run only by hand. `tooling/miri.sh` is run by no workflow in this tree, and `tooling/fuzz-smoke.sh` only by `tooling/ci.sh` when `cargo-fuzz` and a nightly toolchain are present; neither has a negative control listed here. `tacenta-proofs/scripts/check-hypothesis-witnesses-negatives.sh`, the control for `check-hypothesis-witnesses.sh`, needs the built translation package and rebuilds a copy of it for each of its mutating cases; it is run by no workflow.
**A control that runs only locally.** `tooling/mutate-evidence-gates.py` makes 121 single edits that remove or weaken a check of the receipt, manifest, pack, publisher, reproduction and review tooling and requires a case runner to fail for each. A case that accepts a wrong input or misbehaves sees 103 of them; 17 are seen only as a changed message and one is not seen, and the harness lists those 18 as unable to change a verdict, each with its reason, which is by reading and is not proved. Nothing in CI runs it. `tooling/mutate-inventory.py`, for `tacenta-core/src/groups/inventory.rs` (124 mutants). Its own docstring says nothing in it runs in CI. The three calibration controls of the timing harness (`control_the_harness_detects_*` in `tacenta-core/tests/timing.rs`) are `#[ignore]`d and run only by hand. `tooling/miri.sh` is run by no workflow in this tree, and `tooling/fuzz-smoke.sh` only by `tooling/ci.sh` when `cargo-fuzz` and a nightly toolchain are present; neither has a negative control listed here.

**Gates with no retained negative control.** `check-conflict-markers.sh`, `check-proof-hygiene.sh` and `check_authentication_boundary.py`; the twelve `--check` modes of the assemble and port scripts, except that the unit edits of the three Session Braid ports are held by `check-port-negatives.sh` (ten broken anchors: seven refused naming a unit edit and three, for the preservation port, refused for a substitution count, for the pin-section marker and for a declaration after the pins); `check-audit-reach.sh`, `check-translation-coverage.sh`, the log scan in `no-sorry.sh`, the calls of the control scripts inside `no-sorry.sh` and the `sorry` grep in `verify.sh`; the vector-currency step, the differential harness's required-input rule and the test count of `rust_spqr_erasure`; the archive digest checks of `install-elan.sh` (skipped when `~/.elan` already holds the pinned release, as on the self-hosted runner) and `install-actionlint.sh`, and the pinned-revision check of `seed-lake-packages.sh`, which leaves an existing dependency directory to Lake; and the skip-or-fail rules of `tooling/ci.sh`, which CI does not run. `cargo fmt`, `clippy`, `test`, `audit` and the MSRV and armv7 checks are tool exit statuses with no control of their own.

**When an input is absent.** The differential harness and `check-workflows.sh` skip and pass locally and fail in CI when what they need is missing. `check-constant-time-asm.sh` fails in CI only with no Linux target at all, which cannot happen on a GitHub-hosted runner (its host is x86_64 Linux), so a missing aarch64 target is skipped with a printed line there too; the `rust_target` step is what installs it. Only `check-signoff.sh` (missing base) and the collector (missing receipts) have a case that shows a failure.

### Update after the gate-4 pass (2026-10-01)

The inventory table above was written by hand and drifted. [GATE-INVENTORY.md](tacenta-proofs/GATE-INVENTORY.md) is the
exact list and is generated: `python3 tooling/gate-inventory.py --write` makes one row per gate (a script, a CI step or a Lean
check) from `tooling/gate-inventory.json`, `tooling/required-steps.json` and `tooling/gate-mutations.json`, and `--check` fails when
the file is stale, when a control marked local is run by a CI step, or when a step of the required workflow that runs a command is
claimed by no row (a step without an id included, and a step that runs a listed script beside an unlisted one is not claimed). A control
"runs in CI" there when a CI step runs it, directly or through a script that one runs. It says what exists. Whether a control fails when
it should is the Mutations column: `tooling/mutate-gates.py` applies each of 208 single edits in `tooling/gate-mutations.json` to a
disposable worktree and requires the named control to fail with the diagnostic the edit should trip, then says what the failing case saw.
In the run of the 204 edits that [GATE-MUTATION-RECORD.md](tacenta-proofs/GATE-MUTATION-RECORD.md) records, it saw the gate accept a wrong
input (136 edits), another wrong verdict, an honest input refused or a count or a call wrong (53), or only a changed message. A changed
message is listed with its reason or fails the run; 11 edits are listed as equivalent (their verdict cannot change) and 4 as uncovered (a
known gap). The four edits added since delete or swallow the calls of the two proof controls the session contract integration added to
`no-sorry.sh`; they were run with the other `no-sorry.sh` edits (`--only`), and each was seen as accepted or as another wrong verdict. `--guards FILE... --verdict` removes each
failure guard of a gate in turn and reports the guards whose removal no control notices, and those whose removal changes only a diagnostic. In the
tree as committed the inventory has 92 rows: 77 with a control in CI, 3 with a control that runs only locally and 12 with none.

What the pass added, by where it runs.

- Already CI steps, because a CI step runs the runner that was extended: `run-check-signoff-cases.sh`, `run-check-constant-time-asm-cases.sh`,
  `run-check-workflows-cases.sh`, `run-build-assurance-manifest-cases.sh`, `run-collect-assurance-receipts-cases.sh`, `run-check-labels-cases.sh`,
  `run-check-ledger-review-receipt-cases.sh`, `run-check-lifecycle-boundary-surface-cases.sh`, `run-check-precondition-shapes-cases.sh` and
  `check-lifecycle-translation-coverage-negatives.sh`.
- Already in CI through `no-sorry.sh` (the translation job), which now calls them: `check-audit-reach-negatives.sh`, `check-pin-negatives.sh` and
  `check-kernel-replay-negative.sh`.
- CI steps of their own: `tooling/tests/run-gate-controls.sh` (step `checks_41`: the source-gate, proof-script, installer, evidence-pack build and
  generation controls, the cases of the fast local check (`tooling/fast.sh`), the controls of the inventory generator and of the mutation harness, the controls of the tooling for new proof modules and merges (below), and the inventory check),
  `tooling/tests/run-differential-required-input-cases.sh` (step `vectors_differential_cases`), and `tooling/check-vectors-current.sh` with its control
  `tooling/tests/run-check-vectors-current-cases.sh` (steps `proofs_vectors` and `proofs_vectors_control`).

Gates that still have no control, and why: `tooling/validate-reviewed-evidence.py` and `tooling/publish-evidence-archive.py` (they bind a real pack and a
bucket; cases belong with the candidate's pack); `tooling/ci.sh` (CI does not run it, and its skip-or-fail rules need each tool stubbed away); the tool
exit statuses (`cargo fmt`, `clippy`, `test`, `audit`, the MSRV and armv7 checks), whose control would test the tool; `tooling/miri.sh` and
`tooling/fuzz-smoke.sh` (not CI gates); the wrapper `check-generated-files.sh` (not run by CI; `attest.py --check` runs the same function and is held).
Controls that exist and run only locally: `tooling/mutate-inventory.py` and the three `#[ignore]`d timing controls. The test count of
`rust_spqr_erasure` is held only by the workflow command: a `required-features` entry in `tacenta-core/Cargo.toml` would make a run without the feature
fail, but that manifest is a hashed input of the translation attestation, so the change belongs with the next regeneration on the pinned toolchain.

What is not refused by any gate. Removing the inventory check from `run-gate-controls.sh`, or the `checks_41` step with its entry in
`tooling/required-steps.json`, is not refused by any gate; the diff of `GATE-INVENTORY.md` is the only trace. A pin rewritten as `#guard_msgs (drop info) in`
with its docstring deleted passes Lean and, once the manifests are regenerated, `attest.py`; the manifest diff is the only trace.

### Tooling for new proof modules and merges (2026-10-21)

Eight tools and their controls were added, each a row of [GATE-INVENTORY.md](tacenta-proofs/GATE-INVENTORY.md)
with mutations in `tooling/gate-mutations.json`, and their controls run in step `checks_41` through
`tooling/tests/run-gate-controls.sh`: the module scaffold and pin generator
(`tacenta-proofs/scripts/new-lifecycle-module.py`, `genpins.py`; `run-new-lifecycle-module-cases.sh`), the
one-entry-per-line form of the shared lists (`tooling/reflow-shared-lists.py`, whose `--check` also runs there;
the long tables of this file are lists for that reason), the preflight of a lifecycle module
(`tooling/check-proof-module-preflight.py`, also run on every lifecycle module against the baseline of findings
known when it was introduced, `tooling/proof-module-preflight-baseline.json`, in a step of its own, `checks_42`,
and in `tooling/ci.sh`, failing on errors only), the regeneration of generated files
after a merge (`tooling/regenerate-generated.sh`, with the resolver of insertion conflicts it runs first,
`tooling/resolve-insertion-conflicts.py`), the merge-exactness check (`tooling/check-merge-exactness.sh`) and the
check that a merge or a rebase kept what this tooling added (`tooling/check-landing.sh`). They change no claim and no gate's verdict on the proofs. The same change also corrects one count in
`tacenta-proofs/CLAIMS.md` (the restored-session section's kernel-only results, 68, which left out
`export_message_fits`, to 69), says which results the retry-loop section's "other 32" counts (its other pins less two that the
next section describes), and adds one item to the not-shown lists of two module docstrings
(`UnitLifecycleEstablishedEncrypt`: a random source with no state of its own; `UnitLifecycleResponderFirstFrame`:
the model's `establishResponder` equality), all found by the preflight; those edits need the rule-7 read.
Their controls stub
Lean: that the pin generator's probe matches a real `lake env lean --json` run was checked by hand, not in CI.
`run-gate-controls.sh` runs every control through `tooling/tests/with-no-git-identity.sh`, with no global or
system git configuration and no git identity, as the hosted runner has none, so a fixture that commits without
its own identity fails on a developer's machine too (one did, and failed only on the runner).

On 2026-10-22 the scaffold was brought up to what a module it starts needs to pass the gates. Its negatives
template carries the helpers of the lifecycle negatives scripts character for character (the projection
standard and labels, the guard's self-test of each of its six error spellings, `RUNS` and `check_complete`), and
`check-negatives-control-counts.py` (step `checks_43`) holds the template to them and reads its `main` by the same
rules, without counting it. `scaffold` also writes the new script's entry in `negatives-control-counts.json` with
the script's own counts, its name among the scripts `run-check-negatives-control-counts-cases.sh` copies (a list that
must equal the record's), its stub in `tooling/tests/run-no-sorry-parts-cases.sh` (which now reads the phase count
of a full run from its fixture's `no-sorry.sh` instead of a number written by hand, and names the edit when a script
the run calls has no stub; a phase dropped from both `no-sorry.sh` and the parts file is therefore no longer caught
there, and is caught by `tooling/tests/run-proof-script-cases.sh`, whose honest run lists every stubbed script
`no-sorry.sh` must call and requires the success line of the real `check-translation-coverage.sh`, the one phase
script it does not stub), and the two pretty-printer options in the module, so that its pins print whole. The
lists it now edits, the names the count gate's case runner copies among them, are among the files
`tooling/resolve-insertion-conflicts.py` resolves, so two branches that each
scaffold a module still merge through `tooling/regenerate-generated.sh`. `tooling/mutate-gates.py` gives each worktree a Cargo target directory of its
own: run with a `CARGO_TARGET_DIR` shared with a checkout, it had left the last edit's build there, and a later
`cargo test` in the clean checkout ran the mutated library. The controls stub Lean as before; one generated script,
given two controls of the send-preservation module, was run against Lean by hand.

Two gates of that change failed a second hostile read for the same reason, respellings of the shapes they name: the
control-count gate's rules for `main` (`checks_43`) and the quiet-grep gate (`checks_44`). Both are kept, and are
described as textual tripwires for the shapes listed, each with the classes it does not see. Recorded as decisions,
**not built**: (1) a check of what each lifecycle negatives run produced, comparing its `result.json` (the baselines
accepted and the controls refused, by class) with `tacenta-proofs/scripts/negatives-control-counts.json`, which would
refuse a run wrapped so that its refusals exit 0 and a baseline hidden behind a duplicated key; (2) a quiet-grep gate
that reads the shell through a parser (for example `shfmt --tojson`) and so sees the real pipelines and command words
instead of a tokenizer's reading of them.

## Next P1 slices

1. Decide whether `GAP-REGISTER.md` should remain Markdown-only or gain a
   machine-readable sidecar before P2 indexes evidence against gap IDs.
2. Add target/scope decision records for any deferred item that is intended not
   to block gate 1.
