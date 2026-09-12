# Assurance obligation inventory

Current inventory for P1 of the assurance execution plan. This file makes the
remaining readiness work assessable; it is not evidence that the work is done.

Last assessed: 2026-09-12, at `96890d3a07dfa3fa0d0b6b00e5f9e4a6a82485a8`.

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
| P4 | Persistence coverage fixtures | BLOCKING for prekey-store/session persisted-format target raises to L2. |
| P5 | Stored-format differential checks | BLOCKING for differential-testing phase 3 once P4 baselines and P3 decisions exist. |
| P6 | Session/prekey operation model and L2 evidence | BLOCKING for the session orchestration/prekey-store component target. |
| P7 | Remaining proof/vector target obligations | BLOCKING where a component remains below its target; discovery starts before P4/P5 complete. |
| P8 | Validated types and explicit phases | NONBLOCKING unless P1/P6 identifies a target deficit that requires it. |
| P9 | Reproducible gate evidence and final review pack | BLOCKING final assembly after the other packages settle. |

## Component obligations

| Component or gate | Current target deficit | Gate class | Package | Closure evidence |
| --- | --- | --- | --- | --- |
| Sparse post-quantum ratchet | Component table says L3/L4 with partial vectors while target is L4. The exact missing scoped vector/proof obligations are not yet enumerated. | AMBIGUOUS | P7 | Inventory of specified operations/invariants, added evidence or target/scope decision for each deficit. |
| ML-KEM Braid | Component table says L3/L4 with no MAC or state-machine vectors while target is L4. Delegated KEM layout is already a scoped exception, not universal vector work. | AMBIGUOUS | P7 | Separate MAC, operation/state-machine and delegated-layout obligations; one feasible transition result before final estimate. |
| Erasure code | Component table says L3 while target is L4; full decoder refinement is deferred but no decision lowers the target. | BLOCKING | P7 | `DecoderRefines` design note, representative rejection-preservation lemma, then either full L4 evidence or recorded target decision. |
| Session orchestration and prekey store | Component table says L1 while target is L2 by recorded decision. Stored-format modelling alone does not model operations. | BLOCKING | P6 | Operation inventory, abstraction contract, model-generated scenarios, concrete Rust execution and reader coverage for agreed L2 surface. |
| Persisted formats: prekey store | Component table says L1 while target is L2; gaps remain for signature rule, older versions and `previous_kem`. | BLOCKING | P4/P5 | Reachable fixtures or reviewed dispositions, plus stored-format differential checks where in shared model domain. |
| Persisted formats: session | Component table says L1 while target is L2; gaps remain for private/public relation, unanswered initiator/responder exclusion, inner invariants and field-level refusals. | BLOCKING | P4/P5 | Reachable fixtures or reviewed dispositions, plus stored-format differential checks where in shared model domain. |
| Practice 5: invariants catalogue | Invariants are not catalogued as requirements. | AMBIGUOUS | P2/P7 | Requirement evidence index records scoped invariants, or a decision explains why they stay outside requirement IDs. |
| Practice 8: evidence traceability | Structural ID spine is checked; proof/vector/test evidence links are not. | BLOCKING | P2 | Machine-readable requirement evidence index, reference checks and negative controls. |
| Practice 9: differential testing | Session and prekey store stored formats are modelled but not driven through both sides; Braid state machine remains partly outside differential vectors. | BLOCKING | P5/P7 | Required differential run reaches intended versions/branches/refusals, or explicit scoped exclusions. |
| Gate 1 | Every component must meet target or have a recorded target decision. Several rows above do not. | BLOCKING | P1/P7/P6/P4 | Component obligation matrix closed or amended by recorded decisions. |
| Gate 2 | Gap register must have no open BLOCKING rows and no unresolved AMBIGUOUS rows. | BLOCKING | P1/P3/P4/P5/P6/P7 | `GAP-REGISTER.md` rows classified and closed/decided as required. |
| Gate 3 | Claims ledger must receive a final independent claim-by-claim review after its last change. | BLOCKING | P9 | Review record naming reviewer, revision, artifacts read and findings/disposition. |
| Gate 4 | Every gate must have negative-control evidence and must fail when required inputs are absent. | BLOCKING | P9/P2/P7 | Gate mutation records with command/environment, deliberate fault and diagnostic. |

## Deferral decisions still needed

The current register has deferred rows, but a deferral only satisfies readiness
if it states the effect on the target and a revisit trigger. These still need a
recorded decision or a target-closing slice:

| Item | Current risk | Package |
| --- | --- | --- |
| Boundary headroom | Deferred research does not by itself close any target; success theorems still carry headroom premises. | P7 |
| Erasure codec refinement | Deferred while the erasure code target remains L4, so gate 1 is not satisfied until evidence lands or the target changes. | P7 |

## Gate evidence inventory

| Gate/check | Protected property | Current negative-control evidence | Missing evidence |
| --- | --- | --- | --- |
| `tooling/check-traceability.py` | Requirement/status/assumption/reference spine does not drift. | Case runner removes a limitations row and cites an unknown assumption. | Cases for missing status, missing rests-on, bad title/status class, bad assumption inverse list and unknown LIM/ADV/AS/EX references. |
| `tooling/check-workflows.sh` | Workflow files parse and obey repository security rules. | 62 case files under `tooling/tests/check-workflows-cases`. | None identified in this P1 pass. |
| `tooling/check-precondition-shapes.py` | Listed vacuous numeric precondition shapes do not enter first-party Lean. | 71 case directories under `tooling/tests/check-precondition-shapes-cases`. | None identified in this P1 pass. |
| `tooling/check-labels.sh` | Derivation labels stay registered and prefix-free except recorded pairs. | No standalone case runner in current tree. | Negative controls for unregistered label and forbidden prefix relation. |
| `tooling/check-vectors.py` | Vector files obey schemas. | Schema validation itself rejects malformed vectors, but no case runner is recorded here. | A small schema-negative case suite, or a recorded reason existing schema tests suffice. |
| Independent reader | Specification-only reader can interpret and check committed vectors. | Reader derived cases exercise many refusals; historical GAPS reports record findings. | Mutation record showing a representative missing/incorrect vector rule fails the reader. |
| Claims/attestation | Claims and generated artifacts match checked Lean/source state. | `attest.py --check`, audit negative and reach scripts. | P9 must record which planted cases cover which gate claim. |
| Full CI | Public/local required checks run and fail rather than skip when required. | `tooling/ci.sh` and GitHub workflow share most gates; workflow now invokes traceability. | P9 must record environments and missing-tool behavior for each required/optional gate. |

## Next P1 slices

1. Extend `tooling/tests/run-check-traceability-cases.sh` to cover each rule the
   checker claims to enforce.
2. Decide whether `GAP-REGISTER.md` should remain Markdown-only or gain a
   machine-readable sidecar before P2 indexes evidence against gap IDs.
3. Add target/scope decision records for any deferred item that is intended not
   to block gate 1.
