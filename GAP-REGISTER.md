# Gap register

Current register for assurance gate 2. Historical independent-reader reports stay
unchanged under `tacenta-test-vectors/runners/independent/`; this file records
the current disposition after later fixes.

Last assessed: 2026-09-12, at `96890d3a07dfa3fa0d0b6b00e5f9e4a6a82485a8`
plus this P1 classification update.

## Status key

- **Closed:** resolved in current files, with evidence named here.
- **Open:** still needs a specification, model, vector, proof or tooling change.
- **Deferred:** accepted as outside the current month or outside the repository's
  present scope.
- **Historical:** accurate when reported, no longer a current gap.

## Gate class key

- **BLOCKING:** must close, or be changed by a recorded decision, before the
  second external proof-ledger engagement.
- **AMBIGUOUS:** must become closed, BLOCKING, NONBLOCKING or a recorded
  decision before gate 2 can be said to pass.
- **NONBLOCKING:** disclosed work that does not block the second engagement at
  the current recorded target.
- **DEFERRED:** outside the current completion scope only if a recorded decision
  states the target effect and revisit trigger.
- **CLOSED:** resolved in current evidence.

[ASSURANCE-OBLIGATIONS.md](ASSURANCE-OBLIGATIONS.md) records the component and
gate obligations that are not individual reader findings.

## Current items

| ID | Status | Gate class | Package | Area | Current disposition | Acceptance criterion |
| --- | --- | --- | --- | --- | --- | --- |
| G7-01 | Closed | CLOSED | P1 | Vector layouts | `tacenta-test-vectors/README.md` now states the `prekey-store-state.json` and `session-state.json` `fields` layouts, including the derived `braid_tag`, `braid_epoch` and `sparse_epoch` session names. | Independent reader can implement the two files' exact field names from the README layout rather than from inference. |
| G7-02 | Closed | CLOSED | P1 | Vector status | The README status paragraph now says the session and prekey-store persisted formats have vectors, and that every persistence file except the two erasure coders names its refusal. | No current status paragraph says those two files have no vectors or limits refusals to the two ratchet-state files. |
| G7-03 | Closed | CLOSED | P3 | Prekey signatures | `session-persistence.md` now says stored prekey signatures verify using the unlabelled prekey signature input. `CHANGELOG.md` records the clarification. | A reader no longer has to choose between labelled application signatures and unlabelled prekey signatures. |
| G7-04 | Closed | CLOSED | P3 | Prekey signing operations | `session-persistence.md` now names `create_prekeys`, `replenish`, `rotate_signed_prekey` and `rotate_kem` as the operations covered by the signing obligation. `CHANGELOG.md` records the clarification. | A reader no longer has to infer whether the obligation reaches only rotations or every operation that signs a prekey. |
| G7-05 | Open | AMBIGUOUS | P3 | Prekey store rule interaction | `identity_public = p - 1` is canonical but cannot verify a stored signature. The sixth rule therefore narrows the accepted set after the fifth rule. | Add current prose or vector coverage that records this rule interaction, or explicitly decide that it is a wording-only reader finding. |
| G7-06 | Closed | CLOSED | P1 | Session vector comment | The generator comment for `sparse-epoch-does-not-follow-the-braid` now says the Braid epoch is moved outside the relation, rather than saying the sparse epoch moved. Regenerated vectors carry the corrected comment. | The vector's comment names the half that actually changed, and no runner behavior changes. |
| G5-03 | Open | AMBIGUOUS | P3 | Persistence refusal precedence | Short buffers whose first byte is also an unknown version remain deliberately unspecified across formats with different fixed-field lengths. | Decide whether to keep implementation freedom and state it as such for all affected formats, or pin a single precedence with vectors and reader behavior. |
| G5-09 | Open | AMBIGUOUS | P3 | Ratchet refusal ordering | A classical ratchet receive at `Nr = u32::MAX` for a lower unstored message can be read as stale-message refusal or counter exhaustion; the current pages do not order them. | Add a normative ordering decision and a focused vector or test, or record the freedom and the exact effect on interoperability. |
| G4-01 | Open | AMBIGUOUS | P3 | Composite header trailing bytes | The spec defines the ratchet-message decoder, not a standalone composite-header decoder with trailing bytes. Existing vectors carry no bytes after the header. | Decide whether standalone header decoding is a public contract; if yes, state and test trailing-byte behavior. If no, record it as outside the vector contract. |
| G6-01 | Open | AMBIGUOUS | P3 | Vector naming | The vector README still uses `sk` for both an already split Double Ratchet secret and an unsplit Triple Ratchet secret. | Rename or document the two meanings so a runner does not infer the wrong derivation stage. |
| G6-03 | Open | AMBIGUOUS | P3/P7 | Braid operation read-back | The README states read-back obligations for ratchet operation vectors but not as explicitly for Braid operation vectors. | State whether Braid `output` must read back and, if required, add a `-read-back` sibling or an equivalent runner check. |
| G6-05 | Open | AMBIGUOUS | P3/P7 | Braid absent codeword encoding | The Braid step layout does not state the zeroing rule for an absent codeword's index and chunk. | State the zeroing rule in the layout or point to the wire rule that supplies it, then ensure a runner checks it. |
| PK-OLD-VERSIONS | Open | BLOCKING | P4/P5 | Persisted prekey coverage | All byte-carrying prekey-store vectors are v4; older versions are covered by implementation tests, not vectors. | Add versioned fixtures with provenance, or record that older-version behavior remains implementation-tested only and assess whether that meets L2. |
| PK-PREVIOUS-KEM | Open | BLOCKING | P4/P5 | Persisted prekey coverage | No vector carries `previous_kem_present = 0x01`. | Add a deterministic fixture with `previous_kem`, plus manifest provenance and a verifier. |
| PK-SIGNATURE-REFUSAL | Open | BLOCKING | P4 | Prekey signature refusal | Accepted fixtures verify signatures, but no vector reaches the stored-signature refusal; reader faults for the rule are caught by derived cases. | Add a fixture mutation that reaches `incoherent` for the signature rule after proving no earlier parser or KEM check masks it, or record the remaining coverage limit. |
| SESS-BRAID-TAG-BOUNDARY | Open | BLOCKING | P4/P5 | Session coverage | Derived case EP-01 walks the boundary, but no vector distinguishes the two readings. | Add accepted/refused session fixtures that exercise both branches of the epoch relation around tags 6 and 7. |
| SESS-FAILED-BRAID | Open | BLOCKING | P4/P5 | Session coverage | Covered by derived cases only. | Add a session fixture for the failed-Braid exemption or record why a fixture cannot reach it. |
| SESS-BRAID-ROLE | Open | BLOCKING | P4/P5 | Session coverage | Current vector coverage reaches the sparse half of the role rule; the Braid half remains case-only. | Add a fixture that changes the Braid half's role relation without tripping earlier checks. |
| SESS-RATCHET-PRIVATE | Open | BLOCKING | P4/P5 | Session coverage | The model cannot derive the public half from `ratchet_private`; vectors do not reach this rule. | Add a Rust-produced fixture and mutation with manifest provenance, or state why this remains implementation-tested only and assess whether that meets L2. |
| SESS-UNANSWERED-ROLE | Open | BLOCKING | P4/P5 | Session coverage | Current vectors do not reach the rule that an unanswered initiator is not also a responder. | Add a session fixture or mutation that targets only this rule. |
| SESS-INNER-INVARIANTS | Open | BLOCKING | P4/P5 | Session coverage | Current vectors do not reach the rule that each half satisfies its own crate's invariant. | Add targeted fixtures for reachable inner-invariant refusals and expected refusal kinds. |
| TRACE-EVIDENCE-INDEX | Open | BLOCKING | P2 | Tooling | `tooling/check-traceability.py` now enforces the structural spine: every requirement row has status and assumptions, every status-table row matches a requirement, every direct assumption dependency has a live `ASM-*`, and `REQ/ASM/LIM/ADV/AS/EX` references resolve. `tooling/tests/run-check-traceability-cases.sh` holds that gate to pass and refusal cases. The deeper claim/vector/test evidence index is still prose. | Add the machine-readable claim/vector/test index and extend the checker so every requirement's evidence links are enforced, not only its ID and assumption spine. |
| PROOF-BOUNDARY-HEADROOM | Deferred | DEFERRED | P7 | Proof scope | The refinement theorems still require successor headroom; current research says these premises cannot be dropped from the success theorems. The deferral does not by itself close a target. | Attempt boundary-refusal lemmas separately, starting with the Braid's documented refusal transitions, or record a target/scope decision with revisit trigger. |
| PROOF-ERASURE-REFINEMENT | Deferred | BLOCKING | P7 | Proof scope | Field arithmetic and panic-freedom are covered; full codec refinement remains outside current L3 evidence while the erasure target remains L4. | Produce a `DecoderRefines` design note and one rejection-preservation lemma, then either complete the L4 evidence or record a target/scope decision. |

## Notes

- G5-02 is historical and closed: the Braid `key_pair` content clause is scoped
  to implementations that know the delegated KEM layout.
- G5-07 is narrowed by ADR-0006 point 7: evidence may be cited from outside the
  specification, but normative content must be readable from the specification.
- Historical reports should not be edited to match this register. Add a row here
  when later work changes an item's disposition.
