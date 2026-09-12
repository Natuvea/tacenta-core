# Gap register

Current register for assurance gate 2. Historical independent-reader reports stay
unchanged under `tacenta-test-vectors/runners/independent/`; this file records
the current disposition after later fixes.

Last assessed: 2026-09-12, at `bccbd13` plus this register update.

## Status key

- **Closed:** resolved in current files, with evidence named here.
- **Open:** still needs a specification, model, vector, proof or tooling change.
- **Deferred:** accepted as outside the current month or outside the repository's
  present scope.
- **Historical:** accurate when reported, no longer a current gap.

## Current items

| ID | Status | Area | Current disposition | Acceptance criterion |
| --- | --- | --- | --- | --- |
| G7-01 | Closed | Vector layouts | `tacenta-test-vectors/README.md` now states the `prekey-store-state.json` and `session-state.json` `fields` layouts, including the derived `braid_tag`, `braid_epoch` and `sparse_epoch` session names. | Independent reader can implement the two files' exact field names from the README layout rather than from inference. |
| G7-02 | Closed | Vector status | The README status paragraph now says the session and prekey-store persisted formats have vectors, and that every persistence file except the two erasure coders names its refusal. | No current status paragraph says those two files have no vectors or limits refusals to the two ratchet-state files. |
| G7-03 | Closed | Prekey signatures | `session-persistence.md` now says stored prekey signatures verify using the unlabelled prekey signature input. `CHANGELOG.md` records the clarification. | A reader no longer has to choose between labelled application signatures and unlabelled prekey signatures. |
| G7-04 | Closed | Prekey signing operations | `session-persistence.md` now names `create_prekeys`, `replenish`, `rotate_signed_prekey` and `rotate_kem` as the operations covered by the signing obligation. `CHANGELOG.md` records the clarification. | A reader no longer has to infer whether the obligation reaches only rotations or every operation that signs a prekey. |
| G7-05 | Open | Prekey store rule interaction | `identity_public = p - 1` is canonical but cannot verify a stored signature. The sixth rule therefore narrows the accepted set after the fifth rule. | Add current prose or vector coverage that records this rule interaction, or explicitly defer it as a wording-only reader finding. |
| G7-06 | Closed | Session vector comment | The generator comment for `sparse-epoch-does-not-follow-the-braid` now says the Braid epoch is moved outside the relation, rather than saying the sparse epoch moved. Regenerated vectors carry the corrected comment. | The vector's comment names the half that actually changed, and no runner behavior changes. |
| G5-03 | Open | Persistence refusal precedence | Short buffers whose first byte is also an unknown version remain deliberately unspecified across formats with different fixed-field lengths. | Decide whether to keep implementation freedom and state it as such for all affected formats, or pin a single precedence with vectors and reader behavior. |
| G5-09 | Open | Ratchet refusal ordering | A classical ratchet receive at `Nr = u32::MAX` for a lower unstored message can be read as stale-message refusal or counter exhaustion; the current pages do not order them. | Add a normative ordering decision and a focused vector or test, or record the freedom and the exact effect on interoperability. |
| G4-01 | Open | Composite header trailing bytes | The spec defines the ratchet-message decoder, not a standalone composite-header decoder with trailing bytes. Existing vectors carry no bytes after the header. | Decide whether standalone header decoding is a public contract; if yes, state and test trailing-byte behavior. If no, record it as outside the vector contract. |
| G6-01 | Open | Vector naming | The vector README still uses `sk` for both an already split Double Ratchet secret and an unsplit Triple Ratchet secret. | Rename or document the two meanings so a runner does not infer the wrong derivation stage. |
| G6-03 | Open | Braid operation read-back | The README states read-back obligations for ratchet operation vectors but not as explicitly for Braid operation vectors. | State whether Braid `output` must read back and, if required, add a `-read-back` sibling or an equivalent runner check. |
| G6-05 | Open | Braid absent codeword encoding | The Braid step layout does not state the zeroing rule for an absent codeword's index and chunk. | State the zeroing rule in the layout or point to the wire rule that supplies it, then ensure a runner checks it. |
| Persisted prekey older versions | Open | Coverage | All byte-carrying prekey-store vectors are v4; older versions are covered by implementation tests, not vectors. | Add versioned fixtures with provenance, or record that older-version behavior remains implementation-tested only. |
| Persisted prekey `previous_kem` | Open | Coverage | No vector carries `previous_kem_present = 0x01`. | Add a deterministic fixture with `previous_kem`, plus manifest provenance and a verifier. |
| Prekey signature refusal | Open | Coverage | Accepted fixtures verify signatures, but no vector reaches the stored-signature refusal; reader faults for the rule are caught by derived cases. | Add a fixture mutation that reaches `incoherent` for the signature rule after proving no earlier parser or KEM check masks it. |
| Session Braid tag 6/7 boundary | Open | Coverage | Derived case EP-01 walks the boundary, but no vector distinguishes the two readings. | Add accepted/refused session fixtures that exercise both branches of the epoch relation around tags 6 and 7. |
| Session failed-Braid exemption | Open | Coverage | Covered by derived cases only. | Add a session fixture for the failed-Braid exemption or record why a fixture cannot reach it. |
| Session role rule, Braid half | Open | Coverage | Current vector coverage reaches the sparse half of the role rule; the Braid half remains case-only. | Add a fixture that changes the Braid half's role relation without tripping earlier checks. |
| Session `ratchet_private` relation | Open | Coverage | The model cannot derive the public half from `ratchet_private`; vectors do not reach this rule. | Add a Rust-produced fixture and mutation with manifest provenance, or state why this remains implementation-tested only. |
| Session unanswered initiator/responder exclusion | Open | Coverage | Current vectors do not reach the rule that an unanswered initiator is not also a responder. | Add a session fixture or mutation that targets only this rule. |
| Session inner invariant refusals | Open | Coverage | Current vectors do not reach the rule that each half satisfies its own crate's invariant. | Add targeted fixtures for reachable inner-invariant refusals and expected refusal kinds. |
| Requirement traceability gate | Open | Tooling | Requirement IDs, evidence and assumptions are stated in prose, but CI does not enforce the index. | Add a machine-readable index and CI checker calibrated with negative cases. |
| Boundary headroom | Deferred | Proof scope | The refinement theorems still require successor headroom; current research says these premises cannot be dropped from the success theorems. | Attempt boundary-refusal lemmas separately, starting with the Braid's documented refusal transitions. |
| Erasure codec refinement | Deferred | Proof scope | Field arithmetic and panic-freedom are covered; full codec refinement remains outside current L3 evidence. | First produce a `DecoderRefines` design note and one rejection-preservation lemma before estimating full L4 work. |

## Notes

- G5-02 is historical and closed: the Braid `key_pair` content clause is scoped
  to implementations that know the delegated KEM layout.
- G5-07 is narrowed by ADR-0006 point 7: evidence may be cited from outside the
  specification, but normative content must be readable from the specification.
- Historical reports should not be edited to match this register. Add a row here
  when later work changes an item's disposition.
