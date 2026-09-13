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
| G7-05 | Closed | CLOSED | P3 | Prekey store rule interaction | `session-persistence.md` now records this as a wording-only rule interaction: `identity_public = p - 1` passes the canonical curve-key rule, but signature verification refuses that value before converting it to an Edwards point, so the stored-signature rule intentionally narrows the accepted set. | `cases_signed.py` PK-03 and `cases_stored.py` SK-08 keep the independent reader's distinction between canonical-key refusal and the later signature-rule refusal. `prekey-store-state/signed-prekey-signature-does-not-verify` now also pins the later signature-rule refusal with a cryptographic runner verdict outside the model boundary. |
| G7-06 | Closed | CLOSED | P1 | Session vector comment | The generator comment for `sparse-epoch-does-not-follow-the-braid` now says the Braid epoch is moved outside the relation, rather than saying the sparse epoch moved. Regenerated vectors carry the corrected comment. | The vector's comment names the half that actually changed, and no runner behavior changes. |
| G5-03 | Closed | CLOSED | P3 | Persistence refusal precedence | `session-persistence.md` now keeps the implementation freedom deliberately, but scopes it to the exact overlap where a non-empty buffer is too short for every recognised version and its first byte is unknown; a format-by-format table names the six affected persisted formats. | `cases_stored.py` RJ-01 checks that the empty buffer is short, a recognised-version truncation is short-or-malformed, a long enough unknown-version buffer is wrong-version, and only the short unknown-version overlap accepts either refusal. |
| G5-09 | Closed | CLOSED | P3 | Ratchet refusal ordering | `ratchet.md` now records deliberate implementation freedom for the exact overlap where `Nr = u32::MAX` and a same-chain unstored message has a lower number: stale/out-of-order and `ChainExhausted` are both conforming refusals, while accepting is not. | `cases_ratchet.py` CR-20 checks the overlap and cites CR-02 and CR-04 as adjacent cases: message number `u32::MAX` remains exhaustion, and same-chain unstored messages below `Nr < u32::MAX` remain stale. |
| G4-01 | Closed | CLOSED | P3 | Composite header trailing bytes | `message-format.md` now makes standalone composite-header decoding a public contract for vectors, associated-data construction and implementations that parse the header before ciphertext: it accepts exactly 102 bytes and refuses trailing bytes. | `negative_cases.py` RM-14 checks that the standalone composite-header decoder rejects bytes after the fixed-width header, while the vector README records why the ratchet-message decoder still gives the existing 102-byte decoder vectors the same verdict. |
| G6-01 | Closed | CLOSED | P3 | Vector naming | `tacenta-test-vectors/README.md` now documents that `sk` in `ratchet-state.json` and `sparse-ratchet-state.json` is the already split per-ratchet initial root secret, while `sk` in `triple-ratchet-state.json` is the unsplit Triple Ratchet shared secret. | A runner can implement the layouts without inferring whether it must split `sk` before initialising the Double and Sparse Ratchets. The vector field names are left stable. |
| G6-03 | Closed | CLOSED | P3/P7 | Braid operation read-back | `tacenta-test-vectors/README.md` now states that Braid operation `output` must read back and write as the same bytes. | The independent reader's `h_braid_state` handler asserts `output read back and written again`, so the Braid operation vectors use an equivalent runner check rather than separate `-read-back` siblings. |
| G6-05 | Closed | CLOSED | P3/P7 | Braid absent codeword encoding | `tacenta-test-vectors/README.md` now states that Braid operation steps use the wire Braid-message fields, so an absent codeword has all-zero `chunk_index` and `chunk` padding. | The independent reader's vector handler already reports an absent codeword with non-zero index or chunk data as malformed vector data, so the runner check is explicit and matches the layout rule. |
| PK-OLD-VERSIONS | Closed | CLOSED | P4/P5 | Persisted prekey coverage | `prekey-store-state.json` now includes accepted `legacy-v1`, `legacy-v2` and `legacy-v3` fixtures derived from the no-record, no-retired v4 fixture; the independent reader checks their fields and permits the required v4 upgrade on write-back. | Older-version prekey-store parsing is pinned by vectors rather than implementation tests alone. `PK-PREVIOUS-KEM` is now closed by the separate retired-KEM fixture. |
| PK-PREVIOUS-KEM | Closed | CLOSED | P4/P5 | Persisted prekey coverage | `prekey-store-state.json` now includes the accepted `retired-kem-prekey` fixture produced by `print_prekey_store_fixtures`; it carries `previous_kem_present = 0x01`, and the Rust vector runner walks `len(4) || kem_pair || id(4) || sig(64)` before requiring the store to end. | The prekey store's retired-KEM sub-format is pinned by a deterministic fixture; the stored-signature refusal is closed separately by `PK-SIGNATURE-REFUSAL`. |
| PK-SIGNATURE-REFUSAL | Closed | CLOSED | P4 | Prekey signature refusal | `prekey-store-state.json` now includes `signed-prekey-signature-does-not-verify`, a one-byte mutation of `signed_prekey_sig` in a valid fixture. The generator first requires the model to accept and re-encode the mutated bytes, so parser, KEM-pair and structural semantic checks are not the masking refusal. | The cryptographic runners refuse the fixture as `incoherent`, pinning the stored-signature refusal that remains outside the model's signature-free boundary. |
| SESS-BRAID-TAG-BOUNDARY | Closed | CLOSED | P4/P5 | Session coverage | `session-state.json` now includes accepted neighbours on both sides of the boundary: `tag-six-keeps-previous-sparse-epoch` and `tag-seven-uses-current-sparse-epoch`. | The refused siblings `tag-six-with-current-sparse-epoch-refused` and `tag-seven-with-previous-sparse-epoch-refused` reach `inconsistent`, so vectors now distinguish the tag 6 `e - 1` branch from the tag 7 `e` branch. |
| SESS-FAILED-BRAID | Closed | CLOSED | P4/P5 | Session coverage | `session-state.json` now includes `failed-braid-exempts-sparse-epoch`, an accepted session with Braid tag 11 and sparse epoch 1. | The fixture pins that Failed carries no epoch and is exempt from the live-Braid epoch relation; a runner that applies the relation to Failed rejects it. |
| SESS-BRAID-ROLE | Closed | CLOSED | P4/P5 | Session coverage | `session-state.json` now includes `halves-disagree-on-the-braid-role`, a tag 6 / epoch 2 responder fixture whose sparse epoch still follows the Braid. | The vector reaches `inconsistent` only through the Braid tag/parity role relation; the sparse-role sibling remains `halves-disagree-on-the-sparse-role`. |
| SESS-RATCHET-PRIVATE | Closed | CLOSED | P4/P5 | Session coverage | `session-state.json` now includes `ratchet-private-does-not-match-dhs-pub`, appended by `augment-session-state.py` from the responder fixture after the Lean generator runs. | The vector flips byte 7 of `ratchet_private`, away from X25519 clamp bits, and both the independent and Rust readers refuse it as `inconsistent`, covering the rule the Lean model cannot compute. |
| SESS-UNANSWERED-ROLE | Closed | CLOSED | P4/P5 | Session coverage | `session-state.json` now includes `unanswered-initiator-is-also-responder`, generated by adding the valid `pending_initial` from the unanswered initiator fixture to the responder fixture. | The vector remains well-formed and canonical, keeps the responder role through `established_ephemeral`, and reaches `inconsistent` only because an unanswered initiator is also a responder. |
| SESS-INNER-INVARIANTS | Closed | CLOSED | P4/P5 | Session coverage | `session-state.json` now includes `triple-state-reader-refuses` and `braid-reader-refuses`, each changing the nested half's own version byte inside the responder fixture. | The session reader refuses both as `short-or-malformed`, pinning that a half its own reader refuses is rejected at the session boundary before session semantic rules run and without passing through the nested `wrong-version`. |
| TRACE-EVIDENCE-INDEX | Open | BLOCKING | P2 | Tooling | `tooling/check-traceability.py` now enforces the structural spine and migrated evidence-index links. The checked `security-properties/evidence-index.json` covers all authentication and confidentiality requirements, including proof, claim, vector, test and missing-evidence references where present. `tooling/tests/run-check-traceability-cases.sh` holds that gate to pass and ten refusal cases, including a confidentiality vector mutation. Forward-secrecy and post-compromise-security requirements are still not indexed. | Migrate the remaining REQ-FS and REQ-PCS rows into the machine-readable claim/vector/test index, then make missing requirement entries fail once the index covers all 32 requirements. |
| PROOF-BOUNDARY-HEADROOM | Deferred | DEFERRED | P7 | Proof scope | The refinement theorems still require successor headroom; current research says these premises cannot be dropped from the success theorems. The deferral does not by itself close a target. | Attempt boundary-refusal lemmas separately, starting with the Braid's documented refusal transitions, or record a target/scope decision with revisit trigger. |
| PROOF-ERASURE-REFINEMENT | Deferred | BLOCKING | P7 | Proof scope | Field arithmetic and panic-freedom are covered; full codec refinement remains outside current L3 evidence while the erasure target remains L4. | Produce a `DecoderRefines` design note and one rejection-preservation lemma, then either complete the L4 evidence or record a target/scope decision. |

## Notes

- G5-02 is historical and closed: the Braid `key_pair` content clause is scoped
  to implementations that know the delegated KEM layout.
- G5-07 is narrowed by ADR-0006 point 7: evidence may be cited from outside the
  specification, but normative content must be readable from the specification.
- Historical reports should not be edited to match this register. Add a row here
  when later work changes an item's disposition.
