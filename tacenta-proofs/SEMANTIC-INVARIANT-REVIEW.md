# Semantic invariant review

Review scope: current `codex/proven-core-braid` candidate, with the decoder
receive-boundary repair included, reviewed against the invariant catalogue in
`tacenta-spec/security-properties/evidence-index.json`, the implementation,
the model, the translated proofs, and the named Rust tests.

This is a semantic sufficiency review. It does not turn test evidence into a
theorem, and it does not close the separate session-orchestration or contract
vacuity gates.

The receive-boundary review is now explicit: the old needed-only premise was
insufficient for the concrete decoder because `Decoder::message` also reserves
by `size`. The repaired contract requires both `size <= 4128` and
`needed <= 65536`; the state-size fact is preserved and supplied at the T1/T3,
restore, and refinement boundaries. This is a repaired proof boundary, not an
end-to-end lifecycle proof and not an independent review of the contract laws.

## Dispositions

| Invariant | Disposition | Evidence actually established | Remaining limit |
| --- | --- | --- | --- |
| `INV-AUTH-COMMIT` | Partial, operationally well-supported | `establish_responder` is inspected at the authentication-before-commit boundary; `refusal_restore_preserves_continuation` and `session_lifecycle_01_establishes_restores_continues_and_refuses_replays` cover refusal, restore and continuation; the runtime mutation control rejects skipped curve-key consumption on the mixed path. | No product-level crash/transaction proof: durable multi-object storage is outside this crate. |
| `INV-IDENTITY-ROLE` | Partial | Import tests cover associated-data orientation, role agreement, sparse direction, unanswered-role combinations, canonical ephemeral keys, and identity-key admission. | No model property or translated proof establishes the identity/role relation through session establishment and subsequent operations; identity-key computation remains a contract boundary. |
| `INV-PREKEY-CONSUMPTION` | Partial, with transaction regression coverage | Rust tests cover authenticated consumption, failed-auth non-consumption, repeated-failure non-drain, and exhausted last-resort refusal. The four translated responder success commit shapes are kernel-checked, including mixed last-resort plus curve one-time consumption. | No complete real-to-model store relation or independent cryptographic verdict in the reader. |
| `INV-MESSAGE-SINGLE-USE` | Partial | The model has `accepted_replay_is_no_op`; the trace proof has `replay_has_no_second_acceptance`; the session lifecycle test covers replay after restore and later genuine delivery. | The trace result is bounded and does not prove every unbounded delivery schedule; public lifecycle refinement is incomplete. |
| `INV-COUNTER-EPOCH-BOUNDS` | Partial and explicitly scoped | Classical, sparse, and Braid boundary tests and persistence/differential evidence cover refusal behavior; decoded-state panic-freedom is proved. The headroom target decision records the retained successor premise. | Success refinement at the reserved boundary is not claimed. The retained headroom premise is not derived from every decoded-state invariant. |
| `INV-COMPOSED-STATE` | Partial | Import tests cover nested ratchet/Braid role and epoch relations, failed-state exemption, and honest-session invariant preservation. | No full translated lifecycle proof shows that every session produced by establishment preserves the composed relation; this is part of `E2E-01`. |
| `INV-TERMINAL-FAILURE` | Partial, operationally supported | The model and trace proof carry failure through later refusals; Rust tests cover the triggering delivery and later send/receive refusal. | No product-level durable-store recovery proof; persistence is tested at session-byte level. |
| `INV-CANONICAL-RESTORE` | Partial | Export/import continuation and canonical identity-boundary refusals are covered by Rust tests; the implementation checks the stored identity rule without repair. | No model/proof relation for canonical restore, and no atomic multi-object persistence proof; those remain caller/product responsibilities. |

## Headroom disposition

The proof-boundary decision in
[`PROOF-BOUNDARY-HEADROOM-TARGET-DECISION.md`](PROOF-BOUNDARY-HEADROOM-TARGET-DECISION.md)
is accepted as the current scope boundary:

1. successor-headroom premises remain explicit on success-refinement theorems;
2. boundary refusal behavior is evidence-backed and separately tested;
3. no boundary-success refinement claim is made; and
4. the decision must be reopened if ceilings, refusal transitions, theorem
   premises, or the target scope change.

This is a disposition, not a proof that the premise is necessary. It also does
not close the semantic gaps above, contract vacuity, dispatch-vacuity, or the
five public-root composition requirement.

## Review conclusion

The invariant catalogue is now semantically reviewed and every row has an
explicit evidence class and residual. No row should be described as a complete
end-to-end lifecycle invariant proof. The remaining Gate 1/2 decision is
therefore substantive and named: close the contract/dispatch assumptions and
compose the public lifecycle roots, or keep the candidate below the “proven
core” claim.
