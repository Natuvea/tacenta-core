# Session and prekey operation traces

This is the normative trace grammar for the session-establishment and prekey
lifecycle operations. It complements the byte-level vectors: an operation
trace says what a sequence must do to durable state, while a byte-level vector
pins encodings and primitive outputs. It does not describe internal state,
random-source calls, error types, or a check order the protocol leaves open.

Each trace conforms to
[`schema/session-operation-trace.schema.json`](schema/session-operation-trace.schema.json).
The `source` field must cite the specification pages that determine the trace.
Each trace has an `id`, optional named fixtures, and one or more ordered steps.
A fixture is an opaque named input, for example a published bundle, an initial
message, a prekey store, a session, or exported state. Its construction belongs
to a referenced byte-level vector or to the reader's test fixture; this grammar
does not make an implementation's private representation normative.

## Steps

Every step has an `actor`, an `op`, `expect`, and `effect`. `inputs`, when
present, refers to named fixtures and source-defined scalar inputs. Consecutive
steps observe the durable state the preceding accepted step left behind.

`actor` is `initiator`, `responder`, or `application`. `application` is used
for store maintenance and restore because the protocol leaves their scheduling
to the application.

`op` is one of:

- `create-prekey-store`, `publish-bundle`, `replenish`,
  `rotate-signed-prekey`, and `rotate-kem`;
- `establish-initiator` and `establish-responder`;
- `send`, `receive`, and `receive-repeated-initial`; or
- `restore-prekey-store` and `restore-session`.

`expect.outcome` is `ok` or `refused`. A refused step carries the source-named
`expect.refusal`: `decode-failure`, `authentication-failure`,
`NotARepeatedInitial`, `ReplayedLastResort`, or `LastResortRecordFull`. A trace
may use `ok` for a source-defined quiet no-op at the identifier ceiling; its
effect must say `next_id: at-ceiling` and leave the affected durable object
unchanged. A refused step leaves both the prekey store and session unchanged,
which every such trace must state explicitly in `effect`.

## Durable effects

Every `effect` names both the prekey-store and session effect. The values are
the effects the protocol pages require:

| Field | Values | Requirement source |
| --- | --- | --- |
| `prekey_store` | `unchanged`, `created`, `replenished`, `signed-prekey-rotated`, `kem-prekey-rotated`, `one-time-keys-deleted`, `last-resort-fingerprint-added`, `restored` | key-deletion.md, Prekeys at rest; session-persistence.md, Prekey store |
| `session` | `unchanged`, `initiator-pending`, `responder-established`, `message-accepted`, `terminal-failed`, `restored` | session-establishment.md, Sending/Receiving the initial message; mlkem-braid.md, Failure; session-persistence.md, Session |
| `next_id` | `unchanged`, `advanced`, `at-ceiling` | key-deletion.md, One-time prekeys are replenished |
| `one_time_curve` | `unchanged`, `deleted`, `absent` | session-establishment.md, Receiving the initial message |
| `one_time_kem` | `unchanged`, `deleted`, `last-resort` | session-establishment.md, Replay |
| `last_resort_record` | `unchanged`, `added`, `dropped` | session-establishment.md, Replay; key-deletion.md, last-resort replay record |
| `retired_signed_prekey`, `retired_kem_prekey` | `unchanged`, `retained`, `dropped` | key-deletion.md, Signed prekeys rotate |

An omitted optional effect field is outside that step's claim. A trace must use
the fields needed to make its stated property observable. In particular,
prekey-consumption and replay cases must state `one_time_curve`,
`one_time_kem`, and `last_resort_record`; lifecycle cases must state `next_id`
and the applicable retired-key field.

`message-accepted` is deliberately direction-agnostic: it records that an
already-established session accepted and adopted the candidate state for one
message, whether the operation was `send`, `receive`, or
`receive-repeated-initial`. A trace that needs to distinguish the direction
does so with its `op`; it must not infer a separate durable-effect value.

## Required trace families

The committed trace set must contain at least one case for each of these
source-defined outcomes before it is claimed complete:

1. create, publish, replenish, and each rotation, including retained and then
   dropped retired keys and the identifier ceiling;
2. initiator and responder establishment, with and without one-time curve
   prekeys, and responder deletion only after successful authentication;
3. a forged initial message whose authentication failure leaves the prekey
   store unchanged;
4. one-time-key replay refusal, last-resort replay refusal, and a full
   last-resort-record refusal, each as no-ops;
5. repeated-initial acceptance for the same responder session, plus
   `NotARepeatedInitial` for an initiator session and changed identity or
   ephemeral; and
6. prekey-store and session restoration followed by a source-defined operation
   whose durable effect confirms continuation.
7. an ordinary authenticated receive, later-message-first delivery followed by
   skipped-message recovery, and refusal of a duplicate without changing the
   session;
8. an authenticated receive that enters the Braid terminal-failure state, then
   a later operation refused from that persisted state; and
9. initiator bundle signature failure, non-contributory DH, and malformed-wire
   refusal at their source-defined stages, each leaving the claimed durable
   state unchanged.

The source documents intentionally leave some choices to the application. A
trace must not treat session replacement after a reset, scheduling of rotation
or replenishment, or an implementation-specific error type/check order as a
conformance requirement.
