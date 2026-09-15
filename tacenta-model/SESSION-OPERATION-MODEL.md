# Session and prekey operation model

This is the P6 design slice for the session/prekey operation surface that
currently rests on ASM-19. It is a contract for the model and vector work that
will follow; it does not claim proof or differential coverage for the operation
surface by itself.

The persisted session and prekey-store formats are already modelled and driven
through the differential harness over their shared structural domains. This note
covers the next layer up: operations that create, mutate, refuse or export those
states.

## Scope

The L2 operation surface is the part of `tacenta-core/src/sessions` whose
behaviour the security-property pages cite through ASM-19:

- prekey-store creation, publication, replenishment and rotation;
- initiator and responder establishment;
- authenticated send and receive;
- one-time prekey consumption and last-resort replay records;
- failed agreement handling; and
- export/import between operation steps.

The model should state durable state before and after each operation, the exact
commit point, the refusal class, and whether a refused operation preserves state
or records a terminal failure. It should not try to prove the cryptographic
algorithms. Those are supplied as abstract verdicts and byte strings with the
contract below.

## Crypto abstraction contract

| Abstract input | Model value | Required concrete fixture link | Security fact left as an assumption |
| --- | --- | --- | --- |
| Signature check over a signed curve prekey | `valid`, `invalid` | Fixture carries a bundle signed by the identity key, and a second bundle with the same fields but a bad signature. Rust must refuse the bad one before KEM encapsulation or state mutation. | Ed25519 unforgeability and canonical signature verification remain ASM-07/ASM-14 territory. |
| Signature check over a KEM prekey | `valid`, `invalid` | Fixture pairs each KEM public key with its signature; the invalid case changes only the signature or signing identity. | The model only observes the verdict; it does not model FIPS 203 key contents. |
| Diffie-Hellman agreement | `contributory(output)` or `non_contributory` | Fixture uses ordinary keys for the success path and a low-order public key for refusal. | X25519 group arithmetic and low-order classification remain in the primitive implementation. |
| KEM agreement | `decapsulates(output)` or `refuses` | Fixture uses a generated KEM pair/ciphertext for success. The wire decoder rejects a length-malformed initial message before decapsulation; an equal-length altered ML-KEM ciphertext follows the primitive's implicit-rejection path and is observed as later authentication failure, not as a KEM error. | FIPS 203 encapsulation, decapsulation and key-pair consistency are assumed outside the model. |
| AEAD authentication | `authenticates(plaintext)` or `refuses` | Fixture changes only ciphertext/tag/header-associated data after a valid message is generated. | AEAD confidentiality and authenticity are primitive assumptions; the model only states commit behaviour after the verdict. |
| Injected randomness | Named draws for identity/prekey/ratchet/KEM operations | Fixture seed records the draw order or concrete generated public values. | Randomness quality remains ASM-01; the model requires freshness labels and equality/inequality where the protocol relies on it. |

The Rust fixtures that instantiate these abstractions must preserve the operation
shape: a failure trace changes only the abstract verdict being tested, and the
assertion compares durable state before and after the documented commit point.

## `SESSION-LIFECYCLE-01`: bounded composed trace

This is the first P6 composition property. It is deliberately narrower than a
refinement of the Rust session implementation and does not amend any public
security requirement. It connects the operation rows below for a bounded
two-party trace family, with abstract cryptographic verdicts supplied under the
contract above.

For two distinct fixed identities, an accepted establishment creates coherent
peer observations. An accepted authenticated send followed by its matching
receive delivers the intended plaintext exactly once. Exporting either peer
after a committed step and importing fresh objects from those bytes preserves
the observations needed for the remainder of the trace. An ordinary refused
input preserves the specified durable observation, and a terminal Braid
failure persists across export/import and refuses later session operations.

The initial CI budget is at most two peers, three queued messages, 32 protocol
operations and 32 deterministic seeds. Named regression traces are mandatory
in addition to generated traces: one-time and last-resort establishment;
pending, established, post-send and post-receive restoration; third-first
delivery followed by skipped-message delivery; altered authentication/header
and low-order agreement refusal followed by the genuine message; replay after
restore; terminal Braid failure followed by restore and retry; and malformed
stored bytes. The operation count excludes the observation-only exports used
to create fresh objects, but each such checkpoint is recorded explicitly.

The model observes identity binding, role/phase, pending-wrapper state,
accepted plaintext labels, single-use/replay disposition, terminal Braid state
and canonical exported session/store bytes. It does not observe or prove raw
DH, KEM, signature or AEAD calculations, database atomicity, transport
acknowledgements, hostile rollback of a valid store, or product store write
ordering. The joint session/store snapshot is assumed committed at every
checkpoint. A test-budget change must not change this statement without an
explicit update to this section and the trace theorem.

## Operation inventory

| Operation | Input and precondition | Transition and commit point | Outputs | Refusals and durable effects | Requirement families |
| --- | --- | --- | --- | --- | --- |
| Create prekey store | Identity plus requested one-time count. Count is capped by the identifier-space rule. | Allocates signed curve prekey, one-time curve prekeys, last-resort KEM prekey, one-time KEM prekeys, signatures and `next_id` in one new store. | `PrekeyStore`; later `publish` exposes a bundle. | No public refusal; exhaustion is represented by the cap and later quiet no-op replenishment/rotation. | REQ-AUTH-01, REQ-AUTH-12, REQ-FS-03. |
| Publish one bundle | Existing store. | No mutation; returns the current signed prekey, one curve one-time prekey when present, and a one-time KEM prekey when present, otherwise the last-resort KEM key. | `PublishedBundle`. | None; repeated `publish` can hand out the same one-time entries until an authenticated responder operation consumes them. | REQ-AUTH-01, REQ-AUTH-12. |
| Publish one-time batch | Existing store. | No mutation; pairs currently held one-time curve and KEM entries, shortest pool wins. | Ordered vector of `PublishedBundle`s for directory dispensing. | None. | REQ-AUTH-12, REQ-FS-03. |
| Publish multi-use bundle | Existing store. | No mutation; publishes the signed curve prekey and reusable last-resort KEM key with absent one-time ids. | `PublishedBundle`. | None; replay defence comes later from the last-resort record. | REQ-AUTH-12. |
| Replenish one-time pools | Store, matching identity, count, randomness; `next_id` must have room for new ids. | Adds curve one-time entries first, then KEM one-time entries and signatures, advancing `next_id` for every issued id. | Mutated store. | If identity mismatches, no state changes. At identifier exhaustion the operation stops quietly at the first failed allocation point; the model slice must decide whether L2 covers partial replenishment near exhaustion or treats it as an explicit omission. | REQ-AUTH-01, REQ-AUTH-12, REQ-FS-03. |
| Rotate signed prekey | Store, matching identity, randomness, `next_id` room. | Moves current signed prekey into `previous_signed_prekey`, wipes the older previous key if any, installs a fresh signed prekey, advances `next_id`. Commit is the field replacement sequence as one operation. | Mutated store and a bundle change on next publication. | Identity mismatch or id exhaustion leaves the store unchanged. | REQ-AUTH-01, REQ-FS-03. |
| Rotate KEM last-resort prekey | Store, matching identity, randomness, `next_id` room. | Moves current KEM key/signature/id into `previous_kem`, wipes the older retired key, drops replay-record entries for the wiped id, installs a fresh signed KEM key, advances `next_id`. | Mutated store; current last-resort budget is reset for future publications. | Identity mismatch or id exhaustion leaves the store unchanged. | REQ-AUTH-12, REQ-FS-03. |
| Initiator establishment | Our identity, peer bundle, optional expected peer identity, randomness. Bundle identity must match the expected identity when supplied, optional one-time field/id presence must agree, public keys must be canonical, and signatures must verify. | Derives PQXDH secret, creates initiator Triple Ratchet and Braid state, records pending initial fields. Commit is creation of the new session; no prekey store is an input. | Pending `Session`. | Unexpected identity, inconsistent bundle, bad encoding, bad signatures, bad KEM, or non-contributory DH produce no session. | REQ-AUTH-01, REQ-AUTH-02, REQ-AUTH-05, REQ-AUTH-10, REQ-CONF-02, REQ-PCS-02. |
| Initiator first and repeated sends | Pending or established session, plaintext, randomness. Braid must not be failed. | Braid send runs first and commits only with the Triple Ratchet candidate after encryption succeeds. While pending, the initial wrapper is prepended to every send until a peer answer is authenticated. | Message bytes. | Already-failed Braid refuses with no mutation. If Braid send reaches terminal failure, that failed state is committed and no message is emitted. Triple Ratchet refusal leaves the previous state except for the terminal Braid failure case. | REQ-AUTH-05, REQ-CONF-04, REQ-PCS-02. |
| Responder establishment | Our identity, mutable prekey store, initial message, randomness. Message must decode, name a live signed prekey and KEM key, pass replay-budget checks on the last-resort path, decode canonical curve keys, derive contributory secrets, and authenticate the initial ciphertext. | All reads and expensive crypto happen before durable store mutation. After authentication, one-time curve and KEM entries are deleted, or a last-resort fingerprint is recorded under the named KEM id. Commit point is after successful decrypt. | New responder `Session` and first plaintext. | Decode, unknown id, replayed last-resort, full last-resort record, bad encoding, KEM, non-contributory agreement or AEAD failure leave the prekey store unchanged and produce no session. | REQ-AUTH-01, REQ-AUTH-10, REQ-AUTH-12, REQ-AUTH-13, REQ-CONF-02, REQ-FS-03. |
| Established send | Established session, plaintext, randomness. Braid must not be failed. | Same send commit rule as pending sends, without initial wrapper. Triple Ratchet candidate and Braid next state commit together after ciphertext is formed. | Ratchet message bytes. | Already-failed Braid refuses with no mutation; newly failed Braid commits terminal failure and emits no message; Triple refusal leaves the prior state unless terminal Braid failure was just recorded. | REQ-AUTH-05, REQ-CONF-04, REQ-PCS-02. |
| Established receive | Existing session, message bytes, randomness. Braid must not be failed. Initial wrappers are accepted only when they repeat the responder's establishing identity/ephemeral wrapper. | Decode message, run Braid/Triple Ratchet on candidates, derive candidate ratchet key, authenticate AEAD, then commit ratchet private key, Triple state and Braid state together. On success after an answer, clear the initiator's pending initial state. | Plaintext. | Decode errors, non-repeated initial wrappers, non-contributory DH, Triple refusals, and AEAD failures leave durable session state unchanged. An already failed Braid refuses unchanged. | REQ-AUTH-05, REQ-AUTH-11, REQ-AUTH-13, REQ-CONF-04, REQ-PCS-02. |
| Failed agreement observation | Existing session. | Reads Braid failure flag. | Boolean. | None. Once true, future send/receive refuse until re-establishment. | REQ-PCS-02. |
| Session export/import between steps | Session bytes produced after each accepted operation, or before externally acknowledging/transmitting the operation result. | Export records the current version and composed states. Import refuses malformed, non-canonical or inconsistent bytes; accepted bytes re-export canonically. | Persisted bytes or restored session. | Import refusal creates no session. Persistence order is part of the operation contract: after send, persist before transmit; after receive, persist before acknowledge; after responder establishment, persist session then prekey store. | REQ-AUTH-11, REQ-AUTH-12, REQ-AUTH-13, REQ-CONF-04. |
| Prekey-store export/import between steps | Store bytes produced after lifecycle operations and after responder establishment mutates the store. | Export writes the current layout. Import accepts current and specified legacy layouts, upgrades them canonically, and refuses malformed, non-canonical or incoherent bytes. | Persisted bytes or restored store. | Import refusal creates no store. Store writes must follow the session write after responder establishment. | REQ-AUTH-01, REQ-AUTH-12, REQ-AUTH-13, REQ-FS-03. |

## Operation-to-requirement matrix

| Requirement | P6 operations that can pin it | First accepted trace | First failure trace | Omission after this design slice |
| --- | --- | --- | --- | --- |
| REQ-AUTH-01 | create/replenish/rotate prekeys; initiator and responder establishment | Concrete signed bundle establishment reaches a persisted pending initiator and an established responder session whose identity bindings the model checks. | Changed signed-curve and KEM-prekey signatures refuse before the first initiator randomness draw, so no session can be produced. | Signature verdicts remain abstract; the model observes only the state committed after Rust has verified them. |
| REQ-AUTH-02 | initiator establishment with expected identity | Expected identity equals bundle identity. | Bundle identity differs from expected identity and refuses before randomness is drawn. | `establish_initiator`'s deliberately trusting form remains documented, not a pinned identity check. |
| REQ-AUTH-05 | send/receive associated-data construction | A message sent under one identity pair decrypts under the matching peer session. | Same ciphertext/header under swapped or changed identity associated data refuses without state mutation. | AEAD security itself remains an assumption. |
| REQ-AUTH-09 | export/import after operations | Accepted operation states export and import canonically. | Re-spelled public keys in imported session/prekey bytes refuse as already covered by the persisted-format rows. | This requirement is mostly closed by P4/P5; P6 only ties operation outputs to those readers. |
| REQ-AUTH-10 | initiator/responder establishment and established receive | Ordinary DH and ratchet public keys produce contributory outputs. | A low-order received ratchet public refuses as non-contributory, preserves the persisted session under the model's no-op relation, and leaves the genuine message deliverable. | Initiator and responder low-order establishment controls remain concrete tests outside this operation runner. Curve arithmetic remains abstract. |
| REQ-AUTH-11 | established receive | First delivery of a ratchet message accepts and advances state. | Duplicate delivery refuses or fails authentication without accepting the message twice. | Exact skipped-key eviction branches may need their own sub-slice. |
| REQ-AUTH-12 | responder establishment and prekey lifecycle | One-time curve and KEM ids are consumed only after authenticated responder establishment. Last-resort first delivery records a fingerprint. | Replay of one-time ids refuses `UnknownPrekeyId`; replay of last-resort fingerprint refuses `ReplayedLastResort`; full record refuses `LastResortRecordFull` unchanged. | Near-exhaustion partial replenishment/rotation needs a scope decision. |
| REQ-AUTH-13 | responder establishment and established receive | An accepted initial decrypt commits a responder session and the documented one-time store transition. | A forged initial AEAD tag, a malformed initial wire prefix, and a low-order initiator ephemeral all emit no session and leave the store unchanged. | The runner now covers the documented responder refusal order at its wire and agreement boundaries; independent-reader operation coverage remains open. |
| REQ-CONF-02 | establishment and message operations | A concrete initiator and responder complete a compatible initial-message exchange; the model checks both committed session roles and identity bindings. | KEM refusal or non-contributory DH produces no session/message. | Cryptographic derivation values are fixture outputs, not proved by the operation model. |
| REQ-CONF-04 | send/export and receive/export ordering | Send advances state before ciphertext is allowed to leave; receive advances before acknowledgement. | Importing the pre-operation state demonstrates why persistence ordering is a caller obligation rather than a model guarantee. | Storage atomicity remains outside the crate. |
| REQ-CONF-09 | refusal surface | Refusals collapse to the public error classes already exposed by `Error` and the persisted readers. | Malformed input, bad authentication and unknown ids do not expose secrets or commit speculative state. | Side-channel uniformity remains covered by primitive assumptions and tests, not this model. |
| REQ-FS-03 | prekey lifecycle and responder establishment | One-time private halves are deleted after authenticated use; rotations retire and then wipe old keys. | Unauthenticated initial messages do not delete one-time private halves. | Language-level temporary copies remain a known limitation. |
| REQ-PCS-02 | send/receive Braid transitions | Successful send/receive pairs Braid output with Triple Ratchet epoch and commits both. | Failed Braid becomes terminal and future operations refuse until re-establishment. | Full Braid state-machine coverage is still P7 except for P6's session-level commit contract. |

## Implementation slices

1. **Prekey lifecycle and replay.** `publish`, `replenish`, both rotations,
   identity-mismatch no-ops, authenticated responder one-time consumption,
   last-resort replay-record insertion, replay refusal and one-time replay
   refusal now have Lean structural before/after checks driven by concrete Rust
   execution. Still open in this slice: exhausted-identifier edges and the
   corresponding specification-only reader coverage.
2. **Initial session establishment.** `SessionOperations` now checks the
   persisted initiator-pending and responder-established states after concrete
   Rust handshakes, including role, identity binding and the composed session
   invariant. The runner pairs the accepted exchange with an expected-identity
   refusal before randomness/session creation and a forged-initial `Aead`
   refusal that leaves the responder store unchanged. Signature, KEM and DH
   negative controls still need their own cases.
3. **Established messages and failed agreement.** `SessionOperations` now
   checks durable send and receive transitions, including clearing the
   initiator's pending wrapper only after an authenticated reply. The runner
   checks forged and duplicate message refusals as session no-ops, and checks
   that the message which reveals a Braid failure commits the terminal state
   while later sends and receives refuse unchanged. It additionally compares a
   repeated initial-wrapper receive, third-first delivery followed by both
   skipped messages, and a low-order ratchet-header refusal that leaves both
   the persisted session and the genuine in-flight message intact. Bad signed
   curve and KEM-prekey signatures are checked before the initiator's first
   randomness draw; no session exists on those traces to supply a persisted
   comparison. A responder low-order ephemeral and a malformed initial wire
   prefix each preserve the prekey store under its model no-op relation.
   Specification-only operation-reader coverage remains open.

Each slice must emit a reproducible seed, name the reached requirement rows, and
include at least one deliberate model/runner disagreement before it is counted as
P6 evidence. The final P6 update may raise the orchestration row only for the
operations and refusal effects actually reached.
