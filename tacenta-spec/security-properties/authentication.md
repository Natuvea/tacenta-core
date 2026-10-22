# Authentication

Authentication guarantees, as numbered requirements. They cover five things:
- a session is with the identity key it was established with, and is a
  contact's only when a lookup of that key against the party's records
  finds it that contact's;
- two parties can check that they hold the same pair of identity keys;
- a message a session accepts was made by its peer, for that session and
  position, and is accepted once;
- every key has one encoding;
- input nobody authenticated changes nothing.

## How the requirements are stated

Each requirement has a statement and five entries:

- **Protects:** the assets (threat-model/assets.md).
- **Holds against:** the adversaries (threat-model/adversaries.md).
- **Rests on:** the assumptions (threat-model/assumptions.md).
- **Status:** one of three.
  - *Proved* names the theorem, its tier and the section of
    `tacenta-proofs/CLAIMS.md` that records it.
  - *Assumed* names the assumptions that carry it, and anything proved
    beneath it.
  - *Tested only* names the tests or vectors.
- **Does not cover:** what a reader might take it to cover.

A proved requirement is proved about the model, or about the translated leaf
crates of `tacenta-core`. It is not proved about that implementation's session
layer (ASM-19; limitations.md, LIM-05).

## Session establishment

### REQ-AUTH-01: prekey signatures are verified before use

An initiator accepts a prekey bundle only if two signatures verify under the
bundle's identity key: the one on its signed curve prekey, and the one on its
KEM prekey. Verification is as identities-and-devices.md, Verifying a
signature, states, and it is under an identity key (identities-and-devices.md,
Identity keys), which she checks before either signature. She checks both before any agreement or
encapsulation, and refuses the bundle otherwise (session-establishment.md,
Sending the initial message).

- **Protects:** AS-11, and through it AS-01 and AS-04.
- **Holds against:** ADV-04, and ADV-01 replacing a bundle in transit.
- **Rests on:** ASM-03, ASM-07, ASM-14, ASM-19.
- **Status: tested only.**
  - `a_forged_signed_prekey_is_rejected` and `a_forged_kem_prekey_is_rejected`
    (`tacenta-core/lifecycle/src/lib.rs`).
  - The verifier's accepted set is pinned by the twenty vectors in
    `tacenta-test-vectors/vectors/primitives/xeddsa.json`, and by the tests in
    `tacenta-core/boundary/src/xeddsa.rs`.
  - No proof covers signature verification.
- **Does not cover:**
  - That the identity key is the peer's (ASM-14; REQ-AUTH-02).
  - One-time curve prekeys, which are not signed. A directory that substitutes
    one makes that handshake fail. One that omits it removes that prekey's
    contribution to REQ-FS-05.
  - That a signed prekey is current, or a one-time KEM prekey unused. A
    directory can serve an old bundle (ADV-04).

### REQ-AUTH-02: the initiator's expectation is enforced

The initiator establishes only with an expectation, *known* or *first
contact* (session-establishment.md, Records, expectations and attribution).

She refuses an expectation that holds a non-canonical key, or a *known*
expectation whose record is empty (`MalformedRecord`), before any check of
Sending the initial message.

Then, after the bundle's presence and canonical-key checks, and before the
identity-key rule, the signature checks, the KEM prekey's input checks and
anything that draws randomness or computes an agreement, she refuses a bundle
whose identity key is:
- not an identity key: an invalid identity key, as the identity-key rule
  refuses it;
- under *known*: *retired* in the record (`RetiredIdentity`), or *new*
  (`UnexpectedIdentity`);
- under *first contact*: a key her records' lookup finds a contact's or
  ambiguous (`UnexpectedIdentity`), or a retired key, that is, *same* for no
  contact (`RetiredIdentity`).

An implementation offers establishment under both forms.

- **Protects:** AS-10.
- **Holds against:**
  - ADV-04 serving an old bundle under a key a record retires, under *known*
    or, when that key is *same* for no contact, under *first contact*;
  - ADV-04 serving a recorded contact's bundle under another name, under
    *first contact*;
  - ADV-01 substituting a bundle built around a key the record does not
    accept, under *known*.
- **Rests on:** ASM-14, for the records and for stating first contact only
  for a peer with no record; ASM-19.
- **Status: tested only.** `tacenta-core` makes the refusals in
  `establish_initiator` of `tacenta-core/src/sessions/identity.rs`, which
  `tacenta_core::sessions` offers; the lifecycle leaf's
  `establish_initiator_for`, which it calls once the expectation lets the key
  go on, is internal. Vectors and tests cover it; no proof does.
  - The tests in `tacenta-core/tests/identity_expectation.rs`: both forms,
    `RetiredIdentity`, `UnexpectedIdentity`, `MalformedRecord` before any
    bundle check, the presence and canonical-key refusals ahead of the
    expectation, the identity-key rule first, the expectation ahead of the
    signatures, the KEM prekey's input checks and the agreements, no
    randomness drawn for a refusal by the expectation or for any refusal
    before it, *first contact* with no records against the leaf's own
    establishment, *known* with a key also retired in another contact's
    record, and *first contact* over records that include an empty one.
  - `a_bundle_for_another_identity_than_the_named_one_is_refused_and_changes_nothing`
    (`tacenta-core/tests/full_session.rs`), which now runs under *known*: a
    bundle whose prekey signatures verify under another identity key is
    refused as `UnexpectedIdentity` before any randomness is drawn. It also
    asserts that neither prekey store's bytes change, which holds by
    construction rather than by the check, since establishment takes no
    prekey store.
  - `tacenta-test-vectors/vectors/identity/initiator-expectation.json` (47
    vectors, 5 sessions and 42 refusals): both forms, `RetiredIdentity`,
    `UnexpectedIdentity`, `MalformedRecord` before the presence and
    canonical-key checks, the order above (not the order between the
    presence and canonical-key checks, which the page leaves open), and no random
    value drawn for any refusal before the KEM prekey's input checks.
  - The fuzz target `tacenta-core/fuzz/fuzz_targets/identity_records.rs`,
    which varies the presented key, the records and the bundle's identity
    key, and not the bundle's prekeys or signatures. The hosted workflow
    does not run it.
    `generate-identity-vectors.py` writes the bundles, and each outcome is
    checked against the model's (`Model.InitiatorExpectation`). The
    independent reader reads them.
  - No proof covers it (limitations.md, LIM-13). The model's theorems about
    the order are about the model alone, and `establish_initiator` is outside
    the translated crates, so no result about the lifecycle leaf covers it.
- **Does not cover:**
  - Under *first contact*, an unattributed key: any identity key whose prekey
    signatures verify is accepted, and only a comparison of the verification
    number checks it (REQ-AUTH-16; ADV-04).
  - Under *known*, a key also *same* in another contact's record. She goes
    on, and the session is ambiguous and no contact's (ASM-14).
  - A party that states *first contact* for a peer it holds a record for
    (ASM-14).
  - That the record is right for the contact (ASM-14).
  - A key still in a current set that the contact has stopped using. Bundles
    carry no date (REQ-AUTH-01).
  - That a key the expectation accepts signed the bundle. The signatures are
    checked after it (REQ-AUTH-01).
  - The responder (REQ-AUTH-15).
  - What the refusal reveals to whoever served the bundle (EX-09; LIM-15).

### REQ-AUTH-03: the shared secret binds both identities

`SK` is derived from `DH1 = DH(IKA, SPKB)` and `DH2 = DH(EKA, IKB)`, together
with `DH3`, `DH4` when it is used, and `SS` (session-establishment.md). So:
- An attacker can compute the `SK` a responder derives for an initial message
  naming the identity `IKA` only if it holds `IKA`'s secret, or the responder's
  secret for the signed prekey the message names.
- It can compute the `SK` an initiator derives for a bundle under `IKB` only if
  it holds `IKB`'s secret.

The responder accepts an initial message only if its ciphertext authenticates
under keys derived from that `SK`, and deletes `SK` otherwise
(session-establishment.md, Receiving the initial message).

- **Protects:** AS-10.
- **Holds against:** ADV-01, ADV-04, ADV-06.
- **Rests on:** ASM-01, ASM-02, ASM-03, ASM-05, ASM-06, ASM-14.
- **Status: assumed (ASM-02, ASM-05, ASM-06).** Proved beneath it, neither
  saying that an attacker cannot compute `SK`:
  - The keying material determines the agreement outputs that produced it:
    `km_determines` (T2, CLAIMS.md, "Proved (tier T2, PQXDH's input keying
    material)").
  - The code computes `SK` as the model does: `shared_secret_refines_none` and
    `shared_secret_refines_some` (T3, "Proved (tier T3, the PQXDH derivation
    refines the model)").
- **Does not cover:**
  - An attacker that holds the responder's signed prekey secret. It can make an
    initial message the responder accepts as coming from any identity, until
    that prekey is deleted (limitations.md, LIM-15).
  - Confirmation for the initiator. She learns that her peer holds `IKB`'s
    secret only when a reply decrypts.
  - Replay of the initial message (REQ-AUTH-12).
  - A quantum adversary during the handshake (EX-11).
  - Whose key `IKB` is (ASM-14).

### REQ-AUTH-04: the associated data determines both identities

The associated data `AD = EncodeEC(IKA) || EncodeEC(IKB)` determines both
identity keys, because `EncodeEC` is fixed at 33 bytes
(session-establishment.md, Sending the initial message). Two different pairs of
identity keys never give the same `AD`.

- **Protects:** AS-10.
- **Holds against:** ADV-01 and ADV-04 presenting one pair of identities as
  another.
- **Rests on:** ASM-15, ASM-16 and ASM-17 for the T3 part; ASM-17 for the T2
  part.
- **Status: proved (T2 and T3).**
  - `associatedData_inj_of_length` (T2, CLAIMS.md, "Proved (tier T2, PQXDH's
    input keying material)"): the two identities are recoverable from `AD`,
    given the first encoding's width. The same file gives the counterexample
    without that width, and a test in `tacenta-core` pins the width.
  - `associated_data_refines` (T3, "Proved (tier T3, the PQXDH derivation
    refines the model)"): the code builds `AD` as the model does, with no
    hypothesis.
- **Does not cover:**
  - That every message's authenticated data carries `AD` (REQ-AUTH-05). The
    unproved session layer does that (ASM-19).
  - `EncodeKEM(PQPKB)`, which is not in `AD`. Leaving it out relies on ML-KEM
    binding its key (ASM-04).
  - People. `AD` binds keys (ASM-14).

## Messages

### REQ-AUTH-05: every message's associated data covers the whole header

The associated data of every ratchet message's AEAD is `CONCAT(AD, composite
header)`: `AD`'s length in four bytes, then `AD`, then the whole composite
header, including the agreement's fields (message-format.md, Associated data).
It parses as one pair, so a change to `AD` or to any header field changes the
associated data.

- **Protects:** AS-10.
- **Holds against:** ADV-01, including an attacker that strips the agreement's
  message from a header in flight.
- **Rests on:** ASM-19.
- **Status: tested only.**
  - `concat_ad_is_unambiguous`, a property test in
    `tacenta-core/tests/fuzz.rs`.
  - The vectors `session-associated-data` and `associated-data-differs` in
    `tacenta-test-vectors/vectors/aead/aead-decrypt.json`.
  - `a_tampered_message_is_rejected` (`tacenta-core/tests/full_session.rs`).
- **Does not cover:** that a changed associated data is refused, which is
  REQ-AUTH-06.

### REQ-AUTH-06: a message is accepted only if its tag verifies

A session accepts a ratchet message only if HMAC-SHA256, under the message's
`mac_key`, over the associated data and the ciphertext, equals the message's
32-byte tag.
- The tag is compared in constant time.
- Nothing is decrypted before the tag verifies.
- A padding refusal and a tag refusal are one failure (message-format.md,
  Authenticated encryption).

An attacker without the message key cannot make a message, or change one, so
that a session accepts it.

- **Protects:** AS-01, AS-10.
- **Holds against:** ADV-01. ADV-06 only in the victim's other sessions
  (REQ-CONF-08).
- **Rests on:** ASM-05, ASM-06, ASM-08.
- **Status: assumed (ASM-06).** The receiver's steps are pinned by the thirteen
  vectors in `tacenta-test-vectors/vectors/aead/aead-decrypt.json`, among them
  `tag-altered`, `ciphertext-altered` and `associated-data-differs`. No proof
  covers the AEAD.
- **Does not cover:**
  - Replay of an accepted message (REQ-AUTH-11).
  - The agreement's own authenticator (REQ-AUTH-14).
  - An initial message's outer fields, which no tag covers. A session compares
    or ignores them as session-establishment.md, Receiving the initial message,
    states.

### REQ-AUTH-07: a key determines its session and position

A chain key determines the session it belongs to and its position in that
chain, and so does a message key. Keys of distinct sessions, or of distinct
positions, are distinct.

- **Protects:** AS-10.
- **Holds against:** ADV-01 moving a message between sessions or positions.
- **Rests on:** ASM-01, ASM-06, ASM-10, ASM-17.
- **Status: proved, model-level, against the symbolic attacker.**
  `Properties.Authentication.ckAt_inj` and `Properties.Authentication.mkAt_inj`
  (T2, CLAIMS.md, "Proved (tier T2, model-level security properties against
  the symbolic attacker)").
- **Does not cover:**
  - Bytes, as opposed to terms (ASM-10).
  - Sessions whose seeds coincide, which the model excludes by indexing them
    (ASM-01).
  - A session as `Model.State` holds it. The statement is about one chain per
    session (limitations.md, LIM-03).
  - That a message verifying under a key was made by a holder of that key. The
    file takes that as its premise (ASM-06).

### REQ-AUTH-08: decoders refuse re-spelled curve keys

The decoders of a ratchet message, an initial message and a prekey bundle
refuse every curve public key that is not its canonical encoding. The key's 32
bytes, read little-endian, must be below p = 2^255 - 19 (message-format.md,
Curve public keys).

- **Protects:** AS-11, and through it AS-10 and AS-12.
- **Holds against:** ADV-01, ADV-04 and ADV-06 re-spelling a key.
- **Rests on:** ASM-15, ASM-16, ASM-17.
- **Status: proved (T3 and T1).** Each decoder returns, for every byte string,
  exactly what its model returns, with no hypothesis. The model refuses a key
  that is not canonical.
  - `decode_composite_refines` and `decode_message_refines`: CLAIMS.md,
    "Proved (tier T3, the ratchet-message decoder computes what the model
    says)".
  - `decode_initial_refines`, with `decodeInitial_cases`: "Proved (tier T3, the
    initial-message decoder computes what the model says)".
  - `decode_bundle_refines`, with `decodeBundle_cases` and
    `one_time_prekey_at_spec`: "Proved (tier T3, the prekey bundle decoder
    computes what the model says)".
  - The check computes `canonicalX25519`: `is_canonical_x25519_spec` (T1,
    "Proved (tier T1, the message decoders cannot fail)").
- **Does not cover:**
  - The initiator's own check of a bundle that did not come through the
    decoder. That is tested only:
    `a_bundle_built_with_a_respelled_curve_key_is_refused_before_it_is_used`
    (`tacenta-core/tests/canonical_curve_keys.rs`).
  - Stored keys. For the ratchet state their rule is part of what
    `Ratchet.from_bytes_establishes_inv` proves (CLAIMS.md, "Proved: what a
    decoded state satisfies"). For the session and the prekey store it is
    tested only (`tacenta-core/tests/canonical_curve_keys.rs`).
  - What the session does with a decoded key (ASM-19).

### REQ-AUTH-09: decoders accept one encoding of each value

Each decoder a peer's bytes reach accepts at most one encoding of each value:
every byte string it accepts is the encoding of what it returns
(message-format.md, Principles).

- **Protects:** AS-10, AS-12.
- **Holds against:** ADV-01 re-encoding a message into other bytes that still
  decode.
- **Rests on:** ASM-19.
- **Status: tested only.**
  - `tacenta-core/tests/canonicality.rs` mutates every byte position and
    checks that whatever is accepted re-encodes to itself. Its tests are
    `decode_composite_is_canonical`, `decode_message_is_canonical`,
    `decode_initial_is_canonical`, `decode_bundle_is_canonical`,
    `decode_ec_is_canonical` and `decode_kem_is_canonical`.
  - The decoder-edge vectors in `tacenta-test-vectors/vectors/malformed-input/`
    pin refusals.
  - The T3 refinements of REQ-AUTH-08 carry each decoder to its model. The
    model-level statement that a decoded value re-encodes to its input is not
    proved (triple-ratchet.md, Sending and receiving). CLAIMS.md, "Proved (tier
    T2, the composite header's round trip)", proves the other direction only
    (limitations.md, LIM-08).
- **Does not cover:** persisted formats, whose session and prekey store readers
  re-encode and compare (session-persistence.md). That is tested only as well:
  `session_import_is_canonical` and `prekey_store_from_bytes_is_canonical`.

### REQ-AUTH-10: non-contributory agreements are refused

An agreement output of 32 zero bytes is refused wherever one is computed:
- in the handshake, on both sides;
- on every receive, under both the current and the fresh ratchet private key
  (session-establishment.md, Notation; triple-ratchet.md, Sending and
  receiving).

The refusal changes nothing.

- **Protects:** AS-04, AS-05, AS-12.
- **Holds against:** ADV-01, ADV-04 and ADV-06 sending a low-order public key.
- **Rests on:** ASM-02, ASM-19.
- **Status: tested only.**
  - In `tacenta-core/tests/agreement_and_bounds.rs`:
    `establish_initiator_refuses_a_low_order_bundle_key`,
    `establish_responder_refuses_a_low_order_initiator_key_and_changes_nothing`
    and `decrypt_refuses_a_low_order_ratchet_header_and_changes_nothing`.
  - `low_order_peer_keys_are_rejected` (`tacenta-core/boundary/src/dh.rs`).
- **Does not cover:** a contributory output the attacker knows because it holds
  the private key (ADV-02).

### REQ-AUTH-11: a ratchet message is accepted at most once

A session accepts each ratchet message at most once.
- A stored skipped key is removed when it is used.
- A message on the current receiving chain, numbered below `Nr`, whose key is
  not stored, is refused (ratchet.md, Sending and receiving).
- The sparse ratchet removes a stored key when it is used, likewise.

- **Protects:** AS-10.
- **Holds against:** ADV-01 replaying a ratchet message.
- **Rests on:** ASM-19.
- **Status: tested only.**
  - The reject vector `reject-same-chain-duplicate`
    (`tacenta-test-vectors/vectors/malformed-input/ratchet-reject.json`).
  - `a_same_chain_duplicate_is_refused_and_changes_nothing`
    (`tacenta-core/ratchet/src/lib.rs`).
  - The `Model.Ratchet` examples CLAIMS.md lists under "Evidence, not proof".
  - Proved beneath it, for the classical ratchet:
    - a stored key cannot be served twice:
      `Proofs.KeyErasure.trySkipped_is_once` (T2, CLAIMS.md, "Proved (tier
      T2, the models' skipped-key stores)");
    - the code's lookup does what the model's does: `try_skipped_refines` (T3,
      "Proved (tier T3, the classical Double Ratchet refines the model)").
  - No theorem states that the model refuses every repeat.
- **Does not cover:**
  - An initial message (REQ-AUTH-12).
  - A store rolled back by a writer (EX-07).

### REQ-AUTH-12: an initial message is not accepted twice

A captured initial message does not establish a second session, and the session
it established does not accept it again as a new message:

- **One-time KEM prekeys.** A one-time KEM prekey is deleted once the initial
  message naming it authenticates. A replay then names a prekey the store no
  longer holds.
- **The last-resort path.** A handshake on the last-resort path derives its
  replay identity from `SK` after decapsulation and DH combination, before the
  initial ciphertext is decrypted.
  - It is refused if that identity is already in the record.
  - Its identity is recorded only once it authenticates.
  - The record fails closed: once a key's budget of `MAX_LAST_RESORT_SEEN`
    entries is spent, a new handshake naming that key is refused.
- **An existing session.** It accepts an initial message only if it is a
  responder's session and the message's `ephemeral` and `identity` fields equal
  the establishing message's.

The rules are in session-establishment.md (Receiving the initial message;
Replay, and why the ratchet must follow) and key-deletion.md.

- **Protects:** AS-10, AS-12.
- **Holds against:** ADV-01, ADV-04.
- **Rests on:** ASM-07, ASM-12, ASM-19.
- **Status: tested only.** In `tacenta-core/tests/`:
  - `full_session.rs`: `a_replayed_initial_message_is_rejected`,
    `a_last_resort_handshake_cannot_be_replayed`,
    `a_different_peer_on_the_last_resort_key_is_unaffected`,
    `an_unrelated_initial_message_does_not_take_over_a_session` and
    `the_replay_record_survives_persistence`;
  - `agreement_and_bounds.rs`:
    `a_full_last_resort_budget_refuses_new_handshakes_and_still_refuses_replays`
    and `one_rotation_gives_the_new_key_a_full_budget_and_keeps_the_old_refusals`;
  - the tests in `replay_record.rs`;
  - `canonical_curve_keys.rs`:
    `a_last_resort_first_contact_with_a_respelled_ephemeral_is_refused` and
    `a_repeated_initial_message_must_carry_the_sessions_peer_identity`.
- **Does not cover:**
  - A repeat around a ratchet message the session has not yet read. It yields
    that message's plaintext once, as the unaltered repeat would.
  - A store rolled back to before an entry was recorded (EX-07), or written out
    of order (ASM-12).
  - Honest handshakes refused once a budget is spent (EX-03; limitations.md,
    LIM-19).

### REQ-AUTH-13: unauthenticated input changes nothing durable

A message that is refused, or that does not authenticate, changes nothing
durable. In the session, no counter, chain, stored key, eviction,
Diffie-Hellman step or Braid transition. In the prekey store, no one-time
prekey and no replay-record entry.

The rules are stated in triple-ratchet.md (Sending and receiving),
session-establishment.md (Receiving the initial message), key-deletion.md and
error-handling.md.

- **Protects:** AS-12.
- **Holds against:** ADV-01, ADV-04.
- **Rests on:** ASM-19.
- **Status: tested only.**
  - All six tests in `tacenta-core/tests/failed_decrypt_changes_nothing.rs`.
  - `a_forged_message_moves_none_of_the_three_state_machines`
    (`tacenta-core/tests/post_quantum_stack.rs`).
  - `a_forgery_against_a_full_store_evicts_nothing` and
    `a_forged_header_naming_the_epoch_a_fold_opens_evicts_nothing`
    (`tacenta-core/tests/store_eviction.rs`).
  - `an_uncommitted_receive_changes_nothing`
    (`tacenta-core/braid/src/tests.rs`).
  - `tacenta-core/AUTHENTICATION-BOUNDARY.md` registers the functions that
    consume unauthenticated input, and `tooling/check_authentication_boundary.py`
    checks their signatures against it. It does not read their bodies.
  - `Model.Triple` states the candidate-and-commit shape.
    `Tacenta.UnitTripleT3.commit_refines` (T3) proves only the commit's
    projection. The session's verify-then-adopt is translated but unproved.
- **Does not cover:**
  - A caller that calls a leaf crate's mutating receive directly
    (`AUTHENTICATION-BOUNDARY.md`, "Mutating, and safe only because of a
    caller").
  - An authenticated message from ADV-06, which may evict or age stored keys
    by design.

### REQ-AUTH-14: an authenticator failure ends the agreement

A Braid receive moves the Braid to `Failed` if its header MAC or ciphertext MAC
does not verify, or if its completed `ek_vector` fails validation against the
authenticated header. From `Failed`, a send or a receive yields no key, reports
epoch 0, and leaves the Braid in `Failed` (mlkem-braid.md, Failure).

- **Protects:** AS-07, AS-10.
- **Holds against:** ADV-06. ADV-01 reaches the Braid only through a message
  REQ-AUTH-06 accepts, which needs the session's keys.
- **Rests on:** ASM-04, ASM-05, ASM-15, ASM-16, ASM-17, ASM-18.
- **Status: proved (T3).** `step_receive_refines` and `Braid.receive_refines`
  (`Translation/BraidT3.lean`; CLAIMS.md, "Proved (tier T3, the ML-KEM Braid's
  translated code refines the model)"). The code computes the model's
  transition on every MAC-outcome branch, under `HonestChunk`, `hepoch` and the
  KEM and erasure agreements that section lists. That a failing receive reports
  epoch 0 is `receive_reports` (T2, "Proved (tier T2, the ML-KEM Braid's epoch
  accounting)").
- **Does not cover:**
  - A chunk spliced in from another encoding. `HonestChunk` excludes it and
    the theorems say nothing there. It is tested by
    `a_tampered_header_chunk_abandons_the_session`
    (`tacenta-core/braid/src/tests.rs`).
  - That the MAC cannot be forged (ASM-05).
  - The session refusing `encrypt` and `decrypt` once the Braid has failed.
    That is tested only: `the_message_that_fails_the_agreement_still_returns_its_plaintext`
    (`tacenta-core/tests/full_session.rs`) and `nothing_leaves_the_failed_state`
    (`tacenta-core/braid/src/tests.rs`).
  - A peer that fails the agreement on purpose (ADV-06; EX-03).

## Identity records and verification

### REQ-AUTH-15: keys are classified and looked up as specified

A presented identity key is classified against a record, and looked up
across records, as session-establishment.md (Records, expectations and
attribution) states:
- a presented key that is not an identity key is refused first: as a decode
  failure if it is not canonical, and otherwise as an invalid identity key;
- membership is byte equality;
- *retired* takes precedence within a record;
- every member is checked, and a non-canonical member refuses that record's
  classification (`MalformedRecord`); a canonical member that is not an
  identity key does not;
- a lookup skips and reports such a record;
- a lookup finds a key a contact's, ambiguous, a retired key (*same* for no
  contact), or unattributed.

A session's peer identity key is available to the party.

- **Protects:** AS-10, through the attribution ASM-14 assumes of the party.
- **Holds against:** ADV-01, ADV-04 and ADV-06 presenting a session under a
  key no record accepts, or under a label of a recorded contact, when the
  party attributes as ASM-14 assumes.
- **Rests on:** ASM-14, for the records it is applied to; ASM-19, for the
  peer key's availability.
- **Status: tested only.**
  - The unit tests of `tacenta-core/src/sessions/identity.rs`
    (`classification_over_the_cases`, `classification_ignores_duplicates`,
    `non_identity_members_never_match`, `lookup_over_the_cases`,
    `lookup_refuses_a_presented_key_that_is_not_an_identity_key`), the
    responder tests in `tacenta-core/tests/identity_responder.rs`, and
    `known_and_same_but_retired_elsewhere_establishes_a_contacts_session` in
    `tacenta-core/tests/identity_expectation.rs`.
  - The fuzz target `tacenta-core/fuzz/fuzz_targets/identity_records.rs`,
    which varies the presented key, the records and the bundle's identity
    key, and not the bundle's prekeys or signatures. The hosted workflow
    does not run it.
  - `tacenta-test-vectors/vectors/identity/identity-classification.json`
    (20 vectors) and `identity-lookup.json` (14), generated from the model
    (`Model.IdentityRecords`), and the peer key and lookup fields of the
    sessions in `initiator-expectation.json`. The independent reader reads
    them.
  - No proof covers it. The model's theorems about the classification and the
    lookup are about the model alone.
- **Does not cover:**
  - Attribution itself, which is the party's act (ASM-14).
  - A party that attributes by label, attributes once and never again, or
    records a key without a comparison (EX-09).
  - History. Attribution follows the records now, so a record change
    re-attributes past plaintexts.
  - A key accepted for a contact. It stays *same* for every later bundle and
    message under it, a ghost device's included.
  - An attacker holding the responder's signed-prekey secret (REQ-AUTH-03;
    LIM-15).
  - The prekeys a session consumes before it is attributed.
  - A contact's new device, which is *new* like a substituted key.

### REQ-AUTH-16: the identity pair digest binds the pair

The identity pair digest of two identity keys is the same in either order,
and is computed only from identity keys (identities-and-devices.md).
- **The digest.** Finding two different unordered pairs with the same digest
  is a SHA-256 collision. An attacker that chooses its own key in each of two
  different pairs, the other key of each fixed, needs about 2^128 SHA-256
  evaluations to make their digests equal.
- **The verification number.** The same attacker needs about 10^30, near
  2^100, to make the verification numbers equal. That holds only when all
  60 digits are compared. Comparing k digits costs about 10^(k/2).

- **Protects:** AS-10.
- **Holds against:** ADV-01 and ADV-04 substituting an identity key, at first
  contact or later, against two parties who compare all 60 digits of the
  verification number, computed from their own keys and the key vouched for,
  over a channel the adversary does not control. It covers the keys they
  compared.
- **Rests on:** ASM-07, ASM-14.
- **Status: assumed (ASM-07)** for the binding. Beneath it, the order
  independence, the refusals and the verification number are tested only:
  - the unit tests of `tacenta-core/src/sessions/identity.rs`
    (`the_label_is_the_32_bytes_constants_md_gives`,
    `digest_known_answers_in_both_orders`,
    `the_digest_sorts_as_unsigned_bytes_and_not_otherwise`,
    `digest_refuses_keys_that_are_not_identity_keys`,
    `digest_refuses_non_canonical_keys_as_decode_failures`,
    `digest_with_two_refused_keys_reports_one_of_them`,
    `verification_number_known_answers` and
    `verification_number_in_twelve_groups_of_five`);
  - `tacenta-test-vectors/vectors/identity/pair-digest.json` (38 vectors,
    every pair in both orders) and `verification-number.json` (9), generated
    from the model (`Model.IdentityRecords`) and read by the independent
    reader;
  - the fuzz target `tacenta-core/fuzz/fuzz_targets/identity_records.rs`,
    which checks that the digest does not depend on argument order and that
    the number is 60 digits that grouping keeps, on fuzzed keys. The hosted
    workflow does not run it.

  No proof covers any part. The model's theorems that its digest is the same
  in either order and that its number has 60 digits are about the model
  alone, and nothing proves SHA-256 or its reduction to 60 digits.
- **Does not cover:**
  - Whether and how people compare, how many digits they compare, and over
    what channel (ASM-14; EX-09).
  - Whose keys they are (ASM-14).
  - A copied or stolen identity secret: the key, and so the digest, is the
    same (ADV-02).
  - An attacker holding the responder's signed-prekey secret. It can make
    the responder accept an initial message under the peer's genuine key,
    and the verification number then matches (REQ-AUTH-03; LIM-15).
  - Keys other than the two compared, for example another key in the same
    record (EX-05).
  - A key presented under another contact: no identifier is bound, so a
    comparison made with one contact matches again under another.
