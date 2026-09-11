# Authentication

Authentication guarantees, as numbered requirements. They cover four things:
- a session is with the identity key it was established with;
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
signature, states. She checks both before any agreement or encapsulation, and
refuses the bundle otherwise (session-establishment.md, Sending the initial
message).

- **Protects:** AS-11, and through it AS-01 and AS-04.
- **Holds against:** ADV-04, and ADV-01 replacing a bundle in transit.
- **Rests on:** ASM-03, ASM-07, ASM-14, ASM-19.
- **Status: tested only.**
  - `a_forged_signed_prekey_is_rejected` and `a_forged_kem_prekey_is_rejected`
    (`tacenta-core/src/sessions/mod.rs`).
  - The verifier's accepted set is pinned by the twenty vectors in
    `tacenta-test-vectors/vectors/primitives/xeddsa.json`, and by the tests in
    `tacenta-core/src/primitives/xeddsa.rs`.
  - No proof covers signature verification.
- **Does not cover:**
  - That the identity key is the peer's (ASM-14; REQ-AUTH-02).
  - One-time curve prekeys, which are not signed. A directory that substitutes
    one makes that handshake fail. One that omits it removes that prekey's
    contribution to REQ-FS-05.
  - That a signed prekey is current, or a one-time KEM prekey unused. A
    directory can serve an old bundle (ADV-04).

### REQ-AUTH-02: a named identity is enforced

When the initiator names the identity key she means to reach, she refuses a
bundle whose identity key is any other, before encapsulating
(session-establishment.md, Sending the initial message).

- **Protects:** AS-10.
- **Holds against:** ADV-04, and ADV-01 substituting a bundle built around
  another identity key.
- **Rests on:** ASM-14, for the key she names; ASM-19.
- **Status: tested only.** `tacenta-core` makes the refusal in
  `establish_initiator_for` (`UnexpectedIdentity`).
  `a_bundle_for_another_identity_than_the_named_one_is_refused_and_changes_nothing`
  (`tacenta-core/tests/full_session.rs`) exercises it. It offers a bundle whose
  prekey signatures verify under another identity key, and checks two things:
  the refusal is `UnexpectedIdentity`; and no randomness is drawn before it, so
  nothing is encapsulated. It also asserts that neither prekey store's bytes
  change, which holds by construction rather than by the check, since
  `establish_initiator_for` takes no prekey store. No vector or proof covers it
  (limitations.md, LIM-13).
- **Does not cover:** an initiator that names no key. `establish_initiator`
  accepts any identity key whose prekey signatures verify.

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
    untranslated session layer does that (ASM-19).
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
  - `low_order_peer_keys_are_rejected` (`tacenta-core/src/primitives/dh.rs`).
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
- **The last-resort path.** A handshake on the last-resort path is
  fingerprinted before decapsulation.
  - It is refused if the fingerprint is already in the record.
  - Its fingerprint is recorded only once it authenticates.
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
    projection. The session's verify-then-adopt is untranslated.
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
