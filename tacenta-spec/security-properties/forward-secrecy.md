# Forward secrecy

An adversary that takes a party's state at some moment (ADV-02) cannot read
messages from before it. This page states that as numbered requirements, and
says how far each is established.

The guarantee rests on two things:
- **A key schedule whose derivations cannot be run backwards.** That is proved
  against a symbolic attacker, and assumed against a real one (ASM-10).
- **Deleting spent secrets.** protocol/key-deletion.md lists the deletions.
  That they are made is proved for the state's contents, and tested, not
  proved, for memory.

Recovering from a compromise is the other direction, and is on the
post-compromise-security page.

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

### REQ-FS-01: a chain key does not reveal the chain's past

An adversary that takes the chain key at step `n` of a chain derives no message
key, and no chain key, of any earlier step of that chain.

- **Protects:** AS-01, AS-05, AS-08.
- **Holds against:** ADV-02 taking one chain key, then acting as ADV-01.
- **Rests on:** ASM-05, ASM-09, ASM-10, ASM-17.
- **Status: proved, model-level, against the symbolic attacker.**
  `Properties.ForwardSecrecy.past_message_keys_are_safe` and
  `Properties.ForwardSecrecy.past_chain_keys_are_safe`
  (T2, CLAIMS.md, "Proved (tier T2, model-level security properties against
  the symbolic attacker)"). LIMITATIONS.md, "Forward secrecy is proved, against
  a symbolic attacker", states what that means.
- **Does not cover:**
  - Later keys of the same chain. The adversary derives every one of them, and
    that is a theorem too (`Properties.ForwardSecrecy.future_message_keys_are_exposed`).
    Recovery is REQ-PCS-01's.
  - Keys still held when the chain key is taken, such as stored skipped keys
    (REQ-FS-04).
  - Bytes, as opposed to terms (ASM-10).
  - A session, as opposed to one chain (limitations.md, LIM-03).
  - The sparse ratchet's chains, whose step also takes the message number and
    which the symbolic model does not state (limitations.md, LIM-04).
  - A copy of an earlier key that erasure missed (ASM-09).

### REQ-FS-02: spent keys are replaced in the state

The state never holds a key the protocol says is spent (key-deletion.md, What
must be deleted, and when):
- a send replaces the sending chain key with its successor;
- a receive replaces the receiving chain key, or removes the stored key it
  used;
- a Diffie-Hellman step replaces the root key and the ratchet key pair;
- the sparse ratchet does the same for its chains, its root key and its stored
  keys.

- **Protects:** AS-05, AS-06, AS-08.
- **Holds against:** ADV-02.
- **Rests on:** ASM-15, ASM-16, ASM-17, ASM-18.
- **Status: proved (T3),** for the classical and sparse ratchets. The code's
  state after `send` and `receive` is related, field by field, to the model's:
  - "Proved (tier T3, the classical Double Ratchet refines the model)":
    `send_refines`, `receive_refines`, `try_skipped_refines`;
  - "Proved (tier T3, the sparse post-quantum ratchet's translated code refines
    the model)": `send_refines`, `receive_refines`, `try_skipped_refines`.

  The model's state holds one root key and one chain key per direction.
  Its lookup removes the key it returns
  (`Proofs.KeyErasure.trySkipped_removes_the_entry`, T2, CLAIMS.md, "Proved
  (tier T2, the models' skipped-key stores)").
- **Does not cover:**
  - Erasure of the replaced bytes from memory (REQ-FS-03).
  - The Braid's secrets, and the handshake's.
  - A state at a counter's last step, which the refinements' headroom premises
    exclude (limitations.md, LIM-07).

### REQ-FS-03: spent secrets are erased from memory

A party erases spent secrets from memory when key-deletion.md says they become
deletable:
- the handshake's ephemeral private key, agreement outputs and `SS`, once `SK`
  is derived;
- a one-time prekey's secret, once the initial message naming it
  authenticates;
- a retired signed or last-resort prekey's secret, at the rotation after the
  one that retired it;
- every secret a ratchet state, a Braid, an identity or a prekey store holds,
  when it is dropped.

- **Protects:** AS-02 to AS-08.
- **Holds against:** ADV-02.
- **Rests on:** ASM-09, ASM-12, ASM-19.
- **Status: tested only.**
  - Three tests fail to build if their type stops erasing when dropped:
    `the_state_erases_when_dropped` (`tacenta-core/ratchet/src/lib.rs`),
    `the_key_pair_erases_when_dropped` (`tacenta-core/src/primitives/kem.rs`)
    and `the_identity_and_the_prekey_store_erase_when_dropped`
    (`tacenta-core/src/sessions/lifecycle.rs`).
  - Two tests check deletions the store makes:
    `a_successful_initial_message_does_consume_its_prekeys`
    (`tacenta-core/tests/failed_decrypt_changes_nothing.rs`) and
    `the_record_follows_its_key_through_rotation_and_leaves_when_it_is_wiped`
    (`tacenta-core/tests/replay_record.rs`).
  - The translation ignores `Drop`, so no proof sees erasure (LIMITATIONS.md,
    "Secret deletion is partial").
- **Does not cover:**
  - The sparse ratchet's, the Braid's and the Triple Ratchet's types. They
    erase when dropped, and no test holds that in place (limitations.md,
    LIM-11).
  - Copies the language, `libcrux-ml-kem` or the allocator make (ASM-09).
  - Persisted bytes (ASM-12).
  - When a caller rotates (ASM-11).

### REQ-FS-04: stored keys are bounded and expire

A message key stored for a message that has not arrived is held only as long as
the pages allow (ratchet.md, Skipped keys; sparse-pq-ratchet.md, Retiring old
epochs):
- a skip beyond `MAX_SKIP` on one chain is refused;
- each store holds at most `MAX_SKIPPED_STORE` keys;
- a classical stored key is deleted at the end of the accepted receive that
  makes it `MAX_SKIPPED_AGE` receives old;
- the sparse ratchet deletes the stored keys of every epoch it retires.

- **Protects:** AS-05, AS-06.
- **Holds against:** ADV-02, and ADV-06 inducing a party to store keys.
- **Rests on:** ASM-11, ASM-15, ASM-16, ASM-17, ASM-18.
- **Status: proved (T2 and T3).**
  - The skip bounds: `skipMessageKeys_growth` and
    `skipMessageKeys_store_bounded` (T2, CLAIMS.md, "Proved (tier T2,
    functional properties of the model)").
  - The code skips and ages the store as the model does:
    `skip_message_keys_refines` and `age_store_refines` (T3, "Proved (tier T3,
    the classical Double Ratchet refines the model)").
  - The sparse ratchet's code skips and retires epochs as its model does:
    `skip_message_keys_refines` and `clear_old_epochs_refines` (T3, "Proved
    (tier T3, the sparse post-quantum ratchet's translated code refines the
    model)").
  - T2, CLAIMS.md, "Proved (tier T2, the models' skipped-key stores)":
    - the model's ageing leaves no key `MAX_SKIPPED_AGE` or more receives old:
      `Proofs.KeyErasure.ageStore_drops_the_expired`;
    - the bound holds over any sequence of operations:
      `Proofs.MemorySafety.reachable_stays_bounded`;
    - the sparse ratchet's store bound:
      `Proofs.SparseRatchetCorrectness.skipMessageKeys_store_bounded`.
- **Does not cover:**
  - A stored key taken before it is used, expired or evicted. That exposure is
    the price of out-of-order delivery.
  - The count's last step. `age_store_refines` needs a step of room, and once
    the count stops at `u32::MAX - 1`, stored keys no longer age
    (limitations.md, LIM-18).
  - Eviction by the session to make room, which is untranslated. It is tested
    in `tacenta-core/tests/store_eviction.rs`.
  - Erasure of the deleted bytes (REQ-FS-03).

### REQ-FS-05: the handshake is forward secret once a prekey secret is gone

`SK` stays secret from an adversary that takes both parties' state after a
handshake, provided at least one of these secrets was deleted before it did:
- the responder's secret for the signed prekey the handshake used;
- the one-time curve prekey's secret, when the handshake used one;
- the decapsulation key of the KEM prekey the handshake used.

Against ADV-03, only the last counts. An adversary that takes only identity
secrets does not learn `SK`.

- **Protects:** AS-04, and through it the session's later keys and AS-01.
- **Holds against:** ADV-02, ADV-03.
- **Rests on:** ASM-01, ASM-02, ASM-04, ASM-05, ASM-09, ASM-11.
- **Status: assumed (ASM-02, ASM-04, ASM-05, ASM-09).** No proof covers it.
- **Does not cover:**
  - When those deletions happen. A one-time prekey is deleted when it is used.
    A signed or last-resort prekey is deleted only at the rotation after the
    one that retires it, and the caller decides when to rotate (ASM-11). Until
    both are deleted, a session established without a one-time curve prekey,
    against the last-resort KEM prekey, has no forward secrecy against a
    compromise of the responder.
  - A copy of a deleted secret that erasure missed (ASM-09).
  - The keys the ratchets derive from `SK` later (REQ-FS-01, REQ-FS-06).

### REQ-FS-06: replaced chains stay secret

An adversary that takes a party's state does not learn the keys of chains the
party has already replaced. A Diffie-Hellman step replaces the root key and
the ratchet private key, and a replaced root key or chain key cannot be computed
from its successors.

- **Protects:** AS-01, AS-05, AS-08.
- **Holds against:** ADV-02.
- **Rests on:** ASM-01, ASM-02, ASM-05, ASM-09.
- **Status: assumed (ASM-05, ASM-09).** The symbolic theorems of REQ-FS-01
  cover one chain. No theorem covers a root step, or a sequence of them
  (limitations.md, LIM-03).
- **Does not cover:**
  - Stored skipped keys of replaced chains, which stay until used, expired or
    evicted (REQ-FS-04).
  - The chains of the epochs the sparse ratchet keeps (sparse-pq-ratchet.md,
    Retiring old epochs).
  - A copy of a replaced key that erasure missed (ASM-09).

## Sources

- Signal's published Double Ratchet specification, **revision 4, 2025-11-04**,
  for forward secrecy, its security considerations on deleting keys, and the
  observation that a compromised chain runs forward unaided.
- Signal's published PQXDH specification, **revision 3, 2023-05-24, last
  updated 2024-01-23**, for the handshake's forward secrecy and the deletion of
  prekey secrets it rests on.
- protocol/key-deletion.md, for every deletion these requirements rest on.
