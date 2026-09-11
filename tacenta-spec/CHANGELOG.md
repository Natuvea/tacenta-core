# Changelog

All notable changes to the specification. Format: Keep a Changelog; the version
is SemVer against the specified protocol (not the implementation).

## [Unreleased]

### Added
- `protocol/group-messaging.md`: what has been published about group
  messaging, and what each item covers. No Signal specification covers
  groups:
  - Signal's own 2014 description is pairwise fan-out.
  - The Private Group System covers membership privacy against the server,
    not message encryption.
  - Sender keys are described publicly only by WhatsApp's encryption white
    paper and by academic analysis.
  Also added: provenance rules for the page (no mechanism detail is `fact` on
  Signal's authority), and three open questions for a decision record when
  the work is scheduled: sender keys or fan-out, membership privacy against
  the server, and post-quantum signatures and credentials. The page remains
  a scaffold.
- `protocol/session-persistence.md`: a "Validated, not only parsed"
  principle and, per format, the semantic rules the reader refuses on after
  the field-by-field read: for the session, the ratchet private key matching
  the classical ratchet's advertised public key, the sparse ratchet's epoch
  standing in the stated relation to the Braid's (equal in Braid tags 7 to
  10, one behind in tags 0 to 6, exempt when failed), the associated data in
  the role's orientation, the Braid's role agreeing with the session's, an
  unanswered initiator not also being a responder, the two optional fields
  having their shape, and each half satisfying its own crate's invariant,
  refused as *inconsistent*; for the prekey store, the identifier namespace
  (every identifier below `next_id`, none zero, all pairwise distinct across
  every kind) and the record's shape, refused as malformed. The Rejection
  section names the new category. External review, 2026-09.
- `protocol/key-deletion.md`: signed-prekey and last-resort KEM prekey
  rotation, with the retired key kept for exactly one rotation and then
  wiped; what the caller must do around a rotation; and the statement that
  rotation is not scheduled by the crate. The "not implemented" note for
  rotation is removed, since it is.
- `protocol/session-persistence.md`: the prekey store's persisted layout
  (version `0x04`, whose replay-record entries carry the identifier of the
  last-resort KEM key they were made against), and the rule that `0x03`
  (untagged entries, read back tagged with the current key), `0x02` (before
  rotation) and `0x01` (before the replay record) are still read; two
  malformed-store rules for the record, an entry whose identifier names no
  live key and a repeated fingerprint.
- `protocol/message-format.md`: the prekey bundle's wire encoding (type
  `0x03`), which the page named but did not lay out.
- `CONSTANTS.md`: rows for `MAX_SKIPPED_AGE`, `EPOCHS_KEPT`'s value,
  `MAX_LAST_RESORT_SEEN`, the sparse ratchet's `PROTOCOL_INFO`, and the
  classical ratchet's two derivation labels; the prekey-store version row
  now states what is written and what is read.

### Changed
- `protocol/key-deletion.md`, `protocol/session-establishment.md`,
  `protocol/session-persistence.md` and `CONSTANTS.md`: the last-resort
  replay record no longer evicts, and `MAX_LAST_RESORT_SEEN` bounds it **per
  live last-resort KEM key** rather than across the record as a whole. Every
  entry is tagged with the last-resort KEM key its handshake was made
  against and is dropped when a rotation wipes that key, and the record
  fails closed: a last-resort handshake whose fingerprint is not already
  recorded is refused with `LastResortRecordFull`, with nothing decrypted
  and nothing changed, once **the key it names** has spent that key's own
  budget of 1024. So an unauthenticated peer can no longer push a victim's
  fingerprint out of the record with cheap handshakes of its own and replay
  the captured message, and it can no longer spend one key's budget to have
  handshakes against the other refused: the current key and the one the last
  rotation retired each have a budget of 1024, so the record's worst case is
  two budgets. Counting per key is also what makes rotation the lever the
  pages already described it as: the key `rotate_kem` opens starts empty and
  is the key every bundle handed out afterwards names, so one rotation
  relieves a spent budget, where a single shared bound freed nothing until
  the following rotation wiped the retired key.
  `last_resort_record_remaining` reports the room left under the current
  key, the one whose budget the next arrival spends. key-deletion.md and
  session-establishment.md also now say what a replay delivered, the
  initiator's first plaintext a second time as a fresh session, rather than
  calling it a denial of service, and name the operator's levers:
  replenishment and rotation. The pages keep the honest limit -- against a
  peer filling the record deliberately the relief lasts a fraction of a second,
  because they fetch the new bundle too, so the durable defences remain a
  directory that rate-limits bundle fetches and one-time KEM prekeys kept
  stocked. The persisted format is unchanged at `0x04`, which already tags
  every entry with its key; session-persistence.md states the reader's two
  checks, a per-version ceiling on the stored count and the per-key bound as
  a semantic rule over what was read. External review, 2026-09.
- `protocol/session-persistence.md`: the "Validated, not only parsed"
  principle now says what being *inductive* costs the operations, rather
  than only asserting that the predicates are. Three counters reserve their
  ceiling so that no operation can produce a state its own reader refuses:
  the classical ratchet's received-message clock stops at `u32::MAX - 1`
  rather than saturating into `u32::MAX`; an agreement output that would
  advance the sparse ratchet to epoch `u64::MAX` is refused with the
  counter-exhaustion error, since that epoch's retention window covers no
  epoch at all and would retire the chains the advance had just opened; and
  the Braid's two advancing transitions refuse the step onto `u64::MAX`,
  the epoch its own reader already refused. No ceiling is honestly
  reachable (2^32 accepted receives, 2^64 completed agreements), and because
  the Braid's refusing transition also emits an epoch's output, the last
  epoch it completes on both sides is `u64::MAX - 2`. External review,
  2026-09.
- `protocol/key-deletion.md`: the persistence passage says what the reader
  checks an export for (the semantic rules in session-persistence.md) and
  that the check is against corruption, not against a reader of the medium.
- `protocol/session-persistence.md`: the prekey store's record rules (an
  entry under an unknown key, a repeated fingerprint) move from the
  format's own refusals into its semantic rules, beside the identifier
  rules, which the page had not stated.
- `CONSTANTS.md`: `PREKEY_STORE_VERSION` is `0x04` written and `0x03`,
  `0x02`, `0x01` read; `MAX_LAST_RESORT_SEEN` is described as the
  fail-closed, per-key-lifetime bound it now is.
- `protocol/key-deletion.md`: a one-time prekey is deleted once the initial
  message that names it has authenticated, not when the message names it,
  which is what the implementation does and the stronger behaviour. The
  handshake concatenation's wipe is qualified: the buffer's intermediate
  allocations are not wiped until the session crate is re-translated.
- `protocol/session-establishment.md`: the Notation section's description of
  the KDF `info` now matches the Parameters table: the fixed string is passed
  verbatim rather than assembled.
- Citations of scaffold security-property pages in `ratchet.md`,
  `session-establishment.md` and `post-compromise-security.md` now point at
  `tacenta-proofs/CLAIMS.md`, as this directory's README says to; ADR-0001
  notes that the pages it cites are scaffolds.

### Backfilled
Entries this log omitted when the pages landed, recorded here so the log is
complete rather than restarted:

- `protocol/ratchet.md`: the classical Double Ratchet, written from the
  published specification revision 4, Section 3, with the header-encryption
  variant excluded. Its skipped-key store is bounded per chain (`MAX_SKIP`)
  and in total (`MAX_SKIPPED_STORE`), and stored keys expire after a fixed
  number of received messages (`MAX_SKIPPED_AGE`); key-deletion.md records
  the expiry as counting events rather than a timer.
- `protocol/session-establishment.md`: PQXDH, written from the published
  specification revision 3 with X3DH revision 1 for the Diffie-Hellman
  computations it extends. Plain X3DH is excluded.
- `protocol/message-format.md`: the version-and-type framing, the composite
  header, `CONCAT` with a length-prefixed associated data, the initial
  message, and the absent-identifier sentinel. All ours.
- `protocol/key-deletion.md`: every deletion the two specifications require,
  gathered in one place, with what the implementation does and does not do.
- The sparse ratchet's store is bounded in total as well as per chain, an
  addition to the specification, recorded in the conformance manifest.
- A last-resort handshake is fingerprinted and a repeat refused, within a
  bound (`MAX_LAST_RESORT_SEEN`); the prekey store's persisted format went
  to `0x02` to carry the record, and to `0x03` to carry the prekeys a
  rotation retires.
- `protocol/sparse-pq-ratchet.md`: the Sparse Post-Quantum Ratchet, written from
  the published Double Ratchet specification revision 4, Section 5. Specified
  generically over a sparse continuous key agreement, which is treated as a
  boundary in the same way Diffie-Hellman is.
- `protocol/triple-ratchet.md`: the composition of the two message ratchets,
  from Sections 6 and 7.1. Both produce message keys; the encryption key is
  derived from the pair, so an attacker must break both assumptions.
- `protocol/mlkem-braid.md`: the ML-KEM Braid, the sparse continuous key
  agreement the Sparse Post-Quantum Ratchet is specified over. Eleven live
  states plus a terminal failure; the `Ct1Ack` message type is not produced by
  this implementation and is rejected by its decoder.
- `protocol/session-persistence.md`: the bytes a storage layer writes to save a
  `Session` and reads back to restore one. The only page here with no published
  specification behind it -- the Double Ratchet, PQXDH, and Triple Ratchet
  documents specify protocol state and its use, not how an implementation
  persists it between restarts. Entirely ours.

### Changed
- `protocol/ratchet.md`: **the post-quantum ratchet is in scope.** Post-quantum
  protection at session establishment alone does not carry across a session's
  life: the handshake protects a session when it is created and adds nothing
  afterwards, so against an attacker recording traffic for a future quantum
  computer, a long-lived session would be protected by the handshake alone and
  by nothing the ratchet does. Signal's current specification ratchets
  post-quantum continuously, and so does this one -- see the note below.

  The Double Ratchet page itself is otherwise unchanged, and stays that way: the
  composition uses it unaltered.

### Decided
- Old epochs are retired by keeping chains for a bounded number of epochs, the
  approach in the specification's main text, rather than by sealing chains with
  a carried chain length. The second approach leaves the skipped-key store
  unbounded and requires the implementation to supply its own bound, which the
  specification warns about explicitly. We have had to build exactly that
  mechanism for the Double Ratchet; there is no reason to import the problem
  here in order to reuse the solution.

### Note
**Specified and implemented.** The Triple Ratchet and the Braid are integrated
into `Session`: `tacenta-spqr`, `tacenta-braid`, and `tacenta-triple` all ship,
all carry T1 panic-freedom and T3 refinement proofs, and the composite header
carries the agreement's message on every send. The conformance manifest records
the per-component state and is the reference for current coverage.
