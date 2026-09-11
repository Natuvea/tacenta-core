# Changelog

All notable changes to the specification. Format: Keep a Changelog; the version
is SemVer against the specified protocol (not the implementation).

## [Unreleased]

### Added
- `protocol/session-establishment.md`: `DecodeEC` accepts exactly one encoding
  of each curve key. It refuses a key whose bit 255 is set, and a key whose
  value is at least p = 2^255 - 19. This is message-format.md's
  single-encoding principle applied to curve keys, which X25519 alone does
  not enforce. An honest key generator produces neither form.
- `protocol/ratchet.md`, `protocol/sparse-pq-ratchet.md`,
  `protocol/key-deletion.md`, `protocol/session-persistence.md`: what
  replacing a stored skipped key does, as built. A skip deletes the stored
  keys in the range it re-derives, then appends the new ones, in number
  order, at the end of the store. So a replacing key carries the count of the
  receive that stored it, not the replaced key's, and is last in the store's
  order, which decides eviction ties and the persisted order. In the sparse
  ratchet only a state read from storage can hold a key to replace. The model
  and the implementation agree. Independent reader, second pass (G2-01).
- `protocol/sparse-pq-ratchet.md`, `protocol/triple-ratchet.md`: the header's
  `pq_epoch` selects the sparse ratchet's receiving chain, and `pq_n` is the
  message number. The epoch the agreement's receive returns is not used and
  is not compared with `pq_epoch`; a returned secret's own epoch is still the
  one the advance checks. The model's receive takes no returned epoch, and the
  implementation discards it. This departs from Double Ratchet revision 4,
  §5.6, whose header carries no epoch and whose receive uses the returned
  one. The page says so and leaves the departure undecided. Independent
  reader, second pass (G2-07).
- `protocol/session-persistence.md`:
  - The erasure encoder's `next` is the index it issues next, left at 65,535
    once `exhausted`, and its chunks are the value's in order. The decoder's
    `size` is the value's length and `needed` its chunk count. Its codewords
    are written in the order each index first arrived, an order that carries
    no meaning and is kept on read (G2-04).
  - The session reader refuses as malformed a presence byte outside
    `0x00`/`0x01`, a `pending_initial` without its layout, and a
    `triple_state` or `braid` its own reader refuses. Each is refused before
    the re-encode check, so none is reported as non-canonical or inconsistent
    (G2-05).
  - The ratchet and sparse ratchet readers refuse as malformed a presence tag
    outside `0x00`/`0x01`, an absent key or chain that is not zeroed, and an
    unknown `labels` or `direction` tag. These were implied only by the
    Canonical principle (G2-06).
- `protocol/message-format.md`: how the composite-header vectors name its
  fields. The input `chunk_data` is the field `chunk`, and `chunk_present`,
  `chunk_index` and `chunk_data` together encode one optional codeword, with
  all-zero padding when it is absent. The `inputs` description in
  `tacenta-test-vectors/schema/vector.schema.json` points there. No vector
  field is renamed. Independent reader (G-09).
- `protocol/session-establishment.md`, "The fingerprint": the last-resort
  replay fingerprint's construction (reader gap G-26).
  - It is HMAC-SHA256 keyed with the 32-byte label
    `tacenta last-resort handshake v1`. The input is the initial message's
    `identity`, `ephemeral` and `kem_ciphertext`, each prefixed with a 4-byte
    big-endian length, then `one_time_prekey_id` and `kem_prekey_id`, 4 bytes
    each, big-endian.
  - It is computed before decapsulation, matched against every entry whatever
    its tag, and recorded only once the initial ciphertext authenticates.
  - Its curve-key inputs are the canonical encodings `DecodeEC` accepted. This
    is the property security advisory GHSA-cgvw-9r5f-xrxp turned on: a
    re-spelled key gave a captured last-resort first contact a second
    fingerprint.
  - `CONSTANTS.md` has a row for the label. `protocol/key-deletion.md` and
    `protocol/session-persistence.md` point to the construction rather than
    repeat it.
- `protocol/session-establishment.md`, "Primitives, and what is left to them":
  what the protocol requires of X25519 and ML-KEM-1024, and what it leaves to
  RFC 7748, FIPS 203 and the libraries (register item D-3).
  - **X25519:** unclamped storage, `decodeScalar25519` clamping at each use,
    and which peer keys reach RFC 7748's masking and reduction of the
    u-coordinate.
  - **ML-KEM-1024:** the section 7.2 encapsulation-key check with the
    bundle's refusal, the 64-byte key-generation and 32-byte encapsulation
    randomness, implicit rejection kept on decapsulation, and the section 7.3
    hash check made when a store is read.
- `protocol/message-format.md`, "Authenticated encryption": CBC is defined
  (NIST SP 800-38A, section 6.2). `enc_key`, `mac_key` and `iv` are bytes 0-31,
  32-63 and 64-79 of the 80-byte message-key expansion, and the IV is not sent.
  A delegation paragraph names FIPS 197, SP 800-38A, RFC 5652 section 6.3,
  RFC 2104 and FIPS 180-4, and says that nothing observable is left to the
  libraries (G2-02, D-3).
- `protocol/identities-and-devices.md`, "Signing": XEdDSA clamps the 32-byte
  identity secret as X25519 does before `calculate_key_pair`. The page gives
  the whole signing computation, and says why the clamp is needed for `A` to
  be the published key (G-27). `CONSTANTS.md` has a row for the `hash_1`
  prefix.
- `protocol/identities-and-devices.md`, "Verifying a signature": the verifier's
  accepted set as six rules, and where it departs from XEdDSA revision 1 in
  each direction (G-28):
  - a canonical `u` with a point on the curve;
  - the signature's top bit as the sign of `A`;
  - `A` not of small order;
  - `s` below the group order;
  - `R` equal byte for byte to the encoding of `sB - hA`;
  - `R`'s point not of small order.
- `protocol/session-persistence.md`, "Braid": the consequence of delegating the
  `key_pair` and `encaps` layouts to `libcrux-ml-kem`. An implementation
  without that serialisation cannot import or export tags 1-4 and 7-9, and can
  move tags 0, 5, 6, 10 and 11 (G2-08). The reader checks nothing in either
  field beyond its length.
- `protocol/mlkem-braid.md` now states the ML-KEM Braid itself, where it
  used to defer to the published document. It is written as built:
  - "Parameters and derivations":
    - the sizes of the values the Braid sends, and `ToBytes` as eight
      big-endian bytes;
    - the bytes of `PROTOCOL_INFO` and the four suffixes;
    - the epoch key `KDF_OK`: HKDF-SHA256 with a 32-byte zero salt, the KEM
      shared secret as input, `PROTOCOL_INFO || ":SCKA Key" ||
      ToBytes(epoch)` as `info`, and 32 bytes out;
    - the ratcheted authenticator: `Init(1, SK)` from a zero root key, with
      `SK` the PQXDH output itself; each update's 64-byte HKDF output, split
      into root key then MAC key; and the `:ekheader` and `:ciphertext` MAC
      inputs;
    - when each is computed and checked.
  - "Messages": the fields, the six types, and what a Braid message puts in
    the composite header.
  - "The state machine": initialisation; the eleven states with what each
    holds; what each state sends; the thirteen transitions, numbered on the
    page; what a send and a receive return; when an epoch completes; and what
    `Session` does with the results.
- `CONSTANTS.md`: rows for the Braid's MAC length, its epoch encoding, the
  layout of its `info` strings and MAC inputs, its derivation salts and
  lengths, its authenticator's initial state, and its preshared secret.
- `decisions/ADR-0007-behaviours-kept-as-built.md`: three behaviours the pages
  recorded as built and undecided are kept. The header's `pq_epoch` selects
  the sparse ratchet's receiving chain; the leaf readers enforce exactly their
  stated rules; a Braid receive taking transition (5) reports the epoch it
  completed. `sparse-pq-ratchet.md`, `session-persistence.md` and
  `mlkem-braid.md` cite the record where each is stated.

### Changed
- `protocol/message-format.md`, `protocol/session-establishment.md`: every
  curve public key a peer sends is refused unless it is the canonical
  encoding, its 32 bytes read as a little-endian integer below
  p = 2^255 - 19. This extends `DecodeEC`'s rule to the keys the wire carries
  raw: a prekey bundle's `identity_key`, `signed_prekey` and present
  `one_time_prekey`, and a ratchet message's `dh`. Each decoder refuses a
  re-spelled key as a decode failure. A new section of message-format.md,
  "Curve public keys", states the rule once and lists every position. The
  Primitives section of session-establishment.md no longer says those keys
  reach X25519 as received. The bundle's identity key was already held to the
  rule when its signatures are verified (identities-and-devices.md, Verifying
  a signature), and still is. Defence in depth: a key's bytes are its identity
  in the signatures, the associated data, the replay fingerprint and the
  skipped-key store, and an honest key generator produces no refused form
  (register item J-3).
- `protocol/session-persistence.md`: the "Validated, not only parsed"
  principle no longer reads as refusing every state no constructor builds.
  Each type's `invariant` is the set of relations its operations and their
  proofs rely on. Each list of semantic rules is complete, and a state that
  keeps every rule is accepted even where no operation produces it. The leaf
  formats' section names such states the readers accept: a ratchet state with
  `nr` or `ns` above zero and no chain for it, and a sparse ratchet state with
  a stored key numbered 0, or at or past its chain's counter. This is what
  the readers do. The session's rule that each half satisfies its own rules
  now says a half that breaks them is refused as malformed by its own reader
  first. Independent reader, second pass (G2-12).
- `protocol/session-establishment.md`, "Sending the initial message": the
  initial ciphertext's key is stated as the path it takes from `SK`, instead of
  "under `SK` (or a key derived from it)" (G2-09). The path runs through the
  split, the Double Ratchet's initialisation and first chain step, the sparse
  ratchet's first send, the combination, the message-key expansion, and the
  AEAD with `CONCAT(AD, composite header)`.
- `CONSTANTS.md`: the XEdDSA sign-bit row no longer describes the verifier by a
  library function (`verify_strict`). It points to the rules in
  `protocol/identities-and-devices.md` (G-28). The row for the KEM key pair and
  encapsulation state lengths names the import consequence.
- `protocol/mlkem-braid.md`:
  - "What a receive ignores" and "Failure" cite transitions numbered on the
    page itself.
  - The published document is cited as the source this page is written from,
    no longer as authoritative over it (ADR-0006).
  - The page records two more places where the tree reads or departs from
    that document:
    - a receive that completes an epoch, at transition (5), reports that
      epoch, where the document reports the one before;
    - the epoch in the two MAC inputs, written bare there, is `ToBytes(epoch)`
      here.

### Fixed
- `protocol/ratchet.md`: the Message format and Sources sections said the
  header and ciphertext encodings and the byte-level conventions were pinned
  in the conformance manifest, determined under the interoperability research
  boundary. They are ours, recorded in `CONSTANTS.md` and on
  message-format.md, and no peer determined them. The conformance manifest
  credits the ratchet's initialisation to the Initialisation section rather
  than to Sending and receiving (G2-03).
- `protocol/ratchet.md`: "range-checked the same way" for the numbers skipped
  keys are stored under. Every such number is below the header's 32-bit `PN`
  or `N`, so it is at most `u32::MAX - 1` and none is out of range (G2-10).
- `protocol/sparse-pq-ratchet.md`: the initialisation salt is 32 zero bytes,
  as in the model and the implementation (G2-11).

## [0.1.0] - 2026-09-11

The first citable revision. It contains everything recorded above that was under
Unreleased until now.

The specification is normative (ADR-0006):
- the written pages and `CONSTANTS.md` define the protocol;
- the model states them formally;
- `tacenta-core` is one implementation of them.

**Written:**
- PQXDH session establishment;
- the Double Ratchet, the Sparse Post-Quantum Ratchet and the Triple Ratchet;
- the ML-KEM Braid and its erasure code;
- the message format and its authenticated encryption;
- the bounded protobuf profile;
- session persistence;
- key deletion;
- error handling;
- the identity key and application signatures.

**Scaffolds, and so unspecified:** devices, group messaging, and the
security-property pages, whose claims are in `tacenta-proofs/CLAIMS.md`.

**How far the text is enough:** a reader written from this text and the
vectors alone, with no access to the implementation, the model or the proofs,
passes all 79 vectors and 145 refusal and boundary cases drawn from the pages'
sentences (`tacenta-test-vectors/runners/independent`).

What that reader could not build from the text is recorded in its `GAPS-2.md`:
- chiefly the Braid's state machine, epoch key derivation and authenticator,
  which still come from the published ML-KEM Braid document;
- a set of smaller wording gaps.

Closing those is the work for the next minor revision. This release closes the
reader's G-01, "No citable spec revision".

### Added
- The decoders now enforce two of `protocol/message-format.md`'s refusals at
  decode, in the model and in `tacenta-wire`: the initial-message decoder
  refuses an `identity` or `ephemeral` whose first byte is not the `EncodeEC`
  curve byte `0x05`, and the bundle decoder refuses a `kem_prekey_len` other
  than 1,568 bytes. `CONSTANTS.md` has a row for that length, the ML-KEM-1024
  encapsulation-key length.
- `protocol/message-format.md`:
  - An "Authenticated encryption" section: AES-256-CBC with PKCS#7, then
    `HMAC-SHA256(mac_key, AD || ciphertext)` with the full 32-byte tag
    appended. The tag is checked before decryption, and every refusal is one
    authentication failure.
  - The initial-message decoder's refusals, including an `identity` or
    `ephemeral` without the `EncodeEC` curve byte.
  - A bundle's KEM prekey length other than the KEM's key length is a decode
    failure.
  - How identifier `0` is treated in each position.
  - Rejection's restraint is about what a peer learns.
- `protocol/mlkem-braid.md`: the KEM split and `ek_vector` validation, with where
  they depart from the published document (the header hash's input order, and
  the added modulus check); the
  erasure code exactly (the GF(2^16) representation and reduction polynomial,
  chunking, systematic codewords, encoder exhaustion, first-copy-wins
  decoding); what a receive ignores; every transition to `Failed`; and, at the
  epoch ceiling, the step onto `u64::MAX` is refused, and in `Ct2Sampled` at
  `u64::MAX - 1` so is any received message.
- `CONSTANTS.md`: the GF(2^16) reduction polynomial `0x1100B`. The
  presence-byte row now says where an absent field keeps its full width.
- `protocol/session-persistence.md`: the principle on the Braid's states now
  says the tag identifies the state and callers cannot construct or inspect
  one.
- `protocol/ratchet.md`, `protocol/sparse-pq-ratchet.md`,
  `protocol/triple-ratchet.md`, `protocol/session-persistence.md`,
  `protocol/key-deletion.md`, `CONSTANTS.md`: the ratchet behaviour the pages
  did not state, as built.
  - The Double Ratchet's initialisation for both roles, its 80-byte
    message-key expansion, when a DH step triggers, the separate `MAX_SKIP`
    check on the skip to `PN`, the no-chain refusals and counter ceilings,
    and the exact expiry boundary (a skipped key serves the next
    `MAX_SKIPPED_AGE - 1` accepted receives).
  - The sparse ratchet's send counter and chain choice, its counter ceiling,
    refusals, retention rule, and `info` joining with no separator.
  - The Triple Ratchet's split parameters and order, and its commit rules:
    classical half first, send on a copy, and receive yielding a candidate
    adopted only after authentication. Its 32-byte combination is expanded
    by the message-key expansion rather than being the encryption key.
  - Big-endian integers and meaningful entry order in the two ratchet state
    formats.
- **Decided:** a message that would push a skipped-key store past
  `MAX_SKIPPED_STORE` is not refused. The receiver evicts the store's oldest
  keys on a working copy and retries, adopting the copy only if the message
  authenticates. This amends the earlier refuse rule to match the
  implementation. Eviction order is specified; batch size is
  implementation-defined. A delayed message whose key was evicted can no
  longer be decrypted.
- `protocol/protobuf-profile.md`: the bounded protobuf profile for the external
  ratchet message body and prekey envelope, restated from `Model.Protobuf`. It
  covers:
  - the four bounds;
  - minimal, five-byte, 32-bit varints;
  - tags limited to fields 1 to 15 and wire types 0 and 2;
  - length-delimited fields;
  - the two field tables: all five ratchet body fields are required, and
    envelope field 1 is the only optional field;
  - free field order, with re-encoding not required to reproduce the input;
  - no validation inside fields;
  - refusal categories as implementation-defined.
  The page states that the engine's own `Session` path does not use the
  profile. `CONSTANTS.md` now gives the profile's field numbers and limits as
  values, replacing "see implementation", and records that no external
  message version byte is handled here.
- `protocol/error-handling.md`, previously a scaffold, now says what the
  protocol requires of a refusal and what it leaves to an implementation.
  - Required: every refusal a page states; decode failure kept distinct from
    authentication failure; the persistence refusal kinds; and the conditions
    the pages name for a caller to act on.
  - Left to an implementation: its error types, their names, which variant
    reports a refusal, and the order of checks, unless a page fixes one.
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
- `README.md`: a "Normative status" section. This specification is
  normative; implementations, `tacenta-core` included, are not; a change to
  anything it defines lands here first; and a scaffold page's topic is
  unspecified rather than defined by the code (ADR-0006).
- `protocol/session-persistence.md`:
  - the Braid's persisted fields for each of its twelve state tags, with each
    field's length or sub-format, and what the Braid's reader refuses;
  - the erasure encoder's and decoder's sub-formats, with the bounds a reader
    applies before narrowing a 64-bit size;
  - "Semantic rules of the leaf formats": the rules the ratchet, sparse
    ratchet, triple ratchet, Braid and erasure readers enforce, which the
    page had left to each crate's `invariant`.
  `CONSTANTS.md`: rows for `MAX_CODEWORDS`, the Braid's KEM field lengths,
  and the KEM key-pair and encapsulation-state lengths.
- Session-layer and prekey-store behaviour the pages did not state, as built:
  - `protocol/identities-and-devices.md`, previously a scaffold, now covers
    the identity key's secret and application signatures. The secret is 32
    bytes, exported and imported as they are, and serves as both the X25519
    private scalar and the XEdDSA private key. An application signature is
    XEdDSA under the identity key over
    `"tacenta:application-signature:v1" || 0xFF || message`. Devices remain a
    scaffold.
  - `protocol/session-establishment.md`: a non-contributory Diffie-Hellman
    output is an all-zero one, the X25519 library's definition. A repeated
    initial message on an existing session is accepted only by a responder's
    session, and only if its `ephemeral` equals `established_ephemeral` byte
    for byte; otherwise it is refused (`NotARepeatedInitial`).
  - `protocol/triple-ratchet.md`: every receive refuses a header whose
    ratchet public key gives a non-contributory output under the current or
    the freshly generated ratchet private key. The check runs before either
    ratchet runs and before authentication.
  - `protocol/mlkem-braid.md`: the message whose receipt fails the Braid is
    still accepted and its plaintext returned.
  - `protocol/session-persistence.md`: the prekey store's `kem_pair` layout
    (`dk` then `ek`, 4,736 bytes) and the four checks its reader makes,
    replacing "opaque". Also, what the one-time lists' order means and how
    `publish`, `publish_one_time_batch` and `publish_multi_use` choose from
    them. The session's role rule now says the Braid's half is skipped once
    the Braid has failed.
  - `protocol/key-deletion.md`: how `create_prekeys` numbers identifiers, and
    how `replenish` stops at the end of the identifier space.
  - `protocol/message-format.md`: the implementation takes AES, CBC and
    PKCS#7 from libraries, and this page defines the behaviour.
  - `CONSTANTS.md`: rows for the application signature label and the
    `kem_pair` layout. `README.md`: the status paragraph names
    identities-and-devices.md as partly written.
- `protocol/key-deletion.md`: the bound on `create_prekeys` at the end of the
  identifier space. A count above `2^31 - 2` makes `2^31 - 2` one-time
  prekeys of each kind and leaves `next_id` at `u32::MAX`. `u32::MAX` is never
  issued, and no identifier wraps or repeats.

### Changed
- `protocol/ratchet.md`, Sending and receiving: the classical ratchet now
  refuses, itself, a message whose ratchet key equals `DHr`, whose number is
  below `Nr` and whose key is not stored, as the page says. It used to take
  such a message as the one at `Nr`: it derived that key, advanced the
  receiving chain and counted a received message, and only the session's
  AEAD then turned the message away, on a copy the session discarded. The
  model's `receive` returns no result there, and the implementation returns
  `OutOfOrder`, the error the sparse ratchet already returns in the
  analogous case, with the state unchanged. The page's text is unchanged;
  this records that the model and the implementation now match it.
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

### Fixed
A read of every written page against the model and the code, 2026-09. No byte
value, width, offset, label, derivation or bound was wrong. These statements
were:
- `protocol/session-establishment.md`:
  - `SK` is expanded by a key derivation, not split in two, and the §7.1 it
    cited is the Double Ratchet specification's;
  - `CT` is kept and resent with every message until one from the responder
    decrypts, not deleted after sending;
  - the initiator's refusals besides signatures, and the last-resort
    fingerprint's identifiers, are now named.
- `protocol/key-deletion.md`: the stale "growing buffer" limitation, the
  inconsistent timing figures, and a garbled clause.
- `protocol/message-format.md`:
  - the decoder does have a loop, a fixed-width padding check;
  - a field running to the end of its message has no length prefix;
  - the ratchet-message decoder's other refusals are listed, with the note
    that `ag_type` is not tied to the presence byte.
- `protocol/post-compromise-security.md`: the guarantee is narrowed to the
  next chain key and root key, which is what the theorems prove.
- `protocol/sparse-pq-ratchet.md` and `protocol/triple-ratchet.md`: the
  sparse ratchet's derivation parameters, which chain key each direction
  sends on, message numbering from one, the reserved final epoch, and the
  composite header's epoch fields.
- `protocol/session-persistence.md`: the semantic rules it promised, the
  non-canonical refusal, count versus length, version annotations, and the
  sub-formats having no version byte.
- `CONSTANTS.md`: `ABSENT_ID` and the wire presence byte had no entry.
- The model (`tacenta-model`), which states this specification formally,
  described a ratchet message as the Double Ratchet's forty-byte header
  alone, a format `protocol/message-format.md` does not accept. It now follows
  the composite header.
- The model's Braid reported, on a receive that moves it to `Failed` (a MAC
  that does not verify, or an `ek_vector` that fails the header hash), the
  epoch before the one it failed at. It now reports epoch 0, as
  `protocol/mlkem-braid.md` ("Failure") and the implementation do.

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
- **This specification is the product, and implementations conform to it**
  (`decisions/ADR-0006-specification-is-normative.md`). The written pages and
  `CONSTANTS.md` are normative. The model states them formally, and its
  vectors are normative examples. `tacenta-core` is one implementation and is
  not normative. Changes land here first. The specification's sufficiency is
  to be tested by a reader written from it and the vectors alone.

### Note
**Specified and implemented.** The Triple Ratchet and the Braid are integrated
into `Session`: `tacenta-spqr`, `tacenta-braid`, and `tacenta-triple` all ship,
all carry T1 panic-freedom and T3 refinement proofs, and the composite header
carries the agreement's message on every send. The conformance manifest records
the per-component state and is the reference for current coverage.
