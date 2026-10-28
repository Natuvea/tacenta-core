# Changelog

All notable changes to the specification. Format: Keep a Changelog; the version
is SemVer against the specified protocol (not the implementation).

## [Unreleased]

### Added
- `protocol/identities-and-devices.md`: the identity pair digest
  (`PAIR_DIGEST_LABEL`) and the verification number. The pages had left
  identity-key comparison to the application (EX-09). The key order, the
  comparator, the encoding and the treatment of keys that are not identity
  keys each give different bytes, and the page fixes each of them: the
  digest takes identity keys only, under the identity-key rule. The number's
  bound is stated with the digits it needs, and is assumed (REQ-AUTH-16).

- `protocol/session-establishment.md`, Records, expectations and
  attribution:
  - records, the classification and the lookup, which every implementation
    provides. A presented key is held to the identity-key rule; a record's
    members are held to the canonical encoding only;
  - attribution by lookup, against the records as they stand, with labels
    never selecting a record. An application shows a plaintext as a
    contact's only while a lookup finds its session that contact's;
  - keys the lookup finds ambiguous or retired (*same* for no contact)
    attributed to nobody;
  - unattributed first-contact sessions in both roles;
  - initiator expectations, *known* and *first contact*, the latter checked
    by a lookup over her records;
  - no persisted format changes.

- `security-properties/authentication.md`: REQ-AUTH-15 and REQ-AUTH-16.
  - REQ-AUTH-15, keys are classified and looked up as specified, is tested
    only: the classification and lookup unit tests in
    `tacenta-core/src/sessions/identity.rs`,
    `tacenta-core/tests/identity_responder.rs`,
    `identity-classification.json`, `identity-lookup.json` and the
    `identity_records` fuzz target.
  - REQ-AUTH-16, the identity pair digest binds the pair, is assumed
    (ASM-07). The order independence, the refusals and the number beneath
    it are tested only: the digest and number unit tests,
    `pair-digest.json`, `verification-number.json` and the
    `identity_records` fuzz target.
  - No proof covers either. The theorems about `Model.IdentityRecords` and
    `Model.InitiatorExpectation` that `tacenta-proofs/CLAIMS.md` records
    (tier T2) are about the model alone.
  - `evidence-index.json` has an entry for each, citing those tests,
    vectors and theorems and LIM-15, with a `proof` item saying that
    `tacenta-core`'s functions are outside the translated crates.

- `tacenta-test-vectors/vectors/identity/`: vectors for the identity pair
  digest (`pair-digest.json`, every pair in both orders), the verification
  number (`verification-number.json`), the classification and the lookup
  (`identity-classification.json`, `identity-lookup.json`), generated from
  the model, and for initiator establishment under an expectation
  (`initiator-expectation.json`: signed bundles written by
  `generate-identity-vectors.py`, each case's outcome checked against the
  model). The vector schema names their refusals and adds
  `acceptable_refusals`, for a digest whose two keys are refused with
  different kinds. `evidence-index.json` cites them for REQ-AUTH-02, -15 and
  -16. `bundle-admission.json` is unchanged: its runner establishes each
  case under *first contact* with no records. No existing vector changes.
  Three of the initiator vectors pin orders the fourteenth independent
  reader pass found unpinned (`GAPS-14.md`): a malformed expectation before
  the presence and canonical-key checks, and, for a KEM prekey of the wrong
  length whose signature does not verify, the signatures before the KEM
  prekey's input checks.

- `identities-and-devices.md` now specifies the bounded hosted device-inventory
  statement profile: its canonical unsigned encoding, bounds, refusal rules,
  issuer-signature input and replacement-binding commitment. This is an
  inventory statement format only; general device management and group
  messaging remain scaffolded.

- `group-messaging.md` now specifies the two bounded fan-out commitment helper
  domains and their 32-byte SHA-256 outputs. It does not select a group cipher
  or membership protocol.

- `security-properties/evidence-index.json`: migrated `REQ-FS-01` through
  `REQ-FS-06` and `REQ-PCS-01` through `REQ-PCS-03` into the checked evidence
  index, completing coverage for all 32 security-property requirements. The
  traceability checker now fails if any requirement lacks an evidence-index
  entry, and its case runner includes a missing-entry negative control.

- `security-properties/evidence-index-format.md`: the checked JSON format for
  the P2 requirement evidence index, including the boundary between reference
  validation and human semantic review.
- `security-properties/evidence-index.json`: a P2 pilot evidence index for
  REQ-AUTH-04, REQ-AUTH-01 and REQ-AUTH-03, covering one proved requirement,
  one tested-only requirement and one assumed requirement with supporting
  derivation proofs.
- `security-properties/evidence-index.json`: evidence-index entries for
  REQ-AUTH-02, REQ-AUTH-05 and REQ-AUTH-06, extending the P2 migration across
  named identity checks and ratchet-message associated-data/AEAD coverage.
- `security-properties/evidence-index.json`: evidence-index entries for
  REQ-AUTH-07, REQ-AUTH-08 and REQ-AUTH-09, extending the P2 migration across
  model-level key-position uniqueness and decoder canonicality coverage.
- `security-properties/evidence-index.json`: evidence-index entries for
  REQ-AUTH-10, REQ-AUTH-11 and REQ-AUTH-12, extending the P2 migration across
  non-contributory agreement refusal, ratchet replay refusal and initial-message
  replay-record coverage.
- `security-properties/evidence-index.json`: evidence-index entries for
  REQ-AUTH-13 and REQ-AUTH-14, completing the authentication P2 migration with
  unauthenticated-input durability and Braid authenticator-failure coverage.
- `security-properties/evidence-index.json`: evidence-index entries for
  REQ-CONF-01 through REQ-CONF-09, extending the P2 migration across
  confidentiality assumptions, derivation proofs, symbolic secrecy claims, AEAD
  vectors and timing-test evidence.
- `ASSURANCE-OBLIGATIONS.md`: the first P1 obligation inventory for the
  assurance execution plan. It classifies target deficits, gate obligations,
  deferral risks and missing negative-control evidence so readiness is assessed
  from named rows rather than inferred from prose.
- `tooling/check-traceability.py` and
  `tooling/tests/run-check-traceability-cases.sh`: a CI-enforced structural
  traceability check for the security-property ledger. It checks that every
  `REQ-*` row has status and assumptions, the limitations status table covers
  those rows, direct assumption dependencies name live `ASM-*` entries, and
  `REQ/ASM/LIM/ADV/AS/EX` references resolve. The cases prove the gate fails
  when a requirement row drops out of the limitations table or cites an unknown
  assumption.
- `GAP-REGISTER.md`: a current register for assurance gate 2, preserving the
  historical independent-reader reports while recording which findings are now
  closed, open, or deferred.
- `decisions/ADR-0008-assurance-expectations.md`: the practices the
  project holds itself to, the definition of done, and assurance levels per
  component. `ASSURANCE.md` at the repository root records where each practice
  and component stands. A decision about how the work is done, not about the
  protocol.
- `threat-model/`: the threat model, written and normative. All four pages were
  scaffolds.
  - `assets.md`: twelve assets, AS-01 to AS-12. Nine are secrets: plaintexts,
    the identity secret, prekey secrets, handshake secrets, the three
    ratchets' secrets, per-message keys and persisted state. Three are
    properties: the authenticity of a conversation, the authenticity of
    published keys, and state integrity against unauthenticated input.
  - `adversaries.md`: six adversaries, ADV-01 to ADV-06. They are the network;
    compromise of a party's state at a point in time; a future quantum
    adversary recording traffic; a malicious directory; a writer of the
    persisted store, outside this specification under ADR-0007; and a malicious
    peer. Each says what it can do and how the proofs represent it. The only
    adversary in any proof is the symbolic attacker of `Model.Adversary`.
  - `assumptions.md`: nineteen assumptions, ASM-01 to ASM-19, each naming the
    requirements and proofs that rely on it.
    - ASM-01 to ASM-14 are about the world: randomness, the primitives and the
      libraries trusted for them, constant time, erasure, the symbolic model's
      fidelity, the clock, storage, the network and key authenticity.
    - ASM-15 to ASM-19 are about the evidence: the platform, the translation
      toolchain, the Lean kernel and proofs checked by evaluation, the proofs'
      boundary hypotheses, and the untranslated session layer.
  - `exclusions.md`: fourteen exclusions, EX-01 to EX-14. Among them are
    metadata, endpoint compromise beyond a point in time, denial of service
    beyond the stated bounds, group messaging and devices (unspecified), a
    store writer, side channels beyond what is assumed, and deniability.
- `security-properties/`: the security properties as 32 numbered requirements.
  Each gives its statement, what it protects, the adversaries it holds against,
  the assumptions it rests on, its status and what it does not cover. 12 are
  proved, 9 assumed and 11 tested only.
  - `authentication.md`: REQ-AUTH-01 to REQ-AUTH-14.
  - `confidentiality.md`: REQ-CONF-01 to REQ-CONF-09.
  - `forward-secrecy.md`: REQ-FS-01 to REQ-FS-06.
  - `post-compromise-security.md`: REQ-PCS-01 to REQ-PCS-03. The page's existing
    account becomes REQ-PCS-01's, and its Sources point to the forward-secrecy
    page.
  - `limitations.md`: the gaps, LIM-01 to LIM-22, with a status table. Three of
    them:
    - five proved requirements rest on model-level theorems that
      `tacenta-proofs/CLAIMS.md` does not record (LIM-02);
    - REQ-AUTH-02 has no test (LIM-13);
    - tests hold erasure in place only for the classical ratchet's state, the
      KEM key pair, the identity and the prekey store (LIM-11).

### Changed
- `threat-model/assumptions.md` ASM-03, ASM-05, ASM-06, ASM-07, ASM-08,
  ASM-09 and ASM-18,
  `security-properties/limitations.md` LIM-06 and LIM-12 and the
  implementation note of `protocol/message-format.md`: `tacenta-core`'s
  HMAC-SHA256 and HKDF-SHA256
  are now `tacenta-kdf`'s own code, no longer RustCrypto's: written with tool
  assistance under the maintainer's account in a separate, unpublished
  repository; the rule-7 review comments on #272, the pull request that copied
  it here, say under "Not checked" that every review and read of that change was tool-assisted; no review
  or read of the three Rust files or their proofs by anyone independent of the
  maintainer is recorded in this repository. Copied here,
  they are under this repository's licence, Apache-2.0. Eight translations include that code; the six whose theorems
  take the KDF agreement hypotheses prove them of their translated code, and
  ASM-18 no longer lists the KDF among its assumptions. ASM-07 says the model's
  SHA-256 is what the translated SHA-256 is proved to compute there; ASM-08 lists
  the key derivation's compiled-code inventory, a tripwire and not a timing
  measurement, with what one x86_64 Linux machine showed; ASM-09 lists its
  unwiped intermediates; LIM-12 lists that inventory and the one timing
  measurement beside the two straight-line functions. The pages say so, and
  that the model's are the RFCs', the pseudorandom-function property, constant
  time and erasure are not proved; ASM-05 says the timing was measured once, on
  one CPU. The AEAD's tag is computed on encryption by that
  HMAC and checked on decryption by RustCrypto's, which agree by tests. No
  protocol behaviour, byte or refusal changes.

- `protocol/sparse-pq-ratchet.md`, Receiving and The store also has a total
  bound, and `security-properties/forward-secrecy.md`, REQ-FS-04: the page said
  that no state the operations produce holds a key past its chain's counter, and
  so that a skip's deletion removes nothing there, was read off the operations
  and not proved; and that no theorem carried the store's total bound across
  this ratchet's operations. Both are now proved of the model:
  `Proofs.SparseReachableStore.reachable_keysBelowCounter` (no key at or past
  its counter on any state a sequence of sends, receives and evictions reaches
  from initialisation), `reachable_skipSurvivors_eq` (a skip deletes nothing
  there) and `run_store_bounded` (the bound across any such sequence from a
  state within it). One operation at a time the first holds only from a state
  with no key at or past its counter and, for an operation that may open an
  epoch, no chain for an epoch past the current one, and the page says so. Of this implementation's code they are tested, not
  proved, and across a session's operations the bound is still tested rather
  than proved. The rule and the behaviour are unchanged. This entry also takes
  in an earlier one of this release: the page had said
  `Proofs.SparseRatchetCorrectness` "proves the bound holds rather than
  checking it at sample points", and the theorem it means,
  `skipMessageKeys_store_bounded`, is one skip (a skip that succeeds leaves the
  store no longer than the larger of its previous length and
  `MAX_SKIPPED_STORE`); the page names that theorem and says what it proves
  (register item J-14).
- `protocol/session-establishment.md`:
  - the initiator establishes only with an expectation, which replaces the
    named identity the page let her state;
  - **Conformance:** an implementation that offers initiator establishment
    without an expectation, or with a named key in place of a record, does
    not conform. For `tacenta-core` that is its API, `tacenta_core::sessions`;
    the lifecycle leaf crate, an internal workspace member that is not
    published, keeps its own establishment without an expectation public for
    the translation and its tests, and is not a supported entry;
  - she refuses a malformed expectation (`MalformedRecord`) before any check
    of Sending the initial message. A *known* expectation with an empty
    record is malformed;
  - she checks the bundle's identity key against her expectation after the
    bundle's presence and canonical-key checks, and before the identity-key
    rule, the signature checks, the KEM prekey's input checks and anything
    that draws randomness or computes an agreement. That is where the page
    placed the named identity, before the identity-key rule and the
    signatures, so that order is kept. The page had left the named identity
    unordered against the presence and canonical-key checks; it now follows
    them. The check applies the identity-key rule to the key itself, so a key
    that is not an identity key is refused as an invalid identity key either
    way. One outcome changes: a bundle whose key is not an identity key and
    differs from the named key was refused as an unexpected identity, since
    the named identity came first, and is now refused as an invalid identity
    key;
  - whether `EKA` is drawn before the KEM prekey's input checks is stated
    as not fixed;
  - also changed: the lead-in to the session-reset and
    simultaneous-initiation cases, the "changed identity" bullet, and the
    Security properties list, which names REQ-AUTH-15 and REQ-AUTH-16.

- `protocol/session-establishment.md`, `protocol/identities-and-devices.md`
  and `protocol/error-handling.md`: the text settles five of the gaps the
  fourteenth independent reader pass recorded
  (`tacenta-test-vectors/runners/independent/GAPS-14.md`); their rows stay
  open until a later pass reads it.
  - G14-02: decoding the bundle is not a check of Sending the initial
    message, and no order is fixed between it and a malformed expectation;
    either refusal conforms. A malformed expectation with bundle bytes that
    do not decode tells the readings apart.
  - G14-03: the initiator's refusals of a bundle are named as kinds (an
    inconsistent bundle, a non-canonical key, an authentication failure, a
    KEM input refusal, a non-contributory agreement), and error-handling.md
    lists them, since an order can be seen only between refusals that are
    told apart. The vectors use the same names.
  - G14-04: the verification number's input is the 32-byte digest, and the
    number is the 60 digits; the twelve groups of five, and how they are
    separated, are a display only.
  - G14-05: a lookup's result is stated: the attribution, the contacts the
    key is *retired* for and the records skipped as malformed, as sets.
    Naming the contacts an ambiguous key is *same* for is optional.
  - G14-06: the KEM prekey's signature is over the type byte `0x08` and the
    key's bytes as the bundle holds them, which for a 1,568-byte key is
    `EncodeKEM` of it, and both signatures come before the KEM prekey's
    input checks. A bundle that did not come from the decoder, with a KEM
    prekey of the wrong length whose signature does not verify, is an
    authentication failure.
  - No byte, constant or stored format changes, and no existing vector's
    outcome changes.

- `protocol/error-handling.md`: the conditions list; the orders the pages
  fix, among them the initiator's, protobuf-profile.md's and the inventory
  statement's checks; and the closing remark on one check order.

- `protocol/identities-and-devices.md`: the status line; where the
  identity-key rule applies, now including the digest and a presented key;
  and the way forward from a stored key the rule refuses, which now goes
  through an expectation.

- `CONSTANTS.md`: the label row and the Bounds row.

- `threat-model/assumptions.md`: the ASM-07 lead-in and SHA-256 bullet;
  ASM-14; the "Relied on by" lines of ASM-07, ASM-14 and ASM-19.

- `threat-model/exclusions.md`: EX-05, EX-09 with the probe, and EX-10.

- `threat-model/adversaries.md`: ADV-04, whose verification-number margin
  is assumed (ASM-07).

- `threat-model/assets.md`: AS-10 and AS-11.

- `security-properties/authentication.md`: the intro, and REQ-AUTH-02, now
  "the initiator's expectation is enforced". It stays tested only, and its
  status names `establish_initiator` of `tacenta-core/src/sessions/identity.rs`
  as where the refusals are made, the tests in
  `tacenta-core/tests/identity_expectation.rs`, the `full_session.rs` test,
  which runs under *known*, `initiator-expectation.json` and the
  `identity_records` fuzz target. No proof covers it.

- `security-properties/confidentiality.md`: REQ-CONF-01, whose Does not cover
  list says the peer of a session that is no contact's is whoever holds its
  peer key, absent a compromised signed-prekey secret (LIM-15).

- `security-properties/limitations.md`: the counts, the table, LIM-13, which
  names the session layer's `establish_initiator` and its tests and vectors,
  and LIM-15.

- `security-properties/evidence-index.json`: REQ-AUTH-02's property, and its
  evidence: the session layer's functions, its tests and vectors, and the
  model's theorems (tier T2, about the model alone). Its `missing_evidence`
  is a `proof` item saying that `establish_initiator` is outside the
  translated crates.

- `README.md`.

- `protocol/group-messaging.md`: the page no longer lists or relies on one
  published analysis of sender keys (IACR ePrint 2023/1385). The page's rule is
  to check what a published description's authors based it on before using it,
  and no outcome of that check is recorded in this repository, so the row is
  removed. The sentence in the first open question that took that analysis's
  finding about sender keys is replaced by the project's own cost argument:
  sender keys add a second key hierarchy whose guarantees the project would
  have to state and prove itself. This supersedes the earlier entry's remark
  that sender keys are described publicly "by academic analysis". The mechanism
  outline is marked tier `nominated` and cited to WhatsApp's white paper, and it
  says in plain words how a sender key is shared instead of using a fixed
  message name. A new section, "What this page rests on", says which parts of
  the page are `nominated` and that the open questions are questions, not
  choices. It states what the repository records: no check of what any cited
  item was based on beyond who wrote it, and no finding that any of them was
  based on another implementation's source.

- `identities-and-devices.md`, hosted device-inventory statements: state what a
  verifier must check before it relies on a signed statement, as seven ordered
  checks (account match, issuer binding, signature, freshness, duplicate active
  `device_id`, identity keys, then its own binding and statement policy), and
  what the format leaves unchecked: the chain of custody of a
  `replacement_predecessor`, key uniqueness and reactivation, and equivocation.
  A verifier must not refuse a statement solely because a replacement's marker
  names no listed binding, which an honest issuer can produce once the
  tombstone falls at or below the revocation floor. Check 6 requires each
  identity key to be canonical and a point of the prime-order subgroup, which
  refuses low-order, off-curve and mixed-torsion keys, so each key has one
  spelling and a policy can compare identity keys as bytes. The section also
  states the sort order of both lists (strictly ascending byte order of the
  encodings), what an exact binding is, that a
  predecessor tag other than 0 or 1 is refused, that a binding without a valid
  capability word has no commitment, the order in which the binding and
  statement policies run, that check 3 is the page's Verifying a signature and
  that a signed statement is a preimage followed by exactly 64 bytes, and that
  a verifier records a generation as seen only after acceptance, in one atomic
  step that evaluates its freshness rule again. It restores, as the issuer's
  duty, the earlier statement that keys are checked before signing. Check 5
  replaces the earlier statement that the product must reject duplicate
  `device_id` values. The encoding and the signature input are unchanged.

- `protocol/session-persistence.md`, `protocol/session-establishment.md` and
  `protocol/key-deletion.md`: state the rules of the v5 prekey store's
  `legacy_blocked` markers, which `tacenta-core`, the model and the vectors
  already followed and the pages did not say. Migration writes both live
  last-resort KEM identifiers for any nonempty v1-v4 record and keeps the
  record; the list is strictly ascending, holds at most two entries, and names
  only `kem_id` or the identifier inside `previous_kem`; a v5 reader refuses a
  list that is out of order or repeats an identifier (as malformed or as
  non-canonical, at the reader's choice); a handshake naming a listed key is
  refused (`LegacyLastResortRecord`) before decapsulation with the store
  unchanged; and a rotation removes the marker of the key it wipes. The prekey
  store's semantic rules are also corrected from "all four versions" to all
  five. No wire format changes.

- Identity keys are held to one rule at every boundary that admits one.
  `identities-and-devices.md` gains an Identity keys section: the rule of
  Accepting a signed statement, check 6 (a canonical curve public key of the
  prime-order subgroup), applies to the identity key of a prekey bundle, to the
  `identity` of an initial message, to the two identity keys of a stored
  session and the identity key of a stored prekey store, and to the key a
  signature is verified under (Verifying a signature, step 3 now requires `A`
  to be a point of the prime-order subgroup, in place of "not of small order").
  A key that fails it is refused as
  an invalid identity key, a third outcome beside decode failure and
  authentication failure (`error-handling.md`). The check comes before any
  signature is verified, random value drawn, agreement computed, private key
  used or state changed; `session-establishment.md` gives the order for the
  bundle and for the initial message, and `message-format.md` says a decoder
  does not apply the rule. A stored session that holds a key the rule refuses
  is refused as inconsistent and a stored prekey store as malformed
  (`session-persistence.md`), which is a change to what a reader accepts:
  no state an honest party's operations produce holds such a key, the section
  argues that an honest key is never refused, and the page says what a reader
  does with an older state that holds one (refuses it, does not repair it, and
  a caller can find such states beforehand by applying the rule to the stored
  keys). The encodings, the signature input and the persisted layouts are unchanged.

- `tacenta-proofs`: the Braid refinement boundary `KemAgreesFor` no longer
  assumes `K.Correct`. No proof used the conjunct, and it asserted perfect
  decapsulation, which ML-KEM-1024 satisfies only up to the FIPS 203 failure
  bound. The four Braid refinement theorems now rest on the two
  operation-agreement clauses alone; `toyKem_correct` stays a model fact.
  Closes hostile-lens item FM-03.

- `tacenta-core`: session lifecycle orchestration moved into a shipping leaf
  crate and now translates from all 30 public roots. This is a Phase 0
  translatability result only; no session theorem or assurance level changes.

- `protocol/triple-ratchet.md` and `protocol/session-establishment.md`: make
  the session transaction boundary explicit for end-to-end refinement. The
  agreement runs before the Triple Ratchet and both next states commit
  together after a successful send, except that an agreement send entering
  `Failed` commits that terminal state. Responder establishment treats the
  prekey store as read-only until the inner message authenticates; every
  refusal leaves it unchanged, and success performs only the specified
  one-time-key removals and, on the last-resort path, replay-record append.
  Register row `E2E-07`.

- `tacenta-core`: the classical ratchet’s secret-bearing working copies and
  removal paths now allocate at their final capacity and wipe dead slots before
  release. The analogous sparse-ratchet container hardening remains a follow-up
  and is not claimed here. Sparse decoder vectors are sized from checked counts.
  The independent reader follows the v2 agreed-secret replay identity and
  covers fail-closed import of v4 replay records into v5.

- `protocol/session-persistence.md`, Prekey store, Semantic rules: a sixth rule,
  that every stored signature verifies under `identity_public` -- the signed
  prekey's, the KEM prekey's, each one-time KEM prekey's, and the retired pair's
  in the versions carrying them. The page had enumerated five rules and said
  nothing about the signatures, so the two readings -- that the list is
  exhaustive, or that a reader also checks what the signatures authenticate --
  are told apart by a state a reader can be handed: a v4 store with one byte
  flipped at offset 69 re-encodes canonically, satisfies all five existing
  rules, reads back as valid, and then publishes a bundle every initiator
  refuses. The page decides for the second reading, on the reason it already
  gives for refusing a corrupted `next_id`. It also states the obligation that
  falls out of checking this at read time rather than after every operation:
  an operation signs a prekey under the identity whose public key is
  `identity_public`, and an API that lets a caller pass another refuses it.
  Reported, by the project's own account, by an external review at `d2dc386`
  (register R-01); that review is an unverified project assertion, not counted
  as assurance, until its report, reviewed revision, scope and the reviewer's
  relationship to the project are identified (`ASSURANCE.md`, "Readiness for
  external review"). `tacenta-core` did not perform the check and is what the
  decision puts in the wrong.
  - The refusal is reported separately, as "incoherent", the prekey store's
    analogue of the session's "inconsistent" and for the same reason: a store
    well-formed and canonical but unusable is the one case a storage layer
    could have written itself, and a caller that can tell it from corruption
    can still read the secrets out. Rejection records both.
  - **A reader with this rule refuses v4 stores a reader without it accepts**,
    and the version is deliberately not bumped: nothing in the layout changed,
    and the stores they disagree about were never usable. The page says so
    where the rule is stated.
- `protocol/session-persistence.md`, Triple ratchet state: the refusals that
  format's reader gives, and in particular that a `ratchet_state` or
  `spqr_state` its own reader refuses is short or malformed whatever that
  reader's reason, an unrecognised inner version included. The page had stated
  the mapping for the session's two halves and not for the triple ratchet
  state's, leaving two readings a stored state can tell apart (the independent
  reader's `GAPS-5.md`, G5-02's neighbour G5-01).
- `tacenta-model`, `Model.Lifecycle.sameEphemeralAgreement`: the model's
  repeated-initial comparison now does what `protocol/session-establishment.md`,
  Receiving the initial message, says. It decodes the message's `ephemeral` and
  `established_ephemeral` with `DecodeEC` (`Model.Lifecycle.decodeEc`: 33 bytes,
  the curve type byte, a canonical key, through the initial-message decoder's
  own `checkCurve` and `checkKey`), takes X25519 of the session's
  `ratchet_private` with each of the two decoded 32-byte keys, and compares the
  two outputs. It is `false` when either decode or either agreement fails. Before,
  the model handed the two 33-byte `EncodeEC` strings to the agreement as they
  were, which the page does not describe and which no theorem could relate to
  `tacenta-core`'s `same_ephemeral_agreement`, which decodes both first. Both
  strings decode on every session a reader accepts and in every message the
  initial-message decoder accepts, by reading of the code, so the two
  decode-failure arms are reached only on states no reader produces; that is
  not proved. The page is unchanged, and the generated
  vectors do not reach this function and do not change.
- `protocol/mlkem-braid.md`, Failure: one sentence says the model expresses the
  four KEM failures the section lists. `Model.Braid`'s `Kem` operations
  (`keyGen`, `encaps1`, `encaps2`, `decaps`) may now refuse, and each refusal
  takes the `Failed` transition the section names; before, they were total
  functions and the model could not express any of the four. The correctness
  law is conditional on the two draws succeeding. The toy KEM never refuses, so
  the generated vectors do not change. One more sentence says that the send or
  receive that moves the Braid into `Failed` yields no key and reports epoch 0,
  which the page said only of a send or receive from `Failed`; the "A send's
  epoch" bullet of Sending now reads the report off the state the send leaves
  the Braid in and says a send never raises the epoch, where it said a send
  never changes it.
- `protocol/mlkem-braid.md`, Failure: the second half of encapsulation also
  fails, in this implementation, on an encapsulation state restored from
  persistence whose stored coefficients lie outside the bound the KEM library
  states as a precondition of its arithmetic; the Braid then takes the
  `Failed` transition the list already names for that half. Before, the page
  said the library fails only on wrong lengths, and the implementation let a
  corrupted store's state reach the library outside its stated precondition,
  where on its portable backend a large enough coefficient overflowed and
  panicked. `protocol/session-persistence.md`, Braid: one sentence says that
  what the KEM refuses in such a state at use is the KEM's rule. The reader
  still checks the field's length alone; the refusal is at use, so no
  persisted-state vector changes.
- `protocol/session-establishment.md`, `protocol/session-persistence.md` and
  `CONSTANTS.md`: the last-resort replay record now uses an `SK`-bound replay
  identity (`tacenta last-resort handshake v2`). Stores written as v1-v4 with
  a nonempty legacy record import with the affected live KEM keys blocked until
  rotation; v5 is the only format written. This closes the torsion-equivalent
  public-encoding replay gap without pretending an old byte-based record can be
  upgraded safely.
- `protocol/key-deletion.md` and `security-properties/authentication.md`:
  authentication and deletion rules now name the post-decapsulation replay
  identity rather than a public-byte fingerprint.
- `tacenta-core/ratchet`: skipped-key removal avoids `Vec::remove`'s
  secret-bearing dead-tail copy, and persisted secret vectors are sized before
  decode. AES-CBC buffers now use the crates' zeroization features. The
  analogous SPQR container hardening remains a follow-up because its verified
  proof contracts still describe the old standard-library operations.
- `protocol/sparse-pq-ratchet.md`, Receiving and The store also has a total
  bound. Relaxation: a stored sparse ratchet state that holds a key in the
  range a skip replaces is no longer refused for the total bound on the count
  taken before the deletion. A state the operations produce from
  initialisation holds no such key (proved of the model, tested of the code: the
  entry on `Proofs.SparseReachableStore` under Changed), so the two counts differ only for a stored state
  that does. The total bound is checked against the
  store a skip would leave. A skip that steps a chain from `c` to `upto` is
  refused as `TooManySkipped` when `upto - c` passes `MAX_SKIP`. Otherwise it
  deletes the keys stored for its epoch under the numbers it is about to store
  (`c < n <= upto`: the counter itself is excluded, the number it steps to is
  included), counts what remains, and is refused as `SkippedStoreFull` only
  when that count plus `upto - c` passes `MAX_SKIPPED_STORE`. The deletion is
  made on a working copy, and a refusal inside the skip leaves the state as it
  was when the skip began; a receive that folded an agreement's secret in
  before the skip is still spent. A key outside the range, including one
  stored at the counter itself, is kept as it was. This is the order
  `key-deletion.md` states for the Double Ratchet, which now names the sparse
  ratchet as taking it too. An earlier entry here recorded that the sparse
  implementation and model counted the store before the deletion and that the
  change was an open follow-up (`HL-R1-SPARSE-TRANSLATION` in
  `GAP-REGISTER.md`; its translation evidence was recorded on 2026-10-03 on one
  Linux x86_64 regeneration that was not independent, and the reader finding G12-05
  stays open as `HL-R1-SPARSE-READER`). That
  entry, which stands in the tags `tacenta-assurance-v0.3.0` to
  `tacenta-assurance-v0.4.5`, is superseded by this one, and the page states
  the rule as normative. The independent reader, which is project-controlled
  evidence (`GAP-REGISTER.md`, `READER-INDEPENDENCE`), already counted the
  store after the deletion
  (`tacenta-test-vectors/runners/independent/reader/tacenta_reader/spqr.py`,
  case CR-18) and recorded the page's silence as G12-05
  (`tacenta-test-vectors/runners/independent/GAPS-12.md`). Two of its case
  titles and one cite string were edited to quote this page, and its documented
  run tally and one note on G12-05 were updated. No reader has read the new text.
  Through a session the earlier count did not lose such a message: the session
  evicted the oldest stored keys and retried. The difference a session shows
  is in eviction. Where the replaced keys were not the oldest, the earlier
  count evicted up to as many other stored keys as the store held in the
  range, and this count keeps them when the skip fits once the replaced keys
  are dropped. When it does not, both counts evict the same first batch. On the
  state of `replacement-bound-counts-resulting-store` in
  `sparse-ratchet-state.json`, whose two replaced keys are the
  oldest, the two counts leave the same store. An implementation that counted
  the store before the deletion, as the earlier text of this page described,
  must count it after. This changes no byte written to the wire or to storage
  by a state the operations produce, and it is not a security fix: on the
  evidence recorded here no operation produces a state that the two counts
  treat differently.
- `protocol/sparse-pq-ratchet.md`, Receiving: the page now states what the
  implementation, the model and the reader already did. The stored-key lookup
  comes before anything else about the chain is consulted, so a state read
  from storage can answer a receive whatever the chain's counter, whether or
  not the epoch's receiving chain is absent, and for a message numbered zero.
  The list of ways a stored key is deleted now includes its replacement by a
  skip. The steps of a skip name the epoch they act on, the receiving chain of
  the epoch the message names, and the count in step 3 is over the whole
  store, whatever the epoch.
- `tacenta-core/spqr` and `tacenta-model`: `skip_message_keys` and
  `Model.SparseRatchet.skipMessageKeys` follow the order the sparse page now
  states: the keys the skip is about to replace are dropped from a working
  copy and the total bound is checked against that copy plus the keys to
  store. A refusal inside the skip leaves the state as it was when the skip
  began. The two previously counted the store before the deletion and could
  refuse a stored state near the bound for a request that only replaces its
  own keys.
- `sparse-ratchet-state.json`: add `replacement-bound-counts-resulting-store`,
  a 1,999-key store whose two held keys a skip replaces, leaving exactly
  2,000, and `replacement-range-excludes-the-chain-counter`, a chain with keys
  held at its own number, inside the replaced range, at the number the skip
  steps to, above it and under another epoch, with the key at the counter and
  the keys above and under the other epoch kept. Each has its `-read-back`
  vector. No existing vector changes. Only the first of the two tells this
  rule from the earlier one: the second gives the same result on the code
  before this change and pins the range the page now states. No operations
  vector refuses a skip for the total bound, since the file's operation
  refusals are `counter-exhaustion` and `no-chain`. The refusal half of the
  rule is checked by the crate's tests, by the differential harness against
  the model and by the independent reader's cases, and by no vector file.
- Double Ratchet skipped-key capacity is checked after removing entries that
  the operation will replace. `key-deletion.md` states the order explicitly:
  delete held `(DHr, n)` pairs in the re-derived range, then require the
  resulting store to stay within `MAX_SKIPPED_STORE`. The model and
  `tacenta-core` previously checked the pre-replacement length and could refuse
  a conforming revisit near the bound.
- `tooling/check-traceability.py` and its case runner now validate the pilot
  evidence index's requirement IDs, status classes, paths, theorem names, test
  names, vector case IDs, live missing-evidence references and required format
  fields.
- `GAP-REGISTER.md`: add gate classes and work-package ownership to current
  rows, and give stable IDs to the previously descriptive persisted-format and
  proof-scope rows.
- `tacenta-test-vectors/README.md`: add vector-layout sections for
  `prekey-store-state.json` and `session-state.json`, and refresh the
  differential-testing note now that the model states those stored formats.
- `ASSURANCE.md`: point assurance gate 2 at the current gap register, and replace
  stale pass-7 wording about the prekey-store and session vector files.
- Clarify the prekey store signature rule in `protocol/session-persistence.md`: verification uses the unlabelled prekey signature input, and the signing obligation names `create_prekeys`, `replenish`, and both rotations. This resolves G7-03 and G7-04 from the independent reader without changing the stored format or implementation.
- `tacenta-test-vectors/README.md`: clarify that Braid operation steps use the
  wire Braid-message fields, so an absent codeword has all-zero `chunk_index`
  and `chunk` padding, and a runner reports a vector that violates that padding
  as malformed vector data. This resolves G6-05 from the independent reader
  without changing any vector bytes.
- `prekey-store-state.json`: add accepted `legacy-v1`, `legacy-v2` and
  `legacy-v3` fixtures for the prekey store's older stored layouts. The new
  vectors read to the same fields as the no-record, no-retired current fixture
  and upgrade to v5 on write-back, resolving `PK-OLD-VERSIONS` in the gap
  register.
- `prekey-store-state.json`: add the accepted `retired-kem-prekey` fixture,
  produced by `print_prekey_store_fixtures`, so the prekey store's
  `previous_kem` sub-format is covered by a deterministic vector. This
  resolves `PK-PREVIOUS-KEM` in the gap register.
- `protocol/session-persistence.md`, Braid, and Semantic rules of the leaf
  formats, Braid: the `key_pair` content clause of tags 1 to 4 is **scoped**
  to an implementation that knows the KEM key pair's layout. Such an
  implementation checks that the `header` and `ek_vector` a stored `key_pair`
  holds pass the KEM split's validation, as before; one without the layout
  checks the field's length, accepts it, and conforms. Where those two values
  sit inside the field's 11,872 bytes is the KEM library's serialisation,
  which the page delegates rather than defines (ADR-0006, point 5), so the
  rule as written could not be implemented from the specification at all, and
  a reader without that library read as deficient rather than conforming. The
  Principles' "Validated, not only parsed" and the leaf formats' preamble each
  name the one scoped rule, so every list of semantic rules stays complete and
  ADR-0007's "the leaf readers enforce exactly their stated rules" still
  holds: the rule as stated is the conditional one. Nothing changes for
  `tacenta-braid`, which has the layout and checks the content. No vector can
  pin the clause -- a state that fails it is refused by a reader inside the
  scope and accepted by one outside, both conforming -- and the conformance
  manifest and the vectors README say so; the field's length, which every
  implementation applies, stays pinned by `key-pair-wrong-length`. Register
  item G5-02 (the independent reader's `GAPS-5.md`).
- `decisions/ADR-0006-specification-is-normative.md`, new point 7, with the
  amendment recorded and dated as the `threat-model/` amendment was: a
  normative page may cite non-normative evidence for a status it states -- a
  Lean theorem, a test, a vector, `tacenta-proofs/CLAIMS.md` or
  `LIMITATIONS.md` -- and such a citation is not part of the protocol's
  definition. What a page *requires* must be readable from the specification
  alone, and where the content is a property of an implementation the page
  states what the protocol requires and cites the implementation's own record
  as evidence. The citations stay: ADR-0008's practice 8 builds traceability
  on them. `README.md`'s "Normative status" carries the same two points.
  Register item G5-07.
- `threat-model/assets.md`, AS-12, and `threat-model/assumptions.md`, ASM-05:
  the two statements that took their *content* from implementation files now
  carry it themselves (G5-07).
  - AS-12 named what it covers and pointed at `tacenta-core`'s
    `AUTHENTICATION-BOUNDARY.md` for "the rule for that implementation", which
    is a registry of function names. It now states what the protocol requires,
    REQ-AUTH-13's durable state, enumerated for the session and for the prekey
    store, and says that deriving is not committing: the requirement is that
    nothing durable moves before the authenticator verifies, not that nothing
    is computed. No function name is normative.
  - ASM-05 said the derivation labels are "prefix-free apart from two
    registered pairs (`tacenta-core/LABELS.md`)", leaving which strings are
    labels, and which pairs are registered, to that file. It now names both
    pairs with their values -- `COMBINE_INFO` a proper prefix of `SPLIT_INFO`,
    and `Tacenta SPQRChain` of `Tacenta SPQRChain Start` -- over CONSTANTS.md's
    "Derivation labels", which already carries every value, and says why
    neither pair is reachable as a collision.
  - Both keep their evidence citations. The registry and
    `tooling/check-labels.sh` are cited as evidence for `tacenta-core`, which
    is what point 7 allows.
- `protocol/session-persistence.md`, `protocol/session-establishment.md`,
  `protocol/message-format.md`: every curve public key a stored state holds
  must be canonical, and each reader refuses a state that holds one spelled
  any other way. The page had said, as built, that only
  `established_ephemeral` and the session's `dhs_pub` were refused (G4-02, in
  0.2.0). Register item J-8.
  - The session's semantic rules require `our_identity_public`,
    `peer_identity_public` and `pending_initial`'s `ephemeral_public` to be
    canonical, refused as inconsistent.
  - The ratchet state's semantic rules require `dhs_pub`, a present `dhr_pub`
    and each skipped entry's `dh` to be canonical, refused as malformed. A
    session holding one is refused as malformed by its `triple_state`'s
    reader, a re-spelled `dhs_pub` included, which the page had said was
    refused as inconsistent.
  - The prekey store's semantic rules require `identity_public` to be
    canonical, refused as malformed, in all four versions.
  - The sparse ratchet state and the Braid hold no curve public key.
  - "What follows" from each accepted re-spelling is replaced by why a stored
    key is refused: inside the ratchet state a second spelling gives one key a
    second identity, since `DHr` and skipped keys are matched by bytes.
  - For no honest state to be refused, the initiator refuses a bundle whose
    identity key, signed prekey or one-time curve prekey is not canonical
    before she uses it. The bundle decoder already refuses one, so this
    matters only for a bundle that reaches her another way.
  - "Receiving the initial message" says `peer_identity_public` is canonical
    in every session a reader accepts.
- `protocol/message-format.md`, Ratchet message: standalone composite-header
  decoding is now a public contract for vectors, associated-data construction
  and implementations that parse the header before ciphertext. It accepts
  exactly the 102-byte composite header and refuses trailing bytes. Gap item
  G4-01 is closed.
- `protocol/session-persistence.md`, Prekey store: the stored-signature rule
  now states that it deliberately narrows the canonical `identity_public` set.
  In particular, `p - 1` is canonical as a curve public key but cannot verify a
  stored signature because XEdDSA verification refuses it before Edwards
  conversion. Gap item G7-05 is closed as a wording-only reader finding.
- `tacenta-test-vectors/README.md`: the persisted ratchet vector layouts now
  distinguish the already split per-ratchet `sk` inputs from the unsplit Triple
  Ratchet `sk` input. Gap item G6-01 is closed without renaming stable vector
  fields.
- `tacenta-test-vectors/README.md`: Braid operation vectors now state their
  read-back obligation explicitly. Runners must read `output` back and write it
  as the same bytes; this runner assertion is the equivalent check used instead
  of `-read-back` sibling vectors. Gap item G6-03 is closed.
- `protocol/ratchet.md`, Sending and receiving: the classical receive boundary
  where `Nr = u32::MAX` and an unstored same-chain message has a lower number
  now deliberately permits either stale/out-of-order or `ChainExhausted`. The
  freedom is scoped to that overlap; accepting the message is still non
  conforming. Gap item G5-09 is closed.
- `protocol/session-persistence.md`, Rejection: the short-buffer and
  unknown-version overlap is now a format-by-format contract for ratchet
  state, sparse ratchet state, triple ratchet state, Braid state, session state
  and prekey store. The only implementation freedom is a non-empty buffer that
  is too short for every recognised version and also starts with an unknown
  version byte; recognised-version truncations, empty buffers and long enough
  unknown-version buffers keep their single refusal kind. Gap item G5-03 is
  closed.
- `protocol/session-persistence.md`, Rejection: a buffer too short to be read
  that also carries an unknown version byte may be refused either as short or
  malformed or as a wrong version, and which is left to the implementation,
  as error-handling.md leaves the order of checks. The page had named both
  refusals without saying which such a buffer gets, and the model and
  `tacenta-core` answer differently. The vectors pin neither. Register item
  J-11.
- `decisions/ADR-0006-specification-is-normative.md`, point 1: `threat-model/`
  is normative, with `protocol/` and `security-properties/`, and the page
  records the amendment with its date. Every security requirement is stated
  against the threat model's assets, adversaries and assumptions, and the
  README already listed it among the normative pages.
- `README.md`: the status paragraph names the written threat-model and
  security-property pages, and the protocol pages still scaffolds.
  `threat-model/` is listed among the normative pages, since every security
  requirement is stated against its adversaries and assumptions.
- `protocol/ratchet.md`, `protocol/session-establishment.md`: each "Security
  properties" section points to the requirements. They had pointed to
  `tacenta-proofs/CLAIMS.md` in place of scaffold pages.
  `session-establishment.md` no longer says deniability is retained. No
  requirement states it, and nothing in this project establishes it
  (`threat-model/exclusions.md`, EX-12).
- `security-properties/`: the model-level theorems the requirements cite are
  recorded in `tacenta-proofs/CLAIMS.md`, and the requirements say where.
  - REQ-AUTH-07, REQ-CONF-07, REQ-CONF-08, REQ-FS-01 and REQ-PCS-01 name the
    CLAIMS.md section recording their theorems. They stay "proved,
    model-level, against the symbolic attacker".
  - So do the `StateConsistency`, `KeyErasure`, `MemorySafety` and
    `SparseRatchetCorrectness` theorems that REQ-AUTH-11, REQ-CONF-04,
    REQ-FS-02 and REQ-FS-04 cite beneath their status.
  - Each page's "How the requirements are stated" no longer describes a
    theorem cited without a CLAIMS.md record, since none is.
  - `limitations.md`: LIM-02 is closed, and says by what. No requirement's
    status changes.
- `security-properties/authentication.md`, REQ-AUTH-02: the status names the
  test that exercises the refusal. `limitations.md`: LIM-13 is closed, and the
  status table no longer says the requirement has no test. It stays tested
  only.
- `security-properties/limitations.md`, LIM-11: states which types a static
  test holds to erasing when dropped. They are the classical ratchet's `State`
  and `SkippedKey`, the ML-KEM `KeyPair`, `Identity` and `PrekeyStore`. The
  sparse ratchet's, the Braid's and the Triple Ratchet's types have no such
  test. `forward-secrecy.md`, REQ-FS-03, no longer says those types erase
  through derived destructors.
- `security-properties/limitations.md`, LIM-05: names the test that runs a
  session through a Diffie-Hellman step. It no longer reports that
  `tacenta-proofs/CLAIMS.md` and `LIMITATIONS.md` call that test "being added".
- `security-properties/forward-secrecy.md`, REQ-FS-04: the wording overstated
  the theorems it cites. "The bound holds over any sequence of operations" is
  not what `Proofs.MemorySafety.reachable_stays_bounded` says: it covers finite
  sequences of the five transitions `Proofs.MemorySafety.Step` names, from a
  state already within the bound, and `Model.Ratchet.receive` is not one of
  them. The sparse citation,
  `Proofs.SparseRatchetCorrectness.skipMessageKeys_store_bounded`, is one skip.
  Both citations now say what the theorems state, "Does not cover" names the
  bound across `Model.Ratchet.receive` and across the sparse ratchet's `send`,
  `receive` and `advance`, and the status is qualified: the statement's second
  bullet, that each store holds at most `MAX_SKIPPED_STORE` keys, is not proved
  across a session. `limitations.md`'s status table follows.
- `security-properties/post-compromise-security.md`, REQ-PCS-01: the page
  overstated the two theorems it cites. "Healing is not one step's property; it
  persists" is not what `Properties.PostCompromise.fresh_agreement_heals` and
  `fresh_agreement_heals_the_root` say: each is about a single step. The page
  now says so, and says that carrying healing to the following root step, or to
  the sending chain `dhRatchet` derives second, is not proved.
- `security-properties/limitations.md`, LIM-13, and
  `security-properties/authentication.md`, REQ-AUTH-02: the description of
  `a_bundle_for_another_identity_than_the_named_one_is_refused_and_changes_nothing`
  overstated the test by listing "neither prekey store's bytes change" among
  the things it checks. `establish_initiator_for` takes no prekey store, so
  that assertion cannot fail. Both pages now say the stores are unchanged by
  construction.
- `threat-model/assumptions.md`, ASM-17, `security-properties/limitations.md`,
  LIM-10, and `security-properties/confidentiality.md`, REQ-CONF-05: the three
  passages described the sparse ratchet's receive theorems and the Triple
  Ratchet's refinements as trusting the Lean compiler's evaluation. The
  constants those results used `native_decide` for are now proved by the
  kernel, so the passages say they rest on the kernel and the translation's
  opaque runtime constants, and they name what still trusts the compiler: the
  composite header's `bv_decide` round trips and the export and import
  statements, through the length bound of a debug-assertion message in the
  generated `export`. No rule, byte or constant changes.

### Fixed
- `protocol/sparse-pq-ratchet.md`, The store also has a total bound: the
  passage on what the proofs cover said which refusal a skip returns was not
  proved. The leaf refinement fixes it in one direction (a `SkippedStoreFull`
  result is the store's refusal); the copy translated with the session
  lifecycle is now proved in both directions, under that theorem's
  hypotheses
  (`UnitLifecycleSparseSkipKindT3.skip_message_keys_refines_detailed`), and
  `tacenta-core/tests/sparse_skip_order.rs` tests the order on the Rust
  source. The rule and the behaviour are unchanged.

- `protocol/session-establishment.md`: the repeated-initial rule names the key
  its agreement class is taken under. It is the session's current
  `ratchet_private`, not the responder's signed-prekey secret, which the
  persisted session does not hold. The behaviour of `tacenta-core` is
  unchanged; the wording is corrected.

- `protocol/session-persistence.md`: align the repeated-initial semantic rule
  with `session-establishment.md`: the ephemeral is compared by its X25519
  agreement class and the identity by bytes. This removes the stale
  byte-for-byte wording without changing the persisted format.

- `Session::decrypt` now recognises a repeated initial message by the
  responder's X25519 agreement class for its ephemeral, while retaining the
  byte-bound identity check. This keeps canonical torsion-equivalent ephemeral
  encodings in the same established session and closes the repeat-blackhole
  gap.

- `tacenta-spqr`: secret-bearing chain-table updates now wipe the old
  allocation before growth, and skipped-message keys are derived directly into
  their final vector instead of being moved from a temporary buffer. This
  closes the sparse-ratchet container residue paths without changing the wire
  format or ratchet state machine.

- Workflow checks now fail when the workflow or case corpus is absent, with an
  explicit empty-repository control. Vector currency uses `git status` with
  untracked files included, so a newly generated uncommitted vector cannot be
  hidden from the local or hosted gate. This closes hostile-lens item SC-14.

- The constant-time assembly reader's callee allow-list now matches whole
  length-prefixed Rust identifier components, rather than substring regular
  expressions. Its production-reader controls require an exact `compress`
  callee to pass while `compress_sign_fixup` and an empty allow-list fail.
  This closes hostile-lens item HL-SC-16.

- The DCO gate now fails if its comparison base is missing and checks merge
  commits instead of silently excluding them. A production-script case runner
  pins a signed pass plus missing-base, unsigned-commit and unsigned-merge
  refusals. This closes hostile-lens item SC-10.

- Corrections to provenance and review statements (2026-10-28). No rule, byte,
  constant or bound changes.
  - `decisions/ADR-0010-key-derivation-written-here.md` (Context, "What was
    available"), `threat-model/assumptions.md` ASM-05 and the Changed entry
    above on `tacenta-kdf`: the sentence on who wrote and who read the three
    copied KDF files stated a dated reading of the three Rust files by the
    maintainer that no record in this repository supports. It now states only
    the recorded authorship (written with tool assistance under the
    maintainer's account) and the rule-7 review comments on #272, which say
    under "Not checked" that every review and read of that change was tool-assisted. ADR-0010's Consequences no longer list the
    maintainer's reading among what replaces "vetted"; they list the tool-assisted
    reviews of #272, citing what its rule-7 review comments say under "Not checked", and say these are not independent review. Its Status records the amendment. The earlier sentence is in no tagged release.
  - `threat-model/assumptions.md` ASM-08: the statement that `tacenta-core`'s
    own composition "is audited by reading" to branch only on public data had
    no record of such an audit in this repository behind it. The page now says
    the property is stated, not established. The earlier sentence stands in the tags
    `tacenta-assurance-v0.2.0` to `tacenta-assurance-v0.4.6`.
  - Two different citations of an external review are told apart
    (`ASSURANCE.md`, "Readiness for external review"). The "External review,
    2026-09." attributions in the `[0.1.0]` section below come from commits of
    2026-09-09, before `d2dc386` was committed, so they are not the review of
    that commit; this repository does not identify their source. The entry in
    this section on register R-01 cites an external review at `d2dc386`, which
    is an unverified project assertion. For neither are the report, the
    revision reviewed, the scope or the reviewer's relationship to the project
    identified, and neither is counted as assurance until they are. The
    `[0.1.0]` entries are not edited. The R-01 entry in this section now
    carries that label; its earlier wording stands in the tags
    `tacenta-assurance-v0.2.0` to `tacenta-assurance-v0.4.6`.
  - `tacenta-test-vectors/runners/independent/P6-OPERATION-READER-EVIDENCE.md`
    and `tacenta-model/P6-L2-TARGET-DECISION.md` called the P6 operation
    reader "independently authored" and its run "independent evidence". Jie
    Sun, who wrote and ran it from the specification-only packet, is a
    director of Natuvea Ltd, so it is related-party evidence, not independent
    review. The evidence file now says so, and so do ASM-19 in `threat-model/assumptions.md`
    and a `missing_evidence` kind in `security-properties/evidence-index.json`, which called it "the independent
    reader". The L2 target decision still says "independently authored" (lines 8 and 9) and "the independent reader" (line 39), and `tacenta-model/SESSION-OPERATION-MODEL.md` (line 5) says "independent reader"; both change with the next refresh of the source attestation, which hashes `tacenta-model` (`GAP-REGISTER.md`,
    `STALE-WORDING-KNOWN`). Row `READER-INDEPENDENCE` is BLOCKING while
    independence claims the repository does not support remain. The earlier
    wording stands in the tags `tacenta-assurance-v0.2.0` to
    `tacenta-assurance-v0.4.6`.

### Decided
- `decisions/ADR-0009-identity-verification.md` (accepted).
- `decisions/ADR-0010-key-derivation-written-here.md` (accepted):
  `tacenta-kdf`'s SHA-256, HMAC and HKDF are written here, a second exception
  to the no-reimplementation rule after XEdDSA (ADR-0002), with the
  alternatives rejected, the measured costs and the limits.

## [0.2.0] - 2026-09-11

The second citable revision. It contains everything recorded above since 0.1.0.

**What this revision specifies:**
- **The ML-KEM Braid is stated in full:** parameters and derivations, its messages, the state machine with transitions (1) to (13) numbered on the page, and what a send and a receive return. The published document is cited as a source, not an authority, and where the tree departs from it, the page says so.
- **Session establishment:**
  - how the last-resort replay fingerprint is built;
  - what the protocol requires of X25519, ML-KEM-1024 and AES-256-CBC, and what it leaves to them;
  - the exact key path of the initial ciphertext;
  - what follows a refused initial message.
- **XEdDSA:** `identities-and-devices.md` specifies signing and states the verifier's accepted set as rules, not a library name.
- **Canonical curve keys:** every curve public key a peer sends must be its canonical encoding, and is refused at decode. This covers the ratchet header, the prekey bundle and the initial message. A repeated initial message must match the peer's identity as well as its ephemeral key. Which stored curve keys must be canonical is stated as built.
- **Persisted Braid state:** a stored Braid key pair must pass FIPS 203's hash and modulus checks when it is loaded.
- **ADR-0007:** three behaviours are kept as built:
  - the header's `pq_epoch` selects the receiving chain;
  - the leaf readers enforce exactly their stated rules;
  - a Braid receive taking transition (5) reports the epoch it completed.

**How far the text is enough:** a reader written from this revision and the vectors alone, with no access to the implementation, the model or the proofs, passes 402 checks (`tacenta-test-vectors/runners/independent`). That covers every vector, including the erasure, protobuf, persistence, AEAD and decoder-edge vectors added since 0.1.0, and cases derived from the pages' sentences.

**What remains** is recorded in its `GAPS-4.md`. Chiefly:
- most persisted formats (the session, prekey store, ratchet states and Braid) are specified but not yet pinned by vectors;
- simultaneous initiation and session replacement are left to the application.

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
  move tags 0, 5, 6, 10 and 11 (G2-08).
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
- `protocol/sparse-pq-ratchet.md`, `protocol/triple-ratchet.md`: the header's
  `pq_epoch` selects the sparse ratchet's receiving chain, and `pq_n` is the
  message number. The epoch the agreement's receive returns is not used and
  is not compared with `pq_epoch`; a returned secret's own epoch is still the
  one the advance checks. The model's receive takes no returned epoch, and the
  implementation discards it. This departs from Double Ratchet revision 4,
  §5.6, whose header carries no epoch and whose receive uses the returned
  one. The page says so, and ADR-0007 keeps the departure. Independent
  reader, second pass (G2-07).

### Changed
- `protocol/session-persistence.md`, "Braid": the reader refuses as malformed
  a state in tags 1 to 4 whose `key_pair` holds a `header` and `ek_vector`
  that fail the validation a completed `ek_vector` passes against a received
  header (mlkem-braid.md, The KEM split). That is two checks. The first is the
  hash check, `H(ek_vector || rho)` equal to the header's `H(ek)`, which is
  FIPS 203 section 7.3's hash check made on the incremental key pair. The
  second is section 7.2's modulus check on `ek_vector`. The page had said the
  reader checks each KEM field's length and nothing else, so a stored key pair
  with a wrong hash, or with a coefficient at or above q, imported and then
  decapsulated to a wrong secret without an error. A key pair the library
  generates passes both checks and is never changed, so no state the library
  exports is refused. `encaps` is still checked only for its length: it holds
  nothing to check it against (register item J-4).
- `protocol/mlkem-braid.md`, "The erasure code", Codewords;
  `protocol/session-persistence.md`, "Erasure coder sub-formats": an encoder
  holds at most the first 65,536 chunks of its value. Over a value of more
  than 65,536 chunks it holds `chunk_0` to `chunk_65535` and no others. The
  page had left which chunks such an encoder holds unspecified, and the model
  and the implementation differed. The implementation kept the first 65,536.
  The model kept them all, so its encoder broke its own rule that an encoder
  holds at most 65,536 chunks, and its reader refused what its writer wrote.
  The implementation's cap is adopted. What an encoder issues is unchanged,
  and the Braid encodes no such value, so nothing observable in the protocol
  changes. The persisted encoder's `chunk[count]` is now described as the
  chunks the encoder holds (register item J-7).
- `protocol/message-format.md`, `protocol/session-establishment.md`: the
  initial-message decoder refuses an `identity` or `ephemeral` whose
  thirty-two key bytes are not the canonical encoding of a curve public key,
  as a decode failure, as the prekey bundle's and ratchet message's decoders
  refuse theirs. The pages had said the decoder checks only the curve byte and
  `DecodeEC` checks the key bytes later, which left open where a re-spelled
  key is refused, and let a repeated initial message on an established
  session with a re-spelled `identity` be accepted. A repeated initial message
  now also requires `identity` to equal, byte for byte, `EncodeEC` of the
  peer identity key the session holds (`peer_identity_public`), besides
  `ephemeral` equalling `established_ephemeral`. The session already holds
  that key, so no persisted format changes. "Receiving the initial message"
  says which fields a repeat compares, that `kem_ciphertext` and the three
  identifiers are not compared, and why that is safe: the inner message
  authenticates under the session's own keys, its associated data comes from
  session state, and the ratchet refuses a duplicate. Independent reader,
  third pass (G3-05).
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
- `protocol/session-persistence.md`, `protocol/session-establishment.md`,
  `protocol/message-format.md`: which stored curve public keys must be
  canonical, as built. Independent reader, fourth pass (G4-02).
  - The session's shape rule for `established_ephemeral` is that `DecodeEC`
    accepts it, so a re-spelled key there is refused as inconsistent. A
    re-spelled `dhs_pub` is refused as inconsistent because it is not the
    public key of `ratchet_private`, which is canonical.
  - No rule requires `peer_identity_public`, `our_identity_public`,
    `pending_initial`'s `ephemeral_public`, the ratchet state's `dhr_pub`, a
    skipped entry's `dh`, or the prekey store's `identity_public` to be
    canonical, and the readers accept each of them re-spelled. The page says
    what follows from each.
  - "Receiving the initial message" no longer says a repeat is compared
    against canonical encodings in every session: a session read with a
    re-spelled `peer_identity_public` refuses every repeat.
- `protocol/session-establishment.md`, `protocol/error-handling.md`,
  `protocol/message-format.md`: what follows `NotARepeatedInitial`, as built.
  Independent reader, fourth pass (G4-04).
  - The refusal changes nothing, and the session neither establishes a new
    session nor replaces itself.
  - Establishing a new session from the message is the recipient's decision,
    taken as on first receipt. `tacenta-core` provides `establish_responder`
    for it and relates the new session to no other. A repeat of a message
    that already established a session does not establish a second one.
  - For a session reset, a changed identity and simultaneous initiation, the
    specification requires the refusal and leaves the rest to the
    application. After simultaneous initiation, if both sides establish from
    the message they refused, each party holds two sessions, which pair
    across.
  - error-handling.md lists the refusal among the conditions a caller acts on.

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
- `protocol/mlkem-braid.md`, "The erasure code", Codewords: the encoder's two
  edges, as built. Independent reader, third pass (G3-02).
  - For `k = 0` the sum has no terms, so every codeword is 32 zero bytes. The
    indices run as they do for any other `k`.
  - A value of more than 65,536 chunks is not refused. Its encoder issues
    `chunk_0` to `chunk_65535` as indices 0 to 65,535 and then nothing, and a
    decoder for it never completes. Which chunks such an encoder holds was
    left unspecified, since nothing issued depends on the rest; the entry
    under Changed above now specifies the first 65,536 (J-7).
  - The Braid encodes neither, so neither is observable in the protocol.
- `protocol/mlkem-braid.md`, "Receiving": `Ct1Acknowledged` takes transition
  (11) when the completed `ek_vector` validates, and stays while the decoder
  is short. Its bullet now has the same shape as `Ct1Sampled`'s; the
  "Otherwise" it replaces could be read as following a failed validation
  (G3-06).
- `protocol/sparse-pq-ratchet.md`, "What this ratchet assumes underneath it":
  receiving no longer returns "the epoch the sender was working in". The
  ML-KEM Braid returns the epoch of the state its receive leaves it in, less
  one, which at transition (5) is the epoch just completed, as mlkem-braid.md
  and ADR-0007 say. The ratchet does not use the value (G3-08).
- `README.md`, Status: identities-and-devices.md specifies signing and
  verifying as well as the identity key's secret and application signatures.
  The G2-07 entry above says ADR-0007 keeps the departure, where it said the
  departure was undecided (G3-07).

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
