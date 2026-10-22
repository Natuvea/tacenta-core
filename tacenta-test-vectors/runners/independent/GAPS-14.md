# Gap report, fourteenth pass: identity records

The clean-room reader (`reader/`) was extended from `tacenta-spec` and
`tacenta-test-vectors` alone, against the tree as found in this directory:

- `SOURCE-REVISION` `98591a2c50f82c3f1a134649eafa37140ba43b0e`;
- `VERSION` `0.2.0`;
- everything under `CHANGELOG.md` `[Unreleased]`. The entries this pass is
  about are, under Added, the identity pair digest and the verification number
  (`identities-and-devices.md`), Records, expectations and attribution
  (`session-establishment.md`, with REQ-AUTH-15 and REQ-AUTH-16) and the five
  vector files; under Changed, the `session-establishment.md` entry that
  begins "the initiator establishes only with an expectation, which replaces
  the named identity the page let her state", and the entries for
  `error-handling.md`, `identities-and-devices.md`, `CONSTANTS.md`,
  `threat-model/`, `authentication.md` (REQ-AUTH-02 amended), `limitations.md`
  and `evidence-index.json` that follow it; under Decided, ADR-0009
  (proposed).

The pass before this one, the thirteenth, read a local revision taken after
the inventory work (#200) and before the conformance alignment (#202), which is
not a commit of the repository (`GAPS-13.md`). The twelfth read
`1cac363f11305d675844af590a0840774a87656f`.

Severity, as in the earlier reports:

- **BLOCKING**: cannot be implemented from the tree without guessing.
- **AMBIGUOUS**: more than one reading; a vector decided it, or nothing did.
- **MINOR**: wording, pointers, or a value findable only in the wrong place.

A hypothesis confirmed by a vector is still a gap.

**Baseline** (`python3 reader/run.py`, before any change): 1027 PASS, 0 FAIL,
126 SKIP; the exit status was zero.

| | PASS | FAIL | SKIP |
|---|---|---|---|
| Vectors (50 files) | 763 | 0 | 126 |
| Derived cases (14 modules) | 264 | 0 | 0 |
| **Total** | **1027** | **0** | **126** |

125 of the skips were the five identity-record files, allowlisted whole by the
`TEMPORARY` block in `run.py` (38, 9, 20, 14 and 44 vectors). The other was
`identity/initial-message-admission.json` `honest-initial-message`, on the
allowlist since pass 13 with its reason. The other text that changed since
pass 13 (section 1) changed no verdict of the baseline run: every vector and
every derived case passed on the reader as found.

**Final run:**

| | PASS | FAIL | SKIP |
|---|---|---|---|
| Vectors (50 files) | 888 | 0 | 1 |
| Derived cases (15 modules) | 282 | 0 | 0 |
| **Total** | **1170** | **0** | **1** |

The exit status is zero. 888 is the 763 of the baseline and the 125 vectors of
the five files, all of which pass: `pair-digest.json` 38 of 38,
`verification-number.json` 9 of 9, `identity-classification.json` 20 of 20,
`identity-lookup.json` 14 of 14 and `initiator-expectation.json` 44 of 44. The
one skip is `honest-initial-message`, unchanged. The derived cases are the 264
plus RC-01 to RC-18 in the new `cases_records.py`. `work/check_new_vectors14.py`
(88 checks, no problems) confirms that the new vectors pass for the reasons
their comments give (section 3).

**What changed in the reader:**

- **`tacenta_reader/records.py`, new.** `identity_pair_digest` and
  `verification_number`; `Record` (two sets, duplicates ignored,
  `holds_record`); `classify`; `lookup`, whose result is the attribution, the
  contact, the contacts the key is retired for and the records skipped as
  malformed; `attributed_contact`; the two expectations `Known` and
  `FirstContact`; `check_expectation_wellformed` (`MalformedRecord`) and
  `check_bundle_identity` (`UnexpectedIdentity`, `RetiredIdentity`, with the
  identity-key rule applied to the key first). `constants.py` gains
  `PAIR_DIGEST_LABEL` and the 60-digit length.
- **`tacenta_reader/wire.py`, `admission.py`: the named identity replaced by the
  expectation.** Pass 13 read "when its identity key is not the one she set out
  to reach (when she names one)" and gave `initiator_check_bundle` and
  `initiator_prefix` an optional `expected_identity`. The page no longer says
  that, and the CHANGELOG says an implementation that offers initiator
  establishment without an expectation, or with a named key in place of a
  record, does not conform. Both functions now take a required expectation, in
  the page's order: the malformed expectation first; the canonical-key and
  presence checks; the expectation; the identity-key rule; both signatures;
  then, in `initiator_prefix`, the KEM prekey's input checks, the draws and the
  agreements. The bundle's own refusals are now three subclasses of
  `BundleRefused` (`InconsistentBundle`, `NonCanonicalBundleKey`,
  `BundleSignatureFails`), so their kinds can be told apart (G14-03). The KEM
  prekey signature is checked over the key at its own length (G14-06).
- **`run.py`.** The `TEMPORARY` block, `_TEMPORARY_UNREAD_FILES`,
  `_temporary_unread_labels` and the line that added them to the allowlist are
  removed. Five handlers (`pair-digest`, `verification-number`,
  `identity-classification`, `identity-lookup`, `initiator-expectation`), the
  layouts of a list of keys, a list of records, a lookup's result and
  `bundle_fields`, and `acceptable_refusals`. `bundle-admission` now
  establishes under first contact with no records, as the vectors README says.
  `cases_records` in the case table.
- **Cases.** `cases_records.py` (18 cases, RC-01 to RC-18). Changed to the new
  text: PB-09, PB-10, PB-12, PB-13 and PB-15 (`negative_cases.py`) and CK-03
  (`cases_curvekeys.py`) pass an expectation; PB-11 was "refuses an identity
  that is not the one it named" and is now *known* refusing a *new* key as an
  unexpected identity; IK-06 (`cases_idkeys.py`) was written around the named
  identity and is rewritten around *known*, in which a key that fails the rule
  is an invalid identity key whether or not the record names its bytes; SK-09
  (`cases_stored.py`) no longer names a non-canonical spelling as the identity
  she means to reach, since a record cannot hold one: under *known* that
  record is a malformed expectation, refused first. The cite strings of SE-08,
  IK-12 and IK-14 and the docstring of `identity.admit_identity_key` quoted
  sentences the page has since replaced, and now quote the current ones.

---

## 1. The earlier gaps

Counts for the 22 gaps open after pass 13 (G5-04, G5-05, G5-06, G5-07, G5-08,
G5-10, G12-05, G12-06, G12-07, and G13-01 to G13-13): **11 CLOSED, 11 STILL
OPEN, 0 NARROWED**. The gaps recorded as closed before were not re-read one by
one; their cases and vectors all pass in the final run, and nothing this pass
read reopens any of them. No earlier gap was judged wrong.

| Gap | Status | Citation, and what changed in the reader |
|---|---|---|
| G5-04 The work a forged message costs, stated three ways | STILL OPEN | `threat-model/adversaries.md` ADV-01 ("up to `MAX_SKIP` keys before it refuses them") and ADV-06 ("making the victim derive up to `MAX_SKIP`"), and `exclusions.md` ("A skip is refused beyond `MAX_SKIP` before any key is derived"), unchanged. |
| G5-05 LIM-21: "until it is established again" | STILL OPEN | `limitations.md`, LIM-21, unchanged: "encrypt or decrypt until it is established again". `Failed` stays terminal in the reader. |
| G5-06 ASM-13 and ASM-19 are "relied on by every requirement" | STILL OPEN | `assumptions.md`: "every requirement, for the adversary it holds against" and "every requirement, as a statement about `tacenta-core`", unchanged. |
| G5-07 The evidence the requirements cite is outside the specification | STILL OPEN (at pass 7's narrowed extent) | ADR-0006 point 7 and `evidence-index-format.md` ("evidence metadata, not the evidence itself") unchanged. The index now also cites `tacenta-core` symbols and tests for REQ-AUTH-02, -15 and -16, none of which is in this tree. Nothing was looked for. |
| G5-08 The sparse ratchet's retention window: saturating on one page, not on the other | STILL OPEN | `sparse-pq-ratchet.md` still "every epoch `e` with `E < e + EPOCHS_KEPT`"; `session-persistence.md` still "the sum saturating". Unobservable. |
| G5-10 REQ-AUTH-11 does not cite the rule that refuses a replay onto a chain the receiver has left | STILL OPEN | REQ-AUTH-11 unchanged: the same three bullets, "Rests on: ASM-19". |
| G12-05 The sparse store's total bound described the implementation and stated no rule for another | **CLOSED** | `sparse-pq-ratchet.md`, The store also has a total bound, now states the rule as normative: "is refused as `TooManySkipped` when `upto - c` is more than `MAX_SKIP`; otherwise deletes every stored key for that epoch whose number `n` has `c < n` and `n <= upto` ...; counts the keys that remain in the store, whatever their epoch, and is refused as `SkippedStoreFull` when that count plus `upto - c` is more than `MAX_SKIPPED_STORE`", with the refusal leaving the state as it was. The reader's `spqr.receive` already counted the store after the deletion over exactly that range (`chain.n < m < n`, that is `c < m <= upto`); CR-18 and CR-21 pass, and both already quote the new text. |
| G12-06 A repeat's agreement class under the signed-prekey secret on one page and under no named secret on the other | **CLOSED** | `session-establishment.md`, Receiving the initial message: "The class is taken under the session's current ratchet private key (`ratchet_private`, session-persistence.md) ... The signed-prekey secret is not the key"; `session-persistence.md`: "agreement class under the session's `ratchet_private`". The reader already used `ratchet_private`. SE-08's cite now quotes the new sentences. |
| G12-07 Three statements about the prekey store spoke of four versions or of v4 as current | **CLOSED** | Prekey store, Semantic rules: "they apply to all five versions". The vectors README no longer has "write back as current v4" or the other two phrases. The remaining v4 mentions ("`signed_prekey_sig` begins at offset 69 of a v4 store", "the same v4 bytes") describe v4 stores, not the current format. |
| G13-01 The sixth rule put `p - 1` before the signature rule | **CLOSED** | The sixth rule now ends: "The previous rule has already refused, as malformed, every `identity_public` that is not an identity key, `p - 1` among them, before any signature is checked; this rule is reached only by a store whose `identity_public` passes it." That is the reading the reader took. The introductory paragraph now says "the identity key's admission". |
| G13-02 "A key that is not canonical is still a decode failure" for every boundary | **CLOSED** | Identity keys, A refusal: "A key that is not canonical is refused as it always was: as a decode failure where a wire encoding is read, and by the kind that session-persistence.md, Rejection, names for a stored state"; `error-handling.md` says the same. The reader's reading. |
| G13-03 The refusal for a non-canonical key handed to the rule alone is named only in the README and schema | STILL OPEN | The schema still says `identity-key.json`'s non-canonical spellings are `invalid-identity-key`. The new pages name a decode failure for a non-canonical *presented* key (the digest, the classification), which is a boundary, not the rule alone. |
| G13-04 The KEM key check's position, and whether a random value is drawn before it | **CLOSED** | Primitives, ML-KEM-1024: "Whether she has drawn `EKA` before these checks is not fixed." The expectation is now before "the KEM prekey's input checks". The reader draws nothing before them, which the text allows; RC-13 and the handler require only that no agreement precedes a `kem-input` refusal, and control C14-03 (EKA drawn first) fails nothing. |
| G13-05 The kind of a repeat whose `identity` fails the rule | **CLOSED** | Receiving the initial message: "it refuses the message (`NotARepeatedInitial`); that includes a message whose `identity` is not an identity key, since it does not equal the peer's identity key the session holds". The reader's reading (IK-13). |
| G13-06 The two scans are named and not specified | **CLOSED** | `session-persistence.md` no longer names them: "can find the states it will refuse beforehand by reading the identity keys of every stored state and applying the rule to each". The reader's `scan_stored_*` functions are its own helpers; IK-12's cite updated. |
| G13-07 "Which she checks first" against "after the presence, pinning and canonical checks" | **CLOSED** | Sending the initial message: "which she checks before either signature (below)"; REQ-AUTH-01 the same. |
| G13-08 `u = p - 1` is a "low-order value" and a u no point has | STILL OPEN | Accepting a signed statement, check 6, unchanged: "the five low-order values: the u-coordinates 0, 1 and p − 1, and the two of order eight". `pair-digest.json` and `initiator-expectation.json` call `p - 1` neither. No verdict depends on it. |
| G13-09 `error-handling.md` lists the stored kinds without `incoherent` | **CLOSED** | "inconsistent or, for a prekey store, incoherent". |
| G13-10 The XEdDSA vectors and the manifest say "rule 3 (A is not of small order)" | STILL OPEN | `xeddsa.json`'s source and comments, the vectors README (Regenerating) and the manifest's XEdDSA row still say "rule 3 (A is not of small order)". |
| G13-11 The schema named one of the three identity files as carrying `invalid-identity-key` | **CLOSED** | The schema's `refusal`: "invalid-identity-key is carried by every invalid vector of identity-key.json, bundle-admission.json and initial-message-admission.json". |
| G13-12 A responder whose identity is not the store's | STILL OPEN | No sentence added. |
| G13-13 Two different revoked bindings that share a `device_id` | STILL OPEN | Check 5 unchanged; the manifest still lists it as not stated. |

---

## 2. New gaps

### G14-01 Three requirements and one limitation say no vector covers what five vector files now pin (MINOR)

- **Where:** `security-properties/authentication.md`, REQ-AUTH-02, Status: "No
  vector or proof covers it (limitations.md, LIM-13) ... The two forms,
  `RetiredIdentity`, `MalformedRecord` and the order have no test or vector
  yet"; REQ-AUTH-15, Status: "**tested only.** No test or vector covers it
  yet"; REQ-AUTH-16, Status: "No vector covers them yet";
  `limitations.md`, LIM-13: "REQ-AUTH-02 remains tested only. No vector or
  proof covers it." Against `CHANGELOG.md` [Unreleased], Added: the five files
  under `vectors/identity/`, and "`evidence-index.json` cites them for
  REQ-AUTH-02, -15 and -16, whose statuses do not change"; and
  `evidence-index.json`, whose entries for the three requirements list those
  files and case ids.
- **Problem:** the status lines contradict the index and the tree. REQ-AUTH-15
  is "tested only" with no test or vector named, which the page's own
  definition of the status ("*Tested only* names the tests or vectors") does
  not allow.
- **Resolution:** none needed for an implementation. The reader treats the
  vector files as pinning what the README says they pin.

### G14-02 A malformed expectation against a bundle that does not decode (MINOR)

- **Where:** Records, expectations and attribution, The initiator: "She
  refuses an expectation as a malformed record (`MalformedRecord`), before any
  check of Sending the initial message"; the same page, "Malformed input is
  reported as such. A bundle that fails decoding, the presence check or the
  canonical-key check is reported as that"; `error-handling.md`, "The order of
  checks ... unless a page fixes an order".
- **Problem:** decoding a bundle is the decoder's (message-format.md), not one
  of the checks Sending the initial message lists. For a malformed expectation
  and a bundle that does not decode, the page does not say which refusal is
  reported. The "Malformed input" bullet orders a decode failure ahead of a
  *refused identity*, not ahead of a malformed expectation. Every
  `malformed-record` vector's bundle decodes.
- **Resolution:** the reader refuses the expectation before it decodes the
  bundle (`admission.initiator_prefix`), on ADR-0009's reason, "she must know
  her expectation before acting on it". No vector or case tells the readings
  apart.

### G14-03 The kinds of the bundle's own refusals are named by the vectors, not the text (AMBIGUOUS)

- **Where:** Sending the initial message: "She also refuses a bundle ... when
  its one-time curve prekey and that prekey's identifier disagree ..., or when
  its identity key, signed prekey or one-time curve prekey is not the
  canonical encoding" (no kind); Primitives, ML-KEM-1024: "Alice refuses a
  bundle whose key fails either check" (no kind); `error-handling.md`: the
  error types and "which variant reports a given refusal, beyond the kinds
  above", are left to an implementation, and "A key that is not canonical is
  refused as it always was: as a decode failure where a wire encoding is
  read". Against the schema's `refusal` (`inconsistent-bundle`,
  `non-canonical-key`, `authentication-failure`, `kem-input`,
  `non-contributory`) and `initiator-expectation.json`.
- **Problem:** the vectors require a runner to report five distinct kinds for
  refusals the text names no kind for, and the text leaves which variant
  reports them to the implementation. An implementation that reports the
  presence and the canonical-key refusals as one kind conforms to the pages
  and fails the vectors by name. The initiator's own canonical-key check of a
  bundle that reached her without the decoder is a further case: read with
  `error-handling.md`, it could be a decode failure (it is the same rule the
  decoder applies, and the key's bytes are a wire encoding); the vectors say
  `non-canonical-key`, a kind distinct from `decode-failure`.
- **Resolution:** the reader keeps the five apart, `BundleRefused` subclasses
  for the first three, as the vectors name them. The vectors decided it.

### G14-04 The verification number's input and its grouped layout (MINOR)

- **Where:** The verification number: "verification_number(digest): n = digest
  read as an unsigned big-endian integer ... The digits may be laid out in
  twelve groups of five."
- **Problem:** the function is stated over "digest" without a length; every
  vector gives 32 bytes, and the page's only caller is the 32-byte digest. The
  grouped layout names no separator, so two implementations that both group
  show different strings; the page makes the layout optional and the README
  says it is not pinned. Neither affects the 60 digits.
- **Resolution:** the reader refuses an input other than 32 bytes (RC-04 says
  so as its choice) and gives the groups as a list.

### G14-05 A lookup's result is fixed in words; its form comes from the vectors' layout (MINOR)

- **Where:** Lookup: "A record whose classification is refused as a malformed
  record is skipped: it attributes nothing, and it is reported ... Wherever a
  lookup finds the key *retired* for a contact, that is reported alongside its
  result ... Their results are fixed here; their names and signatures are
  not."
- **Problem:** what "reported" consists of is not stated: whether the
  malformed records and the contacts the key is retired for are named, in what
  order, and whether a *retired key* result names "those contacts" separately
  from the retired-for report (the page says the key "is a *retired key* of
  those contacts"). Whether an *ambiguous* result names the contacts it is
  *same* for is not said either (the vectors README says the page does not
  say a lookup reports them, and leaves them out). The vectors' layout supplies
  one form: contacts as record indices, in record order.
- **Resolution:** the reader's `LookupResult` carries the contacts the key is
  retired for and the malformed records in record order, and keeps the *same*
  contacts of an ambiguous key outside what it compares. The layout decided
  the form; the text decides only the attribution.

### G14-06 The signature input for a KEM prekey of the wrong length, and its place against the KEM checks (AMBIGUOUS)

- **Where:** Publishing keys: "the signed last-resort KEM prekey ... and
  `Sig(IKB, EncodeKEM(PQSPKB), Z)`"; message-format.md, EncodeKEM, a fixed
  width for the KEM's key; Sending the initial message: "She also refuses a
  bundle ... The check is for a bundle that reaches her some other way";
  REQ-AUTH-01: "She checks both before any agreement or encapsulation";
  Primitives, ML-KEM-1024: "Before encapsulating, `PQKEM-ENC(PK)` applies FIPS
  203 section 7.2's input checks ...: its length is 1,568 bytes, which the
  bundle decoder already requires". Against `initiator-expectation.json`
  `known-same-short-kem-prekey` and `known-same-long-kem-prekey`
  (`bundle_fields`, KEM prekeys of 1,567 and 1,569 bytes, refused as
  `kem-input`).
- **Problem:** a bundle that reaches the initiator without the decoder can
  carry a KEM prekey of another length. The signatures come before the KEM
  input checks, so her KEM prekey signature check runs on that key first, and
  `EncodeKEM` of a key of the wrong length is not defined. One reading
  (`EncodeKEM` refuses it) gives an authentication failure or an encoding
  error; another (the type byte and the key's bytes) lets the signature
  verify and the length check refuse it as `kem-input`; a third makes the
  length check first. The vectors name `kem-input`. This pass saw, while
  surveying the file's bundles before implementing, that the two rows'
  signatures verify over the type byte followed by the key's bytes; that is a
  hypothesis a vector confirms, so it is recorded here.
- **Resolution:** the reader verifies the KEM prekey signature over the type
  byte and the key at its own length, then refuses the length in the KEM
  checks (`wire.initiator_check_bundle`, `kem_prekey_len=None`). The vectors
  decided it.

### G14-07 What the pages say of `tacenta-core`'s conformance disagrees (MINOR)

- **Where:** ADR-0009, Context: "`tacenta-core` has not changed yet. It offers
  initiator establishment with a named key and without one, and has none of
  what this record decides. Until it changes, it does not conform to the pages
  this record amends"; Consequences: "It will drop initiator establishment
  without an expectation, and provide the classification, the lookup and the
  digest". Against `evidence-index.json`, which names `tacenta-core` symbols
  (`classify`, `lookup`, `identity_pair_digest`, `verification_number`,
  `establish_initiator`, `expectation_refusal`) and tests for REQ-AUTH-02,
  -15 and -16; and REQ-AUTH-02's status, which describes a test of "an
  expectation of one named key".
- **Problem:** the specification states, in different places, that the
  implementation has none of this and that it has it. Nothing an implementer
  needs depends on it, and the reader looked at none of the named symbols.
- **Resolution:** none needed.

**No BLOCKING gap.** Every refusal and every value the five files name could be
decided from the text, given the layouts in the vectors README.

**Where the text was not enough to decide a vector's verdict:** the kinds
G14-03 lists and the wrong-length KEM prekey of G14-06, which the vectors
decided. The form of a lookup's result (G14-05) comes from the layout.

**Disagreements between a vector and the text: none.** The 125 vectors agree
with the reading this reader took from the pages.

---

## 3. Vector gaps: specified, but no vector pins it

### The new vectors pass for the stated reasons

`work/check_new_vectors14.py` (88 checks, no problems):

- **`pair-digest.json`.** Every `-swapped` row is its pair with the keys
  exchanged and the same fields or refusal. The two `unsigned-order-*` pairs
  disagree with the little-endian value order, and the second also with the
  signed-byte and u64-limb orders, by the reader's own comparison.
  `torsion-translate` is a torsion translate of the first key. `u-p-and-u-0`
  has one non-canonical key and one canonical non-identity key.
- **`verification-number.json`.** The four digests the comments attribute to
  `pair-digest.json` are those rows' digests, with the same numbers; the
  `big-endian` row's comment gives the little-endian reading the reader
  computes.
- **`initiator-expectation.json`.** Each row refused by its expectation was
  established again under *known* with the bundle's own key current. The
  refusal the comment says the expectation hides then appears: an
  authentication failure for the bad-signature rows (including the
  malformed-record and empty-record rows), `kem-input` for the unencodable and
  short KEM prekeys, `non-contributory` for the low-order prekeys,
  `invalid-identity-key` for `known-malformed-record-non-identity-key`, and a
  session for the rows with nothing else wrong. The `known-new-*` and
  `known-same-*` rows that share a defect share the defective field's bytes.

### New in this pass: rules the text states that no vector pins

Fault numbers refer to section 5. Where a fault is caught by a derived case and
by no vector, no vector pins the rule.

- **A malformed expectation before the presence and canonical-key checks**
  (F14-43; RC-14). Every `malformed-record` row's bundle passes those checks.
  Its order against decoding is not stated (G14-02).
- **First contact, a key in a record other than the first** (F14-36; RC-11).
  In every first-contact refusal, contact 0's record alone gives the same
  refusal.
- **First contact over records that include an empty one is not malformed**
  (F14-40; RC-09).
- **First contact applies the identity-key rule to the key before its lookup**
  (F14-42; RC-12). No first-contact row presents a non-identity key that a
  record holds; under *known*, `known-retired-mixed-order-identity` pins it.
- **The presence and canonical-key checks before the expectation under first
  contact, and the canonical checks of the signed and one-time prekeys before
  it under either form** (RC-13). The rows that fail those checks are under
  *known*, and the re-spelled rows re-spell the identity key only.
- **The order of the expectation against the identity-key rule** is not
  observable: the expectation applies the rule first, so moving the rule ahead
  of an expectation that does not apply it gives the same refusals (F14-54,
  equivalent). The vectors README says the same.
- **The signatures before the KEM prekey's input checks.** No row fails both.
- **Attribution against the records as they stand** (F14-51; RC-16): recording
  or retiring a key changes the attribution of an existing session. The files
  pin a lookup at one moment.
- **The responder adds no refusal for records** (RC-17), which the manifest
  says is tested in the implementation.
- **No establishment without an expectation, or with a named key** (F14-52;
  RC-15). A vector cannot pin what is not offered.
- **The way forward from a recorded key the rule refuses**: record the new
  key, retire the refused one, establish under *known* (RC-18).
  `known-record-with-non-identity-member` pins half of it (a non-identity
  member does not make the record malformed).
- **The verification number in twelve groups of five** (G14-04), as the README
  says.

### `GAPS-13.md`'s vector gaps, re-assessed

| Vector gap | Status | Note |
|---|---|---|
| The bundle's other keys are not held to the identity-key rule | NARROWED | `known-same-low-order-*` now pin a low-order signed or one-time prekey refused as `non-contributory`, not as an invalid identity key. A mixed-order one admitted is still unpinned (IK-07). |
| The order among the initiator's checks | NARROWED | `initiator-expectation.json` pins presence and the identity key's canonical check before the expectation, and the expectation before the signatures, the KEM checks and the agreements, with no draw before. What is left is listed above. |
| Pinning an identity that itself fails the rule | **CLOSED** | The named identity is gone. `known-retired-mixed-order-identity` and `known-non-identity-key-*` pin that the expectation refuses such a key as an invalid identity key. |
| The responder's checks around the identity check; the responder's ephemeral; the prekey store rule in versions 1 to 4; `p - 1` as a stored identity key; a repeat whose `identity` fails the rule; application signatures; a key read from bytes staying a decode failure at the admission boundaries; a mixed-order issuer key; a well-formed initial message naming a refused key; the identity secrets in the admission files; two revoked bindings with one `device_id`; the rule's reach past the first inventory entry | STILL OPEN | Unchanged. The re-spelled `bundle_fields` rows pin `non-canonical-key` at the initiator's own check, not the decoder's decode failure. |
| The scans and "refused, not deleted, not repaired" | NARROWED | The scans are no longer named (G13-06). "Not repaired" is still pinned by no vector (IK-16). |

`GAPS-12.md`'s and `GAPS-7.md`'s vector gaps, as `GAPS-13.md` left them: not
re-examined row by row; nothing this pass read touches them.

---

## 4. Not attempted, and why

Unchanged from `GAPS-13.md`: ML-KEM-1024 and its incremental split; the
end-to-end `Session`; prekey store operations other than the two rotations;
group messaging beyond the two commitments and the inventory statement; full
JSON-Schema validation; the evidence the requirements cite. The initiator still
stops at `PQKEM-ENC`, so a session in `initiator-expectation.json` is checked to
the point the vectors pin: the peer identity key, the lookup, both signatures
verified and the two 32-byte draws made in order, the four agreements
contributory. No initial message is built.

Attribution, labels and what an application shows are the party's (EX-09) and
are not modelled beyond `attributed_contact`.

`reader/test_session_e2e_sweep.py` resolves the vectors by the repository's
layout and does not run in this directory; it is unchanged, and it failed the
same way before this pass.

---

## 5. Deliberate faults

55 faults and 5 controls (`work/faults14.py`), each a textual change, or for
six of them a set of changes that moves one check, to a fresh copy of the
reader, then the full runner. **54 were caught, 48 of them by a vector file.**
The one not caught is equivalent. Per fault, with the vector files and cases
that failed: `work/faults14.txt` and `work/faults14.json`.

| | Tried | Caught | Caught by a vector file |
|---|---|---|---|
| The digest: the byte order of the key sort (little-endian value, signed bytes, u64 limbs, none, descending), the label (case, terminator), the keys held only to the canonical encoding, the refusal kind, the `EncodeEC` form (F14-01 to F14-10) | 10 | 10 | 10 |
| The verification number: the byte order, the padding (none, on the right, spaces), the leading 60 digits in place of mod 10^60, mod 10^59 (F14-11 to F14-16) | 6 | 6 | 6 |
| Classification: same over retired, first match, members held to the identity-key rule, the record before the presented key, the presented key's identity-key rule dropped so that its bytes can match a member, membership by agreement class, only the current set checked (F14-17 to F14-23) | 7 | 7 | 7 |
| Lookup: a malformed record refuses the lookup or is not reported, retired anywhere taking precedence over a contact's, retired contacts not reported beside a contact's result, an ambiguous key given to the first contact, no key check without records (F14-24 to F14-29) | 6 | 6 | 6 |
| The expectation: retired reported as unexpected; under first contact, retired taking precedence over a contact's key, an ambiguous key or a retired key going on, the union of the records classified as one, nothing refused, only the first record looked up, the retired sets ignored; an empty *known* record accepted; a non-canonical first-contact record accepted; an empty first-contact record refused; the expectation without the identity-key rule, under each form (F14-30 to F14-42) | 13 | 13 | 10 |
| The order: the malformed expectation after the presence and canonical checks, and after the signatures; the expectation before the presence and canonical checks, before presence only, after the signatures, after the KEM checks, after the draws and agreements, after the identity-key rule; a draw before the checks; the identity-key rule before the canonical checks (F14-43 to F14-50, F14-54, F14-55) | 10 | 9 | 8 |
| Attribution, establishment without an expectation, a refusal's kind (F14-51 to F14-53) | 3 | 3 | 1 |
| **Total** | **55** | **54** | **48** |

**Not caught, one, and why:**

- **F14-54** (the expectation moved after the identity-key rule, and no longer
  applying the rule itself) is equivalent: the rule then refuses every key it
  would have refused inside the expectation, with the same kind and before
  anything is spent. The page states both the order and that the expectation
  applies the rule first, and those two together make the order unobservable.

**Caught by derived cases alone, six:** F14-36, F14-40, F14-42, F14-43, F14-51,
F14-52. These are the rules section 3 lists as pinned by no vector.

**Changes made during the run.** The first run (`work/faults14-first-run.txt`)
missed four faults, each because the fault was written wrong: F14-47
and F14-48 added a second expectation check after the KEM checks and after the
agreements without removing the first, F14-52 let a `None` expectation through
one of the two functions that refuse it, and F14-42 returned early for a
non-identity key, which the identity-key rule then refused anyway. Each was
rewritten as the change it names (F14-47, F14-48, F14-52 as moves or pairs of
edits, F14-42 as a lookup by bytes); all four are caught on the later runs.
F14-54 was added on the second run (`work/faults14-second-run.txt`). F14-43
first removed only one of the two malformed-expectation checks and was caught by
SK-09 alone; on the third run it moves the check after the presence and
canonical checks, and F14-55 moves it after the signatures. Before the fault
runs, the handler and RC-13 required no draw before a `kem-input` refusal; the
text leaves that open and the README makes the KEM check one of the two
refusals that may follow a draw, so both now require only that no agreement
precedes it (control C14-03).

**Controls.** C14-01 to C14-05 change nothing, as expected: the presence check
before the canonical-key checks (no order fixed), the digest checking `k2`
before `k1` (either refusal conforms), `EKA` drawn before the KEM checks (not
fixed), the identity-key rule after the expectation dropped (the expectation
applies it first), and the digest checking both keys' canonical encodings
before either key's identity-key rule (either refusal conforms).

---

## 6. Isolation

- **What was read:** this directory and nothing else.
  - `tacenta-spec/`: `protocol/identities-and-devices.md` in full;
    `protocol/session-establishment.md`, Publishing keys to Records,
    expectations and attribution (lines 100 to 620) and Primitives to the end;
    `protocol/error-handling.md` in full; `CHANGELOG.md` `[Unreleased]` in
    full; `decisions/ADR-0009-identity-verification.md` in full;
    `security-properties/authentication.md`, the introduction, REQ-AUTH-01,
    -02, -11, -15 and -16; `limitations.md`, LIM-13 to LIM-19 and the LIM-21
    sentence; `evidence-index.json`, the entries for REQ-AUTH-02, -15 and -16;
    `CONSTANTS.md`, the `PAIR_DIGEST_LABEL` row and the Bounds table;
    `threat-model/assumptions.md` ASM-14 and `exclusions.md` EX-09;
    `VERSION`; and, to re-assess the open gaps, passages of
    `session-persistence.md` (Session, Semantic rules to the paragraph on older
    states; Prekey store, Semantic rules), `sparse-pq-ratchet.md` (Receiving
    and The store also has a total bound), `adversaries.md`, `exclusions.md`,
    `assumptions.md`, `evidence-index-format.md` and ADR-0006, found by
    searching for the sentences the gaps quote.
  - `tacenta-test-vectors/`: `README.md` (the list of headings, The identity
    keys and Identity records, and searches for the v4 phrases and "rule 3");
    `conformance-manifest.md` (Covered: identity keys, and searches);
    `schema/vector.schema.json` (the descriptions of `result`, `inputs`,
    `output`, `refusal`, `acceptable_refusals` and `fields`); the five new
    files under `vectors/identity/` in full, `initiator-expectation.json` with
    its long inputs shortened for display and its bundles parsed by the
    layout (G14-06 records what that showed); a search of
    `vectors/primitives/xeddsa.json` for "rule 3" and "rule 6".
  - `reader/`; `GAPS-13.md` in full; the last lines of `GAPS-11.md` (its tally);
    `SOURCE-REVISION`. `GAPS.md` to `GAPS-10.md` and `GAPS-12.md` were not
    opened.
- **Outside this directory.** Nothing outside it was read, listed or searched.
  Every command named paths inside this directory. Python ran from the system
  installation and loaded its standard library, as any run does.
  **Reads attempted outside this directory: none.**
- **Names treated as text.** The pages, the README, the manifest and the
  evidence index name implementation files, symbols, tests and generators
  (`generate-identity-vectors.py`, `Model.IdentityRecords`,
  `Model.InitiatorExpectation.establishInitiatorExpecting`,
  `tacenta-core/src/sessions/identity.rs` and its functions and tests,
  `runners/rust/tests/identity.rs`, `tests/identity_responder.rs`). None was
  looked for.
- **What was written:** only inside this directory:
  - `reader/`: the new `tacenta_reader/records.py` and `cases_records.py`;
    changes to `tacenta_reader/wire.py`, `admission.py`, `identity.py`,
    `constants.py` and `__init__.py`; `negative_cases.py`, `cases_stored.py`,
    `cases_curvekeys.py` and `cases_idkeys.py` (section "What changed in the
    reader"); `run.py`; `README.md`;
  - `GAPS-14.md`, and the two tally sentences of `GAPS-11.md`, which `run.py`
    checks;
  - `work/`: `baseline14.txt`, `run14-*.txt`, `check_new_vectors14.py` and its
    output, `faults14.py`, `faults14.txt`, `faults14-first-run.txt`,
    `faults14-second-run.txt`, `faults14.json`, `final-run14.txt`, and
    `reader-baseline14/`, a copy of the reader as found.

  The per-fault copies were made under `work/faults14/`, each reaching the
  vectors through a symbolic link inside this directory, and were removed after
  each run. Python wrote its usual `__pycache__` directories inside `reader/`.
- **What was not consulted:** no implementation (tacenta-core, tacenta-model,
  tacenta-proofs, the Rust runner, libcrux, libsignal or anything derived from
  them), no git history, no vector generator, no other scratch files, and no
  web search. FIPS 180-4 (SHA-256, through `hashlib`) and RFC 7748 were used
  from knowledge. Nothing was fetched. Only the Python standard library was
  used.
- **Unrelated notes, not used.** An index of notes from other work was in
  view from the start of this pass; no read this pass made put it there. None
  of the notes it lists was opened, and nothing in it was used for any reading
  or decision here.
