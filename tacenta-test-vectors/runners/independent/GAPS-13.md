# Gap report, thirteenth pass: identity keys

The clean-room reader (`reader/`) was extended from `tacenta-spec` and
`tacenta-test-vectors` alone, against the tree as found in this directory:

- `SOURCE-REVISION`, a local revision of this branch taken after the merge of the inventory work (#200) and before the merge of the conformance alignment (#202); it is not a commit of the repository;
- `VERSION` `0.2.0`;
- everything under `CHANGELOG.md` `[Unreleased]`. The entry this pass is about
  begins "Identity keys are held to one rule at every boundary that admits
  one." It adds `identities-and-devices.md`, Identity keys, and changes
  Verifying a signature (step 3), Application signatures,
  `session-establishment.md` (Sending the initial message, Receiving the initial
  message), `session-persistence.md` (Session and Prekey store, Semantic rules;
  Stored curve public keys; the paragraphs on older states),
  `error-handling.md`, `message-format.md` (Curve public keys) and
  `authentication.md` (REQ-AUTH-01).

The pass before this one, the twelfth, read
`1cac363f11305d675844af590a0840774a87656f` (`GAPS-12.md`). Pass 11 was not
used. The last full pass before those, the seventh, read
`5ae44427d17d0e8bfa1d314780305690000ee770`.

Severity, as in the earlier reports:

- **BLOCKING**: cannot be implemented from the tree without guessing.
- **AMBIGUOUS**: more than one reading; a vector decided it, or nothing did.
- **MINOR**: wording, pointers, or a value findable only in the wrong place.

A hypothesis confirmed by a vector is still a gap.

**Baseline** (`python3 reader/run.py`, before any change): 911 PASS, 12 FAIL,
61 SKIP; the exit status was non-zero.

| | PASS | FAIL | SKIP |
|---|---|---|---|
| Vectors (45 files) | 667 | 12 | 61 |
| Derived cases (13 modules) | 244 | 0 | 0 |
| **Total** | **911** | **12** | **61** |

The twelve failures were the rows the reader read but did not yet refuse:

- `persistence/session-state.json`, six: `peer-identity-mixed-order`,
  `-low-order`, `-no-curve-point` and the three `own-identity-*` rows ("stored
  bytes accepted; expected inconsistent");
- `persistence/prekey-store-state.json`, three: `identity-public-mixed-order`,
  `-low-order`, `-no-curve-point` (refused as `incoherent`, where the vector
  names `short-or-malformed`);
- `primitives/xeddsa.json`, three: `reject-mixed-order-A-order8`, `-order4`,
  `-order2` ("verify-only vector accepted, expected invalid").

The sixty-one skips were the sixty rows of the three files under
`vectors/identity/`, which the runner did not know as a kind, and
`session-establishment/session-e2e.json`, as in passes 10 and 12. The runner's
skip allowlist gate also failed, for the sixty unexpected skips.

**Final run:**

| | PASS | FAIL | SKIP |
|---|---|---|---|
| Vectors (45 files) | 738 | 0 | 2 |
| Derived cases (14 modules) | 263 | 0 | 0 |
| **Total** | **1001** | **0** | **2** |

The exit status is zero. 738 is the 667 that passed at the baseline, the
twelve that failed, and 59 of the 60 identity rows: `identity-key.json` 39 of
39, `bundle-admission.json` 10 of 10, `initial-message-admission.json` 10 of 11.
The two skips are `session-e2e.json` and `initial-message-admission.json`
`honest-initial-message`, which is on the skip allowlist with its reason
(section 4). The derived cases are the 244 plus 19: IK-01 to IK-17 in the new
`cases_idkeys.py`, and IV-23 and IV-24 in `cases_inventory.py`.
`work/check_new_vectors13.py` (231 checks, no problems) confirms that the new
vectors pass for the reasons the text gives (section 3).

**What changed in the reader:**

- **`tacenta_reader/curve25519.py`.** Verifying a signature, step 3, is now
  "`qA` is the identity" in place of "not of small order". New
  `is_identity_key`, the rule as the text states it once (Accepting a signed
  statement, check 6) and applies it at every boundary, and the two helpers
  it and the verifier share for steps 1 and 2. `inventory.py` now uses this
  function in place of its own copy.
- **`tacenta_reader/wire.py`, `identity.py`.** `InvalidIdentityKey`, the third
  outcome beside `DecodeError` and a signature that does not verify. The
  initiator's bundle check applies the rule after the presence, pinning and
  canonical checks and before either signature. `verify_application` applies
  the rule first and answers no. `admit_identity_key` for a key read from
  bytes, which keeps a non-canonical key a decode failure.
- **`tacenta_reader/admission.py`, new.** The initiator's steps from a fetched
  bundle to the four Diffie-Hellman outputs, and the responder's from an
  initial message to just before decapsulation, in the orders the two pages
  give, with a source of random bytes that records its draws and counters for
  signatures verified, agreements computed, encapsulations made, private keys
  used and stored state changed. Encapsulation and decapsulation are not
  computed (section 4).
- **`tacenta_reader/persistence.py`.** A stored session's `our_identity_public`
  and `peer_identity_public` must be identity keys (`inconsistent`); a stored
  prekey store's `identity_public` must be an identity key (`malformed`, before
  any signature is checked). `scan_stored_session_identities` and
  `scan_stored_prekey_identity`, which the page names (G13-06).
- **`tacenta_reader/inventory.py`.** The step after check 7 is now the atomic
  step the text describes; if its second evaluation of the freshness rule
  refuses, the statement is refused as check 4 refuses it (G12-04, closed).
- **`run.py`.** Three handlers (`identity-key`, `bundle-admission`,
  `initial-message-admission`), `cases_idkeys` in the case table, and the one
  new skip label on the allowlist.
- **Cases.** `cases_idkeys.py` (17 cases). IV-09 rewritten for the new check 4
  sentence, and IV-23 and IV-24 added to `cases_inventory.py`. SK-04 and SK-08
  in `cases_stored.py` changed: both had read `p - 1` as an accepted stored
  identity key, which the new text refuses (G13-01).

---

## 1. The earlier gaps

Counts for the thirteen gaps open after pass 12 (G5-04, G5-05, G5-06, G5-07,
G5-08 and G5-10 from pass 5; G12-01 to G12-07): **4 CLOSED, 9 STILL OPEN,
0 NARROWED**. The gaps recorded as closed before (G-01 to G-28, G2-01 to G2-12,
G3-01 to G3-08, G4-01 to G4-04, G5-01 to G5-03, G5-09, G6-01 to G6-05, G7-01 to
G7-06) were not re-read one by one; their cases and vectors all pass in the
final run, and nothing this pass read reopens any of them. No earlier gap was
judged wrong.

| Gap | Status | Citation, and what changed in the reader |
|---|---|---|
| G5-04 The work a forged message costs, stated three ways | STILL OPEN | `threat-model/adversaries.md` ADV-01 ("make a receiver derive up to `MAX_SKIP` keys before it refuses them") and ADV-06 ("making the victim derive up to `MAX_SKIP` keys before the forgery is found"), and `exclusions.md` ("A skip is refused beyond `MAX_SKIP` before any key is derived"), unchanged. The reader follows the protocol pages (CR-08). |
| G5-05 LIM-21: "until it is established again" | STILL OPEN | `security-properties/limitations.md`, LIM-21, unchanged: "The session then refuses to encrypt or decrypt until it is established again." `Failed` stays terminal in the reader. |
| G5-06 ASM-13 and ASM-19 are "relied on by every requirement" | STILL OPEN | `threat-model/assumptions.md`: ASM-13 "every requirement, for the adversary it holds against"; ASM-19 "every requirement, as a statement about `tacenta-core`; in particular ...", unchanged. |
| G5-07 The evidence the requirements cite is outside the specification | STILL OPEN (at pass 7's narrowed extent) | ADR-0006 point 7 unchanged. `security-properties/evidence-index-format.md` still says the index is "evidence metadata, not the evidence itself"; its `requirements` array has 32 entries and an `invariants` array. The theorems, tests and `CLAIMS.md` sections it names are still outside this tree. Nothing was looked for. |
| G5-08 The sparse ratchet's retention window: saturating on one page, not on the other | STILL OPEN | `sparse-pq-ratchet.md`, Retiring old epochs, still "every epoch `e` with `E < e + EPOCHS_KEPT`"; `session-persistence.md`, Semantic rules of the leaf formats, still "the sum saturating". Unobservable. |
| G5-10 REQ-AUTH-11 does not cite the rule that refuses a replay onto a chain the receiver has left | STILL OPEN | `authentication.md`, REQ-AUTH-11, unchanged: the same three bullets, "Rests on: ASM-19". |
| G12-01 The scripted policy's two answers are stated as necessary conditions or over a unique entry | **CLOSED** | `tacenta-test-vectors/README.md`, The hosted-inventory statements: "A generation is current for an account exactly when `fresh` lists that pair", and a binding is refused when its key is `refuse_binding.identity_hex` and it is in the list `refuse_binding.status` names, "however many entries share that key". Both halves of the gap are now stated. |
| G12-02 Check 3 does not say which XEdDSA verifier, or what form the resolved key takes | **CLOSED** | `identities-and-devices.md`, Accepting a signed statement, check 3: "The 32 bytes the binding returns are read as the key `u` of Verifying a signature, whatever they are, and the message `M` is the input above, so a key that fails steps 1 to 6 there is a signature that does not verify, not an unbound issuer." Verifying a signature now names "an inventory statement" among the inputs it verifies. The reader's reading (any value counts as resolved; the page's verifier) is the text. IK-17 adds the mixed-order issuer key. |
| G12-03 The signed statement's framing and its refusal kind are stated for the unsigned decoder only | **CLOSED** | `identities-and-devices.md`, Hosted device-inventory statements: "The last 64 bytes are the signature and every byte before them is the unsigned preimage, which must decode exactly, so an input shorter than 64 bytes or one whose remaining bytes do not decode is a decode failure." The reader splits at 64 from the end, as it did. |
| G12-04 Check 4's compare-and-advance does not say what happens to a statement whose advance fails | **CLOSED** | Accepting a signed statement, check 4: "that step is one atomic step that evaluates the freshness rule again against the value then stored and, if the rule accepts, records the generation; if it does not, the statement is refused as this check refuses it. A stored value never decreases." `inventory.py` now refuses such a statement as `freshness` (the reader had kept it accepted); IV-09 rewritten to the sentence and shows, by a plain-write variant, that it reaches the hazard the page names. |
| G12-05 The sparse store's total bound now describes the implementation and states no rule for another | STILL OPEN | `sparse-pq-ratchet.md`, The store also has a total bound: "The current sparse implementation and model check the pre-purge store length; they do not yet implement resulting-store replacement semantics ... open `HL-R1-SPARSE-TRANSLATION` follow-up, not current sparse behaviour", unchanged. The reader keeps the resulting-store count (CR-18, CR-21). The page text quoted here was replaced after this pass (see `GAP-REGISTER.md`, `READER-OPEN-GAPS`). No reader has read the new text. |
| G12-06 A repeat's agreement class is taken under the signed-prekey secret on one page and under no named secret on the other | STILL OPEN | `session-establishment.md`, Receiving the initial message: "in the same X25519 agreement class, under the responder's signed-prekey secret, as ..."; `session-persistence.md`, Session, Semantic rules: "by the responder's successful X25519 agreement class". Both unchanged. SE-08 shows the verdict does not depend on the choice. |
| G12-07 Three statements about the prekey store still speak of four versions or of v4 as current | STILL OPEN | `session-persistence.md`, Prekey store, Semantic rules: "they apply to all four versions" (the page reads five); "`signed_prekey_sig` begins at offset 69 of a v4 store"; and, in the paragraph on stores written before the signature rule, "the same v4 bytes". `tacenta-test-vectors/README.md`, The prekey store's state: "write back as current v4", "exact stored bytes for accepted v4 vectors", "the required v4 upgrade on write-back". All unchanged; every accepted current fixture begins `0x05`. |

---

## 2. New gaps

### G13-01 A sentence in the prekey store's sixth rule still puts `p - 1` before the signature rule, where the fifth rule now refuses it first (AMBIGUOUS)

- **Where:** `session-persistence.md`, Prekey store, Semantic rules:
  - the fifth rule: "**`identity_public` is an identity key** ... A store that
    fails this rule is refused as malformed, before any signature is checked";
  - the sixth rule's last sentence: "This rule intentionally narrows the
    canonical `identity_public` set accepted by the previous rule: `p - 1` is
    below p and is therefore canonical as a curve public key, but no signature
    verifies under it because signature verification refuses that value before
    converting the Montgomery key to an Edwards point";
  - the paragraph before the list: "The rules are the identifier namespace, the
    record's shape, the identity key's encoding and what the stored signatures
    authenticate";
  - `identities-and-devices.md`, Accepting a signed statement, check 6, whose
    first bullet lists u = `p - 1` among the values the identity-key rule
    refuses.
- **Problem:** the sixth rule's sentence was written when the previous rule was
  "canonical", which accepts `p - 1`. The previous rule is now the identity-key
  rule, which refuses `p - 1` (check 6, "`u` is not p − 1"), so the set the
  signature rule "narrows" no longer contains it. Read literally, a store whose
  `identity_public` is `p - 1` reaches the signature rule and is refused as
  `incoherent`; read with the fifth rule, it is refused as `malformed` before
  any signature is checked. The introductory paragraph also still describes the
  rule as an encoding rule. The rows the vectors add use u = 0, u = 2 and a key
  of mixed order, so no vector decides between the two readings for `p - 1`.
- **Resolution:** the reader refuses `p - 1` as `malformed`, by the fifth rule;
  the fifth rule is explicit about its place, and the key is a value the
  identity-key rule names. SK-08, which read the other way in pass 7 (`p - 1`
  keeps the fifth rule and breaks the sixth, G7-05), was rewritten. F13-34
  shows that the order matters and that the vectors pin it for the keys they
  use.

### G13-02 "A key that is not canonical is still a decode failure" is stated for every boundary that reads bytes; the stored session refuses one as inconsistent (AMBIGUOUS)

- **Where:** `identities-and-devices.md`, Identity keys, A refusal: "Where a
  boundary reads a key from bytes, a key that is not canonical is still a decode
  failure, and the canonical rule is applied first." Against
  `session-persistence.md`, Session, Semantic rules: `our_identity_public` and
  `peer_identity_public` are "each the canonical encoding of a curve public
  key", refused "as inconsistent", and Stored curve public keys, "Refused as
  inconsistent, by the session's rules above". And `error-handling.md`: "A key
  that is not canonical is still a decode failure."
- **Problem:** a stored session reads its identity keys from bytes, and a
  non-canonical one is refused as `inconsistent`, which Rejection distinguishes
  from the short-or-malformed kind a decode failure would be. The prekey store
  gives `malformed`. Taken at its word, the sentence in Identity keys is false
  of the session reader. The vector `peer-identity-not-canonical` decides it
  (`inconsistent`), and nothing in the sentence limits it to the wire's
  decoders, which are the boundaries message-format.md's Curve public keys
  section describes.
- **Resolution:** the sentence is read as being about the wire's boundaries (a
  bundle and an initial message), where `wire.decode_bundle` and
  `wire.decode_initial` refuse a re-spelled key as a decode failure; the stored
  readers keep their own kinds. IK-14 holds the wire reading.

### G13-03 The refusal for a non-canonical key handed to the rule alone is named only in the vectors' README and schema (MINOR)

- **Where:** `identities-and-devices.md`, Accepting a signed statement, check 6
  ("a canonical curve public key ... whose u-coordinate belongs to ...") and
  Identity keys ("A key that fails the rule is refused ... called *invalid
  identity key*"); `tacenta-test-vectors/README.md`, The identity keys, and
  `schema/vector.schema.json` (`refusal`): a non-canonical spelling given to
  the predicate is `invalid-identity-key`.
- **Problem:** the text says a non-canonical key read from bytes is a decode
  failure and that the rule refuses a key that fails it, and canonical is part
  of the rule (check 6). A non-canonical key that no boundary read from bytes,
  such as one in the table `identity-key.json` offers or one an inventory
  statement carries as an opaque field, therefore fails the rule and is an
  invalid identity key. That is derivable, but only the README and the schema
  say so, and they say it for the table alone.
- **Resolution:** `is_identity_key` includes the canonical test, so the
  predicate refuses the 7 non-canonical rows of `identity-key.json` as
  `invalid-identity-key`; `admit_identity_key(read_from_bytes=False)` does the
  same (IK-14).

### G13-04 The position of the encapsulation-key validity check among the bundle's checks, and whether a random value is drawn before it, is not stated (MINOR)

- **Where:** `session-establishment.md`, Primitives, ML-KEM-1024, Validating
  the encapsulation key: "Before encapsulating, `PQKEM-ENC(PK)` applies FIPS 203
  section 7.2's input checks ... Alice refuses a bundle whose key fails either
  check. She has then computed no agreement and sent nothing." Sending the
  initial message: the identity check comes "before she verifies either
  signature, draws a random value or encapsulates", and "She then generates
  `EKA`, encapsulates ... and computes".
- **Problem:** the check is part of `PQKEM-ENC`, which follows the generation of
  `EKA`. For a bundle with an invalid identity key the page says nothing is
  drawn. For a bundle with an invalid KEM key it says only that no agreement is
  computed and nothing sent, so whether `EKA` has been drawn, and whether the
  identity check or the KEM check reports a bundle that fails both, is left
  open. The two refusals differ only in kind and in the draw.
- **Resolution:** the reader validates the KEM key after the signatures and
  before it draws anything, so it draws nothing for either refusal. Control
  C13-02 (KEM check first) fails no vector and no case.

### G13-05 The refusal kind for a repeated initial message whose `identity` is not an identity key is not stated (MINOR)

- **Where:** `identities-and-devices.md`, Identity keys, Where the rule applies:
  "a responder, to the `identity` of an initial message, before any private key
  is used on the message". `session-establishment.md`, Receiving the initial
  message, on an initial message that arrives on an existing session: the
  session "accepts it only if ... the message's `identity` field equals, byte
  for byte, `EncodeEC` of the peer's identity key the session holds ...
  Otherwise, and always on an initiator's session, it refuses the message
  (`NotARepeatedInitial`)".
- **Problem:** a repeat whose `identity` is a canonical key that fails the rule
  is refused by both sentences: it does not equal the session's peer identity
  key (an identity key), and it is not an identity key. The kind, `NotARepeatedInitial`
  or invalid identity key, is not said, nor which check comes first.
  Nothing changes either way.
- **Resolution:** the reader reports `NotARepeatedInitial` (IK-13): the session
  never sees the identity check, which belongs to establishing a session. No
  vector reaches it.

### G13-06 The two scans are named and not specified (MINOR)

- **Where:** `session-persistence.md`, Session, Semantic rules, the paragraph on
  a session or store written before the identity-key rule existed: "A caller
  that means to adopt a reader with the rule can find the states it will refuse
  beforehand by reading the identity keys of every stored state and applying the
  rule to each; `tacenta-core` provides this as `scan_stored_session_identities`
  and `scan_stored_prekey_identity`."
- **Problem:** the operations are named, not stated. Not said: what a scan
  returns; whether it reads a state the reader would refuse for another reason
  (a caller who means to adopt the rule needs it to); what it does with a buffer
  too short to reach the keys or with an unknown version; whether it applies the
  canonical test as well; whether it is part of the specification's requirements
  at all or only a pointer to `tacenta-core`'s API (error-handling.md leaves
  API shapes out of the specification).
- **Resolution:** the reader's scans return the (field, key) pairs the rule
  refuses, read from the framing of the state without applying its other rules,
  refuse an unknown version, and raise the format's short-or-malformed error
  when the keys cannot be reached (IK-12). None of this is in the text.

### G13-07 "Which she checks first" and "after the presence, pinning and canonical checks" (MINOR)

- **Where:** `session-establishment.md`, Sending the initial message: "She
  verifies them only under an `IKB` that is an identity key, which she checks
  first (below)"; and `authentication.md`, REQ-AUTH-01: "under an identity key
  ... which she checks first". Against Sending the initial message, two
  paragraphs later: "She makes that check after the presence, pinning and
  canonical checks above and before she verifies either signature".
- **Problem:** read literally the two say different things about what comes
  first. The context makes "first" mean before the signatures, and the later
  sentence is explicit. A bundle that fails the identity check and one of the
  other three is reported as the other check's refusal.
- **Resolution:** the reader follows the later sentence (IK-06). F13-29 (the
  identity check before the other three) is caught by derived cases only.

### G13-08 `u = p - 1` is a "low-order value" and also a u no point of the curve has (MINOR)

- **Where:** `identities-and-devices.md`, Accepting a signed statement, check 6:
  the first bullet lists "the u-coordinates 0, 1 and p − 1, and the two of order
  eight" as "the five low-order values" and says "X25519 with any of them yields
  the all-zero string for every private key"; the second bullet is "a
  u-coordinate that no point of the curve has". The vectors call `p - 1` the
  second (`identity-key.json` `u-p-minus-1`: "no point of the curve has this u",
  and the same wording in the bundle and initial-message rows).
- **Problem:** both are true. X25519 with u = `p - 1` gives the all-zero string
  for every private key tried (30), and the Montgomery equation has no point at
  u = −1 (`u³ + 486662u² + u = 486660` is a non-residue; the reader checked
  both). The page's first step ("u is not p − 1") treats it separately, since
  the Edwards map divides by zero there. No verdict depends on the
  classification.
- **Resolution:** none needed; the reader accepts either class for `p - 1` in
  `work/check_new_vectors13.py`.

### G13-09 `error-handling.md` lists the stored kinds without `incoherent` (MINOR)

- **Where:** `error-handling.md`, What is required: "A stored state's refusal
  says which kind it is, to the extent session-persistence.md's Rejection
  section names kinds: wrong version, short or malformed, non-canonical, and,
  for a session, inconsistent." Against `session-persistence.md`, Rejection: "the
  prekey store calls it 'incoherent' and gives it for its signature rule alone".
- **Problem:** the list has four kinds and Rejection names five. The same
  paragraph goes on to say a stored key that is not an identity key is refused
  "as malformed in a prekey store", so the omission is not about identity keys,
  but a reader taking the list as complete would fold `incoherent` into
  `malformed`, which the vector `signed-prekey-signature-does-not-verify`
  refuses.
- **Resolution:** the reader keeps five kinds.

### G13-10 The XEdDSA vectors and the manifest still describe step 3 as "A is not of small order" and number the steps as rules (MINOR)

- **Where:** `vectors/primitives/xeddsa.json`: the file's `source` ("its rule 3
  (A is not of small order)", "its rule 6 (R is not of small order)") and the
  comments of the four `reject-small-order-A-rule-3-only-*` vectors ("only rule
  3 (A is not of small order) refuses it"); `tacenta-test-vectors/README.md`,
  Regenerating ("so rule 3 (`A` is ..."); `conformance-manifest.md`, the XEdDSA
  row ("which only rule 3 of identities-and-devices.md, Verifying a signature,
  refuses"). Against `identities-and-devices.md`, Verifying a signature: the
  items are steps, and step 3 is "`A` is a point of the prime-order subgroup:
  `qA` is the identity".
- **Problem:** stale wording after the step changed. Every verdict is the same,
  since a point of small order also fails `qA`. The three new
  `reject-mixed-order-A-*` rows say "Step 3", the older comments say "rule 3".
- **Resolution:** none needed for a verdict.

### G13-11 The schema names one of the three identity files as carrying `invalid-identity-key` (MINOR)

- **Where:** `schema/vector.schema.json`, `result` ("in vectors/identity/identity-key.json, with the refusal invalid-identity-key") and `refusal` ("invalid-identity-key is carried by every invalid vector of vectors/identity/identity-key.json"). Against `tacenta-test-vectors/README.md`,
  The identity keys: "An invalid vector in these three files carries the
  `refusal` `invalid-identity-key`".
- **Problem:** the schema's description of when the value is carried covers one
  file; the other two (`bundle-admission.json`, 9 invalid rows;
  `initial-message-admission.json`, 10) carry it too. The enum allows it.
- **Resolution:** the reader follows the README.

### G13-12 What a responder does when its identity is not the store's identity is not stated (MINOR)

- **Where:** `session-establishment.md`, Receiving the initial message, and
  `session-persistence.md`, Prekey store ("The identity's own secret is not
  here; `Identity` is separate"), Semantic rules ("every operation that signs a
  prekey signs under the identity whose public key is `identity_public`, and an
  implementation whose API lets a caller supply some other identity refuses
  it"). The vector `initial-message-admission.json` takes `bob_identity_secret`
  and `prekey_store` as separate inputs.
- **Problem:** the persistence page requires the signing operations to refuse a
  foreign identity, and says nothing of the operation that receives: a responder
  handed an identity whose public key is not the store's `identity_public` (its
  DH2 would use one identity and its bundles name another). No verdict of the
  vector depends on it, since the honest row has them equal and a refusal is
  reached before the identity secret is used.
- **Resolution:** the reader's handler checks that the vector's identity secret
  is the store's identity (the valid row) and specifies nothing for a mismatch.

### G13-13 Two different revoked bindings that share a `device_id` (MINOR)

- **Where:** `identities-and-devices.md`, Accepting a signed statement, check 5:
  "No two entries of `active` share a `device_id`. An active and a revoked
  binding may share one." `conformance-manifest.md`, Hosted device-inventory
  statements, Not covered: "two different revoked bindings with one `device_id`,
  which check 5 (over `active` only) leaves accepted and the page does not
  state."
- **Problem:** by omission they are accepted; the page states neither that they
  are nor that they are not. The manifest records the omission.
- **Resolution:** accepted (IV-24). The reader can be told nothing more.

**Answered in the specification after the pass.** The text was changed for
G13-01 (the sixth rule's last sentence and the introductory paragraph),
G13-02 (the sentence in Identity keys and its counterpart in `error-handling.md`),
G13-05 (a repeated initial message that names a key the rule refuses is
`NotARepeatedInitial`), G13-06 (`session-persistence.md` no longer names the two
scan operations), G13-07 ("which she checks first" now says before either
signature) and G13-09 (`error-handling.md` lists `incoherent`). No fresh pass
read the new sentences; the reader's cases and vectors were rerun and still
agree, and the readings recorded above are the ones the pass took from the
earlier text.

**No BLOCKING gap.** Every refusal the identity vectors name could be decided
from the text.

**Where the text was not enough to decide a vector's verdict:** none for a
refusal. The one verdict the reader does not reach is the valid
`initial-message-admission.json` row, whose `output` is a plaintext: recovering
it needs ML-KEM-1024 decapsulation and the ratchet's receive, which this reader
does not implement (section 4). That is a limit of the reader, not of the text,
which cites FIPS 203 for the first. Where the text disagrees with itself, a
vector decides (G13-02), or no vector reaches the point (G13-01).

**Disagreements between a vector and the text: none.** The 60 identity rows
(the valid initial-message row as far as section 4 says), the 9 persisted rows
and the 3 XEdDSA rows all agree with the reading this reader took from the
pages.

---

## 3. Vector gaps: specified, but no vector pins it

### The new vectors pass for the stated reasons

`work/check_new_vectors13.py` (231 checks, no problems):

- **`identity-key.json`.** Each of the 33 invalid keys is of the class its
  comment names, by the reader's own arithmetic: 7 non-canonical, 4 low-order
  (0, 1, and the two of order eight), 5 off the curve (`p - 1`, 2, 3, 5, 12) and
  17 mixed-torsion sums, each of which is the base key's point plus a torsion
  point of the order the comment gives, for `honest-h1`, `honest-h3` and
  `9*B`. The six valid keys are canonical keys of the subgroup, and the three
  from fixed secrets and the two of RFC 7748, section 6.1, are the X25519 public
  keys of those secrets.
- **`bundle-admission.json`.** The three `identity-mixed-order-*-signed-under-it`
  rows carry both signatures verifying under the key by steps 1, 2, 4, 5 and 6
  (step 3 as it read before), with the key the honest identity's point plus a
  torsion point of order 8, 4 and 2 and every other field the honest bundle's;
  the full verifier refuses them at step 3. The `original-signatures` row
  carries the honest signatures.
- **`initial-message-admission.json`.** Every refused row is the honest message
  with its `identity` replaced (and, for the last two, one other defect), on the
  honest prekey store. Put back the honest identity and the reader's outcome is
  what the row's name says it hides: the message reaches decapsulation, except
  `before-unknown-one-time-identifier` (unknown identifier) and
  `before-wrong-length-ciphertext` (ciphertext refused). The mixed-order rows'
  keys are the sender's identity plus a torsion point of the order named.
- **`xeddsa.json`.** The three `reject-mixed-order-A-*` rows pass steps 1, 2, 4,
  5 and 6 and are refused by step 3 alone. The comment on each begins "Revision
  1 accepts" or "Revision 1 rejects"; a transcription of revision 1's pseudocode
  (in the script) gives that verdict on each: accepted for the order 8 and order
  4 keys, refused for the order 2 key, whose signature carries the sign bit that
  revision 1 reads as an out-of-range `s`.
- **The nine persisted rows** are refused for the identity-key rule
  ("identity key" in the reason) and by no other rule, with the kinds the
  README names (`inconsistent` for the session, `short-or-malformed` for the
  prekey store).

### New in this pass: rules the text states that no vector pins

Fault numbers refer to section 5. Where a fault is caught by a derived case and
by no vector, no vector pins the rule.

- **The bundle's other keys are not held to the identity-key rule.** A signed
  prekey or a one-time curve prekey of mixed order is admitted; a low-order one
  is refused by the contributory check, after the random values are drawn
  (F13-24, F13-25; IK-07). The `identity-mixed-order-*` bundle rows change
  `identity_key` only.
- **The order among the initiator's checks.** The identity check follows the
  presence, pinning and canonical checks (F13-29; IK-06). No row pins a
  pinned identity, a presence disagreement or a non-canonical identity at the
  admission boundary. The order against the random draw and the agreements is
  not observable from bytes: the `signed-under-it` rows pin the order against
  the signatures, and the reader's handler asserts the rest from the text
  (F13-30 is caught by the vector file through that assertion, not through
  what the row records).
- **Pinning an identity that itself fails the rule** (IK-06).
- **The responder's checks around the identity check.** An unknown signed or KEM
  prekey identifier behind a bad identity is refused as unknown (F13-33); a
  retired signed prekey is found (F13-41); a wrong-length ciphertext or an
  unknown one-time identifier behind a good identity is refused for its own
  reason (F13-42, F13-43). Each refused row has a good identity restored to
  nothing, so none of these is pinned.
- **The responder's ephemeral is not held to the rule** (F13-26; IK-09), nor
  are a stored session's `pending_initial` ephemeral and `established_ephemeral`
  (F13-27; IK-10).
- **The prekey store rule in versions 1 to 4** (F13-38; IK-11). Every identity
  row of the stored formats is version 5.
- **`p - 1` as a stored identity key** (G13-01). The nine persisted rows use
  mixed order, u = 0 and u = 2.
- **The scans and "refused, not deleted, not repaired"** (F13-39, F13-40;
  IK-12, IK-16).
- **A repeated initial message with an `identity` that fails the rule**
  (F13-45 is caught by IK-13 alone; G13-05 for its kind).
- **Application signatures under a key that fails the rule.** No vector; the
  refusal is also made by the verifier's own step 3, so dropping the early rule
  is equivalent (F13-19, not caught), and answering by raising is caught by
  IK-03 only (F13-21).
- **A key read from bytes that is not canonical stays a decode failure**
  (F13-08; IK-14). The admission files have no such row; the decoder files pin
  the decoders.
- **An issuer key of mixed order** (Accepting a signed statement, check 3, with
  step 3): a signature that satisfies the equation under it is an authentication
  failure. The acceptance file has issuer keys 0, `p - 1` and non-canonical,
  and none of mixed order. IK-17.
- **An initial message that is otherwise well formed for the responder and
  names a key the rule refuses.** The manifest says no vector pins it. This
  reader cannot build one either (no KEM); its responder refuses before
  authentication by construction.
- **`initiator_identity_secret`** (bundle admission) and **`bob_identity_secret`**
  (initial-message admission) decide no refusal. They matter only to the valid
  rows (G13-12).
- **Two different revoked bindings with one `device_id`** (G13-13; IV-24).
- **The rule's reach beyond the first entry of an inventory list** (the manifest
  records four classes and names three reader edits that pass every vector file
  and, until this pass, every derived case). F13-46, F13-47 and F13-48 were
  missed on the run that first tried them, and are now caught by IV-23;
  F13-51 to F13-53 (sort order, check 5, check 6 past the first entries) were
  caught by IV-02, IV-16 and IV-15 already.

### `GAPS-12.md`'s vector gaps, re-assessed

| Vector gap | Status | Note |
|---|---|---|
| The issuer's duty (encoding rules, check 5 and check 6 before signing) | STILL OPEN | The manifest, Not covered: "the issuer's duty to check before signing". IV-07. |
| Recording a generation only after check 7, and the atomic step | STILL OPEN | The manifest, Not covered: "a verifier's recording of a generation after acceptance, and the atomic step that evaluates its freshness rule again". IV-08, IV-09 (rewritten). |
| A statement built in memory | STILL OPEN | The manifest, Not covered. IV-05, IV-07. |
| The unsigned decoder's re-encode refusal | STILL OPEN | The manifest, Not covered: "no input reaches it when every rule before it has been applied". |
| An exact binding across the predecessor | **CLOSED** | `accepted-replacement-with-the-retired-bindings-own-device-id-and-key`: the replacement has the retired binding's own device id and key and differs in its predecessor, and is accepted. |
| Check 6's own order | STILL OPEN | The manifest, Not covered: "the order inside check 6". |
| "A replacement identical to what it replaces" | **CLOSED** | The same vector. |
| The big-endian order across a byte boundary | STILL OPEN | The manifest, Not covered: no list holds two entries whose order differs between the two byte orders. IV-02. |
| The page's verifier on the accepting side of the sign bit | **CLOSED** | `accepted-signature-with-the-sign-bit-left-set`. IV-19. |
| The statement policy is given the whole statement as verified | STILL OPEN | The manifest, Not covered. IV-17. |

`GAPS-7.md`'s vector gaps, as `GAPS-12.md` left them:

| Vector gap | Status | Note |
|---|---|---|
| The prekey store's signature rule and `incoherent` | NARROWED (as before) | Only `signed-prekey-signature-does-not-verify` pins it. `kem_sig`, the one-time KEM signatures and the retired pair's are pinned by no refusal vector. |
| The session's, the prekey store's and the initiator's stored-key rules | NARROWED (further) | `own-identity-*` now pins `our_identity_public` (the identity half of the rule), where pass 12 recorded it unpinned. `pending_initial`'s `ephemeral_public` and the initiator's own bundle check (the canonical, pinning and presence checks) are still pinned by no row of the persisted files or of `bundle-admission.json`. |
| The record's pre-sizing ceiling; `non-canonical`; the Braid's `key_pair` content clause | STILL OPEN | Unchanged. |
| The other rows of the earlier table | as in `GAPS-12.md` | Not re-examined vector by vector. |

---

## 4. Not attempted, and why

Unchanged from `GAPS-12.md` and `GAPS-7.md`: ML-KEM-1024 and its incremental
split (the Braid runs over `kem_double.py`); the end-to-end `Session`; prekey
store operations other than the two rotations; group messaging beyond the two
commitments and the inventory statement; full JSON-Schema validation; the
evidence the requirements cite.

**What was not checked for the one identity vector that is skipped.**
`identity/initial-message-admission.json` `honest-initial-message` is on the
skip allowlist. Its `output` is the plaintext the responder recovers. What the
reader checks before it skips, and fails on if any of it disagrees:

- the prekey store reads as version 5 (every stored signature verifies under
  `identity_public`, which is an identity key) and re-encodes to its bytes;
- the responder's identity secret is that store's identity;
- the message decodes, its `identity` is an identity key, the store holds the
  signed prekey, the KEM prekey and the one-time curve prekey it names, and its
  KEM ciphertext is 1,568 bytes;
- the four Diffie-Hellman outputs, computed from the store's secrets and the
  message's keys, are contributory;
- the ratchet message inside decodes as a ratchet message;
- the store is as it was after all of this.

Not checked: `PQKEM-DEC` (ML-KEM-1024 decapsulation and its implicit
rejection), `SK`, the replay identity, the split into the two ratchets, the
first message key, the AEAD tag and decryption, and therefore the plaintext.
FIPS 203 is published and the text cites it, so this is the reader's boundary
and not a gap in the text; the earlier passes drew the same line
(`session-e2e.json`).

The initiator's side stops at the same place: the two random values are drawn
in the page's order and the four agreements computed, and `PQKEM-ENC` is not
made, so the initial message is not built.

---

## 5. Deliberate faults

53 faults and 4 controls (`work/faults13.py`, run twice, with the same result
each time), each a textual change to a fresh copy of the reader, then the full
runner. **52 were caught, 29 of them by a vector file.** Every fault that
breaks a rule this pass implemented, at every boundary the text lists, was
caught. The per-fault list, with the vectors and cases that failed, is in
`reader/README.md` and `work/faults13.txt`.

| | Tried | Caught | Caught by a vector file |
|---|---|---|---|
| An honest key refused (F13-01 to F13-04) | 4 | 4 | 4 |
| A non-canonical spelling accepted (F13-05 to F13-09) | 5 | 5 | 3 |
| The rule dropped at a boundary (F13-10 to F13-23): the bundle, the initial message, the stored session (each key), the stored prekey store, the signature verifier (three ways), application signatures (three ways), the inventory | 14 | 13 | 11 |
| The rule held to keys outside it (F13-24 to F13-27) | 4 | 4 | 0 |
| The order of checks (F13-28 to F13-34): later than the text puts it, and earlier | 7 | 7 | 5 |
| What a refusal is: kinds, the store left alone, the scans, the responder's other checks, a repeat (F13-35 to F13-45) | 11 | 11 | 4 |
| The reach of three inventory rules, past the first entry (F13-46 to F13-48, F13-51 to F13-53) | 6 | 6 | 0 |
| The wire decoders applying the rule (F13-49, F13-50) | 2 | 2 | 2 |
| **Total** | **53** | **52** | **29** |

**Not caught, one, and why:**

- **F13-19** (application signatures: the identity-key rule not applied before
  the verifier) is an equivalent change while the verifier's own step 3 holds:
  step 3 refuses every key the rule refuses, so `verify_application` says no
  either way. The text states the rule in both places. With step 3 weakened as
  well, F13-20 is caught by `xeddsa.json` and IK-02, IK-03.

**Caught, but only by a message:**

- **F13-09** (the stored session's identity fields skip the canonical test, the
  identity rule alone remaining) does not change any verdict: a non-canonical
  key fails the identity rule too, and is refused as `inconsistent` either way.
  SK-04 catches it only because it checks that the refusal's reason still says
  "canonical". It is counted as caught above; on verdicts it is equivalent.

**Caught by derived cases alone:** F13-08, F13-09, F13-21, F13-23 to F13-27,
F13-29, F13-33, F13-38 to F13-43, F13-45 to F13-48, F13-51 to F13-53, 23 in all.
These are the rules section 3 lists as pinned by no vector.

**Changes made during the run.**

- F13-46, F13-47 and F13-48 (the terminal generation range, and the rule that an
  exact binding is in one list only, applied to the first entry of a list) were
  **missed on the first run**: no case put the defective entry past the first.
  The manifest names exactly these three as passing every vector file and this
  reader's cases. IV-23 was added and catches all three.
- Before the first fault run, the store-left-alone assertion was restructured.
  It first checked a fresh copy of the store, which no responder could change;
  the responder now takes the object the caller read and the caller compares it
  after the call. F13-35 (a refusal that consumes the
  named one-time prekey) is caught by the vector file and by IK-08, IK-09 on
  that basis.
- IV-09 was rewritten for the new check 4 sentence, and its first version ran
  the interleaved statement a second time inside the atomic step; it now runs
  it once.

**Controls.** C13-01 to C13-04 change nothing, as expected: the responder
finding the KEM prekey before the signed prekey, the initiator validating the
KEM key before every other check (G13-04), the initiator checking presence
before pinning, and a stored session checking `peer_identity_public` before
`our_identity_public`. The text fixes none of these orders, and no vector or
case has an input that fails two of them.

---

## 6. Isolation

- **What was read:** this directory and nothing else.
  - `tacenta-spec/`: `protocol/identities-and-devices.md` in full;
    `protocol/session-establishment.md` in full; `protocol/session-persistence.md`
    from the Session section to the end; `protocol/error-handling.md` in full;
    `protocol/message-format.md` from Initial message to the end;
    `security-properties/authentication.md`, REQ-AUTH-01 and REQ-AUTH-11;
    `CHANGELOG.md` `[Unreleased]` (its first 140 lines); `VERSION`; and, to
    re-assess the open gaps, passages of `protocol/key-deletion.md`,
    `protocol/sparse-pq-ratchet.md`, `threat-model/adversaries.md`,
    `exclusions.md` and `assumptions.md`, `security-properties/limitations.md`
    (LIM-21) and `evidence-index-format.md`, and the top-level keys of
    `evidence-index.json`. No ADR was opened.
  - `tacenta-test-vectors/`: `README.md` (the opening, Vector layouts for the
    prekey store, the session, the identity keys and the inventory statements,
    the AEAD and Checking the vectors, and the lines mentioning identity keys or
    rules 3 and 6); `conformance-manifest.md` (Covered: identity keys, the
    inventory section, the prekey store's and the session's tables);
    `schema/vector.schema.json`; the three files under `vectors/identity/` in
    full; `vectors/primitives/xeddsa.json` in full; the ids and comments of
    `vectors/persistence/session-state.json` and `prekey-store-state.json`, with
    the identity fields of their bytes; and the ids of the four inventory files
    under `vectors/groups/`.
  - `reader/`; `GAPS-8.md`, `GAPS-9.md`, `GAPS-10.md` and `GAPS-12.md` in full;
    `SOURCE-REVISION`. `GAPS.md` and `GAPS-2.md` to `GAPS-7.md` were not
    opened.
- **Outside this directory.** Nothing outside it was read, listed or searched,
  with two facts to record:
  - the first command of the pass listed this directory (`ls -la`), which
    prints the standard `.` and `..` entries; the `..` line showed that entry's
    permissions, owner, size and date, and nothing inside it;
  - the output of one early command, a print of `reader/README.md`, was too long
    to display, and a copy of it was saved outside this directory. That copy was
    not opened, and nothing from it was used. Every later long output was
    written to a file under `work/` and read from there.
  - **Reads attempted outside this directory: none.**
- **Names treated as text.** The pages, the vectors README and the manifest name
  implementation files, tests, tooling and theorems (a runner test file, the
  model's identity-key module, the vector checker, the two stored-identity scan
  functions, `establish_responder`, `Session::peer_identity`, one named test, and
  the evidence index's paths). None was looked for. No vector generator was
  read.
- **What was written:** only inside this directory:
  - `reader/`: the new `tacenta_reader/admission.py` and `cases_idkeys.py`;
    changes to `tacenta_reader/curve25519.py`, `wire.py`, `identity.py`,
    `persistence.py`, `inventory.py` and `__init__.py`; `cases_stored.py` (SK-04
    and SK-08), `cases_inventory.py` (IV-09, IV-23, IV-24 and the recording
    policy they use); `run.py` (three handlers, one allowlist label, one case
    module); `README.md`;
  - `GAPS-13.md`;
  - `work/`: `baseline.txt`, run outputs, `check_new_vectors13.py` and its output,
    `faults13.py`, `faults13.txt`, `faults13-second-run.txt`, `faults13.json`,
    `faults13-table.md`, `final-run.txt`, and `reader-baseline/`, a copy of the
    reader as found (it is not runnable from there; its vectors path does not
    resolve).

  The per-fault copies were made under `work/faults13/`, each reaching the
  vectors through a symbolic link inside this directory, and were removed after
  each run. Python wrote its usual `__pycache__` directories inside `reader/`.
- **What was not consulted:** no implementation (tacenta-core, tacenta-model,
  tacenta-proofs, the Rust runner, libcrux, libsignal or anything derived from
  them), no git history, no vector generator, no other scratch files, and no web
  search. RFC 7748 (section 5, and the section 6.1 public keys, in the check
  script only), RFC 8032 section 5.1, the XEdDSA document's revision 1
  pseudocode (for the transcription in the check script), the Curve25519
  Montgomery equation and Euler's criterion were used from knowledge. Nothing was
  fetched. Only the Python standard library was used.
- **Unrelated notes, not used.** An index of notes from other work, and a list
  of further material, were available alongside the directory. None of it was
  opened, and nothing in it was used for any reading or decision here.
