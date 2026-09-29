# Gap report, twelfth pass: the hosted device-inventory statements

The clean-room reader (`reader/`) was extended from `tacenta-spec` and
`tacenta-test-vectors` alone, against the tree as found in this directory:

- `SOURCE-REVISION` `1cac363f11305d675844af590a0840774a87656f`;
- `VERSION` `0.2.0`;
- everything under `CHANGELOG.md` `[Unreleased]`. Its first entry begins
  "`identities-and-devices.md`, hosted device-inventory statements: state what a
  verifier must check before it relies on a signed statement, as seven ordered
  checks".

The last full clean-room pass, the seventh, read
`5ae44427d17d0e8bfa1d314780305690000ee770`. Passes 8 to 10 are maintenance
records that re-ran this reader. This pass is numbered 12 because another
branch may use 11.

Severity, as in the earlier reports:

- **BLOCKING**: cannot be implemented from the tree without guessing.
- **AMBIGUOUS**: more than one reading; a vector decided it, or nothing did.
- **MINOR**: wording, pointers, or a value findable only in the wrong place.

A hypothesis confirmed by a vector is still a gap.

**Baseline** (`python3 reader/run.py`, before any change): 675 PASS, 3 FAIL,
1 SKIP.

| | PASS | FAIL | SKIP |
|---|---|---|---|
| Vectors (42 files) | 455 | 3 | 1 |
| Derived cases (12 modules) | 220 | 0 | 0 |
| **Total** | **675** | **3** | **1** |

The three failures were one per file for the three inventory files the runner
did not know (`inventory-acceptance-v1.json`,
`inventory-binding-commitments-v1.json`, `inventory-decode-refusals-v1.json`),
each reported as "file does not have the schema's top-level shape". The one
skip is `session-establishment/session-e2e.json`, as in pass 10:
it needs real ML-KEM-1024 and the end-to-end session, which this reader does
not implement. `inventory-statements-v1.json` already passed its 27 cases,
through a handler in `run.py` that no pass record describes (section 4).

**Final run:**

| | PASS | FAIL | SKIP |
|---|---|---|---|
| Vectors (42 files) | 665 | 0 | 1 |
| Derived cases (13 modules) | 244 | 0 | 0 |
| **Total** | **909** | **0** | **1** |

All 237 inventory vectors -- 27 statements, 54 decode refusals, 10 binding
commitments and 146 acceptance cases -- passed on the first run of the new
code. An acceptance case passes only when the reader's `refusal` and its
`hook_calls` both equal the vector's; the issuer signature is verified by the
reader's own XEdDSA, under the key the scripted policy resolves, over the input
the page gives. `work/check_new_vectors12.py` (384 checks, no problems)
confirms that they pass for the reasons the text gives (section 3).

**What changed in the reader:**

- **`tacenta_reader/inventory.py`, new.** The unsigned preimage, `DeviceBinding`
  and `Revocation`, every encoding rule, applied alike to bytes and to a
  statement built in memory; `binding_commitment`; the signed statement and
  its signing input; check 6's three-step identity-key test; the seven checks
  in order, with the verifier's issuer binding, freshness rule, binding policy
  and statement policy supplied by the caller; the issuer's duty in
  `sign_statement`; three refusal kinds (decode failure, authentication
  failure, refusal of a well-formed authentic statement), each carrying the
  name of the check that made it.
- **`tacenta_reader/inventory_vectors.py`, new.** The four closed layouts of
  the vectors README, "The hosted-inventory statements", and the scripted
  policy that section describes, recording the hook-call strings.
- **`cases_inventory.py`, new.** 22 cases, IV-01 to IV-22. IV-02 was extended
  during the fault run, when F12-07 was missed (section 5).
- **`cases_ratchet.py`: CR-21**, and **`cases_curvekeys.py`: SE-08**, for two
  sentences outside the inventory section that changed since pass 7 (G12-05,
  G12-06).
- **`run.py`:** one import, the four schemas registered in `GROUP_SCHEMAS`, and
  `cases_inventory` in `CASE_MODULES`. The earlier `h_inventory_statement`
  and its helpers are left in place, unregistered, so that the diff to
  `run.py` is the registration alone.

No existing protocol module changed.

---

## 1. The earlier gaps

Counts for the gaps open after pass 7 as pass 8 left them (G5-03 to G5-10 and
G7-01 to G7-06; G4-01, G6-01, G6-03 and G6-05 were closed by pass 8): **8
CLOSED, 6 STILL OPEN, 0 NARROWED**. G5-07 stays at the narrowed extent pass 7
recorded.

The gaps recorded as closed before (G-01 to G-28, G2-01 to G2-12, G3-01 to
G3-08, G4-01 to G4-04, G5-01, G5-02, G6-01 to G6-05) were not re-read one by
one; their cases and vectors all pass in the final run, and nothing this pass
read reopens any of them. No earlier gap was judged wrong.

| Gap | Status | Citation, and what changed in the reader |
|---|---|---|
| G5-03 "Shorter than the fixed fields of the version the reader reads" when there is no one such version | **CLOSED** | session-persistence.md, Rejection: "**A short buffer with an unknown version may be refused as either.** A non-empty buffer ... that is too short for every version that reader recognises, and whose first byte is also not one of those versions ... a reader may refuse that buffer as short or malformed or as a wrong version". "That freedom is only for this overlap. A recognised version byte followed by too few bytes is short or malformed. An unknown version byte on a buffer long enough for any recognised version's fixed fields is a wrong version", and a table for all six formats. The overlap is now defined against every recognised version, so the prekey store's several fixed lengths no longer leave a buffer unassigned: "long enough for any recognised version's fixed fields" can only mean *some*, since a buffer outside the overlap gets one kind and, with an unknown version byte, the only kind left is wrong version. RJ-01 holds the table as the page now states it, citing that paragraph, and passes (section 4 on how it came to cite it). |
| G5-04 The work a forged message costs, stated three ways | STILL OPEN | `threat-model/adversaries.md` ADV-01 ("make a receiver derive up to `MAX_SKIP` keys before it refuses them") and ADV-06, and `exclusions.md` ("A skip is refused beyond `MAX_SKIP` before any key is derived"), unchanged. The reader follows the protocol pages (CR-08). |
| G5-05 LIM-21: "until it is established again" | STILL OPEN | `security-properties/limitations.md`, LIM-21, unchanged: "The session then refuses to encrypt or decrypt until it is established again." `Failed` stays terminal in the reader. |
| G5-06 ASM-13 and ASM-19 are "relied on by every requirement" | STILL OPEN | `threat-model/assumptions.md`: ASM-13 "every requirement, for the adversary it holds against"; ASM-19 "every requirement, as a statement about `tacenta-core`; in particular ...", unchanged. |
| G5-07 The evidence the requirements cite is outside the specification | STILL OPEN (at pass 7's narrowed extent) | ADR-0006 point 7 is unchanged. The tree now carries `security-properties/evidence-index.json` and `evidence-index-format.md`, a machine-readable list of the citations; the format page says it is "evidence metadata, not the evidence itself". The theorems, tests and `CLAIMS.md` sections it names are still outside this tree. Nothing was looked for. |
| G5-08 The sparse ratchet's retention window: saturating on one page, not on the other | STILL OPEN | sparse-pq-ratchet.md, Retiring old epochs, still "every epoch `e` with `E < e + EPOCHS_KEPT`"; session-persistence.md still "the sum saturating". Unobservable. |
| G5-09 The classical ratchet at `Nr = u32::MAX`, for a message numbered below it | **CLOSED** | ratchet.md, Sending and receiving: "If `Nr` is already `u32::MAX` and the same-chain message's number is below it, the message meets both the stale-message rule and the counter-exhaustion rule. This page fixes no order between those two checks. ... Either refusal is conforming, and accepting the message is not. The freedom is only for that overlap". CR-20 accepts either, citing that sentence, and passes (section 4). |
| G5-10 REQ-AUTH-11 does not cite the rule that refuses a replay onto a chain the receiver has left | STILL OPEN | `security-properties/authentication.md`, REQ-AUTH-11, unchanged: the same three bullets, "Rests on: ASM-19". TM-02 still finds the sparse half doing the work. |
| G7-01 The two new vector files have no layout section | **CLOSED** | `tacenta-test-vectors/README.md`, "The prekey store's state" and "The session's state": each lists its `fields` exactly, says the lists are reported as counts and a retired key by its presence byte, and defines `braid_tag`, `braid_epoch` ("the Braid half's epoch") and `sparse_epoch` ("the sparse ratchet half's epoch inside the stored Triple Ratchet state"). The same section now says "write back as current v4", which is G12-07. |
| G7-02 The vectors README's Status paragraph is stale | **CLOSED** | README, Status: "The session's and the prekey store's persisted formats have vectors too"; "In every persistence file but the two erasure coders', an invalid vector also names its `refusal`." |
| G7-03 The sixth rule does not say which signature scheme | **CLOSED** | session-persistence.md, Prekey store, Semantic rules: "**Verified as a prekey signature, not an application one** (identities-and-devices.md, Verifying a signature): the message is the tagged key as written above, with no label in front of it." |
| G7-04 The obligation is stated over "every operation that signs a prekey", and only the rotations are said to refuse | **CLOSED** | Same section: "Four operations sign: `create_prekeys`, ...; `replenish`, which signs each KEM prekey it adds; and the two rotations ... `create_prekeys` is the one that cannot be handed a foreign identity, because it is the identity that builds the store; the other three can be, and refuse." key-deletion.md's paragraph on `replenish` still says nothing of an identity; the rule is stated once, where the obligation is. `replenish` is still not modelled here. |
| G7-05 `identity_public = p - 1` keeps the fifth rule and can never keep the sixth | **CLOSED** | Same section: "This rule intentionally narrows the canonical `identity_public` set accepted by the previous rule: `p - 1` is below p and is therefore canonical ..., but no signature verifies under it". SK-08 already states it. |
| G7-06 `sparse-epoch-does-not-follow-the-braid` moves the Braid's epoch | **CLOSED** | The vector's comment now reads "the Braid epoch moved outside the relation its state tag allows"; the sparse side is exercised by the new `tag-six-with-current-sparse-epoch-refused` and `tag-seven-with-previous-sparse-epoch-refused`. |

---

## 2. New gaps

### G12-01 The scripted policy's two answers are stated as necessary conditions or over a unique entry (MINOR)

- **Where:** `tacenta-test-vectors/README.md`, "The hosted-inventory statements",
  `inventory-acceptance-v1.json`:
  - "A generation is current for an account only if `fresh` lists that pair."
  - "A binding is refused when `refuse_every_binding` is true, or when it is
    the entry of the same identity as `refuse_binding.identity_hex` in the list
    `refuse_binding.status` ... names."
- **Problem:**
  - "Only if" gives a necessary condition. Whether a listed pair is then
    current, which every accepted case needs, is not said.
  - "The entry of the same identity" presumes one entry per identity in the
    named list. The format accepts one key on two bindings (Accepting a signed
    statement, the unchecked properties), and `accepted-one-key-on-two-devices`
    is such a statement, so the policy the README describes is not defined for
    every statement the file could carry. No current case combines a
    `refuse_binding` with a repeated identity in the list it names.
- **Resolution:** "current exactly when listed"; every entry of that identity
  in that list is refused, so the first one stops check 7. All 146 cases
  agree. A confirmed hypothesis is still a gap.

### G12-02 Check 3 does not say which XEdDSA verifier, or what form the resolved key takes (AMBIGUOUS)

- **Where:**
  - identities-and-devices.md, Hosted device-inventory statements: "a 64-byte
    XEdDSA signature over ..."; "The verifier resolves `issuer_key_id` ... and
    then verifies that signature"; Accepting a signed statement, check 3: "The
    signature verifies under that key."
  - the same page, Verifying a signature: "A verifier holds a 32-byte identity
    key `u`", and "For a prekey signature `M` is the tagged key ...; for an
    application signature it is the labelled input below." It names no
    inventory statement.
  - the same page: "**Where this departs from revision 1's `xeddsa_verify`.**
    The accepted set differs in both directions".
  - `conformance-manifest.md`, Hosted device-inventory statements: "Signing and
    verifying the issuer signature are the page's Signing and Verifying a
    signature."
- **Problem:**
  - The hosted section calls the signature XEdDSA and never cites the page's
    verifier. That verifier is introduced for an identity key and lists its two
    uses, neither of them this one. An implementer who used a library's
    revision-1 `xeddsa_verify` would accept `s + q` and refuse a signer that
    leaves A's sign bit set, both of which the page's verifier decides the
    other way.
  - Neither page says the key the issuer-key binding returns is a 32-byte
    Montgomery u-coordinate, or whether a binding that returns a
    non-canonical, `p - 1` or low-order key has resolved (so check 3 refuses)
    or has not (so check 2 does).
  - The only statement tying check 3 to the page's verifier is in the manifest,
    which is not normative.
- **Resolution:** check 3 is the page's "Verifying a signature" under the
  resolved 32-byte u-coordinate; any value the binding returns counts as
  resolved. The vectors decide both: `refused-signature-s-plus-q` is refused
  (revision 1 accepts it), and `refused-signature-issuer-key-zero`,
  `-p-minus-one` and `-not-canonical` are refused at `signature`, not `issuer`.
  IV-19 pins the other direction, which no vector reaches: a signature with A's
  sign bit set, from a signer that does not normalise, is accepted.

### G12-03 The signed statement's framing and its refusal kind are stated for the unsigned decoder only (MINOR)

- **Where:** Hosted device-inventory statements: "The unsigned decoder ... must
  consume exactly the bytes above, so trailing bytes are refused"; "A signed
  statement is the unsigned preimage followed by a 64-byte XEdDSA signature";
  "A refusal by an encoding rule is a decode failure".
- **Problem:** nothing states that a signed input with fewer or more than 64
  bytes after a valid preimage is refused, or that such a refusal is a decode
  failure rather than an authentication failure. A verifier that decodes the
  preimage from the front and takes the next 64 bytes would accept bytes after
  the signature. Reading the last 64 bytes as the signature and decoding the
  rest exactly, which this reader does, and decoding from the front then
  requiring exactly 64 bytes, give the same verdicts (control C12-02), because
  the preimage is self-delimiting; but that is a property of the format, not a
  sentence.
- **Resolution:** the signature is the last 64 bytes and the rest must decode
  exactly; every such refusal is `decode`. `refused-decode-two-signatures`,
  `-fewer-than-64-bytes` and `-exactly-64-bytes` confirm it.

### G12-04 Check 4's compare-and-advance does not say what happens to a statement whose advance fails (AMBIGUOUS)

- **Where:** Accepting a signed statement, check 4: "a verifier records a
  generation as seen, or advances a stored one, only after check 7 has
  accepted the statement. Where statements can be verified concurrently, that
  step is one atomic compare-and-advance against the stored value, and a
  stored value never decreases. Otherwise two statements can both pass this
  check and the later write can lower the record."
- **Problem:**
  - The step comes after check 7 has accepted the statement, and a
    compare-and-advance can fail: two statements pass check 4 against the same
    stored value, the higher one finishes first, and the lower one's advance
    then finds the record past it. The page requires only that the record not
    decrease. Whether the lower statement is still accepted (acted on), is
    refused, or goes back to check 4 is not stated, and neither is the refusal
    it would give.
  - "Compare" is not given its comparison: strictly greater, or greater or
    equal, which decides whether a second statement at the stored generation
    (which the format cannot tell from the first: "The format does not
    distinguish two different validly signed statements at one generation")
    advances anything.
- **Resolution:** the statement stays accepted and the record is left where it
  is (a strictly-greater advance); IV-09 holds only what the page says, that
  the stored value never decreases in either order of completion. The
  manifest says no vector reaches this.

### G12-05 The sparse store's total bound now describes the implementation and states no rule for another (AMBIGUOUS)

- **Where:**
  - sparse-pq-ratchet.md, The store also has a total bound: "a request that
    would exceed it is refused by the ratchet (`SkippedStoreFull`)", then "The
    current sparse implementation and model check the pre-purge store length;
    they do not yet implement resulting-store replacement semantics. The
    purge-before-check order, replacement semantics and refusal atomicity are
    the open `HL-R1-SPARSE-TRANSLATION` follow-up, not current sparse
    behaviour."
  - the same page, Receiving: "Stepping forward deletes any key stored for the
    epoch under a number it is about to store, then stores the keys it passes
    ... this replaces a key only in a state read from storage, which the reader
    accepts"; and "The same cap applies here, for the same reason" as the
    Double Ratchet's, which key-deletion.md now checks against "the resulting
    store" (pass 9).
- **Problem:** the page says what the current implementation and model count,
  says the other count is a follow-up, and does not say which one a conforming
  implementation must use. The two give different verdicts on a stored state
  the sparse reader accepts: CR-18's own state holds 1,997 keys, two of which a
  receive storing five re-derives, and is 2,000 after that receive but 2,002
  counted before the purge. `HL-R1-SPARSE-TRANSLATION` names a record that is not in
  this tree.
- **Resolution:** the reader keeps the resulting-store count that CR-18
  asserts and `spqr.py` implements, which is the Double Ratchet's rule and the reading of "a
  request that would exceed it". CR-21 records both counts on that state. No
  vector distinguishes them. If the page means the pre-purge count to be
  normative, CR-18 and `spqr.py` are wrong; the text does not say so.

### G12-06 A repeat's agreement class is taken under the signed-prekey secret on one page and under no named secret on the other (MINOR)

- **Where:**
  - session-establishment.md, Receiving the initial message: "the message's
    `ephemeral` field is in the same X25519 agreement class, under the
    responder's signed-prekey secret, as the `ephemeral` field carried by the
    initial message that established the session";
  - session-persistence.md, Session, Semantic rules: "A repeated initial
    message is matched against `established_ephemeral` by the responder's
    successful X25519 agreement class";
  - the session's stored fields hold `ratchet_private`, not the signed prekey's
    secret, which is the prekey store's and which a rotation replaces.
- **Problem:** a session asked to compare a repeat after its signed prekey has
  rotated does not hold the secret the first page names. For clamped secrets
  the class does not depend on which secret is used (SE-08), so no verdict
  depends on the choice; neither page says so, and an implementer reading the
  first literally would reach into the prekey store.
- **Resolution:** the reader compares under the session's `ratchet_private`,
  as it has since pass 4; SE-08 shows the verdict is the same under the
  signed-prekey secret, for honest, torsion-equivalent and unrelated
  ephemerals. The docstring of `pqxdh.accept_repeated_initial` quotes a
  sentence ("the same successful X25519 agreement class as the field carried
  by ...") that is not in the current text; it was left unchanged in this pass.

### G12-07 Three statements about the prekey store still speak of four versions or of v4 as current (MINOR)

- **Where:**
  - session-persistence.md, Prekey store, Semantic rules: "they apply to all
    four versions", where the page reads five ("**Five versions are read; one
    is written.**");
  - the same section: "`signed_prekey_sig` begins at offset 69 of a v4 store,
    and a flip there stays canonical under re-encoding", where the re-encode
    check "applies only to the version the writer emits", which is v5;
  - `tacenta-test-vectors/README.md`, "The prekey store's state": "write back
    as current v4", "A runner must reproduce exact stored bytes for accepted v4
    vectors", "the required v4 upgrade on write-back", where every accepted
    current fixture in `prekey-store-state.json` begins `0x05` and the writer
    emits `0x05`.
- **Problem:** stale statements of the kind G3-07, G6-04 and G7-02 recorded. A
  runner that followed the README would write accepted stores back as v4.
- **Resolution:** the reader follows the page: v5 written, v1 to v5 read. The
  vectors pass.

---

## 3. Vector gaps: specified, but no vector pins it

### The 237 inventory vectors pass for the stated reasons

`work/check_new_vectors12.py` (384 checks, no problems):

- **Every decode-refusal case is refused for the rule it names.** The reader's
  refusal reason matches `rule` in all 54, with one expected difference:
  `active-count-exceeds-entries` declares three entries and holds two, so a
  sequential decoder reads the floor and what follows as a third binding and
  stops at its tag byte (201). The input is refused either way.
- **Every statement case** lists both lists in strictly ascending encoded
  order, and `replacement-with-listed-tombstone`'s marker is the
  `binding_commitment` of its listed tombstone.
- **The README's fixed signers hold:** the issuer keys are the X25519 public
  keys of 32 bytes of `0x09` and of `0x0a`, and the signature of every case
  that is not a signature refusal is reproduced by one of them with Z = 64 zero
  bytes. Of the cases refused at `signature`, eight carry a genuine signature
  by one of the two README signers that fails only because of the key the
  policy resolves: the three `refused-signature-issuer-key-*` cases (keys 0,
  p - 1 and p), `refused-signature-by-another-key`, and four
  `first-failing-check-wins-mask-*` cases. The other eleven carry a signature
  no README signer made over the label and the preimage: flipped bits, `s + q`,
  zero bytes, a changed body, and the four wrong signing inputs.
- **Every identity-key refusal holds a key of the class its name gives**
  (non-canonical, one of the five low-order values, off the curve, or mixed
  torsion), and every accepted, binding-policy and statement-policy case holds
  only keys that are X25519 public keys of repeated-byte secrets, as the README
  says.
- **Each of the 15 mixed-torsion keys agrees exactly as the subgroup point it
  was built from**, under a clamped secret.

### New in this pass: inventory rules no vector pins

- **The issuer's duty** (encoding rules, check 5 and check 6 before signing).
  The manifest says so. F12-65 is caught by IV-07 alone.
- **Recording a generation only after check 7, and the compare-and-advance.**
  The manifest says so. F12-64 is caught by IV-08 and IV-17 and by no vector;
  IV-09 holds the compare-and-advance.
- **A statement built in memory.** `inventory-statements-v1.json` gives the
  encoder valid fields only, so no vector checks that an encoder or an
  in-memory verifier refuses a statement that breaks an encoding rule. F12-66
  is caught by IV-05 and IV-07 and by no vector.
- **The unsigned decoder's re-encode refusal.** No input reaches it on its
  own: a decoder that consumes exactly the bytes and checks every field rule
  has already refused anything whose re-encoding would differ, so F12-25 is
  clean. It is not idle, though: it is what refuses an unknown tag byte or a
  trailing byte when the field rule for either is broken (F12-09, F12-10 and
  F12-23 are clean, and are caught once F12-25 is added to them; section 5).
- **An exact binding across the predecessor.** No vector puts in `active` and
  `revoked` two bindings that differ only in the predecessor, so a reader
  whose "same exact binding" ignored the predecessor would pass every vector
  (F12-22, caught by IV-03 and IV-21 only).
- **Check 6's own order**, "those of `active` and then those of `revoked`,
  each in encoded order". No outcome depends on it: every unsound key gives
  the same refusal and no hook is called during check 6. Control C12-01.
- **"A replacement identical to what it replaces"** is one of the four
  properties the page lists as accepted; the acceptance file's `accepted-*`
  cases cover the other three and not this one. IV-21.
- **The big-endian order across a byte boundary.** Of the 163 statements the
  vector files carry that decode, none has a list holding two device ids, or
  two terminal generations, whose big-endian and little-endian byte orders
  disagree. So nothing distinguishes comparing them as big-endian bytes, which
  "compared as unsigned byte strings from the first byte" requires, from
  comparing them little-endian.
  Fault F12-07 was **missed on the first run**; IV-02 was extended to put two
  entries of one list on either side of a byte boundary, and now catches it.
- **The page's verifier on the accepting side of the sign bit**: no
  acceptance case carries a signature with bit 255 set that verifies. IV-19
  (G12-02).
- **The statement policy is given the whole statement as verified.** The
  `statement` hook string carries nothing; the README's "An accepted statement
  is the decoded `signed_hex`" lets the runner check the statement returned and
  the one the policy was given, which this reader does, but a runner that
  handed the policy something else would pass the hook strings. IV-17.

### `GAPS-7.md`'s vector gaps, re-assessed

| Vector gap | Status | Note |
|---|---|---|
| The prekey store's signature rule and `incoherent` | **NARROWED** | `signed-prekey-signature-does-not-verify` pins the refusal and its kind for `signed_prekey_sig`. `kem_sig`, the one-time KEM signatures and the retired pair's are still pinned by no refusal vector. |
| The epoch relation's boundary between tags 6 and 7 | **CLOSED** | `tag-six-keeps-previous-sparse-epoch`, `tag-seven-uses-current-sparse-epoch` and the two refused neighbours. |
| The session's `ratchet_private` rule, the unanswered-initiator rule, each half's own invariant | **CLOSED** | `ratchet-private-does-not-match-dhs-pub`, `unanswered-initiator-is-also-responder`, `triple-state-reader-refuses`, `braid-reader-refuses`. |
| The role rule's Braid half; the failed-Braid exemption | **CLOSED** | `halves-disagree-on-the-braid-role`, `failed-braid-exempts-sparse-epoch`. |
| The record's pre-sizing ceiling | STILL OPEN | No vector offers a count above two budgets. |
| `non-canonical`, for either format | STILL OPEN | Unreachable, as pass 7 said. |
| The Braid's `key_pair` content clause | STILL OPEN | No vector can pin it (G5-02). |
| The session over the Braid | **CLOSED** | The `e` branch, the tag 6/7 boundary, the failed-Braid exemption and both halves of the role rule are now pinned. |
| The prekey store's older versions, and `previous_kem` | **CLOSED** | `legacy-v1`, `legacy-v2`, `legacy-v3`, `retired-kem-prekey`. |
| The session's, the prekey store's and the initiator's stored-key rules | **NARROWED** | `established-ephemeral-key-not-canonical` now pins `established_ephemeral`'s key (whether it was there at pass 7 is not recorded in `GAPS-7.md`). `our_identity_public`, `pending_initial`'s `ephemeral_public` and the initiator's own bundle check are still unpinned. |
| A short buffer with an unknown version | **CLOSED** | The page now makes both refusals conforming for the overlap and says the vectors pin neither (G5-03). There is nothing left to pin. |
| Establishment: PQXDH `AD`; the repeated initial message | **NARROWED** | `session-establishment/session-e2e.json` pins a real handshake's intermediates for the implementation. This reader skips it, so for this reader nothing changed. |
| `DecodeEC` on its own; the erasure encoder's edges; the Braid's MACs, `Init(1, SK)`, state machine and `ek_vector` validation; the fingerprint and `establish_responder`'s refusals; the FIPS 203 section 7.2 check; XEdDSA's remaining edges; AEAD whole-block; an erasure encoder of 65,536 chunks; protobuf `maxFields`; the accepted side of `MAX_SKIPPED_STORE`; classical expiry; the sparse state machine | STILL OPEN | Not re-examined vector by vector. Nothing this pass read (the CHANGELOG, the vectors README and the manifest) records a vector for any of them, apart from the session-e2e file above. |

**Disagreements between a vector and the text: none.** Every one of the 237
inventory vectors agrees with the reading this reader took from the page, and
every rule the vectors exercise is stated in the page or, for the scripted
policy and the hook strings, in the README. The points where the text left a
choice and a vector confirmed it are G12-01, G12-02 and G12-03.

---

## 4. Not attempted, and why

Unchanged from `GAPS-7.md`:

- ML-KEM-1024 and its incremental split (the Braid runs over `kem_double.py`);
  so `session-e2e.json` stays the one skip;
- the end-to-end `Session`;
- prekey store operations other than the two rotations: `create_prekeys`,
  `replenish`, `publish`, `publish_one_time_batch`, `publish_multi_use` and
  `establish_responder`; the store's new read-only rule during establishment
  (session-establishment.md, Receiving the initial message) and the agreement
  send that commits `Failed` (triple-ratchet.md) are therefore not exercised;
- group messaging beyond the two commitments and the inventory statement, and
  device management, which identities-and-devices.md leaves outside itself;
- full JSON-Schema validation;
- every citation of evidence in `threat-model/` and `security-properties/`,
  and the evidence index (G5-07).

**About the reader this pass started from.** Some parts of `reader/` match
texts written after pass 7 and are not described by a clean-room pass record in
`reader/README.md`: `run.py`'s `h_group_commitment` and
`h_inventory_statement`; RJ-01 and CR-20, which cite the sentences that closed
G5-03 and G5-09; and the prekey store's v5, where `GAPS-7.md` found every
accepted store at v4. `CHANGELOG.md` records some of this ("The independent
reader follows the v2 agreed-secret replay identity and covers fail-closed
import of v4 replay records into v5"), and session-persistence.md, Rejection,
itself cites "The independent reader's rejection cases". This pass read those
parts as it found them, ran them, did not re-derive them, and replaced only the
registration of `h_inventory_statement` with its own handlers. Who changed them
is not something this directory records.

---

## 5. Deliberate faults

72 faults and 2 controls (`work/faults12.py`), each a textual change to a
fresh copy of the reader, then the full runner. Where the reader states one of
the page's rules in two places -- the decoder's field read and the encoding
rules a built statement is held to -- the fault breaks both, and says so.
**66 were caught, 61 of them by a vector file.** The per-fault list, with the
vectors and cases that failed, is in `reader/README.md` and
`work/faults12.txt`.

| | Tried | Caught | Caught by a vector file |
|---|---|---|---|
| Sort order of both lists (F12-01 to F12-08) | 8 | 8 | 7 |
| The predecessor tag and its value (F12-09, F12-10, F12-09b, F12-10b, F12-11) | 5 | 3 | 3 |
| The capability rule (F12-12 to F12-15, F12-14e) | 5 | 5 | 5 |
| The other encoding rules (F12-16 to F12-25, F12-16b, F12-23b, F12-24r) | 13 | 11 | 10 |
| Each of the seven checks (F12-26 to F12-37) | 12 | 11 | 11 |
| The order between the checks (F12-38 to F12-43) | 6 | 6 | 6 |
| The binding policy's order, list and stop (F12-44 to F12-47) | 4 | 4 | 4 |
| Check 6's classes of refused key and its reach (F12-48 to F12-55) | 8 | 7 | 7 |
| The signature input and the verifier (F12-56 to F12-61) | 6 | 6 | 6 |
| `binding_commitment` (F12-62, F12-63) | 2 | 2 | 2 |
| The issuer's duty, the generation record, a built statement (F12-64 to F12-66) | 3 | 3 | 0 |
| **Total** | **72** | **66** | **61** |

**Not caught, six, and why:**

- **F12-09 and F12-10** (a predecessor tag other than 0 or 1 read as present,
  or as absent) and **F12-23** (trailing bytes accepted) are each masked by
  the page's other rule, "it must refuse a value whose re-encoding differs from
  the input": the re-encoding carries tag 0 or 1 and no trailing byte, so the
  input is refused anyway. With the re-encode check removed as well, each is
  caught by vectors: F12-09b and F12-10b by `predecessor-tag-2` and
  `predecessor-tag-255` (F12-09b also by an acceptance case), F12-23b by
  `one-trailing-byte`, `signature-sized-trailing-bytes` and
  `refused-decode-two-signatures`. The page states both rules, and this reader
  applies both, so neither alone is observable.
- **F12-25** (the re-encode check removed) is clean for the converse reason:
  the field rules refuse everything first. Section 3.
- **F12-29** (check 2 handed the account asked about rather than the
  statement's) is an equivalent change: after check 1 the two are equal byte
  for byte.
- **F12-51** (check 6's first step, "`u` is not p − 1", removed) is
  equivalent in this reader's arithmetic, which inverts by raising to p − 2 and
  so takes 1/0 as 0: u = p − 1 then gives y = 0, the point of order four, and
  step three refuses it. The step is not redundant in general -- an
  implementation whose division refuses or misbehaves at zero needs it, and
  the page gives it -- but no input tells a reader with it from this one
  without it. `refused-key-low-order-p-minus-one-*` pass either way.

**Caught only by derived cases:** F12-07 (IV-02), F12-22 (IV-03, IV-21), F12-64
(IV-08, IV-17), F12-65 (IV-07) and F12-66 (IV-05, IV-07). F12-64 and F12-65
are behaviour the manifest says no vector covers; F12-07, F12-22 and F12-66 are
section 3's byte-boundary, exact-binding and built-statement gaps.

**Changes made during the run.** The first run (`work/faults12-first-run.txt`)
tried 66 faults and caught 58. Between it and the recorded run:

- **F12-07 was missed**: no vector and no case put two entries of one list on
  either side of a byte boundary. IV-02 was extended to do so and now catches
  it. It is the one fault of the pass that nothing caught at first; the gap
  is recorded in section 3.
- **F12-41 was written wrong**: it added a per-binding key check but left
  check 6 in place, so it changed nothing. Rewritten to remove check 6 and
  check each key just before its binding's policy, it is caught by 31
  acceptance vectors and IV-15.
- The capability, account-length and count faults first broke only the
  encoder's copy of each rule, where the decoder keeps its own. They now break
  both; F12-14e keeps the encoder-only version, which the commitment vectors
  catch. F12-09b, F12-10b, F12-16b, F12-23b and F12-24r were added.
- IV-09 was rewritten to show that its interleaving reaches the hazard the page
  names (a plain write lowers the record), and the full set was then re-run
  against the final reader; that run is the one recorded, and it matches the
  second run fault for fault. Only two docstrings changed after it.

**Controls.** C12-01 (check 6 walks `revoked` before `active`, where the page
says `active` first) and C12-02 (a signed input decoded from the front and then
required to hold exactly 64 more bytes, rather than split at 64 from the end)
fail nothing, as expected: no outcome depends on either (G12-03, section 3).

---

## 6. Isolation

- **What was read:** this directory and nothing else (one attempted read
  outside it failed and read nothing; below).
  - `tacenta-spec/`: `protocol/identities-and-devices.md` in full and
    `error-handling.md` in full, as the pass was directed; `message-format.md`,
    Curve public keys and Rejection; the rows of `CONSTANTS.md` the section
    uses; `CHANGELOG.md` `[Unreleased]`; and the passages the open gaps concern
    in `session-persistence.md`, `session-establishment.md`, `ratchet.md`,
    `sparse-pq-ratchet.md`, `triple-ratchet.md`, `key-deletion.md`,
    `threat-model/` and `security-properties/` (including the opening of
    `evidence-index-format.md` and the top-level keys of
    `evidence-index.json`). No ADR was opened.
  - `tacenta-test-vectors/`: the README's directory list, its prekey-store,
    session and inventory layout sections and Status; the manifest's Hosted
    device-inventory statements section; the five files under
    `vectors/groups/` in full; the ids, comments and version bytes of
    `persistence/prekey-store-state.json` and `session-state.json`.
  - `reader/`; `GAPS-7.md` to `GAPS-10.md`; the G5-04 to G5-10 entries of
    `GAPS-5.md`, to re-assess them; `SOURCE-REVISION`. `GAPS.md`, `GAPS-2.md`,
    `GAPS-3.md`, `GAPS-4.md` and `GAPS-6.md` were not opened.
- **Outside this directory.** Nothing outside it was read, listed or
  searched, with three facts recorded in `reader/README.md`, "Isolation, pass
  12":
  - the pass's first command, `ls -la` of this directory, printed the standard
    `.` and `..` entries, the `..` line giving that entry's permissions, owner,
    size and date and nothing inside it;
  - the deliberate-fault runs were background commands whose output was
    redirected into `work/`; each of them, and each of two commands that
    watched them, also left an output file outside this directory, and none was
    opened;
  - **one attempted read outside this directory**: a command piped a copy of
    `work/faults12_table.py` into Python through standard input, so the script
    took its root from one level too high and tried to open
    `work/faults12-second-run.txt` in the directory that contains this one. No
    such file existed, the open failed, and nothing was read. The comparison
    was redone with a script file inside `work/`.
- **Names treated as text.** The pages, the vectors README, the manifest and
  `CONSTANTS.md` name implementation files, generators and records
  (`groups/inventory.rs`, `tacenta_core::groups::inventory`,
  `tacenta-core/tests/group_commitments.rs`, `generate-inventory-vectors.py`,
  `tooling/check-vectors.py`, `tacenta-core/LABELS.md`,
  `HL-R1-SPARSE-TRANSLATION`, `session-operation-trace.md`, the evidence
  index's paths). None was looked for. No vector generator was read.
- **What was written:** only inside this directory:
  - `reader/`: the new `tacenta_reader/inventory.py`,
    `tacenta_reader/inventory_vectors.py` and `cases_inventory.py`; CR-21
    appended to `cases_ratchet.py`; SE-08 appended to `cases_curvekeys.py`;
    `run.py` (an import and three registration lines); `README.md`;
  - `GAPS-12.md`;
  - `work/`: `accept_dump12.txt`, the run outputs, `check_new_vectors12.py`
    and its output, `faults12.py`, `faults12_table.py`, `faults12.txt`,
    `faults12-first-run.txt` and `faults12-second-run.txt`.

  The per-fault copies were made under `work/faults12/`, each reaching the
  vectors through a symbolic link inside this directory, and removed after
  each run. Python wrote its usual `__pycache__` directories inside `reader/`.
- **What was not consulted:** no implementation (tacenta-core, tacenta-model,
  tacenta-proofs, the Rust runner, libcrux, libsignal or anything derived from
  them), no git history, no vector generator, no other scratch files, and no
  web search. RFC 7748 section 5, RFC 8032 section 5.1, the XEdDSA document's
  revision 1 and the UTF-8 definition Python's strict codec implements (RFC
  3629) were used from knowledge. Nothing was fetched. Only the Python
  standard library was used.
- **Unrelated notes, not used.** An index of notes from other work, and a list
  of further material, were available alongside the directory. None of it was
  opened, and nothing in it was used for any reading or decision here.
