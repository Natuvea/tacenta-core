# Gap report, seventh pass: the reader against the current specification

The clean-room reader (`reader/`) was updated from `tacenta-spec` and
`tacenta-test-vectors` alone, against the tree as found in this directory:

- `SOURCE-REVISION` `5ae44427d17d0e8bfa1d314780305690000ee770`;
- `VERSION` `0.2.0`;
- everything under `CHANGELOG.md` `[Unreleased]`. Its Added section now opens
  with "`protocol/session-persistence.md`, Prekey store, Semantic rules: a
  sixth rule, that every stored signature verifies under `identity_public`".

The sixth pass read `c3a00471fbef23f514eca184aac56be7b76fbc8d`, the fifth
`1dd174609bc5b008564bddef45bee43d71589761`.

Severity, as in the earlier reports:

- **BLOCKING**: cannot be implemented from the tree without guessing.
- **AMBIGUOUS**: more than one reading; a vector decided it, or nothing did.
- **MINOR**: wording, pointers, or a value findable only in the wrong place.

A hypothesis confirmed by a vector is still a gap.

**Baseline** (`python3 reader/run.py`, before any change): 584 PASS, 0 FAIL,
30 SKIP.

| | PASS | FAIL | SKIP |
|---|---|---|---|
| Vectors (36 files) | 377 | 0 | 30 |
| Derived cases (11 modules) | 207 | 0 | 0 |
| **Total** | **584** | **0** | **30** |

The 30 skips were the two new files, `persistence/prekey-store-state.json`
(17) and `session-state.json` (13).

**Final run:**

| | PASS | FAIL | SKIP |
|---|---|---|---|
| Vectors (36 files) | 407 | 0 | 0 |
| Derived cases (12 modules) | 219 | 0 | 0 |
| **Total** | **626** | **0** | **0** |

All 30 new vectors passed on the first run of the new handlers, the four
accepted prekey stores included: the sixth rule was implemented from the page,
and the signatures those four carry verify under the reading the page and
session-establishment.md give, with no value taken from the vectors' bytes.
`work/check_new_vectors7.py` (92 checks, no problems) confirms the 30 pass for
the reasons the text gives and not by accident, and checks the coverage
statements the manifest and the vectors README make about them (section 3).

**What changed in the reader:**

- **`persistence.py`, the prekey store's sixth semantic rule.** Every stored
  signature is verified under `identity_public`: `signed_prekey_sig` over
  `EncodeEC` of the public half of `signed_prekey_secret`, `kem_sig` over
  `EncodeKEM` of `kem_pair`'s `ek`, each `kem_one_time` entry's over its own
  pair's, and `previous_signed`'s and `previous_kem`'s over theirs. The one-time
  curve prekeys carry none and are not covered. Verification is XEdDSA under
  the identity key with no label (session-establishment.md, Publishing keys;
  identities-and-devices.md, Signing and Verifying a signature). It runs last
  of all, after the framing, the v4 re-encode check and the other five rules,
  and it raises the new `Incoherent`.
- **`persistence.py`, a fifth refusal kind.** `Incoherent`, "the prekey store's
  ... alone, its other rules being malformed" (Rejection). `run.py` now maps
  five kinds for these two formats and two for the leaf formats.
- **`persistence.py`, the Braid's `key_pair` content clause is now scoped.**
  `KEY_PAIR_VIEW` defaults to `None`: this reader does not have the KEM
  library's layout, so in tags 1 to 4 it checks the field's 11,872-byte length,
  accepts the content, and conforms. The clause itself is kept and is exercised
  from both sides of the scope by `BK-01`, which supplies a layout for the
  inside-the-scope half and restores `None` after. This closes **G5-02**, the
  gap this reader raised in pass 5.
- **`prekeys.py`, new.** `rotate_signed_prekey` and `rotate_kem`, the two
  operations the new rule puts an obligation on: each signs under the identity
  whose public key the store holds as `identity_public` and refuses, changing
  nothing, if handed any other; each takes the next identifier and returns the
  store unchanged and silently once `next_id` stands at `u32::MAX`; `rotate_kem`
  drops the record entries of the key it wipes (key-deletion.md).
- **`run.py`:** handlers for `prekey-store-state` and `session-state`. Stored
  bytes, checked against `fields`, written back as the input, and against the
  named refusal, with the four kinds these two formats can give.
- **Cases:** a new module `cases_signed.py` (PK-01 to PK-08, RJ-02, IN-03,
  TM-03, EP-01). `cases_persistence.py`'s prekey-store fixtures now carry
  signatures that verify, and its session breakages are factored out so RJ-02
  can run every one of them. `SK-08` and `BK-01` are rewritten for the two
  decisions this revision makes; `TM-01`'s note about `LABELS.md` is dropped,
  ASM-05 having taken the content in.

**The session's format needed no change.** Its eight semantic rules, its four
field-by-field refusals and its two other refusal kinds were implemented from
the page in pass 2 and extended in pass 5; the 13 session vectors passed
against that code unchanged.

---

## 1. The earlier gaps

Counts for the gaps `GAPS-6.md` left open: **3 CLOSED, 11 STILL OPEN, 1
NARROWED.** Those gaps are G5-02 to G5-10, G4-01 and G6-01 to G6-05.

The gaps recorded as closed before are still closed: G-01 to G-28, G2-01 to
G2-12, G3-01 to G3-08, G4-02 to G4-04 and G5-01. Each still has its case or
vector, and all pass.

### Re-assessed

| Gap | Status | Citation, and what changed in the reader |
|---|---|---|
| G5-02 The Braid key pair's load check needs the delegated layout | **CLOSED** | session-persistence.md, Semantic rules of the leaf formats, Braid: "**That clause is scoped to an implementation that knows the key pair's layout.** Where those two values sit inside the field's 11,872 bytes is the KEM library's own serialisation, which this page delegates rather than defines (Braid; ADR-0006, point 5), so an implementation without that layout cannot apply the clause at all. Such an implementation checks the field's length, accepts it, and conforms." The Principles' "Validated, not only parsed" names the one scoped rule and says "A reader outside its scope checks that field's length and accepts it, and is conforming in doing so"; the leaf formats' preamble says the same; the Braid section says "That scope is part of the rule and is stated with it". The vectors README and the manifest both say no vector can pin the clause and why. **The reader was deficient and is now conforming**: `KEY_PAIR_VIEW` is `None`, the length is checked and the content accepted. BK-01 is rewritten to exercise both sides of the scope, and fault F7-39 -- a reader that applies the clause with a guessed layout -- is caught by two vectors and by BK-01. |
| G6-02 `vector.schema.json`'s `refusal` names two files where four now carry it | **CLOSED** | `schema/vector.schema.json`, `refusal`: "Every invalid vector in vectors/persistence/ carries one except the erasure coders': ratchet-state, sparse-ratchet-state, triple-ratchet-state, braid-state, prekey-store-state and session-state." All six are named, `incoherent` is added to the enumeration with its scope ("the prekey store's alone, for its signature rule, which no vector reaches today"), and `inconsistent` is described as the session's alone with the reason Rejection gives. The same paragraph of the vectors README is *not* fixed; that is G7-02 below, recorded as new because it is a different file and a different sentence. |
| G6-04 The conformance manifest says, in one section, both that the Braid's ceiling is pinned by vectors and that no vector pins it | **CLOSED** | The contradicting sentence is gone: `grep "no vector here pins it"` over `tacenta-test-vectors/` returns nothing. "Addition: reserved counter ceilings" now states the pinning once, and agrees with the README's Status and with the manifest's own Covered table. |
| G5-07 The evidence the requirements cite is outside the specification | **NARROWED** | `decisions/ADR-0006-specification-is-normative.md`, new point 7: "**Evidence may be cited; content may not.** ... Such a citation records where the evidence for a claim about this project's work is. It is not part of the protocol's definition ... **What a page requires is readable from the specification alone.** A rule, a list, or a set that a requirement is stated over belongs in these pages." Both statements that took *content* from outside have moved it in: ASM-05 now names the two registered prefix pairs with their values over CONSTANTS.md's "Derivation labels", and AS-12 states REQ-AUTH-13's durable state for the session and the prekey store rather than pointing at a registry of function names. `work/xref7.py` finds no page taking content from outside: the remaining `tacenta-core/LABELS.md` and `AUTHENTICATION-BOUNDARY.md` mentions are beside the values or the requirement the page itself states. **What is still open:** every Status in `security-properties/` still names a theorem, a test or a `CLAIMS.md` section that is not in this tree, so a reader cannot check any of them -- which point 7 now says is intended. TM-03 is new and reads the two moved statements against the page. No theorem, test or `CLAIMS.md` section was looked for. |
| G5-03 "Shorter than the fixed fields of the version the reader reads" when there is no one such version | STILL OPEN | session-persistence.md, Rejection, is unchanged, and the two formats added this pass widen it: the prekey store's fixed part ends after `next_id` at v1 and after two presence bytes at v4, so "the fixed fields of the version the reader reads" names four different lengths for one buffer. The vectors pin neither refusal, as the page says: `prekey-store-state.json` has `empty` (short) and `version-unknown`/`version-zero` at full length, and `session-state.json` the same shape. Control C7-01, a reader that checks the store's length before its version byte, fails nothing. |
| G5-04 The work a forged message costs, stated three ways | STILL OPEN | `threat-model/adversaries.md` ADV-01 and ADV-06, `exclusions.md` EX-03 and ratchet.md, Skipped keys, all unchanged. The reader follows the protocol pages (CR-08). |
| G5-05 LIM-21: "until it is established again" | STILL OPEN | `security-properties/limitations.md` still reads "refuses to encrypt or decrypt until it is established again", and no page re-establishes a session whose Braid has failed. `Failed` is terminal in the reader (BR-12, BR-18). |
| G5-06 ASM-13 and ASM-19 are "relied on by every requirement" | STILL OPEN | `threat-model/assumptions.md`: ASM-13 "Relied on by: every requirement, for the adversary it holds against"; ASM-19 "every requirement, as a statement about `tacenta-core`; in particular ...". `work/xref7.py` (25 checks) reports these two and no other: every other assumption's list agrees exactly with the requirements whose "Rests on" line names it, ASM-17's list is the qualified form followed by the exact twelve, and every cited AS, ADV, ASM, EX, LIM and REQ identifier exists. |
| G5-08 The sparse ratchet's retention window: saturating on one page, not on the other | STILL OPEN | sparse-pq-ratchet.md, Retiring old epochs, still writes "every epoch `e` with `E < e + EPOCHS_KEPT`"; session-persistence.md still writes "`e <= epoch < e + EPOCHS_KEPT`, the sum saturating". The advance to `u64::MAX` is refused, so the difference stays unobservable. |
| G5-09 The classical ratchet at `Nr = u32::MAX`, for a message numbered below it | STILL OPEN | ratchet.md, Sending and receiving, is unchanged, and fixes no order between the two refusals where sparse-pq-ratchet.md does. The reader still gives the stale refusal first. |
| G5-10 REQ-AUTH-11 does not cite the rule that refuses a replay onto a chain the receiver has left | STILL OPEN | `security-properties/authentication.md` REQ-AUTH-11 is unchanged. TM-02 still checks the requirement over a live Triple Ratchet session and finds the sparse half's out-of-order refusal doing the work. |
| G4-01 A decoder of the composite header alone, and its trailing bytes | STILL OPEN | Unchanged since pass 5. |
| G6-01 The two persistence files' `sk` input is the same word for two different secrets | STILL OPEN | `tacenta-test-vectors/README.md`, "The ratchets' persisted states" and "The Triple Ratchet's state", are unchanged, and still use `sk` for the Double Ratchet's already-split secret in one file and the unsplit `SK` in the other. |
| G6-03 Whether a Braid operations vector's `output` must read back is not stated | STILL OPEN | The README's "The Braid's state" still says only "`output` is the stored bytes of the state reached", where "The ratchets' persisted states" states the read-back obligation and the `-read-back` sibling. The two `ct2-sampled-*` vectors still have no sibling. The reader still applies the obligation; a reader that did not would also pass. |
| G6-05 A Braid step's absent codeword has no zeroing rule | STILL OPEN | The README's step layout is unchanged and still does not say that an absent codeword's index and chunk are zero, nor point at the page that says it of the wire. |

### Closed in earlier reports, touched by this revision, still closed

- **G2-08** (the Braid's delegated `key_pair` and `encaps`): the delegation is
  unchanged; what changed is that the consequence for the `key_pair` *content*
  rule is now a scope on the rule rather than a deficiency in a reader without
  the layout (G5-02).
- **G2-12** (complete lists of semantic rules): both lists are still stated as
  complete, and the completeness claim now carries its one exception in three
  places -- the Principles, the leaf formats' preamble and the Braid clause
  itself. The prekey store's list grew from five rules to six, and the page
  says so and says which of the six is exempt from the inductive invariant.
- **G3-07** (stale status statements): closed for `CHANGELOG.md` and, this
  pass, for the conformance manifest (G6-04). The same fault has appeared in
  the vectors README's Status paragraph; that is G7-02, recorded as new.

No earlier gap was judged wrong.

---

## 2. New gaps

### G7-01 The two new vector files have no layout section, so which `fields` they carry, and what three of the session's names mean, is not stated (AMBIGUOUS)

- **Where:**
  - `tacenta-test-vectors/README.md`, "Vector layouts", has a subsection for
    the decoders, the erasure code, the erasure coders' persisted formats, the
    ratchets' persisted states, the Triple Ratchet's state, the Braid's state,
    the protobuf profile and the AEAD -- and none for
    `prekey-store-state.json` or `session-state.json`;
  - `schema/vector.schema.json`, `fields`: "the named values the input decodes
    to ... a runner must check that the names match as well as the values",
    and "The inputs and outputs of the erasure-code, persistence, protobuf and
    AEAD files ... are laid out in `tacenta-test-vectors/README.md`, Vector
    layouts", which for these two files is a pointer to nothing;
  - `conformance-manifest.md`, Covered: "each with its fields, the halves' tag
    and epochs checked through their own crates".
- **Problem:**
  - A runner must reproduce the exact set of names. For the prekey store the
    twelve names are the page's own field names, but the *selection* is not
    derivable: `kem_pair`, the one-time entries, the record's entries and the
    two retired fields' contents are left out, while the three lists appear as
    their counts and the two retired fields as their presence bytes. Nothing
    says the set stops there, and nothing says a present `previous_signed` is
    reported by its presence byte rather than by its secret, identifier and
    signature -- which is the one place the schema's "A value the decoder
    reports absent is left out" does not settle it, the value being present.
  - For the session, three of the nine names are not field names of the
    session format at all. `braid_tag`, `braid_epoch` and `sparse_epoch` are
    values inside the two length-prefixed halves, and the only sentence that
    connects them to anything is in the manifest, not in the layout section.
    A runner has to decide that `braid_epoch` is the Braid's `epoch` field
    (not, say, the epoch the session is negotiating) and that `sparse_epoch`
    is the sparse ratchet's and not the classical ratchet's counter.
- **Resolution:** read as above, from the two formats' own field lists and
  from the two semantic rules that are stated over the halves' tag and epochs.
  All seven accepted vectors match on names and values on the first run. A
  confirmed hypothesis is still a gap; fault F7-12 and F7-18, which change what
  the reader believes an epoch or a tag means, are caught by those vectors, so
  a wrong reading here would have been found -- but only after it was made.

### G7-02 The vectors README's Status paragraph says the two formats have no vectors, and names two files where six now carry a `refusal` (MINOR)

- **Where:** `tacenta-test-vectors/README.md`, "## Status":
  - "The session's and the prekey store's persisted formats have none, because
    the model states neither.";
  - "In the two ratchet-state files an invalid vector also names its
    `refusal`."
- **Problem:** both sentences are the state of the tree before this revision.
  The README's own directory list, eleven lines above the first, names
  `prekey-store-state.json` and `session-state.json` and says what their
  accepted vectors carry; the manifest devotes a Covered table and a Not
  covered section to them; and six files under `vectors/persistence/` now carry
  a `refusal`, which the schema (G6-02, closed) has been corrected to say. A
  reader deciding what to implement from the Status paragraph is told these two
  formats have nothing to run against.
- **Resolution:** the reader follows the vectors, which exist. `work/xref7.py`
  reports both sentences. This is the same kind of stale statement as G3-07
  and G6-04, in the third of the three files.

### G7-03 The sixth rule does not say which signature scheme, or where a prekey signature's verification is defined (MINOR)

- **Where:**
  - session-persistence.md, Prekey store, Semantic rules: "**Every stored
    signature verifies under `identity_public`**: `signed_prekey_sig` over
    `EncodeEC` of the public half of `signed_prekey_secret` ...", whose only
    citation is to session-establishment.md, Sending the initial message, and
    only for "only the KEM prekeys are signed individually";
  - session-establishment.md, Parameters: "`Sig(PK, M, Z)` is an XEdDSA
    signature over `M` by `PK`'s private key", and Publishing keys:
    `Sig(IKB, EncodeEC(SPKB), Z)`, `Sig(IKB, EncodeKEM(PQSPKB), Z)`;
  - identities-and-devices.md, Signing: "Prekey signatures carry no label
    (session-establishment.md, Publishing keys)", and Verifying a signature.
- **Problem:** the rule says "verifies" without naming XEdDSA, without saying
  that the message is unlabelled, and without citing either page that settles
  it. An implementer who reached for identities-and-devices.md's *application*
  signature, which is the labelled one and is the only signing the identity
  page leads with, would put `"tacenta:application-signature:v1" || 0xFF` in
  front of the message and refuse every honest store. The answer is in the
  tree, two pages away, and both sentences that give it are in sections about
  something else.
- **Resolution:** read as `Sig(IK, EncodeEC(pub), Z)` and
  `Sig(IK, EncodeKEM(ek), Z)`, verified by identities-and-devices.md's six
  rules with no label. The four accepted vectors confirm it: they are the first
  vectors in the tree that verify a stored signature, and a wrong message would
  fail all four. Fault F7-32, which takes the message as the signed prekey's
  secret rather than its public half, is refused by all four, and F7-28, which
  takes the KEM message as the whole key pair rather than `EncodeKEM` of its
  `ek`, by all four as well.

### G7-04 The obligation is stated over "every operation that signs a prekey", and only the two rotations are said to refuse (AMBIGUOUS)

- **Where:**
  - session-persistence.md, Prekey store, Semantic rules: "**every operation
    that signs a prekey signs under the identity whose public key is
    `identity_public`**, and an implementation whose API lets a caller supply
    some other identity refuses it rather than storing the result";
  - key-deletion.md: `rotate_signed_prekey` "signs it under the identity whose
    public key the store holds as `identity_public` -- and refuses, changing
    nothing, if handed any other (session-persistence.md, Prekey store,
    Semantic rules)", and "`rotate_kem` does the same";
  - key-deletion.md on `create_prekeys` and `replenish`, neither of which
    mentions an identity at all.
- **Problem:** `replenish` adds one-time KEM prekeys, and every KEM prekey is
  signed individually (session-establishment.md), so `replenish` is an
  operation that signs a prekey and the obligation reaches it. `create_prekeys`
  signs the signed prekey, the last-resort KEM prekey and every one-time KEM
  prekey. Neither is said to take an identity, to check one, or to refuse one;
  key-deletion.md's paragraph on them is about identifiers. So a reader cannot
  tell whether the two rotations are singled out because they are the only
  operations that can be handed an identity, or whether the other two carry the
  same refusal and it is simply not written where they are described.
- **Resolution:** the two rotations are modelled (`prekeys.py`) with the
  refusal the page states. `create_prekeys` and `replenish` are not modelled;
  PK-07 and PK-08 hold the obligation over the rotations only, and PK-08
  checks the consequence the page draws -- that no state forty rotations
  produce is refused on any of the six rules.

### G7-05 `identity_public = p - 1` keeps the fifth rule and can never keep the sixth (MINOR)

- **Where:**
  - session-persistence.md, Prekey store, Semantic rules: "**`identity_public`
    is canonical**: the canonical encoding of a curve public key
    (message-format.md, Curve public keys)", and the sixth rule after it;
  - message-format.md, Curve public keys: the key "is accepted exactly when
    that value is below p";
  - identities-and-devices.md, Verifying a signature: the conversion refuses
    `u = p - 1`, which is the value at which `(u - 1)/(u + 1)` divides by zero.
- **Problem:** `p - 1` is canonical, so the fifth rule accepts it; no signature
  can verify under it, so the sixth refuses every store that holds it. The two
  rules do not contradict -- "No state the operations produce is refused" still
  holds, since X25519's output is never `p - 1` in practice -- but the page
  presents the five cheap rules and the sixth as independent, and does not
  record that the sixth narrows the fifth's accepted set to a strict subset.
  A reader that tested the fifth rule at `p - 1` before this revision, as this
  one did in pass 5 (SK-08), now gets `incoherent` where it got acceptance.
- **Resolution:** SK-08 is rewritten to state it: `p - 1` passes the canonical
  rule and is then refused as incoherent, the accepted case moving to a store
  whose identity is a real X25519 public key. Recorded because the page's own
  list of what the sixth rule binds -- "the signatures themselves,
  `identity_public`, and the signed prekey's secret" -- does not mention that
  it also binds `identity_public` to being a key some identity actually has.

### G7-06 `sparse-epoch-does-not-follow-the-braid` moves the Braid's epoch, not the sparse ratchet's (MINOR)

- **Where:** `vectors/persistence/session-state.json`, the vector's `id` and
  `comment`: "the sparse ratchet's epoch one past what the Braid's state tag
  allows".
- **Problem:** the vector differs from the `responder` fixture in one byte, the
  last of the Braid's eight-byte `epoch`, which moves the Braid's epoch from 1
  to 3. The sparse ratchet's `epoch`, at offset 33 of the `spqr_state` inside
  the `triple_state`, is unchanged at 0. The relation is broken either way and
  the refusal is the `inconsistent` the vector names, so nothing an
  implementation does depends on it; but the vector does not exercise the side
  its name and comment say it does, and "one past" describes neither state --
  at Braid tag 5 the rule requires the sparse epoch to be `e - 1`, which is 2,
  and it is 0.
- **Resolution:** the reader implements the relation from the page and passes
  the vector. Recorded because a reader checking its reading against the
  comment would look in the wrong half of the session, and because the vector
  leaves the sparse side of the relation unexercised -- which the manifest's
  "Not covered" does not list among what the file does not reach.

---

## 3. Vector gaps: specified, but no vector pins it

Everything below is covered in this reader only by derived cases. Those test
the reader's reading of the text, not agreement with anyone else. The fault
evidence is in section 5.

### The 30 new vectors pass for the stated reasons

`work/check_new_vectors7.py` (92 checks, no problems):

- **Every invalid vector is refused with the kind it names**, in both files.
- **Each invalid vector pins its own rule.** With the prekey store's five cheap
  rules made vacuous, exactly the eight vectors whose comments name one are
  accepted -- except `identity-public-not-canonical`, which then lands on the
  sixth rule and is refused as `incoherent` (G7-05) -- and the framing refusals
  do not move. With the session's semantic rules made vacuous, exactly the six
  that name one are accepted.
- **With the signature rule made vacuous, no vector moves**, which is the
  schema's statement that `incoherent` is "the prekey store's alone, for its
  signature rule, which no vector reaches today".
- **With the four `kem_pair` content clauses made vacuous, no vector moves**,
  which is the manifest's "no vector varies `kem_pair` at all".
- **Every accepted store** is v4, re-encodes to its input, has every stored
  signature verifying, has a `kem_pair` that passes all four clauses, and has
  every record entry tagged with a live key.
- **Every accepted session** re-encodes to its input and keeps all eight
  semantic rules.
- **The manifest's coverage statements hold**: no vector carries
  `previous_kem`, the largest `seen_count` is 1,025, no session vector carries
  a Braid tag of 7 to 11, every session refusal vector is the responder fixture
  with one field changed, and `peer-identity-not-canonical` changes only
  `peer_identity_public`.

### New in this pass

- **The prekey store's signature rule, and the `incoherent` refusal.** No
  vector reaches either, and the schema and the manifest both say so. Faults
  F7-21, F7-27, F7-29, F7-30 and F7-32 are caught only by cases (PK-01 to
  PK-06, SK-08).
- **The epoch relation's boundary between tags 6 and 7.** The accepted session
  vectors carry Braid tags 1 and 5 only, and the manifest says the relation is
  reached "only [in] its `e - 1` branch". Nothing in the tree distinguishes a
  reader whose `e` branch begins at tag 7 from one whose begins at tag 6.
  F7-13 was **missed on the first fault run**; EP-01, which walks all twelve
  tags under both readings, was added for it and catches it.
- **The session's `ratchet_private` rule, its "an unanswered initiator is not
  also a responder" rule, and "each half satisfies its own crate's
  invariant".** The manifest names all three as unreached. F7-40 is caught only
  by RJ-02.
- **The role rule's Braid half**, and **the epoch relation's exemption for a
  failed Braid**. F7-16 and F7-15 are caught only by cases.
- **The record's pre-sizing ceiling, and the per-key bound read as a whole.**
  F7-11 and F7-06 are caught only by PS-22; the manifest states the first.
- **`non-canonical`, for either format.** Both re-encode checks are
  unreachable in a reader that accepts only canonical encodings, which is what
  the manifest says and what `SessionState.ofBytes_ok` is said to prove.
  F7-25 and F7-26, which change the kind each reports, are the two faults
  **nothing in this pass catches, and nothing could**: no input exists that
  reaches either check. Recorded as a limit of the fault method rather than as
  a hole a case could fill.
- **The Braid's `key_pair` content clause** (G5-02, now closed): still pinned by
  no vector, and now for a reason the page states -- the clause has no single
  verdict every conforming reader must reach.

### `GAPS-6.md`'s vector gaps, re-assessed

| Vector gap | Status | Note |
|---|---|---|
| The session's and the prekey store's persisted formats | **CLOSED** | Both files exist and pin the layouts, the framing refusals with their kinds, five of the store's six semantic rules and five of the session's eight. What they do not reach is section 3 above and the manifest's own "Not covered". |
| The session over the Braid | **NARROWED** | `session-state.json` pins the epoch relation's `e - 1` branch and the role rule's sparse half over a real Braid. The `e` branch, the tag 6/7 boundary, the failed-Braid exemption and the role rule's Braid half are still unpinned. |
| `DecodeEC` on its own | STILL OPEN | |
| The repeated initial message | STILL OPEN | |
| The erasure encoder's stated edges | STILL OPEN (narrowed in pass 5) | |
| The Braid: MACs, `Init(1, SK)`, the state machine, `ek_vector` validation | STILL OPEN | The `key_pair` content clause is now a rule no vector can pin, by its own scope. |
| The persisted Braid | CLOSED (pass 6) | |
| The triple ratchet state | CLOSED (pass 6) | |
| Establishment: the fingerprint, the record's refusals, per-key budget | **NARROWED** | The stored record's per-key budget is now pinned from both sides (`record-at-budget`, `record-over-budget-for-one-key`) and its tagging rule with it. The fingerprint's construction, and the refusals `establish_responder` gives, are still unpinned. |
| Establishment: `DecodeEC`'s canonical refusals, and G3-05 | STILL OPEN (narrowed in pass 4) | |
| Establishment: the FIPS 203 section 7.2 check | STILL OPEN | The store's `kem_pair` clauses are reached by no vector either (manifest, Not covered). |
| Establishment: PQXDH `AD` and `CONCAT(ad, header)` | STILL OPEN | |
| XEdDSA: a `u` with no point, the cofactored-only signature, a non-canonical `R` not of small order, application signatures | STILL OPEN (narrowed in pass 5) | The four accepted stores are the first vectors in the tree that verify a *prekey* signature, but each verifies, so none exercises a refusal. |
| AEAD: a whole-block plaintext | STILL OPEN | |
| Erasure: a persisted encoder of 65,536 chunks | STILL OPEN | |
| Protobuf `maxFields` | STILL OPEN | |
| The accepted side of `MAX_SKIPPED_STORE` | STILL OPEN | |
| Classical expiry (`MAX_SKIPPED_AGE`) | STILL OPEN | |
| A short buffer with an unknown version | STILL OPEN | G5-03; the page leaves it to the implementation. |
| The session's, the prekey store's and the initiator's stored-key rules | **NARROWED** | `peer-identity-not-canonical` and `identity-public-not-canonical` pin two of them, each with its own kind. `our_identity_public`, `pending_initial`'s `ephemeral_public`, the ratchet state's three positions and the initiator's own bundle check are still unpinned. |
| The prekey store's older versions, and `previous_kem` | STILL OPEN (new) | The manifest states both: every byte-carrying vector is v4, and no vector carries `previous_kem_present = 0x01`, so `len(4) \|\| kem_pair \|\| id(4) \|\| sig(64)` is exercised by nothing. PS-19 and PK-06 hold the four versions; PK-01 holds the retired KEM pair. |
| From `GAPS-2.md`: the sparse ratchet's state machine; the Double Ratchet's eviction, expiry and no-chain refusals | STILL OPEN (narrowed in pass 5) | |

**The reverse case, a vector with no spec behind it:** none. Every refusal,
field and accepted edge in the two new files is stated on the page it cites,
with the two exceptions of wording rather than substance recorded above: the
`fields` names (G7-01) and one vector's comment naming the wrong half of the
epoch relation (G7-06).

---

## 4. Not attempted, and why

Unchanged from `GAPS-6.md`, less one entry:

- ML-KEM-1024 and its incremental split (the Braid runs over `kem_double.py`);
- the end-to-end `Session`;
- prekey store operations other than the two rotations, which this pass added
  because the new rule puts an obligation on them: `create_prekeys`,
  `replenish`, `publish`, `publish_one_time_batch`, `publish_multi_use` and
  `establish_responder` are still not modelled (G7-04);
- group messaging and devices;
- full JSON-Schema validation;
- a session router;
- every citation of evidence in `threat-model/` and `security-properties/`
  (G5-07). No theorem, test or `CLAIMS.md` section was looked for.

**The library layout of the Braid's `key_pair` and `encaps` is no longer on
this list.** It is not something the reader failed to attempt; it is outside
the rule's stated scope, and the reader conforms by checking the field's
length (G5-02).

---

## 5. Deliberate faults

40 faults and one control were tried (`work/faults7.py`), each a one-line or
one-block textual change to a fresh copy of the reader, run with the full
runner. **38 were caught. 27 are caught by a vector file.** The two that were
not caught are the pair nothing in the tree can catch, and the page says so.

| | Tried | Caught | Caught by a vector file |
|---|---|---|---|
| The prekey store's identifier rules (F7-01 to F7-05) | 5 | 5 | 5 |
| The replay record's per-key bound, both sides (F7-06 to F7-11) | 6 | 6 | 4 |
| The session's epoch relation (F7-12 to F7-15) | 4 | 4 | 2 |
| The session's role rule (F7-16 to F7-20) | 5 | 5 | 4 |
| The refusal kind each rule gives (F7-21 to F7-26) | 6 | 4 | 3 |
| The signature rule itself (F7-27 to F7-32) | 6 | 6 | 3 |
| The remaining rules of the two formats (F7-33 to F7-40) | 8 | 8 | 6 |

- **F7-13**, the epoch relation's boundary moved from tags 7-10 to 6-10, failed
  nothing on the first run: no vector carries a session whose Braid is at tag 6
  or 7, and no case walked the boundary. **EP-01** was added for it and catches
  it. This is the pass's one hole, and it is recorded in section 3.
- **F7-25 and F7-26**, the session's and the prekey store's re-encode checks
  reported as `inconsistent` and `malformed` rather than as `non-canonical`,
  are clean and cannot be otherwise: a reader that accepts only canonical
  encodings never reaches either check, so no input distinguishes the two
  readings. The manifest says exactly this of `non-canonical`
  ("carried by no vector"), and the schema repeats it. They are faults the
  specification makes unobservable, not faults the reader missed.
- **F7-06** (the per-key bound counted over the whole record) and **F7-11**
  (the pre-sizing ceiling given one budget instead of two) are caught only by
  PS-22. The first is the reading the page's "The bound is counted per key
  rather than over the record as a whole" exists to rule out; the second is the
  check the manifest says no vector lands on.
- **F7-21** and **F7-27**, the signature rule reported as malformed and the
  rule dropped, are caught by nine cases each and by no vector -- the whole of
  the new rule's evidence in this reader is derived.
- **F7-39**, a reader outside the scope applying the `key_pair` content clause
  with a guessed layout, is caught by two session vectors and by BK-01: the two
  initiator sessions carry a Braid in tag 1, so a guessed layout refuses a
  state the page requires such a reader to accept. That is the fault G5-02's
  closure is about, and it is now caught by vectors rather than by a case.
- **Control C7-01**, a reader that checks the prekey store's length before its
  version byte, is clean: it fails nothing, as Rejection allows (G5-03).

The per-fault list, with the vectors and cases that failed, is in
`reader/README.md` and `work/faults7.txt`.

---

## 6. Isolation

- **What was read:** this directory and nothing else.
  - `tacenta-spec/`, all of it apart from the ADRs, of which only
    `ADR-0006-specification-is-normative.md` was opened, the brief for this
    pass having named its new point 7. ADR-0000 to ADR-0005, ADR-0007 and
    ADR-0008 were not opened.
  - `tacenta-test-vectors/` (`vectors/`, `schema/`, `conformance-manifest.md`,
    `README.md`);
  - `reader/`;
  - `GAPS-6.md` and `SOURCE-REVISION`. `GAPS.md`, `GAPS-2.md`, `GAPS-3.md`,
    `GAPS-4.md` and `GAPS-5.md` were not opened at all; their contents are
    known only through `GAPS-6.md`'s summary of them.
- **No read outside this directory.** Nothing outside it was read, listed or
  searched. Two commands produced output too large to display, and a copy of
  each was saved outside this directory; neither copy was opened, and both
  commands were re-run reading the same files from inside this directory.
- **Names treated as text.** The specification, the vectors README and the
  manifest name implementation files, tests, theorems and records
  (`tacenta-core`, `tacenta-model`, `tacenta-proofs/CLAIMS.md`,
  `LIMITATIONS.md`, `LABELS.md`, `AUTHENTICATION-BOUNDARY.md`,
  `Model.PersistedState`, `Model.Braid`, `libcrux-ml-kem`, the Rust runner and
  the differential harness). None was looked for (G5-07).
- **What was written:** only inside this directory:
  - `reader/`: `tacenta_reader/persistence.py`, the new
    `tacenta_reader/prekeys.py`, `tacenta_reader/__init__.py`, `run.py`,
    `cases_persistence.py`, `cases_stored.py`, the new `cases_signed.py` and
    `README.md`;
  - `GAPS-7.md`;
  - `work/`: run outputs, `check_new_vectors7.py`, `xref7.py`, `faults7.py`
    and `faults7.txt`.

  The per-fault copies were made under `work/faults7/`, each reaching the
  vectors through a symbolic link inside this directory, and removed after each
  run. Python wrote its usual `__pycache__` directories inside `reader/`.
- **What was not consulted:** no implementation (tacenta-core, tacenta-model,
  tacenta-proofs, the Rust runner, libcrux, libsignal), no git history, no
  other scratch files, and no web search. RFC 7748 section 5, FIPS 203
  sections 7.2 and 7.3, and the XEdDSA specification's verification procedure,
  all of which the pages cite, were used from knowledge. Nothing was fetched.
- **Unrelated context, not used.** The working environment again carried
  unrelated material: an index of notes from other work, which names several of
  the repositories this pass must not consult and summarises work on them, and
  a list of further material available. None of it was opened, and nothing in
  it was used for any reading or decision here. In particular, nothing in it
  was consulted about the prekey store, the signature rule or the two new
  vector files.

These are recorded in `reader/README.md` under "Isolation, pass 7".
