# Gap report, fifth pass: the reader against the current specification

The clean-room reader (`reader/`) was updated from `tacenta-spec` and
`tacenta-test-vectors` alone, against the tree as found in this directory:

- `SOURCE-REVISION` `1dd174609bc5b008564bddef45bee43d71589761`;
- `VERSION` `0.2.0`;
- everything under `CHANGELOG.md` `[Unreleased]`. Its Changed section begins
  "`protocol/session-persistence.md`, `protocol/session-establishment.md`,
  `protocol/message-format.md`: every curve public key a stored state holds
  must be canonical" (register item J-8). The `[0.2.0]` section carries the
  Braid key-pair check (J-4), the encoder's first 65,536 chunks (J-7) and the
  answers to G4-02 and G4-04.

Severity, as in the earlier reports:

- **BLOCKING**: cannot be implemented from the tree without guessing.
- **AMBIGUOUS**: more than one reading; a vector decided it, or nothing did.
- **MINOR**: wording, pointers, or a value findable only in the wrong place.

A hypothesis confirmed by a vector is still a gap.

**Baseline** (`python3 reader/run.py`, before any change): 402 PASS, 0 FAIL,
112 SKIP.

| | PASS | FAIL | SKIP |
|---|---|---|---|
| Vectors (32 files) | 214 | 0 | 112 |
| Derived cases (10 modules) | 188 | 0 | 0 |
| **Total** | **402** | **0** | **112** |

The 112 skips were the two new files, `persistence/ratchet-state.json` (62)
and `sparse-ratchet-state.json` (50). The 11 vectors added to existing files
already passed; `work/check_new_vectors5.py` confirms they pass for the
reasons the text gives (section 3).

**Final run:**

| | PASS | FAIL | SKIP |
|---|---|---|---|
| Vectors (32 files) | 326 | 0 | 0 |
| Derived cases (11 modules) | 204 | 0 | 0 |
| **Total** | **530** | **0** | **0** |

All 112 new vectors passed on the first run of the new handlers. No vector
needed a value read from its bytes, and no layout was inferred:
`tacenta-test-vectors/README.md`, "The ratchets' persisted states", describes
every input, output, `fields` entry and refusal.

**What changed in the reader:**

- **`persistence.py`:**
  - Stored curve public keys (session-persistence.md, Session, Semantic rules,
    "Stored curve public keys"):
    - the ratchet state's `dhs_pub`, a present `dhr_pub` and each skipped `dh` are refused as malformed;
    - the session's `our_identity_public`, `peer_identity_public`, `pending_initial`'s `ephemeral_public` and `established_ephemeral`'s key are refused as inconsistent;
    - the prekey store's `identity_public` is refused as malformed, in v1 to v4.
  - The Braid's `key_pair` in tags 1 to 4 is checked on load: `H(ek_vector || rho)` against the header's `H(ek)`, and the modulus check. Where the two sit inside `key_pair` is not stated, so the KEM test double's layout is used (G5-02).
  - The encoder writer writes every encoder, since none holds more than 65,536 chunks.
  - **A reader error, fixed.** The session reader passed an inner `triple_state` or `braid` wrong-version refusal through as a wrong version. The page says the session refuses such a half "whatever that reader's reason" as malformed. PS-16 had asserted the old behaviour. It is rewritten, and fault F5-48 is caught.
- **`wire.py`:** `is_canonical_curve_key`. The initiator's bundle check refuses a non-canonical identity key, signed prekey or present one-time prekey (`BundleRefused`).
- **`erasure.py`:** an encoder holds `chunk_0` to `chunk_65535` of a longer value, and no more.
- **`kem_double.py`:** `key_pair` is `ek_vector || header || z`, and decapsulation uses the stored `H(ek)`.
- **`spqr.py`:** the retention window's sum saturates, as the persisted rule states it. This is unobservable (G5-08).
- **`run.py`:** handlers for `ratchet-state` and `sparse-ratchet-state`:
  - stored bytes, checked against `fields` and the named `refusal`;
  - operations from a new state or `start`, with every step but an invalid vector's last accepted, and that last refused as counter exhaustion;
  - the state reached written as `output`, read back and written again;
  - the `-read-back` vector beside each;
  - the Diffie-Hellman stand-in's zeros exactly when no step is taken.
- **Cases:**
  - The new module `cases_stored.py` holds 15 cases: SK-01 to SK-09, RJ-01, BK-01, IN-01, IN-02, TM-01 and TM-02.
  - EC-13 is new.
  - CK-03 is rewritten: the initiator now refuses a re-spelled key herself.
  - PS-16 is rewritten.
  - CR-03 writes the clock's stop out instead of reading the reader's constant.
  - PS-08 gains an isolated duplicate-epoch check.
  - Fixtures in `cases_persistence.py` use canonical random keys and key pairs in the double's layout.

---

## 1. The earlier gaps

Counts for the gaps `GAPS-4.md` left open: **7 CLOSED, 0 STILL OPEN,
1 NARROWED.** Those gaps are G3-01, G3-03, G3-04, G3-07 (then narrowed) and
G4-01 to G4-04.

The gaps recorded as closed before are still closed: G-01 to G-28, G2-01 to
G2-12, G3-02, G3-05, G3-06 and G3-08. Each still has its case or vector, and
all pass.

### Re-assessed

| Gap | Status | Citation, and what changed in the reader |
|---|---|---|
| G3-01 Layouts of the erasure and persistence vector kinds | CLOSED | `tacenta-test-vectors/README.md`, "Vector layouts", now describes `erasure-encode.json` (`indices`, `stream_length`), `erasure-decode.json` (`size`, `codewords`, and "an invalid vector is a decoder that holds no value"), the erasure coders' persisted formats (`message`, `issued`, `bytes`) and the ratchets' persisted states. `vector.schema.json` `inputs` points there. |
| G3-03 Protobuf vector field names | CLOSED | README, "The protobuf profile", maps every snake_case name to the page's camelCase name. `vector.schema.json` `fields` lists the same mapping, and says "Names are compared in the vectors' spelling". The runner's mechanical mapping agrees. |
| G3-04 The AEAD vectors' `ad` is the page's `AD` | CLOSED | README, "The AEAD": "The input `ad` is the section's `AD` ... a runner gives it to the AEAD as it is and applies no `CONCAT`". The schema's `inputs` and the manifest's paragraph say the same. |
| G3-07 Stale status statements | CLOSED | `CHANGELOG.md` `[0.2.0]` Added now carries one G2-07 entry: "The page says so, and ADR-0007 keeps the departure". The Fixed entry records the correction. The "undecided" wording that remains describes what was corrected, and ADR-0007's bullet ("recorded as built and undecided are kept"), which is accurate. |
| G4-01 The decoder files' layout, and a decoder the page does not define alone | NARROWED | README, "The decoders": `encoding` is "the bytes handed to the decoder, whole"; the composite file is "a composite header alone ... with nothing after it"; the ratchet-message decoder "gives each vector the same verdict"; and "An invalid vector's `encoding` is refused as a decode failure ... and not as any other refusal" (also the schema's `result`). **Still open:** message-format.md still defines no decoder of the header alone. What one does with trailing bytes is stated only as an implementation's behaviour ("`tacenta-wire`'s `decode_composite` ... returns them"), which ADR-0006 makes non-normative, and "No vector has bytes after the header". The reader's header decoder still refuses them. |
| G4-02 Stored peer keys not held to the canonical rule | CLOSED | session-persistence.md, Session, Semantic rules: "Every curve public key the session stores is canonical"; the `established_ephemeral` shape rule; "Stored curve public keys", which names each field and its refusal; Semantic rules of the leaf formats, Ratchet state; Prekey store, Semantic rules. session-establishment.md, Receiving: "So are `established_ephemeral` and `peer_identity_public`, in every session establishment builds and in every session a reader accepts". **Reader:** pass 4's probe state (a responder whose `established_ephemeral` has bit 255 set) is now refused as inconsistent (SK-04, SK-05). `ratchet-state.json` pins the leaf's three positions. |
| G4-03 The manifest's stale statements about the encoder edges and the bundle | CLOSED | `conformance-manifest.md`, "The erasure code, by vector": the zero-length encoder row is pinned by `zero-length-value`, and "Not pinned: an encoder for a value longer than 65,536 chunks ... The text says such an encoder holds only the first 65,536 chunks". "Also covered, outside this directory": the bundle "[has] vectors under the Message format section below (... `prekey-bundle-decode.json`)". |
| G4-04 What follows `NotARepeatedInitial` | CLOSED | session-establishment.md, Receiving the initial message: "**A refused initial message changes nothing.** ... What happens next is the recipient's decision, not the session's". "For the two cases message-format.md names ... and for simultaneous initiation, the specification requires the refusal and nothing after it". error-handling.md names the condition, and `threat-model/exclusions.md` EX-10 excludes choosing among sessions. This is reading (a): the refusal is final for that session. The reader still has no session router (section 4). |

### Closed in earlier reports, touched by this revision, still closed

- **G3-02** (encoder edges): mlkem-braid.md, Codewords, now also says which
  chunks the longer encoder holds. The reader changed to hold the first
  65,536 (EC-13, F5-47).
- **G2-08** (the Braid's delegated `key_pair` and `encaps`): the delegation
  and its consequence are still stated. The new load check reaches inside
  `key_pair`, which is G5-02.
- **G2-12** (complete lists of semantic rules): the lists gained the
  stored-key rules and are still stated as complete.

No earlier gap was judged wrong.

---

## 2. New gaps

### G5-01 The refusal kind of a triple ratchet state whose inner state has an unknown version (AMBIGUOUS)
- **Where:** session-persistence.md:
  - Triple ratchet state: "this format does not know or care what is inside either one";
  - Rejection: "Each of the formats above carries its own error type, distinguishing 'wrong version' from 'short or malformed'";
  - Session: "a `triple_state` or `braid` that its own reader refuses, whatever that reader's reason" is malformed.
- **Problem:**
  - The session's mapping of an inner refusal is stated. The triple ratchet state's is not.
  - Its own version byte is recognised, but its `ratchet_state` or `spqr_state` may carry an unknown one. So there are two readings: (a) the triple state's reader reports malformed; (b) it passes the inner wrong version through.
  - No vector covers the triple ratchet state.
  - This reader had passed the inner refusal through at the session too, against the session's sentence. That is fixed (PS-16, F5-48).
- **Resolution:** reading (b) for the triple state (PS-09). The session maps every inner refusal to malformed.

### G5-02 The Braid key pair's load check needs the delegated layout (MINOR)
- **Where:**
  - session-persistence.md, Braid: "A `key_pair` holds, among the rest, the `header` and `ek_vector` its party sends ... The reader checks those two";
  - Semantic rules of the leaf formats, Braid: "In tags 1 to 4, the `header` and `ek_vector` that `key_pair` holds pass the validation";
  - CONSTANTS.md, "KEM key pair and encapsulation state lengths";
  - `[0.2.0]` Changed (J-4).
- **Problem:**
  - The check and its refusal (malformed) are stated. Where `header` and `ek_vector` sit inside the 11,872 bytes is not: the layout is `libcrux-ml-kem` 0.0.10's.
  - The page says an implementation without it "cannot find in `key_pair` the header and `ek_vector` that this format's semantic rules check". So the rule can be implemented only with that library.
  - The delegation is stated (ADR-0006, point 5), but the new rule adds a second thing another implementation cannot do.
  - mlkem-braid.md, The KEM split, states the validation; it says nothing about stored key pairs.
  - No vector covers the Braid.
- **Resolution:** implemented against this reader's KEM test double, whose `key_pair` is `ek_vector || header || z` (`kem_double.key_pair_view`, `persistence.KEY_PAIR_VIEW`). BK-01 covers the hash check, the modulus check with a matching hash, padding not checked, and `encaps` checked for length only. Faults F5-45 and F5-46 are caught by BK-01 only.

### G5-03 "Shorter than the fixed fields of the version the reader reads" when there is no one such version (MINOR)
- **Where:** session-persistence.md, Rejection, "A short buffer with an unknown version may be refused as either"; Prekey store, "Four versions are read"; Braid (fields per `state_tag`); Session (nested lengths).
- **Problem:**
  - The paragraph measures "too short" against "the fixed fields of the version the reader reads". A buffer with an unknown version byte names no version.
  - For the prekey store, which reads v1 to v4 with different fixed parts, take a buffer long enough for v1's fixed fields but short of v4's, with version `0x05`. It is short by v4, so either refusal conforms. It is not short by v1, so only a wrong version conforms.
  - The Braid's fixed part is 2 bytes for `Failed` and 74 or more for a live state. The session's depends on lengths it reads.
- **Resolution:** the reader reads the version byte first, so it reports a wrong version for any non-empty buffer with an unknown version. That conforms under both readings. RJ-01 accepts either refusal only below the smallest fixed part. Control C5-01, the length checked first, fails nothing.

### G5-04 The work a forged message costs, stated three ways (MINOR)
- **Where:**
  - `threat-model/adversaries.md`, ADV-01: forged messages "make a receiver derive up to `MAX_SKIP` keys before it refuses them"; ADV-06: "making the victim derive up to `MAX_SKIP` keys before the forgery is found";
  - `threat-model/exclusions.md`, EX-03: "A skip is refused beyond `MAX_SKIP` before any key is derived";
  - ratchet.md, Skipped keys: "one message may store up to twice `MAX_SKIP` keys"; The Diffie-Hellman ratchet, step 1; Sending and receiving (the step is taken before the skip to `N`);
  - sparse-pq-ratchet.md, Receiving; triple-ratchet.md, Sending and receiving ("Both run the classical half first and the sparse half second").
- **Problem:**
  - By the protocol pages, a forged header under a new ratchet key has two skips checked separately: one to `PN` (up to `MAX_SKIP` keys) and one to `N` (up to `MAX_SKIP` more). The step's two root derivations come between them, and the sparse half's skip of up to `MAX_SKIP` follows. Only then does the tag fail.
  - The threat-model pages state a bound of `MAX_SKIP` keys. EX-03's "before any key is derived" holds only for the refused skip itself: a skip to `N` beyond `MAX_SKIP` is refused after the skip to `PN` has stored its keys and the step has derived.
- **Resolution:** the protocol pages are followed (CR-08: 2 × `MAX_SKIP` stored by one message). No case asserts the threat-model figure.

### G5-05 LIM-21: "until it is established again" (MINOR)
- **Where:** `security-properties/limitations.md`, LIM-21: "A malicious peer can fail the agreement. The session then refuses to encrypt or decrypt until it is established again." mlkem-braid.md, Failure: from `Failed` a send or receive "leaves the Braid in `Failed`"; `Session` refuses both "once the Braid has failed". session-establishment.md: a refused initial message "does not establish a new session from the message, and does not replace itself".
- **Problem:** no page re-establishes a session whose Braid has failed. Recovery is a new session, which the application relates to the old one or not (EX-10). "Until it is established again" can be read as the same session recovering.
- **Resolution:** the protocol pages are followed. `Failed` is terminal (BR-12, BR-18).

### G5-06 ASM-13 and ASM-19 are "relied on by every requirement", but most requirements do not rest on them (MINOR)
- **Where:** `threat-model/assumptions.md`:
  - ASM-13, "Relied on by: every requirement, for the adversary it holds against";
  - ASM-19, "Relied on by: every requirement, as a statement about `tacenta-core`; in particular ...";
  - each requirement's "Rests on" in `security-properties/`.
- **Problem:**
  - Every other assumption's "Relied on by" list agrees exactly with the requirements that name it: 110 "Rests on" links checked by `work/xref5.py`.
  - ASM-13 is named by 2 of the 32 requirements, and ASM-19 by 13.
  - ASM-19's "in particular" list matches the 13 exactly. So each of the two assumptions has two records that disagree.
  - The rest of the numbering is consistent: every cited AS, ADV, ASM, EX, LIM and REQ id exists; each Status agrees with the limitations table; the counts are 12 proved, 9 assumed and 11 tested only; ASM-17's list is exactly the proved twelve.
- **Resolution:** none needed by the reader.

### G5-07 The evidence the requirements cite is outside the specification (MINOR)
- **Where:**
  - every "Status" entry in `security-properties/`, and every "Proofs" entry in `threat-model/assumptions.md` and `adversaries.md`;
  - `threat-model/assets.md`, AS-12: "tacenta-core's `AUTHENTICATION-BOUNDARY.md` states the rule for that implementation";
  - ASM-05: "prefix-free apart from two registered pairs (`tacenta-core/LABELS.md` ...)";
  - README.md and ADR-0006, point 1 (as amended): `threat-model/` and `security-properties/` are normative; `tacenta-core` is not.
- **Problem:**
  - Every status names a CLAIMS.md section, a LIMITATIONS.md passage, a Lean theorem or a `tacenta-core` test. None of them is in the tree whose pages are normative, and none can be checked from the specification.
  - Two statements lean on implementation files for their content, not only their evidence: which functions consume unauthenticated input (AS-12), and which strings are "the derivation labels" and which pairs are "registered" (ASM-05).
- **Resolution:**
  - What the text allows was checked. Each requirement's protocol statement was compared with the protocol pages, which found G5-04, G5-05 and G5-10. The numbering was cross-checked (G5-06).
  - ASM-05's label claim was checked against CONSTANTS.md's values (TM-01): of the fourteen info strings and keys it gives, exactly two are proper prefixes of another, `COMBINE_INFO` of `SPLIT_INFO` and `Tacenta SPQRChain` of `Tacenta SPQRChain Start`.
  - No theorem, test or CLAIMS.md section was looked for.

### G5-08 The sparse ratchet's retention window: saturating on one page, not on the other (MINOR)
- **Where:** sparse-pq-ratchet.md, Retiring old epochs: "keeps the chains and stored keys of every epoch `e` with `E < e + EPOCHS_KEPT`"; session-persistence.md, Semantic rules of the leaf formats, Sparse ratchet state: "`e <= epoch < e + EPOCHS_KEPT`, the sum saturating"; Principles, where epoch `u64::MAX` is one "its own retention window then reads as covering nothing".
- **Problem:** the operation's window is written without saturation, and the reader's rule with it. The advance to `u64::MAX` is refused, so the two keep the same chains in every reachable state, and the difference is unobservable. The Principles' reason for the refusal is true only of the saturating sum.
- **Resolution:** the reader's advance saturates, as the persisted rule does. `epoch-reaches-one-below-the-ceiling` passes either way.

### G5-09 The classical ratchet at `Nr = u32::MAX`, for a message numbered below it (MINOR)
- **Where:** ratchet.md, Sending and receiving: "refuse if ... `Nr` is now `u32::MAX` (`ChainExhausted`)", and "A message whose ratchet key equals `DHr`, whose number `N` is below `Nr`, and whose key is not stored is not accepted"; sparse-pq-ratchet.md, Receiving: "refused as out of order (`OutOfOrder`), or as counter exhaustion (`ChainExhausted`) once the counter is `u64::MAX`"; `vector.schema.json` `refusal`.
- **Problem:**
  - The sparse page fixes the refusal for every unstored number once the counter is at its ceiling. The classical page does not: a same-chain message numbered below `Nr = u32::MAX` meets both refusals, and the page names only the stale one's condition.
  - error-handling.md leaves the order of checks open. But the persisted-state vectors now make the refusal kind observable (`counter-exhaustion`).
  - `receive-at-nr-u32-max-refused` offers the message numbered `u32::MAX` itself, which only the ceiling refuses. So no vector decides.
- **Resolution:** the reader refuses such a message as out of order (the stale refusal first).

### G5-10 REQ-AUTH-11 does not cite the rule that refuses a replay onto a chain the receiver has left (MINOR)
- **Where:** `security-properties/authentication.md`, REQ-AUTH-11: "A session accepts each ratchet message at most once". Its three bullets: a stored key removed on use; a same-chain message below `Nr` refused; "The sparse ratchet removes a stored key when it is used, likewise". "Rests on: ASM-19". ratchet.md, Sending and receiving: a header whose key "differs from `DHr` ... take a DH ratchet step". sparse-pq-ratchet.md, Receiving: `OutOfOrder`, `NoChain`.
- **Problem:**
  - Once the receiver has taken a Diffie-Hellman step, a replayed message from its previous chain is neither stored nor on the current chain. The classical rules the requirement cites do not refuse it: they take a step.
  - By the text, the session refuses it through the sparse half: the message's `pq_n` is not past its epoch's counter and not stored (`OutOfOrder`), or the epoch is retired (`NoChain`). Failing that, the tag fails under a re-derived key, which rests on ASM-05 and ASM-06, not named.
  - The requirement holds by the text, but not by the mechanisms and assumptions it states.
- **Resolution:** TM-02 checks it over a live Triple Ratchet session. The replay is refused; the classical half alone would step; the sparse half refuses.

---

## 3. Vector gaps: specified, but no vector pins it

Everything below is covered in this reader only by derived cases. Those test
the reader's reading of the text, not agreement with anyone else. The fault
evidence is in section 5.

### The vectors added to existing files pass for the stated reasons

`work/check_new_vectors5.py` (33 checks, no problems):

- **The three decoder files.** Every invalid vector is refused with the canonical-key refusal, and decodes once that check alone is removed. The new vectors refuse a key equal to p in every position.
- **`xeddsa.json`.** The four `rule-3-only` vectors are refused, and accepted once rule 3 alone (A not of small order) is removed. The four small-order-A vectors with `R` the identity stay refused without rule 3, by rule 6.
- **`erasure-encode.json` `zero-length-value`.** An encoder of no chunks whose codewords are 32 zero bytes, by the `k = 0` sentence.

### New in this pass

- **The accepted side of `MAX_SKIPPED_STORE`** (2,000 keys) in the ratchet state. The README says so. F5-13 is caught only by PS-04.
- **The session's and the prekey store's stored-key rules**, and the session's mapping of an inner refusal to malformed. No vector covers either format. F5-25 to F5-30 and F5-48 are caught only by SK-04, SK-05, SK-08 and PS-16.
- **The initiator's own canonical check of a bundle.** F5-31 and F5-32 are caught only by CK-03 and SK-09.
- **The Braid key pair's load check** (G5-02). F5-45 and F5-46 are caught only by BK-01.
- **Which chunks an encoder over 65,536 chunks holds**, and its stored form. The manifest says so. F5-47 is caught only by EC-13.
- **Classical expiry** (`MAX_SKIPPED_AGE`). No persisted-state or ratchet vector ages a key out. F5-42 is caught only by DR-06.
- **A short buffer with an unknown version.** The README and G5-03 say so. Control C5-01 fails nothing, as the text allows.

### `GAPS-4.md`'s vector gaps, re-assessed

| Vector gap | Status | Note |
|---|---|---|
| The value p itself | CLOSED | Each decoder file now refuses p in every position (`*-equal-to-p`), and `ratchet-state.json` refuses it in all three stored positions. F5-23, the "above p" fault, is caught by `ratchet-state.json`. |
| `DecodeEC` on its own | STILL OPEN | |
| The repeated initial message | STILL OPEN | |
| The erasure encoder's stated edges | NARROWED | `zero-length-value` pins the zero-byte encoder. The encoder over 65,536 chunks is not pinned (above). |
| The Braid: MACs, `Init(1, SK)`, the state machine, `ek_vector` validation, the persisted Braid | STILL OPEN | The persisted Braid also gained the key-pair check (above). |
| The session over the Braid | STILL OPEN | |
| Establishment: the fingerprint, the record's refusals, per-key budget | STILL OPEN | |
| Establishment: `DecodeEC`'s canonical refusals, and G3-05 | NARROWED | Unchanged since pass 4. |
| Establishment: the FIPS 203 section 7.2 check | STILL OPEN | |
| Establishment: PQXDH `AD` and `CONCAT(ad, header)` | STILL OPEN | |
| XEdDSA: rule 3 alone, a `u` with no point, the cofactored-only signature, a non-canonical `R` not of small order, application signatures | NARROWED | Rule 3 alone is now pinned (`rule-3-only`, checked above). The rest are not. |
| AEAD: a whole-block plaintext | STILL OPEN | The manifest gives the reason. |
| Erasure: a persisted encoder of 65,536 chunks | STILL OPEN | |
| Protobuf `maxFields` | STILL OPEN | Unreachable, as the page argues. |
| Persistence: every format but the erasure sub-formats | NARROWED | The ratchet and sparse ratchet states are now pinned: layout, every leaf refusal with its kind, the stored-key rule, and the accepted edges. The triple ratchet state, the Braid, the session and the prekey store are not. |
| From `GAPS-2.md`: Triple Ratchet commit rules; the sparse ratchet's state machine; the Double Ratchet's store bound, eviction, expiry, ceilings and no-chain refusals | NARROWED | Now pinned through stored states: both ratchets' counter ceilings, the clock's stop, the epoch ceiling, the store bound's refused side, and sends, receives, Diffie-Hellman steps, skipped keys stored and used, epoch advance, retirement with stored keys, and the chains order. Still not: the commit rules, eviction, expiry, the no-chain and gap refusals, `SkippedStoreFull` and `TooManySkipped` in the sparse ratchet, and stored-key replacement order. |
| From `GAPS-2.md`: the composite header's and initial message's negative cases, and the prekey bundle | NARROWED | Unchanged since pass 4, apart from p (above). |

**The reverse case, a vector with no spec behind it:** none. Every refusal and
accepted edge in the two new files is stated on the page it cites.

---

## 4. Not attempted, and why

Unchanged from `GAPS-4.md`:

- ML-KEM-1024 and its incremental split (the Braid runs over `kem_double.py`);
- the end-to-end `Session`;
- prekey store operations;
- group messaging and devices;
- full JSON-Schema validation;
- a session router (G4-04 is closed; the application decides).

Added this pass:

- **The library layout of the Braid's `key_pair` and `encaps`** (G5-02).
- **Every citation of evidence in `threat-model/` and `security-properties/`**
  (G5-07). No theorem, test or CLAIMS.md section was looked for; they are not
  in this directory.

---

## 5. Deliberate faults

48 faults were tried, each a one-line or one-block textual change to a fresh
copy of the reader (`work/faults5.py`), run with the full runner, six at a
time. **All 48 were caught. 34 were caught by a vector file.** One control, a
change the text allows, failed nothing.

| | Tried | Caught | Caught by a vector file |
|---|---|---|---|
| Counter ceilings and the clock's stop (F5-01 to F5-09) | 9 | 9 | 9 |
| Wrong version versus short or malformed (F5-10, F5-11) | 2 | 2 | 2 |
| Ratchet state semantic and framing rules (F5-12 to F5-19) | 8 | 8 | 7 (not F5-13, a store of exactly 2,000) |
| Stored curve key canonicality (F5-20 to F5-32) | 13 | 13 | 5 (the ratchet state's; not the session's, the prekey store's or the initiator's) |
| Sparse ratchet state semantic and framing rules (F5-33 to F5-40) | 8 | 8 | 8 |
| Operations the vectors drive (F5-41 to F5-44) | 4 | 4 | 3 (not F5-42, expiry) |
| Braid key pair, erasure encoder, the session's inner refusal kind (F5-45 to F5-48) | 4 | 4 | 0 |

- **Before this pass's case changes**, F5-05 (the clock stopping at
  `u32::MAX - 2`) and F5-35 (two chains entries for one epoch) were caught
  only by vectors. CR-03 read the stop from the reader's own constant, and
  PS-08's duplicate-epoch check also broke another rule. Both cases were
  strengthened, and both now catch their fault too.
- **Control C5-01**, a reader that checks length before the version byte, is
  clean. The vectors and RJ-01 accept either refusal, as Rejection says.

The per-fault list, with the vectors and cases that failed, is in
`reader/README.md` and `work/faults5.txt`.

---

## 6. Isolation

- **What was read:** only this directory:
  - `tacenta-spec/`, all of it apart from ADR-0000 to ADR-0005, ADR-0007 and ADR-0008, which were not needed;
  - `tacenta-test-vectors/` (`vectors/`, `schema/`, `conformance-manifest.md`, `README.md`);
  - `reader/`;
  - `GAPS-4.md` and `SOURCE-REVISION`.

  `GAPS.md`, `GAPS-2.md` and `GAPS-3.md` were not opened beyond a line count.
- **What was written:** only inside this directory:
  - `reader/`: the modules and cases named above, the new `cases_stored.py`, and `README.md`;
  - `GAPS-5.md`;
  - `work/`: a dump of the two new vector files, run outputs, `check_new_vectors5.py`, `xref5.py`, `faults5.py` and their outputs.

  The per-fault copies were made under `work/faults5/`, each reaching the vectors through a symbolic link inside this directory, and removed after each run. Python wrote its usual `__pycache__` directories inside `reader/`.
- **What was not consulted:** no implementation (tacenta-core, tacenta-model, tacenta-proofs, the Rust runner, libsignal), no git history, no other scratch files, and no web search. RFC 7748 section 5 and FIPS 203 sections 7.2 and 7.3, which the pages cite, were used from knowledge. Nothing was fetched. Implementation files, tests and theorems named in the pages were treated as text.
- **Unrelated context, not used:** unrelated material was present in the working environment, a short index of notes from other work and a list of further material available. None of it was opened or used.

These are recorded in `reader/README.md` under "Isolation, pass 5".
