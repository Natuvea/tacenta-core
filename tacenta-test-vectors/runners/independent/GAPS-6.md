# Gap report, sixth pass: the reader against the current specification

The clean-room reader (`reader/`) was updated from `tacenta-spec` and
`tacenta-test-vectors` alone, against the tree as found in this directory:

- `SOURCE-REVISION` `c3a00471fbef23f514eca184aac56be7b76fbc8d`;
- `VERSION` `0.2.0`;
- everything under `CHANGELOG.md` `[Unreleased]`. Its Added section now opens
  with "`protocol/session-persistence.md`, Triple ratchet state: the refusals
  that format's reader gives", the answer to `GAPS-5.md` G5-01.

The fifth pass read `1dd174609bc5b008564bddef45bee43d71589761`.

Severity, as in the earlier reports:

- **BLOCKING**: cannot be implemented from the tree without guessing.
- **AMBIGUOUS**: more than one reading; a vector decided it, or nothing did.
- **MINOR**: wording, pointers, or a value findable only in the wrong place.

A hypothesis confirmed by a vector is still a gap.

**Baseline** (`python3 reader/run.py`, before any change): 530 PASS, 0 FAIL,
51 SKIP.

| | PASS | FAIL | SKIP |
|---|---|---|---|
| Vectors (34 files) | 326 | 0 | 51 |
| Derived cases (11 modules) | 204 | 0 | 0 |
| **Total** | **530** | **0** | **51** |

The 51 skips were the two new files, `persistence/triple-ratchet-state.json`
(18) and `braid-state.json` (33).

**Final run:**

| | PASS | FAIL | SKIP |
|---|---|---|---|
| Vectors (34 files) | 377 | 0 | 0 |
| Derived cases (11 modules) | 207 | 0 | 0 |
| **Total** | **584** | **0** | **0** |

All 51 new vectors passed on the first run of the new handlers. No vector
needed a value read from its bytes, and no layout was inferred:
`tacenta-test-vectors/README.md`, "The Triple Ratchet's state" and "The Braid's
state", describe every input, output, `fields` entry and refusal, and
`session-persistence.md` gives both formats. `work/check_new_vectors6.py`
(162 checks, no problems) confirms the 51 pass for the reasons the text gives
and not by accident (section 3).

**What changed in the reader:**

- **A reader error, fixed** (`persistence.py`, `triple_from_bytes`). The page
  has decided what pass 5 recorded as G5-01, and it decided against this
  reader: a `ratchet_state` or `spqr_state` whose own reader refuses it is
  *short or malformed* to the triple ratchet state, "whatever that reader's
  reason", an unrecognised inner version included, "and it is not passed
  through". This reader passed an inner wrong version through, which was
  reading (b) of G5-01, chosen while the page was silent. It now maps every
  inner refusal to malformed, as it already did for the session. PS-09 had
  asserted the old behaviour and is rewritten; PS-24 is new and states the
  decided rule. Fault F6-01 is caught by two vectors and by PS-24.
- **`triple.py`:** the Triple Ratchet's own initialisation, send and receive,
  with the agreement's results handed in (`init_halves`, `halves_send`,
  `halves_receive`), which is the shape the new file's `steps` drive.
  triple-ratchet.md, Initialisation, gives the split; Sending and receiving
  gives "Both run the classical half first and the sparse half second".
- **`run.py`:** handlers for `triple-ratchet-state` and `braid-state`:
  - stored bytes, checked against `fields`, against the layout the README
    composes them into, and against the named `refusal`;
  - the triple state's operations, from a new state named by `role` or from
    `start`, written as `output`, read back and written again, with the
    `-read-back` vector beside each;
  - the Braid's two `Ct2Sampled` steps, each one received Braid message, from
    stored `start` bytes and with no KEM.
- **Cases:** PS-24 (the decided rule), TR-11 (the Triple Ratchet's own send and
  receive, and the epoch the agreement names) and CR-19 (the sparse store's
  total bound as the page now states its evidence). PS-09 rewritten.

**No other change was needed.** The Braid's stored format, its twelve tags,
its semantic rules and both its refusal kinds were already implemented from
the page in pass 2 and extended in pass 5; the 33 braid vectors passed against
that code unchanged.

---

## 1. The earlier gaps

Counts for the gaps `GAPS-5.md` left open: **1 CLOSED, 9 STILL OPEN, 0
NARROWED.** Those gaps are G5-01 to G5-10, and G4-01, which pass 5 left open
as narrowed.

The gaps recorded as closed before are still closed: G-01 to G-28, G2-01 to
G2-12, G3-01 to G3-08 and G4-02 to G4-04. Each still has its case or vector,
and all pass.

### Re-assessed

| Gap | Status | Citation, and what changed in the reader |
|---|---|---|
| G5-01 The refusal kind of a triple ratchet state whose inner state has an unknown version | **CLOSED** | session-persistence.md, Triple ratchet state: "The reader refuses as a *wrong version* a first byte other than `0x01`, and as *short or malformed* everything else it refuses: ... and a `ratchet_state` or `spqr_state` that its own reader refuses, whatever that reader's reason. An unrecognised version inside a half is one of those reasons, and it is not passed through", with the reason (each format's version byte is its own namespace) and the parallel to the session. `CHANGELOG.md` `[Unreleased]` Added records the decision and names the two readings. The vectors README says the same, and `triple-ratchet-state.json` pins it with `classical-half-with-an-unknown-version` and `sparse-half-with-an-unknown-version`. **The reader was wrong and is fixed** (above). |
| G5-02 The Braid key pair's load check needs the delegated layout | STILL OPEN | session-persistence.md, Braid, still delegates `key_pair` and `encaps` to `libcrux-ml-kem` 0.0.10 and still requires a reader to find the `header` and `ek_vector` inside a `key_pair` (Semantic rules of the leaf formats, Braid). What is new is that the consequence is now recorded where a reader meets it: the vectors README says "What no vector in this file pins, then, is **the `key_pair` content rule of tags 1 to 4**", and the manifest's "Not covered" says the same and states that no accepted vector carries a `key_pair`. The 33 vectors bear that out: tags 1 to 4 appear only at a length both readers refuse (`key-pair-wrong-length`). The rule itself still cannot be implemented from the tree; this reader still runs it over its own KEM test double's layout. Fault F6-23 is caught only by BK-01. |
| G5-03 "Shorter than the fixed fields of the version the reader reads" when there is no one such version | STILL OPEN | session-persistence.md, Rejection, is unchanged, and now names two more formats whose fixed part varies (the Braid's is 2 bytes for `Failed` and 74 or more for a live state). The two new files leave it open in the same way: `braid-state.json` has `empty` and `version-only` (both `short-or-malformed`, both at version `0x01`) and `version-zero`/`version-two` at full length, so no vector offers a buffer that is both too short and wrongly versioned. Control C6-01 still fails nothing. |
| G5-04 The work a forged message costs, stated three ways | STILL OPEN | `threat-model/adversaries.md` ADV-01 ("make a receiver derive up to `MAX_SKIP` keys before it refuses them") and ADV-06 ("up to `MAX_SKIP` keys before the forgery is found"); `exclusions.md` EX-03 ("A skip is refused beyond `MAX_SKIP` before any key is derived"); ratchet.md, Skipped keys ("one message may store up to twice `MAX_SKIP` keys"). All four unchanged. The reader follows the protocol pages (CR-08). |
| G5-05 LIM-21: "until it is established again" | STILL OPEN | `security-properties/limitations.md` LIM-21 still reads "A malicious peer can fail the agreement. The session then refuses to encrypt or decrypt until it is established again", and no page re-establishes a session whose Braid has failed. `Failed` is terminal in the reader (BR-12, BR-18). |
| G5-06 ASM-13 and ASM-19 are "relied on by every requirement" | STILL OPEN | `threat-model/assumptions.md`: ASM-13 "Relied on by: every requirement, for the adversary it holds against", named by 2 of the 32; ASM-19 "every requirement, as a statement about `tacenta-core`; in particular ...", named by 13, which is exactly its "in particular" list. `work/xref6.py` (814 checks) reports these two and nothing else: every other assumption's list agrees exactly with the requirements that name it, every cited AS, ADV, ASM, EX, LIM and REQ identifier exists, every Status agrees with the limitations table, and the counts are 12 proved, 9 assumed and 11 tested only. ASM-17's list, which pass 5's script also flagged, is the qualified form "every requirement whose status is proved:" followed by the exact twelve, and is consistent. |
| G5-07 The evidence the requirements cite is outside the specification | STILL OPEN | Every Status in `security-properties/` still names a `tacenta-proofs/CLAIMS.md` section, a `LIMITATIONS.md` passage, a Lean theorem or a `tacenta-core` test, none of which is in the tree whose pages are normative. This revision adds citations rather than removing them: LIM-02 is closed by recording the model-level theorems in CLAIMS.md, and REQ-AUTH-02's status names the test that exercises its refusal. What the text allows was checked instead (`work/xref6.py`, and the protocol statements against the protocol pages). No theorem, test or CLAIMS.md section was looked for. |
| G5-08 The sparse ratchet's retention window: saturating on one page, not on the other | STILL OPEN | sparse-pq-ratchet.md, Retiring old epochs, still writes "every epoch `e` with `E < e + EPOCHS_KEPT`" without saturation; session-persistence.md, Semantic rules of the leaf formats, still writes "`e <= epoch < e + EPOCHS_KEPT`, the sum saturating". The advance to `u64::MAX` is refused, so the difference stays unobservable. |
| G5-09 The classical ratchet at `Nr = u32::MAX`, for a message numbered below it | STILL OPEN | ratchet.md, Sending and receiving, is unchanged: "refuse if ... `Nr` is now `u32::MAX` (`ChainExhausted`)" beside "A message whose ratchet key equals `DHr`, whose number `N` is below `Nr`, and whose key is not stored is not accepted", with no order between them, where sparse-pq-ratchet.md fixes one. The reader still gives the stale refusal first. |
| G5-10 REQ-AUTH-11 does not cite the rule that refuses a replay onto a chain the receiver has left | STILL OPEN | `security-properties/authentication.md` REQ-AUTH-11's three bullets and its "Rests on: ASM-19" are unchanged. Its status gained citations (`Proofs.KeyErasure.trySkipped_is_once`, `try_skipped_refines`, and "No theorem states that the model refuses every repeat"), none of which is the mechanism that refuses a replay after a Diffie-Hellman step. TM-02 still checks the requirement over a live Triple Ratchet session. |
| G4-01 A decoder of the composite header alone, and its trailing bytes | STILL OPEN | Unchanged since pass 5. message-format.md still defines the ratchet-message decoder and no decoder of the header on its own, and the vectors README still settles the vectors' verdicts rather than that decoder's behaviour ("No vector has bytes after the header"). The reader's header decoder still refuses them. |

### Closed in earlier reports, touched by this revision, still closed

- **G2-08** (the Braid's delegated `key_pair` and `encaps`): the delegation and
  its consequence for which tags move between implementations are unchanged,
  and the new vectors respect them: `encaps` is checked for length alone in
  tags 7 to 9, which the page says is the whole of its rule.
- **G2-12** (complete lists of semantic rules): both lists are still stated as
  complete, and the Braid's list is now exercised by vectors for every rule in
  it but the `key_pair` content rule (G5-02).
- **G3-07** (stale status statements): closed for `CHANGELOG.md`, but the same
  fault has appeared in the conformance manifest at this revision. That is
  G6-04 below, recorded as new rather than as a reopening, since it is a
  different file and a different sentence.

No earlier gap was judged wrong.

---

## 2. New gaps

### G6-01 The two persistence files' `sk` input is the same word for two different secrets (AMBIGUOUS)
- **Where:**
  - `tacenta-test-vectors/README.md`, "The ratchets' persisted states": "In `ratchet-state.json` a new state is named by `role` ... from `sk`, `our_pub`, `peer_pub` and `dh_out`";
  - the same file, "The Triple Ratchet's state": "A new state is named by `role`, `00` the party that sends first and `01` the party that receives first, from `sk` and `our_pub` (and, for `00`, `peer_pub` and `dh_out`)";
  - triple-ratchet.md, Initialisation: the expansion of `SK` into 64 bytes, "The first 32 initialise the Double Ratchet ... and the last 32 the sparse ratchet";
  - ratchet.md, Initialisation: "the same 32-byte secret `SK`, which under the Triple Ratchet is the classical half of the split secret".
- **Problem:**
  - In `ratchet-state.json` the input `sk` is the secret the Double Ratchet is initialised from, which under the Triple Ratchet is already the classical *half*. In `triple-ratchet-state.json` the same input name must be the unsplit `SK`, since that format initialises both halves.
  - The README does not say the difference, and uses one word for both. A reader that carried the first file's meaning across would initialise both halves from an already-split half, and every derivation in the file would differ.
  - The protocol pages settle it, but only by reading triple-ratchet.md rather than the file's own description: ratchet.md's sentence points the other way if read on its own.
- **Resolution:** the Triple Ratchet's initialisation is read as taking `SK` and splitting it (`triple.init_halves`). The four `role` vectors confirm it. A confirmed hypothesis is still a gap. Fault F6-06 is caught by those vectors and by no case, so nothing but the vectors would have found a wrong reading.

### G6-02 `vector.schema.json`'s `refusal` names two files where four now carry it (MINOR)
- **Where:**
  - `tacenta-test-vectors/schema/vector.schema.json`, `refusal`: "Carried only by an invalid vector, in vectors/persistence/ratchet-state.json and sparse-ratchet-state.json, where every invalid vector carries one";
  - `tacenta-test-vectors/README.md`, "The Triple Ratchet's state": "An invalid vector's `refusal` is `wrong-version` for a first byte other than `0x01` and `short-or-malformed` for everything else"; "The Braid's state", which refers to Rejection the same way;
  - the manifest, Session persistence, Layout: "or offers stored `bytes` to the reader, which accepts them with `fields` or refuses them with the `refusal` the vector names", said of both new files.
- **Problem:** every invalid vector in the two new files carries a `refusal`, and a runner must check it, but the field's own description still enumerates only the two files pass 5 added. The README's Status paragraph has the same shape: "In the two ratchet-state files an invalid vector also names its `refusal`."
- **Resolution:** the reader requires a `refusal` on every invalid vector in all four files and checks the kind. Nothing is ambiguous; the schema is a stale pointer.

### G6-03 Whether a Braid operations vector's `output` must read back is not stated (MINOR)
- **Where:**
  - `tacenta-test-vectors/README.md`, "The ratchets' persisted states": "A runner must write that state as `output`, and read `output` back to a state it writes as `output` again", and "Each valid built-by-operations vector has one of these beside it, whose id is its own with `-read-back` added";
  - the same file, "The Braid's state": "**Built by operations** ... `output` is the stored bytes of the state reached", and nothing more.
- **Problem:**
  - For the two ratchet files and, through "The two shapes are the ratchets' above", the Triple Ratchet's, the read-back obligation and the sibling vector are stated. The Braid's section states neither, and its two `ct2-sampled-*` vectors have no `-read-back` sibling.
  - So it is not said whether a Braid state reached by operations must be readable by the same format's reader. For `ct2-sampled-at-the-ceiling-fails` the answer matters least (the output is `Failed`), but for `ct2-sampled-below-the-ceiling-steps` the output is a live tag 0 state at `u64::MAX - 1`, one below the epoch the reader refuses.
- **Resolution:** the reader applies the obligation to the Braid too: it writes the state reached, reads it back and writes it again, and compares. Both vectors pass. A reader that did not check it would also pass, so no vector decides.

### G6-04 The conformance manifest says, in one section, both that the Braid's ceiling is pinned by vectors and that no vector pins it (MINOR)
- **Where:** `tacenta-test-vectors/conformance-manifest.md`, "Addition: reserved counter ceilings":
  - "Now that `Model.PersistedState.BraidState` states one, both sides of the Braid's reservation are pinned: `braid-state.json`'s `epoch-u64-max` is the reader refusing the reserved epoch, and its `ct2-sampled-below-the-ceiling-steps` and `ct2-sampled-at-the-ceiling-fails` drive transition (13) and the failure that replaces it one epoch later";
  - eleven lines later, in the same section: "The Braid's reservation is tested by its crate ... and no vector here pins it: no vector file holds a Braid state or drives the Braid's state machine."
- **Problem:** the second sentence is the state of the tree before this revision, and it contradicts the first. It also contradicts the README's Status ("**is now pinned from both sides**") and the manifest's own "Covered: the Triple Ratchet's and the Braid's states" table, which lists all four vectors under "Braid epoch ceiling, from the reader and from the transitions".
- **Resolution:** the reader follows the vectors, which exist. Recorded because a reader deciding what to implement from the manifest would be told twice, differently, whether this is pinned. This is the same kind of stale statement as G3-07, in a different file.

### G6-05 A Braid step's absent codeword has no zeroing rule (MINOR)
- **Where:**
  - `tacenta-test-vectors/README.md`, "The Braid's state": "Each step is one received Braid message, `epoch(8) || type(1) || chunk_present(1) || chunk_index(2) || chunk(32)`, the type byte being `AgreementType`'s";
  - message-format.md, Ratchet message, for the wire's three fields, and `vector.schema.json`: "when chunk_present is 00, the other two are its all-zero padding";
  - mlkem-braid.md, Messages, On the wire: "`chunk_index` ... zero without", "`chunk` ... zero without".
- **Problem:** the step layout is the wire's four agreement fields, but the README does not say that an absent codeword's index and chunk are zero there, and does not point at the page that does. The three sources above state it of the composite header, which is where those fields travel, not of this input.
- **Resolution:** read as the wire's rule, and checked as a vector-sanity condition rather than a protocol rule: a step with `chunk_present` `0x00` and a non-zero index or chunk is reported as a malformed vector. Both `ct2-sampled-*` steps carry no codeword and are zeroed, so the reading is consistent with the file but not decided by it.

---

## 3. Vector gaps: specified, but no vector pins it

Everything below is covered in this reader only by derived cases. Those test
the reader's reading of the text, not agreement with anyone else. The fault
evidence is in section 5.

### The 51 new vectors pass for the stated reasons

`work/check_new_vectors6.py` (162 checks, no problems):

- **Every invalid vector is refused with the kind it names**, in both files.
- **Each invalid vector pins its own rule.** With the triple state's role rule
  made vacuous, `halves-disagree-on-the-role` is accepted and no other vector
  in the file changes. With the Braid's `braid_invariant` made vacuous,
  exactly the eight vectors whose comments name a semantic rule are accepted
  and the framing refusals are unchanged. With the inner-refusal mapping
  removed, the two half-version vectors become `wrong-version` and
  `classical-half-malformed` does not move.
- **Every accepted Braid vector holds exactly the fields its tag's row lists,
  in that order**, carries no `key_pair`, has an epoch in `[1, u64::MAX)`, and
  has every coder sized for the value it streams.
- **The two `Ct2Sampled` vectors drive what they claim**: transition (13) from
  `u64::MAX - 2` to tag 0 at `u64::MAX - 1` carrying the authenticator, and the
  failure at `u64::MAX - 1`, where a message of any epoch and any type fails.

### New in this pass

- **The epoch a triple send names.** Every triple vector sends on the epoch the
  state is already at, so none distinguishes the epoch the agreement named from
  the sparse ratchet's own. Fault F6-09 was **missed on the first run** and is
  now caught only by TR-11, added for it.
- **`Ct2Sampled` checking the ceiling before it looks at the message.** Both
  `ct2-sampled-*` vectors carry a message at the next epoch, so a reader that
  checked the ceiling only on an advancing message passes them. F6-20 is caught
  only by BR-13.
- **The Braid's `key_pair` content rule** (G5-02). F6-23 is caught only by
  BK-01, as in pass 5. The README and the manifest now say this in the tree.
- **A Braid operations vector's read-back** (G6-03), which no vector decides.

### `GAPS-5.md`'s vector gaps, re-assessed

| Vector gap | Status | Note |
|---|---|---|
| `DecodeEC` on its own | STILL OPEN | |
| The repeated initial message | STILL OPEN | |
| The erasure encoder's stated edges | STILL OPEN (narrowed in pass 5) | The encoder over 65,536 chunks is still not pinned; the manifest gives the reason (two megabytes). |
| The Braid: MACs, `Init(1, SK)`, the state machine, `ek_vector` validation | STILL OPEN | mlkem-braid.md still says "No vector pins a MAC". Two of the thirteen transitions are now driven; the other eleven need the delegated KEM layout. |
| The persisted Braid | **CLOSED** | `braid-state.json` pins every tag's layout, the epoch range from both ends, every framing refusal with its kind, and every semantic rule but the `key_pair` content rule (G5-02). |
| The triple ratchet state | **CLOSED** | `triple-ratchet-state.json` pins the layout, both refusal kinds, the inner-refusal mapping, the role rule, and initialisation and one operation in each role. Not pinned: an operations vector whose last step is refused (`counter-exhaustion` through the composition), and the epoch a send names (above). |
| The session over the Braid | STILL OPEN | |
| The session's and the prekey store's persisted formats | STILL OPEN | The manifest's "Not covered" states it: the model states neither. |
| Establishment: the fingerprint, the record's refusals, per-key budget | STILL OPEN | |
| Establishment: `DecodeEC`'s canonical refusals, and G3-05 | STILL OPEN (narrowed in pass 4) | |
| Establishment: the FIPS 203 section 7.2 check | STILL OPEN | |
| Establishment: PQXDH `AD` and `CONCAT(ad, header)` | STILL OPEN | |
| XEdDSA: a `u` with no point, the cofactored-only signature, a non-canonical `R` not of small order, application signatures | STILL OPEN (narrowed in pass 5) | |
| AEAD: a whole-block plaintext | STILL OPEN | The manifest gives the reason. |
| Erasure: a persisted encoder of 65,536 chunks | STILL OPEN | |
| Protobuf `maxFields` | STILL OPEN | Unreachable, as the page argues. |
| The accepted side of `MAX_SKIPPED_STORE` | STILL OPEN | The README gives the reason (about 290 kilobytes). |
| Classical expiry (`MAX_SKIPPED_AGE`) | STILL OPEN | |
| A short buffer with an unknown version | STILL OPEN | The page leaves it to the implementation (G5-03). |
| The session's, the prekey store's and the initiator's stored-key rules | STILL OPEN | |
| From `GAPS-2.md`: the sparse ratchet's state machine; the Double Ratchet's eviction, expiry and no-chain refusals | STILL OPEN (narrowed in pass 5) | The Triple Ratchet's commit rules are still not pinned: the new file's steps are all accepted, so nothing exercises a half refusing. |

**The reverse case, a vector with no spec behind it:** none. Every refusal,
field and accepted edge in the two new files is stated on the page it cites,
with one exception of wording rather than substance: a step's absent codeword
is zeroed by the wire's rule rather than by the vectors README (G6-05).

---

## 4. Not attempted, and why

Unchanged from `GAPS-5.md`:

- ML-KEM-1024 and its incremental split (the Braid runs over `kem_double.py`);
- the end-to-end `Session`;
- prekey store operations;
- group messaging and devices;
- full JSON-Schema validation;
- a session router;
- the library layout of the Braid's `key_pair` and `encaps` (G5-02);
- every citation of evidence in `threat-model/` and `security-properties/`
  (G5-07). No theorem, test or CLAIMS.md section was looked for.

---

## 5. Deliberate faults

23 faults and one control were tried (`work/faults6.py`), each a one-line or
one-block textual change to a fresh copy of the reader, run with the full
runner. **22 were caught on the first run. The one that was missed, F6-09, is
caught after TR-11 was added for it, so all 23 are caught. 20 are caught by a
vector file.**

| | Tried | Caught | Caught by a vector file |
|---|---|---|---|
| The triple ratchet state's framing and refusal kinds (F6-01, F6-02, F6-04) | 3 | 3 | 3 |
| Its semantic rule and role reading (F6-03, F6-05) | 2 | 2 | 2 |
| The Triple Ratchet's operations (F6-06 to F6-09) | 4 | 4 | 3 (not F6-09) |
| The Braid's tag and epoch rules (F6-10 to F6-13) | 4 | 4 | 4 |
| The Braid's field and coder rules (F6-14 to F6-18) | 5 | 5 | 5 |
| The Braid's refusal kinds and framing (F6-17, F6-19) | in the two rows above | | |
| The two `Ct2Sampled` transitions (F6-20 to F6-22) | 3 | 3 | 2 (not F6-20) |
| The Braid key pair's content check (F6-23) | 1 | 1 | 0 |

- **F6-09**, a triple send that hands the sparse half the state's own epoch
  rather than the one the agreement named, failed nothing: in every vector the
  two are equal. TR-11 drives a send after an advance, where they differ, and
  catches it. This is the pass's one hole, and it is recorded in section 3.
- **F6-01**, the pass-5 behaviour the page has now decided against, is caught
  by `classical-half-with-an-unknown-version`,
  `sparse-half-with-an-unknown-version` and PS-24. The reader was wrong before
  this pass and no vector then existed to say so.
- **F6-20** and **F6-23** are caught only by cases, for the reasons section 3
  gives.
- **Control C6-01**, a reader that refuses a buffer shorter than two bytes as
  short even when its version byte is unknown, is clean: it fails nothing, as
  session-persistence.md, Rejection, allows.

The per-fault list, with the vectors and cases that failed, is in
`reader/README.md` and `work/faults6.txt`.

---

## 6. Isolation

- **What was read:** this directory, with one exception recorded below:
  - `tacenta-spec/`, all of it apart from the ADRs, which were not opened;
  - `tacenta-test-vectors/` (`vectors/`, `schema/`, `conformance-manifest.md`,
    `README.md`);
  - `reader/`;
  - `GAPS-5.md` and `SOURCE-REVISION`. `GAPS.md`, `GAPS-2.md`, `GAPS-3.md` and
    `GAPS-4.md` were not opened at all; their contents are known only through
    `GAPS-5.md`'s summary of them.
- **One read outside this directory.** The fault run was started as a
  backgrounded command whose output was redirected to `work/faults6.txt`. The
  output file of that backgrounded command, which is written outside this
  directory, was opened once to see whether the run had finished. It was empty,
  because the command's output had been redirected into this directory, and
  nothing was taken from it. It contained no specification, vector or
  implementation material; it was a record of a command this pass itself ran.
  No other path outside this directory was read, listed or searched.
- **Names treated as text.** The specification, the vectors README and the
  manifest name implementation files, tests, theorems and records
  (`tacenta-core`, `tacenta-model`, `tacenta-proofs/CLAIMS.md`,
  `LIMITATIONS.md`, `LABELS.md`, `Model.PersistedState`, `Model.Braid`, the
  Rust runner and the differential harness). None was looked for (G5-07).
- **What was written:** only inside this directory:
  - `reader/`: `tacenta_reader/persistence.py`, `triple.py`, `run.py`,
    `cases_persistence.py`, `cases_ratchet.py`, `cases_triple.py` and
    `README.md`;
  - `GAPS-6.md`;
  - `work/`: run outputs, `check_new_vectors6.py`, `xref6.py`, `faults6.py`
    and `faults6.txt`.

  The per-fault copies were made under `work/faults6/`, each reaching the
  vectors through a symbolic link inside this directory, and removed after each
  run. Python wrote its usual `__pycache__` directories inside `reader/`.
- **What was not consulted:** no implementation (tacenta-core, tacenta-model,
  tacenta-proofs, the Rust runner, libsignal), no git history, no other scratch
  files, and no web search. RFC 7748 section 5 and FIPS 203 sections 7.2 and
  7.3, which the pages cite, were used from knowledge. Nothing was fetched.
- **Unrelated context, not used.** The working environment again carried
  unrelated material: a short index of notes from other work, which names
  several of the repositories this pass must not consult, and a list of further
  material available. None of it was opened, and nothing in it was used for any
  reading or decision here.

These are recorded in `reader/README.md` under "Isolation, pass 6".
