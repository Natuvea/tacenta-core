# Gap report, third pass: the reader against the current specification

The clean-room reader (`reader/`) was extended from `tacenta-spec` and
`tacenta-test-vectors` alone, against the tree as found in this directory:

- `SOURCE-REVISION` `a9cf860ecfd5eca6951dff5471d1342875e85c1c`;
- `VERSION` `0.1.0`;
- everything under `CHANGELOG.md` `[Unreleased]`, whose first entry begins
  "`protocol/session-establishment.md`: `DecodeEC` accepts exactly one encoding".

Severity, as in `GAPS.md` and `GAPS-2.md`:

- **BLOCKING**: cannot be implemented from the tree without guessing.
- **AMBIGUOUS**: more than one reading; a vector decided it, or nothing did.
- **MINOR**: wording, pointers, or a value findable only in the wrong place.

A hypothesis confirmed by a vector is still a gap.

**Baseline** (`python3 reader/run.py`, before any change): 224 PASS, 0 FAIL,
106 SKIP. The 79 vectors and 145 derived cases passed. The 106 skips were the
eight vector files of kinds the reader did not read.

**Final run:**

| | PASS | FAIL | SKIP |
|---|---|---|---|
| Vectors (27 files) | 185 | 0 | 0 |
| Derived cases (9 modules) | 179 | 0 | 0 |
| **Total** | **364** | **0** | **0** |

**The eight new files needed no change to any module.** All 106 of their
vectors pass on the erasure, protobuf, AEAD and persistence modules the second
pass wrote from the text. Only runner handlers were added. The layouts those
handlers read are G3-01 to G3-04 below.

---

## 1. The earlier gaps

Counts for the 20 gaps `GAPS-2.md` left open: **20 CLOSED, 0 STILL OPEN, 0
NARROWED.** The 20 gaps `GAPS-2.md` had already closed are still closed. Each
still has its case or vector, and all pass.

### Re-assessed

| Gap | Status | Citation, and what changed in the reader |
|---|---|---|
| G-01 No citable spec revision | CLOSED | `VERSION` is `0.1.0`, and `CHANGELOG.md` has a `[0.1.0] - 2026-09-11` section: "The first citable revision". The tree read here is 0.1.0 plus `[Unreleased]`, named above. |
| G-09 Vector field names; 40/42 wording | CLOSED | `message-format.md` Ratchet message: "the input `chunk_data` is the field `chunk`". The three codeword inputs "are one optional value and not independent ones". `vector.schema.json` `inputs` points there. The same kind of gap reappears in the new files: G3-03 and G3-04. |
| G-21 Composing the session | CLOSED | `mlkem-braid.md` now states what the Braid sends and when: "The state machine", with Sending, Receiving, transitions (1)-(13) numbered on the page, "What a send and a receive return", "When an epoch completes" and "What the session does with them". The authenticator starts from `SK` ("Both parties run `Init(1, SK)`"). "What a receive ignores" and "Failure" cite the page's own numbers. **Reader:** new `braid.py` implements the machine over an injected KEM (`kem_double.py`, a test double, not ML-KEM). `braid.BraidAgreement` puts it behind `triple.py`'s agreement boundary. `triple.encrypt` and `decrypt` now run the Braid first, as the page says. BR-09 sees all thirteen transitions in runs with loss, and no other change of state. BR-17 runs two Triple Ratchet sessions over two post-quantum epochs, checking `session-persistence.md`'s epoch and role relations after every message. What is left is delegated on purpose (G2-08) or is wording (G3-06). |
| G-22 Braid epoch key derivation | CLOSED | `mlkem-braid.md` Parameters and derivations: `KDF_OK(K, e)` with a 32-zero-byte salt, `PROTOCOL_INFO \|\| ":SCKA Key" \|\| ToBytes(e)`, 32 bytes. `CONSTANTS.md` has rows for the salts and lengths. **Reader:** `braid.kdf_ok` cites the page. The old hypothesis was the same construction. `braid.json` passes, and BR-01 checks the layout byte for byte. |
| G-23 Ratcheted Authenticator | CLOSED | The same section gives `Init(e, s)`, `Update` (first 32 bytes `root_key`, last 32 `mac_key`), `MacHdr`/`MacCt` with `ToBytes(e)`, `Init(1, SK)` with `SK` whole, and when each is updated and checked. **Reader:** `braid.Auth`. `auth.json` passes, and its `from-zero` vector also checks as `Init(1, s)`. BR-02 covers the MACs, which no vector pins. |
| G-26 Last-resort fingerprint | CLOSED | `session-establishment.md` "The fingerprint" gives the HMAC key, the input layout, the integer widths, what is left out, when the fingerprint is computed, matched and recorded, and that the curve-key inputs are canonical. `CONSTANTS.md` has `LAST_RESORT_HANDSHAKE_LABEL`. **Reader:** `pqxdh.last_resort_fingerprint`, `check_last_resort` and `receive_last_resort` over the prekey store's `seen`. Cases LR-01 to LR-07. |
| G-27 Clamping before XEdDSA signing | CLOSED | `identities-and-devices.md` Signing: "`k = clamp(secret) mod q`", and "Why the clamp". **Reader:** docstring re-cited, behaviour unchanged. XS-01 rebuilds the signature from the page's table and shows that an unclamped signer's signatures do not verify. |
| G-28 Verifier accepted set by reference to a library | CLOSED | `identities-and-devices.md` Verifying a signature: six rules, "No step multiplies by the cofactor", and the departures from revision 1 in both directions. `CONSTANTS.md`'s sign-bit row points there, no longer to `verify_strict`. **Reader:** `xeddsa_verify` already enforced exactly these rules; the docstring now cites them. XS-02 to XS-04 build their own edge signatures, including one that holds only under the cofactored equation. |
| G2-01 Replacing a stored skipped key | CLOSED | `ratchet.md` Skipped keys; `sparse-pq-ratchet.md` Receiving; `key-deletion.md`: a skip deletes the held keys in its range, then appends the range in number order, with the current count. **Reader fix:** the sparse ratchet assigned into its store, which kept a replaced key's old place. It now deletes first and counts the resulting size against the bound (`spqr.receive`; CR-18). The Double Ratchet already did this. No vector would have caught it. |
| G2-02 CBC not defined | CLOSED | `message-format.md` Authenticated encryption: NIST SP 800-38A section 6.2, the chaining equations, key and IV positions, "The IV is not sent", and what is left to the primitives. `aead-encrypt.json` and `aead-decrypt.json` now pin it with SP 800-38A block values. AE-12 added. |
| G2-03 Stale provenance pointers | CLOSED | `ratchet.md` Message format and Sources now say the encodings are ours and recorded in `CONSTANTS.md`. The manifest credits initialisation to "Initialisation". |
| G2-04 Erasure sub-formats: `next`, codeword order | CLOSED | `session-persistence.md` Erasure coder sub-formats: "`next` is the index of the codeword the encoder issues next"; decoder codewords are "in the order in which each index first arrived", an order that "carries no meaning". `erasure-encoder-state.json` and `erasure-decoder-state.json` pin both. |
| G2-05 Session refusal kind for two inputs | CLOSED | `session-persistence.md` Session: a bad presence byte and a half its own reader refuses are both *malformed*, "made before the re-encode check". The reader already did this. |
| G2-06 Leaf-format field refusals | CLOSED | `session-persistence.md` Ratchet state and Sparse ratchet state now list the presence-tag, zeroing, `labels` and `direction` refusals as malformed. The reader already did this. |
| G2-07 Which epoch names the receiving chain | CLOSED | `sparse-pq-ratchet.md` Receiving: "The epoch the agreement's receive returns is not used". ADR-0007 decision 1 keeps it. The reader already did this. A stale changelog line is G3-07; the boundary paragraph still reads otherwise (G3-08). |
| G2-08 Braid `key_pair`/`encaps` are one library's layout | CLOSED | `session-persistence.md` Braid: "`key_pair` and `encaps` are delegated, and that limits which states move". Tags 1-4 and 7-9 cannot move between implementations; tags 0, 5, 6, 10 and 11 can. `CONSTANTS.md` names the consequence. The limitation remains, and is now stated as a deliberate delegation. **Reader:** the KEM double pads its own layouts to the stated lengths, so BR-15 round-trips all twelve tags. |
| G2-09 "Encrypted under `SK` (or a key derived from it)" | CLOSED | `session-establishment.md` Sending the initial message: "Nothing is encrypted under `SK` itself. The key comes from `SK` by this path", six numbered steps. |
| G2-10 "Range-checked the same way" | CLOSED | `ratchet.md` Sending and receiving: every stored number "is at most `u32::MAX - 1` and none can be out of range". The reader's now-unreachable check is kept. |
| G2-11 Zero-salt length (sparse ratchet) | CLOSED | `sparse-pq-ratchet.md` Derivations: "a 32-byte all-zero salt". |
| G2-12 Leaf semantic rules narrower than their principle | CLOSED | `session-persistence.md` Principles and "Semantic rules of the leaf formats": "Each list is complete", and a state that keeps every rule is accepted. ADR-0007 decision 2. The reader already enforced exactly the listed rules. CR-18 uses such a state. |

### Closed in `GAPS-2.md`, still closed

G-02 error taxonomy; G-03 check order; G-04 embedded ratchet message; G-05
initial-message refusals; G-06 bundle KEM length; G-07 presence/identifier
disagreement; G-08 identifier 0; G-10 AEAD, now also pinned by vectors; G-11
ratchet initialisation; G-12 `info` strings; G-13 expansion lengths; G-14 "up to
the header's counts"; G-15 edge behaviour; G-16 `MAX_SKIPPED_AGE`; G-17
`PROTOCOL_INFO` joining; G-18 sparse ratchet state machine; G-19
`split_secret`; G-20 combined key; G-24 the erasure code, now also pinned by
vectors; G-25 initial ciphertext key and AD.

No earlier gap was judged wrong.

---

## 2. New gaps

### G3-01 Layouts of the new vector kinds are not written down (MINOR)
- **Where:**
  - `vector.schema.json`, `result` and `inputs`;
  - `conformance-manifest.md`, "The erasure code, by vector" and "Session persistence";
  - the `source` strings of `erasure-encode.json`, `erasure-decode.json`, `erasure-encoder-state.json` and `erasure-decoder-state.json`.
- **Problem:**
  - Nothing says how these files lay out their inputs and outputs:
    - `indices` is a run of 16-bit big-endian indices;
    - `codewords` is a run of `index(2) || chunk(32)`;
    - `size`, `issued` and `stream_length` are 32-bit;
    - an encode `output` is the listed codewords' 32 bytes back to back, without indices;
    - a persistence vector gives either `message` and `issued`, meaning build the coder by operations, or `bytes`, meaning read the stored bytes.
  - The schema says an invalid vector "must be rejected". `erasure-decode.json` uses `result: invalid` for a decoder that holds no value, which is not a refusal. Only that file's `source` string says so.
- **Resolution:** Each layout is the only one the lengths allow. The codeword run is the persisted decoder's `codeword` layout (`session-persistence.md`). `invalid` is read as the `source` string says.

### G3-02 Two erasure-encoder edges the text does not cover (MINOR)
- **Where:** `mlkem-braid.md` The erasure code, Codewords. The manifest's "Not pinned" says so too.
- **Problem:**
  - For `k = 0`, "the polynomial of degree below `k` through the points" has no points. Nothing says what an encoder for zero bytes issues. `erasure-encoder-state.json` `zero-length-value` builds one but issues nothing.
  - Nothing says what encoding a value longer than 65,536 chunks does. `session-persistence.md` refuses such a persisted encoder, but the code page states no refusal.
  - The Braid never encodes either, so neither is observable in the protocol.
- **Resolution:** A zero-chunk encoder issues all-zero codewords (this reader's choice; the runner skips that comparison). A longer value is refused when the encoder is built.

### G3-03 Protobuf vector field names differ from the page's (MINOR)
- **Where:** `protobuf-profile.md` Ratchet message body and Prekey envelope (`ratchetKey`, `previousCounter`, `prekeyId`, `baseKey`, `identityKey`, `registrationId`, `signedPrekeyId`, `pqPrekeyId`); `protobuf-ratchet-body.json` and `protobuf-prekey-envelope.json` `fields` (`ratchet_key`, `previous_counter`, `prekey_id`, ...); `conformance-manifest.md` ("an absent `prekey_id`").
- **Problem:**
  - The schema says a runner "must check that the names match".
  - The page names the fields in camelCase, and the vectors in snake_case.
  - Nothing maps one to the other. `message-format.md` does that for `chunk_data`, but no page does it for these names.
- **Resolution:** A mechanical camelCase-to-snake_case mapping. Names are compared exactly, so an absent `prekeyId` must be absent.

### G3-04 The AEAD vectors' `ad` is the page's `AD` (MINOR)
- **Where:** `message-format.md` Authenticated encryption, which distinguishes `ad` from `AD = CONCAT(ad, header)`; the `ad` input of `aead-encrypt.json` and `aead-decrypt.json`.
- **Problem:**
  - The input is named `ad`, but it is what the page calls `AD`, the whole associated data given to HMAC.
  - Only the `session-associated-data` comment ("AD is CONCAT(ad, header)") shows this.
  - A reader who applies `CONCAT` to the input computes a different tag.
- **Resolution:** The input is `AD`. For the vector whose comment names `CONCAT`, the runner also checks that the input parses as `len(ad) || ad || composite header`.

### G3-05 Where a non-canonical `EncodeEC` key in an initial message is refused (AMBIGUOUS)
- **Where:**
  - `session-establishment.md`:
    - `DecodeEC` "refuses every one but the canonical encoding";
    - Primitives: "Keys in `EncodeEC` form, an initial message's `identity` and `ephemeral`, are checked by `DecodeEC` first";
    - The fingerprint: "A handshake is accepted only if `DecodeEC` accepts both".
  - `message-format.md` Initial message lists the decoder's refusals. For these two fields it lists only the curve byte, "a decode failure like the others". Rejection says a decoder rejects "any encoding that is not the canonical one".
- **Problem:** Two readings:
  - (a) the initial-message decoder applies `DecodeEC`, so a key with bit 255 set, or at or above p, is a decode failure;
  - (b) the decoder checks the curve byte, and establishment applies `DecodeEC`.

  The difference is observable:
  - `error-handling.md` makes decode failure a distinct outcome.
  - A repeated initial message on an existing session compares `ephemeral` byte for byte and "no other field". Under (b), one whose `identity` is re-spelled is accepted and its ratchet message decrypted. Under (a) it is refused at decode.
- **Resolution:**
  - Reading (b), following the decoder's list: `wire.decode_initial` checks the curve byte, and `pqxdh.handshake_keys` applies `DecodeEC`.
  - `accept_repeated_initial` compares `ephemeral` only, as written.
  - SE-03 and LR-06.
  - No vector decides this.

### G3-06 "Otherwise it takes (11)" (MINOR)
- **Where:** `mlkem-braid.md` The state machine, Receiving, `Ct1Acknowledged`: "If the decoder then holds all of `ek_vector`, it validates it, going to `Failed` on failure. Otherwise it takes **(11)**".
- **Problem:** "Otherwise" can attach to "holds all of `ek_vector`", which would complete the encapsulation with an incomplete key, or to "on failure". Only the first-mentioned condition is grammatically closest.
- **Resolution:** "Otherwise" means validation succeeded. The parallel `Ct1Sampled` bullet ("If the decoder now holds all ... failing that, it goes to `Failed`") supports this. With fewer codewords the state stays. BR-09 and BR-11.

### G3-07 Stale status statements (MINOR)
- **Where:**
  - `CHANGELOG.md` `[Unreleased]`, the G2-07 entry: "The page says so and leaves the departure undecided".
  - `README.md` Status: `identities-and-devices.md` "specifies the identity key's secret and application signatures".
- **Problem:**
  - In the same `[Unreleased]` section, `ADR-0007` decides the departure. `sparse-pq-ratchet.md` says ADR-0007 "keeps the departure".
  - The README leaves out the page's new Signing and Verifying sections, which the page's own status line lists.
- **Resolution:** Followed the pages and ADR-0007.

### G3-08 The sparse ratchet's boundary still says a receive returns the sender's epoch (MINOR)
- **Where:** `sparse-pq-ratchet.md` What this ratchet assumes: receiving "returns the epoch the sender was working in". `mlkem-braid.md` What a send and a receive return, and ADR-0007 decision 3.
- **Problem:** The Braid's receive taking (5) reports the epoch it completed, one past the epoch the `ct2` message was sent in. The Braid page records this as a departure from the published document, but the sparse page's description of the interface was not updated. The value is not used (`sparse-pq-ratchet.md` Receiving; `mlkem-braid.md` "The receiving epoch is not used"), so this is wording only.
- **Resolution:** The Braid page and ADR-0007 are followed; nothing reads the value.

---

## 3. Vector gaps: specified, but no vector pins it

Everything below is covered in this reader only by derived cases. Those test
the reader's reading of the text, not agreement with anyone else.

- **The ML-KEM Braid** (`mlkem-braid.md`):
  - `MacHdr` and `MacCt`. The page says so: "No vector pins a MAC".
  - `Init(1, SK)` with a real `SK`, and the order of `Update` before the `MacCt` check at (5).
  - The whole state machine: the send table and codeword indices; all thirteen transitions; what a receive ignores; the send and receive epochs, including ADR-0007 decision 3; every way into `Failed`; the epoch ceiling; encoder exhaustion inside the Braid.
  - The KEM split's `ek_vector` validation: the hash input order `ek_vector || rho`, which departs from the published document, and the added modulus check.
  - The persisted Braid, all twelve tags.
  - `composite.json` pins only that the header's last four fields round-trip, not that a Braid produces them.
- **The session over the Braid:** the sending epoch and output handed to the sparse ratchet; `AgreementFailed` and the adoption of a receive's move to `Failed`; `session-persistence.md`'s epoch and role relations as they hold during a run.
- **Session establishment:**
  - the last-resort fingerprint, the record's refusals and its per-key budget;
  - `DecodeEC`'s canonical-encoding refusals, and G3-05;
  - raw curve keys left to RFC 7748;
  - the FIPS 203 section 7.2 check on a bundle's KEM prekey;
  - the repeated initial message;
  - PQXDH `AD` and `CONCAT(ad, header)`.
- **XEdDSA:**
  - Signing is pinned by three vectors, and verification by thirteen verify-only vectors.
  - **Rule 3, "`A` is not of small order", is not pinned on its own.** All four `reject-small-order-A-*` vectors use `R` the identity and `s = 0`, and rule 6 refuses the identity `R` too. A verifier without rule 3 passes all sixteen vectors: deliberate fault F17 in this pass. It was missed, until XS-03 was given a small-order `A` with a full-order `R` and an equation that holds.
  - Also unpinned: a `u` whose `y` has no point; a signature over `R + T`, with `T` of small order, that holds only under the cofactored equation ("No step multiplies by the cofactor"); a non-canonical `R` whose point is not of small order.
  - Application signatures have no vector.
- **AEAD:** a whole-block plaintext, whose padding needs a second enciphered block. The manifest says why: no SP 800-38A value exists for it. The key and IV positions within the expansion are pinned only indirectly, by the ratchet vectors' `message_keys`.
- **Erasure code:** an encoder for zero bytes issuing anything (G3-02); a value over 65,536 chunks; a persisted encoder of 65,536 chunks (the manifest: two megabytes).
- **Protobuf:** `maxFields`, which the page shows can never be the limit reached.
- **Persistence:** the ratchet, sparse ratchet and triple states, the Braid, the session, and the prekey store v1 to v4, with every semantic rule. Only the erasure sub-formats have vectors.
- **Still unpinned from `GAPS-2.md`:**
  - Triple Ratchet commit rules, the non-contributory check and eviction retry;
  - the sparse ratchet's state machine beyond the chain step, including G2-01's replacement order;
  - the Double Ratchet's store bound, eviction, expiry, ceilings, `NoSendingChain` and `NoReceivingChain`;
  - the composite header's and initial message's negative cases, and the prekey bundle.

**The reverse case, a vector with no spec behind it:** none remains. `braid.json` and `auth.json` now have text.

---

## 4. Not attempted, and why

- **ML-KEM-1024 (FIPS 203) and its incremental split.**
  - The Braid runs over `kem_double.ToyIncrementalKem`. It keeps the split's sizes, the header's hash in the page's order, a valid `ByteEncode12` `ek_vector`, and implicit rejection. It is not ML-KEM.
  - Without FIPS 203 known-answer vectors in the tree, a Python ML-KEM could be checked only for self-consistency.
  - The persisted `key_pair` and `encaps` are the double's own layouts, padded to the stated lengths (G2-08).
- **The end-to-end `Session`**: the PQXDH handshake with a real KEM, `pending_initial` resend, `established_ephemeral`, and `Session::export`/`import` over live states. These pieces are implemented and tested separately: the Triple Ratchet over the Braid, the session format and its rules, the repeated-initial rule, the replay record, and `DecodeEC`.
- **Prekey store operations** (`create_prekeys` numbering, `replenish`, rotations, `publish` selection). They are specified in `key-deletion.md` and `session-persistence.md`, but were outside this pass's priorities. The replay record's check and recording are implemented over the store's `seen`.
- **Group messaging and devices.** Scaffolds; unspecified.
- **Full JSON-Schema validation.** Still only the top-level shape; no validator in the standard library.

---

## 5. Isolation

- **What was read:** only this directory: `tacenta-spec/`, `tacenta-test-vectors/` (`vectors/`, `schema/`, `conformance-manifest.md`), `reader/`, `GAPS.md`, `GAPS-2.md` and `SOURCE-REVISION`.
- **What was written:** only inside this directory. That is `reader/`, `GAPS-3.md`, and a `work/` scratch folder holding run outputs, a smoke script and the fault-injection script. Its per-fault copies of the reader are removed after each run.
- **What was not consulted:** no implementation (tacenta-core, tacenta-model, tacenta-proofs, the Rust runner, libsignal), no git history, no other scratch files, and no web search. Published standards were used as the pages cite them: FIPS 203's `ByteEncode12` layout, RFC 7748, RFC 8032, NIST SP 800-38A and the XEdDSA document.
- **One tool-output copy, not a read:** the output of an early command in this pass, a dump of the new vector files, was too long to display and the tooling saved a copy outside the directory. That copy was not opened; the command was re-run into `../work/`.
- **Unrelated notes, not used:** the working environment carried a short index of notes from other work. Nothing from it was used.

These are recorded in `reader/README.md` under "Isolation, pass 3".
