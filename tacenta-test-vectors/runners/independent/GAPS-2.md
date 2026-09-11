# Gap report, second pass: the reader against the current specification

The clean-room reader (`reader/`) was extended from `tacenta-spec` and
`tacenta-test-vectors` alone, against the tree as found in this directory:
`VERSION` `0.0.0`, everything under `CHANGELOG.md` `[Unreleased]`, whose first
entry begins "The decoders now enforce two of `protocol/message-format.md`'s
refusals at".

Severity, as in `GAPS.md`:

- **BLOCKING**: cannot be implemented from the tree without guessing.
- **AMBIGUOUS**: more than one reading; a vector decided it, or nothing did.
- **MINOR**: wording, pointers, or a value findable only in the wrong place.

A hypothesis confirmed by a vector is still a gap.

Final run (`python3 reader/run.py`): 79 vectors in 19 files, 79 PASS, 0 FAIL,
0 SKIP; 145 derived cases in 8 modules, 145 PASS. Total 224 PASS.

---

## 1. The old gaps

Counts: **20 CLOSED, 8 STILL OPEN, 0 WRONG.**

| Gap | Status | Citation, and what changed in the reader |
|---|---|---|
| G-01 No citable spec revision | STILL OPEN (MINOR) | `VERSION` is still `0.0.0` and `CHANGELOG.md` still has only `[Unreleased]`. This report names the revision by the changelog's first line. |
| G-02 Normative content deferred to code; no error taxonomy | CLOSED | `README.md` "Normative status"; `error-handling.md` "What is required" and "What is left to an implementation": refusals required, decode failure distinct from authentication failure, persistence kinds named, names and check order left free. Deferrals that remain are tracked individually: G-21 to G-23, G-28, G2-08. Reader: refusal classes renamed after the pages' parentheses; the persistence kinds are implemented. |
| G-03 Order of decoder checks | CLOSED | `error-handling.md`: the order of checks is left to an implementation "unless a page fixes one". The reader keeps framing first, which is consistent with `message-format.md`'s "should reject a bundle ... on the type byte". |
| G-04 Embedded `ratchet_message` versus the vectors | CLOSED | `message-format.md` Initial message: the decoder "does not validate it: it may be empty, or not a ratchet message at all". Reader: the opt-in strict mode, a hypothesis, is removed; IM-08 rewritten from the sentence. |
| G-05 Initial-message refusals not enumerated | CLOSED | `message-format.md` Initial message: the full refusal list, the `EncodeEC` curve-byte refusal "is a decode failure", and the ciphertext length is refused at decapsulation, "not a decode failure". Reader: behaviour unchanged. IM-05 now cites the sentence. Added `pqxdh.check_kem_ciphertext` and IM-09. |
| G-06 Bundle KEM key length check implied | CLOSED | `message-format.md` Prekey bundle: "refuses a `kem_prekey_len` other than the encapsulation-key length"; `CONSTANTS.md` "Bundle KEM prekey length". Reader unchanged; PB-08 cites it and adds 1,569. |
| G-07 Which layer refuses presence/identifier disagreement | CLOSED | `message-format.md` Prekey bundle: "The decoder does not compare the two: such a bundle decodes". The initiator refuses it. Reader unchanged; PB-10. |
| G-08 Identifier 0 in non-optional positions | CLOSED | `message-format.md` Key identifiers: "Neither decoder looks at an identifier's value"; the initiator does not check, and the recipient refuses as unknown. Added IM-10 and PB-15. |
| G-09 Vector field names; 40/42 wording | STILL OPEN (MINOR) | The 40/42 figures are reconciled in `triple-ratchet.md` (2 + 40). The vectors still name the codeword `chunk_data` against the spec's `chunk`, and still flatten presence, index and data into independent inputs. |
| G-10 AEAD not specified | CLOSED | `message-format.md` "Authenticated encryption": padding, `HMAC-SHA256(mac_key, AD || ciphertext)`, 32-byte tag appended, the four receiver steps, one failure. Reader: new `aes.py` (FIPS 197) and `aead.py`; `cases_aead.py`. |
| G-11 Ratchet initialisation | CLOSED | `ratchet.md` Initialisation, both roles. Reader: `init_initiator`/`init_responder` rewritten from the text. The result is the same as the old hypothesis H. |
| G-12 Where `info` strings are recorded | CLOSED | `ratchet.md` Derivations: "free choices, recorded at tier `ours` in CONSTANTS.md". Stale residue elsewhere on the page is G2-03. |
| G-13 Message-key expansion lengths | CLOSED | `ratchet.md` Derivations: "a 32-byte zero salt ... into 80 bytes", split 32/32/16. |
| G-14 "Up to the header's counts" | CLOSED | `ratchet.md` DH ratchet step 1: "from `Nr` up to the header's `PN`, exclusive", checked against `MAX_SKIP` on its own. |
| G-15 Edge behaviour (a)-(e) | CLOSED | (a) `NoSendingChain` (Sending and receiving). (b) the same-chain refusal (Sending and receiving, plus the new vector `reject-same-chain-duplicate`). (c) "A refused receive may already have moved the state"; callers run on a copy (`triple-ratchet.md` commit rules). (d) step 1 applies only "If there is a receiving chain". (e) "push the store past this bound" read with `key-deletion.md`'s "storing a key for a pair already held replaces it", so the resulting size counts. **Reader changed for (d)**: `MAX_SKIP` on `PN` is no longer checked without a receiving chain (CR-07). Ratchet operations are now pure functions returning a candidate state. |
| G-16 `MAX_SKIPPED_AGE` boundary | CLOSED | `ratchet.md` Skipped keys: count at the start of the storing receive, increment at the end of each accepted receive after the lookup, delete at age "at least `MAX_SKIPPED_AGE`", clock stops at `u32::MAX - 1`. `CONSTANTS.md` agrees. **Reader changed: the old hypothesis (`>`) was one receive too late.** DR-06 rewritten; CR-03 covers the clock. |
| G-17 `PROTOCOL_INFO` joining | CLOSED | `sparse-pq-ratchet.md` Derivations: "immediately followed by its own suffix, with no separator"; salts, inputs, 96/64-byte outputs and their order. `CONSTANTS.md` no longer contradicts itself (the `SPLIT_INFO` row). |
| G-18 Sparse ratchet state machine | CLOSED | `sparse-pq-ratchet.md` Sending (counter's new value is input and number; the epoch the agreement named; `NoChain`; `u64::MAX` usable), Receiving (`OutOfOrder`, `ChainExhausted`), Retiring (`E < e + EPOCHS_KEPT`). Reader: named refusals, 64-bit ceilings, eviction (CR-12..CR-17). |
| G-19 `split_secret` | CLOSED | `triple-ratchet.md` Initialisation: 32-byte zero salt, `SK`, `SPLIT_INFO`, 64 bytes; first 32 to the Double Ratchet, last 32 to the sparse ratchet (`A2b` initiator). Reader: halves assigned (TR-01). |
| G-20 Combined key length and use | CLOSED | `triple-ratchet.md` What the combination must be: 32 bytes, "It is not itself the encryption key"; the message-key expansion applies. TR-02. |
| G-21 Composing the session | STILL OPEN, narrowed (BLOCKING) | Now stated: the meaning of the header fields (`triple-ratchet.md` Sending and receiving; `sparse-pq-ratchet.md` Sending), `chunk_index` as the codeword index (`mlkem-braid.md` Codewords), the initiator's fresh ratchet key pair (`ratchet.md` Initialisation), the commit rules and the non-contributory check. Still missing from the tree: what the Braid sends and when (its state machine, sections 2.2-2.6 of the external document), and how the authenticator is initialised "from `SK` directly". `mlkem-braid.md`'s "What a receive ignores" and "Failure" refer to transitions (1)-(13) numbered only in that external document. Reader: composition implemented with the agreement as an injected boundary (`triple.py`). |
| G-22 Braid epoch key derivation | STILL OPEN (BLOCKING) | `mlkem-braid.md` still "does not restate the protocol". The tree says only that the epoch key "is derived from the KEM shared secret and the epoch alone". Salt, input and length are still unstated. Hypothesis still confirmed by `braid.json`. |
| G-23 Ratcheted Authenticator | STILL OPEN (BLOCKING) | Only "MAC. HMAC-SHA256" was added. The update construction, output order, MAC inputs for `:ekheader`/`:ciphertext` and initialisation are still not in the tree. |
| G-24 GF(2^16) and the erasure code | CLOSED | `mlkem-braid.md` The erasure code (field representation, reduction, chunks, systematic codewords, the parity formula, first-copy-wins decoding, encoder exhaustion); `CONSTANTS.md` polynomial `0x1100B`. Reader: constant re-cited; new `erasure.py`; `cases_erasure.py`. |
| G-25 Initial ciphertext key and AD | CLOSED | The key path: `triple-ratchet.md` (split; "It covers the ratchet message inside an initial message") and `ratchet.md` Initialisation. The AD: `message-format.md` Associated data, "`ad` is the associated data that page defines". Outer fields bind through `SK` (`session-establishment.md` Replay). The non-committal wording left behind is G2-09. |
| G-26 Last-resort fingerprint | STILL OPEN (now AMBIGUOUS) | `session-establishment.md` Replay and `key-deletion.md` still name only the fields. Hash, encodings and order are unstated. Lowered from BLOCKING: the refusal behaviour works with any injective fingerprint, and `session-persistence.md` says stores are "read back by the same code that wrote them", so only store bytes would differ. |
| G-27 Clamping before XEdDSA signing | STILL OPEN (MINOR) | `identities-and-devices.md` says the same 32 bytes serve as the X25519 scalar, "clamped when used", and as "the XEdDSA private key". The clamp is stated only for the X25519 role. Clamp-then-sign is still confirmed only by `xeddsa.json`. |
| G-28 Verifier accepted set by reference to a library | STILL OPEN (AMBIGUOUS) | `CONSTANTS.md`'s sign-bit row still says `verify` "narrows it through `verify_strict`". The fuller statement is in ADR-0002, which `README.md` now calls not normative, so the normative text says less than before. Unchanged in the reader. |

No old gap was judged WRONG. Every one described the tree as it then stood.

---

## 2. New gaps

### G2-01 Replacing a stored skipped key: stored count and store position (AMBIGUOUS)
- **Where:** `key-deletion.md` What this implementation does: "storing a key for a pair already held replaces it". `ratchet.md` Skipped keys (expiry by stored count; eviction ties "going to the key stored first"). `session-persistence.md` Ratchet state: entries "in the order the keys were stored".
- **Problem:** When a skip re-stores a `(ratchet key, n)` pair already held, nothing says:
  - whether the entry takes the current count as its stored count or keeps the old one;
  - whether it moves to the end of the store order.

  Both are observable. The first decides when the key expires, so whether a delayed message is accepted. The second decides eviction ties and the persisted order. The vector `peer-revisits-ratchet-key` performs exactly such a replacement but pins only message keys.
- **Resolution:** Reader choice: a replacement is a new store, with the new count, placed last (`ratchet._store`). Not decided by any vector.

### G2-02 CBC mode is named, not defined or cited (MINOR)
- **Where:** `message-format.md` Authenticated encryption: `AES-256-CBC-Encrypt(enc_key, iv, padded)`.
- **Problem:** FIPS 197 defines the block cipher only. The chaining mode has no definition or reference in the tree. The page says it "defines the behaviour", and CBC is the one piece it does not define.
- **Resolution:** Textbook CBC (`C_i = E(P_i xor C_(i-1))`, `C_0 = IV`), checked for structure by AE-04. AES itself is checked against FIPS 197 Appendix C.3 (AE-00).

### G2-03 Stale provenance pointers on `ratchet.md` and in the manifest (MINOR)
- **Where:**
  - `ratchet.md` Message format: encodings "pinned in the conformance manifest".
  - `ratchet.md` Sources, last paragraph: byte-level conventions "determined under the interoperability research boundary and recorded in the conformance manifest".
  - `conformance-manifest.md` Double Ratchet: "Session initialisation | Sending and receiving".
- **Problem:** The same page's Derivations, `message-format.md` and `CONSTANTS.md` say these values are tier `ours` and recorded in `CONSTANTS.md`. The manifest credits initialisation to a section that does not contain it; the page now has an Initialisation section.
- **Resolution:** Followed Derivations and `CONSTANTS.md`.

### G2-04 Erasure sub-formats: `next` undefined, codeword order unstated (MINOR)
- **Where:** `session-persistence.md` Erasure coder sub-formats: `encoder = next(2) || exhausted(1) || ...`; `decoder = ... || codeword[count]`.
- **Problem:**
  - `next` is never defined (the next index to issue, or the last one issued). It can be inferred only from the rule "exhausted only when `next` is `u16::MAX`" together with `mlkem-braid.md` Encoder lifetime.
  - The ratchet and sparse-ratchet formats say whether their list order means anything. The decoder's codeword list says nothing.
- **Resolution:** `next` is the next index to issue. Codewords are kept in arrival order. Decoding does not depend on the order.

### G2-05 Session refusal kind for two inputs (MINOR)
- **Where:** `session-persistence.md` Session and Rejection; `error-handling.md` ("A stored state's refusal says which kind it is").
- **Problem:** The kind is not stated for:
  - (a) a `pending_initial_present` or `established_ephemeral_present` byte outside `0x00`/`0x01`. It could be *malformed*, or *non-canonical* through the re-encode check. The prekey store says malformed for its own presence bytes; the session does not.
  - (b) a session whose embedded `triple_state` or `braid` its own leaf reader refuses. It could be *malformed*, as the leaf reader reports, or *inconsistent* under "Each half satisfies its own crate's invariant".
- **Resolution:** *Malformed* in both cases (PS-16).

### G2-06 Leaf-format field refusals implied only by "Canonical" (MINOR)
- **Where:** `session-persistence.md` Ratchet state and Sparse ratchet state; Rejection.
- **Problem:** Nothing lists as a refusal:
  - a presence tag other than `0x00`/`0x01`;
  - an absent key or chain that is not zeroed;
  - an unknown `labels` or `direction` tag.

  Each follows only from the Canonical principle. The prekey store ("A presence byte is `0x00` or `0x01` and nothing else") and the erasure encoder (`exhausted`) state theirs.
- **Resolution:** All refused as *malformed* (PS-03, PS-07).

### G2-07 Which epoch names the sparse ratchet's receiving chain (AMBIGUOUS)
- **Where:** `sparse-pq-ratchet.md`, What this ratchet assumes: receiving "returns the epoch the sender was working in". Receiving: "the receiving chain for the named epoch". `message-format.md`: `pq_epoch`.
- **Problem:** The agreement returns an epoch on receive, and the header also carries `pq_epoch`. The page never says which one selects the chain, what the returned epoch is used for, or what happens when the two differ.
- **Resolution:** The header's `pq_epoch` selects the chain; the returned epoch is not used (`triple.decrypt`).

### G2-08 Braid `key_pair` and `encaps` are one library's serialisations (MINOR)
- **Where:** `CONSTANTS.md` "KEM key pair and encapsulation state lengths". `session-persistence.md` Braid: "no structure this page relies on".
- **Problem:** A second implementation can read and write the Braid format with these fields as opaque, length-checked bytes. It cannot produce or use them without that library's layout. ADR-0006 point 5 asks for the consequence to be named; only the version-bump consequence of a library change is.
- **Resolution:** Opaque, length-checked (PS-14).

### G2-09 "Encrypted under `SK` (or a key derived from it)" (MINOR)
- **Where:** `session-establishment.md` Sending the initial message.
- **Problem:** The wording still does not commit. Other pages now fix the key path (G-25), so this page reads as looser than the protocol.
- **Resolution:** Followed `triple-ratchet.md` and `ratchet.md`.

### G2-10 "Range-checked the same way" for stored skipped-key numbers (MINOR)
- **Where:** `ratchet.md` Sending and receiving: "The numbers skipped keys are stored under are range-checked the same way (`ChainExhausted`)".
- **Problem:** "The same way" does not say which value is refused. The page notes the check is unreachable, so this is wording only.
- **Resolution:** A stored number of `u32::MAX` or more is refused.

### G2-11 Zero-salt length on the sparse ratchet page (MINOR)
- **Where:** `sparse-pq-ratchet.md` Derivations: "Initialisation takes an all-zero salt".
- **Problem:** No length is given, while `ratchet.md` says "32-byte" and `session-establishment.md` says "the length of the hash output". HMAC makes every zero salt up to 64 bytes equivalent, so this is harmless.
- **Resolution:** 32 zero bytes. `spqr.json` does not exercise initialisation.

### G2-12 Leaf semantic rules are narrower than their principle (MINOR)
- **Where:** `session-persistence.md` Principles, "Validated, not only parsed": a decoder "can still hand back a state no constructor builds". Semantic rules of the leaf formats: "The rules are these".
- **Problem:** The listed rules accept states no operation produces. The principle says such states are refused; the list is closed. A reader cannot tell whether it may refuse more. Examples:
  - a ratchet state with `nr > 0` and no receiving chain, or `ns > 0` and no sending chain;
  - a sparse ratchet with a stored key numbered at or past its chain's counter, or numbered 0.
- **Resolution:** The reader enforces exactly the listed rules and no more.

---

## 3. Vector gaps: specified, but no vector pins it

Everything below is covered in this reader only by derived cases, which test
the reader's reading of the text and not agreement with anyone else.

- **AEAD** (`message-format.md`): encryption, the tag input, padding and every refusal. No vector at all; AES is checked against FIPS 197 C.3 only.
- **Erasure code**: chunking, systematic and parity codewords, decoding from any `k`, first-copy-wins, encoder exhaustion. Field arithmetic and interpolation are pinned; nothing above them is.
- **Triple Ratchet composition**:
  - the split halves' assignment (`split.json` pins 64 bytes, not which half goes where);
  - combine then expand then AEAD;
  - the commit rules;
  - the non-contributory check on every receive;
  - eviction and retry.
- **Sparse ratchet**: initialisation (`Chain Start`), the root step, the send counter and chain choice, retention, `NoChain`/`OutOfOrder`/`ChainExhausted`, the total bound, eviction. `spqr.json` pins only the chain step.
- **Double Ratchet**:
  - `MAX_SKIPPED_STORE` and eviction order;
  - the exact expiry boundary and clock ceiling;
  - counter ceilings;
  - `MAX_SKIP` on `PN` (and its absence without a receiving chain);
  - `NoSendingChain`, `NoReceivingChain`;
  - replacement of held pairs (G2-01).

  The vectors cover initialisation, derivations, expansion, `MAX_SKIP` on `N` and the same-chain duplicate.
- **Wire refusals**:
  - no negative vectors for the composite header (`ag_type` range, presence byte, zero padding, truncation);
  - the initial-message curve byte, overruns, identifier 0 and ciphertext length;
  - the prekey bundle as a whole (no bundle vectors, as the manifest says);
  - `CONCAT(ad, header)`;
  - PQXDH `AD`.
- **All persistence formats**:
  - ratchet, sparse ratchet and triple states;
  - Braid (12 tags);
  - erasure sub-formats;
  - session;
  - prekey store v1-v4, including the `kem_pair` checks and the record bounds;
  - every semantic rule.
- **Protobuf profile**: varints, tags, bounds, both field tables.
- **Application signatures**; the **repeated initial message** rule; the **last-resort replay record**.
- **The reverse case, a vector with no spec behind it**: `braid.json` and `auth.json` pin constructions the tree does not state (G-22, G-23).

---

## 4. Not attempted, and why

- **ML-KEM-1024 (FIPS 203) and the incremental KEM split.**
  - `mlkem-braid.md` "The KEM split" now specifies the split, so this is no longer blocked by the spec.
  - It is a large piece of work, and no vector needs it.
  - Only what the prekey store reader needs was implemented: the FIPS 203 modulus check and the SHA3-256 hash check on `kem_pair`.
- **ML-KEM Braid state machine, header/ciphertext MACs, authenticator initialisation, epoch key.** Still deferred to a document outside the tree (G-21 to G-23). The Failure and "What a receive ignores" sections cannot be implemented without that document's transition numbering.
- **End-to-end `Session`**: the handshake, `pending_initial` resend, `established_ephemeral` handling. These need the KEM and the Braid.
  - Implemented without them: the Triple Ratchet with an injected agreement, the repeated-initial rule, the decapsulation-length refusal, and the session format with its semantic rules.
- **Prekey store operations.**
  - `create_prekeys` numbering, `replenish`, rotation, `publish*` selection, the last-resort replay record.
  - These are specified (`key-deletion.md`, `session-persistence.md`) and mostly feasible without a KEM.
  - They were outside the requested priorities, and the record's fingerprint is still unspecified (G-26). The store's persisted format and all its rules are implemented.
- **A NonCanonical case for the session or the v4 prekey store.** The re-encode check is implemented. With every stated field rule enforced, this reader found no input that reaches it, so no case exercises it.
- **Group messaging and devices.** Scaffolds; their topics are unspecified.
- **Full JSON-Schema validation.** Still only the top-level shape; no validator in the standard library.
