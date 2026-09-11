# Gap report, fourth pass: the reader against the current specification

The clean-room reader (`reader/`) was updated from `tacenta-spec` and
`tacenta-test-vectors` alone, against the tree as found in this directory:

- `SOURCE-REVISION` `24c602d375bbebe49c25d23c6a73d9ef8fe39df0`;
- `VERSION` `0.1.0`;
- everything under `CHANGELOG.md` `[Unreleased]`. Its first entry still begins
  "`protocol/session-establishment.md`: `DecodeEC` accepts exactly one
  encoding". The section now also carries the Changed entries for G3-05 and
  register item J-3, and Fixed entries for G3-02, G3-06, G3-07 and G3-08.

Severity, as in the earlier reports:

- **BLOCKING**: cannot be implemented from the tree without guessing.
- **AMBIGUOUS**: more than one reading; a vector decided it, or nothing did.
- **MINOR**: wording, pointers, or a value findable only in the wrong place.

A hypothesis confirmed by a vector is still a gap.

**Baseline** (`python3 reader/run.py`, before any change): 364 PASS, 0 FAIL,
18 SKIP. The 185 vectors and 179 derived cases passed. The 18 skips were the
three new decoder files (4, 8 and 6 vectors). The two files whose bytes
changed, `post-quantum/composite.json` and the AEAD `session-associated-data`
vectors, already passed.

**Final run:**

| | PASS | FAIL | SKIP |
|---|---|---|---|
| Vectors (30 files) | 203 | 0 | 0 |
| Derived cases (10 modules) | 188 | 0 | 0 |
| **Total** | **391** | **0** | **0** |

**What changed in the reader:**

- **`wire.py`:** one check, `check_curve_key`, per message-format.md, Curve
  public keys: the 32 bytes read little-endian must be below p. It is applied
  by:
  - the composite-header decoder, to `dh`;
  - the bundle decoder, to `identity_key`, `signed_prekey` and a present
    `one_time_prekey`;
  - the initial-message decoder, to the key bytes of `identity` and
    `ephemeral`.

  `DecodeEC` uses the same check.
- **`pqxdh.py`:**
  - `accept_repeated_initial` now compares `identity` with
    `EncodeEC(peer_identity_public)` as well as `ephemeral` with
    `established_ephemeral`.
  - The new `receive_repeated_initial` decodes first, then compares, then
    decrypts the inner message.
- **`erasure.py`, `persistence.py`:**
  - A live encoder over 65,536 chunks is no longer refused (G3-02, now in the
    text).
  - The writer does not write one, because which chunks it holds is
    unspecified.
  - The decoder's first-copy check uses a set. Behaviour is unchanged.
- **`run.py`:**
  - handlers for the three new kinds;
  - the zero-chunk encoder comparison, now stated, runs for every
    encoder-state vector.
- **Cases:**
  - SE-01, SE-03, SE-04 and LR-06 are rewritten to the current text.
  - EC-11 and EC-12 are new.
  - The new module `cases_curvekeys.py` holds CK-01 to CK-05, SE-06 and SE-07.

No vector needed a value read from its bytes. The one thing inferred, the new
files' input layout, is G4-01.

---

## 1. The earlier gaps

Counts for the eight gaps `GAPS-3.md` opened: **4 CLOSED, 3 STILL OPEN,
1 NARROWED.** The gaps `GAPS-3.md` recorded as closed (G-01 to G-28 and G2-01
to G2-12) are still closed. Each still has its case or vector, and all pass.

### Re-assessed

| Gap | Status | Citation, and what changed in the reader |
|---|---|---|
| G3-01 Layouts of the erasure and persistence vector kinds | STILL OPEN | `vector.schema.json` `inputs` still describes only the composite header's inputs. `conformance-manifest.md`, "The erasure code, by vector" and "Session persistence", still gives no layout for `indices`, `codewords`, `size`, `issued` or `stream_length`. Only `erasure-decode.json`'s `source` says "a vector with no output is a decoder that holds no value". The new decoder files add a smaller instance of the same kind (G4-01). |
| G3-02 Erasure-encoder edges | CLOSED | `mlkem-braid.md` The erasure code, Codewords: "For `k = 0` there are no points and the sum has no terms, so every codeword of an encoder for zero bytes is 32 zero bytes"; the index rule "holds for every `k`, including 0"; "An encoder over a value of more than 65,536 chunks ... is not refused ... issues `chunk_0` to `chunk_65535` as indices 0 to 65,535 and then nothing"; "Which chunks such an encoder holds is not specified". **Reader fix:** pass 3 refused the longer encoder when it was built, a reading the text now contradicts. It is accepted, with EC-12 and fault F4-18. The zero-chunk codewords matched pass 3's choice. They are now asserted in EC-11, and in the runner for `erasure-encoder-state.json`, where fault F4-19 is caught. The manifest still says the text does not cover either edge (G4-03). |
| G3-03 Protobuf vector field names | STILL OPEN | `protobuf-profile.md` still names fields in camelCase (`ratchetKey`, `prekeyId` ...), and the vectors' `fields` use snake_case. `vector.schema.json` `fields` still says a runner "must check that the names match". No page maps one to the other. |
| G3-04 The AEAD vectors' `ad` is the page's `AD` | STILL OPEN | `message-format.md` Authenticated encryption and the schema are unchanged on this point. The input is still named `ad` and is still the page's `AD`. Two things now point to the reading, but neither is a mapping: `aead-encrypt.json`'s comment is fuller ("AD is CONCAT(ad, header): a length, the identity keys, then a composite header"), and the manifest's AEAD row writes "`AD` empty, short, and a `CONCAT(ad, header)`". The runner's CONCAT cross-check now also applies the canonical-`dh` rule to the embedded header, and passes. |
| G3-05 Where a non-canonical key in an initial message is refused | CLOSED | `message-format.md` Initial message: "It also refuses ... an `identity` or `ephemeral` whose thirty-two key bytes are not the canonical encoding of a curve public key ... Each is a decode failure like the others ... every key this decoder returns is one `DecodeEC` accepts". Curve public keys lists both fields. `session-establishment.md` Sending: "The initial-message decoder applies the same rule ... so `DecodeEC` never meets a key in either field that it would refuse". Receiving: "It must first decode". The text chose reading (a), and `initial-message-decode.json` pins it. **Reader fix:** the check moved into `wire.decode_initial`. SE-03, SE-06 and LR-06 are rewritten. Fault F4-10, pass 3's reading, is caught by the vector file. |
| G3-06 "Otherwise it takes (11)" | CLOSED | `mlkem-braid.md` The state machine, Receiving, `Ct1Acknowledged`: "If the decoder now holds all of `ek_vector`, it validates it ...; failing that, it goes to `Failed`. If it is valid, it takes **(11)** ... If not, it stays." This is the resolution pass 3 took. BR-09 and BR-11 are unchanged and pass. |
| G3-07 Stale status statements | NARROWED | `README.md` Status now reads that identities-and-devices.md "specifies the identity key's secret, how that key signs (XEdDSA) and how a verifier checks a signature against it, and application signatures". **Still stale:** `CHANGELOG.md` `[Unreleased]`, Added, still has the original G2-07 entry ("The page says so and leaves the departure undecided"). A corrected copy was added further down the same list ("The page says so, and ADR-0007 keeps the departure"). The Fixed entry says "The G2-07 entry above says ADR-0007 keeps the departure, where it said the departure was undecided". So the section now carries both statements. |
| G3-08 The sparse ratchet's boundary and the receive epoch | CLOSED | `sparse-pq-ratchet.md` What this ratchet assumes underneath it: "The ML-KEM Braid's receive returns the epoch of the state it leaves the Braid in, less one, so a receive that completes an epoch returns that epoch ... This ratchet does not use the returned epoch". This agrees with `mlkem-braid.md` and ADR-0007. |

### Closed in earlier reports, still closed

G-01 to G-28, and G2-01 to G2-12, as `GAPS-3.md` lists them. Two of them are
touched by this revision's text, and both are still closed:

- **G-26:** "The fingerprint" now says a re-spelled key's message "does not
  decode, so it is never fingerprinted or recorded". LR-06 now goes through the
  bytes.
- **G-05:** the initial-message decoder's refusal list gained the canonical-key
  refusal.

No earlier gap was judged wrong.

---

## 2. New gaps

### G4-01 The new decoder files' layout, and a decoder the page does not define alone (MINOR)
- **Where:**
  - `malformed-input/composite-header-decode.json`, `prekey-bundle-decode.json` and `initial-message-decode.json`: the input `encoding`, and each `source`;
  - `vector.schema.json`, `inputs` and `result`;
  - `message-format.md` Ratchet message and Rejection.
- **Problem:**
  - Nothing describes the input `encoding`. Each `source` says "an accepted vector's output is the re-encoding of the header [bundle, initial message] it decodes to", which implies that `encoding` is the bytes decoded.
  - `composite-header-decode` names a decoder of the composite header alone. The page specifies the ratchet-message decoder, whose ciphertext "runs to the end of the message". Only `CONCAT` and `composite.json` use the header alone.
  - Every input is exactly 102 bytes, where the two decoders agree. So no vector decides whether a header decoder refuses bytes after the header, which the ratchet-message decoder takes as ciphertext.
  - The schema says an invalid vector "must be rejected", not as which failure. The page says: "A refused key is a decode failure".
- **Resolution:**
  - `encoding` is the bytes handed to the decoder.
  - The composite file runs through both decoders, and they must agree. The header decoder refuses trailing bytes (Rejection).
  - An invalid vector must be refused as a decode failure (`wire.DecodeError`), not as any other refusal. Fault F4-11 is caught this way.

### G4-02 The canonical-key rule stops at the wire; stored peer keys are not held to it (MINOR)
- **Where:**
  - `message-format.md` Curve public keys: "The rule covers every curve public key a peer sends".
  - `session-establishment.md` Receiving the initial message: "Both comparisons are against canonical encodings, and a key has one".
  - `session-persistence.md` Session, Semantic rules: `established_ephemeral` is "33 bytes with the curve byte first", and `peer_identity_public` has no rule of its own. "Semantic rules of the leaf formats": the rules "are all of them: a reader ... accepts every state that keeps them all". The ratchet state's `dhr_pub` and each skipped entry's `dh` have no key rule.
  - ADR-0007 decision 2.
- **Problem:**
  - A stored session, ratchet state or skipped-key entry can hold a re-spelled peer key. Because the lists are complete, a conforming reader must accept it.
  - This reader's session reader, written to those lists, accepts a responder session whose `established_ephemeral` has bit 255 set (`work/probe_stored_keys.py`). Every genuine repeat is then refused as `NotARepeatedInitial`. So "Both comparisons are against canonical encodings" is not true of every session a conforming reader accepts.
  - A re-spelled `peer_identity_public` is refused only while `identity_ad` still carries the canonical form. The refusal is incidental.
  - By `ratchet.md`'s rule (a Diffie-Hellman step "when that key differs from `DHr`"), a ratchet state whose `dhr_pub` is re-spelled would step on the peer's next header. That is the second identity the Curve public keys section is written to prevent. This follows from the text; it was not run.
  - The reach is an imported or corrupted state, not a peer. The `[0.1.0]` changelog says the export check "is against corruption, not against a reader of the medium".
- **Resolution:** The reader follows the complete lists and accepts such states. No case asserts either behaviour; the probe's output is recorded in this report only.

### G4-03 The manifest still says the text leaves the encoder's edges open, and that the bundle has only core tests (MINOR)
- **Where:** `conformance-manifest.md`:
  - "The erasure code, by vector": "Not pinned: an encoder for a value longer than 65,536 chunks, which the text does not cover and `tacenta-erasure` caps; parity codewords of a zero-length value, for which 'the polynomial of degree below `k`' has no points".
  - "Also covered, outside this directory": the prekey-bundle encoding has "a core round-trip test".
- **Problem:**
  - `mlkem-braid.md` Codewords now covers both edges (G3-02). "Caps" can be read as the refusal the page now rules out ("is not refused"). Only the changelog explains that the implementation keeps the first 65,536 chunks.
  - The bundle now has `prekey-bundle-decode.json`, which the manifest's own Message format table lists.
- **Resolution:** The page is followed.

### G4-04 What follows `NotARepeatedInitial` is not stated (AMBIGUOUS)
- **Where:**
  - `message-format.md` Message type: "a peer that already has a session can still receive an initial message (a session reset, or a changed identity), and must recognise it as one".
  - `session-establishment.md` Receiving the initial message: "It does not establish again ... Otherwise, and always on an initiator's session, it refuses the message (`NotARepeatedInitial`)".
  - `error-handling.md`: "Conditions a caller must act on are named by the page that defines them". It names two last-resort conditions, and not this one.
- **Problem:**
  - With the new identity comparison, both of message-format.md's examples are refused by the existing session: a reset, which has a new `ephemeral`, and a changed identity.
  - Nothing says what the recipient does next. It could establish a new session from the same message, under first receipt's rules for one-time prekeys, decapsulation and the last-resort record. It could replace or keep the old session, or drop the message.
  - So there are two readings:
    - (a) `NotARepeatedInitial` is final for that message;
    - (b) it is the point at which the recipient establishes afresh, as the reset and changed-identity examples suggest.
  - The difference is observable: whether a peer who reset or re-installed can reach a responder that still holds a session.
  - The same question arises for simultaneous initiation. Each side holds an initiator's session and "always" refuses the other's initial message.
- **Resolution:** None is needed by the reader, which has no session router. It models only the rule on the existing session, and no case takes either reading.

---

## 3. Vector gaps: specified, but no vector pins it

Everything below is covered in this reader only by derived cases. Those test
the reader's reading of the text, not agreement with anyone else.

### New in this pass

- **The value p itself.**
  - Of the nineteen values at or above p with bit 255 clear, each file refuses only 9 + p, and accepts p - 1.
  - A decoder that refuses "above p" rather than "at least p" passes all 203 vectors: deliberate fault F4-02. It is caught only by SE-03, CK-01 and CK-02.
  - A key with bit 255 set and a value at or above p is not pinned either.
- **`DecodeEC` on its own**, establishment's check. By the text it can no longer refuse a decoded message's key, so it is observable only through an interface that hands establishment an undecoded message.
- **The repeated initial message**, which no vector pins:
  - both comparisons, `identity` against `EncodeEC(peer_identity_public)` included;
  - the role;
  - decoding first, with the refusal a decode failure;
  - the fields not compared;
  - "yields that message's plaintext once".

  Faults F4-12 to F4-17 are each caught only by SE-01, SE-06 or SE-07.
- **The erasure encoder's stated edges** (G3-02):
  - An encoder over 65,536 chunks is not pinned. F4-18 is caught only by EC-12.
  - An encoder for zero bytes issues no codeword in any vector. F4-19 fails `erasure-encoder-state.json` only because the runner now applies the text's zero-codeword rule to that vector's encoder; no vector carries such a codeword.

### `GAPS-3.md`'s vector gaps, re-assessed

| Vector gap | Status | Note |
|---|---|---|
| The Braid: MACs, `Init(1, SK)`, the state machine, `ek_vector` validation, the persisted Braid | STILL OPEN | `braid.json` and `auth.json` are unchanged. `composite.json`'s bytes changed, and its three `dh` values are now canonical, but it still pins only the header's round trip. |
| The session over the Braid | STILL OPEN | |
| Establishment: the fingerprint, the record's refusals, per-key budget | STILL OPEN | |
| Establishment: `DecodeEC`'s canonical refusals, and G3-05 | NARROWED | The initial-message decoder's refusal is pinned by `initial-message-decode.json`: bit 255 and 9 + p in each field, and p - 1 accepted. `DecodeEC` alone and the value p are not (above). |
| Establishment: raw curve keys left to RFC 7748 | CLOSED (superseded) | No longer the rule. The bundle's and `dh`'s refusals are pinned by `prekey-bundle-decode.json` and `composite-header-decode.json`. |
| Establishment: the FIPS 203 section 7.2 check | STILL OPEN | |
| Establishment: the repeated initial message | STILL OPEN | It now has a second comparison (above). |
| Establishment: PQXDH `AD` and `CONCAT(ad, header)` | STILL OPEN | The AEAD vector's `AD` has the `CONCAT` layout, but nothing derives `AD` from a handshake. |
| XEdDSA: rule 3 alone, a `u` with no point, the cofactored-only signature, a non-canonical `R` not of small order, application signatures | STILL OPEN | `xeddsa.json` is unchanged. |
| AEAD: a whole-block plaintext | STILL OPEN | The manifest gives the reason. |
| Erasure: zero-byte encoder output, over 65,536 chunks, a persisted encoder of 65,536 chunks | STILL OPEN | The first two are now stated (G3-02). |
| Protobuf `maxFields` | STILL OPEN | Unreachable, as the page argues. |
| Persistence: every format but the erasure sub-formats | STILL OPEN | |
| From `GAPS-2.md`: Triple Ratchet commit rules; the sparse ratchet's state machine; the Double Ratchet's store bound, eviction, expiry, ceilings and no-chain refusals | STILL OPEN | |
| From `GAPS-2.md`: the composite header's and initial message's negative cases, and the prekey bundle | NARROWED | Accepted forms and the curve-key refusals are pinned by the three new files. Still unpinned: truncation, the version and type bytes, `ag_type`, presence bytes and padding, length overruns, `kem_prekey_len`, trailing bytes, and the curve byte. The manifest's "Not yet covered" says so. |

**The reverse case, a vector with no spec behind it:** none. The refusal
`composite-header-decode.json` pins is stated. Only the stand-alone header
decoder it runs is not (G4-01).

---

## 4. Not attempted, and why

Unchanged from `GAPS-3.md`:

- ML-KEM-1024 and its incremental split (the Braid runs over `kem_double.py`);
- the end-to-end `Session`;
- prekey store operations;
- group messaging and devices;
- full JSON-Schema validation.

Added this pass:

- **A session router.** Nothing here decides which session an arriving initial
  message goes to, or what follows `NotARepeatedInitial` (G4-04). The
  repeated-initial rule is exercised on a responder's persisted fields over a
  live Triple Ratchet half (SE-06, SE-07).

---

## 5. Deliberate faults

19 faults were tried, each a one-line or one-block textual change to a fresh
copy of the reader (`work/faults4.py`), run with the full runner. **All 19 were
caught.**

| | Tried | Caught | Caught by a vector file |
|---|---|---|---|
| Canonical-key checks (F4-01 to F4-11) | 11 | 11 | 10 (not F4-02, "above p") |
| Repeated-initial rule (F4-12 to F4-17) | 6 | 6 | 0 |
| Erasure edges, G3-02 (F4-18, F4-19) | 2 | 2 | 1 (F4-19, through the runner's stated rule) |

The per-fault list, with the vectors and cases that failed, is in
`reader/README.md`.

---

## 6. Isolation

- **What was read:** only this directory:
  - `tacenta-spec/` and `tacenta-test-vectors/` (`vectors/`, `schema/`, `conformance-manifest.md`);
  - `reader/`;
  - `GAPS-3.md` and `SOURCE-REVISION`.

  `GAPS.md` and `GAPS-2.md` were not opened beyond a line count.
- **What was written:** only inside this directory:
  - `reader/`: the modules and cases named above, the new `cases_curvekeys.py`, and `README.md`;
  - `GAPS-4.md`;
  - `work/`: run outputs, a dump of the new vector files, the stored-key probe, `faults4.py` and its output.

  The per-fault copies were made under `work/faults4/`, each reaching the vectors through a symbolic link inside this directory, and removed after each run. Python wrote its usual `__pycache__` directories inside `reader/`.
- **What was not consulted:** no implementation (tacenta-core, tacenta-model, tacenta-proofs, the Rust runner, libsignal), no git history, no other scratch files, and no web search. RFC 7748 section 5, which the pages cite, was used from knowledge for X25519's masking and reduction. Nothing was fetched.
- **Unrelated context, not used:** the working environment carried a short index of notes from other work. Nothing from it was used.

These are recorded in `reader/README.md` under "Isolation, pass 4".
