# tacenta_reader: a clean-room reading of tacenta-spec

An independent implementation of parts of the Tacenta protocol specification,
written to test whether the specification alone is enough to build from.
Python 3, standard library only (`hashlib`, `hmac`, `json`, `copy`, `re`,
`dataclasses`).

**Specification revision.** Fourth pass, against the tree as found:

- `SOURCE-REVISION` `24c602d375bbebe49c25d23c6a73d9ef8fe39df0`;
- `VERSION` `0.1.0`;
- every change under `CHANGELOG.md` `[Unreleased]`, whose first entry begins
  "`protocol/session-establishment.md`: `DecodeEC` accepts exactly one encoding".

## Provenance

Written only from the specification in `../tacenta-spec` and the vectors,
schemas and conformance manifest in `../tacenta-test-vectors`. It also used the
public standards those documents name:

- RFC 2104, RFC 5869, FIPS 180-4, RFC 7748, RFC 8032;
- XEdDSA revision 1;
- FIPS 197 and NIST SP 800-38A, for AES-256 and CBC;
- FIPS 202 and FIPS 203, for SHA3, `ByteEncode12` and the ML-KEM
  encapsulation-key checks.

It was written without network access. It consulted no existing implementation
of these protocols: not tacenta-core, tacenta-model, tacenta-proofs, the Rust
vector runner, libsignal or anything else.

Where the spec does not state something, the code comment names the entry in
`../GAPS.md` (first pass), `../GAPS-2.md` (second), `../GAPS-3.md` (third) or
`../GAPS-4.md` (fourth).
A hypothesis that matches a vector is still recorded as a gap.

## Isolation

**Pass 2.** One shell command listed the file names of the scratch directory
that contains the clean-room directory. It listed names only. No file outside
the clean-room directory was opened or searched, and nothing from that listing
was used.

### Isolation, pass 3

- **Reads.** Nothing outside the clean-room directory was read, listed or
  searched.
- **A tool-output copy, not a read.** The output of one early command, a
  dump of the new vector files, was too long to display, and the tooling
  saved a copy outside this directory. That copy was not opened. The command
  was re-run with its output written to `../work/`, and the fault run's output
  was read from `../work/faults.txt`.
- **Unrelated notes, not used.** The working environment carried a short
  index of notes from other work. Nothing from it was used for any reading or
  decision here.
- **Writes.** Temporary files were written only inside the clean-room
  directory, under `../work/`.

### Isolation, pass 4

- **Reads.** Nothing outside the clean-room directory was read, listed or
  searched. Inside it, `GAPS.md` and `GAPS-2.md` were not opened beyond a
  line count.
- **Writes.** Only inside the clean-room directory:
  - this reader;
  - `../GAPS-4.md`;
  - `../work/`: run outputs, a dump of the three new vector files, `probe_stored_keys.py`, `faults4.py` and `faults4.txt`.

  The per-fault copies under `../work/faults4/` reached the vectors through a symbolic link inside this directory, and were removed after each run.
- **Not consulted.** No implementation, git history, other scratch files or
  web search. RFC 7748 section 5, which the pages cite, was used from
  knowledge for X25519's masking and reduction.
- **Unrelated notes, not used.** The working environment again carried a short
  index of notes from other work. Nothing from it was used.

## What changed in pass 4

- **`wire.py`: canonical curve keys at every decoder** (message-format.md,
  Curve public keys).
  - `check_curve_key` accepts 32 bytes exactly when, read little-endian, they
    are below p.
  - It is applied to the composite header's `dh`, the bundle's
    `identity_key`, `signed_prekey` and present `one_time_prekey`, and the
    initial message's `identity` and `ephemeral`. A refusal is a
    `DecodeError`.
  - `DecodeEC` uses the same check. G3-05 is closed by the text.
- **`pqxdh.py`: the repeated-initial rule as now written.**
  - `accept_repeated_initial` requires `ephemeral` to equal
    `established_ephemeral`, and `identity` to equal
    `EncodeEC(peer_identity_public)`, on a responder's session.
  - `receive_repeated_initial` decodes first, then compares, then decrypts the
    inner ratchet message.
- **`erasure.py`: G3-02, closed by the text.**
  - A live encoder over 65,536 chunks is not refused. Pass 3 refused it.
  - `persistence.encoder_to_bytes` does not write one, because which chunks it
    holds is unspecified and a stored one is refused.
  - A zero-chunk encoder's all-zero codewords are now asserted.
- **`run.py`:**
  - handlers for `composite-header-decode`, `prekey-bundle-decode` and
    `initial-message-decode` (the input layout is GAPS-4.md G4-01);
  - the zero-chunk encoder comparison runs for every encoder-state vector.

## What it implements

| Module | Spec source | Pinned by |
|---|---|---|
| `kdf.py`: HMAC-SHA256, HKDF-SHA256 | RFC 2104, RFC 5869 | `primitives/hmac-sha256.json`, `hkdf-sha256.json` |
| `curve25519.py`: X25519, Ed25519, XEdDSA signing (with the clamp) and the six verifier rules | RFC 7748, RFC 8032, identities-and-devices.md Signing and Verifying a signature | `primitives/x25519.json`, `ed25519.json`, `xeddsa.json` (rule 3 not on its own: GAPS-3.md vector gaps) |
| `wire.py`: composite header, ratchet message, `CONCAT`, initial message, prekey bundle, `EncodeEC`/`EncodeKEM`, **the canonical curve-key rule in all three decoders** and `DecodeEC`, every stated decoder refusal, the initiator's bundle refusals | message-format.md (Curve public keys), session-establishment.md | `post-quantum/composite.json`, `serialization/*.json`, `malformed-input/composite-header-decode.json`, `prekey-bundle-decode.json`, `initial-message-decode.json` (the curve-key refusals); other refusals by derived cases only |
| `aes.py`, `aead.py`: AES-256, CBC, PKCS#7, the HMAC-SHA256 tag, the four receiver steps, one authentication failure | message-format.md Authenticated encryption | `aead/aead-encrypt.json`, `aead-decrypt.json` |
| `ratchet.py`: the Double Ratchet: initialisation, derivations, expansion, DH triggers, `MAX_SKIP`, store bound, replacement, stale same-chain refusal, ceilings, expiry, eviction | ratchet.md, CONSTANTS.md, key-deletion.md | `ratchet/double-ratchet.json`, `malformed-input/ratchet-reject.json` |
| `spqr.py`: the sparse ratchet: derivations, send counter, ceilings, refusals, total bound, eviction, retention, and **replacement order (fixed in pass 3, G2-01)** | sparse-pq-ratchet.md, session-persistence.md | `post-quantum/spqr.json` (chain step only) |
| `triple.py`: split, combination, encrypt/decrypt with the commit rules, the non-contributory check, eviction retry; the agreement runs before the ratchets | triple-ratchet.md, mlkem-braid.md What the session does with them | `post-quantum/triple.json`, `split.json` |
| `pqxdh.py`: `KDF`, `AD`, DH1..DH4, the decapsulation-length refusal, the FIPS 203 section 7.2 check on a bundle's KEM prekey, **the repeated-initial rule (both comparisons, decode first; pass 4)**, the last-resort fingerprint and the replay record's refusals | session-establishment.md, key-deletion.md | `session-establishment/pqxdh-sk.json`; the fingerprint and the repeated-initial rule by derived cases only |
| `gf65536.py`, `erasure.py`: GF(2^16), chunking, codewords, first-copy-wins decoding, encoder exhaustion, **the zero-chunk and over-65,536-chunk encoders (pass 4)** | mlkem-braid.md The erasure code | `post-quantum/gf.json`, `inv.json`, `interp.json`, `erasure-encode.json`, `erasure-decode.json` |
| `braid.py`: **the ML-KEM Braid**: `ToBytes`, `KDF_OK`, `KDF_AUTH`, the authenticator and both MACs, `ek_vector` validation, messages, the eleven live states and `Failed`, all thirteen transitions, send and receive epochs, what a receive ignores, every way into `Failed`, the epoch ceiling; conversion to the persisted layout; `BraidAgreement` for `triple.py` | mlkem-braid.md | `post-quantum/braid.json`, `auth.json`; the rest by derived cases |
| `kem_double.py`: a **test double** for the incremental KEM interface, with the split's sizes, hash order and implicit rejection. **Not ML-KEM** | mlkem-braid.md The KEM split | none |
| `persistence.py`: readers and writers with every stated refusal and semantic rule: ratchet, sparse ratchet and triple states, erasure sub-formats, Braid (12 tags), session, prekey store (v4 written, v1-v3 read, `kem_pair` checks) | session-persistence.md, CONSTANTS.md | `persistence/erasure-encoder-state.json`, `erasure-decoder-state.json`; the other formats have no vectors |
| `protobuf.py`: the bounded protobuf profile, both message types | protobuf-profile.md, CONSTANTS.md | `protobuf/protobuf-ratchet-body.json`, `protobuf-prekey-envelope.json` |
| `identity.py`: the identity secret, application signatures | identities-and-devices.md | no vectors |

**The eight vector files new in pass 3 needed no module change.** Their 106
vectors pass on the modules pass 2 wrote. The runner gained handlers for them;
GAPS-3.md G3-01 to G3-04 record the input layouts it had to infer.

## Derived cases

Each case cites the page and sentence it tests. There is one module per area,
and each is a row in the runner's table.

| Module | Cases | Covers |
|---|---|---|
| `negative_cases.py` | 59 | wire decoders and refusals, bundle signatures, non-contributory DH, ratchet and sparse ratchet basics, field |
| `cases_ratchet.py` | 18 | counter ceilings, clock ceiling, stale same-chain refusal, DH triggers, `PN` skip rules, store bound, eviction order, sparse ceilings and eviction, sparse replacement order (CR-18) |
| `cases_triple.py` | 10 | split halves, expansion of the combination, commit rules, AD binding, non-contributory check order, eviction retry, epoch advance |
| `cases_aead.py` | 13 | FIPS 197 KAT, round trips, padding, tag input, every refusal, one failure kind, no decryption before the tag, key and IV positions and the IV not sent (AE-12) |
| `cases_erasure.py` | 12 | table arithmetic, chunking, codewords, decoding from any `k`, first copy wins, exhaustion; an encoder for zero bytes (EC-11) and over 65,536 chunks (EC-12) |
| `cases_persistence.py` | 23 | round trips and every stated refusal and semantic rule of each format |
| `cases_protobuf.py` | 9 | varints, tags, bounds, both field tables, free order |
| `cases_identity.py` | 19 | application signatures, clamping on use, the repeated-initial comparisons (SE-01, both fields, rewritten in pass 4), non-contributory definition; `DecodeEC` and the initial decoder's refusal (SE-03), X25519's masking against the decoders' refusals (SE-04), the section 7.2 KEM prekey check (SE-05); XEdDSA signing and the six verifier rules (XS-01 to XS-04); the fingerprint and replay record (LR-01 to LR-07, LR-06 through the bytes) |
| `cases_braid.py` | 18 | derivation bytes, authenticator and MACs, sizes and holdings, initialisation, the send table, epoch completion and roles, send and receive epochs, what a receive ignores, all thirteen transitions, MAC and validation failures, KEM failures and `Failed`, the epoch ceiling, encoder exhaustion, persistence of all twelve tags, the composite header, the Triple Ratchet over the Braid with `session-persistence.md`'s relations, `AgreementFailed` |
| `cases_curvekeys.py` | 7 | pass 4. The canonical-key rule at p and every value up to 2^255 - 1 (CK-01); the composite header's `dh`, including a live session refusing at decode (CK-02); the bundle's three keys, refused though signed, with low-order canonical keys left to the contributory check (CK-03); the initial message's two keys, and `DecodeEC` accepting every key the decoder returns (CK-04); why a second spelling is a second identity (CK-05); a repeat must first decode (SE-06); the repeated initial message over a live Triple Ratchet half: ignored fields, yield once, already-read messages, refusals before decryption, the initiator's session (SE-07) |

## Deliberate faults

**Passes 1 and 2.** The runner was checked against 13 faults:

- the expiry boundary written as `>`;
- `MAX_SKIP` on `PN` without a receiving chain;
- eviction ties reversed;
- no stale same-chain refusal;
- three epochs kept;
- an unchecked padding byte;
- decrypting before the tag;
- last-copy-wins;
- the decoder bound removed;
- the Braid role parity flipped;
- non-minimal varints;
- the contributory check moved after the ratchets;
- a validating initial decoder.

Each produced FAILs that included the targeted case.

**Pass 3.** Eighteen faults, each a one-line textual change made in a fresh
copy of the reader by `../work/faults.py`, then the full runner:

| Fault | Caught by |
|---|---|
| F01 `KDF_OK` with a non-zero salt | `braid.json`, BR-01 |
| F02 `Update` swaps `root_key` and `mac_key` | `auth.json`, BR-02 |
| F03 MAC inputs with the epoch bare (the published document's notation) | BR-02 only |
| F04 (12) requires a codeword | BR-08 |
| F05 (5) reports the sending epoch | BR-07 |
| F06 `Ct2Sampled` checks the ceiling only on an advancing message | BR-13 |
| F07 `ek_vector` validation without the modulus check | BR-11 |
| F08 fingerprint without the ciphertext's length prefix | LR-01 |
| F09 record budget of 1,025 per key | LR-05 |
| F10 replay matched only under the named key's tag | LR-04 |
| F11 `DecodeEC` without the canonical refusals | SE-03, SE-04, LR-06 |
| F12 sparse replacement keeps the old place | CR-18 |
| F13 erasure decoder, last copy wins | `erasure-decode.json`, `erasure-decoder-state.json`, EC-06 |
| F14 persisted encoder writes `next` as 0 once exhausted | `erasure-encoder-state.json`, PS-10 |
| F15 protobuf accepts a repeated field 1 | both protobuf files, PF-07 |
| F16 AEAD checks only the last padding byte | `aead-decrypt.json`, AE-09 |
| F17 XEdDSA verifier accepts a small-order `A` | **missed at first** (no vector and no case failed); caught by XS-03 once it was given a small-order `A` with a full-order `R` |
| F18 the session hands the sparse ratchet the state's epoch | BR-17, BR-18 |

On the first run, 17 of 18 were caught. The miss showed that no `xeddsa.json`
vector isolates rule 3 (GAPS-3.md, vector gaps). After XS-03 was
strengthened, F17 is caught, so all 18 are. (Pass 3's `faults.py` was not in
the tree this pass was read from.)

**Pass 4.** Nineteen faults in `../work/faults4.py`, run the same way, four at
a time. **All 19 were caught on the first run.**

| Fault | Vector files that failed | Derived cases that failed |
|---|---|---|
| F4-01 composite header: `dh` not checked | `composite-header-decode.json` | SE-04, CK-02 |
| F4-02 the rule off by one: a key equal to p accepted | **none** | SE-03, CK-01, CK-02 |
| F4-03 the rule tests bit 255 only | all three decoder files | SE-03, SE-04, CK-01 to CK-04, SE-06 |
| F4-04 the rule masks bit 255 before comparing | all three decoder files | SE-03, SE-04, LR-06, CK-01 to CK-04, SE-06 |
| F4-05 bundle `identity_key` not checked at decode | `prekey-bundle-decode.json` | CK-03 |
| F4-06 bundle `signed_prekey` not checked | `prekey-bundle-decode.json` | SE-04, CK-03 |
| F4-07 bundle present `one_time_prekey` not checked | `prekey-bundle-decode.json` | CK-03 |
| F4-08 initial `identity` key bytes not checked | `initial-message-decode.json` | SE-03, CK-04, SE-06 |
| F4-09 initial `ephemeral` key bytes not checked | `initial-message-decode.json` | SE-03, SE-04, CK-04, SE-06 |
| F4-10 both left to establishment (pass 3's reading of G3-05) | `initial-message-decode.json` | SE-03, SE-04, CK-04, SE-06 |
| F4-11 a refused key reported as an encoding error | all three decoder files | RM-12, SE-03, SE-04, LR-06, CK-01 to CK-04, SE-06 |
| F4-12 repeat: `identity` not compared (pass 3's rule) | none | SE-01, SE-07 |
| F4-13 repeat: `ephemeral` not compared | none | SE-01, SE-07 |
| F4-14 repeat: `identity` compared with the raw key | none | SE-01, SE-06, SE-07 |
| F4-15 repeat: an initiator's session with an ephemeral accepts | none | SE-01 |
| F4-16 repeat: inner message decrypted before the comparisons | none | SE-07 |
| F4-17 repeat: an undecodable repeat reported as `NotARepeatedInitial` | none | SE-06 |
| F4-18 erasure: an encoder over 65,536 chunks refused again | none | EC-12 |
| F4-19 erasure: an encoder for zero bytes issues non-zero codewords | `erasure-encoder-state.json`, through the runner's stated rule | EC-11 |

The vector files catch 11 of the 19. They miss the boundary at exactly p
(F4-02), every repeated-initial fault, and the over-65,536-chunk encoder
(GAPS-4.md, vector gaps).

## Not implemented

- ML-KEM-1024 and its incremental split. The Braid runs over `kem_double.py`.
- The end-to-end `Session`: the handshake with a real KEM, `pending_initial`
  resend, `established_ephemeral`, and export/import over live states.
- Prekey store operations: numbering, `replenish`, rotations, `publish`
  selection.

- A session router: which session an initial message goes to, and what
  follows `NotARepeatedInitial` (GAPS-4.md G4-04).

The reasons are in `../GAPS-3.md` and `../GAPS-4.md` ("Not attempted"). No
vector file needs any of these, so the runner reports no SKIPs.

## Running

```
python3 reader/run.py              # from the clean-room directory
python3 work/faults4.py [F4-01 ...]    # the pass-4 deliberate faults
```

The runner prints:

1. one line per vector (`PASS`, `FAIL` with a short diff, or `SKIP` with a reason);
2. one line per derived case;
3. a per-file table with a vectors subtotal, a derived-cases subtotal and a total.

The exit status is non-zero on any FAIL. A full run takes about five seconds.

Current result:

| | Count | PASS | FAIL | SKIP |
|---|---|---|---|---|
| Vectors (30 files) | 203 | 203 | 0 | 0 |
| Derived cases (10 modules) | 188 | 188 | 0 | 0 |
| **Total** | 391 | 391 | 0 | 0 |

## In this repository

Copied into `tacenta-test-vectors/runners/independent/` unchanged, apart from
the one line in `run.py` that says where the vectors are. In this README,
`../tacenta-spec` and `../tacenta-test-vectors` name the clean-room directory it
was written in. In the repository they are the repository's own `tacenta-spec`
and `tacenta-test-vectors`. Run it from the repository root with

```
python3 tacenta-test-vectors/runners/independent/reader/run.py
```

`tooling/ci.sh` and the CI `vectors` job both run it.

**Keeping it independent** (ADR-0006):

- A change to this reader is made from the specification and the vectors only,
  by someone who has not consulted `tacenta-core`, `tacenta-model`,
  `tacenta-proofs` or the Rust runner for that change.
- When a change to the specification, the model or the vectors breaks it, the
  breakage is a question about the specification. It is answered there, not by
  reading the implementation.

Each gap report re-assesses its predecessors against the revision it names:

- `../GAPS.md`: the first pass.
- `../GAPS-2.md`: the second pass.
- `../GAPS-3.md`: the third pass.
- `../GAPS-4.md`: this pass.

A gap is closed by changing the specification. Its entry is marked closed when
the reader is next updated from the new text.
