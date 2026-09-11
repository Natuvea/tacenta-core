# tacenta_reader: a clean-room reading of tacenta-spec

An independent implementation of parts of the Tacenta protocol specification,
written to test whether the specification alone is enough to build from.
Python 3, standard library only (`hashlib`, `hmac`, `json`, `copy`, `re`,
`dataclasses`).

**Specification revision.** Third pass, against the tree as found:

- `SOURCE-REVISION` `a9cf860ecfd5eca6951dff5471d1342875e85c1c`;
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
`../GAPS.md` (first pass), `../GAPS-2.md` (second) or `../GAPS-3.md` (third).
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

## What it implements

| Module | Spec source | Pinned by |
|---|---|---|
| `kdf.py`: HMAC-SHA256, HKDF-SHA256 | RFC 2104, RFC 5869 | `primitives/hmac-sha256.json`, `hkdf-sha256.json` |
| `curve25519.py`: X25519, Ed25519, XEdDSA signing (with the clamp) and the six verifier rules | RFC 7748, RFC 8032, identities-and-devices.md Signing and Verifying a signature | `primitives/x25519.json`, `ed25519.json`, `xeddsa.json` (rule 3 not on its own: GAPS-3.md vector gaps) |
| `wire.py`: composite header, ratchet message, `CONCAT`, initial message, prekey bundle, `EncodeEC`/`EncodeKEM`, `DecodeEC`'s canonical-encoding refusals (applied at establishment, G3-05), every stated decoder refusal, the initiator's bundle refusals | message-format.md, session-establishment.md | `post-quantum/composite.json`, `serialization/*.json`; refusals by derived cases only |
| `aes.py`, `aead.py`: AES-256, CBC, PKCS#7, the HMAC-SHA256 tag, the four receiver steps, one authentication failure | message-format.md Authenticated encryption | `aead/aead-encrypt.json`, `aead-decrypt.json` |
| `ratchet.py`: the Double Ratchet: initialisation, derivations, expansion, DH triggers, `MAX_SKIP`, store bound, replacement, stale same-chain refusal, ceilings, expiry, eviction | ratchet.md, CONSTANTS.md, key-deletion.md | `ratchet/double-ratchet.json`, `malformed-input/ratchet-reject.json` |
| `spqr.py`: the sparse ratchet: derivations, send counter, ceilings, refusals, total bound, eviction, retention, and **replacement order (fixed in pass 3, G2-01)** | sparse-pq-ratchet.md, session-persistence.md | `post-quantum/spqr.json` (chain step only) |
| `triple.py`: split, combination, encrypt/decrypt with the commit rules, the non-contributory check, eviction retry; the agreement runs before the ratchets | triple-ratchet.md, mlkem-braid.md What the session does with them | `post-quantum/triple.json`, `split.json` |
| `pqxdh.py`: `KDF`, `AD`, DH1..DH4, the decapsulation-length refusal, the FIPS 203 section 7.2 check on a bundle's KEM prekey, the repeated-initial rule, **the last-resort fingerprint and the replay record's refusals** | session-establishment.md, key-deletion.md | `session-establishment/pqxdh-sk.json`; the fingerprint by derived cases only |
| `gf65536.py`, `erasure.py`: GF(2^16), chunking, codewords, first-copy-wins decoding, encoder exhaustion | mlkem-braid.md The erasure code | `post-quantum/gf.json`, `inv.json`, `interp.json`, `erasure-encode.json`, `erasure-decode.json` |
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
| `cases_erasure.py` | 10 | table arithmetic, chunking, codewords, decoding from any `k`, first copy wins, exhaustion |
| `cases_persistence.py` | 23 | round trips and every stated refusal and semantic rule of each format |
| `cases_protobuf.py` | 9 | varints, tags, bounds, both field tables, free order |
| `cases_identity.py` | 19 | application signatures, clamping on use, repeated initial message, non-contributory definition; `DecodeEC` (SE-03), raw keys left to RFC 7748 (SE-04), the section 7.2 KEM prekey check (SE-05); XEdDSA signing and the six verifier rules (XS-01 to XS-04); the fingerprint and replay record (LR-01 to LR-07) |
| `cases_braid.py` | 18 | derivation bytes, authenticator and MACs, sizes and holdings, initialisation, the send table, epoch completion and roles, send and receive epochs, what a receive ignores, all thirteen transitions, MAC and validation failures, KEM failures and `Failed`, the epoch ceiling, encoder exhaustion, persistence of all twelve tags, the composite header, the Triple Ratchet over the Braid with `session-persistence.md`'s relations, `AgreementFailed` |

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
strengthened, F17 is caught, so all 18 are.

## Not implemented

- ML-KEM-1024 and its incremental split. The Braid runs over `kem_double.py`.
- The end-to-end `Session`: the handshake with a real KEM, `pending_initial`
  resend, `established_ephemeral`, and export/import over live states.
- Prekey store operations: numbering, `replenish`, rotations, `publish`
  selection.

The reasons are in `../GAPS-3.md` ("Not attempted"). No vector file needs any of
these, so the runner reports no SKIPs.

## Running

```
python3 reader/run.py          # from the clean-room directory
python3 work/faults.py [F01 ...]   # the pass-3 deliberate faults
```

The runner prints:

1. one line per vector (`PASS`, `FAIL` with a short diff, or `SKIP` with a reason);
2. one line per derived case;
3. a per-file table with a vectors subtotal, a derived-cases subtotal and a total.

The exit status is non-zero on any FAIL. A full run takes about five seconds.

Current result:

| | Count | PASS | FAIL | SKIP |
|---|---|---|---|---|
| Vectors (27 files) | 185 | 185 | 0 | 0 |
| Derived cases (9 modules) | 179 | 179 | 0 | 0 |
| **Total** | 364 | 364 | 0 | 0 |

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
- `../GAPS-3.md`: this pass.

A gap is closed by changing the specification. Its entry is marked closed when
the reader is next updated from the new text.
