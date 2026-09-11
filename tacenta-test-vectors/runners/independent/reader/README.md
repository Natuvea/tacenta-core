# tacenta_reader: a clean-room second reading of tacenta-spec

An independent implementation of parts of the Tacenta protocol specification,
written to test whether the specification alone is enough to build from.
Python 3, standard library only (`hashlib`, `hmac`, `json`, `copy`,
`dataclasses`).

**Specification revision.** Updated against `tacenta-spec` as found, with
`VERSION` `0.0.0` and every change under `CHANGELOG.md` `[Unreleased]`. That
section's first entry begins: "The decoders now enforce two of
`protocol/message-format.md`'s refusals at".

## Provenance

Written only from the specification in `../tacenta-spec` and the vectors,
schemas and conformance manifest in `../tacenta-test-vectors`. It also used the
public standards those documents name:

- RFC 2104, RFC 5869, FIPS 180-4, RFC 7748, RFC 8032;
- XEdDSA revision 1;
- FIPS 197, for AES-256;
- FIPS 202 and FIPS 203, for the SHA3-256 and ML-KEM encapsulation-key checks
  the prekey store's reader makes.

It was written without network access and without consulting any existing
implementation of these protocols: tacenta-core, tacenta-model, the Rust vector
runner, libsignal, or anything else.

A slip in the second pass: one shell command listed the file names of the
scratch directory that contains the clean-room directory. It listed names only;
no file outside the clean-room directory was opened or searched, and nothing
from that listing was used.

Where the spec does not state something, the code comment names the entry in
`../GAPS.md` (first pass) or `../GAPS-2.md` (this pass). A hypothesis that
matches a vector is still recorded as a gap.

## What it implements

| Module | Spec source | Pinned by |
|---|---|---|
| `kdf.py`: HMAC-SHA256, HKDF-SHA256 | RFC 2104, RFC 5869 | `primitives/hmac-sha256.json`, `hkdf-sha256.json` |
| `curve25519.py`: X25519, Ed25519, XEdDSA sign and verify | RFC 7748, RFC 8032, XEdDSA rev. 1, CONSTANTS.md, ADR-0002 | `primitives/x25519.json`, `ed25519.json`, `xeddsa.json` |
| `wire.py`: composite header, ratchet message, `CONCAT`, initial message, prekey bundle, `EncodeEC`/`EncodeKEM`, every stated decoder refusal, the initiator's bundle refusals | message-format.md, session-establishment.md | `post-quantum/composite.json`, `serialization/*.json`; refusals by derived cases only |
| `aes.py`, `aead.py`: AES-256 (FIPS 197), CBC, PKCS#7, HMAC-SHA256 tag, the four receiver steps, one authentication failure | message-format.md Authenticated encryption | FIPS 197 C.3 block example only; **no vector** |
| `ratchet.py`: Double Ratchet (initialisation, derivations, 80-byte expansion, DH step triggers, `MAX_SKIP` on `PN` and on `N` separately, store bound, stale same-chain refusal, counter ceilings, exact expiry and clock ceiling, eviction order); pure functions returning candidate states | ratchet.md, CONSTANTS.md, key-deletion.md | `ratchet/double-ratchet.json`, `malformed-input/ratchet-reject.json`; the rest by derived cases |
| `spqr.py`: sparse ratchet (derivations, send counter and chain choice, 64-bit ceilings, `NoChain`/`OutOfOrder`/`ChainExhausted`/`ChainRetired`, total bound, eviction, retention, chains order) | sparse-pq-ratchet.md, session-persistence.md | `post-quantum/spqr.json` (chain step only) |
| `triple.py`: split and its halves, combination through the expansion, encrypt/decrypt with the commit rules, the non-contributory check, eviction retry; the Braid is an injected boundary with test doubles | triple-ratchet.md, ratchet.md, sparse-pq-ratchet.md | `post-quantum/triple.json`, `split.json` (bytes only) |
| `pqxdh.py`: `KDF`, `AD`, DH1..DH4 with the all-zero refusal, decapsulation-length refusal, repeated-initial rule | session-establishment.md, message-format.md | `session-establishment/pqxdh-sk.json` |
| `gf65536.py`, `erasure.py`: GF(2^16), chunking, systematic and parity codewords, first-copy-wins decoding, encoder exhaustion | mlkem-braid.md The erasure code, CONSTANTS.md | `post-quantum/gf.json`, `inv.json`, `interp.json` (field and interpolation only) |
| `braid.py`: epoch key and authenticator update (hypotheses: GAPS.md G-22, G-23, still open) | CONSTANTS.md labels only | `post-quantum/braid.json`, `auth.json` |
| `persistence.py`: readers and writers with every stated refusal and semantic rule for the ratchet, sparse ratchet and triple states, erasure sub-formats, Braid (12 tags), session, and prekey store (v4 written; v1-v3 read; `kem_pair` checks) | session-persistence.md, CONSTANTS.md | **no vectors** |
| `protobuf.py`: bounded protobuf profile, both message types | protobuf-profile.md, CONSTANTS.md | **no vectors** |
| `identity.py`: identity secret, application signatures | identities-and-devices.md | **no vectors** |

## Derived cases

Each case cites the page and sentence it tests. One module per area, each a row
in the runner's table:

| Module | Cases | Covers |
|---|---|---|
| `negative_cases.py` | 59 | wire decoders and refusals (including identifier 0, curve byte, KEM lengths), bundle signatures, non-contributory DH, ratchet and sparse ratchet basics, field |
| `cases_ratchet.py` | 17 | counter ceilings, clock ceiling, stale same-chain refusal, DH triggers, `PN` skip rules, store bound, eviction order, sparse ceilings and eviction |
| `cases_triple.py` | 10 | split halves, expansion of the combination, send on a copy, candidate adoption, AD binding, non-contributory check order, eviction retry in both stores, epoch advance |
| `cases_aead.py` | 12 | FIPS 197 KAT, round trips, padding, tag input, every refusal, one failure kind, no decryption before the tag |
| `cases_erasure.py` | 10 | table arithmetic equals the definition, chunking, codewords (with `interp.json` values), decoding from any `k`, first copy wins, exhaustion |
| `cases_persistence.py` | 23 | round trips and every stated refusal and semantic rule of each format |
| `cases_protobuf.py` | 9 | varints, tags, bounds, both field tables, free order |
| `cases_identity.py` | 5 | application signatures, label separation, clamping on use, repeated initial message, non-contributory definition |

The runner was also checked against deliberate faults:

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

Each produced FAILs that included the targeted case. For the two persistence
faults the targeted case could not be isolated from other failures the
injection caused.

## Not implemented

- ML-KEM-1024 and the incremental KEM split.
- The ML-KEM Braid state machine, its MACs and authenticator initialisation.
- The end-to-end handshake and `Session`.
- Prekey store operations and the last-resort replay record.

Reasons are in `../GAPS-2.md` ("Not attempted"). No vector file needs any of
these, so the runner reports no SKIPs.

## Running

```
python3 reader/run.py          # from the clean-room directory
```

The runner prints:

1. one line per vector (`PASS`, `FAIL` with a short diff, or `SKIP` with a reason);
2. one line per derived case;
3. a per-file table with a vectors subtotal, a derived-cases subtotal and a total.

The exit status is non-zero on any FAIL.

Current result:

| | Count | PASS | FAIL | SKIP |
|---|---|---|---|---|
| Vectors (19 files) | 79 | 79 | 0 | 0 |
| Derived cases (8 modules) | 145 | 145 | 0 | 0 |
| **Total** | 224 | 224 | 0 | 0 |

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

`../GAPS.md` records where the specification was not enough on 2026-09-11,
when the reader was first written. `../GAPS-2.md` re-assesses every entry
against the revision above and adds this pass's gaps. A gap is closed by
changing the specification. Its entry is marked closed when the reader is next
updated from the new text.
