# tacenta_reader: a clean-room second reading of tacenta-spec

An independent implementation of parts of the Tacenta protocol specification,
written to test whether the specification alone is enough to build from.
Python 3, standard library only (`hashlib`, `hmac`, `json`, `copy`,
`dataclasses`).

## Provenance

Written only from the specification in `../tacenta-spec` and the vectors,
schemas and conformance manifest in `../tacenta-test-vectors`, together with
the public standards those documents name (RFC 2104, RFC 5869, FIPS 180-4,
RFC 7748, RFC 8032, and XEdDSA revision 1), and the published Double Ratchet
and ML-KEM Braid specifications only where a page in the spec tree defers to
them. It was written without reading or searching anything outside this
clean-room directory, without network access, and without consulting any
existing implementation of these protocols (tacenta-core, tacenta-model, the
Rust vector runner, libsignal, or anything else).

Wherever the spec did not state something and a value had to be guessed and
checked against a vector, the code comment names the entry in `../GAPS.md`.
A hypothesis that matches a vector is still recorded as a gap.

## What it implements

| Module | Spec source | Pinned by |
|---|---|---|
| `kdf.py`: HMAC-SHA256, HKDF-SHA256 | RFC 2104, RFC 5869 | `primitives/hmac-sha256.json`, `hkdf-sha256.json` |
| `wire.py`: composite header, ratchet message, `CONCAT(ad, header)`, initial message, prekey bundle, `EncodeEC`/`EncodeKEM`, every decoder refusal the spec states, and the initiator's bundle refusals (identity, presence disagreement, both signatures) | message-format.md, session-establishment.md | `post-quantum/composite.json`, `serialization/*.json`, negative cases |
| `ratchet.py`: Double Ratchet (KDF_RK, KDF_CK, message-key expansion, symmetric and DH ratchets, skipped keys, `MAX_SKIP`, `MAX_SKIPPED_STORE`, `MAX_SKIPPED_AGE` expiry), with Diffie-Hellman injected as bytes | ratchet.md, CONSTANTS.md, key-deletion.md | `ratchet/double-ratchet.json`, `malformed-input/ratchet-reject.json`, negative cases |
| `pqxdh.py`: `KDF(F || KM)`, `AD`, DH1..DH4 with the non-contributory refusal | session-establishment.md | `session-establishment/pqxdh-sk.json`, negative cases |
| `triple.py`: `KDF_HYBRID` combination, `split_secret` | triple-ratchet.md, CONSTANTS.md | `post-quantum/triple.json`, `split.json` |
| `spqr.py`: sparse PQ ratchet derivations and state machine (directions, per-epoch chains, skipped store, epoch retirement, refusals) with the agreement injected | sparse-pq-ratchet.md, session-persistence.md (retention predicate) | `post-quantum/spqr.json` (chain step only); state machine by negative cases |
| `braid.py`: epoch key and authenticator update only | mlkem-braid.md, CONSTANTS.md (+ hypotheses) | `post-quantum/braid.json`, `auth.json` |
| `gf65536.py`: GF(2^16) multiply, inverse, Lagrange interpolation | mlkem-braid.md (+ polynomial inferred from vectors) | `post-quantum/gf.json`, `inv.json`, `interp.json` |
| `curve25519.py`: X25519, Ed25519, XEdDSA sign and verify (with the accepted set CONSTANTS.md and ADR-0002 describe) | RFC 7748, RFC 8032, XEdDSA rev. 1, CONSTANTS.md, ADR-0002 | `primitives/x25519.json`, `ed25519.json`, `xeddsa.json` |

`negative_cases.py` holds 56 cases derived from spec sentences (each cites the
page and the sentence): truncation, version and type bytes, `ag_type` range,
presence bytes, non-zero padding, trailing bytes, length overruns, a
single-byte mutation sweep asserting that whatever the decoder accepts
re-encodes to itself, bundle refusals and signature checks, non-contributory
DH, `MAX_SKIP` and `MAX_SKIPPED_STORE` boundaries, one-use skipped keys, and
the sparse ratchet's refusals and epoch retirement.

## Not implemented

ML-KEM-1024 and the incremental KEM, the ML-KEM Braid state machine and its
erasure encoder/decoder and MACs, the AEAD (AES-256-CBC + HMAC-SHA256), the
full PQXDH handshake and session composition, session persistence and the
prekey store. Reasons are in `../GAPS.md` ("Not attempted"). No vector file
needs any of these, so the runner reports no SKIPs.

## Running

```
python3 reader/run.py          # from the clean-room directory
```

One line per vector (`PASS`, `FAIL` with a short diff, or `SKIP` with a
reason), then one line per negative case, then a per-file totals table. The
exit status is non-zero on any FAIL.

Current result: 78 vectors in 19 files, 78 PASS, 0 FAIL, 0 SKIP; 56 negative
cases, 56 PASS. The runner was also checked against deliberate faults
(swapped KDF_CK outputs, a widened `ag_type` set, no small-order check, a
different field polynomial, a looser `MAX_SKIP`); each one produced FAILs.

## In this repository

Copied into `tacenta-test-vectors/runners/independent/` unchanged, apart from
the one line in `run.py` that says where the vectors are. The `../tacenta-spec`
and `../tacenta-test-vectors` above name the clean-room directory it was
written in; here they are the repository's own `tacenta-spec` and
`tacenta-test-vectors`. Run it from the repository root with

```
python3 tacenta-test-vectors/runners/independent/reader/run.py
```

`tooling/ci.sh` and the CI `vectors` job both run it.

**Keeping it independent** (ADR-0006):
- A change to this reader is made from the specification and the vectors only,
  by someone who has not consulted `tacenta-core`, `tacenta-model`,
  `tacenta-proofs` or the Rust runner for that change.
- When a change to the specification, the model or the vectors breaks it, the
  breakage is a question about the specification, answered there, and not by
  reading the implementation.

`../GAPS.md` is the record of where the specification was not enough, as it
stood when the reader was written (2026-09-11). A gap is closed by changing the
specification. Its entry is marked closed when the reader is next updated from
the new text.
