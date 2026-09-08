# Conformance manifest

Exactly which specifications, revisions, and components the vectors cover, and
what is deliberately excluded. The point is an honest coverage claim: an omission
is recorded here rather than left implied.

## The pinned specifications

Each protocol document this manifest covers is written from a published Signal
specification, from a copy "pinned by SHA-256" (the section for it says so).
This is where the pins are, so that provenance can be checked from inside this
repository rather than taken on trust. Where a document also records Tacenta's
own analysis or extensions, the section says which parts those are.

| Document | Revision as published | SHA-256 |
| --- | --- | --- |
| `pqxdh.pdf` | Revision 3, 2023-05-24, last updated 2024-01-23 | `9fd0e02a5e13075b64adc7aa6dc9baade4f65af70b5571a332991756d98fe896` |
| `doubleratchet.pdf` | Revision 4, 2025-11-04 | `1d9b4dc3c6440b0777d747ff42707fccba3a45d209a2bdc33d1ea816aa05990c` |
| `mlkembraid.pdf` | Revision 1, 2025-02-21, last updated 2025-09-26 | `c38a3ab844c7c583e7be15ff714b07792220cb662b5d1e9590e46aa5909a3ee6` |
| `x3dh.pdf` | Revision 1, 2016-11-04 | `4f699ce92b5afdc1fb7d2f670f18f48372895c30a84cd34e9aec3589dc851a49` |
| `xeddsa.pdf` | Revision 1, 2016-10-20 | `a65684d87d747934e5b05698ed20bec72cd3c30e3f7ff2f6376555d65a5104b7` |
| `sesame.pdf` | Revision 2, 2017-04-14 | `e7eca9fdc7bf79a769bea626fd39bf21fbaee5a9ac6bae9350e63768d9502593` |

Retrieved from `https://signal.org/docs/specifications/<name>/<name>.pdf` on
2026-07-24, except the ML-KEM Braid, retrieved 2026-07-26.

The documents themselves are not redistributed here. They are Signal's to
publish, this repository is licensed differently, and a hash serves the purpose a
copy would: it fixes which revision was implemented. Anyone auditing this work
can fetch the same files
and compare.

These specifications are not the only input category permitted by the current
engineering policy. [ADR-0005](../tacenta-spec/decisions/ADR-0005-segregated-reference-adapter.md)
also permits recorded black-box observation of protocol peers and, for the
isolated reference-adapter role, the consumer-facing API of an official
compiled package. ADR-0005 excludes implementation source from permissible
inputs; libsignal's source code is not an input to this project.

## Double Ratchet

- **Specification:** tacenta-spec/protocol/ratchet.md, written from Signal's
  published Double Ratchet specification (Trevor Perrin, editor; Moxie
  Marlinspike; Rolfe Schmidt, revision 3 and later), **revision 4, 2025-11-04**,
  from the archived copy pinned by SHA-256. We implement Section 3, the Double
  Ratchet proper.
- **Oracle:** tacenta-model (`Model.State`, `Model.Ratchet`). Vectors are
  generated from the model by `lake exe genvectors` and regenerated with
  `regenerate-vectors.sh`.

### Covered

| Component | Spec section | Covered by |
|---|---|---|
| KDF_CK (chain step) | Derivations | ratchet vectors, `deriveChain` proofs |
| KDF_RK (root step) | Derivations | ratchet vectors (bidirectional) |
| Message-key expansion | Derivations | core AEAD round-trip test |
| Symmetric-key ratchet | The symmetric-key ratchet | in-order vector |
| Diffie-Hellman ratchet | The Diffie-Hellman ratchet | bidirectional vector |
| Skipped keys, MAX_SKIP | Skipped keys | out-of-order vector, `skipMessageKeys_growth`, reject vector |
| Skipped store bound, MAX_SKIPPED_STORE | Skipped keys | `skipMessageKeys_store_bounded`, core store-bound test |
| Session initialisation | Sending and receiving | all vectors (init_sender / init_receiver) |

Vectors: `vectors/ratchet/double-ratchet.json` (`in-order-3`,
`out-of-order-skip`, `bidirectional`) and
`vectors/malformed-input/ratchet-reject.json`
(`reject-too-many-skipped`, a header demanding more than `MAX_SKIP` skips,
which the receiver must reject). Runner: `runners/rust/tests/ratchet.rs`.

### Excluded

- **Header-encryption variant.** The published specification defines an optional
  header-encryption mode. The product does not use it, so it is out of scope
  (ratchet.md, Scope). Headers are carried in the clear and bound by the AEAD's
  associated data.
- **Sparse Post-Quantum Ratchet and Triple Ratchet: in scope, not excluded.**
  Post-quantum protection at session establishment alone does not carry across
  a session's life: the handshake protects a session when it is created and
  adds nothing afterwards, so against an attacker recording traffic for a
  future quantum computer, a long-lived session would be protected by the
  handshake alone and by nothing the ratchet does. Signal's current
  specification ratchets post-quantum continuously, and so does this
  implementation.

  Written up in `tacenta-spec/protocol/sparse-pq-ratchet.md` and
  `triple-ratchet.md`. `tacenta-spqr`, `tacenta-triple` and `tacenta-braid`
  are modelled, covered by vectors, and integrated into `Session`, which
  drives the classical ratchet, the sparse ratchet, and the Braid as one
  transaction on every encrypt and decrypt. The post-quantum section below
  sets out the state per component.

### Determined elsewhere

- **Wire `info` values and header/ciphertext byte encodings.** The published
  specification leaves the `info` strings and concrete encodings
  application-specific. The model fixes its own labels so its vectors are
  internally consistent, and `tacenta-spec/CONSTANTS.md` records each label's
  provenance. Message-layer interoperability with a peer is not claimed, so
  the ratchet vectors assert the key schedule, not peer wire compatibility.

## Post-quantum ratcheting (implemented, unevenly verified)

- **Specification:** tacenta-spec/protocol/sparse-pq-ratchet.md,
  triple-ratchet.md and mlkem-braid.md, written from Signal's published Double Ratchet
  specification, **revision 4, 2025-11-04**, Sections 5, 6 and 7.1, and from the
  ML-KEM Braid specification (Rolfe Schmidt), **revision 1, 2025-02-21, last
  updated 2025-09-26**. Both archived and pinned by SHA-256.
- **Oracle:** `tacenta-model` (`Model.SparseRatchet`) for the ratchet,
  (`Model.Braid`) for the agreement, and (`Model.Gf65536`, `Model.Polynomial`)
  for the field and the interpolation the erasure code performs, and
  (`Model.TripleRatchet`) for the Triple Ratchet, the smallest layer.

### Covered

**Implemented and running.** Five crates carry it: `tacenta-erasure`, `tacenta-kem`, `tacenta-braid`,
`tacenta-spqr` and `tacenta-triple`. `tacenta-core/tests/post_quantum_stack.rs`
runs them together against real ML-KEM-1024, eight hundred messages across eight
post-quantum epochs, and survives two of every three agreement messages being
destroyed.

The derivations are pinned to the models by vectors under
`vectors/post-quantum/`: field multiplication and inversion, interpolation, the
sparse ratchet's chain step, and the Braid's epoch key and authenticator ratchet.
That covers the class of transcription error these vectors exist to catch: a
constant such as the Braid's `PROTOCOL_INFO` that differed between the model
and the implementation would change every MAC and every epoch key with it, and
the vectors are what compare the two.

The state machines are not driven by vectors. A derivation is pinned by its
bytes; a state machine is only pinned by running it, and no vectors drive the
Braid or the sparse ratchet through a scenario the way the Double Ratchet's do.
**That gap is covered by proof rather than by vectors** -- `tacenta-spqr`,
`tacenta-braid`, and `tacenta-triple` each carry T1 panic-freedom and T3
refinement against their models, so the state machines are established, just
not by this directory. The row-by-row state below is what is established, and
it names the route in each case.

| Component | Where specified | State |
| --- | --- | --- |
| Sparse continuous key agreement interface | Double Ratchet §5.1 | a boundary in both model and implementation; consumed, not computed |
| `KDF_SCKA_INIT`, `KDF_SCKA_RK`, `KDF_SCKA_CK` | §5.2 | modelled; implemented (`tacenta-spqr`); chain step pinned by vectors |
| Epoch-indexed chains and skipped-key store | §5.3, §5.6 | modelled, store proved to be a map; implemented |
| Skipped keys match in-order keys | §5.6 | proved (`deriveInto_get`) |
| Store bounded in total | this implementation's addition | modelled, proved, and implemented |
| Retiring old epochs | §5.7 | modelled, main-text approach; implemented |
| ML-KEM Braid state machine | Braid §2.5 | modelled (`Model.Braid`), epoch labelling proved; implemented (`tacenta-braid`) and reaching agreement against real ML-KEM; **T1 and T3 both complete** (`BraidT1.lean`, `BraidT3.lean`). One invariant is still assumed rather than proved: `ct1_bounded`, a size cap on the KEM ciphertext, which `step_send` maintains but no theorem yet says so -- see `tacenta-proofs/CLAIMS.md`. Not driven by vectors |
| Ratcheted Authenticator | Braid §2.4 | modelled and computed byte for byte; implemented in `tacenta-braid`; update step pinned by vectors |
| Incremental ML-KEM interface | Braid §1.2.1 | a boundary in the model, with the one law it must satisfy; wrapped from libcrux in `primitives::kem_incremental`, with the size mapping asserted by test |
| GF(2^16) arithmetic | Braid §2.2 | modelled and proved a field (`Model.Gf65536`); implementation pinned by vectors |
| Polynomial interpolation over that field | Braid §2.2 | modelled, delta property and unisolvence both proved (`Model.Polynomial`); implementation pinned by vectors |
| Reed-Solomon erasure coding | Braid §2.2 | implemented (`tacenta-erasure`), systematic by evaluation; **recovery of lost symbols proved** (`Model.Polynomial.unisolvence`); translates with no gap, **T1 complete**, every function proved panic-free under two named boundary assumptions. **T3 covers the field arithmetic only** (`ErasureT3.lean`: `add`, `clmul`, `reduce`, `mul` each refine `Model.Gf65536` for every input, not just the thirty-eight sampled points). `interpolate`, the chunk helpers, and both encoder/decoder entry points have T1 and no refinement, so `Model.Polynomial`'s recovery theorems stay statements about a Lean definition. Above that, the crate enters `BraidT3.lean` as the `ErasureAgrees` boundary assumption |
| `KDF_HYBRID` and the composite header | §6.3, §6.5 | modelled (`Model.TripleRatchet`, `Model.CompositeHeader`); `KDF_HYBRID` implemented (`tacenta-triple`), pinned by vectors, and **T3-refined** (`TripleT3.lean`). The header encoding is modelled, its round-trip proved, implemented (`serialization::composite`) and pinned by vectors. **No unambiguous-concatenation theorem is claimed or needed**: §7.2's parameters pass the two keys as *salt* and *IKM* rather than as one concatenated input, so distinct pairs are distinct inputs by construction and there is nothing to prove |
| Expanding the handshake secret into two | §7.1 | modelled (`Model.TripleRatchet.splitSecret`, both halves proved thirty-two bytes), implemented (`tacenta_triple::split_secret`), and **T3-refined** (`split_secret_refines`). Driven live: `Session` splits the PQXDH output and initialises both ratchets from the halves |

### Addition: the store's total bound

The published algorithm bounds one skip request against `MAX_SKIP` and retires
whole epochs. This implementation additionally caps the store's total size, the
same cap the Double Ratchet uses here, so the store is bounded independently of
how many messages are skipped within an epoch;
`Proofs.SparseRatchetCorrectness.skipMessageKeys_store_bounded` proves it holds.
Recorded here because it is an addition to the specification.

`tacenta-spqr` demonstrates both halves of this in Rust. Three requests on a
single chain in a single epoch, each inside the per-call bound, reach the cap and
the third is refused. And skipping the maximum in every epoch does **not**
accumulate, because retirement drops everything older: the cross-epoch total sits
at exactly `MAX_SKIP * EPOCHS_KEPT`, which is the cap. So the two bounds are
consistent rather than in tension, and the total cap is doing its work against
one chain rather than against many.

### Determined elsewhere

The constants naming the protocol in each derivation, the combination constant,
and the composite header's encoding are ours: the message layer is outside the
interoperability claim, so they are free choices, recorded with their
provenance in `tacenta-spec/CONSTANTS.md` rather than chosen here.

## Session establishment, PQXDH

- **Specification:** tacenta-spec/protocol/session-establishment.md, written from
  Signal's published PQXDH specification (Ehren Kret and Rolfe Schmidt),
  **revision 3, 2023-05-24, last updated 2024-01-23**, with X3DH revision 1 for
  the Diffie-Hellman computations it extends. Both archived and pinned by
  SHA-256.
- **Oracle:** tacenta-model (`Model.SessionEstablishment`).

### Covered

| Component | Spec section | Covered by |
|---|---|---|
| `KDF(KM)` with the `F` prefix and parameter `info` | Notation | `vectors/session-establishment/pqxdh-sk.json` |
| Shared secret without a one-time curve prekey | Sending the initial message | vector `without-one-time-curve-prekey` |
| Shared secret with a one-time curve prekey | Sending the initial message | vector `with-one-time-curve-prekey` |
| Associated data construction | Sending the initial message | core unit tests |
| The four Diffie-Hellman agreements, both sides | Sending / receiving the initial message | core tests: initiator and responder derive the same secret, with and without a one-time curve prekey |
| Prekey signature verification | Sending the initial message | core tests: a forged signed prekey and a forged KEM prekey are both rejected |
| `EncodeEC` / `EncodeKEM` disjoint ranges | Parameters | core test on the leading bytes |
| One identity key for both agreement and signing | ADR-0002 | core test: an XEdDSA signature under the X25519 identity key verifies |
| ML-KEM-1024 encapsulation | Notation, PQKEM-ENC / PQKEM-DEC | core tests: round trip, freshness, implicit rejection, malformed input |
| The full handshake, both sides | The PQXDH protocol | core test with a real KEM prekey |
| Composition into the ratchet | Replay (why a ratchet must follow) | `tests/handshake_to_ratchet.rs`: the secret seeds the ratchet and a message round-trips through the AEAD |

Runner: `runners/rust/tests/session_establishment.rs`.

### Not yet covered

Key identifiers, one-time-key selection and depletion on the server side, and
the initial-message encoding are still to come, as is the deletion discipline
for used private keys.

### Excluded

- **Plain X3DH.** Its shared secret omits the encapsulated secret. We do not
  establish sessions with X3DH-only peers (session-establishment.md, Scope).

## Message format

- **Specification:** tacenta-spec/protocol/message-format.md. Almost nothing here
  is fixed by a published specification: the Double Ratchet document defines
  `HEADER` and `CONCAT` functionally and PQXDH requires only that the initial
  message be unambiguous. The concrete encodings are ours, structured so that the
  wire-sensitive values are isolated in one place.
- **Oracle:** tacenta-model (`Model.Messages`).

### Covered

| Component | Covered by |
|---|---|
| Ratchet message encoding | `vectors/serialization/message-encoding.json`, and `decode_encode` (round-trip proof) |
| Header encoding | same |
| `CONCAT(ad, header)` uniqueness | core and model tests: two splits of the same bytes differ |
| Initial (prekey) message encoding | core round-trip test |
| Rejection of unknown version, truncation, and length overrun | core tests |

Runner: `runners/rust/tests/serialization.rs`.

### Determined elsewhere

The message version byte, the field order and widths, and the absent-identifier
sentinel are our own conventions, gathered in one place in the spec, the model,
and the core. The `EncodeEC` and `EncodeKEM` leading bytes are the values that
must match a peer at the bundle layer, and `tacenta-spec/CONSTANTS.md` records
their provenance. Message-layer interoperability with any other implementation
is not claimed, and this is recorded rather than implied.

## Interoperability with libsignal

Scope is the bundle layer: prekey-bundle exchange and the session establishment
it enables. Any result is obtained against a pinned official libsignal release
through the neutral harness (ADR-0004) and claimed by version and covered
surface; see "Not yet covered" below for the current state of execution.
Message-layer interoperability is out of reach under the clean-room boundary and
is not claimed.

The concrete, version-specific wire facts a peer requires are determined under
the interoperability research boundary (ADR-0003, ADR-0005) and maintained with
the harness rather than restated here, since they encode third-party
version detail rather than anything about this implementation.

## Primitives

RFC and NIST known-answer vectors, checked against tacenta-core by
`runners/rust/tests/primitives.rs` and against the model at build time.

| Primitive | Source | Vectors |
|---|---|---|
| SHA-256 | NIST FIPS 180-4 examples | model build-time checks |
| HMAC-SHA256 | RFC 4231 | `vectors/primitives/hmac-sha256.json` |
| HKDF-SHA256 | RFC 5869 | `vectors/primitives/hkdf-sha256.json` |
| X25519 | RFC 7748 | `vectors/primitives/x25519.json` |
| Ed25519 | RFC 8032 | `vectors/primitives/ed25519.json` |

## Not yet covered

Sender keys and multi-device are later milestones and have no vectors. Session
establishment is partly covered: see
the PQXDH section above for what the vectors reach and what they do not.
Malformed-input handling is covered for the ratchet's skip bound;
broader malformed-input cases (bad decryption, truncated headers) come with the
message-format work. Interoperability against a libsignal-based peer is bundle-layer scope: the
harness contract is defined (the neutral adapter API, the black-box boundary,
and claim-by-version discipline), with execution gated on session establishment
in tacenta-core and a pinned libsignal build.
