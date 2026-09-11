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
| Message-key expansion | Derivations | every step of the model-generated ratchet vectors (`message_keys`: enc, mac, iv, checked by the runner against the implementation's expansion), core AEAD round-trip test |
| Symmetric-key ratchet | The symmetric-key ratchet | in-order vector |
| Diffie-Hellman ratchet | The Diffie-Hellman ratchet | bidirectional and peer-revisits-ratchet-key vectors |
| Skipped keys, MAX_SKIP | Skipped keys | out-of-order vector, `skipMessageKeys_growth`, reject vector |
| Skipped store bound, MAX_SKIPPED_STORE | Skipped keys | `skipMessageKeys_store_bounded`, core store-bound test |
| Session initialisation | Sending and receiving | all vectors (init_sender / init_receiver) |
| Same-chain message below `Nr` with no stored key refused | Sending and receiving | same-chain-duplicate reject vector, `Model.Ratchet` examples (a duplicate after an in-order receive and after a stored-key receive is refused, the next message is still received), `receive_refines` (the model's refusal is part of what the Rust success case refines), core unit test `a_same_chain_duplicate_is_refused_and_changes_nothing` (`OutOfOrder`, state unchanged) |

Vectors: `vectors/ratchet/double-ratchet.json` (`in-order-3`,
`out-of-order-skip`, `bidirectional`, and `peer-revisits-ratchet-key`, in
which a peer returns to a ratchet key it had left and numbers a fresh chain
from zero under a key already in the store) and
`vectors/malformed-input/ratchet-reject.json`
(`reject-too-many-skipped`, a header demanding more than `MAX_SKIP` skips,
which the receiver must reject; and `reject-same-chain-duplicate`, a message
received a second time on the chain the receiver holds, which it must reject
rather than take as the message at `Nr`, followed by the next message, which
it must still accept with the sender's key). Runner:
`runners/rust/tests/ratchet.rs`.

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
  are modelled, their derivations pinned by vectors, their state machines
  established by proof rather than by vectors, and all three integrated into
  `Session`, which drives the classical ratchet, the sparse ratchet, and the
  Braid as one transaction on every encrypt and decrypt. The post-quantum
  section below sets out the state per component and draws that line
  precisely.

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
  (`Model.Braid`) for the agreement, (`Model.Gf65536`, `Model.Polynomial`)
  for the field and the interpolation the erasure code performs,
  (`Model.Erasure`) for the erasure code above them, and
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
The erasure code above the field is pinned the same way, by
`erasure-encode.json` and `erasure-decode.json` (below).
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
| Reed-Solomon erasure coding | Braid §2.2 | implemented (`tacenta-erasure`), systematic by evaluation; **recovery of lost symbols proved** (`Model.Polynomial.unisolvence`); translates with no gap, **T1 complete**, every function proved panic-free under two named boundary assumptions. **T3 covers the field arithmetic only** (`ErasureT3.lean`: `add`, `clmul`, `reduce`, `mul` each refine `Model.Gf65536` for every input, not just the thirty-eight sampled points). `interpolate`, the chunk helpers, and both encoder/decoder entry points have T1 and no refinement, so `Model.Polynomial`'s recovery theorems stay statements about a Lean definition. Above that, the crate enters `BraidT3.lean` as the `ErasureAgrees` boundary assumption. **The code's bytes are pinned by vectors, not by refinement**: `Model.Erasure` states chunking, the systematic and parity codewords, the encoder's lifetime and first-copy-wins decoding byte for byte over `Model.Polynomial.interp`, and the vectors below check the crate against it on the sampled inputs |
| `KDF_HYBRID` and the composite header | §6.3, §6.5 | modelled (`Model.TripleRatchet`, `Model.CompositeHeader`); `KDF_HYBRID` implemented (`tacenta-triple`), pinned by vectors, and **T3-refined** (`UnitTripleT3.lean`, on the three-leaf translation unit). The header encoding is modelled, its round-trip proved, implemented (`serialization::composite`) and pinned by vectors. **No unambiguous-concatenation theorem is claimed or needed**: §7.2's parameters pass the two keys as *salt* and *IKM* rather than as one concatenated input, so distinct pairs are distinct inputs by construction and there is nothing to prove |
| Expanding the handshake secret into two | §7.1 | modelled (`Model.TripleRatchet.splitSecret`, both halves proved thirty-two bytes), implemented (`tacenta_triple::split_secret`), and **T3-refined** (`split_secret_refines`). Driven live: `Session` splits the PQXDH output and initialises both ratchets from the halves |

#### The erasure code, by vector

Specification: `tacenta-spec/protocol/mlkem-braid.md`, The erasure code. Model:
`Model.Erasure`, over `Model.Gf65536` and `Model.Polynomial`. Runner:
`runners/rust/tests/post_quantum.rs`, against `tacenta-erasure`'s `Encoder`
and `Decoder`.

| Component | Spec section | Covered by |
|---|---|---|
| Chunks: 16 big-endian elements each, `k = ceil(n / 32)`, the last padded with zero bytes | The erasure code, Chunks | `erasure-encode.json` (`one-chunk-padded`, `last-chunk-padded`), `erasure-decode.json` (`short-value-truncated`) |
| Systematic codewords `i < k` are the chunks | The erasure code, Codewords | every `erasure-encode.json` vector; `erasure-decode.json` `systematic-in-order` |
| Parity codewords `i >= k`: `P_j(i)` through the chunks | The erasure code, Codewords | `erasure-encode.json`: values of three, four, six and 48 chunks (the Braid's header with MAC, `ct2` with MAC and `ek_vector` sizes), at indices up to 4,096 |
| The encoder issues indices in order, once each, and nothing after 65,535 | The erasure code, Codewords; Encoder lifetime | `erasure-encode.json` (the runner checks every issued index), `stream-exhaustion` (`stream_length` 65,536) |
| Decoding from any `k` codewords, in any order, at any indices | The erasure code, Decoding | `erasure-decode.json` (`parity-only`, `mixed-out-of-order`, `far-indices`, `ek-vector-two-chunks-lost`) |
| First copy at an index wins, whatever a later one holds; a held chunk `t` is taken as it is | The erasure code, Decoding | `erasure-decode.json` (`later-copy-ignored`, `first-copy-wins-though-corrupt`, `held-chunk-taken-as-it-is`, `repeats-do-not-count`) |
| Every codeword after the `k`-th is ignored | The erasure code, Decoding | `erasure-decode.json` (`ignored-once-full`, `empty-value-ignores-codewords`) |
| Fewer than `k` codewords are no value; a decoder for zero bytes holds the empty value | The erasure code, Decoding | `erasure-decode.json` (`one-short`, `nothing-arrived`, `empty-value`) |

Not pinned: an encoder for a value longer than 65,536 chunks, which the text
does not cover and `tacenta-erasure` caps; parity codewords of a zero-length
value, for which "the polynomial of degree below `k`" has no points.

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

### Addition: reserved counter ceilings

Three of the crates reserve the top value of a counter the published algorithms
leave unreserved, and the models -- which count in `Nat` -- have no notion of a
reserved counter value at all. Recorded here for the same reason the store's
total bound is: it is this implementation's addition, and it is a deliberate
divergence from the model rather than a discrepancy to be fixed.

- `tacenta-ratchet`'s skipped-key clock stops at `MAX_EVENTS = u32::MAX - 1`:
  `age_store` clamps the saturating step there rather than reaching `u32::MAX`.
- `tacenta-spqr`'s `advance` refuses the step to `epoch == u64::MAX` and
  returns `ChainExhausted`, because at that epoch the retention window would
  retire every chain including the one just opened.
- `tacenta-braid`'s `step_receive` refuses the same step in transitions (5)
  and (13), answering `Failed`.

In each case the reservation makes the crate's own `invariant()` clause
inductive: `from_bytes` then refuses only states the operations cannot build,
rather than refusing a state the crate itself could export and never import
again. The models reserve nothing and keep counting, so the refinement
theorems are stated one step below the ceiling
(`tacenta-proofs/CLAIMS.md` and `LIMITATIONS.md` carry the exact
preconditions). No vector drives a counter anywhere near these values; the
divergence is established by the crates' own tests
(`the_clock_stops_one_below_its_ceiling`, `the_epoch_ceiling_is_unreachable`,
`the_epoch_ceiling_is_out_of_reach`) and by the proofs, not by this directory.

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

### Also covered, outside this directory

The initial-message encoding and the prekey-bundle encoding are specified in
`tacenta-spec/protocol/message-format.md` (Initial message; Prekey bundle);
the former has vectors under the Message format section below, the latter a
core round-trip test. Key identifiers, one-time-key consumption after
authentication, replenishment, the last-resort replay record, and signed and
KEM prekey rotation are specified in `key-deletion.md` and covered by core
tests; the prekey store's persisted layout is in `session-persistence.md`
(Prekey store).

### Not yet covered

One-time-key selection and depletion on the *server* side, which is outside
this implementation; the client's expectations of the server are stated in
`key-deletion.md`, Prekeys at rest.

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
| Ratchet message encoding | `vectors/serialization/message-encoding.json`, and `decode_encode_composite` (round-trip proof of the composite header) |
| Header encoding | same |
| `CONCAT(ad, header)` uniqueness | core and model tests: two splits of the same bytes differ |
| Initial (prekey) message encoding | `vectors/serialization/initial-message.json`, generated from the model, and a core round-trip test |
| Prekey bundle encoding (message-format.md, Prekey bundle) | core round-trip and rejection tests; no vectors, since the model does not encode bundles |
| Rejection of unknown version, truncation, and length overrun | core tests |
| Authenticated encryption (message-format.md, Authenticated encryption): PKCS#7 padding, `ciphertext \|\| HMAC-SHA256(mac_key, AD \|\| ciphertext)`, and the receiver's four steps | `vectors/aead/aead-encrypt.json` (padding of 16, 15 and 1 bytes; `AD` empty, short, and a `CONCAT(ad, header)`), `vectors/aead/aead-decrypt.json` (three accepted inputs; refusals at step 1, at step 2 for an altered tag, an altered ciphertext and other associated data, at step 3 for an empty and a partial-block ciphertext under a valid tag, and for a padding byte of 0, of 17, of 2 over a 3, and of 16 over fifteen other bytes); runner `runners/rust/tests/aead.rs`, which also requires every refusal to be the one `DecryptError` |

Runners: `runners/rust/tests/serialization.rs`, and `runners/rust/tests/aead.rs`
for the AEAD.

**Where the AEAD vectors' bytes come from.** The model has no AES, so these
two files are neither model output alone nor a published vector alone. The
generator (`Vectors.lean`, `lake exe genvectors aead-encrypt` and
`aead-decrypt`) computes the padding, the tag (with `Model.Kdf.hmac`) and the
receiver's decision from the section's text, and takes every AES-256 block
value from NIST SP 800-38A under that standard's key: the four ECB-AES256
pairs of F.1.5 and the CBC-AES256 chain of F.2.5. Each IV is chosen so the
cipher's input is one of those blocks, and a block outside that table fails the
file rather than being computed. Each file's `source` field says so. Two
consequences follow. The keys are the standard's, not an output of the
message-key expansion, so the expansion is pinned by the ratchet vectors'
`message_keys` and not here. And a whole-block plaintext, whose padding needs
a second enciphered block the standard does not list, has no encrypt vector;
the padding of 16 is pinned by the empty plaintext instead.

### Determined elsewhere

The message version byte, the field order and widths, and the absent-identifier
sentinel are our own conventions, gathered in one place in the spec, the model,
and the core. The `EncodeEC` and `EncodeKEM` leading bytes are the values that
must match a peer at the bundle layer, and `tacenta-spec/CONSTANTS.md` records
their provenance. Message-layer interoperability with any other implementation
is not claimed, and this is recorded rather than implied.

## Protobuf profile

- **Specification:** tacenta-spec/protocol/protobuf-profile.md. The field
  numbers and wire types are tier `nominated` (CONSTANTS.md); the bounds and
  refusal policies are ours.
- **Oracle:** tacenta-model (`Model.Protobuf`, `parseRatchetBody` and
  `parsePrekeyBody`). Runner: `runners/rust/tests/protobuf.rs`, against
  `tacenta-protobuf`'s `parse_ratchet_body` and `parse_prekey_body`.

Vectors: `vectors/protobuf/protobuf-ratchet-body.json` and
`protobuf-prekey-envelope.json`. An accepted region carries `fields`, the
values it decodes to, integers as four big-endian bytes; a refused one carries
`result: invalid`. The runner checks the names as well as the values, so an
absent `prekey_id` must decode as absent.

### Covered

| Component | Spec section | Covered by |
|---|---|---|
| `maxMessageLen`: 16,384 bytes accepted, 16,385 refused | Bounds | `at-the-length-bound`, `over-the-length-bound` in both files |
| Varints: minimal, at most five bytes, at most `2^32 - 1`, not cut off | Varints | ratchet body: `widest-varints`, `non-minimal-varint`, `non-minimal-length`, `six-byte-varint`, `varint-over-32-bits`, `varint-truncated`; envelope: `registration-id-over-32-bits` |
| Tags: field 0 and fields above 15 refused, wire types other than 0 and 2 refused, a multi-byte tag refused | Tags | `field-zero`, `field-sixteen`, `wire-type-one`, `wire-type-five`, `non-minimal-tag` |
| Length-delimited fields: a zero length accepted, a length past the region refused | Length-delimited fields | `empty-values-and-zero-counters`, `empty-values-and-zero-identifiers`, `length-overruns-the-region` |
| A repeated field refused; an undefined number or the other wire type refused; leftover bytes refused | Fields in a message | `repeated-counter`, `repeated-after-all-five`, `repeated-prekey-id`, `field-six`, `field-nine`, `field-fifteen`, `counter-length-delimited`, `ciphertext-varint`, `prekey-id-length-delimited`, `kem-varint`, `trailing-zero-byte` |
| Ratchet message body: all five fields required | Ratchet message body | `missing-pq`, `empty-region` |
| Prekey envelope: field 1 optional, absent distinct from 0; fields 2 to 8 required; `message` not parsed | Prekey envelope | `prekey-id-absent`, `prekey-id-zero`, `missing-kem`, `missing-registration-id`, `inner-message-not-parsed` |
| Field order is free | Field order and canonicality | `descending-order`, `interleaved-order`, `shuffled-order` |

### Not covered

The encoders (`encode_ratchet_body`, `encode_prekey_body`): the model defines
none and the page fixes no emission order. The `maxFields` bound is never the
limit reached for these two message types (Fields in a message), so no vector
can reach it.

## Session persistence

- **Specification:** tacenta-spec/protocol/session-persistence.md. Entirely
  ours; nothing here is wire-sensitive.
- **Oracle:** tacenta-model (`Model.Erasure`: `Encoder.toBytes`/`ofBytes` and
  `Decoder.toBytes`/`ofBytes`). Runner: `runners/rust/tests/persistence.rs`,
  against `tacenta-erasure`'s `to_bytes`/`from_bytes`.

### Covered

| Component | Spec section | Covered by |
|---|---|---|
| Erasure encoder layout `next(2) \|\| exhausted(1) \|\| count(4) \|\| chunk(32)[count]`, written by operations and read back to the same encoder, which issues the same next codeword | Erasure coder sub-formats | `vectors/persistence/erasure-encoder-state.json`: fresh, two and six codewords issued, a zero-length value, 65,535 issued (`next` at the last index) and 65,536 (`exhausted`) |
| Erasure encoder refusals and rules: `exhausted` only `0x00`/`0x01`, and only at `next = 65535`; a count the buffer does not hold; trailing bytes; a short buffer | Erasure coder sub-formats; Semantic rules of the leaf formats, Erasure encoder | same file, `bytes` vectors |
| Erasure decoder layout `size(8) \|\| needed(8) \|\| count(4) \|\| codeword[count]`, held codewords in arrival order, read back to the same decoder | Erasure coder sub-formats | `vectors/persistence/erasure-decoder-state.json`: fresh, partial, full, a repeat and an extra not held, a zero-length value |
| Erasure decoder refusals and rules: `needed` other than `ceil(size / 32)`, `needed` above 65,536, values bounded as 64-bit before narrowing, a repeated index, more codewords than `needed`, a count the buffer does not hold, trailing bytes; and the widest decoder accepted | Erasure coder sub-formats; Semantic rules of the leaf formats, Erasure decoder | same file, `bytes` vectors |

**Two readings these vectors decide.** The page leaves two things unstated
(the independent reader's `GAPS-2.md`, G2-04): what `next` counts, and what
order a decoder's codewords are written in. `Model.Erasure` takes `next` as
the index the encoder issues next, and writes held codewords in arrival order;
`tacenta-erasure` does the same, and the `partial`, `repeats-and-extras-not-held`
and `last-index-next` vectors pin both. Until the page states them, these are
the model's readings rather than the page's.

### Not covered

Every other persisted format: the ratchet state, the sparse ratchet state, the
triple ratchet state, the Braid, the session, and the prekey store (v1 to v4),
with their semantic rules. The model states none of them, so there is no
oracle to generate vectors from, and they remain covered by `tacenta-core`'s
round-trip and refusal tests and its fuzz targets. The encoder rule "at most
65,536 chunks" is not pinned, since a vector for it is two megabytes.

## Interoperability with libsignal

Scope is the bundle layer: prekey-bundle exchange and the session establishment
it enables. Our side of that layer is specified in
`tacenta-spec/protocol/message-format.md` (Prekey bundle) and
`session-establishment.md`. Any result is obtained against a pinned official
libsignal release through the neutral harness (ADR-0004) and claimed by
version and covered surface; see "Not yet covered" below for the current
state of execution.
Message-layer interoperability is out of reach under the clean-room boundary and
is not claimed.

The concrete, version-specific wire facts a peer requires are determined under
the interoperability research boundary (ADR-0003, ADR-0005) and maintained with
the harness rather than restated here, since they encode third-party
version detail rather than anything about this implementation.

## Primitives

RFC and NIST known-answer vectors, checked by `runners/rust/tests/primitives.rs`
and, for the hash and its derivations, against the model at build time. Each
row says what the vectors are checked against, because it is not the same
thing in every row.

| Primitive | Source | Vectors | Checked against |
|---|---|---|---|
| SHA-256 | NIST FIPS 180-4 examples | model build-time checks | the model's own SHA-256 |
| HMAC-SHA256 | RFC 4231 | `vectors/primitives/hmac-sha256.json` | tacenta-core |
| HKDF-SHA256 | RFC 5869 | `vectors/primitives/hkdf-sha256.json` | tacenta-core |
| X25519 | RFC 7748 | `vectors/primitives/x25519.json` | tacenta-core |
| AES-256 | NIST SP 800-38A, F.1.5 (ECB-AES256) and F.2.5 (CBC-AES256) | no file of its own: the block values are embedded in `vectors/aead/` (Message format, above) | tacenta-core's AEAD, through `aead::encrypt` and `aead::decrypt` |
| Ed25519 | RFC 8032 | `vectors/primitives/ed25519.json` | `ed25519-dalek`, the trusted-boundary crate `xeddsa::verify` calls; tacenta-core exposes no Ed25519 API of its own, so the runner checks the crate directly at the version its lockfile pins |
| XEdDSA | project-generated | `vectors/primitives/xeddsa.json` | tacenta-core: three signing vectors, signed under a fixed nonce and verified; thirteen verify-only vectors at the edges of the accepted set (`s + l`, `s >= 2^253`, the sign bit, small-order `A` and `R`, non-canonical `R` and `u`, `u = p - 1`), each refused or accepted as its `result` says, with a per-vector comment stating whether XEdDSA Revision 1's `xeddsa_verify` accepts the same input, held to a transcription of that pseudocode by a test in `primitives/xeddsa.rs`, which in turn holds the transcription to ed25519-dalek's non-strict `verify` on every vector where both are defined, the four small-order-`A` vectors among them |

**XEdDSA has no published known-answer vectors**: the specification carries
none. The signing vectors are this implementation's own output for a fixed
key, nonce and message, recorded so that a change to the nonce derivation,
the scalar negation, or the sign-bit handling shows up as a diff. They are a
pin, not a validation against an authority, and the row says so. The
independent check is that every signature verifies under `ed25519-dalek`'s
strict verifier, a separate implementation of the underlying scheme. The
verify-only vectors pin the other thing a reader needs to know about a
verifier with no authority to check against: exactly where its accepted set
ends, and on which side of each edge Revision 1 stands.

## Not yet covered

Sender keys and multi-device are not yet scheduled and have no vectors. Session
establishment: see the PQXDH section above for what the vectors reach and what
core tests cover instead. Malformed-input handling is covered by vectors for
the ratchet's skip bound, the AEAD's refusals, the protobuf profile's
refusals and the erasure coders' stored-state refusals; the broader cases
(truncated headers, length overruns, the bundle's presence rule, the other
persisted formats) are covered by core tests and by the fuzz targets rather
than by files in this directory.
Interoperability against a libsignal-based peer is bundle-layer scope: the
harness contract is defined (the neutral adapter API, the black-box boundary,
and claim-by-version discipline) and session establishment is implemented;
what remains is a run against a pinned libsignal build, and the harness and
its adapters are not part of this public tree.
