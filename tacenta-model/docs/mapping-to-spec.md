# Mapping to spec

How each part of the model corresponds to tacenta-spec. Every model definition is
written from the named spec page, not from any other implementation's source.
One definition also draws on this project's own implementation:
`Model/Triple.lean` says in its header that it is written from
`tacenta-spec/protocol/triple-ratchet.md` *and* from
`tacenta-core/triple/src/lib.rs`, because the clone-candidate-commit shape is
an implementation decision the spec page does not carry. That is our own code,
so no third-party boundary is involved; the consequence is that `UnitTripleT3`
refines the crate against a model transcribed from it, which is less
independence than the other tiers have.

## Double Ratchet

Source page: `tacenta-spec/protocol/ratchet.md`.

| Spec section | Model definition | File |
|---|---|---|
| Derivations, KDF_CK | `kdfCk` | `Model/State.lean` |
| Derivations, KDF_RK | `kdfRk` | `Model/State.lean` |
| Derivations, message-key expansion | `messageKeys` | `Model/State.lean` |
| State | `State`, `Header` | `Model/State.lean` |
| The symmetric-key ratchet | `deriveChain`, the chain step in `send`/`receive` | `Model/State.lean`, `Model/Ratchet.lean` |
| The Diffie-Hellman ratchet | `dhRatchet` | `Model/Ratchet.lean` |
| Message format (header contents) | `Header`, built in `send` | `Model/Ratchet.lean` |
| Sending and receiving | `send`, `receive`, `trySkipped` | `Model/Ratchet.lean` |
| Skipped keys, MAX_SKIP | `skipMessageKeys`, `maxSkip` | `Model/State.lean` |
| Session initialisation | `initSender`, `initReceiver` | `Model/Ratchet.lean` |

The primitives the spec's Derivations section composes are computed concretely in
`Model/Sha256.lean` (SHA-256) and `Model/Kdf.lean` (HMAC, HKDF), each anchored to
the standard vectors the spec's Sources cite. Diffie-Hellman agreement and the
AEAD are held at the trusted boundary; see `abstraction-boundary.md`.

## The erasure code

Source pages: `tacenta-spec/protocol/mlkem-braid.md` and
`tacenta-spec/protocol/session-persistence.md`. `Model/Erasure.lean` is
imported by the vector generator, the axiom audit and
`Model/PersistedState.lean`, which reads integers with it;
`Model/Braid.lean` keeps the code at its contract.

| Spec section | Model definition | File |
|---|---|---|
| The erasure code, Chunks | `chunkCount`, `chunks`, `element` | `Model/Erasure.lean` |
| The erasure code, Codewords | `codeword`, `Encoder.new` (at most the first 65,536 chunks), `Encoder.advance`, `Encoder.nextCodeword`; the cap changes no codeword issued: `Encoder.new_issue_nextCodeword` | `Model/Erasure.lean` |
| The erasure code, Decoding | `Decoder.new`, `Decoder.add`, `Decoder.chunk`, `Decoder.message` | `Model/Erasure.lean` |
| Erasure coder sub-formats | `Encoder.toBytes`/`ofBytes`, `Decoder.toBytes`/`ofBytes`; `Encoder.ofBytes_toBytes` | `Model/Erasure.lean` |
| Semantic rules of the leaf formats, Erasure encoder and decoder | `Encoder.invariant`, `Decoder.invariant`; `Encoder.new_issue_keeps` | `Model/Erasure.lean` |

The field arithmetic and the interpolation beneath it are `Model/Gf65536.lean`
and `Model/Polynomial.lean` (`interp`).

## The ratchets' persisted states

Source page: `tacenta-spec/protocol/session-persistence.md`.
`Model/PersistedState.lean` is imported by the vector generator and the axiom
audit only. Its states are `Model/State.lean`'s and `Model/SparseRatchet.lean`'s,
with no field added.

| Spec section | Model definition | File |
|---|---|---|
| Ratchet state | `RatchetState.toBytes`, `RatchetState.ofBytes`, `optKeyBytes`/`readOptKey`, `labelsByte`/`readLabels`, `entryBytes`/`readEntry` | `Model/PersistedState.lean` |
| Sparse ratchet state | `SparseState.toBytes`, `SparseState.ofBytes`, `directionByte`/`readDirection`, `chainBytes`/`readChain`, `chainsEntryBytes`/`readChainsEntry`, `skippedBytes`/`readSkipped` | `Model/PersistedState.lean` |
| Semantic rules of the leaf formats, Ratchet state; Stored curve public keys | `RatchetState.invariant`, `RatchetState.keysCanonical` (with `Model.Messages.canonicalKey`) | `Model/PersistedState.lean` |
| Semantic rules of the leaf formats, Sparse ratchet state | `SparseState.invariant`, `SparseState.satAdd` | `Model/PersistedState.lean` |
| Rejection: "wrong version" and "short or malformed" | `Refusal` | `Model/PersistedState.lean` |
| Principles, Canonical and length-prefixed; Validated, not only parsed | `RatchetState.ofBytes_toBytes`, `SparseState.ofBytes_toBytes` (a state that keeps the rules and fits its fields reads back from its bytes); `RatchetState.ofBytes_ok`, `SparseState.ofBytes_ok` (a state a reader accepts keeps the rules, fits its fields, and is written as the bytes it was read from) | `Model/PersistedState.lean` |

Two points the model decides and the page does not, so no vector depends on
them. A buffer too short for its fixed fields whose version byte is not `0x01`
is refused as a wrong version, because the reader reads the version byte
first. And the model's operations count in the naturals, so they do not refuse
the steps past the ceilings ratchet.md and sparse-pq-ratchet.md state (`ns`,
`nr` and a sparse chain's `n` at their maximum, the clock's stop at
`u32::MAX - 1`, the advance to epoch `u64::MAX`); the vectors stop at those
ceilings.

## Scope held to the spec

The spec's Scope section excludes the header-encryption variant of the Double
Ratchet; the model excludes it too. Headers are carried in the clear and bound by
the AEAD's associated data at the implementation layer, so the model represents
`Header` as plain fields and does not model header encryption.

## Not yet modelled

**Sender keys and multi-device**, neither yet scheduled. There is no sender-keys
model file; `Model/MultiDevice.lean` is a five-line scaffold. Their spec pages
state their in-scope surface.

Session establishment is modelled: PQXDH is in
`Model/SessionEstablishment.lean` and its derivation is T3-refined against the
shipped Rust (`Translation/SessionT3.lean`). The mapping rows above cover the
Double Ratchet slice; the session-establishment and post-quantum rows are not
written yet, which is a gap in *this page* rather than in the model.
