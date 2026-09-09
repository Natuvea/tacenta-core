# Mapping to spec

How each part of the model corresponds to tacenta-spec. Every model definition is
written from the named spec page, not from any other implementation's source.
One definition also draws on this project's own implementation:
`Model/Triple.lean` says in its header that it is written from
`tacenta-spec/protocol/triple-ratchet.md` *and* from
`tacenta-core/triple/src/lib.rs`, because the clone-candidate-commit shape is
an implementation decision the spec page does not carry. That is our own code,
so no third-party boundary is involved; the consequence is that `TripleT3`
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
