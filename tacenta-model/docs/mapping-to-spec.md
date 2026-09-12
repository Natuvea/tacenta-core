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

## The persisted states

Source page: `tacenta-spec/protocol/session-persistence.md`.
`Model/PersistedState.lean` is imported by the vector generator, the
differential harness and the axiom audit. Three of its four states are the
ones the operations run on, with no field added: `Model/State.lean`'s,
`Model/SparseRatchet.lean`'s and `Model/Triple.lean`'s. The Braid's is its
own, because the stored format's erasure coders are `Model/Erasure.lean`'s
byte-level ones where `Model/Braid.lean` holds the code at its contract, and
because two of its fields have no model at all (below).

| Spec section | Model definition | File |
|---|---|---|
| Ratchet state | `RatchetState.toBytes`, `RatchetState.ofBytes`, `optKeyBytes`/`readOptKey`, `labelsByte`/`readLabels`, `entryBytes`/`readEntry` | `Model/PersistedState.lean` |
| Sparse ratchet state | `SparseState.toBytes`, `SparseState.ofBytes`, `directionByte`/`readDirection`, `chainBytes`/`readChain`, `chainsEntryBytes`/`readChainsEntry`, `skippedBytes`/`readSkipped` | `Model/PersistedState.lean` |
| Semantic rules of the leaf formats, Ratchet state; Stored curve public keys | `RatchetState.invariant`, `RatchetState.keysCanonical` (with `Model.Messages.canonicalKey`) | `Model/PersistedState.lean` |
| Semantic rules of the leaf formats, Sparse ratchet state | `SparseState.invariant`, `SparseState.satAdd` | `Model/PersistedState.lean` |
| Triple ratchet state | `TripleState.toBytes`, `TripleState.ofBytes`, `lenPrefixed`/`readLenPrefixed` | `Model/PersistedState.lean` |
| Semantic rules of the leaf formats, Triple ratchet state | `TripleState.invariant`, `TripleState.rolesAgree`, `TripleState.startedAsSender` | `Model/PersistedState.lean` |
| Braid (the tag table, the epoch, the authenticator, the length-prefixed fields) | `BraidState.toBytes`, `BraidState.ofBytes`, `FieldKind`, `kindsOfNat`/`fieldKinds`, `fieldOk`, `readFields`, `BraidState.largestEpoch` | `Model/PersistedState.lean` |
| Semantic rules of the leaf formats, Braid | `BraidState.invariant`, `BraidState.fieldsOk` (every rule that applies; the `key_pair` content clause of tags 1 to 4 is scoped to a reader with the KEM layout, and this model is outside that scope, below) | `Model/PersistedState.lean` |
| Rejection: "wrong version" and "short or malformed" | `Refusal` | `Model/PersistedState.lean` |
| Principles, Canonical and length-prefixed; Validated, not only parsed | `RatchetState.ofBytes_toBytes`, `SparseState.ofBytes_toBytes`, `TripleState.ofBytes_toBytes`, `BraidState.ofBytes_toBytes` (a state that keeps the rules and fits its fields reads back from its bytes); `RatchetState.ofBytes_ok`, `SparseState.ofBytes_ok`, `TripleState.ofBytes_ok`, `BraidState.ofBytes_ok` (a state a reader accepts keeps the rules, fits its fields, and is written as the bytes it was read from) | `Model/PersistedState.lean` |

One point the page leaves to the implementation, so no vector depends on it.
A buffer too short for its fixed fields whose version byte is not `0x01` is
refused as a wrong version, because the reader reads the version byte first
(session-persistence.md, Rejection, allows either refusal).

The operations stop at the ceilings ratchet.md and sparse-pq-ratchet.md state,
so no state they produce holds a counter its format cannot write:
`Model.Ratchet.send` refuses at `ns = u32::MAX` and `Model.Ratchet.receive`
past `nr = u32::MAX` (`Model.State.u32Max`); `Model.State.ageStore` stops the
clock at `u32::MAX - 1` (`Model.State.maxEvents`);
`Model.SparseRatchet.advance` refuses the step onto epoch `u64::MAX` and
`Model.SparseRatchet.send` a send past a chain's counter at `u64::MAX`
(`Model.SparseRatchet.u64Max`). The range lemmas are
`Model.Ratchet.send_ns_le`, `Model.Ratchet.receive_events_lt`,
`Model.SparseRatchet.advance_epoch_lt` and `Model.SparseRatchet.send_number_le`,
and the persistence vectors pin each ceiling.

The Braid's model stops at the epoch ceiling mlkem-braid.md (Failure) and
session-persistence.md (Principles) state: `Model.Braid.receive` refuses, in
transitions (5) and (13), the step onto epoch `u64::MAX` and goes to `failed`
(`Model.Braid.u64Max`). In `EkSentCt1Received` it refuses when `ct2`
completes, before decapsulating; in `Ct2Sampled`, before reading the message.
The range lemmas are `Model.Braid.receive_epoch_lt`,
`Model.Braid.receive_advance_lt` and `Model.Braid.receive_output_epoch_lt`,
and the two refusals are `Model.Braid.receive_ct2Sampled_at_ceiling` and
`Model.Braid.receive_ekSentCt1Received_at_ceiling`.

The stored format is what makes that ceiling pinnable, and both halves of it
are now pinned. The reader's half is `BraidState.ofBytes` refusing a stored
epoch of `u64::MAX`. The transitions' half is driven from stored bytes through
the model's own `receive`: `Model.Braid.receive_ct2Sampled_steps` and
`receive_ct2Sampled_at_ceiling` say that the two transitions out of
`Ct2Sampled` read the stored epoch and the message and nothing else -- neither
the KEM nor the encoder the state holds -- so `BraidState.toCt2Sampled` and
`BraidState.ofBraid` can put a stored state back into the machine and take its
answer out again. That is the one place a stored Braid can be run, and it is
enough for the ceiling.

**What the Braid's model does not state, and why it conforms anyway.** For
tags 1 to 4 the page also requires the `header` and `ek_vector` inside the
stored `key_pair` to pass the KEM split's validation, and **scopes that clause
to a reader that knows the key pair's layout.** Where those two sit inside the
11,872 bytes is `libcrux-ml-kem`'s layout, which the page does not define and
ADR-0006, point 5, delegates. `BraidState.fieldOk` therefore checks
`key_pair`'s length and accepts it, which is exactly what the page asks of a
reader outside the scope, so the model conforms here rather than falling
short. For those four tags it still accepts stored states `tacenta-braid`,
which has the layout, refuses. No vector generated here accepts one and the
differential harness offers none: a state whose key pair fails the clause has
no single conforming verdict, since a reader inside the scope refuses it and
one outside accepts it. The conformance manifest and `ASSURANCE.md` record
this. `encaps`, by contrast, is checked for its length and nothing else by the
page itself, for every implementation, so tags 7 to 9 are modelled in full.

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
