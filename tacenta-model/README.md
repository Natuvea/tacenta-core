# tacenta-model

Executable / formal mathematical model.

The formal statement of the specification (Lean): the same definition as
`../tacenta-spec`'s prose, against which the proofs are stated and the
implementation is shown to refine. It belongs to the specification, not to
the implementation. Where it and the prose disagree, the specification is
defective and both are fixed
(`../tacenta-spec/decisions/ADR-0006-specification-is-normative.md`).
The model is also the vector oracle: it
computes the protocol key schedule to exact bytes, so protocol-level test vectors
are generated from it rather than from the implementation checking itself.

Build with `lake build`, on the Lean toolchain `lean-toolchain` names
(installed through elan). That builds the model, the properties, the vector
generator `genvectors` and the differential harness `difftest`, so a change
that breaks either executable fails here rather than at the next regeneration
or the next run; `../tacenta-test-vectors/regenerate-vectors.sh` runs the
generator and says which files it writes, and `Difftest.lean` says what the
harness reads and prints (`../tacenta-test-vectors/README.md`, Differential
testing against the model). The derivations are anchored to standard known-answer
values (NIST for SHA-256, RFC 4231 for HMAC, RFC 5869 for HKDF) checked at build
time, and the ratchet carries build-time self-consistency checks.

- `Model/Sha256.lean`, `Model/Kdf.lean`: SHA-256, HMAC-SHA256, HKDF-SHA256, from
  scratch, no dependency.
- `Model/State.lean`, `Model/Ratchet.lean`: the Double Ratchet state, key
  schedule, and send/receive procedures.
- `docs/abstraction-boundary.md`: what the model computes versus what it holds at
  the trusted boundary, and why the split is sound.
- `docs/mapping-to-spec.md`: each model definition mapped to its spec section.

Status: everything the engine runs is modelled. Beyond the Double Ratchet slice
the model now carries PQXDH session establishment
(`Model/SessionEstablishment.lean`), the sparse post-quantum ratchet
(`Model/SparseRatchet.lean`), the ML-KEM Braid and the field and polynomial
theory beneath it (`Model/Braid.lean`, `Model/Gf65536.lean`,
`Model/Polynomial.lean`), the erasure code's bytes and its coders' persisted
formats (`Model/Erasure.lean`), four persisted states with their readers and
the rules the readers enforce -- the classical ratchet's, the sparse
ratchet's, the Triple Ratchet's and the ML-KEM Braid's
(`Model/PersistedState.lean`, which proves of each that it reads back what it
writes and that its reader accepts only what it writes), the Triple Ratchet
(`Model/Triple.lean`, `Model/TripleRatchet.lean`), the composite header, and a
protobuf profile. The vectors are generated from the two persistence modules,
and apart from the vector generator, the differential harness and the axiom
audit only `Model/PersistedState.lean` imports the erasure module.

Two things the persisted-state model deliberately stops short of. The
session's and the prekey store's formats are not modelled at all. And in the
Braid's tags 1 to 4 the `key_pair`'s own `header` and `ek_vector` are checked
for the field's length and nothing else: the page has a reader validate them,
and where they sit inside the 11,872 bytes is a library layout ADR-0006, point
5, delegates. `Model/PersistedState.lean`'s header and
`docs/mapping-to-spec.md` say what follows for those four tags.

Two are still scaffolds and are named rather than left to be discovered:
`Model/MultiDevice.lean` is five lines, and there is no sender-keys model at all.
Neither is yet scheduled.

## Trademarks and non-affiliation

tacenta-core and Tacenta are not affiliated with, endorsed by, or sponsored by
Signal Messenger LLC or the Signal Foundation. "Signal" and "libsignal" are used
only to name the published protocols and the third-party software they refer to.
