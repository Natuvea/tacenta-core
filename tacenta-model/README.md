# tacenta-model

Executable / formal mathematical model.

The formal model of the protocol (Lean), against which the proofs are stated and
the implementation is shown to refine. The model is also the vector oracle: it
computes the protocol key schedule to exact bytes, so protocol-level test vectors
are generated from it rather than from the implementation checking itself.

Build with `lake build`. The derivations are anchored to standard known-answer
values (NIST for SHA-256, RFC 4231 for HMAC, RFC 5869 for HKDF) checked at build
time, and the ratchet carries build-time self-consistency checks.

- `Model/Sha256.lean`, `Model/Kdf.lean`: SHA-256, HMAC-SHA256, HKDF-SHA256, from
  scratch, no dependency.
- `Model/State.lean`, `Model/Ratchet.lean`: the Double Ratchet state, key
  schedule, and send/receive procedures.
- `docs/abstraction-boundary.md`: what the model computes versus what it holds at
  the trusted boundary, and why the split is sound.
- `docs/mapping-to-spec.md`: each model definition mapped to its spec section.

Status: everything the engine runs is modelled. Beyond the Double Ratchet slice the model now carries PQXDH session establishment
(`Model/SessionEstablishment.lean`), the sparse post-quantum ratchet
(`Model/SparseRatchet.lean`), the ML-KEM Braid and the field and polynomial
theory beneath it (`Model/Braid.lean`, `Model/Gf65536.lean`,
`Model/Polynomial.lean`), the Triple Ratchet (`Model/Triple.lean`,
`Model/TripleRatchet.lean`), the composite header, and a protobuf profile.

Two are still scaffolds and are named rather than left to be discovered:
`Model/MultiDevice.lean` is five lines, and there is no sender-keys model at all.
Both are milestone M4.
