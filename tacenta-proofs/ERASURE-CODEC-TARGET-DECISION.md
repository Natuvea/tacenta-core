# Erasure codec target decision

## Decision

For the current second external proof-ledger engagement, the erasure codec's
recorded target is **L3**, its present level. This decision replaces the
unfunded L4 target; it does not claim a full codec refinement or change any
protocol behaviour.

The L3 evidence is specific:

- translated panic-freedom covers the encoder and decoder entry points;
- the Lean model proves the GF(2^16) field used by the codec;
- generated encoding/decoding and persisted-coder vectors run through the Rust
  implementation and the specification-only reader;
- Braid fuzzing and real-ML-KEM state-machine controls exercise the codec on
  the live agreement path.

None of those is a proof that the concrete encoder or decoder refines the
model for every input. `ERASURE-DECODER-REFINEMENT.md` and `LIMITATIONS.md`
remain the record of that boundary.

## Why L4 is not claimed

The remaining L4 work is a coherent proof programme, not a small omitted
lemma. It needs all of the following:

1. prove the barycentric implementation's `weights`, `coefficients` and
   `evaluate` equal the model interpolation expression;
2. establish a concrete representation relation for decoder offers,
   duplicates, completion and malformed/inconsistent codewords;
3. prove encoder and decoder preservation of that relation, including valid
   recovery; and
4. port the resulting theorems to `tacenta-braid-unit`, where erasure has real
   translated bodies. The standalone Braid translation imports a separately
   translated erasure crate as opaque symbols, so its `ErasureAgrees`
   assumption cannot be discharged by a theorem over the standalone leaf.

The existing completed-decoder theorem establishes only one concrete leaf
effect. Treating it as a Braid refinement would hide the three unfinished
steps above.

## Target effect and revisit triggers

The component table now records L3 as both current and target, and the P7
erasure obligation is closed by this scoped decision. The deferred
`PROOF-ERASURE-REFINEMENT` row remains visible: it is not evidence of L4 and
does not authorize an L4 claim.

Reopen the L4 target before any claim that the codec is fully refined, or when
any of the following occurs:

- the encoder, decoder, field representation, coding parameters, or persisted
  coder format changes;
- a shipped feature relies on erasure recovery as an independently verified
  security or correctness property;
- the Braid-and-erasure unit gains a decoder relation or an implementation
  starts using its theorems; or
- an external review asks for a codec refinement claim.

The reopening work starts with the four proof steps above and must restore an
L4 target before it can be closed.
