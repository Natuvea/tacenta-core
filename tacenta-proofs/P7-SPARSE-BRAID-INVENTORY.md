# P7 sparse-ratchet and Braid obligation inventory

This inventory records the source inspection behind the remaining P7 vector
and state-machine rows. It is a scope record, not evidence that either
component meets its L4 target.

## Sparse post-quantum ratchet

`Model.SparseRatchet` specifies initialization, epoch advancement, send,
receive, skipped-key lookup and the bounded retained-epoch/store rules. The
differential harness generates sparse send/receive sequences and imports, then
compares the Rust state, canonical persisted bytes, read-back and model refusal
at every step. It explicitly reaches send and receive chain ceilings, the
reserved epoch boundary, stored-key recovery and retirement of an old epoch.

The protocol-vector set remains marked partial because this run is generated
test evidence rather than an inventory of every normative operation and
invariant. The next sparse slice must make that inventory explicit, map each
item to model/vector/differential/reader evidence, and add a missing scoped
case only after identifying one. It must not call the existing generated
coverage a complete L4 vector surface by inference.

## ML-KEM Braid

The harness builds and compares persisted Braid states for tags 0 and 5 through
11, their corrupted imports, and three `Ct2Sampled` receive transitions: one
ordinary transition, one immediately below the reserved epoch, and one that
enters `Failed` at the epoch ceiling. It also completes the three systematic
codewords of an empty `NoHeaderReceived` state: a header MAC made from the
persisted MAC key reaches `HeaderReceived`, while a one-byte MAC mutation
reaches terminal `Failed`. The Lean model independently recomputes that MAC
and compares the resulting persisted state. This pins canonical persisted
state read-back, reader refusal, the documented boundary transition, and one
accepted/failure authenticated-header pair without a KEM value.

Tags 1 through 4 require a valid ML-KEM key-pair layout. That layout is the
recorded ADR-0006 delegated boundary, so the harness currently exercises only
an invalid-length refusal there. The header pair does not cover ciphertext MAC
traffic or the other receive/send state-machine branches. Those are separate
obligations: do not treat a header MAC, a state transition, or a delegated
layout exclusion as interchangeable.

| Obligation | Current evidence | Next closure step |
| --- | --- | --- |
| Sparse operation/invariant inventory | Model and generated differential coverage, but no itemized norm-to-evidence map | Publish the scoped map and identify an actual uncovered operation/invariant before adding a case. |
| Braid persisted-state tags | Model/vector/reader/import comparison for tags 0 and 5--11; invalid-length check for 1--4 | Keep the delegated key-pair layout exclusion narrow and add valid tag evidence only with a specified independent producer. |
| Braid MAC behavior | Differential check of a persisted-key header MAC and a one-byte mutation, with model recomputation | Specify ciphertext-MAC provenance and add accepted-neighbour/failure-state ciphertext evidence. |
| Braid state machine | `Ct2Sampled` boundaries plus empty-`NoHeaderReceived` transition (6) | Identify the next branch that can be driven without a KEM fixture, or make a narrow fixture/scope decision. |
