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
enters `Failed` at the epoch ceiling. This pins canonical persisted state
read-back, reader refusal and the documented boundary transition.

Tags 1 through 4 require a valid ML-KEM key-pair layout. That layout is the
recorded ADR-0006 delegated boundary, so the harness currently exercises only
an invalid-length refusal there. The harness also does not construct
authenticated MAC-valid Braid message traffic or cover the other receive/send
state-machine branches. Those are separate obligations: do not treat a failed
MAC, a state transition, or a delegated-layout exclusion as interchangeable.

| Obligation | Current evidence | Next closure step |
| --- | --- | --- |
| Sparse operation/invariant inventory | Model and generated differential coverage, but no itemized norm-to-evidence map | Publish the scoped map and identify an actual uncovered operation/invariant before adding a case. |
| Braid persisted-state tags | Model/vector/reader/import comparison for tags 0 and 5--11; invalid-length check for 1--4 | Keep the delegated key-pair layout exclusion narrow and add valid tag evidence only with a specified independent producer. |
| Braid MAC behavior | No MAC-valid or MAC-invalid operation vector | Specify the message construction/provenance and add both an accepted-neighbour and failure-state case. |
| Braid state machine | `Ct2Sampled` boundary transitions only | Specify and drive one additional feasible transition with observable state/output effects. |
