# P7 sparse-ratchet and Braid obligation inventory

This inventory records the source inspection behind the remaining P7 vector
and state-machine rows. It is a scope record, not evidence that either
component meets its L4 target.

## Sparse post-quantum ratchet

`Model.SparseRatchet` specifies initialization, epoch advancement, send,
receive, skipped-key lookup and the bounded retained-epoch/store rules. The
differential harness generates sparse send/receive sequences and imports, then
compares the Rust state, canonical persisted bytes, read-back and model refusal
at every step.

| Scoped operation or invariant | Model/proof evidence | Differential and vector evidence | Independent-reader evidence | Scope still open |
| --- | --- | --- | --- | --- |
| Initialization and direction | `Model.SparseRatchet.init`; persisted-state semantic rules | Fresh starts in templates 0--1; canonical export/import at each step; committed sparse-state fixtures | Clean-room `tacenta_reader/spqr.py`; CR-12--CR-17 | Fixed vectors pin each direction's initial state; generated templates cover operation variations. |
| Advance only to the next epoch, and never onto the reserved epoch | `advance`, `advance_epoch_lt` | Generated agreement outputs; templates 6--7 reach the reserved boundary and require the same refusal; `advance-onto-u64-max-refused` is a fixed vector | Clean-room SP-07 and CR-17 advance/retention exercises | `EpochOutOfOrder` is generated-only: it has no separate fixed-vector contract. |
| Send and receive counters | `send`, `receive`, `send_number_le` | Templates 2--5 force both chain ceilings and compare every accepted/refused result; fixed vectors pin both ceiling outcomes | Clean-room CR-12 and CR-13 | Counter/refusal permutations beyond the named ceiling cases are generated-only. |
| Skip/store bound, lookup and one-time use | `skipMessageKeys`, `trySkipped`; `deriveInto_*`, `skipMessageKeys_store_bounded`, `trySkipped_store_lt` | Generated gaps, `TooManySkipped`/`SkippedStoreFull` counter, template 8 stored-key recovery, and byte/read-back comparison | Clean-room CR-15 and SP-06 | The differential counter combines the two store-bound kinds. |
| Retention removes old chains and their stored keys | `clearOldEpochs`, `clearOldEpochs_store_le` | Template 9 advances twice and requires the store to shrink by more than one; `bob-retires-an-epoch-with-its-keys` is the fixed accepted trace | Clean-room SP-07 | Generated cases vary skipped keys and message numbers. |
| An operation on a retired epoch refuses | `findChains`/`send` model transition | Template 9 requires Rust `NoChain`, model refusal, unchanged bytes, and a coverage counter; `retired-epoch-no-chain-refused` fixes the same state and final send | Clean-room CR-14 and SP-07 | Closed for the named `NoChain` observable. |
| Persisted-state acceptance and canonicalization | Persisted-state model encoding/decoding | Every generated start and resulting state is exported, re-imported, and corrupted-import classifications are compared | Clean-room state reader and committed persistence fixtures | KEM/Braid delegation is outside this leaf format. |

### Fixed-vector decision

P7's fixed operation-vector surface is the named, externally observable sparse
outcomes that change the durable-state contract: both directions' initial
states, epoch and chain-counter ceilings, retirement's accepted trace, and the
retired-epoch `NoChain` refusal. The new
`retired-epoch-no-chain-refused` vector starts from the canonical state after
epochs 1 and 2 are opened and checks the final epoch-0 send only. Both runners
must report `no-chain`; an accepted operation or another refusal fails.

The generated differential harness remains the evidence for the combinatorial
operation space: message numbers, skipped-key occupancy, output placement and
the refusal combinations that do not define an additional fixed-vector
contract. It compares every refusal's unchanged persisted bytes and read-back;
the clean-room reader independently executes the specified retention rules.
This is the recorded P7 target decision for sparse-ratchet vectors. It closes
the sparse vector deficit without claiming that finite vectors exhaust the
operation space.

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

The same runner separately drives a genuine ML-KEM Braid exchange through
transition (5), where the persisted-state bridge cannot construct the delegated
key-pair and encapsulation fields. A complete six-codeword `ct2 || MacCt`
stream emits epoch 1; changing one byte of systematic codeword 5, which carries
only `MacCt`, emits no key and reaches terminal `Failed`. The clean-room
reader's BR-10 independently covers the matching ciphertext-MAC failure rule.

Tags 1 through 4 require a valid ML-KEM key-pair layout. That layout is the
recorded ADR-0006 delegated boundary, so the harness currently exercises only
an invalid-length refusal there. The persisted header pair and the real-KEM
ciphertext control are separate evidence; they do not cover the other
receive/send state-machine branches. Do not treat a MAC, a state transition,
or a delegated-layout exclusion as interchangeable.

| Obligation | Current evidence | Next closure step |
| --- | --- | --- |
| Sparse operation/invariant inventory | Scoped map above; the fixed-vector decision names the ceiling and retired-epoch observations, while generated differential and the clean-room reader cover combinations | Closed for P7's sparse vector target. |
| Braid persisted-state tags | Model/vector/reader/import comparison for tags 0 and 5--11; invalid-length check for 1--4 | Keep the delegated key-pair layout exclusion narrow and add valid tag evidence only with a specified independent producer. |
| Braid MAC behavior | Differential check of a persisted-key header MAC and mutation, with model recomputation; real-ML-KEM runner check of accepted `ct2 || MacCt` and a MAC-only-codeword mutation to `Failed`; clean-room BR-10 | Keep the KEM-backed control separate from the persisted-state bridge and add a committed operation vector only if the target decision requires one. |
| Braid state machine | `Ct2Sampled` boundaries, empty-`NoHeaderReceived` transition (6), and real-ML-KEM transition (5) MAC controls | The remaining branches require delegated KEM material; decide whether they need committed operation vectors or record that narrow target boundary. |
