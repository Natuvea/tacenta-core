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
| Initialization and direction | `Model.SparseRatchet.init`; persisted-state semantic rules | Fresh starts in templates 0--1; canonical export/import at each step; committed sparse-state fixtures | Clean-room `tacenta_reader/spqr.py`; CR-12--CR-17 | No fixed operation-vector corpus for all initialization variants. |
| Advance only to the next epoch, and never onto the reserved epoch | `advance`, `advance_epoch_lt` | Generated agreement outputs; templates 6--7 reach the reserved boundary and require the same refusal | Clean-room SP-07 and CR-17 advance/retention exercises | The generated run does not separately classify every `EpochOutOfOrder` refusal. |
| Send and receive counters | `send`, `receive`, `send_number_le` | Templates 2--5 force both chain ceilings and compare every accepted/refused result | Clean-room CR-12 and CR-13 | No fixed operation-vector corpus for all counter/refusal permutations. |
| Skip/store bound, lookup and one-time use | `skipMessageKeys`, `trySkipped`; `deriveInto_*`, `skipMessageKeys_store_bounded`, `trySkipped_store_lt` | Generated gaps, `TooManySkipped`/`SkippedStoreFull` counter, template 8 stored-key recovery, and byte/read-back comparison | Clean-room CR-15 and SP-06 | The differential counter combines the two store-bound kinds. |
| Retention removes old chains and their stored keys | `clearOldEpochs`, `clearOldEpochs_store_le` | Template 9 advances twice and requires the store to shrink by more than one | Clean-room SP-07 | No committed Rust/model fixed operation vector for the sequence. |
| An operation on a retired epoch refuses | `findChains`/`send` model transition | Template 9 now sends at retired epoch 0 after advancing to 2 and requires Rust `NoChain`, model refusal, unchanged bytes, and a coverage counter | Clean-room CR-14 and SP-07 | This closes the previously unexercised Rust/model observable effect of retirement; it does not make the overall operation surface complete. |
| Persisted-state acceptance and canonicalization | Persisted-state model encoding/decoding | Every generated start and resulting state is exported, re-imported, and corrupted-import classifications are compared | Clean-room state reader and committed persistence fixtures | KEM/Braid delegation is outside this leaf format. |

This is a scoped operation/invariant map, not a claim that generated coverage
is a complete L4 vector surface. The remaining target gap is a fixed-vector
decision for the refusal combinations the generated differential run does not
separately classify.

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
| Sparse operation/invariant inventory | Scoped map above; generated differential and clean-room reader evidence include the post-retirement `NoChain` refusal it identified as missing | Decide which remaining generated refusal combinations need fixed vectors, then add them or record the target decision. |
| Braid persisted-state tags | Model/vector/reader/import comparison for tags 0 and 5--11; invalid-length check for 1--4 | Keep the delegated key-pair layout exclusion narrow and add valid tag evidence only with a specified independent producer. |
| Braid MAC behavior | Differential check of a persisted-key header MAC and mutation, with model recomputation; real-ML-KEM runner check of accepted `ct2 || MacCt` and a MAC-only-codeword mutation to `Failed`; clean-room BR-10 | Keep the KEM-backed control separate from the persisted-state bridge and add a committed operation vector only if the target decision requires one. |
| Braid state machine | `Ct2Sampled` boundaries, empty-`NoHeaderReceived` transition (6), and real-ML-KEM transition (5) MAC controls | The remaining branches require delegated KEM material; decide whether they need committed operation vectors or record that narrow target boundary. |
