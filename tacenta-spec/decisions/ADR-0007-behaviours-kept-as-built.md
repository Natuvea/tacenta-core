# ADR-0007: three behaviours the specification records as built are kept

## Status

Accepted.

## Context

Under ADR-0006, behaviour the specification did not define is a finding: the specification either specifies it or the implementation removes it. The independent reader's second pass, and the work that closed its gaps, wrote three such behaviours into the pages as built and marked each one undecided:

1. **The receiving epoch.** The sparse ratchet receives on the chain of the epoch the composite header names (`pq_epoch`), not the epoch the agreement's receive returns (sparse-pq-ratchet.md, Receiving). Double Ratchet revision 4, §5.6, looks the chain up by the returned epoch, and its header carries none.
   - Where the agreement keeps its guarantee, the two are the same.
   - They differ only on the message whose receipt fails the Braid: its receive returns epoch 0 (mlkem-braid.md, Failure), and the message is still received under its `pq_epoch`.
2. **What the leaf readers accept.** Each leaf format's list of semantic rules is complete, and a state that keeps every rule is accepted even where no operation produces it (session-persistence.md, Semantic rules of the leaf formats). Examples:
   - a ratchet state with `nr` or `ns` above zero and no chain for it;
   - a sparse ratchet state holding a stored key numbered 0, or at or past its chain's counter.
3. **The epoch transition (5) reports.** A Braid receive that takes transition (5) reports the epoch it completed. The published ML-KEM Braid document reports the one before, the sending epoch the `ct2` message was sent with (mlkem-braid.md, What a send and a receive return). The epoch in the authenticator's MAC inputs is `ToBytes(epoch)`, as in the document's derivations.

In each case `tacenta-model`, `tacenta-core` and the proofs agree with one another, and no vector depends on the alternative.

## Decision

The three behaviours are the protocol.

1. **The header's `pq_epoch` selects the receiving chain.**
   - The composite header is this specification's own format, and it carries the sending epoch explicitly.
   - Selecting by it gives every received message one chain, including the message whose receipt fails the agreement.
   - A `pq_epoch` that names the wrong chain yields a key the message does not authenticate under, so a peer gains nothing by lying in it.
2. **The leaf readers enforce exactly their stated rules.** A rule list is the set of relations the operations and their proofs rely on, and every operation is correct on any state that keeps them.
   - Refusing states no operation produces would add rules the proofs do not need.
   - It would not protect a store against deliberate modification, which is the storage layer's concern.
3. **Transition (5) reports the completed epoch.** `Session` does not use the value. The model's `Braid.receive_reports` and the implementation agree on it.

The pages' "undecided" notes are replaced by references to this record. The departures from the published documents stay stated where they occur.

## Consequences

- A second implementation that follows Double Ratchet revision 4 §5.6, or the published Braid document at transition (5), does not conform on those points. It interoperates everywhere except the message whose receipt fails the Braid.
- A store edited so that every rule still holds is accepted. Integrity of a persisted store against a writer is outside this specification.
- Reopening any of these points needs a new decision record, and a specification change before any code change (ADR-0006).
