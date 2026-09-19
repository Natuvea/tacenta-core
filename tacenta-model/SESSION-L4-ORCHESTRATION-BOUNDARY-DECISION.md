# Session L4 orchestration location decision

## Status

Proposed for rule-7 review.

Recorded 2026-09-18 against `tacenta-core` main `abd0c3b`.

## Context

`Session::encrypt`, `Session::decrypt`, `establish_initiator_for` and
`establish_responder` live in the top-level `tacenta-core` crate. That crate
also depends directly on cryptographic libraries and Rust trait hierarchies
that the pinned Charon/Aeneas toolchain does not translate. Translating a
copy of `lifecycle.rs` in a proof-only crate would leave the headline theorem
about a different compiled artifact from the one products call.

The session L4 programme therefore needs a shipping crate boundary that is
also a translation boundary. The public Rust API and persisted and wire bytes
must remain unchanged.

## Decision

Create a shipping leaf crate named `tacenta-lifecycle`. Move the non-test
session lifecycle implementation, its session module wiring, and the
`Composite` serialization helpers into that crate. The top-level
`tacenta-core` crate re-exports the existing public items, including
`Session`, `Error`, `Identity`, `PrekeyStore`, `PublishedBundle`,
`establish_initiator`, `establish_initiator_for` and
`establish_responder`.

The leaf depends on the existing ratchet, sparse-ratchet, Triple, Braid,
session, wire, erasure and KDF leaves and on the primitive-boundary crate
defined in `SESSION-L4-PRIMITIVE-BOUNDARY-DECISION.md`. The product continues
to call the same public API, but the implementation behind that API is now a
crate which the pinned translation command can select directly.

Directory-facing prekey publication, replenishment and rotation operations
move with `Identity` and `PrekeyStore`. They are translated but remain outside
the accepted L4 theorem surface. `CLAIMS.md` must list them under
"Translated is not proved" until separate theorems exist.

## Rejected alternatives

- Translating the top-level crate retains dependencies that the toolchain
  cannot presently lower.
- Copying `lifecycle.rs` into a proof-only unit proves a different crate graph
  from the shipping artifact.
- Separating the store behind a Rust trait adds the kind of trait boundary
  this carve-out is intended to avoid and still leaves responder establishment
  dependent on an opaque store interface.

## Consequences and validation

- This is a mechanical move. It does not authorize a change to a protocol
  rule, refusal kind, check order, commit point, public type path, wire byte or
  persisted byte.
- The Phase 0 pull request must keep all vectors byte-identical, pass the full
  workspace and product suites, and record an empty public-API diff.
- A product pin bump and Windows build are part of Phase 0 acceptance.
- Reopen this decision if the selected leaf cannot be translated without
  putting session semantics behind a new opaque boundary, or if preserving
  the public API requires a consumer-visible change.

## Review

This proposal is not an assurance result. It becomes accepted only after the
recorded rule-7 review required by the session end-to-end proof plan.
