# Session L4 primitive boundary decision

## Status

Proposed for rule-7 review.

Recorded 2026-09-18 against `tacenta-core` main `abd0c3b`.

## Context

The session orchestration calls X25519, AEAD, ML-KEM, XEdDSA and randomness.
Their production implementations use dependencies that are outside the pinned
Charon/Aeneas translation surface. The session refinement must still expose
the complete arguments and results of every such call; otherwise, for
example, a Rust encryption under the wrong key could agree with a model which
encrypts under the intended key.

## Decision

Create a shipping crate named `tacenta-boundary` containing the existing
production implementations and these nine plain-function entry points:

1. `dh_public`
2. `dh_agree`
3. `aead_seal`
4. `aead_open`
5. `kem_encapsulate`
6. `kem_decapsulate`
7. `xeddsa_verify`
8. `xeddsa_sign`
9. `random32`

The lifecycle leaf calls these functions directly. Their bodies remain
outside its translation, and the generated Lean treats them as opaque
declarations. Each declaration has one named totality contract, a concrete
non-vacuity witness in `Satisfiability.lean`, and a corresponding entry in
`LIMITATIONS.md`. Returning `None` or `Err` is an ordinary result of a
boundary function and is not assumed away.

The executable lifecycle model represents every boundary operation as a
function of its complete argument list. Randomness is an ordered draw trace:
each call consumes the head and returns the remaining trace. `OracleOf`
relates each concrete boundary call to the matching model call and relates
the concrete RNG interaction to that ordered trace.

XEdDSA signing is included even though prekey publication is outside the L4
theorem surface. `Identity::sign`, `sign_message` and the store publication
and rotation methods move with the lifecycle leaf, so the translator will
encounter their bodies.

## Assumption budget

The initial budget is nine new primitive contracts, one for each function
above. Existing KDF, RNG-trait and unit-composition contracts are inherited
and named separately. More than twelve new session contracts requires this
decision to be reopened and the boundary to be recut before proof work
continues.

## Consequences and validation

- The boundary contracts establish termination and the shape of returned
  values. They do not prove the cryptographic primitives correct or secure.
- Zeroization and heap-residue behavior remain outside the formal proof and
  stay governed by their tests and security process.
- The Phase 0 spike must confirm that translating `tacenta-lifecycle` with the
  pinned `aeneas` preset leaves these dependencies opaque and produces no
  unexpected primitive bodies or contracts.
- Reopen this decision if Charon traverses the boundary implementation, if a
  complete call cannot be represented by these functions, or if the
  assumption cap is exceeded.

## Review

This proposal is not an assurance result. It becomes accepted only after the
recorded rule-7 review required by the session end-to-end proof plan.
