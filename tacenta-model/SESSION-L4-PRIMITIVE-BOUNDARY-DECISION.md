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
production implementations. Keep its public `PrivateKey`, `PublicKeyBytes`
and `KeyPair` types at the boundary: moving their representation into the
lifecycle leaf would either expose primitive internals to translation or
change the existing public API.

The complete Phase 0 translation determines the opaque call surface rather
than an anticipated wrapper list. For the five proof roots (`encrypt`,
`decrypt`, initiator and responder establishment, and session import), that
surface is covered by these ten named contracts:

1. `DhCodecTotal`: construction, public derivation, byte projection,
   persistence projection and public-key equality;
2. `DhAgreeTotal`;
3. `AeadSealTotal`;
4. `AeadOpenTotal`;
5. `KemEncapsulateTotal`;
6. `KemDecapsulateTotal`;
7. `KemCiphertextLenTotal`;
8. `XeddsaVerifyTotal`;
9. `XeddsaSignTotal`; and
10. `Random32Total`, over the lifecycle's fixed-width use of `RngCore`.

`DhCodecTotal` groups operations over the same two opaque DH types so their
non-vacuity is witnessed jointly; separate witnesses would not show that all
of the contracts can hold in one interpretation. The other contracts each
cover one opaque call. The proposal requires every contract to have a concrete
non-vacuity witness in the session unit's satisfiability module and a
corresponding entry in `LIMITATIONS.md`;
returning `None` or `Err` is an ordinary result of a
boundary call and is not assumed away.

The executable lifecycle model represents every boundary operation as a
function of its complete argument list. Randomness is an ordered draw trace:
each call consumes the head and returns the remaining trace. `OracleOf`
relates each concrete boundary call to the matching model call and relates
the concrete RNG interaction to that ordered trace.

XEdDSA signing is included even though prekey publication is outside the five
proof roots. `Identity::sign`, `sign_message` and the store publication and
rotation methods move with the lifecycle leaf, so the translation and its
audit still encounter that opaque call.

## Assumption budget

The complete translation requires ten new primitive contracts. Existing KDF
and unit-composition contracts are inherited and named separately; the one
fixed-width RNG contract above replaces a generic new RNG assumption. More
than twelve new session contracts requires this decision to be reopened and
the boundary to be recut before proof work continues.

## Consequences and validation

- The boundary contracts establish termination and the shape of returned
  values. They do not prove the cryptographic primitives correct or secure.
- Drop and allocator behavior remain outside the formal proof; the public
  limitations record the corresponding implementation hardening and its test
  evidence.
- The Phase 0 spike record records the reachable opaque-call inventory for the
  five proof roots. Adding a reachable primitive call without adding it to one
  of the ten contracts is a review finding.
- Reopen this decision if Charon traverses the boundary implementation, if a
  complete call cannot be represented by these functions, or if the
  assumption cap is exceeded.

## Review

This proposal is not an assurance result. It becomes accepted only after the
recorded rule-7 review required by the session end-to-end proof plan.
