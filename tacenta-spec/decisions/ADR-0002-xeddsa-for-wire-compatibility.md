# ADR-0002: XEdDSA single-key identities

## Status

Accepted. Supersedes ADR-0001.

## Context

The X3DH and PQXDH specifications use a single X25519 identity key and sign
prekeys with that key via XEdDSA. ADR-0001's dual-key identity (a separate
Ed25519 signing key) cannot produce that form, so matching the specifications
requires a single-key identity.

No vetted, permissively licensed Rust crate provides XEdDSA. This is the one
candidate exception to the no-reimplementation rule.

## Decision

- Identities are single X25519 keys, as the specifications define. Prekey
  signatures are XEdDSA.
- XEdDSA is implemented inside the verified zone, written from the published
  XEdDSA specification ("The XEdDSA and VXEdDSA Signature Schemes", revision 1),
  using curve25519-dalek for the underlying curve arithmetic and ed25519-dalek
  for the Ed25519 verification equation. This is the deliberate, specified
  exception to the rule that primitives are not implemented here.
- The Ed25519 primitive module remains as the verification backend and as a
  general building block.

Wire-level details a peer requires that the published specifications do not fix
are determined under the interoperability research boundary (ADR-0003, ADR-0005)
and are not recorded here.

## Consequences

- The verified zone now contains one piece of implemented cryptography, so the
  proofs' trusted computing base shrinks: curve arithmetic is still trusted, and
  the XEdDSA construction on top becomes provable.
- There are no published XEdDSA known-answer vectors. Validation is structural:
  sign-verify round trips, and that XEdDSA signatures verify as standard Ed25519
  signatures under the converted public key.
- ADR-0001's dual-key registration flow is dropped.
