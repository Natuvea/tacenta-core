# ADR-0001: dual-key identity instead of XEdDSA

## Status

Superseded by ADR-0002. Wire compatibility with libsignal-based implementations
became a goal, and a dual-key identity is incompatible with the single-key wire
format, so XEdDSA is implemented in the verified zone instead.

## Context

The X3DH and PQXDH specifications sign prekeys with the party's X25519 identity
key, using XEdDSA so one key serves both Diffie-Hellman and signing. No vetted,
permissively licensed Rust crate provides XEdDSA, and this project's rule is
that standard primitives come from vetted libraries rather than being
implemented here.

## Decision

An identity is a pair of keys: an X25519 key for agreement and an Ed25519 key
for signatures, both from vetted libraries (x25519-dalek, ed25519-dalek).
Prekey signatures are ordinary Ed25519 signatures under the identity's signing
key. This deviates from the specifications' single-key design; the deviation is
carried in tacenta-spec's identities-and-devices and key-registration pages and
in the conformance manifest, so no compatibility with the single-key wire
format is implied.

## Consequences

- Identity bundles carry two public keys instead of one, and both must be
  bound together at registration (the signing key signs the agreement key).
- Wire-level compatibility with implementations that use XEdDSA single-key
  identities is not possible for the affected messages and is not claimed.
- Implementing XEdDSA inside the verified zone later, as a deliberate and
  specified exception to the no-reimplementation rule, would reopen this and
  restore the single-key design.
