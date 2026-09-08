# ADR-0004: interoperability harness design and claim discipline

## Status
Accepted

## Context

Bundle-layer interoperability with a libsignal-based peer must be demonstrable
on the wire. ADR-0003 defines the permitted research inputs. This record fixes
the shape of the harness and the discipline for any resulting compatibility
claim.

Two failure modes to avoid. First, a harness that couples to libsignal's API
shape, which would both weaken the clean-room posture and make Tacenta mirror an
interface it should not. Second, an over-broad compatibility claim, when
libsignal's APIs are unsupported outside official Signal use and may change
without notice.

## Decision

A neutral test runner. Each implementation sits behind an adapter exposing one
small behavioural API (`create_identity`, `generate_prekey_bundle`,
`process_prekey_bundle`, `export_public_state`). The
adapter translates between the neutral API and its implementation; Tacenta does
not reproduce libsignal's API, and the neutral API is not libsignal's.

Interoperability at this layer is asserted by behavioural properties of bundle
exchange and session establishment, not by byte equality, since correct
implementations may use randomness differently. Byte equality is required only
where an encoding must be canonical, and named where so.

Scope is the bundle layer: prekey-bundle exchange and the session establishment
it enables. Message-layer interoperability is out of scope for this record.

Every run is pinned to an exact libsignal build and reported against it.
Compatibility is claimed by version and covered surface: "Tacenta Core `<v>`
passed the suite against libsignal `<v>`, covering `<surfaces>`." The blanket
claim "fully compatible with libsignal" is not made.

The libsignal reference adapter and its version-specific mapping are private
and absent from this public tree (ADR-0005).

## Consequences

The harness can grow scenario by scenario without ever depending on libsignal's
API shape, and a compatibility statement is always traceable to a pinned version
and a covered surface. What would reopen it: a decision to claim compatibility
beyond specific versions (needs a defined, stable surface first), or a change to
the boundary in ADR-0003.
