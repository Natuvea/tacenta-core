# tacenta-spec

The protocol and security specification, written as prose.

The plain-language definition of the protocol (PQXDH agreement, which extends
X3DH's Diffie-Hellman computations with a post-quantum encapsulation; the
Double Ratchet and the post-quantum ratchet beside it; prekeys) and the
security properties it must hold. Derived from the public Signal
specifications, it is the source that the model, proofs, and implementation
are all written against, and it is normative: see "Normative status" below.
Plain X3DH is out of scope, and session-establishment.md and the conformance
manifest both record that.

Status: eight written protocol pages cover everything the engine runs:
session-establishment.md (PQXDH), ratchet.md (the classical Double Ratchet),
sparse-pq-ratchet.md and mlkem-braid.md (the post-quantum ratchet and the
agreement beneath it), triple-ratchet.md (their composition), message-format.md,
key-deletion.md, and session-persistence.md; post-compromise-security.md is the
one written security-property page. group-messaging.md is an outline ahead of
the code, and that work is not yet scheduled. Every other page in protocol/,
threat-model/ and security-properties/ is a scaffold -- a title and a one-line
scope, marked "Status: scaffold" -- kept as the table of contents for what is
still to be written. Until a scaffold is written, its topic is unspecified:
what the implementation does there is neither a precedent for this
specification nor a conformance target, and tacenta-proofs/CLAIMS.md and
LIMITATIONS.md record only what is and is not proven about that code.

[CONSTANTS.md](CONSTANTS.md) records every constant this engine emits or
accepts with the source that authorises it, at one of three tiers; every
constant the engine emits or accepts is required to have an entry there.
[CHANGELOG.md](CHANGELOG.md) tracks
changes to the specification, versioned against the protocol rather than the
implementation.

## Normative status

This specification is the product, and `tacenta-core` is one implementation
of it ([ADR-0006](decisions/ADR-0006-specification-is-normative.md)).

- **Normative:** the written pages under `protocol/` and
  `security-properties/`, and `CONSTANTS.md`. `tacenta-model` states the same
  definition formally, and the protocol vectors it generates are normative
  examples of it. The decision records say why; they are not themselves the
  protocol.
- **Not normative:** any implementation, including `tacenta-core`, and any
  page marked "Status: scaffold". Nothing is true of the protocol because
  the code does it.
- **When they disagree:** an implementation that disagrees with this
  specification does not conform, and is fixed unless the specification is
  amended first. A disagreement between the prose, the model and the vectors
  is a defect in the specification, fixed in all three before any of them is
  relied on for that point.
- **Specification first:** a change to anything this specification defines
  (bytes emitted or accepted, a refusal, a constant, a derivation, a bound,
  or a rule over persisted state) lands here first, in the same pull request
  as the code and ahead of it, with an entry in `CHANGELOG.md`. Behaviour an
  implementation has that this specification does not define is a finding.
- **Deliberate delegation is stated:** where a detail is left to a dependency
  on purpose, the page says so and names what that means for another
  implementation.

## Trademarks and non-affiliation

tacenta-core and Tacenta are not affiliated with, endorsed by, or sponsored by
Signal Messenger LLC or the Signal Foundation. "Signal" and "libsignal" are used
only to name the published protocols and the third-party software they refer to.
