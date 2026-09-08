# ADR-0003: independent interoperability research boundary

## Status

Accepted as public engineering policy. **Amended by ADR-0005**, which replaces
the absolute interface ban below with separate implementation and
reference-adapter roles. This record specifies the permitted inputs for
development. Read ADR-0005 alongside this record.

## Decision

Implementation and verification changes under this policy may use:

1. Publicly published protocol specifications.
2. Standards and academic materials referenced by those specifications.
3. Behaviour observed through black-box interaction with a pinned build of a
   third-party implementation operated for that purpose: inputs, outputs,
   errors, state behaviour, and transcripts of the exchange.
4. Independently generated test vectors, and clean-room behavioural
   requirements produced under this ADR.

Implementation and verification personnel must not inspect or use any
source-controlled material from Signal's libsignal repository. The prohibition
covers implementation source in any language, wrappers and bridge code, schema
and interface-definition files, generated bindings and headers, constants,
tests and fixtures, comments and internal documentation, commit history and
review discussions, and third-party explanations that are themselves derived
from the source. Copying identifiers, layouts, or error wording from libsignal
is prohibited. A file is not a public protocol specification merely because it
describes externally callable functions or data structures.

## Rationale

The boundary makes the provenance of every change auditable and reduces the
risk of incorporating third-party expression. Interface layers can carry
structure, names, types, and design choices even when publicly visible, so the
implementation role uses only the inputs listed above.

## Interoperability gaps

Where the published specifications omit a fact required for interoperability,
the fact is derived by black-box experimentation first, and the research record
must include: the unanswered question, the inputs tested, the outputs observed,
the protocol transcripts, the alternative hypotheses, the experiment that
distinguished them, the resulting behavioural requirement, and any uncertainty
or version dependency. Implementers receive behavioural requirements and
independently produced test vectors, never upstream source material.

## Compatibility targets

Three targets are distinguished and reported separately:

1. **Specification conformance**: implements the published protocol
   specifications. A goal.
2. **Bundle-layer interoperability**: establishes a session with a named
   libsignal version from an exchanged prekey bundle, using independently
   determined encodings, with supported peer versions reported. A goal.
3. **API compatibility**: reproduces libsignal's programming interfaces. Not a
   goal. The public API is independently designed and does not reproduce
   libsignal package structures, method names, or type hierarchies, except
   where a name is required by a public standard or protocol specification.

## Consequences

- Published specifications come first, followed where necessary by recorded
  black-box research conducted under this policy.
- The interop harness (libsignal as a black-box test peer) is the sanctioned
  instrument for wire-level facts, and its experiments follow the research
  record format above.
- This policy binds every contributor and every tool used to make a change.
