# ADR-0006: the specification is the product, and implementations conform to it

## Status

Accepted.

Amended 2026-09-11: `threat-model/` is added to what is normative (point 1).
When the threat model and the security properties were written, every
security requirement came to be stated against the threat model's assets,
adversaries and assumptions, so a requirement cannot be normative unless those
are too.

Amended 2026-09-12: a normative page may cite non-normative evidence for a
status it states, and such a citation is not part of the protocol's definition
(point 7). What a page *requires* must still be readable from the
specification alone. The independent reader's fifth pass found every
requirement's status citing `CLAIMS.md`, `LIMITATIONS.md`, a Lean theorem or a
`tacenta-core` test, none of them in the normative tree, and two statements
taking their *content* from implementation files (`GAPS-5.md`, G5-07).

## Context

`tacenta-spec/README.md` has always called the specification the source that
the model, the proofs and the implementation are written against. In practice
the implementation was the definition:

- In the September 2026 review of the specification against the code, nearly
  every disagreement was settled by changing the specification to match the
  code. Examples: how `SK` is expanded, `CT` being kept and resent, and the
  sparse ratchet's derivation parameters.
- The specification left whole formats to the code until it was told
  otherwise: the Braid's persisted fields per state, the erasure coders'
  sub-formats, and the leaf formats' semantic rules, which it called "each
  crate's own `invariant`".
- The specification's own README said that where a page is unwritten, "the
  code, the model, and tacenta-proofs/CLAIMS.md and LIMITATIONS.md are the
  record".
- The machine-checked link runs from the Rust to the Lean model. Nothing
  mechanical connects the model to the prose.
- There is one implementation. Nobody has shown that the specification is
  enough to build a second.

A specification that yields to its one implementation cannot serve other
implementations, and what it promises ends up being whatever that code does.

## Decision

1. **What is normative.** The written pages of `tacenta-spec` (under
   `protocol/`, `threat-model/` and `security-properties/`, with
   `CONSTANTS.md`) define the protocol, its formats, its rules and the
   security it is required to provide. `tacenta-model` states the same
   definition formally. The protocol vectors it generates in
   `tacenta-test-vectors` are normative examples of it. `tacenta-core` is one
   implementation of the specification. It is not normative, and nothing is
   true of the protocol because the code does it.

2. **Precedence.**
   - Where an implementation disagrees with the specification, the
     implementation does not conform. It is fixed, unless the specification
     is first amended under point 3.
   - Where the prose, the model and the vectors disagree with each other, the
     specification is defective. The defect is fixed in all three before any
     of them is relied on for that point. Neither side wins by default.

3. **Specification first.** A change to anything the specification defines
   updates the specification first: bytes emitted or accepted, a refusal, a
   constant, a derivation, a bound, or a rule over persisted state.
   - The specification commit lands before the code commit in the same pull
     request, with an entry in `tacenta-spec/CHANGELOG.md`.
   - Behaviour an implementation has that the specification does not define
     is a finding. The fix is to specify it or to remove it.

4. **Unwritten topics are unspecified.** Where a page is still a scaffold, the
   protocol is unspecified. What an implementation does there is neither a
   precedent for the specification nor a conformance target.

5. **Deliberate delegation is stated.** Where the specification leaves a
   detail to a dependency on purpose, it says so and names the consequence
   for another implementation. The KEM library's key-pair and encapsulation
   state, persisted as that library serialises them, is one example.

6. **Sufficiency is tested.** A second reader is written from the
   specification and the vectors alone. Its authors do not consult
   `tacenta-core`, `tacenta-model`, `tacenta-proofs` or the Rust vector
   runner. It runs in the gate against the vectors. Anything it needs that
   the specification does not say is a defect in the specification, recorded
   and fixed there. The isolation is procedural, like ADR-0003's boundary.
   Coverage is stated: until the reader covers a page, that page's
   sufficiency has not been shown, and the reader's README says which pages
   it covers.

7. **Evidence may be cited; content may not.** A normative page may cite
   non-normative evidence for a status it states: a Lean theorem, a test, a
   vector, `tacenta-proofs/CLAIMS.md` or `tacenta-proofs/LIMITATIONS.md`. Such
   a citation records where the evidence for a claim about this project's work
   is. It is not part of the protocol's definition, and nothing is true of the
   protocol because a cited theorem or test exists. Removing a citation would
   lose the traceability ADR-0008's practice 8 is built on; the citations stay.
   - **What a page requires is readable from the specification alone.** A
     rule, a list, or a set that a requirement is stated over belongs in these
     pages. A page that takes its *content* from a file outside them makes
     that implementation normative through the back door, which point 1
     denies, and leaves a second implementer unable to tell what is required.
   - **Where the content is a property of an implementation** rather than of
     the protocol -- which functions of some codebase consume unauthenticated
     input, say -- the page states what the protocol requires, and cites the
     implementation's own record as evidence that this implementation meets
     it.
   - The distinction is the one point 1 already draws. A citation answers
     "how do we know this holds here"; content answers "what must hold". Only
     the second defines the protocol.

## Consequences

- A pull request that changes behaviour says which specification text it
  implements. The pull-request template asks.
- Protocol vectors are regenerated from the model. A model change that the
  prose does not follow either fails the independent reader or is caught at
  review.
- Changes are slower: the specification is written before the code, and the
  independent reader has to be maintained alongside both.
- `tacenta-proofs/CLAIMS.md` remains the record of what is proven. This
  record decides what is specified.
- This would be reopened if the project chose a different normative artifact
  (for example the Lean model alone, with the prose informative), or if a
  second implementation showed that the prose cannot be made sufficient.
