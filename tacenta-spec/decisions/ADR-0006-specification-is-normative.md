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
specification alone. The specification-only, project-controlled reader's fifth pass found every
requirement's status citing `CLAIMS.md`, `LIMITATIONS.md`, a Lean theorem or a
`tacenta-core` test, none of them in the normative tree, and two statements
taking their *content* from implementation files (`GAPS-5.md`, G5-07).

Amended 2026-10-28: the reader is called the specification-only, project-controlled reader;
nothing else changed (`tacenta-spec/CHANGELOG.md`).

Amended by #297, effective when that pull request was merged into `main`: point 6 says
what each pass of a reader offered as evidence of sufficiency records, and what a pass
may be called given its record. It had not said what a pass records. No requirement of
the point is relaxed, the amendment is not retrospective, and no target, closure or
level changes (`tacenta-spec/CHANGELOG.md`). The next change to `tacenta-spec/` records
here the date and the commit on `main` that #297 produced; until then the pull request's
merge record is the reference.

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
   - **Passes.** These rules apply to every reader offered as evidence that the
     specification is sufficient. A pass is work that writes, extends or checks such a
     reader from the specification; running an unchanged reader, in the gate or elsewhere,
     is not a pass. A change to such a reader made outside a pass is recorded with who made
     it and what was in view.
   - **The record.** Each pass keeps a record stating, as separate items: (1) its permitted
     inputs, with hashes, including any earlier reader code and the toolchain; (2) the
     context supplied before its first action, instructions and any catalogue of tools or
     skills included; (3) the files it accessed, inside and outside the permitted inputs;
     (4) its outputs; (5) its subsequent exposure, and every later edit to the record or the
     outputs; (6) any context not retained, stated as such and never reconstructed; (7) its
     demonstrated use, as its outputs and access records show it. It says who ran the pass,
     under whose control, with what assistance, and how items 3 and 4 were recorded. Content
     that cannot be published is recorded as withheld, never omitted. The reader's README
     says how each item is written.
   - **The context check.** Before the pass's first read of the specification, someone
     other than its author checks the supplied context and records the check: their role,
     their relationship to the project and to the author, the method, and what they could
     actually inspect. Context they could not inspect is stated as a limitation, never as
     absent. A check made within the project is project-controlled; it is not independent
     review.
   - **Context and use are different facts, and both are recorded.** Context in view does
     not establish that a pass used knowledge of an implementation, and its absence from a
     record does not establish that none was in view. A record that cannot state an item
     completely says so, and the pass is described with that qualification.
   - **Strict clean-room isolation** is claimed only for a pass whose record states every
     item completely and meets these conditions. Apart from the specification, the vectors
     and any earlier reader code listed under item 1 by revision and file hashes, neither its
     permitted inputs nor the context the check found includes anything that describes the
     implementation, the model, the proofs, project notes, prior findings or review
     histories; names of such things inside the permitted inputs are text, and the files
     they name stay excluded. Where the check records context it could not inspect, that
     limitation stays in the record and the claim is not made. Its accesses and outputs are
     captured as the pass runs, by the execution environment or by another directly
     checkable recording mechanism not kept by the pass's author, with their coverage and
     omissions stated. The coverage includes every means by which the pass could read or
     write files, and a recording that covers only the pass's own directory does not support
     the claim; the records show no access outside the permitted inputs and the toolchain's
     own files. An account by the author, alone or corroborated only by the author, does not
     qualify. Without such records a pass may be qualified evidence, never a strict claim. A
     fresh directory or session is not enough by itself. These exclusions bind the strict
     claim only; this point's existing prohibitions bind every pass. A pass given earlier gap
     reports says so, and is not presented as a fresh, strict derivation.
   - **What a claim covers.** A strict claim names the pass, its outputs and the revision
     it covers, and does not extend to inherited reader code. An edit made later with
     excluded material in view is identified as a separate revision, and the original
     outputs are kept. Recording the edit does not preserve the claim: the affected part,
     and every conclusion whose justification depends on the change, fall outside it.
     Unaffected parts keep it where the separation is supported.
   - **Names.** After #297 was merged, an unqualified claim that a pass was isolated or
     clean-room is a strict claim; earlier statements are read as the reader's README
     describes them. "Specification-only" names a second reader written from the
     specification and the vectors under the conditions its passes' records state. It is not
     a claim of strict isolation, nor that every line was written that way. A pass run by
     the project, its maintainer or a related party is project-controlled checking.
     Independent review is a reading by someone outside the project, independent of the
     maintainer and not a related party; a target or register row may ask more. Neither
     stands in for review under ADR-0008, decision 7. A pass that opened anything this
     point's second sentence names is not a test of sufficiency.
   - **From when.** These rules bind passes, and changes made to a reader outside a pass,
     begun after #297 was merged. A pass begun earlier may follow them and say so. Earlier
     records are kept as they stand. None is reconstructed; adding an authentic existing
     record verified against its previously recorded hash is not reconstruction. This point
     changes no target, closure or level.

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
  prose does not follow either fails the specification-only, project-controlled reader or is caught
  at review.
- Changes are slower: the specification is written before the code, and the
  specification-only, project-controlled reader has to be maintained alongside both.
- A pass's record states the items of point 6, or says which it cannot state and why,
  before the pass is offered as evidence, and someone other than its author checks the
  supplied context first. Records made before the amendment took effect are described by
  the reader's README or the evidence file that holds them, and are not rewritten.
- `tacenta-proofs/CLAIMS.md` remains the record of what is proven. This
  record decides what is specified.
- This would be reopened if the project chose a different normative artifact
  (for example the Lean model alone, with the prose informative), or if a
  second implementation showed that the prose cannot be made sufficient.
