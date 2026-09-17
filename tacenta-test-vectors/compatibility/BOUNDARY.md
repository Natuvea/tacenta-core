# Black-box boundary

The operational form of ADR-0003 and ADR-0005. It defines allowed inputs and
outputs.

The boundary is not "nobody may read interface definitions". It is:

> Protocol implementation work must not use libsignal's implementation
> details. The isolated reference-adapter role may use the
> minimum published calling-surface information needed to operate an official
> compiled package. Only approved behavioural outputs may cross from the adapter
> role to the implementation role.

## Three isolated roles

```
Tacenta implementation
        |
        |  neutral RPC interface (Tacenta-defined)
        v
Interoperability harness
        |
        +-- Tacenta adapter
        |
        +-- libsignal reference adapter   <-- segregated
                    |
                    v
           pinned libsignal package
```

**1. Tacenta implementation role.** May see: published protocol specifications;
Tacenta's own behavioural requirements; the neutral interoperability scenarios;
inputs and outputs from test runs; wire-level observations. Must not see:
libsignal source; internal bridge declarations; repository tests or fixtures;
source comments or internal architecture; and the implementation of the
libsignal adapter, including its libsignal-specific API mapping.

**2. Reference-adapter role.** May see only what an ordinary consumer needs to
use the package: official package documentation; the public classes, methods,
and types exposed by the compiled package; package metadata; public API
declaration files shipped as part of an official package. Must not inspect:
implementation source; internal bridge code; private symbols; protocol constants
embedded in the implementation; tests or fixtures that expose expected wire
values; implementation comments or commit history.

**3. Harness.** Speaks to both adapters through the Tacenta-defined neutral RPC
interface in `neutral-api.md`. The implementation role sees that interface only,
never libsignal's names, types, or structure.

These are information-flow roles, not a claim that separate teams or identities
have always filled them. The public repository has one maintainer account, and
automated and AI-assisted tools contribute across implementation,
specification, tests and review preparation. No completed reference-adapter run
or retained research transcript is public or present in the retained project
records. The policy therefore describes the required boundary for future work;
it does not establish provenance for the unresolved legacy profile values.

## Which interface files are acceptable

An interface declaration is acceptable for the adapter role when it is shipped
with the compiled package as its normal consumer-facing API, is necessary to
compile an ordinary application against that package, is limited to names,
argument types, return types, and documented errors, and is used only inside the
segregated adapter. In practice: TypeScript `.d.ts` files in an official npm
package, public Java class signatures in a released JAR, public Swift module
interfaces shipped with a framework, generated API documentation for the
supported surface.

Prohibited for everyone: declarations found by browsing internal repository
bridge directories, raw JNI exports, C headers generated from internal bridges,
internal schemas, private or undocumented symbols, and any file disclosing
constants, KDF labels, encoding rules, or internal state representation. This is
not limited to a single upstream repository; the same posture applies to any
Signal repository.

**The test to apply:** is this information needed to call the library normally,
or is it being used to learn how the protocol is implemented? The first is
acceptable for the adapter role. The second breaches the boundary, for everyone.

## Containment

The reference adapter is internal-only. It is isolated from this public tree,
runs in a separate process or container, and is never linked into or shipped
with any Tacenta product. Only its neutral behavioural contract is described
here.

## Public statement

This public tree contains no libsignal implementation source, compiled
libsignal objects, reference-adapter implementation, research transcripts, or
libsignal-derived fixtures. The ADRs describe the engineering rules;
libsignal's source code is not an input to this project.

## Filling specification gaps

Where a byte-level convention is not settled by a published specification and is
needed for interoperability, resolve it by black-box experiment with a written
research record: the question, the inputs, the observed outputs and transcripts,
the hypotheses, the distinguishing experiment, the resulting requirement, and the
remaining uncertainty. Never by reading the other implementation.
