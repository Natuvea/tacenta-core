# ADR-0005: segregated reference-adapter role

## Status

Accepted as public engineering policy. Amends ADR-0003 by replacing its absolute
interface ban with the role split below.

## Context

ADR-0003's interface ban addresses implementation detail. Operating a compiled
library also requires enough of its supported calling interface to invoke it,
while the harness in ADR-0004 still needs to prevent interface shape or
implementation detail from reaching protocol work. This record separates the
two.

The fix is not to weaken the boundary but to locate it correctly. What must stay
out of the implementation is libsignal's *implementation detail*. What an
ordinary consumer needs in order to *call* an official package is a different
thing: the published, consumer-facing APIs (the Java, Swift, and TypeScript
surfaces) are distinct from the raw C, JNI, and Node bridge layers, which are
not part of the intended consumer surface.

## Decision

Implementation and verification work under this policy must not inspect or use
libsignal source code, internal interface definitions, tests, fixtures, or
implementation-derived documentation.

The private reference-adapter role may inspect the minimum consumer-facing API
information distributed with an official compiled libsignal package where
necessary to invoke that package as an ordinary user. This permission does not
extend to internal bridge definitions, implementation source, protocol
constants, wire schemas, test fixtures, or undocumented symbols.

The reference adapter must expose a Tacenta-defined neutral RPC interface.
Implementation work may receive only the approved behavioural outputs; it must
not receive the adapter implementation or its libsignal-specific API mapping.

### The test to apply

Is this information needed to call the library normally, or is it being used to
learn how the protocol is implemented? The first is acceptable for the adapter
team. The second breaches the clean-room boundary, for everyone.

### Acceptable for the adapter team

An interface declaration is acceptable when it is shipped with the compiled
package as its normal consumer-facing API, is necessary to compile an ordinary
application against that package, is limited to names, argument types, return
types, and documented errors, and is used only inside the segregated adapter.
That covers TypeScript `.d.ts` files in an official npm package, public Java
class signatures in a released JAR, public Swift module interfaces distributed
with a framework, and generated API documentation for the supported surface.
These are the library's operating instructions; without them ordinary use is
impossible.

### Prohibited for everyone

Declarations found by browsing internal repository bridge directories, raw JNI
exports, C headers generated from internal Rust bridges, internal Protobuf
schemas, private or undocumented symbols, and any file that discloses constants,
KDF labels, encoding rules, or internal state representation.

## Containment

The reference adapter is internal-only. It must be isolated from this public
tree, run in a separate process or container, and never be linked into or
shipped with any Tacenta product.

## What this public record establishes

This record establishes the project's engineering policy and the role
separation. Implementation and verification work uses only the inputs ADR-0003
lists; libsignal's source code is not among them.

The public tree itself contains no libsignal implementation source, compiled
libsignal objects, reference-adapter implementation, research transcripts, or
libsignal-derived fixtures.

## Consequences

- The role separation is enforced through repository, process, and input
  controls, not merely by contributor identity.
- Compliance rests on the inputs actually used; repository layout is the
  enforcement mechanism, not the definition of the boundary.
- What would reopen it: upstream changing what it publishes as the supported
  consumer surface.
