# Session L4 translatability rewrite decision

## Status

Proposed for rule-7 review.

Recorded 2026-09-18 against `tacenta-core` main `abd0c3b`.

## Context

The shipping lifecycle implementation contains Rust constructs which the
pinned Charon/Aeneas toolchain either cannot lower or lowers into proof
obligations that obscure the session control flow. They include `?`
desugaring, closures over borrowed state, iterator closures, a value-returning
eviction loop with early returns, a `debug_assert!`, and external equality
implementations.

The code that is translated must remain the code that ships. A separate
proof-shaped implementation is not acceptable.

## Decision

Permit behavior-preserving rewrites of the shipping lifecycle leaf solely to
make the selected proof surface translatable. Each logical rewrite lands as a
separate signed commit and preserves:

- every returned value and refusal kind;
- the ordering of validation and cryptographic operations;
- every state commit point and failure-atomicity rule;
- public API paths and types;
- wire and persistence bytes.

The initial rewrite set is:

- replace `?` and translation-hostile combinators with explicit `match`;
- replace captured closures and iterator closures with named helpers or
  explicit loops;
- split the prekey-store decoder into head, replay-record and retired-prekey
  helpers, the shape the Phase 0 spike showed reduces its rooted LLBC from
  about 10 GiB to 13 MiB;
- replace the two `create_prekeys` iterator pipelines with explicit loops and
  replace `usize::max(1)` in receive shortfall with the equivalent comparison,
  because both produced Lean that Aeneas accepted but the kernel refused;
- replace the eviction loop with either a bounded loop or a fuelled helper,
  chosen by the Phase 0 spike;
- remove the responder `debug_assert!` only when its condition is represented
  by the corresponding refusal theorem;
- replace external `Vec` equality on repeat recognition with a translated
  byte-slice helper if the pinned standard model does not cover it.

The Phase 0 spike is disposable and may compare candidate rewrites before an
implementation is selected. Production rewrites are allowed only after this
decision's review.

Translate with Charon's `--start-from-pub` rather than from the whole crate.
That option includes public free functions and inherent methods without adding
wrapper functions or maintaining a second root list. A coverage gate compares
the generated public definitions with the shipping lifecycle API and must fail
if a public operation has no translated definition. The spike translated and
kernel-checked all 30 public lifecycle operations independently, then passed
the unified `--start-from-pub` translation at 27 MiB; translating the whole
package produced an approximately 10 GiB LLBC and an impractical Aeneas memory
footprint.

## Validation and stop conditions

Every production rewrite must pass the full workspace tests and all existing
vector runners with byte-identical vector and persistence files. A mutation
which changes a refusal, check order or commit point is a behavior change and
must not be folded into this work.

The root-coverage gate needs a negative control which removes one generated
public definition from its input and requires the gate to fail. Record LLBC
size, translation wall time and peak memory in addition to pass/fail, so a
technically successful translation cannot silently make the pinned CI runner
unusable.

If a construct remains untranslatable after two reasonable rewrite attempts,
record the exact tool failure. A pure helper may cross the primitive boundary
only after its contract, witness and assumption-budget impact are reviewed.
Any normative behavior change follows ADR-0006 and updates the specification
first in a separate change.

## Review

This proposal is not an assurance result. It becomes accepted only after the
recorded rule-7 review required by the session end-to-end proof plan.
