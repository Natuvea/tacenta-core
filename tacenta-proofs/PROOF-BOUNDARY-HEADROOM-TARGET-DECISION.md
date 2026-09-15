# Proof-boundary headroom target decision

## Decision

The current assurance target retains the existing success-refinement theorems
with their stated successor-headroom premises. It does not claim refinement of
a successful operation at the final unreserved counter value, and it does not
lower the target of any component merely because the corresponding concrete and
model operations refuse at the reserved ceiling.

This is a scope decision for `PROOF-BOUNDARY-HEADROOM`, not a proof that the
premises are necessary. `LIMITATIONS.md` records the relevant theorem shapes:
decoded states are panic-free without this premise; the success refinements
retain `events + 1 < u32::MAX` or `epoch + 1 < u64::MAX`.

## Evidence and target effect

The implementation and models reserve matching boundary values. Persistence
vectors cover the two ratchet ceilings. The Braid model states the matching
epoch-boundary outcomes, and its crate tests and differential harness exercise
the documented refusal transitions. That evidence supports the stated refusal
behaviour. It does not establish a success-refinement theorem at the boundary,
so no claim, component level, or gate outcome may imply one.

The existing targets are therefore unchanged: unconditional decoded-state
panic-freedom and the scoped success-refinement theorems remain the evidence
being assessed. The deferred row is no longer an unspecified research item;
it is an explicit scope of those targets. The required semantic review of the
invariant catalogue remains separate and is not completed by this decision.

## Revisit triggers

Reopen this decision before asserting boundary success refinement, or when:

- a counter ceiling, reservation rule, refusal outcome, or corresponding model
  transition changes;
- a theorem header, translation theorem, or composition begins to require the
  boundary case without its current headroom premise;
- a component target is raised to require whole-domain success refinement; or
- a semantic or external review requests a boundary-refusal theorem.

The reopening work must either prove matching refusal refinements at the
boundary or restate and prove the success theorems without the premise, then
update `CLAIMS.md`, `LIMITATIONS.md`, the invariant catalogue, and this target
decision before the stronger claim is made.
