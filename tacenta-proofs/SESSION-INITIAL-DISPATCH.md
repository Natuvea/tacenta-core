# Initial-message dispatch composition

`Translation/UnitLifecycleInitialDispatch.lean` composes the initial-message
wrapper around the ratchet receive. This does **not** close the full Session
T3 or end-to-end encryption/decryption plan.

## What the theorem establishes

`initial_dispatch_route_from_ratchet` constructs the six routes from the
translated initial decoder, the session's established ephemeral, the two key
comparisons, and the actual inner receive result. It takes no caller-selected
route or public-decrypt witness. Its first four branches invoke the existing
wrapper refinement proofs. The two repeated-initial branches reuse
`decrypt_initial_repeat_step_refines`, which rules out disagreeing result tags
and clears pending state only on success.

`decrypt_initial_refines_from_ratchet` joins the constructed route into a
public `Session.decrypt` refinement witness. The companion
`initial_dispatch_atomicity_from_ratchet` derives refusal preservation and
success clearance of the pending-state **projection**. It does not claim
byte-for-byte identity of every concrete session field on refusal.

The assumptions are explicit: initial message classification, the existing
session relation and RNG trace, `DhCodecOf`, and `InitialRatchetRefines` for
inner receives reached after all wrapper checks pass. The latter remains a
semantic obligation for general receive; it is not a primitive axiom or an
unconditional proof of receive correctness.

`decrypt_ratchet_refines_of_t1` is the shared T1-to-T3 bridge for that inner
call. It obtains the concrete result from `decrypt_ratchet_no_panic` under
`DecryptRatchetContracts`, `DecryptRatchetHeadroom`, and `DerivedKeysModel`,
then applies the semantic `StepRefines` obligation to that result. The initial
wrapper theorem uses this bridge rather than duplicating the existence proof.

## Discharged obligations

- `initial_ratchet_refines_of_t1` obtains the actual inner result using
  `decrypt_ratchet_no_panic`, under `DecryptRatchetContracts`,
  `DecryptRatchetHeadroom`, and `DerivedKeysModel`. It still requires a semantic
  refinement proof for every actual result. Thus outer-call existence is no
  longer an additional unexplained premise.
- `initial_ratchet_refines_terminal` discharges the inner semantic premise from
  the existing terminal-guard proof. `decrypt_initial_terminal_refines`
  composes this discharge with the whole initial wrapper.
- `initial_ratchet_refines_decode_refusal` discharges it for malformed embedded
  ratchet messages, using decoder failure evidence and the nonterminal guard.

The general nonterminal receive—including DH agreements, Braid/Triple receive,
AEAD output, committed state and consumed randomness—still needs its aggregate
T3 composition. The existing conditional branch lemmas are inputs to that work.

## Reproduction and limits of the controls

From `tacenta-proofs/translation`:

```sh
lake build Translation.UnitLifecycleInitialDispatch
```

From the repository root:

```sh
python3 tacenta-proofs/scripts/check-initial-dispatch-negatives.py
bash tacenta-proofs/scripts/no-sorry.sh
```

The negative suite elaborates a positive copy first, then three disposable
copies: bypass the ephemeral equality, bypass the identity equality, and
replace the terminal guard with its opposite. Each must fail with exit 1 and
a type mismatch at the named premise. Logs include a JSON result with the
proof source SHA-256. Timeout, missing compiler, missing dependencies, and an
unrelated failure do not count as a passing mutation. The suite uses existing
built imports, and does not edit repository files or create git worktrees.

These are **proof-dependency controls**, not tests of altered Rust or regenerated
code. They do not establish complete branch-mutation coverage or demonstrate
that a successful receive is reachable. Runtime/vector mutations and the
remaining aggregate receive proof stay open in the session plan.

The full `no-sorry.sh` gate runs the controls and includes this module in the
Session unit's axiom-audit closure and kernel replay.

## Verification record (2026-09-20)

The focused build and complete `no-sorry.sh` command both finished with exit
code 0. The complete run included the positive dispatcher baseline, all three
expected type-error controls, all thirteen axiom-audit negative cases, and
kernel replay of 68 translation/proof modules, 11 model-layer proof modules,
and 34 model/property modules. The control harness was also checked with a
zero-second timeout and an unavailable compiler; both returned nonzero without
reporting a passing control. These are local results, not hosted CI results.
