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

`braid_receive_evidence` is the first nonterminal adapter. It derives
`msg_of`, `Braid.receive`, the Braid message relation, next-state relation, and
the optional sparse-output conversion from the existing Braid T3 theorem. Its
additional inputs are explicit Braid semantic contracts (`KemAgreesFor`,
`ErasureAgrees`, the length/clone contracts, and the honest-chunk/epoch
conditions). `decrypt_ratchet_first_dh_refusal_from_braid` consumes that record
and closes the first non-contributory-DH refusal branch. Triple, second-DH,
AEAD, and success composition remain open.

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

The first nonterminal branch is now composed through
`decrypt_ratchet_first_dh_refusal_from_braid`. Its Braid evidence is derived
by `braid_receive_evidence` from the existing Braid T3 theorem plus explicit
semantic contracts, honest-chunk evidence and the successor-epoch bound. This
closes only the model `dhAgree = none` refusal branch; the second-DH, Triple,
AEAD and success branches still require their own evidence.

`decrypt_ratchet_second_dh_refusal_from_braid` now reuses the same adapter for
the second-DH refusal. Its consumed draw and first/second DH oracle results
remain explicit, including the advanced trace; it does not treat the refusal
as state-preserving without accounting for that draw.

The full `no-sorry.sh` gate runs the controls and includes this module in the
Session unit's axiom-audit closure and kernel replay.

## Current composition boundary (2026-09-23)

The public result-shaped bridge is now exposed by
`decrypt_initial_refines_of_t1_with_nonterminal_route`. It splits the actual
`decrypt_ratchet` result, derives terminal and malformed-message evidence from
the generated call, and accepts a typed refusal route for the remaining
nonterminal families. `InitialRatchetRefusalRoute` is indexed by the exact
error, successor session, and RNG successor; its DH constructor is fed by the
first/second-DH adapter, and its Triple/AEAD constructors accept only an exact
generated `Err` call paired with the matching `StepRefines` result.

On the success side, `InitialRatchetSuccessPrefix` and
`InitialRatchetModelSuccessFacts` expose the generated and model receive
partitions. The direct adapter routes through
`aggregate_receive_core_refinement_of_direct`; the classical/post-quantum
full-store adapter routes through the shared retry refinement. The resulting
`InitialRatchetSuccessSplice` is indexed by the same concrete and model
results, so a detached Triple candidate cannot be substituted. The
`initial_ratchet_success_branch_of_actual_receive_cases` and
`initial_ratchet_success_splice_of_actual_receive_cases` bridges require the
provider to consume the two partitions extracted from those exact prefixes
before constructing the splice.

The latest success boundary packages those obligations in
`InitialRatchetConcreteSuccessProvider`. Its direct and full-store callbacks,
state/key/plaintext relations, and oracle trace are all indexed by the exact
`InitialRatchetSuccessPrefix` and `InitialRatchetModelSuccessFacts`.
`initial_ratchet_model_success_facts_of_result` now obtains those model facts
by case-splitting the actual successful `decryptRatchet` result, so a caller
cannot supply an unrelated model candidate. The
`initial_ratchet_success_callback_of_model_step_and_provider` theorem combines
that inversion with the concrete provider and lifts it into the result-shaped
callback consumed by `InitialRatchetRefines`.

The refusal side now has the matching model-result boundary in
`initial_ratchet_refines_of_t1_result_split_with_model_refusal_provider`.
It classifies terminal and malformed results before the nonterminal split,
passes the exact decoder exclusion into the model refusal inversion, and
hands the resulting `InitialRatchetModelRefusalCase` to an indexed DH,
Triple, or AEAD provider. The route remains indexed by the actual error,
successor, and RNG state. This is still a composition boundary: the provider
must be instantiated from the concrete Braid/primitive contracts, and the
success callback must be supplied at the public Session bridge. Vector and
mutation evidence then need to cover every resulting route.

The exact head `a4e9a82` passed focused Lean compilation, all three dispatcher
mutation controls, attestation refresh/check, and diff checks. The exact-head
full local replay was clean on `0de9430` before this wrapper-only theorem was
added: 2,318 translation/T1/T3 jobs, 37 model proof jobs, 64 model/property
jobs, all kernel replays, audit negatives, reachability, and dispatcher
mutation controls. Hosted run `35818611209` for `0de9430` has armv7, rust,
vectors, proofs, msrv, sign-off, audit, and checks green; `translation` is
still in progress, so no hosted-green claim is made.

## Verification record (2026-09-20)

The focused build and complete `no-sorry.sh` command both finished with exit
code 0. The complete run included the positive dispatcher baseline, all three
expected type-error controls, all thirteen axiom-audit negative cases, and
kernel replay of 68 translation/proof modules, 11 model-layer proof modules,
and 34 model/property modules. The control harness was also checked with a
zero-second timeout and an unavailable compiler; both returned nonzero without
reporting a passing control. These are local results, not hosted CI results.

After the first-DH adapter landed in `48610c0` (manifests refreshed in
`8a0aeaf`), the focused 1,733-job build and the complete `no-sorry.sh` gate
again finished with exit code 0. Kernel replay again covered 68 translation,
11 model-layer proof, and 34 model/property modules.
