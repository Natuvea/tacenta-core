import Translation.UnitLifecycleT3
import Translation.UnitLifecyclePublicT1

/-!
# Initial-message dispatcher composition

The selector derives the four wrapper guards, constructs the corresponding
route, and splits the actual inner receive result. Its only remaining semantic
premise is refinement of the inner ratchet receive on a matching initial frame.
This is a conditional composition theorem, not the full session T3 theorem.
The T1 bridge below derives existence of the inner result from the existing
boundary contracts and headroom theorem. No public-decrypt witness or route
is accepted as an input.
-/

namespace Tacenta.UnitLifecycleT3
open Aeneas Aeneas.Std Result
open tacenta_session_unit

/-- Inner-call evidence is needed only after all initial-wrapper guards pass. -/
def InitialRatchetRefines {R : Type}
    (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R)
    (trace : R → List Model.Lifecycle.Key) (dh : DhView) (K : Model.Braid.Kem)
    (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle)
    (real : lifecycle.Session) (model : Model.Lifecycle.Session)
    (message : Slice Std.U8) (rng : R) : Prop :=
  ∀ (decoded : tacenta_wire.DecodedInitial) (established : alloc.vec.Vec Std.U8),
    tacenta_wire.decode_initial message = ok (.Ok decoded) →
    real.established_ephemeral = some established →
    vecOf established = vecOf decoded.ephemeral →
    vecOf decoded.identity =
      Model.PersistedState.SessionState.encodeEc (dh.publicKey real.peer_identity_public) →
    ∃ output,
      lifecycle.Session.decrypt_ratchet rc crc real decoded.message.deref rng = ok output ∧
      StepRefines trace dh K output (Model.Lifecycle.decryptRatchet view oracle model
        (Tacenta.SessionUnitWireInitialT3.initialOf decoded).ratchetMessage)

/-! ## T1-to-T3 bridge for the inner ratchet call

The generated T1 theorem proves that `decrypt_ratchet` returns some concrete
result under the boundary contracts and headroom conditions.  Keeping that
existence step separate means the aggregate T3 work only has to establish the
semantic relation for the result selected by the translated computation.
-/

theorem decrypt_ratchet_refines_of_t1
    {R : Type} {rc : rand_core_1.RngCore R} {crc : rand_core_1.CryptoRng R}
    {trace : R → List Model.Lifecycle.Key} {dh : DhView} {K : Model.Braid.Kem}
    {view : Model.Lifecycle.CodewordView} {oracle : Model.Lifecycle.Oracle}
    {real : lifecycle.Session} {model : Model.Lifecycle.Session}
    {message : Slice Std.U8} {rng : R}
    [Tacenta.SessionUnitT1.DerivedKeysModel]
    (boundary : Tacenta.UnitLifecycleT1.DecryptRatchetContracts rc)
    (headroom : Tacenta.UnitLifecycleT1.DecryptRatchetHeadroom real)
    (hrefines : ∀ output,
      lifecycle.Session.decrypt_ratchet rc crc real message rng = ok output →
      StepRefines trace dh K output
        (Model.Lifecycle.decryptRatchet view oracle model (sliceOf message))) :
    ∃ output,
      lifecycle.Session.decrypt_ratchet rc crc real message rng = ok output ∧
      StepRefines trace dh K output
        (Model.Lifecycle.decryptRatchet view oracle model (sliceOf message)) := by
  obtain ⟨output, hcall, _⟩ := Std.WP.spec_imp_exists
    (Tacenta.UnitLifecycleT1.decrypt_ratchet_no_panic rc crc boundary real message rng headroom)
  exact ⟨output, hcall, hrefines output hcall⟩

/-- Construct all six routes from the decoded input and state. The existential
route is a proposition so decoder proofs can be eliminated without choosing a
route supplied by the caller. -/
theorem initial_dispatch_route_from_ratchet
    {R : Type} {rc : rand_core_1.RngCore R} {crc : rand_core_1.CryptoRng R}
    {trace : R → List Model.Lifecycle.Key} {dh : DhView} {K : Model.Braid.Kem}
    {view : Model.Lifecycle.CodewordView} {oracle : Model.Lifecycle.Oracle}
    {real : lifecycle.Session} {model : Model.Lifecycle.Session}
    {message : Slice Std.U8} {rng : R}
    (codec : DhCodecOf dh)
    (ctx : InitialDispatchContext rc crc trace dh K view oracle real model message rng)
    (hreceive : InitialRatchetRefines rc crc trace dh K view oracle real model message rng) :
    Nonempty (InitialDispatchRoute rc crc trace dh K view oracle real model message rng) := by
  rcases initial_decode_cases message with ⟨reason, hdecode⟩ | ⟨decoded, hdecode⟩
  · exact ⟨.decodeRefusal (decrypt_initial_decode_refusal_refines rc crc trace dh K view
      oracle real model message rng reason ctx.hrel ctx.htrace ctx.htype hdecode)⟩
  · cases hestablished : real.established_ephemeral with
    | none =>
        exact ⟨initial_dispatch_no_established_from_premises ctx decoded hdecode hestablished⟩
    | some established =>
        by_cases he : vecOf established = vecOf decoded.ephemeral
        · by_cases hi : vecOf decoded.identity =
            Model.PersistedState.SessionState.encodeEc (dh.publicKey real.peer_identity_public)
          · obtain ⟨⟨result, next, rngNext⟩, hcall, hstep⟩ :=
              hreceive decoded established hdecode hestablished he hi
            have hw := decrypt_initial_repeat_step_refines rc crc trace dh codec K view oracle
              real model message rng established decoded (result, next, rngNext)
              ctx.hrel ctx.htype hdecode hestablished he hi hcall hstep
            cases result with
            | Err reason => exact ⟨.repeatRefusal hw⟩
            | Ok plaintext => exact ⟨.repeatSuccess hw⟩
          · exact ⟨initial_dispatch_identity_mismatch_from_premises (codec := codec)
              ctx established decoded hdecode hestablished he hi⟩
        · exact ⟨initial_dispatch_ephemeral_mismatch_from_premises
            ctx established decoded hdecode hestablished he⟩

/-- Initial-wrapper T3, conditional only on inner ratchet refinement and the
codec contract. No route or branch callback is an input. -/
theorem decrypt_initial_refines_from_ratchet
    {R : Type} {rc : rand_core_1.RngCore R} {crc : rand_core_1.CryptoRng R}
    {trace : R → List Model.Lifecycle.Key} {dh : DhView} {K : Model.Braid.Kem}
    {view : Model.Lifecycle.CodewordView} {oracle : Model.Lifecycle.Oracle}
    {real : lifecycle.Session} {model : Model.Lifecycle.Session}
    {message : Slice Std.U8} {rng : R}
    (codec : DhCodecOf dh)
    (ctx : InitialDispatchContext rc crc trace dh K view oracle real model message rng)
    (hreceive : InitialRatchetRefines rc crc trace dh K view oracle real model message rng) :
    PublicDecryptWitness rc crc trace dh K view oracle real model message rng := by
  obtain ⟨route⟩ := initial_dispatch_route_from_ratchet codec ctx hreceive
  exact initial_dispatch_join route

/-- Derive the inner call's existence from T1. The supplied semantic relation
must hold for every actual output; it cannot assume the call succeeds or pick
an output independently of the generated call. -/
theorem initial_ratchet_refines_of_t1
    {R : Type} {rc : rand_core_1.RngCore R} {crc : rand_core_1.CryptoRng R}
    {trace : R → List Model.Lifecycle.Key} {dh : DhView} {K : Model.Braid.Kem}
    {view : Model.Lifecycle.CodewordView} {oracle : Model.Lifecycle.Oracle}
    {real : lifecycle.Session} {model : Model.Lifecycle.Session}
    {message : Slice Std.U8} {rng : R}
    [Tacenta.SessionUnitT1.DerivedKeysModel]
    (boundary : Tacenta.UnitLifecycleT1.DecryptRatchetContracts rc)
    (headroom : Tacenta.UnitLifecycleT1.DecryptRatchetHeadroom real)
    (hrefines : ∀ (decoded : tacenta_wire.DecodedInitial) (established : alloc.vec.Vec Std.U8),
      tacenta_wire.decode_initial message = ok (.Ok decoded) →
      real.established_ephemeral = some established →
      vecOf established = vecOf decoded.ephemeral →
      vecOf decoded.identity =
        Model.PersistedState.SessionState.encodeEc (dh.publicKey real.peer_identity_public) →
      ∀ output, lifecycle.Session.decrypt_ratchet rc crc real decoded.message.deref rng = ok output →
        StepRefines trace dh K output (Model.Lifecycle.decryptRatchet view oracle model
          (Tacenta.SessionUnitWireInitialT3.initialOf decoded).ratchetMessage)) :
    InitialRatchetRefines rc crc trace dh K view oracle real model message rng := by
  intro decoded established hdecode hestablished he hi
  exact decrypt_ratchet_refines_of_t1 boundary headroom (fun output hcall =>
    hrefines decoded established hdecode hestablished he hi output hcall)

/-- A concrete discharge of the inner semantic premise for terminal Braid
states, with no assumed inner output or StepRefines witness. -/
theorem initial_ratchet_refines_terminal
    {R : Type} {rc : rand_core_1.RngCore R} {crc : rand_core_1.CryptoRng R}
    {trace : R → List Model.Lifecycle.Key} {dh : DhView} {K : Model.Braid.Kem}
    {view : Model.Lifecycle.CodewordView} {oracle : Model.Lifecycle.Oracle}
    {real : lifecycle.Session} {model : Model.Lifecycle.Session}
    {message : Slice Std.U8} {rng : R}
    (ctx : InitialDispatchContext rc crc trace dh K view oracle real model message rng)
    (hfailed : Model.Lifecycle.agreementFailed model = true) :
    InitialRatchetRefines rc crc trace dh K view oracle real model message rng := by
  intro decoded established hdecode hestablished he hi
  obtain ⟨hcall, hstep⟩ := decrypt_ratchet_terminal_guard_step_refines rc crc trace dh K view
    oracle real model decoded.message.deref rng ctx.hrel ctx.htrace hfailed
  exact ⟨_, hcall, hstep⟩

/-- Terminal-state initial decrypt: every wrapper guard and the inner receive
are discharged from the generated code and existing refinements. -/
theorem decrypt_initial_terminal_refines
    {R : Type} {rc : rand_core_1.RngCore R} {crc : rand_core_1.CryptoRng R}
    {trace : R → List Model.Lifecycle.Key} {dh : DhView} {K : Model.Braid.Kem}
    {view : Model.Lifecycle.CodewordView} {oracle : Model.Lifecycle.Oracle}
    {real : lifecycle.Session} {model : Model.Lifecycle.Session}
    {message : Slice Std.U8} {rng : R}
    (codec : DhCodecOf dh)
    (ctx : InitialDispatchContext rc crc trace dh K view oracle real model message rng)
    (hfailed : Model.Lifecycle.agreementFailed model = true) :
    PublicDecryptWitness rc crc trace dh K view oracle real model message rng :=
  decrypt_initial_refines_from_ratchet codec ctx (initial_ratchet_refines_terminal ctx hfailed)

/-- The selector's pending-state consequences follow from the same constructed
route: refusal preserves the pending projection, success clears it. -/
theorem initial_dispatch_atomicity_from_ratchet
    {R : Type} {rc : rand_core_1.RngCore R} {crc : rand_core_1.CryptoRng R}
    {trace : R → List Model.Lifecycle.Key} {dh : DhView} {K : Model.Braid.Kem}
    {view : Model.Lifecycle.CodewordView} {oracle : Model.Lifecycle.Oracle}
    {real : lifecycle.Session} {model : Model.Lifecycle.Session}
    {message : Slice Std.U8} {rng : R}
    (codec : DhCodecOf dh)
    (ctx : InitialDispatchContext rc crc trace dh K view oracle real model message rng)
    (hreceive : InitialRatchetRefines rc crc trace dh K view oracle real model message rng) :
    (∃ reason output,
      (Model.Lifecycle.decrypt view oracle model (sliceOf message)).result = .error reason ∧
      lifecycle.Session.decrypt rc crc real message rng = ok output ∧
      output.2.1.pending_initial.map (pendingInitialOf dh) = model.pendingInitial) ∨
    (∃ plaintext output,
      (Model.Lifecycle.decrypt view oracle model (sliceOf message)).result = .ok plaintext ∧
      lifecycle.Session.decrypt rc crc real message rng = ok output ∧
      output.2.1.pending_initial.map (pendingInitialOf dh) = none) := by
  obtain ⟨route⟩ := initial_dispatch_route_from_ratchet codec ctx hreceive
  exact initial_dispatch_select_atomicity route

/-- The inner premise is also discharged for malformed ratchet payloads. This
requires a decoder result, not a hypothesized ratchet output or refinement. -/
theorem initial_ratchet_refines_decode_refusal
    {R : Type} {rc : rand_core_1.RngCore R} {crc : rand_core_1.CryptoRng R}
    {trace : R → List Model.Lifecycle.Key} {dh : DhView} {K : Model.Braid.Kem}
    {view : Model.Lifecycle.CodewordView} {oracle : Model.Lifecycle.Oracle}
    {real : lifecycle.Session} {model : Model.Lifecycle.Session}
    {message : Slice Std.U8} {rng : R}
    (ctx : InitialDispatchContext rc crc trace dh K view oracle real model message rng)
    (hready : Model.Lifecycle.agreementFailed model = false)
    (hbad : ∀ decoded : tacenta_wire.DecodedInitial,
      tacenta_wire.decode_initial message = ok (.Ok decoded) →
      ∃ reason, tacenta_wire.decode_message decoded.message.deref = ok (.Err reason)) :
    InitialRatchetRefines rc crc trace dh K view oracle real model message rng := by
  intro decoded established hdecode hestablished he hi
  obtain ⟨reason, hbad⟩ := hbad decoded hdecode
  obtain ⟨hcall, hstep⟩ := decrypt_ratchet_decode_refusal_refines rc crc trace dh K view
    oracle real model decoded.message.deref rng reason ctx.hrel ctx.htrace hready hbad
  exact ⟨_, hcall, hstep⟩

end Tacenta.UnitLifecycleT3
