import Translation.UnitLifecycleDecryptRatchetCompleteScreen
import Translation.UnitHeadroomInvariant

/-!
# The public `Session::decrypt` refines the model's step on frames that are not initial messages

`UnitLifecycleT3.decrypt_passthrough_refines` lifts a refinement of the private `decrypt_ratchet`
through the pass-through arms of the generated public `decrypt` (no type, too short, wrong version,
unknown type, and the ratchet type), but it takes that inner refinement as two hypotheses
(`hinner`, `hstep`).  `UnitLifecycleDecryptRatchetCompleteT3.decrypt_ratchet_refines_complete`
concludes exactly that inner refinement, on every path of `decrypt_ratchet`.  This module joins the
two:

* `decrypt_refines_ratchet_frame`: for every message the model's dispatch passes through unchanged,
  the generated public `lifecycle.Session.decrypt` returns, and its result, the session it leaves
  (with `pending_initial` cleared exactly on success) and the remaining trace refine
  `Model.Lifecycle.decrypt`.  Its hypotheses are those of `decrypt_ratchet_refines_complete` and one
  scope premise on the input, `hframe`: the model's reading of the bytes is not an initial message.
  `hframe` is decidable from the message alone and selects no branch of the proof; the proof derives
  the generated type from it through `message_type_refines`.  The binders of the inner theorem are
  fixed as follows: the Braid KEM model is `oracle.braidKem`, the generated type `realType` and its
  equation come from `message_type_refines`, and the inner output is the one the complete theorem
  gives.
* `decrypt_refines_ratchet_frame_of_invariant`: the same, with `DecryptRatchetHeadroom` replaced by
  `Session::invariant` (`UnitHeadroomInvariant.decryptHeadroom_of_invariant`, from two fields of the
  contract record the theorem already takes).
* `decrypt_refines_ratchet_frame_at_refusal`: the theorem at the run of
  `UnitLifecycleDecryptRatchetCompleteScreen.ref_run_satisfiable`.  That state fails
  `Session::invariant` (empty associated data, `refReal_fails_invariant`) and `Ratchet::invariant`, so it
  shows the hypotheses consistent, not met by an admissible state.
* `decrypt_refines_ratchet_frame_of_invariant_at_sample`: the corollary at the sample run of
  `UnitLifecycleDecryptRatchetScreen.sample_run_satisfiable` rebased on the session of
  `UnitHeadroomInvariant.sessionOf_invariant` (associated data `identity_ad(pk, pk)`, the ratchet
  key's own public bytes), which passes `Session::invariant` under that theorem's two recorded
  assumptions (a canonical prime-order key, `ValidKeyShape`; `Option::eq` on `u64`,
  `OptionEqU64Shape`).

## What this does not show

* Any initial frame: the repeated-initial branch is outside `hframe`.
* That the boundary records hold of the shipped functions: three fields of `DecryptRatchetContracts`
  are stronger than the crate supports, so the theorem cannot be applied to the shipped functions
  until they are restated; `VecRetainAgrees` and `RemoveSkippedAtAgrees` are assumed and undecided.
* A run carrying an agreement chunk: every witness here carries none.
* Anything about a random source with no state of its own: the trace is read as a function of the
  source's value, so for such a source the hypotheses cannot all hold and the theorem makes no claim.
* That any witness state is one the shipped code produces: the invariant-passing session has no
  pending initial message, no receiving chain and no established ephemeral key, and its model step
  refuses at the first agreement.

The results rest on the nine compiler-trusted `native_decide` facts `decrypt_ratchet_refines_complete`
rests on, which their pins list.
-/

namespace Tacenta.UnitLifecycleDecryptT3

open Aeneas Aeneas.Std Result
open tacenta_session_unit
open Tacenta.UnitLifecycleT3
open Tacenta.UnitLifecycleDecryptRatchetT3

/-! ## Statement -/

/-- The statement of `decrypt_refines_ratchet_frame`, as a proposition: the hypotheses of
`DecryptRatchetRefinesCompleteStatement` and the scope premise `hframe`, with the public `decrypt`
and the model's full step in the conclusion. -/
def DecryptRefinesRatchetFrameStatement : Prop :=
  ∀ {R : Type} (rngCore : rand_core_1.RngCore R) (cryptoRng : rand_core_1.CryptoRng R)
    (trace : R → List Model.Lifecycle.Key) (dh : DhView)
    (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle),
    DecryptOracleOf rngCore cryptoRng dh trace oracle →
    DhCodecOf dh →
    Tacenta.UnitLifecycleT1.DecryptRatchetContracts rngCore →
    ∀ [Tacenta.SessionUnitT1.DerivedKeysModel],
    DecryptRatchetAgreements oracle.braidKem →
    ∀ (real : lifecycle.Session) (model : Model.Lifecycle.Session)
      (message : Slice Std.U8) (rng : R),
      Model.Lifecycle.messageType (sliceOf message) ≠ some .initial →
      SessionRefines dh oracle.braidKem real model →
      Tacenta.UnitLifecycleT1.DecryptRatchetHeadroom real →
      trace rng = oracle.draws →
      DecryptRatchetRun view oracle trace real model message rng →
      ∃ output,
        lifecycle.Session.decrypt rngCore cryptoRng real message rng = ok output ∧
        StepRefines trace dh oracle.braidKem output
          (Model.Lifecycle.decrypt view oracle model (sliceOf message))

/-! ## The join -/

/-- **The generated public `decrypt` refines `Model.Lifecycle.decrypt` on every frame that is not an
initial message.**  The inner step is `decrypt_ratchet_refines_complete`, discharged by proof, and the
pass-through arm and the clearing of `pending_initial` are `decrypt_passthrough_refines`.  Every
hypothesis is one `decrypt_ratchet_refines_complete` takes, except `hframe`, a scope premise on the
input stated on the model's reading of the bytes. -/
theorem decrypt_refines_ratchet_frame {R : Type}
    (rngCore : rand_core_1.RngCore R) (cryptoRng : rand_core_1.CryptoRng R)
    (trace : R → List Model.Lifecycle.Key) (dh : DhView)
    (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle)
    (oracleOf : DecryptOracleOf rngCore cryptoRng dh trace oracle)
    (codec : DhCodecOf dh)
    (contracts : Tacenta.UnitLifecycleT1.DecryptRatchetContracts rngCore)
    [Tacenta.SessionUnitT1.DerivedKeysModel]
    (agreements : DecryptRatchetAgreements oracle.braidKem)
    (real : lifecycle.Session) (model : Model.Lifecycle.Session)
    (message : Slice Std.U8) (rng : R)
    (hframe : Model.Lifecycle.messageType (sliceOf message) ≠ some .initial)
    (hrel : SessionRefines dh oracle.braidKem real model)
    (headroom : Tacenta.UnitLifecycleT1.DecryptRatchetHeadroom real)
    (htrace : trace rng = oracle.draws)
    (run : DecryptRatchetRun view oracle trace real model message rng) :
    ∃ output,
      lifecycle.Session.decrypt rngCore cryptoRng real message rng = ok output ∧
      StepRefines trace dh oracle.braidKem output
        (Model.Lifecycle.decrypt view oracle model (sliceOf message)) := by
  obtain ⟨innerOutput, hinner, hstep⟩ :=
    Tacenta.UnitLifecycleDecryptRatchetCompleteT3.decrypt_ratchet_refines_complete rngCore cryptoRng
      trace dh view oracle oracleOf codec contracts agreements real model message rng hrel headroom
      htrace run
  obtain ⟨realType, htype, -⟩ := Std.WP.spec_imp_exists (message_type_refines message)
  have hnotInitial : realType ≠ some .Initial := by
    rintro rfl
    exact hframe (message_type_refines_initial message htype)
  exact decrypt_passthrough_refines rngCore cryptoRng trace dh oracle.braidKem view oracle real model
    message rng realType innerOutput htype hnotInitial hinner hstep

/-- The theorem has exactly the statement recorded in `DecryptRefinesRatchetFrameStatement`. -/
theorem decrypt_refines_ratchet_frame_statement : DecryptRefinesRatchetFrameStatement := by
  intro R rngCore cryptoRng trace dh view oracle oracleOf codec contracts inst agreements real
    model message rng hframe hrel headroom htrace run
  exact decrypt_refines_ratchet_frame rngCore cryptoRng trace dh view oracle oracleOf codec
    contracts agreements real model message rng hframe hrel headroom htrace run

/-- **The same, for a session that passes `Session::invariant`**, which gives
`DecryptRatchetHeadroom` through two fields of the contract record (`dhCodec`, `braid.ct1Len`). -/
theorem decrypt_refines_ratchet_frame_of_invariant {R : Type}
    (rngCore : rand_core_1.RngCore R) (cryptoRng : rand_core_1.CryptoRng R)
    (trace : R → List Model.Lifecycle.Key) (dh : DhView)
    (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle)
    (oracleOf : DecryptOracleOf rngCore cryptoRng dh trace oracle)
    (codec : DhCodecOf dh)
    (contracts : Tacenta.UnitLifecycleT1.DecryptRatchetContracts rngCore)
    [Tacenta.SessionUnitT1.DerivedKeysModel]
    (agreements : DecryptRatchetAgreements oracle.braidKem)
    (real : lifecycle.Session) (model : Model.Lifecycle.Session)
    (message : Slice Std.U8) (rng : R)
    (hframe : Model.Lifecycle.messageType (sliceOf message) ≠ some .initial)
    (hrel : SessionRefines dh oracle.braidKem real model)
    (hinv : lifecycle.Session.invariant real = ok true)
    (htrace : trace rng = oracle.draws)
    (run : DecryptRatchetRun view oracle trace real model message rng) :
    ∃ output,
      lifecycle.Session.decrypt rngCore cryptoRng real message rng = ok output ∧
      StepRefines trace dh oracle.braidKem output
        (Model.Lifecycle.decrypt view oracle model (sliceOf message)) :=
  decrypt_refines_ratchet_frame rngCore cryptoRng trace dh view oracle oracleOf codec contracts
    agreements real model message rng hframe hrel
    (Tacenta.UnitHeadroomInvariant.decryptHeadroom_of_invariant contracts.dhCodec
      contracts.braid.ct1Len real hinv)
    htrace run

/-! ## Witnesses

Two runs at which every per-run hypothesis holds.  The boundary records (`DecryptOracleOf`,
`DhCodecOf`, `DecryptRatchetContracts`, `DerivedKeysModel`, `DecryptRatchetAgreements`) stay
arguments: they are not discharged at either run. -/

open Tacenta.UnitLifecycleDecryptRatchetScreen
open Tacenta.UnitLifecycleDecryptRatchetCompleteScreen

/-- The message of the refusal run is not an initial message on the model's reading. -/
theorem succMessage_not_initial :
    Model.Lifecycle.messageType (sliceOf succMessage) ≠ some .initial := by
  rw [show sliceOf succMessage = succBytes from
    Tacenta.UnitSatisfiabilityBraidStates.sliceOf_sliceOfBytes succBytes succBytes_le]
  decide

/-- The message of the sample run is not an initial message on the model's reading. -/
theorem sampleMessage_not_initial :
    Model.Lifecycle.messageType (sliceOf sampleMessage) ≠ some .initial := by
  rw [sliceOf_sampleMessage]
  decide

/-- The state of the refusal run fails `Session::invariant`: its associated data is empty, and a session
that passes the invariant holds 66 bytes there (`UnitHeadroomInvariant.invariant_gives_ad_length`, under
`DhCodecTotal`, a field of every contract record). -/
theorem refReal_fails_invariant (hdh : Tacenta.UnitLifecycleT1.DhCodecTotal)
    (sk : tacenta_boundary.dh.PrivateKey) (pk : tacenta_boundary.dh.PublicKeyBytes) :
    lifecycle.Session.invariant (refReal sk pk) ≠ ok true := by
  intro h
  have hlen := Tacenta.UnitHeadroomInvariant.invariant_gives_ad_length hdh _ h
  simp [refReal, sampleReal, Tacenta.UnitHeadroomSatisfiable.sessionOf,
    Tacenta.UnitHeadroomSatisfiable.vecOf] at hlen

/-- **The theorem at the run of `ref_run_satisfiable`**, whose model step is the Triple refusal
`outOfOrder` with part B's oracle.  Its state fails `Session::invariant` (`refReal_fails_invariant`:
empty associated data) and `Ratchet::invariant` (a receiving chain without a sending chain), so this
shows the hypotheses consistent, not met by a state the crate admits. -/
theorem decrypt_refines_ratchet_frame_at_refusal (dh : DhView)
    (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle)
    (hdraws : oracle.draws = Tacenta.UnitLifecycleIntegrationScreen.byteTrace sampleRng)
    (oracleOf : DecryptOracleOf Tacenta.UnitLifecycleIntegrationScreen.byteRng
      Tacenta.UnitLifecycleIntegrationScreen.byteCrc dh
      Tacenta.UnitLifecycleIntegrationScreen.byteTrace oracle)
    (codec : DhCodecOf dh)
    (contracts : Tacenta.UnitLifecycleT1.DecryptRatchetContracts
      Tacenta.UnitLifecycleIntegrationScreen.byteRng)
    [Tacenta.SessionUnitT1.DerivedKeysModel]
    (agreements : DecryptRatchetAgreements oracle.braidKem)
    (sk : tacenta_boundary.dh.PrivateKey) (pk : tacenta_boundary.dh.PublicKeyBytes) :
    ∃ output,
      lifecycle.Session.decrypt Tacenta.UnitLifecycleIntegrationScreen.byteRng
        Tacenta.UnitLifecycleIntegrationScreen.byteCrc (refReal sk pk) succMessage sampleRng =
          ok output ∧
      StepRefines Tacenta.UnitLifecycleIntegrationScreen.byteTrace dh oracle.braidKem output
        (Model.Lifecycle.decrypt view oracle (modelOf dh (refReal sk pk)) (sliceOf succMessage)) := by
  obtain ⟨hrel, hroom, hrun⟩ := ref_run_satisfiable oracle.braidKem dh sk pk
  obtain ⟨htrace, run⟩ := hrun view oracle rfl hdraws
  exact decrypt_refines_ratchet_frame _ _ _ dh view oracle oracleOf codec contracts agreements
    (refReal sk pk) (modelOf dh (refReal sk pk)) succMessage sampleRng succMessage_not_initial hrel
    hroom htrace run

/-- The session of `UnitHeadroomInvariant.sessionOf_invariant`: fresh Triple and Braid states over the
ratchet key's own public bytes `a`, the identity public key `pkb` on both sides, the associated data
`ad`, no pending initial message and no established ephemeral key. -/
def invReal (k : tacenta_boundary.dh.PrivateKey) (pkb : tacenta_boundary.dh.PublicKeyBytes)
    (a : Array U8 32#usize) (ad : alloc.vec.Vec U8) : lifecycle.Session :=
  Tacenta.UnitHeadroomSatisfiable.sessionOf k pkb pkb ad a none

theorem inv_sessionRefines (K : Model.Braid.Kem) (dh : DhView)
    (k : tacenta_boundary.dh.PrivateKey) (pkb : tacenta_boundary.dh.PublicKeyBytes)
    (a : Array U8 32#usize) (ad : alloc.vec.Vec U8) :
    SessionRefines dh K (invReal k pkb a ad) (modelOf dh (invReal k pkb a ad)) :=
  ⟨⟨rfl, rfl⟩, (Tacenta.UnitSatisfiabilityBraidStates.good_keysUnsampled (K := K)).1,
    rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem inv_retryRunBounds (k : tacenta_boundary.dh.PrivateKey)
    (pkb : tacenta_boundary.dh.PublicKeyBytes) (a : Array U8 32#usize) (ad : alloc.vec.Vec U8)
    (dh : DhView) (output : Option Model.SparseRatchet.Output) (houtput : output = none) :
    RetryRunBounds (modelOf dh (invReal k pkb a ad)).triple
      (Model.Lifecycle.tripleHeaderOf sampleComposite) output := by
  subst houtput
  have hu := Tacenta.UnitHeadroomSatisfiable.usize_max_ge
  constructor <;>
    simp [modelOf, invReal, Tacenta.UnitHeadroomSatisfiable.sessionOf,
      Tacenta.UnitHeadroomSatisfiable.freshTriple, Tacenta.UnitHeadroomSatisfiable.vecOf,
      Tacenta.SessionUnitTripleT3.ratchetAbs, Tacenta.SessionUnitTripleT3.spqrAbs,
      Model.State.maxSkippedStore, Model.SparseRatchet.maxSkippedStore,
      Model.SparseRatchet.epochsKept, U32.max_eq, U64.max_eq, cMax_usize,
      Tacenta.SessionUnitSpqrT3.chainsEntryOf, Tacenta.SessionUnitSpqrT3.chainsOf]
  all_goals omega

/-- **The per-run hypotheses hold at the sample run over the invariant-passing session**, for every
Braid KEM model, codeword view and oracle with that KEM model and the source's draws.  The message is
`sampleMessage`, whose composite carries no agreement chunk. -/
theorem inv_run_satisfiable (K : Model.Braid.Kem) (dh : DhView)
    (k : tacenta_boundary.dh.PrivateKey) (pkb : tacenta_boundary.dh.PublicKeyBytes)
    (a : Array U8 32#usize) (ad : alloc.vec.Vec U8) :
    SessionRefines dh K (invReal k pkb a ad) (modelOf dh (invReal k pkb a ad)) ∧
    ∀ (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle),
      oracle.braidKem = K →
      oracle.draws = Tacenta.UnitLifecycleIntegrationScreen.byteTrace sampleRng →
      Tacenta.UnitLifecycleIntegrationScreen.byteTrace sampleRng = oracle.draws ∧
      DecryptRatchetRun view oracle Tacenta.UnitLifecycleIntegrationScreen.byteTrace
        (invReal k pkb a ad) (modelOf dh (invReal k pkb a ad)) sampleMessage sampleRng := by
  refine ⟨inv_sessionRefines K dh k pkb a ad, ?_⟩
  intro view oracle hK hdraws
  refine ⟨hdraws.symm, ?_⟩
  have hmodelBraid : (modelOf dh (invReal k pkb a ad)).braid =
      .keysUnsampled 1 Tacenta.UnitSatisfiabilityBraidStates.modelAuth0 := rfl
  refine
    { chunk := ?_
      honest := ?_
      braidEpoch := ?_
      draw := ⟨_, [], sample_trace⟩
      retry := ?_ }
  · intro realComposite modelComposite ciphertext hdecode hcomposite
    rw [sample_decode_model] at hdecode
    have hmc : sampleComposite = modelComposite := (Prod.mk.inj (Except.ok.inj hdecode)).1
    subst hmc
    have hchunk := hcomposite.agChunk
    unfold IncomingChunkRefines
    cases hr : realComposite.ag_chunk with
    | none => simp [sampleComposite]
    | some c => simp [hr, sampleComposite] at hchunk
  · intro modelComposite ciphertext hdecode
    rw [sample_decode_model] at hdecode
    have hmc : sampleComposite = modelComposite := (Prod.mk.inj (Except.ok.inj hdecode)).1
    subst hmc
    intro mc hmc
    simp [Model.Lifecycle.braidMessageOf, sampleComposite] at hmc
  · simp only [invReal, Tacenta.UnitHeadroomSatisfiable.sessionOf,
      Tacenta.UnitHeadroomSatisfiable.freshBraid, Tacenta.SessionUnitBraidT1.State.epoch_val]
    scalar_tac
  · intro modelComposite ciphertext hdecode
    rw [sample_decode_model] at hdecode
    have hmc : sampleComposite = modelComposite := (Prod.mk.inj (Except.ok.inj hdecode)).1
    subst hmc
    apply inv_retryRunBounds
    rw [hmodelBraid, hK, sample_braid_output]
    rfl

/-- With part B's oracle of `UnitLifecycleDecryptRatchetScreen`, the model's step at the sample run
over the invariant-passing session refuses at the first agreement, as the sample run's does. -/
theorem inv_model_refuses (dh : DhView) (view : Model.Lifecycle.CodewordView)
    (k : tacenta_boundary.dh.PrivateKey) (pkb : tacenta_boundary.dh.PublicKeyBytes)
    (a : Array U8 32#usize) (ad : alloc.vec.Vec U8) :
    (Model.Lifecycle.decrypt view
      (oracleDecrypt (Tacenta.UnitLifecycleIntegrationScreen.byteTrace sampleRng))
      (modelOf dh (invReal k pkb a ad)) (sliceOf sampleMessage)).result =
      .error (.handshake .nonContributoryAgreement) := by
  have hzero : sampleComposite.dh = arrayOf zeros32 := by
    simp [sampleComposite, arrayOf, zeros32, Array.repeat, Tacenta.SessionUnitBraidT3.u8]
  have hdispatch := Model.Lifecycle.dispatchDecrypt_passthrough
    (oracleDecrypt (Tacenta.UnitLifecycleIntegrationScreen.byteTrace sampleRng))
    (modelOf dh (invReal k pkb a ad)) (sliceOf sampleMessage) sampleMessage_not_initial
  have hstep : (Model.Lifecycle.decryptRatchet view
      (oracleDecrypt (Tacenta.UnitLifecycleIntegrationScreen.byteTrace sampleRng))
      (modelOf dh (invReal k pkb a ad)) (sliceOf sampleMessage)).result =
      .error (.handshake .nonContributoryAgreement) := by
    simp [Model.Lifecycle.decryptRatchet, Model.Lifecycle.agreementFailed, modelOf,
      sample_decode_model, oracleDecrypt, hzero]
  unfold Model.Lifecycle.decrypt
  rw [hdispatch]
  simp only
  split <;> simp_all

/-- **The `Session::invariant` corollary at a state that passes `Session::invariant`.**  The session
is `invReal k pkb a ad`, the session of `UnitHeadroomInvariant.sessionOf_invariant`, and the
hypotheses `hpub` to `had` are that theorem's: `a` is the public bytes of `k`'s public key `pkb`,
canonical and of prime order (`ValidKeyShape`), `Option::eq` on `u64` compares (`OptionEqU64Shape`),
and `ad` is `identity_ad(pkb, pkb)`.  The invariant holds there, and the corollary applies at the
sample run.  The boundary records are arguments, not discharged here.  The state is built for the
hypotheses and is not shown to be produced by `establish_initiator` or `establish_responder`: it
holds no pending initial message, no receiving chain and no established ephemeral key. -/
theorem decrypt_refines_ratchet_frame_of_invariant_at_sample (dh : DhView)
    (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle)
    (hdraws : oracle.draws = Tacenta.UnitLifecycleIntegrationScreen.byteTrace sampleRng)
    (oracleOf : DecryptOracleOf Tacenta.UnitLifecycleIntegrationScreen.byteRng
      Tacenta.UnitLifecycleIntegrationScreen.byteCrc dh
      Tacenta.UnitLifecycleIntegrationScreen.byteTrace oracle)
    (codec : DhCodecOf dh)
    (contracts : Tacenta.UnitLifecycleT1.DecryptRatchetContracts
      Tacenta.UnitLifecycleIntegrationScreen.byteRng)
    [Tacenta.SessionUnitT1.DerivedKeysModel]
    (agreements : DecryptRatchetAgreements oracle.braidKem)
    (k : tacenta_boundary.dh.PrivateKey) (pkb : tacenta_boundary.dh.PublicKeyBytes)
    (a : Array U8 32#usize)
    (hpub : tacenta_boundary.dh.PrivateKey.public_key k = ok pkb)
    (hbytes : tacenta_boundary.dh.PublicKeyBytes.as_bytes pkb = ok a)
    (hcan : Tacenta.SessionUnitT1.canonicalX25519 a = true)
    (hprime : tacenta_boundary.dh.is_prime_order_public pkb = ok true)
    (hoeq : Tacenta.UnitHeadroomInvariant.OptionEqU64Shape
      (@core.option.Option.Insts.CoreCmpPartialEqOption.eq))
    (ad : alloc.vec.Vec U8) (had : lifecycle.identity_ad pkb pkb = ok ad) :
    lifecycle.Session.invariant (invReal k pkb a ad) = ok true ∧
    ∃ output,
      lifecycle.Session.decrypt Tacenta.UnitLifecycleIntegrationScreen.byteRng
        Tacenta.UnitLifecycleIntegrationScreen.byteCrc (invReal k pkb a ad) sampleMessage
          sampleRng = ok output ∧
      StepRefines Tacenta.UnitLifecycleIntegrationScreen.byteTrace dh oracle.braidKem output
        (Model.Lifecycle.decrypt view oracle (modelOf dh (invReal k pkb a ad))
          (sliceOf sampleMessage)) := by
  have hinv : lifecycle.Session.invariant (invReal k pkb a ad) = ok true :=
    Tacenta.UnitHeadroomInvariant.sessionOf_invariant k pkb a hpub hbytes hcan hprime hoeq ad had
  obtain ⟨hrel, hrun⟩ := inv_run_satisfiable oracle.braidKem dh k pkb a ad
  obtain ⟨htrace, run⟩ := hrun view oracle rfl hdraws
  exact ⟨hinv, decrypt_refines_ratchet_frame_of_invariant _ _ _ dh view oracle oracleOf codec
    contracts agreements (invReal k pkb a ad) (modelOf dh (invReal k pkb a ad)) sampleMessage
    sampleRng sampleMessage_not_initial hrel hinv htrace run⟩

end Tacenta.UnitLifecycleDecryptT3

/-! ## Pins -/

/--
info: 'Tacenta.UnitLifecycleDecryptT3.decrypt_refines_ratchet_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kdf.hkdf_sha256,
 tacenta_session_unit.tacenta_kdf.hmac_sha256,
 tacenta_session_unit.tacenta_kem.CT1_LEN,
 tacenta_session_unit.tacenta_kem.CT2_LEN,
 tacenta_session_unit.tacenta_kem.EK_VECTOR_LEN,
 tacenta_session_unit.tacenta_kem.EncapsState,
 tacenta_session_unit.tacenta_kem.HEADER_LEN,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair,
 tacenta_session_unit.tacenta_kem.encapsulate1,
 tacenta_session_unit.tacenta_kem.encapsulate2,
 tacenta_session_unit.tacenta_kem.validate_ek,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.rand_core_1.error.Error,
 tacenta_session_unit.tacenta_boundary.aead.decrypt,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.generate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.header,
 tacenta_session_unit.zeroize.Zeroizing.new,
 tacenta_session_unit.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.Pair.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.TupleABC.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.alloc.vec.Vec.capacity,
 tacenta_session_unit.alloc.vec.Vec.pop,
 tacenta_session_unit.alloc.vec.Vec.truncate,
 tacenta_session_unit.core.num.Usize.div_ceil,
 tacenta_session_unit.core.option.Option.as_mut,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.agree,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.from_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.public_key,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.to_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.from_bytes,
 tacenta_session_unit.zeroize.Zeroize.Blanket.zeroize,
 Tacenta.SessionUnitSpqrT3.chain_label_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.chain_start_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.max_skip_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.max_skip_val._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.max_skipped_store_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.protocol_info_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.receive_refines_continuation._native.native_decide.ax_1_29,
 Tacenta.SessionUnitSpqrT3.root_label_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitTripleT3.combine_info_agrees._native.native_decide.ax_1_1,
 tacenta_session_unit.tacenta_kem.EncapsState.Insts.CoreCloneClone.clone,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 tacenta_session_unit.alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.core.option.Option.Insts.CoreCloneClone.clone,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes.eq,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleDecryptT3.decrypt_refines_ratchet_frame

/--
info: 'Tacenta.UnitLifecycleDecryptT3.decrypt_refines_ratchet_frame_statement' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kdf.hkdf_sha256,
 tacenta_session_unit.tacenta_kdf.hmac_sha256,
 tacenta_session_unit.tacenta_kem.CT1_LEN,
 tacenta_session_unit.tacenta_kem.CT2_LEN,
 tacenta_session_unit.tacenta_kem.EK_VECTOR_LEN,
 tacenta_session_unit.tacenta_kem.EncapsState,
 tacenta_session_unit.tacenta_kem.HEADER_LEN,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair,
 tacenta_session_unit.tacenta_kem.encapsulate1,
 tacenta_session_unit.tacenta_kem.encapsulate2,
 tacenta_session_unit.tacenta_kem.validate_ek,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.rand_core_1.error.Error,
 tacenta_session_unit.tacenta_boundary.aead.decrypt,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.generate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.header,
 tacenta_session_unit.zeroize.Zeroizing.new,
 tacenta_session_unit.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.Pair.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.TupleABC.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.alloc.vec.Vec.capacity,
 tacenta_session_unit.alloc.vec.Vec.pop,
 tacenta_session_unit.alloc.vec.Vec.truncate,
 tacenta_session_unit.core.num.Usize.div_ceil,
 tacenta_session_unit.core.option.Option.as_mut,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.agree,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.from_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.public_key,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.to_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.from_bytes,
 tacenta_session_unit.zeroize.Zeroize.Blanket.zeroize,
 Tacenta.SessionUnitSpqrT3.chain_label_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.chain_start_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.max_skip_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.max_skip_val._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.max_skipped_store_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.protocol_info_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.receive_refines_continuation._native.native_decide.ax_1_29,
 Tacenta.SessionUnitSpqrT3.root_label_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitTripleT3.combine_info_agrees._native.native_decide.ax_1_1,
 tacenta_session_unit.tacenta_kem.EncapsState.Insts.CoreCloneClone.clone,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 tacenta_session_unit.alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.core.option.Option.Insts.CoreCloneClone.clone,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes.eq,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleDecryptT3.decrypt_refines_ratchet_frame_statement

/--
info: 'Tacenta.UnitLifecycleDecryptT3.decrypt_refines_ratchet_frame_of_invariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kdf.hkdf_sha256,
 tacenta_session_unit.tacenta_kdf.hmac_sha256,
 tacenta_session_unit.tacenta_kem.CT1_LEN,
 tacenta_session_unit.tacenta_kem.CT2_LEN,
 tacenta_session_unit.tacenta_kem.EK_VECTOR_LEN,
 tacenta_session_unit.tacenta_kem.EncapsState,
 tacenta_session_unit.tacenta_kem.HEADER_LEN,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair,
 tacenta_session_unit.tacenta_kem.encapsulate1,
 tacenta_session_unit.tacenta_kem.encapsulate2,
 tacenta_session_unit.tacenta_kem.validate_ek,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.rand_core_1.error.Error,
 tacenta_session_unit.tacenta_boundary.aead.decrypt,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_boundary.dh.is_prime_order_public,
 tacenta_session_unit.tacenta_boundary.kem.ciphertext_len,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.generate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.header,
 tacenta_session_unit.zeroize.Zeroizing.new,
 tacenta_session_unit.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.Pair.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.TupleABC.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.alloc.vec.Vec.capacity,
 tacenta_session_unit.alloc.vec.Vec.pop,
 tacenta_session_unit.alloc.vec.Vec.truncate,
 tacenta_session_unit.core.num.Usize.div_ceil,
 tacenta_session_unit.core.option.Option.as_mut,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.agree,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.from_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.public_key,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.to_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.from_bytes,
 tacenta_session_unit.zeroize.Zeroize.Blanket.zeroize,
 Tacenta.SessionUnitSpqrT3.chain_label_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.chain_start_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.max_skip_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.max_skip_val._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.max_skipped_store_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.protocol_info_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.receive_refines_continuation._native.native_decide.ax_1_29,
 Tacenta.SessionUnitSpqrT3.root_label_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitTripleT3.combine_info_agrees._native.native_decide.ax_1_1,
 tacenta_session_unit.tacenta_kem.EncapsState.Insts.CoreCloneClone.clone,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 tacenta_session_unit.alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.core.option.Option.Insts.CoreCloneClone.clone,
 tacenta_session_unit.core.option.Option.Insts.CoreCmpPartialEqOption.eq,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes.eq,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleDecryptT3.decrypt_refines_ratchet_frame_of_invariant

/--
info: 'Tacenta.UnitLifecycleDecryptT3.succMessage_not_initial' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleDecryptT3.succMessage_not_initial

/--
info: 'Tacenta.UnitLifecycleDecryptT3.sampleMessage_not_initial' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleDecryptT3.sampleMessage_not_initial

/--
info: 'Tacenta.UnitLifecycleDecryptT3.decrypt_refines_ratchet_frame_at_refusal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kdf.hkdf_sha256,
 tacenta_session_unit.tacenta_kdf.hmac_sha256,
 tacenta_session_unit.tacenta_kem.CT1_LEN,
 tacenta_session_unit.tacenta_kem.CT2_LEN,
 tacenta_session_unit.tacenta_kem.EK_VECTOR_LEN,
 tacenta_session_unit.tacenta_kem.EncapsState,
 tacenta_session_unit.tacenta_kem.HEADER_LEN,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair,
 tacenta_session_unit.tacenta_kem.encapsulate1,
 tacenta_session_unit.tacenta_kem.encapsulate2,
 tacenta_session_unit.tacenta_kem.validate_ek,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.rand_core_1.error.Error,
 tacenta_session_unit.tacenta_boundary.aead.decrypt,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.generate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.header,
 tacenta_session_unit.zeroize.Zeroizing.new,
 tacenta_session_unit.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.Pair.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.TupleABC.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.alloc.vec.Vec.capacity,
 tacenta_session_unit.alloc.vec.Vec.pop,
 tacenta_session_unit.alloc.vec.Vec.truncate,
 tacenta_session_unit.core.num.Usize.div_ceil,
 tacenta_session_unit.core.option.Option.as_mut,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.agree,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.from_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.public_key,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.to_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.from_bytes,
 tacenta_session_unit.zeroize.Zeroize.Blanket.zeroize,
 Tacenta.SessionUnitSpqrT3.chain_label_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.chain_start_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.max_skip_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.max_skip_val._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.max_skipped_store_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.protocol_info_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.receive_refines_continuation._native.native_decide.ax_1_29,
 Tacenta.SessionUnitSpqrT3.root_label_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitTripleT3.combine_info_agrees._native.native_decide.ax_1_1,
 tacenta_session_unit.tacenta_kem.EncapsState.Insts.CoreCloneClone.clone,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 tacenta_session_unit.alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.core.option.Option.Insts.CoreCloneClone.clone,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes.eq,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleDecryptT3.decrypt_refines_ratchet_frame_at_refusal

/--
info: 'Tacenta.UnitLifecycleDecryptT3.refReal_fails_invariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kem.CT1_LEN,
 tacenta_session_unit.tacenta_kem.CT2_LEN,
 tacenta_session_unit.tacenta_kem.EK_VECTOR_LEN,
 tacenta_session_unit.tacenta_kem.EncapsState,
 tacenta_session_unit.tacenta_kem.HEADER_LEN,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair,
 tacenta_session_unit.tacenta_kem.validate_ek,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_boundary.dh.is_prime_order_public,
 tacenta_session_unit.tacenta_boundary.kem.ciphertext_len,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.header,
 tacenta_session_unit.core.num.Usize.div_ceil,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.from_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.public_key,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.to_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.from_bytes,
 tacenta_session_unit.core.option.Option.Insts.CoreCmpPartialEqOption.eq,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes.eq]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleDecryptT3.refReal_fails_invariant

/--
info: 'Tacenta.UnitLifecycleDecryptT3.inv_sessionRefines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kem.EncapsState,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair,
 tacenta_session_unit.tacenta_kem.encapsulate2,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.header,
 tacenta_session_unit.alloc.vec.Vec.truncate,
 tacenta_session_unit.core.num.Usize.div_ceil]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleDecryptT3.inv_sessionRefines

/--
info: 'Tacenta.UnitLifecycleDecryptT3.inv_retryRunBounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kem.EncapsState,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleDecryptT3.inv_retryRunBounds

/--
info: 'Tacenta.UnitLifecycleDecryptT3.inv_run_satisfiable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kem.EncapsState,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair,
 tacenta_session_unit.tacenta_kem.encapsulate2,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.header,
 tacenta_session_unit.alloc.vec.Vec.truncate,
 tacenta_session_unit.core.num.Usize.div_ceil]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleDecryptT3.inv_run_satisfiable

/--
info: 'Tacenta.UnitLifecycleDecryptT3.inv_model_refuses' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kem.EncapsState,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleDecryptT3.inv_model_refuses

/--
info: 'Tacenta.UnitLifecycleDecryptT3.decrypt_refines_ratchet_frame_of_invariant_at_sample' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kdf.hkdf_sha256,
 tacenta_session_unit.tacenta_kdf.hmac_sha256,
 tacenta_session_unit.tacenta_kem.CT1_LEN,
 tacenta_session_unit.tacenta_kem.CT2_LEN,
 tacenta_session_unit.tacenta_kem.EK_VECTOR_LEN,
 tacenta_session_unit.tacenta_kem.EncapsState,
 tacenta_session_unit.tacenta_kem.HEADER_LEN,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair,
 tacenta_session_unit.tacenta_kem.encapsulate1,
 tacenta_session_unit.tacenta_kem.encapsulate2,
 tacenta_session_unit.tacenta_kem.validate_ek,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.rand_core_1.error.Error,
 tacenta_session_unit.tacenta_boundary.aead.decrypt,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_boundary.dh.is_prime_order_public,
 tacenta_session_unit.tacenta_boundary.kem.ciphertext_len,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.generate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.header,
 tacenta_session_unit.zeroize.Zeroizing.new,
 tacenta_session_unit.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.Pair.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.TupleABC.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.alloc.vec.Vec.capacity,
 tacenta_session_unit.alloc.vec.Vec.pop,
 tacenta_session_unit.alloc.vec.Vec.truncate,
 tacenta_session_unit.core.num.Usize.div_ceil,
 tacenta_session_unit.core.option.Option.as_mut,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.agree,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.from_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.public_key,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.to_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.from_bytes,
 tacenta_session_unit.zeroize.Zeroize.Blanket.zeroize,
 Tacenta.SessionUnitSpqrT3.chain_label_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.chain_start_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.max_skip_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.max_skip_val._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.max_skipped_store_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.protocol_info_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.receive_refines_continuation._native.native_decide.ax_1_29,
 Tacenta.SessionUnitSpqrT3.root_label_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitTripleT3.combine_info_agrees._native.native_decide.ax_1_1,
 tacenta_session_unit.tacenta_kem.EncapsState.Insts.CoreCloneClone.clone,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 tacenta_session_unit.alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.core.option.Option.Insts.CoreCloneClone.clone,
 tacenta_session_unit.core.option.Option.Insts.CoreCmpPartialEqOption.eq,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes.eq,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleDecryptT3.decrypt_refines_ratchet_frame_of_invariant_at_sample

/--
info: @Tacenta.UnitLifecycleDecryptT3.decrypt_refines_ratchet_frame : ∀ {R : Type}
  (rngCore : tacenta_session_unit.rand_core_1.RngCore R) (cryptoRng : tacenta_session_unit.rand_core_1.CryptoRng R)
  (trace : R → List Model.Lifecycle.Key) (dh : Tacenta.UnitLifecycleT3.DhView) (view : Model.Lifecycle.CodewordView)
  (oracle : Model.Lifecycle.Oracle),
  Tacenta.UnitLifecycleDecryptRatchetT3.DecryptOracleOf rngCore cryptoRng dh trace oracle →
    Tacenta.UnitLifecycleT3.DhCodecOf dh →
      Tacenta.UnitLifecycleT1.DecryptRatchetContracts rngCore →
        ∀ [Tacenta.SessionUnitT1.DerivedKeysModel],
          Tacenta.UnitLifecycleDecryptRatchetT3.DecryptRatchetAgreements oracle.braidKem →
            ∀ (real : tacenta_session_unit.lifecycle.Session) (model : Model.Lifecycle.Session)
              (message : Aeneas.Std.Slice Aeneas.Std.U8) (rng : R),
              Model.Lifecycle.messageType (Tacenta.UnitLifecycleT3.sliceOf message) ≠
                  some Model.Lifecycle.MessageType.initial →
                Tacenta.UnitLifecycleT3.SessionRefines dh oracle.braidKem real model →
                  Tacenta.UnitLifecycleT1.DecryptRatchetHeadroom real →
                    trace rng = oracle.draws →
                      Tacenta.UnitLifecycleDecryptRatchetT3.DecryptRatchetRun view oracle trace real model message rng →
                        ∃ output,
                          tacenta_session_unit.lifecycle.Session.decrypt rngCore cryptoRng real message rng =
                              Aeneas.Std.Result.ok output ∧
                            Tacenta.UnitLifecycleT3.StepRefines trace dh oracle.braidKem output
                              (Model.Lifecycle.decrypt view oracle model (Tacenta.UnitLifecycleT3.sliceOf message))
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptT3.decrypt_refines_ratchet_frame

/--
info: @Tacenta.UnitLifecycleDecryptT3.decrypt_refines_ratchet_frame_statement : Tacenta.UnitLifecycleDecryptT3.DecryptRefinesRatchetFrameStatement
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptT3.decrypt_refines_ratchet_frame_statement

/--
info: @Tacenta.UnitLifecycleDecryptT3.decrypt_refines_ratchet_frame_of_invariant : ∀ {R : Type}
  (rngCore : tacenta_session_unit.rand_core_1.RngCore R) (cryptoRng : tacenta_session_unit.rand_core_1.CryptoRng R)
  (trace : R → List Model.Lifecycle.Key) (dh : Tacenta.UnitLifecycleT3.DhView) (view : Model.Lifecycle.CodewordView)
  (oracle : Model.Lifecycle.Oracle),
  Tacenta.UnitLifecycleDecryptRatchetT3.DecryptOracleOf rngCore cryptoRng dh trace oracle →
    Tacenta.UnitLifecycleT3.DhCodecOf dh →
      Tacenta.UnitLifecycleT1.DecryptRatchetContracts rngCore →
        ∀ [Tacenta.SessionUnitT1.DerivedKeysModel],
          Tacenta.UnitLifecycleDecryptRatchetT3.DecryptRatchetAgreements oracle.braidKem →
            ∀ (real : tacenta_session_unit.lifecycle.Session) (model : Model.Lifecycle.Session)
              (message : Aeneas.Std.Slice Aeneas.Std.U8) (rng : R),
              Model.Lifecycle.messageType (Tacenta.UnitLifecycleT3.sliceOf message) ≠
                  some Model.Lifecycle.MessageType.initial →
                Tacenta.UnitLifecycleT3.SessionRefines dh oracle.braidKem real model →
                  real.invariant = Aeneas.Std.Result.ok true →
                    trace rng = oracle.draws →
                      Tacenta.UnitLifecycleDecryptRatchetT3.DecryptRatchetRun view oracle trace real model message rng →
                        ∃ output,
                          tacenta_session_unit.lifecycle.Session.decrypt rngCore cryptoRng real message rng =
                              Aeneas.Std.Result.ok output ∧
                            Tacenta.UnitLifecycleT3.StepRefines trace dh oracle.braidKem output
                              (Model.Lifecycle.decrypt view oracle model (Tacenta.UnitLifecycleT3.sliceOf message))
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptT3.decrypt_refines_ratchet_frame_of_invariant

/--
info: Tacenta.UnitLifecycleDecryptT3.succMessage_not_initial : Model.Lifecycle.messageType
    (Tacenta.UnitLifecycleT3.sliceOf Tacenta.UnitLifecycleDecryptRatchetScreen.succMessage) ≠
  some Model.Lifecycle.MessageType.initial
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptT3.succMessage_not_initial

/--
info: Tacenta.UnitLifecycleDecryptT3.sampleMessage_not_initial : Model.Lifecycle.messageType
    (Tacenta.UnitLifecycleT3.sliceOf Tacenta.UnitLifecycleDecryptRatchetScreen.sampleMessage) ≠
  some Model.Lifecycle.MessageType.initial
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptT3.sampleMessage_not_initial

/--
info: Tacenta.UnitLifecycleDecryptT3.decrypt_refines_ratchet_frame_at_refusal : ∀ (dh : Tacenta.UnitLifecycleT3.DhView)
  (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle),
  oracle.draws = Tacenta.UnitLifecycleIntegrationScreen.byteTrace Tacenta.UnitLifecycleDecryptRatchetScreen.sampleRng →
    Tacenta.UnitLifecycleDecryptRatchetT3.DecryptOracleOf Tacenta.UnitLifecycleIntegrationScreen.byteRng
        Tacenta.UnitLifecycleIntegrationScreen.byteCrc dh Tacenta.UnitLifecycleIntegrationScreen.byteTrace oracle →
      Tacenta.UnitLifecycleT3.DhCodecOf dh →
        Tacenta.UnitLifecycleT1.DecryptRatchetContracts Tacenta.UnitLifecycleIntegrationScreen.byteRng →
          ∀ [Tacenta.SessionUnitT1.DerivedKeysModel],
            Tacenta.UnitLifecycleDecryptRatchetT3.DecryptRatchetAgreements oracle.braidKem →
              ∀ (sk : tacenta_session_unit.tacenta_boundary.dh.PrivateKey)
                (pk : tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes),
                ∃ output,
                  tacenta_session_unit.lifecycle.Session.decrypt Tacenta.UnitLifecycleIntegrationScreen.byteRng
                        Tacenta.UnitLifecycleIntegrationScreen.byteCrc
                        (Tacenta.UnitLifecycleDecryptRatchetCompleteScreen.refReal sk pk)
                        Tacenta.UnitLifecycleDecryptRatchetScreen.succMessage
                        Tacenta.UnitLifecycleDecryptRatchetScreen.sampleRng =
                      Aeneas.Std.Result.ok output ∧
                    Tacenta.UnitLifecycleT3.StepRefines Tacenta.UnitLifecycleIntegrationScreen.byteTrace dh
                      oracle.braidKem output
                      (Model.Lifecycle.decrypt view oracle
                        (Tacenta.UnitLifecycleDecryptRatchetScreen.modelOf dh
                          (Tacenta.UnitLifecycleDecryptRatchetCompleteScreen.refReal sk pk))
                        (Tacenta.UnitLifecycleT3.sliceOf Tacenta.UnitLifecycleDecryptRatchetScreen.succMessage))
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptT3.decrypt_refines_ratchet_frame_at_refusal

/--
info: Tacenta.UnitLifecycleDecryptT3.refReal_fails_invariant : Tacenta.UnitLifecycleT1.DhCodecTotal →
  ∀ (sk : tacenta_session_unit.tacenta_boundary.dh.PrivateKey)
    (pk : tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes),
    (Tacenta.UnitLifecycleDecryptRatchetCompleteScreen.refReal sk pk).invariant ≠ Aeneas.Std.Result.ok true
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptT3.refReal_fails_invariant

/--
info: Tacenta.UnitLifecycleDecryptT3.inv_sessionRefines : ∀ (K : Model.Braid.Kem) (dh : Tacenta.UnitLifecycleT3.DhView)
  (k : tacenta_session_unit.tacenta_boundary.dh.PrivateKey)
  (pkb : tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes) (a : Aeneas.Std.Array Aeneas.Std.U8 32#usize)
  (ad : Aeneas.Std.alloc.vec.Vec Aeneas.Std.U8),
  Tacenta.UnitLifecycleT3.SessionRefines dh K (Tacenta.UnitLifecycleDecryptT3.invReal k pkb a ad)
    (Tacenta.UnitLifecycleDecryptRatchetScreen.modelOf dh (Tacenta.UnitLifecycleDecryptT3.invReal k pkb a ad))
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptT3.inv_sessionRefines

/--
info: Tacenta.UnitLifecycleDecryptT3.inv_retryRunBounds : ∀ (k : tacenta_session_unit.tacenta_boundary.dh.PrivateKey)
  (pkb : tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes) (a : Aeneas.Std.Array Aeneas.Std.U8 32#usize)
  (ad : Aeneas.Std.alloc.vec.Vec Aeneas.Std.U8) (dh : Tacenta.UnitLifecycleT3.DhView)
  (output : Option Model.SparseRatchet.Output),
  output = none →
    Tacenta.UnitLifecycleDecryptRatchetT3.RetryRunBounds
      (Tacenta.UnitLifecycleDecryptRatchetScreen.modelOf dh (Tacenta.UnitLifecycleDecryptT3.invReal k pkb a ad)).triple
      (Model.Lifecycle.tripleHeaderOf Tacenta.UnitLifecycleDecryptRatchetScreen.sampleComposite) output
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptT3.inv_retryRunBounds

/--
info: Tacenta.UnitLifecycleDecryptT3.inv_run_satisfiable : ∀ (K : Model.Braid.Kem) (dh : Tacenta.UnitLifecycleT3.DhView)
  (k : tacenta_session_unit.tacenta_boundary.dh.PrivateKey)
  (pkb : tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes) (a : Aeneas.Std.Array Aeneas.Std.U8 32#usize)
  (ad : Aeneas.Std.alloc.vec.Vec Aeneas.Std.U8),
  Tacenta.UnitLifecycleT3.SessionRefines dh K (Tacenta.UnitLifecycleDecryptT3.invReal k pkb a ad)
      (Tacenta.UnitLifecycleDecryptRatchetScreen.modelOf dh (Tacenta.UnitLifecycleDecryptT3.invReal k pkb a ad)) ∧
    ∀ (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle),
      oracle.braidKem = K →
        oracle.draws =
            Tacenta.UnitLifecycleIntegrationScreen.byteTrace Tacenta.UnitLifecycleDecryptRatchetScreen.sampleRng →
          Tacenta.UnitLifecycleIntegrationScreen.byteTrace Tacenta.UnitLifecycleDecryptRatchetScreen.sampleRng =
              oracle.draws ∧
            Tacenta.UnitLifecycleDecryptRatchetT3.DecryptRatchetRun view oracle
              Tacenta.UnitLifecycleIntegrationScreen.byteTrace (Tacenta.UnitLifecycleDecryptT3.invReal k pkb a ad)
              (Tacenta.UnitLifecycleDecryptRatchetScreen.modelOf dh (Tacenta.UnitLifecycleDecryptT3.invReal k pkb a ad))
              Tacenta.UnitLifecycleDecryptRatchetScreen.sampleMessage
              Tacenta.UnitLifecycleDecryptRatchetScreen.sampleRng
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptT3.inv_run_satisfiable

/--
info: Tacenta.UnitLifecycleDecryptT3.inv_model_refuses : ∀ (dh : Tacenta.UnitLifecycleT3.DhView)
  (view : Model.Lifecycle.CodewordView) (k : tacenta_session_unit.tacenta_boundary.dh.PrivateKey)
  (pkb : tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes) (a : Aeneas.Std.Array Aeneas.Std.U8 32#usize)
  (ad : Aeneas.Std.alloc.vec.Vec Aeneas.Std.U8),
  (Model.Lifecycle.decrypt view
        (Tacenta.UnitLifecycleDecryptRatchetScreen.oracleDecrypt
          (Tacenta.UnitLifecycleIntegrationScreen.byteTrace Tacenta.UnitLifecycleDecryptRatchetScreen.sampleRng))
        (Tacenta.UnitLifecycleDecryptRatchetScreen.modelOf dh (Tacenta.UnitLifecycleDecryptT3.invReal k pkb a ad))
        (Tacenta.UnitLifecycleT3.sliceOf Tacenta.UnitLifecycleDecryptRatchetScreen.sampleMessage)).result =
    Except.error (Model.Lifecycle.Refusal.handshake Model.Lifecycle.HandshakeRefusal.nonContributoryAgreement)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptT3.inv_model_refuses

/--
info: Tacenta.UnitLifecycleDecryptT3.decrypt_refines_ratchet_frame_of_invariant_at_sample : ∀
  (dh : Tacenta.UnitLifecycleT3.DhView) (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle),
  oracle.draws = Tacenta.UnitLifecycleIntegrationScreen.byteTrace Tacenta.UnitLifecycleDecryptRatchetScreen.sampleRng →
    Tacenta.UnitLifecycleDecryptRatchetT3.DecryptOracleOf Tacenta.UnitLifecycleIntegrationScreen.byteRng
        Tacenta.UnitLifecycleIntegrationScreen.byteCrc dh Tacenta.UnitLifecycleIntegrationScreen.byteTrace oracle →
      Tacenta.UnitLifecycleT3.DhCodecOf dh →
        Tacenta.UnitLifecycleT1.DecryptRatchetContracts Tacenta.UnitLifecycleIntegrationScreen.byteRng →
          ∀ [Tacenta.SessionUnitT1.DerivedKeysModel],
            Tacenta.UnitLifecycleDecryptRatchetT3.DecryptRatchetAgreements oracle.braidKem →
              ∀ (k : tacenta_session_unit.tacenta_boundary.dh.PrivateKey)
                (pkb : tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes)
                (a : Aeneas.Std.Array Aeneas.Std.U8 32#usize),
                k.public_key = Aeneas.Std.Result.ok pkb →
                  pkb.as_bytes = Aeneas.Std.Result.ok a →
                    Tacenta.SessionUnitT1.canonicalX25519 a = true →
                      tacenta_session_unit.tacenta_boundary.dh.is_prime_order_public pkb = Aeneas.Std.Result.ok true →
                        Tacenta.UnitHeadroomInvariant.OptionEqU64Shape
                            @tacenta_session_unit.core.option.Option.Insts.CoreCmpPartialEqOption.eq →
                          ∀ (ad : Aeneas.Std.alloc.vec.Vec Aeneas.Std.U8),
                            tacenta_session_unit.lifecycle.identity_ad pkb pkb = Aeneas.Std.Result.ok ad →
                              (Tacenta.UnitLifecycleDecryptT3.invReal k pkb a ad).invariant =
                                  Aeneas.Std.Result.ok true ∧
                                ∃ output,
                                  tacenta_session_unit.lifecycle.Session.decrypt
                                        Tacenta.UnitLifecycleIntegrationScreen.byteRng
                                        Tacenta.UnitLifecycleIntegrationScreen.byteCrc
                                        (Tacenta.UnitLifecycleDecryptT3.invReal k pkb a ad)
                                        Tacenta.UnitLifecycleDecryptRatchetScreen.sampleMessage
                                        Tacenta.UnitLifecycleDecryptRatchetScreen.sampleRng =
                                      Aeneas.Std.Result.ok output ∧
                                    Tacenta.UnitLifecycleT3.StepRefines Tacenta.UnitLifecycleIntegrationScreen.byteTrace
                                      dh oracle.braidKem output
                                      (Model.Lifecycle.decrypt view oracle
                                        (Tacenta.UnitLifecycleDecryptRatchetScreen.modelOf dh
                                          (Tacenta.UnitLifecycleDecryptT3.invReal k pkb a ad))
                                        (Tacenta.UnitLifecycleT3.sliceOf
                                          Tacenta.UnitLifecycleDecryptRatchetScreen.sampleMessage))
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptT3.decrypt_refines_ratchet_frame_of_invariant_at_sample

/--
info: def Tacenta.UnitLifecycleDecryptT3.DecryptRefinesRatchetFrameStatement : Prop :=
∀ {R : Type} (rngCore : tacenta_session_unit.rand_core_1.RngCore R)
  (cryptoRng : tacenta_session_unit.rand_core_1.CryptoRng R) (trace : R → List Model.Lifecycle.Key)
  (dh : Tacenta.UnitLifecycleT3.DhView) (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle),
  Tacenta.UnitLifecycleDecryptRatchetT3.DecryptOracleOf rngCore cryptoRng dh trace oracle →
    Tacenta.UnitLifecycleT3.DhCodecOf dh →
      Tacenta.UnitLifecycleT1.DecryptRatchetContracts rngCore →
        ∀ [Tacenta.SessionUnitT1.DerivedKeysModel],
          Tacenta.UnitLifecycleDecryptRatchetT3.DecryptRatchetAgreements oracle.braidKem →
            ∀ (real : tacenta_session_unit.lifecycle.Session) (model : Model.Lifecycle.Session)
              (message : Aeneas.Std.Slice Aeneas.Std.U8) (rng : R),
              Model.Lifecycle.messageType (Tacenta.UnitLifecycleT3.sliceOf message) ≠
                  some Model.Lifecycle.MessageType.initial →
                Tacenta.UnitLifecycleT3.SessionRefines dh oracle.braidKem real model →
                  Tacenta.UnitLifecycleT1.DecryptRatchetHeadroom real →
                    trace rng = oracle.draws →
                      Tacenta.UnitLifecycleDecryptRatchetT3.DecryptRatchetRun view oracle trace real model message rng →
                        ∃ output,
                          tacenta_session_unit.lifecycle.Session.decrypt rngCore cryptoRng real message rng =
                              Aeneas.Std.Result.ok output ∧
                            Tacenta.UnitLifecycleT3.StepRefines trace dh oracle.braidKem output
                              (Model.Lifecycle.decrypt view oracle model (Tacenta.UnitLifecycleT3.sliceOf message))
-/
#guard_msgs in
#print Tacenta.UnitLifecycleDecryptT3.DecryptRefinesRatchetFrameStatement

/--
info: def Tacenta.UnitLifecycleDecryptT3.invReal : tacenta_session_unit.tacenta_boundary.dh.PrivateKey →
  tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes →
    Aeneas.Std.Array Aeneas.Std.U8 32#usize →
      Aeneas.Std.alloc.vec.Vec Aeneas.Std.U8 → tacenta_session_unit.lifecycle.Session :=
fun k pkb a ad => Tacenta.UnitHeadroomSatisfiable.sessionOf k pkb pkb ad a none
-/
#guard_msgs in
#print Tacenta.UnitLifecycleDecryptT3.invReal
