import Translation.UnitLifecycleDecryptRatchetCompleteT3
import Translation.UnitLifecycleDecryptRatchetScreen

/-!
# Screening the refusal refinement and the complete `decrypt_ratchet` theorem

`UnitLifecycleTripleRefusalT3.triple_receive_refusal_refines` takes the hypotheses of the existing
Triple receive refinement (`NumericWitnessSession.sat_SessionUnitTripleT3_receive_refines_discharged`
meets them at one state), and `decrypt_ratchet_refines_complete` takes the hypotheses of
`decrypt_ratchet_refines` (`UnitLifecycleDecryptRatchetScreen` meets them at two runs).  Neither adds
a hypothesis.  What this module adds is that both theorems speak on the path that was open, in two
parts.

## A. One Triple receive that refuses for a reason other than a full store

`ref_triple_refuses`: at a Triple state whose classical half receives on a chain already at message
number 1, a header for message number 0 on that chain meets every premise of the refusal theorem,
the model's detailed receive refuses with the classical `outOfOrder`, which is not a full store, and,
under the boundary the theorem takes, the generated receive refuses too, with a reason whose public
mapping is that refusal.  The generated receive cannot succeed there, because the success theorem
would then give a model success.  So the refusal theorem's premise (a generated refusal) is met at a
state that meets its hypotheses.

## B. A `decrypt_ratchet` run on that path

`hypotheses_meet_open_path`: with the oracle of `UnitLifecycleDecryptRatchetScreen`'s part B, every
per-run hypothesis holds at a run over that Triple state, and the model's step there is the Triple
refusal `outOfOrder`, which is not a full store, returned by the first attempt.
`decrypt_ratchet_refines_complete_at_refusal` is the complete theorem at that run.  Under the boundary
records, the generated output there is the Triple refusal `Classical OutOfOrder`, of which
`TripleRefusalOpen` holds (`generated_reaches_open_path`): the path `decrypt_ratchet_refines` left
open.  No run here reaches a sparse refusal or a refusal returned by a retry inside the eviction loop,
and unlike the first and third runs of `UnitLifecycleDecryptRatchetScreen` this run is not composed
with the boundary model inside Lean.

No proof here chooses a width of `usize`; the facts used hold at both.  The oracle clauses hold of
part B's interpretation, not at the real constants, as in the earlier screen.
-/

open Aeneas Aeneas.Std Result
open tacenta_session_unit
open Tacenta.UnitLifecycleT3
open Tacenta.UnitLifecycleDecryptRatchetT3
open Tacenta.UnitLifecycleDecryptRatchetScreen

namespace Tacenta.UnitLifecycleDecryptRatchetCompleteScreen

/-! ## A. One Triple receive -/

/-- `succTriple` with the classical receiving chain one message ahead. -/
def refTriple : tacenta_triple.State :=
  { succTriple with classical := { succTriple.classical with nr := 1#u32 } }

/-- A header for message number 0 on the classical chain `ones32`, sparse epoch 0, number 1. -/
def refHeader : tacenta_triple.Header :=
  { dr := { dh := ones32, pn := 0#u32, n := 0#u32 }, epoch := 0#u64, pq_n := 1#u64 }

def refModelHeader : Model.State.Header :=
  { dh := Tacenta.SessionUnitTripleT3.keyOf ones32, pn := 0, n := 0 }

def refModel : Model.Triple.State :=
  { classical := Tacenta.SessionUnitTripleT3.ratchetAbs refTriple.classical
    postQuantum := Tacenta.SessionUnitTripleT3.spqrAbs refTriple.post_quantum }

/-- The model refuses that receive with the classical `outOfOrder`, a refusal that is not a full
store. -/
theorem ref_model_triple_refuses :
    Model.Triple.receiveDetailed refModel
        { dr := refModelHeader, epoch := refHeader.epoch.val, pqN := refHeader.pq_n.val }
        (Tacenta.SessionUnitTripleT3.keyOf zeros32) (Tacenta.SessionUnitTripleT3.keyOf zeros32)
        (Tacenta.SessionUnitTripleT3.keyOf zeros32) none =
      .error (.classical .outOfOrder) ∧
    Model.Lifecycle.fullStore (.classical .outOfOrder) = none := by
  refine ⟨?_, rfl⟩
  simp [Model.Triple.receiveDetailed, Model.Ratchet.receiveDetailed, refModel, refModelHeader,
    refTriple, succTriple, Tacenta.SessionUnitTripleT3.ratchetAbs,
    Tacenta.UnitHeadroomSatisfiable.vecOf, Tacenta.SessionUnitT3.keyOf,
    Tacenta.SessionUnitTripleT3.keyOf, ones32, zeros32, Array.repeat, Model.Ratchet.trySkipped,
    Model.Ratchet.skipMessageKeysDetailed, Model.State.skipMessageKeys, Tacenta.SessionUnitT3.u8,
    Tacenta.SessionUnitTripleT3.u8]

/-- Every premise of the refusal theorem holds at that state, header and output. -/
theorem ref_premises :
    Tacenta.SessionUnitTripleT3.StateRefines Tacenta.SessionUnitTripleT3.ratchetAbs
      Tacenta.SessionUnitTripleT3.spqrAbs refTriple refModel ∧
    Tacenta.SessionUnitTripleT3.RatchetHeaderR refHeader.dr refModelHeader ∧
    (refModel.classical.skipped.filter
      (fun x => x.1 == refModelHeader.dh && x.2.1 == refModelHeader.n)).length ≤ 1 ∧
    max refModel.classical.skipped.length Model.State.maxSkippedStore + Model.State.maxSkip ≤
      Usize.max ∧
    refModel.classical.events + 1 < Std.U32.max ∧
    refModel.postQuantum.epoch + 1 < Std.U64.max ∧
    refModel.postQuantum.chains.length + 2 < Usize.max ∧
    (∀ p ∈ refModel.postQuantum.chains, p.1 + Model.SparseRatchet.epochsKept ≤ Std.U64.max) ∧
    (∀ sk ∈ refModel.postQuantum.skipped, sk.1 + Model.SparseRatchet.epochsKept ≤ Std.U64.max) ∧
    (∀ o : tacenta_spqr.Output, (none : Option tacenta_spqr.Output) = some o →
      o.key_epoch.val + Model.SparseRatchet.epochsKept ≤ Std.U64.max) ∧
    refModel.postQuantum.skipped.length + Model.SparseRatchet.maxSkip ≤ Usize.max ∧
    (refModel.postQuantum.skipped.filter
      (fun x => x.1 == refHeader.epoch.val && x.2.1 == refHeader.pq_n.val)).length ≤ 1 ∧
    (∀ p ∈ refModel.postQuantum.chains, ∀ ch : Model.SparseRatchet.Chain,
      (p.2.send = some ch ∨ p.2.receive = some ch) → ch.n < Std.U64.max) := by
  have hu := Tacenta.UnitHeadroomSatisfiable.usize_max_ge
  refine ⟨⟨rfl, rfl⟩, ⟨rfl, rfl, rfl⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [refModel, refTriple, succTriple, refHeader, refModelHeader,
      Tacenta.UnitHeadroomSatisfiable.vecOf, Tacenta.SessionUnitTripleT3.ratchetAbs,
      Tacenta.SessionUnitTripleT3.spqrAbs, Model.State.maxSkippedStore, Model.State.maxSkip,
      Model.SparseRatchet.maxSkip, Model.SparseRatchet.epochsKept, U32.max_eq, U64.max_eq,
      Tacenta.SessionUnitSpqrT3.chainsEntryOf, Tacenta.SessionUnitSpqrT3.chainsOf,
      Tacenta.SessionUnitSpqrT3.chainOf] <;>
    omega

/-- **The generated Triple receive refuses at that state, under the boundary of the refusal
theorem, and its reason maps to the model's classical `outOfOrder`.**  The success theorem rules out
a generated success (the model refuses), and the refusal theorem names the reason. -/
theorem ref_triple_refuses
    (hmac : Tacenta.SessionUnitT3.HmacAgrees) (hkdf : Tacenta.SessionUnitT3.HkdfAgrees)
    (hzr : Tacenta.SessionUnitT3.ZeroizingRoundTrips)
    (hvr : Tacenta.SessionUnitT1.RemoveSkippedAtTotal)
    [Tacenta.SessionUnitT1.DerivedKeysModel]
    (hz96 : Tacenta.SessionUnitSpqrT3.ZeroizingRoundTrips96)
    (hz64 : Tacenta.SessionUnitSpqrT3.ZeroizingRoundTrips64)
    (hret : Tacenta.SessionUnitSpqrT3.VecRetainAgrees)
    (hret_total : Tacenta.SessionUnitSpqrT1.VecRetainTotal)
    (hrm : Tacenta.SessionUnitSpqrT3.RemoveSkippedAtAgrees)
    (hzs : Tacenta.SessionUnitSpqrT1.ZeroizeTotal)
    (hopt : Tacenta.SessionUnitSpqrT1.OptionCloneTotal) :
    ∃ reason,
      tacenta_triple.State.receive refTriple refHeader zeros32 zeros32 zeros32 none =
        ok (.Err reason) ∧
      tripleReceiveRefusalOfReal reason = some (.classical .outOfOrder) := by
  obtain ⟨hst, hhd, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := ref_premises
  obtain ⟨hmodel, -⟩ := ref_model_triple_refuses
  obtain ⟨r, hr, hrefusal⟩ := Std.WP.spec_imp_exists
    (Tacenta.UnitLifecycleTripleRefusalT3.triple_receive_refusal_refines hmac hkdf hzr hvr hz96
      hz64 hret hret_total hrm hzs hopt refTriple refModel hst refHeader refModelHeader hhd zeros32
      zeros32 zeros32 none h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11)
  obtain ⟨r', hr', hsuccess⟩ := Std.WP.spec_imp_exists
    (Tacenta.SessionUnitTripleT3.receive_refines_discharged hmac hkdf hzr hvr hz96 hz64 hret
      hret_total hrm hzs hopt hst refHeader refModelHeader hhd zeros32 zeros32 zeros32 none
      h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11)
  rw [hr] at hr'
  cases hr'
  cases r with
  | Ok value =>
      obtain ⟨m', k, hrecv, -, -⟩ := hsuccess value.1 value.2 rfl
      have hdet := (Model.Triple.receiveDetailed_ok_iff _ _ _ _ _ _ _).mpr hrecv
      simp only [Option.map_none] at hdet
      rw [hmodel] at hdet
      cases hdet
  | Err reason =>
      obtain ⟨mr, hmap, hdet⟩ := hrefusal reason rfl
      simp only [Option.map_none] at hdet
      rw [hmodel] at hdet
      cases hdet
      exact ⟨reason, hr, hmap⟩

/-! ## B. A `decrypt_ratchet` run on the path that was open -/

/-- `succReal` with the Triple state of part A. -/
def refReal (sk : tacenta_boundary.dh.PrivateKey) (pk : tacenta_boundary.dh.PublicKeyBytes) :
    lifecycle.Session :=
  { sampleReal sk pk with triple := refTriple }

theorem ref_headroom (sk : tacenta_boundary.dh.PrivateKey)
    (pk : tacenta_boundary.dh.PublicKeyBytes) :
    Tacenta.UnitLifecycleT1.DecryptRatchetHeadroom (refReal sk pk) := by
  have h4 := Tacenta.UnitHeadroomSatisfiable.usize_max_ge
  refine ⟨?_, Tacenta.UnitHeadroomSatisfiable.freshBraid_bounds.1,
    Tacenta.UnitHeadroomSatisfiable.freshBraid_bounds.2,
    Tacenta.UnitHeadroomSatisfiable.freshBraid_decoder_sized, ?_⟩
  · unfold Tacenta.UnitLifecycleT1.ReceiveHeadroom
    simp [refReal, refTriple, succTriple, Tacenta.UnitHeadroomSatisfiable.vecOf,
      tacenta_ratchet.MAX_SKIPPED_STORE, tacenta_ratchet.MAX_SKIP, tacenta_spqr.MAX_SKIP]
    omega
  · simp [refReal, sampleReal, Tacenta.UnitHeadroomSatisfiable.sessionOf,
      Tacenta.UnitHeadroomSatisfiable.vecOf]
    omega

/-- **The run meets every per-run hypothesis**, with the message of `succ_run_satisfiable` (message
number 0 on the chain `ones32`). -/
theorem ref_run_satisfiable (K : Model.Braid.Kem) (dh : DhView)
    (sk : tacenta_boundary.dh.PrivateKey) (pk : tacenta_boundary.dh.PublicKeyBytes) :
    SessionRefines dh K (refReal sk pk) (modelOf dh (refReal sk pk)) ∧
    Tacenta.UnitLifecycleT1.DecryptRatchetHeadroom (refReal sk pk) ∧
    ∀ (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle),
      oracle.braidKem = K →
      oracle.draws = Tacenta.UnitLifecycleIntegrationScreen.byteTrace sampleRng →
      Tacenta.UnitLifecycleIntegrationScreen.byteTrace sampleRng = oracle.draws ∧
      DecryptRatchetRun view oracle Tacenta.UnitLifecycleIntegrationScreen.byteTrace
        (refReal sk pk) (modelOf dh (refReal sk pk)) succMessage sampleRng := by
  refine ⟨⟨⟨rfl, rfl⟩, (Tacenta.UnitSatisfiabilityBraidStates.good_keysUnsampled (K := K)).1,
      rfl, rfl, rfl, rfl, rfl, rfl⟩, ref_headroom sk pk, ?_⟩
  intro view oracle hK hdraws
  refine ⟨hdraws.symm, ?_⟩
  refine
    { chunk := ?_
      honest := ?_
      braidEpoch := ?_
      draw := ⟨_, [], sample_trace⟩
      retry := ?_ }
  · intro realComposite modelComposite ciphertext hdecode hcomposite
    rw [succ_decode_model] at hdecode
    have hmc : succComposite = modelComposite := (Prod.mk.inj (Except.ok.inj hdecode)).1
    subst hmc
    have hchunk := hcomposite.agChunk
    unfold IncomingChunkRefines
    cases hr : realComposite.ag_chunk with
    | none => simp [succComposite]
    | some c => simp [hr, succComposite] at hchunk
  · intro modelComposite ciphertext hdecode
    rw [succ_decode_model] at hdecode
    have hmc : succComposite = modelComposite := (Prod.mk.inj (Except.ok.inj hdecode)).1
    subst hmc
    intro mc hmc
    simp [Model.Lifecycle.braidMessageOf, succComposite] at hmc
  · simp only [refReal, sampleReal, Tacenta.UnitHeadroomSatisfiable.sessionOf,
      Tacenta.UnitHeadroomSatisfiable.freshBraid, Tacenta.SessionUnitBraidT1.State.epoch_val]
    scalar_tac
  · intro modelComposite ciphertext hdecode
    rw [succ_decode_model] at hdecode
    have hmc : succComposite = modelComposite := (Prod.mk.inj (Except.ok.inj hdecode)).1
    subst hmc
    have hout : Model.Lifecycle.sparseOutputOf
        (Model.Braid.receive oracle.braidKem (modelOf dh (refReal sk pk)).braid
          (Model.Lifecycle.braidMessageOf view (modelOf dh (refReal sk pk)).braid
            succComposite)).2.1 = none := by
      simp [modelOf, Model.Braid.receive, Model.Lifecycle.sparseOutputOf]
    rw [hout]
    have hu := Tacenta.UnitHeadroomSatisfiable.usize_max_ge
    constructor <;>
      simp [modelOf, refReal, refTriple, succTriple, Tacenta.UnitHeadroomSatisfiable.vecOf,
        Tacenta.SessionUnitTripleT3.ratchetAbs, Tacenta.SessionUnitTripleT3.spqrAbs,
        Model.State.maxSkippedStore, Model.SparseRatchet.maxSkippedStore,
        Model.SparseRatchet.epochsKept, U32.max_eq, U64.max_eq, cMax_usize,
        Tacenta.SessionUnitSpqrT3.chainsEntryOf, Tacenta.SessionUnitSpqrT3.chainsOf,
        Tacenta.SessionUnitSpqrT3.chainOf]
    all_goals omega

/-- With part B's oracle the model's step at that run returns the Triple refusal `outOfOrder`. -/
theorem ref_model_refuses (dh : DhView) (view : Model.Lifecycle.CodewordView)
    (sk : tacenta_boundary.dh.PrivateKey) (pk : tacenta_boundary.dh.PublicKeyBytes) :
    (Model.Lifecycle.decryptRatchet view
      (oracleDecrypt (Tacenta.UnitLifecycleIntegrationScreen.byteTrace sampleRng))
      (modelOf dh (refReal sk pk)) (sliceOf succMessage)).result =
      .error (Model.Lifecycle.tripleReceiveRefusalOf (.classical .outOfOrder)) := by
  simp [Model.Lifecycle.decryptRatchet, Model.Lifecycle.agreementFailed, modelOf, refReal,
    sampleReal, Tacenta.UnitHeadroomSatisfiable.sessionOf, succ_decode_model, oracleDecrypt,
    Model.Lifecycle.random32, Model.Lifecycle.takeDraw, sample_trace,
    Model.Lifecycle.receiveWithEviction,
    Model.Lifecycle.fullStore, Model.Triple.receiveDetailed, Model.Ratchet.receiveDetailed,
    refTriple, succTriple, succComposite, Model.Lifecycle.tripleHeaderOf,
    Tacenta.SessionUnitTripleT3.ratchetAbs, Tacenta.SessionUnitTripleT3.spqrAbs,
    Tacenta.UnitHeadroomSatisfiable.vecOf, Tacenta.SessionUnitT3.keyOf, ones32, zeros32,
    Array.repeat, Model.Ratchet.trySkipped, Model.Ratchet.skipMessageKeysDetailed,
    Model.State.skipMessageKeys, Tacenta.SessionUnitT3.u8, arrayOf, Tacenta.SessionUnitBraidT3.u8]

/-- **The per-run hypotheses hold at a run whose model step is a Triple refusal that is not a full
store**, with part B's oracle, at both platform widths. -/
theorem hypotheses_meet_open_path (dh : DhView) (view : Model.Lifecycle.CodewordView)
    (sk : tacenta_boundary.dh.PrivateKey) (pk : tacenta_boundary.dh.PublicKeyBytes) :
    let oracle := oracleDecrypt (Tacenta.UnitLifecycleIntegrationScreen.byteTrace sampleRng)
    SessionRefines dh oracle.braidKem (refReal sk pk) (modelOf dh (refReal sk pk)) ∧
    Tacenta.UnitLifecycleT1.DecryptRatchetHeadroom (refReal sk pk) ∧
    DecryptRatchetRun view oracle Tacenta.UnitLifecycleIntegrationScreen.byteTrace
      (refReal sk pk) (modelOf dh (refReal sk pk)) succMessage sampleRng ∧
    (Model.Lifecycle.decryptRatchet view oracle (modelOf dh (refReal sk pk))
      (sliceOf succMessage)).result =
      .error (Model.Lifecycle.tripleReceiveRefusalOf (.classical .outOfOrder)) ∧
    Model.Lifecycle.fullStore (.classical .outOfOrder) = none := by
  intro oracle
  obtain ⟨hrel, hroom, hrun⟩ := ref_run_satisfiable oracle.braidKem dh sk pk
  exact ⟨hrel, hroom, (hrun view oracle rfl rfl).2, ref_model_refuses dh view sk pk, rfl⟩

/-- The complete theorem at that run: every per-run hypothesis is discharged by the witnesses
above, and only the boundary records remain, as arguments. -/
theorem decrypt_ratchet_refines_complete_at_refusal (dh : DhView)
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
      lifecycle.Session.decrypt_ratchet Tacenta.UnitLifecycleIntegrationScreen.byteRng
        Tacenta.UnitLifecycleIntegrationScreen.byteCrc (refReal sk pk) succMessage sampleRng =
          ok output ∧
      StepRefines Tacenta.UnitLifecycleIntegrationScreen.byteTrace dh oracle.braidKem output
        (Model.Lifecycle.decryptRatchet view oracle (modelOf dh (refReal sk pk))
          (sliceOf succMessage)) := by
  obtain ⟨hrel, hroom, hrun⟩ := ref_run_satisfiable oracle.braidKem dh sk pk
  obtain ⟨htrace, run⟩ := hrun view oracle rfl hdraws
  exact Tacenta.UnitLifecycleDecryptRatchetCompleteT3.decrypt_ratchet_refines_complete _ _ _ dh
    view oracle oracleOf codec contracts agreements (refReal sk pk) (modelOf dh (refReal sk pk))
    succMessage sampleRng hrel hroom htrace run

/-! The same complete refusal, with the agreement record constructed from the joint boundary
records rather than supplied as an opaque per-run argument.  The real law and primitive records
remain explicit: this theorem removes only the duplicate agreement packaging boundary. -/

open Tacenta.UnitSatisfiabilityJoint Tacenta.UnitSatisfiabilityBraidAgreements in
theorem decrypt_ratchet_refines_complete_from_shapes_at_refusal
    (dh : DhView) (view : Model.Lifecycle.CodewordView)
    (hA : AllT1Shapes Interp.real) (hL : StdLaws Interp.real)
    (hTP : TruncatePrefixShape Interp.real)
    (hD : ZeroizingModelShape Interp.real DerivedZ)
    (hT : T3Agreements Interp.real
      (oracleDecrypt (Tacenta.UnitLifecycleIntegrationScreen.byteTrace sampleRng)).braidKem)
    (hZ : ZeroizeRoundTripShapes Interp.real)
    (hC : DhCodecOfShape Interp.real ⟨dh.privateKey, dh.publicKey⟩)
    (hO : DecryptOracleShape Interp.real ⟨dh.privateKey, dh.publicKey⟩
      Tacenta.UnitLifecycleIntegrationScreen.byteRng Tacenta.UnitLifecycleIntegrationScreen.byteCrc
      Tacenta.UnitLifecycleIntegrationScreen.byteTrace
      (oracleDecrypt (Tacenta.UnitLifecycleIntegrationScreen.byteTrace sampleRng)))
    (sk : tacenta_boundary.dh.PrivateKey) (pk : tacenta_boundary.dh.PublicKeyBytes) :
    ∃ output,
      lifecycle.Session.decrypt_ratchet Tacenta.UnitLifecycleIntegrationScreen.byteRng
        Tacenta.UnitLifecycleIntegrationScreen.byteCrc (refReal sk pk) succMessage sampleRng =
          ok output ∧
      StepRefines Tacenta.UnitLifecycleIntegrationScreen.byteTrace dh
        (oracleDecrypt (Tacenta.UnitLifecycleIntegrationScreen.byteTrace sampleRng)).braidKem output
        (Model.Lifecycle.decryptRatchet view
          (oracleDecrypt (Tacenta.UnitLifecycleIntegrationScreen.byteTrace sampleRng))
          (modelOf dh (refReal sk pk)) (sliceOf succMessage)) := by
  have hb := decrypt_shapes_are_predicates
  let oracle := oracleDecrypt (Tacenta.UnitLifecycleIntegrationScreen.byteTrace sampleRng)
  have oracleOf := (hb.2.1 Tacenta.UnitLifecycleIntegrationScreen.byteRng
    Tacenta.UnitLifecycleIntegrationScreen.byteCrc dh
    Tacenta.UnitLifecycleIntegrationScreen.byteTrace oracle).2 hO
  have codec := (hb.1 dh).2 hC
  have hz := hb.2.2.2 hZ
  have r32 : Tacenta.UnitLifecycleT1.Random32Total Tacenta.UnitLifecycleIntegrationScreen.byteRng :=
    fun _ _ _ => ⟨_, rfl⟩
  have ax : DecryptAxiom Interp.real Tacenta.UnitLifecycleIntegrationScreen.byteRng :=
    ⟨hA.dhCodec, hA.dhAgree, hA.aeadOpen, r32,
      ⟨hA.ct1Len, hA.ct2Len, hA.headerLen, hA.ekVectorLen, hA.keyPairEkVector,
        hA.keyPairDecapsulate, hA.hkdf, hA.hmac, hA.validateEk, hA.encapsulate2, hA.keyPairClone,
        hA.encapsStateClone, hA.optionClone, hA.zeroizingArray, hA.arrayZeroize, hA.rangeFullIndex⟩,
      ⟨hA.hmac, hA.hkdf, hA.zeroizingTotal, hA.spqrZeroize, hA.vecRetainAxiom, hA.optionClone,
        trivial⟩,
      hA.messageKeyMaterial⟩
  have contracts := Tacenta.UnitSatisfiabilityRecords.decrypt_contracts_of_axiom_base
    Tacenta.UnitLifecycleIntegrationScreen.byteRng ax hL
  have er : Tacenta.SessionUnitBraidT3.ErasureAgrees :=
    Tacenta.UnitErasureRs.Glue.erasureAgrees hA.divCeilValue hTP
  obtain ⟨vr, rm⟩ := Tacenta.SessionUnitSatisfiabilitySpqrLaws.session_sparse_agreements_of_shapes
    hL hA.vecRetainAxiom hA.spqrZeroize
  letI : Tacenta.SessionUnitT1.DerivedKeysModel := hD.toDerived
  have agreements : DecryptRatchetAgreements oracle.braidKem :=
    ⟨hT.hmac, hT.hkdf, hz.1, hz.2.1, hz.2.2.1, hz.2.2.2.1, vr, rm, hT.kemAgrees, er, hT.kemLen,
      hT.validateEk, hT.kemClone, hz.2.2.2.2⟩
  exact decrypt_ratchet_refines_complete_at_refusal dh view oracle rfl oracleOf codec contracts
    agreements sk pk

/-- **The generated output at the run is on the path the first form left open**: under the boundary
records, `decrypt_ratchet` returns the Triple refusal `Classical OutOfOrder`, which is not a full
store, so `TripleRefusalOpen` holds of it.  The complete theorem relates it to the model's refusal
there; this is the generated side of the run, conditional on those records, and says nothing about
the real primitives. -/
theorem generated_reaches_open_path (dh : DhView) (view : Model.Lifecycle.CodewordView)
    (oracleOf : DecryptOracleOf Tacenta.UnitLifecycleIntegrationScreen.byteRng
      Tacenta.UnitLifecycleIntegrationScreen.byteCrc dh Tacenta.UnitLifecycleIntegrationScreen.byteTrace
      (oracleDecrypt (Tacenta.UnitLifecycleIntegrationScreen.byteTrace sampleRng)))
    (codec : DhCodecOf dh)
    (contracts : Tacenta.UnitLifecycleT1.DecryptRatchetContracts
      Tacenta.UnitLifecycleIntegrationScreen.byteRng)
    [Tacenta.SessionUnitT1.DerivedKeysModel]
    (agreements : DecryptRatchetAgreements
      (oracleDecrypt (Tacenta.UnitLifecycleIntegrationScreen.byteTrace sampleRng)).braidKem)
    (sk : tacenta_boundary.dh.PrivateKey) (pk : tacenta_boundary.dh.PublicKeyBytes) :
    ∃ output,
      lifecycle.Session.decrypt_ratchet Tacenta.UnitLifecycleIntegrationScreen.byteRng
        Tacenta.UnitLifecycleIntegrationScreen.byteCrc (refReal sk pk) succMessage sampleRng =
          ok output ∧
      output.1 = .Err (.Triple (.Classical .OutOfOrder)) ∧ TripleRefusalOpen output := by
  obtain ⟨output, hcall, hstep⟩ := decrypt_ratchet_refines_complete_at_refusal dh view
    (oracleDecrypt (Tacenta.UnitLifecycleIntegrationScreen.byteTrace sampleRng)) rfl oracleOf
    codec contracts agreements sk pk
  have hres := hstep.result
  rw [ref_model_refuses dh view sk pk] at hres
  have hsound : refusalOf (.Triple (.Classical .OutOfOrder)) =
      Model.Lifecycle.tripleReceiveRefusalOf (.classical .outOfOrder) :=
    tripleReceiveRefusalOfReal_sound (realReason := .Classical .OutOfOrder) rfl
  have hout : output.1 = .Err (.Triple (.Classical .OutOfOrder)) := by
    rcases h1 : output.1 with v | e
    · rw [h1] at hres
      exact absurd hres (by simp [ResultRefines])
    · rw [h1] at hres
      have he : refusalOf e = refusalOf (.Triple (.Classical .OutOfOrder)) := by
        rw [hsound]
        exact hres
      rw [refusalOf_injective he]
  exact ⟨output, hcall, hout, .Classical .OutOfOrder, hout, rfl⟩

open Tacenta.UnitSatisfiabilityJoint Tacenta.UnitSatisfiabilityBraidAgreements in
/-- The generated open-path witness with its complete agreement record built from the joint
boundary shapes.  This is the shape-backed facade for `generated_reaches_open_path`. -/
theorem generated_reaches_open_path_from_shapes
    (dh : DhView) (view : Model.Lifecycle.CodewordView)
    (hA : AllT1Shapes Interp.real) (hL : StdLaws Interp.real)
    (hTP : TruncatePrefixShape Interp.real)
    (hD : ZeroizingModelShape Interp.real DerivedZ)
    (hT : T3Agreements Interp.real
      (oracleDecrypt (Tacenta.UnitLifecycleIntegrationScreen.byteTrace sampleRng)).braidKem)
    (hZ : ZeroizeRoundTripShapes Interp.real)
    (hC : DhCodecOfShape Interp.real ⟨dh.privateKey, dh.publicKey⟩)
    (hO : DecryptOracleShape Interp.real ⟨dh.privateKey, dh.publicKey⟩
      Tacenta.UnitLifecycleIntegrationScreen.byteRng Tacenta.UnitLifecycleIntegrationScreen.byteCrc
      Tacenta.UnitLifecycleIntegrationScreen.byteTrace
      (oracleDecrypt (Tacenta.UnitLifecycleIntegrationScreen.byteTrace sampleRng)))
    (sk : tacenta_boundary.dh.PrivateKey) (pk : tacenta_boundary.dh.PublicKeyBytes) :
    ∃ output,
      lifecycle.Session.decrypt_ratchet Tacenta.UnitLifecycleIntegrationScreen.byteRng
        Tacenta.UnitLifecycleIntegrationScreen.byteCrc (refReal sk pk) succMessage sampleRng =
          ok output ∧ output.1 = .Err (.Triple (.Classical .OutOfOrder)) ∧
      TripleRefusalOpen output := by
  have hb := decrypt_shapes_are_predicates
  let oracle := oracleDecrypt (Tacenta.UnitLifecycleIntegrationScreen.byteTrace sampleRng)
  have oracleOf := (hb.2.1 Tacenta.UnitLifecycleIntegrationScreen.byteRng
    Tacenta.UnitLifecycleIntegrationScreen.byteCrc dh
    Tacenta.UnitLifecycleIntegrationScreen.byteTrace oracle).2 hO
  have codec := (hb.1 dh).2 hC
  have hz := hb.2.2.2 hZ
  have r32 : Tacenta.UnitLifecycleT1.Random32Total Tacenta.UnitLifecycleIntegrationScreen.byteRng :=
    fun _ _ _ => ⟨_, rfl⟩
  have ax : DecryptAxiom Interp.real Tacenta.UnitLifecycleIntegrationScreen.byteRng :=
    ⟨hA.dhCodec, hA.dhAgree, hA.aeadOpen, r32,
      ⟨hA.ct1Len, hA.ct2Len, hA.headerLen, hA.ekVectorLen, hA.keyPairEkVector,
        hA.keyPairDecapsulate, hA.hkdf, hA.hmac, hA.validateEk, hA.encapsulate2, hA.keyPairClone,
        hA.encapsStateClone, hA.optionClone, hA.zeroizingArray, hA.arrayZeroize, hA.rangeFullIndex⟩,
      ⟨hA.hmac, hA.hkdf, hA.zeroizingTotal, hA.spqrZeroize, hA.vecRetainAxiom, hA.optionClone,
        trivial⟩,
      hA.messageKeyMaterial⟩
  have contracts := Tacenta.UnitSatisfiabilityRecords.decrypt_contracts_of_axiom_base
    Tacenta.UnitLifecycleIntegrationScreen.byteRng ax hL
  have er : Tacenta.SessionUnitBraidT3.ErasureAgrees :=
    Tacenta.UnitErasureRs.Glue.erasureAgrees hA.divCeilValue hTP
  obtain ⟨vr, rm⟩ := Tacenta.SessionUnitSatisfiabilitySpqrLaws.session_sparse_agreements_of_shapes
    hL hA.vecRetainAxiom hA.spqrZeroize
  letI : Tacenta.SessionUnitT1.DerivedKeysModel := hD.toDerived
  have agreements : DecryptRatchetAgreements oracle.braidKem :=
    ⟨hT.hmac, hT.hkdf, hz.1, hz.2.1, hz.2.2.1, hz.2.2.2.1, vr, rm, hT.kemAgrees, er, hT.kemLen,
      hT.validateEk, hT.kemClone, hz.2.2.2.2⟩
  exact generated_reaches_open_path dh view oracleOf codec contracts agreements sk pk

end Tacenta.UnitLifecycleDecryptRatchetCompleteScreen

/-! ## Pins -/

/--
info: 'Tacenta.UnitLifecycleDecryptRatchetCompleteScreen.ref_model_triple_refuses' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleDecryptRatchetCompleteScreen.ref_model_triple_refuses

/--
info: 'Tacenta.UnitLifecycleDecryptRatchetCompleteScreen.ref_premises' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleDecryptRatchetCompleteScreen.ref_premises

/--
info: 'Tacenta.UnitLifecycleDecryptRatchetCompleteScreen.ref_triple_refuses' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_kdf.hkdf_sha256,
 tacenta_kdf.hmac_sha256,
 zeroize.Zeroizing,
 zeroize.Zeroizing.new,
 Array.Insts.ZeroizeZeroize.zeroize,
 Pair.Insts.ZeroizeZeroize.zeroize,
 alloc.vec.Vec.capacity,
 alloc.vec.Vec.pop,
 core.option.Option.as_mut,
 zeroize.Zeroize.Blanket.zeroize,
 Tacenta.SessionUnitSpqrT3.chain_label_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.chain_start_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.max_skip_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.max_skip_val._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.max_skipped_store_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.protocol_info_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.receive_refines_continuation._native.native_decide.ax_1_29,
 Tacenta.SessionUnitSpqrT3.root_label_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitTripleT3.combine_info_agrees._native.native_decide.ax_1_1,
 zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 core.option.Option.Insts.CoreCloneClone.clone]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleDecryptRatchetCompleteScreen.ref_triple_refuses

/--
info: 'Tacenta.UnitLifecycleDecryptRatchetCompleteScreen.ref_headroom' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_kem.EncapsState,
 tacenta_kem.IncrementalKeyPair,
 tacenta_boundary.dh.PrivateKey,
 tacenta_boundary.dh.PublicKeyBytes]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleDecryptRatchetCompleteScreen.ref_headroom

/--
info: 'Tacenta.UnitLifecycleDecryptRatchetCompleteScreen.ref_run_satisfiable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_kem.EncapsState,
 tacenta_kem.IncrementalKeyPair,
 tacenta_kem.encapsulate2,
 tacenta_boundary.dh.PrivateKey,
 tacenta_boundary.dh.PublicKeyBytes,
 tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_kem.IncrementalKeyPair.header,
 alloc.vec.Vec.truncate,
 core.num.Usize.div_ceil]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleDecryptRatchetCompleteScreen.ref_run_satisfiable

/--
info: 'Tacenta.UnitLifecycleDecryptRatchetCompleteScreen.ref_model_refuses' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_kem.EncapsState,
 tacenta_kem.IncrementalKeyPair,
 tacenta_boundary.dh.PrivateKey,
 tacenta_boundary.dh.PublicKeyBytes]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleDecryptRatchetCompleteScreen.ref_model_refuses

/--
info: 'Tacenta.UnitLifecycleDecryptRatchetCompleteScreen.hypotheses_meet_open_path' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_kem.EncapsState,
 tacenta_kem.IncrementalKeyPair,
 tacenta_kem.encapsulate2,
 tacenta_boundary.dh.PrivateKey,
 tacenta_boundary.dh.PublicKeyBytes,
 tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_kem.IncrementalKeyPair.header,
 alloc.vec.Vec.truncate,
 core.num.Usize.div_ceil]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleDecryptRatchetCompleteScreen.hypotheses_meet_open_path

/--
info: 'Tacenta.UnitLifecycleDecryptRatchetCompleteScreen.decrypt_ratchet_refines_complete_at_refusal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_kdf.hkdf_sha256,
 tacenta_kdf.hmac_sha256,
 tacenta_kem.CT1_LEN,
 tacenta_kem.CT2_LEN,
 tacenta_kem.EK_VECTOR_LEN,
 tacenta_kem.EncapsState,
 tacenta_kem.HEADER_LEN,
 tacenta_kem.IncrementalKeyPair,
 tacenta_kem.encapsulate1,
 tacenta_kem.encapsulate2,
 tacenta_kem.validate_ek,
 zeroize.Zeroizing,
 rand_core_1.error.Error,
 tacenta_boundary.aead.decrypt,
 tacenta_boundary.dh.PrivateKey,
 tacenta_boundary.dh.PublicKeyBytes,
 tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_kem.IncrementalKeyPair.generate,
 tacenta_kem.IncrementalKeyPair.header,
 zeroize.Zeroizing.new,
 Array.Insts.ZeroizeZeroize.zeroize,
 Pair.Insts.ZeroizeZeroize.zeroize,
 TupleABC.Insts.ZeroizeZeroize.zeroize,
 alloc.vec.Vec.capacity,
 alloc.vec.Vec.pop,
 alloc.vec.Vec.truncate,
 core.num.Usize.div_ceil,
 core.option.Option.as_mut,
 tacenta_boundary.dh.PrivateKey.agree,
 tacenta_boundary.dh.PrivateKey.from_bytes,
 tacenta_boundary.dh.PrivateKey.public_key,
 tacenta_boundary.dh.PrivateKey.to_bytes,
 tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_boundary.dh.PublicKeyBytes.from_bytes,
 zeroize.Zeroize.Blanket.zeroize,
 Tacenta.SessionUnitSpqrT3.chain_label_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.chain_start_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.max_skip_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.max_skip_val._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.max_skipped_store_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.protocol_info_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.receive_refines_continuation._native.native_decide.ax_1_29,
 Tacenta.SessionUnitSpqrT3.root_label_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitTripleT3.combine_info_agrees._native.native_decide.ax_1_1,
 tacenta_kem.EncapsState.Insts.CoreCloneClone.clone,
 tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone,
 zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 core.option.Option.Insts.CoreCloneClone.clone,
 tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes.eq,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleDecryptRatchetCompleteScreen.decrypt_ratchet_refines_complete_at_refusal

/--
info: Tacenta.UnitLifecycleDecryptRatchetCompleteScreen.ref_model_triple_refuses : Model.Triple.receiveDetailed
      Tacenta.UnitLifecycleDecryptRatchetCompleteScreen.refModel
      { dr := Tacenta.UnitLifecycleDecryptRatchetCompleteScreen.refModelHeader,
        epoch := ↑Tacenta.UnitLifecycleDecryptRatchetCompleteScreen.refHeader.epoch,
        pqN := ↑Tacenta.UnitLifecycleDecryptRatchetCompleteScreen.refHeader.pq_n }
      (Tacenta.SessionUnitTripleT3.keyOf zeros32) (Tacenta.SessionUnitTripleT3.keyOf zeros32)
      (Tacenta.SessionUnitTripleT3.keyOf zeros32) none =
    Except.error (Model.Triple.ReceiveRefusal.classical Model.Ratchet.ReceiveRefusal.outOfOrder) ∧
  Model.Lifecycle.fullStore (Model.Triple.ReceiveRefusal.classical Model.Ratchet.ReceiveRefusal.outOfOrder) = none
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptRatchetCompleteScreen.ref_model_triple_refuses

/--
info: Tacenta.UnitLifecycleDecryptRatchetCompleteScreen.ref_premises : Tacenta.SessionUnitTripleT3.StateRefines
    Tacenta.SessionUnitTripleT3.ratchetAbs Tacenta.SessionUnitTripleT3.spqrAbs
    Tacenta.UnitLifecycleDecryptRatchetCompleteScreen.refTriple
    Tacenta.UnitLifecycleDecryptRatchetCompleteScreen.refModel ∧
  Tacenta.SessionUnitTripleT3.RatchetHeaderR Tacenta.UnitLifecycleDecryptRatchetCompleteScreen.refHeader.dr
      Tacenta.UnitLifecycleDecryptRatchetCompleteScreen.refModelHeader ∧
    (List.filter
            (fun x =>
              x.1 == Tacenta.UnitLifecycleDecryptRatchetCompleteScreen.refModelHeader.dh &&
                x.2.1 == Tacenta.UnitLifecycleDecryptRatchetCompleteScreen.refModelHeader.n)
            Tacenta.UnitLifecycleDecryptRatchetCompleteScreen.refModel.classical.skipped).length ≤
        1 ∧
      max Tacenta.UnitLifecycleDecryptRatchetCompleteScreen.refModel.classical.skipped.length
              Model.State.maxSkippedStore +
            Model.State.maxSkip ≤
          Usize.max ∧
        Tacenta.UnitLifecycleDecryptRatchetCompleteScreen.refModel.classical.events + 1 < U32.max ∧
          Tacenta.UnitLifecycleDecryptRatchetCompleteScreen.refModel.postQuantum.epoch + 1 < U64.max ∧
            Tacenta.UnitLifecycleDecryptRatchetCompleteScreen.refModel.postQuantum.chains.length + 2 < Usize.max ∧
              (∀ p ∈ Tacenta.UnitLifecycleDecryptRatchetCompleteScreen.refModel.postQuantum.chains,
                  p.1 + Model.SparseRatchet.epochsKept ≤ U64.max) ∧
                (∀ sk ∈ Tacenta.UnitLifecycleDecryptRatchetCompleteScreen.refModel.postQuantum.skipped,
                    sk.1 + Model.SparseRatchet.epochsKept ≤ U64.max) ∧
                  (∀ (o : tacenta_spqr.Output),
                      none = some o → ↑o.key_epoch + Model.SparseRatchet.epochsKept ≤ U64.max) ∧
                    Tacenta.UnitLifecycleDecryptRatchetCompleteScreen.refModel.postQuantum.skipped.length +
                          Model.SparseRatchet.maxSkip ≤
                        Usize.max ∧
                      (List.filter
                              (fun x =>
                                x.1 == ↑Tacenta.UnitLifecycleDecryptRatchetCompleteScreen.refHeader.epoch &&
                                  x.2.1 == ↑Tacenta.UnitLifecycleDecryptRatchetCompleteScreen.refHeader.pq_n)
                              Tacenta.UnitLifecycleDecryptRatchetCompleteScreen.refModel.postQuantum.skipped).length ≤
                          1 ∧
                        ∀ p ∈ Tacenta.UnitLifecycleDecryptRatchetCompleteScreen.refModel.postQuantum.chains,
                          ∀ (ch : Model.SparseRatchet.Chain),
                            p.2.send = some ch ∨ p.2.receive = some ch → ch.n < U64.max
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptRatchetCompleteScreen.ref_premises

/--
info: Tacenta.UnitLifecycleDecryptRatchetCompleteScreen.ref_triple_refuses : Tacenta.SessionUnitT3.HmacAgrees →
  Tacenta.SessionUnitT3.HkdfAgrees →
    Tacenta.SessionUnitT3.ZeroizingRoundTrips →
      Tacenta.SessionUnitT1.RemoveSkippedAtTotal →
        ∀ [Tacenta.SessionUnitT1.DerivedKeysModel],
          Tacenta.SessionUnitSpqrT3.ZeroizingRoundTrips96 →
            Tacenta.SessionUnitSpqrT3.ZeroizingRoundTrips64 →
              Tacenta.SessionUnitSpqrT3.VecRetainAgrees →
                Tacenta.SessionUnitSpqrT1.VecRetainTotal →
                  Tacenta.SessionUnitSpqrT3.RemoveSkippedAtAgrees →
                    Tacenta.SessionUnitSpqrT1.ZeroizeTotal →
                      Tacenta.SessionUnitSpqrT1.OptionCloneTotal →
                        ∃ reason,
                          Tacenta.UnitLifecycleDecryptRatchetCompleteScreen.refTriple.receive
                                Tacenta.UnitLifecycleDecryptRatchetCompleteScreen.refHeader zeros32 zeros32 zeros32
                                none =
                              ok (core.result.Result.Err reason) ∧
                            tripleReceiveRefusalOfReal reason =
                              some (Model.Triple.ReceiveRefusal.classical Model.Ratchet.ReceiveRefusal.outOfOrder)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptRatchetCompleteScreen.ref_triple_refuses

/--
info: Tacenta.UnitLifecycleDecryptRatchetCompleteScreen.ref_headroom : ∀ (sk : tacenta_boundary.dh.PrivateKey)
  (pk : tacenta_boundary.dh.PublicKeyBytes),
  Tacenta.UnitLifecycleT1.DecryptRatchetHeadroom (Tacenta.UnitLifecycleDecryptRatchetCompleteScreen.refReal sk pk)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptRatchetCompleteScreen.ref_headroom

/--
info: Tacenta.UnitLifecycleDecryptRatchetCompleteScreen.ref_run_satisfiable : ∀ (K : Model.Braid.Kem) (dh : DhView)
  (sk : tacenta_boundary.dh.PrivateKey) (pk : tacenta_boundary.dh.PublicKeyBytes),
  SessionRefines dh K (Tacenta.UnitLifecycleDecryptRatchetCompleteScreen.refReal sk pk)
      (modelOf dh (Tacenta.UnitLifecycleDecryptRatchetCompleteScreen.refReal sk pk)) ∧
    Tacenta.UnitLifecycleT1.DecryptRatchetHeadroom (Tacenta.UnitLifecycleDecryptRatchetCompleteScreen.refReal sk pk) ∧
      ∀ (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle),
        oracle.braidKem = K →
          oracle.draws = Tacenta.UnitLifecycleIntegrationScreen.byteTrace sampleRng →
            Tacenta.UnitLifecycleIntegrationScreen.byteTrace sampleRng = oracle.draws ∧
              DecryptRatchetRun view oracle Tacenta.UnitLifecycleIntegrationScreen.byteTrace
                (Tacenta.UnitLifecycleDecryptRatchetCompleteScreen.refReal sk pk)
                (modelOf dh (Tacenta.UnitLifecycleDecryptRatchetCompleteScreen.refReal sk pk)) succMessage sampleRng
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptRatchetCompleteScreen.ref_run_satisfiable

/--
info: Tacenta.UnitLifecycleDecryptRatchetCompleteScreen.ref_model_refuses : ∀ (dh : DhView)
  (view : Model.Lifecycle.CodewordView) (sk : tacenta_boundary.dh.PrivateKey) (pk : tacenta_boundary.dh.PublicKeyBytes),
  (Model.Lifecycle.decryptRatchet view (oracleDecrypt (Tacenta.UnitLifecycleIntegrationScreen.byteTrace sampleRng))
        (modelOf dh (Tacenta.UnitLifecycleDecryptRatchetCompleteScreen.refReal sk pk)) (sliceOf succMessage)).result =
    Except.error
      (Model.Lifecycle.tripleReceiveRefusalOf
        (Model.Triple.ReceiveRefusal.classical Model.Ratchet.ReceiveRefusal.outOfOrder))
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptRatchetCompleteScreen.ref_model_refuses

/--
info: Tacenta.UnitLifecycleDecryptRatchetCompleteScreen.hypotheses_meet_open_path : ∀ (dh : DhView)
  (view : Model.Lifecycle.CodewordView) (sk : tacenta_boundary.dh.PrivateKey) (pk : tacenta_boundary.dh.PublicKeyBytes),
  have oracle := oracleDecrypt (Tacenta.UnitLifecycleIntegrationScreen.byteTrace sampleRng);
  SessionRefines dh oracle.braidKem (Tacenta.UnitLifecycleDecryptRatchetCompleteScreen.refReal sk pk)
      (modelOf dh (Tacenta.UnitLifecycleDecryptRatchetCompleteScreen.refReal sk pk)) ∧
    Tacenta.UnitLifecycleT1.DecryptRatchetHeadroom (Tacenta.UnitLifecycleDecryptRatchetCompleteScreen.refReal sk pk) ∧
      DecryptRatchetRun view oracle Tacenta.UnitLifecycleIntegrationScreen.byteTrace
          (Tacenta.UnitLifecycleDecryptRatchetCompleteScreen.refReal sk pk)
          (modelOf dh (Tacenta.UnitLifecycleDecryptRatchetCompleteScreen.refReal sk pk)) succMessage sampleRng ∧
        (Model.Lifecycle.decryptRatchet view oracle
                (modelOf dh (Tacenta.UnitLifecycleDecryptRatchetCompleteScreen.refReal sk pk))
                (sliceOf succMessage)).result =
            Except.error
              (Model.Lifecycle.tripleReceiveRefusalOf
                (Model.Triple.ReceiveRefusal.classical Model.Ratchet.ReceiveRefusal.outOfOrder)) ∧
          Model.Lifecycle.fullStore (Model.Triple.ReceiveRefusal.classical Model.Ratchet.ReceiveRefusal.outOfOrder) =
            none
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptRatchetCompleteScreen.hypotheses_meet_open_path

/--
info: Tacenta.UnitLifecycleDecryptRatchetCompleteScreen.decrypt_ratchet_refines_complete_at_refusal : ∀ (dh : DhView)
  (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle),
  oracle.draws = Tacenta.UnitLifecycleIntegrationScreen.byteTrace sampleRng →
    DecryptOracleOf Tacenta.UnitLifecycleIntegrationScreen.byteRng Tacenta.UnitLifecycleIntegrationScreen.byteCrc dh
        Tacenta.UnitLifecycleIntegrationScreen.byteTrace oracle →
      DhCodecOf dh →
        Tacenta.UnitLifecycleT1.DecryptRatchetContracts Tacenta.UnitLifecycleIntegrationScreen.byteRng →
          ∀ [Tacenta.SessionUnitT1.DerivedKeysModel],
            DecryptRatchetAgreements oracle.braidKem →
              ∀ (sk : tacenta_boundary.dh.PrivateKey) (pk : tacenta_boundary.dh.PublicKeyBytes),
                ∃ output,
                  lifecycle.Session.decrypt_ratchet Tacenta.UnitLifecycleIntegrationScreen.byteRng
                        Tacenta.UnitLifecycleIntegrationScreen.byteCrc
                        (Tacenta.UnitLifecycleDecryptRatchetCompleteScreen.refReal sk pk) succMessage sampleRng =
                      ok output ∧
                    StepRefines Tacenta.UnitLifecycleIntegrationScreen.byteTrace dh oracle.braidKem output
                      (Model.Lifecycle.decryptRatchet view oracle
                        (modelOf dh (Tacenta.UnitLifecycleDecryptRatchetCompleteScreen.refReal sk pk))
                        (sliceOf succMessage))
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptRatchetCompleteScreen.decrypt_ratchet_refines_complete_at_refusal

/--
info: def Tacenta.UnitLifecycleDecryptRatchetCompleteScreen.refTriple : tacenta_triple.State :=
have __src := succTriple;
{
  classical :=
    have __src := succTriple.classical;
    { dhs_pub := __src.dhs_pub, dhr_pub := __src.dhr_pub, rk := __src.rk, cks := __src.cks, ckr := __src.ckr,
      ns := __src.ns, nr := 1#u32, pn := __src.pn, skipped := __src.skipped, events := __src.events,
      labels := __src.labels },
  post_quantum := __src.post_quantum }
-/
#guard_msgs in
#print Tacenta.UnitLifecycleDecryptRatchetCompleteScreen.refTriple

/--
info: def Tacenta.UnitLifecycleDecryptRatchetCompleteScreen.refHeader : tacenta_triple.Header :=
{ dr := { dh := ones32, pn := 0#u32, n := 0#u32 }, epoch := 0#u64, pq_n := 1#u64 }
-/
#guard_msgs in
#print Tacenta.UnitLifecycleDecryptRatchetCompleteScreen.refHeader

/--
info: def Tacenta.UnitLifecycleDecryptRatchetCompleteScreen.refModelHeader : Model.State.Header :=
{ dh := Tacenta.SessionUnitTripleT3.keyOf ones32, pn := 0, n := 0 }
-/
#guard_msgs in
#print Tacenta.UnitLifecycleDecryptRatchetCompleteScreen.refModelHeader

/--
info: def Tacenta.UnitLifecycleDecryptRatchetCompleteScreen.refModel : Model.Triple.State :=
{
  classical :=
    Tacenta.SessionUnitTripleT3.ratchetAbs Tacenta.UnitLifecycleDecryptRatchetCompleteScreen.refTriple.classical,
  postQuantum :=
    Tacenta.SessionUnitTripleT3.spqrAbs Tacenta.UnitLifecycleDecryptRatchetCompleteScreen.refTriple.post_quantum }
-/
#guard_msgs in
#print Tacenta.UnitLifecycleDecryptRatchetCompleteScreen.refModel

/--
info: def Tacenta.UnitLifecycleDecryptRatchetCompleteScreen.refReal : tacenta_boundary.dh.PrivateKey →
  tacenta_boundary.dh.PublicKeyBytes → lifecycle.Session :=
fun sk pk =>
  have __src := sampleReal sk pk;
  { triple := Tacenta.UnitLifecycleDecryptRatchetCompleteScreen.refTriple, braid := __src.braid,
    ratchet_private := __src.ratchet_private, identity_ad := __src.identity_ad,
    our_identity_public := __src.our_identity_public, peer_identity_public := __src.peer_identity_public,
    pending_initial := __src.pending_initial, established_ephemeral := __src.established_ephemeral }
-/
#guard_msgs in
#print Tacenta.UnitLifecycleDecryptRatchetCompleteScreen.refReal

/--
info: 'Tacenta.UnitLifecycleDecryptRatchetCompleteScreen.generated_reaches_open_path' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_kdf.hkdf_sha256,
 tacenta_kdf.hmac_sha256,
 tacenta_kem.CT1_LEN,
 tacenta_kem.CT2_LEN,
 tacenta_kem.EK_VECTOR_LEN,
 tacenta_kem.EncapsState,
 tacenta_kem.HEADER_LEN,
 tacenta_kem.IncrementalKeyPair,
 tacenta_kem.encapsulate1,
 tacenta_kem.encapsulate2,
 tacenta_kem.validate_ek,
 zeroize.Zeroizing,
 rand_core_1.error.Error,
 tacenta_boundary.aead.decrypt,
 tacenta_boundary.dh.PrivateKey,
 tacenta_boundary.dh.PublicKeyBytes,
 tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_kem.IncrementalKeyPair.generate,
 tacenta_kem.IncrementalKeyPair.header,
 zeroize.Zeroizing.new,
 Array.Insts.ZeroizeZeroize.zeroize,
 Pair.Insts.ZeroizeZeroize.zeroize,
 TupleABC.Insts.ZeroizeZeroize.zeroize,
 alloc.vec.Vec.capacity,
 alloc.vec.Vec.pop,
 alloc.vec.Vec.truncate,
 core.num.Usize.div_ceil,
 core.option.Option.as_mut,
 tacenta_boundary.dh.PrivateKey.agree,
 tacenta_boundary.dh.PrivateKey.from_bytes,
 tacenta_boundary.dh.PrivateKey.public_key,
 tacenta_boundary.dh.PrivateKey.to_bytes,
 tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_boundary.dh.PublicKeyBytes.from_bytes,
 zeroize.Zeroize.Blanket.zeroize,
 Tacenta.SessionUnitSpqrT3.chain_label_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.chain_start_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.max_skip_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.max_skip_val._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.max_skipped_store_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.protocol_info_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.receive_refines_continuation._native.native_decide.ax_1_29,
 Tacenta.SessionUnitSpqrT3.root_label_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitTripleT3.combine_info_agrees._native.native_decide.ax_1_1,
 tacenta_kem.EncapsState.Insts.CoreCloneClone.clone,
 tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone,
 zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 core.option.Option.Insts.CoreCloneClone.clone,
 tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes.eq,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleDecryptRatchetCompleteScreen.generated_reaches_open_path

/--
info: Tacenta.UnitLifecycleDecryptRatchetCompleteScreen.generated_reaches_open_path : ∀ (dh : DhView)
  (view : Model.Lifecycle.CodewordView),
  DecryptOracleOf Tacenta.UnitLifecycleIntegrationScreen.byteRng Tacenta.UnitLifecycleIntegrationScreen.byteCrc dh
      Tacenta.UnitLifecycleIntegrationScreen.byteTrace
      (oracleDecrypt (Tacenta.UnitLifecycleIntegrationScreen.byteTrace sampleRng)) →
    DhCodecOf dh →
      Tacenta.UnitLifecycleT1.DecryptRatchetContracts Tacenta.UnitLifecycleIntegrationScreen.byteRng →
        ∀ [Tacenta.SessionUnitT1.DerivedKeysModel],
          DecryptRatchetAgreements
              (oracleDecrypt (Tacenta.UnitLifecycleIntegrationScreen.byteTrace sampleRng)).braidKem →
            ∀ (sk : tacenta_boundary.dh.PrivateKey) (pk : tacenta_boundary.dh.PublicKeyBytes),
              ∃ output,
                lifecycle.Session.decrypt_ratchet Tacenta.UnitLifecycleIntegrationScreen.byteRng
                      Tacenta.UnitLifecycleIntegrationScreen.byteCrc
                      (Tacenta.UnitLifecycleDecryptRatchetCompleteScreen.refReal sk pk) succMessage sampleRng =
                    ok output ∧
                  output.1 =
                      core.result.Result.Err
                        (lifecycle.Error.Triple
                          (tacenta_triple.TripleError.Classical tacenta_ratchet.RatchetError.OutOfOrder)) ∧
                    TripleRefusalOpen output
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptRatchetCompleteScreen.generated_reaches_open_path
