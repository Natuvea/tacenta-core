import Translation.UnitLifecycleDecryptRatchetT3
import Translation.UnitLifecycleIntegrationScreen
import Translation.UnitHeadroomSatisfiable
import Translation.UnitSatisfiabilityBraidStates
import Translation.UnitSatisfiabilityBraidAgreements

/-!
# Screening the hypotheses of `decrypt_ratchet_refines`

A theorem whose hypotheses nothing satisfies is true and says nothing.  This module decides the
hypotheses `UnitLifecycleDecryptRatchetT3.lean` introduces and the ones it uses that no earlier
module decided, in two parts.

## A. One run meets the per-run hypotheses together

`sample_run_satisfiable`: there are a translated session, a model session, a message and a
byte-stream random source such that the message decodes on both sides (so the fields of
`DecryptRatchetRun`, which are asked of the decoded composite, are not met by an undecodable
message), and `SessionRefines`, `DecryptRatchetHeadroom`, the trace equation and every field of
`DecryptRatchetRun` hold, for every Braid KEM model, every codeword view and every oracle whose
KEM model is that one and whose draws are the source's.  The session is the fresh one of
`UnitHeadroomSatisfiable.sessionOf` (no skipped key, one chain-table entry, a Braid in
`KeysUnsampled`); the composite carries no agreement chunk.  The values of the two opaque key
types are arguments, as in `UnitHeadroomSatisfiable.lean`.  No proof here chooses a width of
`usize`: the one fact used, that `Usize.max` is at least `2^32 - 1`, holds at both
(`UnitHeadroomSatisfiable.usize_max_ge`).

The fields are not true of every run: `run_draw_not_trivial` (an exhausted source),
`retryRunBounds_not_trivial` (a sparse epoch at `u64::MAX`, a classical store past the bound),
`run_chunk_not_trivial` (a chunk on one side only).  `TripleRefusalOpen`, the second disjunct of the
conclusion, is false of every success and of every refusal that is not a Triple refusal
(`tripleRefusalOpen_iff`), so it does not make the conclusion trivial.

## C. Runs the model refuses and accepts

`hypotheses_meet_refusal_and_success`: with part B's oracle, the per-run hypotheses hold at part A's
run, whose model step refuses at the first agreement, and at a second run over a Triple state that
already receives on both halves (`succ_run_satisfiable`), whose model step succeeds.

## What this does not show

That a run carrying a chunk meets the record (the witness has no
chunk, and `HonestChunk` holds by its vacuous arm there; `UnitSatisfiabilityBraidStates` has
witnesses with data for the Braid relations alone).  Anything about the real primitives.
-/

open Aeneas Aeneas.Std Result
open tacenta_session_unit
open Tacenta.UnitLifecycleT3
open Tacenta.UnitLifecycleDecryptRatchetT3

namespace Tacenta.UnitLifecycleDecryptRatchetScreen

/-! ## A. One run -/

/-- A composite with a canonical (all-zero) ratchet key and no agreement chunk. -/
def sampleComposite : Model.CompositeHeader.Composite :=
  { dh := List.replicate 32 0, pn := 0, n := 1, pqEpoch := 0, pqN := 1, agEpoch := 1,
    agType := .none, agChunk := none }

def sampleBytes : Bytes := Model.CompositeHeader.encode sampleComposite

theorem sampleBytes_length : sampleBytes.length = 102 := by decide

theorem sampleBytes_le : sampleBytes.length ≤ Usize.max := by
  rw [sampleBytes_length]
  exact Tacenta.SessionUnitSessionT1.small_le_usize_max (by omega)

/-- The message: the encoded composite with an empty ciphertext. -/
def sampleMessage : Slice U8 :=
  Tacenta.UnitSatisfiabilityBraidStates.sliceOfBytes sampleBytes sampleBytes_le

theorem sliceOf_sampleMessage : sliceOf sampleMessage = sampleBytes :=
  Tacenta.UnitSatisfiabilityBraidStates.sliceOf_sliceOfBytes sampleBytes sampleBytes_le

theorem sample_decode_model :
    Model.CompositeHeader.decodeDetailed (sliceOf sampleMessage) = .ok (sampleComposite, []) := by
  rw [sliceOf_sampleMessage, Model.CompositeHeader.decodeDetailed_ok_iff]
  decide

/-- The translated decoder accepts the message, and its header refines the model composite. -/
theorem sample_decode_real :
    ∃ decoded, tacenta_wire.decode_message sampleMessage = ok (.Ok decoded) ∧
      CompositeRefines decoded.header sampleComposite := by
  obtain ⟨r, hr, hpost⟩ := Std.WP.spec_imp_exists (decode_message_refines_lifecycle sampleMessage)
  have hmodel : Model.CompositeHeader.decode (sliceOf sampleMessage) = some (sampleComposite, []) :=
    (Model.CompositeHeader.decodeDetailed_ok_iff _ _).mp sample_decode_model
  cases r with
  | Err e =>
      rw [hmodel] at hpost
      exact absurd hpost (by simp)
  | Ok decoded =>
      obtain ⟨mh, hdec, hrel⟩ := hpost
      rw [hmodel] at hdec
      have hmh : sampleComposite = mh := (Prod.mk.inj (Option.some.inj hdec)).1
      subst hmh
      exact ⟨decoded, hr, hrel⟩

/-- The translated session: fresh Triple and Braid states, empty associated data. -/
def sampleReal (sk : tacenta_boundary.dh.PrivateKey) (pk : tacenta_boundary.dh.PublicKeyBytes) :
    lifecycle.Session :=
  Tacenta.UnitHeadroomSatisfiable.sessionOf sk pk pk
    (Tacenta.UnitHeadroomSatisfiable.vecOf [] (by simp))
    (Array.repeat 32#usize 0#u8) none

/-- The model session read off a translated session through the DH view, with the Braid at the
model's `KeysUnsampled` state. -/
def modelOf (dh : DhView) (real : lifecycle.Session) : Model.Lifecycle.Session :=
  { triple :=
      { classical := Tacenta.SessionUnitTripleT3.ratchetAbs real.triple.classical
        postQuantum := Tacenta.SessionUnitTripleT3.spqrAbs real.triple.post_quantum }
    braid := .keysUnsampled 1 Tacenta.UnitSatisfiabilityBraidStates.modelAuth0
    ratchetPrivate := dh.privateKey real.ratchet_private
    identityAd := vecOf real.identity_ad
    ourIdentityPublic := dh.publicKey real.our_identity_public
    peerIdentityPublic := dh.publicKey real.peer_identity_public
    pendingInitial := real.pending_initial.map (pendingInitialOf dh)
    establishedEphemeral := real.established_ephemeral.map vecOf }

theorem sample_sessionRefines (K : Model.Braid.Kem) (dh : DhView)
    (sk : tacenta_boundary.dh.PrivateKey) (pk : tacenta_boundary.dh.PublicKeyBytes) :
    SessionRefines dh K (sampleReal sk pk) (modelOf dh (sampleReal sk pk)) :=
  ⟨⟨rfl, rfl⟩, (Tacenta.UnitSatisfiabilityBraidStates.good_keysUnsampled (K := K)).1,
    rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem sample_headroom (sk : tacenta_boundary.dh.PrivateKey)
    (pk : tacenta_boundary.dh.PublicKeyBytes) :
    Tacenta.UnitLifecycleT1.DecryptRatchetHeadroom (sampleReal sk pk) := by
  have h4 := Tacenta.UnitHeadroomSatisfiable.usize_max_ge
  rw [sampleReal, Tacenta.UnitHeadroomSatisfiable.decryptHeadroom_sessionOf_iff]
  simp [Tacenta.UnitHeadroomSatisfiable.vecOf]
  omega

/-- A byte-stream source holding exactly one 32-byte draw. -/
def sampleRng : List U8 := List.replicate 32 0#u8

theorem sample_trace :
    Tacenta.UnitLifecycleIntegrationScreen.byteTrace sampleRng =
      [List.replicate 32 (0 : UInt8)] := by
  unfold Tacenta.UnitLifecycleIntegrationScreen.byteTrace sampleRng
  rw [Tacenta.UnitLifecycleIntegrationScreen.chunks32]
  simp only [List.length_map, List.length_replicate, le_refl, if_true]
  rw [Tacenta.UnitLifecycleIntegrationScreen.chunks32]
  simp [Tacenta.SessionUnitBraidT3.u8]

theorem sample_braid_output (K : Model.Braid.Kem) (view : Model.Lifecycle.CodewordView) :
    (Model.Braid.receive K (.keysUnsampled 1 Tacenta.UnitSatisfiabilityBraidStates.modelAuth0)
      (Model.Lifecycle.braidMessageOf view
        (.keysUnsampled 1 Tacenta.UnitSatisfiabilityBraidStates.modelAuth0)
        sampleComposite)).2.1 = none := by
  simp [Model.Braid.receive]

theorem sample_retryRunBounds (sk : tacenta_boundary.dh.PrivateKey)
    (pk : tacenta_boundary.dh.PublicKeyBytes) (dh : DhView) (output : Option Model.SparseRatchet.Output)
    (houtput : output = none) :
    RetryRunBounds (modelOf dh (sampleReal sk pk)).triple
      (Model.Lifecycle.tripleHeaderOf sampleComposite) output := by
  subst houtput
  have hu := Tacenta.UnitHeadroomSatisfiable.usize_max_ge
  constructor <;>
    simp [modelOf, sampleReal, Tacenta.UnitHeadroomSatisfiable.sessionOf,
      Tacenta.UnitHeadroomSatisfiable.freshTriple, Tacenta.UnitHeadroomSatisfiable.vecOf,
      Tacenta.SessionUnitTripleT3.ratchetAbs, Tacenta.SessionUnitTripleT3.spqrAbs,
      Model.State.maxSkippedStore, Model.SparseRatchet.maxSkippedStore,
      Model.SparseRatchet.epochsKept, U32.max_eq, U64.max_eq, cMax_usize,
      Tacenta.SessionUnitSpqrT3.chainsEntryOf, Tacenta.SessionUnitSpqrT3.chainsOf]
  all_goals omega

/-- **One run meets every per-run hypothesis of `decrypt_ratchet_refines` together.**  The
message decodes on both sides, and for every Braid KEM model, codeword view and oracle with that
KEM model and the source's draws, the session relation, the headroom, the trace equation and
the run record hold. -/
theorem sample_run_satisfiable (K : Model.Braid.Kem) (dh : DhView)
    (sk : tacenta_boundary.dh.PrivateKey) (pk : tacenta_boundary.dh.PublicKeyBytes) :
    (∃ decoded, tacenta_wire.decode_message sampleMessage = ok (.Ok decoded)) ∧
    Model.CompositeHeader.decodeDetailed (sliceOf sampleMessage) = .ok (sampleComposite, []) ∧
    SessionRefines dh K (sampleReal sk pk) (modelOf dh (sampleReal sk pk)) ∧
    Tacenta.UnitLifecycleT1.DecryptRatchetHeadroom (sampleReal sk pk) ∧
    ∀ (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle),
      oracle.braidKem = K →
      oracle.draws = Tacenta.UnitLifecycleIntegrationScreen.byteTrace sampleRng →
      Tacenta.UnitLifecycleIntegrationScreen.byteTrace sampleRng = oracle.draws ∧
      DecryptRatchetRun view oracle Tacenta.UnitLifecycleIntegrationScreen.byteTrace
        (sampleReal sk pk) (modelOf dh (sampleReal sk pk)) sampleMessage sampleRng := by
  obtain ⟨decoded, hdec, _⟩ := sample_decode_real
  refine ⟨⟨decoded, hdec⟩, sample_decode_model, sample_sessionRefines K dh sk pk,
    sample_headroom sk pk, ?_⟩
  intro view oracle hK hdraws
  refine ⟨hdraws.symm, ?_⟩
  have hmodelBraid : (modelOf dh (sampleReal sk pk)).braid =
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
  · simp only [sampleReal, Tacenta.UnitHeadroomSatisfiable.sessionOf,
      Tacenta.UnitHeadroomSatisfiable.freshBraid, Tacenta.SessionUnitBraidT1.State.epoch_val]
    scalar_tac
  · intro modelComposite ciphertext hdecode
    rw [sample_decode_model] at hdecode
    have hmc : sampleComposite = modelComposite := (Prod.mk.inj (Except.ok.inj hdecode)).1
    subst hmc
    apply sample_retryRunBounds
    rw [hmodelBraid, hK, sample_braid_output]
    rfl


/-! ## Controls: the per-run fields are not true of every run -/

/-- An exhausted byte-stream source fails `draw`, so no run record holds there. -/
theorem run_draw_not_trivial {view : Model.Lifecycle.CodewordView}
    {oracle : Model.Lifecycle.Oracle} {real : lifecycle.Session}
    {model : Model.Lifecycle.Session} {message : Slice U8} :
    ¬ DecryptRatchetRun view oracle Tacenta.UnitLifecycleIntegrationScreen.byteTrace
      real model message [] := by
  intro h
  obtain ⟨draw, rest, hd⟩ := h.draw
  have := (Tacenta.UnitLifecycleIntegrationScreen.chunks32_eq_cons hd).1
  simp at this

/-- `RetryRunBounds` fails at a sparse epoch of `u64::MAX` and at a classical store whose length
leaves less than `2000` below `2^32 - 1`. -/
theorem retryRunBounds_not_trivial (state : Model.Triple.State) (header : Model.Triple.Header)
    (output : Option Model.SparseRatchet.Output) :
    ¬ RetryRunBounds
        { state with postQuantum := { state.postQuantum with epoch := U64.max } } header output ∧
      ∀ entries : List Model.Ratchet.SkippedEntry, 4294967295 - 1999 ≤ entries.length →
        ¬ RetryRunBounds
          { state with classical := { state.classical with skipped := entries } } header output := by
  refine ⟨fun h => ?_, fun entries hlen h => ?_⟩
  · have := h.sparseEpoch
    simp at this
  · have := h.classicalStore
    simp only [cMax_usize, Model.State.maxSkippedStore] at this
    omega

/-- The open disjunct is exactly a Triple refusal whose reason `full_store` does not classify; it
is false of every success, of every refusal that is not a Triple refusal, and of the two full-store
refusals. -/
theorem tripleRefusalOpen_iff {R : Type}
    (output : core.result.Result (alloc.vec.Vec U8) lifecycle.Error × lifecycle.Session × R) :
    TripleRefusalOpen output ↔
      ∃ reason, output.1 = .Err (.Triple reason) ∧ lifecycle.full_store reason = ok none :=
  Iff.rfl

theorem tripleRefusalOpen_false_of_ok {R : Type} (plaintext : alloc.vec.Vec U8)
    (session : lifecycle.Session) (rng : R) :
    ¬ TripleRefusalOpen (.Ok plaintext, session, rng) := by
  rintro ⟨reason, h, _⟩
  cases h

theorem tripleRefusalOpen_false_of_store_full {R : Type} (session : lifecycle.Session) (rng : R) :
    ¬ TripleRefusalOpen
        (.Err (.Triple (.Classical .SkippedStoreFull)), session, rng) ∧
      ¬ TripleRefusalOpen
        (.Err (.Triple (.PostQuantum .SkippedStoreFull)), session, rng) := by
  refine ⟨?_, ?_⟩ <;> rintro ⟨reason, h, hfull⟩ <;> cases h <;> simp [lifecycle.full_store] at hfull

/-! ## B. The boundary clauses have a model

`DecryptOracleOf` and `DhCodecOf` are about the opaque DH and AEAD constants of the unit and the two
opaque key types, and `DecryptRatchetAgreements` holds five round trips of the opaque `zeroize`
wrappers.  No earlier module decided `DhCodecOf`, the DH and AEAD clauses, or the 32-, 80- and
96-byte round trips.  Here each is a shape over an interpretation of the unit's opaque constants
(`UnitSatisfiabilityJoint.Interp`), bound to the predicate at `Interp.real` (`decrypt_shapes_are_predicates`),
and one interpretation, `Interp.modelDecrypt`, satisfies them together with every axiom-level shape
of the session contract records, the laws `StdLaws`, `FaithfulShape` and `TruncatePrefix`, the two
model classes, and the six Braid agreements of `UnitSatisfiabilityBraidAgreements` at
`Model.Braid.toyKem` (`decrypt_boundary_has_a_model`).  `Interp.modelDecrypt` is
`Interp.modelT3` with the two key types read as 32-byte arrays and the DH family and the XEdDSA
verifier over them replaced; every other field is `Interp.modelT3`'s, so the shapes that mention
no replaced field are `UnitSatisfiabilityBraidAgreements`' own theorems, accepted by definitional
unfolding.  In it the agreement refuses the all-zero public key and the AEAD refuses the empty
ciphertext, so the clauses are not met only by an oracle that never refuses.

The sense is the substitution argument of `UnitSatisfiabilityJoint.lean`: a derivation of `False`
from these predicates at the real constants would become one from facts that hold in the model.
That is an argument about derivations, not a theorem inside Lean, and nothing here is shown of the
real X25519, AEAD or `zeroize` code.  Part A's witness takes values of the two key types as
arguments; in this interpretation those types are inhabited.

Not decided here: `SessionUnitSpqrT3.VecRetainAgrees` and `SessionUnitSpqrT3.RemoveSkippedAtAgrees`,
statements about translated functions that the session unit takes as assumptions
(`GAP-REGISTER.md`, row `SESSION-SPARSE-AGREEMENTS`), and `ErasureAgrees`, which
`UnitErasureRs.Glue.erasureAgrees` derives from two laws, the value of `usize::div_ceil` and the prefix
`Vec::truncate` keeps (`DivCeilValue`, `TruncatePrefix`), both of which hold in this model
(`AllT1Shapes.divCeilValue`, `TruncatePrefixShape`). -/

open Tacenta.UnitSatisfiabilityJoint
open Tacenta.UnitSatisfiabilityBraidAgreements

/-- The byte views of the two key types, over an interpretation. -/
structure DhViewShape (I : Interp) where
  privateKey : I.PrivateKey → Bytes
  publicKey : I.PublicKeyBytes → Bytes

structure DhCodecOfShape (I : Interp) (dh : DhViewShape I) : Prop where
  privateFromBytes : ∀ bytes, ∃ privateKey,
    I.dhPrivFromBytes bytes = ok privateKey ∧ dh.privateKey privateKey = arrayOf bytes
  fromBytes : ∀ bytes, ∃ publicKey,
    I.dhPubFromBytes bytes = ok publicKey ∧ dh.publicKey publicKey = arrayOf bytes
  asBytes : ∀ publicKey, ∃ bytes,
    I.dhPubAsBytes publicKey = ok bytes ∧ arrayOf bytes = dh.publicKey publicKey

structure DecryptOracleShape (I : Interp) (dh : DhViewShape I) {R : Type}
    (rngCore : rand_core_1.RngCore R) (cryptoRng : rand_core_1.CryptoRng R)
    (trace : R → List Model.Lifecycle.Key) (oracle : Model.Lifecycle.Oracle) : Prop where
  dhPublic : ∀ secret,
    ∃ publicKey, I.dhPrivPublicKey secret = ok publicKey ∧
      dh.publicKey publicKey = oracle.dhPublic (dh.privateKey secret)
  dhAgree : ∀ secret publicKey,
    ∃ result, I.dhPrivAgree secret publicKey = ok result ∧
      result.map arrayOf = oracle.dhAgree (dh.privateKey secret) (dh.publicKey publicKey)
  aeadOpen : ∀ key1 key2 iv ciphertext associatedData,
    ∃ result,
      I.aeadDecrypt key1 key2 iv ciphertext associatedData = ok result ∧
      resultOptionOf vecOf result = oracle.aeadOpen (arrayOf key1) (arrayOf key2)
        (arrayOf iv) (sliceOf ciphertext) (sliceOf associatedData)
  random32 : ∀ rng draw rest, trace rng = draw :: rest →
    ∃ value rng',
      lifecycle.random_secret rngCore cryptoRng rng = ok (value, rng') ∧
      arrayOf value = draw ∧ trace rng' = rest

/-- The five `zeroize` round trips of `DecryptRatchetAgreements`, over an interpretation. -/
structure ZeroizeRoundTripShapes (I : Interp) : Prop where
  w64 : ∀ inst : zeroize.Zeroize (Array U8 64#usize),
    (∀ z, ∃ w, I.zNew inst z = ok w ∧ I.zDeref inst w = ok z) ∧
    (∀ w, ∃ z, I.zDeref inst w = ok z)
  w80 : ∀ inst : zeroize.Zeroize (Array U8 80#usize),
    (∀ z, ∃ w, I.zNew inst z = ok w ∧ I.zDeref inst w = ok z) ∧
    (∀ w, ∃ z, I.zDeref inst w = ok z)
  w96 : ∀ inst : zeroize.Zeroize (Array U8 96#usize),
    ∀ z, ∃ w, I.zNew inst z = ok w ∧ I.zDeref inst w = ok z
  w64Sparse : ∀ inst : zeroize.Zeroize (Array U8 64#usize),
    ∀ z, ∃ w, I.zNew inst z = ok w ∧ I.zDeref inst w = ok z
  w32 : ∀ inst : zeroize.Zeroize (Array U8 32#usize),
    ∀ value, ∃ wrapped, I.zNew inst value = ok wrapped ∧ I.zDeref inst wrapped = ok value

/-- The bridges: at the real constants each shape is the predicate the theorem takes.  The
oracle and codec bridges repack a structure field for field; the round trips are `Iff.rfl`. -/
theorem decrypt_shapes_are_predicates :
    (∀ dh : DhView, DhCodecOf dh ↔ DhCodecOfShape Interp.real ⟨dh.privateKey, dh.publicKey⟩) ∧
    (∀ {R : Type} (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R)
        (dh : DhView) (trace : R → List Model.Lifecycle.Key) (oracle : Model.Lifecycle.Oracle),
      DecryptOracleOf rc crc dh trace oracle ↔
        DecryptOracleShape Interp.real ⟨dh.privateKey, dh.publicKey⟩ rc crc trace oracle) ∧
    ((Tacenta.SessionUnitT3.ZeroizingRoundTrips ∧ Tacenta.SessionUnitT3.ZeroizingRoundTrips80 ∧
        Tacenta.SessionUnitSpqrT3.ZeroizingRoundTrips96 ∧
        Tacenta.SessionUnitSpqrT3.ZeroizingRoundTrips64 ∧
        ZeroizingRoundTrips (Array U8 32#usize)) ↔
      ZeroizeRoundTripShapes Interp.real) := by
  refine ⟨fun dh => ⟨fun h => ⟨h.1, h.2, h.3⟩, fun h => ⟨h.1, h.2, h.3⟩⟩,
    fun rc crc dh trace oracle => ⟨fun h => ⟨h.1, h.2, h.3, h.4⟩, fun h => ⟨h.1, h.2, h.3, h.4⟩⟩,
    ⟨fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩,
      fun h => ⟨h.1, h.2, h.3, h.4, h.5⟩⟩⟩

def zeros32 : Array U8 32#usize := Array.repeat 32#usize 0#u8

/-- `Interp.modelT3` with the two key types read as 32-byte arrays.  The private key is its bytes,
the public key is the private key's bytes, the agreement refuses the all-zero public key and
otherwise returns the private key, and the AEAD open refuses the empty ciphertext. -/
noncomputable def Interp.modelDecrypt : Interp :=
  { Interp.modelT3 with
    PrivateKey := Array U8 32#usize
    PublicKeyBytes := Array U8 32#usize
    dhPrivFromBytes := fun a => ok a
    dhPrivPublicKey := fun k => ok k
    dhPrivAgree := fun k p => ok (if p.val = zeros32.val then none else some k)
    dhPrivToBytes := fun k => ok k
    dhPubFromBytes := fun a => ok a
    dhPubAsBytes := fun k => ok k
    dhPubEq := fun a b => ok (decide (a.val = b.val))
    dhIsPrimeOrderPublic := fun _ => ok true
    aeadDecrypt := fun _ _ _ c _ =>
      ok (if c.val = [] then core.result.Result.Err () else core.result.Result.Ok (alloc.vec.Vec.new U8))
    xeddsaVerify := fun _ _ _ => ok (core.result.Result.Ok ()) }

def viewDecrypt : DhViewShape Interp.modelDecrypt := ⟨arrayOf, arrayOf⟩

/-- The model oracle: the toy KEM, the identity public key, an agreement that refuses the zero key,
and an AEAD open that refuses the empty ciphertext. -/
def oracleDecrypt (draws : List Model.Lifecycle.Key) : Model.Lifecycle.Oracle :=
  { draws
    braidKem := Model.Braid.toyKem
    dhPublic := id
    dhAgree := fun a b => if b = arrayOf zeros32 then none else some a
    identityValid := fun _ => true
    aeadSeal := fun _ _ _ _ _ => []
    aeadOpen := fun _ _ _ c _ => if c = [] then none else some []
    kemValid := fun _ => true
    kemEncaps := fun _ _ => none
    kemDecaps := fun _ _ => none
    sigVerify := fun _ _ _ => true
    sigSign := fun _ _ _ _ => [] }

theorem modelDecrypt_allT1 : AllT1Shapes Interp.modelDecrypt where
  dhCodec := ⟨fun _ => ⟨_, rfl⟩, fun _ => ⟨_, rfl⟩, fun _ => ⟨_, rfl⟩, fun _ => ⟨_, rfl⟩,
    fun _ => ⟨_, rfl⟩, fun _ _ => ⟨_, rfl⟩⟩
  dhIdentity := fun _ => ⟨_, rfl⟩
  dhAgree := fun _ _ => ⟨_, rfl⟩
  kemEncapsulate := modelT3_allT1.kemEncapsulate
  kemDecapsulate := modelT3_allT1.kemDecapsulate
  xeddsaVerify := fun _ _ _ => ⟨_, rfl⟩
  aeadOpen := fun _ _ _ _ _ => ⟨_, rfl⟩
  aeadSealBounded := modelT3_allT1.aeadSealBounded
  messageKeyMaterial := modelT3_allT1.messageKeyMaterial
  vecPop := modelT3_allT1.vecPop
  hkdf := modelT3_allT1.hkdf
  hmac := modelT3_allT1.hmac
  zeroizingTotal := modelT3_allT1.zeroizingTotal
  spqrZeroize := modelT3_allT1.spqrZeroize
  vecRetainAxiom := modelT3_allT1.vecRetainAxiom
  optionClone := modelT3_allT1.optionClone
  ct1Len := modelT3_allT1.ct1Len
  ct2Len := modelT3_allT1.ct2Len
  headerLen := modelT3_allT1.headerLen
  ekVectorLen := modelT3_allT1.ekVectorLen
  keyPairEkVector := modelT3_allT1.keyPairEkVector
  keyPairHeader := modelT3_allT1.keyPairHeader
  keyPairDecapsulate := modelT3_allT1.keyPairDecapsulate
  keyPairClone := modelT3_allT1.keyPairClone
  encapsStateClone := modelT3_allT1.encapsStateClone
  validateEk := modelT3_allT1.validateEk
  keyPairGenerate := modelT3_allT1.keyPairGenerate
  encapsulate1 := modelT3_allT1.encapsulate1
  encapsulate2 := modelT3_allT1.encapsulate2
  zeroizingArray := modelT3_allT1.zeroizingArray
  arrayZeroize := modelT3_allT1.arrayZeroize
  rangeFullIndex := modelT3_allT1.rangeFullIndex
  divCeilValue := modelT3_allT1.divCeilValue

theorem modelDecrypt_stdLaws : StdLaws Interp.modelDecrypt where
  pop := modelT3_stdLaws.pop
  asMut := modelT3_stdLaws.asMut
  blanketU32 := modelT3_stdLaws.blanketU32
  truncate := modelT3_stdLaws.truncate
  divCeil := modelT3_stdLaws.divCeil

theorem modelDecrypt_faithful : FaithfulShape Interp.modelDecrypt where
  pop_nil := model_Faithful.pop_nil
  pop_snoc := model_Faithful.pop_snoc
  truncate := model_Faithful.truncate
  divCeil := model_Faithful.divCeil
  asMut := model_Faithful.asMut
  capacity := model_Faithful.capacity

def modelDecrypt_zeroizingModel (Z : Type) : ZeroizingModelShape Interp.modelDecrypt Z where
  contents z := z
  new := (modelT3_zeroizingModel Z).new
  deref := (modelT3_zeroizingModel Z).deref
  deref_mut := (modelT3_zeroizingModel Z).deref_mut

theorem modelDecrypt_t3 : T3Agreements Interp.modelDecrypt Model.Braid.toyKem where
  kemLen := modelT3_t3.kemLen
  kemAgrees := modelT3_t3.kemAgrees
  validateEk := modelT3_t3.validateEk
  kemClone := modelT3_t3.kemClone
  hkdf := modelT3_t3.hkdf
  hmac := modelT3_t3.hmac

theorem modelDecrypt_truncatePrefix : TruncatePrefixShape Interp.modelDecrypt :=
  modelT3_truncatePrefix

theorem modelDecrypt_codec : DhCodecOfShape Interp.modelDecrypt viewDecrypt :=
  ⟨fun _ => ⟨_, rfl, rfl⟩, fun _ => ⟨_, rfl, rfl⟩, fun _ => ⟨_, rfl, rfl⟩⟩

theorem modelDecrypt_zeroize : ZeroizeRoundTripShapes Interp.modelDecrypt :=
  ⟨fun _ => ⟨fun _ => ⟨_, rfl, rfl⟩, fun _ => ⟨_, rfl⟩⟩,
    fun _ => ⟨fun _ => ⟨_, rfl, rfl⟩, fun _ => ⟨_, rfl⟩⟩,
    fun _ _ => ⟨_, rfl, rfl⟩, fun _ _ => ⟨_, rfl, rfl⟩, fun _ _ => ⟨_, rfl, rfl⟩⟩

theorem arrayOf_eq_zeros_iff (p : Array U8 32#usize) :
    arrayOf p = arrayOf zeros32 ↔ p.val = zeros32.val := by
  constructor
  · intro h
    exact congrArg Subtype.val (Tacenta.DispatchEvidenceVacuity.arrayOf_inj h)
  · intro h
    have : p = zeros32 := Subtype.ext h
    rw [this]

theorem modelDecrypt_oracle (draws : List Model.Lifecycle.Key) :
    DecryptOracleShape Interp.modelDecrypt viewDecrypt
      Tacenta.UnitLifecycleIntegrationScreen.byteRng
      Tacenta.UnitLifecycleIntegrationScreen.byteCrc
      Tacenta.UnitLifecycleIntegrationScreen.byteTrace (oracleDecrypt draws) := by
  refine ⟨fun k => ⟨k, rfl, rfl⟩, fun k p => ?_, fun k1 k2 iv c ad => ?_,
    Tacenta.UnitLifecycleIntegrationScreen.byte_random32Clause⟩
  · refine ⟨_, rfl, ?_⟩
    by_cases hp : p.val = zeros32.val
    · have hp' : arrayOf p = arrayOf zeros32 := (arrayOf_eq_zeros_iff p).mpr hp
      simp [Interp.modelDecrypt, oracleDecrypt, viewDecrypt, hp, hp']
    · have hp' : ¬ arrayOf p = arrayOf zeros32 := fun h => hp ((arrayOf_eq_zeros_iff p).mp h)
      simp [Interp.modelDecrypt, oracleDecrypt, viewDecrypt, hp, hp']
  · refine ⟨_, rfl, ?_⟩
    by_cases hc : c.val = []
    · simp [oracleDecrypt, hc, sliceOf, resultOptionOf]
    · simp [oracleDecrypt, hc, sliceOf, resultOptionOf, vecOf, alloc.vec.Vec.new]

/-- **The boundary hypotheses of `decrypt_ratchet_refines` that are about opaque constants have one
model.**  One interpretation of the unit's opaque constants, one DH view and one oracle meet,
together: every axiom-level shape of the session contract records, the laws `StdLaws`,
`FaithfulShape` and `TruncatePrefix`, the two model classes, the six Braid agreements at
`toyKem`, the five `zeroize` round trips, `DhCodecOf` and the four clauses of `DecryptOracleOf`
at the byte-stream source holding the draws of part A, with the oracle's KEM model `toyKem`; and in
it the agreement and the AEAD each refuse one input and accept another.  Both platform widths:
no proof chooses a width. -/
theorem decrypt_boundary_has_a_model :
    ∃ (I : Interp) (dh : DhViewShape I) (oracle : Model.Lifecycle.Oracle),
      AllT1Shapes I ∧ StdLaws I ∧ FaithfulShape I ∧ TruncatePrefixShape I ∧
      Nonempty (ZeroizingModelShape I SessionZ) ∧ Nonempty (ZeroizingModelShape I DerivedZ) ∧
      T3Agreements I Model.Braid.toyKem ∧ ZeroizeRoundTripShapes I ∧ DhCodecOfShape I dh ∧
      DecryptOracleShape I dh Tacenta.UnitLifecycleIntegrationScreen.byteRng
        Tacenta.UnitLifecycleIntegrationScreen.byteCrc
        Tacenta.UnitLifecycleIntegrationScreen.byteTrace oracle ∧
      oracle.braidKem = Model.Braid.toyKem ∧
      oracle.draws = Tacenta.UnitLifecycleIntegrationScreen.byteTrace sampleRng ∧
      (∃ k p, I.dhPrivAgree k p = ok none) ∧ (∃ k p r, I.dhPrivAgree k p = ok (some r)) ∧
      (∃ k1 k2 iv c ad e, I.aeadDecrypt k1 k2 iv c ad = ok (core.result.Result.Err e)) ∧
      (∃ k1 k2 iv c ad v, I.aeadDecrypt k1 k2 iv c ad = ok (core.result.Result.Ok v)) := by
  refine ⟨Interp.modelDecrypt, viewDecrypt,
    oracleDecrypt (Tacenta.UnitLifecycleIntegrationScreen.byteTrace sampleRng),
    modelDecrypt_allT1, modelDecrypt_stdLaws, modelDecrypt_faithful, modelDecrypt_truncatePrefix,
    ⟨modelDecrypt_zeroizingModel SessionZ⟩, ⟨modelDecrypt_zeroizingModel DerivedZ⟩, modelDecrypt_t3,
    modelDecrypt_zeroize, modelDecrypt_codec, modelDecrypt_oracle _, rfl, rfl,
    ⟨zeros32, zeros32, ?_⟩, ⟨zeros32, Array.repeat 32#usize 1#u8, zeros32, ?_⟩,
    ⟨zeros32, zeros32, Array.repeat 16#usize 0#u8, ⟨[], by simp⟩, ⟨[], by simp⟩, (), ?_⟩,
    ⟨zeros32, zeros32, Array.repeat 16#usize 0#u8,
      ⟨[0#u8], by simp; exact Tacenta.SessionUnitSessionT1.small_le_usize_max (by omega)⟩, ⟨[], by simp⟩,
      alloc.vec.Vec.new U8, ?_⟩⟩
  · simp [Interp.modelDecrypt]
  · simp [Interp.modelDecrypt, zeros32, Array.repeat]
  · simp [Interp.modelDecrypt]
  · simp only [Interp.modelDecrypt, ok.injEq, ite_eq_right_iff]
    intro h
    simp at h

/-! ## The theorem at the sample run

`decrypt_ratchet_refines` applied at part A's run: every per-run hypothesis is discharged by the
witnesses above, and only the boundary records remain, as arguments.  A hypothesis added to the
theorem that the witnesses do not give stops this module building. -/

theorem decrypt_ratchet_refines_at_sample (dh : DhView) (view : Model.Lifecycle.CodewordView)
    (oracle : Model.Lifecycle.Oracle)
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
        Tacenta.UnitLifecycleIntegrationScreen.byteCrc (sampleReal sk pk) sampleMessage sampleRng =
          ok output ∧
      (StepRefines Tacenta.UnitLifecycleIntegrationScreen.byteTrace dh oracle.braidKem output
          (Model.Lifecycle.decryptRatchet view oracle (modelOf dh (sampleReal sk pk))
            (sliceOf sampleMessage)) ∨
        TripleRefusalOpen output) := by
  obtain ⟨-, -, hrel, hroom, hrun⟩ := sample_run_satisfiable oracle.braidKem dh sk pk
  obtain ⟨htrace, run⟩ := hrun view oracle rfl hdraws
  exact decrypt_ratchet_refines _ _ _ dh view oracle oracleOf codec contracts agreements
    (sampleReal sk pk) (modelOf dh (sampleReal sk pk)) sampleMessage sampleRng hrel hroom htrace run

/-! ## C. The hypotheses at a run the model refuses and at one it accepts

Part A's run, with part B's oracle, is one at which the model refuses at the first agreement (the
composite carries the all-zero key, which that oracle's agreement refuses).  A second run, over a
Triple state that already holds a receiving chain on both sides, meets the same per-run hypotheses,
and there the model's step succeeds with that oracle: the Triple receive takes no eviction round
and the AEAD opens.  So the hypotheses are met at runs whose model step is a refusal and at runs
whose model step is a success; each holds at both platform widths (no proof chooses a width).  The
oracle clauses of the theorem hold of that oracle in part B's interpretation and not at the real
constants, so this shows the model side of each run, not which branch the shipped code takes. -/

theorem sample_model_refuses (dh : DhView) (view : Model.Lifecycle.CodewordView)
    (sk : tacenta_boundary.dh.PrivateKey) (pk : tacenta_boundary.dh.PublicKeyBytes) :
    (Model.Lifecycle.decryptRatchet view
      (oracleDecrypt (Tacenta.UnitLifecycleIntegrationScreen.byteTrace sampleRng))
      (modelOf dh (sampleReal sk pk)) (sliceOf sampleMessage)).result =
      .error (.handshake .nonContributoryAgreement) := by
  have hzero : sampleComposite.dh = arrayOf zeros32 := by
    simp [sampleComposite, arrayOf, zeros32, Array.repeat, Tacenta.SessionUnitBraidT3.u8]
  simp [Model.Lifecycle.decryptRatchet, Model.Lifecycle.agreementFailed, modelOf,
    sample_decode_model, oracleDecrypt, hzero]

def ones32 : Array U8 32#usize := Array.repeat 32#usize 1#u8

/-- A Triple state whose classical half already receives on the chain of `ones32` and whose sparse
half holds a receiving chain at epoch 0. -/
def succTriple : tacenta_triple.State :=
  { classical :=
      { dhs_pub := zeros32, dhr_pub := some ones32, rk := zeros32, cks := none,
        ckr := some zeros32, ns := 0#u32, nr := 0#u32, pn := 0#u32,
        skipped := Tacenta.UnitHeadroomSatisfiable.vecOf [] (by simp), events := 0#u32,
        labels := tacenta_ratchet.LabelSet.Tacenta },
    post_quantum :=
      { rk := zeros32, epoch := 0#u64,
        chains := Tacenta.UnitHeadroomSatisfiable.vecOf
          [(0#u64, { send := none, receive := some { ck := zeros32, n := 0#u64 } })] (by simp),
        skipped := Tacenta.UnitHeadroomSatisfiable.vecOf [] (by simp),
        direction := tacenta_spqr.Direction.A2b } }

def succReal (sk : tacenta_boundary.dh.PrivateKey) (pk : tacenta_boundary.dh.PublicKeyBytes) :
    lifecycle.Session :=
  { sampleReal sk pk with triple := succTriple }

/-- The first message on that chain, with a one-byte ciphertext. -/
def succComposite : Model.CompositeHeader.Composite :=
  { dh := List.replicate 32 1, pn := 0, n := 0, pqEpoch := 0, pqN := 1, agEpoch := 1,
    agType := .none, agChunk := none }

def succBytes : Bytes := Model.CompositeHeader.encode succComposite ++ [7]

theorem succBytes_le : succBytes.length ≤ Usize.max := by
  have h : succBytes.length = 103 := by decide
  rw [h]
  exact Tacenta.SessionUnitSessionT1.small_le_usize_max (by omega)

def succMessage : Slice U8 :=
  Tacenta.UnitSatisfiabilityBraidStates.sliceOfBytes succBytes succBytes_le

theorem succ_decode_model :
    Model.CompositeHeader.decodeDetailed (sliceOf succMessage) = .ok (succComposite, [7]) := by
  rw [show sliceOf succMessage = succBytes from
    Tacenta.UnitSatisfiabilityBraidStates.sliceOf_sliceOfBytes succBytes succBytes_le,
    Model.CompositeHeader.decodeDetailed_ok_iff]
  decide

theorem succ_model_accepts (dh : DhView) (view : Model.Lifecycle.CodewordView)
    (sk : tacenta_boundary.dh.PrivateKey) (pk : tacenta_boundary.dh.PublicKeyBytes) :
    ∃ plaintext, (Model.Lifecycle.decryptRatchet view
      (oracleDecrypt (Tacenta.UnitLifecycleIntegrationScreen.byteTrace sampleRng))
      (modelOf dh (succReal sk pk)) (sliceOf succMessage)).result = .ok plaintext := by
  simp [Model.Lifecycle.decryptRatchet, Model.Lifecycle.agreementFailed, modelOf, succReal,
    sampleReal, Tacenta.UnitHeadroomSatisfiable.sessionOf, succ_decode_model, oracleDecrypt,
    Model.Lifecycle.random32, Model.Lifecycle.takeDraw, sample_trace, Model.Braid.receive,
    Model.Lifecycle.sparseOutputOf, Model.Lifecycle.receiveWithEviction,
    Model.Triple.receiveDetailed, Model.Ratchet.receiveDetailed,
    Model.SparseRatchet.receiveDetailed, succTriple, succComposite, Model.Lifecycle.tripleHeaderOf,
    Tacenta.SessionUnitTripleT3.ratchetAbs, Tacenta.SessionUnitTripleT3.spqrAbs,
    Tacenta.UnitHeadroomSatisfiable.vecOf, Tacenta.SessionUnitT3.keyOf, ones32, zeros32,
    Array.repeat, Model.Ratchet.trySkipped, Model.Ratchet.skipMessageKeysDetailed,
    Model.State.skipMessageKeys, Model.SparseRatchet.maybeAdvanceReceiveDetailed,
    Model.SparseRatchet.maybeAdvanceDetailed, Model.SparseRatchet.trySkipped,
    Model.SparseRatchet.skipMessageKeysDetailed, Model.SparseRatchet.skipMessageKeys,
    Model.SparseRatchet.findChains, Tacenta.SessionUnitSpqrT3.chainsEntryOf,
    Tacenta.SessionUnitSpqrT3.chainsOf, Tacenta.SessionUnitSpqrT3.chainOf, Model.State.u32Max,
    Model.SparseRatchet.u64Max, Tacenta.SessionUnitT3.u8, arrayOf, Tacenta.SessionUnitBraidT3.u8,
    Tacenta.SessionUnitSpqrT3.keyOf]

theorem succ_decode_real :
    ∃ decoded, tacenta_wire.decode_message succMessage = ok (.Ok decoded) ∧
      CompositeRefines decoded.header succComposite := by
  obtain ⟨r, hr, hpost⟩ := Std.WP.spec_imp_exists (decode_message_refines_lifecycle succMessage)
  have hmodel : Model.CompositeHeader.decode (sliceOf succMessage) = some (succComposite, [7]) :=
    (Model.CompositeHeader.decodeDetailed_ok_iff _ _).mp succ_decode_model
  cases r with
  | Err e =>
      rw [hmodel] at hpost
      exact absurd hpost (by simp)
  | Ok decoded =>
      obtain ⟨mh, hdec, hrel⟩ := hpost
      rw [hmodel] at hdec
      have hmh : succComposite = mh := (Prod.mk.inj (Option.some.inj hdec)).1
      subst hmh
      exact ⟨decoded, hr, hrel⟩

theorem succ_headroom (sk : tacenta_boundary.dh.PrivateKey)
    (pk : tacenta_boundary.dh.PublicKeyBytes) :
    Tacenta.UnitLifecycleT1.DecryptRatchetHeadroom (succReal sk pk) := by
  have h4 := Tacenta.UnitHeadroomSatisfiable.usize_max_ge
  refine ⟨?_, Tacenta.UnitHeadroomSatisfiable.freshBraid_bounds.1,
    Tacenta.UnitHeadroomSatisfiable.freshBraid_bounds.2, ?_⟩
  · unfold Tacenta.UnitLifecycleT1.ReceiveHeadroom
    simp [succReal, succTriple, Tacenta.UnitHeadroomSatisfiable.vecOf,
      tacenta_ratchet.MAX_SKIPPED_STORE, tacenta_ratchet.MAX_SKIP, tacenta_spqr.MAX_SKIP]
    omega
  · simp [succReal, sampleReal, Tacenta.UnitHeadroomSatisfiable.sessionOf,
      Tacenta.UnitHeadroomSatisfiable.vecOf]
    omega

/-- **The second run meets every per-run hypothesis too**, with a message that decodes on both
sides. -/
theorem succ_run_satisfiable (K : Model.Braid.Kem) (dh : DhView)
    (sk : tacenta_boundary.dh.PrivateKey) (pk : tacenta_boundary.dh.PublicKeyBytes) :
    (∃ decoded, tacenta_wire.decode_message succMessage = ok (.Ok decoded)) ∧
    Model.CompositeHeader.decodeDetailed (sliceOf succMessage) = .ok (succComposite, [7]) ∧
    SessionRefines dh K (succReal sk pk) (modelOf dh (succReal sk pk)) ∧
    Tacenta.UnitLifecycleT1.DecryptRatchetHeadroom (succReal sk pk) ∧
    ∀ (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle),
      oracle.braidKem = K →
      oracle.draws = Tacenta.UnitLifecycleIntegrationScreen.byteTrace sampleRng →
      Tacenta.UnitLifecycleIntegrationScreen.byteTrace sampleRng = oracle.draws ∧
      DecryptRatchetRun view oracle Tacenta.UnitLifecycleIntegrationScreen.byteTrace
        (succReal sk pk) (modelOf dh (succReal sk pk)) succMessage sampleRng := by
  obtain ⟨decoded, hdec, _⟩ := succ_decode_real
  refine ⟨⟨decoded, hdec⟩, succ_decode_model,
    ⟨⟨rfl, rfl⟩, (Tacenta.UnitSatisfiabilityBraidStates.good_keysUnsampled (K := K)).1,
      rfl, rfl, rfl, rfl, rfl, rfl⟩, succ_headroom sk pk, ?_⟩
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
  · simp only [succReal, sampleReal, Tacenta.UnitHeadroomSatisfiable.sessionOf,
      Tacenta.UnitHeadroomSatisfiable.freshBraid, Tacenta.SessionUnitBraidT1.State.epoch_val]
    scalar_tac
  · intro modelComposite ciphertext hdecode
    rw [succ_decode_model] at hdecode
    have hmc : succComposite = modelComposite := (Prod.mk.inj (Except.ok.inj hdecode)).1
    subst hmc
    have hout : Model.Lifecycle.sparseOutputOf
        (Model.Braid.receive oracle.braidKem (modelOf dh (succReal sk pk)).braid
          (Model.Lifecycle.braidMessageOf view (modelOf dh (succReal sk pk)).braid
            succComposite)).2.1 = none := by
      simp [modelOf, Model.Braid.receive, Model.Lifecycle.sparseOutputOf]
    rw [hout]
    have hu := Tacenta.UnitHeadroomSatisfiable.usize_max_ge
    constructor <;>
      simp [modelOf, succReal, succTriple, Tacenta.UnitHeadroomSatisfiable.vecOf,
        Tacenta.SessionUnitTripleT3.ratchetAbs, Tacenta.SessionUnitTripleT3.spqrAbs,
        Model.State.maxSkippedStore, Model.SparseRatchet.maxSkippedStore,
        Model.SparseRatchet.epochsKept, U32.max_eq, U64.max_eq, cMax_usize,
        Tacenta.SessionUnitSpqrT3.chainsEntryOf, Tacenta.SessionUnitSpqrT3.chainsOf,
        Tacenta.SessionUnitSpqrT3.chainOf]
    all_goals omega

/-- **The hypotheses hold at a run whose model step refuses and at one whose model step
succeeds**, with part B's oracle, at both platform widths. -/
theorem hypotheses_meet_refusal_and_success (dh : DhView) (view : Model.Lifecycle.CodewordView)
    (sk : tacenta_boundary.dh.PrivateKey) (pk : tacenta_boundary.dh.PublicKeyBytes) :
    let oracle := oracleDecrypt (Tacenta.UnitLifecycleIntegrationScreen.byteTrace sampleRng)
    (SessionRefines dh oracle.braidKem (sampleReal sk pk) (modelOf dh (sampleReal sk pk)) ∧
      Tacenta.UnitLifecycleT1.DecryptRatchetHeadroom (sampleReal sk pk) ∧
      DecryptRatchetRun view oracle Tacenta.UnitLifecycleIntegrationScreen.byteTrace
        (sampleReal sk pk) (modelOf dh (sampleReal sk pk)) sampleMessage sampleRng ∧
      (Model.Lifecycle.decryptRatchet view oracle (modelOf dh (sampleReal sk pk))
        (sliceOf sampleMessage)).result = .error (.handshake .nonContributoryAgreement)) ∧
    (SessionRefines dh oracle.braidKem (succReal sk pk) (modelOf dh (succReal sk pk)) ∧
      Tacenta.UnitLifecycleT1.DecryptRatchetHeadroom (succReal sk pk) ∧
      DecryptRatchetRun view oracle Tacenta.UnitLifecycleIntegrationScreen.byteTrace
        (succReal sk pk) (modelOf dh (succReal sk pk)) succMessage sampleRng ∧
      ∃ plaintext, (Model.Lifecycle.decryptRatchet view oracle (modelOf dh (succReal sk pk))
        (sliceOf succMessage)).result = .ok plaintext) := by
  intro oracle
  obtain ⟨-, -, hrelA, hroomA, hrunA⟩ := sample_run_satisfiable oracle.braidKem dh sk pk
  obtain ⟨-, -, hrelB, hroomB, hrunB⟩ := succ_run_satisfiable oracle.braidKem dh sk pk
  exact ⟨⟨hrelA, hroomA, (hrunA view oracle rfl rfl).2, sample_model_refuses dh view sk pk⟩,
    ⟨hrelB, hroomB, (hrunB view oracle rfl rfl).2, succ_model_accepts dh view sk pk⟩⟩

end Tacenta.UnitLifecycleDecryptRatchetScreen

/-! ## Pins -/

/--
info: 'Tacenta.UnitLifecycleDecryptRatchetScreen.sample_run_satisfiable' depends on axioms: [propext,
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
#print axioms Tacenta.UnitLifecycleDecryptRatchetScreen.sample_run_satisfiable

/--
info: 'Tacenta.UnitLifecycleDecryptRatchetScreen.decrypt_boundary_has_a_model' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 rand_core_1.error.Error]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleDecryptRatchetScreen.decrypt_boundary_has_a_model

/--
info: 'Tacenta.UnitLifecycleDecryptRatchetScreen.decrypt_shapes_are_predicates' depends on axioms: [propext,
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
 tacenta_boundary.aead.encrypt,
 tacenta_boundary.dh.PrivateKey,
 tacenta_boundary.dh.PublicKeyBytes,
 tacenta_boundary.dh.is_prime_order_public,
 tacenta_boundary.kem.KeyPair,
 tacenta_boundary.kem.decapsulate,
 tacenta_boundary.kem.encapsulate,
 tacenta_boundary.xeddsa.verify,
 tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_kem.IncrementalKeyPair.generate,
 tacenta_kem.IncrementalKeyPair.header,
 zeroize.Zeroizing.new,
 Array.Insts.ZeroizeZeroize.zeroize,
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
 tacenta_kem.EncapsState.Insts.CoreCloneClone.clone,
 tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone,
 zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 core.option.Option.Insts.CoreCloneClone.clone,
 tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes.eq,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleDecryptRatchetScreen.decrypt_shapes_are_predicates

/--
info: 'Tacenta.UnitLifecycleDecryptRatchetScreen.run_draw_not_trivial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_kem.EncapsState,
 tacenta_kem.IncrementalKeyPair,
 tacenta_boundary.dh.PrivateKey,
 tacenta_boundary.dh.PublicKeyBytes,
 core.num.Usize.div_ceil]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleDecryptRatchetScreen.run_draw_not_trivial

/--
info: 'Tacenta.UnitLifecycleDecryptRatchetScreen.retryRunBounds_not_trivial' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleDecryptRatchetScreen.retryRunBounds_not_trivial

/--
info: 'Tacenta.UnitLifecycleDecryptRatchetScreen.tripleRefusalOpen_false_of_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_kem.EncapsState,
 tacenta_kem.IncrementalKeyPair,
 tacenta_boundary.dh.PrivateKey,
 tacenta_boundary.dh.PublicKeyBytes]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleDecryptRatchetScreen.tripleRefusalOpen_false_of_ok

/--
info: 'Tacenta.UnitLifecycleDecryptRatchetScreen.tripleRefusalOpen_false_of_store_full' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_kem.EncapsState,
 tacenta_kem.IncrementalKeyPair,
 tacenta_boundary.dh.PrivateKey,
 tacenta_boundary.dh.PublicKeyBytes]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleDecryptRatchetScreen.tripleRefusalOpen_false_of_store_full

/--
info: Tacenta.UnitLifecycleDecryptRatchetScreen.sample_run_satisfiable : ∀ (K : Model.Braid.Kem) (dh : DhView)
  (sk : tacenta_boundary.dh.PrivateKey) (pk : tacenta_boundary.dh.PublicKeyBytes),
  (∃ decoded,
      tacenta_wire.decode_message Tacenta.UnitLifecycleDecryptRatchetScreen.sampleMessage =
        ok (core.result.Result.Ok decoded)) ∧
    Model.CompositeHeader.decodeDetailed (sliceOf Tacenta.UnitLifecycleDecryptRatchetScreen.sampleMessage) =
        Except.ok (Tacenta.UnitLifecycleDecryptRatchetScreen.sampleComposite, []) ∧
      SessionRefines dh K (Tacenta.UnitLifecycleDecryptRatchetScreen.sampleReal sk pk)
          (Tacenta.UnitLifecycleDecryptRatchetScreen.modelOf dh
            (Tacenta.UnitLifecycleDecryptRatchetScreen.sampleReal sk pk)) ∧
        Tacenta.UnitLifecycleT1.DecryptRatchetHeadroom (Tacenta.UnitLifecycleDecryptRatchetScreen.sampleReal sk pk) ∧
          ∀ (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle),
            oracle.braidKem = K →
              oracle.draws =
                  Tacenta.UnitLifecycleIntegrationScreen.byteTrace Tacenta.UnitLifecycleDecryptRatchetScreen.sampleRng →
                Tacenta.UnitLifecycleIntegrationScreen.byteTrace Tacenta.UnitLifecycleDecryptRatchetScreen.sampleRng =
                    oracle.draws ∧
                  DecryptRatchetRun view oracle Tacenta.UnitLifecycleIntegrationScreen.byteTrace
                    (Tacenta.UnitLifecycleDecryptRatchetScreen.sampleReal sk pk)
                    (Tacenta.UnitLifecycleDecryptRatchetScreen.modelOf dh
                      (Tacenta.UnitLifecycleDecryptRatchetScreen.sampleReal sk pk))
                    Tacenta.UnitLifecycleDecryptRatchetScreen.sampleMessage
                    Tacenta.UnitLifecycleDecryptRatchetScreen.sampleRng
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptRatchetScreen.sample_run_satisfiable

/--
info: Tacenta.UnitLifecycleDecryptRatchetScreen.decrypt_boundary_has_a_model : ∃ I dh oracle,
  Tacenta.UnitSatisfiabilityBraidAgreements.AllT1Shapes I ∧
    Tacenta.UnitSatisfiabilityJoint.StdLaws I ∧
      Tacenta.UnitSatisfiabilityJoint.FaithfulShape I ∧
        Tacenta.UnitSatisfiabilityBraidAgreements.TruncatePrefixShape I ∧
          Nonempty (Tacenta.UnitSatisfiabilityJoint.ZeroizingModelShape I Tacenta.UnitSatisfiabilityJoint.SessionZ) ∧
            Nonempty (Tacenta.UnitSatisfiabilityJoint.ZeroizingModelShape I Tacenta.UnitSatisfiabilityJoint.DerivedZ) ∧
              Tacenta.UnitSatisfiabilityBraidAgreements.T3Agreements I Model.Braid.toyKem ∧
                Tacenta.UnitLifecycleDecryptRatchetScreen.ZeroizeRoundTripShapes I ∧
                  Tacenta.UnitLifecycleDecryptRatchetScreen.DhCodecOfShape I dh ∧
                    Tacenta.UnitLifecycleDecryptRatchetScreen.DecryptOracleShape I dh
                        Tacenta.UnitLifecycleIntegrationScreen.byteRng Tacenta.UnitLifecycleIntegrationScreen.byteCrc
                        Tacenta.UnitLifecycleIntegrationScreen.byteTrace oracle ∧
                      oracle.braidKem = Model.Braid.toyKem ∧
                        oracle.draws =
                            Tacenta.UnitLifecycleIntegrationScreen.byteTrace
                              Tacenta.UnitLifecycleDecryptRatchetScreen.sampleRng ∧
                          (∃ k p, I.dhPrivAgree k p = ok none) ∧
                            (∃ k p r, I.dhPrivAgree k p = ok (some r)) ∧
                              (∃ k1 k2 iv c ad e, I.aeadDecrypt k1 k2 iv c ad = ok (core.result.Result.Err e)) ∧
                                ∃ k1 k2 iv c ad v, I.aeadDecrypt k1 k2 iv c ad = ok (core.result.Result.Ok v)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptRatchetScreen.decrypt_boundary_has_a_model

/--
info: Tacenta.UnitLifecycleDecryptRatchetScreen.decrypt_shapes_are_predicates : (∀ (dh : DhView),
    DhCodecOf dh ↔
      Tacenta.UnitLifecycleDecryptRatchetScreen.DhCodecOfShape Tacenta.UnitSatisfiabilityJoint.Interp.real
        { privateKey := dh.privateKey, publicKey := dh.publicKey }) ∧
  (∀ {R : Type} (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R) (dh : DhView)
      (trace : R → List Model.Lifecycle.Key) (oracle : Model.Lifecycle.Oracle),
      DecryptOracleOf rc crc dh trace oracle ↔
        Tacenta.UnitLifecycleDecryptRatchetScreen.DecryptOracleShape Tacenta.UnitSatisfiabilityJoint.Interp.real
          { privateKey := dh.privateKey, publicKey := dh.publicKey } rc crc trace oracle) ∧
    (Tacenta.SessionUnitT3.ZeroizingRoundTrips ∧
        Tacenta.SessionUnitT3.ZeroizingRoundTrips80 ∧
          Tacenta.SessionUnitSpqrT3.ZeroizingRoundTrips96 ∧
            Tacenta.SessionUnitSpqrT3.ZeroizingRoundTrips64 ∧ ZeroizingRoundTrips (Std.Array U8 32#usize) ↔
      Tacenta.UnitLifecycleDecryptRatchetScreen.ZeroizeRoundTripShapes Tacenta.UnitSatisfiabilityJoint.Interp.real)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptRatchetScreen.decrypt_shapes_are_predicates

/--
info: @Tacenta.UnitLifecycleDecryptRatchetScreen.run_draw_not_trivial : ∀ {view : Model.Lifecycle.CodewordView}
  {oracle : Model.Lifecycle.Oracle} {real : lifecycle.Session} {model : Model.Lifecycle.Session} {message : Slice U8},
  ¬DecryptRatchetRun view oracle Tacenta.UnitLifecycleIntegrationScreen.byteTrace real model message []
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptRatchetScreen.run_draw_not_trivial

/--
info: Tacenta.UnitLifecycleDecryptRatchetScreen.retryRunBounds_not_trivial : ∀ (state : Model.Triple.State)
  (header : Model.Triple.Header) (output : Option Model.SparseRatchet.Output),
  ¬RetryRunBounds
        { classical := state.classical,
          postQuantum :=
            have __src := state.postQuantum;
            { rk := __src.rk, epoch := U64.max, chains := __src.chains, skipped := __src.skipped,
              direction := __src.direction } }
        header output ∧
    ∀ (entries : List Model.Ratchet.SkippedEntry),
      4294967295 - 1999 ≤ entries.length →
        ¬RetryRunBounds
            {
              classical :=
                have __src := state.classical;
                { dhsPub := __src.dhsPub, dhrPub := __src.dhrPub, rk := __src.rk, cks := __src.cks, ckr := __src.ckr,
                  ns := __src.ns, nr := __src.nr, pn := __src.pn, skipped := entries, events := __src.events,
                  labels := __src.labels },
              postQuantum := state.postQuantum }
            header output
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptRatchetScreen.retryRunBounds_not_trivial

/--
info: @Tacenta.UnitLifecycleDecryptRatchetScreen.tripleRefusalOpen_false_of_ok : ∀ {R : Type} (plaintext : alloc.vec.Vec U8)
  (session : lifecycle.Session) (rng : R), ¬TripleRefusalOpen (core.result.Result.Ok plaintext, session, rng)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptRatchetScreen.tripleRefusalOpen_false_of_ok

/--
info: @Tacenta.UnitLifecycleDecryptRatchetScreen.tripleRefusalOpen_false_of_store_full : ∀ {R : Type}
  (session : lifecycle.Session) (rng : R),
  ¬TripleRefusalOpen
        (core.result.Result.Err
            (lifecycle.Error.Triple
              (tacenta_triple.TripleError.Classical tacenta_ratchet.RatchetError.SkippedStoreFull)),
          session, rng) ∧
    ¬TripleRefusalOpen
        (core.result.Result.Err
            (lifecycle.Error.Triple (tacenta_triple.TripleError.PostQuantum tacenta_spqr.SpqrError.SkippedStoreFull)),
          session, rng)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptRatchetScreen.tripleRefusalOpen_false_of_store_full

/--
info: def Tacenta.UnitLifecycleDecryptRatchetScreen.sampleComposite : Model.CompositeHeader.Composite :=
{ dh := List.replicate 32 0, pn := 0, n := 1, pqEpoch := 0, pqN := 1, agEpoch := 1,
  agType := Model.CompositeHeader.AgreementType.none, agChunk := none }
-/
#guard_msgs in
#print Tacenta.UnitLifecycleDecryptRatchetScreen.sampleComposite

/--
info: def Tacenta.UnitLifecycleDecryptRatchetScreen.sampleReal : tacenta_boundary.dh.PrivateKey →
  tacenta_boundary.dh.PublicKeyBytes → lifecycle.Session :=
fun sk pk =>
  Tacenta.UnitHeadroomSatisfiable.sessionOf sk pk pk
    (Tacenta.UnitHeadroomSatisfiable.vecOf [] Tacenta.UnitLifecycleDecryptRatchetScreen.sampleReal._proof_1)
    (Array.repeat 32#usize 0#u8) none
-/
#guard_msgs in
#print Tacenta.UnitLifecycleDecryptRatchetScreen.sampleReal

/--
info: def Tacenta.UnitLifecycleDecryptRatchetScreen.modelOf : DhView → lifecycle.Session → Model.Lifecycle.Session :=
fun dh real =>
  {
    triple :=
      { classical := Tacenta.SessionUnitTripleT3.ratchetAbs real.triple.classical,
        postQuantum := Tacenta.SessionUnitTripleT3.spqrAbs real.triple.post_quantum },
    braid := Model.Braid.BraidState.keysUnsampled 1 Tacenta.UnitSatisfiabilityBraidStates.modelAuth0,
    ratchetPrivate := dh.privateKey real.ratchet_private, identityAd := vecOf real.identity_ad,
    ourIdentityPublic := dh.publicKey real.our_identity_public,
    peerIdentityPublic := dh.publicKey real.peer_identity_public,
    pendingInitial := Option.map (pendingInitialOf dh) real.pending_initial,
    establishedEphemeral := Option.map vecOf real.established_ephemeral }
-/
#guard_msgs in
#print Tacenta.UnitLifecycleDecryptRatchetScreen.modelOf

/--
info: def Tacenta.UnitLifecycleDecryptRatchetScreen.sampleRng : List U8 :=
List.replicate 32 0#u8
-/
#guard_msgs in
#print Tacenta.UnitLifecycleDecryptRatchetScreen.sampleRng

/--
info: structure Tacenta.UnitLifecycleDecryptRatchetScreen.DhCodecOfShape (I : Tacenta.UnitSatisfiabilityJoint.Interp)
  (dh : Tacenta.UnitLifecycleDecryptRatchetScreen.DhViewShape I) : Prop
number of parameters: 2
fields:
  Tacenta.UnitLifecycleDecryptRatchetScreen.DhCodecOfShape.privateFromBytes : ∀ (bytes : Std.Array U8 32#usize),
      ∃ privateKey, I.dhPrivFromBytes bytes = ok privateKey ∧ dh.privateKey privateKey = arrayOf bytes
  Tacenta.UnitLifecycleDecryptRatchetScreen.DhCodecOfShape.fromBytes : ∀ (bytes : Std.Array U8 32#usize),
      ∃ publicKey, I.dhPubFromBytes bytes = ok publicKey ∧ dh.publicKey publicKey = arrayOf bytes
  Tacenta.UnitLifecycleDecryptRatchetScreen.DhCodecOfShape.asBytes : ∀ (publicKey : I.PublicKeyBytes),
      ∃ bytes, I.dhPubAsBytes publicKey = ok bytes ∧ arrayOf bytes = dh.publicKey publicKey
constructor:
  Tacenta.UnitLifecycleDecryptRatchetScreen.DhCodecOfShape.mk {I : Tacenta.UnitSatisfiabilityJoint.Interp}
    {dh : Tacenta.UnitLifecycleDecryptRatchetScreen.DhViewShape I}
    (privateFromBytes :
      ∀ (bytes : Std.Array U8 32#usize),
        ∃ privateKey, I.dhPrivFromBytes bytes = ok privateKey ∧ dh.privateKey privateKey = arrayOf bytes)
    (fromBytes :
      ∀ (bytes : Std.Array U8 32#usize),
        ∃ publicKey, I.dhPubFromBytes bytes = ok publicKey ∧ dh.publicKey publicKey = arrayOf bytes)
    (asBytes :
      ∀ (publicKey : I.PublicKeyBytes),
        ∃ bytes, I.dhPubAsBytes publicKey = ok bytes ∧ arrayOf bytes = dh.publicKey publicKey) :
    Tacenta.UnitLifecycleDecryptRatchetScreen.DhCodecOfShape I dh
-/
#guard_msgs in
#print Tacenta.UnitLifecycleDecryptRatchetScreen.DhCodecOfShape

/--
info: structure Tacenta.UnitLifecycleDecryptRatchetScreen.DecryptOracleShape (I : Tacenta.UnitSatisfiabilityJoint.Interp)
  (dh : Tacenta.UnitLifecycleDecryptRatchetScreen.DhViewShape I) {R : Type} (rngCore : rand_core_1.RngCore R)
  (cryptoRng : rand_core_1.CryptoRng R) (trace : R → List Model.Lifecycle.Key) (oracle : Model.Lifecycle.Oracle) : Prop
number of parameters: 7
fields:
  Tacenta.UnitLifecycleDecryptRatchetScreen.DecryptOracleShape.dhPublic : ∀ (secret : I.PrivateKey),
      ∃ publicKey,
        I.dhPrivPublicKey secret = ok publicKey ∧ dh.publicKey publicKey = oracle.dhPublic (dh.privateKey secret)
  Tacenta.UnitLifecycleDecryptRatchetScreen.DecryptOracleShape.dhAgree : ∀ (secret : I.PrivateKey)
      (publicKey : I.PublicKeyBytes),
      ∃ result,
        I.dhPrivAgree secret publicKey = ok result ∧
          Option.map arrayOf result = oracle.dhAgree (dh.privateKey secret) (dh.publicKey publicKey)
  Tacenta.UnitLifecycleDecryptRatchetScreen.DecryptOracleShape.aeadOpen : ∀ (key1 key2 : Std.Array U8 32#usize)
      (iv : Std.Array U8 16#usize) (ciphertext associatedData : Slice U8),
      ∃ result,
        I.aeadDecrypt key1 key2 iv ciphertext associatedData = ok result ∧
          resultOptionOf vecOf result =
            oracle.aeadOpen (arrayOf key1) (arrayOf key2) (arrayOf iv) (sliceOf ciphertext) (sliceOf associatedData)
  Tacenta.UnitLifecycleDecryptRatchetScreen.DecryptOracleShape.random32 : ∀ (rng : R) (draw : Model.Lifecycle.Key)
      (rest : List Model.Lifecycle.Key),
      trace rng = draw :: rest →
        ∃ value rng',
          lifecycle.random_secret rngCore cryptoRng rng = ok (value, rng') ∧ arrayOf value = draw ∧ trace rng' = rest
constructor:
  Tacenta.UnitLifecycleDecryptRatchetScreen.DecryptOracleShape.mk {I : Tacenta.UnitSatisfiabilityJoint.Interp}
    {dh : Tacenta.UnitLifecycleDecryptRatchetScreen.DhViewShape I} {R : Type} {rngCore : rand_core_1.RngCore R}
    {cryptoRng : rand_core_1.CryptoRng R} {trace : R → List Model.Lifecycle.Key} {oracle : Model.Lifecycle.Oracle}
    (dhPublic :
      ∀ (secret : I.PrivateKey),
        ∃ publicKey,
          I.dhPrivPublicKey secret = ok publicKey ∧ dh.publicKey publicKey = oracle.dhPublic (dh.privateKey secret))
    (dhAgree :
      ∀ (secret : I.PrivateKey) (publicKey : I.PublicKeyBytes),
        ∃ result,
          I.dhPrivAgree secret publicKey = ok result ∧
            Option.map arrayOf result = oracle.dhAgree (dh.privateKey secret) (dh.publicKey publicKey))
    (aeadOpen :
      ∀ (key1 key2 : Std.Array U8 32#usize) (iv : Std.Array U8 16#usize) (ciphertext associatedData : Slice U8),
        ∃ result,
          I.aeadDecrypt key1 key2 iv ciphertext associatedData = ok result ∧
            resultOptionOf vecOf result =
              oracle.aeadOpen (arrayOf key1) (arrayOf key2) (arrayOf iv) (sliceOf ciphertext) (sliceOf associatedData))
    (random32 :
      ∀ (rng : R) (draw : Model.Lifecycle.Key) (rest : List Model.Lifecycle.Key),
        trace rng = draw :: rest →
          ∃ value rng',
            lifecycle.random_secret rngCore cryptoRng rng = ok (value, rng') ∧
              arrayOf value = draw ∧ trace rng' = rest) :
    Tacenta.UnitLifecycleDecryptRatchetScreen.DecryptOracleShape I dh rngCore cryptoRng trace oracle
-/
#guard_msgs in
#print Tacenta.UnitLifecycleDecryptRatchetScreen.DecryptOracleShape

/--
info: structure Tacenta.UnitLifecycleDecryptRatchetScreen.ZeroizeRoundTripShapes
  (I : Tacenta.UnitSatisfiabilityJoint.Interp) : Prop
number of parameters: 1
fields:
  Tacenta.UnitLifecycleDecryptRatchetScreen.ZeroizeRoundTripShapes.w64 : ∀
      (inst : zeroize.Zeroize (Std.Array U8 64#usize)),
      (∀ (z : Std.Array U8 64#usize), ∃ w, I.zNew inst z = ok w ∧ I.zDeref inst w = ok z) ∧
        ∀ (w : I.Zeroizing (Std.Array U8 64#usize)), ∃ z, I.zDeref inst w = ok z
  Tacenta.UnitLifecycleDecryptRatchetScreen.ZeroizeRoundTripShapes.w80 : ∀
      (inst : zeroize.Zeroize (Std.Array U8 80#usize)),
      (∀ (z : Std.Array U8 80#usize), ∃ w, I.zNew inst z = ok w ∧ I.zDeref inst w = ok z) ∧
        ∀ (w : I.Zeroizing (Std.Array U8 80#usize)), ∃ z, I.zDeref inst w = ok z
  Tacenta.UnitLifecycleDecryptRatchetScreen.ZeroizeRoundTripShapes.w96 : ∀
      (inst : zeroize.Zeroize (Std.Array U8 96#usize)) (z : Std.Array U8 96#usize),
      ∃ w, I.zNew inst z = ok w ∧ I.zDeref inst w = ok z
  Tacenta.UnitLifecycleDecryptRatchetScreen.ZeroizeRoundTripShapes.w64Sparse : ∀
      (inst : zeroize.Zeroize (Std.Array U8 64#usize)) (z : Std.Array U8 64#usize),
      ∃ w, I.zNew inst z = ok w ∧ I.zDeref inst w = ok z
  Tacenta.UnitLifecycleDecryptRatchetScreen.ZeroizeRoundTripShapes.w32 : ∀
      (inst : zeroize.Zeroize (Std.Array U8 32#usize)) (value : Std.Array U8 32#usize),
      ∃ wrapped, I.zNew inst value = ok wrapped ∧ I.zDeref inst wrapped = ok value
constructor:
  Tacenta.UnitLifecycleDecryptRatchetScreen.ZeroizeRoundTripShapes.mk {I : Tacenta.UnitSatisfiabilityJoint.Interp}
    (w64 :
      ∀ (inst : zeroize.Zeroize (Std.Array U8 64#usize)),
        (∀ (z : Std.Array U8 64#usize), ∃ w, I.zNew inst z = ok w ∧ I.zDeref inst w = ok z) ∧
          ∀ (w : I.Zeroizing (Std.Array U8 64#usize)), ∃ z, I.zDeref inst w = ok z)
    (w80 :
      ∀ (inst : zeroize.Zeroize (Std.Array U8 80#usize)),
        (∀ (z : Std.Array U8 80#usize), ∃ w, I.zNew inst z = ok w ∧ I.zDeref inst w = ok z) ∧
          ∀ (w : I.Zeroizing (Std.Array U8 80#usize)), ∃ z, I.zDeref inst w = ok z)
    (w96 :
      ∀ (inst : zeroize.Zeroize (Std.Array U8 96#usize)) (z : Std.Array U8 96#usize),
        ∃ w, I.zNew inst z = ok w ∧ I.zDeref inst w = ok z)
    (w64Sparse :
      ∀ (inst : zeroize.Zeroize (Std.Array U8 64#usize)) (z : Std.Array U8 64#usize),
        ∃ w, I.zNew inst z = ok w ∧ I.zDeref inst w = ok z)
    (w32 :
      ∀ (inst : zeroize.Zeroize (Std.Array U8 32#usize)) (value : Std.Array U8 32#usize),
        ∃ wrapped, I.zNew inst value = ok wrapped ∧ I.zDeref inst wrapped = ok value) :
    Tacenta.UnitLifecycleDecryptRatchetScreen.ZeroizeRoundTripShapes I
-/
#guard_msgs in
#print Tacenta.UnitLifecycleDecryptRatchetScreen.ZeroizeRoundTripShapes

/--
info: 'Tacenta.UnitLifecycleDecryptRatchetScreen.decrypt_ratchet_refines_at_sample' depends on axioms: [propext,
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
#print axioms Tacenta.UnitLifecycleDecryptRatchetScreen.decrypt_ratchet_refines_at_sample

/--
info: Tacenta.UnitLifecycleDecryptRatchetScreen.decrypt_ratchet_refines_at_sample : ∀ (dh : DhView)
  (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle),
  oracle.draws = Tacenta.UnitLifecycleIntegrationScreen.byteTrace Tacenta.UnitLifecycleDecryptRatchetScreen.sampleRng →
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
                        (Tacenta.UnitLifecycleDecryptRatchetScreen.sampleReal sk pk)
                        Tacenta.UnitLifecycleDecryptRatchetScreen.sampleMessage
                        Tacenta.UnitLifecycleDecryptRatchetScreen.sampleRng =
                      ok output ∧
                    (StepRefines Tacenta.UnitLifecycleIntegrationScreen.byteTrace dh oracle.braidKem output
                        (Model.Lifecycle.decryptRatchet view oracle
                          (Tacenta.UnitLifecycleDecryptRatchetScreen.modelOf dh
                            (Tacenta.UnitLifecycleDecryptRatchetScreen.sampleReal sk pk))
                          (sliceOf Tacenta.UnitLifecycleDecryptRatchetScreen.sampleMessage)) ∨
                      TripleRefusalOpen output)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptRatchetScreen.decrypt_ratchet_refines_at_sample

/--
info: 'Tacenta.UnitLifecycleDecryptRatchetScreen.sample_model_refuses' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_kem.EncapsState,
 tacenta_kem.IncrementalKeyPair,
 tacenta_boundary.dh.PrivateKey,
 tacenta_boundary.dh.PublicKeyBytes]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleDecryptRatchetScreen.sample_model_refuses

/--
info: 'Tacenta.UnitLifecycleDecryptRatchetScreen.succ_model_accepts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_kem.EncapsState,
 tacenta_kem.IncrementalKeyPair,
 tacenta_boundary.dh.PrivateKey,
 tacenta_boundary.dh.PublicKeyBytes]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleDecryptRatchetScreen.succ_model_accepts

/--
info: 'Tacenta.UnitLifecycleDecryptRatchetScreen.succ_run_satisfiable' depends on axioms: [propext,
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
#print axioms Tacenta.UnitLifecycleDecryptRatchetScreen.succ_run_satisfiable

/--
info: 'Tacenta.UnitLifecycleDecryptRatchetScreen.hypotheses_meet_refusal_and_success' depends on axioms: [propext,
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
#print axioms Tacenta.UnitLifecycleDecryptRatchetScreen.hypotheses_meet_refusal_and_success

/--
info: Tacenta.UnitLifecycleDecryptRatchetScreen.sample_model_refuses : ∀ (dh : DhView) (view : Model.Lifecycle.CodewordView)
  (sk : tacenta_boundary.dh.PrivateKey) (pk : tacenta_boundary.dh.PublicKeyBytes),
  (Model.Lifecycle.decryptRatchet view
        (Tacenta.UnitLifecycleDecryptRatchetScreen.oracleDecrypt
          (Tacenta.UnitLifecycleIntegrationScreen.byteTrace Tacenta.UnitLifecycleDecryptRatchetScreen.sampleRng))
        (Tacenta.UnitLifecycleDecryptRatchetScreen.modelOf dh
          (Tacenta.UnitLifecycleDecryptRatchetScreen.sampleReal sk pk))
        (sliceOf Tacenta.UnitLifecycleDecryptRatchetScreen.sampleMessage)).result =
    Except.error (Model.Lifecycle.Refusal.handshake Model.Lifecycle.HandshakeRefusal.nonContributoryAgreement)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptRatchetScreen.sample_model_refuses

/--
info: Tacenta.UnitLifecycleDecryptRatchetScreen.succ_model_accepts : ∀ (dh : DhView) (view : Model.Lifecycle.CodewordView)
  (sk : tacenta_boundary.dh.PrivateKey) (pk : tacenta_boundary.dh.PublicKeyBytes),
  ∃ plaintext,
    (Model.Lifecycle.decryptRatchet view
          (Tacenta.UnitLifecycleDecryptRatchetScreen.oracleDecrypt
            (Tacenta.UnitLifecycleIntegrationScreen.byteTrace Tacenta.UnitLifecycleDecryptRatchetScreen.sampleRng))
          (Tacenta.UnitLifecycleDecryptRatchetScreen.modelOf dh
            (Tacenta.UnitLifecycleDecryptRatchetScreen.succReal sk pk))
          (sliceOf Tacenta.UnitLifecycleDecryptRatchetScreen.succMessage)).result =
      Except.ok plaintext
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptRatchetScreen.succ_model_accepts

/--
info: Tacenta.UnitLifecycleDecryptRatchetScreen.succ_run_satisfiable : ∀ (K : Model.Braid.Kem) (dh : DhView)
  (sk : tacenta_boundary.dh.PrivateKey) (pk : tacenta_boundary.dh.PublicKeyBytes),
  (∃ decoded,
      tacenta_wire.decode_message Tacenta.UnitLifecycleDecryptRatchetScreen.succMessage =
        ok (core.result.Result.Ok decoded)) ∧
    Model.CompositeHeader.decodeDetailed (sliceOf Tacenta.UnitLifecycleDecryptRatchetScreen.succMessage) =
        Except.ok (Tacenta.UnitLifecycleDecryptRatchetScreen.succComposite, [7]) ∧
      SessionRefines dh K (Tacenta.UnitLifecycleDecryptRatchetScreen.succReal sk pk)
          (Tacenta.UnitLifecycleDecryptRatchetScreen.modelOf dh
            (Tacenta.UnitLifecycleDecryptRatchetScreen.succReal sk pk)) ∧
        Tacenta.UnitLifecycleT1.DecryptRatchetHeadroom (Tacenta.UnitLifecycleDecryptRatchetScreen.succReal sk pk) ∧
          ∀ (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle),
            oracle.braidKem = K →
              oracle.draws =
                  Tacenta.UnitLifecycleIntegrationScreen.byteTrace Tacenta.UnitLifecycleDecryptRatchetScreen.sampleRng →
                Tacenta.UnitLifecycleIntegrationScreen.byteTrace Tacenta.UnitLifecycleDecryptRatchetScreen.sampleRng =
                    oracle.draws ∧
                  DecryptRatchetRun view oracle Tacenta.UnitLifecycleIntegrationScreen.byteTrace
                    (Tacenta.UnitLifecycleDecryptRatchetScreen.succReal sk pk)
                    (Tacenta.UnitLifecycleDecryptRatchetScreen.modelOf dh
                      (Tacenta.UnitLifecycleDecryptRatchetScreen.succReal sk pk))
                    Tacenta.UnitLifecycleDecryptRatchetScreen.succMessage
                    Tacenta.UnitLifecycleDecryptRatchetScreen.sampleRng
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptRatchetScreen.succ_run_satisfiable

/--
info: Tacenta.UnitLifecycleDecryptRatchetScreen.hypotheses_meet_refusal_and_success : ∀ (dh : DhView)
  (view : Model.Lifecycle.CodewordView) (sk : tacenta_boundary.dh.PrivateKey) (pk : tacenta_boundary.dh.PublicKeyBytes),
  have oracle :=
    Tacenta.UnitLifecycleDecryptRatchetScreen.oracleDecrypt
      (Tacenta.UnitLifecycleIntegrationScreen.byteTrace Tacenta.UnitLifecycleDecryptRatchetScreen.sampleRng);
  (SessionRefines dh oracle.braidKem (Tacenta.UnitLifecycleDecryptRatchetScreen.sampleReal sk pk)
        (Tacenta.UnitLifecycleDecryptRatchetScreen.modelOf dh
          (Tacenta.UnitLifecycleDecryptRatchetScreen.sampleReal sk pk)) ∧
      Tacenta.UnitLifecycleT1.DecryptRatchetHeadroom (Tacenta.UnitLifecycleDecryptRatchetScreen.sampleReal sk pk) ∧
        DecryptRatchetRun view oracle Tacenta.UnitLifecycleIntegrationScreen.byteTrace
            (Tacenta.UnitLifecycleDecryptRatchetScreen.sampleReal sk pk)
            (Tacenta.UnitLifecycleDecryptRatchetScreen.modelOf dh
              (Tacenta.UnitLifecycleDecryptRatchetScreen.sampleReal sk pk))
            Tacenta.UnitLifecycleDecryptRatchetScreen.sampleMessage
            Tacenta.UnitLifecycleDecryptRatchetScreen.sampleRng ∧
          (Model.Lifecycle.decryptRatchet view oracle
                (Tacenta.UnitLifecycleDecryptRatchetScreen.modelOf dh
                  (Tacenta.UnitLifecycleDecryptRatchetScreen.sampleReal sk pk))
                (sliceOf Tacenta.UnitLifecycleDecryptRatchetScreen.sampleMessage)).result =
            Except.error
              (Model.Lifecycle.Refusal.handshake Model.Lifecycle.HandshakeRefusal.nonContributoryAgreement)) ∧
    SessionRefines dh oracle.braidKem (Tacenta.UnitLifecycleDecryptRatchetScreen.succReal sk pk)
        (Tacenta.UnitLifecycleDecryptRatchetScreen.modelOf dh
          (Tacenta.UnitLifecycleDecryptRatchetScreen.succReal sk pk)) ∧
      Tacenta.UnitLifecycleT1.DecryptRatchetHeadroom (Tacenta.UnitLifecycleDecryptRatchetScreen.succReal sk pk) ∧
        DecryptRatchetRun view oracle Tacenta.UnitLifecycleIntegrationScreen.byteTrace
            (Tacenta.UnitLifecycleDecryptRatchetScreen.succReal sk pk)
            (Tacenta.UnitLifecycleDecryptRatchetScreen.modelOf dh
              (Tacenta.UnitLifecycleDecryptRatchetScreen.succReal sk pk))
            Tacenta.UnitLifecycleDecryptRatchetScreen.succMessage Tacenta.UnitLifecycleDecryptRatchetScreen.sampleRng ∧
          ∃ plaintext,
            (Model.Lifecycle.decryptRatchet view oracle
                  (Tacenta.UnitLifecycleDecryptRatchetScreen.modelOf dh
                    (Tacenta.UnitLifecycleDecryptRatchetScreen.succReal sk pk))
                  (sliceOf Tacenta.UnitLifecycleDecryptRatchetScreen.succMessage)).result =
              Except.ok plaintext
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptRatchetScreen.hypotheses_meet_refusal_and_success

/--
info: def Tacenta.UnitLifecycleDecryptRatchetScreen.succTriple : tacenta_triple.State :=
{
  classical :=
    { dhs_pub := Tacenta.UnitLifecycleDecryptRatchetScreen.zeros32,
      dhr_pub := some Tacenta.UnitLifecycleDecryptRatchetScreen.ones32,
      rk := Tacenta.UnitLifecycleDecryptRatchetScreen.zeros32, cks := none,
      ckr := some Tacenta.UnitLifecycleDecryptRatchetScreen.zeros32, ns := 0#u32, nr := 0#u32, pn := 0#u32,
      skipped := Tacenta.UnitHeadroomSatisfiable.vecOf [] Tacenta.UnitLifecycleDecryptRatchetScreen.sampleReal._proof_1,
      events := 0#u32, labels := tacenta_ratchet.LabelSet.Tacenta },
  post_quantum :=
    { rk := Tacenta.UnitLifecycleDecryptRatchetScreen.zeros32, epoch := 0#u64,
      chains :=
        Tacenta.UnitHeadroomSatisfiable.vecOf
          [(0#u64,
              { send := none,
                receive := some { ck := Tacenta.UnitLifecycleDecryptRatchetScreen.zeros32, n := 0#u64 } })]
          Tacenta.UnitLifecycleDecryptRatchetScreen.succTriple._proof_3,
      skipped := Tacenta.UnitHeadroomSatisfiable.vecOf [] Tacenta.UnitLifecycleDecryptRatchetScreen.sampleReal._proof_1,
      direction := tacenta_spqr.Direction.A2b } }
-/
#guard_msgs in
#print Tacenta.UnitLifecycleDecryptRatchetScreen.succTriple

/--
info: def Tacenta.UnitLifecycleDecryptRatchetScreen.succReal : tacenta_boundary.dh.PrivateKey →
  tacenta_boundary.dh.PublicKeyBytes → lifecycle.Session :=
fun sk pk =>
  have __src := Tacenta.UnitLifecycleDecryptRatchetScreen.sampleReal sk pk;
  { triple := Tacenta.UnitLifecycleDecryptRatchetScreen.succTriple, braid := __src.braid,
    ratchet_private := __src.ratchet_private, identity_ad := __src.identity_ad,
    our_identity_public := __src.our_identity_public, peer_identity_public := __src.peer_identity_public,
    pending_initial := __src.pending_initial, established_ephemeral := __src.established_ephemeral }
-/
#guard_msgs in
#print Tacenta.UnitLifecycleDecryptRatchetScreen.succReal

/--
info: def Tacenta.UnitLifecycleDecryptRatchetScreen.succComposite : Model.CompositeHeader.Composite :=
{ dh := List.replicate 32 1, pn := 0, n := 0, pqEpoch := 0, pqN := 1, agEpoch := 1,
  agType := Model.CompositeHeader.AgreementType.none, agChunk := none }
-/
#guard_msgs in
#print Tacenta.UnitLifecycleDecryptRatchetScreen.succComposite

/--
info: def Tacenta.UnitLifecycleDecryptRatchetScreen.succBytes : Bytes :=
Model.CompositeHeader.encode Tacenta.UnitLifecycleDecryptRatchetScreen.succComposite ++ [7]
-/
#guard_msgs in
#print Tacenta.UnitLifecycleDecryptRatchetScreen.succBytes

/--
info: def Tacenta.UnitLifecycleDecryptRatchetScreen.oracleDecrypt : List Model.Lifecycle.Key → Model.Lifecycle.Oracle :=
fun draws =>
  { draws := draws, braidKem := Model.Braid.toyKem, dhPublic := id,
    dhAgree := fun a b => if b = arrayOf Tacenta.UnitLifecycleDecryptRatchetScreen.zeros32 then none else some a,
    identityValid := fun x => true, aeadSeal := fun x x_1 x_2 x_3 x_4 => [],
    aeadOpen := fun x x_1 x_2 c x_3 => if c = [] then none else some [], kemValid := fun x => true,
    kemEncaps := fun x x_1 => none, kemDecaps := fun x x_1 => none, sigVerify := fun x x_1 x_2 => true,
    sigSign := fun x x_1 x_2 x_3 => [] }
-/
#guard_msgs in
#print Tacenta.UnitLifecycleDecryptRatchetScreen.oracleDecrypt
