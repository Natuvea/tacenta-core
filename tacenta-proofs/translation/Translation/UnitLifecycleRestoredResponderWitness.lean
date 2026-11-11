import Translation.UnitLifecycleRestoredResponder
import Translation.UnitLifecycleResponderReply
import Translation.UnitLifecycleInitiatorSecondSend

/-!
# A successful encrypt of the empty plaintext, last-resort path, from the restored responder session

The witness below retains the existing reach's primitive and codec laws. It is a
conditional consistency result, not realization of those laws by shipping code.
In particular, it does not repair `AEAD-LENGTH-CONTRACTS`.

The session, saved bytes, imported session, encrypt hypothesis record and successful
continuation are selected together from one establishment/first-receipt execution.
No additional success or continuation premise is taken from the caller.

At the restored responder (`NoHeaderReceived`) the record's encoder premise `EncodersLive` and its draw premise hold
vacuously: the model session holds no encoder and the state is not `KeysUnsampled`.  So the module also exhibits the
record at a session that holds an encoder, `encoder_state_encrypt_hypotheses_jointly_satisfiable`: the established
initiator's session after its first send of the empty plaintext, at `KeysSampled` epoch 1, whose model session holds
the header encoder at position 1, which meets `EncodersLive`; the second `encrypt` there returns `Ok`.  No message is
received in between.  No other encoder-holding state, and no encoder near exhaustion, is exhibited.

## What it does not show

* That shipping primitives and codec operations satisfy the assumed laws.
* General restore/continue for later responder states, stored keys or sampling states.
* Restore/continue with decrypt, every refusal branch, or the full five-root lifecycle.
* Any plaintext but the empty one, or any path but the last-resort one: each witness is one run.
* An encoder-holding state other than the initiator's `KeysSampled` after its first send, or an encoder near
  exhaustion.
* Rust mutation sensitivity or translation-regeneration correctness.

## Regression controls

`check-responder-restored-witness-negatives.py` separately typechecks three changed
definitions of the proof-level composition, then requires the unchanged
`restore_then_encrypt_of_calls` to reject each at an equality goal: wrong saved bytes,
a reset RNG and a skipped continuation. It also accepts an equivalent RNG expression
with the complete proof and calibrates its failure classifier. These are proof-level
controls, not shipping-code experiments; no proof is emptied to typecheck a mutant.  Six more controls change a
statement, three of each witness (a state claimed `KeysUnsampled`; the source claimed moved or the encoder claimed at
position two; a budget claimed past the clock), each refused where the proof places the conjunct it derived.
-/

open Aeneas Aeneas.Std Result
open tacenta_session_unit

namespace Tacenta.UnitLifecycleRestoredResponderWitness

open Tacenta.UnitLifecycleRestoredResponder
open Tacenta.UnitLifecycleSessionCodec
open Tacenta.UnitLifecycleT3
open Tacenta.UnitLifecycleSendPreserve (CounterRoom)
open Tacenta.UnitLifecycleEncryptCompose (EncryptOfInvariantHypotheses)
open Tacenta.UnitLifecycleIntegrationScreen (byteRng byteCrc byteTrace)
open Tacenta.UnitLifecycleEstablishInitiatorShape (DhPublicValid)
open Tacenta.UnitLifecycleResponderFirstFrame (FirstFrameSuccessShape InitiatorSecretParts DhAgreeSymmetric)
open Tacenta.UnitLifecycleResponderFirstReceipt (DhAgreeContributory AeadRoundTrip first_send_receive_reachable
  firstReceiptSession headerSource)
open Tacenta.UnitLifecycleDecryptRatchetT3 (DecryptRatchetAgreements)
open Tacenta.UnitLifecycleEstablishedEncrypt (EncryptExtraLaws emptyPlaintext)
open Tacenta.UnitSatisfiabilityJoint (Interp Interp.real InitiatorAxiom ResponderAxiom)

/-- A proof-level composition of the two public operations, not an additional shipping API.
An import refusal is `none`; an accepted import is followed by exactly one encrypt
of that returned session, using the supplied plaintext and RNG state unchanged. -/
noncomputable def restoreThenEncrypt (saved plaintext : Slice U8) (rng : List U8) :
    Result (Option (core.result.Result (alloc.vec.Vec U8) lifecycle.Error × lifecycle.Session × List U8)) := do
  let imported ← lifecycle.Session.import saved
  match imported with
  | .Err _ => pure none
  | .Ok restored => do
    let output ← lifecycle.Session.encrypt byteRng byteCrc restored plaintext rng
    pure (some output)

/-- The composition uses the very session returned by import and the very result
returned by its next encrypt. Typed, proof-level body mutation controls protect
this equation; those controls are not Rust or translation-regeneration evidence. -/
theorem restore_then_encrypt_of_calls (saved plaintext : Slice U8) (rng : List U8)
    (session : lifecycle.Session)
    (output : core.result.Result (alloc.vec.Vec U8) lifecycle.Error × lifecycle.Session × List U8)
    (himport : lifecycle.Session.import saved = ok (core.result.Result.Ok session))
    (hencrypt : lifecycle.Session.encrypt byteRng byteCrc session plaintext rng = ok output) :
    restoreThenEncrypt saved plaintext rng = ok (some output) := by
  simp [restoreThenEncrypt, himport, hencrypt]
  rfl

/-- The original first-receipt reach, with its actual exported/imported responder
and a jointly instantiated encrypt hypothesis record at that restored session.
The continued encrypt of the empty plaintext (last-resort path) succeeds,
refines the normative lifecycle model and preserves
the invariant. The record is exhibited at `NoHeaderReceived`, not merely at the
initiator's `KeysUnsampled` state. All primitive/codec laws remain explicit. -/
theorem first_send_restored_encrypt_jointly_reachable
    (hzR : ZeroizingVecRoundTrip) (hbrR : OptionBranchSome)
    (hslR : VecAsSlice) (hprivR : DhPrivateBytesRoundTrip)
    (K : Model.Braid.Kem) (dh : DhView) (kem : KemView)
    (L : Tacenta.UnitLifecycleDecryptScreen.DecryptJointLaws K dh)
    (A : Nonempty (InitiatorAxiom Interp.real byteRng))
    (S : Tacenta.UnitLifecycleEstablishInitiatorShape.InitiatorSuccessShape Interp.real byteRng byteCrc)
    (hpub : DhPublicValid) (hct : Tacenta.UnitLifecycleEstablishInitiatorShape.KemCiphertextLenOf)
    (X : EncryptExtraLaws K dh kem) (RA : Nonempty (ResponderAxiom Interp.real byteRng))
    (hsym : DhAgreeSymmetric) (hrt : DhPublicBytesRoundTrip)
    (FS : FirstFrameSuccessShape Interp.real tacenta_boundary.kem.KeyPair.public_key
      @alloc.vec.Vec.is_empty)
    (hsizes : Tacenta.UnitLifecycleEstablishedEncrypt.KeyGenSizesOf K)
    (hcon : DhAgreeContributory) (haead : AeadRoundTrip)
    (ourA : lifecycle.Identity) (seed : List Std.U8) (hseed : seed.length = 64)
    (hkg : K.keyGen (Model.Lifecycle.braidRandomness (seed.map Tacenta.SessionUnitBraidT3.u8)) ≠ none) :
    ∃ (oracle : Model.Lifecycle.Oracle) (bundle : lifecycle.PublishedBundle)
      (q : InitiatorSecretParts byteRng byteCrc ourA bundle)
      (bytes : alloc.vec.Vec Std.U8) (sA : lifecycle.Session) (rngA : List Std.U8)
      (ourB : lifecycle.Identity) (storeB : lifecycle.PrekeyStore)
      (sB : lifecycle.Session) (ptB : alloc.vec.Vec Std.U8)
      (storeB' : lifecycle.PrekeyStore) (rngB : List Std.U8)
      (mB : Model.Lifecycle.Session) (z : zeroize.Zeroizing (alloc.vec.Vec Std.U8))
      (v : alloc.vec.Vec Std.U8) (reply : alloc.vec.Vec Std.U8)
      (sB' : lifecycle.Session) (rngB' : List Std.U8),
      oracle.braidKem = K ∧
      lifecycle.Session.encrypt byteRng byteCrc q.session emptyPlaintext seed =
        ok (core.result.Result.Ok bytes, sA, rngA) ∧
      lifecycle.PrekeyStore.publish storeB = ok bundle ∧
      lifecycle.establish_responder byteRng byteCrc ourB storeB (alloc.vec.Vec.deref bytes) seed =
        ok (core.result.Result.Ok (sB, ptB), storeB', rngB) ∧
      lifecycle.Session.export sB = ok z ∧
      zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref vecInst z = ok v ∧
      lifecycle.Session.import (alloc.vec.Vec.deref v) = ok (core.result.Result.Ok sB) ∧
      (∃ epoch auth dec, sB.braid.state = tacenta_braid.State.NoHeaderReceived epoch auth dec) ∧
      EncryptOfInvariantHypotheses byteRng byteCrc byteTrace dh kem
        Tacenta.UnitLifecycleRepair.witnessView { oracle with draws := byteTrace rngB }
        sB mB 0 emptyPlaintext rngB ∧
      lifecycle.Session.encrypt byteRng byteCrc sB emptyPlaintext rngB =
        ok (core.result.Result.Ok reply, sB', rngB') ∧
      StepRefines byteTrace dh oracle.braidKem (core.result.Result.Ok reply, sB', rngB')
        (Model.Lifecycle.encrypt Tacenta.UnitLifecycleRepair.witnessView
          { oracle with draws := byteTrace rngB } mB (sliceOf emptyPlaintext)) ∧
      restoreThenEncrypt (alloc.vec.Vec.deref v) emptyPlaintext rngB =
        ok (some (core.result.Result.Ok reply, sB', rngB')) ∧
      rngB' = rngB ∧
      lifecycle.Session.invariant sB' = ok true ∧ CounterRoom sB' 0 := by
  obtain ⟨oracle, bundle, rng0, rng1, q, bytes, sA, rngA, ourB, storeB, sB, ptB, storeB', rngB,
    hK, H, hcall, hpublish, hidentity, hdistinct, hkem, -, oracleOfB, htraceB, -, -, hcallB, -⟩ :=
    first_send_receive_reachable K dh kem L A S hpub hct X RA hsym hrt FS hsizes hcon haead
      ourA seed hseed hkg
  obtain ⟨contracts⟩ := Tacenta.UnitSatisfiabilityRecords.responder_contracts_of_axiom_base byteRng RA L.laws
  obtain ⟨inst⟩ := H.derivedKeys
  subst hK
  obtain ⟨oracle0, bundle1, s1, rng11, hK0, H1⟩ :=
    Tacenta.UnitLifecycleEstablishedDecrypt.established_decrypt_hypotheses_jointly_satisfiable
      oracle.braidKem dh L A S hpub hct ourA
  have ag : DecryptRatchetAgreements oracle.braidKem :=
    hK0 ▸ (H1 Tacenta.UnitLifecycleRepair.witnessView).agreements
  obtain ⟨d1, d2, rest2, hdrB⟩ : ∃ d1 d2 rest2, byteTrace seed = d1 :: d2 :: rest2 := by
    have := Tacenta.UnitLifecycleEstablishedEncrypt.byteTrace_two seed (by omega)
    exact ⟨_, _, _, this⟩
  obtain ⟨p, ec, dSend, dk, ekSeed, ekVector, -, hrel, hinv, -, hroom, z, v, hexport, hderef, himport⟩ :=
    initiator_first_send_responder_restored hzR hbrR hslR hprivR byteRng byteCrc byteTrace dh kem
      Tacenta.UnitLifecycleRepair.witnessView oracle H.braid H.triple H.aead H.dhCodec H.oracleOf H.codec
      H.codewordView H.zeroizing80 H.zeroizing32 H.zeroizingKeys H.keyGen hsizes H.kemCiphertextLen
      H.kemCiphertextBound byteRng byteCrc ourA _ _ _ rng1 q.session H.established q rfl emptyPlaintext H.room
      seed H.trace_eq _ _ _ (Tacenta.UnitLifecycleEstablishedEncrypt.byteTrace_two seed (by omega))
      bytes sA rngA hcall byteRng byteCrc contracts hpub hsym hcon haead hrt L.optionEq byteTrace oracle
      oracleOfB ag ourB storeB hpublish hidentity hdistinct hkem seed htraceB d1 (d2 :: rest2) hdrB
      ptB sB storeB' rngB hcallB
  let mB := firstReceiptSession (Tacenta.UnitLifecycleEstablishResponder.responderModelOf dh p)
    (sliceOf p.braidSecret)
    ⟨headerSource oracle.braidKem (Tacenta.SessionUnitBraidT3.AuthOf q.auth) ekSeed ekVector, 0⟩
    (arrayOf ec) (arrayOf q.sparseRoot) (arrayOf q.sparseSend) (arrayOf q.sparseReceive)
    (arrayOf q.ratchetBytes) (arrayOf q.dhOut) dSend (oracle.dhPublic d1) d1
  have hrelated : SessionRefines dh oracle.braidKem sB mB := hrel
  obtain ⟨epoch, auth, dec, hstate⟩ :=
    Tacenta.UnitLifecycleResponderReply.noHeader_of_receipt_refines hrel
  have HE : EncryptOfInvariantHypotheses byteRng byteCrc byteTrace dh kem
      Tacenta.UnitLifecycleRepair.witnessView { oracle with draws := byteTrace rngB }
      sB mB 0 emptyPlaintext rngB :=
    { braid := H.braid, triple := H.triple, derivedKeys := H.derivedKeys, aead := H.aead
      dhCodec := H.dhCodec
      oracleOf := Tacenta.UnitLifecycleResponderReply.oracleOf_with_draws H.oracleOf (byteTrace rngB)
      codec := H.codec, codewordView := H.codewordView
      zeroizing80 := H.zeroizing80, zeroizing32 := H.zeroizing32, zeroizingKeys := H.zeroizingKeys
      laws := ⟨ag.kemLen, hsizes, ag.validateEk, contracts.divCeilValue⟩, keyGen := H.keyGen
      kemCiphertextBound := H.kemCiphertextBound, invariant := hinv, related := hrelated
      room := hroom 1 (by simp [Std.U32.max_eq])
      live := by
        intro enc henc
        simp [mB, firstReceiptSession, Tacenta.SessionUnitBraidT3.EncoderOf] at henc
      notSampling := by
        intro e a hdr decoder h
        rw [hstate] at h
        cases h
      plaintextRoom := H.room, trace_eq := rfl
      draws := by
        intro e a h
        rw [hstate] at h
        cases h }
  obtain ⟨⟨res, sB', rngB'⟩, hcontinue, hstep, hinv', hroom'⟩ := HE.refines
  have hmodel := Tacenta.UnitLifecycleResponderReply.reply_model_step
    Tacenta.UnitLifecycleRepair.witnessView { oracle with draws := byteTrace rngB }
    (Tacenta.UnitLifecycleEstablishResponder.responderModelOf dh p) (sliceOf p.braidSecret)
    ⟨headerSource oracle.braidKem (Tacenta.SessionUnitBraidT3.AuthOf q.auth) ekSeed ekVector, 0⟩
    (arrayOf ec) (arrayOf q.sparseRoot) (arrayOf q.sparseSend) (arrayOf q.sparseReceive)
    (arrayOf q.ratchetBytes) (arrayOf q.dhOut) dSend (oracle.dhPublic d1) d1 rfl
    (sliceOf emptyPlaintext) (by simp [sliceOf, emptyPlaintext])
  have hresult := hstep.result
  change ResultRefines res (Model.Lifecycle.encrypt Tacenta.UnitLifecycleRepair.witnessView
    { oracle with draws := byteTrace rngB } mB (sliceOf emptyPlaintext)).result at hresult
  dsimp only [mB] at hresult
  rw [hmodel] at hresult
  cases res with
  | Err err => exact hresult.elim
  | Ok reply =>
    obtain ⟨msg, ep, out, braidNext, hsend, _sparse, _candidate, _header, _key, -, _session⟩ :=
      Tacenta.UnitLifecycleEstablishedEncrypt.encrypt_ok_parts byteRng byteCrc sB emptyPlaintext rngB
        reply sB' rngB' hcontinue
    obtain ⟨hrng, _braid, -, -⟩ := Tacenta.UnitLifecycleResponderReply.braid_send_noHeader
      byteRng byteCrc sB.braid epoch auth dec hstate rngB _ rngB' hsend
    exact ⟨oracle, bundle, q, bytes, sA, rngA, ourB, storeB, sB, ptB, storeB', rngB, mB,
      z, v, reply, sB', rngB', rfl, hcall, hpublish, hcallB, hexport, hderef, himport,
      ⟨epoch, auth, dec, hstate⟩, HE, hcontinue, hstep,
      restore_then_encrypt_of_calls _ _ _ _ _ himport hcontinue, hrng, hinv', hroom'⟩

open Tacenta.UnitLifecycleEstablishInitiatorShape (DhPublicValid KemCiphertextLenOf establishedModelOf
  InitiatorSuccessShape) in
open Tacenta.UnitLifecycleEstablishedEncrypt (KeyGenSizesOf) in
open Tacenta.UnitLifecycleEncryptCompose (encrypt_refines_keeps_invariant) in
/-- **The hypotheses of `encrypt_refines_keeps_invariant` hold together at a session that holds an encoder**,
with the encoder premise met by that encoder rather than vacuously: under the laws of
`established_encrypt_successor_reachable` (which a model holds together, `established_encrypt_laws_model`), at every
64-byte source at whose bytes the model's key generation answers, the established initiator's first `encrypt` of the
empty plaintext returns `Ok` and leaves a session whose agreement is at `KeysSampled` epoch 1, related to a model
session holding the header encoder at position 1.  That session meets every field of `EncryptOfInvariantHypotheses`
with that model session, one operation of budget, the empty plaintext and the source the first call left (the
oracle's draws set to that source's trace): `EncodersLive` by the encoder's position, `notSampling` and `draws` by the
agreement state.  The second `encrypt` there returns `Ok`, refines the model's step and passes `Session::invariant`.
No message is received in between; last-resort path; empty plaintext.  The record's AEAD contracts are false of the
shipping AEAD by reading, so this is consistency in a model, not exhibition of the shipping code. -/
theorem encoder_state_encrypt_hypotheses_jointly_satisfiable (K : Model.Braid.Kem) (dh : DhView)
    (kem : KemView) (L : Tacenta.UnitLifecycleDecryptScreen.DecryptJointLaws K dh)
    (A : Nonempty (InitiatorAxiom Interp.real byteRng))
    (S : InitiatorSuccessShape Interp.real byteRng byteCrc)
    (hpub : DhPublicValid) (hct : KemCiphertextLenOf) (X : EncryptExtraLaws K dh kem)
    (hsizes : KeyGenSizesOf K) (our : lifecycle.Identity) (seed : List Std.U8)
    (hseed : seed.length = 64)
    (hkg : K.keyGen (Model.Lifecycle.braidRandomness (seed.map Tacenta.SessionUnitBraidT3.u8)) ≠ none) :
    ∃ (oracle : Model.Lifecycle.Oracle) (s : lifecycle.Session) (bytes : alloc.vec.Vec Std.U8)
      (s' : lifecycle.Session) (rng' : List Std.U8) (m' : Model.Lifecycle.Session),
      oracle.braidKem = K ∧
      lifecycle.Session.encrypt byteRng byteCrc s emptyPlaintext seed =
        ok (core.result.Result.Ok bytes, s', rng') ∧
      (∃ auth kp enc, s'.braid.state = tacenta_braid.State.KeysSampled 1#u64 auth kp enc) ∧
      (∃ e, Tacenta.SessionUnitBraidT3.EncoderOf m'.braid = some e ∧ e.next = 1) ∧
      EncryptOfInvariantHypotheses byteRng byteCrc byteTrace dh kem Tacenta.UnitLifecycleRepair.witnessView
        { oracle with draws := byteTrace rng' } s' m' 0 emptyPlaintext rng' ∧
      ∃ (bytes2 : alloc.vec.Vec Std.U8) (s'' : lifecycle.Session) (rng'' : List Std.U8),
        lifecycle.Session.encrypt byteRng byteCrc s' emptyPlaintext rng' =
          ok (core.result.Result.Ok bytes2, s'', rng'') ∧
        StepRefines byteTrace dh oracle.braidKem (core.result.Result.Ok bytes2, s'', rng'')
          (Model.Lifecycle.encrypt Tacenta.UnitLifecycleRepair.witnessView { oracle with draws := byteTrace rng' }
            m' (sliceOf emptyPlaintext)) ∧
        lifecycle.Session.invariant s'' = ok true := by
  obtain ⟨oracle, bundle, s, rng1, bytes, s', rng', hK, H, hcall, -, -⟩ :=
    Tacenta.UnitLifecycleEstablishedEncrypt.established_encrypt_successor_reachable K dh kem L A S hpub hct X
      hsizes our seed hseed hkg
  obtain ⟨inst⟩ := H.derivedKeys
  have hinv := Tacenta.UnitLifecycleEstablishInitiatorShape.establish_initiator_for_admissible _ _
    H.dhPublicValid H.kemCiphertextLen H.optionEq our bundle _ [] rng1 s H.established
  have hrel := Tacenta.UnitLifecycleEstablishInitiatorShape.sessionRefines_established _ _ dh oracle.braidKem our
    bundle _ [] rng1 s H.established
  have hroom := Tacenta.UnitLifecycleEncryptPreserve.counterRoom_established _ _ our bundle _ [] rng1 s
    H.established 2 (by simp [Std.U32.max_eq])
  obtain ⟨p, hp⟩ := Tacenta.UnitLifecycleEstablishInitiatorShape.establish_initiator_for_parts _ _ our bundle _ []
    rng1 s H.established
  have hlive : Tacenta.SessionUnitBraidT3.EncodersLive (establishedModelOf dh s).braid := by
    intro enc henc
    subst hp
    simp [establishedModelOf, Tacenta.UnitLifecycleEstablishInitiatorShape.InitiatorOutputParts.session,
      Tacenta.UnitLifecycleEstablishInitiatorShape.unsampledModelOf, Tacenta.SessionUnitBraidT3.EncoderOf] at henc
  have hns : ∀ e a hdr dec, s.braid.state ≠ .HeaderReceived e a hdr dec := by
    intro e a hdr dec h
    subst hp
    simp [Tacenta.UnitLifecycleEstablishInitiatorShape.InitiatorOutputParts.session] at h
  have laws : Tacenta.UnitLifecycleEncryptPreserve.SendInvariantLaws oracle.braidKem :=
    ⟨H.kemLen, H.keyGenSizes, H.validateEk, H.divCeil⟩
  -- the first send, through the composition at budget two
  obtain ⟨o, hcallo, hstep, hinv', hroom'⟩ := encrypt_refines_keeps_invariant H.braid H.triple H.aead H.dhCodec
    H.oracleOf H.codec H.codewordView H.zeroizing80 H.zeroizing32 H.zeroizingKeys laws H.keyGen
    H.kemCiphertextBound s (establishedModelOf dh s) 1 hinv hrel hroom hlive hns emptyPlaintext H.room seed
    H.trace_eq (fun _ _ _ => H.draws)
  rw [hcall] at hcallo
  cases hcallo
  -- the key generation of that send, and the agreement state it leaves
  have hfits := Tacenta.UnitLifecycleT3.encrypt_ok_plaintext_fits byteRng byteCrc s emptyPlaintext seed bytes s'
    rng' hcall
  obtain ⟨d1, d2, rest, hdr⟩ : ∃ d1 d2 rest, byteTrace seed = d1 :: d2 :: rest :=
    ⟨_, _, _, Tacenta.UnitLifecycleEstablishedEncrypt.byteTrace_two seed (by omega)⟩
  obtain ⟨output, hcall', -, hcases⟩ := Tacenta.UnitLifecycleEstablishedEncrypt.established_encrypt_outcomes
    byteRng byteCrc byteTrace dh kem Tacenta.UnitLifecycleRepair.witnessView oracle H.braid H.triple H.aead
    H.dhCodec H.oracleOf H.codec H.codewordView H.zeroizing80 H.zeroizing32 H.zeroizingKeys H.keyGen
    H.kemCiphertextLen H.kemCiphertextBound byteRng byteCrc our bundle _ [] rng1 s H.established
    emptyPlaintext H.room hfits seed H.trace_eq d1 d2 rest hdr
  rw [hcall] at hcall'
  cases hcall'
  rcases hcases with ⟨-, hres, -⟩ | ⟨dk, ekSeed, ekVector, hkgs, bytes', -, -, hstate, -⟩
  · cases hres
  obtain ⟨q, hq⟩ := Tacenta.UnitLifecycleResponderFirstFrame.establish_initiator_for_secret byteRng byteCrc our
    bundle _ [] rng1 s H.established
  have hmA := Tacenta.UnitLifecycleInitiatorSecondSend.first_send_model_session_encoder dh
    Tacenta.UnitLifecycleRepair.witnessView oracle q (sliceOf emptyPlaintext) hfits d1 d2 rest
    (H.trace_eq.symm.trans hdr) dk ekSeed ekVector hkgs
  rw [← hq] at hmA
  have hu : 4294967295 ≤ Usize.max := Tacenta.SessionUnitSessionT1.small_le_usize_max (le_refl _)
  have Hc : EncryptOfInvariantHypotheses byteRng byteCrc byteTrace dh kem Tacenta.UnitLifecycleRepair.witnessView
      { oracle with draws := byteTrace rng' } s'
      (Model.Lifecycle.encrypt Tacenta.UnitLifecycleRepair.witnessView oracle (establishedModelOf dh s)
        (sliceOf emptyPlaintext)).session 0 emptyPlaintext rng' :=
    { braid := H.braid, triple := H.triple, derivedKeys := H.derivedKeys, aead := H.aead, dhCodec := H.dhCodec
      oracleOf := Tacenta.UnitLifecycleResponderReply.oracleOf_with_draws H.oracleOf (byteTrace rng')
      codec := H.codec, codewordView := H.codewordView, zeroizing80 := H.zeroizing80
      zeroizing32 := H.zeroizing32, zeroizingKeys := H.zeroizingKeys, laws := laws, keyGen := H.keyGen
      kemCiphertextBound := H.kemCiphertextBound, invariant := hinv', related := hstep.session, room := hroom'
      live := by
        intro e he
        rw [hmA] at he
        simp [Tacenta.SessionUnitBraidT3.EncoderOf] at he
        subst he
        show (1 : Nat) < 65536
        omega
      notSampling := by
        intro e a hdr dec h
        obtain ⟨auth, kp, enc, hs⟩ := hstate
        rw [hs] at h
        cases h
      plaintextRoom := H.room
      trace_eq := rfl
      draws := by
        intro e a h
        obtain ⟨auth, kp, enc, hs⟩ := hstate
        rw [hs] at h
        cases h }
  obtain ⟨o2, hcall2, hstep2, hinv2, -⟩ := Hc.refines
  have hok : ∃ b, (Model.Lifecycle.encrypt Tacenta.UnitLifecycleRepair.witnessView
      { oracle with draws := byteTrace rng' }
      (Model.Lifecycle.encrypt Tacenta.UnitLifecycleRepair.witnessView oracle (establishedModelOf dh s)
        (sliceOf emptyPlaintext)).session (sliceOf emptyPlaintext)).result = .ok b := by
    rw [hmA]
    simp [Model.Lifecycle.encrypt, Model.Lifecycle.agreementFailed, Model.Lifecycle.sendAgreement,
      Model.Lifecycle.braidSendNeedsDraw, Model.Braid.send, Model.Lifecycle.braidFailed,
      Model.Lifecycle.sparseOutputOf, Model.Braid.BraidState.epoch,
      Tacenta.UnitLifecycleResponderFirstReceipt.senderAfterFirst,
      Model.Triple.sendDetailed, Model.Ratchet.sendDetailed, Model.SparseRatchet.sendDetailed,
      Model.SparseRatchet.maybeAdvanceDetailed, Model.SparseRatchet.findChains, Model.State.u32Max,
      Model.SparseRatchet.u64Max, Model.SparseRatchet.setChains, sliceOf, emptyPlaintext,
      Model.Lifecycle.maxPlaintextLen, Model.Lifecycle.compositeOf, Model.Lifecycle.compositeTypeOf]
  obtain ⟨b, hb⟩ := hok
  obtain ⟨r2, s'', rng''⟩ := o2
  have hres := hstep2.result
  rw [hb] at hres
  cases r2 with
  | Err e => simp [ResultRefines] at hres
  | Ok bytes2 =>
    refine ⟨oracle, s, bytes, s', rng', _, hK, hcall, hstate, ?_, Hc, bytes2, s'', rng'', hcall2, hstep2, hinv2⟩
    rw [hmA]
    exact ⟨_, rfl, rfl⟩

end Tacenta.UnitLifecycleRestoredResponderWitness

set_option pp.deepTerms true
set_option pp.proofs.withType true

/-! ## Pins

The constants each result depends on, and the statement of each result and definition, held by the
build.  `attest.py` requires every one of them (`REQUIRED_PINS`, `REQUIRED_STATEMENT_PINS`,
`REQUIRED_PRINT_FORM`). -/

/--
info: 'Tacenta.UnitLifecycleRestoredResponderWitness.restore_then_encrypt_of_calls' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_kem.CT1_LEN,
 tacenta_kem.CT2_LEN,
 tacenta_kem.EK_VECTOR_LEN,
 tacenta_kem.EncapsState,
 tacenta_kem.HEADER_LEN,
 tacenta_kem.IncrementalKeyPair,
 tacenta_kem.encapsulate1,
 tacenta_kem.validate_ek,
 zeroize.Zeroizing,
 rand_core_1.error.Error,
 tacenta_boundary.aead.encrypt,
 tacenta_boundary.dh.PrivateKey,
 tacenta_boundary.dh.PublicKeyBytes,
 tacenta_boundary.dh.is_prime_order_public,
 tacenta_boundary.kem.ciphertext_len,
 tacenta_kem.EncapsState.from_bytes,
 tacenta_kem.EncapsState.to_bytes,
 tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_kem.IncrementalKeyPair.from_bytes,
 tacenta_kem.IncrementalKeyPair.generate,
 tacenta_kem.IncrementalKeyPair.header,
 tacenta_kem.IncrementalKeyPair.to_bytes,
 zeroize.Zeroizing.new,
 Array.Insts.ZeroizeZeroize.zeroize,
 Pair.Insts.ZeroizeZeroize.zeroize,
 TupleABC.Insts.ZeroizeZeroize.zeroize,
 alloc.vec.Vec.as_slice,
 alloc.vec.Vec.capacity,
 alloc.vec.Vec.pop,
 core.num.Usize.div_ceil,
 core.option.Option.as_mut,
 tacenta_boundary.dh.PrivateKey.from_bytes,
 tacenta_boundary.dh.PrivateKey.public_key,
 tacenta_boundary.dh.PrivateKey.to_bytes,
 tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_boundary.dh.PublicKeyBytes.from_bytes,
 zeroize.Zeroize.Blanket.zeroize,
 tacenta_kem.EncapsState.Insts.CoreCloneClone.clone,
 tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone,
 zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 core.option.Option.Insts.CoreCloneClone.clone,
 core.option.Option.Insts.CoreCmpPartialEqOption.eq,
 core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual,
 core.option.Option.Insts.CoreOpsTry_traitTry.branch,
 lifecycle.PrekeyStore.to_bytes._native.decide.ax_1,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleRestoredResponderWitness.restore_then_encrypt_of_calls

/--
info: 'Tacenta.UnitLifecycleRestoredResponderWitness.first_send_restored_encrypt_jointly_reachable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
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
 tacenta_boundary.kem.ciphertext_len,
 tacenta_boundary.kem.decapsulate,
 tacenta_boundary.kem.encapsulate,
 tacenta_boundary.xeddsa.sign,
 tacenta_boundary.xeddsa.verify,
 tacenta_kem.EncapsState.from_bytes,
 tacenta_kem.EncapsState.to_bytes,
 tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_kem.IncrementalKeyPair.from_bytes,
 tacenta_kem.IncrementalKeyPair.generate,
 tacenta_kem.IncrementalKeyPair.header,
 tacenta_kem.IncrementalKeyPair.to_bytes,
 zeroize.Zeroizing.new,
 Array.Insts.ZeroizeZeroize.zeroize,
 Pair.Insts.ZeroizeZeroize.zeroize,
 TupleABC.Insts.ZeroizeZeroize.zeroize,
 alloc.vec.Vec.as_slice,
 alloc.vec.Vec.capacity,
 alloc.vec.Vec.is_empty,
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
 tacenta_boundary.kem.KeyPair.public_key,
 zeroize.Zeroize.Blanket.zeroize,
 tacenta_kem.EncapsState.Insts.CoreCloneClone.clone,
 tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone,
 zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 core.option.Option.Insts.CoreCloneClone.clone,
 core.option.Option.Insts.CoreCmpPartialEqOption.eq,
 core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual,
 core.option.Option.Insts.CoreOpsTry_traitTry.branch,
 lifecycle.PrekeyStore.to_bytes._native.decide.ax_1,
 tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes.eq,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleRestoredResponderWitness.first_send_restored_encrypt_jointly_reachable

/--
info: 'Tacenta.UnitLifecycleRestoredResponderWitness.encoder_state_encrypt_hypotheses_jointly_satisfiable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
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
 tacenta_boundary.kem.ciphertext_len,
 tacenta_boundary.kem.decapsulate,
 tacenta_boundary.kem.encapsulate,
 tacenta_boundary.xeddsa.sign,
 tacenta_boundary.xeddsa.verify,
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
 tacenta_kem.EncapsState.Insts.CoreCloneClone.clone,
 tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone,
 zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 core.option.Option.Insts.CoreCloneClone.clone,
 core.option.Option.Insts.CoreCmpPartialEqOption.eq,
 tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes.eq,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleRestoredResponderWitness.encoder_state_encrypt_hypotheses_jointly_satisfiable

/--
info: Tacenta.UnitLifecycleRestoredResponderWitness.restore_then_encrypt_of_calls : ∀ (saved plaintext : Slice U8)
  (rng : List U8) (session : lifecycle.Session)
  (output : core.result.Result (alloc.vec.Vec U8) lifecycle.Error × lifecycle.Session × List U8),
  lifecycle.Session.import saved = ok (core.result.Result.Ok session) →
    lifecycle.Session.encrypt Tacenta.UnitLifecycleIntegrationScreen.byteRng
          Tacenta.UnitLifecycleIntegrationScreen.byteCrc session plaintext rng =
        ok output →
      Tacenta.UnitLifecycleRestoredResponderWitness.restoreThenEncrypt saved plaintext rng = ok (some output)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleRestoredResponderWitness.restore_then_encrypt_of_calls

/--
info: Tacenta.UnitLifecycleRestoredResponderWitness.first_send_restored_encrypt_jointly_reachable : Tacenta.UnitLifecycleSessionCodec.ZeroizingVecRoundTrip →
  Tacenta.UnitLifecycleSessionCodec.OptionBranchSome →
    Tacenta.UnitLifecycleSessionCodec.VecAsSlice →
      Tacenta.UnitLifecycleSessionCodec.DhPrivateBytesRoundTrip →
        ∀ (K : Model.Braid.Kem) (dh : Tacenta.UnitLifecycleT3.DhView) (kem : Tacenta.UnitLifecycleT3.KemView),
          Tacenta.UnitLifecycleDecryptScreen.DecryptJointLaws K dh →
            Nonempty
                (Tacenta.UnitSatisfiabilityJoint.InitiatorAxiom Tacenta.UnitSatisfiabilityJoint.Interp.real
                  Tacenta.UnitLifecycleIntegrationScreen.byteRng) →
              Tacenta.UnitLifecycleEstablishInitiatorShape.InitiatorSuccessShape
                  Tacenta.UnitSatisfiabilityJoint.Interp.real Tacenta.UnitLifecycleIntegrationScreen.byteRng
                  Tacenta.UnitLifecycleIntegrationScreen.byteCrc →
                Tacenta.UnitLifecycleEstablishInitiatorShape.DhPublicValid →
                  Tacenta.UnitLifecycleEstablishInitiatorShape.KemCiphertextLenOf →
                    Tacenta.UnitLifecycleEstablishedEncrypt.EncryptExtraLaws K dh kem →
                      Nonempty
                          (Tacenta.UnitSatisfiabilityJoint.ResponderAxiom Tacenta.UnitSatisfiabilityJoint.Interp.real
                            Tacenta.UnitLifecycleIntegrationScreen.byteRng) →
                        Tacenta.UnitLifecycleResponderFirstFrame.DhAgreeSymmetric →
                          Tacenta.UnitLifecycleSessionCodec.DhPublicBytesRoundTrip →
                            Tacenta.UnitLifecycleResponderFirstFrame.FirstFrameSuccessShape
                                Tacenta.UnitSatisfiabilityJoint.Interp.real tacenta_boundary.kem.KeyPair.public_key
                                @alloc.vec.Vec.is_empty →
                              Tacenta.UnitLifecycleEstablishedEncrypt.KeyGenSizesOf K →
                                Tacenta.UnitLifecycleResponderFirstReceipt.DhAgreeContributory →
                                  Tacenta.UnitLifecycleResponderFirstReceipt.AeadRoundTrip →
                                    ∀ (ourA : lifecycle.Identity) (seed : List U8),
                                      seed.length = 64 →
                                        K.keyGen
                                              (Model.Lifecycle.braidRandomness
                                                (List.map Tacenta.SessionUnitBraidT3.u8 seed)) ≠
                                            none →
                                          ∃ oracle bundle q bytes sA rngA ourB storeB sB ptB storeB' rngB mB z v reply
                                            sB' rngB',
                                            oracle.braidKem = K ∧
                                              lifecycle.Session.encrypt Tacenta.UnitLifecycleIntegrationScreen.byteRng
                                                    Tacenta.UnitLifecycleIntegrationScreen.byteCrc q.session
                                                    Tacenta.UnitLifecycleEstablishedEncrypt.emptyPlaintext seed =
                                                  ok (core.result.Result.Ok bytes, sA, rngA) ∧
                                                storeB.publish = ok bundle ∧
                                                  lifecycle.establish_responder
                                                        Tacenta.UnitLifecycleIntegrationScreen.byteRng
                                                        Tacenta.UnitLifecycleIntegrationScreen.byteCrc ourB storeB
                                                        bytes.deref seed =
                                                      ok (core.result.Result.Ok (sB, ptB), storeB', rngB) ∧
                                                    sB.export = ok z ∧
                                                      zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref
                                                            Tacenta.UnitLifecycleSessionCodec.vecInst z =
                                                          ok v ∧
                                                        lifecycle.Session.import v.deref =
                                                            ok (core.result.Result.Ok sB) ∧
                                                          (∃ epoch auth dec,
                                                              sB.braid.state =
                                                                tacenta_braid.State.NoHeaderReceived epoch auth dec) ∧
                                                            Tacenta.UnitLifecycleEncryptCompose.EncryptOfInvariantHypotheses
                                                                Tacenta.UnitLifecycleIntegrationScreen.byteRng
                                                                Tacenta.UnitLifecycleIntegrationScreen.byteCrc
                                                                Tacenta.UnitLifecycleIntegrationScreen.byteTrace dh kem
                                                                Tacenta.UnitLifecycleRepair.witnessView
                                                                {
                                                                  draws :=
                                                                    Tacenta.UnitLifecycleIntegrationScreen.byteTrace
                                                                      rngB,
                                                                  braidKem := oracle.braidKem,
                                                                  dhPublic := oracle.dhPublic,
                                                                  dhAgree := oracle.dhAgree,
                                                                  identityValid := oracle.identityValid,
                                                                  aeadSeal := oracle.aeadSeal,
                                                                  aeadOpen := oracle.aeadOpen,
                                                                  kemValid := oracle.kemValid,
                                                                  kemEncaps := oracle.kemEncaps,
                                                                  kemDecaps := oracle.kemDecaps,
                                                                  sigVerify := oracle.sigVerify,
                                                                  sigSign := oracle.sigSign }
                                                                sB mB 0
                                                                Tacenta.UnitLifecycleEstablishedEncrypt.emptyPlaintext
                                                                rngB ∧
                                                              lifecycle.Session.encrypt
                                                                    Tacenta.UnitLifecycleIntegrationScreen.byteRng
                                                                    Tacenta.UnitLifecycleIntegrationScreen.byteCrc sB
                                                                    Tacenta.UnitLifecycleEstablishedEncrypt.emptyPlaintext
                                                                    rngB =
                                                                  ok (core.result.Result.Ok reply, sB', rngB') ∧
                                                                Tacenta.UnitLifecycleT3.StepRefines
                                                                    Tacenta.UnitLifecycleIntegrationScreen.byteTrace dh
                                                                    oracle.braidKem
                                                                    (core.result.Result.Ok reply, sB', rngB')
                                                                    (Model.Lifecycle.encrypt
                                                                      Tacenta.UnitLifecycleRepair.witnessView
                                                                      {
                                                                        draws :=
                                                                          Tacenta.UnitLifecycleIntegrationScreen.byteTrace
                                                                            rngB,
                                                                        braidKem := oracle.braidKem,
                                                                        dhPublic := oracle.dhPublic,
                                                                        dhAgree := oracle.dhAgree,
                                                                        identityValid := oracle.identityValid,
                                                                        aeadSeal := oracle.aeadSeal,
                                                                        aeadOpen := oracle.aeadOpen,
                                                                        kemValid := oracle.kemValid,
                                                                        kemEncaps := oracle.kemEncaps,
                                                                        kemDecaps := oracle.kemDecaps,
                                                                        sigVerify := oracle.sigVerify,
                                                                        sigSign := oracle.sigSign }
                                                                      mB
                                                                      (Tacenta.UnitLifecycleT3.sliceOf
                                                                        Tacenta.UnitLifecycleEstablishedEncrypt.emptyPlaintext)) ∧
                                                                  Tacenta.UnitLifecycleRestoredResponderWitness.restoreThenEncrypt
                                                                        v.deref
                                                                        Tacenta.UnitLifecycleEstablishedEncrypt.emptyPlaintext
                                                                        rngB =
                                                                      ok
                                                                        (some
                                                                          (core.result.Result.Ok reply, sB', rngB')) ∧
                                                                    rngB' = rngB ∧
                                                                      sB'.invariant = ok true ∧
                                                                        Tacenta.UnitLifecycleSendPreserve.CounterRoom
                                                                          sB' 0
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleRestoredResponderWitness.first_send_restored_encrypt_jointly_reachable

/--
info: Tacenta.UnitLifecycleRestoredResponderWitness.encoder_state_encrypt_hypotheses_jointly_satisfiable : ∀
  (K : Model.Braid.Kem) (dh : Tacenta.UnitLifecycleT3.DhView) (kem : Tacenta.UnitLifecycleT3.KemView),
  Tacenta.UnitLifecycleDecryptScreen.DecryptJointLaws K dh →
    Nonempty
        (Tacenta.UnitSatisfiabilityJoint.InitiatorAxiom Tacenta.UnitSatisfiabilityJoint.Interp.real
          Tacenta.UnitLifecycleIntegrationScreen.byteRng) →
      Tacenta.UnitLifecycleEstablishInitiatorShape.InitiatorSuccessShape Tacenta.UnitSatisfiabilityJoint.Interp.real
          Tacenta.UnitLifecycleIntegrationScreen.byteRng Tacenta.UnitLifecycleIntegrationScreen.byteCrc →
        Tacenta.UnitLifecycleEstablishInitiatorShape.DhPublicValid →
          Tacenta.UnitLifecycleEstablishInitiatorShape.KemCiphertextLenOf →
            Tacenta.UnitLifecycleEstablishedEncrypt.EncryptExtraLaws K dh kem →
              Tacenta.UnitLifecycleEstablishedEncrypt.KeyGenSizesOf K →
                ∀ (our : lifecycle.Identity) (seed : List U8),
                  seed.length = 64 →
                    K.keyGen (Model.Lifecycle.braidRandomness (List.map Tacenta.SessionUnitBraidT3.u8 seed)) ≠ none →
                      ∃ oracle s bytes s' rng' m',
                        oracle.braidKem = K ∧
                          lifecycle.Session.encrypt Tacenta.UnitLifecycleIntegrationScreen.byteRng
                                Tacenta.UnitLifecycleIntegrationScreen.byteCrc s
                                Tacenta.UnitLifecycleEstablishedEncrypt.emptyPlaintext seed =
                              ok (core.result.Result.Ok bytes, s', rng') ∧
                            (∃ auth kp enc, s'.braid.state = tacenta_braid.State.KeysSampled 1#u64 auth kp enc) ∧
                              (∃ e, Tacenta.SessionUnitBraidT3.EncoderOf m'.braid = some e ∧ e.next = 1) ∧
                                Tacenta.UnitLifecycleEncryptCompose.EncryptOfInvariantHypotheses
                                    Tacenta.UnitLifecycleIntegrationScreen.byteRng
                                    Tacenta.UnitLifecycleIntegrationScreen.byteCrc
                                    Tacenta.UnitLifecycleIntegrationScreen.byteTrace dh kem
                                    Tacenta.UnitLifecycleRepair.witnessView
                                    { draws := Tacenta.UnitLifecycleIntegrationScreen.byteTrace rng',
                                      braidKem := oracle.braidKem, dhPublic := oracle.dhPublic,
                                      dhAgree := oracle.dhAgree, identityValid := oracle.identityValid,
                                      aeadSeal := oracle.aeadSeal, aeadOpen := oracle.aeadOpen,
                                      kemValid := oracle.kemValid, kemEncaps := oracle.kemEncaps,
                                      kemDecaps := oracle.kemDecaps, sigVerify := oracle.sigVerify,
                                      sigSign := oracle.sigSign }
                                    s' m' 0 Tacenta.UnitLifecycleEstablishedEncrypt.emptyPlaintext rng' ∧
                                  ∃ bytes2 s'' rng'',
                                    lifecycle.Session.encrypt Tacenta.UnitLifecycleIntegrationScreen.byteRng
                                          Tacenta.UnitLifecycleIntegrationScreen.byteCrc s'
                                          Tacenta.UnitLifecycleEstablishedEncrypt.emptyPlaintext rng' =
                                        ok (core.result.Result.Ok bytes2, s'', rng'') ∧
                                      Tacenta.UnitLifecycleT3.StepRefines
                                          Tacenta.UnitLifecycleIntegrationScreen.byteTrace dh oracle.braidKem
                                          (core.result.Result.Ok bytes2, s'', rng'')
                                          (Model.Lifecycle.encrypt Tacenta.UnitLifecycleRepair.witnessView
                                            { draws := Tacenta.UnitLifecycleIntegrationScreen.byteTrace rng',
                                              braidKem := oracle.braidKem, dhPublic := oracle.dhPublic,
                                              dhAgree := oracle.dhAgree, identityValid := oracle.identityValid,
                                              aeadSeal := oracle.aeadSeal, aeadOpen := oracle.aeadOpen,
                                              kemValid := oracle.kemValid, kemEncaps := oracle.kemEncaps,
                                              kemDecaps := oracle.kemDecaps, sigVerify := oracle.sigVerify,
                                              sigSign := oracle.sigSign }
                                            m'
                                            (Tacenta.UnitLifecycleT3.sliceOf
                                              Tacenta.UnitLifecycleEstablishedEncrypt.emptyPlaintext)) ∧
                                        s''.invariant = ok true
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleRestoredResponderWitness.encoder_state_encrypt_hypotheses_jointly_satisfiable

/--
info: def Tacenta.UnitLifecycleRestoredResponderWitness.restoreThenEncrypt : Slice U8 →
  Slice U8 →
    List U8 → Result (Option (core.result.Result (alloc.vec.Vec U8) lifecycle.Error × lifecycle.Session × List U8)) :=
fun saved plaintext rng => do
  let imported ← lifecycle.Session.import saved
  match imported with
    | core.result.Result.Err a => pure none
    | core.result.Result.Ok restored => do
      let output ←
        lifecycle.Session.encrypt Tacenta.UnitLifecycleIntegrationScreen.byteRng
            Tacenta.UnitLifecycleIntegrationScreen.byteCrc restored plaintext rng
      pure (some output)
-/
#guard_msgs in
#print Tacenta.UnitLifecycleRestoredResponderWitness.restoreThenEncrypt
