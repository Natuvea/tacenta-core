import Translation.UnitLifecycleEncryptPreserve

/-!
# `Session::encrypt` at every invariant session outside the sampling state

`UnitLifecycleEncryptPreserve` keeps `Session::invariant` and the counter budget through every successful `encrypt`,
given the relation after the call, and derives that relation from the general encrypt route
`public_session_encrypt_of_send_contracts` only under that route's per-call records: `braidTrace`
(`BraidSendTraceAgreementCounted`, what the agreement's send returns at the run's draws), `providers`
(`EncryptNonterminalRouteProviders`, finite-store facts about the model's sparse ratchet) and the headroom
`EncryptHeadroom`.  Before this module those three were discharged only on named runs (the established initiator's
first send, the responder's reply, the two second sends).  This module derives them at every session that passes
`Session::invariant`, has room for one operation and refines a model session, at every agreement state but
`HeaderReceived`, and composes the route with the preservation step.

## What it shows

* `braid_send_failed_rng`: at a failed agreement the translated `Braid::send` returns the source it was given.
  Hypothesis-free.
* `braidSendTraceCounted_of_scope`: the counted draw record holds at every such session: at `Failed` and at the nine
  states whose send takes no draw the send returns the source as given (`braid_send_failed_rng`,
  `braid_send_no_draw`); at `KeysUnsampled` key generation reads the two draws the model counts
  (`braidSendTraceCounted_of_keysUnsampled`).
* `sparseOutput_none_of_scope`, `model_not_headerReceived`: outside `headerReceived` the model's agreement send has no
  output, so the sparse output the code hands the Triple is `none`.
* `tripleStoreFacts_of_invariant`, `encryptProviders_of_invariant`: the five finite-store facts both Triple condition
  records ask for, from `Session::invariant` read on the model (`ModelSpqrInv`: every chain's and stored key's epoch at
  most the sparse epoch; the receive headroom: room in the chain table) and any budget (`CounterRoom s k`, so the
  ceilings: the epoch and every chain counter below `u64::MAX`).
* `pending_ciphertext_len_of_structural`, `encryptHeadroom_of_invariant`: `Session::structural_invariant` fixes a pending
  initial message's ciphertext to `kem::ciphertext_len` bytes, so `EncryptHeadroom` holds at every invariant session
  for every plaintext of at most `Usize.max - 65770` bytes, under `KemCiphertextLenBound`.
* `encrypt_refines_keeps_invariant` (and its record form `EncryptOfInvariantHypotheses`,
  `EncryptOfInvariantHypotheses.refines`): **at every session `s` that passes `Session::invariant`, has room for `k + 1`
  operations, refines a model session `m` whose encoder, if any, has codewords left, and whose agreement is not at
  `HeaderReceived`, the public `encrypt` returns, its result, the session it returns and the draws it leaves refine
  `Model.Lifecycle.encrypt` at `m`, and the session it returns passes `Session::invariant` and has room for `k`
  operations.**  Every outcome: success, the size refusal, the terminal refusal, a failed key generation, a Triple
  refusal.
* `encrypt_ok_arm` (model only), `encrypt_refines_effects`: on success, additionally, the classical sending counter is
  one more than before, the classical clock and stored keys are as before, the agreement's epoch is as before, and at
  every state but `KeysUnsampled` the source's draws are as before.
* `encrypt_of_invariant_hypotheses_jointly_satisfiable`: every field of `EncryptOfInvariantHypotheses` holds together at
  the real constants, at an established initiator session with the model session read off it, for the empty plaintext
  from the byte-stream source, under the laws of `established_encrypt_successor_reachable`, and `encrypt` there
  returns `Ok`.

## The laws and premises

No new law.  The route's boundary records and laws are the ones `public_session_encrypt_of_send_contracts` takes
(`BraidSendRefinementContracts`, whose `HkdfAgrees` field supplies the KDF agreement, `TripleSendRefinementContracts`,
`AeadSealBounded`, `DhCodecTotal`, `OracleOf`, `DhCodecOf`, `CodewordViewSendOf`, the three `zeroize` round trips,
`DerivedKeysModel`), the four of `SendInvariantLaws`, `KeyGenSeededFor` (used at `KeysUnsampled` only) and
`KemCiphertextLenBound` (used where a pending initial message is held).  `AeadSealBounded` and the AEAD clauses of
`OracleOf` are stated for every length and are false of the shipping AEAD by reading (`LIMITATIONS.md`, the totality
row; register row `AEAD-LENGTH-CONTRACTS`), so these results, as stated, say nothing about the shipping code at any
length until those contracts are repaired.

Session premises: the invariant, the relation, `CounterRoom s (k + 1)` (the uniform budget every step theorem takes),
`EncodersLive m.braid` (the model encoder the agreement emits from, if any, has codewords left), the agreement not at
`HeaderReceived`, the plaintext bound, the trace equation and, at `KeysUnsampled`, two draws.  `EncodersLive` is kept:
whether `Session::invariant` implies it has not been checked; by reading, `Encoder::invariant` accepts an exhausted
encoder, so it is not expected to.  No premise names a platform width.

## Non-vacuity

`encrypt_of_invariant_hypotheses_jointly_satisfiable` exhibits the whole premise list at one session, the established
initiator's at `KeysUnsampled`, at the real constants under laws a toy model holds together
(`established_encrypt_laws_model`), some of them (the AEAD totality laws) false of the shipping AEAD by reading:
consistency in a model, not exhibition of the shipping code.  No other agreement state is exhibited by this module;
`UnitLifecycleRestoredResponderWitness` exhibits the same premise list at two states whose agreement takes no draw:
`NoHeaderReceived` (the restored responder's session after its first receipt,
`first_send_restored_encrypt_jointly_reachable`) and `KeysSampled` epoch 1 (the initiator's session after its first
send, `encoder_state_encrypt_hypotheses_jointly_satisfiable`, the only exhibited session that holds an encoder).

## What it does not show

* `encrypt` at a session whose agreement is at `HeaderReceived` (the first half of encapsulation, which draws): the
  counted draw record there needs a law relating `encapsulate1` at the drawn bytes to the model KEM's at that
  randomness, and none is assumed in the tree; `Encaps1SizesOf` would also be needed.
* `encrypt` at a session whose model encoder has no codewords left, or without the budget premise
  (PROOF-BOUNDARY-HEADROOM).
* That a session reached in a conversation meets these premises, beyond the runs of the earlier modules; a second
  party, the conversation, or a joint relation between two parties' sessions.
* That the real primitives meet the boundary records or the laws; the AEAD contracts are false of the shipping AEAD
  by reading at long lengths.
* That `Session::invariant` says a session is reachable: it is a predicate on fields.
-/

open Aeneas Aeneas.Std Result
open tacenta_session_unit
open Tacenta.SessionUnitRatchetImportInv (bind_eq_ok_inv)

namespace Tacenta.UnitLifecycleEncryptCompose

open Tacenta.UnitTripleInvModel
open Tacenta.UnitLifecycleSendPreserve
open Tacenta.UnitLifecycleEncryptPreserve
open Tacenta.UnitLifecycleT3 (DhView SessionRefines KemView OracleOf DhCodecOf CodewordViewSendOf
  BraidSendRefinementContracts TripleSendRefinementContracts ZeroizingRoundTrips StepRefines
  BraidSendTraceAgreementCounted EncryptNonterminalRouteProviders GeneratedBraidSuccessEvidence
  RealSparseConversion PublicEncryptWitness public_session_encrypt_of_send_contracts)
open Tacenta.UnitLifecycleEstablishedEncrypt (KeyGenSeededFor braidSendTraceCounted_of_keysUnsampled)

/-- At a failed agreement, the translated `Braid::send` returns the source it was given. -/
theorem braid_send_failed_rng {R : Type} (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R)
    (b : tacenta_braid.Braid) (hb : b.state = .Failed) (rng : R)
    (msg : tacenta_braid.Msg) (ep : U64) (out : Option tacenta_braid.Output) (b' : tacenta_braid.Braid)
    (rng' : R) (h : tacenta_braid.Braid.send rc crc b rng = ok ((msg, ep, out, b'), rng')) :
    rng' = rng := by
  obtain ⟨st⟩ := b
  simp only at hb
  subst hb
  unfold tacenta_braid.Braid.send at h
  obtain ⟨s, hs, h⟩ := bind_eq_ok_inv h
  obtain ⟨⟨⟨m1, o1, nxt⟩, rng1⟩, hstep, h⟩ := bind_eq_ok_inv h
  obtain ⟨i, -, h⟩ := bind_eq_ok_inv h
  simp only [ok.injEq, Prod.mk.injEq] at h
  obtain ⟨⟨-, -, rfl, rfl⟩, rfl⟩ := h
  unfold tacenta_braid.State.Insts.CoreCloneClone.clone at hs
  simp only [ok.injEq] at hs
  subst hs
  unfold tacenta_braid.Braid.step_send at hstep
  obtain ⟨m, -, hstep⟩ := bind_eq_ok_inv hstep
  simp only [ok.injEq, Prod.mk.injEq] at hstep
  exact hstep.2.symm

/-- **The counted draw record of the encrypt route holds at every session outside the sampling state**, with the
model session it refines: at a failed agreement and at the nine states whose send takes no draw the translated send
returns the source it was given (`braid_send_failed_rng`, `braid_send_no_draw`), and at `KeysUnsampled` key
generation reads the two draws the model counts (`braidSendTraceCounted_of_keysUnsampled`, under
`KeyGenSeededFor` and two draws left).  The model encoder premise `EncodersLive` is kept. -/
theorem braidSendTraceCounted_of_scope {R : Type} {rc : rand_core_1.RngCore R}
    {crc : rand_core_1.CryptoRng R} {trace : R → List Model.Lifecycle.Key} {dh : DhView}
    {K : Model.Braid.Kem} {oracle : Model.Lifecycle.Oracle} {real : lifecycle.Session}
    {model : Model.Lifecycle.Session} {rng : R}
    (contracts : BraidSendRefinementContracts rc K) (hgen : KeyGenSeededFor K rc crc trace)
    (hkem : oracle.braidKem = K) (hrel : SessionRefines dh K real model)
    (hbinv : tacenta_braid.Braid.invariant real.braid = ok true)
    (hlive : Tacenta.SessionUnitBraidT3.EncodersLive model.braid)
    (hns : ∀ e a hdr dec, real.braid.state ≠ .HeaderReceived e a hdr dec)
    (hdraws : ∀ e a, real.braid.state = .KeysUnsampled e a → ∃ d1 d2 rest, trace rng = d1 :: d2 :: rest) :
    BraidSendTraceAgreementCounted rc crc trace K oracle real model rng := by
  by_cases hku : ∃ e a, real.braid.state = .KeysUnsampled e a
  · obtain ⟨e, a, hst⟩ := hku
    have hb := hrel.braid
    rw [hst] at hb
    cases hm : model.braid with
    | keysUnsampled e' a' =>
        rw [hm] at hb
        obtain ⟨he, ha⟩ := hb
        subst he ha
        exact braidSendTraceCounted_of_keysUnsampled contracts hgen hkem e a hst hm (hdraws e a hst)
    | _ => rw [hm] at hb; simp [Tacenta.SessionUnitBraidT3.StateRefines] at hb
  have hnd : Model.Lifecycle.braidSendNeedsDraw model.braid = false :=
    needsDraw_false_of_kind hrel.braid (fun e a h => hku ⟨e, a, h⟩) hns
  exact
    { encodersLive := hlive
      braidKem := hkem
      noDrawTrace := by
        intro msg ep out b rngNext hsend _
        by_cases hf : real.braid.state = .Failed
        · rw [braid_send_failed_rng rc crc real.braid hf rng msg ep out b rngNext hsend]
        · have hsw := sendsWithoutDraw_of_refines hrel.braid hnd hf
          rw [(braid_send_no_draw contracts.kemClone rc crc real.braid hsw hbinv rng msg ep out b rngNext
            hsend).1]
      drawTrace := by
        intro _ _ _ _ _ _ hneeds
        rw [hnd] at hneeds; cases hneeds
      drawPost := by
        intro _ _ _ _ _ _ hneeds
        rw [hnd] at hneeds; cases hneeds }

/-- At a model agreement other than `headerReceived`, the sparse output the generated `encrypt` hands the Triple is
`none`: the model's send has an output only at `headerReceived` (`braid_send_output`), so the code's has none. -/
theorem sparseOutput_none_of_scope {R : Type} {rc : rand_core_1.RngCore R}
    {crc : rand_core_1.CryptoRng R} {trace : R → List Model.Lifecycle.Key} {dh : DhView}
    {K : Model.Braid.Kem} {oracle : Model.Lifecycle.Oracle} {real : lifecycle.Session}
    {model : Model.Lifecycle.Session} {rng : R} {realMessage : tacenta_braid.Msg}
    {realEpoch : Std.U64} {realOutput : Option tacenta_braid.Output}
    {realBraidNext : tacenta_braid.Braid} {rngNext : R}
    {sparseOutput : Option tacenta_spqr.Output}
    (hmodel : ∀ e a s hk d, model.braid ≠ .headerReceived e a s hk d)
    (hsparse : RealSparseConversion realOutput sparseOutput)
    (hevidence : Nonempty (GeneratedBraidSuccessEvidence rc crc trace dh K oracle real model rng
      realMessage realEpoch realOutput realBraidNext rngNext)) :
    sparseOutput = none := by
  obtain ⟨ev⟩ := hevidence
  obtain ⟨rand, hr⟩ := sendAgreement_is_send ev.modelSend
  have hout : ev.modelOutput = none := by
    cases ho : ev.modelOutput with
    | none => rfl
    | some o =>
        have h2 : (Model.Braid.send oracle.braidKem rand model.braid).2.2.1 = some o := by
          rw [← hr]; exact ho
        obtain ⟨-, e, a, s, hk, d, hst⟩ := braid_send_output _ _ _ o h2
        exact absurd hst (hmodel e a s hk d)
  have hreal : realOutput = none := by
    have h := ev.output
    rw [hout] at h
    cases realOutput with
    | none => rfl
    | some o => exact h.elim
  cases hsparse with
  | none => rfl
  | some _ _ hsome _ => rw [hreal] at hsome; cases hsome

/-- **The five finite-store facts both Triple condition records of the encrypt route ask for, at every session that
passes `Session::invariant` and has any budget `CounterRoom s k`** (so the ceilings, `k = 0`), read on the model session it refines: the chain table
has room for one entry (from the receive headroom the invariant gives), every chain and every stored key's epoch is
at most the sparse epoch (the epoch window and the stored keys' chains of `ModelSpqrInv`), and the epoch and every
chain counter are below `u64::MAX` (the budget). -/
theorem tripleStoreFacts_of_invariant (hct1 : Tacenta.SessionUnitBraidT1.Ct1LenTotal) {dh : DhView}
    {K : Model.Braid.Kem} {s : lifecycle.Session} {m : Model.Lifecycle.Session} {k : Nat}
    (hinv : lifecycle.Session.invariant s = ok true) (hrel : SessionRefines dh K s m)
    (hroom : CounterRoom s k) :
    m.triple.postQuantum.chains.length + 1 < Usize.max ∧
    (∀ q ∈ m.triple.postQuantum.chains, q.1 + Model.SparseRatchet.epochsKept ≤ Std.U64.max) ∧
    (∀ sk ∈ m.triple.postQuantum.skipped, sk.1 + Model.SparseRatchet.epochsKept ≤ Std.U64.max) ∧
    m.triple.postQuantum.epoch + 1 < Std.U64.max ∧
    (∀ q ∈ m.triple.postQuantum.chains, ∀ ch : Model.SparseRatchet.Chain,
      (q.2.send = some ch ∨ q.2.receive = some ch) → ch.n < Std.U64.max) := by
  obtain ⟨-, htri, -⟩ := (session_invariant_iff s).mp hinv
  have hM : ModelTripleInv m.triple := (triple_invariant_iff_model hrel.triple).mp htri
  have hsp := hM.2.1
  have hmr := (counterRoom_iff_model hrel k).mp hroom
  obtain ⟨hpre, -, -⟩ := Tacenta.UnitLifecycleT1.invariant_gives_preconditions hct1 s hinv
  have hlen : m.triple.postQuantum.chains.length = s.triple.post_quantum.chains.val.length := by
    rw [← hrel.triple.2]; simp [Tacenta.SessionUnitTripleT3.spqrAbs]
  have hk : Model.SparseRatchet.epochsKept = 2 := rfl
  have hep := hmr.sparseEpoch
  refine ⟨by have := hpre.2.1; omega, ?_, ?_, by omega, ?_⟩
  · intro q hq
    have := (hsp.epoch_window q hq).1
    omega
  · intro sk hsk
    obtain ⟨q, hq, he⟩ := hsp.skipped_chained sk hsk
    have := (hsp.epoch_window q hq).1
    omega
  · intro q hq ch hch
    have := hmr.sparseCounters q hq ch hch
    omega

/-- **The providers of the encrypt route at every session that passes `Session::invariant`, has any budget
`CounterRoom s k` and whose model agreement is not `headerReceived`**: both Triple condition records, for every generated
run. -/
theorem encryptProviders_of_invariant [Tacenta.SessionUnitT1.DerivedKeysModel] {R : Type}
    {rc : rand_core_1.RngCore R} {crc : rand_core_1.CryptoRng R}
    {trace : R → List Model.Lifecycle.Key} (hct1 : Tacenta.SessionUnitBraidT1.Ct1LenTotal) {dh : DhView}
    (kem : KemView) {K : Model.Braid.Kem} (view : Model.Lifecycle.CodewordView)
    (oracle : Model.Lifecycle.Oracle) {s : lifecycle.Session} {m : Model.Lifecycle.Session} {k : Nat}
    (hinv : lifecycle.Session.invariant s = ok true) (hrel : SessionRefines dh K s m)
    (hroom : CounterRoom s k)
    (hmodel : ∀ e a s0 hk d, m.braid ≠ .headerReceived e a s0 hk d)
    (plaintext : Slice Std.U8) (rng : R) :
    Nonempty (EncryptNonterminalRouteProviders rc crc trace dh kem K view oracle s m plaintext rng) := by
  obtain ⟨hroomC, hcb, hsb, hepoch, hcounter⟩ := tripleStoreFacts_of_invariant hct1 hinv hrel hroom
  exact ⟨{
    refusal := fun _ _ _ _ _ _ _ _ _ _ _ hsparse _ hev =>
      { derivedKeys := inferInstance, room := hroomC, chainBound := hcb, skippedBound := hsb
        newBound := by
          intro o ho
          rw [sparseOutput_none_of_scope hmodel hsparse hev] at ho
          cases ho
        epochBound := hepoch, counterBound := hcounter }
    success := fun _ _ _ _ _ _ _ _ _ _ _ _ hsparse _ hev =>
      { derivedKeys := inferInstance, room := hroomC, chainBound := hcb, skippedBound := hsb
        newBound := by
          intro o ho
          rw [sparseOutput_none_of_scope hmodel hsparse hev] at ho
          cases ho
        epochBound := hepoch, counterBound := hcounter } }⟩

/-- A model agreement related to a code agreement that is not `HeaderReceived` is not `headerReceived`. -/
theorem model_not_headerReceived {K : Model.Braid.Kem} {st : tacenta_braid.State} {m : Model.Braid.BraidState}
    (h : Tacenta.SessionUnitBraidT3.StateRefines K st m)
    (hns : ∀ e a hdr dec, st ≠ .HeaderReceived e a hdr dec) :
    ∀ e a s0 hk d, m ≠ .headerReceived e a s0 hk d := by
  intro e a s0 hk d hm
  subst hm
  cases st <;> simp only [Tacenta.SessionUnitBraidT3.StateRefines] at h
  exact hns _ _ _ _ rfl

/-! ## The encrypt headroom at an invariant session -/

open Tacenta.UnitLifecycleRestoredSession (KemCiphertextLenBound)

/-- **`Session::structural_invariant` fixes a pending initial message's ciphertext length to
`kem::ciphertext_len`**: at every session it accepts that holds a pending initial message, the ciphertext has
exactly that many bytes.  No hypothesis about any opaque operation. -/
theorem pending_ciphertext_len_of_structural (s : lifecycle.Session) (p : lifecycle.PendingInitial)
    (hp : s.pending_initial = some p) (n : Usize) (hn : tacenta_boundary.kem.ciphertext_len = ok n)
    (h : lifecycle.Session.structural_invariant s = ok true) :
    p.kem_ciphertext.val.length = n.val := by
  by_contra hne
  have hb : (alloc.vec.Vec.len p.kem_ciphertext != n) = true := by
    simp only [bne_iff_ne, ne_eq]
    intro heq
    apply hne
    have := congrArg UScalar.val heq
    simpa [alloc.vec.Vec.len] using this
  unfold lifecycle.Session.structural_invariant at h
  simp only [hp, hn, hb, bind_tc_ok, core.option.Option.is_some, if_true] at h
  repeat' first
    | (obtain ⟨_, _, h⟩ := bind_eq_ok_inv h)
    | (split at h)
    | (simp at h)

/-- **`EncryptHeadroom` at every session that passes `Session::invariant`**, for every plaintext of at most
`Usize.max - 65770` bytes, under `DhCodecTotal`, `Ct1LenTotal` and `KemCiphertextLenBound`: the chain table and the
associated data from the invariant (`encryptHeadroom_iff_of_invariant`), a pending ciphertext of
`kem::ciphertext_len` bytes (`pending_ciphertext_len_of_structural`), at most 65536 by the law. -/
theorem encryptHeadroom_of_invariant (hdh : Tacenta.UnitLifecycleT1.DhCodecTotal)
    (hct1 : Tacenta.SessionUnitBraidT1.Ct1LenTotal) (hbound : KemCiphertextLenBound)
    (s : lifecycle.Session) (hinv : lifecycle.Session.invariant s = ok true)
    (plaintext : Slice U8) (hpt : plaintext.val.length + 65770 ≤ Usize.max) :
    Tacenta.UnitLifecycleT1.EncryptHeadroom s plaintext := by
  refine (Tacenta.UnitHeadroomInvariant.encryptHeadroom_iff_of_invariant hdh hct1 s hinv plaintext).mpr
    ⟨by omega, ?_⟩
  cases hp : s.pending_initial with
  | none => trivial
  | some p =>
      obtain ⟨n, hn, hle⟩ := hbound
      have hstr := ((session_invariant_iff s).mp hinv).1
      have hl := pending_ciphertext_len_of_structural s p hp n hn hstr
      simp only
      omega

/-! ## The encrypt refinement at every invariant session outside the sampling state -/

/-- **`Session::encrypt` refines the model's step and keeps `Session::invariant` and the counter budget at every
session that passes `Session::invariant`, has room for one operation and refines a model session, at every agreement
state but `HeaderReceived`.**  The route's per-call records are derived here rather than taken: the counted draw
record (`braidSendTraceCounted_of_scope`), the Triple providers (`encryptProviders_of_invariant`) and the encrypt
headroom (`encryptHeadroom_of_invariant`).  The call returns, its result, the session it returns and the draws it
leaves refine `Model.Lifecycle.encrypt` at the model session, and the session it returns passes
`Session::invariant` and has room for `k` operations.  Every outcome: success, the size refusal, the terminal
refusal, a failed key generation and a Triple refusal. -/
theorem encrypt_refines_keeps_invariant [Tacenta.SessionUnitT1.DerivedKeysModel]
    {R : Type} {rc : rand_core_1.RngCore R} {crc : rand_core_1.CryptoRng R}
    {trace : R → List Model.Lifecycle.Key} {dh : DhView} {kem : KemView}
    {view : Model.Lifecycle.CodewordView} {oracle : Model.Lifecycle.Oracle}
    (braid : BraidSendRefinementContracts rc oracle.braidKem)
    (triple : TripleSendRefinementContracts)
    (aead : Tacenta.UnitLifecycleT1.AeadSealBounded)
    (dhCodec : Tacenta.UnitLifecycleT1.DhCodecTotal)
    (oracleOf : OracleOf rc crc dh kem trace oracle)
    (codec : DhCodecOf dh) (codewordView : CodewordViewSendOf view)
    (hz80 : Tacenta.SessionUnitT3.ZeroizingRoundTrips80)
    (hz32 : ZeroizingRoundTrips (Array Std.U8 32#usize))
    (hzKeys : ZeroizingRoundTrips
      (Array Std.U8 32#usize × Array Std.U8 32#usize × Array Std.U8 16#usize))
    (laws : SendInvariantLaws oracle.braidKem) (hgen : KeyGenSeededFor oracle.braidKem rc crc trace)
    (hbound : KemCiphertextLenBound)
    (s : lifecycle.Session) (m : Model.Lifecycle.Session) (k : Nat)
    (hinv : lifecycle.Session.invariant s = ok true) (hrel : SessionRefines dh oracle.braidKem s m)
    (hroom : CounterRoom s (k + 1))
    (hlive : Tacenta.SessionUnitBraidT3.EncodersLive m.braid)
    (hns : ∀ e a hdr dec, s.braid.state ≠ .HeaderReceived e a hdr dec)
    (plaintext : Slice U8) (hpt : plaintext.val.length + 65770 ≤ Usize.max)
    (rng : R) (htrace : trace rng = oracle.draws)
    (hdraws : ∀ e a, s.braid.state = .KeysUnsampled e a → ∃ d1 d2 rest, trace rng = d1 :: d2 :: rest) :
    ∃ output, lifecycle.Session.encrypt rc crc s plaintext rng = ok output ∧
      StepRefines trace dh oracle.braidKem output
        (Model.Lifecycle.encrypt view oracle m (Tacenta.UnitLifecycleT3.sliceOf plaintext)) ∧
      lifecycle.Session.invariant output.2.1 = ok true ∧ CounterRoom output.2.1 k := by
  have hbinv := ((session_invariant_iff s).mp hinv).2.2
  have braidTrace := braidSendTraceCounted_of_scope (crc := crc) braid hgen rfl hrel hbinv hlive hns hdraws
  obtain ⟨providers⟩ := encryptProviders_of_invariant (rc := rc) (crc := crc) (trace := trace) braid.ct1Len kem
    view oracle hinv hrel hroom (model_not_headerReceived hrel.braid hns) plaintext rng
  have headroom := encryptHeadroom_of_invariant dhCodec braid.ct1Len hbound s hinv plaintext hpt
  obtain ⟨⟨r, s', rng'⟩, hcall, hstep⟩ := public_session_encrypt_of_send_contracts braid braidTrace triple aead
    dhCodec headroom oracleOf codec codewordView braid.hkdf hz80 hz32 hzKeys hrel htrace providers
  refine ⟨_, hcall, hstep, ?_⟩
  rcases r with bytes | e
  · exact encrypt_keeps_invariant_unless_sampling braid.kemClone braid.hka laws rc crc braid.rng dh view oracle s
      m k hinv hroom hrel hns plaintext _ rng bytes s' rng' hcall hstep.session
  · obtain ⟨h1, h2⟩ := encrypt_err_keeps_invariant rc crc s plaintext rng e s' rng' hinv hcall
    exact ⟨h1, h2 k (counterRoom_mono s (by omega) hroom)⟩

/-! ## The effects of a successful `encrypt` -/

/-- **The model's `encrypt` returns bytes only on its success arm**: the agreement's send returned a message and a
next state that has not failed, the Triple's send succeeded at the reported epoch with the agreement's output, the
session is the one given with the two replaced, and the oracle is the one the agreement's send left.  Model only. -/
theorem encrypt_ok_arm (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle)
    (m : Model.Lifecycle.Session) (pt : Model.Lifecycle.Bytes) (b : Model.Lifecycle.Bytes)
    (h : (Model.Lifecycle.encrypt view oracle m pt).result = .ok b) :
    ∃ msg ep out braidNext oracleNext tripleNext hd key,
      Model.Lifecycle.sendAgreement oracle m.braid = some ((msg, ep, out, braidNext), oracleNext) ∧
      Model.Lifecycle.braidFailed braidNext = false ∧
      Model.Triple.sendDetailed m.triple ep (Model.Lifecycle.sparseOutputOf out) = .ok (tripleNext, hd, key) ∧
      (Model.Lifecycle.encrypt view oracle m pt).session = { m with triple := tripleNext, braid := braidNext } ∧
      (Model.Lifecycle.encrypt view oracle m pt).oracle = oracleNext := by
  unfold Model.Lifecycle.encrypt at h ⊢
  by_cases hl : Model.Lifecycle.maxPlaintextLen < pt.length
  · simp [hl] at h
  simp only [hl, if_false] at h ⊢
  by_cases hf : Model.Lifecycle.agreementFailed m = true
  · simp [hf] at h
  simp only [hf, Bool.false_eq_true, if_false] at h ⊢
  rcases hsa : Model.Lifecycle.sendAgreement oracle m.braid with _ | ⟨⟨msg, ep, out, nxt⟩, oracleNext⟩
  · simp [hsa] at h
  simp only [hsa] at h ⊢
  by_cases hbf : Model.Lifecycle.braidFailed nxt = true
  · simp [hbf] at h
  simp only [hbf, Bool.false_eq_true, if_false] at h ⊢
  split at h
  · simp at h
  · rename_i agreementMessage
    split at h
    · simp at h
    · rename_i tripleNext header messageKey hsend
      split at h
      · simp at h
      · exact ⟨_, ep, out, nxt, oracleNext, tripleNext, header, messageKey, rfl, by simpa using hbf, hsend, rfl,
          rfl⟩

/-- **The effects of a successful `encrypt` at every invariant session outside the sampling state**, under the
hypotheses of `encrypt_refines_keeps_invariant`: on top of its conclusion, when the call returns bytes, the classical
sending counter of the session returned is one more than the session given's, its clock and its stored keys are as
given, the agreement's epoch is as given, and at a state whose send takes no draw (every state but `KeysUnsampled`)
the source's draws are as given. -/
theorem encrypt_refines_effects [Tacenta.SessionUnitT1.DerivedKeysModel]
    {R : Type} {rc : rand_core_1.RngCore R} {crc : rand_core_1.CryptoRng R}
    {trace : R → List Model.Lifecycle.Key} {dh : DhView} {kem : KemView}
    {view : Model.Lifecycle.CodewordView} {oracle : Model.Lifecycle.Oracle}
    (braid : BraidSendRefinementContracts rc oracle.braidKem)
    (triple : TripleSendRefinementContracts)
    (aead : Tacenta.UnitLifecycleT1.AeadSealBounded)
    (dhCodec : Tacenta.UnitLifecycleT1.DhCodecTotal)
    (oracleOf : OracleOf rc crc dh kem trace oracle)
    (codec : DhCodecOf dh) (codewordView : CodewordViewSendOf view)
    (hz80 : Tacenta.SessionUnitT3.ZeroizingRoundTrips80)
    (hz32 : ZeroizingRoundTrips (Array Std.U8 32#usize))
    (hzKeys : ZeroizingRoundTrips
      (Array Std.U8 32#usize × Array Std.U8 32#usize × Array Std.U8 16#usize))
    (laws : SendInvariantLaws oracle.braidKem) (hgen : KeyGenSeededFor oracle.braidKem rc crc trace)
    (hbound : KemCiphertextLenBound)
    (s : lifecycle.Session) (m : Model.Lifecycle.Session) (k : Nat)
    (hinv : lifecycle.Session.invariant s = ok true) (hrel : SessionRefines dh oracle.braidKem s m)
    (hroom : CounterRoom s (k + 1))
    (hlive : Tacenta.SessionUnitBraidT3.EncodersLive m.braid)
    (hns : ∀ e a hdr dec, s.braid.state ≠ .HeaderReceived e a hdr dec)
    (plaintext : Slice U8) (hpt : plaintext.val.length + 65770 ≤ Usize.max)
    (rng : R) (htrace : trace rng = oracle.draws)
    (hdraws : ∀ e a, s.braid.state = .KeysUnsampled e a → ∃ d1 d2 rest, trace rng = d1 :: d2 :: rest) :
    ∃ output, lifecycle.Session.encrypt rc crc s plaintext rng = ok output ∧
      StepRefines trace dh oracle.braidKem output
        (Model.Lifecycle.encrypt view oracle m (Tacenta.UnitLifecycleT3.sliceOf plaintext)) ∧
      lifecycle.Session.invariant output.2.1 = ok true ∧ CounterRoom output.2.1 k ∧
      ∀ bytes, output.1 = .Ok bytes →
        output.2.1.triple.classical.ns.val = s.triple.classical.ns.val + 1 ∧
        output.2.1.triple.classical.events = s.triple.classical.events ∧
        (Tacenta.SessionUnitTripleT3.ratchetAbs output.2.1.triple.classical).skipped =
          (Tacenta.SessionUnitTripleT3.ratchetAbs s.triple.classical).skipped ∧
        (Tacenta.SessionUnitBraidT1.State.epoch_val output.2.1.braid.state).val =
          (Tacenta.SessionUnitBraidT1.State.epoch_val s.braid.state).val ∧
        ((∀ e a, s.braid.state ≠ .KeysUnsampled e a) → trace output.2.2 = trace rng) := by
  obtain ⟨output, hcall, hstep, hinv', hroom'⟩ := encrypt_refines_keeps_invariant braid triple aead dhCodec
    oracleOf codec codewordView hz80 hz32 hzKeys laws hgen hbound s m k hinv hrel hroom hlive hns plaintext
    hpt rng htrace hdraws
  refine ⟨output, hcall, hstep, hinv', hroom', ?_⟩
  intro bytes hok
  have hres := hstep.result
  rw [hok] at hres
  generalize hmr : (Model.Lifecycle.encrypt view oracle m (Tacenta.UnitLifecycleT3.sliceOf plaintext)).result
    = r at hres
  rcases r with _ | b
  · exact hres.elim
  obtain ⟨msg, ep, out, braidNext, oracleNext, tripleNext, hd, key, hsa, hbf, hts, hsess, horacle⟩ :=
    encrypt_ok_arm view oracle m _ b hmr
  obtain ⟨c, dr, mkc, q, pqN, mkq, hcs, -, rfl⟩ := triple_send_parts hts
  have hrel' := hstep.session
  rw [hsess] at hrel'
  have hc' : Tacenta.SessionUnitTripleT3.ratchetAbs output.2.1.triple.classical = c := hrel'.triple.1
  have hc0 : Tacenta.SessionUnitTripleT3.ratchetAbs s.triple.classical = m.triple.classical := hrel.triple.1
  -- the classical send
  have hsend : c.ns = m.triple.classical.ns + 1 ∧ c.events = m.triple.classical.events ∧
      c.skipped = m.triple.classical.skipped := by
    unfold Model.Ratchet.sendDetailed at hcs
    split at hcs
    · simp at hcs
    · split at hcs
      · simp only [Except.ok.injEq, Prod.mk.injEq] at hcs
        obtain ⟨rfl, -, -⟩ := hcs
        exact ⟨rfl, rfl, rfl⟩
      · simp at hcs
  have hns' : output.2.1.triple.classical.ns.val = s.triple.classical.ns.val + 1 := by
    have h1 := congrArg Model.State.State.ns hc'
    have h0 := congrArg Model.State.State.ns hc0
    simp only [Tacenta.SessionUnitTripleT3.ratchetAbs] at h1 h0
    omega
  have hev : output.2.1.triple.classical.events = s.triple.classical.events := by
    have h1 := congrArg Model.State.State.events hc'
    have h0 := congrArg Model.State.State.events hc0
    simp only [Tacenta.SessionUnitTripleT3.ratchetAbs] at h1 h0
    exact UScalar.eq_of_val_eq (by omega)
  -- the agreement's epoch
  have hep : (Tacenta.SessionUnitBraidT1.State.epoch_val output.2.1.braid.state).val =
      (Tacenta.SessionUnitBraidT1.State.epoch_val s.braid.state).val := by
    rw [epoch_val_refines hrel'.braid, epoch_val_refines hrel.braid]
    obtain ⟨rand, hr⟩ := sendAgreement_is_send hsa
    rcases braid_send_epoch oracle.braidKem rand m.braid with h | h
    · rw [← h, ← hr]
    · rw [← hr] at h
      simp only at h
      rw [h] at hbf
      simp [Model.Lifecycle.braidFailed] at hbf
  refine ⟨hns', hev, by rw [hc', hc0]; exact hsend.2.2, hep, ?_⟩
  intro hku
  have hnd : Model.Lifecycle.braidSendNeedsDraw m.braid = false :=
    needsDraw_false_of_kind hrel.braid hku hns
  rw [Model.Lifecycle.sendAgreement_no_draw oracle m.braid hnd] at hsa
  simp only [Option.some.injEq, Prod.mk.injEq] at hsa
  rw [hstep.draws, horacle, ← hsa.2, htrace]

/-! ## The hypotheses as one record, and together on a run -/

open Tacenta.UnitLifecycleEstablishInitiatorShape (DhPublicValid KemCiphertextLenOf establishedModelOf
  establish_initiator_for_parts establish_initiator_for_admissible sessionRefines_established)

/-- **The hypotheses of `encrypt_refines_keeps_invariant`**, for one choice of every binder: the encrypt boundary
records and laws, the session's part (the invariant, the relation, room for `k + 1` operations, a live model encoder,
an agreement not at `HeaderReceived`), the plaintext bound, the trace equation and, at `KeysUnsampled`, two draws. -/
structure EncryptOfInvariantHypotheses {R : Type} (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R)
    (trace : R → List Model.Lifecycle.Key) (dh : DhView) (kem : KemView) (view : Model.Lifecycle.CodewordView)
    (oracle : Model.Lifecycle.Oracle) (s : lifecycle.Session) (m : Model.Lifecycle.Session) (k : Nat)
    (plaintext : Slice U8) (rng : R) : Prop where
  braid : BraidSendRefinementContracts rc oracle.braidKem
  triple : TripleSendRefinementContracts
  derivedKeys : Nonempty Tacenta.SessionUnitT1.DerivedKeysModel
  aead : Tacenta.UnitLifecycleT1.AeadSealBounded
  dhCodec : Tacenta.UnitLifecycleT1.DhCodecTotal
  oracleOf : OracleOf rc crc dh kem trace oracle
  codec : DhCodecOf dh
  codewordView : CodewordViewSendOf view
  zeroizing80 : Tacenta.SessionUnitT3.ZeroizingRoundTrips80
  zeroizing32 : ZeroizingRoundTrips (Array Std.U8 32#usize)
  zeroizingKeys : ZeroizingRoundTrips
    (Array Std.U8 32#usize × Array Std.U8 32#usize × Array Std.U8 16#usize)
  laws : SendInvariantLaws oracle.braidKem
  keyGen : KeyGenSeededFor oracle.braidKem rc crc trace
  kemCiphertextBound : KemCiphertextLenBound
  invariant : lifecycle.Session.invariant s = ok true
  related : SessionRefines dh oracle.braidKem s m
  room : CounterRoom s (k + 1)
  live : Tacenta.SessionUnitBraidT3.EncodersLive m.braid
  notSampling : ∀ e a hdr dec, s.braid.state ≠ .HeaderReceived e a hdr dec
  plaintextRoom : plaintext.val.length + 65770 ≤ Usize.max
  trace_eq : trace rng = oracle.draws
  draws : ∀ e a, s.braid.state = .KeysUnsampled e a → ∃ d1 d2 rest, trace rng = d1 :: d2 :: rest

/-- From the record, `encrypt_refines_keeps_invariant`'s conclusion. -/
theorem EncryptOfInvariantHypotheses.refines {R : Type} {rc : rand_core_1.RngCore R}
    {crc : rand_core_1.CryptoRng R} {trace : R → List Model.Lifecycle.Key} {dh : DhView} {kem : KemView}
    {view : Model.Lifecycle.CodewordView} {oracle : Model.Lifecycle.Oracle} {s : lifecycle.Session}
    {m : Model.Lifecycle.Session} {k : Nat} {plaintext : Slice U8} {rng : R}
    (H : EncryptOfInvariantHypotheses rc crc trace dh kem view oracle s m k plaintext rng) :
    ∃ output, lifecycle.Session.encrypt rc crc s plaintext rng = ok output ∧
      StepRefines trace dh oracle.braidKem output
        (Model.Lifecycle.encrypt view oracle m (Tacenta.UnitLifecycleT3.sliceOf plaintext)) ∧
      lifecycle.Session.invariant output.2.1 = ok true ∧ CounterRoom output.2.1 k := by
  obtain ⟨inst⟩ := H.derivedKeys
  exact encrypt_refines_keeps_invariant H.braid H.triple H.aead H.dhCodec H.oracleOf H.codec H.codewordView
    H.zeroizing80 H.zeroizing32 H.zeroizingKeys H.laws H.keyGen H.kemCiphertextBound s m k H.invariant H.related
    H.room H.live H.notSampling plaintext H.plaintextRoom rng H.trace_eq H.draws

/-- **The hypotheses of `encrypt_refines_keeps_invariant` hold together on a run**: at the real constants, under
the laws of `established_encrypt_successor_reachable` (a toy model holds them together,
`established_encrypt_laws_model`), at every 64-byte source where the model's key generation answers, there is an
establishment at whose session, with the model session read off it and one operation of budget, every field of
`EncryptOfInvariantHypotheses` holds for the empty plaintext from the byte-stream source, and `encrypt` there returns
`Ok`.  The state is `KeysUnsampled`, the one the established initiator's first send starts from: consistency in a
model, not exhibition of the shipping code, and no other agreement state is exhibited here. -/
theorem encrypt_of_invariant_hypotheses_jointly_satisfiable (K : Model.Braid.Kem) (dh : DhView) (kem : KemView)
    (L : Tacenta.UnitLifecycleDecryptScreen.DecryptJointLaws K dh)
    (A : Nonempty (Tacenta.UnitSatisfiabilityJoint.InitiatorAxiom
      Tacenta.UnitSatisfiabilityJoint.Interp.real Tacenta.UnitLifecycleIntegrationScreen.byteRng))
    (S : Tacenta.UnitLifecycleEstablishInitiatorShape.InitiatorSuccessShape
      Tacenta.UnitSatisfiabilityJoint.Interp.real Tacenta.UnitLifecycleIntegrationScreen.byteRng
      Tacenta.UnitLifecycleIntegrationScreen.byteCrc)
    (hpub : DhPublicValid) (hct : KemCiphertextLenOf)
    (X : Tacenta.UnitLifecycleEstablishedEncrypt.EncryptExtraLaws K dh kem)
    (hsizes : Tacenta.UnitLifecycleEstablishedEncrypt.KeyGenSizesOf K) (our : lifecycle.Identity)
    (seed : List Std.U8) (hseed : seed.length = 64)
    (hkg : K.keyGen (Model.Lifecycle.braidRandomness (seed.map Tacenta.SessionUnitBraidT3.u8)) ≠ none) :
    ∃ (oracle : Model.Lifecycle.Oracle) (s : lifecycle.Session) (bytes : alloc.vec.Vec Std.U8)
      (s' : lifecycle.Session) (rng' : List Std.U8),
      oracle.braidKem = K ∧
      EncryptOfInvariantHypotheses Tacenta.UnitLifecycleIntegrationScreen.byteRng
        Tacenta.UnitLifecycleIntegrationScreen.byteCrc Tacenta.UnitLifecycleIntegrationScreen.byteTrace dh kem
        Tacenta.UnitLifecycleRepair.witnessView oracle s (establishedModelOf dh s) 0
        Tacenta.UnitLifecycleEstablishedEncrypt.emptyPlaintext seed ∧
      lifecycle.Session.encrypt Tacenta.UnitLifecycleIntegrationScreen.byteRng
        Tacenta.UnitLifecycleIntegrationScreen.byteCrc s Tacenta.UnitLifecycleEstablishedEncrypt.emptyPlaintext
        seed = ok (core.result.Result.Ok bytes, s', rng') := by
  obtain ⟨oracle, bundle, s, rng1, bytes, s', rng', hK, H, hcall, -, -⟩ :=
    Tacenta.UnitLifecycleEstablishedEncrypt.established_encrypt_successor_reachable K dh kem L A S hpub hct X
      hsizes our seed hseed hkg
  have hinv := establish_initiator_for_admissible _ _ H.dhPublicValid H.kemCiphertextLen H.optionEq our bundle _
    [] rng1 s H.established
  have hrel := sessionRefines_established _ _ dh oracle.braidKem our bundle _ [] rng1 s H.established
  have hroom := counterRoom_established _ _ our bundle _ [] rng1 s H.established 1 (by
    simp [Std.U32.max_eq])
  obtain ⟨p, hp⟩ := establish_initiator_for_parts _ _ our bundle _ [] rng1 s H.established
  refine ⟨oracle, s, bytes, s', rng', hK, ?_, hcall⟩
  exact
    { braid := H.braid, triple := H.triple, derivedKeys := H.derivedKeys, aead := H.aead, dhCodec := H.dhCodec
      oracleOf := H.oracleOf, codec := H.codec, codewordView := H.codewordView, zeroizing80 := H.zeroizing80
      zeroizing32 := H.zeroizing32, zeroizingKeys := H.zeroizingKeys
      laws := ⟨H.kemLen, H.keyGenSizes, H.validateEk, H.divCeil⟩, keyGen := H.keyGen
      kemCiphertextBound := H.kemCiphertextBound, invariant := hinv, related := hrel, room := hroom
      live := by
        intro enc henc
        subst hp
        simp [establishedModelOf, Tacenta.UnitLifecycleEstablishInitiatorShape.InitiatorOutputParts.session,
          Tacenta.UnitLifecycleEstablishInitiatorShape.unsampledModelOf, Tacenta.SessionUnitBraidT3.EncoderOf] at henc
      notSampling := by
        intro e a hdr dec h
        subst hp
        simp [Tacenta.UnitLifecycleEstablishInitiatorShape.InitiatorOutputParts.session] at h
      plaintextRoom := H.room, trace_eq := H.trace_eq
      draws := fun _ _ _ => H.draws }

end Tacenta.UnitLifecycleEncryptCompose

-- The pins `genpins.py` writes after this line print each statement whole: with no cut at depth 50
-- (`pp.deepTerms`) and each omitted proof with its proposition, `(⋯ : P)` (`pp.proofs.withType`). `attest.py`
-- refuses a statement pin that prints a bare `⋯`, and every other `pp` option.
set_option pp.deepTerms true
set_option pp.proofs.withType true

/-! ## Pins

The constants each result depends on, and the statement of each result and definition, held by the
build.  `attest.py` requires every one of them (`REQUIRED_PINS`, `REQUIRED_STATEMENT_PINS`,
`REQUIRED_PRINT_FORM`). -/

/--
info: 'Tacenta.UnitLifecycleEncryptCompose.braid_send_failed_rng' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_kem.EncapsState,
 tacenta_kem.IncrementalKeyPair,
 tacenta_kem.encapsulate1,
 zeroize.Zeroizing,
 rand_core_1.error.Error,
 tacenta_kem.IncrementalKeyPair.generate,
 tacenta_kem.IncrementalKeyPair.header,
 zeroize.Zeroizing.new,
 Array.Insts.ZeroizeZeroize.zeroize,
 core.num.Usize.div_ceil,
 zeroize.Zeroize.Blanket.zeroize,
 tacenta_kem.EncapsState.Insts.CoreCloneClone.clone,
 tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone,
 zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEncryptCompose.braid_send_failed_rng

/--
info: 'Tacenta.UnitLifecycleEncryptCompose.braidSendTraceCounted_of_scope' depends on axioms: [propext,
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
 tacenta_boundary.dh.PrivateKey,
 tacenta_boundary.dh.PublicKeyBytes,
 tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_kem.IncrementalKeyPair.generate,
 tacenta_kem.IncrementalKeyPair.header,
 zeroize.Zeroizing.new,
 Array.Insts.ZeroizeZeroize.zeroize,
 alloc.vec.Vec.truncate,
 core.num.Usize.div_ceil,
 zeroize.Zeroize.Blanket.zeroize,
 tacenta_kem.EncapsState.Insts.CoreCloneClone.clone,
 tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone,
 zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEncryptCompose.braidSendTraceCounted_of_scope

/--
info: 'Tacenta.UnitLifecycleEncryptCompose.sparseOutput_none_of_scope' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_kem.EncapsState,
 tacenta_kem.IncrementalKeyPair,
 tacenta_kem.encapsulate1,
 tacenta_kem.encapsulate2,
 zeroize.Zeroizing,
 rand_core_1.error.Error,
 tacenta_boundary.dh.PrivateKey,
 tacenta_boundary.dh.PublicKeyBytes,
 tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_kem.IncrementalKeyPair.generate,
 tacenta_kem.IncrementalKeyPair.header,
 zeroize.Zeroizing.new,
 Array.Insts.ZeroizeZeroize.zeroize,
 alloc.vec.Vec.truncate,
 core.num.Usize.div_ceil,
 zeroize.Zeroize.Blanket.zeroize,
 tacenta_kem.EncapsState.Insts.CoreCloneClone.clone,
 tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone,
 zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEncryptCompose.sparseOutput_none_of_scope

/--
info: 'Tacenta.UnitLifecycleEncryptCompose.tripleStoreFacts_of_invariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_kem.CT1_LEN,
 tacenta_kem.CT2_LEN,
 tacenta_kem.EK_VECTOR_LEN,
 tacenta_kem.EncapsState,
 tacenta_kem.HEADER_LEN,
 tacenta_kem.IncrementalKeyPair,
 tacenta_kem.encapsulate2,
 tacenta_kem.validate_ek,
 tacenta_boundary.dh.PrivateKey,
 tacenta_boundary.dh.PublicKeyBytes,
 tacenta_boundary.dh.is_prime_order_public,
 tacenta_boundary.kem.ciphertext_len,
 tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_kem.IncrementalKeyPair.header,
 alloc.vec.Vec.truncate,
 core.num.Usize.div_ceil,
 tacenta_boundary.dh.PrivateKey.public_key,
 tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_boundary.dh.PublicKeyBytes.from_bytes,
 core.option.Option.Insts.CoreCmpPartialEqOption.eq]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEncryptCompose.tripleStoreFacts_of_invariant

/--
info: 'Tacenta.UnitLifecycleEncryptCompose.encryptProviders_of_invariant' depends on axioms: [propext,
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
 tacenta_boundary.aead.encrypt,
 tacenta_boundary.dh.PrivateKey,
 tacenta_boundary.dh.PublicKeyBytes,
 tacenta_boundary.dh.is_prime_order_public,
 tacenta_boundary.kem.KeyPair,
 tacenta_boundary.kem.ciphertext_len,
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
 tacenta_boundary.dh.PrivateKey.public_key,
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
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEncryptCompose.encryptProviders_of_invariant

/--
info: 'Tacenta.UnitLifecycleEncryptCompose.model_not_headerReceived' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_kem.EncapsState,
 tacenta_kem.IncrementalKeyPair,
 tacenta_kem.encapsulate2,
 tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_kem.IncrementalKeyPair.header,
 alloc.vec.Vec.truncate,
 core.num.Usize.div_ceil]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEncryptCompose.model_not_headerReceived

/--
info: 'Tacenta.UnitLifecycleEncryptCompose.pending_ciphertext_len_of_structural' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_kem.EncapsState,
 tacenta_kem.IncrementalKeyPair,
 tacenta_boundary.dh.PrivateKey,
 tacenta_boundary.dh.PublicKeyBytes,
 tacenta_boundary.dh.is_prime_order_public,
 tacenta_boundary.kem.ciphertext_len,
 tacenta_boundary.dh.PrivateKey.public_key,
 tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_boundary.dh.PublicKeyBytes.from_bytes,
 core.option.Option.Insts.CoreCmpPartialEqOption.eq]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEncryptCompose.pending_ciphertext_len_of_structural

/--
info: 'Tacenta.UnitLifecycleEncryptCompose.encryptHeadroom_of_invariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_kem.CT1_LEN,
 tacenta_kem.CT2_LEN,
 tacenta_kem.EK_VECTOR_LEN,
 tacenta_kem.EncapsState,
 tacenta_kem.HEADER_LEN,
 tacenta_kem.IncrementalKeyPair,
 tacenta_kem.validate_ek,
 zeroize.Zeroizing,
 tacenta_boundary.dh.PrivateKey,
 tacenta_boundary.dh.PublicKeyBytes,
 tacenta_boundary.dh.is_prime_order_public,
 tacenta_boundary.kem.ciphertext_len,
 tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_kem.IncrementalKeyPair.header,
 core.num.Usize.div_ceil,
 tacenta_boundary.dh.PrivateKey.from_bytes,
 tacenta_boundary.dh.PrivateKey.public_key,
 tacenta_boundary.dh.PrivateKey.to_bytes,
 tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_boundary.dh.PublicKeyBytes.from_bytes,
 core.option.Option.Insts.CoreCmpPartialEqOption.eq,
 tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes.eq]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEncryptCompose.encryptHeadroom_of_invariant

/--
info: 'Tacenta.UnitLifecycleEncryptCompose.encrypt_refines_keeps_invariant' depends on axioms: [propext,
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
#print axioms Tacenta.UnitLifecycleEncryptCompose.encrypt_refines_keeps_invariant

/--
info: 'Tacenta.UnitLifecycleEncryptCompose.encrypt_ok_arm' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEncryptCompose.encrypt_ok_arm

/--
info: 'Tacenta.UnitLifecycleEncryptCompose.encrypt_refines_effects' depends on axioms: [propext,
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
#print axioms Tacenta.UnitLifecycleEncryptCompose.encrypt_refines_effects

/--
info: 'Tacenta.UnitLifecycleEncryptCompose.EncryptOfInvariantHypotheses.refines' depends on axioms: [propext,
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
#print axioms Tacenta.UnitLifecycleEncryptCompose.EncryptOfInvariantHypotheses.refines

/--
info: 'Tacenta.UnitLifecycleEncryptCompose.encrypt_of_invariant_hypotheses_jointly_satisfiable' depends on axioms: [propext,
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
#print axioms Tacenta.UnitLifecycleEncryptCompose.encrypt_of_invariant_hypotheses_jointly_satisfiable

/--
info: @Tacenta.UnitLifecycleEncryptCompose.braid_send_failed_rng : ∀ {R : Type} (rc : rand_core_1.RngCore R)
  (crc : rand_core_1.CryptoRng R) (b : tacenta_braid.Braid),
  b.state = tacenta_braid.State.Failed →
    ∀ (rng : R) (msg : tacenta_braid.Msg) (ep : U64) (out : Option tacenta_braid.Output) (b' : tacenta_braid.Braid)
      (rng' : R), tacenta_braid.Braid.send rc crc b rng = ok ((msg, ep, out, b'), rng') → rng' = rng
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEncryptCompose.braid_send_failed_rng

/--
info: @Tacenta.UnitLifecycleEncryptCompose.braidSendTraceCounted_of_scope : ∀ {R : Type} {rc : rand_core_1.RngCore R}
  {crc : rand_core_1.CryptoRng R} {trace : R → List Model.Lifecycle.Key} {dh : Tacenta.UnitLifecycleT3.DhView}
  {K : Model.Braid.Kem} {oracle : Model.Lifecycle.Oracle} {real : lifecycle.Session} {model : Model.Lifecycle.Session}
  {rng : R},
  Tacenta.UnitLifecycleT3.BraidSendRefinementContracts rc K →
    Tacenta.UnitLifecycleEstablishedEncrypt.KeyGenSeededFor K rc crc trace →
      oracle.braidKem = K →
        Tacenta.UnitLifecycleT3.SessionRefines dh K real model →
          real.braid.invariant = ok true →
            Tacenta.SessionUnitBraidT3.EncodersLive model.braid →
              (∀ (e : U64) (a : tacenta_braid.Auth) (hdr : alloc.vec.Vec U8) (dec : tacenta_erasure.Decoder),
                  real.braid.state ≠ tacenta_braid.State.HeaderReceived e a hdr dec) →
                (∀ (e : U64) (a : tacenta_braid.Auth),
                    real.braid.state = tacenta_braid.State.KeysUnsampled e a →
                      ∃ d1 d2 rest, trace rng = d1 :: d2 :: rest) →
                  Tacenta.UnitLifecycleT3.BraidSendTraceAgreementCounted rc crc trace K oracle real model rng
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEncryptCompose.braidSendTraceCounted_of_scope

/--
info: @Tacenta.UnitLifecycleEncryptCompose.sparseOutput_none_of_scope : ∀ {R : Type} {rc : rand_core_1.RngCore R}
  {crc : rand_core_1.CryptoRng R} {trace : R → List Model.Lifecycle.Key} {dh : Tacenta.UnitLifecycleT3.DhView}
  {K : Model.Braid.Kem} {oracle : Model.Lifecycle.Oracle} {real : lifecycle.Session} {model : Model.Lifecycle.Session}
  {rng : R} {realMessage : tacenta_braid.Msg} {realEpoch : U64} {realOutput : Option tacenta_braid.Output}
  {realBraidNext : tacenta_braid.Braid} {rngNext : R} {sparseOutput : Option tacenta_spqr.Output},
  (∀ (e : ℕ) (a : Model.Braid.Auth) (s hk : Model.Braid.Bytes) (d : Model.Braid.Decoder),
      model.braid ≠ Model.Braid.BraidState.headerReceived e a s hk d) →
    Tacenta.UnitLifecycleT3.RealSparseConversion realOutput sparseOutput →
      Nonempty
          (Tacenta.UnitLifecycleT3.GeneratedBraidSuccessEvidence rc crc trace dh K oracle real model rng realMessage
            realEpoch realOutput realBraidNext rngNext) →
        sparseOutput = none
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEncryptCompose.sparseOutput_none_of_scope

/--
info: Tacenta.UnitLifecycleEncryptCompose.tripleStoreFacts_of_invariant : Tacenta.SessionUnitBraidT1.Ct1LenTotal →
  ∀ {dh : Tacenta.UnitLifecycleT3.DhView} {K : Model.Braid.Kem} {s : lifecycle.Session} {m : Model.Lifecycle.Session}
    {k : ℕ},
    s.invariant = ok true →
      Tacenta.UnitLifecycleT3.SessionRefines dh K s m →
        Tacenta.UnitLifecycleSendPreserve.CounterRoom s k →
          m.triple.postQuantum.chains.length + 1 < Usize.max ∧
            (∀ q ∈ m.triple.postQuantum.chains, q.1 + Model.SparseRatchet.epochsKept ≤ U64.max) ∧
              (∀ sk ∈ m.triple.postQuantum.skipped, sk.1 + Model.SparseRatchet.epochsKept ≤ U64.max) ∧
                m.triple.postQuantum.epoch + 1 < U64.max ∧
                  ∀ q ∈ m.triple.postQuantum.chains,
                    ∀ (ch : Model.SparseRatchet.Chain), q.2.send = some ch ∨ q.2.receive = some ch → ch.n < U64.max
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEncryptCompose.tripleStoreFacts_of_invariant

/--
info: @Tacenta.UnitLifecycleEncryptCompose.encryptProviders_of_invariant : ∀ [Tacenta.SessionUnitT1.DerivedKeysModel]
  {R : Type} {rc : rand_core_1.RngCore R} {crc : rand_core_1.CryptoRng R} {trace : R → List Model.Lifecycle.Key},
  Tacenta.SessionUnitBraidT1.Ct1LenTotal →
    ∀ {dh : Tacenta.UnitLifecycleT3.DhView} (kem : Tacenta.UnitLifecycleT3.KemView) {K : Model.Braid.Kem}
      (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle) {s : lifecycle.Session}
      {m : Model.Lifecycle.Session} {k : ℕ},
      s.invariant = ok true →
        Tacenta.UnitLifecycleT3.SessionRefines dh K s m →
          Tacenta.UnitLifecycleSendPreserve.CounterRoom s k →
            (∀ (e : ℕ) (a : Model.Braid.Auth) (s0 hk : Model.Braid.Bytes) (d : Model.Braid.Decoder),
                m.braid ≠ Model.Braid.BraidState.headerReceived e a s0 hk d) →
              ∀ (plaintext : Slice U8) (rng : R),
                Nonempty
                  (Tacenta.UnitLifecycleT3.EncryptNonterminalRouteProviders rc crc trace dh kem K view oracle s m
                    plaintext rng)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEncryptCompose.encryptProviders_of_invariant

/--
info: @Tacenta.UnitLifecycleEncryptCompose.model_not_headerReceived : ∀ {K : Model.Braid.Kem} {st : tacenta_braid.State}
  {m : Model.Braid.BraidState},
  Tacenta.SessionUnitBraidT3.StateRefines K st m →
    (∀ (e : U64) (a : tacenta_braid.Auth) (hdr : alloc.vec.Vec U8) (dec : tacenta_erasure.Decoder),
        st ≠ tacenta_braid.State.HeaderReceived e a hdr dec) →
      ∀ (e : ℕ) (a : Model.Braid.Auth) (s0 hk : Model.Braid.Bytes) (d : Model.Braid.Decoder),
        m ≠ Model.Braid.BraidState.headerReceived e a s0 hk d
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEncryptCompose.model_not_headerReceived

/--
info: Tacenta.UnitLifecycleEncryptCompose.pending_ciphertext_len_of_structural : ∀ (s : lifecycle.Session)
  (p : lifecycle.PendingInitial),
  s.pending_initial = some p →
    ∀ (n : Usize),
      tacenta_boundary.kem.ciphertext_len = ok n → s.structural_invariant = ok true → (↑p.kem_ciphertext).length = ↑n
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEncryptCompose.pending_ciphertext_len_of_structural

/--
info: Tacenta.UnitLifecycleEncryptCompose.encryptHeadroom_of_invariant : Tacenta.UnitLifecycleT1.DhCodecTotal →
  Tacenta.SessionUnitBraidT1.Ct1LenTotal →
    Tacenta.UnitLifecycleRestoredSession.KemCiphertextLenBound →
      ∀ (s : lifecycle.Session),
        s.invariant = ok true →
          ∀ (plaintext : Slice U8),
            (↑plaintext).length + 65770 ≤ Usize.max → Tacenta.UnitLifecycleT1.EncryptHeadroom s plaintext
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEncryptCompose.encryptHeadroom_of_invariant

/--
info: @Tacenta.UnitLifecycleEncryptCompose.encrypt_refines_keeps_invariant : ∀ [Tacenta.SessionUnitT1.DerivedKeysModel]
  {R : Type} {rc : rand_core_1.RngCore R} {crc : rand_core_1.CryptoRng R} {trace : R → List Model.Lifecycle.Key}
  {dh : Tacenta.UnitLifecycleT3.DhView} {kem : Tacenta.UnitLifecycleT3.KemView} {view : Model.Lifecycle.CodewordView}
  {oracle : Model.Lifecycle.Oracle},
  Tacenta.UnitLifecycleT3.BraidSendRefinementContracts rc oracle.braidKem →
    Tacenta.UnitLifecycleT3.TripleSendRefinementContracts →
      Tacenta.UnitLifecycleT1.AeadSealBounded →
        Tacenta.UnitLifecycleT1.DhCodecTotal →
          Tacenta.UnitLifecycleT3.OracleOf rc crc dh kem trace oracle →
            Tacenta.UnitLifecycleT3.DhCodecOf dh →
              Tacenta.UnitLifecycleT3.CodewordViewSendOf view →
                Tacenta.SessionUnitT3.ZeroizingRoundTrips80 →
                  Tacenta.UnitLifecycleT3.ZeroizingRoundTrips (Std.Array U8 32#usize) →
                    Tacenta.UnitLifecycleT3.ZeroizingRoundTrips
                        (Std.Array U8 32#usize × Std.Array U8 32#usize × Std.Array U8 16#usize) →
                      Tacenta.UnitLifecycleEncryptPreserve.SendInvariantLaws oracle.braidKem →
                        Tacenta.UnitLifecycleEstablishedEncrypt.KeyGenSeededFor oracle.braidKem rc crc trace →
                          Tacenta.UnitLifecycleRestoredSession.KemCiphertextLenBound →
                            ∀ (s : lifecycle.Session) (m : Model.Lifecycle.Session) (k : ℕ),
                              s.invariant = ok true →
                                Tacenta.UnitLifecycleT3.SessionRefines dh oracle.braidKem s m →
                                  Tacenta.UnitLifecycleSendPreserve.CounterRoom s (k + 1) →
                                    Tacenta.SessionUnitBraidT3.EncodersLive m.braid →
                                      (∀ (e : U64) (a : tacenta_braid.Auth) (hdr : alloc.vec.Vec U8)
                                          (dec : tacenta_erasure.Decoder),
                                          s.braid.state ≠ tacenta_braid.State.HeaderReceived e a hdr dec) →
                                        ∀ (plaintext : Slice U8),
                                          (↑plaintext).length + 65770 ≤ Usize.max →
                                            ∀ (rng : R),
                                              trace rng = oracle.draws →
                                                (∀ (e : U64) (a : tacenta_braid.Auth),
                                                    s.braid.state = tacenta_braid.State.KeysUnsampled e a →
                                                      ∃ d1 d2 rest, trace rng = d1 :: d2 :: rest) →
                                                  ∃ output,
                                                    lifecycle.Session.encrypt rc crc s plaintext rng = ok output ∧
                                                      Tacenta.UnitLifecycleT3.StepRefines trace dh oracle.braidKem
                                                          output
                                                          (Model.Lifecycle.encrypt view oracle m
                                                            (Tacenta.UnitLifecycleT3.sliceOf plaintext)) ∧
                                                        output.2.1.invariant = ok true ∧
                                                          Tacenta.UnitLifecycleSendPreserve.CounterRoom output.2.1 k
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEncryptCompose.encrypt_refines_keeps_invariant

/--
info: Tacenta.UnitLifecycleEncryptCompose.encrypt_ok_arm : ∀ (view : Model.Lifecycle.CodewordView)
  (oracle : Model.Lifecycle.Oracle) (m : Model.Lifecycle.Session) (pt b : Model.Lifecycle.Bytes),
  (Model.Lifecycle.encrypt view oracle m pt).result = Except.ok b →
    ∃ msg ep out braidNext oracleNext tripleNext hd key,
      Model.Lifecycle.sendAgreement oracle m.braid = some ((msg, ep, out, braidNext), oracleNext) ∧
        Model.Lifecycle.braidFailed braidNext = false ∧
          Model.Triple.sendDetailed m.triple ep (Model.Lifecycle.sparseOutputOf out) = Except.ok (tripleNext, hd, key) ∧
            (Model.Lifecycle.encrypt view oracle m pt).session =
                { triple := tripleNext, braid := braidNext, ratchetPrivate := m.ratchetPrivate,
                  identityAd := m.identityAd, ourIdentityPublic := m.ourIdentityPublic,
                  peerIdentityPublic := m.peerIdentityPublic, pendingInitial := m.pendingInitial,
                  establishedEphemeral := m.establishedEphemeral } ∧
              (Model.Lifecycle.encrypt view oracle m pt).oracle = oracleNext
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEncryptCompose.encrypt_ok_arm

/--
info: @Tacenta.UnitLifecycleEncryptCompose.encrypt_refines_effects : ∀ [Tacenta.SessionUnitT1.DerivedKeysModel] {R : Type}
  {rc : rand_core_1.RngCore R} {crc : rand_core_1.CryptoRng R} {trace : R → List Model.Lifecycle.Key}
  {dh : Tacenta.UnitLifecycleT3.DhView} {kem : Tacenta.UnitLifecycleT3.KemView} {view : Model.Lifecycle.CodewordView}
  {oracle : Model.Lifecycle.Oracle},
  Tacenta.UnitLifecycleT3.BraidSendRefinementContracts rc oracle.braidKem →
    Tacenta.UnitLifecycleT3.TripleSendRefinementContracts →
      Tacenta.UnitLifecycleT1.AeadSealBounded →
        Tacenta.UnitLifecycleT1.DhCodecTotal →
          Tacenta.UnitLifecycleT3.OracleOf rc crc dh kem trace oracle →
            Tacenta.UnitLifecycleT3.DhCodecOf dh →
              Tacenta.UnitLifecycleT3.CodewordViewSendOf view →
                Tacenta.SessionUnitT3.ZeroizingRoundTrips80 →
                  Tacenta.UnitLifecycleT3.ZeroizingRoundTrips (Std.Array U8 32#usize) →
                    Tacenta.UnitLifecycleT3.ZeroizingRoundTrips
                        (Std.Array U8 32#usize × Std.Array U8 32#usize × Std.Array U8 16#usize) →
                      Tacenta.UnitLifecycleEncryptPreserve.SendInvariantLaws oracle.braidKem →
                        Tacenta.UnitLifecycleEstablishedEncrypt.KeyGenSeededFor oracle.braidKem rc crc trace →
                          Tacenta.UnitLifecycleRestoredSession.KemCiphertextLenBound →
                            ∀ (s : lifecycle.Session) (m : Model.Lifecycle.Session) (k : ℕ),
                              s.invariant = ok true →
                                Tacenta.UnitLifecycleT3.SessionRefines dh oracle.braidKem s m →
                                  Tacenta.UnitLifecycleSendPreserve.CounterRoom s (k + 1) →
                                    Tacenta.SessionUnitBraidT3.EncodersLive m.braid →
                                      (∀ (e : U64) (a : tacenta_braid.Auth) (hdr : alloc.vec.Vec U8)
                                          (dec : tacenta_erasure.Decoder),
                                          s.braid.state ≠ tacenta_braid.State.HeaderReceived e a hdr dec) →
                                        ∀ (plaintext : Slice U8),
                                          (↑plaintext).length + 65770 ≤ Usize.max →
                                            ∀ (rng : R),
                                              trace rng = oracle.draws →
                                                (∀ (e : U64) (a : tacenta_braid.Auth),
                                                    s.braid.state = tacenta_braid.State.KeysUnsampled e a →
                                                      ∃ d1 d2 rest, trace rng = d1 :: d2 :: rest) →
                                                  ∃ output,
                                                    lifecycle.Session.encrypt rc crc s plaintext rng = ok output ∧
                                                      Tacenta.UnitLifecycleT3.StepRefines trace dh oracle.braidKem
                                                          output
                                                          (Model.Lifecycle.encrypt view oracle m
                                                            (Tacenta.UnitLifecycleT3.sliceOf plaintext)) ∧
                                                        output.2.1.invariant = ok true ∧
                                                          Tacenta.UnitLifecycleSendPreserve.CounterRoom output.2.1 k ∧
                                                            ∀ (bytes : alloc.vec.Vec U8),
                                                              output.1 = core.result.Result.Ok bytes →
                                                                ↑output.2.1.triple.classical.ns =
                                                                    ↑s.triple.classical.ns + 1 ∧
                                                                  output.2.1.triple.classical.events =
                                                                      s.triple.classical.events ∧
                                                                    (Tacenta.SessionUnitTripleT3.ratchetAbs
                                                                            output.2.1.triple.classical).skipped =
                                                                        (Tacenta.SessionUnitTripleT3.ratchetAbs
                                                                            s.triple.classical).skipped ∧
                                                                      ↑(Tacenta.SessionUnitBraidT1.State.epoch_val
                                                                              output.2.1.braid.state) =
                                                                          ↑(Tacenta.SessionUnitBraidT1.State.epoch_val
                                                                              s.braid.state) ∧
                                                                        ((∀ (e : U64) (a : tacenta_braid.Auth),
                                                                            s.braid.state ≠
                                                                              tacenta_braid.State.KeysUnsampled e a) →
                                                                          trace output.2.2 = trace rng)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEncryptCompose.encrypt_refines_effects

/--
info: @Tacenta.UnitLifecycleEncryptCompose.EncryptOfInvariantHypotheses.refines : ∀ {R : Type} {rc : rand_core_1.RngCore R}
  {crc : rand_core_1.CryptoRng R} {trace : R → List Model.Lifecycle.Key} {dh : Tacenta.UnitLifecycleT3.DhView}
  {kem : Tacenta.UnitLifecycleT3.KemView} {view : Model.Lifecycle.CodewordView} {oracle : Model.Lifecycle.Oracle}
  {s : lifecycle.Session} {m : Model.Lifecycle.Session} {k : ℕ} {plaintext : Slice U8} {rng : R},
  Tacenta.UnitLifecycleEncryptCompose.EncryptOfInvariantHypotheses rc crc trace dh kem view oracle s m k plaintext rng →
    ∃ output,
      lifecycle.Session.encrypt rc crc s plaintext rng = ok output ∧
        Tacenta.UnitLifecycleT3.StepRefines trace dh oracle.braidKem output
            (Model.Lifecycle.encrypt view oracle m (Tacenta.UnitLifecycleT3.sliceOf plaintext)) ∧
          output.2.1.invariant = ok true ∧ Tacenta.UnitLifecycleSendPreserve.CounterRoom output.2.1 k
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEncryptCompose.EncryptOfInvariantHypotheses.refines

/--
info: Tacenta.UnitLifecycleEncryptCompose.encrypt_of_invariant_hypotheses_jointly_satisfiable : ∀ (K : Model.Braid.Kem)
  (dh : Tacenta.UnitLifecycleT3.DhView) (kem : Tacenta.UnitLifecycleT3.KemView),
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
                      ∃ oracle s bytes s' rng',
                        oracle.braidKem = K ∧
                          Tacenta.UnitLifecycleEncryptCompose.EncryptOfInvariantHypotheses
                              Tacenta.UnitLifecycleIntegrationScreen.byteRng
                              Tacenta.UnitLifecycleIntegrationScreen.byteCrc
                              Tacenta.UnitLifecycleIntegrationScreen.byteTrace dh kem
                              Tacenta.UnitLifecycleRepair.witnessView oracle s
                              (Tacenta.UnitLifecycleEstablishInitiatorShape.establishedModelOf dh s) 0
                              Tacenta.UnitLifecycleEstablishedEncrypt.emptyPlaintext seed ∧
                            lifecycle.Session.encrypt Tacenta.UnitLifecycleIntegrationScreen.byteRng
                                Tacenta.UnitLifecycleIntegrationScreen.byteCrc s
                                Tacenta.UnitLifecycleEstablishedEncrypt.emptyPlaintext seed =
                              ok (core.result.Result.Ok bytes, s', rng')
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEncryptCompose.encrypt_of_invariant_hypotheses_jointly_satisfiable

/--
info: structure Tacenta.UnitLifecycleEncryptCompose.EncryptOfInvariantHypotheses {R : Type} (rc : rand_core_1.RngCore R)
  (crc : rand_core_1.CryptoRng R) (trace : R → List Model.Lifecycle.Key) (dh : Tacenta.UnitLifecycleT3.DhView)
  (kem : Tacenta.UnitLifecycleT3.KemView) (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle)
  (s : lifecycle.Session) (m : Model.Lifecycle.Session) (k : ℕ) (plaintext : Slice U8) (rng : R) : Prop
number of parameters: 13
fields:
  Tacenta.UnitLifecycleEncryptCompose.EncryptOfInvariantHypotheses.braid : Tacenta.UnitLifecycleT3.BraidSendRefinementContracts
      rc oracle.braidKem
  Tacenta.UnitLifecycleEncryptCompose.EncryptOfInvariantHypotheses.triple : Tacenta.UnitLifecycleT3.TripleSendRefinementContracts
  Tacenta.UnitLifecycleEncryptCompose.EncryptOfInvariantHypotheses.derivedKeys : Nonempty
      Tacenta.SessionUnitT1.DerivedKeysModel
  Tacenta.UnitLifecycleEncryptCompose.EncryptOfInvariantHypotheses.aead : Tacenta.UnitLifecycleT1.AeadSealBounded
  Tacenta.UnitLifecycleEncryptCompose.EncryptOfInvariantHypotheses.dhCodec : Tacenta.UnitLifecycleT1.DhCodecTotal
  Tacenta.UnitLifecycleEncryptCompose.EncryptOfInvariantHypotheses.oracleOf : Tacenta.UnitLifecycleT3.OracleOf rc crc dh
      kem trace oracle
  Tacenta.UnitLifecycleEncryptCompose.EncryptOfInvariantHypotheses.codec : Tacenta.UnitLifecycleT3.DhCodecOf dh
  Tacenta.UnitLifecycleEncryptCompose.EncryptOfInvariantHypotheses.codewordView : Tacenta.UnitLifecycleT3.CodewordViewSendOf
      view
  Tacenta.UnitLifecycleEncryptCompose.EncryptOfInvariantHypotheses.zeroizing80 : Tacenta.SessionUnitT3.ZeroizingRoundTrips80
  Tacenta.UnitLifecycleEncryptCompose.EncryptOfInvariantHypotheses.zeroizing32 : Tacenta.UnitLifecycleT3.ZeroizingRoundTrips
      (Std.Array U8 32#usize)
  Tacenta.UnitLifecycleEncryptCompose.EncryptOfInvariantHypotheses.zeroizingKeys : Tacenta.UnitLifecycleT3.ZeroizingRoundTrips
      (Std.Array U8 32#usize × Std.Array U8 32#usize × Std.Array U8 16#usize)
  Tacenta.UnitLifecycleEncryptCompose.EncryptOfInvariantHypotheses.laws : Tacenta.UnitLifecycleEncryptPreserve.SendInvariantLaws
      oracle.braidKem
  Tacenta.UnitLifecycleEncryptCompose.EncryptOfInvariantHypotheses.keyGen : Tacenta.UnitLifecycleEstablishedEncrypt.KeyGenSeededFor
      oracle.braidKem rc crc trace
  Tacenta.UnitLifecycleEncryptCompose.EncryptOfInvariantHypotheses.kemCiphertextBound : Tacenta.UnitLifecycleRestoredSession.KemCiphertextLenBound
  Tacenta.UnitLifecycleEncryptCompose.EncryptOfInvariantHypotheses.invariant : s.invariant = ok true
  Tacenta.UnitLifecycleEncryptCompose.EncryptOfInvariantHypotheses.related : Tacenta.UnitLifecycleT3.SessionRefines dh
      oracle.braidKem s m
  Tacenta.UnitLifecycleEncryptCompose.EncryptOfInvariantHypotheses.room : Tacenta.UnitLifecycleSendPreserve.CounterRoom
      s (k + 1)
  Tacenta.UnitLifecycleEncryptCompose.EncryptOfInvariantHypotheses.live : Tacenta.SessionUnitBraidT3.EncodersLive
      m.braid
  Tacenta.UnitLifecycleEncryptCompose.EncryptOfInvariantHypotheses.notSampling : ∀ (e : U64) (a : tacenta_braid.Auth)
      (hdr : alloc.vec.Vec U8) (dec : tacenta_erasure.Decoder),
      s.braid.state ≠ tacenta_braid.State.HeaderReceived e a hdr dec
  Tacenta.UnitLifecycleEncryptCompose.EncryptOfInvariantHypotheses.plaintextRoom : (↑plaintext).length + 65770 ≤
      Usize.max
  Tacenta.UnitLifecycleEncryptCompose.EncryptOfInvariantHypotheses.trace_eq : trace rng = oracle.draws
  Tacenta.UnitLifecycleEncryptCompose.EncryptOfInvariantHypotheses.draws : ∀ (e : U64) (a : tacenta_braid.Auth),
      s.braid.state = tacenta_braid.State.KeysUnsampled e a → ∃ d1 d2 rest, trace rng = d1 :: d2 :: rest
constructor:
  Tacenta.UnitLifecycleEncryptCompose.EncryptOfInvariantHypotheses.mk {R : Type} {rc : rand_core_1.RngCore R}
    {crc : rand_core_1.CryptoRng R} {trace : R → List Model.Lifecycle.Key} {dh : Tacenta.UnitLifecycleT3.DhView}
    {kem : Tacenta.UnitLifecycleT3.KemView} {view : Model.Lifecycle.CodewordView} {oracle : Model.Lifecycle.Oracle}
    {s : lifecycle.Session} {m : Model.Lifecycle.Session} {k : ℕ} {plaintext : Slice U8} {rng : R}
    (braid : Tacenta.UnitLifecycleT3.BraidSendRefinementContracts rc oracle.braidKem)
    (triple : Tacenta.UnitLifecycleT3.TripleSendRefinementContracts)
    (derivedKeys : Nonempty Tacenta.SessionUnitT1.DerivedKeysModel) (aead : Tacenta.UnitLifecycleT1.AeadSealBounded)
    (dhCodec : Tacenta.UnitLifecycleT1.DhCodecTotal)
    (oracleOf : Tacenta.UnitLifecycleT3.OracleOf rc crc dh kem trace oracle)
    (codec : Tacenta.UnitLifecycleT3.DhCodecOf dh) (codewordView : Tacenta.UnitLifecycleT3.CodewordViewSendOf view)
    (zeroizing80 : Tacenta.SessionUnitT3.ZeroizingRoundTrips80)
    (zeroizing32 : Tacenta.UnitLifecycleT3.ZeroizingRoundTrips (Std.Array U8 32#usize))
    (zeroizingKeys :
      Tacenta.UnitLifecycleT3.ZeroizingRoundTrips
        (Std.Array U8 32#usize × Std.Array U8 32#usize × Std.Array U8 16#usize))
    (laws : Tacenta.UnitLifecycleEncryptPreserve.SendInvariantLaws oracle.braidKem)
    (keyGen : Tacenta.UnitLifecycleEstablishedEncrypt.KeyGenSeededFor oracle.braidKem rc crc trace)
    (kemCiphertextBound : Tacenta.UnitLifecycleRestoredSession.KemCiphertextLenBound)
    (invariant : s.invariant = ok true) (related : Tacenta.UnitLifecycleT3.SessionRefines dh oracle.braidKem s m)
    (room : Tacenta.UnitLifecycleSendPreserve.CounterRoom s (k + 1))
    (live : Tacenta.SessionUnitBraidT3.EncodersLive m.braid)
    (notSampling :
      ∀ (e : U64) (a : tacenta_braid.Auth) (hdr : alloc.vec.Vec U8) (dec : tacenta_erasure.Decoder),
        s.braid.state ≠ tacenta_braid.State.HeaderReceived e a hdr dec)
    (plaintextRoom : (↑plaintext).length + 65770 ≤ Usize.max) (trace_eq : trace rng = oracle.draws)
    (draws :
      ∀ (e : U64) (a : tacenta_braid.Auth),
        s.braid.state = tacenta_braid.State.KeysUnsampled e a → ∃ d1 d2 rest, trace rng = d1 :: d2 :: rest) :
    Tacenta.UnitLifecycleEncryptCompose.EncryptOfInvariantHypotheses rc crc trace dh kem view oracle s m k plaintext rng
-/
#guard_msgs in
#print Tacenta.UnitLifecycleEncryptCompose.EncryptOfInvariantHypotheses
