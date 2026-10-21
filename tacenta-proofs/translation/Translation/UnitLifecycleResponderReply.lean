import Translation.UnitLifecycleResponderSuccessor

/-!
# The responder's reply: `Session::encrypt` at the session `establish_responder` returned

`UnitLifecycleResponderSuccessor` shows that the session `sB'` that `establish_responder` returns on the bytes the
initiator's first `encrypt` emitted passes `Session::invariant` and meets the four counter ceilings, and that it refines
the model's step `firstReceiptSession`.  This module takes the next operation on that same session: the responder's
public `Session::encrypt` at `sB'`, on the same run (the same `sB'`, from the same call on the same bytes), and states
its one outcome and its effects.

## How

At `sB'` the agreement waits for the header (`NoHeaderReceived`, epoch 1, one 32-byte chunk of the 96-byte header
held), so:
* `braid_send_noHeader`: the translated `Braid::send` there returns the source it was given, the agreement as given
  (the state's clone is the state: `auth_clone_eq`, the decoder's clone by `erasureCloneAgrees`), an empty message
  (type `None`, no chunk) and no output.  The model's send there reads no draw either (`braidSendNeedsDraw` is false),
  so the dispatch layer's counted draw record holds (`braidSendTraceCounted_of_noHeader`).
* `reply_send_key`, `reply_model_step` (model only): the model's Triple send from `receiverAfterFirst` succeeds with
  header `firstHeader newPub` and key `replyKey` (the classical sending chain the receipt's second Diffie-Hellman step
  derived, the sparse chain `k2` at number 1), and the model's `encrypt` has one outcome: the bare reply frame
  (`replyFrame`, composite `replyComposite`: agreement type `none`, no chunk, no initial wrapper since the responder's
  model session has no pending initial message), no draw, the session with the Triple `replierAfterSend` and the
  agreement unchanged.
* `encryptProviders_reply`, `encryptHeadroom_reply`: the two Triple condition records of the route at the model
  session (one chain entry at epoch 0, counters 0 and 1, no stored key, no agreement output), and `EncryptHeadroom`
  from `Session::invariant` with no pending initial message (`encryptHeadroom_iff_of_invariant`).
* `responder_reply_refines`: the generic dispatch-layer route `public_session_encrypt_of_send_contracts` at every
  session related to `firstReceiptSession` that passes the invariant.
* `responder_first_frame_successor_keys`, `initiator_first_send_responder_successor_keys`: the derivations of
  `responder_first_frame_successor` and `initiator_first_send_responder_successor_hypotheses`, with three equations the
  receipt derives on that run kept in the conclusion instead of dropped: the model's root-key step from the responder's
  root `ec` and the initiator's `dh_out` gives the initiator's root and sending chain, the responder oracle's agreement
  of its draw with the initiator's ratchet key is the `dSend` the relation names, and the two sessions' associated data
  are equal.
* `initiator_first_send_responder_replies` composes them on the run: `sB'` and its relation come from the successor
  derivation, the refinement from `responder_reply_refines` at the responder's oracle with the source's draws, the
  bytes and the session from `reply_model_step`, and the source and agreement after the call from the walk
  (`encrypt_ok_parts`, `braid_send_noHeader`).

## The statements

* `initiator_first_send_responder_replies`: under the hypotheses of
  `initiator_first_send_responder_successor_hypotheses`, with the responder's oracle record `OracleOf` (instead of
  `DecryptOracleOf`) and `BraidSendRefinementContracts` at the responder's source, at every successful return of
  `establish_responder` on the bytes the initiator's first `encrypt` emitted, for every plaintext `ptR` of at most
  `Usize.max - 150` bytes and every source state `rngR`: `Session::encrypt` at `sB'` returns `Ok bytesR` and `sB''`
  and leaves `rngR` as it was; `sB''` is `sB'` with only the Triple Ratchet replaced (the agreement unchanged, no
  pending initial message); `bytesR` is `replyFrame` at the responder's oracle, the initiator's associated data, the
  fresh ratchet key and `replyKey`; `sB''` refines the model session after the receipt with the Triple
  `replierAfterSend`.  The three run equations above and the receipt's relation at `sB'` are in the conclusion.
* `first_send_reply_reachable`: the receipt's reach run continued with the responder's `encrypt` of the empty
  plaintext from the source `establish_responder` left, which returns bytes, takes no draw and keeps the agreement.

## Laws and premises

No new law and no new per-run premise.  Beyond the hypotheses of `initiator_first_send_responder_successor_hypotheses`,
the headline takes two boundary records at the responder's source: the full oracle record `OracleOf` (strengthening
`DecryptOracleOf`, which it implies) and the Braid send record `BraidSendRefinementContracts` at the responder
oracle's KEM.  The encrypt route's other records (`TripleSendRefinementContracts`, `AeadSealBounded`, `DhCodecTotal`,
`DhCodecOf`, `CodewordViewSendOf`, the three `zeroize` round trips) do not depend on the source and are the hypotheses
the initiator's first send already takes; `Ct1LenTotal` is a field of the responder's contracts.  The plaintext bound
`102 + (ptR.length + 48) ≤ Usize.max` holds of every plaintext of at most `2^32 - 151` bytes on a 32-bit target.
At this state the agreement's send reads neither randomness nor its oracle's Braid KEM, so no fact relating the two
parties' KEMs is needed; the Braid send record still carries the KEM agreement `KemAgreesFor` at the responder oracle's
KEM, as the generic route takes it for every state, and whether it could be dropped here is not checked.  The
headline so takes `KemAgreesFor` at both parties' KEMs (the initiator's and the responder's Braid send records); each
ties its KEM to the same translated code, so the premises carry an indirect, weak relation between the two KEMs.  The source
state `rngR` is free, with no draw premise.

## Trust

`responder_reply_refines`, the two `_keys` derivations, the headline and the reach are compiler-trusted through the
nine `native_decide` constants of the encrypt and decrypt refinements.  Every lemma before them rests on the kernel
and opaque constants only (pins below).

## Non-vacuity

No law is added, so `first_receipt_laws_model` already puts every law the statements take in one interpretation.
`first_send_reply_reachable` exhibits, at the real constants under the reach's laws, one run (last-resort path, empty
plaintexts) in which the responder's `encrypt` after the receipt returns bytes; there the responder's records are the
run's encrypt records, since the two parties share the oracle and the byte-stream source type.

## What it does not show

* The initiator's receipt of the reply (its `decrypt` at the session after its first send): not shown here;
  `UnitLifecycleResponderReplyReceipt` takes it, on the same run, under a per-run premise that the fresh ratchet key is
  not the peer key the initiator holds.
* A refusal `encrypt` can reach: at this state none occurs (the terminal guard is false, the agreement's send cannot
  fail at `NoHeaderReceived`, the Triple's send succeeds from counters 0 with a sending chain, the composite header is
  defined); the refusals reachable elsewhere in a session (the terminal guard, `ChainExhausted`, `NoSendingChain`)
  are not covered.
* `Session::invariant` or the ceilings at `sB''`, a second reply, a second message from the initiator, the header's
  later chunks, the responder's first sampling send, a restored copy of `sB'`.
* That the model session the successor refines holds only bytes the responder received (the receipt's relation is at
  the view that attributes the received codeword).  (The statement does not tie `rngR` to the source
  `establish_responder` left; it holds for every source state, that one included, and the reach takes it.)
* That the real primitives meet the boundary records or the laws the receipt rests on (`AeadRoundTrip`,
  `DhAgreeContributory`, `DhAgreeSymmetric`), that ML-KEM decapsulation agrees on a run (`FirstKemAgrees`), or
  `PrekeyIdsDistinct` from `PrekeyStore::invariant`; the model's own `establishResponder` equality; the one-time path
  in a run.  The results are compiler-trusted through the nine `native_decide` constants of the encrypt and decrypt
  refinements.
-/

open Aeneas Aeneas.Std Result
open tacenta_session_unit
open Tacenta.SessionUnitRatchetImportInv (bind_eq_ok_inv)

namespace Tacenta.UnitLifecycleResponderReply

open Tacenta.UnitLifecycleT3 (DhView DhCodecOf KemView arrayOf vecOf sliceOf SessionRefines OracleOf
  BraidSendRefinementContracts TripleSendRefinementContracts CodewordViewSendOf PublicEncryptWitness
  ZeroizingRoundTrips EncryptNonterminalRouteProviders BraidSendTraceAgreementCounted
  GeneratedBraidSuccessEvidence RealSparseConversion)
open Tacenta.UnitLifecycleResponderFirstReceipt (firstReceiptSession receiverAfterFirst firstHeader firstKey)

/-! ## The agreement's send while it waits for the header -/

/-- A 32-byte array's clone is the array. -/
theorem array_clone_u8 {n : Usize} (a : Array U8 n) :
    core.array.CloneArray.clone core.clone.CloneU8 a = ok a := by
  obtain ⟨r, hr, hp⟩ := Std.WP.spec_imp_exists
    (core.array.CloneArray.clone_spec core.clone.CloneU8 a (fun _ _ => rfl))
  rw [hr, ← hp]

/-- An authenticator's clone is the authenticator.  Hypothesis-free. -/
theorem auth_clone_eq (a : tacenta_braid.Auth) : tacenta_braid.Auth.Insts.CoreCloneClone.clone a = ok a := by
  unfold tacenta_braid.Auth.Insts.CoreCloneClone.clone
  simp [array_clone_u8]

/-- **`Braid::send` while the agreement waits for the header takes no randomness and changes nothing**: at a
`NoHeaderReceived` state, every return of the send leaves the source as given, returns the agreement as given, an
empty message (type `None`, no chunk) at the state's epoch, and no output.  Hypothesis-free (the decoder's clone is
the decoder, `erasureCloneAgrees`). -/
theorem braid_send_noHeader {R : Type} (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R)
    (b : tacenta_braid.Braid) (epoch : U64) (auth : tacenta_braid.Auth) (d : tacenta_erasure.Decoder)
    (hst : b.state = tacenta_braid.State.NoHeaderReceived epoch auth d) (rng : R)
    (x : tacenta_braid.Msg × U64 × Option tacenta_braid.Output × tacenta_braid.Braid) (rngN : R)
    (h : tacenta_braid.Braid.send rc crc b rng = ok (x, rngN)) :
    rngN = rng ∧ x.2.2.2 = b ∧
      x.1 = { epoch := epoch, ty := tacenta_braid.MsgType.None, data := none } ∧ x.2.2.1 = none := by
  obtain ⟨st⟩ := b
  simp only at hst
  subst hst
  unfold tacenta_braid.Braid.send at h
  simp only [tacenta_braid.State.Insts.CoreCloneClone.clone, lift, core.clone.impls.CloneU64.clone,
    bind_tc_ok] at h
  obtain ⟨s, hs, h⟩ := bind_eq_ok_inv h
  rw [auth_clone_eq] at hs
  simp only [bind_tc_ok] at hs
  obtain ⟨dd, hdd, hs2⟩ := bind_eq_ok_inv hs
  have hdd' := Tacenta.UnitSatisfiabilityErasureAgrees.erasureCloneAgrees.2 d dd hdd
  simp only [ok.injEq] at hs2
  subst hdd'
  subst hs2
  obtain ⟨⟨⟨m, o, nxt⟩, rng1⟩, hstep, h⟩ := bind_eq_ok_inv h
  simp only [tacenta_braid.Braid.step_send, tacenta_braid.state_back, tacenta_braid.Msg.empty, bind_tc_ok,
    ok.injEq, Prod.mk.injEq] at hstep
  obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := hstep
  obtain ⟨r, -, h⟩ := bind_eq_ok_inv h
  simp only [ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- At a `noHeaderReceived` model agreement the lifecycle's agreement send has no output. -/
theorem sendAgreement_noHeader_output (oracle oracleNext : Model.Lifecycle.Oracle) (e : Nat)
    (a : Model.Braid.Auth) (dec : Model.Braid.Decoder) (message : Option Model.Braid.Msg) (epoch : Nat)
    (output : Option Model.Braid.Output) (next : Model.Braid.BraidState)
    (h : Model.Lifecycle.sendAgreement oracle (.noHeaderReceived e a dec) =
      some ((message, epoch, output, next), oracleNext)) :
    output = none := by
  simp only [Model.Lifecycle.sendAgreement, Model.Lifecycle.braidSendNeedsDraw, Bool.false_eq_true, if_false,
    Model.Braid.send, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨⟨-, -, rfl, -⟩, -⟩ := h
  rfl

/-- **The counted draw record of the dispatch layer at a session whose agreement waits for the header**: the send
reads no draw (`braid_send_noHeader`), the model's send there reads none, and the state carries no encoder.
Hypothesis-free beyond the two state equations and the oracle's KEM. -/
theorem braidSendTraceCounted_of_noHeader {R : Type} {rc : rand_core_1.RngCore R}
    {crc : rand_core_1.CryptoRng R} {trace : R → List Model.Lifecycle.Key} {K : Model.Braid.Kem}
    {oracle : Model.Lifecycle.Oracle} {real : lifecycle.Session} {model : Model.Lifecycle.Session}
    {rng : R} (hkem : oracle.braidKem = K) (epoch : U64) (auth : tacenta_braid.Auth)
    (dec : tacenta_erasure.Decoder)
    (hreal : real.braid.state = .NoHeaderReceived epoch auth dec) (e : Nat) (a : Model.Braid.Auth)
    (decM : Model.Braid.Decoder) (hmodel : model.braid = .noHeaderReceived e a decM) :
    BraidSendTraceAgreementCounted rc crc trace K oracle real model rng where
  encodersLive := by
    intro enc henc
    rw [hmodel] at henc
    simp [Tacenta.SessionUnitBraidT3.EncoderOf] at henc
  braidKem := hkem
  noDrawTrace := by
    intro m ep o b rngNext hsend _
    obtain ⟨hr, -⟩ := braid_send_noHeader rc crc real.braid epoch auth dec hreal rng _ rngNext hsend
    rw [hr]
  drawTrace := by
    intro _ _ _ _ _ _ hneeds
    rw [hmodel] at hneeds
    simp [Model.Lifecycle.braidSendNeedsDraw] at hneeds
  drawPost := by
    intro _ _ _ _ _ _ hneeds
    rw [hmodel] at hneeds
    simp [Model.Lifecycle.braidSendNeedsDraw] at hneeds

/-! ## The model's reply -/

section Model
open Model.State (Key)

/-- The responder's Triple after its reply: the classical sending chain stepped once (one message sent), the
sparse sending chain of epoch 0 stepped once to number 1; everything else as after the first receive. -/
def replierAfterSend (ec prk k1 k2 a4 d dSend newPub : Key) : Model.Triple.State :=
  { classical :=
      { dhsPub := newPub, dhrPub := some a4,
        rk := (Model.State.kdfRk (Model.State.kdfRk ec d .tacenta).1 dSend .tacenta).1,
        cks := some (Model.State.kdfCk (Model.State.kdfRk (Model.State.kdfRk ec d .tacenta).1 dSend .tacenta).2).1,
        ckr := some (Model.State.kdfCk (Model.State.kdfRk ec d .tacenta).2).1,
        ns := 1, nr := 1, pn := 0, skipped := [], events := 1, labels := .tacenta }
    postQuantum :=
      { rk := prk, epoch := 0,
        chains :=
          [(0, { send := some ⟨(Model.SparseRatchet.kdfCk k2 1).1, 1⟩
                 receive := some ⟨(Model.SparseRatchet.kdfCk k1 1).1, 1⟩ })],
        skipped := [], direction := .b2a } }

/-- The reply's message key: the combination of the classical message key of the sending chain the first receive's
second Diffie-Hellman step derived and the sparse message key of `k2` at number 1. -/
def replyKey (ec k2 d dSend : Key) : Key :=
  firstKey (Model.State.kdfRk (Model.State.kdfRk ec d .tacenta).1 dSend .tacenta).2 k2

/-- **The model's reply send from the receiver after its first receipt**: header `firstHeader newPub` (the fresh
ratchet key, classical numbers 0 and 0, sparse epoch 0 and number 1), key `replyKey`, successor
`replierAfterSend`.  Hypothesis-free. -/
theorem reply_send_key (ec prk k1 k2 a4 d dSend newPub : Key) :
    Model.Triple.sendDetailed (receiverAfterFirst ec prk k1 k2 a4 d dSend newPub) 0 none =
      .ok (replierAfterSend ec prk k1 k2 a4 d dSend newPub, firstHeader newPub, replyKey ec k2 d dSend) := by
  simp [Model.Triple.sendDetailed, Model.Ratchet.sendDetailed, Model.SparseRatchet.sendDetailed,
    Model.SparseRatchet.maybeAdvanceDetailed, Model.SparseRatchet.findChains, receiverAfterFirst,
    replierAfterSend, firstHeader, replyKey, firstKey, Model.State.u32Max, Model.SparseRatchet.u64Max,
    Model.SparseRatchet.setChains]

/-- The reply's composite header: the fresh ratchet key, classical numbers 0 and 0, sparse epoch 0 and number 1,
agreement epoch 1, agreement type `none`, no chunk. -/
def replyComposite (newPub : Key) : Model.CompositeHeader.Composite :=
  { dh := newPub
    pn := UInt32.ofNat 0
    n := UInt32.ofNat 0
    pqEpoch := UInt64.ofNat 0
    pqN := UInt64.ofNat 1
    agEpoch := UInt64.ofNat 1
    agType := .none
    agChunk := none }

/-- The reply frame: the composite header and the plaintext sealed under the message key, with the associated data
`ad` followed by the encoded header. -/
def replyFrame (oracle : Model.Lifecycle.Oracle) (ad : Model.Lifecycle.Bytes) (newPub messageKey : Key)
    (plaintext : Model.Lifecycle.Bytes) : Model.Lifecycle.Bytes :=
  Model.CompositeHeader.encodeMessage (replyComposite newPub)
    (oracle.aeadSeal (Model.State.messageKeys messageKey .tacenta).1
      (Model.State.messageKeys messageKey .tacenta).2.1
      (Model.State.messageKeys messageKey .tacenta).2.2 plaintext
      (Model.Messages.concatAd ad (Model.CompositeHeader.encode (replyComposite newPub))))

/-- The reply frame reads only the oracle's seal: it is the same at the oracle with any draws. -/
theorem replyFrame_with_draws (oracle : Model.Lifecycle.Oracle) (draws : List Key) (ad : Model.Lifecycle.Bytes)
    (newPub messageKey : Key) (plaintext : Model.Lifecycle.Bytes) :
    replyFrame { oracle with draws := draws } ad newPub messageKey plaintext =
      replyFrame oracle ad newPub messageKey plaintext :=
  rfl

/-- **The model's `encrypt` at the receiver after its first receipt has one outcome**, for every codeword view,
oracle and plaintext, when the model session has no pending initial message: it reads no draw, returns the bare
reply frame (`replyFrame`, no initial wrapper), and leaves the session with the Triple after the send and everything
else, the agreement included, unchanged.  Model only. -/
theorem reply_model_step (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle)
    (mB : Model.Lifecycle.Session) (secret : Model.Lifecycle.Bytes) (rcv : Model.Braid.Chunk)
    (ec prk k1 k2 a4 d dSend newPub c : Key) (hpend : mB.pendingInitial = none) (pt : Model.Lifecycle.Bytes) :
    Model.Lifecycle.encrypt view oracle (firstReceiptSession mB secret rcv ec prk k1 k2 a4 d dSend newPub c) pt =
      { session := { firstReceiptSession mB secret rcv ec prk k1 k2 a4 d dSend newPub c with
          triple := replierAfterSend ec prk k1 k2 a4 d dSend newPub }
        result := .ok (replyFrame oracle mB.identityAd newPub (replyKey ec k2 d dSend) pt)
        oracle := oracle } := by
  simp [Model.Lifecycle.encrypt, Model.Lifecycle.agreementFailed, Model.Lifecycle.sendAgreement,
    Model.Lifecycle.braidSendNeedsDraw, Model.Braid.send, Model.Lifecycle.braidFailed,
    Model.Lifecycle.sparseOutputOf, Model.Braid.BraidState.epoch, firstReceiptSession, reply_send_key,
    Model.Lifecycle.compositeOf, Model.Lifecycle.compositeTypeOf, hpend, replyFrame, replyComposite,
    firstHeader]

end Model

/-! ## The route's providers and headroom at the session after the first receipt -/

/-- The sparse output the generated `encrypt` hands the Triple at a `noHeaderReceived` model agreement is `none`:
the model's send there has no output, so the code's has none. -/
theorem sparseOutput_none_of_noHeader {R : Type} {rc : rand_core_1.RngCore R}
    {crc : rand_core_1.CryptoRng R} {trace : R → List Model.Lifecycle.Key} {dh : DhView}
    {K : Model.Braid.Kem} {oracle : Model.Lifecycle.Oracle} {real : lifecycle.Session}
    {model : Model.Lifecycle.Session} {rng : R} {realMessage : tacenta_braid.Msg}
    {realEpoch : Std.U64} {realOutput : Option tacenta_braid.Output}
    {realBraidNext : tacenta_braid.Braid} {rngNext : R}
    {sparseOutput : Option tacenta_spqr.Output} (e : Nat) (a : Model.Braid.Auth) (decM : Model.Braid.Decoder)
    (hmodel : model.braid = .noHeaderReceived e a decM)
    (hsparse : RealSparseConversion realOutput sparseOutput)
    (hevidence : Nonempty (GeneratedBraidSuccessEvidence rc crc trace dh K oracle real model rng
      realMessage realEpoch realOutput realBraidNext rngNext)) :
    sparseOutput = none := by
  obtain ⟨ev⟩ := hevidence
  have hsend := ev.modelSend
  rw [hmodel] at hsend
  have hout := sendAgreement_noHeader_output _ _ _ _ _ _ _ _ _ hsend
  have hreal : realOutput = none := by
    have h := ev.output
    rw [hout] at h
    cases realOutput with
    | none => rfl
    | some o => exact h.elim
  cases hsparse with
  | none => rfl
  | some _ _ hsome _ => rw [hreal] at hsome; cases hsome

/-- **The providers of the encrypt route at the model session after the first receipt**: both Triple condition
records, for every generated run.  The model Triple there holds one chain entry at epoch 0 with counters 0 and 1,
no stored key, sparse epoch 0, and the agreement's send has no output. -/
theorem encryptProviders_reply [Tacenta.SessionUnitT1.DerivedKeysModel] {R : Type}
    {rc : rand_core_1.RngCore R} {crc : rand_core_1.CryptoRng R}
    {trace : R → List Model.Lifecycle.Key} (dh : DhView) (kem : KemView) (K : Model.Braid.Kem)
    (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle) (real : lifecycle.Session)
    (mB : Model.Lifecycle.Session) (secret : Model.Lifecycle.Bytes) (rcv : Model.Braid.Chunk)
    (ec prk k1 k2 a4 d dSend newPub c : Model.State.Key) (plaintext : Slice Std.U8) (rng : R) :
    Nonempty (EncryptNonterminalRouteProviders rc crc trace dh kem K view oracle real
      (firstReceiptSession mB secret rcv ec prk k1 k2 a4 d dSend newPub c) plaintext rng) := by
  have hu : 4294967295 ≤ Usize.max :=
    Tacenta.SessionUnitSessionT1.small_le_usize_max (le_refl _)
  let M := firstReceiptSession mB secret rcv ec prk k1 k2 a4 d dSend newPub c
  have hroom : M.triple.postQuantum.chains.length + 1 < Usize.max := by
    simp [M, firstReceiptSession, receiverAfterFirst]; omega
  have hcb : ∀ q ∈ M.triple.postQuantum.chains, q.1 + Model.SparseRatchet.epochsKept ≤ Std.U64.max := by
    simp [M, firstReceiptSession, receiverAfterFirst, Model.SparseRatchet.epochsKept, U64.max_eq]
  have hsb : ∀ sk ∈ M.triple.postQuantum.skipped, sk.1 + Model.SparseRatchet.epochsKept ≤ Std.U64.max := by
    simp [M, firstReceiptSession, receiverAfterFirst]
  have hepoch : M.triple.postQuantum.epoch + 1 < Std.U64.max := by
    simp [M, firstReceiptSession, receiverAfterFirst, U64.max_eq]
  have hcounter : ∀ q ∈ M.triple.postQuantum.chains, ∀ ch : Model.SparseRatchet.Chain,
      (q.2.send = some ch ∨ q.2.receive = some ch) → ch.n < Std.U64.max := by
    simp only [M, firstReceiptSession, receiverAfterFirst, List.mem_singleton]
    rintro q rfl ch (h | h) <;> (simp at h; subst h; simp [U64.max_eq])
  have hmodel : M.braid = .noHeaderReceived 1 (Model.Braid.Auth.init 1 secret)
      ((Model.Braid.Decoder.new (Model.Braid.headerSize + Model.Braid.macSize)).addChunk rcv) := rfl
  exact ⟨{
    refusal := fun _ _ _ _ _ _ _ _ _ _ _ hsparse _ hev =>
      { derivedKeys := inferInstance, room := hroom, chainBound := hcb, skippedBound := hsb
        newBound := by
          intro o ho
          rw [sparseOutput_none_of_noHeader _ _ _ hmodel hsparse hev] at ho
          cases ho
        epochBound := hepoch, counterBound := hcounter }
    success := fun _ _ _ _ _ _ _ _ _ _ _ _ hsparse _ hev =>
      { derivedKeys := inferInstance, room := hroom, chainBound := hcb, skippedBound := hsb
        newBound := by
          intro o ho
          rw [sparseOutput_none_of_noHeader _ _ _ hmodel hsparse hev] at ho
          cases ho
        epochBound := hepoch, counterBound := hcounter } }⟩

/-- **`EncryptHeadroom` at a session that passes `Session::invariant` and holds no pending initial message**, for
every plaintext of at most `Usize.max - 150` bytes, under `DhCodecTotal` and `Ct1LenTotal`
(`encryptHeadroom_iff_of_invariant`). -/
theorem encryptHeadroom_reply (hdh : Tacenta.UnitLifecycleT1.DhCodecTotal)
    (hct1 : Tacenta.SessionUnitBraidT1.Ct1LenTotal) (s : lifecycle.Session)
    (hinv : lifecycle.Session.invariant s = ok true) (hpend : s.pending_initial = none)
    (plaintext : Slice U8) (hroom : 102 + (plaintext.val.length + 48) ≤ Usize.max) :
    Tacenta.UnitLifecycleT1.EncryptHeadroom s plaintext :=
  (Tacenta.UnitHeadroomInvariant.encryptHeadroom_iff_of_invariant hdh hct1 s hinv plaintext).mpr
    ⟨hroom, by rw [hpend]; trivial⟩

/-- `OracleOf` does not read the oracle's draws: it holds of the same oracle with any draws. -/
theorem oracleOf_with_draws {R : Type} {rc : rand_core_1.RngCore R} {crc : rand_core_1.CryptoRng R}
    {dh : DhView} {kem : KemView} {trace : R → List Model.Lifecycle.Key} {oracle : Model.Lifecycle.Oracle}
    (h : OracleOf rc crc dh kem trace oracle) (draws : List Model.Lifecycle.Key) :
    OracleOf rc crc dh kem trace { oracle with draws := draws } :=
  ⟨h.dhPublic, h.dhAgree, h.identityValid, h.aeadSeal, h.aeadOpen, h.kemEncapsulateSuccess, h.kemInvalidKey,
    h.kemEncapsulateError, h.kemDecapsulate, h.sigVerify, h.sigSign, h.random32⟩

/-! ## The encrypt refinement at the session after the first receipt -/

/-- A session related to `firstReceiptSession` holds an agreement waiting for the header.  Hypothesis-free. -/
theorem noHeader_of_receipt_refines {dh : DhView} {K : Model.Braid.Kem} {sB : lifecycle.Session}
    {mB : Model.Lifecycle.Session} {secret : Model.Lifecycle.Bytes} {rcv : Model.Braid.Chunk}
    {ec prk k1 k2 a4 d dSend newPub c : Model.State.Key}
    (hrel : SessionRefines dh K sB (firstReceiptSession mB secret rcv ec prk k1 k2 a4 d dSend newPub c)) :
    ∃ e auth dec, sB.braid.state = tacenta_braid.State.NoHeaderReceived e auth dec := by
  have hb := hrel.braid
  simp only [firstReceiptSession] at hb
  rcases hst : sB.braid.state with _ | _ | _ | _ | _ | ⟨e, auth, dec⟩ | _ | _ | _ | _ | _ | _
  all_goals (rw [hst] at hb; try (simp [Tacenta.SessionUnitBraidT3.StateRefines] at hb; done))
  exact ⟨e, auth, dec, rfl⟩

/-- A session related to `firstReceiptSession` of a model session with no pending initial message holds none.
Hypothesis-free. -/
theorem pendingInitial_none_of_receipt_refines {dh : DhView} {K : Model.Braid.Kem} {sB : lifecycle.Session}
    {mB : Model.Lifecycle.Session} {secret : Model.Lifecycle.Bytes} {rcv : Model.Braid.Chunk}
    {ec prk k1 k2 a4 d dSend newPub c : Model.State.Key} (hpend : mB.pendingInitial = none)
    (hrel : SessionRefines dh K sB (firstReceiptSession mB secret rcv ec prk k1 k2 a4 d dSend newPub c)) :
    sB.pending_initial = none := by
  have h := hrel.pendingInitial
  simp only [firstReceiptSession, hpend, Option.map_eq_none_iff] at h
  exact h

/-- **The public `Session::encrypt` at a session related to the model session after the first receipt refines the
model's step**: for a session that refines `firstReceiptSession mB …` (whose pending initial message is none),
passes `Session::invariant`, every plaintext of at most `Usize.max - 150` bytes and every source state, the call
returns, and its result, its post-state and the draws it leaves refine `Model.Lifecycle.encrypt` there.  Under the
encrypt boundary records on that source, the oracle record, `DhCodecOf`, `CodewordViewSendOf`, three `zeroize`
round trips, `Ct1LenTotal` and the trace equation.  The generic dispatch-layer route
(`public_session_encrypt_of_send_contracts`) with its session-specific inputs discharged here. -/
theorem responder_reply_refines [Tacenta.SessionUnitT1.DerivedKeysModel] {R : Type}
    (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R)
    (trace : R → List Model.Lifecycle.Key) (dh : DhView) (kem : KemView)
    (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle)
    (braid : BraidSendRefinementContracts rc oracle.braidKem) (triple : TripleSendRefinementContracts)
    (aead : Tacenta.UnitLifecycleT1.AeadSealBounded) (dhCodec : Tacenta.UnitLifecycleT1.DhCodecTotal)
    (oracleOf : OracleOf rc crc dh kem trace oracle) (codec : DhCodecOf dh)
    (codewordView : CodewordViewSendOf view)
    (hz80 : Tacenta.SessionUnitT3.ZeroizingRoundTrips80)
    (hz32 : ZeroizingRoundTrips (Array Std.U8 32#usize))
    (hzKeys : ZeroizingRoundTrips
      (Array Std.U8 32#usize × Array Std.U8 32#usize × Array Std.U8 16#usize))
    (hct1 : Tacenta.SessionUnitBraidT1.Ct1LenTotal)
    (mB : Model.Lifecycle.Session) (secret : Model.Lifecycle.Bytes) (rcv : Model.Braid.Chunk)
    (ec prk k1 k2 a4 d dSend newPub c : Model.State.Key) (hpend : mB.pendingInitial = none)
    (sB : lifecycle.Session)
    (hrel : SessionRefines dh oracle.braidKem sB (firstReceiptSession mB secret rcv ec prk k1 k2 a4 d dSend newPub c))
    (hinv : lifecycle.Session.invariant sB = ok true)
    (plaintext : Slice Std.U8) (hroom : 102 + (plaintext.val.length + 48) ≤ Usize.max)
    (rng : R) (htrace : trace rng = oracle.draws) :
    PublicEncryptWitness rc crc trace dh oracle.braidKem view oracle sB
      (firstReceiptSession mB secret rcv ec prk k1 k2 a4 d dSend newPub c) plaintext rng := by
  have hpendR := pendingInitial_none_of_receipt_refines hpend hrel
  obtain ⟨e, auth, dec, hst⟩ := noHeader_of_receipt_refines hrel
  obtain ⟨providers⟩ := encryptProviders_reply dh kem oracle.braidKem view oracle sB mB secret rcv ec prk k1 k2
    a4 d dSend newPub c plaintext rng
  exact Tacenta.UnitLifecycleT3.public_session_encrypt_of_send_contracts braid
    (braidSendTraceCounted_of_noHeader rfl e auth dec hst 1 _ _ rfl) triple aead dhCodec
    (encryptHeadroom_reply dhCodec hct1 sB hinv hpendR plaintext hroom)
    oracleOf codec codewordView braid.hkdf hz80 hz32 hzKeys hrel htrace providers

/-! ## The run's keys, kept on the composed route -/

section Comp
variable {R : Type} {rc : rand_core_1.RngCore R} {crc : rand_core_1.CryptoRng R}
  {our : lifecycle.Identity} {bundle : lifecycle.PublishedBundle}

open Tacenta.UnitLifecycleT3 (modelChunkOf modelCodewordOf)
open Tacenta.UnitLifecycleEstablishInitiatorShape (establishedModelOf DhPublicValid dhPublicValid_canonical)
open Tacenta.UnitLifecycleEstablishedEncrypt (firstFrame initialWire)
open Tacenta.UnitLifecycleEstablishResponder (ResponderPreparedParts responderModelOf)
open Tacenta.UnitLifecycleResponderFirstFrame (InitiatorSecretParts DhAgreeSymmetric PrekeyIdsDistinct
  FirstKemAgrees responder_first_frame_prepares)
open Tacenta.UnitLifecycleDecryptRatchetT3 (DecryptOracleOf DecryptRatchetAgreements)
open Tacenta.UnitLifecycleResponderFirstReceipt (DhAgreeContributory AeadRoundTrip parts_of_first_frame
  responder_first_frame_inner_succeeds establish_responder_commit_of_inner first_kdf_model zeroized_eq
  first_identityAd_eq)
open Tacenta.UnitHeadroomInvariant (OptionEqU64Shape)
open Tacenta.UnitSatisfiabilityJoint (Interp Interp.real)

/-- **The session `establish_responder` returns on the initiator's first frame, with the run's keys**: under the
hypotheses of `responder_first_frame_successor`, at every return of the call that is `Ok (sB', ptB)`, there are the
call's prepare-phase parts `p`, the responder's root key `ec` before its first Diffie-Hellman step and the agreement
`dSend` of its draw with the initiator's ratchet key such that the model's root-key step from `ec` and the initiator's
`dh_out` is the initiator's root and sending chain, the responder oracle's agreement of the draw with the initiator's
ratchet key is `dSend`, the two sessions' associated data are equal, and `sB'` refines `firstReceiptSession` at those
keys, passes `Session::invariant` and meets `CounterHeadroom`.  The same derivation as `responder_first_frame_successor`,
with the key equations the inner receive derives kept.  Compiler-trusted through the nine `native_decide` constants of
the decrypt refinement. -/
theorem responder_first_frame_successor_keys [Tacenta.SessionUnitT1.DerivedKeysModel] {E : Type}
    (rcB : rand_core_1.RngCore E) (crcB : rand_core_1.CryptoRng E)
    (contracts : Tacenta.UnitLifecycleT1.EstablishResponderContracts rcB)
    (hpub : DhPublicValid) (hsym : DhAgreeSymmetric) (hcon : DhAgreeContributory) (haead : AeadRoundTrip)
    (hrt : Tacenta.UnitLifecycleSessionCodec.DhPublicBytesRoundTrip)
    (hct : Tacenta.UnitLifecycleEstablishInitiatorShape.KemCiphertextLenOf)
    (hbound : Tacenta.UnitLifecycleRestoredSession.KemCiphertextLenBound)
    (hoeq : OptionEqU64Shape (@core.option.Option.Insts.CoreCmpPartialEqOption.eq))
    {dh : DhView} (codec : DhCodecOf dh) (view : Model.Lifecycle.CodewordView)
    (oracleA : Model.Lifecycle.Oracle) (hsealA : Tacenta.UnitOracleShape.AeadSealClause Interp.real oracleA)
    (traceB : E → List Model.Lifecycle.Key) (oracleB : Model.Lifecycle.Oracle)
    (oracleOfB : DecryptOracleOf rcB crcB dh traceB oracleB)
    (agreements : DecryptRatchetAgreements oracleB.braidKem)
    (q : InitiatorSecretParts rc crc our bundle) (pending : Model.Lifecycle.PendingInitial)
    (hpend : (establishedModelOf dh q.session).pendingInitial = some pending)
    (plaintext : Slice U8) (hroom : plaintext.val.length + 48 ≤ Usize.max)
    (src : Model.Lifecycle.Bytes) (hsrc : src.length = Model.Braid.headerSize + Model.Braid.macSize)
    (c : tacenta_erasure.Chunk) (hcw : Tacenta.SessionUnitBraidT3.CodewordOf src c)
    (hsend : view.send (establishedModelOf dh q.session).braid (modelChunkOf src c) = modelCodewordOf c)
    (msg : Slice U8)
    (hmsg : sliceOf msg = initialWire (establishedModelOf dh q.session) pending
      (firstFrame view oracleA (establishedModelOf dh q.session) (sliceOf plaintext)
        (Tacenta.UnitLifecycleResponderFirstReceipt.firstKey (arrayOf q.sendChain) (arrayOf q.sparseSend))
        (modelChunkOf src c)))
    (ourB : lifecycle.Identity) (storeB : lifecycle.PrekeyStore)
    (hpublish : lifecycle.PrekeyStore.publish storeB = ok bundle)
    (hidentity : lifecycle.Identity.public ourB = ok storeB.identity_public)
    (hdistinct : PrekeyIdsDistinct storeB)
    (hkem : FirstKemAgrees storeB bundle.kem_prekey_id q.kemCiphertext q.kemSecret)
    (rngB : E) (htraceB : traceB rngB = oracleB.draws) (dB : Model.Lifecycle.Key)
    (restB : List Model.Lifecycle.Key) (hdrawB : traceB rngB = dB :: restB)
    (ptB : alloc.vec.Vec U8) (sB' : lifecycle.Session) (storeB' : lifecycle.PrekeyStore) (rngB' : E)
    (hcallB : lifecycle.establish_responder rcB crcB ourB storeB msg rngB =
      ok (core.result.Result.Ok (sB', ptB), storeB', rngB')) :
    ∃ (p : ResponderPreparedParts ourB storeB msg) (ec : Array U8 32#usize) (dSend : Model.Lifecycle.Key),
      Model.State.kdfRk (arrayOf ec) (arrayOf q.dhOut) .tacenta = (arrayOf q.rootKey, arrayOf q.sendChain) ∧
      oracleB.dhAgree dB (arrayOf q.ratchetBytes) = some dSend ∧
      p.identityAd = q.identityAd ∧
      SessionRefines dh oracleB.braidKem sB'
        (firstReceiptSession (responderModelOf dh p) (sliceOf p.braidSecret) (modelChunkOf src c)
          (arrayOf ec) (arrayOf q.sparseRoot) (arrayOf q.sparseSend) (arrayOf q.sparseReceive)
          (arrayOf q.ratchetBytes) (arrayOf q.dhOut) dSend (oracleB.dhPublic dB) dB) ∧
      lifecycle.Session.invariant sB' = ok true ∧
      Tacenta.UnitLifecycleDecryptRunBounds.CounterHeadroom sB' := by
  rcases responder_first_frame_prepares rcB crcB contracts hpub hsym hrt hct hbound codec q pending hpend _ msg
      hmsg ourB storeB hpublish hidentity hdistinct hkem rngB with ⟨-, e, -, hrefuse⟩ |
    ⟨p, -, -, h3, -, h5, -, -, h8, -⟩
  · rw [hrefuse] at hcallB
    cases hcallB
  obtain ⟨-, -, hsp, hop⟩ := parts_of_first_frame contracts.decrypt.braid.zeroizingArray hpub codec hct
    hbound q pending hpend _ msg hmsg ourB storeB hpublish hidentity p
  obtain ⟨ec, dSend, ptB0, sB0, rngB0, hkdfr, hagree, hinner, -, -, hrel⟩ :=
    responder_first_frame_inner_succeeds rcB crcB contracts hpub hsym hcon haead hoeq codec view oracleA hsealA
      traceB oracleB oracleOfB agreements q plaintext hroom src hsrc c hcw hsend p h3 h5 hsp hop h8 rngB
      htraceB dB restB hdrawB
  obtain ⟨storeB0, -, hout⟩ := establish_responder_commit_of_inner rcB crcB p rngB ptB0 sB0 rngB0 hinner _ hcallB
  simp only [Prod.mk.injEq, core.result.Result.Ok.injEq] at hout
  obtain ⟨⟨rfl, rfl⟩, -, rfl⟩ := hout
  have ha4 := dhPublicValid_canonical hpub q.hRatchetPublic q.hRatchetBytes
  have hdo : q.dhOutBytes = q.dhOut :=
    zeroized_eq contracts.decrypt.braid.zeroizingArray q.hDhOutZ q.hDhOutBytes
  have hkdf := first_kdf_model agreements.hkdf agreements.zeroizing64 hkdfr
  rw [hdo] at hkdf
  exact ⟨p, ec, dSend, hkdf, hagree, first_identityAd_eq q p h5 hop, hrel,
    Tacenta.UnitLifecycleResponderSuccessor.first_receipt_successor_facts hpub hoeq contracts.divCeilValue
      contracts.decrypt.braid.headerLen rcB crcB codec oracleOfB p rngB dB restB hdrawB _ _ _ hinner
      _ _ _ _ _ _ _ _ q.ratchetBytes ha4 hrel⟩

open Tacenta.UnitLifecycleResponderFirstReceipt (headerSource established_triple_first first_send_key)
open Tacenta.UnitLifecycleEstablishInitiatorShape (InitiatorOutputParts)
/-- **The responder's session after the initiator's first send, with the run's keys**: under the hypotheses of
`initiator_first_send_responder_successor_hypotheses`, at every successful return `(Ok (sB', ptB), storeB', rngB')`
of `establish_responder` on the bytes the initiator's first `encrypt` emitted, the conclusion of that theorem holds
together with three equations of the same run: the model's root-key step from the responder's `ec` and the
initiator's `dh_out` gives the initiator's root and sending chain, the responder oracle's agreement of its draw with
the initiator's ratchet key is the `dSend` the relation names, and the two sessions' associated data are equal.
Compiler-trusted through the nine `native_decide` constants of the encrypt and decrypt refinements. -/
theorem initiator_first_send_responder_successor_keys [Tacenta.SessionUnitT1.DerivedKeysModel] {R E F : Type}
    (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R)
    (trace : R → List Model.Lifecycle.Key) (dh : DhView) (kem : KemView)
    (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle)
    (braid : BraidSendRefinementContracts rc oracle.braidKem)
    (triple : TripleSendRefinementContracts)
    (aead : Tacenta.UnitLifecycleT1.AeadSealBounded) (dhCodec : Tacenta.UnitLifecycleT1.DhCodecTotal)
    (oracleOf : OracleOf rc crc dh kem trace oracle) (codec : DhCodecOf dh)
    (codewordView : CodewordViewSendOf view)
    (hz80 : Tacenta.SessionUnitT3.ZeroizingRoundTrips80)
    (hz32 : ZeroizingRoundTrips (Array Std.U8 32#usize))
    (hzKeys : ZeroizingRoundTrips
      (Array Std.U8 32#usize × Array Std.U8 32#usize × Array Std.U8 16#usize))
    (hgen : Tacenta.UnitLifecycleEstablishedEncrypt.KeyGenSeededFor oracle.braidKem rc crc trace)
    (hsizes : Tacenta.UnitLifecycleEstablishedEncrypt.KeyGenSizesOf oracle.braidKem)
    (hct : Tacenta.UnitLifecycleEstablishInitiatorShape.KemCiphertextLenOf)
    (hbound : Tacenta.UnitLifecycleRestoredSession.KemCiphertextLenBound)
    (rcE : rand_core_1.RngCore E) (crcE : rand_core_1.CryptoRng E) (ourA : lifecycle.Identity)
    (bundleA : lifecycle.PublishedBundle) (expected : tacenta_boundary.dh.PublicKeyBytes) (rng0 rng1 : E)
    (s : lifecycle.Session)
    (h : lifecycle.establish_initiator_for rcE crcE ourA bundleA expected rng0 =
      ok (core.result.Result.Ok s, rng1))
    (q : InitiatorSecretParts rcE crcE ourA bundleA) (hq : s = q.session)
    (plaintext : Slice Std.U8) (hroom : plaintext.val.length + 65770 ≤ Usize.max)
    (rng : R) (htrace : trace rng = oracle.draws) (d1 d2 : Model.Lifecycle.Key)
    (rest : List Model.Lifecycle.Key) (hdraws : trace rng = d1 :: d2 :: rest)
    (bytes : alloc.vec.Vec Std.U8) (s' : lifecycle.Session) (rng' : R)
    (hcall : lifecycle.Session.encrypt rc crc s plaintext rng = ok (core.result.Result.Ok bytes, s', rng'))
    (rcB : rand_core_1.RngCore F) (crcB : rand_core_1.CryptoRng F)
    (contracts : Tacenta.UnitLifecycleT1.EstablishResponderContracts rcB)
    (hpub : DhPublicValid) (hsym : DhAgreeSymmetric) (hcon : DhAgreeContributory) (haead : AeadRoundTrip)
    (hrt : Tacenta.UnitLifecycleSessionCodec.DhPublicBytesRoundTrip)
    (hoeq : OptionEqU64Shape (@core.option.Option.Insts.CoreCmpPartialEqOption.eq))
    (traceB : F → List Model.Lifecycle.Key) (oracleB : Model.Lifecycle.Oracle)
    (oracleOfB : DecryptOracleOf rcB crcB dh traceB oracleB)
    (agreements : DecryptRatchetAgreements oracleB.braidKem)
    (ourB : lifecycle.Identity) (storeB : lifecycle.PrekeyStore)
    (hpublish : lifecycle.PrekeyStore.publish storeB = ok bundleA)
    (hidentity : lifecycle.Identity.public ourB = ok storeB.identity_public)
    (hdistinct : PrekeyIdsDistinct storeB)
    (hkem : FirstKemAgrees storeB bundleA.kem_prekey_id q.kemCiphertext q.kemSecret)
    (rngB : F) (htraceB : traceB rngB = oracleB.draws) (dB : Model.Lifecycle.Key)
    (restB : List Model.Lifecycle.Key) (hdrawB : traceB rngB = dB :: restB)
    (ptB : alloc.vec.Vec U8) (sB' : lifecycle.Session) (storeB' : lifecycle.PrekeyStore) (rngB' : F)
    (hcallB : lifecycle.establish_responder rcB crcB ourB storeB (alloc.vec.Vec.deref bytes) rngB =
      ok (core.result.Result.Ok (sB', ptB), storeB', rngB')) :
    ∃ (p : ResponderPreparedParts ourB storeB (alloc.vec.Vec.deref bytes)) (ec : Array U8 32#usize)
      (dSend : Model.Lifecycle.Key) (dk ekSeed ekVector : Model.Braid.Bytes),
      oracle.braidKem.keyGen (Model.Lifecycle.braidRandomness (d1 ++ d2)) = some (dk, ekSeed, ekVector) ∧
      Model.State.kdfRk (arrayOf ec) (arrayOf q.dhOut) .tacenta = (arrayOf q.rootKey, arrayOf q.sendChain) ∧
      oracleB.dhAgree dB (arrayOf q.ratchetBytes) = some dSend ∧
      p.identityAd = q.identityAd ∧
      SessionRefines dh oracleB.braidKem sB'
        (firstReceiptSession (responderModelOf dh p) (sliceOf p.braidSecret)
          ⟨headerSource oracle.braidKem (Tacenta.SessionUnitBraidT3.AuthOf q.auth) ekSeed ekVector, 0⟩
          (arrayOf ec) (arrayOf q.sparseRoot) (arrayOf q.sparseSend) (arrayOf q.sparseReceive)
          (arrayOf q.ratchetBytes) (arrayOf q.dhOut) dSend (oracleB.dhPublic dB) dB) ∧
      lifecycle.Session.invariant sB' = ok true ∧
      Tacenta.UnitLifecycleDecryptRunBounds.CounterHeadroom sB' := by
  obtain ⟨output, hcall', hdr, hcases⟩ := Tacenta.UnitLifecycleEstablishedEncrypt.established_encrypt_outcomes rc
    crc trace dh kem view oracle braid triple aead dhCodec oracleOf codec codewordView hz80 hz32 hzKeys hgen
    hct hbound rcE crcE ourA bundleA expected rng0 rng1 s h plaintext hroom rng htrace d1 d2 rest hdraws
  rw [hcall] at hcall'
  cases hcall'
  rcases hcases with ⟨-, hres, -⟩ | ⟨dk, ekSeed, ekVector, hkg, bytes', hres, -, -, tripleNext, messageKey,
    chunk, encoder, pending, a, ⟨header, hsendM⟩, hbraidA, hnc, hpend, hwire, -⟩
  · cases hres
  simp only [core.result.Result.Ok.injEq] at hres
  subst hres
  subst hq
  have hmk : messageKey = firstKey (arrayOf q.sendChain) (arrayOf q.sparseSend) := by
    rw [established_triple_first dh q.toInitiatorOutputParts, first_send_key] at hsendM
    simp only [Except.ok.injEq, Prod.mk.injEq] at hsendM
    exact hsendM.2.2.symm
  have ha : a = Tacenta.SessionUnitBraidT3.AuthOf q.auth := by
    simp only [establishedModelOf, InitiatorOutputParts.session,
      Tacenta.UnitLifecycleEstablishInitiatorShape.unsampledModelOf, Model.Braid.BraidState.keysUnsampled.injEq]
      at hbraidA
    exact hbraidA.2.symm
  subst ha
  have hchunk : chunk = ⟨headerSource oracle.braidKem (Tacenta.SessionUnitBraidT3.AuthOf q.auth) ekSeed
      ekVector, 0⟩ := by
    simp only [Model.Braid.encode, Model.Braid.Encoder.nextChunk, Prod.mk.injEq] at hnc
    rw [← hnc.1]
    rfl
  obtain ⟨hs32, -, hhl⟩ := hsizes _ _ _ _ hkg
  have hsrc : (headerSource oracle.braidKem (Tacenta.SessionUnitBraidT3.AuthOf q.auth) ekSeed ekVector).length =
      Model.Braid.headerSize + Model.Braid.macSize := by
    simp [headerSource, Model.Braid.Auth.macHdr, Model.Kdf.hmac_length, Model.Kdf.hashLen, hs32, hhl,
      Model.Braid.headerSize, Model.Braid.macSize]
  obtain ⟨-, -, c, -, -, hc0, hcw, -⟩ := Tacenta.UnitHeldKemWitness.held_encoder contracts.divCeilValue
    agreements.erasure _ (by rw [hsrc]; rfl)
  have hmc : modelChunkOf (headerSource oracle.braidKem (Tacenta.SessionUnitBraidT3.AuthOf q.auth) ekSeed
      ekVector) c = ⟨headerSource oracle.braidKem (Tacenta.SessionUnitBraidT3.AuthOf q.auth) ekSeed ekVector, 0⟩ := by
    simp [modelChunkOf, hc0]
  have hsend := codewordView.send (establishedModelOf dh q.session).braid _ c hcw
  rw [hmk, hchunk, ← hmc] at hwire
  obtain ⟨p, ec, dSend, hkdf, hagree, hidad, hrel, hinv, hhead'⟩ := responder_first_frame_successor_keys rcB
    crcB contracts hpub hsym hcon haead hrt hct hbound hoeq codec view oracle oracleOf.aeadSeal traceB oracleB
    oracleOfB agreements q pending hpend plaintext (by omega) _ hsrc c hcw hsend (alloc.vec.Vec.deref bytes) hwire
    ourB storeB hpublish hidentity hdistinct hkem rngB htraceB dB restB hdrawB ptB sB' storeB' rngB' hcallB
  rw [hmc] at hrel
  exact ⟨p, ec, dSend, dk, ekSeed, ekVector, hkg, hkdf, hagree, hidad, hrel, hinv, hhead'⟩

open Tacenta.UnitLifecycleResponderFirstReceipt (headerSource)
open Tacenta.UnitLifecycleResponderFirstFrame (InitiatorSecretParts DhAgreeSymmetric PrekeyIdsDistinct
  FirstKemAgrees)
open Tacenta.UnitLifecycleDecryptRatchetT3 (DecryptOracleOf DecryptRatchetAgreements)
open Tacenta.UnitLifecycleResponderFirstReceipt (DhAgreeContributory AeadRoundTrip)
open Tacenta.UnitLifecycleEstablishInitiatorShape (DhPublicValid)
open Tacenta.UnitLifecycleEstablishResponder (ResponderPreparedParts responderModelOf)
/-- **The responder's reply, on the run of the initiator's first send.**  Under the hypotheses of
`initiator_first_send_responder_successor_hypotheses`, with the responder's oracle record strengthened to the full
`OracleOf` at its source and the Braid send record `BraidSendRefinementContracts` at that source, at every successful
return `(Ok (sB', ptB), storeB', rngB')` of `establish_responder` on the bytes the initiator's first `encrypt`
emitted, for every plaintext `ptR` of at most `Usize.max - 150` bytes and every source state `rngR`:
`Session::encrypt` at `sB'` returns `Ok` with bytes `bytesR` and session `sB''` and leaves the source state `rngR` as
given (no draw); `sB''` is `sB'` with only the Triple Ratchet replaced, so the agreement is unchanged and no initial
wrapper is pending; the bytes are the bare reply frame (`replyFrame`: the fresh ratchet key `oracleB.dhPublic dB`,
classical numbers 0 and 0, sparse epoch 0 and number 1, agreement epoch 1 and type `none`, no chunk) sealed under
`replyKey` (the sending chain of the receipt's second Diffie-Hellman step and the sparse chain `k2` the initiator
receives on) with the initiator's associated data; and `sB''` refines the model session after the receipt with the
Triple `replierAfterSend`.  The run's keys are kept with it: the root-key equation from `ec` and the initiator's
`dh_out`, the responder oracle's agreement `dSend`, and equal associated data.  Compiler-trusted through the nine
`native_decide` constants of the encrypt and decrypt refinements. -/
theorem initiator_first_send_responder_replies [Tacenta.SessionUnitT1.DerivedKeysModel] {R E F : Type}
    (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R)
    (trace : R → List Model.Lifecycle.Key) (dh : DhView) (kem : KemView)
    (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle)
    (braid : BraidSendRefinementContracts rc oracle.braidKem)
    (triple : TripleSendRefinementContracts)
    (aead : Tacenta.UnitLifecycleT1.AeadSealBounded) (dhCodec : Tacenta.UnitLifecycleT1.DhCodecTotal)
    (oracleOf : OracleOf rc crc dh kem trace oracle) (codec : DhCodecOf dh)
    (codewordView : CodewordViewSendOf view)
    (hz80 : Tacenta.SessionUnitT3.ZeroizingRoundTrips80)
    (hz32 : ZeroizingRoundTrips (Array Std.U8 32#usize))
    (hzKeys : ZeroizingRoundTrips
      (Array Std.U8 32#usize × Array Std.U8 32#usize × Array Std.U8 16#usize))
    (hgen : Tacenta.UnitLifecycleEstablishedEncrypt.KeyGenSeededFor oracle.braidKem rc crc trace)
    (hsizes : Tacenta.UnitLifecycleEstablishedEncrypt.KeyGenSizesOf oracle.braidKem)
    (hct : Tacenta.UnitLifecycleEstablishInitiatorShape.KemCiphertextLenOf)
    (hbound : Tacenta.UnitLifecycleRestoredSession.KemCiphertextLenBound)
    (rcE : rand_core_1.RngCore E) (crcE : rand_core_1.CryptoRng E) (ourA : lifecycle.Identity)
    (bundleA : lifecycle.PublishedBundle) (expected : tacenta_boundary.dh.PublicKeyBytes) (rng0 rng1 : E)
    (s : lifecycle.Session)
    (h : lifecycle.establish_initiator_for rcE crcE ourA bundleA expected rng0 =
      ok (core.result.Result.Ok s, rng1))
    (q : InitiatorSecretParts rcE crcE ourA bundleA) (hq : s = q.session)
    (plaintext : Slice Std.U8) (hroom : plaintext.val.length + 65770 ≤ Usize.max)
    (rng : R) (htrace : trace rng = oracle.draws) (d1 d2 : Model.Lifecycle.Key)
    (rest : List Model.Lifecycle.Key) (hdraws : trace rng = d1 :: d2 :: rest)
    (bytes : alloc.vec.Vec Std.U8) (s' : lifecycle.Session) (rng' : R)
    (hcall : lifecycle.Session.encrypt rc crc s plaintext rng = ok (core.result.Result.Ok bytes, s', rng'))
    (rcB : rand_core_1.RngCore F) (crcB : rand_core_1.CryptoRng F)
    (contracts : Tacenta.UnitLifecycleT1.EstablishResponderContracts rcB)
    (hpub : DhPublicValid) (hsym : DhAgreeSymmetric) (hcon : DhAgreeContributory) (haead : AeadRoundTrip)
    (hrt : Tacenta.UnitLifecycleSessionCodec.DhPublicBytesRoundTrip)
    (hoeq : Tacenta.UnitHeadroomInvariant.OptionEqU64Shape
      (@core.option.Option.Insts.CoreCmpPartialEqOption.eq))
    (traceB : F → List Model.Lifecycle.Key) (oracleB : Model.Lifecycle.Oracle)
    (oracleOfB : OracleOf rcB crcB dh kem traceB oracleB)
    (braidB : BraidSendRefinementContracts rcB oracleB.braidKem)
    (agreements : DecryptRatchetAgreements oracleB.braidKem)
    (ourB : lifecycle.Identity) (storeB : lifecycle.PrekeyStore)
    (hpublish : lifecycle.PrekeyStore.publish storeB = ok bundleA)
    (hidentity : lifecycle.Identity.public ourB = ok storeB.identity_public)
    (hdistinct : PrekeyIdsDistinct storeB)
    (hkem : FirstKemAgrees storeB bundleA.kem_prekey_id q.kemCiphertext q.kemSecret)
    (rngB : F) (htraceB : traceB rngB = oracleB.draws) (dB : Model.Lifecycle.Key)
    (restB : List Model.Lifecycle.Key) (hdrawB : traceB rngB = dB :: restB)
    (ptB : alloc.vec.Vec U8) (sB' : lifecycle.Session) (storeB' : lifecycle.PrekeyStore) (rngB' : F)
    (hcallB : lifecycle.establish_responder rcB crcB ourB storeB (alloc.vec.Vec.deref bytes) rngB =
      ok (core.result.Result.Ok (sB', ptB), storeB', rngB'))
    (ptR : Slice Std.U8) (hroomR : 102 + (ptR.val.length + 48) ≤ Usize.max) (rngR : F) :
    ∃ (p : ResponderPreparedParts ourB storeB (alloc.vec.Vec.deref bytes)) (ec : Array U8 32#usize)
      (dSend : Model.Lifecycle.Key) (dk ekSeed ekVector : Model.Braid.Bytes) (bytesR : alloc.vec.Vec Std.U8)
      (sB'' : lifecycle.Session),
      oracle.braidKem.keyGen (Model.Lifecycle.braidRandomness (d1 ++ d2)) = some (dk, ekSeed, ekVector) ∧
      Model.State.kdfRk (arrayOf ec) (arrayOf q.dhOut) .tacenta = (arrayOf q.rootKey, arrayOf q.sendChain) ∧
      oracleB.dhAgree dB (arrayOf q.ratchetBytes) = some dSend ∧
      p.identityAd = q.identityAd ∧
      SessionRefines dh oracleB.braidKem sB'
        (firstReceiptSession (responderModelOf dh p) (sliceOf p.braidSecret)
          ⟨headerSource oracle.braidKem (Tacenta.SessionUnitBraidT3.AuthOf q.auth) ekSeed ekVector, 0⟩
          (arrayOf ec) (arrayOf q.sparseRoot) (arrayOf q.sparseSend) (arrayOf q.sparseReceive)
          (arrayOf q.ratchetBytes) (arrayOf q.dhOut) dSend (oracleB.dhPublic dB) dB) ∧
      lifecycle.Session.encrypt rcB crcB sB' ptR rngR = ok (core.result.Result.Ok bytesR, sB'', rngR) ∧
      sB''.braid = sB'.braid ∧ sB''.pending_initial = none ∧ sB'' = { sB' with triple := sB''.triple } ∧
      vecOf bytesR = replyFrame oracleB (vecOf q.identityAd) (oracleB.dhPublic dB)
        (replyKey (arrayOf ec) (arrayOf q.sparseReceive) (arrayOf q.dhOut) dSend) (sliceOf ptR) ∧
      SessionRefines dh oracleB.braidKem sB''
        { firstReceiptSession (responderModelOf dh p) (sliceOf p.braidSecret)
            ⟨headerSource oracle.braidKem (Tacenta.SessionUnitBraidT3.AuthOf q.auth) ekSeed ekVector, 0⟩
            (arrayOf ec) (arrayOf q.sparseRoot) (arrayOf q.sparseSend) (arrayOf q.sparseReceive)
            (arrayOf q.ratchetBytes) (arrayOf q.dhOut) dSend (oracleB.dhPublic dB) dB with
          triple := replierAfterSend (arrayOf ec) (arrayOf q.sparseRoot) (arrayOf q.sparseSend)
            (arrayOf q.sparseReceive) (arrayOf q.ratchetBytes) (arrayOf q.dhOut) dSend (oracleB.dhPublic dB) } := by
  -- the session establish_responder returned, with the run's keys
  obtain ⟨p, ec, dSend, dk, ekSeed, ekVector, hkg, hkdf, hagree, hidad, hrel, hinv, -⟩ :=
    initiator_first_send_responder_successor_keys rc crc trace dh kem view oracle braid triple aead dhCodec
      oracleOf codec codewordView hz80 hz32 hzKeys hgen hsizes hct hbound rcE crcE ourA bundleA expected rng0 rng1 s
      h q hq plaintext hroom rng htrace d1 d2 rest hdraws bytes s' rng' hcall rcB crcB contracts hpub hsym hcon
      haead hrt hoeq traceB oracleB (DecryptOracleOf.of_oracleOf oracleOfB) agreements ourB storeB hpublish
      hidentity hdistinct hkem rngB htraceB dB restB hdrawB ptB sB' storeB' rngB' hcallB
  have hpend : (responderModelOf dh p).pendingInitial = none := rfl
  -- the encrypt refinement at that session, at the responder's oracle with the source's draws
  obtain ⟨output, hcallR, hstep⟩ := responder_reply_refines rcB crcB traceB dh kem view
    { oracleB with draws := traceB rngR } braidB triple aead dhCodec (oracleOf_with_draws oracleOfB _) codec
    codewordView hz80 hz32 hzKeys contracts.decrypt.braid.ct1Len (responderModelOf dh p) _ _ _ _ _ _ _ _ _ _ _
    hpend sB' hrel hinv ptR hroomR rngR rfl
  -- the model's step: one outcome, the bare reply frame
  rw [reply_model_step _ _ _ _ _ _ _ _ _ _ _ _ _ _ hpend] at hstep
  obtain ⟨res, sB'', rngR'⟩ := output
  have hres := hstep.result
  have hsess := hstep.session
  simp only at hres hsess hcallR
  cases res with
  | Err err => exact hres.elim
  | Ok bytesR =>
    -- the walk of the call: the agreement's send took no draw and returned the agreement as given
    obtain ⟨m, ep, o, b, hsendB, _sparse, _cand, _hdr, _mk, -, hs''⟩ :=
      Tacenta.UnitLifecycleEstablishedEncrypt.encrypt_ok_parts rcB crcB sB' ptR rngR bytesR sB'' rngR' hcallR
    obtain ⟨e, auth, dec, hst⟩ := noHeader_of_receipt_refines hrel
    obtain ⟨hr, hb, -, -⟩ := braid_send_noHeader rcB crcB sB'.braid e auth dec hst rngR _ rngR' hsendB
    simp only at hb
    subst hr hb
    have hpendR := pendingInitial_none_of_receipt_refines hpend hrel
    refine ⟨p, ec, dSend, dk, ekSeed, ekVector, bytesR, sB'', hkg, hkdf, hagree, hidad, hrel, hcallR, ?_, ?_, ?_,
      ?_, hsess⟩
    · rw [hs'']
    · rw [hs'']; exact hpendR
    · rw [hs'']
    · rw [hres, replyFrame_with_draws]
      simp only [responderModelOf, hidad]

open Tacenta.UnitLifecycleIntegrationScreen (byteRng byteCrc byteTrace)
open Tacenta.UnitLifecycleResponderFirstFrame (FirstFrameSuccessShape)
open Tacenta.UnitLifecycleResponderFirstReceipt (first_send_receive_reachable)
open Tacenta.UnitSatisfiabilityJoint (Interp Interp.real InitiatorAxiom ResponderAxiom) in
open Tacenta.UnitLifecycleEstablishedEncrypt (EncryptExtraLaws emptyPlaintext) in
/-- **The reach of the receipt module, continued with the responder's reply**: under the laws of
`first_send_receive_reachable`, for every initiator identity and every 64-byte source at whose bytes the model's key
generation answers, there is a run from `publish` through the establishment, a first send of the empty plaintext and
a successful `establish_responder`, after which the responder's `encrypt` of the empty plaintext, from the source
`establish_responder` left, returns bytes, leaves that source as it was and keeps the agreement.  It applies
`initiator_first_send_responder_replies` to that run, with the responder's records the run's encrypt records (the two
parties share the oracle and the byte-stream source type there).  Last-resort path only.  Compiler-trusted. -/
theorem first_send_reply_reachable (K : Model.Braid.Kem) (dh : DhView)
    (kem : Tacenta.UnitLifecycleT3.KemView) (L : Tacenta.UnitLifecycleDecryptScreen.DecryptJointLaws K dh)
    (A : Nonempty (InitiatorAxiom Interp.real byteRng))
    (S : Tacenta.UnitLifecycleEstablishInitiatorShape.InitiatorSuccessShape Interp.real byteRng byteCrc)
    (hpub : DhPublicValid) (hct : Tacenta.UnitLifecycleEstablishInitiatorShape.KemCiphertextLenOf)
    (X : EncryptExtraLaws K dh kem) (RA : Nonempty (ResponderAxiom Interp.real byteRng))
    (hsym : DhAgreeSymmetric) (hrt : Tacenta.UnitLifecycleSessionCodec.DhPublicBytesRoundTrip)
    (FS : FirstFrameSuccessShape Interp.real tacenta_boundary.kem.KeyPair.public_key
      @alloc.vec.Vec.is_empty)
    (hsizes : Tacenta.UnitLifecycleEstablishedEncrypt.KeyGenSizesOf K)
    (hcon : DhAgreeContributory) (haead : AeadRoundTrip)
    (ourA : lifecycle.Identity) (seed : List Std.U8) (hseed : seed.length = 64)
    (hkg : K.keyGen (Model.Lifecycle.braidRandomness (seed.map Tacenta.SessionUnitBraidT3.u8)) ≠ none) :
    ∃ (oracle : Model.Lifecycle.Oracle) (bundle : lifecycle.PublishedBundle)
      (q : InitiatorSecretParts byteRng byteCrc ourA bundle) (bytes : alloc.vec.Vec Std.U8)
      (s' : lifecycle.Session) (rng' : List Std.U8) (ourB : lifecycle.Identity)
      (storeB : lifecycle.PrekeyStore) (sB' : lifecycle.Session) (ptB : alloc.vec.Vec Std.U8)
      (storeB' : lifecycle.PrekeyStore) (rngB' : List Std.U8) (bytesR : alloc.vec.Vec Std.U8)
      (sB'' : lifecycle.Session),
      oracle.braidKem = K ∧
      lifecycle.Session.encrypt byteRng byteCrc q.session emptyPlaintext seed =
        ok (core.result.Result.Ok bytes, s', rng') ∧
      lifecycle.PrekeyStore.publish storeB = ok bundle ∧
      lifecycle.establish_responder byteRng byteCrc ourB storeB (alloc.vec.Vec.deref bytes) seed =
        ok (core.result.Result.Ok (sB', ptB), storeB', rngB') ∧
      lifecycle.Session.encrypt byteRng byteCrc sB' emptyPlaintext rngB' =
        ok (core.result.Result.Ok bytesR, sB'', rngB') ∧
      sB''.braid = sB'.braid := by
  obtain ⟨oracle, bundle, rng0, rng1, q, bytes, s', rng', ourB, storeB, sB', ptB, storeB', rngB', hK, H, hcall,
    hpublish, hidentity, hdistinct, hkem, -, -, htraceB, -, -, hcallB, -⟩ :=
    first_send_receive_reachable K dh kem L A S hpub hct X RA hsym hrt FS hsizes hcon haead ourA seed hseed hkg
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
  have hu : 4294967295 ≤ Usize.max :=
    Tacenta.SessionUnitSessionT1.small_le_usize_max (le_refl _)
  obtain ⟨_, _, _, _, _, _, bytesR, sB'', -, -, -, -, -, hcallR, hbraid, -⟩ :=
    initiator_first_send_responder_replies byteRng byteCrc byteTrace dh kem Tacenta.UnitLifecycleRepair.witnessView
    oracle H.braid H.triple H.aead H.dhCodec H.oracleOf H.codec H.codewordView H.zeroizing80 H.zeroizing32
    H.zeroizingKeys H.keyGen hsizes H.kemCiphertextLen H.kemCiphertextBound byteRng byteCrc ourA _ _ _ rng1 q.session
    H.established q rfl emptyPlaintext H.room seed H.trace_eq _ _ _
    (Tacenta.UnitLifecycleEstablishedEncrypt.byteTrace_two seed (by omega)) bytes s' rng' hcall byteRng byteCrc
    contracts hpub hsym hcon haead hrt L.optionEq byteTrace oracle H.oracleOf H.braid ag ourB storeB hpublish
    hidentity hdistinct hkem seed htraceB d1 (d2 :: rest2) hdrB ptB sB' storeB' rngB' hcallB emptyPlaintext
    (by simp [emptyPlaintext]; omega) rngB'
  exact ⟨oracle, bundle, q, bytes, s', rng', ourB, storeB, sB', ptB, storeB', rngB', bytesR, sB'', rfl, hcall,
    hpublish, hcallB, hcallR, hbraid⟩

end Comp

end Tacenta.UnitLifecycleResponderReply

/-! ## Pins

The constants each result depends on, and the statement of each result and definition, held by the
build.  `attest.py` requires every one of them (`REQUIRED_PINS`, `REQUIRED_STATEMENT_PINS`,
`REQUIRED_PRINT_FORM`). -/

/--
info: 'Tacenta.UnitLifecycleResponderReply.array_clone_u8' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleResponderReply.array_clone_u8

/--
info: 'Tacenta.UnitLifecycleResponderReply.auth_clone_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleResponderReply.auth_clone_eq

/--
info: 'Tacenta.UnitLifecycleResponderReply.braid_send_noHeader' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_kdf.hkdf_sha256,
 tacenta_kdf.hmac_sha256,
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
#print axioms Tacenta.UnitLifecycleResponderReply.braid_send_noHeader

/--
info: 'Tacenta.UnitLifecycleResponderReply.sendAgreement_noHeader_output' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleResponderReply.sendAgreement_noHeader_output

/--
info: 'Tacenta.UnitLifecycleResponderReply.braidSendTraceCounted_of_noHeader' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_kdf.hkdf_sha256,
 tacenta_kdf.hmac_sha256,
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
#print axioms Tacenta.UnitLifecycleResponderReply.braidSendTraceCounted_of_noHeader

/--
info: 'Tacenta.UnitLifecycleResponderReply.reply_send_key' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleResponderReply.reply_send_key

/--
info: 'Tacenta.UnitLifecycleResponderReply.replyFrame_with_draws' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleResponderReply.replyFrame_with_draws

/--
info: 'Tacenta.UnitLifecycleResponderReply.reply_model_step' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleResponderReply.reply_model_step

/--
info: 'Tacenta.UnitLifecycleResponderReply.sparseOutput_none_of_noHeader' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_kdf.hkdf_sha256,
 tacenta_kdf.hmac_sha256,
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
#print axioms Tacenta.UnitLifecycleResponderReply.sparseOutput_none_of_noHeader

/--
info: 'Tacenta.UnitLifecycleResponderReply.encryptProviders_reply' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_kdf.hkdf_sha256,
 tacenta_kdf.hmac_sha256,
 tacenta_kem.EncapsState,
 tacenta_kem.IncrementalKeyPair,
 tacenta_kem.encapsulate1,
 tacenta_kem.encapsulate2,
 zeroize.Zeroizing,
 rand_core_1.error.Error,
 tacenta_boundary.aead.encrypt,
 tacenta_boundary.dh.PrivateKey,
 tacenta_boundary.dh.PublicKeyBytes,
 tacenta_boundary.kem.KeyPair,
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
 tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 zeroize.Zeroize.Blanket.zeroize,
 tacenta_kem.EncapsState.Insts.CoreCloneClone.clone,
 tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone,
 zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 core.option.Option.Insts.CoreCloneClone.clone,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleResponderReply.encryptProviders_reply

/--
info: 'Tacenta.UnitLifecycleResponderReply.encryptHeadroom_reply' depends on axioms: [propext,
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
#print axioms Tacenta.UnitLifecycleResponderReply.encryptHeadroom_reply

/--
info: 'Tacenta.UnitLifecycleResponderReply.oracleOf_with_draws' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 rand_core_1.error.Error,
 tacenta_boundary.aead.decrypt,
 tacenta_boundary.aead.encrypt,
 tacenta_boundary.dh.PrivateKey,
 tacenta_boundary.dh.PublicKeyBytes,
 tacenta_boundary.dh.is_prime_order_public,
 tacenta_boundary.kem.KeyPair,
 tacenta_boundary.kem.decapsulate,
 tacenta_boundary.kem.encapsulate,
 tacenta_boundary.xeddsa.sign,
 tacenta_boundary.xeddsa.verify,
 tacenta_boundary.dh.PrivateKey.agree,
 tacenta_boundary.dh.PrivateKey.public_key,
 tacenta_boundary.dh.PublicKeyBytes.as_bytes]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleResponderReply.oracleOf_with_draws

/--
info: 'Tacenta.UnitLifecycleResponderReply.noHeader_of_receipt_refines' depends on axioms: [propext,
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
#print axioms Tacenta.UnitLifecycleResponderReply.noHeader_of_receipt_refines

/--
info: 'Tacenta.UnitLifecycleResponderReply.pendingInitial_none_of_receipt_refines' depends on axioms: [propext,
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
#print axioms Tacenta.UnitLifecycleResponderReply.pendingInitial_none_of_receipt_refines

/--
info: 'Tacenta.UnitLifecycleResponderReply.responder_reply_refines' depends on axioms: [propext,
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
#print axioms Tacenta.UnitLifecycleResponderReply.responder_reply_refines

/--
info: 'Tacenta.UnitLifecycleResponderReply.responder_first_frame_successor_keys' depends on axioms: [propext,
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
 tacenta_boundary.kem.ciphertext_len,
 tacenta_boundary.kem.decapsulate,
 tacenta_boundary.kem.encapsulate,
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
#print axioms Tacenta.UnitLifecycleResponderReply.responder_first_frame_successor_keys

/--
info: 'Tacenta.UnitLifecycleResponderReply.initiator_first_send_responder_successor_keys' depends on axioms: [propext,
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
#print axioms Tacenta.UnitLifecycleResponderReply.initiator_first_send_responder_successor_keys

/--
info: 'Tacenta.UnitLifecycleResponderReply.initiator_first_send_responder_replies' depends on axioms: [propext,
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
#print axioms Tacenta.UnitLifecycleResponderReply.initiator_first_send_responder_replies

/--
info: 'Tacenta.UnitLifecycleResponderReply.first_send_reply_reachable' depends on axioms: [propext,
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
#print axioms Tacenta.UnitLifecycleResponderReply.first_send_reply_reachable

/--
info: @Tacenta.UnitLifecycleResponderReply.array_clone_u8 : ∀ {n : Usize} (a : Std.Array U8 n),
  core.array.CloneArray.clone core.clone.CloneU8 a = ok a
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderReply.array_clone_u8

/--
info: Tacenta.UnitLifecycleResponderReply.auth_clone_eq : ∀ (a : tacenta_braid.Auth),
  tacenta_braid.Auth.Insts.CoreCloneClone.clone a = ok a
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderReply.auth_clone_eq

/--
info: @Tacenta.UnitLifecycleResponderReply.braid_send_noHeader : ∀ {R : Type} (rc : rand_core_1.RngCore R)
  (crc : rand_core_1.CryptoRng R) (b : tacenta_braid.Braid) (epoch : U64) (auth : tacenta_braid.Auth)
  (d : tacenta_erasure.Decoder),
  b.state = tacenta_braid.State.NoHeaderReceived epoch auth d →
    ∀ (rng : R) (x : tacenta_braid.Msg × U64 × Option tacenta_braid.Output × tacenta_braid.Braid) (rngN : R),
      tacenta_braid.Braid.send rc crc b rng = ok (x, rngN) →
        rngN = rng ∧
          x.2.2.2 = b ∧ x.1 = { epoch := epoch, ty := tacenta_braid.MsgType.None, data := none } ∧ x.2.2.1 = none
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderReply.braid_send_noHeader

/--
info: Tacenta.UnitLifecycleResponderReply.sendAgreement_noHeader_output : ∀ (oracle oracleNext : Model.Lifecycle.Oracle)
  (e : ℕ) (a : Model.Braid.Auth) (dec : Model.Braid.Decoder) (message : Option Model.Braid.Msg) (epoch : ℕ)
  (output : Option Model.Braid.Output) (next : Model.Braid.BraidState),
  Model.Lifecycle.sendAgreement oracle (Model.Braid.BraidState.noHeaderReceived e a dec) =
      some ((message, epoch, output, next), oracleNext) →
    output = none
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderReply.sendAgreement_noHeader_output

/--
info: @Tacenta.UnitLifecycleResponderReply.braidSendTraceCounted_of_noHeader : ∀ {R : Type} {rc : rand_core_1.RngCore R}
  {crc : rand_core_1.CryptoRng R} {trace : R → List Model.Lifecycle.Key} {K : Model.Braid.Kem}
  {oracle : Model.Lifecycle.Oracle} {real : lifecycle.Session} {model : Model.Lifecycle.Session} {rng : R},
  oracle.braidKem = K →
    ∀ (epoch : U64) (auth : tacenta_braid.Auth) (dec : tacenta_erasure.Decoder),
      real.braid.state = tacenta_braid.State.NoHeaderReceived epoch auth dec →
        ∀ (e : ℕ) (a : Model.Braid.Auth) (decM : Model.Braid.Decoder),
          model.braid = Model.Braid.BraidState.noHeaderReceived e a decM →
            Tacenta.UnitLifecycleT3.BraidSendTraceAgreementCounted rc crc trace K oracle real model rng
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderReply.braidSendTraceCounted_of_noHeader

/--
info: Tacenta.UnitLifecycleResponderReply.reply_send_key : ∀ (ec prk k1 k2 a4 d dSend newPub : Model.State.Key),
  Model.Triple.sendDetailed
      (Tacenta.UnitLifecycleResponderFirstReceipt.receiverAfterFirst ec prk k1 k2 a4 d dSend newPub) 0 none =
    Except.ok
      (Tacenta.UnitLifecycleResponderReply.replierAfterSend ec prk k1 k2 a4 d dSend newPub,
        Tacenta.UnitLifecycleResponderFirstReceipt.firstHeader newPub,
        Tacenta.UnitLifecycleResponderReply.replyKey ec k2 d dSend)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderReply.reply_send_key

/--
info: Tacenta.UnitLifecycleResponderReply.replyFrame_with_draws : ∀ (oracle : Model.Lifecycle.Oracle)
  (draws : List Model.State.Key) (ad : Model.Lifecycle.Bytes) (newPub messageKey : Model.State.Key)
  (plaintext : Model.Lifecycle.Bytes),
  Tacenta.UnitLifecycleResponderReply.replyFrame
      { draws := draws, braidKem := oracle.braidKem, dhPublic := oracle.dhPublic, dhAgree := oracle.dhAgree,
        identityValid := oracle.identityValid, aeadSeal := oracle.aeadSeal, aeadOpen := oracle.aeadOpen,
        kemValid := oracle.kemValid, kemEncaps := oracle.kemEncaps, kemDecaps := oracle.kemDecaps,
        sigVerify := oracle.sigVerify, sigSign := oracle.sigSign }
      ad newPub messageKey plaintext =
    Tacenta.UnitLifecycleResponderReply.replyFrame oracle ad newPub messageKey plaintext
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderReply.replyFrame_with_draws

/--
info: Tacenta.UnitLifecycleResponderReply.reply_model_step : ∀ (view : Model.Lifecycle.CodewordView)
  (oracle : Model.Lifecycle.Oracle) (mB : Model.Lifecycle.Session) (secret : Model.Lifecycle.Bytes)
  (rcv : Model.Braid.Chunk) (ec prk k1 k2 a4 d dSend newPub c : Model.State.Key),
  mB.pendingInitial = none →
    ∀ (pt : Model.Lifecycle.Bytes),
      Model.Lifecycle.encrypt view oracle
          (Tacenta.UnitLifecycleResponderFirstReceipt.firstReceiptSession mB secret rcv ec prk k1 k2 a4 d dSend newPub
            c)
          pt =
        {
          session :=
            have __src :=
              Tacenta.UnitLifecycleResponderFirstReceipt.firstReceiptSession mB secret rcv ec prk k1 k2 a4 d dSend
                newPub c;
            { triple := Tacenta.UnitLifecycleResponderReply.replierAfterSend ec prk k1 k2 a4 d dSend newPub,
              braid := __src.braid, ratchetPrivate := __src.ratchetPrivate, identityAd := __src.identityAd,
              ourIdentityPublic := __src.ourIdentityPublic, peerIdentityPublic := __src.peerIdentityPublic,
              pendingInitial := __src.pendingInitial, establishedEphemeral := __src.establishedEphemeral },
          result :=
            Except.ok
              (Tacenta.UnitLifecycleResponderReply.replyFrame oracle mB.identityAd newPub
                (Tacenta.UnitLifecycleResponderReply.replyKey ec k2 d dSend) pt),
          oracle := oracle }
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderReply.reply_model_step

/--
info: @Tacenta.UnitLifecycleResponderReply.sparseOutput_none_of_noHeader : ∀ {R : Type} {rc : rand_core_1.RngCore R}
  {crc : rand_core_1.CryptoRng R} {trace : R → List Model.Lifecycle.Key} {dh : Tacenta.UnitLifecycleT3.DhView}
  {K : Model.Braid.Kem} {oracle : Model.Lifecycle.Oracle} {real : lifecycle.Session} {model : Model.Lifecycle.Session}
  {rng : R} {realMessage : tacenta_braid.Msg} {realEpoch : U64} {realOutput : Option tacenta_braid.Output}
  {realBraidNext : tacenta_braid.Braid} {rngNext : R} {sparseOutput : Option tacenta_spqr.Output} (e : ℕ)
  (a : Model.Braid.Auth) (decM : Model.Braid.Decoder),
  model.braid = Model.Braid.BraidState.noHeaderReceived e a decM →
    Tacenta.UnitLifecycleT3.RealSparseConversion realOutput sparseOutput →
      Nonempty
          (Tacenta.UnitLifecycleT3.GeneratedBraidSuccessEvidence rc crc trace dh K oracle real model rng realMessage
            realEpoch realOutput realBraidNext rngNext) →
        sparseOutput = none
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderReply.sparseOutput_none_of_noHeader

/--
info: @Tacenta.UnitLifecycleResponderReply.encryptProviders_reply : ∀ [Tacenta.SessionUnitT1.DerivedKeysModel] {R : Type}
  {rc : rand_core_1.RngCore R} {crc : rand_core_1.CryptoRng R} {trace : R → List Model.Lifecycle.Key}
  (dh : Tacenta.UnitLifecycleT3.DhView) (kem : Tacenta.UnitLifecycleT3.KemView) (K : Model.Braid.Kem)
  (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle) (real : lifecycle.Session)
  (mB : Model.Lifecycle.Session) (secret : Model.Lifecycle.Bytes) (rcv : Model.Braid.Chunk)
  (ec prk k1 k2 a4 d dSend newPub c : Model.State.Key) (plaintext : Slice U8) (rng : R),
  Nonempty
    (Tacenta.UnitLifecycleT3.EncryptNonterminalRouteProviders rc crc trace dh kem K view oracle real
      (Tacenta.UnitLifecycleResponderFirstReceipt.firstReceiptSession mB secret rcv ec prk k1 k2 a4 d dSend newPub c)
      plaintext rng)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderReply.encryptProviders_reply

/--
info: Tacenta.UnitLifecycleResponderReply.encryptHeadroom_reply : Tacenta.UnitLifecycleT1.DhCodecTotal →
  Tacenta.SessionUnitBraidT1.Ct1LenTotal →
    ∀ (s : lifecycle.Session),
      s.invariant = ok true →
        s.pending_initial = none →
          ∀ (plaintext : Slice U8),
            102 + ((↑plaintext).length + 48) ≤ Usize.max → Tacenta.UnitLifecycleT1.EncryptHeadroom s plaintext
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderReply.encryptHeadroom_reply

/--
info: @Tacenta.UnitLifecycleResponderReply.oracleOf_with_draws : ∀ {R : Type} {rc : rand_core_1.RngCore R}
  {crc : rand_core_1.CryptoRng R} {dh : Tacenta.UnitLifecycleT3.DhView} {kem : Tacenta.UnitLifecycleT3.KemView}
  {trace : R → List Model.Lifecycle.Key} {oracle : Model.Lifecycle.Oracle},
  Tacenta.UnitLifecycleT3.OracleOf rc crc dh kem trace oracle →
    ∀ (draws : List Model.Lifecycle.Key),
      Tacenta.UnitLifecycleT3.OracleOf rc crc dh kem trace
        { draws := draws, braidKem := oracle.braidKem, dhPublic := oracle.dhPublic, dhAgree := oracle.dhAgree,
          identityValid := oracle.identityValid, aeadSeal := oracle.aeadSeal, aeadOpen := oracle.aeadOpen,
          kemValid := oracle.kemValid, kemEncaps := oracle.kemEncaps, kemDecaps := oracle.kemDecaps,
          sigVerify := oracle.sigVerify, sigSign := oracle.sigSign }
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderReply.oracleOf_with_draws

/--
info: @Tacenta.UnitLifecycleResponderReply.noHeader_of_receipt_refines : ∀ {dh : Tacenta.UnitLifecycleT3.DhView}
  {K : Model.Braid.Kem} {sB : lifecycle.Session} {mB : Model.Lifecycle.Session} {secret : Model.Lifecycle.Bytes}
  {rcv : Model.Braid.Chunk} {ec prk k1 k2 a4 d dSend newPub c : Model.State.Key},
  Tacenta.UnitLifecycleT3.SessionRefines dh K sB
      (Tacenta.UnitLifecycleResponderFirstReceipt.firstReceiptSession mB secret rcv ec prk k1 k2 a4 d dSend newPub c) →
    ∃ e auth dec, sB.braid.state = tacenta_braid.State.NoHeaderReceived e auth dec
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderReply.noHeader_of_receipt_refines

/--
info: @Tacenta.UnitLifecycleResponderReply.pendingInitial_none_of_receipt_refines : ∀ {dh : Tacenta.UnitLifecycleT3.DhView}
  {K : Model.Braid.Kem} {sB : lifecycle.Session} {mB : Model.Lifecycle.Session} {secret : Model.Lifecycle.Bytes}
  {rcv : Model.Braid.Chunk} {ec prk k1 k2 a4 d dSend newPub c : Model.State.Key},
  mB.pendingInitial = none →
    Tacenta.UnitLifecycleT3.SessionRefines dh K sB
        (Tacenta.UnitLifecycleResponderFirstReceipt.firstReceiptSession mB secret rcv ec prk k1 k2 a4 d dSend newPub
          c) →
      sB.pending_initial = none
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderReply.pendingInitial_none_of_receipt_refines

/--
info: @Tacenta.UnitLifecycleResponderReply.responder_reply_refines : ∀ [Tacenta.SessionUnitT1.DerivedKeysModel] {R : Type}
  (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R) (trace : R → List Model.Lifecycle.Key)
  (dh : Tacenta.UnitLifecycleT3.DhView) (kem : Tacenta.UnitLifecycleT3.KemView) (view : Model.Lifecycle.CodewordView)
  (oracle : Model.Lifecycle.Oracle),
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
                      Tacenta.SessionUnitBraidT1.Ct1LenTotal →
                        ∀ (mB : Model.Lifecycle.Session) (secret : Model.Lifecycle.Bytes) (rcv : Model.Braid.Chunk)
                          (ec prk k1 k2 a4 d dSend newPub c : Model.State.Key),
                          mB.pendingInitial = none →
                            ∀ (sB : lifecycle.Session),
                              Tacenta.UnitLifecycleT3.SessionRefines dh oracle.braidKem sB
                                  (Tacenta.UnitLifecycleResponderFirstReceipt.firstReceiptSession mB secret rcv ec prk
                                    k1 k2 a4 d dSend newPub c) →
                                sB.invariant = ok true →
                                  ∀ (plaintext : Slice U8),
                                    102 + ((↑plaintext).length + 48) ≤ Usize.max →
                                      ∀ (rng : R),
                                        trace rng = oracle.draws →
                                          Tacenta.UnitLifecycleT3.PublicEncryptWitness rc crc trace dh oracle.braidKem
                                            view oracle sB
                                            (Tacenta.UnitLifecycleResponderFirstReceipt.firstReceiptSession mB secret
                                              rcv ec prk k1 k2 a4 d dSend newPub c)
                                            plaintext rng
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderReply.responder_reply_refines

/--
info: @Tacenta.UnitLifecycleResponderReply.responder_first_frame_successor_keys : ∀ {R : Type} {rc : rand_core_1.RngCore R}
  {crc : rand_core_1.CryptoRng R} {our : lifecycle.Identity} {bundle : lifecycle.PublishedBundle}
  [Tacenta.SessionUnitT1.DerivedKeysModel] {E : Type} (rcB : rand_core_1.RngCore E) (crcB : rand_core_1.CryptoRng E)
  (contracts : Tacenta.UnitLifecycleT1.EstablishResponderContracts rcB),
  Tacenta.UnitLifecycleEstablishInitiatorShape.DhPublicValid →
    Tacenta.UnitLifecycleResponderFirstFrame.DhAgreeSymmetric →
      Tacenta.UnitLifecycleResponderFirstReceipt.DhAgreeContributory →
        Tacenta.UnitLifecycleResponderFirstReceipt.AeadRoundTrip →
          Tacenta.UnitLifecycleSessionCodec.DhPublicBytesRoundTrip →
            Tacenta.UnitLifecycleEstablishInitiatorShape.KemCiphertextLenOf →
              Tacenta.UnitLifecycleRestoredSession.KemCiphertextLenBound →
                Tacenta.UnitHeadroomInvariant.OptionEqU64Shape @core.option.Option.Insts.CoreCmpPartialEqOption.eq →
                  ∀ {dh : Tacenta.UnitLifecycleT3.DhView},
                    Tacenta.UnitLifecycleT3.DhCodecOf dh →
                      ∀ (view : Model.Lifecycle.CodewordView) (oracleA : Model.Lifecycle.Oracle),
                        Tacenta.UnitOracleShape.AeadSealClause Tacenta.UnitSatisfiabilityJoint.Interp.real oracleA →
                          ∀ (traceB : E → List Model.Lifecycle.Key) (oracleB : Model.Lifecycle.Oracle),
                            Tacenta.UnitLifecycleDecryptRatchetT3.DecryptOracleOf rcB crcB dh traceB oracleB →
                              Tacenta.UnitLifecycleDecryptRatchetT3.DecryptRatchetAgreements oracleB.braidKem →
                                ∀ (q : Tacenta.UnitLifecycleResponderFirstFrame.InitiatorSecretParts rc crc our bundle)
                                  (pending : Model.Lifecycle.PendingInitial),
                                  (Tacenta.UnitLifecycleEstablishInitiatorShape.establishedModelOf dh
                                          q.session).pendingInitial =
                                      some pending →
                                    ∀ (plaintext : Slice U8),
                                      (↑plaintext).length + 48 ≤ Usize.max →
                                        ∀ (src : Model.Lifecycle.Bytes),
                                          List.length src = Model.Braid.headerSize + Model.Braid.macSize →
                                            ∀ (c : tacenta_erasure.Chunk),
                                              Tacenta.SessionUnitBraidT3.CodewordOf src c →
                                                view.send
                                                      (Tacenta.UnitLifecycleEstablishInitiatorShape.establishedModelOf
                                                          dh q.session).braid
                                                      (Tacenta.UnitLifecycleT3.modelChunkOf src c) =
                                                    Tacenta.UnitLifecycleT3.modelCodewordOf c →
                                                  ∀ (msg : Slice U8),
                                                    Tacenta.UnitLifecycleT3.sliceOf msg =
                                                        Tacenta.UnitLifecycleEstablishedEncrypt.initialWire
                                                          (Tacenta.UnitLifecycleEstablishInitiatorShape.establishedModelOf
                                                            dh q.session)
                                                          pending
                                                          (Tacenta.UnitLifecycleEstablishedEncrypt.firstFrame view
                                                            oracleA
                                                            (Tacenta.UnitLifecycleEstablishInitiatorShape.establishedModelOf
                                                              dh q.session)
                                                            (Tacenta.UnitLifecycleT3.sliceOf plaintext)
                                                            (Tacenta.UnitLifecycleResponderFirstReceipt.firstKey
                                                              (Tacenta.UnitLifecycleT3.arrayOf q.sendChain)
                                                              (Tacenta.UnitLifecycleT3.arrayOf q.sparseSend))
                                                            (Tacenta.UnitLifecycleT3.modelChunkOf src c)) →
                                                      ∀ (ourB : lifecycle.Identity) (storeB : lifecycle.PrekeyStore),
                                                        storeB.publish = ok bundle →
                                                          ourB.public = ok storeB.identity_public →
                                                            Tacenta.UnitLifecycleResponderFirstFrame.PrekeyIdsDistinct
                                                                storeB →
                                                              Tacenta.UnitLifecycleResponderFirstFrame.FirstKemAgrees
                                                                  storeB bundle.kem_prekey_id q.kemCiphertext
                                                                  q.kemSecret →
                                                                ∀ (rngB : E),
                                                                  traceB rngB = oracleB.draws →
                                                                    ∀ (dB : Model.Lifecycle.Key)
                                                                      (restB : List Model.Lifecycle.Key),
                                                                      traceB rngB = dB :: restB →
                                                                        ∀ (ptB : alloc.vec.Vec U8), ⋯
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderReply.responder_first_frame_successor_keys

/--
info: @Tacenta.UnitLifecycleResponderReply.initiator_first_send_responder_successor_keys : ∀
  [Tacenta.SessionUnitT1.DerivedKeysModel] {R E F : Type} (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R)
  (trace : R → List Model.Lifecycle.Key) (dh : Tacenta.UnitLifecycleT3.DhView) (kem : Tacenta.UnitLifecycleT3.KemView)
  (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle),
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
                      Tacenta.UnitLifecycleEstablishedEncrypt.KeyGenSeededFor oracle.braidKem rc crc trace →
                        Tacenta.UnitLifecycleEstablishedEncrypt.KeyGenSizesOf oracle.braidKem →
                          Tacenta.UnitLifecycleEstablishInitiatorShape.KemCiphertextLenOf →
                            Tacenta.UnitLifecycleRestoredSession.KemCiphertextLenBound →
                              ∀ (rcE : rand_core_1.RngCore E) (crcE : rand_core_1.CryptoRng E)
                                (ourA : lifecycle.Identity) (bundleA : lifecycle.PublishedBundle)
                                (expected : tacenta_boundary.dh.PublicKeyBytes) (rng0 rng1 : E) (s : lifecycle.Session),
                                lifecycle.establish_initiator_for rcE crcE ourA bundleA expected rng0 =
                                    ok (core.result.Result.Ok s, rng1) →
                                  ∀
                                    (q :
                                      Tacenta.UnitLifecycleResponderFirstFrame.InitiatorSecretParts rcE crcE ourA
                                        bundleA),
                                    s = q.session →
                                      ∀ (plaintext : Slice U8),
                                        (↑plaintext).length + 65770 ≤ Usize.max →
                                          ∀ (rng : R),
                                            trace rng = oracle.draws →
                                              ∀ (d1 d2 : Model.Lifecycle.Key) (rest : List Model.Lifecycle.Key),
                                                trace rng = d1 :: d2 :: rest →
                                                  ∀ (bytes : alloc.vec.Vec U8) (s' : lifecycle.Session) (rng' : R),
                                                    lifecycle.Session.encrypt rc crc s plaintext rng =
                                                        ok (core.result.Result.Ok bytes, s', rng') →
                                                      ∀ (rcB : rand_core_1.RngCore F) (crcB : rand_core_1.CryptoRng F)
                                                        (contracts :
                                                          Tacenta.UnitLifecycleT1.EstablishResponderContracts rcB),
                                                        Tacenta.UnitLifecycleEstablishInitiatorShape.DhPublicValid →
                                                          Tacenta.UnitLifecycleResponderFirstFrame.DhAgreeSymmetric →
                                                            Tacenta.UnitLifecycleResponderFirstReceipt.DhAgreeContributory →
                                                              Tacenta.UnitLifecycleResponderFirstReceipt.AeadRoundTrip →
                                                                ⋯
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderReply.initiator_first_send_responder_successor_keys

/--
info: @Tacenta.UnitLifecycleResponderReply.initiator_first_send_responder_replies : ∀ [Tacenta.SessionUnitT1.DerivedKeysModel]
  {R E F : Type} (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R) (trace : R → List Model.Lifecycle.Key)
  (dh : Tacenta.UnitLifecycleT3.DhView) (kem : Tacenta.UnitLifecycleT3.KemView) (view : Model.Lifecycle.CodewordView)
  (oracle : Model.Lifecycle.Oracle),
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
                      Tacenta.UnitLifecycleEstablishedEncrypt.KeyGenSeededFor oracle.braidKem rc crc trace →
                        Tacenta.UnitLifecycleEstablishedEncrypt.KeyGenSizesOf oracle.braidKem →
                          Tacenta.UnitLifecycleEstablishInitiatorShape.KemCiphertextLenOf →
                            Tacenta.UnitLifecycleRestoredSession.KemCiphertextLenBound →
                              ∀ (rcE : rand_core_1.RngCore E) (crcE : rand_core_1.CryptoRng E)
                                (ourA : lifecycle.Identity) (bundleA : lifecycle.PublishedBundle)
                                (expected : tacenta_boundary.dh.PublicKeyBytes) (rng0 rng1 : E) (s : lifecycle.Session),
                                lifecycle.establish_initiator_for rcE crcE ourA bundleA expected rng0 =
                                    ok (core.result.Result.Ok s, rng1) →
                                  ∀
                                    (q :
                                      Tacenta.UnitLifecycleResponderFirstFrame.InitiatorSecretParts rcE crcE ourA
                                        bundleA),
                                    s = q.session →
                                      ∀ (plaintext : Slice U8),
                                        (↑plaintext).length + 65770 ≤ Usize.max →
                                          ∀ (rng : R),
                                            trace rng = oracle.draws →
                                              ∀ (d1 d2 : Model.Lifecycle.Key) (rest : List Model.Lifecycle.Key),
                                                trace rng = d1 :: d2 :: rest →
                                                  ∀ (bytes : alloc.vec.Vec U8) (s' : lifecycle.Session) (rng' : R),
                                                    lifecycle.Session.encrypt rc crc s plaintext rng =
                                                        ok (core.result.Result.Ok bytes, s', rng') →
                                                      ∀ (rcB : rand_core_1.RngCore F) (crcB : rand_core_1.CryptoRng F)
                                                        (contracts :
                                                          Tacenta.UnitLifecycleT1.EstablishResponderContracts rcB),
                                                        Tacenta.UnitLifecycleEstablishInitiatorShape.DhPublicValid →
                                                          Tacenta.UnitLifecycleResponderFirstFrame.DhAgreeSymmetric →
                                                            Tacenta.UnitLifecycleResponderFirstReceipt.DhAgreeContributory →
                                                              Tacenta.UnitLifecycleResponderFirstReceipt.AeadRoundTrip →
                                                                ⋯
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderReply.initiator_first_send_responder_replies

/--
info: Tacenta.UnitLifecycleResponderReply.first_send_reply_reachable : ∀ (K : Model.Braid.Kem)
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
                                      (Model.Lifecycle.braidRandomness (List.map Tacenta.SessionUnitBraidT3.u8 seed)) ≠
                                    none →
                                  ∃ oracle bundle q bytes s' rng' ourB storeB sB' ptB storeB' rngB' bytesR sB'',
                                    oracle.braidKem = K ∧
                                      lifecycle.Session.encrypt Tacenta.UnitLifecycleIntegrationScreen.byteRng
                                            Tacenta.UnitLifecycleIntegrationScreen.byteCrc q.session
                                            Tacenta.UnitLifecycleEstablishedEncrypt.emptyPlaintext seed =
                                          ok (core.result.Result.Ok bytes, s', rng') ∧
                                        storeB.publish = ok bundle ∧
                                          lifecycle.establish_responder Tacenta.UnitLifecycleIntegrationScreen.byteRng
                                                Tacenta.UnitLifecycleIntegrationScreen.byteCrc ourB storeB bytes.deref
                                                seed =
                                              ok (core.result.Result.Ok (sB', ptB), storeB', rngB') ∧
                                            lifecycle.Session.encrypt Tacenta.UnitLifecycleIntegrationScreen.byteRng
                                                  Tacenta.UnitLifecycleIntegrationScreen.byteCrc sB'
                                                  Tacenta.UnitLifecycleEstablishedEncrypt.emptyPlaintext rngB' =
                                                ok (core.result.Result.Ok bytesR, sB'', rngB') ∧
                                              sB''.braid = sB'.braid
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderReply.first_send_reply_reachable

/--
info: def Tacenta.UnitLifecycleResponderReply.replierAfterSend : Model.State.Key →
  Model.State.Key →
    Model.State.Key →
      Model.State.Key → Model.State.Key → Model.State.Key → Model.State.Key → Model.State.Key → Model.Triple.State :=
fun ec prk k1 k2 a4 d dSend newPub =>
  {
    classical :=
      { dhsPub := newPub, dhrPub := some a4,
        rk :=
          (Model.State.kdfRk (Model.State.kdfRk ec d Model.State.LabelSet.tacenta).1 dSend
              Model.State.LabelSet.tacenta).1,
        cks :=
          some
            (Model.State.kdfCk
                (Model.State.kdfRk (Model.State.kdfRk ec d Model.State.LabelSet.tacenta).1 dSend
                    Model.State.LabelSet.tacenta).2).1,
        ckr := some (Model.State.kdfCk (Model.State.kdfRk ec d Model.State.LabelSet.tacenta).2).1, ns := 1, nr := 1,
        pn := 0, skipped := [], events := 1, labels := Model.State.LabelSet.tacenta },
    postQuantum :=
      { rk := prk, epoch := 0,
        chains :=
          [(0,
              { send := some { ck := (Model.SparseRatchet.kdfCk k2 1).1, n := 1 },
                receive := some { ck := (Model.SparseRatchet.kdfCk k1 1).1, n := 1 } })],
        skipped := [], direction := Model.SparseRatchet.Direction.b2a } }
-/
#guard_msgs in
#print Tacenta.UnitLifecycleResponderReply.replierAfterSend

/--
info: def Tacenta.UnitLifecycleResponderReply.replyKey : Model.State.Key →
  Model.State.Key → Model.State.Key → Model.State.Key → Model.State.Key :=
fun ec k2 d dSend =>
  Tacenta.UnitLifecycleResponderFirstReceipt.firstKey
    (Model.State.kdfRk (Model.State.kdfRk ec d Model.State.LabelSet.tacenta).1 dSend Model.State.LabelSet.tacenta).2 k2
-/
#guard_msgs in
#print Tacenta.UnitLifecycleResponderReply.replyKey

/--
info: def Tacenta.UnitLifecycleResponderReply.replyComposite : Model.State.Key → Model.CompositeHeader.Composite :=
fun newPub =>
  { dh := newPub, pn := UInt32.ofNat 0, n := UInt32.ofNat 0, pqEpoch := UInt64.ofNat 0, pqN := UInt64.ofNat 1,
    agEpoch := UInt64.ofNat 1, agType := Model.CompositeHeader.AgreementType.none, agChunk := none }
-/
#guard_msgs in
#print Tacenta.UnitLifecycleResponderReply.replyComposite

/--
info: def Tacenta.UnitLifecycleResponderReply.replyFrame : Model.Lifecycle.Oracle →
  Model.Lifecycle.Bytes → Model.State.Key → Model.State.Key → Model.Lifecycle.Bytes → Model.Lifecycle.Bytes :=
fun oracle ad newPub messageKey plaintext =>
  Model.CompositeHeader.encodeMessage (Tacenta.UnitLifecycleResponderReply.replyComposite newPub)
    (oracle.aeadSeal (Model.State.messageKeys messageKey Model.State.LabelSet.tacenta).1
      (Model.State.messageKeys messageKey Model.State.LabelSet.tacenta).2.1
      (Model.State.messageKeys messageKey Model.State.LabelSet.tacenta).2.2 plaintext
      (Model.Messages.concatAd ad
        (Model.CompositeHeader.encode (Tacenta.UnitLifecycleResponderReply.replyComposite newPub))))
-/
#guard_msgs in
#print Tacenta.UnitLifecycleResponderReply.replyFrame
