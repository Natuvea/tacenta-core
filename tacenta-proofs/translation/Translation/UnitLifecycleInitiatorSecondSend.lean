import Translation.UnitLifecycleResponderReplyReceipt

/-!
# The initiator's second send: `Session::encrypt` at the session the receipt of the reply returned

`UnitLifecycleResponderReplyReceipt` shows that the initiator's public `Session::decrypt` of the responder's reply, at
the session `s'` its first `encrypt` left and from the source `rng'` that call left, returns the responder's plaintext
and a session `s''` related to the model's step (`replyReceiptSession`), on one run from the initiator's establishment.
This module takes the initiator's next operation on that same session: its second `Session::encrypt`, at `s''` and from
the source `rngA'` the receipt left, on the same run (the same `s''`, from the same call on the same bytes).

## How

At `s''` the initiator's agreement is at `KeysSampled` epoch 1, emitting the 96-byte header (the encapsulation-key
seed, its hash and the header MAC) in 32-byte chunks, the chunk at index 0 already sent in the first frame; the receipt
cleared the pending initial message, so the frame is a bare ratchet frame.  So:
* `braid_send_keysSampled`: the translated `Braid::send` at `KeysSampled` clones the state (the key pair included; the
  authenticator's clone is the authenticator, `auth_clone_eq`, and the encoder's is the encoder,
  `erasureCloneAgrees`), advances the encoder by one `next_chunk`, returns the source it was given and no output.  The
  walk names every call on that path; none is an encapsulation, a decapsulation, a key generation or a draw.
  `braidSendTraceCounted_of_keysSampled` is the dispatch layer's counted draw record there.
* `send_output_none_of_no_draw`, `sparseOutput_none_of_no_draw`, `encryptProviders_of_invariant`: at every session
  that passes `Session::invariant` and meets `CounterHeadroom`, related to a model session whose agreement send reads
  no draw, the two Triple condition records of the encrypt route hold: the chain-table room and the chain and
  stored-key epoch bounds from the sparse ratchet's invariant, the epoch and counter bounds from the ceilings, and the
  new-key bound because a send that reads no draw has no output.  It is the generic form of the records the first send
  and the reply compute at their literal states.
* `second_send_key`, `second_model_step`, `first_send_model_session_encoder` (model only): the model Triple's send
  from `initiatorAfterReply` at epoch 0 succeeds with header `secondHeader` (the ratchet key the receipt installed,
  previous chain length 1, message number 0, sparse epoch 0 and number 2), key `secondKey` and successor
  `initiatorAfterSecond`; the model's `encrypt` there has one outcome, the bare `secondFrame` carrying the header
  encoder's next chunk, with no draw and the encoder advanced; and the model session the first send leaves holds the
  header encoder at position 1.
* `initiator_second_send_refines`: the generic dispatch-layer route `public_session_encrypt_of_send_contracts` at
  every session related to `replyReceiptSession` of a model session at `keysSampled` epoch 1 that passes the invariant
  and meets the ceilings.
* `initiator_second_send_after_reply` composes them on the run: `s''`, its relation and `rngA'` from
  `initiator_receives_reply`, the first send's key generation from `established_encrypt_outcomes` on the same call,
  the model session from `first_send_model_session_encoder`, the refinement at the initiator's oracle with the draws
  `rngA'` holds, the bytes and the session from `second_model_step`, and the source after the call from the walk
  (`encrypt_ok_parts`, `braid_send_keysSampled`).

## The statements

* `initiator_second_send_after_reply`: under the hypotheses of `initiator_receives_reply` and for every plaintext
  `ptS` of at most `Usize.max - 150` bytes, the receipt's conjuncts hold except the reply's bytes as `replyFrame` and
  the frame equation of `s''` against `s'` (both follow by applying the receipt again, since `encrypt` and `decrypt`
  are functions, but the statement does not carry them), with the first send's key generation
  `(dk, ekSeed, ekVector)` kept, the agreement of the model session `s''` refines reads no draw at its send, and the
  model's `encrypt` of `ptS` there has the one outcome above.  If `s''` passes `Session::invariant` and meets
  `CounterHeadroom` (the premises of an implication in the conclusion; neither is shown here), the public
  `Session::encrypt` of `ptS` at `s''` from `rngA'` returns `Ok bytes2` and a session `s'''` and leaves `rngA'` as it
  was (no draw); `s'''` is `s''` with only the Triple Ratchet and the agreement written and no pending initial message;
  `bytes2` is `secondFrame` (agreement type `hdr`, the header chunk at index 1, no initial wrapper) sealed under
  `secondKey` with the initiator's associated data; and `s'''` refines the model session after that step (the Triple
  `initiatorAfterSecond`, the header encoder at position 2).

## Laws and premises

No new law and no new per-run premise.  Beyond the hypotheses of `initiator_receives_reply`, the statement takes the
plaintext bound `102 + (ptS.length + 48) ≤ Usize.max`, which holds of every plaintext of at most `2^32 - 151` bytes on
a 32-bit target.  The encrypt records the second send uses are the ones the initiator's first send already takes
(`BraidSendRefinementContracts`, `TripleSendRefinementContracts`, `AeadSealBounded`, `DhCodecTotal`, `OracleOf`,
`DhCodecOf`, `CodewordViewSendOf`, the three `zeroize` round trips), at the source the receipt left (the oracle record
holds of the oracle with any draws, `oracleOf_with_draws`), and `Ct1LenTotal` from the initiator's decrypt record.  The
code-level conclusions are conditional on `Session::invariant` and `CounterHeadroom` at `s''`, which this module does
not derive.  At `KeysSampled` the agreement's send reads neither randomness nor a KEM operation
(`braid_send_keysSampled`), so no fact relating the two parties' KEMs is used for this step; the Braid send record still
carries `KemAgreesFor` at the initiator oracle's KEM, as the generic route takes it for every state, and whether it
could be dropped here is not checked.

## Trust

Every result here rests on the kernel and opaque constants only, with no compiler-trust axiom (pins below);
`initiator_second_send_refines` and `initiator_second_send_after_reply` apply the encrypt and decrypt refinements, whose
nine `native_decide` constants are kernel proofs since 2026-10-21.  The headline's statement pin is cut off by Lean's `⋯` after the binder `crcB`: it holds
the binders up to the contracts, and the later binders and the whole conclusion are held by the build and by reading
only, as with every pin that ends in `⋯` (with this module, 16 modules hold such pins; a pin form that prints the whole
statement is to be fixed separately).

## Non-vacuity

No law is added, so `reply_receipt_laws_model` still puts every law the statement takes in one interpretation, the
toy `InterpO.modelReply`.  `first_send_reply_receipt_reachable` exhibits, at the real constants under its laws, a run
at which every hypothesis of `initiator_receives_reply` holds, and the added plaintext bound holds of the empty
plaintext.  No run is exhibited at which the implication's premises hold: that `s''` passes `Session::invariant` and
meets `CounterHeadroom` is not shown, so the code-level part of the statement is not shown to apply to any run.

## What it does not show

* `Session::invariant` or `CounterHeadroom` at `s''` (the implication's premises) or at `s'''` after the send; a run
  at which the code-level part applies.
* The responder's receipt of this second message, a second reply and its receipt, the header's third chunk, the
  responder's first sampling send and every later step.  The statement covers exactly one further send by the
  initiator on this route, not a second exchange.
* A refusal `encrypt` can reach: at this state none occurs (the terminal guard is false, the agreement's send at
  `KeysSampled` does not refuse, the model's Triple send succeeds from message number 0 on the chain the receipt
  derived, the composite header is defined); the refusals reachable elsewhere in a session (the terminal guard,
  `AgreementFailed`, `ChainExhausted`, `NoSendingChain`) are not covered.
* That the code's key pair after the call equals the one before: the send clones it and the relation holds through
  `KemCloneAgrees`; code-level equality is not checked.
* A restored copy of `s''`; the one-time path in a run; that the related model sessions hold only bytes the parties
  received (the responder's relation is at the view that attributes the received codeword); that `hfreshB` holds under
  an honest random source.
* That the real primitives meet the boundary records or the laws the run rests on (`AeadRoundTrip`,
  `DhAgreeContributory`, `DhAgreeSymmetric`, `DhPublicValid`), that ML-KEM decapsulation agrees on a run
  (`FirstKemAgrees`), or `PrekeyIdsDistinct` from `PrekeyStore::invariant`; the model's own `establishResponder`
  equality.  The results list no compiler-trust axiom: the nine `native_decide` constants are kernel proofs since
  2026-10-21.
-/

open Aeneas Aeneas.Std Result
open tacenta_session_unit
open Tacenta.SessionUnitRatchetImportInv (bind_eq_ok_inv)

namespace Tacenta.UnitLifecycleInitiatorSecondSend

open Tacenta.UnitLifecycleT3 (DhView DhCodecOf KemView arrayOf vecOf sliceOf SessionRefines OracleOf
  BraidSendRefinementContracts TripleSendRefinementContracts CodewordViewSendOf PublicEncryptWitness
  ZeroizingRoundTrips EncryptNonterminalRouteProviders BraidSendTraceAgreementCounted
  GeneratedBraidSuccessEvidence RealSparseConversion)
open Tacenta.UnitLifecycleDecryptRunBounds (CounterHeadroom)

/-! ## The route's providers, from the invariant and the ceilings -/

/-- At a model agreement state whose send reads no draw, the model's send has no output.  Model only. -/
theorem send_output_none_of_no_draw (K : Model.Braid.Kem) (rand : Nat) (st : Model.Braid.BraidState)
    (h : Model.Lifecycle.braidSendNeedsDraw st = false) :
    (Model.Braid.send K rand st).2.2.1 = none := by
  cases st <;> simp [Model.Lifecycle.braidSendNeedsDraw, Model.Braid.send] at h ⊢

/-- The sparse output the generated `encrypt` hands the Triple at a model agreement whose send reads no draw is
`none`: the model's send there has no output (`send_output_none_of_no_draw`), so the code's has none. -/
theorem sparseOutput_none_of_no_draw {R : Type} {rc : rand_core_1.RngCore R}
    {crc : rand_core_1.CryptoRng R} {trace : R → List Model.Lifecycle.Key} {dh : DhView}
    {K : Model.Braid.Kem} {oracle : Model.Lifecycle.Oracle} {real : lifecycle.Session}
    {model : Model.Lifecycle.Session} {rng : R} {realMessage : tacenta_braid.Msg}
    {realEpoch : Std.U64} {realOutput : Option tacenta_braid.Output}
    {realBraidNext : tacenta_braid.Braid} {rngNext : R}
    {sparseOutput : Option tacenta_spqr.Output}
    (hdraw : Model.Lifecycle.braidSendNeedsDraw model.braid = false)
    (hsparse : RealSparseConversion realOutput sparseOutput)
    (hevidence : Nonempty (GeneratedBraidSuccessEvidence rc crc trace dh K oracle real model rng
      realMessage realEpoch realOutput realBraidNext rngNext)) :
    sparseOutput = none := by
  obtain ⟨ev⟩ := hevidence
  have hsend := ev.modelSend
  rw [Model.Lifecycle.sendAgreement_no_draw _ _ hdraw] at hsend
  have h1 := (Prod.mk.inj (Option.some.inj hsend)).1
  have hout : ev.modelOutput = none := by
    have h2 := congrArg (fun y => y.2.2.1) h1
    simp only at h2
    rw [← h2]
    exact send_output_none_of_no_draw _ _ _ hdraw
  have hreal : realOutput = none := by
    have h := ev.output
    rw [hout] at h
    cases realOutput with
    | none => rfl
    | some o => exact h.elim
  cases hsparse with
  | none => rfl
  | some _ _ hsome _ => rw [hreal] at hsome; cases hsome

/-- **The providers of the encrypt route at every session that passes `Session::invariant` and meets the four
counter ceilings, when the related model agreement's send reads no draw**: both Triple condition records, for
every generated run.  The chain-table room, the chain and stored-key epoch bounds come from the sparse ratchet's
invariant (with the sparse epoch ceiling for the two epoch bounds), the epoch and counter bounds from
`CounterHeadroom`, carried to the model through the relation, and the new-key bound holds because a send that
reads no draw has no output. -/
theorem encryptProviders_of_invariant [Tacenta.SessionUnitT1.DerivedKeysModel] {R : Type}
    {rc : rand_core_1.RngCore R} {crc : rand_core_1.CryptoRng R}
    {trace : R → List Model.Lifecycle.Key} (dh : DhView) (kem : KemView) (K : Model.Braid.Kem)
    (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle) (real : lifecycle.Session)
    (model : Model.Lifecycle.Session) (hinv : lifecycle.Session.invariant real = ok true)
    (hrel : SessionRefines dh K real model) (hc : CounterHeadroom real)
    (hdraw : Model.Lifecycle.braidSendNeedsDraw model.braid = false)
    (plaintext : Slice Std.U8) (rng : R) :
    Nonempty (EncryptNonterminalRouteProviders rc crc trace dh kem K view oracle real model plaintext rng) := by
  obtain ⟨htriple, -⟩ := Tacenta.UnitLifecycleT1.leaf_check_gives_leaf_invariants real
    (Tacenta.UnitLifecycleT1.session_invariant_gives_leaf_check real hinv)
  have hspqInv : Tacenta.SessionUnitRatchetImportInv.Spqr.Inv real.triple.post_quantum :=
    (Tacenta.SessionUnitRatchetImportInv.Spqr.invariant_true_iff _).mp
      (Tacenta.UnitHeadroomInvariant.triple_invariant_gives_spqr _ htriple)
  obtain ⟨-, hpq⟩ := hrel.triple
  have hS : Tacenta.SessionUnitSpqrT3.StateRefines real.triple.post_quantum model.triple.postQuantum :=
    hpq ▸ Tacenta.SessionUnitTripleT3.spqrAbs_refines real.triple.post_quantum
  have hfam := Tacenta.SessionUnitDecodedStateDischarge.session_unit_spqr_epoch_family hspqInv hc.sparseEpoch
  have hroom0 := Tacenta.SessionUnitRatchetImportInv.Spqr.inv_gives_chain_room _ hspqInv
  have hroom : model.triple.postQuantum.chains.length + 1 < Usize.max := by
    rw [← hS.chains, List.length_map]; omega
  have hcb : ∀ q ∈ model.triple.postQuantum.chains, q.1 + Model.SparseRatchet.epochsKept ≤ Std.U64.max := by
    intro p hp
    rw [← hS.chains, List.mem_map] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    exact hfam.1 q hq
  have hsb : ∀ sk ∈ model.triple.postQuantum.skipped, sk.1 + Model.SparseRatchet.epochsKept ≤ Std.U64.max := by
    intro sk hsk
    rw [← hS.skipped, List.mem_map] at hsk
    obtain ⟨q, hq, rfl⟩ := hsk
    exact hfam.2 q hq
  have hepoch : model.triple.postQuantum.epoch + 1 < Std.U64.max := by
    rw [← hS.epoch]; exact hc.sparseEpoch
  have hcounter := Tacenta.UnitLifecycleDecryptRunBounds.sparseCounters_transport hS hc.sparseCounters
  exact ⟨{
    refusal := fun _ _ _ _ _ _ _ _ _ _ _ hsparse _ hev =>
      { derivedKeys := inferInstance, room := hroom, chainBound := hcb, skippedBound := hsb
        newBound := by
          intro o ho
          rw [sparseOutput_none_of_no_draw hdraw hsparse hev] at ho
          cases ho
        epochBound := hepoch, counterBound := hcounter }
    success := fun _ _ _ _ _ _ _ _ _ _ _ _ hsparse _ hev =>
      { derivedKeys := inferInstance, room := hroom, chainBound := hcb, skippedBound := hsb
        newBound := by
          intro o ho
          rw [sparseOutput_none_of_no_draw hdraw hsparse hev] at ho
          cases ho
        epochBound := hepoch, counterBound := hcounter } }⟩

/-! ## The agreement's send while it emits the header -/

/-- **`Braid::send` at `KeysSampled` takes no randomness and emits the header encoder's next chunk**: at a
`KeysSampled` state, every return of the send leaves the source as given, has no output, and is the state's
clone (the key pair cloned, the authenticator and the encoder as given) with the encoder advanced by one
`next_chunk`, the message being `Msg::with` of the state's epoch, type `Hdr` and that chunk.  Hypothesis-free
(the encoder's clone is the encoder, `erasureCloneAgrees`). -/
theorem braid_send_keysSampled {R : Type} (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R)
    (b : tacenta_braid.Braid) (epoch : U64) (auth : tacenta_braid.Auth)
    (kp : tacenta_kem.IncrementalKeyPair) (enc : tacenta_erasure.Encoder)
    (hst : b.state = tacenta_braid.State.KeysSampled epoch auth kp enc) (rng : R)
    (x : tacenta_braid.Msg × U64 × Option tacenta_braid.Output × tacenta_braid.Braid) (rngN : R)
    (h : tacenta_braid.Braid.send rc crc b rng = ok (x, rngN)) :
    rngN = rng ∧ x.2.2.1 = none ∧
      ∃ kp' chunk enc', tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone kp = ok kp' ∧
        tacenta_erasure.Encoder.next_chunk enc = ok (chunk, enc') ∧
        tacenta_braid.Msg.with epoch tacenta_braid.MsgType.Hdr chunk = ok x.1 ∧
        x.2.2.2 = { state := tacenta_braid.State.KeysSampled epoch auth kp' enc' } := by
  obtain ⟨st⟩ := b
  simp only at hst
  subst hst
  unfold tacenta_braid.Braid.send at h
  simp only [tacenta_braid.State.Insts.CoreCloneClone.clone, lift, core.clone.impls.CloneU64.clone,
    bind_tc_ok] at h
  obtain ⟨s, hs1, h1⟩ := bind_eq_ok_inv h
  rw [Tacenta.UnitLifecycleResponderReply.auth_clone_eq] at hs1
  simp only [bind_tc_ok] at hs1
  obtain ⟨kp', hkp, hs2⟩ := bind_eq_ok_inv hs1
  obtain ⟨e', he, hs3⟩ := bind_eq_ok_inv hs2
  have he' := Tacenta.UnitSatisfiabilityErasureAgrees.erasureCloneAgrees.1 enc e' he
  simp only [ok.injEq] at hs3
  subst he'
  subst hs3
  obtain ⟨⟨⟨m, o, nxt⟩, rng1⟩, hstep, h⟩ := bind_eq_ok_inv h1
  simp only [tacenta_braid.Braid.step_send] at hstep
  obtain ⟨⟨chunk, enc1⟩, hnc, hstep⟩ := bind_eq_ok_inv hstep
  obtain ⟨msg, hmsg, hstep⟩ := bind_eq_ok_inv hstep
  simp only [ok.injEq, Prod.mk.injEq] at hstep
  obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := hstep
  obtain ⟨r, -, h⟩ := bind_eq_ok_inv h
  simp only [ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨rfl, rfl, kp', chunk, enc1, hkp, hnc, hmsg, rfl⟩

/-- **The counted draw record of the dispatch layer at a session whose agreement is at `KeysSampled`**: the send
reads no draw (`braid_send_keysSampled`), the model's send there reads none, and the model encoder the state emits
from has codewords left.  Hypothesis-free beyond the two state equations, the encoder's position and the oracle's
KEM. -/
theorem braidSendTraceCounted_of_keysSampled {R : Type} {rc : rand_core_1.RngCore R}
    {crc : rand_core_1.CryptoRng R} {trace : R → List Model.Lifecycle.Key} {K : Model.Braid.Kem}
    {oracle : Model.Lifecycle.Oracle} {real : lifecycle.Session} {model : Model.Lifecycle.Session}
    {rng : R} (hkem : oracle.braidKem = K) (epoch : U64) (auth : tacenta_braid.Auth)
    (kp : tacenta_kem.IncrementalKeyPair) (enc : tacenta_erasure.Encoder)
    (hreal : real.braid.state = .KeysSampled epoch auth kp enc) (e : Nat) (a : Model.Braid.Auth)
    (dk ekVector : Model.Braid.Bytes) (encM : Model.Braid.Encoder)
    (hmodel : model.braid = .keysSampled e a dk ekVector encM) (hlive : encM.next < 65536) :
    BraidSendTraceAgreementCounted rc crc trace K oracle real model rng where
  encodersLive := by
    intro enc' henc
    rw [hmodel] at henc
    simp only [Tacenta.SessionUnitBraidT3.EncoderOf, Option.some.injEq] at henc
    subst henc
    exact hlive
  braidKem := hkem
  noDrawTrace := by
    intro m ep o b rngNext hsend _
    obtain ⟨hr, -⟩ := braid_send_keysSampled rc crc real.braid epoch auth kp enc hreal rng _ rngNext hsend
    rw [hr]
  drawTrace := by
    intro _ _ _ _ _ _ hneeds
    rw [hmodel] at hneeds
    simp [Model.Lifecycle.braidSendNeedsDraw] at hneeds
  drawPost := by
    intro _ _ _ _ _ _ hneeds
    rw [hmodel] at hneeds
    simp [Model.Lifecycle.braidSendNeedsDraw] at hneeds

/-! ## The model's second send -/

section Model
open Model.State (Key)
open Tacenta.UnitLifecycleResponderReplyReceipt (initiatorAfterReply replyReceiptSession)

/-- The initiator's Triple after its second send: the classical sending chain the receipt of the reply derived,
stepped once (one message sent on it), the sparse sending chain of epoch 0 stepped from number 1 to 2; everything
else as after the receipt. -/
def initiatorAfterSecond (rkA prk k1 k2 dSend x newPub candPub : Key) : Model.Triple.State :=
  { classical :=
      { dhsPub := candPub, dhrPub := some newPub,
        rk := (Model.State.kdfRk (Model.State.kdfRk rkA dSend .tacenta).1 x .tacenta).1,
        cks := some (Model.State.kdfCk
          (Model.State.kdfRk (Model.State.kdfRk rkA dSend .tacenta).1 x .tacenta).2).1,
        ckr := some (Model.State.kdfCk (Model.State.kdfRk rkA dSend .tacenta).2).1,
        ns := 1, nr := 1, pn := 1, skipped := [], events := 1, labels := .tacenta }
    postQuantum :=
      { rk := prk, epoch := 0,
        chains :=
          [(0, { send := some ⟨(Model.SparseRatchet.kdfCk (Model.SparseRatchet.kdfCk k1 1).1 2).1, 2⟩
                 receive := some ⟨(Model.SparseRatchet.kdfCk k2 1).1, 1⟩ })],
        skipped := [], direction := .a2b } }

/-- The second message's Triple header: the ratchet key `candPub` the receipt of the reply installed, classical
message number 0 on the new chain, previous chain length 1, sparse epoch 0 and sparse message number 2. -/
def secondHeader (candPub : Key) : Model.Triple.Header := ⟨⟨candPub, 1, 0⟩, 0, 2⟩

/-- The second message's key: the combination of the classical message key of the sending chain the receipt of
the reply derived (root `rkA` after `dSend`, then `x`) and the sparse message key of `k1`'s chain at number 2. -/
def secondKey (rkA k1 dSend x : Key) : Key :=
  Model.TripleRatchet.combine
    (Model.State.kdfCk (Model.State.kdfRk (Model.State.kdfRk rkA dSend .tacenta).1 x .tacenta).2).2
    (Model.SparseRatchet.kdfCk (Model.SparseRatchet.kdfCk k1 1).1 2).2

/-- **The model's second send from the initiator after the receipt of the reply**: header `secondHeader candPub`,
key `secondKey`, successor `initiatorAfterSecond`.  Hypothesis-free. -/
theorem second_send_key (rkA prk k1 k2 dSend x newPub candPub : Key) :
    Model.Triple.sendDetailed (initiatorAfterReply rkA prk k1 k2 dSend x newPub candPub) 0 none =
      .ok (initiatorAfterSecond rkA prk k1 k2 dSend x newPub candPub, secondHeader candPub,
        secondKey rkA k1 dSend x) := by
  simp [Model.Triple.sendDetailed, Model.Ratchet.sendDetailed, Model.SparseRatchet.sendDetailed,
    Model.SparseRatchet.maybeAdvanceDetailed, Model.SparseRatchet.findChains, initiatorAfterReply,
    initiatorAfterSecond, secondHeader, secondKey, Model.State.u32Max, Model.SparseRatchet.u64Max,
    Model.SparseRatchet.setChains]

/-- The second message's composite header: the ratchet key `candPub`, classical numbers 1 (previous chain) and
0, sparse epoch 0 and number 2, agreement epoch 1, agreement type `hdr`, and the chunk as the view sends it from
the agreement state `braid`. -/
def secondComposite (view : Model.Lifecycle.CodewordView) (braid : Model.Braid.BraidState) (candPub : Key)
    (chunk : Model.Braid.Chunk) : Model.CompositeHeader.Composite :=
  { dh := candPub
    pn := UInt32.ofNat 1
    n := UInt32.ofNat 0
    pqEpoch := UInt64.ofNat 0
    pqN := UInt64.ofNat 2
    agEpoch := UInt64.ofNat 1
    agType := .hdr
    agChunk := some (view.send braid chunk) }

/-- The second frame: the composite header and the plaintext sealed under the message key, with the associated
data `ad` followed by the encoded header.  No initial wrapper. -/
def secondFrame (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle)
    (ad : Model.Lifecycle.Bytes) (braid : Model.Braid.BraidState) (candPub messageKey : Key)
    (chunk : Model.Braid.Chunk) (plaintext : Model.Lifecycle.Bytes) : Model.Lifecycle.Bytes :=
  Model.CompositeHeader.encodeMessage (secondComposite view braid candPub chunk)
    (oracle.aeadSeal (Model.State.messageKeys messageKey .tacenta).1
      (Model.State.messageKeys messageKey .tacenta).2.1
      (Model.State.messageKeys messageKey .tacenta).2.2 plaintext
      (Model.Messages.concatAd ad (Model.CompositeHeader.encode (secondComposite view braid candPub chunk))))

/-- The second frame reads only the oracle's seal: it is the same at the oracle with any draws. -/
theorem secondFrame_with_draws (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle)
    (draws : List Key) (ad : Model.Lifecycle.Bytes) (braid : Model.Braid.BraidState) (candPub messageKey : Key)
    (chunk : Model.Braid.Chunk) (plaintext : Model.Lifecycle.Bytes) :
    secondFrame view { oracle with draws := draws } ad braid candPub messageKey chunk plaintext =
      secondFrame view oracle ad braid candPub messageKey chunk plaintext :=
  rfl

/-- **The model's `encrypt` at the initiator after the receipt of the reply has one outcome**, for every codeword
view, oracle and plaintext, when the session the receipt started from had its agreement at `keysSampled` epoch 1:
it reads no draw, returns the bare second frame (`secondFrame`: agreement type `hdr` and the encoder's next chunk,
no initial wrapper since the receipt cleared the pending initial message), and leaves the session with the Triple
`initiatorAfterSecond` and the agreement's encoder advanced by one chunk, everything else unchanged.  Model
only. -/
theorem second_model_step (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle)
    (mA : Model.Lifecycle.Session) (rkA prk k1 k2 dSend x newPub candPub c : Key) (a : Model.Braid.Auth)
    (dk ekVector : Model.Braid.Bytes) (enc : Model.Braid.Encoder)
    (hbraid : mA.braid = .keysSampled 1 a dk ekVector enc) (pt : Model.Lifecycle.Bytes) :
    Model.Lifecycle.encrypt view oracle (replyReceiptSession mA rkA prk k1 k2 dSend x newPub candPub c) pt =
      { session := { replyReceiptSession mA rkA prk k1 k2 dSend x newPub candPub c with
          triple := initiatorAfterSecond rkA prk k1 k2 dSend x newPub candPub
          braid := .keysSampled 1 a dk ekVector enc.nextChunk.2 }
        result := .ok (secondFrame view oracle mA.identityAd (.keysSampled 1 a dk ekVector enc) candPub
          (secondKey rkA k1 dSend x) enc.nextChunk.1 pt)
        oracle := oracle } := by
  simp [Model.Lifecycle.encrypt, Model.Lifecycle.agreementFailed, Model.Lifecycle.sendAgreement,
    Model.Lifecycle.braidSendNeedsDraw, Model.Braid.send, Model.Lifecycle.braidFailed,
    Model.Lifecycle.sparseOutputOf, Model.Braid.BraidState.epoch, replyReceiptSession, hbraid,
    second_send_key, Model.Lifecycle.compositeOf, Model.Lifecycle.compositeTypeOf, secondFrame,
    secondComposite, secondHeader]

end Model

/-! ## The encrypt refinement at the session after the receipt of the reply -/

section Refines
open Tacenta.UnitLifecycleResponderReplyReceipt (replyReceiptSession)

/-- **The public `Session::encrypt` at a session related to the model session after the receipt of the reply
refines the model's step**: for a session `s''` that refines `replyReceiptSession mA …`, where the agreement of
`mA` is at `keysSampled` epoch 1 with an encoder that has codewords left, that passes `Session::invariant` and meets
`CounterHeadroom`, every plaintext of at most `Usize.max - 150` bytes and every source state, the call returns, and
its result, its post-state and the draws it leaves refine `Model.Lifecycle.encrypt` there.  Under the encrypt
boundary records on that source, the oracle record, `DhCodecOf`, `CodewordViewSendOf`, three `zeroize` round trips,
`Ct1LenTotal` and the trace equation.  The generic dispatch-layer route (`public_session_encrypt_of_send_contracts`)
with its session-specific inputs discharged here: the providers from the invariant and the ceilings
(`encryptProviders_of_invariant`), the counted draw record at `KeysSampled`, and the headroom from the invariant
with no pending initial message (`encryptHeadroom_reply`). -/
theorem initiator_second_send_refines [Tacenta.SessionUnitT1.DerivedKeysModel] {R : Type}
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
    (mA : Model.Lifecycle.Session) (rkA prk k1 k2 dSend x newPub candPub c : Model.State.Key)
    (a : Model.Braid.Auth) (dk ekVector : Model.Braid.Bytes) (enc : Model.Braid.Encoder)
    (hbraid : mA.braid = .keysSampled 1 a dk ekVector enc) (hlive : enc.next < 65536)
    (s'' : lifecycle.Session)
    (hrel : SessionRefines dh oracle.braidKem s''
      (replyReceiptSession mA rkA prk k1 k2 dSend x newPub candPub c))
    (hinv : lifecycle.Session.invariant s'' = ok true) (hc : CounterHeadroom s'')
    (plaintext : Slice Std.U8) (hroom : 102 + (plaintext.val.length + 48) ≤ Usize.max)
    (rng : R) (htrace : trace rng = oracle.draws) :
    PublicEncryptWitness rc crc trace dh oracle.braidKem view oracle s''
      (replyReceiptSession mA rkA prk k1 k2 dSend x newPub candPub c) plaintext rng := by
  have hpendR : s''.pending_initial = none := by
    have h := hrel.pendingInitial
    simp only [replyReceiptSession, Option.map_eq_none_iff] at h
    exact h
  have hmb : (replyReceiptSession mA rkA prk k1 k2 dSend x newPub candPub c).braid =
      .keysSampled 1 a dk ekVector enc := hbraid
  have hb := hrel.braid
  rw [hmb] at hb
  obtain ⟨epoch, auth, kp, encoder, hst, -⟩ :=
    Tacenta.UnitLifecycleEstablishedEncrypt.state_keysSampled_of_refines hb
  have hdraw : Model.Lifecycle.braidSendNeedsDraw
      (replyReceiptSession mA rkA prk k1 k2 dSend x newPub candPub c).braid = false := by
    rw [hmb]; rfl
  obtain ⟨providers⟩ := encryptProviders_of_invariant dh kem oracle.braidKem view oracle s'' _ hinv hrel hc
    hdraw plaintext rng
  exact Tacenta.UnitLifecycleT3.public_session_encrypt_of_send_contracts braid
    (braidSendTraceCounted_of_keysSampled rfl epoch auth kp encoder hst 1 a dk ekVector enc hmb hlive)
    triple aead dhCodec
    (Tacenta.UnitLifecycleResponderReply.encryptHeadroom_reply dhCodec hct1 s'' hinv hpendR plaintext hroom)
    oracleOf codec codewordView braid.hkdf hz80 hz32 hzKeys hrel htrace providers

end Refines

/-! ## The initiator's second send, on the run -/

section Comp

open Tacenta.UnitLifecycleResponderReplyReceipt (initiatorAfterReply replyReceiptSession initiator_receives_reply)
open Tacenta.UnitLifecycleResponderFirstReceipt (headerSource senderAfterFirst firstKey DhAgreeContributory
  AeadRoundTrip established_triple_first first_send_key)
open Tacenta.UnitLifecycleResponderFirstFrame (InitiatorSecretParts DhAgreeSymmetric PrekeyIdsDistinct
  FirstKemAgrees)
open Tacenta.UnitLifecycleDecryptRatchetT3 (DecryptRatchetAgreements)
open Tacenta.UnitLifecycleEstablishInitiatorShape (DhPublicValid establishedModelOf)
open Tacenta.UnitLifecycleResponderReply (replyFrame oracleOf_with_draws)

variable {our : lifecycle.Identity} {bundle : lifecycle.PublishedBundle}

/-- **The model session the initiator's first send leaves, with its encoder**: when the model's key generation
answers `(dk, ekSeed, ekVector)` at the two draws, the established model session with the Triple after the first
message and the agreement at `keysSampled` epoch 1, holding `dk`, `ekVector` and the header encoder of
`headerSource` after one chunk (position 1).  Model only (through the establishment's parts). -/
theorem first_send_model_session_encoder {E : Type} {rcE : rand_core_1.RngCore E}
    {crcE : rand_core_1.CryptoRng E} (dh : DhView) (view : Model.Lifecycle.CodewordView)
    (oracle : Model.Lifecycle.Oracle) (q : InitiatorSecretParts rcE crcE our bundle)
    (plaintext : Model.Lifecycle.Bytes) (d1 d2 : Model.Lifecycle.Key) (rest : List Model.Lifecycle.Key)
    (hdraws : oracle.draws = d1 :: d2 :: rest) (dk ekSeed ekVector : Model.Braid.Bytes)
    (hkg : oracle.braidKem.keyGen (Model.Lifecycle.braidRandomness (d1 ++ d2)) = some (dk, ekSeed, ekVector)) :
    (Model.Lifecycle.encrypt view oracle (establishedModelOf dh q.session) plaintext).session =
      { establishedModelOf dh q.session with
        triple := senderAfterFirst (arrayOf q.ratchetBytes) (arrayOf q.peerRatchetBytes) (arrayOf q.rootKey)
          (arrayOf q.sendChain) (arrayOf q.sparseRoot) (arrayOf q.sparseSend) (arrayOf q.sparseReceive)
        braid := .keysSampled 1 (Tacenta.SessionUnitBraidT3.AuthOf q.auth) dk ekVector
          ⟨headerSource oracle.braidKem (Tacenta.SessionUnitBraidT3.AuthOf q.auth) ekSeed ekVector, 1⟩ } := by
  obtain ⟨-, hc⟩ := Tacenta.UnitLifecycleEstablishedEncrypt.established_encrypt_model_cases dh view oracle
    q.toInitiatorOutputParts plaintext d1 d2 rest hdraws
  rcases hc with ⟨hnone, -⟩ | ⟨dk', ekSeed', ekVector', hkg', tripleNext, header, mk, chunk, encoder, pending,
    htriple, hnc, -, -, hsess⟩
  · rw [hkg] at hnone; cases hnone
  rw [hkg] at hkg'
  simp only [Option.some.injEq, Prod.mk.injEq] at hkg'
  obtain ⟨rfl, rfl, rfl⟩ := hkg'
  rw [established_triple_first dh q.toInitiatorOutputParts, first_send_key] at htriple
  simp only [Except.ok.injEq, Prod.mk.injEq] at htriple
  obtain ⟨rfl, -, -⟩ := htriple
  have henc := congrArg Prod.snd hnc
  simp only [Model.Braid.encode, Model.Braid.Encoder.nextChunk] at henc
  rw [hsess, ← henc]
  rfl

/-- **The initiator's second send, on the run of the reply's receipt.**  Under the hypotheses of
`initiator_receives_reply` (the run from the initiator's establishment through its first send, the responder's
receipt and reply, and the initiator's receipt of the reply, with the per-run premises that the initiator's source
after its first send holds a draw `dA` and that the responder's fresh ratchet key is not the peer key the initiator
holds), and for every plaintext `ptS` of at most `Usize.max - 150` bytes: the receipt's conjuncts hold (the two
agreements, the responder's `encrypt` of its reply, the initiator's `decrypt` of the reply returning `Ok ptA` and `s''`
from `rng'` and leaving `rngA'`, whose trace is the rest after `dA`, no pending initial message at `s''`, and the
relation of `s''`) except the reply's bytes as `replyFrame` and the frame equation of `s''` against `s'`, which follow
by applying the receipt again but are not carried here, with the key generation of the first send kept, and

* the model's `encrypt` of `ptS` at the model session `s''` refines (oracle with the draws `rngA'` holds) has one
  outcome: the bare second frame `secondFrame` (classical numbers 1 and 0 under the ratchet key the receipt
  installed, sparse epoch 0 and number 2, agreement epoch 1, type `hdr`, the header chunk at index 1, no initial
  wrapper), sealed under `secondKey` with the initiator's associated data; the session with the Triple
  `initiatorAfterSecond` and the header encoder at position 2; no draw; and the model agreement there reads no draw;
* if `s''` passes `Session::invariant` and meets `CounterHeadroom`, the public `Session::encrypt` of `ptS` at
  `s''` from `rngA'` returns `Ok bytes2` and `s'''` and leaves `rngA'` as it was; `s'''` is `s''` with only the
  Triple Ratchet and the agreement written, no pending initial message; `bytes2` is that frame; and `s'''` refines
  that model session.

The invariant and the ceilings at `s''` are not shown here: they are the implication's premises.
No compiler-trust axiom (the pin): the nine `native_decide` constants of the encrypt and decrypt refinements it applies
are kernel proofs since 2026-10-21. -/
theorem initiator_second_send_after_reply [Tacenta.SessionUnitT1.DerivedKeysModel] {R E F : Type}
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
    (contractsA : Tacenta.UnitLifecycleT1.DecryptRatchetContracts rc)
    (agreementsA : DecryptRatchetAgreements oracle.braidKem)
    (dA : Model.Lifecycle.Key) (restA : List Model.Lifecycle.Key) (hdrawA : trace rng' = dA :: restA)
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
    (ptR : Slice Std.U8) (hroomR : 102 + (ptR.val.length + 48) ≤ Usize.max) (rngR : F)
    (hfreshB : oracleB.dhPublic dB ≠ arrayOf q.peerRatchetBytes)
    (ptS : Slice Std.U8) (hroomS : 102 + (ptS.val.length + 48) ≤ Usize.max) :
    ∃ (dSend x : Model.Lifecycle.Key) (bytesR : alloc.vec.Vec Std.U8) (sB'' : lifecycle.Session)
      (ptA : alloc.vec.Vec Std.U8) (s'' : lifecycle.Session) (rngA' : R) (dk ekSeed ekVector : Model.Braid.Bytes),
      oracle.braidKem.keyGen (Model.Lifecycle.braidRandomness (d1 ++ d2)) = some (dk, ekSeed, ekVector) ∧
      oracleB.dhAgree dB (arrayOf q.ratchetBytes) = some dSend ∧
      oracle.dhAgree dA (oracleB.dhPublic dB) = some x ∧
      lifecycle.Session.encrypt rcB crcB sB' ptR rngR = ok (core.result.Result.Ok bytesR, sB'', rngR) ∧
      lifecycle.Session.decrypt rc crc s' (alloc.vec.Vec.deref bytesR) rng' =
        ok (core.result.Result.Ok ptA, s'', rngA') ∧
      ptA.val = ptR.val ∧ trace rngA' = restA ∧ s''.pending_initial = none ∧
      SessionRefines dh oracle.braidKem s''
        (replyReceiptSession
          (Model.Lifecycle.encrypt view oracle (establishedModelOf dh s) (sliceOf plaintext)).session
          (arrayOf q.rootKey) (arrayOf q.sparseRoot) (arrayOf q.sparseSend) (arrayOf q.sparseReceive) dSend x
          (oracleB.dhPublic dB) (oracle.dhPublic dA) dA) ∧
      Model.Lifecycle.braidSendNeedsDraw
        (replyReceiptSession
          (Model.Lifecycle.encrypt view oracle (establishedModelOf dh s) (sliceOf plaintext)).session
          (arrayOf q.rootKey) (arrayOf q.sparseRoot) (arrayOf q.sparseSend) (arrayOf q.sparseReceive) dSend x
          (oracleB.dhPublic dB) (oracle.dhPublic dA) dA).braid = false ∧
      Model.Lifecycle.encrypt view { oracle with draws := restA }
        (replyReceiptSession
          (Model.Lifecycle.encrypt view oracle (establishedModelOf dh s) (sliceOf plaintext)).session
          (arrayOf q.rootKey) (arrayOf q.sparseRoot) (arrayOf q.sparseSend) (arrayOf q.sparseReceive) dSend x
          (oracleB.dhPublic dB) (oracle.dhPublic dA) dA) (sliceOf ptS) =
        { session :=
            { replyReceiptSession
                (Model.Lifecycle.encrypt view oracle (establishedModelOf dh s) (sliceOf plaintext)).session
                (arrayOf q.rootKey) (arrayOf q.sparseRoot) (arrayOf q.sparseSend) (arrayOf q.sparseReceive) dSend x
                (oracleB.dhPublic dB) (oracle.dhPublic dA) dA with
              triple := initiatorAfterSecond (arrayOf q.rootKey) (arrayOf q.sparseRoot) (arrayOf q.sparseSend)
                (arrayOf q.sparseReceive) dSend x (oracleB.dhPublic dB) (oracle.dhPublic dA)
              braid := .keysSampled 1 (Tacenta.SessionUnitBraidT3.AuthOf q.auth) dk ekVector
                ⟨headerSource oracle.braidKem (Tacenta.SessionUnitBraidT3.AuthOf q.auth) ekSeed ekVector, 2⟩ }
          result := .ok (secondFrame view oracle (vecOf q.identityAd)
            (.keysSampled 1 (Tacenta.SessionUnitBraidT3.AuthOf q.auth) dk ekVector
              ⟨headerSource oracle.braidKem (Tacenta.SessionUnitBraidT3.AuthOf q.auth) ekSeed ekVector, 1⟩)
            (oracle.dhPublic dA) (secondKey (arrayOf q.rootKey) (arrayOf q.sparseSend) dSend x)
            ⟨headerSource oracle.braidKem (Tacenta.SessionUnitBraidT3.AuthOf q.auth) ekSeed ekVector, 1⟩
            (sliceOf ptS))
          oracle := { oracle with draws := restA } } ∧
      (lifecycle.Session.invariant s'' = ok true → CounterHeadroom s'' →
        ∃ (bytes2 : alloc.vec.Vec Std.U8) (s''' : lifecycle.Session),
          lifecycle.Session.encrypt rc crc s'' ptS rngA' = ok (core.result.Result.Ok bytes2, s''', rngA') ∧
          s''' = { s'' with triple := s'''.triple, braid := s'''.braid } ∧ s'''.pending_initial = none ∧
          vecOf bytes2 = secondFrame view oracle (vecOf q.identityAd)
            (.keysSampled 1 (Tacenta.SessionUnitBraidT3.AuthOf q.auth) dk ekVector
              ⟨headerSource oracle.braidKem (Tacenta.SessionUnitBraidT3.AuthOf q.auth) ekSeed ekVector, 1⟩)
            (oracle.dhPublic dA) (secondKey (arrayOf q.rootKey) (arrayOf q.sparseSend) dSend x)
            ⟨headerSource oracle.braidKem (Tacenta.SessionUnitBraidT3.AuthOf q.auth) ekSeed ekVector, 1⟩
            (sliceOf ptS) ∧
          SessionRefines dh oracle.braidKem s'''
            { replyReceiptSession
                (Model.Lifecycle.encrypt view oracle (establishedModelOf dh s) (sliceOf plaintext)).session
                (arrayOf q.rootKey) (arrayOf q.sparseRoot) (arrayOf q.sparseSend) (arrayOf q.sparseReceive) dSend x
                (oracleB.dhPublic dB) (oracle.dhPublic dA) dA with
              triple := initiatorAfterSecond (arrayOf q.rootKey) (arrayOf q.sparseRoot) (arrayOf q.sparseSend)
                (arrayOf q.sparseReceive) dSend x (oracleB.dhPublic dB) (oracle.dhPublic dA)
              braid := .keysSampled 1 (Tacenta.SessionUnitBraidT3.AuthOf q.auth) dk ekVector
                ⟨headerSource oracle.braidKem (Tacenta.SessionUnitBraidT3.AuthOf q.auth) ekSeed ekVector, 2⟩ }) := by
  -- the initiator's receipt of the reply, on the run
  obtain ⟨dSend, x, bytesR, sB'', ptA, s'', rngA', hagreeB, hx, hcallR, -, hcallA, hpt, hdr, hpend, -, hsess⟩ :=
    initiator_receives_reply rc crc trace dh kem view oracle braid triple aead dhCodec oracleOf codec
      codewordView hz80 hz32 hzKeys hgen hsizes hct hbound rcE crcE ourA bundleA expected rng0 rng1 s h q hq
      plaintext hroom rng htrace d1 d2 rest hdraws bytes s' rng' hcall contractsA agreementsA dA restA hdrawA rcB
      crcB contracts hpub hsym hcon haead hrt hoeq traceB oracleB oracleOfB braidB agreements ourB storeB hpublish
      hidentity hdistinct hkem rngB htraceB dB restB hdrawB ptB sB' storeB' rngB' hcallB ptR hroomR rngR hfreshB
  -- the key generation of the first send, on the same call
  obtain ⟨output, hcall', -, hcases⟩ := Tacenta.UnitLifecycleEstablishedEncrypt.established_encrypt_outcomes rc
    crc trace dh kem view oracle braid triple aead dhCodec oracleOf codec codewordView hz80 hz32 hzKeys hgen
    hct hbound rcE crcE ourA bundleA expected rng0 rng1 s h plaintext hroom rng htrace d1 d2 rest hdraws
  rw [hcall] at hcall'
  cases hcall'
  rcases hcases with ⟨-, hres, -⟩ | ⟨dk, ekSeed, ekVector, hkg, -⟩
  · cases hres
  subst hq
  -- the model session the receipt started from: its agreement emits the header's second chunk next
  have hmA := first_send_model_session_encoder dh view oracle q (sliceOf plaintext) d1 d2 rest
    (htrace.symm.trans hdraws) dk ekSeed ekVector hkg
  have hbraid : (Model.Lifecycle.encrypt view oracle (establishedModelOf dh q.session) (sliceOf plaintext)).session.braid =
      .keysSampled 1 (Tacenta.SessionUnitBraidT3.AuthOf q.auth) dk ekVector
        ⟨headerSource oracle.braidKem (Tacenta.SessionUnitBraidT3.AuthOf q.auth) ekSeed ekVector, 1⟩ := by
    rw [hmA]
  have hadA : (Model.Lifecycle.encrypt view oracle (establishedModelOf dh q.session)
      (sliceOf plaintext)).session.identityAd = vecOf q.identityAd := by
    rw [hmA]; rfl
  -- the model's second send: one outcome
  have hM := second_model_step view { oracle with draws := restA }
    (Model.Lifecycle.encrypt view oracle (establishedModelOf dh q.session) (sliceOf plaintext)).session
    (arrayOf q.rootKey) (arrayOf q.sparseRoot) (arrayOf q.sparseSend) (arrayOf q.sparseReceive) dSend x
    (oracleB.dhPublic dB) (oracle.dhPublic dA) dA _ _ _ _ hbraid (sliceOf ptS)
  rw [hadA, secondFrame_with_draws] at hM
  have hdraw : Model.Lifecycle.braidSendNeedsDraw
      (replyReceiptSession
        (Model.Lifecycle.encrypt view oracle (establishedModelOf dh q.session) (sliceOf plaintext)).session
        (arrayOf q.rootKey) (arrayOf q.sparseRoot) (arrayOf q.sparseSend) (arrayOf q.sparseReceive) dSend x
        (oracleB.dhPublic dB) (oracle.dhPublic dA) dA).braid = false := by
    simp only [replyReceiptSession, hbraid]; rfl
  refine ⟨dSend, x, bytesR, sB'', ptA, s'', rngA', dk, ekSeed, ekVector, hkg, hagreeB, hx, hcallR, hcallA, hpt,
    hdr, hpend, hsess, hdraw, hM, ?_⟩
  intro hinv hc
  -- the encrypt refinement at `s''`, at the initiator's oracle with the source's draws
  obtain ⟨output, hcallS, hstep⟩ := initiator_second_send_refines rc crc trace dh kem view
    { oracle with draws := trace rngA' } braid triple aead dhCodec (oracleOf_with_draws oracleOf _) codec
    codewordView hz80 hz32 hzKeys contractsA.braid.ct1Len
    (Model.Lifecycle.encrypt view oracle (establishedModelOf dh q.session) (sliceOf plaintext)).session
    (arrayOf q.rootKey) (arrayOf q.sparseRoot) (arrayOf q.sparseSend) (arrayOf q.sparseReceive) dSend x
    (oracleB.dhPublic dB) (oracle.dhPublic dA) dA _ _ _ _ hbraid (by simp) s'' hsess hinv hc ptS hroomS rngA' rfl
  rw [hdr, hM] at hstep
  obtain ⟨res, s''', rngS'⟩ := output
  have hres := hstep.result
  have hsess3 := hstep.session
  simp only at hres hsess3 hcallS
  cases res with
  | Err err => exact hres.elim
  | Ok bytes2 =>
    -- the walk of the call: the agreement's send took no draw
    obtain ⟨m, ep, o, b, hsendB, _sparse, _cand, _hdr, _mk, -, hs'''⟩ :=
      Tacenta.UnitLifecycleEstablishedEncrypt.encrypt_ok_parts rc crc s'' ptS rngA' bytes2 s''' rngS' hcallS
    have hb := hsess.braid
    simp only [replyReceiptSession, hbraid] at hb
    obtain ⟨epoch, auth, kp, encoder, hst, -⟩ :=
      Tacenta.UnitLifecycleEstablishedEncrypt.state_keysSampled_of_refines hb
    obtain ⟨hr, -⟩ := braid_send_keysSampled rc crc s''.braid epoch auth kp encoder hst rngA' _ rngS' hsendB
    subst hr
    refine ⟨bytes2, s''', hcallS, ?_, ?_, ?_, hsess3⟩
    · rw [hs''']
    · rw [hs''']; exact hpend
    · -- the bytes: the model's frame, closed by rewriting so that a wrong key or chunk fails fast
      simp only [Tacenta.UnitLifecycleT3.ResultRefines, Model.Braid.Encoder.nextChunk] at hres
      rw [hres]

end Comp

end Tacenta.UnitLifecycleInitiatorSecondSend

/-! ## Pins

The constants each result depends on, and the statement of each result and definition, held by the
build.  `attest.py` requires every one of them (`REQUIRED_PINS`, `REQUIRED_STATEMENT_PINS`,
`REQUIRED_PRINT_FORM`). -/

/--
info: 'Tacenta.UnitLifecycleInitiatorSecondSend.send_output_none_of_no_draw' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleInitiatorSecondSend.send_output_none_of_no_draw

/--
info: 'Tacenta.UnitLifecycleInitiatorSecondSend.sparseOutput_none_of_no_draw' depends on axioms: [propext,
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
#print axioms Tacenta.UnitLifecycleInitiatorSecondSend.sparseOutput_none_of_no_draw

/--
info: 'Tacenta.UnitLifecycleInitiatorSecondSend.encryptProviders_of_invariant' depends on axioms: [propext,
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
#print axioms Tacenta.UnitLifecycleInitiatorSecondSend.encryptProviders_of_invariant

/--
info: 'Tacenta.UnitLifecycleInitiatorSecondSend.braid_send_keysSampled' depends on axioms: [propext,
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
#print axioms Tacenta.UnitLifecycleInitiatorSecondSend.braid_send_keysSampled

/--
info: 'Tacenta.UnitLifecycleInitiatorSecondSend.braidSendTraceCounted_of_keysSampled' depends on axioms: [propext,
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
#print axioms Tacenta.UnitLifecycleInitiatorSecondSend.braidSendTraceCounted_of_keysSampled

/--
info: 'Tacenta.UnitLifecycleInitiatorSecondSend.second_send_key' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleInitiatorSecondSend.second_send_key

/--
info: 'Tacenta.UnitLifecycleInitiatorSecondSend.secondFrame_with_draws' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleInitiatorSecondSend.secondFrame_with_draws

/--
info: 'Tacenta.UnitLifecycleInitiatorSecondSend.second_model_step' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleInitiatorSecondSend.second_model_step

/--
info: 'Tacenta.UnitLifecycleInitiatorSecondSend.initiator_second_send_refines' depends on axioms: [propext,
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
#print axioms Tacenta.UnitLifecycleInitiatorSecondSend.initiator_second_send_refines

/--
info: 'Tacenta.UnitLifecycleInitiatorSecondSend.first_send_model_session_encoder' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_kdf.hkdf_sha256,
 tacenta_kem.EncapsState,
 tacenta_kem.IncrementalKeyPair,
 zeroize.Zeroizing,
 rand_core_1.error.Error,
 tacenta_boundary.dh.PrivateKey,
 tacenta_boundary.dh.PublicKeyBytes,
 tacenta_boundary.dh.is_prime_order_public,
 tacenta_boundary.kem.encapsulate,
 tacenta_boundary.xeddsa.verify,
 zeroize.Zeroizing.new,
 Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_boundary.dh.PrivateKey.agree,
 tacenta_boundary.dh.PrivateKey.from_bytes,
 tacenta_boundary.dh.PrivateKey.public_key,
 tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 zeroize.Zeroize.Blanket.zeroize,
 zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleInitiatorSecondSend.first_send_model_session_encoder

/--
info: 'Tacenta.UnitLifecycleInitiatorSecondSend.initiator_second_send_after_reply' depends on axioms: [propext,
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
#print axioms Tacenta.UnitLifecycleInitiatorSecondSend.initiator_second_send_after_reply

/--
info: Tacenta.UnitLifecycleInitiatorSecondSend.send_output_none_of_no_draw : ∀ (K : Model.Braid.Kem) (rand : ℕ)
  (st : Model.Braid.BraidState),
  Model.Lifecycle.braidSendNeedsDraw st = false → (Model.Braid.send K rand st).2.2.1 = none
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleInitiatorSecondSend.send_output_none_of_no_draw

/--
info: @Tacenta.UnitLifecycleInitiatorSecondSend.sparseOutput_none_of_no_draw : ∀ {R : Type} {rc : rand_core_1.RngCore R}
  {crc : rand_core_1.CryptoRng R} {trace : R → List Model.Lifecycle.Key} {dh : Tacenta.UnitLifecycleT3.DhView}
  {K : Model.Braid.Kem} {oracle : Model.Lifecycle.Oracle} {real : lifecycle.Session} {model : Model.Lifecycle.Session}
  {rng : R} {realMessage : tacenta_braid.Msg} {realEpoch : U64} {realOutput : Option tacenta_braid.Output}
  {realBraidNext : tacenta_braid.Braid} {rngNext : R} {sparseOutput : Option tacenta_spqr.Output},
  Model.Lifecycle.braidSendNeedsDraw model.braid = false →
    Tacenta.UnitLifecycleT3.RealSparseConversion realOutput sparseOutput →
      Nonempty
          (Tacenta.UnitLifecycleT3.GeneratedBraidSuccessEvidence rc crc trace dh K oracle real model rng realMessage
            realEpoch realOutput realBraidNext rngNext) →
        sparseOutput = none
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleInitiatorSecondSend.sparseOutput_none_of_no_draw

/--
info: @Tacenta.UnitLifecycleInitiatorSecondSend.encryptProviders_of_invariant : ∀ [Tacenta.SessionUnitT1.DerivedKeysModel]
  {R : Type} {rc : rand_core_1.RngCore R} {crc : rand_core_1.CryptoRng R} {trace : R → List Model.Lifecycle.Key}
  (dh : Tacenta.UnitLifecycleT3.DhView) (kem : Tacenta.UnitLifecycleT3.KemView) (K : Model.Braid.Kem)
  (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle) (real : lifecycle.Session)
  (model : Model.Lifecycle.Session),
  real.invariant = ok true →
    Tacenta.UnitLifecycleT3.SessionRefines dh K real model →
      Tacenta.UnitLifecycleDecryptRunBounds.CounterHeadroom real →
        Model.Lifecycle.braidSendNeedsDraw model.braid = false →
          ∀ (plaintext : Slice U8) (rng : R),
            Nonempty
              (Tacenta.UnitLifecycleT3.EncryptNonterminalRouteProviders rc crc trace dh kem K view oracle real model
                plaintext rng)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleInitiatorSecondSend.encryptProviders_of_invariant

/--
info: @Tacenta.UnitLifecycleInitiatorSecondSend.braid_send_keysSampled : ∀ {R : Type} (rc : rand_core_1.RngCore R)
  (crc : rand_core_1.CryptoRng R) (b : tacenta_braid.Braid) (epoch : U64) (auth : tacenta_braid.Auth)
  (kp : tacenta_kem.IncrementalKeyPair) (enc : tacenta_erasure.Encoder),
  b.state = tacenta_braid.State.KeysSampled epoch auth kp enc →
    ∀ (rng : R) (x : tacenta_braid.Msg × U64 × Option tacenta_braid.Output × tacenta_braid.Braid) (rngN : R),
      tacenta_braid.Braid.send rc crc b rng = ok (x, rngN) →
        rngN = rng ∧
          x.2.2.1 = none ∧
            ∃ kp' chunk enc',
              tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone kp = ok kp' ∧
                enc.next_chunk = ok (chunk, enc') ∧
                  tacenta_braid.Msg.with epoch tacenta_braid.MsgType.Hdr chunk = ok x.1 ∧
                    x.2.2.2 = { state := tacenta_braid.State.KeysSampled epoch auth kp' enc' }
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleInitiatorSecondSend.braid_send_keysSampled

/--
info: @Tacenta.UnitLifecycleInitiatorSecondSend.braidSendTraceCounted_of_keysSampled : ∀ {R : Type}
  {rc : rand_core_1.RngCore R} {crc : rand_core_1.CryptoRng R} {trace : R → List Model.Lifecycle.Key}
  {K : Model.Braid.Kem} {oracle : Model.Lifecycle.Oracle} {real : lifecycle.Session} {model : Model.Lifecycle.Session}
  {rng : R},
  oracle.braidKem = K →
    ∀ (epoch : U64) (auth : tacenta_braid.Auth) (kp : tacenta_kem.IncrementalKeyPair) (enc : tacenta_erasure.Encoder),
      real.braid.state = tacenta_braid.State.KeysSampled epoch auth kp enc →
        ∀ (e : ℕ) (a : Model.Braid.Auth) (dk ekVector : Model.Braid.Bytes) (encM : Model.Braid.Encoder),
          model.braid = Model.Braid.BraidState.keysSampled e a dk ekVector encM →
            encM.next < 65536 →
              Tacenta.UnitLifecycleT3.BraidSendTraceAgreementCounted rc crc trace K oracle real model rng
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleInitiatorSecondSend.braidSendTraceCounted_of_keysSampled

/--
info: Tacenta.UnitLifecycleInitiatorSecondSend.second_send_key : ∀ (rkA prk k1 k2 dSend x newPub candPub : Model.State.Key),
  Model.Triple.sendDetailed
      (Tacenta.UnitLifecycleResponderReplyReceipt.initiatorAfterReply rkA prk k1 k2 dSend x newPub candPub) 0 none =
    Except.ok
      (Tacenta.UnitLifecycleInitiatorSecondSend.initiatorAfterSecond rkA prk k1 k2 dSend x newPub candPub,
        Tacenta.UnitLifecycleInitiatorSecondSend.secondHeader candPub,
        Tacenta.UnitLifecycleInitiatorSecondSend.secondKey rkA k1 dSend x)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleInitiatorSecondSend.second_send_key

/--
info: Tacenta.UnitLifecycleInitiatorSecondSend.secondFrame_with_draws : ∀ (view : Model.Lifecycle.CodewordView)
  (oracle : Model.Lifecycle.Oracle) (draws : List Model.State.Key) (ad : Model.Lifecycle.Bytes)
  (braid : Model.Braid.BraidState) (candPub messageKey : Model.State.Key) (chunk : Model.Braid.Chunk)
  (plaintext : Model.Lifecycle.Bytes),
  Tacenta.UnitLifecycleInitiatorSecondSend.secondFrame view
      { draws := draws, braidKem := oracle.braidKem, dhPublic := oracle.dhPublic, dhAgree := oracle.dhAgree,
        identityValid := oracle.identityValid, aeadSeal := oracle.aeadSeal, aeadOpen := oracle.aeadOpen,
        kemValid := oracle.kemValid, kemEncaps := oracle.kemEncaps, kemDecaps := oracle.kemDecaps,
        sigVerify := oracle.sigVerify, sigSign := oracle.sigSign }
      ad braid candPub messageKey chunk plaintext =
    Tacenta.UnitLifecycleInitiatorSecondSend.secondFrame view oracle ad braid candPub messageKey chunk plaintext
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleInitiatorSecondSend.secondFrame_with_draws

/--
info: Tacenta.UnitLifecycleInitiatorSecondSend.second_model_step : ∀ (view : Model.Lifecycle.CodewordView)
  (oracle : Model.Lifecycle.Oracle) (mA : Model.Lifecycle.Session)
  (rkA prk k1 k2 dSend x newPub candPub c : Model.State.Key) (a : Model.Braid.Auth) (dk ekVector : Model.Braid.Bytes)
  (enc : Model.Braid.Encoder),
  mA.braid = Model.Braid.BraidState.keysSampled 1 a dk ekVector enc →
    ∀ (pt : Model.Lifecycle.Bytes),
      Model.Lifecycle.encrypt view oracle
          (Tacenta.UnitLifecycleResponderReplyReceipt.replyReceiptSession mA rkA prk k1 k2 dSend x newPub candPub c)
          pt =
        {
          session :=
            have __src :=
              Tacenta.UnitLifecycleResponderReplyReceipt.replyReceiptSession mA rkA prk k1 k2 dSend x newPub candPub c;
            {
              triple :=
                Tacenta.UnitLifecycleInitiatorSecondSend.initiatorAfterSecond rkA prk k1 k2 dSend x newPub candPub,
              braid := Model.Braid.BraidState.keysSampled 1 a dk ekVector enc.nextChunk.2,
              ratchetPrivate := __src.ratchetPrivate, identityAd := __src.identityAd,
              ourIdentityPublic := __src.ourIdentityPublic, peerIdentityPublic := __src.peerIdentityPublic,
              pendingInitial := __src.pendingInitial, establishedEphemeral := __src.establishedEphemeral },
          result :=
            Except.ok
              (Tacenta.UnitLifecycleInitiatorSecondSend.secondFrame view oracle mA.identityAd
                (Model.Braid.BraidState.keysSampled 1 a dk ekVector enc) candPub
                (Tacenta.UnitLifecycleInitiatorSecondSend.secondKey rkA k1 dSend x) enc.nextChunk.1 pt),
          oracle := oracle }
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleInitiatorSecondSend.second_model_step

/--
info: @Tacenta.UnitLifecycleInitiatorSecondSend.initiator_second_send_refines : ∀ [Tacenta.SessionUnitT1.DerivedKeysModel]
  {R : Type} (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R) (trace : R → List Model.Lifecycle.Key)
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
                        ∀ (mA : Model.Lifecycle.Session) (rkA prk k1 k2 dSend x newPub candPub c : Model.State.Key)
                          (a : Model.Braid.Auth) (dk ekVector : Model.Braid.Bytes) (enc : Model.Braid.Encoder),
                          mA.braid = Model.Braid.BraidState.keysSampled 1 a dk ekVector enc →
                            enc.next < 65536 →
                              ∀ (s'' : lifecycle.Session),
                                Tacenta.UnitLifecycleT3.SessionRefines dh oracle.braidKem s''
                                    (Tacenta.UnitLifecycleResponderReplyReceipt.replyReceiptSession mA rkA prk k1 k2
                                      dSend x newPub candPub c) →
                                  s''.invariant = ok true →
                                    Tacenta.UnitLifecycleDecryptRunBounds.CounterHeadroom s'' →
                                      ∀ (plaintext : Slice U8),
                                        102 + ((↑plaintext).length + 48) ≤ Usize.max →
                                          ∀ (rng : R),
                                            trace rng = oracle.draws →
                                              Tacenta.UnitLifecycleT3.PublicEncryptWitness rc crc trace dh
                                                oracle.braidKem view oracle s''
                                                (Tacenta.UnitLifecycleResponderReplyReceipt.replyReceiptSession mA rkA
                                                  prk k1 k2 dSend x newPub candPub c)
                                                plaintext rng
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleInitiatorSecondSend.initiator_second_send_refines

/--
info: @Tacenta.UnitLifecycleInitiatorSecondSend.first_send_model_session_encoder : ∀ {our : lifecycle.Identity}
  {bundle : lifecycle.PublishedBundle} {E : Type} {rcE : rand_core_1.RngCore E} {crcE : rand_core_1.CryptoRng E}
  (dh : Tacenta.UnitLifecycleT3.DhView) (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle)
  (q : Tacenta.UnitLifecycleResponderFirstFrame.InitiatorSecretParts rcE crcE our bundle)
  (plaintext : Model.Lifecycle.Bytes) (d1 d2 : Model.Lifecycle.Key) (rest : List Model.Lifecycle.Key),
  oracle.draws = d1 :: d2 :: rest →
    ∀ (dk ekSeed ekVector : Model.Braid.Bytes),
      oracle.braidKem.keyGen (Model.Lifecycle.braidRandomness (d1 ++ d2)) = some (dk, ekSeed, ekVector) →
        (Model.Lifecycle.encrypt view oracle
              (Tacenta.UnitLifecycleEstablishInitiatorShape.establishedModelOf dh q.session) plaintext).session =
          have __src := Tacenta.UnitLifecycleEstablishInitiatorShape.establishedModelOf dh q.session;
          {
            triple :=
              Tacenta.UnitLifecycleResponderFirstReceipt.senderAfterFirst
                (Tacenta.UnitLifecycleT3.arrayOf q.ratchetBytes) (Tacenta.UnitLifecycleT3.arrayOf q.peerRatchetBytes)
                (Tacenta.UnitLifecycleT3.arrayOf q.rootKey) (Tacenta.UnitLifecycleT3.arrayOf q.sendChain)
                (Tacenta.UnitLifecycleT3.arrayOf q.sparseRoot) (Tacenta.UnitLifecycleT3.arrayOf q.sparseSend)
                (Tacenta.UnitLifecycleT3.arrayOf q.sparseReceive),
            braid :=
              Model.Braid.BraidState.keysSampled 1 (Tacenta.SessionUnitBraidT3.AuthOf q.auth) dk ekVector
                {
                  source :=
                    Tacenta.UnitLifecycleResponderFirstReceipt.headerSource oracle.braidKem
                      (Tacenta.SessionUnitBraidT3.AuthOf q.auth) ekSeed ekVector,
                  next := 1 },
            ratchetPrivate := __src.ratchetPrivate, identityAd := __src.identityAd,
            ourIdentityPublic := __src.ourIdentityPublic, peerIdentityPublic := __src.peerIdentityPublic,
            pendingInitial := __src.pendingInitial, establishedEphemeral := __src.establishedEphemeral }
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleInitiatorSecondSend.first_send_model_session_encoder

/--
info: @Tacenta.UnitLifecycleInitiatorSecondSend.initiator_second_send_after_reply : ∀ [Tacenta.SessionUnitT1.DerivedKeysModel]
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
                                                      Tacenta.UnitLifecycleT1.DecryptRatchetContracts rc →
                                                        Tacenta.UnitLifecycleDecryptRatchetT3.DecryptRatchetAgreements
                                                            oracle.braidKem →
                                                          ∀ (dA : Model.Lifecycle.Key)
                                                            (restA : List Model.Lifecycle.Key),
                                                            trace rng' = dA :: restA →
                                                              ∀ (rcB : rand_core_1.RngCore F)
                                                                (crcB : rand_core_1.CryptoRng F), ⋯
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleInitiatorSecondSend.initiator_second_send_after_reply

/--
info: def Tacenta.UnitLifecycleInitiatorSecondSend.initiatorAfterSecond : Model.State.Key →
  Model.State.Key →
    Model.State.Key →
      Model.State.Key → Model.State.Key → Model.State.Key → Model.State.Key → Model.State.Key → Model.Triple.State :=
fun rkA prk k1 k2 dSend x newPub candPub =>
  {
    classical :=
      { dhsPub := candPub, dhrPub := some newPub,
        rk :=
          (Model.State.kdfRk (Model.State.kdfRk rkA dSend Model.State.LabelSet.tacenta).1 x
              Model.State.LabelSet.tacenta).1,
        cks :=
          some
            (Model.State.kdfCk
                (Model.State.kdfRk (Model.State.kdfRk rkA dSend Model.State.LabelSet.tacenta).1 x
                    Model.State.LabelSet.tacenta).2).1,
        ckr := some (Model.State.kdfCk (Model.State.kdfRk rkA dSend Model.State.LabelSet.tacenta).2).1, ns := 1,
        nr := 1, pn := 1, skipped := [], events := 1, labels := Model.State.LabelSet.tacenta },
    postQuantum :=
      { rk := prk, epoch := 0,
        chains :=
          [(0,
              { send := some { ck := (Model.SparseRatchet.kdfCk (Model.SparseRatchet.kdfCk k1 1).1 2).1, n := 2 },
                receive := some { ck := (Model.SparseRatchet.kdfCk k2 1).1, n := 1 } })],
        skipped := [], direction := Model.SparseRatchet.Direction.a2b } }
-/
#guard_msgs in
#print Tacenta.UnitLifecycleInitiatorSecondSend.initiatorAfterSecond

/--
info: def Tacenta.UnitLifecycleInitiatorSecondSend.secondHeader : Model.State.Key → Model.Triple.Header :=
fun candPub => { dr := { dh := candPub, pn := 1, n := 0 }, epoch := 0, pqN := 2 }
-/
#guard_msgs in
#print Tacenta.UnitLifecycleInitiatorSecondSend.secondHeader

/--
info: def Tacenta.UnitLifecycleInitiatorSecondSend.secondKey : Model.State.Key →
  Model.State.Key → Model.State.Key → Model.State.Key → Model.State.Key :=
fun rkA k1 dSend x =>
  Model.TripleRatchet.combine
    (Model.State.kdfCk
        (Model.State.kdfRk (Model.State.kdfRk rkA dSend Model.State.LabelSet.tacenta).1 x
            Model.State.LabelSet.tacenta).2).2
    (Model.SparseRatchet.kdfCk (Model.SparseRatchet.kdfCk k1 1).1 2).2
-/
#guard_msgs in
#print Tacenta.UnitLifecycleInitiatorSecondSend.secondKey

/--
info: def Tacenta.UnitLifecycleInitiatorSecondSend.secondComposite : Model.Lifecycle.CodewordView →
  Model.Braid.BraidState → Model.State.Key → Model.Braid.Chunk → Model.CompositeHeader.Composite :=
fun view braid candPub chunk =>
  { dh := candPub, pn := UInt32.ofNat 1, n := UInt32.ofNat 0, pqEpoch := UInt64.ofNat 0, pqN := UInt64.ofNat 2,
    agEpoch := UInt64.ofNat 1, agType := Model.CompositeHeader.AgreementType.hdr,
    agChunk := some (view.send braid chunk) }
-/
#guard_msgs in
#print Tacenta.UnitLifecycleInitiatorSecondSend.secondComposite

/--
info: def Tacenta.UnitLifecycleInitiatorSecondSend.secondFrame : Model.Lifecycle.CodewordView →
  Model.Lifecycle.Oracle →
    Model.Lifecycle.Bytes →
      Model.Braid.BraidState →
        Model.State.Key → Model.State.Key → Model.Braid.Chunk → Model.Lifecycle.Bytes → Model.Lifecycle.Bytes :=
fun view oracle ad braid candPub messageKey chunk plaintext =>
  Model.CompositeHeader.encodeMessage
    (Tacenta.UnitLifecycleInitiatorSecondSend.secondComposite view braid candPub chunk)
    (oracle.aeadSeal (Model.State.messageKeys messageKey Model.State.LabelSet.tacenta).1
      (Model.State.messageKeys messageKey Model.State.LabelSet.tacenta).2.1
      (Model.State.messageKeys messageKey Model.State.LabelSet.tacenta).2.2 plaintext
      (Model.Messages.concatAd ad
        (Model.CompositeHeader.encode
          (Tacenta.UnitLifecycleInitiatorSecondSend.secondComposite view braid candPub chunk))))
-/
#guard_msgs in
#print Tacenta.UnitLifecycleInitiatorSecondSend.secondFrame
