import Translation.UnitLifecycleReceivePreserve

/-!
# The reply again: the initiator's `Session::decrypt` of the responder's reply a second time, after its first receipt

`UnitLifecycleResponderReplyReceipt` shows that the initiator's public `Session::decrypt` of the responder's reply at
the session `s'` its first send left accepts it and returns a session `s''`, and `UnitLifecycleReceivePreserve` that
`s''` passes `Session::invariant` and meets the four counter ceilings.  A transport can deliver the same bytes twice.
This module takes that second delivery on the same run: the initiator's public `decrypt` of the reply's bytes at
`s''`.  The reply is a bare ratchet frame (no initial wrapper), so the call goes straight to the inner receive: the
agreement has not failed, the frame decodes, the session's ratchet key agrees with the reply's ratchet key, the
candidate key is drawn and agrees with it too, and the Triple's classical receive then refuses the frame as out of
order, because the reply's ratchet key is now the peer key the initiator holds, no stored key matches, and the frame's
number 0 is below the receive count 1.  The refusal has no durable effect: the session returned is `s''` itself (so it
still passes the invariant and meets the ceilings), and the source loses exactly one draw.  The code's step refines the
model's public `decrypt` step, which refuses `triple (classical outOfOrder)`, consumes the draw and leaves the model
session as it was.

## What is shown

* `reply_again_receive_outOfOrder`, `reply_again_with_eviction`, `reply_again_model_refused` (model only): the model
  Triple's receive of the reply's header at the initiator after the reply (`initiatorAfterReply`) refuses
  `outOfOrder` whatever the agreements and the sparse output; the session's receive with eviction refuses the same
  without evicting; and the model's public `decrypt` of the reply frame at `replyReceiptSession`, when the agreement is
  at `keysSampled`, the frame's ratchet key is 32 canonical bytes and both agreements with it return, consumes one draw,
  refuses `triple (classical outOfOrder)` and keeps the session, at every codeword view.
* `reply_key_agreement` (bridge, under `DhAgreeContributory`): every private key agrees with a public key the boundary
  returned, in a decrypt oracle.
* `reply_again_refused_of_invariant`: at every session that passes `Session::invariant`, meets `CounterHeadroom` and
  refines `replyReceiptSession` of a model session whose agreement is at `keysSampled`, under the decrypt boundary
  records, the view's codec relation, `DhPublicValid` and `DhAgreeContributory`, the translated `decrypt` of the reply
  frame from a source with a draw returns `Triple(Classical(OutOfOrder))`, the session itself and the source after
  that draw, and the model's step is the refusal above.  The invariant, the ceilings and the relation are its
  hypotheses.
* `initiator_repeated_reply_refused` (the composed statement): on the run of the initiator's first send, the
  responder's receipt and its reply, under the hypotheses of `initiator_receives_reply` (`hfreshB` among them) and a
  second source `rngA2` whose trace holds a draw `dA2`: the first receipt returns `Ok` of the responder's plaintext and
  `s''`, which passes `Session::invariant`, meets `CounterHeadroom` and refines `replyReceiptSession`; the model's
  `decrypt` of the same bytes there, at every view, with the oracle holding `dA2` first, refuses
  `triple (classical outOfOrder)`, consumes `dA2` and keeps the model session; and the translated `decrypt` of the same
  bytes at `s''` from `rngA2` returns `Triple(Classical(OutOfOrder))`, `s''` itself and a source whose trace is the
  rest after `dA2`.  The invariant and the ceilings come from `initiator_receives_reply_successor` on the same run, the
  reply's bytes and the relation from `initiator_receives_reply`, the model session the first send left from
  `first_send_model_session`, and the second delivery from `reply_again_refused_of_invariant`.
* `byteTrace_seed_two_extra`, `repeated_reply_refused_reachable` (non-vacuity, below).

## The laws and premises

No new law, and no new per-run premise beyond the second source's draw.  The composed statement takes the hypotheses
of `initiator_receives_reply`: its laws (`AeadRoundTrip`, `DhAgreeContributory`, `DhAgreeSymmetric`, `DhPublicValid`,
`DhPublicBytesRoundTrip`, `OptionEqU64Shape`, `KemCiphertextLenOf`, `KemCiphertextLenBound`, `KeyGenSeededFor`,
`KeyGenSizesOf`), its boundary records (the encrypt records and the oracle records at both parties' sources, the decrypt
records `DecryptRatchetContracts` and `DecryptRatchetAgreements` at the initiator's source, the responder's
`EstablishResponderContracts` and `DecryptRatchetAgreements`), `PrekeyIdsDistinct` and `FirstKemAgrees` of the store,
the zeroizing round trips, the run's trace equations and draws, the success equations of the establishment, the first
send and `establish_responder`, and the per-run premise `hfreshB` (the responder's fresh ratchet key is not the peer key
the initiator held).  `DhAgreeContributory` is used here once more: the ratchet key of `s''` and the second draw both
agree with the reply's ratchet key, without which the model and the code would refuse
`handshake nonContributoryAgreement` instead.  The second source's draw is a per-run premise, as the first's is: with no
draw left the model refuses `ceiling` and the code's draw is not described.  No premise names a width; the plaintext
bounds are those of the first send and the reply.

## Trust

Every result here rests on the kernel and opaque constants only, with no compiler-trust axiom (the pins below).  The
composed statement and the reach apply the encrypt and decrypt refinements through the theorems they call, whose nine
`native_decide` constants are kernel proofs since 2026-10-21.

## Non-vacuity

`repeated_reply_refused_reachable` exhibits every premise of `initiator_repeated_reply_refused` on one run at the real
constants, under the laws of `first_send_reply_receipt_reachable`, which `reply_receipt_laws_model` puts in one toy
interpretation (`InterpO.modelReply`, as recorded in `UnitLifecycleResponderReplyReceipt`).  The second delivery's
source there is the one the first receipt left: the initiator's source is a 64-byte seed followed by two runs of 32
bytes, of which the first send takes the seed, the first receipt the first run and the second delivery the second.

## What it does not show

* That the refusal consumes nothing: it consumes one draw of the source (the candidate key, drawn before the Triple's
  receive), as the model's step does; only the session is left as it was.
* A delivery of the reply again at any other point: after the initiator's second send, after the responder's second
  message, on a restored copy of the session, or when the first receipt refused (the stale arm, where `hfreshB` fails
  and the first receipt returns `s'`): only the delivery right after a first receipt that succeeded is taken.
* A frame that differs from the reply in its bytes (a tampered reply at `s''`; `UnitLifecycleTamperedReply` takes a
  tampered reply at `s'` only), and any other out-of-order delivery: a message that arrives after a later one of the same
  chain, delayed or dropped delivery, a receive that uses a stored skipped key.  Here the store is empty and the
  refusal is the one for a key already used.
* The arms an empty source or a refused agreement would give (`ceiling`, `handshake nonContributoryAgreement`): excluded
  by the draw premise and `DhAgreeContributory`.
* The responder's second reply, the initiator's second send, the header's later chunks and every step that runs a KEM:
  at `s''` the agreement is at `KeysSampled`, the reply carries a message of type `none`, and the call clones the
  agreement (which the decrypt records cover through `KemCloneAgrees`); no fact relating the two parties' KEMs is used.
* That `Session::invariant` is kept by refused calls in general: here the session returned is `s''` itself
  (`decrypt_err_leaves_state`), and its invariant and ceilings are those of the first receipt's successor.
* That `hfreshB` or the second draw holds of a run with an honest random source: they are premises, and no probability
  is claimed; a source with no state of its own, such as `OsRng`, is outside the statements about draws.
* That the real primitives meet the boundary records or the laws the run rests on; the one-time path in a run (the reach
  takes the last-resort path); the model's own `establishResponder` equality.
-/

open Aeneas Aeneas.Std Result
open tacenta_session_unit

namespace Tacenta.UnitLifecycleInitiatorRepeatedReply

open Tacenta.UnitLifecycleT3 (DhView DhCodecOf arrayOf vecOf sliceOf SessionRefines ResultRefines)
open Tacenta.UnitLifecycleResponderFirstReceipt (firstHeader firstKey)
open Tacenta.UnitLifecycleResponderReply (replyComposite replyFrame)
open Tacenta.UnitLifecycleResponderReplyReceipt (initiatorAfterReply replyReceiptSession replyFrame_messageType
  replyFrame_decodeDetailed)

/-! ## The model's step on the reply delivered again -/

section Model
open Model.State (Key)

/-- **The model Triple's receive of the reply's header again, at the initiator after the reply**: the header's ratchet
key `newPub` is the peer key the initiator now holds, no stored key matches (the store is empty), nothing is skipped,
and the header's number 0 is below the receive count 1, so the classical half refuses `outOfOrder`, whatever the
agreements, the candidate key and the sparse output.  Model only. -/
theorem reply_again_receive_outOfOrder (rkA prk k1 k2 dSend x newPub candPub dR dS np : Key)
    (out : Option Model.SparseRatchet.Output) :
    Model.Triple.receiveDetailed (initiatorAfterReply rkA prk k1 k2 dSend x newPub candPub) (firstHeader newPub)
        dR dS np out = .error (.classical .outOfOrder) := by
  simp [Model.Triple.receiveDetailed, Model.Ratchet.receiveDetailed, Model.Ratchet.trySkipped,
    Model.Ratchet.skipMessageKeysDetailed, Model.State.skipMessageKeys, initiatorAfterReply, firstHeader]

/-- The same through the session's receive with eviction: `outOfOrder` names no full store, so no eviction is
tried.  Model only. -/
theorem reply_again_with_eviction (rkA prk k1 k2 dSend x newPub candPub dR dS np : Key)
    (composite : Model.CompositeHeader.Composite) (out : Option Model.SparseRatchet.Output) :
    Model.Lifecycle.receiveWithEviction (initiatorAfterReply rkA prk k1 k2 dSend x newPub candPub) composite
      (firstHeader newPub) dR dS np out = .error (.classical .outOfOrder) := by
  unfold Model.Lifecycle.receiveWithEviction
  rw [reply_again_receive_outOfOrder]
  rfl

/-- **The model's public `decrypt` of the reply frame again, at the initiator's model session after the reply**
(`replyReceiptSession` of a model session whose agreement is at `keysSampled`): when the frame's ratchet key is 32
canonical bytes, the session's ratchet key agrees with it and the oracle's first draw `c` agrees with it too, the step
consumes `c`, refuses `triple (classical outOfOrder)` and leaves the session as it was, at every codeword view.  The
frame is a ratchet message, so the dispatch passes it through; the agreement's receive at `keysSampled` of a message
of type `none` is computed and discarded with the refusal.  No other refusal (`agreementFailed`, `decode`, either
agreement, `ceiling`, another Triple refusal, `aead`) occurs under these premises.  Model only. -/
theorem reply_again_model_refused (view : Model.Lifecycle.CodewordView)
    (oracleA oracleB : Model.Lifecycle.Oracle) (mA : Model.Lifecycle.Session)
    (rkA prk k1 k2 dSend x newPub candPub c0 : Key) (e : Nat) (auth : Model.Braid.Auth)
    (dk ekVector : Model.Braid.Bytes) (enc : Model.Braid.Encoder)
    (hbraid : mA.braid = .keysSampled e auth dk ekVector enc)
    (mk : Key) (pt : Model.Lifecycle.Bytes)
    (hlen : newPub.length = 32) (hkey : Model.Messages.checkKey newPub = some ())
    (dR : Key)
    (hagree : oracleA.dhAgree (replyReceiptSession mA rkA prk k1 k2 dSend x newPub candPub c0).ratchetPrivate
      newPub = some dR)
    (c : Key) (rest : List Key) (hdraw : oracleA.draws = c :: rest)
    (dS : Key) (hcand : oracleA.dhAgree c newPub = some dS) :
    Model.Lifecycle.decrypt view oracleA (replyReceiptSession mA rkA prk k1 k2 dSend x newPub candPub c0)
        (replyFrame oracleB mA.identityAd newPub mk pt) =
      { session := replyReceiptSession mA rkA prk k1 k2 dSend x newPub candPub c0
        result := .error (.triple (.classical .outOfOrder))
        oracle := { oracleA with draws := rest } } := by
  set mR := replyReceiptSession mA rkA prk k1 k2 dSend x newPub candPub c0 with hmR
  have hbraidR : mR.braid = .keysSampled e auth dk ekVector enc := by rw [hmR]; exact hbraid
  have hadR : mR.identityAd = mA.identityAd := rfl
  have htripleR : mR.triple = initiatorAfterReply rkA prk k1 k2 dSend x newPub candPub := rfl
  have hdisp := Model.Lifecycle.dispatchDecrypt_passthrough oracleA mR
    (replyFrame oracleB mA.identityAd newPub mk pt) (by rw [replyFrame_messageType]; simp)
  have hdec := replyFrame_decodeDetailed oracleB mA.identityAd newPub mk pt hlen hkey
  have hhdr : Model.Lifecycle.tripleHeaderOf (replyComposite newPub) = firstHeader newPub := by
    simp [Model.Lifecycle.tripleHeaderOf, replyComposite, firstHeader]
  have hbr : Model.Braid.receive oracleA.braidKem mR.braid
      (Model.Lifecycle.braidMessageOf view mR.braid (replyComposite newPub)) = (e - 1, none, mR.braid) := by
    rw [hbraidR]
    simp [Model.Braid.receive, Model.Lifecycle.braidMessageOf, replyComposite, Model.Lifecycle.braidTypeOf,
      Model.Braid.BraidState.epoch]
  have hfail : Model.Lifecycle.agreementFailed mR = false := by
    simp [Model.Lifecycle.agreementFailed, hbraidR]
  have hdh : (replyComposite newPub).dh = newPub := rfl
  have hrand : Model.Lifecycle.random32 oracleA = some (c, { oracleA with draws := rest }) := by
    simp [Model.Lifecycle.random32, Model.Lifecycle.takeDraw, hdraw]
  have hrecv : Model.Lifecycle.receiveWithEviction mR.triple (replyComposite newPub) (firstHeader newPub) dR dS
      (oracleA.dhPublic c) (Model.Lifecycle.sparseOutputOf none) = .error (.classical .outOfOrder) := by
    rw [htripleR]; exact reply_again_with_eviction _ _ _ _ _ _ _ _ _ _ _ _ _
  unfold Model.Lifecycle.decrypt Model.Lifecycle.decryptRatchet
  rw [hdisp]
  dsimp only
  rw [hfail, if_neg (by simp), hdec]
  dsimp only
  rw [hbr, hdh, hagree]
  dsimp only
  rw [hrand]
  dsimp only
  rw [hcand]
  dsimp only
  rw [hhdr, hrecv]
  rfl

end Model


section Inner

open Tacenta.UnitLifecycleDecryptRatchetT3 (DecryptOracleOf DecryptRatchetAgreements)
open Tacenta.UnitLifecycleEstablishInitiatorShape (DhPublicValid)
open Tacenta.UnitLifecycleResponderFirstReceipt (DhAgreeContributory dhAgreeContributory_is)

/-! ## The code's step at any session related to the model's after the reply -/

/-- **Every private key agrees with a public key the boundary returned**, in a decrypt oracle, under
`DhAgreeContributory`, the oracle record's agreement clause and the view: for `pk` the public key of some `k`, the
oracle's agreement of any `k'` with `pk` returns. -/
theorem reply_key_agreement (hcon : DhAgreeContributory) {R : Type} {rc : rand_core_1.RngCore R}
    {crc : rand_core_1.CryptoRng R} {dh : DhView} {trace : R → List Model.Lifecycle.Key}
    {oracle : Model.Lifecycle.Oracle} (oracleOf : DecryptOracleOf rc crc dh trace oracle)
    (k : tacenta_boundary.dh.PrivateKey) (pk : tacenta_boundary.dh.PublicKeyBytes)
    (hpk : tacenta_boundary.dh.PrivateKey.public_key k = ok pk) (k' : tacenta_boundary.dh.PrivateKey) :
    ∃ y, oracle.dhAgree (dh.privateKey k') (dh.publicKey pk) = some y := by
  obtain ⟨res, hres, hmap⟩ := oracleOf.dhAgree k' pk
  obtain ⟨y, hy⟩ := (dhAgreeContributory_is.mp hcon) k' k pk hpk
  rw [hy] at hres
  cases hres
  exact ⟨arrayOf y, by rw [← hmap]; rfl⟩

/-- **The reply frame again, at every session that passes the invariant, meets the ceilings and refines the
initiator's model session after the reply.**  For a session `sA` with `Session::invariant sA = ok true`,
`CounterHeadroom sA` and `SessionRefines` to `replyReceiptSession mA … (dh.publicKey pk) …` where `mA`'s agreement is
at `keysSampled` and `pk` is the public key the boundary returned for some private key, under the decrypt boundary
records (`DecryptOracleOf`, `DecryptRatchetContracts`, `DecryptRatchetAgreements`), the view's codec relation and the
laws `DhPublicValid` and `DhAgreeContributory`, and for bytes `msg` that are the reply frame on `pk` (any message key,
any plaintext, sealed by any oracle, with `mA`'s associated data) and a source `rng` whose trace is the oracle's draws
and holds a draw `c`: the model's public `decrypt` of `msg` at that model session, at every view, consumes `c`,
refuses `triple (classical outOfOrder)` and keeps the session (`reply_again_model_refused`), and the translated
`decrypt` of `msg` at `sA` from `rng` returns `Triple(Classical(OutOfOrder))`, `sA` itself and a source whose trace
is the rest after `c`.  The refinement of the call is `decrypt_refines_ratchet_frame_of_counter_headroom`; the
session is `sA` by `decrypt_err_leaves_state`.  The invariant, the ceilings and the relation are hypotheses here; the
run's headline derives them. -/
theorem reply_again_refused_of_invariant [Tacenta.SessionUnitT1.DerivedKeysModel] {R : Type}
    (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R)
    (trace : R → List Model.Lifecycle.Key) (dh : DhView)
    (oracle : Model.Lifecycle.Oracle) (oracleOf : DecryptOracleOf rc crc dh trace oracle)
    (codec : DhCodecOf dh) (contracts : Tacenta.UnitLifecycleT1.DecryptRatchetContracts rc)
    (agreements : DecryptRatchetAgreements oracle.braidKem)
    (hpub : DhPublicValid) (hcon : DhAgreeContributory)
    (mA : Model.Lifecycle.Session) (rkA prk k1 k2 dSend x candPub c0 : Model.Lifecycle.Key) (e : Nat)
    (auth : Model.Braid.Auth) (dk ekVector : Model.Braid.Bytes) (enc : Model.Braid.Encoder)
    (hbraid : mA.braid = .keysSampled e auth dk ekVector enc)
    (k : tacenta_boundary.dh.PrivateKey) (pk : tacenta_boundary.dh.PublicKeyBytes)
    (hpk : tacenta_boundary.dh.PrivateKey.public_key k = ok pk)
    (sA : lifecycle.Session) (hinv : lifecycle.Session.invariant sA = ok true)
    (hc : Tacenta.UnitLifecycleDecryptRunBounds.CounterHeadroom sA)
    (hrel : SessionRefines dh oracle.braidKem sA
      (replyReceiptSession mA rkA prk k1 k2 dSend x (dh.publicKey pk) candPub c0))
    (oracleB : Model.Lifecycle.Oracle) (mk : Model.Lifecycle.Key) (pt : Model.Lifecycle.Bytes)
    (msg : Slice U8) (hmsg : sliceOf msg = replyFrame oracleB mA.identityAd (dh.publicKey pk) mk pt)
    (rng : R) (htrace : trace rng = oracle.draws) (c : Model.Lifecycle.Key) (rest : List Model.Lifecycle.Key)
    (hdraw : trace rng = c :: rest) :
    (∀ view : Model.Lifecycle.CodewordView,
      Model.Lifecycle.decrypt view oracle
          (replyReceiptSession mA rkA prk k1 k2 dSend x (dh.publicKey pk) candPub c0) (sliceOf msg) =
        { session := replyReceiptSession mA rkA prk k1 k2 dSend x (dh.publicKey pk) candPub c0
          result := .error (.triple (.classical .outOfOrder))
          oracle := { oracle with draws := rest } }) ∧
    ∃ rng' : R,
      lifecycle.Session.decrypt rc crc sA msg rng =
        ok (core.result.Result.Err (lifecycle.Error.Triple (tacenta_triple.TripleError.Classical
          tacenta_ratchet.RatchetError.OutOfOrder)), sA, rng') ∧
      trace rng' = rest := by
  set mR := replyReceiptSession mA rkA prk k1 k2 dSend x (dh.publicKey pk) candPub c0 with hmR
  have hbraidR : mR.braid = .keysSampled e auth dk ekVector enc := by rw [hmR]; exact hbraid
  -- the reply's ratchet key: 32 canonical bytes
  obtain ⟨b, -, hcan, hbv⟩ := Tacenta.UnitLifecycleResponderFirstFrame.view_of_public hpub codec hpk
  have hlen : (dh.publicKey pk).length = 32 := by rw [hbv]; simp [arrayOf]
  have hkey : Model.Messages.checkKey (dh.publicKey pk) = some () := by
    rw [hbv]
    simp [Model.Messages.checkKey, Tacenta.UnitLifecycleResponderFirstFrame.canonicalKey_arrayOf _ hcan]
  -- the two agreements the model's step reaches
  obtain ⟨dR, hdR⟩ := reply_key_agreement hcon oracleOf k pk hpk sA.ratchet_private
  rw [hrel.ratchetPrivate] at hdR
  have hdrO : oracle.draws = c :: rest := htrace.symm.trans hdraw
  obtain ⟨dS, hdS⟩ := Tacenta.UnitLifecycleResponderReplyReceipt.initiator_candidate_agreement hcon codec oracleOf
    rng c rest hdraw k pk hpk
  -- the model's step on the frame again, at every view
  refine ⟨fun view => ?_, ?_⟩
  · rw [hmsg]
    exact reply_again_model_refused view oracle oracleB mA rkA prk k1 k2 dSend x (dh.publicKey pk) candPub c0 e
      auth dk ekVector enc hbraid mk pt hlen hkey dR hdR c rest hdrO dS hdS
  -- the same at the view the run inputs below use
  have hMw := reply_again_model_refused Tacenta.UnitLifecycleRepair.witnessView oracle oracleB mA rkA prk k1 k2
    dSend x (dh.publicKey pk) candPub c0 e auth dk ekVector enc hbraid mk pt hlen hkey dR hdR c rest hdrO dS hdS
  rw [← hmsg, ← hmR] at hMw
  -- the run inputs: the reply carries no agreement chunk, and the agreement is at `KeysSampled`
  have hdec := replyFrame_decodeDetailed oracleB mA.identityAd (dh.publicKey pk) mk pt hlen hkey
  have inputs : Tacenta.UnitLifecycleDecryptRunBounds.DecryptRatchetRunInputs
      Tacenta.UnitLifecycleRepair.witnessView oracle trace sA mR msg rng := by
    refine ⟨?_, ?_, ⟨c, rest, hdraw⟩⟩
    · intro rcomp mcomp ct hd hcr
      rw [hmsg, hdec] at hd
      simp only [Except.ok.injEq, Prod.mk.injEq] at hd
      obtain ⟨rfl, -⟩ := hd
      have hag := hcr.agChunk
      unfold Tacenta.UnitLifecycleT3.IncomingChunkRefines
      simp only [replyComposite] at hag ⊢
      rcases hrc : rcomp.ag_chunk with _ | rch
      · trivial
      · rw [hrc] at hag; exact hag.elim
    · intro mc ct _
      unfold Tacenta.SessionUnitBraidT3.HonestChunk
      intro m _ _
      rw [hbraidR]
      split <;> trivial
  have hframe : Model.Lifecycle.messageType (sliceOf msg) ≠ some .initial := by
    rw [hmsg, replyFrame_messageType]; simp
  obtain ⟨output, hcall, hstep⟩ :=
    Tacenta.UnitLifecycleDecryptT3.decrypt_refines_ratchet_frame_of_counter_headroom rc crc trace dh
      Tacenta.UnitLifecycleRepair.witnessView oracle oracleOf codec contracts agreements sA mR msg rng hframe hinv
      hrel hc htrace inputs
  have hres := hstep.result
  have hdr := hstep.draws
  rw [hMw] at hres hdr
  obtain ⟨res, sA2, rng'⟩ := output
  have he : res = core.result.Result.Err (lifecycle.Error.Triple (tacenta_triple.TripleError.Classical
      tacenta_ratchet.RatchetError.OutOfOrder)) := by
    cases res with
    | Ok v => simp [ResultRefines] at hres
    | Err e =>
      simp only [ResultRefines] at hres
      have h' : Tacenta.UnitLifecycleT3.refusalOf e = Tacenta.UnitLifecycleT3.refusalOf
          (lifecycle.Error.Triple (tacenta_triple.TripleError.Classical tacenta_ratchet.RatchetError.OutOfOrder)) :=
        hres
      rw [Tacenta.UnitLifecycleT3.refusalOf_injective h']
  -- the code's refusal is the model's, and the session it returns is the one it was given
  rw [he] at hcall
  have hs := Tacenta.UnitLifecycleAtomicity.decrypt_err_leaves_state rc crc sA msg rng _ sA2 rng' hcall
  rw [hs] at hcall
  exact ⟨rng', hcall, hdr⟩

end Inner


/-! ## The second delivery on the run of the initiator's first send -/

section Run

open Tacenta.UnitLifecycleT3 (KemView vecOf sliceOf OracleOf BraidSendRefinementContracts
  TripleSendRefinementContracts CodewordViewSendOf ZeroizingRoundTrips)
open Tacenta.UnitLifecycleResponderFirstReceipt (DhAgreeContributory AeadRoundTrip)
open Tacenta.UnitLifecycleResponderFirstFrame (InitiatorSecretParts DhAgreeSymmetric PrekeyIdsDistinct
  FirstKemAgrees)
open Tacenta.UnitLifecycleDecryptRatchetT3 (DecryptOracleOf DecryptRatchetAgreements)
open Tacenta.UnitLifecycleEstablishInitiatorShape (DhPublicValid establishedModelOf)

/-- **The responder's reply, delivered to the initiator a second time after its first receipt, is refused with no
durable effect, on the run of the initiator's first send.**  Under the hypotheses of `initiator_receives_reply` (those
of `initiator_receives_reply_successor`; the per-run premise `hfreshB` among them) and one per-run premise more, a
source `rngA2` whose trace holds a draw `dA2`: the responder's `encrypt` at `sB'` returns `bytesR`; the initiator's
first `decrypt` of `bytesR` at `s'` from `rng'` returns `Ok ptA` (the bytes of `ptR`) and a session `s''` that passes
`Session::invariant`, meets `CounterHeadroom` and refines `replyReceiptSession` of the model session the first send
left; the model's public `decrypt` of the same bytes at that model session, at every view, with the oracle holding
`dA2` first, consumes `dA2`, refuses `triple (classical outOfOrder)` and leaves the model session as it was; and the
translated `decrypt` of the same bytes at `s''` from `rngA2` returns `Triple(Classical(OutOfOrder))`, `s''` itself (so
the session after the refusal is the one that passes the invariant and meets the ceilings) and a source whose trace is
the rest after `dA2`.  Derived on the run: the first receipt and its invariant and ceilings are
`initiator_receives_reply_successor`'s, the reply's bytes and the relation `initiator_receives_reply`'s (one call, as
`encrypt` and `decrypt` are functions), the model session the first send left is `first_send_model_session`'s at the
key generation `initiator_first_send_responder_replies` gives, and `reply_again_refused_of_invariant` takes the second
delivery.  `rngA2` is any source with a draw; the reach takes the one the first receipt left. -/
theorem initiator_repeated_reply_refused [Tacenta.SessionUnitT1.DerivedKeysModel] {R E F : Type}
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
    (rngA2 : R) (dA2 : Model.Lifecycle.Key) (restA2 : List Model.Lifecycle.Key)
    (hdrawA2 : trace rngA2 = dA2 :: restA2) :
    ∃ (dSend x : Model.Lifecycle.Key) (bytesR : alloc.vec.Vec Std.U8) (sB'' : lifecycle.Session)
      (ptA : alloc.vec.Vec Std.U8) (s'' : lifecycle.Session) (rngA' rngA3 : R),
      lifecycle.Session.encrypt rcB crcB sB' ptR rngR = ok (core.result.Result.Ok bytesR, sB'', rngR) ∧
      lifecycle.Session.decrypt rc crc s' (alloc.vec.Vec.deref bytesR) rng' =
        ok (core.result.Result.Ok ptA, s'', rngA') ∧
      ptA.val = ptR.val ∧
      lifecycle.Session.invariant s'' = ok true ∧
      Tacenta.UnitLifecycleDecryptRunBounds.CounterHeadroom s'' ∧
      SessionRefines dh oracle.braidKem s''
        (replyReceiptSession
          (Model.Lifecycle.encrypt view oracle (establishedModelOf dh s) (sliceOf plaintext)).session
          (arrayOf q.rootKey) (arrayOf q.sparseRoot) (arrayOf q.sparseSend) (arrayOf q.sparseReceive) dSend x
          (oracleB.dhPublic dB) (oracle.dhPublic dA) dA) ∧
      (∀ viewA : Model.Lifecycle.CodewordView,
        Model.Lifecycle.decrypt viewA { oracle with draws := dA2 :: restA2 }
            (replyReceiptSession
              (Model.Lifecycle.encrypt view oracle (establishedModelOf dh s) (sliceOf plaintext)).session
              (arrayOf q.rootKey) (arrayOf q.sparseRoot) (arrayOf q.sparseSend) (arrayOf q.sparseReceive) dSend x
              (oracleB.dhPublic dB) (oracle.dhPublic dA) dA) (vecOf bytesR) =
          { session := replyReceiptSession
              (Model.Lifecycle.encrypt view oracle (establishedModelOf dh s) (sliceOf plaintext)).session
              (arrayOf q.rootKey) (arrayOf q.sparseRoot) (arrayOf q.sparseSend) (arrayOf q.sparseReceive) dSend x
              (oracleB.dhPublic dB) (oracle.dhPublic dA) dA
            result := .error (.triple (.classical .outOfOrder))
            oracle := { oracle with draws := restA2 } }) ∧
      lifecycle.Session.decrypt rc crc s'' (alloc.vec.Vec.deref bytesR) rngA2 =
        ok (core.result.Result.Err (lifecycle.Error.Triple (tacenta_triple.TripleError.Classical
          tacenta_ratchet.RatchetError.OutOfOrder)), s'', rngA3) ∧
      trace rngA3 = restA2 := by
  -- the first receipt keeps the invariant and the ceilings (receive preservation, on the same run)
  obtain ⟨-, -, bytesR, sB'', ptA, s'', rngA', hcallR, hcallA, -, hinv, hc, -, -⟩ :=
    Tacenta.UnitLifecycleReceivePreserve.initiator_receives_reply_successor rc crc trace dh kem view oracle braid
      triple aead dhCodec oracleOf codec codewordView hz80 hz32 hzKeys hgen hsizes hct hbound rcE crcE ourA bundleA
      expected rng0 rng1 s h q hq plaintext hroom rng htrace d1 d2 rest hdraws bytes s' rng' hcall contractsA
      agreementsA dA restA hdrawA rcB crcB contracts hpub hsym hcon haead hrt hoeq traceB oracleB oracleOfB braidB
      agreements ourB storeB hpublish hidentity hdistinct hkem rngB htraceB dB restB hdrawB ptB sB' storeB' rngB'
      hcallB ptR hroomR rngR hfreshB
  -- the first receipt itself: the reply's bytes, the agreements and the relation after it
  obtain ⟨dSend, x, bytesR1, sB''1, ptA1, s''1, rngA'1, -, -, hcallR1, hbytes, hcallA1, hpt, -, -, -, hsess⟩ :=
    Tacenta.UnitLifecycleResponderReplyReceipt.initiator_receives_reply rc crc trace dh kem view oracle braid triple
      aead dhCodec oracleOf codec codewordView hz80 hz32 hzKeys hgen hsizes hct hbound rcE crcE ourA bundleA expected
      rng0 rng1 s h q hq plaintext hroom rng htrace d1 d2 rest hdraws bytes s' rng' hcall contractsA agreementsA dA
      restA hdrawA rcB crcB contracts hpub hsym hcon haead hrt hoeq traceB oracleB oracleOfB braidB agreements ourB
      storeB hpublish hidentity hdistinct hkem rngB htraceB dB restB hdrawB ptB sB' storeB' rngB' hcallB ptR hroomR
      rngR hfreshB
  -- the two are one run: `encrypt` and `decrypt` are functions
  rw [hcallR] at hcallR1
  simp only [ok.injEq, Prod.mk.injEq, core.result.Result.Ok.injEq] at hcallR1
  obtain ⟨rfl, rfl, -⟩ := hcallR1
  rw [hcallA] at hcallA1
  simp only [ok.injEq, Prod.mk.injEq, core.result.Result.Ok.injEq] at hcallA1
  obtain ⟨rfl, rfl, rfl⟩ := hcallA1
  -- the model session the first send left, at the key generation of its two draws
  obtain ⟨-, -, -, dk, ekSeed, ekVector, -, -, hkg, -⟩ :=
    Tacenta.UnitLifecycleResponderReply.initiator_first_send_responder_replies rc crc trace dh kem view oracle braid
      triple aead dhCodec oracleOf codec codewordView hz80 hz32 hzKeys hgen hsizes hct hbound rcE crcE ourA bundleA
      expected rng0 rng1 s h q hq plaintext hroom rng htrace d1 d2 rest hdraws bytes s' rng' hcall rcB crcB contracts
      hpub hsym hcon haead hrt hoeq traceB oracleB oracleOfB braidB agreements ourB storeB hpublish hidentity
      hdistinct hkem rngB htraceB dB restB hdrawB ptB sB' storeB' rngB' hcallB ptR hroomR rngR
  subst hq
  obtain ⟨encoder, hmA⟩ := Tacenta.UnitLifecycleResponderReplyReceipt.first_send_model_session dh view oracle q
    (sliceOf plaintext) d1 d2 rest (htrace.symm.trans hdraws) dk ekSeed ekVector hkg
  set mA := (Model.Lifecycle.encrypt view oracle (establishedModelOf dh q.session) (sliceOf plaintext)).session
    with hmAdef
  have hbraid : mA.braid = .keysSampled 1 (Tacenta.SessionUnitBraidT3.AuthOf q.auth) dk ekVector encoder := by
    rw [hmA]
  have hadA : mA.identityAd = vecOf q.identityAd := by rw [hmA]; rfl
  -- the reply's ratchet key is the public key of the responder's draw
  obtain ⟨-, k, pk, b, -, -, -, hpk, -, -, hpkb, hnew⟩ :=
    Tacenta.UnitLifecycleResponderReplyReceipt.fresh_public_of_draw hpub codec
      (DecryptOracleOf.of_oracleOf oracleOfB) rngB dB restB hdrawB
  have hpkey : oracleB.dhPublic dB = dh.publicKey pk := by rw [hnew, hpkb]
  -- the second delivery, from the second source
  let oracleA2 : Model.Lifecycle.Oracle := { oracle with draws := dA2 :: restA2 }
  have oracleOfA2 : DecryptOracleOf rc crc dh trace oracleA2 :=
    DecryptOracleOf.of_oracleOf (Tacenta.UnitLifecycleResponderReply.oracleOf_with_draws oracleOf _)
  have hmsg : sliceOf (alloc.vec.Vec.deref bytesR) =
      replyFrame oracleB mA.identityAd (dh.publicKey pk)
        (firstKey (Model.State.kdfRk (arrayOf q.rootKey) dSend .tacenta).2 (arrayOf q.sparseReceive))
        (sliceOf ptR) := by
    rw [hadA, ← hpkey]; exact hbytes
  rw [hpkey] at hsess
  obtain ⟨hM, rngA3, hcall2, hdr2⟩ := reply_again_refused_of_invariant rc crc trace dh oracleA2 oracleOfA2 codec
    contractsA agreementsA hpub hcon mA _ _ _ _ _ _ _ _ 1 _ dk ekVector encoder hbraid k pk hpk s'' hinv hc hsess
    oracleB _ _ _ hmsg rngA2 hdrawA2 dA2 restA2 hdrawA2
  refine ⟨dSend, x, bytesR, sB'', ptA, s'', rngA', rngA3, hcallR, hcallA, hpt, hinv, hc, ?_, ?_, hcall2, hdr2⟩
  · rw [hpkey]; exact hsess
  · intro viewA
    rw [hpkey]
    exact hM viewA

end Run


/-! ## The reach: one run, from `publish` to the refusal of the reply delivered again -/

section Reach

open Tacenta.UnitSatisfiabilityJoint (Interp Interp.real)
open Tacenta.UnitLifecycleIntegrationScreen (byteRng byteCrc byteTrace chunks32)
open Tacenta.UnitLifecycleResponderFirstFrame (FirstFrameSuccessShape PoolEntry reachStore reachBundle
  publish_reachStore reachStore_distinct reach_establishment heldKemPair zPool InitiatorSecretParts
  DhAgreeSymmetric FirstKemAgrees)
open Tacenta.UnitLifecycleResponderFirstReceipt (DhAgreeContributory AeadRoundTrip)
open Tacenta.UnitLifecycleDecryptRatchetT3 (DecryptOracleOf DecryptRatchetAgreements)
open Tacenta.UnitLifecycleEstablishInitiatorShape (DhPublicValid)
open Tacenta.UnitLifecycleResponderReply (oracleOf_with_draws)
open Tacenta.UnitLifecycleResponderReplyReceipt (DhPublicNotConstant dhPublicNotConstant_is two_draws_of_seed_extra
  byteTrace_one)

/-- A byte-stream state of a 64-byte seed followed by two runs of 32 bytes holds four draws: the seed's two halves,
then the two runs. -/
theorem byteTrace_seed_two_extra (seed e1 e2 : List Std.U8) (hseed : seed.length = 64) (h1 : e1.length = 32)
    (h2 : e2.length = 32) :
    byteTrace (seed ++ (e1 ++ e2)) =
      ((seed ++ (e1 ++ e2)).map Tacenta.SessionUnitBraidT3.u8).take 32 ::
        (((seed ++ (e1 ++ e2)).map Tacenta.SessionUnitBraidT3.u8).drop 32).take 32 ::
          e1.map Tacenta.SessionUnitBraidT3.u8 :: [e2.map Tacenta.SessionUnitBraidT3.u8] := by
  rw [Tacenta.UnitLifecycleEstablishedEncrypt.byteTrace_two _ (by simp [hseed])]
  have hd : (((seed ++ (e1 ++ e2)).map Tacenta.SessionUnitBraidT3.u8).drop 32).drop 32 =
      (e1 ++ e2).map Tacenta.SessionUnitBraidT3.u8 := by
    rw [List.drop_drop, List.map_append, List.drop_append_of_le_length (by simp [hseed])]
    simp [hseed]
  rw [hd, chunks32, if_pos (by simp [h1, h2])]
  have he1 : ((e1 ++ e2).map Tacenta.SessionUnitBraidT3.u8).take 32 = e1.map Tacenta.SessionUnitBraidT3.u8 := by
    rw [List.map_append, List.take_append_of_le_length (by simp [h1])]
    exact List.take_of_length_le (by simp [h1])
  have he2 : ((e1 ++ e2).map Tacenta.SessionUnitBraidT3.u8).drop 32 = e2.map Tacenta.SessionUnitBraidT3.u8 := by
    rw [List.map_append, List.drop_append_of_le_length (by simp [h1])]
    simp [h1]
  rw [he1, he2, chunks32, if_pos (by simp [h2]), chunks32, if_neg (by simp [h2])]
  simp [h2]

open Tacenta.UnitSatisfiabilityJoint (InitiatorAxiom ResponderAxiom) in
open Tacenta.UnitLifecycleEstablishedEncrypt (EstablishedEncryptHypotheses EncryptExtraLaws emptyPlaintext) in
/-- **The reach: one run from `publish` to the initiator's refusal of the reply delivered again.**  At the real
constants, under the laws of `first_send_reply_receipt_reachable` (all assumed; `DhPublicNotConstant` chooses the
responder's source), for every initiator identity, every 64-byte seed at whose bytes the model's key generation
answers, every two runs of 32 further bytes and every reply plaintext `ptR` of at most 4096 bytes: there is a run (the
initiator's source the seed followed by the two runs; the last-resort path) in which `establish_responder` on the
initiator's first-send bytes succeeds, the responder's `encrypt` of `ptR` returns `bytesR`, the initiator's `decrypt`
of `bytesR` from the source its first send left returns `ptR`, and the initiator's `decrypt` of the same `bytesR` at
the session that call returned, from the source that call left (the second run of 32 bytes), refuses
`Triple(Classical(OutOfOrder))` and returns that session.  It applies `initiator_repeated_reply_refused` to the run,
so every premise of that theorem holds on it. -/
theorem repeated_reply_refused_reachable (K : Model.Braid.Kem) (dh : DhView)
    (kem : Tacenta.UnitLifecycleT3.KemView) (L : Tacenta.UnitLifecycleDecryptScreen.DecryptJointLaws K dh)
    (A : Nonempty (InitiatorAxiom Interp.real byteRng))
    (S : Tacenta.UnitLifecycleEstablishInitiatorShape.InitiatorSuccessShape Interp.real byteRng byteCrc)
    (hpub : DhPublicValid) (hct : Tacenta.UnitLifecycleEstablishInitiatorShape.KemCiphertextLenOf)
    (X : EncryptExtraLaws K dh kem) (RA : Nonempty (ResponderAxiom Interp.real byteRng))
    (hsym : DhAgreeSymmetric) (hrt : Tacenta.UnitLifecycleSessionCodec.DhPublicBytesRoundTrip)
    (FS : FirstFrameSuccessShape Interp.real tacenta_boundary.kem.KeyPair.public_key
      @alloc.vec.Vec.is_empty)
    (hsizes : Tacenta.UnitLifecycleEstablishedEncrypt.KeyGenSizesOf K)
    (hcon : DhAgreeContributory) (haead : AeadRoundTrip) (hnc : DhPublicNotConstant)
    (ourA : lifecycle.Identity) (seed : List Std.U8) (hseed : seed.length = 64)
    (extra1 extra2 : List Std.U8) (h1 : extra1.length = 32) (h2 : extra2.length = 32)
    (hkg : K.keyGen (Model.Lifecycle.braidRandomness (seed.map Tacenta.SessionUnitBraidT3.u8)) ≠ none)
    (ptR : Slice Std.U8) (hptR : ptR.val.length ≤ 4096) :
    ∃ (oracle : Model.Lifecycle.Oracle) (bundle : lifecycle.PublishedBundle)
      (q : InitiatorSecretParts byteRng byteCrc ourA bundle) (bytes : alloc.vec.Vec Std.U8)
      (s' : lifecycle.Session) (rng' : List Std.U8) (ourB : lifecycle.Identity)
      (storeB : lifecycle.PrekeyStore) (seedB : List Std.U8) (sB' : lifecycle.Session) (ptB : alloc.vec.Vec Std.U8)
      (storeB' : lifecycle.PrekeyStore) (rngB' : List Std.U8) (bytesR : alloc.vec.Vec Std.U8)
      (sB'' : lifecycle.Session) (ptA : alloc.vec.Vec Std.U8) (s'' : lifecycle.Session)
      (rngA' rngA3 : List Std.U8),
      oracle.braidKem = K ∧
      lifecycle.Session.encrypt byteRng byteCrc q.session emptyPlaintext (seed ++ (extra1 ++ extra2)) =
        ok (core.result.Result.Ok bytes, s', rng') ∧
      lifecycle.PrekeyStore.publish storeB = ok bundle ∧
      lifecycle.establish_responder byteRng byteCrc ourB storeB (alloc.vec.Vec.deref bytes) seedB =
        ok (core.result.Result.Ok (sB', ptB), storeB', rngB') ∧
      lifecycle.Session.encrypt byteRng byteCrc sB' ptR rngB' =
        ok (core.result.Result.Ok bytesR, sB'', rngB') ∧
      lifecycle.Session.decrypt byteRng byteCrc s' (alloc.vec.Vec.deref bytesR) rng' =
        ok (core.result.Result.Ok ptA, s'', rngA') ∧
      ptA.val = ptR.val ∧
      lifecycle.Session.decrypt byteRng byteCrc s'' (alloc.vec.Vec.deref bytesR) rngA' =
        ok (core.result.Result.Err (lifecycle.Error.Triple (tacenta_triple.TripleError.Classical
          tacenta_ratchet.RatchetError.OutOfOrder)), s'', rngA3) := by
  -- the run's keys and KEM pair
  obtain ⟨sb, kB, pkb, a, hkB, hpkb, ha, hcan, hprime, heq, hsig, hag⟩ := FS.key
  obtain ⟨kp, kemPk, stream, ct, ss, rest, hkp, hlen, henc, hdec⟩ := FS.kem
  obtain ⟨z, hz⟩ := FS.pool
  have hkB' : tacenta_boundary.dh.PrivateKey.from_bytes sb = ok kB := hkB
  have hpkb' : tacenta_boundary.dh.PrivateKey.public_key kB = ok pkb := hpkb
  have ha' : tacenta_boundary.dh.PublicKeyBytes.as_bytes pkb = ok a := ha
  have hprime' : tacenta_boundary.dh.is_prime_order_public pkb = ok true := hprime
  have heq' : tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes.eq pkb pkb =
      ok true := heq
  have hsig' : ∀ m, ∃ sig, tacenta_boundary.xeddsa.verify pkb m sig = ok (core.result.Result.Ok ()) := hsig
  have hag' : ∀ k, ∃ x, tacenta_boundary.dh.PrivateKey.agree k pkb = ok (some x) := hag
  have henc' : tacenta_boundary.kem.encapsulate byteRng byteCrc (alloc.vec.Vec.deref kemPk) stream =
      ok (core.result.Result.Ok (ct, ss), rest) := henc
  have hdec' : tacenta_boundary.kem.decapsulate kp (alloc.vec.Vec.deref ct) = ok (core.result.Result.Ok ss) :=
    hdec
  have hz' : zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref zPool z = ok (alloc.vec.Vec.new PoolEntry) := hz
  -- the contracts
  obtain ⟨c⟩ := Tacenta.UnitSatisfiabilityRecords.initiator_contracts_of_axiom_base byteRng A
  obtain ⟨contracts⟩ := Tacenta.UnitSatisfiabilityRecords.responder_contracts_of_axiom_base byteRng RA L.laws
  have hdh := c.dhCodec
  -- the bundle's signatures
  obtain ⟨v, hv, -⟩ := Std.WP.spec_imp_exists (Tacenta.UnitLifecycleT1.encode_ec_spec hdh pkb)
  obtain ⟨sig1, hs1⟩ := hsig' (alloc.vec.Vec.deref v)
  obtain ⟨v1, hv1, -⟩ := Std.WP.spec_imp_exists
    (Tacenta.UnitLifecycleT1.encode_kem_no_panic (alloc.vec.Vec.deref kemPk) hlen)
  obtain ⟨sig2, hs2⟩ := hsig' (alloc.vec.Vec.deref v1)
  have hverify : verify_bundle (reachBundle pkb sig1 sig2 kemPk).bundle = ok (core.result.Result.Ok ()) :=
    Tacenta.UnitLifecycleEstablishInitiatorShape.verify_successBundle pkb a ha' hcan hprime' sig1 sig2 kemPk
      v v1 hv hs1 hv1 hs2
  -- the establishment
  obtain ⟨q, rng1, hqct, hqss, h⟩ := reach_establishment c ourA pkb a ha' hcan heq' sig1 sig2 kemPk hverify
    hag' stream rest ct ss henc'
  -- the encrypt record at that establishment, from the seed followed by the 64 bytes
  have hlen128 : 64 ≤ (seed ++ (extra1 ++ extra2)).length := by simp [hseed]
  obtain ⟨oracle, bundle0, s0, rng10, hK, hdraws0, H0⟩ :=
    Tacenta.UnitLifecycleEstablishedEncrypt.established_encrypt_hypotheses_jointly_satisfiable K dh kem L A S
      hpub hct X ourA (seed ++ (extra1 ++ extra2)) hlen128
  have H : EstablishedEncryptHypotheses byteRng byteCrc byteTrace dh kem
      Tacenta.UnitLifecycleRepair.witnessView oracle byteRng byteCrc ourA (reachBundle pkb sig1 sig2 kemPk)
      (reachBundle pkb sig1 sig2 kemPk).bundle.identity_key (List.replicate 32 0#u8 ++ stream) rng1 q.session
      emptyPlaintext (seed ++ (extra1 ++ extra2)) :=
    { braid := H0.braid, triple := H0.triple, derivedKeys := H0.derivedKeys, aead := H0.aead,
      dhCodec := H0.dhCodec, oracleOf := H0.oracleOf, codec := H0.codec, codewordView := H0.codewordView,
      zeroizing80 := H0.zeroizing80, zeroizing32 := H0.zeroizing32, zeroizingKeys := H0.zeroizingKeys,
      keyGen := H0.keyGen, kemCiphertextLen := H0.kemCiphertextLen,
      kemCiphertextBound := H0.kemCiphertextBound, established := h, room := H0.room,
      trace_eq := H0.trace_eq, draws := H0.draws }
  obtain ⟨inst⟩ := H.derivedKeys
  subst hK
  have htr := byteTrace_seed_two_extra seed extra1 extra2 hseed h1 h2
  -- the first send's success, and the source it leaves
  obtain ⟨output, hcall, hrest, hcases⟩ := Tacenta.UnitLifecycleEstablishedEncrypt.established_encrypt_outcomes
    byteRng byteCrc byteTrace dh kem Tacenta.UnitLifecycleRepair.witnessView oracle H.braid H.triple H.aead
    H.dhCodec H.oracleOf H.codec H.codewordView H.zeroizing80 H.zeroizing32 H.zeroizingKeys H.keyGen
    H.kemCiphertextLen H.kemCiphertextBound byteRng byteCrc ourA _ _ _ rng1 q.session H.established
    emptyPlaintext H.room (seed ++ (extra1 ++ extra2)) H.trace_eq _ _ _ htr
  rw [two_draws_of_seed_extra seed (extra1 ++ extra2) hseed] at hcases
  obtain ⟨res, s', rng'⟩ := output
  rcases hcases with ⟨hnone, -⟩ | ⟨dk, ekSeed, ekVector, -, bytes, hres, -⟩
  · exact absurd hnone hkg
  simp only at hres hrest
  subst hres
  -- the responder's side
  let ourB : lifecycle.Identity := { secret := sb }
  have hidentity : lifecycle.Identity.public ourB = ok pkb := by
    show (do let pk ← tacenta_boundary.dh.PrivateKey.from_bytes sb; tacenta_boundary.dh.PrivateKey.public_key pk)
      = ok pkb
    rw [hkB']; exact hpkb'
  let storeB := reachStore pkb sb sig1 sig2 z kp
  have hpublish := publish_reachStore pkb sb kB hkB' hpkb' sig1 sig2 z hz' FS.empty kp kemPk hkp
  have hdistinct := reachStore_distinct pkb sb sig1 sig2 z hz' kp
  have hkem : FirstKemAgrees storeB (reachBundle pkb sig1 sig2 kemPk).kem_prekey_id q.kemCiphertext
      q.kemSecret := by
    refine ⟨kp, by simp [heldKemPair, storeB, reachStore, reachBundle], ?_⟩
    rw [hqct, hqss]; exact hdec'
  have hhead : Tacenta.UnitLifecycleT1.EstablishResponderHeadroom storeB :=
    ⟨by simp [storeB, reachStore]; exact Tacenta.UnitSatisfiabilityBraidAgreements.usize_max_ge 1 (by norm_num)⟩
  obtain ⟨oracle0, bundle1, s1, rng11, hK0, H1⟩ :=
    Tacenta.UnitLifecycleEstablishedDecrypt.established_decrypt_hypotheses_jointly_satisfiable
      oracle.braidKem dh L A S hpub hct ourA
  have ag : DecryptRatchetAgreements oracle.braidKem :=
    hK0 ▸ (H1 Tacenta.UnitLifecycleRepair.witnessView).agreements
  -- the oracle's public key of the responder's 32 bytes is the bytes of the boundary's public key of them
  have hpubOf : ∀ (sb' : Array U8 32#usize) (k : tacenta_boundary.dh.PrivateKey)
      (pk : tacenta_boundary.dh.PublicKeyBytes) (b : Array U8 32#usize),
      tacenta_boundary.dh.PrivateKey.from_bytes sb' = ok k →
      tacenta_boundary.dh.PrivateKey.public_key k = ok pk → tacenta_boundary.dh.PublicKeyBytes.as_bytes pk = ok b →
      oracle.dhPublic (arrayOf sb') = arrayOf b := by
    intro sb' k pk b hk hpk hb
    obtain ⟨k', hk', hkv⟩ := H.codec.privateFromBytes sb'
    rw [hk] at hk'; cases hk'
    obtain ⟨pk', hpk', hpkv⟩ := H.oracleOf.dhPublic k
    rw [hpk] at hpk'; cases hpk'
    obtain ⟨b', hb', hbv⟩ := H.codec.asBytes pk
    rw [hb] at hb'; cases hb'
    rw [← hkv, ← hpkv, hbv]
  -- the initiator's draws after its first send: the 64 bytes after the seed, as two draws
  have hdrawA : byteTrace rng' = extra1.map Tacenta.SessionUnitBraidT3.u8 ::
      [extra2.map Tacenta.SessionUnitBraidT3.u8] := hrest
  have hu : 4294967295 ≤ Usize.max :=
    Tacenta.SessionUnitSessionT1.small_le_usize_max (le_refl _)
  -- the responder's 32-byte source: a key whose public key is not the peer key the initiator holds
  obtain ⟨sbB, kF, pkF, bF, hkF, hpkF, hbF, hne⟩ := (dhPublicNotConstant_is.mp hnc) q.peerRatchetBytes
  let seedB := sbB.val
  have hseedB : seedB.length = 32 := by simp [seedB]
  let oracleB : Model.Lifecycle.Oracle := { oracle with draws := byteTrace seedB }
  have oracleOfB : Tacenta.UnitLifecycleT3.OracleOf byteRng byteCrc dh kem byteTrace oracleB :=
    oracleOf_with_draws H.oracleOf _
  have hdrB : byteTrace seedB = seedB.map Tacenta.SessionUnitBraidT3.u8 :: [] := byteTrace_one seedB hseedB
  have hfresh : oracleB.dhPublic (seedB.map Tacenta.SessionUnitBraidT3.u8) ≠ arrayOf q.peerRatchetBytes := by
    show oracle.dhPublic (sbB.val.map Tacenta.SessionUnitBraidT3.u8) ≠ arrayOf q.peerRatchetBytes
    rw [show sbB.val.map Tacenta.SessionUnitBraidT3.u8 = arrayOf sbB from rfl, hpubOf sbB kF pkF bF hkF hpkF hbF]
    intro hab
    exact hne (Tacenta.UnitLifecycleEstablishedEncrypt.array_eq_of_bytes hab)
  obtain ⟨-, hdisj⟩ := Tacenta.UnitLifecycleResponderFirstReceipt.initiator_first_send_responder_receives byteRng
    byteCrc byteTrace dh kem Tacenta.UnitLifecycleRepair.witnessView oracle H.braid H.triple H.aead H.dhCodec
    H.oracleOf H.codec H.codewordView H.zeroizing80 H.zeroizing32 H.zeroizingKeys H.keyGen hsizes
    H.kemCiphertextLen H.kemCiphertextBound byteRng byteCrc ourA _ _ _ rng1 q.session h q rfl emptyPlaintext H.room
    (seed ++ (extra1 ++ extra2)) H.trace_eq _ _ _ htr bytes s' rng' hcall byteRng byteCrc contracts hpub hsym hcon
    haead hrt L.optionEq byteTrace oracleB (DecryptOracleOf.of_oracleOf oracleOfB) ag ourB storeB hpublish
    hidentity hdistinct hkem hhead seedB rfl _ [] hdrB
  rcases hdisj with ⟨-, e, hrefuse, -⟩ |
    ⟨p, ec, dSend, dk', ekSeed', ekVector', ptB, sB', storeB', rngB', -, -, -, -, -, -, -, -, -, -, hcallB, -⟩
  · exfalso
    rcases hrefuse with ⟨-, hleg⟩ | ⟨-, fp, -, x, hx, -⟩ | ⟨-, -, hne', -⟩
    · simp [storeB, reachStore] at hleg
    · simp [storeB, reachStore] at hx
    · exact hne' (by simp [storeB, reachStore])
  -- the first receipt of the reply, and the source it leaves
  obtain ⟨-, -, bytesR, sB'', ptA, s'', rngA', -, -, hcallR, -, hcallA, hpt, hdrA', -⟩ :=
    Tacenta.UnitLifecycleResponderReplyReceipt.initiator_receives_reply byteRng byteCrc byteTrace dh kem
      Tacenta.UnitLifecycleRepair.witnessView oracle H.braid H.triple H.aead H.dhCodec H.oracleOf H.codec
      H.codewordView H.zeroizing80 H.zeroizing32 H.zeroizingKeys H.keyGen hsizes H.kemCiphertextLen
      H.kemCiphertextBound byteRng byteCrc ourA _ _ _ rng1 q.session H.established q rfl emptyPlaintext H.room
      (seed ++ (extra1 ++ extra2)) H.trace_eq _ _ _ htr bytes s' rng' hcall contracts.decrypt ag _ _ hdrawA byteRng
      byteCrc contracts hpub hsym hcon haead hrt L.optionEq byteTrace oracleB oracleOfB H.braid ag ourB storeB
      hpublish hidentity hdistinct hkem seedB rfl _ [] hdrB ptB sB' storeB' rngB' hcallB ptR (by omega) rngB' hfresh
  -- the second delivery, from that source
  obtain ⟨-, -, bytesR2, sB''2, ptA2, s''2, rngA'2, rngA3, hcallR2, hcallA2, -, -, -, -, -, hcall2, -⟩ :=
    initiator_repeated_reply_refused byteRng byteCrc byteTrace dh kem Tacenta.UnitLifecycleRepair.witnessView oracle
      H.braid H.triple H.aead H.dhCodec H.oracleOf H.codec H.codewordView H.zeroizing80 H.zeroizing32
      H.zeroizingKeys H.keyGen hsizes H.kemCiphertextLen H.kemCiphertextBound byteRng byteCrc ourA _ _ _ rng1
      q.session H.established q rfl emptyPlaintext H.room (seed ++ (extra1 ++ extra2)) H.trace_eq _ _ _ htr bytes s'
      rng' hcall contracts.decrypt ag _ _ hdrawA byteRng byteCrc contracts hpub hsym hcon haead hrt L.optionEq
      byteTrace oracleB oracleOfB H.braid ag ourB storeB hpublish hidentity hdistinct hkem seedB rfl _ [] hdrB ptB
      sB' storeB' rngB' hcallB ptR (by omega) rngB' hfresh rngA' _ [] hdrA'
  rw [hcallR] at hcallR2
  simp only [ok.injEq, Prod.mk.injEq, core.result.Result.Ok.injEq] at hcallR2
  obtain ⟨rfl, rfl, -⟩ := hcallR2
  rw [hcallA] at hcallA2
  simp only [ok.injEq, Prod.mk.injEq, core.result.Result.Ok.injEq] at hcallA2
  obtain ⟨rfl, rfl, rfl⟩ := hcallA2
  exact ⟨oracle, _, q, bytes, s', rng', ourB, storeB, seedB, sB', ptB, storeB', rngB', bytesR, sB'', ptA, s'',
    rngA', rngA3, rfl, hcall, hpublish, hcallB, hcallR, hcallA, hpt, hcall2⟩

end Reach

end Tacenta.UnitLifecycleInitiatorRepeatedReply

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
info: 'Tacenta.UnitLifecycleInitiatorRepeatedReply.reply_again_receive_outOfOrder' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleInitiatorRepeatedReply.reply_again_receive_outOfOrder

/--
info: 'Tacenta.UnitLifecycleInitiatorRepeatedReply.reply_again_with_eviction' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleInitiatorRepeatedReply.reply_again_with_eviction

/--
info: 'Tacenta.UnitLifecycleInitiatorRepeatedReply.reply_again_model_refused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleInitiatorRepeatedReply.reply_again_model_refused

/--
info: 'Tacenta.UnitLifecycleInitiatorRepeatedReply.reply_key_agreement' depends on axioms: [propext,
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
 tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes.eq,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleInitiatorRepeatedReply.reply_key_agreement

/--
info: 'Tacenta.UnitLifecycleInitiatorRepeatedReply.reply_again_refused_of_invariant' depends on axioms: [propext,
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
#print axioms Tacenta.UnitLifecycleInitiatorRepeatedReply.reply_again_refused_of_invariant

/--
info: 'Tacenta.UnitLifecycleInitiatorRepeatedReply.initiator_repeated_reply_refused' depends on axioms: [propext,
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
#print axioms Tacenta.UnitLifecycleInitiatorRepeatedReply.initiator_repeated_reply_refused

/--
info: 'Tacenta.UnitLifecycleInitiatorRepeatedReply.byteTrace_seed_two_extra' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleInitiatorRepeatedReply.byteTrace_seed_two_extra

/--
info: 'Tacenta.UnitLifecycleInitiatorRepeatedReply.repeated_reply_refused_reachable' depends on axioms: [propext,
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
#print axioms Tacenta.UnitLifecycleInitiatorRepeatedReply.repeated_reply_refused_reachable

/--
info: Tacenta.UnitLifecycleInitiatorRepeatedReply.reply_again_receive_outOfOrder : ∀
  (rkA prk k1 k2 dSend x newPub candPub dR dS np : Model.State.Key) (out : Option Model.SparseRatchet.Output),
  Model.Triple.receiveDetailed
      (Tacenta.UnitLifecycleResponderReplyReceipt.initiatorAfterReply rkA prk k1 k2 dSend x newPub candPub)
      (Tacenta.UnitLifecycleResponderFirstReceipt.firstHeader newPub) dR dS np out =
    Except.error (Model.Triple.ReceiveRefusal.classical Model.Ratchet.ReceiveRefusal.outOfOrder)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleInitiatorRepeatedReply.reply_again_receive_outOfOrder

/--
info: Tacenta.UnitLifecycleInitiatorRepeatedReply.reply_again_with_eviction : ∀
  (rkA prk k1 k2 dSend x newPub candPub dR dS np : Model.State.Key) (composite : Model.CompositeHeader.Composite)
  (out : Option Model.SparseRatchet.Output),
  Model.Lifecycle.receiveWithEviction
      (Tacenta.UnitLifecycleResponderReplyReceipt.initiatorAfterReply rkA prk k1 k2 dSend x newPub candPub) composite
      (Tacenta.UnitLifecycleResponderFirstReceipt.firstHeader newPub) dR dS np out =
    Except.error (Model.Triple.ReceiveRefusal.classical Model.Ratchet.ReceiveRefusal.outOfOrder)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleInitiatorRepeatedReply.reply_again_with_eviction

/--
info: Tacenta.UnitLifecycleInitiatorRepeatedReply.reply_again_model_refused : ∀ (view : Model.Lifecycle.CodewordView)
  (oracleA oracleB : Model.Lifecycle.Oracle) (mA : Model.Lifecycle.Session)
  (rkA prk k1 k2 dSend x newPub candPub c0 : Model.State.Key) (e : ℕ) (auth : Model.Braid.Auth)
  (dk ekVector : Model.Braid.Bytes) (enc : Model.Braid.Encoder),
  mA.braid = Model.Braid.BraidState.keysSampled e auth dk ekVector enc →
    ∀ (mk : Model.State.Key) (pt : Model.Lifecycle.Bytes),
      List.length newPub = 32 →
        Model.Messages.checkKey newPub = some () →
          ∀ (dR : Model.State.Key),
            oracleA.dhAgree
                  (Tacenta.UnitLifecycleResponderReplyReceipt.replyReceiptSession mA rkA prk k1 k2 dSend x newPub
                      candPub c0).ratchetPrivate
                  newPub =
                some dR →
              ∀ (c : Model.State.Key) (rest : List Model.State.Key),
                oracleA.draws = c :: rest →
                  ∀ (dS : Model.State.Key),
                    oracleA.dhAgree c newPub = some dS →
                      Model.Lifecycle.decrypt view oracleA
                          (Tacenta.UnitLifecycleResponderReplyReceipt.replyReceiptSession mA rkA prk k1 k2 dSend x
                            newPub candPub c0)
                          (Tacenta.UnitLifecycleResponderReply.replyFrame oracleB mA.identityAd newPub mk pt) =
                        {
                          session :=
                            Tacenta.UnitLifecycleResponderReplyReceipt.replyReceiptSession mA rkA prk k1 k2 dSend x
                              newPub candPub c0,
                          result :=
                            Except.error
                              (Model.Lifecycle.Refusal.triple
                                (Model.Lifecycle.TripleRefusal.classical Model.Lifecycle.RatchetRefusal.outOfOrder)),
                          oracle :=
                            { draws := rest, braidKem := oracleA.braidKem, dhPublic := oracleA.dhPublic,
                              dhAgree := oracleA.dhAgree, identityValid := oracleA.identityValid,
                              aeadSeal := oracleA.aeadSeal, aeadOpen := oracleA.aeadOpen, kemValid := oracleA.kemValid,
                              kemEncaps := oracleA.kemEncaps, kemDecaps := oracleA.kemDecaps,
                              sigVerify := oracleA.sigVerify, sigSign := oracleA.sigSign } }
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleInitiatorRepeatedReply.reply_again_model_refused

/--
info: Tacenta.UnitLifecycleInitiatorRepeatedReply.reply_key_agreement : Tacenta.UnitLifecycleResponderFirstReceipt.DhAgreeContributory →
  ∀ {R : Type} {rc : rand_core_1.RngCore R} {crc : rand_core_1.CryptoRng R} {dh : Tacenta.UnitLifecycleT3.DhView}
    {trace : R → List Model.Lifecycle.Key} {oracle : Model.Lifecycle.Oracle},
    Tacenta.UnitLifecycleDecryptRatchetT3.DecryptOracleOf rc crc dh trace oracle →
      ∀ (k : tacenta_boundary.dh.PrivateKey) (pk : tacenta_boundary.dh.PublicKeyBytes),
        k.public_key = ok pk →
          ∀ (k' : tacenta_boundary.dh.PrivateKey), ∃ y, oracle.dhAgree (dh.privateKey k') (dh.publicKey pk) = some y
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleInitiatorRepeatedReply.reply_key_agreement

/--
info: @Tacenta.UnitLifecycleInitiatorRepeatedReply.reply_again_refused_of_invariant : ∀
  [Tacenta.SessionUnitT1.DerivedKeysModel] {R : Type} (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R)
  (trace : R → List Model.Lifecycle.Key) (dh : Tacenta.UnitLifecycleT3.DhView) (oracle : Model.Lifecycle.Oracle),
  Tacenta.UnitLifecycleDecryptRatchetT3.DecryptOracleOf rc crc dh trace oracle →
    Tacenta.UnitLifecycleT3.DhCodecOf dh →
      Tacenta.UnitLifecycleT1.DecryptRatchetContracts rc →
        Tacenta.UnitLifecycleDecryptRatchetT3.DecryptRatchetAgreements oracle.braidKem →
          Tacenta.UnitLifecycleEstablishInitiatorShape.DhPublicValid →
            Tacenta.UnitLifecycleResponderFirstReceipt.DhAgreeContributory →
              ∀ (mA : Model.Lifecycle.Session) (rkA prk k1 k2 dSend x candPub c0 : Model.Lifecycle.Key) (e : ℕ)
                (auth : Model.Braid.Auth) (dk ekVector : Model.Braid.Bytes) (enc : Model.Braid.Encoder),
                mA.braid = Model.Braid.BraidState.keysSampled e auth dk ekVector enc →
                  ∀ (k : tacenta_boundary.dh.PrivateKey) (pk : tacenta_boundary.dh.PublicKeyBytes),
                    k.public_key = ok pk →
                      ∀ (sA : lifecycle.Session),
                        sA.invariant = ok true →
                          Tacenta.UnitLifecycleDecryptRunBounds.CounterHeadroom sA →
                            Tacenta.UnitLifecycleT3.SessionRefines dh oracle.braidKem sA
                                (Tacenta.UnitLifecycleResponderReplyReceipt.replyReceiptSession mA rkA prk k1 k2 dSend x
                                  (dh.publicKey pk) candPub c0) →
                              ∀ (oracleB : Model.Lifecycle.Oracle) (mk : Model.Lifecycle.Key)
                                (pt : Model.Lifecycle.Bytes) (msg : Slice U8),
                                Tacenta.UnitLifecycleT3.sliceOf msg =
                                    Tacenta.UnitLifecycleResponderReply.replyFrame oracleB mA.identityAd
                                      (dh.publicKey pk) mk pt →
                                  ∀ (rng : R),
                                    trace rng = oracle.draws →
                                      ∀ (c : Model.Lifecycle.Key) (rest : List Model.Lifecycle.Key),
                                        trace rng = c :: rest →
                                          (∀ (view : Model.Lifecycle.CodewordView),
                                              Model.Lifecycle.decrypt view oracle
                                                  (Tacenta.UnitLifecycleResponderReplyReceipt.replyReceiptSession mA rkA
                                                    prk k1 k2 dSend x (dh.publicKey pk) candPub c0)
                                                  (Tacenta.UnitLifecycleT3.sliceOf msg) =
                                                {
                                                  session :=
                                                    Tacenta.UnitLifecycleResponderReplyReceipt.replyReceiptSession mA
                                                      rkA prk k1 k2 dSend x (dh.publicKey pk) candPub c0,
                                                  result :=
                                                    Except.error
                                                      (Model.Lifecycle.Refusal.triple
                                                        (Model.Lifecycle.TripleRefusal.classical
                                                          Model.Lifecycle.RatchetRefusal.outOfOrder)),
                                                  oracle :=
                                                    { draws := rest, braidKem := oracle.braidKem,
                                                      dhPublic := oracle.dhPublic, dhAgree := oracle.dhAgree,
                                                      identityValid := oracle.identityValid,
                                                      aeadSeal := oracle.aeadSeal, aeadOpen := oracle.aeadOpen,
                                                      kemValid := oracle.kemValid, kemEncaps := oracle.kemEncaps,
                                                      kemDecaps := oracle.kemDecaps, sigVerify := oracle.sigVerify,
                                                      sigSign := oracle.sigSign } }) ∧
                                            ∃ rng',
                                              lifecycle.Session.decrypt rc crc sA msg rng =
                                                  ok
                                                    (core.result.Result.Err
                                                        (lifecycle.Error.Triple
                                                          (tacenta_triple.TripleError.Classical
                                                            tacenta_ratchet.RatchetError.OutOfOrder)),
                                                      sA, rng') ∧
                                                trace rng' = rest
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleInitiatorRepeatedReply.reply_again_refused_of_invariant

/--
info: @Tacenta.UnitLifecycleInitiatorRepeatedReply.initiator_repeated_reply_refused : ∀
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
                                                      Tacenta.UnitLifecycleT1.DecryptRatchetContracts rc →
                                                        Tacenta.UnitLifecycleDecryptRatchetT3.DecryptRatchetAgreements
                                                            oracle.braidKem →
                                                          ∀ (dA : Model.Lifecycle.Key)
                                                            (restA : List Model.Lifecycle.Key),
                                                            trace rng' = dA :: restA →
                                                              ∀ (rcB : rand_core_1.RngCore F)
                                                                (crcB : rand_core_1.CryptoRng F)
                                                                (contracts :
                                                                  Tacenta.UnitLifecycleT1.EstablishResponderContracts
                                                                    rcB),
                                                                Tacenta.UnitLifecycleEstablishInitiatorShape.DhPublicValid →
                                                                  Tacenta.UnitLifecycleResponderFirstFrame.DhAgreeSymmetric →
                                                                    Tacenta.UnitLifecycleResponderFirstReceipt.DhAgreeContributory →
                                                                      Tacenta.UnitLifecycleResponderFirstReceipt.AeadRoundTrip →
                                                                        Tacenta.UnitLifecycleSessionCodec.DhPublicBytesRoundTrip →
                                                                          Tacenta.UnitHeadroomInvariant.OptionEqU64Shape
                                                                              @core.option.Option.Insts.CoreCmpPartialEqOption.eq →
                                                                            ∀ (traceB : F → List Model.Lifecycle.Key)
                                                                              (oracleB : Model.Lifecycle.Oracle),
                                                                              Tacenta.UnitLifecycleT3.OracleOf rcB crcB
                                                                                  dh kem traceB oracleB →
                                                                                Tacenta.UnitLifecycleT3.BraidSendRefinementContracts
                                                                                    rcB oracleB.braidKem →
                                                                                  Tacenta.UnitLifecycleDecryptRatchetT3.DecryptRatchetAgreements
                                                                                      oracleB.braidKem →
                                                                                    ∀ (ourB : lifecycle.Identity)
                                                                                      (storeB : lifecycle.PrekeyStore),
                                                                                      storeB.publish = ok bundleA →
                                                                                        ourB.public =
                                                                                            ok storeB.identity_public →
                                                                                          Tacenta.UnitLifecycleResponderFirstFrame.PrekeyIdsDistinct
                                                                                              storeB →
                                                                                            Tacenta.UnitLifecycleResponderFirstFrame.FirstKemAgrees
                                                                                                storeB
                                                                                                bundleA.kem_prekey_id
                                                                                                q.kemCiphertext
                                                                                                q.kemSecret →
                                                                                              ∀ (rngB : F),
                                                                                                traceB rngB =
                                                                                                    oracleB.draws →
                                                                                                  ∀
                                                                                                    (dB :
                                                                                                      Model.Lifecycle.Key)
                                                                                                    (restB :
                                                                                                      List
                                                                                                        Model.Lifecycle.Key),
                                                                                                    traceB rngB =
                                                                                                        dB :: restB →
                                                                                                      ∀
                                                                                                        (ptB :
                                                                                                          alloc.vec.Vec
                                                                                                            U8)
                                                                                                        (sB' :
                                                                                                          lifecycle.Session)
                                                                                                        (storeB' :
                                                                                                          lifecycle.PrekeyStore)
                                                                                                        (rngB' : F),
                                                                                                        lifecycle.establish_responder
                                                                                                              rcB crcB
                                                                                                              ourB
                                                                                                              storeB
                                                                                                              bytes.deref
                                                                                                              rngB =
                                                                                                            ok
                                                                                                              (core.result.Result.Ok
                                                                                                                  (sB',
                                                                                                                    ptB),
                                                                                                                storeB',
                                                                                                                rngB') →
                                                                                                          ∀
                                                                                                            (ptR :
                                                                                                              Slice U8),
                                                                                                            102 +
                                                                                                                  ((↑ptR).length +
                                                                                                                    48) ≤
                                                                                                                Usize.max →
                                                                                                              ∀
                                                                                                                (rngR :
                                                                                                                  F),
                                                                                                                oracleB.dhPublic
                                                                                                                      dB ≠
                                                                                                                    Tacenta.UnitLifecycleT3.arrayOf
                                                                                                                      q.peerRatchetBytes →
                                                                                                                  ∀
                                                                                                                    (rngA2 :
                                                                                                                      R)
                                                                                                                    (dA2 :
                                                                                                                      Model.Lifecycle.Key)
                                                                                                                    (restA2 :
                                                                                                                      List
                                                                                                                        Model.Lifecycle.Key),
                                                                                                                    trace
                                                                                                                          rngA2 =
                                                                                                                        dA2 ::
                                                                                                                          restA2 →
                                                                                                                      ∃
                                                                                                                        dSend
                                                                                                                        x
                                                                                                                        bytesR
                                                                                                                        sB''
                                                                                                                        ptA
                                                                                                                        s''
                                                                                                                        rngA'
                                                                                                                        rngA3,
                                                                                                                        lifecycle.Session.encrypt
                                                                                                                              rcB
                                                                                                                              crcB
                                                                                                                              sB'
                                                                                                                              ptR
                                                                                                                              rngR =
                                                                                                                            ok
                                                                                                                              (core.result.Result.Ok
                                                                                                                                  bytesR,
                                                                                                                                sB'',
                                                                                                                                rngR) ∧
                                                                                                                          lifecycle.Session.decrypt
                                                                                                                                rc
                                                                                                                                crc
                                                                                                                                s'
                                                                                                                                bytesR.deref
                                                                                                                                rng' =
                                                                                                                              ok
                                                                                                                                (core.result.Result.Ok
                                                                                                                                    ptA,
                                                                                                                                  s'',
                                                                                                                                  rngA') ∧
                                                                                                                            ↑ptA =
                                                                                                                                ↑ptR ∧
                                                                                                                              s''.invariant =
                                                                                                                                  ok
                                                                                                                                    true ∧
                                                                                                                                Tacenta.UnitLifecycleDecryptRunBounds.CounterHeadroom
                                                                                                                                    s'' ∧
                                                                                                                                  Tacenta.UnitLifecycleT3.SessionRefines
                                                                                                                                      dh
                                                                                                                                      oracle.braidKem
                                                                                                                                      s''
                                                                                                                                      (Tacenta.UnitLifecycleResponderReplyReceipt.replyReceiptSession
                                                                                                                                        (Model.Lifecycle.encrypt
                                                                                                                                            view
                                                                                                                                            oracle
                                                                                                                                            (Tacenta.UnitLifecycleEstablishInitiatorShape.establishedModelOf
                                                                                                                                              dh
                                                                                                                                              s)
                                                                                                                                            (Tacenta.UnitLifecycleT3.sliceOf
                                                                                                                                              plaintext)).session
                                                                                                                                        (Tacenta.UnitLifecycleT3.arrayOf
                                                                                                                                          q.rootKey)
                                                                                                                                        (Tacenta.UnitLifecycleT3.arrayOf
                                                                                                                                          q.sparseRoot)
                                                                                                                                        (Tacenta.UnitLifecycleT3.arrayOf
                                                                                                                                          q.sparseSend)
                                                                                                                                        (Tacenta.UnitLifecycleT3.arrayOf
                                                                                                                                          q.sparseReceive)
                                                                                                                                        dSend
                                                                                                                                        x
                                                                                                                                        (oracleB.dhPublic
                                                                                                                                          dB)
                                                                                                                                        (oracle.dhPublic
                                                                                                                                          dA)
                                                                                                                                        dA) ∧
                                                                                                                                    (∀
                                                                                                                                        (viewA :
                                                                                                                                          Model.Lifecycle.CodewordView),
                                                                                                                                        Model.Lifecycle.decrypt
                                                                                                                                            viewA
                                                                                                                                            {
                                                                                                                                              draws :=
                                                                                                                                                dA2 ::
                                                                                                                                                  restA2,
                                                                                                                                              braidKem :=
                                                                                                                                                oracle.braidKem,
                                                                                                                                              dhPublic :=
                                                                                                                                                oracle.dhPublic,
                                                                                                                                              dhAgree :=
                                                                                                                                                oracle.dhAgree,
                                                                                                                                              identityValid :=
                                                                                                                                                oracle.identityValid,
                                                                                                                                              aeadSeal :=
                                                                                                                                                oracle.aeadSeal,
                                                                                                                                              aeadOpen :=
                                                                                                                                                oracle.aeadOpen,
                                                                                                                                              kemValid :=
                                                                                                                                                oracle.kemValid,
                                                                                                                                              kemEncaps :=
                                                                                                                                                oracle.kemEncaps,
                                                                                                                                              kemDecaps :=
                                                                                                                                                oracle.kemDecaps,
                                                                                                                                              sigVerify :=
                                                                                                                                                oracle.sigVerify,
                                                                                                                                              sigSign :=
                                                                                                                                                oracle.sigSign }
                                                                                                                                            (Tacenta.UnitLifecycleResponderReplyReceipt.replyReceiptSession
                                                                                                                                              (Model.Lifecycle.encrypt
                                                                                                                                                  view
                                                                                                                                                  oracle
                                                                                                                                                  (Tacenta.UnitLifecycleEstablishInitiatorShape.establishedModelOf
                                                                                                                                                    dh
                                                                                                                                                    s)
                                                                                                                                                  (Tacenta.UnitLifecycleT3.sliceOf
                                                                                                                                                    plaintext)).session
                                                                                                                                              (Tacenta.UnitLifecycleT3.arrayOf
                                                                                                                                                q.rootKey)
                                                                                                                                              (Tacenta.UnitLifecycleT3.arrayOf
                                                                                                                                                q.sparseRoot)
                                                                                                                                              (Tacenta.UnitLifecycleT3.arrayOf
                                                                                                                                                q.sparseSend)
                                                                                                                                              (Tacenta.UnitLifecycleT3.arrayOf
                                                                                                                                                q.sparseReceive)
                                                                                                                                              dSend
                                                                                                                                              x
                                                                                                                                              (oracleB.dhPublic
                                                                                                                                                dB)
                                                                                                                                              (oracle.dhPublic
                                                                                                                                                dA)
                                                                                                                                              dA)
                                                                                                                                            (Tacenta.UnitLifecycleT3.vecOf
                                                                                                                                              bytesR) =
                                                                                                                                          {
                                                                                                                                            session :=
                                                                                                                                              Tacenta.UnitLifecycleResponderReplyReceipt.replyReceiptSession
                                                                                                                                                (Model.Lifecycle.encrypt
                                                                                                                                                    view
                                                                                                                                                    oracle
                                                                                                                                                    (Tacenta.UnitLifecycleEstablishInitiatorShape.establishedModelOf
                                                                                                                                                      dh
                                                                                                                                                      s)
                                                                                                                                                    (Tacenta.UnitLifecycleT3.sliceOf
                                                                                                                                                      plaintext)).session
                                                                                                                                                (Tacenta.UnitLifecycleT3.arrayOf
                                                                                                                                                  q.rootKey)
                                                                                                                                                (Tacenta.UnitLifecycleT3.arrayOf
                                                                                                                                                  q.sparseRoot)
                                                                                                                                                (Tacenta.UnitLifecycleT3.arrayOf
                                                                                                                                                  q.sparseSend)
                                                                                                                                                (Tacenta.UnitLifecycleT3.arrayOf
                                                                                                                                                  q.sparseReceive)
                                                                                                                                                dSend
                                                                                                                                                x
                                                                                                                                                (oracleB.dhPublic
                                                                                                                                                  dB)
                                                                                                                                                (oracle.dhPublic
                                                                                                                                                  dA)
                                                                                                                                                dA,
                                                                                                                                            result :=
                                                                                                                                              Except.error
                                                                                                                                                (Model.Lifecycle.Refusal.triple
                                                                                                                                                  (Model.Lifecycle.TripleRefusal.classical
                                                                                                                                                    Model.Lifecycle.RatchetRefusal.outOfOrder)),
                                                                                                                                            oracle :=
                                                                                                                                              {
                                                                                                                                                draws :=
                                                                                                                                                  restA2,
                                                                                                                                                braidKem :=
                                                                                                                                                  oracle.braidKem,
                                                                                                                                                dhPublic :=
                                                                                                                                                  oracle.dhPublic,
                                                                                                                                                dhAgree :=
                                                                                                                                                  oracle.dhAgree,
                                                                                                                                                identityValid :=
                                                                                                                                                  oracle.identityValid,
                                                                                                                                                aeadSeal :=
                                                                                                                                                  oracle.aeadSeal,
                                                                                                                                                aeadOpen :=
                                                                                                                                                  oracle.aeadOpen,
                                                                                                                                                kemValid :=
                                                                                                                                                  oracle.kemValid,
                                                                                                                                                kemEncaps :=
                                                                                                                                                  oracle.kemEncaps,
                                                                                                                                                kemDecaps :=
                                                                                                                                                  oracle.kemDecaps,
                                                                                                                                                sigVerify :=
                                                                                                                                                  oracle.sigVerify,
                                                                                                                                                sigSign :=
                                                                                                                                                  oracle.sigSign } }) ∧
                                                                                                                                      lifecycle.Session.decrypt
                                                                                                                                            rc
                                                                                                                                            crc
                                                                                                                                            s''
                                                                                                                                            bytesR.deref
                                                                                                                                            rngA2 =
                                                                                                                                          ok
                                                                                                                                            (core.result.Result.Err
                                                                                                                                                (lifecycle.Error.Triple
                                                                                                                                                  (tacenta_triple.TripleError.Classical
                                                                                                                                                    tacenta_ratchet.RatchetError.OutOfOrder)),
                                                                                                                                              s'',
                                                                                                                                              rngA3) ∧
                                                                                                                                        trace
                                                                                                                                            rngA3 =
                                                                                                                                          restA2
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleInitiatorRepeatedReply.initiator_repeated_reply_refused

/--
info: Tacenta.UnitLifecycleInitiatorRepeatedReply.byteTrace_seed_two_extra : ∀ (seed e1 e2 : List U8),
  seed.length = 64 →
    e1.length = 32 →
      e2.length = 32 →
        Tacenta.UnitLifecycleIntegrationScreen.byteTrace (seed ++ (e1 ++ e2)) =
          [List.take 32 (List.map Tacenta.SessionUnitBraidT3.u8 (seed ++ (e1 ++ e2))),
            List.take 32 (List.drop 32 (List.map Tacenta.SessionUnitBraidT3.u8 (seed ++ (e1 ++ e2)))),
            List.map Tacenta.SessionUnitBraidT3.u8 e1, List.map Tacenta.SessionUnitBraidT3.u8 e2]
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleInitiatorRepeatedReply.byteTrace_seed_two_extra

/--
info: Tacenta.UnitLifecycleInitiatorRepeatedReply.repeated_reply_refused_reachable : ∀ (K : Model.Braid.Kem)
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
                            Tacenta.UnitLifecycleResponderReplyReceipt.DhPublicNotConstant →
                              ∀ (ourA : lifecycle.Identity) (seed : List U8),
                                seed.length = 64 →
                                  ∀ (extra1 extra2 : List U8),
                                    extra1.length = 32 →
                                      extra2.length = 32 →
                                        K.keyGen
                                              (Model.Lifecycle.braidRandomness
                                                (List.map Tacenta.SessionUnitBraidT3.u8 seed)) ≠
                                            none →
                                          ∀ (ptR : Slice U8),
                                            (↑ptR).length ≤ 4096 →
                                              ∃ oracle bundle q bytes s' rng' ourB storeB seedB sB' ptB storeB' rngB'
                                                bytesR sB'' ptA s'' rngA' rngA3,
                                                oracle.braidKem = K ∧
                                                  lifecycle.Session.encrypt
                                                        Tacenta.UnitLifecycleIntegrationScreen.byteRng
                                                        Tacenta.UnitLifecycleIntegrationScreen.byteCrc q.session
                                                        Tacenta.UnitLifecycleEstablishedEncrypt.emptyPlaintext
                                                        (seed ++ (extra1 ++ extra2)) =
                                                      ok (core.result.Result.Ok bytes, s', rng') ∧
                                                    storeB.publish = ok bundle ∧
                                                      lifecycle.establish_responder
                                                            Tacenta.UnitLifecycleIntegrationScreen.byteRng
                                                            Tacenta.UnitLifecycleIntegrationScreen.byteCrc ourB storeB
                                                            bytes.deref seedB =
                                                          ok (core.result.Result.Ok (sB', ptB), storeB', rngB') ∧
                                                        lifecycle.Session.encrypt
                                                              Tacenta.UnitLifecycleIntegrationScreen.byteRng
                                                              Tacenta.UnitLifecycleIntegrationScreen.byteCrc sB' ptR
                                                              rngB' =
                                                            ok (core.result.Result.Ok bytesR, sB'', rngB') ∧
                                                          lifecycle.Session.decrypt
                                                                Tacenta.UnitLifecycleIntegrationScreen.byteRng
                                                                Tacenta.UnitLifecycleIntegrationScreen.byteCrc s'
                                                                bytesR.deref rng' =
                                                              ok (core.result.Result.Ok ptA, s'', rngA') ∧
                                                            ↑ptA = ↑ptR ∧
                                                              lifecycle.Session.decrypt
                                                                  Tacenta.UnitLifecycleIntegrationScreen.byteRng
                                                                  Tacenta.UnitLifecycleIntegrationScreen.byteCrc s''
                                                                  bytesR.deref rngA' =
                                                                ok
                                                                  (core.result.Result.Err
                                                                      (lifecycle.Error.Triple
                                                                        (tacenta_triple.TripleError.Classical
                                                                          tacenta_ratchet.RatchetError.OutOfOrder)),
                                                                    s'', rngA3)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleInitiatorRepeatedReply.repeated_reply_refused_reachable
