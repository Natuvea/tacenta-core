import Translation.UnitLifecycleResponderFirstReceipt

/-!
# `establish_responder` again on the initiator's first frame, at the store its first success committed

`UnitLifecycleResponderFirstReceipt` shows that `establish_responder` on the bytes the initiator's first `encrypt`
emits either refuses as the store decides or succeeds, and that on success it commits the prekey store
(`ResponderCommit`): on the last-resort path the replay record gains the fingerprint of the handshake's shared
secret.  This module delivers the same bytes again, to `establish_responder` at the store that commit left, on the
same run, and shows the call refuses them as a replay with no durable effect: it returns `ReplayedLastResort`, the
store it was given and the source of randomness it was given, and no session.  `UnitLifecycleEstablishResponder`'s
`establish_responder_replay_refused` reaches the same refusal at a store built for the purpose; here the store is the
one the run's own first success left.

## What is shown

* `replay_refused_of_mem` (no hypothesis beyond the fingerprint's equation): the replay check on the last-resort path
  refuses `ReplayedLastResort` whenever some entry of the record holds the fingerprint of the given secret.
* `commit_last_resort` (no hypothesis): the success commit on the last-resort path with no one-time curve prekey
  named changes only the replay record, which gains `(kemId, fp)` at its end.
* `establish_responder_again_refused` (no hypothesis beyond its inputs): for parts `p` of an input on the
  last-resort path (`p.lastResort = true`) and the store such a commit left with the fingerprint of `p`'s shared
  secret, `establish_responder` on the same message at that store returns `ReplayedLastResort`, that store and the
  source as given.  Every step of the prepare phase before the replay check reads the store's fields other than the
  replay record, so it repeats the first call's step; the replay check then finds the entry the commit appended.
* `initiator_first_send_responder_replay_refused` (the composed statement): for every successful first `encrypt` at
  an establishment output (`established_encrypt_outcomes`), every responder identity and prekey store whose
  `publish` returned the bundle the initiator used, when that bundle names the store's last-resort KEM key and no
  one-time curve prekey, and every successful return `(Ok (sB', ptB), storeB', rngB')` of `establish_responder` on
  the bytes the initiator emitted: the parts of that call take the last-resort path, `storeB'` is the store with only
  its replay record changed, that record is the old one with `(kem_id, fp)` appended for the fingerprint `fp` of the
  shared secret the call computed, and `establish_responder` on the same bytes at `storeB'` returns
  `ReplayedLastResort`, `storeB'` and the source as given, from every source.
* Non-vacuity.  `first_send_replay_refused_reachable`: at the real constants, under the laws of
  `first_send_receive_reachable` (all assumed), one run from `publish` through the establishment, the first send and
  the responder's success, at a store whose bundle names its last-resort KEM key and no one-time curve prekey and
  whose replay record starts empty, after which the record holds exactly one entry and the second call is refused
  from every source.

## The laws and premises

No new law.  The composed statement takes the hypotheses of `established_encrypt_outcomes` for the initiator's
send, the zeroizing round trip `ZeroizingArrayRoundTrip` and `DhPublicValid` (which `parts_of_first_frame` uses to
read the decoded identifiers back), the store's `publish` and identity equations, the success equation of the first
call, and two premises on the run's shape: the bundle names the store's last-resort KEM key, and it names no one-time
curve prekey.  Both hold on the reach run.  It takes none of the receipt's laws (`AeadRoundTrip`,
`DhAgreeContributory`, `DhAgreeSymmetric`), `FirstKemAgrees` or `PrekeyIdsDistinct`: the success equation is a
hypothesis, and the refusal does not depend on why the first call succeeded.

## Non-vacuity

`first_send_replay_refused_reachable` exhibits every premise of the composed statement on one run at the real
constants, under the laws of `first_send_receive_reachable`, assumed and modelled together in `first_receipt_laws_model`
(a toy interpretation, as recorded there).

## What it does not show

* The model's side: no relation between the code's prekey store and the model's, and no refinement of the model's
  `establishResponder`, exists in the tree, so this is a statement about the translated code alone; that the model
  refuses the same delivery is not shown here.
* The one-time path: a bundle that names a one-time KEM prekey or a one-time curve prekey, whose second delivery the
  code refuses (by reading) because the commit removed the key, is not covered; which entry the commit's removals take
  is not stated.
* A second delivery after a first call that refused, or after any other store change between the two calls (a
  `publish`, a rotation, another handshake); the second delivery of the same bytes to the session the first call
  returned (`UnitLifecycleResponderRepeatedFrame` takes that).
* A delivery of other bytes that carry the same handshake (a re-encoding, a tampered frame): the statement is about
  the same bytes; that a different message with the same shared secret is refused follows from the generic lemma only
  when its prepare phase repeats, which is not shown for any other message.
* That the replay record keeps this entry for the store's life (a later record-full rotation or legacy marker);
  that the real primitives meet the laws the run rests on; `PrekeyIdsDistinct` from `PrekeyStore::invariant`.  A
  source with no state of its own, such as `OsRng`, is outside the statements about the source.
-/

namespace Tacenta.UnitLifecycleResponderEstablishReplay

open Aeneas Aeneas.Std Result
open tacenta_session_unit
open Tacenta.UnitLifecycleEstablishResponder (ResponderPreparedParts ResponderCommit)

/-- The replay check refuses when the record holds the fingerprint. -/
theorem replay_refused_of_mem (store : lifecycle.PrekeyStore) (kemId : U32) (sk fp : Array U8 32#usize)
    (hfp : lifecycle.last_resort_fingerprint sk = ok fp)
    (hmem : ∃ x ∈ store.last_resort_seen.val, x.2 = fp) :
    lifecycle.responder_replay_fingerprint store kemId sk true =
      ok (core.result.Result.Err lifecycle.Error.ReplayedLastResort) := by
  unfold lifecycle.responder_replay_fingerprint
  rw [if_pos rfl, hfp, Aeneas.Std.bind_tc_ok]
  obtain ⟨r, hr, rfl⟩ := Std.WP.spec_imp_exists
    (Tacenta.UnitLifecycleResponderFirstFrame.replay_loop_flag store fp)
  rw [hr, Aeneas.Std.bind_tc_ok]
  simp only [decide_eq_true hmem]
  rfl

/-- The commit on the last-resort path, with no one-time curve prekey named: only the replay record changes, and
it gains `(kemId, fp)` at its end. -/
theorem commit_last_resort (store store' : lifecycle.PrekeyStore) (kemId : U32) (fp : Array U8 32#usize)
    (h : ResponderCommit store kemId serialization.ABSENT_ID true (some fp) store') :
    ∃ seen : alloc.vec.Vec (U32 × Array U8 32#usize),
      seen.val = store.last_resort_seen.val.concat (kemId, fp) ∧
      store' = { store with last_resort_seen := seen } := by
  obtain ⟨store1, store2, c1, c2, c3⟩ := h
  rw [if_pos rfl] at c1
  rw [if_neg (by simp)] at c2
  subst c1 c2
  obtain ⟨count, seen, -, -, hseen, rfl⟩ := c3
  exact ⟨seen, by rw [Tacenta.UnitLifecycleEstablishResponder.vec_push_ok hseen]; simp, rfl⟩

/-- **The same initial message again, at the store the success commit left, is refused as a replay**: for parts `p`
of an input on the last-resort path and a store `storeB'` that the commit of the last-resort path with no one-time
curve prekey left from the parts' store, with the fingerprint `fp` of `p`'s shared secret, `establish_responder` on
the same message at `storeB'` returns `ReplayedLastResort` with `storeB'` and the source as given.  The prepare phase
repeats the first call's steps up to the replay check, whose record now holds `fp`. -/
theorem establish_responder_again_refused {E : Type} (rcB : rand_core_1.RngCore E)
    (crcB : rand_core_1.CryptoRng E) {ourB : lifecycle.Identity} {storeB : lifecycle.PrekeyStore} {msg : Slice U8}
    (p : ResponderPreparedParts ourB storeB msg) (hlr : p.lastResort = true)
    (kemId : U32) (fp : Array U8 32#usize) (hfp : lifecycle.last_resort_fingerprint p.secret = ok fp)
    (storeB' : lifecycle.PrekeyStore)
    (hcommit : ResponderCommit storeB kemId serialization.ABSENT_ID true (some fp) storeB') (rng : E) :
    lifecycle.establish_responder rcB crcB ourB storeB' msg rng =
      ok (core.result.Result.Err lifecycle.Error.ReplayedLastResort, storeB', rng) := by
  obtain ⟨seen, hseen, rfl⟩ := commit_last_resort storeB storeB' kemId fp hcommit
  have hSigned : lifecycle.responder_signed_prekey_secret { storeB with last_resort_seen := seen }
      p.decoded.signed_prekey_id = ok (core.result.Result.Ok p.signedSecret) := p.hSigned
  have hSlot : lifecycle.responder_kem_slot { storeB with last_resort_seen := seen } p.decoded.kem_prekey_id =
      ok (core.result.Result.Ok (p.kemSlot, true)) := hlr ▸ p.hSlot
  have hOneTime : lifecycle.responder_one_time_key { storeB with last_resort_seen := seen }
      p.decoded.one_time_prekey_id = ok (core.result.Result.Ok p.oneTime) := p.hOneTime
  have hDecaps : lifecycle.responder_decapsulate { storeB with last_resort_seen := seen } p.kemSlot
      p.decoded.kem_ciphertext.deref = ok (core.result.Result.Ok p.kemSecret) := p.hDecaps
  have hrep := replay_refused_of_mem { storeB with last_resort_seen := seen } p.decoded.kem_prekey_id p.secret fp
    hfp ⟨(kemId, fp), by simp [hseen], rfl⟩
  obtain ⟨ik, enc, hik, henc, hsh⟩ := p.hShared
  exact Tacenta.UnitLifecycleResponderFirstFrame.establish_responder_replay_refused_at rcB crcB ourB _ msg rng
    p.decoded p.hDecode p.signedSecret hSigned p.kemSlot true hSlot p.peerIdentity p.peerEphemeral p.hCurve
    p.oneTime hOneTime p.kemSecret hDecaps p.kemSecretZ p.hKemSecretZ p.signedBytes p.hSignedBytes
    p.signedPrekey p.hSignedPrekey ik hik enc henc p.shared hsh p.secretZ p.hSecretZ p.secret p.hSecret _ hrep


open Tacenta.UnitLifecycleT3 (DhView DhCodecOf vecOf sliceOf arrayOf CodewordViewSendOf)
open Tacenta.UnitLifecycleEstablishInitiatorShape (DhPublicValid establishedModelOf)
open Tacenta.UnitLifecycleResponderFirstFrame (InitiatorSecretParts)
open Tacenta.UnitLifecycleT3 (OracleOf BraidSendRefinementContracts TripleSendRefinementContracts KemView) in
/-- **The initiator's first frame, delivered to `establish_responder` a second time, is refused as a replay with no
durable effect.**  For every successful first `encrypt` at an establishment output (the hypotheses of
`established_encrypt_outcomes`), every responder identity and prekey store whose `publish` returned the bundle the
initiator used, when that bundle names the store's last-resort KEM key (`hlast`) and no one-time curve prekey
(`hnoOneTime`), and every successful return `(Ok (sB', ptB), storeB', rngB')` of `establish_responder` on the bytes
the initiator emitted: the call's parts `p` take the last-resort path, `storeB'` is `storeB` with only its replay
record changed, that record is the old one with `(kem_id, fp)` appended for the fingerprint `fp` of the shared secret
`p` computed, and `establish_responder` on the same bytes at `storeB'` returns `ReplayedLastResort` with `storeB'` and
the source as given, from every source.  Under the zeroizing round trip and `DhPublicValid`, which read the decoded
identifiers back.  The first call's success is a hypothesis: the statement does not depend on why it succeeded. -/
theorem initiator_first_send_responder_replay_refused [Tacenta.SessionUnitT1.DerivedKeysModel] {R E F : Type}
    (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R)
    (trace : R → List Model.Lifecycle.Key) (dh : DhView) (kem : KemView)
    (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle)
    (braid : BraidSendRefinementContracts rc oracle.braidKem)
    (triple : TripleSendRefinementContracts)
    (aead : Tacenta.UnitLifecycleT1.AeadSealBounded) (dhCodec : Tacenta.UnitLifecycleT1.DhCodecTotal)
    (oracleOf : OracleOf rc crc dh kem trace oracle) (codec : DhCodecOf dh)
    (codewordView : CodewordViewSendOf view)
    (hz80 : Tacenta.SessionUnitT3.ZeroizingRoundTrips80)
    (hz32 : Tacenta.UnitLifecycleT3.ZeroizingRoundTrips (Array Std.U8 32#usize))
    (hzKeys : Tacenta.UnitLifecycleT3.ZeroizingRoundTrips
      (Array Std.U8 32#usize × Array Std.U8 32#usize × Array Std.U8 16#usize))
    (hgen : Tacenta.UnitLifecycleEstablishedEncrypt.KeyGenSeededFor oracle.braidKem rc crc trace)
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
    (hzB : Tacenta.SessionUnitBraidT1.ZeroizingArrayRoundTrip) (hpub : DhPublicValid)
    (ourB : lifecycle.Identity) (storeB : lifecycle.PrekeyStore)
    (hpublish : lifecycle.PrekeyStore.publish storeB = ok bundleA)
    (hidentity : lifecycle.Identity.public ourB = ok storeB.identity_public)
    (hlast : bundleA.kem_prekey_id = storeB.kem_id)
    (hnoOneTime : bundleA.one_time_prekey_id = serialization.ABSENT_ID)
    (rngB : F) (ptB : alloc.vec.Vec U8) (sB' : lifecycle.Session) (storeB' : lifecycle.PrekeyStore) (rngB' : F)
    (hcallB : lifecycle.establish_responder rcB crcB ourB storeB (alloc.vec.Vec.deref bytes) rngB =
      ok (core.result.Result.Ok (sB', ptB), storeB', rngB')) :
    ∃ (p : ResponderPreparedParts ourB storeB (alloc.vec.Vec.deref bytes)) (fp : Array U8 32#usize),
      p.lastResort = true ∧ lifecycle.last_resort_fingerprint p.secret = ok fp ∧
      storeB' = { storeB with last_resort_seen := storeB'.last_resort_seen } ∧
      storeB'.last_resort_seen.val = storeB.last_resort_seen.val.concat (storeB.kem_id, fp) ∧
      ∀ rngB2 : F, lifecycle.establish_responder rcB crcB ourB storeB' (alloc.vec.Vec.deref bytes) rngB2 =
        ok (core.result.Result.Err lifecycle.Error.ReplayedLastResort, storeB', rngB2) := by
  obtain ⟨output, hcall', -, hcases⟩ := Tacenta.UnitLifecycleEstablishedEncrypt.established_encrypt_outcomes rc
    crc trace dh kem view oracle braid triple aead dhCodec oracleOf codec codewordView hz80 hz32 hzKeys hgen
    hct hbound rcE crcE ourA bundleA expected rng0 rng1 s h plaintext hroom rng htrace d1 d2 rest hdraws
  rw [hcall] at hcall'
  cases hcall'
  rcases hcases with ⟨-, hres, -⟩ | ⟨dk, ekSeed, ekVector, -, bytes', hres, -, -, tripleNext, messageKey,
    chunk, encoder, pending, a, -, -, -, hpend, hwire, -⟩
  · cases hres
  simp only [core.result.Result.Ok.injEq] at hres
  subst hres
  subst hq
  -- the first call's success: parts, and the commit
  rcases Tacenta.UnitLifecycleEstablishResponder.establish_responder_cases rcB crcB ourB storeB _ rngB _ hcallB with
    ⟨e, -, hout⟩ | ⟨p, inner, -, ⟨e, -, hout⟩ | ⟨pt, store1, -, hcommit, hout⟩⟩
  · cases hout
  · cases hout
  simp only [Prod.mk.injEq] at hout
  obtain ⟨-, rfl, -⟩ := hout
  obtain ⟨hkid, hoid, -, -⟩ := Tacenta.UnitLifecycleResponderFirstReceipt.parts_of_first_frame hzB hpub codec hct
    hbound q pending hpend _ _ hwire ourB storeB hpublish hidentity p
  -- the last-resort path
  have hlr : p.lastResort = true := by
    have hs := p.hSlot
    rw [hkid, hlast, Tacenta.UnitLifecycleResponderFirstFrame.kem_slot_last_resort] at hs
    split at hs
    · cases hs
    · simp only [ok.injEq, core.result.Result.Ok.injEq, Prod.mk.injEq] at hs
      exact hs.2.symm
  obtain ⟨-, hsome⟩ := Tacenta.UnitLifecycleEstablishResponder.replay_ok _ _ _ _ _ p.hReplay
  obtain ⟨fp, hfp, hfpv⟩ := hsome hlr
  rw [hkid, hoid, hlast, hnoOneTime, hlr, hfp] at hcommit
  obtain ⟨seen, hseen, hst⟩ := commit_last_resort storeB _ _ fp hcommit
  refine ⟨p, fp, hlr, hfpv, by rw [hst], by rw [hst]; exact hseen, fun rngB2 => ?_⟩
  exact establish_responder_again_refused rcB crcB p hlr storeB.kem_id fp hfpv _ hcommit rngB2


section Reach
open Tacenta.UnitLifecycleT3 (DhView)
open Tacenta.UnitLifecycleDecryptRatchetT3 (DecryptOracleOf DecryptRatchetAgreements)
open Tacenta.UnitLifecycleResponderFirstFrame (DhAgreeSymmetric PrekeyIdsDistinct FirstKemAgrees)
open Tacenta.UnitLifecycleResponderFirstReceipt (DhAgreeContributory AeadRoundTrip initiator_first_send_responder_receives)
open Tacenta.UnitSatisfiabilityJoint (Interp Interp.real)
open Tacenta.UnitLifecycleIntegrationScreen (byteRng byteCrc byteTrace)
open Tacenta.UnitLifecycleResponderFirstFrame (FirstFrameSuccessShape PoolEntry reachStore reachBundle
  publish_reachStore reachStore_distinct reach_establishment heldKemPair zPool)
open Tacenta.UnitSatisfiabilityJoint (InitiatorAxiom ResponderAxiom) in
open Tacenta.UnitLifecycleEstablishedEncrypt (EstablishedEncryptHypotheses EncryptExtraLaws emptyPlaintext) in
/-- **The reach of the refused second delivery**: at the real constants, under the laws of
`first_send_receive_reachable` (all assumed), for every initiator identity and every 64-byte source at whose bytes
the model's key generation answers, there are a prekey store, its owner and the bundle it publishes (naming the
store's last-resort KEM key and no one-time curve prekey; the replay record empty), a successful establishment, a
first send of the empty plaintext that returns bytes, and a successful `establish_responder` on those bytes, after
which the replay record holds exactly `(kem_id, fp)`, and `establish_responder` on the same bytes at the store that
call left returns `ReplayedLastResort`, that store and the source as given, from every source.  It reruns the proof
of `first_send_receive_reachable`, which keeps the store and the bundle hidden, and applies
`initiator_first_send_responder_replay_refused` to the run.  Last-resort path only. -/
theorem first_send_replay_refused_reachable (K : Model.Braid.Kem) (dh : DhView)
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
      (storeB' : lifecycle.PrekeyStore) (rngB' : List Std.U8) (fp : Array U8 32#usize),
      oracle.braidKem = K ∧
      lifecycle.Session.encrypt byteRng byteCrc q.session emptyPlaintext seed =
        ok (core.result.Result.Ok bytes, s', rng') ∧
      lifecycle.PrekeyStore.publish storeB = ok bundle ∧
      bundle.kem_prekey_id = storeB.kem_id ∧ bundle.one_time_prekey_id = serialization.ABSENT_ID ∧
      storeB.last_resort_seen.val = [] ∧
      lifecycle.establish_responder byteRng byteCrc ourB storeB (alloc.vec.Vec.deref bytes) seed =
        ok (core.result.Result.Ok (sB', ptB), storeB', rngB') ∧
      storeB'.last_resort_seen.val = [(storeB.kem_id, fp)] ∧
      ∀ rngB2 : List Std.U8,
        lifecycle.establish_responder byteRng byteCrc ourB storeB' (alloc.vec.Vec.deref bytes) rngB2 =
          ok (core.result.Result.Err lifecycle.Error.ReplayedLastResort, storeB', rngB2) := by
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
  -- the encrypt record at that establishment, from the joint construction of the encrypt branch
  obtain ⟨oracle, bundle0, s0, rng10, hK, hdraws0, H0⟩ :=
    Tacenta.UnitLifecycleEstablishedEncrypt.established_encrypt_hypotheses_jointly_satisfiable K dh kem L A S
      hpub hct X ourA seed (by omega)
  have H : EstablishedEncryptHypotheses byteRng byteCrc byteTrace dh kem
      Tacenta.UnitLifecycleRepair.witnessView oracle byteRng byteCrc ourA (reachBundle pkb sig1 sig2 kemPk)
      (reachBundle pkb sig1 sig2 kemPk).bundle.identity_key (List.replicate 32 0#u8 ++ stream) rng1 q.session
      emptyPlaintext seed :=
    { braid := H0.braid, triple := H0.triple, derivedKeys := H0.derivedKeys, aead := H0.aead,
      dhCodec := H0.dhCodec, oracleOf := H0.oracleOf, codec := H0.codec, codewordView := H0.codewordView,
      zeroizing80 := H0.zeroizing80, zeroizing32 := H0.zeroizing32, zeroizingKeys := H0.zeroizingKeys,
      keyGen := H0.keyGen, kemCiphertextLen := H0.kemCiphertextLen,
      kemCiphertextBound := H0.kemCiphertextBound, established := h, room := H0.room,
      trace_eq := H0.trace_eq, draws := H0.draws }
  obtain ⟨inst⟩ := H.derivedKeys
  subst hK
  -- the first send's success
  obtain ⟨output, hcall, -, hcases⟩ := Tacenta.UnitLifecycleEstablishedEncrypt.established_encrypt_outcomes
    byteRng byteCrc byteTrace dh kem Tacenta.UnitLifecycleRepair.witnessView oracle H.braid H.triple H.aead
    H.dhCodec H.oracleOf H.codec H.codewordView H.zeroizing80 H.zeroizing32 H.zeroizingKeys H.keyGen
    H.kemCiphertextLen H.kemCiphertextBound byteRng byteCrc ourA _ _ _ rng1 q.session H.established
    emptyPlaintext H.room seed H.trace_eq _ _ _
    (Tacenta.UnitLifecycleEstablishedEncrypt.byteTrace_two seed (by omega))
  rw [Tacenta.UnitLifecycleEstablishedEncrypt.two_draws_of_64 seed hseed] at hcases
  obtain ⟨res, s', rng'⟩ := output
  rcases hcases with ⟨hnone, -⟩ | ⟨dk, ekSeed, ekVector, -, bytes, hres, -⟩
  · exact absurd hnone hkg
  simp only at hres
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
  have D := (Tacenta.UnitLifecycleEstablishedDecrypt.established_decrypt_hypotheses_jointly_satisfiable
    oracle.braidKem dh L A S hpub hct ourA)
  obtain ⟨oracle0, bundle1, s1, rng11, hK0, H1⟩ := D
  have ag : DecryptRatchetAgreements oracle.braidKem :=
    hK0 ▸ (H1 Tacenta.UnitLifecycleRepair.witnessView).agreements
  have oracleOfB : DecryptOracleOf byteRng byteCrc dh byteTrace oracle :=
    DecryptOracleOf.of_oracleOf H.oracleOf
  obtain ⟨d1, d2, rest2, hdrB⟩ : ∃ d1 d2 rest2, byteTrace seed = d1 :: d2 :: rest2 := by
    have := Tacenta.UnitLifecycleEstablishedEncrypt.byteTrace_two seed (by omega)
    exact ⟨_, _, _, this⟩
  obtain ⟨-, hdisj⟩ := initiator_first_send_responder_receives byteRng byteCrc byteTrace dh kem
    Tacenta.UnitLifecycleRepair.witnessView oracle H.braid H.triple H.aead H.dhCodec H.oracleOf H.codec
    H.codewordView H.zeroizing80 H.zeroizing32 H.zeroizingKeys H.keyGen hsizes H.kemCiphertextLen
    H.kemCiphertextBound byteRng byteCrc ourA _ _ _ rng1 q.session h q rfl emptyPlaintext H.room seed
    H.trace_eq _ _ _ (Tacenta.UnitLifecycleEstablishedEncrypt.byteTrace_two seed (by omega)) bytes s' rng'
    hcall byteRng byteCrc contracts hpub hsym hcon haead hrt L.optionEq byteTrace oracle oracleOfB ag ourB
    storeB hpublish hidentity hdistinct hkem hhead seed H.trace_eq d1 (d2 :: rest2) hdrB
  rcases hdisj with ⟨-, e, hrefuse, -⟩ |
    ⟨p, ec, dSend, dk', ekSeed', ekVector', ptB, sB', storeB', rngB', -, -, -, -, -, -, -, -, -, -, hcallB, hpt, -⟩
  · exfalso
    rcases hrefuse with ⟨-, hleg⟩ | ⟨-, fp, -, x, hx, -⟩ | ⟨-, -, hne, -⟩
    · simp [storeB, reachStore] at hleg
    · simp [storeB, reachStore] at hx
    · exact hne (by simp [storeB, reachStore])
  · obtain ⟨-, fp, -, -, -, hseen, hrep⟩ := initiator_first_send_responder_replay_refused byteRng byteCrc byteTrace
      dh kem Tacenta.UnitLifecycleRepair.witnessView oracle H.braid H.triple H.aead H.dhCodec H.oracleOf H.codec
      H.codewordView H.zeroizing80 H.zeroizing32 H.zeroizingKeys H.keyGen H.kemCiphertextLen H.kemCiphertextBound
      byteRng byteCrc ourA _ _ _ rng1 q.session h q rfl emptyPlaintext H.room seed H.trace_eq _ _ _
      (Tacenta.UnitLifecycleEstablishedEncrypt.byteTrace_two seed (by omega)) bytes s' rng' hcall byteRng byteCrc
      contracts.decrypt.braid.zeroizingArray hpub ourB storeB hpublish hidentity (by simp [storeB, reachStore, reachBundle])
      (by simp [reachBundle]) seed ptB sB' storeB' rngB' hcallB
    refine ⟨oracle, _, q, bytes, s', rng', ourB, storeB, sB', ptB, storeB', rngB', fp, rfl, hcall, hpublish,
      by simp [storeB, reachStore, reachBundle], by simp [reachBundle], by simp [storeB, reachStore], hcallB, ?_, hrep⟩
    rw [hseen]
    simp [storeB, reachStore]
end Reach

end Tacenta.UnitLifecycleResponderEstablishReplay

/-! ## Pins

The constants each result depends on, and the statement of each result and definition, held by the
build.  `attest.py` requires every one of them (`REQUIRED_PINS`, `REQUIRED_STATEMENT_PINS`,
`REQUIRED_PRINT_FORM`). -/

/--
info: 'Tacenta.UnitLifecycleResponderEstablishReplay.replay_refused_of_mem' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_boundary.kem.KeyPair]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleResponderEstablishReplay.replay_refused_of_mem

/--
info: 'Tacenta.UnitLifecycleResponderEstablishReplay.commit_last_resort' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_boundary.kem.KeyPair,
 tacenta_session_unit.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.Pair.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.alloc.vec.Vec.pop,
 tacenta_session_unit.zeroize.Zeroize.Blanket.zeroize,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 tacenta_session_unit.alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleResponderEstablishReplay.commit_last_resort

/--
info: 'Tacenta.UnitLifecycleResponderEstablishReplay.establish_responder_again_refused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kem.CT1_LEN,
 tacenta_session_unit.tacenta_kem.CT2_LEN,
 tacenta_session_unit.tacenta_kem.EK_VECTOR_LEN,
 tacenta_session_unit.tacenta_kem.EncapsState,
 tacenta_session_unit.tacenta_kem.HEADER_LEN,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair,
 tacenta_session_unit.tacenta_kem.encapsulate2,
 tacenta_session_unit.tacenta_kem.validate_ek,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.rand_core_1.error.Error,
 tacenta_session_unit.tacenta_boundary.aead.decrypt,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_boundary.dh.is_prime_order_public,
 tacenta_session_unit.tacenta_boundary.kem.KeyPair,
 tacenta_session_unit.tacenta_boundary.kem.decapsulate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.ek_vector,
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
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.from_bytes,
 tacenta_session_unit.zeroize.Zeroize.Blanket.zeroize,
 tacenta_session_unit.tacenta_kem.EncapsState.Insts.CoreCloneClone.clone,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 tacenta_session_unit.alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.core.option.Option.Insts.CoreCloneClone.clone,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleResponderEstablishReplay.establish_responder_again_refused

/--
info: 'Tacenta.UnitLifecycleResponderEstablishReplay.initiator_first_send_responder_replay_refused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
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
 tacenta_session_unit.tacenta_boundary.aead.encrypt,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_boundary.dh.is_prime_order_public,
 tacenta_session_unit.tacenta_boundary.kem.KeyPair,
 tacenta_session_unit.tacenta_boundary.kem.ciphertext_len,
 tacenta_session_unit.tacenta_boundary.kem.decapsulate,
 tacenta_session_unit.tacenta_boundary.kem.encapsulate,
 tacenta_session_unit.tacenta_boundary.xeddsa.sign,
 tacenta_session_unit.tacenta_boundary.xeddsa.verify,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.generate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.header,
 tacenta_session_unit.zeroize.Zeroizing.new,
 tacenta_session_unit.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.Pair.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.TupleABC.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.alloc.vec.Vec.capacity,
 tacenta_session_unit.alloc.vec.Vec.is_empty,
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
 tacenta_session_unit.tacenta_boundary.kem.KeyPair.public_key,
 tacenta_session_unit.zeroize.Zeroize.Blanket.zeroize,
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
#print axioms Tacenta.UnitLifecycleResponderEstablishReplay.initiator_first_send_responder_replay_refused

/--
info: 'Tacenta.UnitLifecycleResponderEstablishReplay.first_send_replay_refused_reachable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
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
 tacenta_session_unit.tacenta_boundary.aead.encrypt,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_boundary.dh.is_prime_order_public,
 tacenta_session_unit.tacenta_boundary.kem.KeyPair,
 tacenta_session_unit.tacenta_boundary.kem.ciphertext_len,
 tacenta_session_unit.tacenta_boundary.kem.decapsulate,
 tacenta_session_unit.tacenta_boundary.kem.encapsulate,
 tacenta_session_unit.tacenta_boundary.xeddsa.sign,
 tacenta_session_unit.tacenta_boundary.xeddsa.verify,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.generate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.header,
 tacenta_session_unit.zeroize.Zeroizing.new,
 tacenta_session_unit.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.Pair.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.TupleABC.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.alloc.vec.Vec.capacity,
 tacenta_session_unit.alloc.vec.Vec.is_empty,
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
 tacenta_session_unit.tacenta_boundary.kem.KeyPair.public_key,
 tacenta_session_unit.zeroize.Zeroize.Blanket.zeroize,
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
#print axioms Tacenta.UnitLifecycleResponderEstablishReplay.first_send_replay_refused_reachable

set_option pp.deepTerms true
set_option pp.proofs.withType true

/--
info: Tacenta.UnitLifecycleResponderEstablishReplay.replay_refused_of_mem : ∀
  (store : tacenta_session_unit.lifecycle.PrekeyStore) (kemId : Aeneas.Std.U32)
  (sk fp : Aeneas.Std.Array Aeneas.Std.U8 32#usize),
  tacenta_session_unit.lifecycle.last_resort_fingerprint sk = Aeneas.Std.Result.ok fp →
    (∃ x ∈ ↑store.last_resort_seen, x.2 = fp) →
      tacenta_session_unit.lifecycle.responder_replay_fingerprint store kemId sk true =
        Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Err tacenta_session_unit.lifecycle.Error.ReplayedLastResort)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderEstablishReplay.replay_refused_of_mem

/--
info: Tacenta.UnitLifecycleResponderEstablishReplay.commit_last_resort : ∀
  (store store' : tacenta_session_unit.lifecycle.PrekeyStore) (kemId : Aeneas.Std.U32)
  (fp : Aeneas.Std.Array Aeneas.Std.U8 32#usize),
  Tacenta.UnitLifecycleEstablishResponder.ResponderCommit store kemId tacenta_session_unit.serialization.ABSENT_ID true
      (some fp) store' →
    ∃ seen,
      ↑seen = (↑store.last_resort_seen).concat (kemId, fp) ∧
        store' =
          { identity_public := store.identity_public, signed_prekey_secret := store.signed_prekey_secret,
            signed_prekey_id := store.signed_prekey_id, signed_prekey_sig := store.signed_prekey_sig,
            one_time := store.one_time, kem := store.kem, kem_id := store.kem_id, kem_sig := store.kem_sig,
            kem_one_time := store.kem_one_time, previous_signed_prekey := store.previous_signed_prekey,
            previous_kem := store.previous_kem, next_id := store.next_id, last_resort_seen := seen,
            legacy_last_resort_blocked := store.legacy_last_resort_blocked }
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderEstablishReplay.commit_last_resort

/--
info: @Tacenta.UnitLifecycleResponderEstablishReplay.establish_responder_again_refused : ∀ {E : Type}
  (rcB : tacenta_session_unit.rand_core_1.RngCore E) (crcB : tacenta_session_unit.rand_core_1.CryptoRng E)
  {ourB : tacenta_session_unit.lifecycle.Identity} {storeB : tacenta_session_unit.lifecycle.PrekeyStore}
  {msg : Aeneas.Std.Slice Aeneas.Std.U8}
  (p : Tacenta.UnitLifecycleEstablishResponder.ResponderPreparedParts ourB storeB msg),
  p.lastResort = true →
    ∀ (kemId : Aeneas.Std.U32) (fp : Aeneas.Std.Array Aeneas.Std.U8 32#usize),
      tacenta_session_unit.lifecycle.last_resort_fingerprint p.secret = Aeneas.Std.Result.ok fp →
        ∀ (storeB' : tacenta_session_unit.lifecycle.PrekeyStore),
          Tacenta.UnitLifecycleEstablishResponder.ResponderCommit storeB kemId
              tacenta_session_unit.serialization.ABSENT_ID true (some fp) storeB' →
            ∀ (rng : E),
              tacenta_session_unit.lifecycle.establish_responder rcB crcB ourB storeB' msg rng =
                Aeneas.Std.Result.ok
                  (Aeneas.Std.core.result.Result.Err tacenta_session_unit.lifecycle.Error.ReplayedLastResort, storeB',
                    rng)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderEstablishReplay.establish_responder_again_refused

/--
info: @Tacenta.UnitLifecycleResponderEstablishReplay.initiator_first_send_responder_replay_refused : ∀
  [Tacenta.SessionUnitT1.DerivedKeysModel] {R E F : Type} (rc : tacenta_session_unit.rand_core_1.RngCore R)
  (crc : tacenta_session_unit.rand_core_1.CryptoRng R) (trace : R → List Model.Lifecycle.Key)
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
                  Tacenta.UnitLifecycleT3.ZeroizingRoundTrips (Aeneas.Std.Array Aeneas.Std.U8 32#usize) →
                    Tacenta.UnitLifecycleT3.ZeroizingRoundTrips
                        (Aeneas.Std.Array Aeneas.Std.U8 32#usize ×
                          Aeneas.Std.Array Aeneas.Std.U8 32#usize × Aeneas.Std.Array Aeneas.Std.U8 16#usize) →
                      Tacenta.UnitLifecycleEstablishedEncrypt.KeyGenSeededFor oracle.braidKem rc crc trace →
                        Tacenta.UnitLifecycleEstablishInitiatorShape.KemCiphertextLenOf →
                          Tacenta.UnitLifecycleRestoredSession.KemCiphertextLenBound →
                            ∀ (rcE : tacenta_session_unit.rand_core_1.RngCore E)
                              (crcE : tacenta_session_unit.rand_core_1.CryptoRng E)
                              (ourA : tacenta_session_unit.lifecycle.Identity)
                              (bundleA : tacenta_session_unit.lifecycle.PublishedBundle)
                              (expected : tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes) (rng0 rng1 : E)
                              (s : tacenta_session_unit.lifecycle.Session),
                              tacenta_session_unit.lifecycle.establish_initiator_for rcE crcE ourA bundleA expected
                                    rng0 =
                                  Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok s, rng1) →
                                ∀
                                  (q :
                                    Tacenta.UnitLifecycleResponderFirstFrame.InitiatorSecretParts rcE crcE ourA
                                      bundleA),
                                  s = q.session →
                                    ∀ (plaintext : Aeneas.Std.Slice Aeneas.Std.U8),
                                      (↑plaintext).length + 65770 ≤ Aeneas.Std.Usize.max →
                                        ∀ (rng : R),
                                          trace rng = oracle.draws →
                                            ∀ (d1 d2 : Model.Lifecycle.Key) (rest : List Model.Lifecycle.Key),
                                              trace rng = d1 :: d2 :: rest →
                                                ∀ (bytes : Aeneas.Std.alloc.vec.Vec Aeneas.Std.U8)
                                                  (s' : tacenta_session_unit.lifecycle.Session) (rng' : R),
                                                  tacenta_session_unit.lifecycle.Session.encrypt rc crc s plaintext
                                                        rng =
                                                      Aeneas.Std.Result.ok
                                                        (Aeneas.Std.core.result.Result.Ok bytes, s', rng') →
                                                    ∀ (rcB : tacenta_session_unit.rand_core_1.RngCore F)
                                                      (crcB : tacenta_session_unit.rand_core_1.CryptoRng F),
                                                      Tacenta.SessionUnitBraidT1.ZeroizingArrayRoundTrip →
                                                        Tacenta.UnitLifecycleEstablishInitiatorShape.DhPublicValid →
                                                          ∀ (ourB : tacenta_session_unit.lifecycle.Identity)
                                                            (storeB : tacenta_session_unit.lifecycle.PrekeyStore),
                                                            storeB.publish = Aeneas.Std.Result.ok bundleA →
                                                              ourB.public =
                                                                  Aeneas.Std.Result.ok storeB.identity_public →
                                                                bundleA.kem_prekey_id = storeB.kem_id →
                                                                  bundleA.one_time_prekey_id =
                                                                      tacenta_session_unit.serialization.ABSENT_ID →
                                                                    ∀ (rngB : F)
                                                                      (ptB : Aeneas.Std.alloc.vec.Vec Aeneas.Std.U8)
                                                                      (sB' : tacenta_session_unit.lifecycle.Session)
                                                                      (storeB' :
                                                                        tacenta_session_unit.lifecycle.PrekeyStore)
                                                                      (rngB' : F),
                                                                      tacenta_session_unit.lifecycle.establish_responder
                                                                            rcB crcB ourB storeB bytes.deref rngB =
                                                                          Aeneas.Std.Result.ok
                                                                            (Aeneas.Std.core.result.Result.Ok
                                                                                (sB', ptB),
                                                                              storeB', rngB') →
                                                                        ∃ p fp,
                                                                          p.lastResort = true ∧
                                                                            tacenta_session_unit.lifecycle.last_resort_fingerprint
                                                                                  p.secret =
                                                                                Aeneas.Std.Result.ok fp ∧
                                                                              storeB' =
                                                                                  {
                                                                                    identity_public :=
                                                                                      storeB.identity_public,
                                                                                    signed_prekey_secret :=
                                                                                      storeB.signed_prekey_secret,
                                                                                    signed_prekey_id :=
                                                                                      storeB.signed_prekey_id,
                                                                                    signed_prekey_sig :=
                                                                                      storeB.signed_prekey_sig,
                                                                                    one_time := storeB.one_time,
                                                                                    kem := storeB.kem,
                                                                                    kem_id := storeB.kem_id,
                                                                                    kem_sig := storeB.kem_sig,
                                                                                    kem_one_time := storeB.kem_one_time,
                                                                                    previous_signed_prekey :=
                                                                                      storeB.previous_signed_prekey,
                                                                                    previous_kem := storeB.previous_kem,
                                                                                    next_id := storeB.next_id,
                                                                                    last_resort_seen :=
                                                                                      storeB'.last_resort_seen,
                                                                                    legacy_last_resort_blocked :=
                                                                                      storeB.legacy_last_resort_blocked } ∧
                                                                                ↑storeB'.last_resort_seen =
                                                                                    (↑storeB.last_resort_seen).concat
                                                                                      (storeB.kem_id, fp) ∧
                                                                                  ∀ (rngB2 : F),
                                                                                    tacenta_session_unit.lifecycle.establish_responder
                                                                                        rcB crcB ourB storeB'
                                                                                        bytes.deref rngB2 =
                                                                                      Aeneas.Std.Result.ok
                                                                                        (Aeneas.Std.core.result.Result.Err
                                                                                            tacenta_session_unit.lifecycle.Error.ReplayedLastResort,
                                                                                          storeB', rngB2)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderEstablishReplay.initiator_first_send_responder_replay_refused

/--
info: Tacenta.UnitLifecycleResponderEstablishReplay.first_send_replay_refused_reachable : ∀ (K : Model.Braid.Kem)
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
                        Tacenta.UnitSatisfiabilityJoint.Interp.real
                        tacenta_session_unit.tacenta_boundary.kem.KeyPair.public_key
                        @tacenta_session_unit.alloc.vec.Vec.is_empty →
                      Tacenta.UnitLifecycleEstablishedEncrypt.KeyGenSizesOf K →
                        Tacenta.UnitLifecycleResponderFirstReceipt.DhAgreeContributory →
                          Tacenta.UnitLifecycleResponderFirstReceipt.AeadRoundTrip →
                            ∀ (ourA : tacenta_session_unit.lifecycle.Identity) (seed : List Aeneas.Std.U8),
                              seed.length = 64 →
                                K.keyGen
                                      (Model.Lifecycle.braidRandomness (List.map Tacenta.SessionUnitBraidT3.u8 seed)) ≠
                                    none →
                                  ∃ oracle bundle q bytes s' rng' ourB storeB sB' ptB storeB' rngB' fp,
                                    oracle.braidKem = K ∧
                                      tacenta_session_unit.lifecycle.Session.encrypt
                                            Tacenta.UnitLifecycleIntegrationScreen.byteRng
                                            Tacenta.UnitLifecycleIntegrationScreen.byteCrc q.session
                                            Tacenta.UnitLifecycleEstablishedEncrypt.emptyPlaintext seed =
                                          Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok bytes, s', rng') ∧
                                        storeB.publish = Aeneas.Std.Result.ok bundle ∧
                                          bundle.kem_prekey_id = storeB.kem_id ∧
                                            bundle.one_time_prekey_id = tacenta_session_unit.serialization.ABSENT_ID ∧
                                              ↑storeB.last_resort_seen = [] ∧
                                                tacenta_session_unit.lifecycle.establish_responder
                                                      Tacenta.UnitLifecycleIntegrationScreen.byteRng
                                                      Tacenta.UnitLifecycleIntegrationScreen.byteCrc ourB storeB
                                                      bytes.deref seed =
                                                    Aeneas.Std.Result.ok
                                                      (Aeneas.Std.core.result.Result.Ok (sB', ptB), storeB', rngB') ∧
                                                  ↑storeB'.last_resort_seen = [(storeB.kem_id, fp)] ∧
                                                    ∀ (rngB2 : List Aeneas.Std.U8),
                                                      tacenta_session_unit.lifecycle.establish_responder
                                                          Tacenta.UnitLifecycleIntegrationScreen.byteRng
                                                          Tacenta.UnitLifecycleIntegrationScreen.byteCrc ourB storeB'
                                                          bytes.deref rngB2 =
                                                        Aeneas.Std.Result.ok
                                                          (Aeneas.Std.core.result.Result.Err
                                                              tacenta_session_unit.lifecycle.Error.ReplayedLastResort,
                                                            storeB', rngB2)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderEstablishReplay.first_send_replay_refused_reachable
