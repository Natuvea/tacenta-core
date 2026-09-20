import Translation.UnitLifecycleT1
import Translation.SessionUnitBraidT1
import Translation.SessionUnitBraidImportInv

/-!
# Public Session lifecycle T1 proofs

The eviction retry is proved in `UnitLifecycleT1` without importing the Braid
proof package, whose local stepping configuration intentionally differs from
the wire proofs in that module. This file composes those already checked
layers for the five public lifecycle entry points.
-/

namespace Tacenta.UnitLifecycleT1

open Aeneas Aeneas.Std Result
open tacenta_session_unit

@[step]
theorem is_canonical_key_no_panic (hdh : DhCodecTotal)
    (pk : tacenta_boundary.dh.PublicKeyBytes) :
    is_canonical_key pk ⦃ fun _ => True ⦄ := by
  unfold is_canonical_key
  step with public_key_as_bytes_no_panic hdh pk
  exact WP.spec_mono
    (Tacenta.SessionUnitSessionT1.is_canonical_x25519_spec a) (by simp)

@[step]
theorem decode_ec_no_panic (hdh : DhCodecTotal) (bytes : Slice U8) :
    decode_ec bytes ⦃ fun _ => True ⦄ := by
  unfold decode_ec
  step with Tacenta.SessionUnitSessionT1.decode_ec_spec bytes
  split
  · simp
  · step with public_key_from_bytes_no_panic hdh

@[step]
theorem identity_dh_key_no_panic (hdh : DhCodecTotal)
    (identity : lifecycle.Identity) :
    lifecycle.Identity.dh_key identity ⦃ fun _ => True ⦄ := by
  unfold lifecycle.Identity.dh_key
  exact private_key_from_bytes_no_panic hdh identity.secret

@[step]
theorem identity_public_no_panic (hdh : DhCodecTotal)
    (identity : lifecycle.Identity) :
    lifecycle.Identity.public identity ⦃ fun _ => True ⦄ := by
  unfold lifecycle.Identity.public
  step with identity_dh_key_no_panic hdh identity
  exact private_key_public_no_panic hdh pk

@[step]
theorem public_key_eq_no_panic (hdh : DhCodecTotal)
    (a b : tacenta_boundary.dh.PublicKeyBytes) :
    tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes.eq a b
      ⦃ fun _ => True ⦄ :=
  (Tacenta.SessionUnitT1.noPanic_iff _).2 (hdh.2.2.2.2.2 a b)

@[step]
theorem public_key_ne_no_panic (hdh : DhCodecTotal)
    (a b : tacenta_boundary.dh.PublicKeyBytes) :
    core.cmp.PartialEq.ne.trait_default
      tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes a b
      ⦃ fun _ => True ⦄ := by
  unfold core.cmp.PartialEq.ne.trait_default core.cmp.PartialEq.ne.default
  step with public_key_eq_no_panic hdh a b

@[step]
theorem encode_kem_no_panic (pk : Slice U8)
    (hroom : pk.val.length + 1 ≤ Usize.max) :
    encode_kem pk ⦃ fun _ => True ⦄ := by
  unfold encode_kem
  exact WP.spec_mono
    (Tacenta.SessionUnitSessionT1.encode_kem_spec pk hroom) (by simp)

theorem verify_bundle_no_panic (hdh : DhCodecTotal) (hx : XeddsaVerifyTotal)
    (bundle : PreKeyBundle)
    (hkem : bundle.kem_prekey.val.length + 1 ≤ Usize.max) :
    verify_bundle bundle ⦃ fun _ => True ⦄ := by
  unfold verify_bundle
  step with encode_ec_spec hdh bundle.signed_prekey
  step with xeddsa_verify_no_panic hx bundle.identity_key v.deref
    bundle.signed_prekey_signature
  rcases r with _ | _
  · step with encode_kem_no_panic bundle.kem_prekey.deref hkem
    rename_i encodedKem
    step with xeddsa_verify_no_panic hx bundle.identity_key encodedKem.deref
      bundle.kem_prekey_signature
    rcases r1 <;> simp
  · simp

theorem verify_bundle_with_one_time_no_panic
    (hdh : DhCodecTotal) (hx : XeddsaVerifyTotal) (bundle : PreKeyBundle)
    {oneTime : Option tacenta_boundary.dh.PublicKeyBytes}
    (hkem : bundle.kem_prekey.val.length + 1 ≤ Usize.max) :
    verify_bundle { bundle with one_time_prekey := oneTime }
      ⦃ fun _ => True ⦄ :=
  verify_bundle_no_panic hdh hx _ hkem

@[step]
theorem contributory_no_panic (value : Option (Array U8 32#usize)) :
    contributory value ⦃ fun _ => True ⦄ := by
  rcases value with _ | _ <;> simp [contributory]

theorem initiator_shared_secret_no_panic
    (hdh : DhCodecTotal) (hagree : DhAgreeTotal) (hx : XeddsaVerifyTotal)
    (hz : Tacenta.SessionUnitBraidT1.ZeroizingArrayRoundTrip)
    (hkdf : Tacenta.SessionUnitSessionT1.HkdfTotal)
    [Tacenta.SessionUnitSessionT1.ZeroizingModel]
    (identityPrivate ephemeralPrivate : tacenta_boundary.dh.PrivateKey)
    (bundle : PreKeyBundle) (encapsulated : Array U8 32#usize)
    (hkem : bundle.kem_prekey.val.length + 1 ≤ Usize.max) :
    initiator_shared_secret identityPrivate ephemeralPrivate bundle encapsulated
      ⦃ fun _ => True ⦄ := by
  unfold initiator_shared_secret
  step with verify_bundle_no_panic hdh hx bundle hkem
  rcases r with verified | verifyError
  · step with core.result.Result.Insts.CoreOpsTry.branch_Ok.spec verified
    simp only [cf_post]
    step with private_key_agree_no_panic hagree identityPrivate bundle.signed_prekey
    step with contributory_no_panic o
    rcases r1 with dh1Value | dh1Error
    · step with core.result.Result.Insts.CoreOpsTry.branch_Ok.spec dh1Value
      simp only [cf1_post]
      step with Tacenta.SessionUnitBraidT1.zeroizing_new_spec hz dh1Value
      step with private_key_agree_no_panic hagree ephemeralPrivate bundle.identity_key
      step with contributory_no_panic o1
      rcases r2 with dh2Value | dh2Error
      · step with core.result.Result.Insts.CoreOpsTry.branch_Ok.spec dh2Value
        simp only [cf2_post]
        step with Tacenta.SessionUnitBraidT1.zeroizing_new_spec hz dh2Value
        step with private_key_agree_no_panic hagree ephemeralPrivate bundle.signed_prekey
        step with contributory_no_panic o2
        rcases r3 with dh3Value | dh3Error
        · step with core.result.Result.Insts.CoreOpsTry.branch_Ok.spec dh3Value
          simp only [cf3_post]
          step with Tacenta.SessionUnitBraidT1.zeroizing_new_spec hz dh3Value
          rcases bundle.one_time_prekey with _ | opk
          · have hss := Tacenta.SessionUnitSessionT1.shared_secret_no_panic hkdf
              dh1Value dh2Value dh3Value encapsulated none
            obtain ⟨shared, hshared⟩ :=
              (Tacenta.SessionUnitT1.noPanic_iff _).mp hss
            simp [dh1_post, dh2_post, dh3_post, hshared]
          · step with private_key_agree_no_panic hagree ephemeralPrivate opk
            rename_i o3
            step with contributory_no_panic o3
            rcases r4 with dh4Value | dh4Error
            · step with core.result.Result.Insts.CoreOpsTry.branch_Ok.spec dh4Value
              simp only [cf4_post]
              step with Tacenta.SessionUnitBraidT1.zeroizing_new_spec hz dh4Value
              have hss := Tacenta.SessionUnitSessionT1.shared_secret_no_panic hkdf
                dh1Value dh2Value dh3Value encapsulated (some dh4Value)
              obtain ⟨shared, hshared⟩ :=
                (Tacenta.SessionUnitT1.noPanic_iff _).mp hss
              simp [dh1_post, dh2_post, dh3_post, secret_post, hshared]
            · step with core.result.Result.Insts.CoreOpsTry.branch_Err.spec dh4Error
              simp only [cf4_post]
              simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                core.convert.FromSame.from]
        · step with core.result.Result.Insts.CoreOpsTry.branch_Err.spec dh3Error
          simp only [cf3_post]
          simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
            core.convert.FromSame.from]
      · step with core.result.Result.Insts.CoreOpsTry.branch_Err.spec dh2Error
        simp only [cf2_post]
        simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
          core.convert.FromSame.from]
    · step with core.result.Result.Insts.CoreOpsTry.branch_Err.spec dh1Error
      simp only [cf1_post]
      simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
        core.convert.FromSame.from]
  · step with core.result.Result.Insts.CoreOpsTry.branch_Err.spec verifyError
    simp only [cf_post]
    simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
      core.convert.FromSame.from]

theorem initiator_shared_secret_with_one_time_no_panic
    (hdh : DhCodecTotal) (hagree : DhAgreeTotal) (hx : XeddsaVerifyTotal)
    (hz : Tacenta.SessionUnitBraidT1.ZeroizingArrayRoundTrip)
    (hkdf : Tacenta.SessionUnitSessionT1.HkdfTotal)
    [Tacenta.SessionUnitSessionT1.ZeroizingModel]
    (identityPrivate ephemeralPrivate : tacenta_boundary.dh.PrivateKey)
    (bundle : PreKeyBundle) {oneTime : Option tacenta_boundary.dh.PublicKeyBytes}
    (encapsulated : Array U8 32#usize)
    (hkem : bundle.kem_prekey.val.length + 1 ≤ Usize.max) :
    initiator_shared_secret identityPrivate ephemeralPrivate
      { bundle with one_time_prekey := oneTime } encapsulated
      ⦃ fun _ => True ⦄ :=
  initiator_shared_secret_no_panic hdh hagree hx hz hkdf _ _ _ _ hkem

theorem responder_shared_secret_no_panic
    (hagree : DhAgreeTotal)
    (hz : Tacenta.SessionUnitBraidT1.ZeroizingArrayRoundTrip)
    (hkdf : Tacenta.SessionUnitSessionT1.HkdfTotal)
    [Tacenta.SessionUnitSessionT1.ZeroizingModel]
    (identityPrivate signedPrekeyPrivate : tacenta_boundary.dh.PrivateKey)
    (oneTimePrekeyPrivate : Option tacenta_boundary.dh.PrivateKey)
    (initiatorIdentity initiatorEphemeral : tacenta_boundary.dh.PublicKeyBytes)
    (encapsulated : Array U8 32#usize) :
    responder_shared_secret identityPrivate signedPrekeyPrivate oneTimePrekeyPrivate
      initiatorIdentity initiatorEphemeral encapsulated ⦃ fun _ => True ⦄ := by
  unfold responder_shared_secret
  step with private_key_agree_no_panic hagree signedPrekeyPrivate initiatorIdentity
  step with contributory_no_panic o
  rcases r with dh1Value | dh1Error
  · step with core.result.Result.Insts.CoreOpsTry.branch_Ok.spec dh1Value
    simp only [cf_post]
    step with Tacenta.SessionUnitBraidT1.zeroizing_new_spec hz dh1Value
    step with private_key_agree_no_panic hagree identityPrivate initiatorEphemeral
    step with contributory_no_panic o1
    rcases r1 with dh2Value | dh2Error
    · step with core.result.Result.Insts.CoreOpsTry.branch_Ok.spec dh2Value
      simp only [cf1_post]
      step with Tacenta.SessionUnitBraidT1.zeroizing_new_spec hz dh2Value
      step with private_key_agree_no_panic hagree signedPrekeyPrivate initiatorEphemeral
      step with contributory_no_panic o2
      rcases r2 with dh3Value | dh3Error
      · step with core.result.Result.Insts.CoreOpsTry.branch_Ok.spec dh3Value
        simp only [cf2_post]
        step with Tacenta.SessionUnitBraidT1.zeroizing_new_spec hz dh3Value
        rcases oneTimePrekeyPrivate with _ | opk
        · have hss := Tacenta.SessionUnitSessionT1.shared_secret_no_panic hkdf
            dh1Value dh2Value dh3Value encapsulated none
          obtain ⟨shared, hshared⟩ :=
            (Tacenta.SessionUnitT1.noPanic_iff _).mp hss
          simp [dh1_post, dh2_post, dh3_post, hshared]
        · step with private_key_agree_no_panic hagree opk initiatorEphemeral
          rename_i o3
          step with contributory_no_panic o3
          rcases r3 with dh4Value | dh4Error
          · step with core.result.Result.Insts.CoreOpsTry.branch_Ok.spec dh4Value
            simp only [cf3_post]
            step with Tacenta.SessionUnitBraidT1.zeroizing_new_spec hz dh4Value
            have hss := Tacenta.SessionUnitSessionT1.shared_secret_no_panic hkdf
              dh1Value dh2Value dh3Value encapsulated (some dh4Value)
            obtain ⟨shared, hshared⟩ :=
              (Tacenta.SessionUnitT1.noPanic_iff _).mp hss
            simp [dh1_post, dh2_post, dh3_post, secret_post, hshared]
          · step with core.result.Result.Insts.CoreOpsTry.branch_Err.spec dh4Error
            simp only [cf3_post]
            simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
              core.convert.FromSame.from]
      · step with core.result.Result.Insts.CoreOpsTry.branch_Err.spec dh3Error
        simp only [cf2_post]
        simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
          core.convert.FromSame.from]
    · step with core.result.Result.Insts.CoreOpsTry.branch_Err.spec dh2Error
      simp only [cf1_post]
      simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
        core.convert.FromSame.from]
  · step with core.result.Result.Insts.CoreOpsTry.branch_Err.spec dh1Error
    simp only [cf_post]
    simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
      core.convert.FromSame.from]

structure EstablishInitiatorContracts {R : Type}
    (rngCore : rand_core_1.RngCore R) where
  dhCodec : DhCodecTotal
  dhAgree : DhAgreeTotal
  kemEncapsulate : KemEncapsulateTotal
  xeddsaVerify : XeddsaVerifyTotal
  random32 : Random32Total rngCore
  sessionHkdf : Tacenta.SessionUnitSessionT1.HkdfTotal
  sessionZeroizing : Tacenta.SessionUnitSessionT1.ZeroizingModel
  tripleZeroizing : Tacenta.SessionUnitT1.ZeroizingTotal
  spqrKdfInit : Tacenta.SessionUnitTripleT1.KdfInitTotal
  spqrZeroize : Tacenta.SessionUnitSpqrT1.ZeroizeTotal
  braidHkdf : Tacenta.SessionUnitBraidT1.HkdfSha256Total
  zeroizingArray : Tacenta.SessionUnitBraidT1.ZeroizingArrayRoundTrip
  rangeFullIndex : Tacenta.SessionUnitBraidT1.RangeFullIndexTotal

structure EstablishInitiatorHeadroom
    (theirBundle : lifecycle.PublishedBundle) : Prop where
  kemPrekey : theirBundle.bundle.kem_prekey.val.length + 1 ≤ Usize.max

theorem establish_initiator_for_no_panic {R : Type}
    (rngCore : rand_core_1.RngCore R) (cryptoRng : rand_core_1.CryptoRng R)
    (contracts : EstablishInitiatorContracts rngCore)
    (ourIdentity : lifecycle.Identity) (theirBundle : lifecycle.PublishedBundle)
    (expectedIdentity : tacenta_boundary.dh.PublicKeyBytes) (rng : R)
    (headroom : EstablishInitiatorHeadroom theirBundle) :
    lifecycle.establish_initiator_for rngCore cryptoRng ourIdentity theirBundle
      expectedIdentity rng ⦃ fun _ => True ⦄ := by
  rcases contracts with
    ⟨hdh, hagree, hkem, hx, hrng, hkdf, hzero, htripleZero, hkdfInit,
      hspqrZero, hbraidKdf, hzeroArray, hindex⟩
  let _ : Tacenta.SessionUnitSessionT1.ZeroizingModel := hzero
  unfold lifecycle.establish_initiator_for
  step with public_key_ne_no_panic hdh theirBundle.bundle.identity_key expectedIdentity
  split <;> simp
  step*
  rcases hopt : theirBundle.bundle.one_time_prekey with _ | oneTime
  all_goals simp only [hopt]
  all_goals (try (step with is_canonical_key_no_panic hdh))
  all_goals (try split <;> try simp)
  all_goals (try (step with is_canonical_key_no_panic hdh))
  all_goals (try split <;> try simp)
  all_goals (try (step with is_canonical_key_no_panic hdh))
  all_goals (try split <;> try simp)
  all_goals (step with verify_bundle_with_one_time_no_panic hdh hx theirBundle.bundle headroom.kemPrekey)
  all_goals (rcases r with verified | verifyError)
  all_goals simp
  all_goals (step with random_secret_no_panic rngCore cryptoRng hrng)
  all_goals (step with private_key_from_bytes_no_panic hdh)
  all_goals (step with kem_encapsulate_no_panic hkem rngCore cryptoRng)
  all_goals (rcases r1 with value | kemError)
  all_goals simp
  all_goals (rcases value with ⟨kemCiphertext, encapsulated⟩)
  all_goals (step with Tacenta.SessionUnitBraidT1.zeroizing_new_spec hzeroArray encapsulated)
  all_goals (step with identity_dh_key_no_panic hdh ourIdentity)
  all_goals (step with Tacenta.SessionUnitBraidT1.zeroizing_deref_spec ‹_›)
  all_goals (step with initiator_shared_secret_with_one_time_no_panic hdh hagree hx hzeroArray hkdf pk ephemeral theirBundle.bundle a1 headroom.kemPrekey)
  all_goals (rcases r2 with secret | handshakeError)
  all_goals simp
  all_goals (step with Tacenta.SessionUnitBraidT1.zeroizing_new_spec hzeroArray secret)
  all_goals (step with random_secret_no_panic rngCore cryptoRng hrng)
  all_goals (step with private_key_from_bytes_no_panic hdh)
  all_goals (step with private_key_agree_no_panic hagree)
  all_goals (rcases o1 with _ | ratchetSecret)
  all_goals simp
  all_goals (step with Tacenta.SessionUnitBraidT1.zeroizing_new_spec hzeroArray ratchetSecret)
  all_goals (step with Tacenta.SessionUnitBraidT1.zeroizing_deref_spec sk_post)
  all_goals (step with Tacenta.SessionUnitBraidT1.index_full_spec hindex)
  all_goals (step with private_key_public_no_panic hdh ratchet_private)
  all_goals (step with public_key_as_bytes_no_panic hdh pkb)
  all_goals (step with public_key_as_bytes_no_panic hdh theirBundle.bundle.signed_prekey)
  all_goals (step with Tacenta.SessionUnitBraidT1.zeroizing_deref_spec dh_out_post)
  all_goals (step with Tacenta.SessionUnitTripleT1.State.init_sender_no_panic hkdf htripleZero hkdfInit hspqrZero)
  all_goals (step with Tacenta.SessionUnitBraidT1.index_full_spec hindex)
  all_goals (step with Tacenta.SessionUnitBraidT1.Braid.initiator_no_panic hbraidKdf hzeroArray)
  all_goals (step with identity_public_no_panic hdh ourIdentity)
  all_goals (step with identity_ad_no_panic hdh)
  all_goals (step with private_key_public_no_panic hdh ephemeral)

theorem establish_initiator_no_panic {R : Type}
    (rngCore : rand_core_1.RngCore R) (cryptoRng : rand_core_1.CryptoRng R)
    (contracts : EstablishInitiatorContracts rngCore)
    (ourIdentity : lifecycle.Identity) (theirBundle : lifecycle.PublishedBundle)
    (rng : R) (headroom : EstablishInitiatorHeadroom theirBundle) :
    lifecycle.establish_initiator rngCore cryptoRng ourIdentity theirBundle rng
      ⦃ fun _ => True ⦄ := by
  unfold lifecycle.establish_initiator
  exact establish_initiator_for_no_panic rngCore cryptoRng contracts ourIdentity
    theirBundle theirBundle.bundle.identity_key rng headroom

def ReadableSecretResult
    (r : core.result.Result (zeroize.Zeroizing (Array U8 32#usize)) lifecycle.Error) : Prop :=
  match r with
  | core.result.Result.Ok z => ∃ a,
      zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref
        (Array.Insts.ZeroizeZeroize 32#usize
          (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) z = ok a
  | core.result.Result.Err _ => True

theorem responder_signed_prekey_secret_no_panic
    (hz : Tacenta.SessionUnitBraidT1.ZeroizingArrayRoundTrip)
    (store : lifecycle.PrekeyStore) (id : U32) :
    lifecycle.responder_signed_prekey_secret store id
      ⦃ fun r => ReadableSecretResult r ⦄ := by
  unfold lifecycle.responder_signed_prekey_secret
  split
  · step with Tacenta.SessionUnitBraidT1.zeroizing_new_spec hz
    exact ⟨_, z_post⟩
  · rcases store.previous_signed_prekey with _ | previous
    · simp [ReadableSecretResult]
    · rcases previous with ⟨secret, previousId, signature⟩
      by_cases h : previousId = id
      · simp [h]
        step with Tacenta.SessionUnitBraidT1.zeroizing_new_spec hz
        exact ⟨_, z_post⟩
      · simp [h, ReadableSecretResult]

def IndexInBounds (values : Slice U32) (o : Option Usize) : Prop :=
  match o with
  | none => True
  | some i => i.val < values.val.length

theorem u32_index_loop_no_panic (values : Slice U32) (needle : U32)
    (index : Usize) (hindex : index.val ≤ values.val.length) :
    lifecycle.u32_index_loop values needle index
      ⦃ fun r => IndexInBounds values r ⦄ := by
  unfold lifecycle.u32_index_loop
  apply loop.spec_decr_nat
    (measure := fun i => values.val.length - i.val)
    (inv := fun i => i.val ≤ values.val.length)
  · intro index1 hi
    simp only [lifecycle.u32_index_loop.body]
    split
    · step
      split
      · simp [IndexInBounds]
        scalar_tac
      · step
        constructor <;> scalar_tac
    · simp [IndexInBounds]
  · exact hindex

@[step]
theorem u32_index_no_panic (values : Slice U32) (needle : U32) :
    lifecycle.u32_index values needle
      ⦃ fun r => IndexInBounds values r ⦄ := by
  unfold lifecycle.u32_index
  exact u32_index_loop_no_panic values needle 0#usize (by simp)

theorem one_time_kem_ids_loop_no_panic
    (values : alloc.vec.Vec (U32 × tacenta_boundary.kem.KeyPair × Array U8 64#usize))
    (ids : alloc.vec.Vec U32) (index : Usize)
    (hindex : index.val ≤ values.val.length)
    (hlen : ids.val.length = index.val) :
    lifecycle.PrekeyStore.one_time_kem_ids_loop values ids index
      ⦃ fun r => r.val.length = values.val.length ⦄ := by
  unfold lifecycle.PrekeyStore.one_time_kem_ids_loop
  apply loop.spec_decr_nat
    (measure := fun p => values.val.length - (Prod.snd p).val)
    (inv := fun p => (Prod.snd p).val ≤ values.val.length ∧
      (Prod.fst p).val.length = (Prod.snd p).val)
  · rintro ⟨ids1, index1⟩ ⟨hi, hlen1⟩
    simp only at hi hlen1
    simp only [lifecycle.PrekeyStore.one_time_kem_ids_loop.body]
    split
    · step
      step
      case h => scalar_tac
      case a =>
        have hlen2 : ids1.val.length = index1.val + 1 := by
          rw [ids1_post]
          simp [hlen1]
        step
        clear ids index hindex hlen
        constructor
        · rw [index1_post]
          scalar_tac
        · constructor
          · rw [hlen2, index1_post]
          · rw [index1_post]
            scalar_tac
    · simp
      scalar_tac
  · exact ⟨hindex, hlen⟩

@[step]
theorem one_time_kem_ids_no_panic (store : lifecycle.PrekeyStore) :
    lifecycle.PrekeyStore.one_time_kem_ids store
      ⦃ fun r => r.val.length = store.kem_one_time.val.length ⦄ := by
  unfold lifecycle.PrekeyStore.one_time_kem_ids
  exact one_time_kem_ids_loop_no_panic store.kem_one_time
    (alloc.vec.Vec.with_capacity U32 (alloc.vec.Vec.len store.kem_one_time))
    0#usize (by simp)
    (by simp [alloc.vec.Vec.with_capacity, alloc.vec.Vec.new])

@[step]
theorem u32_slice_contains_no_panic (values : Slice U32) (needle : U32) :
    core.slice.Slice.contains core.cmp.PartialEqU32 values needle
      ⦃ fun _ => True ⦄ := by
  simp only [core.slice.Slice.contains]
  induction values.val with
  | nil => simp [List.anyM, pure, WP.spec_ok]
  | cons value values ih =>
      rw [List.anyM_cons]
      by_cases h : needle = value <;>
        simp [core.cmp.impls.PartialEqU32.eq, h, ih, pure, WP.spec_ok]

/-- The slot a responder resolves for a KEM identifier names a real entry
when it is a one-time slot. `responder_decapsulate` indexes the store with
it, so this is the bound that call needs. -/
def SlotResultInBounds (store : lifecycle.PrekeyStore)
    (r : core.result.Result (lifecycle.KemKeySlot × Bool) lifecycle.Error) : Prop :=
  match r with
  | core.result.Result.Ok (lifecycle.KemKeySlot.OneTime index, _) =>
      index.val < store.kem_one_time.val.length
  | _ => True

theorem responder_one_time_slot_no_panic
    (store : lifecycle.PrekeyStore) (ids : alloc.vec.Vec U32)
    (hlen : ids.val.length = store.kem_one_time.val.length) (id : U32) :
    (do
      let o ← lifecycle.u32_index ids.deref id
      match o with
      | none => ok (core.result.Result.Err lifecycle.Error.UnknownPrekeyId)
      | some index =>
        ok (core.result.Result.Ok (lifecycle.KemKeySlot.OneTime index, false)))
      ⦃ fun r => SlotResultInBounds store r ⦄ := by
  step with u32_index_no_panic
  rcases o with _ | index
  · simp [SlotResultInBounds]
  · simp [IndexInBounds] at o_post
    have hindex : index.val < store.kem_one_time.val.length := by
      change index.val < ids.val.length at o_post
      omega
    simp [SlotResultInBounds, hindex]

@[step]
theorem responder_kem_slot_no_panic (store : lifecycle.PrekeyStore) (id : U32) :
    lifecycle.responder_kem_slot store id
      ⦃ fun r => SlotResultInBounds store r ⦄ := by
  unfold lifecycle.responder_kem_slot
  split
  · step
    split
    · simp [SlotResultInBounds]
    · simp [SlotResultInBounds]
  · cases hprevious : store.previous_kem with
    | none =>
      simp [hprevious]
      step
      exact responder_one_time_slot_no_panic store _ ‹_› id
    | some previous =>
      rcases previous with ⟨pair, previousId, signature⟩
      change (if previousId = id then _ else _) ⦃ fun r => SlotResultInBounds store r ⦄
      split
      · step
        split
        · simp [SlotResultInBounds]
        · simp [SlotResultInBounds]
      · step
        exact responder_one_time_slot_no_panic store _ ‹_› id

@[step]
theorem responder_decapsulate_no_panic (hkem : KemDecapsulateTotal)
    (store : lifecycle.PrekeyStore) (slot : lifecycle.KemKeySlot)
    (ciphertext : Slice U8)
    (hslot : ∀ index, slot = lifecycle.KemKeySlot.OneTime index →
      index.val < store.kem_one_time.val.length) :
    lifecycle.responder_decapsulate store slot ciphertext
      ⦃ fun _ => True ⦄ := by
  unfold lifecycle.responder_decapsulate
  cases slot with
  | Current =>
    try dsimp only
    step
    rcases r <;> simp
  | Previous =>
    try dsimp only
    cases hprevious : store.previous_kem with
    | none => simp
    | some t =>
      rcases t with ⟨pair, previousId, signature⟩
      try dsimp only
      step with kem_decapsulate_no_panic hkem pair ciphertext
      rename_i r
      rcases r <;> simp
  | OneTime index =>
    have hindex := hslot index rfl
    try dsimp only
    step
    step
    rcases r <;> simp

@[step]
theorem hmac_sha256_no_panic (h : Tacenta.SessionUnitT1.HmacTotal)
    (key data : Slice U8) :
    tacenta_kdf.hmac_sha256 key data ⦃ fun _ => True ⦄ :=
  (Tacenta.SessionUnitT1.noPanic_iff _).2 (h key data)

@[step]
theorem last_resort_fingerprint_no_panic
    (h : Tacenta.SessionUnitT1.HmacTotal) (sk : Array U8 32#usize) :
    lifecycle.last_resort_fingerprint sk ⦃ fun _ => True ⦄ := by
  unfold lifecycle.last_resort_fingerprint
  step
  exact hmac_sha256_no_panic h lifecycle.LAST_RESORT_HANDSHAKE_LABEL s

theorem last_resort_seen_for_loop_no_panic
    (store : lifecycle.PrekeyStore) (keyId : U32)
    (count index : Usize)
    (hindex : index.val ≤ store.last_resort_seen.val.length)
    (hcount : count.val ≤ index.val) :
    lifecycle.PrekeyStore.last_resort_seen_for_loop store keyId count index
      ⦃ fun _ => True ⦄ := by
  unfold lifecycle.PrekeyStore.last_resort_seen_for_loop
  apply loop.spec_decr_nat
    (measure := fun p => store.last_resort_seen.val.length - (Prod.snd p).val)
    (inv := fun p => (Prod.snd p).val ≤ store.last_resort_seen.val.length ∧
      (Prod.fst p).val ≤ (Prod.snd p).val)
  · rintro ⟨count1, index1⟩ ⟨hi, hc⟩
    simp only at hi hc
    simp only [lifecycle.PrekeyStore.last_resort_seen_for_loop.body]
    split
    · step
      split
      · step
        case hmax => scalar_tac
        case a =>
          step
          case hmax => scalar_tac
          case a =>
            constructor
            · scalar_tac
            · constructor <;> scalar_tac
      · step
        case hmax => scalar_tac
        case a =>
          constructor
          · scalar_tac
          · constructor <;> scalar_tac
    · simp
  · exact ⟨hindex, hcount⟩

@[step]
theorem last_resort_seen_for_no_panic
    (store : lifecycle.PrekeyStore) (keyId : U32) :
    lifecycle.PrekeyStore.last_resort_seen_for store keyId
      ⦃ fun _ => True ⦄ := by
  unfold lifecycle.PrekeyStore.last_resort_seen_for
  exact last_resort_seen_for_loop_no_panic store keyId 0#usize 0#usize
    (by simp) (by simp)

theorem last_resort_seen_for_eq_of_seen_eq
    (left right : lifecycle.PrekeyStore) (keyId : U32)
    (hseen : left.last_resort_seen = right.last_resort_seen) :
    lifecycle.PrekeyStore.last_resort_seen_for left keyId =
      lifecycle.PrekeyStore.last_resort_seen_for right keyId := by
  unfold lifecycle.PrekeyStore.last_resort_seen_for
  unfold lifecycle.PrekeyStore.last_resort_seen_for_loop
  congr 1
  funext p
  rcases p with ⟨count, index⟩
  simp only [lifecycle.PrekeyStore.last_resort_seen_for_loop.body]
  rw [hseen]

theorem responder_replay_fingerprint_loop_no_panic
    (store : lifecycle.PrekeyStore) (fingerprint : Array U8 32#usize)
    (replayed : Bool) (index : Usize)
    (hindex : index.val ≤ store.last_resort_seen.val.length) :
    lifecycle.responder_replay_fingerprint_loop store fingerprint replayed index
      ⦃ fun r =>
        let (pkb, a, i, a1, z, kp, i1, a2, v, o, o1, i2, v1, v2, _) := r
        ({
          identity_public := pkb,
          signed_prekey_secret := a,
          signed_prekey_id := i,
          signed_prekey_sig := a1,
          one_time := z,
          kem := kp,
          kem_id := i1,
          kem_sig := a2,
          kem_one_time := v,
          previous_signed_prekey := o,
          previous_kem := o1,
          next_id := i2,
          last_resort_seen := v1,
          legacy_last_resort_blocked := v2
        } : lifecycle.PrekeyStore) = store ⦄ := by
  unfold lifecycle.responder_replay_fingerprint_loop
  apply loop.spec_decr_nat
    (measure := fun p => store.last_resort_seen.val.length - (Prod.snd p).val)
    (inv := fun p => (Prod.snd p).val ≤ store.last_resort_seen.val.length)
  · rintro ⟨replayed1, index1⟩ hi
    simp only at hi
    simp only [lifecycle.responder_replay_fingerprint_loop.body]
    split
    · step
      step with Tacenta.SessionUnitT1.array_eq_total
      split
      · step
        case hmax => scalar_tac
        case a => exact ⟨by scalar_tac, by scalar_tac⟩
      · step
        case hmax => scalar_tac
        case a => exact ⟨by scalar_tac, by scalar_tac⟩
    · simp
  · exact hindex

def ReplayFingerprintSafe (store : lifecycle.PrekeyStore) (kemId : U32)
    (r : core.result.Result (Option (Array U8 32#usize)) lifecycle.Error) : Prop :=
  match r with
  | core.result.Result.Ok (some _) =>
      ∃ count, lifecycle.PrekeyStore.last_resort_seen_for store kemId = ok count ∧
        count < lifecycle.MAX_LAST_RESORT_SEEN
  | _ => True

@[step]
theorem responder_replay_fingerprint_no_panic
    (h : Tacenta.SessionUnitT1.HmacTotal)
    (store : lifecycle.PrekeyStore) (kemId : U32)
    (sk : Array U8 32#usize) (lastResort : Bool) :
    lifecycle.responder_replay_fingerprint store kemId sk lastResort
      ⦃ ReplayFingerprintSafe store kemId ⦄ := by
  unfold lifecycle.responder_replay_fingerprint
  split
  · step
    step with responder_replay_fingerprint_loop_no_panic store fingerprint false
      0#usize (by simp)
    split
    · simp [ReplayFingerprintSafe]
    · obtain ⟨count, hcount, _⟩ := Std.WP.spec_imp_exists
        (last_resort_seen_for_no_panic
          {
            identity_public := pkb,
            signed_prekey_secret := a,
            signed_prekey_id := i,
            signed_prekey_sig := a1,
            one_time := z,
            kem := kp,
            kem_id := i1,
            kem_sig := a2,
            kem_one_time := v,
            previous_signed_prekey := o,
            previous_kem := o1,
            next_id := i2,
            last_resort_seen := v1,
            legacy_last_resort_blocked := v2
          } kemId)
      rw [hcount]
      simp only [Aeneas.Std.bind_tc_ok]
      split
      · simp [ReplayFingerprintSafe]
      · simp [ReplayFingerprintSafe]
        refine ⟨count, ?_, by scalar_tac⟩
        simpa [pkb_post] using hcount
  · simp [ReplayFingerprintSafe]

def OptionalIndexBelow (length : Nat) (found : Option Usize) : Prop :=
  match found with
  | none => True
  | some index => index.val < length

/-- Aeneas leaves `Vec::pop` opaque at this extraction boundary. This contract
states only the totality needed by T1; T3 separately has to pin the returned
value and shortened vector. The standard-library implementation is total for
every vector, including the empty vector (where it returns `none`). -/
def VecPopTotal : Prop :=
  ∀ (T : Type) (v : alloc.vec.Vec T),
    ∃ r, alloc.vec.Vec.pop Global v = ok r

@[step]
theorem slice_swap_no_panic {T : Type} (s : Slice T) (a b : Usize)
    (ha : a.val < s.length) (hb : b.val < s.length) :
    core.slice.Slice.swap s a b ⦃ fun _ => True ⦄ := by
  unfold core.slice.Slice.swap
  step
  step
  step
  step

theorem take_one_time_loop_no_panic [Tacenta.SessionUnitT1.DerivedKeysModel]
    (store : lifecycle.PrekeyStore) (id : U32) (index : Usize)
    (hindex : index.val ≤
      (Tacenta.SessionUnitT1.DerivedKeysModel.contents store.one_time).val.length) :
    lifecycle.PrekeyStore.take_one_time_loop store id index
      ⦃ fun r =>
        let (_, _, _, _, z, _, _, _, _, _, _, _, seen, _, found1) := r
        z = store.one_time ∧ seen = store.last_resort_seen ∧ OptionalIndexBelow
          (Tacenta.SessionUnitT1.DerivedKeysModel.contents store.one_time).val.length
          found1 ⦄ := by
  unfold lifecycle.PrekeyStore.take_one_time_loop
  apply loop.spec_decr_nat
    (measure := fun i =>
      (Tacenta.SessionUnitT1.DerivedKeysModel.contents store.one_time).val.length -
        i.val)
    (inv := fun i => i.val ≤
      (Tacenta.SessionUnitT1.DerivedKeysModel.contents store.one_time).val.length)
  · intro index1 hi
    simp only [lifecycle.PrekeyStore.take_one_time_loop.body]
    step
    split
    · step
      split
      · simp [OptionalIndexBelow]
        scalar_tac
      · step
        case hmax => scalar_tac
        case a => constructor <;> scalar_tac
    · simp [OptionalIndexBelow]
  · exact hindex

@[step]
theorem take_one_time_no_panic [Tacenta.SessionUnitT1.DerivedKeysModel]
    (hz : Tacenta.SessionUnitSpqrT1.ZeroizeTotal)
    (hpop : VecPopTotal)
    (store : lifecycle.PrekeyStore) (id : U32) :
    lifecycle.PrekeyStore.take_one_time store id
      ⦃ fun r => r.2.last_resort_seen = store.last_resort_seen ⦄ := by
  unfold lifecycle.PrekeyStore.take_one_time
  step with take_one_time_loop_no_panic store id 0#usize (by simp)
  rcases pkb_post with ⟨hzstore, hseen, hfound⟩
  rcases found with _ | foundIndex
  · simpa using hseen
  ·
    simp [OptionalIndexBelow] at hfound
    have hfoundz : foundIndex.val <
        (Tacenta.SessionUnitT1.DerivedKeysModel.contents z).val.length := by
      rw [hzstore]
      exact hfound
    step
    have hfoundValues : foundIndex.val < r.val.length := by
      rw [r_post1]
      exact hfoundz
    step
    step with Tacenta.SessionUnitTripleT1.zeroize_step hz
    step
    have hv5len : v5.val.length = r.val.length := by
      rw [v5_post, r_post2, i4_post2]
      simp
    have hv5nonempty : 0 < v5.val.length := by omega
    step
    step
    simp [alloc.vec.Vec.deref_mut, lift]
    have hv6len : v6.val.length = v5.val.length := by
      rw [v6_post1, v5_post]
    have hfoundV6 : foundIndex.val < v6.val.length := by
      rw [hv6len, hv5len]
      exact hfoundValues
    have hlastV5 : last.val < v5.val.length := by
      simp [alloc.vec.Vec.len] at last_post1 last_post2
      omega
    have hlastV6 : last.val < v6.val.length := by
      rw [hv6len]
      exact hlastV5
    step with core.slice.Slice.swap_spec v6 foundIndex last hfoundV6 hlastV6
    step
    obtain ⟨popped, hpopped⟩ := hpop _ v8
    rw [hpopped]
    rcases popped with ⟨poppedValue, poppedVec⟩
    simpa using hseen

theorem take_one_time_kem_loop_no_panic
    (store : lifecycle.PrekeyStore) (id : U32) (index : Usize)
    (hindex : index.val ≤ store.kem_one_time.val.length) :
    lifecycle.PrekeyStore.take_one_time_kem_loop store id index
      ⦃ fun r =>
        let (_, _, _, _, _, _, _, _, v, _, _, _, seen, _, found1) := r
        v = store.kem_one_time ∧ seen = store.last_resort_seen ∧
          OptionalIndexBelow store.kem_one_time.val.length found1 ⦄ := by
  unfold lifecycle.PrekeyStore.take_one_time_kem_loop
  apply loop.spec_decr_nat
    (measure := fun i => store.kem_one_time.val.length - i.val)
    (inv := fun i => i.val ≤ store.kem_one_time.val.length)
  · intro index1 hi
    simp only [lifecycle.PrekeyStore.take_one_time_kem_loop.body]
    simp only [alloc.vec.Vec.len]
    split
    · step
      split
      · simp [OptionalIndexBelow]
        scalar_tac
      · step
        case hmax => scalar_tac
        case a => constructor <;> scalar_tac
    · simp [OptionalIndexBelow]
  · exact hindex

@[step]
theorem take_one_time_kem_no_panic
    (hpop : VecPopTotal)
    (store : lifecycle.PrekeyStore) (id : U32) :
    lifecycle.PrekeyStore.take_one_time_kem store id
      ⦃ fun r => r.2.last_resort_seen = store.last_resort_seen ⦄ := by
  unfold lifecycle.PrekeyStore.take_one_time_kem
  step with take_one_time_kem_loop_no_panic store id 0#usize (by simp)
  rcases pkb_post with ⟨hv, hseen, hfound⟩
  rcases found with _ | foundIndex
  · simpa using hseen
  · simp [OptionalIndexBelow] at hfound
    have hfoundV : foundIndex.val < v.val.length := by
      rw [hv]
      exact hfound
    step
    simp [alloc.vec.Vec.deref_mut, lift]
    have hlastV : r.val < v.val.length := by
      simp [alloc.vec.Vec.len] at r_post1 r_post2
      omega
    step with slice_swap_no_panic v foundIndex r hfoundV hlastV
    obtain ⟨popped, hpopped⟩ := hpop _ s1
    rw [hpopped]
    rcases popped with ⟨poppedValue, poppedVec⟩
    rcases poppedValue with _ | entry
    · simpa using hseen
    · rcases entry with ⟨entryId, entryPair, entrySignature⟩
      simpa using hseen

def ReadableOneTime
    (o : Option (zeroize.Zeroizing (Array U8 32#usize))) : Prop :=
  match o with
  | none => True
  | some z => ∃ a, zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref
      (Array.Insts.ZeroizeZeroize 32#usize
        (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) z = ok a

theorem peek_one_time_loop_no_panic [Tacenta.SessionUnitT1.DerivedKeysModel]
    (hz : Tacenta.SessionUnitBraidT1.ZeroizingArrayRoundTrip)
    (store : lifecycle.PrekeyStore) (id : U32) (index : Usize)
    (hindex : index.val ≤
      (Tacenta.SessionUnitT1.DerivedKeysModel.contents store.one_time).val.length) :
    lifecycle.PrekeyStore.peek_one_time_loop store id index
      ⦃ fun r => ReadableOneTime r ⦄ := by
  unfold lifecycle.PrekeyStore.peek_one_time_loop
  apply loop.spec_decr_nat
    (measure := fun i =>
      (Tacenta.SessionUnitT1.DerivedKeysModel.contents store.one_time).val.length -
        i.val)
    (inv := fun i => i.val ≤
      (Tacenta.SessionUnitT1.DerivedKeysModel.contents store.one_time).val.length)
  · intro index1 hi
    simp only [lifecycle.PrekeyStore.peek_one_time_loop.body]
    step
    split
    · step
      split
      · step
        step with Tacenta.SessionUnitBraidT1.zeroizing_new_spec hz a
        simp only [ReadableOneTime]
        exact ⟨a, z_post⟩
      · step
        case hmax =>
          rw [v_post] at *
          scalar_tac
        case a =>
          rw [v_post] at *
          constructor <;> scalar_tac
    · simp [ReadableOneTime]
  · exact hindex

@[step]
theorem peek_one_time_no_panic [Tacenta.SessionUnitT1.DerivedKeysModel]
    (hz : Tacenta.SessionUnitBraidT1.ZeroizingArrayRoundTrip)
    (store : lifecycle.PrekeyStore) (id : U32) :
    lifecycle.PrekeyStore.peek_one_time store id
      ⦃ fun r => ReadableOneTime r ⦄ := by
  unfold lifecycle.PrekeyStore.peek_one_time
  exact peek_one_time_loop_no_panic hz store id 0#usize (by simp)

theorem responder_one_time_key_no_panic
    [Tacenta.SessionUnitT1.DerivedKeysModel]
    (hdh : DhCodecTotal)
    (hz : Tacenta.SessionUnitBraidT1.ZeroizingArrayRoundTrip)
    (store : lifecycle.PrekeyStore) (id : U32) :
    lifecycle.responder_one_time_key store id ⦃ fun _ => True ⦄ := by
  unfold lifecycle.responder_one_time_key
  split
  · simp
  · step with peek_one_time_no_panic hz store id
    rcases o with _ | secret
    · simp
    · simp only [ReadableOneTime] at o_post
      obtain ⟨key, hkey⟩ := o_post
      step with Tacenta.SessionUnitBraidT1.zeroizing_deref_spec hkey
      rename_i derefed hderef
      rw [hderef]
      step with private_key_from_bytes_no_panic hdh key

theorem responder_curve_inputs_no_panic (hdh : DhCodecTotal)
    (identity ephemeral : Slice U8) :
    lifecycle.responder_curve_inputs identity ephemeral ⦃ fun _ => True ⦄ := by
  unfold lifecycle.responder_curve_inputs
  step with decode_ec_no_panic hdh identity
  rcases o with _ | identityKey
  · simp
  · step with decode_ec_no_panic hdh ephemeral
    rename_i decodedEphemeral
    rcases decodedEphemeral <;> simp


@[step]
theorem agreement_failed_no_panic (self : lifecycle.Session) :
    lifecycle.Session.agreement_failed self ⦃ fun _ => True ⦄ := by
  unfold lifecycle.Session.agreement_failed
  exact Tacenta.SessionUnitBraidT1.Braid.failed_no_panic self.braid

@[step]
theorem message_keys_no_panic
    (hkdf : Tacenta.SessionUnitT1.HkdfTotal)
    (hza : Tacenta.SessionUnitBraidT1.ZeroizingArrayRoundTrip)
    (mk : Array U8 32#usize) (labels : tacenta_ratchet.LabelSet) :
    tacenta_ratchet.message_keys mk labels ⦃ fun _ => True ⦄ := by
  unfold tacenta_ratchet.message_keys
  step
  simp_all only
  step
  simp_all only
  step with Tacenta.SessionUnitT1.hkdf_step hkdf 80#usize
    (Array.to_slice (Array.repeat 32#usize 0#u8)) (Array.to_slice mk)
    tacenta_ratchet.MK_INFO (by scalar_tac)
  step with Tacenta.SessionUnitBraidT1.zeroizing_new_spec hza a1
  step
  step with Tacenta.SessionUnitBraidT1.zeroizing_deref_spec out_post
  step*
  all_goals simp_all


structure BraidReceiveContracts : Prop where
  decoderNew : Tacenta.SessionUnitBraidT1.DecoderNewTotal
  decoderAdd : Tacenta.SessionUnitBraidT1.DecoderAddChunkTotal
  decoderMessage : Tacenta.SessionUnitBraidT1.DecoderMessageTotal
  ct1Len : Tacenta.SessionUnitBraidT1.Ct1LenTotal
  ct2Len : Tacenta.SessionUnitBraidT1.Ct2LenTotal
  headerLen : Tacenta.SessionUnitBraidT1.HeaderLenTotal
  ekVectorLen : Tacenta.SessionUnitBraidT1.EkVectorLenTotal
  keyPairEkVector : Tacenta.SessionUnitBraidT1.KeyPairEkVectorTotal
  encoderNew : Tacenta.SessionUnitBraidT1.EncoderNewTotal
  keyPairDecapsulate : Tacenta.SessionUnitBraidT1.KeyPairDecapsulateTotal
  hkdf : Tacenta.SessionUnitBraidT1.HkdfSha256Total
  hmac : Tacenta.SessionUnitBraidT1.HmacSha256Total
  validateEk : Tacenta.SessionUnitBraidT1.ValidateEkTotal
  encapsulate2 : Tacenta.SessionUnitBraidT1.Encapsulate2Total
  encoderClone : Tacenta.SessionUnitBraidT1.EncoderCloneTotal
  decoderClone : Tacenta.SessionUnitBraidT1.DecoderCloneTotal
  keyPairClone : Tacenta.SessionUnitBraidT1.KeyPairCloneTotal
  encapsStateClone : Tacenta.SessionUnitBraidT1.EncapsStateCloneTotal
  optionClone : Tacenta.SessionUnitBraidT1.OptionCloneTotal
  zeroizingArray : Tacenta.SessionUnitBraidT1.ZeroizingArrayRoundTrip
  arrayZeroize : Tacenta.SessionUnitBraidT1.ArrayZeroizeTotal
  rangeFullIndex : Tacenta.SessionUnitBraidT1.RangeFullIndexTotal

structure TripleReceiveContracts : Prop where
  hmac : Tacenta.SessionUnitT1.HmacTotal
  hkdf : Tacenta.SessionUnitT1.HkdfTotal
  zeroizing : Tacenta.SessionUnitT1.ZeroizingTotal
  spqrZeroize : Tacenta.SessionUnitSpqrT1.ZeroizeTotal
  vecRetain : Tacenta.SessionUnitSpqrT1.VecRetainTotal
  kdfRk : Tacenta.SessionUnitSpqrT1.KdfRkTotal
  kdfCk : Tacenta.SessionUnitSpqrT1.KdfCkTotal
  optionClone : Tacenta.SessionUnitSpqrT1.OptionCloneTotal
  ratchetRemove : Tacenta.SessionUnitT1.RemoveSkippedAtTotal
  spqrRemove : Tacenta.SessionUnitSpqrT1.RemoveSkippedAtTotal
  vecAppend : Tacenta.SessionUnitSpqrT1.VecAppendTotal

abbrev MessageKeyMaterial :=
  Array U8 32#usize × Array U8 32#usize × Array U8 16#usize

noncomputable abbrev messageKeyMaterialZeroize : zeroize.Zeroize MessageKeyMaterial :=
  TupleABC.Insts.ZeroizeZeroize
    (Array.Insts.ZeroizeZeroize 32#usize (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes))
    (Array.Insts.ZeroizeZeroize 32#usize (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes))
    (Array.Insts.ZeroizeZeroize 16#usize (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes))

def MessageKeyMaterialRoundTrip : Prop :=
  ∀ t : MessageKeyMaterial, ∃ z,
    zeroize.Zeroizing.new messageKeyMaterialZeroize t = ok z ∧
    zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref messageKeyMaterialZeroize z = ok t

theorem message_key_material_new_spec (h : MessageKeyMaterialRoundTrip)
    (t : MessageKeyMaterial) :
    zeroize.Zeroizing.new messageKeyMaterialZeroize t ⦃ fun z =>
      zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref messageKeyMaterialZeroize z = ok t ⦄ := by
  obtain ⟨z, hz, hd⟩ := h t
  rw [hz]
  simp [hd]

theorem message_key_material_deref_spec {z : zeroize.Zeroizing MessageKeyMaterial}
    {t : MessageKeyMaterial}
    (h : zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref messageKeyMaterialZeroize z = ok t) :
    zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref messageKeyMaterialZeroize z
      ⦃ fun r => r = t ⦄ := by
  rw [h]
  simp

structure DecryptRatchetContracts {R : Type}
    (rc : rand_core_1.RngCore R) : Prop where
  dhCodec : DhCodecTotal
  dhAgree : DhAgreeTotal
  aeadOpen : AeadOpenTotal
  random32 : Random32Total rc
  braid : BraidReceiveContracts
  triple : TripleReceiveContracts
  messageKeyMaterial : MessageKeyMaterialRoundTrip

structure DecryptRatchetHeadroom (self : lifecycle.Session) : Prop where
  triple : ReceiveHeadroom self.triple
  braid : Tacenta.SessionUnitBraidT1.State.ct1_bounded self.braid.state
  associatedData : self.identity_ad.val.length + 106 ≤ Usize.max

/-- The Triple invariant discharges every receive-capacity premise inherited
from the classical and sparse ratchets.  These are consequences of the
leaf-store bounds and platform constants, rather than assumptions clients
must carry alongside an invariant state. -/
theorem triple_invariant_gives_receive_headroom
    (state : tacenta_triple.State)
    (h : tacenta_triple.State.invariant state = ok true) :
    ReceiveHeadroom state := by
  unfold tacenta_triple.State.invariant at h
  repeat' first
    | (replace h := Tacenta.SessionUnitRatchetImportInv.bind_eq_ok_inv h;
       obtain ⟨_, _, h⟩ := h)
    | split at h
    | simp at h
  all_goals
    constructor
    · exact Tacenta.SessionUnitRatchetImportInv.Ratchet.inv_gives_store_bound
        state.classical
        ((Tacenta.SessionUnitRatchetImportInv.Ratchet.invariant_true_iff
          state.classical).mp (by simp_all))
    · constructor
      · exact Tacenta.SessionUnitRatchetImportInv.Spqr.inv_gives_chain_room
          state.post_quantum
          ((Tacenta.SessionUnitRatchetImportInv.Spqr.invariant_true_iff
            state.post_quantum).mp (by simp_all))
      · exact Tacenta.SessionUnitRatchetImportInv.Spqr.inv_gives_skip_room
          state.post_quantum
          ((Tacenta.SessionUnitRatchetImportInv.Spqr.invariant_true_iff
            state.post_quantum).mp (by simp_all))

/-- The part of lifecycle headroom fixed by a valid persisted session.  Size
ceilings involving caller-provided plaintext or associated data remain on the
public operation theorem, as do counter ceilings that valid states may
eventually reach. -/
structure InvariantPreconditions (self : lifecycle.Session) : Prop where
  triple : ReceiveHeadroom self.triple
  braid : Tacenta.SessionUnitBraidT1.State.ct1_bounded self.braid.state

/-- A successful whole-session invariant check necessarily traversed and
accepted the common leaf-invariant boundary. -/
theorem session_invariant_gives_leaf_check (self : lifecycle.Session)
    (h : lifecycle.Session.invariant self = ok true) :
    lifecycle.Session.leaf_invariants self = ok true := by
  rw [lifecycle.Session.invariant] at h
  repeat' first
    | (replace h := Tacenta.SessionUnitRatchetImportInv.bind_eq_ok_inv h;
       obtain ⟨_, _, h⟩ := h)
    | split at h
    | simp at h
  all_goals unfold lifecycle.Session.leaf_invariants; simp_all

/-- The common leaf boundary is exactly the conjunction needed by the
capacity proof. -/
theorem leaf_check_gives_leaf_invariants (self : lifecycle.Session)
    (h : lifecycle.Session.leaf_invariants self = ok true) :
    tacenta_triple.State.invariant self.triple = ok true ∧
      tacenta_braid.Braid.invariant self.braid = ok true := by
  unfold lifecycle.Session.leaf_invariants at h
  replace h := Tacenta.SessionUnitRatchetImportInv.bind_eq_ok_inv h
  obtain ⟨tripleOk, htriple, h⟩ := h
  split at h
  · exact ⟨by simp_all, h⟩
  · simp at h

/-- `Session.invariant` supplies all leaf-implied capacity preconditions.
This is the session boundary promised by D5: callers do not restate ratchet
store bounds that the persisted-state invariant already enforces. -/
theorem invariant_gives_preconditions
    (hct1 : Tacenta.SessionUnitBraidT1.Ct1LenTotal)
    (self : lifecycle.Session)
    (h : lifecycle.Session.invariant self = ok true) :
    InvariantPreconditions self := by
  have hleaf := session_invariant_gives_leaf_check self h
  obtain ⟨htriple, hbraid⟩ := leaf_check_gives_leaf_invariants self hleaf
  exact ⟨triple_invariant_gives_receive_headroom self.triple htriple,
    (Tacenta.SessionUnitBraidImportInv.Braid.invariant_true_gives_inv
      hct1 self.braid hbraid).ct1_bounded⟩

theorem ratchet_init_receiver_empty
    (sk ourPub : Array U8 32#usize) (labels : tacenta_ratchet.LabelSet) :
    tacenta_ratchet.init_receiver sk ourPub labels
      ⦃ fun state => state.skipped.val.length = 0 ⦄ := by
  simp [tacenta_ratchet.init_receiver]

theorem spqr_init_bob_headroom
    (hki : Tacenta.SessionUnitTripleT1.KdfInitTotal) (sk : Slice U8) :
    tacenta_spqr.State.init_bob sk ⦃ fun state =>
      state.chains.val.length = 1 ∧ state.skipped.val.length = 0 ⦄ := by
  obtain ⟨⟨rk, k1, k2⟩, hkdf⟩ := hki sk
  simp [tacenta_spqr.State.init_bob, tacenta_spqr.State.init, hkdf, lift,
    alloc.slice.Slice.into_vec, Array.to_slice, Array.make]

theorem triple_init_receiver_headroom
    (hss : Tacenta.SessionUnitT1.HkdfTotal)
    (hzw : Tacenta.SessionUnitT1.ZeroizingTotal)
    (hki : Tacenta.SessionUnitTripleT1.KdfInitTotal)
    (hz : Tacenta.SessionUnitSpqrT1.ZeroizeTotal)
    (sk : Slice U8) (ourPub : Array U8 32#usize)
    (labels : tacenta_ratchet.LabelSet) :
    tacenta_triple.State.init_receiver sk ourPub labels
      ⦃ fun state => ReceiveHeadroom state ⦄ := by
  unfold tacenta_triple.State.init_receiver
  step with Tacenta.SessionUnitTripleT1.split_secret_no_panic hss hzw sk
  step with ratchet_init_receiver_empty ec ourPub labels
  step
  step with spqr_init_bob_headroom hki s1
  step with Tacenta.SessionUnitTripleT1.zeroize_step hz
  step with Tacenta.SessionUnitTripleT1.zeroize_step hz
  unfold ReceiveHeadroom
  rw [s_post, s2_post1, s2_post2]
  simp [tacenta_ratchet.MAX_SKIPPED_STORE, tacenta_ratchet.MAX_SKIP,
    tacenta_spqr.MAX_SKIP]
  scalar_tac

theorem braid_responder_headroom
    (hkdf : Tacenta.SessionUnitBraidT1.HkdfSha256Total)
    (hz : Tacenta.SessionUnitBraidT1.ZeroizingArrayRoundTrip)
    (hdec : Tacenta.SessionUnitBraidT1.DecoderNewTotal)
    (hhl : Tacenta.SessionUnitBraidT1.HeaderLenTotal)
    (secret : Slice U8) :
    tacenta_braid.Braid.responder secret ⦃ fun braid =>
      Tacenta.SessionUnitBraidT1.State.ct1_bounded braid.state ⦄ := by
  unfold tacenta_braid.Braid.responder
  step with Tacenta.SessionUnitBraidT1.Auth.init_no_panic hkdf hz 1#u64 secret
  step with Tacenta.SessionUnitBraidT1.hdr_decoder_no_panic hdec hhl
  simp [Tacenta.SessionUnitBraidT1.State.ct1_bounded]

theorem identity_ad_length (hdh : DhCodecTotal)
    (initiator responder : tacenta_boundary.dh.PublicKeyBytes) :
    lifecycle.identity_ad initiator responder ⦃ fun r => r.val.length = 66 ⦄ := by
  unfold lifecycle.identity_ad
  step*
  all_goals simp_all [alloc.vec.Vec.deref]
  exact Tacenta.SessionUnitSessionT1.small_le_usize_max (by omega)

set_option maxHeartbeats 800000 in
theorem decrypt_ratchet_no_panic {R : Type}
    (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R)
    (boundary : DecryptRatchetContracts rc)
    [Tacenta.SessionUnitT1.DerivedKeysModel]
    (self : lifecycle.Session) (message : Slice U8) (rng : R)
    (headroom : DecryptRatchetHeadroom self) :
    lifecycle.Session.decrypt_ratchet rc crc self message rng ⦃ fun _ => True ⦄ := by
  unfold lifecycle.Session.decrypt_ratchet
  step with Tacenta.SessionUnitBraidT1.Braid.failed_no_panic self.braid
  split
  · simp
  · step with decode_message_no_panic message
    rcases r with decoded | decodeError
    · step with msg_of_no_panic decoded.header
      rename_i braidMsg
      step with Tacenta.SessionUnitBraidT1.Braid.receive_no_panic
        boundary.braid.decoderNew boundary.braid.decoderAdd
        boundary.braid.decoderMessage boundary.braid.ct1Len boundary.braid.ct2Len
        boundary.braid.headerLen boundary.braid.ekVectorLen
        boundary.braid.keyPairEkVector boundary.braid.encoderNew
        boundary.braid.keyPairDecapsulate boundary.braid.hkdf boundary.braid.hmac
        boundary.braid.validateEk boundary.braid.encapsulate2
        boundary.braid.encoderClone boundary.braid.decoderClone
        boundary.braid.keyPairClone boundary.braid.encapsStateClone
        boundary.braid.optionClone boundary.braid.zeroizingArray
        boundary.braid.arrayZeroize boundary.braid.rangeFullIndex
        self.braid braidMsg (DecryptRatchetHeadroom.braid headroom)
      rcases hag : ag_out with _ | o <;> simp only [hag, tacenta_spqr.Output.new]
      all_goals step with public_key_from_bytes_no_panic boundary.dhCodec decoded.header.dh
      all_goals step with private_key_agree_no_panic boundary.dhAgree self.ratchet_private
      all_goals (rcases ho : o with _ | secret <;> simp only [ho])
      all_goals try simp
      all_goals step with Tacenta.SessionUnitBraidT1.zeroizing_new_spec boundary.braid.zeroizingArray secret
      all_goals step with random_secret_no_panic rc crc boundary.random32 rng
      all_goals step with private_key_from_bytes_no_panic boundary.dhCodec
      all_goals step with private_key_agree_no_panic boundary.dhAgree
      all_goals (rcases ho1 : o1 with _ | secret1 <;> simp only [ho1])
      all_goals try simp
      all_goals step with Tacenta.SessionUnitBraidT1.zeroizing_new_spec boundary.braid.zeroizingArray secret1
      all_goals step with Tacenta.SessionUnitTripleT1.State.sending_public_no_panic self.triple
      all_goals step with triple_header_of_no_panic decoded.header
      all_goals step with private_key_public_no_panic boundary.dhCodec candidate_key
      all_goals step with public_key_as_bytes_no_panic boundary.dhCodec
      all_goals simp only [dh_out_recv_post, dh_out_send_post]
      all_goals step with receive_with_eviction_no_panic
      all_goals try exact boundary.triple.hmac
      all_goals try exact boundary.triple.hkdf
      all_goals try exact boundary.triple.zeroizing
      all_goals try exact boundary.triple.spqrZeroize
      all_goals try exact boundary.triple.vecRetain
      all_goals try exact boundary.triple.kdfRk
      all_goals try exact boundary.triple.kdfCk
      all_goals try exact boundary.triple.optionClone
      all_goals try exact boundary.triple.ratchetRemove
      all_goals try exact boundary.triple.spqrRemove
      all_goals try exact boundary.triple.vecAppend
      all_goals try exact DecryptRatchetHeadroom.triple headroom
      all_goals (rcases hx : x with value | error <;> simp only [hx])
      all_goals try simp
      all_goals rcases value with ⟨triple_candidate, mk⟩
      all_goals step with Tacenta.SessionUnitBraidT1.zeroizing_new_spec boundary.braid.zeroizingArray mk
      all_goals rename_i mk1 mk1_post
      all_goals step with Tacenta.SessionUnitBraidT1.zeroizing_deref_spec mk1_post
      all_goals step with message_keys_no_panic boundary.triple.hkdf boundary.braid.zeroizingArray
      all_goals step with message_key_material_new_spec boundary.messageKeyMaterial
      all_goals rename_i keys keys_post
      all_goals step with message_key_material_deref_spec keys_post
      all_goals step with concat_ad_no_panic self.identity_ad.deref decoded.header (DecryptRatchetHeadroom.associatedData headroom)
      all_goals step with aead_open_no_panic boundary.aeadOpen
      all_goals (rcases haead : r1 with value1 | error <;> simp only [haead])
      all_goals try simp
      all_goals step with Tacenta.SessionUnitTripleT1.State.sending_public_no_panic triple_candidate
      all_goals step with Tacenta.SessionUnitT1.array_ne_total
      all_goals split <;> simp
    · simp

structure EstablishResponderContracts {R : Type}
    (rngCore : rand_core_1.RngCore R) where
  decrypt : DecryptRatchetContracts rngCore
  kemDecapsulate : KemDecapsulateTotal
  sessionHkdf : Tacenta.SessionUnitSessionT1.HkdfTotal
  sessionZeroizing : Tacenta.SessionUnitSessionT1.ZeroizingModel
  spqrKdfInit : Tacenta.SessionUnitTripleT1.KdfInitTotal
  vecPop : VecPopTotal

structure EstablishResponderHeadroom (store : lifecycle.PrekeyStore) : Prop where
  lastResortSeen : store.last_resort_seen.val.length + 1 ≤ Usize.max

theorem copy_bool_eq (value : Bool) :
    (if value then ok true else ok false) = (ok value : Result Bool) := by
  cases value <;> rfl

theorem maybe_take_one_time_kem_no_panic
    (hpop : VecPopTotal) (store : lifecycle.PrekeyStore) (id : U32)
    (keep : Bool) :
    (if keep then ok store else do
      let (_, store1) ← lifecycle.PrekeyStore.take_one_time_kem store id
      ok store1) ⦃ fun store1 =>
        store1.last_resort_seen = store.last_resort_seen ⦄ := by
  split
  · simp
  ·
    step with take_one_time_kem_no_panic hpop store id
    assumption

theorem maybe_take_one_time_no_panic
    [Tacenta.SessionUnitT1.DerivedKeysModel]
    (hz : Tacenta.SessionUnitSpqrT1.ZeroizeTotal) (hpop : VecPopTotal)
    (store : lifecycle.PrekeyStore) (id : U32) (take : Bool) :
    (if take then do
      let (_, store1) ← lifecycle.PrekeyStore.take_one_time store id
      ok store1
    else ok store) ⦃ fun store1 =>
      store1.last_resort_seen = store.last_resort_seen ⦄ := by
  split
  ·
    step with take_one_time_no_panic hz hpop store id
    assumption
  · simp

theorem maybe_take_one_time_normalized_no_panic
    [Tacenta.SessionUnitT1.DerivedKeysModel]
    (hz : Tacenta.SessionUnitSpqrT1.ZeroizeTotal) (hpop : VecPopTotal)
    (store : lifecycle.PrekeyStore) (id : U32) :
    (if id.val = serialization.ABSENT_ID.val then ok store else do
      let (_, store1) ← lifecycle.PrekeyStore.take_one_time store id
      ok store1) ⦃ fun store1 =>
      store1.last_resort_seen = store.last_resort_seen ⦄ := by
  split
  · simp
  · step with take_one_time_no_panic hz hpop store id
    assumption

theorem finish_responder_prekeys_no_panic {R : Type}
    [Tacenta.SessionUnitT1.DerivedKeysModel]
    (hz : Tacenta.SessionUnitSpqrT1.ZeroizeTotal) (hpop : VecPopTotal)
    (store : lifecycle.PrekeyStore) (kemId oneTimeId : U32)
    (lastResort : Bool) (replayValue : Option (Array U8 32#usize))
    (session : lifecycle.Session) (plaintext : alloc.vec.Vec U8) (rng : R)
    (hreplay : ReplayFingerprintSafe store kemId
      (core.result.Result.Ok replayValue))
    (headroom : EstablishResponderHeadroom store) :
    (do
      let store1 ← if lastResort then ok store else do
        let (_, next) ← lifecycle.PrekeyStore.take_one_time_kem store kemId
        ok next
      let store2 ← if oneTimeId.val = serialization.ABSENT_ID.val then ok store1
        else do
          let (_, next) ← lifecycle.PrekeyStore.take_one_time store1 oneTimeId
          ok next
      match replayValue with
      | none => ok (core.result.Result.Ok (E := lifecycle.Error)
          (session, plaintext), store2, rng)
      | some fp => do
        let count ← lifecycle.PrekeyStore.last_resort_seen_for store2 kemId
        massert (count < lifecycle.MAX_LAST_RESORT_SEEN)
        let seen ← alloc.vec.Vec.push store2.last_resort_seen (kemId, fp)
        ok (core.result.Result.Ok (E := lifecycle.Error) (session, plaintext),
          { store2 with last_resort_seen := seen }, rng))
      ⦃ fun _ => True ⦄ := by
  step with maybe_take_one_time_kem_no_panic hpop store kemId lastResort
  step with maybe_take_one_time_normalized_no_panic hz hpop store1 oneTimeId
  rcases replayValue with _ | fingerprint
  · simp
  · simp [ReplayFingerprintSafe] at hreplay
    obtain ⟨checked, hchecked, hbound⟩ := hreplay
    have hseen : store2.last_resort_seen = store.last_resort_seen := by
      rw [store2_post, store1_post]
    have hcount := last_resort_seen_for_eq_of_seen_eq store2 store kemId hseen
    rw [hchecked] at hcount
    rw [hcount]
    simp only [Aeneas.Std.bind_tc_ok]
    step
    step
    case h => simpa [hseen] using headroom.lastResortSeen

theorem responder_initial_decrypt_headroom
    (triple : tacenta_triple.State) (braid : tacenta_braid.Braid)
    (pk : tacenta_boundary.dh.PrivateKey) (identityAd : alloc.vec.Vec U8)
    (ourPublic peerPublic : tacenta_boundary.dh.PublicKeyBytes)
    (ephemeral : alloc.vec.Vec U8)
    (htriple : ReceiveHeadroom triple)
    (hbraid : Tacenta.SessionUnitBraidT1.State.ct1_bounded braid.state)
    (had : identityAd.val.length = 66) :
    DecryptRatchetHeadroom
      {
        triple,
        braid,
        ratchet_private := pk,
        identity_ad := identityAd,
        our_identity_public := ourPublic,
        peer_identity_public := peerPublic,
        pending_initial := none,
        established_ephemeral := some ephemeral
      } := by
  constructor
  · exact htriple
  · exact hbraid
  · rw [had]
    exact Tacenta.SessionUnitSessionT1.small_le_usize_max (by omega)

set_option maxHeartbeats 1000000 in
theorem establish_responder_no_panic {R : Type}
    (rngCore : rand_core_1.RngCore R) (cryptoRng : rand_core_1.CryptoRng R)
    (contracts : EstablishResponderContracts rngCore)
    [Tacenta.SessionUnitT1.DerivedKeysModel]
    (ourIdentity : lifecycle.Identity) (ourPrekeys : lifecycle.PrekeyStore)
    (initialMessage : Slice U8) (rng : R)
    (headroom : EstablishResponderHeadroom ourPrekeys) :
    lifecycle.establish_responder rngCore cryptoRng ourIdentity ourPrekeys
      initialMessage rng ⦃ fun _ => True ⦄ := by
  let _ : Tacenta.SessionUnitSessionT1.ZeroizingModel := contracts.sessionZeroizing
  unfold lifecycle.establish_responder
  step with decode_initial_no_panic initialMessage
  rcases r with decoded | decodeError
  · step with responder_signed_prekey_secret_no_panic
      contracts.decrypt.braid.zeroizingArray ourPrekeys decoded.signed_prekey_id
    rename_i signedResult signedResult_post
    rcases signedResult with signedSecret | signedError
    · simp [ReadableSecretResult] at signedResult_post
      obtain ⟨signedBytes, hsignedBytes⟩ := signedResult_post
      step with core.result.Result.Insts.CoreOpsTry.branch_Ok.spec signedSecret
      simp only [cf_post]
      step with responder_kem_slot_no_panic ourPrekeys decoded.kem_prekey_id
      rcases r2 with kemValue | kemError
      · step with core.result.Result.Insts.CoreOpsTry.branch_Ok.spec kemValue
        simp only [cf1_post]
        rcases kemValue with ⟨kemSlot, lastResort⟩
        simp only [copy_bool_eq]
        step with responder_curve_inputs_no_panic contracts.decrypt.dhCodec
          decoded.identity.deref decoded.ephemeral.deref
        rename_i curveResult
        rcases curveResult with curveInputs | curveError
        · step with core.result.Result.Insts.CoreOpsTry.branch_Ok.spec curveInputs
          simp only [cf2_post]
          rcases curveInputs with ⟨initiatorIdentity, initiatorEphemeral⟩
          step with responder_one_time_key_no_panic contracts.decrypt.dhCodec
            contracts.decrypt.braid.zeroizingArray ourPrekeys decoded.one_time_prekey_id
          rename_i oneTimeResult
          rcases oneTimeResult with oneTime | oneTimeError
          · step with core.result.Result.Insts.CoreOpsTry.branch_Ok.spec oneTime
            simp only [cf3_post]
            step with responder_decapsulate_no_panic contracts.kemDecapsulate ourPrekeys
              kemSlot decoded.kem_ciphertext.deref
              (by
                intro index hslot
                subst hslot
                simpa [SlotResultInBounds] using r2_post)
            rcases r5 with kemSecret | kemDecapsulateError
            · step with core.result.Result.Insts.CoreOpsTry.branch_Ok.spec kemSecret
              simp only [cf4_post]
              step with Tacenta.SessionUnitBraidT1.zeroizing_new_spec
                contracts.decrypt.braid.zeroizingArray kemSecret
              step with Tacenta.SessionUnitBraidT1.zeroizing_deref_spec hsignedBytes
              step with private_key_from_bytes_no_panic contracts.decrypt.dhCodec a
              rcases oneTime with _ | oneTimeKey
              all_goals step with identity_dh_key_no_panic contracts.decrypt.dhCodec ourIdentity
              all_goals step with Tacenta.SessionUnitBraidT1.zeroizing_deref_spec ss_post
              all_goals first
                | step with responder_shared_secret_no_panic contracts.decrypt.dhAgree
                    contracts.decrypt.braid.zeroizingArray contracts.sessionHkdf shared
                    signed_prekey none initiatorIdentity initiatorEphemeral x
                | step with responder_shared_secret_no_panic contracts.decrypt.dhAgree
                    contracts.decrypt.braid.zeroizingArray contracts.sessionHkdf shared
                    signed_prekey (some oneTimeKey) initiatorIdentity initiatorEphemeral x
              all_goals (rcases shared with secret | handshakeError)
              all_goals try simp
              all_goals step with Tacenta.SessionUnitBraidT1.zeroizing_new_spec contracts.decrypt.braid.zeroizingArray secret
              all_goals step with Tacenta.SessionUnitBraidT1.zeroizing_deref_spec sk_post
              all_goals step with responder_replay_fingerprint_no_panic contracts.decrypt.triple.hmac ourPrekeys decoded.kem_prekey_id a1 lastResort
              all_goals (rcases r6 with replayValue | replayError)
              all_goals try
                { step with core.result.Result.Insts.CoreOpsTry.branch_Err.spec replayError
                  simp only [cf5_post]
                  simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                    core.convert.FromSame.from] }
              all_goals step with core.result.Result.Insts.CoreOpsTry.branch_Ok.spec replayValue
              all_goals simp only [cf5_post]
              all_goals step with Tacenta.SessionUnitBraidT1.index_full_spec contracts.decrypt.braid.rangeFullIndex
              all_goals step with private_key_public_no_panic contracts.decrypt.dhCodec signed_prekey
              all_goals step with public_key_as_bytes_no_panic contracts.decrypt.dhCodec pkb
              all_goals step with triple_init_receiver_headroom contracts.decrypt.triple.hkdf contracts.decrypt.triple.zeroizing contracts.spqrKdfInit contracts.decrypt.triple.spqrZeroize s3 a2 tacenta_ratchet.LabelSet.Tacenta
              all_goals step with Tacenta.SessionUnitBraidT1.index_full_spec contracts.decrypt.braid.rangeFullIndex
              all_goals step with braid_responder_headroom contracts.decrypt.braid.hkdf contracts.decrypt.braid.zeroizingArray contracts.decrypt.braid.decoderNew contracts.decrypt.braid.headerLen s4
              all_goals step with private_key_from_bytes_no_panic contracts.decrypt.dhCodec a
              all_goals step with identity_public_no_panic contracts.decrypt.dhCodec ourIdentity
              all_goals step with identity_ad_length contracts.decrypt.dhCodec initiatorIdentity pkb1
              all_goals step with Tacenta.SessionUnitBraidT1.vecU8_clone_no_panic decoded.ephemeral
              all_goals have decryptHeadroom := responder_initial_decrypt_headroom triple braid pk v pkb1 initiatorIdentity v1 triple_post braid_post v_post
              all_goals step with decrypt_ratchet_no_panic rngCore cryptoRng contracts.decrypt _ decoded.message.deref rng decryptHeadroom
              all_goals (rcases r7 with decrypted | decryptError)
              all_goals try
                { step with core.result.Result.Insts.CoreOpsTry.branch_Err.spec decryptError
                  simp only [cf6_post]
                  simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                    core.convert.FromSame.from] }
              all_goals step with core.result.Result.Insts.CoreOpsTry.branch_Ok.spec decrypted
              all_goals rw [cf6_post]
              all_goals exact finish_responder_prekeys_no_panic contracts.decrypt.triple.spqrZeroize contracts.vecPop ourPrekeys decoded.kem_prekey_id decoded.one_time_prekey_id lastResort replayValue session decrypted rng1 r6_post headroom
            · step with core.result.Result.Insts.CoreOpsTry.branch_Err.spec kemDecapsulateError
              simp only [cf4_post]
              simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                core.convert.FromSame.from]
          · step with core.result.Result.Insts.CoreOpsTry.branch_Err.spec oneTimeError
            simp only [cf3_post]
            simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
              core.convert.FromSame.from]
        · step with core.result.Result.Insts.CoreOpsTry.branch_Err.spec curveError
          simp only [cf2_post]
          simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
            core.convert.FromSame.from]
      · step with core.result.Result.Insts.CoreOpsTry.branch_Err.spec kemError
        simp only [cf1_post]
        simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
          core.convert.FromSame.from]
    · step with core.result.Result.Insts.CoreOpsTry.branch_Err.spec signedError
      simp only [cf_post]
      simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
        core.convert.FromSame.from]
  · simp


open Aeneas Aeneas.Std Result
open tacenta_session_unit

structure BraidSendContracts {R : Type} (rc : rand_core_1.RngCore R) : Prop where
  rng : Tacenta.SessionUnitBraidT1.RngTotal rc
  encoderClone : Tacenta.SessionUnitBraidT1.EncoderCloneTotal
  decoderClone : Tacenta.SessionUnitBraidT1.DecoderCloneTotal
  keyPairClone : Tacenta.SessionUnitBraidT1.KeyPairCloneTotal
  encapsStateClone : Tacenta.SessionUnitBraidT1.EncapsStateCloneTotal
  keyPairGenerate : Tacenta.SessionUnitBraidT1.KeyPairGenerateTotal
  keyPairHeader : Tacenta.SessionUnitBraidT1.KeyPairHeaderTotal
  hmac : Tacenta.SessionUnitBraidT1.HmacSha256Total
  encoderNew : Tacenta.SessionUnitBraidT1.EncoderNewTotal
  encoderNext : Tacenta.SessionUnitBraidT1.EncoderNextChunkTotal
  hkdf : Tacenta.SessionUnitBraidT1.HkdfSha256Total
  encapsulate1 : Tacenta.SessionUnitBraidT1.Encapsulate1Total
  zeroizingArray : Tacenta.SessionUnitBraidT1.ZeroizingArrayRoundTrip
  arrayZeroize : Tacenta.SessionUnitBraidT1.ArrayZeroizeTotal
  rangeFullIndex : Tacenta.SessionUnitBraidT1.RangeFullIndexTotal

structure TripleSendContracts : Prop where
  hmac : Tacenta.SessionUnitT1.HmacTotal
  hkdf : Tacenta.SessionUnitT1.HkdfTotal
  zeroize : Tacenta.SessionUnitSpqrT1.ZeroizeTotal
  vecRetain : Tacenta.SessionUnitSpqrT1.VecRetainTotal
  kdfRk : Tacenta.SessionUnitSpqrT1.KdfRkTotal
  kdfCk : Tacenta.SessionUnitSpqrT1.KdfCkTotal
  optionClone : Tacenta.SessionUnitSpqrT1.OptionCloneTotal

theorem send_candidate_no_panic
    (boundary : TripleSendContracts) (self : tacenta_triple.State)
    (sendingEpoch : U64) (output : Option tacenta_spqr.Output)
    (hroom : self.post_quantum.chains.val.length + 1 < Usize.max) :
    lifecycle.send_candidate self sendingEpoch output ⦃ fun _ => True ⦄ := by
  unfold lifecycle.send_candidate
  rw [Tacenta.SessionUnitTripleT1.triple_state_clone_id boundary.optionClone self]
  rcases output with _ | o
  · step with Tacenta.SessionUnitTripleT1.State.send_no_panic
      boundary.hmac boundary.hkdf boundary.zeroize boundary.vecRetain
      boundary.kdfRk boundary.kdfCk boundary.optionClone self sendingEpoch none hroom
  · step with Tacenta.SessionUnitTripleT1.State.send_no_panic
      boundary.hmac boundary.hkdf boundary.zeroize boundary.vecRetain
      boundary.kdfRk boundary.kdfCk boundary.optionClone self sendingEpoch
      (some o) hroom

theorem prepare_send_candidate_no_panic
    (boundary : TripleSendContracts) (self : tacenta_triple.State)
    (sendingEpoch : U64) (output : Option tacenta_braid.Output)
    (hroom : self.post_quantum.chains.val.length + 1 < Usize.max) :
    (do
      let spqrOutput ← match output with
        | none => ok none
        | some o => do
          let o1 ← tacenta_spqr.Output.new o.key_epoch o.key
          ok (some o1)
      lifecycle.send_candidate self sendingEpoch spqrOutput)
      ⦃ fun _ => True ⦄ := by
  rcases output with _ | o
  · simp only [Aeneas.Std.bind_tc_ok]
    exact send_candidate_no_panic boundary self sendingEpoch none hroom
  · simp only [tacenta_spqr.Output.new, Aeneas.Std.bind_tc_ok]
    exact send_candidate_no_panic boundary self sendingEpoch
      (some { key_epoch := o.key_epoch, key := o.key }) hroom

def AeadSealBounded : Prop :=
  ∀ ek mk : Array U8 32#usize, ∀ iv : Array U8 16#usize,
    ∀ plaintext ad : Slice U8, ∃ r,
      tacenta_boundary.aead.encrypt ek mk iv plaintext ad = ok r ∧
      r.val.length ≤ plaintext.val.length + 16

theorem aead_seal_bounded_spec (h : AeadSealBounded)
    (ek mk : Array U8 32#usize) (iv : Array U8 16#usize)
    (plaintext ad : Slice U8) :
    tacenta_boundary.aead.encrypt ek mk iv plaintext ad ⦃ fun r =>
      r.val.length ≤ plaintext.val.length + 16 ⦄ := by
  obtain ⟨r, hr, hb⟩ := h ek mk iv plaintext ad
  rw [hr]
  simpa

structure EncryptContracts {R : Type} (rc : rand_core_1.RngCore R) : Prop where
  braid : BraidSendContracts rc
  triple : TripleSendContracts
  aeadSeal : AeadSealBounded
  messageKeyMaterial : MessageKeyMaterialRoundTrip
  dhCodec : DhCodecTotal

structure EncryptHeadroom (self : lifecycle.Session) (plaintext : Slice U8) : Prop where
  triple : self.triple.post_quantum.chains.val.length + 1 < Usize.max
  associatedData : self.identity_ad.val.length + 106 ≤ Usize.max
  ratchetMessage : 102 + (plaintext.val.length + 16) ≤ Usize.max
  initial : match self.pending_initial with
    | none => True
    | some p => 33 + 33 + p.kem_ciphertext.val.length +
        (102 + (plaintext.val.length + 16)) + 18 ≤ Usize.max

set_option maxHeartbeats 800000 in
theorem encrypt_no_panic {R : Type}
    (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R)
    (boundary : EncryptContracts rc)
    (self : lifecycle.Session) (plaintext : Slice U8) (rng : R)
    (headroom : EncryptHeadroom self plaintext) :
    lifecycle.Session.encrypt rc crc self plaintext rng ⦃ fun _ => True ⦄ := by
  unfold lifecycle.Session.encrypt
  step with Tacenta.SessionUnitBraidT1.Braid.failed_no_panic self.braid
  split
  · simp
  · step with Tacenta.SessionUnitBraidT1.Braid.send_no_panic rc crc
      boundary.braid.rng boundary.braid.encoderClone boundary.braid.decoderClone
      boundary.braid.keyPairClone boundary.braid.encapsStateClone
      boundary.braid.keyPairGenerate boundary.braid.keyPairHeader
      boundary.braid.hmac boundary.braid.encoderNew boundary.braid.encoderNext
      boundary.braid.hkdf boundary.braid.encapsulate1
      boundary.braid.zeroizingArray boundary.braid.arrayZeroize
      boundary.braid.rangeFullIndex self.braid rng
    step with Tacenta.SessionUnitBraidT1.Braid.failed_no_panic braid_next
    split
    · simp
    · rw [← Aeneas.Std.bind_assoc_eq]
      apply Aeneas.Std.WP.spec_bind
        (prepare_send_candidate_no_panic boundary.triple self.triple sending_epoch output
          (EncryptHeadroom.triple headroom))
      rintro ⟨candidate, sent⟩ _
      change (match sent with
        | core.result.Result.Ok value => _
        | core.result.Result.Err error => _) ⦃ fun _ => True ⦄
      rcases sent with value | error
      · rcases value with ⟨header, mk⟩
        step with composite_of_no_panic header ag_msg
        rename_i composite
        step with Tacenta.SessionUnitBraidT1.zeroizing_new_spec boundary.braid.zeroizingArray mk
        rename_i mk1 mk1_post
        step with Tacenta.SessionUnitBraidT1.zeroizing_deref_spec mk1_post
        step with message_keys_no_panic boundary.triple.hkdf boundary.braid.zeroizingArray
        step with message_key_material_new_spec boundary.messageKeyMaterial
        rename_i keys keys_post
        step with message_key_material_deref_spec keys_post
        step with concat_ad_no_panic self.identity_ad.deref composite
          (EncryptHeadroom.associatedData headroom)
        step with aead_seal_bounded_spec boundary.aeadSeal
        step with encode_message_no_panic composite ciphertext.deref
          (by
            change 102 + ciphertext.val.length ≤ Usize.max
            have h := EncryptHeadroom.ratchetMessage headroom
            omega)
        rcases hp : self.pending_initial with _ | p
        · simp
        · step with encode_ec_spec boundary.dhCodec self.our_identity_public
          rename_i identityEncoded identityEncoded_post
          step with encode_ec_spec boundary.dhCodec p.ephemeral_public
          step with encode_initial_no_panic
          change identityEncoded.val.length + v1.val.length + p.kem_ciphertext.val.length +
            ratchet_message.val.length + 18 ≤ Usize.max
          have hinit := EncryptHeadroom.initial headroom
          rw [hp] at hinit
          have hratchet : ratchet_message.val.length =
              102 + ciphertext.val.length := by
            change ratchet_message.val.length = 102 + ciphertext.val.length
            exact ratchet_message_post
          rw [identityEncoded_post, v1_post, hratchet]
          omega
      · change (ok (core.result.Result.Err (lifecycle.Error.Triple error), self, rng1))
          ⦃ fun _ => True ⦄
        simp


set_option maxHeartbeats 800000 in
@[step]
theorem vec_u8_eq_no_panic (a b : alloc.vec.Vec U8) :
    alloc.vec.partial_eq.PartialEqVec.eq core.cmp.PartialEqU8 a b
      ⦃ fun _ => True ⦄ := by
  unfold alloc.vec.partial_eq.PartialEqVec.eq
  split
  · generalize List.zip a.val b.val = xs
    induction xs with
    | nil => simp [List.allM, pure, WP.spec_ok]
    | cons x xs ih =>
      simp only [List.allM]
      by_cases h : decide (x.1 = x.2) = true
      · simp [h, ih, pure, WP.spec_ok]
      · simp [h, pure, WP.spec_ok]
  · simp [pure, WP.spec_ok]

set_option maxHeartbeats 800000 in
theorem decrypt_no_panic {R : Type}
    (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R)
    (boundary : DecryptRatchetContracts rc)
    [Tacenta.SessionUnitT1.DerivedKeysModel]
    (self : lifecycle.Session) (message : Slice U8) (rng : R)
    (headroom : DecryptRatchetHeadroom self) :
    lifecycle.Session.decrypt rc crc self message rng ⦃ fun _ => True ⦄ := by
  unfold lifecycle.Session.decrypt
  step with message_type_no_panic message
  rcases o with _ | mt
  · step
    rename_i inner _
    step with decrypt_ratchet_no_panic rc crc boundary self inner.deref rng headroom
    step*
  · rcases mt with _ | _
    · step
      rename_i inner _
      step with decrypt_ratchet_no_panic rc crc boundary self inner.deref rng headroom
      step*
    · step with decode_initial_no_panic message
      rename_i decodedResult
      rcases decodedResult with decoded | error
      · rcases self.established_ephemeral with _ | established
        · simp
        · step
          split
          · step with encode_ec_spec boundary.dhCodec self.peer_identity_public
            step
            split
            · step with decrypt_ratchet_no_panic rc crc boundary self
                decoded.message.deref rng headroom
              step*
            · simp
          · simp
      · simp


end Tacenta.UnitLifecycleT1
