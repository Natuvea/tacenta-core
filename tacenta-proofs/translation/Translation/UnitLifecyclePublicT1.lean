import Translation.UnitLifecycleT1
import Translation.SessionUnitBraidT1

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
