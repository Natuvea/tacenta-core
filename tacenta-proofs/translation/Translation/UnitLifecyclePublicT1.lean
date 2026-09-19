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

end Tacenta.UnitLifecycleT1
