import Translation.UnitLifecycleSessionCodec

/-!
# `Session::export` then `Session::import` at a session of the covered shape

From the leaf codecs of `UnitLifecycleSessionCodec`:

* `export_spec`: `export` of a session with `CodecShape` returns the bytes `sessionEnc` of its leaf
  encodings, its private key bytes and its two identity keys' bytes.
* `import_unchecked_spec`: the field-by-field decode of those bytes returns the session, every field
  equal.
* `export_import_of_shape`: for every session with `CodecShape` that passes `Session::invariant`, `import`
  of the exported bytes accepts and returns the session itself: the canonical re-encode compares the
  same bytes and the invariant is the session's own.

Under the five laws of `UnitLifecycleSessionCodec`.  The shape is the one an established initiator
session has (`UnitLifecycleRestoredSession.codecShape_parts`); it excludes stored skipped keys, Braid
states other than `KeysUnsampled`, an absent pending initial message and a present established ephemeral.
-/

namespace Tacenta.UnitLifecycleSessionRoundTrip

open Aeneas Aeneas.Std Result
open tacenta_session_unit
open Tacenta.UnitLifecycleSessionCodec

/-! ## The session -/

/-- The shape of a session the round trip below covers: Braid in `KeysUnsampled` below the epoch
`import` refuses, no stored key in either ratchet, one sparse chain-table entry with both chains, a
pending initial message, no established ephemeral, and the two variable-length fields below 64 KiB. -/
structure CodecShape (s : lifecycle.Session) (epoch : U64) (auth : tacenta_braid.Auth) (e : U64)
    (c1 c2 : tacenta_spqr.Chain) (p : lifecycle.PendingInitial) : Prop where
  braid : s.braid = ⟨tacenta_braid.State.KeysUnsampled epoch auth⟩
  epochNotMax : epoch ≠ core.num.U64.MAX
  classicalSkipped : s.triple.classical.skipped.val = []
  chains : s.triple.post_quantum.chains.val = [(e, { send := some c1, receive := some c2 })]
  sparseSkipped : s.triple.post_quantum.skipped.val = []
  identityAd : s.identity_ad.val.length ≤ 65536
  pending : s.pending_initial = some p
  ciphertext : p.kem_ciphertext.val.length ≤ 65536
  established : s.established_ephemeral = none

/-- The bytes `Session::export` writes for a session of that shape, from the encoded Triple `vt`, Braid
`vb`, ratchet private key bytes `pa`, identity public key bytes `oa`, `pea` and encoded pending initial
message `vp`. -/
def sessionEnc (vt vb : alloc.vec.Vec U8) (pa : Array U8 32#usize) (ad : alloc.vec.Vec U8)
    (oa pea : Array U8 32#usize) (vp : alloc.vec.Vec U8) : List U8 :=
  1#u8 :: (lenEnc (alloc.vec.Vec.deref vt) ++ (lenEnc (alloc.vec.Vec.deref vb) ++ (pa.val ++
    (lenEnc (alloc.vec.Vec.deref ad) ++ (oa.val ++ (pea.val ++ (1#u8 ::
    (lenEnc (alloc.vec.Vec.deref vp) ++ [0#u8]))))))))

theorem export_spec (hz : ZeroizingVecRoundTrip) (s : lifecycle.Session) (epoch : U64)
    (auth : tacenta_braid.Auth) (e : U64) (c1 c2 : tacenta_spqr.Chain) (p : lifecycle.PendingInitial)
    (shape : CodecShape s epoch auth e c1 c2 p)
    (zp : zeroize.Zeroizing (Array U8 32#usize)) (pa : Array U8 32#usize)
    (hpk : tacenta_boundary.dh.PrivateKey.to_bytes s.ratchet_private = ok zp)
    (hpa : zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref arrInst zp = ok pa)
    (oa pea ea : Array U8 32#usize)
    (hoa : tacenta_boundary.dh.PublicKeyBytes.as_bytes s.our_identity_public = ok oa)
    (hpea : tacenta_boundary.dh.PublicKeyBytes.as_bytes s.peer_identity_public = ok pea)
    (hea : tacenta_boundary.dh.PublicKeyBytes.as_bytes p.ephemeral_public = ok ea) :
    lifecycle.Session.export s ⦃ z => ∃ vt vb vp v,
      zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref vecInst z = ok v ∧
      vt.val = tripleEnc s.triple e c1 c2 ∧ vb.val = braidEnc epoch auth ∧ vp.val = pendEnc p ea ∧
      v.val = sessionEnc vt vb pa s.identity_ad oa pea vp ⦄ := by
  unfold lifecycle.Session.export
  step with triple_to_bytes_spec hz s.triple e c1 c2 shape.classicalSkipped shape.chains
    shape.sparseSkipped as ⟨vt, zt, hvt, hvtv⟩
  rw [shape.braid]
  step with braid_to_bytes_spec hz epoch auth as ⟨vb, zb, hvb, hvbv⟩
  rw [hpk, shape.pending]
  simp only [bind_tc_ok]
  step with pending_to_bytes_spec p ea hea shape.ciphertext as ⟨vp, hvp⟩
  simp only [shape.established, hvt, hvb, hpa, hoa, hpea, bind_tc_ok]
  have hlt : vt.val.length = 334 := by rw [hvtv, tripleEnc_length]
  have hlb : vb.val.length = 74 := by rw [hvbv, braidEnc_length]
  have hlp : vp.val.length = 48 + p.kem_ciphertext.val.length := by rw [hvp, pendEnc_length]
  have had := shape.identityAd
  have hct := shape.ciphertext
  step*
  all_goals try (simp only [*, Slice.length, alloc.vec.Vec.deref, Array.to_slice, alloc.vec.Vec.with_capacity,
    alloc.vec.Vec.new, List.length_append, List.length_cons, List.length_nil, List.length_singleton,
    lenEnc_length, arr32_len]; scalar_tac)
  · refine ⟨vt, vb, vp, out9, z_post, hvtv, hvbv, hvp, ?_⟩
    simp only [out9_post, out8_post, x_post, out7_post, out6_post, out5_post, out4_post, out3_post,
      out2_post, out1_post, s3_post, s5_post, s6_post, Array.to_slice, alloc.vec.Vec.with_capacity,
      alloc.vec.Vec.new, lifecycle.SESSION_VERSION, sessionEnc, List.nil_append, List.append_assoc,
      List.cons_append, List.singleton_append]
  · exfalso
    rename_i hne
    apply hne
    rw [UScalar.eq_equiv]
    simp only [*, alloc.vec.Vec.len, Slice.len, Slice.length, alloc.vec.Vec.deref, Array.to_slice,
      alloc.vec.Vec.with_capacity, alloc.vec.Vec.new, List.length_append, List.length_cons,
      List.length_nil, List.length_singleton, lenEnc_length, arr32_len]
    scalar_tac


set_option maxHeartbeats 2000000 in
theorem import_unchecked_spec (hbr : OptionBranchSome) (s : lifecycle.Session) (epoch : U64)
    (auth : tacenta_braid.Auth) (e : U64) (c1 c2 : tacenta_spqr.Chain) (p : lifecycle.PendingInitial)
    (shape : CodecShape s epoch auth e c1 c2 p)
    (hinvT : tacenta_triple.State.invariant s.triple = ok true)
    (hinvB : tacenta_braid.Braid.invariant s.braid = ok true)
    (vt vb vp : alloc.vec.Vec U8) (pa oa pea ea : Array U8 32#usize)
    (hvt : vt.val = tripleEnc s.triple e c1 c2) (hvb : vb.val = braidEnc epoch auth)
    (hvp : vp.val = pendEnc p ea)
    (hfpa : tacenta_boundary.dh.PrivateKey.from_bytes pa = ok s.ratchet_private)
    (hfoa : tacenta_boundary.dh.PublicKeyBytes.from_bytes oa = ok s.our_identity_public)
    (hfpea : tacenta_boundary.dh.PublicKeyBytes.from_bytes pea = ok s.peer_identity_public)
    (hfea : tacenta_boundary.dh.PublicKeyBytes.from_bytes ea = ok p.ephemeral_public)
    (bytes : Slice U8) (hb : bytes.val = sessionEnc vt vb pa s.identity_ad oa pea vp) :
    lifecycle.Session.import_unchecked bytes ⦃ r => r = core.result.Result.Ok s ⦄ := by
  have hlt : vt.val.length = 334 := by rw [hvt, tripleEnc_length]
  have hlb : vb.val.length = 74 := by rw [hvb, braidEnc_length]
  have hlp : vp.val.length = 48 + p.kem_ciphertext.val.length := by rw [hvp, pendEnc_length]
  have had := shape.identityAd
  have hct := shape.ciphertext
  have hmaxb : bytes.val.length ≤ Usize.max := bytes.property
  have hlen : bytes.val.length = 1 + (4 + 334) + (4 + 74) + 32 + (4 + s.identity_ad.val.length) + 32 + 32 + 1 +
      (4 + vp.val.length) + 1 := by
    rw [hb]; simp [sessionEnc, lenEnc_length, alloc.vec.Vec.deref, hlt, hlb]; omega
  have d0 : bytes.val.drop (0#usize).val = 1#u8 :: (sessionEnc vt vb pa s.identity_ad oa pea vp).tail := by
    simp only [hb, sessionEnc]; rfl
  have d1 : bytes.val.drop (1#usize).val = (sessionEnc vt vb pa s.identity_ad oa pea vp).tail := by
    rw [hb]; rfl
  simp only [sessionEnc, List.tail_cons, lenEnc, List.append_assoc] at d1
  unfold lifecycle.Session.import_unchecked
  simp only [core.slice.Slice.is_empty, bind_tc_ok]
  rw [if_neg (by simp [Slice.length, hlen])]
  rw [index_usize_of _ _ _ _ d0]
  simp only [bind_tc_ok, lifecycle.SESSION_VERSION, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  step with lifecycle_take_len_prefixed_of hbr bytes 1#usize _ (alloc.vec.Vec.deref vt).val _
    (cast_len_val _ (by simp [alloc.vec.Vec.deref, hlt])) d1 as ⟨tsl, pos, o, ho, htsl, hpos⟩
  simp only [ho]
  step with (show tacenta_triple.State.from_bytes tsl ⦃ x => x = core.result.Result.Ok s.triple ⦄ by
    rw [triple_from_bytes_of tsl s.triple e c1 c2 (by rw [htsl]; exact hvt) shape.classicalSkipped
      shape.chains shape.sparseSkipped hinvT]; simp) as ⟨r, hr⟩
  simp only [hr]
  have dB := drop_next (drop_next d1)
  rw [be32_length, show (1#usize).val + 4 + (alloc.vec.Vec.deref vt).val.length = pos.val by
    rw [hpos]; simp] at dB
  step with lifecycle_take_len_prefixed_of hbr bytes pos _ (alloc.vec.Vec.deref vb).val _
    (cast_len_val _ (by simp [alloc.vec.Vec.deref, hlb])) dB as ⟨bsl, pos1, o1, ho1, hbsl, hpos1⟩
  simp only [ho1]
  rw [shape.braid] at hinvB
  step with (show tacenta_braid.Braid.from_bytes bsl ⦃ x => x = core.result.Result.Ok s.braid ⦄ by
    rw [shape.braid, braid_from_bytes_of bsl epoch auth (by rw [hbsl]; exact hvb) shape.epochNotMax hinvB]
    simp) as ⟨r1, hr1⟩
  simp only [hr1]
  have dP := drop_next (drop_next dB)
  rw [be32_length, ← hpos1] at dP
  have hp1v : pos1.val = 417 := by
    rw [hpos1, hpos]; simp [alloc.vec.Vec.deref, hlt, hlb]
  step as ⟨i2, hi2⟩
  rw [if_neg (by simp only [Slice.len]; scalar_tac)]
  step as ⟨sp, backp, hsp1, hsp2⟩
  step as ⟨sp1, hsp11, hsp12⟩
  step as ⟨sp2, hsp2'⟩
  · rw [hsp12]; simp [Slice.length, hsp1, hi2]
  have hba : backp sp2 = pa := by
    rw [hsp2]; exact from_slice_eq _ _ _ (by
      rw [hsp2', hsp11, hi2]; exact slice_of_drop dP (by rw [arr32_len]))
  rw [hba, hfpa]
  simp only [bind_tc_ok]
  have dA := drop_next dP
  rw [arr32_len, show pos1.val + 32 = i2.val by rw [hi2]] at dA
  step with lifecycle_take_len_prefixed_of hbr bytes i2 _ (alloc.vec.Vec.deref s.identity_ad).val _
    (cast_len_val _ (by simp [alloc.vec.Vec.deref]; omega)) dA as ⟨asl, pos2, o2, ho2, hasl, hpos2⟩
  simp only [ho2]
  step as ⟨ad1, had1⟩
  have dO := drop_next (drop_next dA)
  rw [be32_length, ← hpos2] at dO
  have dPe := drop_next dO
  rw [arr32_len] at dPe
  have dF := drop_next dPe
  rw [arr32_len] at dF
  have hp2v : pos2.val = 453 + s.identity_ad.val.length := by
    rw [hpos2, hi2, hp1v]; simp [alloc.vec.Vec.deref]
  step as ⟨i4, hi4⟩
  rw [if_neg (by simp only [Slice.len]; scalar_tac)]
  step as ⟨so, backo, hso1, hso2⟩
  step as ⟨i5, hi5⟩
  step as ⟨so1, hso11, hso12⟩
  step as ⟨so2, hso2'⟩
  · rw [hso12]; simp [Slice.length, hso1, hi5]
  step as ⟨se, backe, hse1, hse2⟩
  step as ⟨se1, hse11, hse12⟩
  step as ⟨se2, hse2'⟩
  · rw [hse12]; simp [Slice.length, hse1, hi5, hi4]
  step as ⟨i7, hi7⟩
  rw [if_neg (by simp only [Slice.len]; scalar_tac)]
  rw [index_usize_of bytes i4 1#u8 _ (by rw [hi4, show pos2.val + 64 = pos2.val + 32 + 32 by omega]; exact dF)]
  simp only [bind_tc_ok]
  split
  · rename_i h01; exact absurd h01 (by decide)
  rotate_left
  · rename_i h0 h1; exact (h1 (by decide)).elim
  have dPd := drop_next (seg := [1#u8]) dF
  simp only [List.length_singleton] at dPd
  rw [show pos2.val + 32 + 32 + 1 = i7.val by rw [hi7, hi4]] at dPd
  step with lifecycle_take_len_prefixed_of hbr bytes i7 _ (alloc.vec.Vec.deref vp).val _
    (cast_len_val _ (by simp [alloc.vec.Vec.deref]; omega)) dPd as ⟨psl, next, o3, ho3, hpsl, hnext⟩
  simp only [ho3]
  step with (show lifecycle.PendingInitial.from_bytes psl ⦃ x => x = some p ⦄ by
    rw [pending_from_bytes_of hbr psl p ea (by rw [hpsl]; exact hvp) hfea hct]; simp) as ⟨o4, ho4⟩
  simp only [ho4]
  have dZ := drop_next (drop_next dPd)
  rw [be32_length, ← hnext] at dZ
  have hnv : next.val + 1 = bytes.val.length := by
    rw [hnext, hi7, hi4, hp2v, hlen]; simp [alloc.vec.Vec.deref]; omega
  step as ⟨i10, hi10⟩
  rw [if_neg (by simp only [Slice.len]; scalar_tac)]
  rw [index_usize_of bytes next 0#u8 [] dZ]
  simp only [bind_tc_ok]
  split
  rotate_left
  · rename_i h1; exact absurd h1 (by decide)
  · rename_i h0 h1; exact (h0 (by decide)).elim
  have hi10l : i10 = Slice.len bytes := by rw [UScalar.eq_equiv, hi10]; simp [Slice.len, hnv]
  have hbo : backo so2 = oa := by
    rw [hso2]; exact from_slice_eq _ _ _ (by
      rw [hso2', hso11, hi5]; exact slice_of_drop dO (by rw [arr32_len]))
  have hbe : backe se2 = pea := by
    rw [hse2]; exact from_slice_eq _ _ _ (by
      rw [hse2', hse11, hi5, hi4]; exact slice_of_drop dPe (by rw [arr32_len]))
  have hadv : ad1 = s.identity_ad := by rw [← had1]; exact Subtype.ext hasl
  simp only [hi10l, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, hbo, hbe, hfoa, hfpea,
    bind_tc_ok, hadv, ← shape.pending, ← shape.established]
  simp


/-- A byte slice is not unequal to itself under the translated slice comparison. -/
theorem slice_ne_self (x : Slice U8) :
    core.cmp.impls.PartialEqShared.ne (Slice.Insts.CoreCmpPartialEqSlice core.cmp.PartialEqU8) x x =
      ok false := by
  have h : core.cmp.impls.PartialEqShared.ne (Slice.Insts.CoreCmpPartialEqSlice core.cmp.PartialEqU8) x x
      ⦃ b => b = false ⦄ := by
    simp only [core.cmp.impls.PartialEqShared.ne]
    apply Std.WP.spec_mono (core.cmp.PartialEq.ne.default.spec _ x x ?_)
    · intro b hb; simpa using hb
    · apply core.slice.cmp.PartialEqSlice.eq_homo_spec
      intro a b
      step*
  obtain ⟨r, hr, rfl⟩ := Std.WP.spec_imp_exists h
  exact hr


open Tacenta.SessionUnitRatchetImportInv (bind_eq_ok_inv)

/-- `Session::invariant` holds only if the Triple's and the Braid's own invariants hold. -/
theorem session_invariant_leaves (s : lifecycle.Session) (h : lifecycle.Session.invariant s = ok true) :
    tacenta_triple.State.invariant s.triple = ok true ∧ tacenta_braid.Braid.invariant s.braid = ok true := by
  unfold lifecycle.Session.invariant at h
  obtain ⟨b, -, h⟩ := bind_eq_ok_inv h
  split at h
  · unfold lifecycle.Session.leaf_invariants at h
    obtain ⟨b1, hb1, h⟩ := bind_eq_ok_inv h
    split at h
    · rename_i hb1t; subst hb1t; exact ⟨hb1, h⟩
    · simp at h
  · simp at h

/-- **Export then import is the identity on sessions of the covered shape**: for every session `s` that
passes `Session::invariant` and has `CodecShape`, `export` returns, and `import` of the exported bytes
accepts and returns `s` itself, every field equal.  Under five laws about opaque functions on the path
(`ZeroizingVecRoundTrip`, `OptionBranchSome`, `VecAsSlice`, `DhPrivateBytesRoundTrip`,
`DhPublicBytesRoundTrip`). -/
theorem export_import_of_shape (hz : ZeroizingVecRoundTrip) (hbr : OptionBranchSome)
    (hsl : VecAsSlice) (hpriv : DhPrivateBytesRoundTrip) (hpub : DhPublicBytesRoundTrip)
    (s : lifecycle.Session) (epoch : U64) (auth : tacenta_braid.Auth) (e : U64)
    (c1 c2 : tacenta_spqr.Chain) (p : lifecycle.PendingInitial) (shape : CodecShape s epoch auth e c1 c2 p)
    (hinv : lifecycle.Session.invariant s = ok true) :
    ∃ z v, lifecycle.Session.export s = ok z ∧
      zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref vecInst z = ok v ∧
      lifecycle.Session.import (alloc.vec.Vec.deref v) = ok (core.result.Result.Ok s) := by
  obtain ⟨hinvT, hinvB⟩ := session_invariant_leaves s hinv
  obtain ⟨zp, pa, hzp, hpa, hfpa⟩ := hpriv s.ratchet_private
  obtain ⟨oa, hoa, hfoa⟩ := hpub s.our_identity_public
  obtain ⟨pea, hpea, hfpea⟩ := hpub s.peer_identity_public
  obtain ⟨ea, hea, hfea⟩ := hpub p.ephemeral_public
  obtain ⟨z, hz', vt, vb, vp, v, hv, hvt, hvb, hvp, hvv⟩ := Std.WP.spec_imp_exists
    (export_spec hz s epoch auth e c1 c2 p shape zp pa hzp hpa oa pea ea hoa hpea hea)
  refine ⟨z, v, hz', hv, ?_⟩
  obtain ⟨r, hr, hrs⟩ := Std.WP.spec_imp_exists
    (import_unchecked_spec hbr s epoch auth e c1 c2 p shape hinvT hinvB vt vb vp pa oa pea ea hvt hvb hvp
      hfpa hfoa hfpea hfea (alloc.vec.Vec.deref v) (by simpa [alloc.vec.Vec.deref] using hvv))
  subst hrs
  unfold lifecycle.Session.import
  rw [hr]
  have hsv : alloc.vec.Vec.as_slice Global v = ok (alloc.vec.Vec.deref v) := hsl v
  simp only [bind_tc_ok, core.result.Result.Insts.CoreOpsTry.branch, hz', hv, hsv, slice_ne_self,
    Bool.false_eq_true, ↓reduceIte, hinv]


/-- The associated data `identity_ad` returns is 66 bytes, given that the public-key byte view returns
(here from `DhPublicBytesRoundTrip`). -/
theorem identity_ad_length_of (hpub : DhPublicBytesRoundTrip) (a b : tacenta_boundary.dh.PublicKeyBytes)
    (v : alloc.vec.Vec U8) (h : lifecycle.identity_ad a b = ok v) : v.val.length = 66 := by
  obtain ⟨xa, hxa, -⟩ := dhPublicBytesRoundTrip_is.mp hpub a
  obtain ⟨xb, hxb, -⟩ := dhPublicBytesRoundTrip_is.mp hpub b
  have hs : lifecycle.identity_ad a b ⦃ w => w.val.length = 66 ⦄ := by
    simp only [lifecycle.identity_ad, tacenta_session_unit.encode_ec, hxa, hxb, bind_tc_ok]
    unfold tacenta_session.encode_ec tacenta_session.associated_data
    simp only [lift, bind_tc_ok, alloc.vec.Vec.with_capacity]
    step*
    all_goals (try simp_all [alloc.vec.Vec.deref, Array.to_slice, alloc.vec.Vec.with_capacity,
      alloc.vec.Vec.new, arr32_len])
    all_goals (try scalar_tac)
  obtain ⟨w, hw, hl⟩ := Std.WP.spec_imp_exists hs
  rw [h] at hw
  cases hw
  exact hl

/-! ## The one compiler-evaluated fact under `export`

Every statement here that names `Session::export` lists one compiler-trust axiom,
`tacenta_session_unit.lifecycle.PrekeyStore.to_bytes._native.decide.ax_1`.  It is not a proof step of this
file: the generated `Session.export` passes the message of its `debug_assert_eq!(out.len(), capacity, ...)`
to Aeneas's `toStr`, whose length bound is discharged by `decide +native` in the generated definition.
`PrekeyStore::to_bytes` carries the same check with the same text and is generated first, so Lean reuses the
axiom it made there for the identical proposition, and the axiom carries that function's name.  The axiom
states `decide (<message>.toByteArray.size ≤ U32.max) = true`.

`export_message_fits` proves that same proposition (syntactically the axiom's type) with the kernel alone, so
the fact the compiler is trusted with is true.  The dependency itself stays: the generated definition refers to
the axiom, not to this theorem, and removing it needs a change to the Rust message or to Aeneas's `toStr`,
at a re-translation. -/

/-- The panic message of the two size checks in `PrekeyStore::to_bytes` and `Session::export` fits a `u32`
length: the proposition of the compiler-trust axiom those definitions carry, proved by the kernel. -/
theorem export_message_fits :
    decide ("the size arithmetic above drifted from the encoding".toByteArray.size ≤ U32.max) = true := by
  rw [decide_eq_true_iff, String.size_toByteArray]
  simp only [U32.max, U32.numBits, UScalarTy.numBits]
  decide

end Tacenta.UnitLifecycleSessionRoundTrip

/-! ## Pins

The constants each result depends on, and the statement of each result and definition, held by the
build.  `attest.py` requires every one of them (`REQUIRED_PINS`, `REQUIRED_STATEMENT_PINS`,
`REQUIRED_PRINT_FORM`). -/

/--
info: 'Tacenta.UnitLifecycleSessionRoundTrip.export_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kem.EncapsState,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_kem.EncapsState.to_bytes,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.to_bytes,
 tacenta_session_unit.zeroize.Zeroizing.new,
 tacenta_session_unit.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.to_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_session_unit.zeroize.Zeroize.Blanket.zeroize,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 tacenta_session_unit.alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.lifecycle.PrekeyStore.to_bytes._native.decide.ax_1]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleSessionRoundTrip.export_spec

/--
info: 'Tacenta.UnitLifecycleSessionRoundTrip.import_unchecked_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kem.CT1_LEN,
 tacenta_session_unit.tacenta_kem.CT2_LEN,
 tacenta_session_unit.tacenta_kem.EK_VECTOR_LEN,
 tacenta_session_unit.tacenta_kem.EncapsState,
 tacenta_session_unit.tacenta_kem.HEADER_LEN,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair,
 tacenta_session_unit.tacenta_kem.validate_ek,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_kem.EncapsState.from_bytes,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.from_bytes,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.header,
 tacenta_session_unit.core.num.Usize.div_ceil,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.from_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.from_bytes,
 tacenta_session_unit.core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual,
 tacenta_session_unit.core.option.Option.Insts.CoreOpsTry_traitTry.branch]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleSessionRoundTrip.import_unchecked_spec

/--
info: 'Tacenta.UnitLifecycleSessionRoundTrip.slice_ne_self' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleSessionRoundTrip.slice_ne_self

/--
info: 'Tacenta.UnitLifecycleSessionRoundTrip.session_invariant_leaves' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kem.CT1_LEN,
 tacenta_session_unit.tacenta_kem.CT2_LEN,
 tacenta_session_unit.tacenta_kem.EK_VECTOR_LEN,
 tacenta_session_unit.tacenta_kem.EncapsState,
 tacenta_session_unit.tacenta_kem.HEADER_LEN,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair,
 tacenta_session_unit.tacenta_kem.validate_ek,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_boundary.dh.is_prime_order_public,
 tacenta_session_unit.tacenta_boundary.kem.ciphertext_len,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.header,
 tacenta_session_unit.core.num.Usize.div_ceil,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.public_key,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.from_bytes,
 tacenta_session_unit.core.option.Option.Insts.CoreCmpPartialEqOption.eq]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleSessionRoundTrip.session_invariant_leaves

/--
info: 'Tacenta.UnitLifecycleSessionRoundTrip.export_import_of_shape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kdf.hkdf_sha256,
 tacenta_session_unit.tacenta_kdf.hmac_sha256,
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
 tacenta_session_unit.tacenta_boundary.xeddsa.verify,
 tacenta_session_unit.tacenta_kem.EncapsState.from_bytes,
 tacenta_session_unit.tacenta_kem.EncapsState.to_bytes,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.from_bytes,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.generate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.header,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.to_bytes,
 tacenta_session_unit.zeroize.Zeroizing.new,
 tacenta_session_unit.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.Pair.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.TupleABC.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.alloc.vec.Vec.as_slice,
 tacenta_session_unit.alloc.vec.Vec.capacity,
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
 tacenta_session_unit.zeroize.Zeroize.Blanket.zeroize,
 tacenta_session_unit.tacenta_kem.EncapsState.Insts.CoreCloneClone.clone,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 tacenta_session_unit.alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.core.option.Option.Insts.CoreCloneClone.clone,
 tacenta_session_unit.core.option.Option.Insts.CoreCmpPartialEqOption.eq,
 tacenta_session_unit.core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual,
 tacenta_session_unit.core.option.Option.Insts.CoreOpsTry_traitTry.branch,
 tacenta_session_unit.lifecycle.PrekeyStore.to_bytes._native.decide.ax_1,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes.eq,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleSessionRoundTrip.export_import_of_shape

/--
info: 'Tacenta.UnitLifecycleSessionRoundTrip.identity_ad_length_of' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kdf.hkdf_sha256,
 tacenta_session_unit.tacenta_kdf.hmac_sha256,
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
 tacenta_session_unit.tacenta_boundary.kem.decapsulate,
 tacenta_session_unit.tacenta_boundary.kem.encapsulate,
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
 tacenta_session_unit.zeroize.Zeroize.Blanket.zeroize,
 tacenta_session_unit.tacenta_kem.EncapsState.Insts.CoreCloneClone.clone,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 tacenta_session_unit.alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.core.option.Option.Insts.CoreCloneClone.clone,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes.eq,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleSessionRoundTrip.identity_ad_length_of

/--
info: 'Tacenta.UnitLifecycleSessionRoundTrip.export_message_fits' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleSessionRoundTrip.export_message_fits

/--
info: Tacenta.UnitLifecycleSessionRoundTrip.export_spec : Tacenta.UnitLifecycleSessionCodec.ZeroizingVecRoundTrip →
  ∀ (s : tacenta_session_unit.lifecycle.Session) (epoch : Aeneas.Std.U64)
    (auth : tacenta_session_unit.tacenta_braid.Auth) (e : Aeneas.Std.U64)
    (c1 c2 : tacenta_session_unit.tacenta_spqr.Chain) (p : tacenta_session_unit.lifecycle.PendingInitial),
    Tacenta.UnitLifecycleSessionRoundTrip.CodecShape s epoch auth e c1 c2 p →
      ∀ (zp : tacenta_session_unit.zeroize.Zeroizing (Aeneas.Std.Array Aeneas.Std.U8 32#usize))
        (pa : Aeneas.Std.Array Aeneas.Std.U8 32#usize),
        s.ratchet_private.to_bytes = Aeneas.Std.Result.ok zp →
          tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref Tacenta.UnitLifecycleSessionCodec.arrInst
                zp =
              Aeneas.Std.Result.ok pa →
            ∀ (oa pea ea : Aeneas.Std.Array Aeneas.Std.U8 32#usize),
              s.our_identity_public.as_bytes = Aeneas.Std.Result.ok oa →
                s.peer_identity_public.as_bytes = Aeneas.Std.Result.ok pea →
                  p.ephemeral_public.as_bytes = Aeneas.Std.Result.ok ea →
                    Aeneas.Std.WP.spec s.export fun z =>
                      ∃ vt vb vp v,
                        tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref
                              Tacenta.UnitLifecycleSessionCodec.vecInst z =
                            Aeneas.Std.Result.ok v ∧
                          ↑vt = Tacenta.UnitLifecycleSessionCodec.tripleEnc s.triple e c1 c2 ∧
                            ↑vb = Tacenta.UnitLifecycleSessionCodec.braidEnc epoch auth ∧
                              ↑vp = Tacenta.UnitLifecycleSessionCodec.pendEnc p ea ∧
                                ↑v = Tacenta.UnitLifecycleSessionRoundTrip.sessionEnc vt vb pa s.identity_ad oa pea vp
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleSessionRoundTrip.export_spec

/--
info: Tacenta.UnitLifecycleSessionRoundTrip.import_unchecked_spec : Tacenta.UnitLifecycleSessionCodec.OptionBranchSome →
  ∀ (s : tacenta_session_unit.lifecycle.Session) (epoch : Aeneas.Std.U64)
    (auth : tacenta_session_unit.tacenta_braid.Auth) (e : Aeneas.Std.U64)
    (c1 c2 : tacenta_session_unit.tacenta_spqr.Chain) (p : tacenta_session_unit.lifecycle.PendingInitial),
    Tacenta.UnitLifecycleSessionRoundTrip.CodecShape s epoch auth e c1 c2 p →
      s.triple.invariant = Aeneas.Std.Result.ok true →
        s.braid.invariant = Aeneas.Std.Result.ok true →
          ∀ (vt vb vp : Aeneas.Std.alloc.vec.Vec Aeneas.Std.U8)
            (pa oa pea ea : Aeneas.Std.Array Aeneas.Std.U8 32#usize),
            ↑vt = Tacenta.UnitLifecycleSessionCodec.tripleEnc s.triple e c1 c2 →
              ↑vb = Tacenta.UnitLifecycleSessionCodec.braidEnc epoch auth →
                ↑vp = Tacenta.UnitLifecycleSessionCodec.pendEnc p ea →
                  tacenta_session_unit.tacenta_boundary.dh.PrivateKey.from_bytes pa =
                      Aeneas.Std.Result.ok s.ratchet_private →
                    tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.from_bytes oa =
                        Aeneas.Std.Result.ok s.our_identity_public →
                      tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.from_bytes pea =
                          Aeneas.Std.Result.ok s.peer_identity_public →
                        tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.from_bytes ea =
                            Aeneas.Std.Result.ok p.ephemeral_public →
                          ∀ (bytes : Aeneas.Std.Slice Aeneas.Std.U8),
                            ↑bytes = Tacenta.UnitLifecycleSessionRoundTrip.sessionEnc vt vb pa s.identity_ad oa pea vp →
                              Aeneas.Std.WP.spec (tacenta_session_unit.lifecycle.Session.import_unchecked bytes)
                                fun r => r = Aeneas.Std.core.result.Result.Ok s
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleSessionRoundTrip.import_unchecked_spec

/--
info: Tacenta.UnitLifecycleSessionRoundTrip.slice_ne_self : ∀ (x : Aeneas.Std.Slice Aeneas.Std.U8),
  Aeneas.Std.core.cmp.impls.PartialEqShared.ne
      (tacenta_session_unit.Slice.Insts.CoreCmpPartialEqSlice Aeneas.Std.core.cmp.PartialEqU8) x x =
    Aeneas.Std.Result.ok false
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleSessionRoundTrip.slice_ne_self

/--
info: Tacenta.UnitLifecycleSessionRoundTrip.session_invariant_leaves : ∀ (s : tacenta_session_unit.lifecycle.Session),
  s.invariant = Aeneas.Std.Result.ok true →
    s.triple.invariant = Aeneas.Std.Result.ok true ∧ s.braid.invariant = Aeneas.Std.Result.ok true
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleSessionRoundTrip.session_invariant_leaves

/--
info: Tacenta.UnitLifecycleSessionRoundTrip.export_import_of_shape : Tacenta.UnitLifecycleSessionCodec.ZeroizingVecRoundTrip →
  Tacenta.UnitLifecycleSessionCodec.OptionBranchSome →
    Tacenta.UnitLifecycleSessionCodec.VecAsSlice →
      Tacenta.UnitLifecycleSessionCodec.DhPrivateBytesRoundTrip →
        Tacenta.UnitLifecycleSessionCodec.DhPublicBytesRoundTrip →
          ∀ (s : tacenta_session_unit.lifecycle.Session) (epoch : Aeneas.Std.U64)
            (auth : tacenta_session_unit.tacenta_braid.Auth) (e : Aeneas.Std.U64)
            (c1 c2 : tacenta_session_unit.tacenta_spqr.Chain) (p : tacenta_session_unit.lifecycle.PendingInitial),
            Tacenta.UnitLifecycleSessionRoundTrip.CodecShape s epoch auth e c1 c2 p →
              s.invariant = Aeneas.Std.Result.ok true →
                ∃ z v,
                  s.export = Aeneas.Std.Result.ok z ∧
                    tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref
                          Tacenta.UnitLifecycleSessionCodec.vecInst z =
                        Aeneas.Std.Result.ok v ∧
                      tacenta_session_unit.lifecycle.Session.import v.deref =
                        Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok s)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleSessionRoundTrip.export_import_of_shape

/--
info: Tacenta.UnitLifecycleSessionRoundTrip.identity_ad_length_of : Tacenta.UnitLifecycleSessionCodec.DhPublicBytesRoundTrip →
  ∀ (a b : tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes) (v : Aeneas.Std.alloc.vec.Vec Aeneas.Std.U8),
    tacenta_session_unit.lifecycle.identity_ad a b = Aeneas.Std.Result.ok v → (↑v).length = 66
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleSessionRoundTrip.identity_ad_length_of

/--
info: Tacenta.UnitLifecycleSessionRoundTrip.export_message_fits : decide
    ("the size arithmetic above drifted from the encoding".toByteArray.size ≤ Aeneas.Std.U32.max) =
  true
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleSessionRoundTrip.export_message_fits

/--
info: structure Tacenta.UnitLifecycleSessionRoundTrip.CodecShape (s : tacenta_session_unit.lifecycle.Session)
  (epoch : Aeneas.Std.U64) (auth : tacenta_session_unit.tacenta_braid.Auth) (e : Aeneas.Std.U64)
  (c1 c2 : tacenta_session_unit.tacenta_spqr.Chain) (p : tacenta_session_unit.lifecycle.PendingInitial) : Prop
number of parameters: 7
fields:
  Tacenta.UnitLifecycleSessionRoundTrip.CodecShape.braid : s.braid =
      { state := tacenta_session_unit.tacenta_braid.State.KeysUnsampled epoch auth }
  Tacenta.UnitLifecycleSessionRoundTrip.CodecShape.epochNotMax : epoch ≠ Aeneas.Std.core.num.U64.MAX
  Tacenta.UnitLifecycleSessionRoundTrip.CodecShape.classicalSkipped : ↑s.triple.classical.skipped = []
  Tacenta.UnitLifecycleSessionRoundTrip.CodecShape.chains : ↑s.triple.post_quantum.chains =
      [(e, { send := some c1, receive := some c2 })]
  Tacenta.UnitLifecycleSessionRoundTrip.CodecShape.sparseSkipped : ↑s.triple.post_quantum.skipped = []
  Tacenta.UnitLifecycleSessionRoundTrip.CodecShape.identityAd : (↑s.identity_ad).length ≤ 65536
  Tacenta.UnitLifecycleSessionRoundTrip.CodecShape.pending : s.pending_initial = some p
  Tacenta.UnitLifecycleSessionRoundTrip.CodecShape.ciphertext : (↑p.kem_ciphertext).length ≤ 65536
  Tacenta.UnitLifecycleSessionRoundTrip.CodecShape.established : s.established_ephemeral = none
constructor:
  Tacenta.UnitLifecycleSessionRoundTrip.CodecShape.mk {s : tacenta_session_unit.lifecycle.Session}
    {epoch : Aeneas.Std.U64} {auth : tacenta_session_unit.tacenta_braid.Auth} {e : Aeneas.Std.U64}
    {c1 c2 : tacenta_session_unit.tacenta_spqr.Chain} {p : tacenta_session_unit.lifecycle.PendingInitial}
    (braid : s.braid = { state := tacenta_session_unit.tacenta_braid.State.KeysUnsampled epoch auth })
    (epochNotMax : epoch ≠ Aeneas.Std.core.num.U64.MAX) (classicalSkipped : ↑s.triple.classical.skipped = [])
    (chains : ↑s.triple.post_quantum.chains = [(e, { send := some c1, receive := some c2 })])
    (sparseSkipped : ↑s.triple.post_quantum.skipped = []) (identityAd : (↑s.identity_ad).length ≤ 65536)
    (pending : s.pending_initial = some p) (ciphertext : (↑p.kem_ciphertext).length ≤ 65536)
    (established : s.established_ephemeral = none) :
    Tacenta.UnitLifecycleSessionRoundTrip.CodecShape s epoch auth e c1 c2 p
-/
#guard_msgs in
#print Tacenta.UnitLifecycleSessionRoundTrip.CodecShape

/--
info: def Tacenta.UnitLifecycleSessionRoundTrip.sessionEnc : Aeneas.Std.alloc.vec.Vec Aeneas.Std.U8 →
  Aeneas.Std.alloc.vec.Vec Aeneas.Std.U8 →
    Aeneas.Std.Array Aeneas.Std.U8 32#usize →
      Aeneas.Std.alloc.vec.Vec Aeneas.Std.U8 →
        Aeneas.Std.Array Aeneas.Std.U8 32#usize →
          Aeneas.Std.Array Aeneas.Std.U8 32#usize → Aeneas.Std.alloc.vec.Vec Aeneas.Std.U8 → List Aeneas.Std.U8 :=
fun vt vb pa ad oa pea vp =>
  1#u8 ::
    (Tacenta.UnitLifecycleSessionCodec.lenEnc vt.deref ++
      (Tacenta.UnitLifecycleSessionCodec.lenEnc vb.deref ++
        (↑pa ++
          (Tacenta.UnitLifecycleSessionCodec.lenEnc ad.deref ++
            (↑oa ++ (↑pea ++ 1#u8 :: (Tacenta.UnitLifecycleSessionCodec.lenEnc vp.deref ++ [0#u8])))))))
-/
#guard_msgs in
#print Tacenta.UnitLifecycleSessionRoundTrip.sessionEnc
