import Translation.UnitLifecycleT3

/-!
# `decode_ec`: what the translated curve-key decoder returns, on every input

`Translation/SessionUnitSessionT1.lean` proves `decode_ec_spec`: the translated
`tacenta_session::decode_ec` returns, and when it returns `some k` the key is the thirty-two bytes
after the curve type byte. It says nothing about when it returns `none`. This module states the
whole function, both ways:

* `decodeEc_eq_some_iff`, `decodeEc_eq_none_iff`: the model's `DecodeEC`, `Model.Lifecycle.decodeEc`,
  accepts a byte string exactly when it is 33 bytes long, its first byte is the curve type byte and
  its other thirty-two bytes are a canonical curve public key, and then returns those bytes.
* `session_decode_ec_refines`: the translated `tacenta_session::decode_ec` returns, on every slice,
  the model's result carried across the byte boundary: `none` where the model returns `none`, and
  `some k` with `k`'s bytes the model's key where it returns `some`.
* `session_decode_ec_characterization`: the same, stated directly: `none` exactly when the length is
  not 33, the curve byte is wrong, or the key is not canonical; otherwise `some k` with `k` the
  thirty-two bytes after the curve byte.
* `decode_ec_refines`: the Session unit's `decode_ec` (`session-unit/src/lib.rs`), which wraps the
  key in the opaque `PublicKeyBytes`, returns the model's result read through the DH view, given
  `DhCodecOf`.

The proofs rest on the generated code and the model alone; the only hypothesis anywhere in the
module is `DhCodecOf` in `decode_ec_refines`, the byte view of the opaque public-key type.
-/

namespace Tacenta.SessionUnitDecodeEc

open Aeneas Aeneas.Std Result
open tacenta_session_unit
open Tacenta.UnitLifecycleT3

/-! ## The model's `DecodeEC` -/

theorem decodeEc_eq_some_iff (e k : List UInt8) :
    Model.Lifecycle.decodeEc e = some k ↔
      e.length = 33 ∧ e.head? = some Model.Messages.ecCurveByte ∧
        Model.Messages.canonicalKey (e.drop 1) = true ∧ k = e.drop 1 := by
  unfold Model.Lifecycle.decodeEc Model.Messages.checkCurve Model.Messages.checkKey
  generalize hd : e.drop 1 = d
  by_cases hl : e.length = 33
  · rw [if_pos hl]
    by_cases hc : e.head? = some Model.Messages.ecCurveByte
    · cases hk : Model.Messages.canonicalKey d
      · simp [hl, hc]
      · constructor
        · intro h
          simp [hc] at h
          exact ⟨hl, hc, rfl, h.symm⟩
        · rintro ⟨_, _, _, rfl⟩
          simp [hc]
    · simp [hl, hc]
  · simp [hl]

theorem decodeEc_eq_none_iff (e : List UInt8) :
    Model.Lifecycle.decodeEc e = none ↔
      e.length ≠ 33 ∨ e.head? ≠ some Model.Messages.ecCurveByte ∨
        Model.Messages.canonicalKey (e.drop 1) = false := by
  unfold Model.Lifecycle.decodeEc Model.Messages.checkCurve Model.Messages.checkKey
  generalize hd : e.drop 1 = d
  by_cases hl : e.length = 33
  · rw [if_pos hl]
    by_cases hc : e.head? = some Model.Messages.ecCurveByte
    · cases Model.Messages.canonicalKey d <;> simp [hl, hc]
    · simp [hl, hc]
  · simp [hl]

/-- A key `DecodeEC` returns is thirty-two bytes long. -/
theorem decodeEc_length {e k : List UInt8} (h : Model.Lifecycle.decodeEc e = some k) :
    k.length = 32 := by
  obtain ⟨hl, _, _, rfl⟩ := (decodeEc_eq_some_iff e k).1 h
  simp [hl]

/-! ## The translated decoder -/

/-- The two canonicity predicates of the generated code, the one the Session crate's port defines
for `is_canonical_x25519` and the one the wire crate's port defines, are the same function. -/
theorem canonicalX25519_session_eq_wire (k : Array Std.U8 32#usize) :
    Tacenta.SessionUnitSessionT1.canonicalX25519 k = Tacenta.SessionUnitWireT1.canonicalX25519 k :=
  rfl

/-- The thirty-two bytes the decoder's loop copied are the bytes after the curve byte. -/
theorem key_eq_drop (bytes : Slice Std.U8) (k : Array Std.U8 32#usize)
    (hlen : bytes.val.length = 33) (hk : ∀ j, j < 32 → k.val[j]! = bytes.val[j + 1]!) :
    k.val = bytes.val.drop 1 := by
  have hkl : k.val.length = 32 := Tacenta.SessionUnitSessionT1.array32_length k
  apply List.ext_getElem
  · simp [hkl, hlen]
  · intro j h1 h2
    have hj : j < 32 := by omega
    have h := hk j hj
    rw [getElem!_pos k.val j h1, getElem!_pos bytes.val (j + 1) (by omega)] at h
    simp [h]

theorem arrayOf_eq_drop (bytes : Slice Std.U8) (k : Array Std.U8 32#usize)
    (hk : k.val = bytes.val.drop 1) :
    arrayOf k = (sliceOf bytes).drop 1 := by
  simp [arrayOf, sliceOf, hk]

theorem head_sliceOf (bytes : Slice Std.U8) (h : 0 < bytes.val.length) :
    (sliceOf bytes).head? = some (Tacenta.SessionUnitBraidT3.u8 (bytes.val[0]!)) := by
  cases hb : bytes.val with
  | nil => simp [hb] at h
  | cons b rest => simp [sliceOf, hb]

theorem u8_eq_curve_iff (b : Std.U8) :
    Tacenta.SessionUnitBraidT3.u8 b = Model.Messages.ecCurveByte ↔
      b = tacenta_session.ENCODE_EC_CURVE25519 := by
  have h := Tacenta.SessionUnitWireT3.byteOf_inj b tacenta_session.ENCODE_EC_CURVE25519
  have hc : Tacenta.SessionUnitWireT3.byteOf tacenta_session.ENCODE_EC_CURVE25519 =
      Model.Messages.ecCurveByte := by
    simp [Tacenta.SessionUnitWireT3.byteOf, tacenta_session.ENCODE_EC_CURVE25519,
      Model.Messages.ecCurveByte]
  rw [← hc]
  exact h

/-- **`tacenta_session::decode_ec` computes `DecodeEC`.** On every slice it returns, and what it
returns, carried across the byte boundary, is the model's result: `none` exactly where
`Model.Lifecycle.decodeEc` is `none`, and `some k` whose bytes are the model's key otherwise. -/
theorem session_decode_ec_refines (bytes : Slice Std.U8) :
    tacenta_session.decode_ec bytes ⦃ fun r =>
      r.map arrayOf = Model.Lifecycle.decodeEc (sliceOf bytes) ⦄ := by
  have hlenSlice : (sliceOf bytes).length = bytes.val.length := by simp [sliceOf]
  unfold tacenta_session.decode_ec
  by_cases hl : Slice.len bytes = tacenta_session.ENCODE_EC_LEN
  · have hlen : bytes.val.length = 33 := by
      simp only [Slice.len, tacenta_session.ENCODE_EC_LEN] at hl
      scalar_tac
    have h0 : 0 < bytes.val.length := by omega
    simp only [hl, if_pos]
    have hhead := head_sliceOf bytes h0
    by_cases hc : bytes.val[0]! = tacenta_session.ENCODE_EC_CURVE25519
    · have hloop := Tacenta.SessionUnitSessionT1.decode_ec_loop_spec_zero bytes
        (Array.repeat 32#usize 0#u8) hlen
      obtain ⟨k1, hk1call, hk1⟩ := Std.WP.spec_imp_exists hloop
      have hkdrop := key_eq_drop bytes k1 hlen hk1
      obtain ⟨b, hbcall, hb⟩ :=
        Std.WP.spec_imp_exists (Tacenta.SessionUnitSessionT1.is_canonical_x25519_spec k1)
      have hcanon : Model.Messages.canonicalKey ((sliceOf bytes).drop 1) =
          Tacenta.SessionUnitSessionT1.canonicalX25519 k1 := by
        rw [← arrayOf_eq_drop bytes k1 hkdrop, canonicalX25519_session_eq_wire]
        exact Tacenta.SessionUnitWireT3.canonicalKey_bytesOf k1
      have hcurve : (sliceOf bytes).head? = some Model.Messages.ecCurveByte := by
        rw [hhead, (u8_eq_curve_iff _).2 hc]
      have hidx : Slice.index_usize bytes 0#usize = ok (bytes.val[0]!) := by
        have := Slice.index_usize_spec bytes 0#usize (by simp; omega)
        obtain ⟨v, hv, hvv⟩ := Std.WP.spec_imp_exists this
        rw [hv, hvv]
        simp [getElem!_pos bytes.val 0 h0]
      simp only [hidx, bind_tc_ok, hc, if_true, hk1call, hbcall]
      cases hbv : b
      · have hfalse : Model.Messages.canonicalKey ((sliceOf bytes).drop 1) = false := by
          rw [hcanon, ← hb, hbv]
        have hnone : Model.Lifecycle.decodeEc (sliceOf bytes) = none :=
          (decodeEc_eq_none_iff _).2 (Or.inr (Or.inr hfalse))
        simp [hnone]
      · have htrue : Model.Messages.canonicalKey ((sliceOf bytes).drop 1) = true := by
          rw [hcanon, ← hb, hbv]
        have hsome : Model.Lifecycle.decodeEc (sliceOf bytes) = some (arrayOf k1) :=
          (decodeEc_eq_some_iff _ _).2
            ⟨by rw [hlenSlice, hlen], hcurve, htrue, arrayOf_eq_drop bytes k1 hkdrop⟩
        simp [hsome]
    · have hcurve : (sliceOf bytes).head? ≠ some Model.Messages.ecCurveByte := by
        rw [hhead]
        intro h
        apply hc
        exact (u8_eq_curve_iff _).1 (Option.some.inj h)
      have hnone : Model.Lifecycle.decodeEc (sliceOf bytes) = none :=
        (decodeEc_eq_none_iff _).2 (Or.inr (Or.inl hcurve))
      have hidx : Slice.index_usize bytes 0#usize = ok (bytes.val[0]!) := by
        have := Slice.index_usize_spec bytes 0#usize (by simp; omega)
        obtain ⟨v, hv, hvv⟩ := Std.WP.spec_imp_exists this
        rw [hv, hvv]
        simp [getElem!_pos bytes.val 0 h0]
      simp only [hidx, bind_tc_ok, hc, if_false]
      simp [hnone]
  · have hlen : bytes.val.length ≠ 33 := by
      intro h
      apply hl
      simp only [Slice.len, tacenta_session.ENCODE_EC_LEN]
      scalar_tac
    have hnone : Model.Lifecycle.decodeEc (sliceOf bytes) = none :=
      (decodeEc_eq_none_iff _).2 (Or.inl (by rw [hlenSlice]; exact hlen))
    simp only [hl, if_false]
    simp [hnone]

/-- **The translated `decode_ec`, characterized.** It returns on every slice. It returns `none`
exactly when the slice is not 33 bytes long, or its first byte is not the curve type byte, or its
last thirty-two bytes are not a canonical curve public key; otherwise it returns `some k`, and `k`
holds those thirty-two bytes. This adds the rejecting direction to `decode_ec_spec`. -/
theorem session_decode_ec_characterization (bytes : Slice Std.U8) :
    ∃ r, tacenta_session.decode_ec bytes = ok r ∧
      (r = none ↔ (sliceOf bytes).length ≠ 33 ∨
        (sliceOf bytes).head? ≠ some Model.Messages.ecCurveByte ∨
        Model.Messages.canonicalKey ((sliceOf bytes).drop 1) = false) ∧
      (∀ k, r = some k → arrayOf k = (sliceOf bytes).drop 1) := by
  obtain ⟨r, hcall, hr⟩ := Std.WP.spec_imp_exists (session_decode_ec_refines bytes)
  refine ⟨r, hcall, ?_, ?_⟩
  · rw [← decodeEc_eq_none_iff, ← hr]
    cases r <;> simp
  · intro k hk
    subst hk
    exact ((decodeEc_eq_some_iff _ _).1 hr.symm).2.2.2

/-- **The Session unit's `decode_ec` computes `DecodeEC` through the DH view.** It returns on every
slice, `none` exactly where the model's `decodeEc` is `none`, and otherwise a public key whose view
is the model's key. `DhCodecOf` is the byte view of the opaque `PublicKeyBytes` that
`PublicKeyBytes::from_bytes` builds. -/
theorem decode_ec_refines (dh : DhView) (codec : DhCodecOf dh) (bytes : Slice Std.U8) :
    ∃ r, decode_ec bytes = ok r ∧
      r.map dh.publicKey = Model.Lifecycle.decodeEc (sliceOf bytes) := by
  obtain ⟨r, hcall, hr⟩ := Std.WP.spec_imp_exists (session_decode_ec_refines bytes)
  unfold decode_ec
  rw [hcall]
  cases r with
  | none => exact ⟨none, by simp, by simpa using hr⟩
  | some key =>
      obtain ⟨pk, hpk, hview⟩ := codec.fromBytes key
      refine ⟨some pk, by simp [hpk], ?_⟩
      rw [← hr]
      simp [hview]

end Tacenta.SessionUnitDecodeEc

/-! ## Pins

The axiom list and the statement of each result, and the body of the model's `decodeEc`, held by the
build. `attest.py` requires them (`REQUIRED_PINS`, `REQUIRED_STATEMENT_PINS`, `REQUIRED_PRINT_FORM`).
No result here lists a compiler-trust axiom. -/

/--
info: def Model.Lifecycle.decodeEc : Model.Lifecycle.Bytes → Option Model.Lifecycle.Key :=
fun e =>
  if List.length e = 33 then do
    Model.Messages.checkCurve e
    Model.Messages.checkKey (List.drop 1 e)
    pure (List.drop 1 e)
  else none
-/
#guard_msgs in
#print Model.Lifecycle.decodeEc

/--
info: 'Tacenta.SessionUnitDecodeEc.decodeEc_eq_some_iff' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.SessionUnitDecodeEc.decodeEc_eq_some_iff

/--
info: Tacenta.SessionUnitDecodeEc.decodeEc_eq_some_iff : ∀ (e k : List UInt8),
  Model.Lifecycle.decodeEc e = some k ↔
    e.length = 33 ∧
      e.head? = some Model.Messages.ecCurveByte ∧ Model.Messages.canonicalKey (List.drop 1 e) = true ∧ k = List.drop 1 e
-/
#guard_msgs in
#check @Tacenta.SessionUnitDecodeEc.decodeEc_eq_some_iff

/--
info: 'Tacenta.SessionUnitDecodeEc.decodeEc_eq_none_iff' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.SessionUnitDecodeEc.decodeEc_eq_none_iff

/--
info: Tacenta.SessionUnitDecodeEc.decodeEc_eq_none_iff : ∀ (e : List UInt8),
  Model.Lifecycle.decodeEc e = none ↔
    e.length ≠ 33 ∨ e.head? ≠ some Model.Messages.ecCurveByte ∨ Model.Messages.canonicalKey (List.drop 1 e) = false
-/
#guard_msgs in
#check @Tacenta.SessionUnitDecodeEc.decodeEc_eq_none_iff

/--
info: 'Tacenta.SessionUnitDecodeEc.decodeEc_length' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.SessionUnitDecodeEc.decodeEc_length

/--
info: @Tacenta.SessionUnitDecodeEc.decodeEc_length : ∀ {e k : List UInt8}, Model.Lifecycle.decodeEc e = some k → k.length = 32
-/
#guard_msgs in
#check @Tacenta.SessionUnitDecodeEc.decodeEc_length

/--
info: 'Tacenta.SessionUnitDecodeEc.canonicalX25519_session_eq_wire' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.SessionUnitDecodeEc.canonicalX25519_session_eq_wire

/--
info: Tacenta.SessionUnitDecodeEc.canonicalX25519_session_eq_wire : ∀ (k : Aeneas.Std.Array Aeneas.Std.U8 32#usize),
  Tacenta.SessionUnitSessionT1.canonicalX25519 k = Tacenta.SessionUnitWireT1.canonicalX25519 k
-/
#guard_msgs in
#check @Tacenta.SessionUnitDecodeEc.canonicalX25519_session_eq_wire

/--
info: 'Tacenta.SessionUnitDecodeEc.key_eq_drop' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.SessionUnitDecodeEc.key_eq_drop

/--
info: Tacenta.SessionUnitDecodeEc.key_eq_drop : ∀ (bytes : Aeneas.Std.Slice Aeneas.Std.U8)
  (k : Aeneas.Std.Array Aeneas.Std.U8 32#usize),
  (↑bytes).length = 33 → (∀ j < 32, (↑k)[j]! = (↑bytes)[j + 1]!) → ↑k = List.drop 1 ↑bytes
-/
#guard_msgs in
#check @Tacenta.SessionUnitDecodeEc.key_eq_drop

/--
info: 'Tacenta.SessionUnitDecodeEc.arrayOf_eq_drop' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.SessionUnitDecodeEc.arrayOf_eq_drop

/--
info: Tacenta.SessionUnitDecodeEc.arrayOf_eq_drop : ∀ (bytes : Aeneas.Std.Slice Aeneas.Std.U8)
  (k : Aeneas.Std.Array Aeneas.Std.U8 32#usize),
  ↑k = List.drop 1 ↑bytes → Tacenta.UnitLifecycleT3.arrayOf k = List.drop 1 (Tacenta.UnitLifecycleT3.sliceOf bytes)
-/
#guard_msgs in
#check @Tacenta.SessionUnitDecodeEc.arrayOf_eq_drop

/--
info: 'Tacenta.SessionUnitDecodeEc.head_sliceOf' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.SessionUnitDecodeEc.head_sliceOf

/--
info: Tacenta.SessionUnitDecodeEc.head_sliceOf : ∀ (bytes : Aeneas.Std.Slice Aeneas.Std.U8),
  0 < (↑bytes).length →
    List.head? (Tacenta.UnitLifecycleT3.sliceOf bytes) = some (Tacenta.SessionUnitBraidT3.u8 (↑bytes)[0]!)
-/
#guard_msgs in
#check @Tacenta.SessionUnitDecodeEc.head_sliceOf

/--
info: 'Tacenta.SessionUnitDecodeEc.u8_eq_curve_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.SessionUnitDecodeEc.u8_eq_curve_iff

/--
info: Tacenta.SessionUnitDecodeEc.u8_eq_curve_iff : ∀ (b : Aeneas.Std.U8),
  Tacenta.SessionUnitBraidT3.u8 b = Model.Messages.ecCurveByte ↔
    b = tacenta_session_unit.tacenta_session.ENCODE_EC_CURVE25519
-/
#guard_msgs in
#check @Tacenta.SessionUnitDecodeEc.u8_eq_curve_iff

/--
info: 'Tacenta.SessionUnitDecodeEc.session_decode_ec_refines' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.SessionUnitDecodeEc.session_decode_ec_refines

/--
info: Tacenta.SessionUnitDecodeEc.session_decode_ec_refines : ∀ (bytes : Aeneas.Std.Slice Aeneas.Std.U8),
  Aeneas.Std.WP.spec (tacenta_session_unit.tacenta_session.decode_ec bytes) fun r =>
    Option.map Tacenta.UnitLifecycleT3.arrayOf r = Model.Lifecycle.decodeEc (Tacenta.UnitLifecycleT3.sliceOf bytes)
-/
#guard_msgs in
#check @Tacenta.SessionUnitDecodeEc.session_decode_ec_refines

/--
info: 'Tacenta.SessionUnitDecodeEc.session_decode_ec_characterization' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.SessionUnitDecodeEc.session_decode_ec_characterization

/--
info: Tacenta.SessionUnitDecodeEc.session_decode_ec_characterization : ∀ (bytes : Aeneas.Std.Slice Aeneas.Std.U8),
  ∃ r,
    tacenta_session_unit.tacenta_session.decode_ec bytes = Aeneas.Std.Result.ok r ∧
      (r = none ↔
          List.length (Tacenta.UnitLifecycleT3.sliceOf bytes) ≠ 33 ∨
            List.head? (Tacenta.UnitLifecycleT3.sliceOf bytes) ≠ some Model.Messages.ecCurveByte ∨
              Model.Messages.canonicalKey (List.drop 1 (Tacenta.UnitLifecycleT3.sliceOf bytes)) = false) ∧
        ∀ (k : Aeneas.Std.Array Aeneas.Std.U8 32#usize),
          r = some k → Tacenta.UnitLifecycleT3.arrayOf k = List.drop 1 (Tacenta.UnitLifecycleT3.sliceOf bytes)
-/
#guard_msgs in
#check @Tacenta.SessionUnitDecodeEc.session_decode_ec_characterization

/--
info: 'Tacenta.SessionUnitDecodeEc.decode_ec_refines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.from_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.from_bytes]
-/
#guard_msgs in
#print axioms Tacenta.SessionUnitDecodeEc.decode_ec_refines

/--
info: Tacenta.SessionUnitDecodeEc.decode_ec_refines : ∀ (dh : Tacenta.UnitLifecycleT3.DhView),
  Tacenta.UnitLifecycleT3.DhCodecOf dh →
    ∀ (bytes : Aeneas.Std.Slice Aeneas.Std.U8),
      ∃ r,
        tacenta_session_unit.decode_ec bytes = Aeneas.Std.Result.ok r ∧
          Option.map dh.publicKey r = Model.Lifecycle.decodeEc (Tacenta.UnitLifecycleT3.sliceOf bytes)
-/
#guard_msgs in
#check @Tacenta.SessionUnitDecodeEc.decode_ec_refines
