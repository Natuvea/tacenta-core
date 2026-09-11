import Translation.WireInitialT3

/-!
# T3 for the prekey bundle decoder: the translated decoder computes what the model says

`decode_bundle` decodes a published prekey bundle, the bytes a sender fetches
from a directory it does not control before any session exists.
`Translation/WireT1.lean` proves it cannot fail; this proves that, for every
byte string, it returns `Ok` exactly when `Model.Messages.decodeBundle` returns
`some`, with the same keys, signatures, KEM prekey, one-time prekey and three
identifiers, and `Err` exactly when the model returns `none`.

## The model, by cases

The model decodes with a chain of `take?` and `readBe32`, the KEM prekey's
length read off the wire in the middle. Every way the chain fails is `none`, so
the order the code checks things in does not matter to the result, and
`decodeBundle_cases` puts the model in the simplest shape that says so: too
short for the fixed prefix, a wrong version or type byte, or otherwise
`decodeBundleRest` of the bytes after the framing, which is `some` exactly when
the length is the one the KEM prekey's length implies and the one-time prekey's
field is a valid spelling (`decodeOptionalKey`). The chain is unfolded with the
non-definitional `bind_take` and `bind_readBe32` from `WireInitialT3.lean`, for
the reason given there. The same reason rules out `simp` under the binder the
one-time prekey introduces: rewriting `be32At` there with `simp` leaves the
kernel the same unfolding, so `bundle_tail` states the identifiers once for
abstract lists and every use is a first-order `rw`.
-/

open Aeneas Aeneas.Std Result

namespace Tacenta.WireBundleT3

open Model.Messages
open Tacenta.WireInitialT3 (take?_of_length take?_none readBe32_none be32At be32At_lt
  getElem!_drop' bind_take bind_take_none bind_readBe32 bind_readBe32_none be32At_drop0)

/-- The bundle after its framing, one expression over fixed offsets and the KEM
prekey's length, read at offset 128. -/
def decodeBundleRest (rest : List UInt8) : Option Bundle :=
  if rest.length = 241 + be32At rest 128 then
    (decodeOptionalKey ((rest.drop (196 + be32At rest 128)).take 1)
        ((rest.drop (197 + be32At rest 128)).take 32)).bind fun oneTimePrekey => some
      { identityKey := rest.take 32
        signedPrekey := (rest.drop 32).take 32
        signedPrekeySig := (rest.drop 64).take 64
        kemPrekey := (rest.drop 132).take (be32At rest 128)
        kemPrekeySig := (rest.drop (132 + be32At rest 128)).take 64
        oneTimePrekey
        signedPrekeyId := UInt32.ofNat (be32At rest (229 + be32At rest 128))
        oneTimeId := UInt32.ofNat (be32At rest (233 + be32At rest 128))
        kemPrekeyId := UInt32.ofNat (be32At rest (237 + be32At rest 128)) }
  else none

theorem take_one_drop (l : List UInt8) (n : Nat) (h : n < l.length) : (l.drop n).take 1 = [l[n]!] := by
  rw [List.drop_eq_getElem_cons h]
  simp only [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]
  rfl

theorem singleton_beq (a b : UInt8) : ([a] == [b]) = (a == b) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq, List.cons.injEq]
  simp

theorem bundle_wrong_vt (v t : UInt8) (rest : List UInt8) (hvt : (v != version || t != typeBundle) = true) :
    decodeBundle (v :: t :: rest) = none := by
  simp only [decodeBundle, hvt, if_true]

theorem bundle_short_rest (v t : UInt8) (rest : List UInt8) (hvt : ¬(v != version || t != typeBundle) = true)
    (h : rest.length < 132) : decodeBundle (v :: t :: rest) = none := by
  simp only [decodeBundle, hvt, if_false, Option.bind_eq_bind, Bool.false_eq_true]
  by_cases h1 : rest.length < 32
  · rw [bind_take_none _ _ _ h1]
  rw [bind_take 32 rest _ (by omega)]
  by_cases h2 : rest.length < 64
  · rw [bind_take_none _ _ _ (by simp; omega)]
  rw [bind_take 32 _ _ (by simp; omega)]
  by_cases h3 : rest.length < 128
  · rw [bind_take_none _ _ _ (by simp; omega)]
  rw [bind_take 64 _ _ (by simp; omega)]
  rw [bind_readBe32_none _ _ (by simp; omega)]

theorem be32At_drop (l : List UInt8) (n k : Nat) : be32At (l.drop n) k = be32At l (n + k) := by
  simp only [be32At, getElem!_drop', Nat.add_assoc]

/-- The three identifiers and the end of the input, stated once for abstract
lists and an abstract one-time prekey decision. Stepping through them inside the
decoder's own term, under the binder the one-time prekey introduces, leaves the
kernel definitional unfolding to do on the byte sums; stated here, there is
nothing to unfold, and the decoder's proof uses it as a first-order rewrite. -/
theorem bundle_tail (x : Option (Option (List UInt8))) (r ik sp ss kp ks : List UInt8) :
    (x.bind fun a => (readBe32 r).bind fun b => (readBe32 b.2).bind fun c => (readBe32 c.2).bind fun d =>
        if d.2.isEmpty then
          pure ({ identityKey := ik
                  signedPrekey := sp
                  signedPrekeySig := ss
                  kemPrekey := kp
                  kemPrekeySig := ks
                  oneTimePrekey := a
                  signedPrekeyId := b.1
                  oneTimeId := c.1
                  kemPrekeyId := d.1 } : Bundle)
        else none)
      = if r.length = 12 then
          x.bind fun a => some
            { identityKey := ik
              signedPrekey := sp
              signedPrekeySig := ss
              kemPrekey := kp
              kemPrekeySig := ks
              oneTimePrekey := a
              signedPrekeyId := UInt32.ofNat (be32At r 0)
              oneTimeId := UInt32.ofNat (be32At r 4)
              kemPrekeyId := UInt32.ofNat (be32At r 8) }
        else none := by
  cases x with
  | none => simp only [Option.bind_none, ite_self]
  | some a =>
    simp only [Option.bind_some]
    by_cases h1 : r.length < 4
    · rw [bind_readBe32_none _ _ h1, if_neg (by omega)]
    rw [bind_readBe32 _ _ (by omega)]
    by_cases h2 : r.length < 8
    · rw [bind_readBe32_none _ _ (by simp; omega), if_neg (by omega)]
    rw [bind_readBe32 _ _ (by simp; omega)]
    by_cases h3 : r.length < 12
    · rw [bind_readBe32_none _ _ (by simp; omega), if_neg (by omega)]
    rw [bind_readBe32 _ _ (by simp; omega)]
    simp only [List.drop_drop, be32At_drop, pure, Nat.reduceAdd, Nat.add_zero]
    by_cases h4 : r.length = 12
    · rw [if_pos (by simp; omega), if_pos h4]
    · rw [if_neg (by simp; omega), if_neg h4]

theorem bundle_long_rest (v t : UInt8) (rest : List UInt8) (hvt : ¬(v != version || t != typeBundle) = true)
    (h0 : ¬ rest.length < 132) :
    decodeBundle (v :: t :: rest) = decodeBundleRest rest := by
  have hKlt := be32At_lt rest 128
  have hofnat : (UInt32.ofNat (be32At rest 128)).toNat = be32At rest 128 := by
    rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt hKlt]
  simp only [decodeBundle, hvt, Option.bind_eq_bind, Bool.false_eq_true, if_false]
  rw [bind_take 32 rest _ (by omega)]
  rw [bind_take 32 _ _ (by simp; omega)]
  rw [bind_take 64 _ _ (by simp; omega)]
  rw [bind_readBe32 _ _ (by simp; omega)]
  simp only [List.drop_drop, Nat.reduceAdd, be32At_drop0, hofnat]
  unfold decodeBundleRest
  by_cases hk : rest.length < 132 + be32At rest 128
  · rw [bind_take_none _ _ _ (by simp; omega), if_neg (by omega)]
  rw [bind_take _ _ _ (by simp; omega)]
  simp only [List.drop_drop]
  by_cases h1 : rest.length < 196 + be32At rest 128
  · rw [bind_take_none _ _ _ (by simp; omega), if_neg (by omega)]
  rw [bind_take 64 _ _ (by simp; omega)]
  simp only [List.drop_drop]
  by_cases h2 : rest.length < 197 + be32At rest 128
  · rw [bind_take_none _ _ _ (by simp; omega), if_neg (by omega)]
  rw [bind_take 1 _ _ (by simp; omega)]
  simp only [List.drop_drop]
  by_cases h3 : rest.length < 229 + be32At rest 128
  · rw [bind_take_none _ _ _ (by simp; omega), if_neg (by omega)]
  rw [bind_take 32 _ _ (by simp; omega)]
  simp only [List.drop_drop]
  rw [show 132 + be32At rest 128 + 64 = 196 + be32At rest 128 by omega,
    show 196 + be32At rest 128 + 1 = 197 + be32At rest 128 by omega,
    show 197 + be32At rest 128 + 32 = 229 + be32At rest 128 by omega]
  rw [bundle_tail]
  rw [List.length_drop, be32At_drop, be32At_drop, be32At_drop, Nat.add_zero]
  rw [show 229 + be32At rest 128 + 4 = 233 + be32At rest 128 by omega, show 229 + be32At rest 128 + 8 = 237 + be32At rest 128 by omega]
  by_cases hlen : rest.length = 241 + be32At rest 128
  · rw [if_pos (by omega), if_pos hlen]
  · rw [if_neg (by omega), if_neg hlen]

/-- **The model's bundle decoder, by cases**, in the order the code checks: too
short for the framing, a wrong version or type byte, or too short for the fixed
prefix is `none`; otherwise it is `decodeBundleRest` on the bytes after the
framing. -/
theorem decodeBundle_cases (l : List UInt8) :
    decodeBundle l =
      if l.length < 2 then none
      else if (l[0]! != version || l[1]! != typeBundle) = true then none
      else if l.length < 134 then none
      else decodeBundleRest (l.drop 2) := by
  match l with
  | [] => rfl
  | [_] => rfl
  | v :: t :: rest =>
    have hlen : ¬ (v :: t :: rest).length < 2 := by simp
    have h0 : (v :: t :: rest)[0]! = v := rfl
    have h1 : (v :: t :: rest)[1]! = t := rfl
    have hd : (v :: t :: rest).drop 2 = rest := rfl
    have hl : (v :: t :: rest).length = rest.length + 2 := rfl
    rw [if_neg hlen, h0, h1, hd, hl]
    by_cases hvt : (v != version || t != typeBundle) = true
    · rw [if_pos hvt, bundle_wrong_vt v t rest hvt]
    rw [if_neg hvt]
    by_cases h3 : rest.length < 132
    · rw [if_pos (by omega), bundle_short_rest v t rest hvt h3]
    rw [if_neg (by omega), bundle_long_rest v t rest hvt h3]

/-! ## The code's decoder against the model's -/

open Tacenta.WireT3 tacenta_wire
open Tacenta.WireInitialT3 (bne_byteOf' cast_u32_usize_val bytesOf_getElem!' be32At_bytesOf_drop2
  be32At_bytesOf_drop2')

/-- The model's bundle for a decoded one, field by field. -/
def bundleOf (b : WireBundle) : Bundle :=
  { identityKey := bytesOf b.identity_key.val
    signedPrekey := bytesOf b.signed_prekey.val
    signedPrekeySig := bytesOf b.signed_prekey_signature.val
    kemPrekey := bytesOf b.kem_prekey.val
    kemPrekeySig := bytesOf b.kem_prekey_signature.val
    oneTimePrekey := b.one_time_prekey.map fun k => bytesOf k.val
    signedPrekeyId := UInt32.ofNat b.signed_prekey_id.val
    oneTimeId := UInt32.ofNat b.one_time_prekey_id.val
    kemPrekeyId := UInt32.ofNat b.kem_prekey_id.val }

@[simp] theorem byteOf_type_bundle : byteOf TYPE_BUNDLE = typeBundle := by
  simp [TYPE_BUNDLE, byteOf, typeBundle]

/-- "Every byte of the thirty-two at `p` is zero", in the model's list form and
the code's indexed form. -/
theorem all_zero_at_iff (l : List Std.U8) (p : Nat) (h : p + 32 ≤ l.length) :
    (((bytesOf l).drop p).take 32).all (· == 0) = true ↔ ∀ j, j < 32 → l[p + j]! = 0#u8 := by
  rw [bytesOf_drop_take, List.all_eq_true]
  constructor
  · intro hall j hj
    have hmem : byteOf l[p + j]! ∈ bytesOf ((l.drop p).take 32) := by
      simp only [bytesOf, List.mem_map]
      refine ⟨l[p + j]!, ?_, rfl⟩
      rw [List.mem_iff_getElem]
      refine ⟨j, by simp; omega, ?_⟩
      simp [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem (by omega : p + j < l.length)]
    have := hall _ hmem
    simp only [beq_iff_eq] at this
    have h0 : byteOf l[p + j]! = byteOf 0#u8 := by rw [this]; rfl
    exact (byteOf_inj _ _).mp h0
  · intro hall x hx
    rw [List.mem_iff_getElem] at hx
    obtain ⟨j, hj, rfl⟩ := hx
    have hj' : j < 32 := by simp [bytesOf] at hj; omega
    have hz := hall j hj'
    rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem (by omega : p + j < l.length)] at hz
    simp only [Option.getD_some] at hz
    simp only [bytesOf, List.getElem_map, List.getElem_take, List.getElem_drop, hz, beq_iff_eq]
    rfl

/-- Deciding the one-time prekey's field computes what the model's
`decodeOptionalKey` says of the same thirty-three bytes. -/
@[step]
theorem one_time_prekey_at_spec (bytes : Slice Std.U8) (at1 : Usize) (h : at1.val + 33 ≤ bytes.length) :
    one_time_prekey_at bytes at1 ⦃ r => match r with
      | core.result.Result.Ok o =>
          decodeOptionalKey (((bytesOf bytes.val).drop at1.val).take 1)
            (((bytesOf bytes.val).drop (at1.val + 1)).take 32) = some (o.map fun k => bytesOf k.val)
      | core.result.Result.Err _ =>
          decodeOptionalKey (((bytesOf bytes.val).drop at1.val).take 1)
            (((bytesOf bytes.val).drop (at1.val + 1)).take 32) = none ⦄ := by
  have hl : at1.val + 33 ≤ bytes.val.length := by simpa [Slice.length] using h
  rw [take_one_drop _ _ (by simp; omega)]
  simp only [decodeOptionalKey, singleton_beq, bytesOf_getElem!', byteOf_beq_zero, byteOf_beq_one]
  unfold one_time_prekey_at
  step*
  all_goals (try simp (disch := omega) only [getElem!_pos])
  all_goals (try rw [← present_post])
  -- a zero presence byte over non-zero padding: refused
  on_goal 1 =>
    have hp0 : present = 0#u8 := by assumption
    have hi1 : (i1 != 0#u8) = true := by assumption
    have hz : ¬ ∀ j, j < 32 → bytes.val[at1.val + 1 + j]! = 0#u8 := fun hall => by
      have := i1_post.mpr (by simpa [i_post] using hall); simp_all
    have hne : ((List.take 32 (List.drop (at1.val + 1) (bytesOf bytes.val))).all fun x => x == 0) = false := by
      rw [← Bool.not_eq_true, all_zero_at_iff _ _ (by omega)]; exact hz
    simp only [hp0, beq_self_eq_true, if_true, hne, Bool.false_eq_true, if_false]
  -- a zero presence byte over zero padding: absent
  on_goal 1 =>
    have hp0 : present = 0#u8 := by assumption
    have hi1 : ¬(i1 != 0#u8) = true := by assumption
    have hall : ((List.take 32 (List.drop (at1.val + 1) (bytesOf bytes.val))).all fun x => x == 0) = true := by
      rw [all_zero_at_iff _ _ (by omega)]
      have := i1_post.mp (UScalar.eq_of_val_eq (by simpa using hi1))
      simpa [i_post] using this
    simp only [hp0, beq_self_eq_true, if_true, hall, Option.map]
  -- the copy's two lengths agree
  on_goal 1 => simp_all [Slice.length, Array.repeat]
  -- a presence byte of one: present, and the key is the thirty-two bytes after it
  on_goal 1 =>
    have hp0 : ¬present = 0#u8 := by assumption
    have hp1 : present = 1#u8 := by assumption
    have hkey : (to_slice_mut_back s2).val = (bytes.val.drop (at1.val + 1)).take 32 := by
      rw [s_post2, s2_post, Array.from_slice_val _ _ (by simp [s1_post1, List.slice, i_post, i1_post]; omega),
        s1_post1, i_post, i1_post]
      simp [List.slice]
    have h0f : (present == 0#u8) = false := by simpa using hp0
    have h1t : (present == 1#u8) = true := by simpa using hp1
    simp only [h0f, h1t, Bool.false_eq_true, if_false, if_true, Option.map, hkey,
      bytesOf, List.map_take, List.map_drop]
  -- any other presence byte: refused
  on_goal 1 =>
    have hp0 : ¬present = 0#u8 := by assumption
    have hp1 : ¬present = 1#u8 := by assumption
    have h0f : (present == 0#u8) = false := by simpa using hp0
    have h1f : (present == 1#u8) = false := by simpa using hp1
    simp only [h0f, h1f, Bool.false_eq_true, if_false]


theorem drop_drop2 (l : List UInt8) (a b : Nat) : (l.drop a).drop b = l.drop (a + b) := by
  simp [List.drop_drop]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 1000000 in
/-- **The translated decoder computes what the model says, on every byte string.**

An `Ok` carries exactly the keys, signatures, KEM prekey, one-time prekey and
identifiers `Model.Messages.decodeBundle` returns; an `Err` is exactly the
model's `none`. Since the model accepts one spelling of each bundle, so does the
code. No hypothesis, and kernel-only.

**How it is closed, because the obvious way fails.** `scalar_tac` is not used
past `step*`: the four fixed-width copies leave zero-filled arrays in every
later goal's context, and its preprocessing exhausts the heartbeat budget on
them. The length facts come from `span_end`'s postconditions by `omega` and
`assumption` instead. The model side is rewritten with `rw`, never `simp`,
under the one-time prekey's binder, for the kernel reason given in the module
header. -/
theorem decode_bundle_refines (bytes : Slice Std.U8) :
    decode_bundle bytes ⦃ fun r => match r with
      | core.result.Result.Ok b => decodeBundle (bytesOf bytes.val) = some (bundleOf b)
      | core.result.Result.Err _ => decodeBundle (bytesOf bytes.val) = none ⦄ := by
  unfold decode_bundle
  simp only [BUNDLE_KEM_AT]
  step*
  all_goals first | (simp_all [Slice.length, Array.repeat]; done) | skip
  all_goals (rw [decodeBundle_cases]; simp only [bytesOf_length])
  all_goals first | (rw [if_pos (by scalar_tac)]) | skip
  all_goals (
    have h2 : 2 ≤ bytes.val.length := by scalar_tac
    rw [if_neg (by omega)]
    simp (disch := omega) only [bytesOf_getElem!, ← byteOf_version, ← byteOf_type_bundle, bne_byteOf']
    subst_vars)
  all_goals first
    | (rw [if_pos (by rw [Bool.or_eq_true]; exact Or.inl (by assumption))])
    | (rw [if_pos (by rw [Bool.or_eq_true]; exact Or.inr (by assumption))])
    | skip
  all_goals (rw [if_neg (by rw [Bool.or_eq_true, not_or]; exact ⟨by assumption, by assumption⟩)])
  all_goals (try simp only [cast_u32_usize_val] at *)
  all_goals first | (rw [if_pos (by assumption)]) | skip
  all_goals (rw [if_neg (by assumption)])
  all_goals (have hsl : bytes.length = bytes.val.length := rfl)
  all_goals (
    have hK : be32At ((bytesOf bytes.val).drop 2) 128 = i4.val := by
      rw [be32At_bytesOf_drop2, i4_post]
    unfold decodeBundleRest
    rw [List.length_drop, bytesOf_length, hK])
  all_goals first | (rw [if_neg (by omega)]) | skip
  -- the input does not end where the identifiers do
  on_goal 1 =>
    have hne : (end4 != bytes.len) = true := by assumption
    have hne' : end4.val ≠ bytes.length := by
      intro h; apply (bne_iff_ne.mp hne); apply UScalar.eq_of_val_eq
      simp [h]
    rw [if_neg (by omega)]
  -- success: every field is the model's
  on_goal 1 =>
    have hne : ¬(end4 != bytes.len) = true := by assumption
    have heq : end4.val = bytes.length := by
      simp only [bne_iff_ne, ne_eq, not_not] at hne
      rw [hne]; simp
    have he1 : end1.val = 134 + i4.val := o_post.1
    have he2 : end2.val = 198 + i4.val := by omega
    have he3 : end3.val = 231 + i4.val := by omega
    have hlen : (↑bytes : List Std.U8).length - 2 = 241 + i4.val := by omega
    rw [if_pos hlen, drop_drop2 _ 2 (196 + i4.val), drop_drop2 _ 2 (197 + i4.val),
      show 2 + (196 + i4.val) = end2.val by omega, show 2 + (197 + i4.val) = end2.val + 1 by omega]
    have hr := r_post
    try simp only at hr
    rw [hr, Option.bind_some, Option.some.injEq]
    unfold bundleOf
    rw [Bundle.mk.injEq]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · dsimp only
      rw [Array.from_slice_val _ _ (by simp [s1_post1, List.slice]; omega), s1_post1]
      simp [bytesOf, List.slice, List.map_take, List.map_drop]
    · dsimp only
      rw [Array.from_slice_val _ _ (by simp [s4_post1, List.slice]; omega), s4_post1, drop_drop2]
      simp [bytesOf, List.slice, List.map_take, List.map_drop]
    · dsimp only
      rw [Array.from_slice_val _ _ (by simp [s7_post1, List.slice]; omega), s7_post1, drop_drop2]
      simp [bytesOf, List.slice, List.map_take, List.map_drop]
    · dsimp only
      rw [s12_post1, drop_drop2, he1]
      simp [bytesOf, List.slice, List.map_take, List.map_drop]
    · dsimp only
      rw [Array.from_slice_val _ _ (by simp [s10_post1, List.slice]; omega), s10_post1, drop_drop2,
        show 2 + (132 + i4.val) = end1.val by omega]
      simp [bytesOf, List.slice, List.map_take, List.map_drop, he1, he2, Nat.add_sub_add_right]
    · rfl
    · dsimp only
      rw [be32At_bytesOf_drop2' _ _ end3.val (by omega), ← i6_post]
    · dsimp only
      rw [be32At_bytesOf_drop2' _ _ i7.val (by omega), ← i8_post]
    · dsimp only
      rw [be32At_bytesOf_drop2' _ _ i9.val (by omega), ← i10_post]
  -- the one-time prekey's field is not a valid spelling
  on_goal 1 =>
    have he2 : end2.val = 198 + i4.val := by omega
    rw [ite_eq_right_iff]
    intro _
    rw [drop_drop2 _ 2 (196 + i4.val), drop_drop2 _ 2 (197 + i4.val),
      show 2 + (196 + i4.val) = end2.val by omega, show 2 + (197 + i4.val) = end2.val + 1 by omega]
    have hr := r_post
    try simp only at hr
    rw [hr, Option.bind_none]

-- The axiom audit, enforced rather than asserted: the refinement rests on the
-- kernel's three axioms and nothing else. A proof that starts trusting something
-- new fails here.
/-- info: 'Tacenta.WireBundleT3.decode_bundle_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Tacenta.WireBundleT3.decode_bundle_refines

end Tacenta.WireBundleT3
