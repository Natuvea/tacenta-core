import Translation.WireT3

/-!
# T3 for the initial-message decoder: the translated decoder computes what the model says

`decode_initial` decodes an initial (prekey) message, the other kind of message
a peer sends. `Translation/WireT1.lean` proves it cannot fail; this proves that,
for every byte string, it returns `Ok` exactly when `Model.Messages.decodeInitial`
returns `some`, with the same two keys, KEM ciphertext, three prekey identifiers
and trailing ratchet message, and `Err` exactly when the model returns `none`.

## The model, by cases

The model decodes with a chain of `take?` and `readBe32`, the KEM ciphertext's
length read off the wire in the middle. `decodeInitial_cases` puts it in the
shape the code has: too short, a wrong version or type byte, or no room for the
two keys and the length is `none`, and otherwise the message is
`decodeInitialRest` of the bytes after the framing, one expression over fixed
offsets and that length.

**How the chain is unfolded, because the obvious way fails.** Rewriting the
chain with `Option.bind_some`, or any lemma proved by `rfl`, leaves the kernel to
check the rewrite by definitional unfolding inside a term that carries the
four-byte read as a `UInt32.ofNat` of a sum, and it gives up with "deep recursion
detected". `bind_take` and `bind_readBe32` state each step once, for an abstract
continuation, and are proved by rewriting; used in place of `Option.bind_some`
they leave the kernel nothing to unfold.
-/

open Aeneas Aeneas.Std Result

namespace Tacenta.WireInitialT3

open Model.Messages

open Model.Messages

/-- The model's four-byte read, proved in `WireT3.lean`. -/
theorem readBe32_of_length (l : List UInt8) (h : 4 ≤ l.length) :
    readBe32 l = some (UInt32.ofNat (l[0]!.toNat * 2^24 + l[1]!.toNat * 2^16 + l[2]!.toNat * 2^8 + l[3]!.toNat), l.drop 4) :=
  Tacenta.WireT3.readBe32_of_length l h

theorem take?_of_length (n : Nat) (l : List UInt8) (h : n ≤ l.length) :
    take? n l = some (l.take n, l.drop n) := by
  simp [take?, Nat.not_lt.mpr h]

theorem take?_none (n : Nat) (l : List UInt8) (h : l.length < n) : take? n l = none := by
  simp [take?, h]

theorem readBe32_none (l : List UInt8) (h : l.length < 4) : readBe32 l = none := by
  match l, h with
  | [], _ | [_], _ | [_, _], _ | [_, _, _], _ => rfl
  | _ :: _ :: _ :: _ :: _, h => simp only [List.length_cons] at h; omega

/-- Four big-endian bytes at position `k`, as a number. -/
def be32At (l : List UInt8) (k : Nat) : Nat :=
  l[k]!.toNat * 2^24 + l[k+1]!.toNat * 2^16 + l[k+2]!.toNat * 2^8 + l[k+3]!.toNat

theorem be32At_lt (l : List UInt8) (k : Nat) : be32At l k < 2 ^ 32 := by
  have := l[k]!.toNat_lt; have := l[k+1]!.toNat_lt; have := l[k+2]!.toNat_lt; have := l[k+3]!.toNat_lt
  simp only [be32At]; omega



theorem getElem!_drop' (l : List UInt8) (n i : Nat) : (l.drop n)[i]! = l[n + i]! := by
  simp [List.getElem!_eq_getElem?_getD, List.getElem?_drop]

/-- The long case against a right-hand side already written in terms of `rest`. -/
def decodeInitialRest (rest : List UInt8) : Option Initial :=
  if rest.length < 82 + be32At rest 66 then none
  else some
    { identity := rest.take 33
      ephemeral := (rest.drop 33).take 33
      kemCiphertext := (rest.drop 70).take (be32At rest 66)
      signedPrekeyId := UInt32.ofNat (be32At rest (70 + be32At rest 66))
      oneTimeId := UInt32.ofNat (be32At rest (74 + be32At rest 66))
      kemPrekeyId := UInt32.ofNat (be32At rest (78 + be32At rest 66))
      ratchetMessage := rest.drop (82 + be32At rest 66) }


/-- Binding a long-enough `take?`: the continuation gets the split, with no
definitional unfolding of `Option.bind` left for the kernel. -/
theorem bind_take {β : Type} (n : Nat) (l : List UInt8) (f : List UInt8 × List UInt8 → Option β)
    (h : n ≤ l.length) : (take? n l).bind f = f (l.take n, l.drop n) := by
  rw [take?_of_length n l h]; rfl

theorem bind_take_none {β : Type} (n : Nat) (l : List UInt8) (f : List UInt8 × List UInt8 → Option β)
    (h : l.length < n) : (take? n l).bind f = none := by
  rw [take?_none n l h]; rfl

theorem bind_readBe32 {β : Type} (l : List UInt8) (f : UInt32 × List UInt8 → Option β) (h : 4 ≤ l.length) :
    (readBe32 l).bind f = f (UInt32.ofNat (be32At l 0), l.drop 4) := by
  rw [readBe32_of_length l h]; rfl

theorem bind_readBe32_none {β : Type} (l : List UInt8) (f : UInt32 × List UInt8 → Option β)
    (h : l.length < 4) : (readBe32 l).bind f = none := by
  rw [readBe32_none l h]; rfl

theorem be32At_drop0 (l : List UInt8) (n : Nat) : be32At (l.drop n) 0 = be32At l n := by
  simp only [be32At, getElem!_drop', Nat.add_zero]

theorem long_rest (v t : UInt8) (rest : List UInt8) (hvt : ¬(v != version || t != typeInitial) = true)
    (h3 : ¬ rest.length < 70) :
    decodeInitial (v :: t :: rest) = decodeInitialRest rest := by
  have hKlt := be32At_lt rest 66
  have hofnat : (UInt32.ofNat (be32At rest 66)).toNat = be32At rest 66 := by
    rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt hKlt]
  simp only [decodeInitial, hvt, Option.bind_eq_bind]
  rw [bind_take 33 rest _ (by omega)]
  rw [bind_take 33 _ _ (by simp; omega)]
  rw [bind_readBe32 _ _ (by simp; omega)]
  simp only [List.drop_drop, Nat.reduceAdd, be32At_drop0, hofnat, Bool.false_eq_true, if_false]
  unfold decodeInitialRest
  by_cases hk : rest.length < 70 + be32At rest 66
  · rw [bind_take_none _ _ _ (by simp; omega), if_pos (by omega)]
  rw [bind_take _ _ _ (by simp; omega)]
  by_cases h1 : rest.length < 74 + be32At rest 66
  · rw [bind_readBe32_none _ _ (by simp; omega), if_pos (by omega)]
  rw [bind_readBe32 _ _ (by simp; omega)]
  by_cases h2 : rest.length < 78 + be32At rest 66
  · rw [bind_readBe32_none _ _ (by simp; omega), if_pos (by omega)]
  rw [bind_readBe32 _ _ (by simp; omega)]
  by_cases h4 : rest.length < 82 + be32At rest 66
  · rw [bind_readBe32_none _ _ (by simp; omega), if_pos h4]
  rw [bind_readBe32 _ _ (by simp; omega), if_neg h4]
  simp only [List.drop_drop, be32At_drop0, pure]
  rw [show 70 + be32At rest 66 + 4 = 74 + be32At rest 66 by omega,
    show 74 + be32At rest 66 + 4 = 78 + be32At rest 66 by omega,
    show 78 + be32At rest 66 + 4 = 82 + be32At rest 66 by omega]

/-- A header too short to hold the two keys and the ciphertext length decodes to
nothing. -/
theorem short_rest (v t : UInt8) (rest : List UInt8) (hvt : ¬(v != version || t != typeInitial) = true)
    (h3 : rest.length < 70) : decodeInitial (v :: t :: rest) = none := by
  simp only [decodeInitial, hvt, if_false, Option.bind_eq_bind, Bool.false_eq_true]
  by_cases h1 : rest.length < 33
  · rw [bind_take_none _ _ _ h1]
  rw [bind_take 33 rest _ (by omega)]
  by_cases h2 : rest.length < 66
  · rw [bind_take_none _ _ _ (by simp; omega)]
  rw [bind_take 33 _ _ (by simp; omega)]
  rw [bind_readBe32_none _ _ (by simp; omega)]

/-- The model's version or type check fails: nothing. -/
theorem wrong_vt (v t : UInt8) (rest : List UInt8) (hvt : (v != version || t != typeInitial) = true) :
    decodeInitial (v :: t :: rest) = none := by
  simp only [decodeInitial, hvt, if_true]

/-- **The model's initial-message decoder, by cases.** Too short, a wrong
version or type byte, or no room for the two keys and the ciphertext length is
`none`; otherwise it is `decodeInitialRest` on the bytes after the framing. -/
theorem decodeInitial_cases (l : List UInt8) :
    decodeInitial l =
      if l.length < 2 then none
      else if (l[0]! != version || l[1]! != typeInitial) = true then none
      else if l.length < 72 then none
      else decodeInitialRest (l.drop 2) := by
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
    by_cases hvt : (v != version || t != typeInitial) = true
    · rw [if_pos hvt, wrong_vt v t rest hvt]
    rw [if_neg hvt]
    by_cases h3 : rest.length < 70
    · rw [if_pos (by omega), short_rest v t rest hvt h3]
    rw [if_neg (by omega), long_rest v t rest hvt h3]

/-! ## The code's decoder against the model's -/

open Tacenta.WireT3 tacenta_wire

def initialOf (d : DecodedInitial) : Initial :=
  { identity := bytesOf d.identity.val
    ephemeral := bytesOf d.ephemeral.val
    kemCiphertext := bytesOf d.kem_ciphertext.val
    signedPrekeyId := UInt32.ofNat d.signed_prekey_id.val
    oneTimeId := UInt32.ofNat d.one_time_prekey_id.val
    kemPrekeyId := UInt32.ofNat d.kem_prekey_id.val
    ratchetMessage := bytesOf d.message.val }

@[simp] theorem byteOf_type_initial : byteOf TYPE_INITIAL = typeInitial := by
  simp [TYPE_INITIAL, byteOf, typeInitial]

theorem bne_byteOf' (x y : Std.U8) : (byteOf x != byteOf y) = (x != y) := by
  rw [Bool.eq_iff_iff, bne_iff_ne, bne_iff_ne]
  exact not_congr (byteOf_inj x y)

theorem ec_len_val : EC_LEN.val = 33 := by simp [EC_LEN]

theorem cast_u32_usize_val (x : Std.U32) : (UScalar.cast UScalarTy.Usize x).val = x.val := by
  scalar_tac

/-- Indexing across the boundary needs no bound: out of range both sides are
zero. -/
theorem bytesOf_getElem!' (l : List Std.U8) (j : Nat) : (bytesOf l)[j]! = byteOf l[j]! := by
  by_cases hj : j < l.length
  · simp [bytesOf, List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hj]
  · simp [bytesOf, List.getElem!_eq_getElem?_getD, List.getElem?_eq_none (by omega : l.length ≤ j)]; rfl

/-- The ciphertext length the model reads, after the framing bytes, in the
code's bytes. -/
theorem be32At_bytesOf_drop2 (l : List Std.U8) (k : Nat) :
    be32At ((bytesOf l).drop 2) k =
      l[k + 2]!.val * 2^24 + l[k + 3]!.val * 2^16 + l[k + 4]!.val * 2^8 + l[k + 5]!.val := by
  simp only [be32At, getElem!_drop', bytesOf_getElem!', byteOf_toNat]
  simp only [show 2 + k = k + 2 by omega, show 2 + (k + 1) = k + 3 by omega, show 2 + (k + 2) = k + 4 by omega,
    show 2 + (k + 3) = k + 5 by omega]

/-- The same, at the absolute position `j` the code reads. -/
theorem be32At_bytesOf_drop2' (l : List Std.U8) (k j : Nat) (hj : k + 2 = j) :
    be32At ((bytesOf l).drop 2) k =
      l[j]!.val * 2^24 + l[j + 1]!.val * 2^16 + l[j + 2]!.val * 2^8 + l[j + 3]!.val := by
  subst hj
  rw [be32At_bytesOf_drop2]

@[step]
theorem be32_at_spec (bytes : Slice Std.U8) (at1 : Usize) (h : at1.val + 4 ≤ bytes.length) :
    be32_at bytes at1 ⦃ v => v.val =
      bytes.val[at1.val]!.val * 2^24 + bytes.val[at1.val + 1]!.val * 2^16
        + bytes.val[at1.val + 2]!.val * 2^8 + bytes.val[at1.val + 3]!.val ⦄ := by
  unfold be32_at
  step*
  rw [u32_from_be_val]
  have hl : at1.val + 3 < bytes.val.length := by simpa [Slice.length] using (by omega : at1.val + 3 < bytes.length)
  simp only [i_post, i2_post, i4_post, i6_post, i1_post, i3_post, i5_post,
    List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem (by omega : at1.val < bytes.val.length),
    List.getElem?_eq_getElem (by omega : at1.val + 1 < bytes.val.length),
    List.getElem?_eq_getElem (by omega : at1.val + 2 < bytes.val.length),
    List.getElem?_eq_getElem hl, Option.getD_some]

set_option maxHeartbeats 1000000 in
/-- **The translated decoder computes what the model says, on every byte string.**

An `Ok` carries exactly the keys, ciphertext, identifiers and ratchet message
`Model.Messages.decodeInitial` returns; an `Err` is exactly the model's `none`.
No hypothesis, and kernel-only. -/
theorem decode_initial_refines (bytes : Slice Std.U8) :
    decode_initial bytes ⦃ fun r => match r with
      | core.result.Result.Ok d => decodeInitial (bytesOf bytes.val) = some (initialOf d)
      | core.result.Result.Err _ => decodeInitial (bytesOf bytes.val) = none ⦄ := by
  unfold decode_initial
  step*
  all_goals (rw [decodeInitial_cases]; simp only [bytesOf_length])
  all_goals first | (rw [if_pos (by scalar_tac)]) | skip
  all_goals (
    have h2 : 2 ≤ bytes.val.length := by scalar_tac
    rw [if_neg (by omega)]
    simp (disch := omega) only [bytesOf_getElem!, ← byteOf_version, ← byteOf_type_initial, bne_byteOf']
    subst_vars)
  all_goals first
    | (rw [if_pos (by rw [Bool.or_eq_true]; exact Or.inl (by assumption))])
    | (rw [if_pos (by rw [Bool.or_eq_true]; exact Or.inr (by assumption))])
    | skip
  all_goals (rw [if_neg (by rw [Bool.or_eq_true, not_or]; exact ⟨by assumption, by assumption⟩)])
  all_goals (simp only [ec_len_val, cast_u32_usize_val] at *)
  -- a field end past the input before offset 72: the model's short branch
  all_goals first | (rw [if_pos (by scalar_tac)]) | skip
  all_goals (
    rw [if_neg (by scalar_tac)]
    have hend2 : end2.val = 68 := by scalar_tac
    simp only [hend2] at i3_post
    have hK : be32At ((bytesOf bytes.val).drop 2) 66 = i3.val := by
      rw [be32At_bytesOf_drop2, i3_post]
    unfold decodeInitialRest
    simp only [List.length_drop, bytesOf_length, hK])
  -- the ciphertext or an identifier does not fit: the model's second short branch
  all_goals first | (rw [if_pos (by scalar_tac)]) | skip
  -- success: every field is the model's
  rw [if_neg (by scalar_tac)]
  have hend1 : end1.val = 35 := by scalar_tac
  have hend3 : end3.val = 72 := by scalar_tac
  have hend4 : end4.val = 72 + i3.val := by scalar_tac
  have hend5 : end5.val = 76 + i3.val := by scalar_tac
  have hend6 : end6.val = 80 + i3.val := by scalar_tac
  have hend7 : end7.val = 84 + i3.val := by scalar_tac
  simp only [Option.some.injEq, initialOf]
  rw [be32At_bytesOf_drop2' _ _ end4.val (by omega), ← i4_post,
    be32At_bytesOf_drop2' _ _ end5.val (by omega), ← i5_post,
    be32At_bytesOf_drop2' _ _ end6.val (by omega), ← i6_post]
  simp only [s_post1, s1_post1, s2_post1, s3_post1, List.slice, hend1, hend2, hend3, hend4, hend7,
    List.drop_drop, bytesOf_drop, Nat.reduceAdd, Nat.reduceSub, Nat.add_sub_cancel_left]
  rw [show 2 + (82 + i3.val) = 84 + i3.val by omega]
  simp only [bytesOf, List.map_take]

-- The axiom audit, enforced rather than asserted: the refinement rests on the
-- kernel's three axioms and nothing else. A proof that starts trusting something
-- new fails here.
/-- info: 'Tacenta.WireInitialT3.decode_initial_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Tacenta.WireInitialT3.decode_initial_refines

end Tacenta.WireInitialT3
