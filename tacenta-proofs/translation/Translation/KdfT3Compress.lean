/- Copied from an independent verified implementation of SHA-256, HMAC-SHA256 and HKDF-SHA256, the
source of `tacenta-core/kdf/src`: its proofs file `T3Compress.lean`, at commit `646fcdadb943`. Elaborated
here against the Session unit's own translation of those bodies. Changes from the source: the
translated crate's namespace is `tacenta_session_unit.tacenta_kdf`, the Session unit's
translation of `tacenta-kdf`; the source's other namespaces are renamed `KdfStandardModel`,
`Tacenta.KdfProof` and `KdfBridge`; its imports name this package's `Kdf*` modules.
Of the source's model only the SHA-256, HMAC and HKDF files were copied. "This repository" in the
prose below means that implementation, and a path such as `scripts/...` or `std/...` names one of
its files. -/
import Translation.KdfT3Base

/-!
# T3 for the SHA-256 compression function

`compress_spec`: the translated `sha256::compress` computes the model's
`Sha256.compress` (FIPS 180-4 §6.2.2) on the words of the state and the
parsed block, for every input.
-/

open Aeneas Aeneas.Std Result
namespace Tacenta.KdfProof
open tacenta_session_unit.tacenta_kdf KdfStandardModel

/-! ## Word-level bridges -/

theorem toW_xor (x y : U32) : toW (x ^^^ y) = toW x ^^^ toW y := rfl
theorem toW_and (x y : U32) : toW (x &&& y) = toW x &&& toW y := rfl
theorem toW_or (x y : U32) : toW (x ||| y) = toW x ||| toW y := rfl
theorem toW_not (x : U32) : toW (~~~x) = ~~~toW x := rfl
theorem toW_wrapping_add (x y : U32) :
    toW (core.num.U32.wrapping_add x y) = toW x + toW y := rfl

/-- `rotateRight` on 32-bit vectors is the model's `ROTR`, for 0 < n < 32. -/
theorem rotr_bv (x : BitVec 32) (n : Nat) (hn0 : 0 < n) (hn : n < 32) :
    UInt32.ofBitVec (x.rotateRight n) = Sha256.ROTR (UInt32.ofNat n) (UInt32.ofBitVec x) := by
  apply UInt32.toBitVec_inj.mp
  simp only [Sha256.ROTR, BitVec.rotateRight_def, Nat.mod_eq_of_lt hn, UInt32.toBitVec_or,
    UInt32.toBitVec_shiftRight, UInt32.toBitVec_shiftLeft, UInt32.toBitVec_sub,
    UInt32.toBitVec_ofNat]
  rw [BitVec.ushiftRight_eq' x (_ % 32), BitVec.shiftLeft_eq']
  have h1 : ((UInt32.ofNat n).toBitVec % 32).toNat = n := by simp; omega
  have h2 : ((32#32 - (UInt32.ofNat n).toBitVec) % 32).toNat = 32 - n := by
    simp [BitVec.toNat_sub]; omega
  rw [h1, h2]

/-- A logical right shift of a 32-bit vector is the model's `SHR`, for n < 32. -/
theorem shr_bv (x : BitVec 32) (n : Nat) (hn : n < 32) :
    UInt32.ofBitVec (x >>> n) = Sha256.SHR (UInt32.ofNat n) (UInt32.ofBitVec x) := by
  apply UInt32.toBitVec_inj.mp
  simp only [Sha256.SHR, UInt32.toBitVec_shiftRight]
  rw [BitVec.ushiftRight_eq' x (_ % 32)]
  have h1 : ((UInt32.ofNat n).toBitVec % 32).toNat = n := by simp; omega
  rw [h1]

/-- `u32::rotate_right` is the model's `ROTR`, for 0 < n < 32. -/
theorem toW_rotr (x n : U32) (hn0 : 0 < n.val) (hn : n.val < 32) :
    toW (core.num.U32.rotate_right x n) = Sha256.ROTR (UInt32.ofNat n.val) (toW x) :=
  rotr_bv x.bv n.val hn0 hn

/-- A translated byte's bits. -/
theorem toM_bv (b : U8) : (toM b).toBitVec = b.bv := by
  show BitVec.ofNat 8 b.bv.toNat = b.bv
  simp

/-- The translation's big-endian word assembly is the model's `word`. -/
theorem word_bv (b0 b1 b2 b3 : U8) :
    UInt32.ofBitVec ((((UScalar.cast .U32 b0).bv <<< 24 ||| (UScalar.cast .U32 b1).bv <<< 16) |||
      (UScalar.cast .U32 b2).bv <<< 8) ||| (UScalar.cast .U32 b3).bv) =
    Sha256.word (toM b0) (toM b1) (toM b2) (toM b3) := by
  apply UInt32.toBitVec_inj.mp
  simp only [Sha256.word, UInt32.toBitVec_or, UInt32.toBitVec_shiftLeft, UInt8.toBitVec_toUInt32,
    toM_bv, UScalar.cast]
  have h24 : (UInt32.toBitVec 24 % 32) = 24#32 := by decide
  have h16 : (UInt32.toBitVec 16 % 32) = 16#32 := by decide
  have h8 : (UInt32.toBitVec 8 % 32) = 8#32 := by decide
  rw [h24, h16, h8]
  simp only [BitVec.shiftLeft_eq', BitVec.toNat_ofNat]
  rfl

/-! ## The six logical functions -/

@[step]
theorem small_sigma0_spec (x : U32) :
    sha256.small_sigma0 x ⦃ r => toW r = Sha256.sigma0 (toW x) ⦄ := by
  unfold sha256.small_sigma0
  step*
  have e2 : toW i2 = toW i ^^^ toW i1 := by simp only [toW, i2_post2]; rfl
  have e3 : toW i3 = Sha256.SHR 3 (toW x) := by
    simp only [toW, i3_post2]; exact shr_bv _ 3 (by decide)
  rw [toW_xor, e2, e3, i_post, i1_post, toW_rotr x 7#u32 (by decide) (by decide),
    toW_rotr x 18#u32 (by decide) (by decide)]
  rfl

@[step]
theorem small_sigma1_spec (x : U32) :
    sha256.small_sigma1 x ⦃ r => toW r = Sha256.sigma1 (toW x) ⦄ := by
  unfold sha256.small_sigma1
  step*
  have e2 : toW i2 = toW i ^^^ toW i1 := by simp only [toW, i2_post2]; rfl
  have e3 : toW i3 = Sha256.SHR 10 (toW x) := by
    simp only [toW, i3_post2]; exact shr_bv _ 10 (by decide)
  rw [toW_xor, e2, e3, i_post, i1_post, toW_rotr x 17#u32 (by decide) (by decide),
    toW_rotr x 19#u32 (by decide) (by decide)]
  rfl

@[step]
theorem big_sigma0_spec (x : U32) :
    sha256.big_sigma0 x ⦃ r => toW r = Sha256.Sigma0 (toW x) ⦄ := by
  unfold sha256.big_sigma0
  step*
  have e2 : toW i2 = toW i ^^^ toW i1 := by simp only [toW, i2_post2]; rfl
  rw [toW_xor, e2, i_post, i1_post, i3_post, toW_rotr x 2#u32 (by decide) (by decide),
    toW_rotr x 13#u32 (by decide) (by decide), toW_rotr x 22#u32 (by decide) (by decide)]
  rfl

@[step]
theorem big_sigma1_spec (x : U32) :
    sha256.big_sigma1 x ⦃ r => toW r = Sha256.Sigma1 (toW x) ⦄ := by
  unfold sha256.big_sigma1
  step*
  have e2 : toW i2 = toW i ^^^ toW i1 := by simp only [toW, i2_post2]; rfl
  rw [toW_xor, e2, i_post, i1_post, i3_post, toW_rotr x 6#u32 (by decide) (by decide),
    toW_rotr x 11#u32 (by decide) (by decide), toW_rotr x 25#u32 (by decide) (by decide)]
  rfl

@[step]
theorem ch_spec (x y z : U32) :
    sha256.ch x y z ⦃ r => toW r = Sha256.Ch (toW x) (toW y) (toW z) ⦄ := by
  unfold sha256.ch
  step*
  have e0 : toW i = toW x &&& toW y := by simp only [toW, i_post2]; rfl
  have e2 : toW i2 = toW i1 &&& toW z := by simp only [toW, i2_post2]; rfl
  rw [toW_xor, e0, e2, i1_post, toW_not]
  rfl

@[step]
theorem maj_spec (x y z : U32) :
    sha256.maj x y z ⦃ r => toW r = Sha256.Maj (toW x) (toW y) (toW z) ⦄ := by
  unfold sha256.maj
  step*
  have e0 : toW i = toW x &&& toW y := by simp only [toW, i_post2]; rfl
  have e1 : toW i1 = toW x &&& toW z := by simp only [toW, i1_post2]; rfl
  have e2 : toW i2 = toW i ^^^ toW i1 := by simp only [toW, i2_post2]; rfl
  have e3 : toW i3 = toW y &&& toW z := by simp only [toW, i3_post2]; rfl
  rw [toW_xor, e2, e0, e1, e3]
  rfl

/-! ## List facts -/

theorem arr_len {α : Type} {n : Usize} (a : Array α n) : a.val.length = n.val := a.property

theorem take_succ_set {α : Type} (l : List α) (t : Nat) (v : α) (ht : t < l.length) :
    (l.set t v).take (t + 1) = l.take t ++ [v] := by
  rw [List.take_succ_eq_append_getElem (by simpa using ht)]
  simp only [List.getElem_set_self, List.take_set]
  rw [List.set_eq_of_length_le (by simp)]

/-- Reading the model's byte list at `j` where the translation read `x`. -/
theorem bytesOf_getD {n : Usize} (a : Array U8 n) (k : Usize) (j : Nat) (hk : k.val = j)
    {h : k.val < a.val.length} (x : U8) (hx : x = a.val[k.val]'h) :
    (bytesOf a).getD j 0 = toM x := by
  subst hk hx
  simp [bytesOf, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

theorem wordsOf_set {n : Usize} (w : Array U32 n) (t : Usize) (v : U32) :
    wordsOf (w.set t v) = (wordsOf w).set t.val (toW v) := by
  simp [wordsOf, Std.Array.set_val_eq, List.map_set]

theorem wordsOf_length {n : Usize} (w : Array U32 n) : (wordsOf w).length = n.val := by
  simp [wordsOf]

/-- Reading a prefix of a word array's words at `j < t` where the translation read `x`. -/
theorem wordsOf_take_getD {n : Usize} (w : Array U32 n) (t : Nat) (k : Usize) (j : Nat)
    (hk : k.val = j) (hj : j < t) {h : k.val < w.val.length} (x : U32) (hx : x = w.val[k.val]'h) :
    ((wordsOf w).take t).getD j 0 = toW x := by
  subst hk hx
  simp [wordsOf, List.getD_eq_getElem?_getD, hj, List.getElem?_eq_getElem h]

/-! ## The model's message schedule -/

theorem scheduleAux_succ (n : Nat) (W : List UInt32) :
    Sha256.scheduleAux (n + 1) W = Sha256.scheduleStep (Sha256.scheduleAux n W) := by
  induction n generalizing W with
  | zero => rfl
  | succ n ih => exact ih (Sha256.scheduleStep W)

theorem scheduleAux_length (n : Nat) (W : List UInt32) :
    (Sha256.scheduleAux n W).length = W.length + n := by
  induction n generalizing W with
  | zero => rfl
  | succ n ih =>
    show (Sha256.scheduleAux n (Sha256.scheduleStep W)).length = _
    rw [ih]; simp [Sha256.scheduleStep]; omega

theorem parseBlock_length (B : Bytes) : (Sha256.parseBlock B).length = 16 := by
  simp [Sha256.parseBlock]

/-! ## The first schedule loop: `W_t = M_t`, t < 16 -/

theorem schedule_loop0_spec (block : Array U8 64#usize) (w : Array U32 64#usize) (t : Usize)
    (ht : t.val ≤ 16)
    (h : (wordsOf w).take t.val = (Sha256.parseBlock (bytesOf block)).take t.val) :
    sha256.schedule_loop0 block w t ⦃ r =>
      r.2.val = 16 ∧ (wordsOf r.1).take 16 = Sha256.parseBlock (bytesOf block) ⦄ := by
  unfold sha256.schedule_loop0
  apply loop.spec_decr_nat
    (measure := fun p => 16 - p.2.val)
    (inv := fun p => p.2.val ≤ 16 ∧
      (wordsOf p.1).take p.2.val = (Sha256.parseBlock (bytesOf block)).take p.2.val)
  · rintro ⟨w1, tc⟩ ⟨hinv1, hinv2⟩
    dsimp only at hinv1 hinv2
    unfold sha256.schedule_loop0.body
    simp only []
    split
    · rename_i hlt
      have htl : tc.val < 16 := by scalar_tac
      step*
      refine ⟨by scalar_tac, ?_, by scalar_tac⟩
      have hw : toW i17 = Sha256.word (toM i1) (toM i5) (toM i10) (toM i15) := by
        simp only [toW, i17_post2, i13_post2, i8_post2, i3_post2, i7_post2, i12_post2, i2_post,
          i6_post, i11_post, i16_post]
        exact word_bv ..
      rw [a_post, wordsOf_set, t1_post, take_succ_set _ _ _ (by rw [wordsOf_length]; scalar_tac),
        hinv2, List.take_succ_eq_append_getElem (by rw [parseBlock_length]; omega)]
      congr 2
      rw [hw]
      simp only [Sha256.parseBlock, List.getElem_map, List.getElem_range]
      rw [bytesOf_getD block i _ (by scalar_tac) i1 i1_post,
        bytesOf_getD block i4 _ (by scalar_tac) i5 i5_post,
        bytesOf_getD block i9 _ (by scalar_tac) i10 i10_post,
        bytesOf_getD block i14 _ (by scalar_tac) i15 i15_post]
    · simp only [WP.spec_ok]
      have h16 : tc.val = 16 := by scalar_tac
      refine ⟨h16, ?_⟩
      rw [← h16, hinv2, List.take_of_length_le (by rw [parseBlock_length]; omega)]
  · exact ⟨ht, h⟩

/-! ## The second schedule loop: `W_t = σ1(W_(t−2)) + W_(t−7) + σ0(W_(t−15)) + W_(t−16)` -/

theorem schedule_loop1_spec (w : Array U32 64#usize) (t : Usize) (M : List UInt32)
    (hM : M.length = 16) (ht1 : 16 ≤ t.val) (ht2 : t.val ≤ 64)
    (h : (wordsOf w).take t.val = Sha256.scheduleAux (t.val - 16) M) :
    sha256.schedule_loop1 w t ⦃ r => wordsOf r = Sha256.schedule M ⦄ := by
  unfold sha256.schedule_loop1
  apply loop.spec_decr_nat
    (measure := fun p => 64 - p.2.val)
    (inv := fun p => 16 ≤ p.2.val ∧ p.2.val ≤ 64 ∧
      (wordsOf p.1).take p.2.val = Sha256.scheduleAux (p.2.val - 16) M)
  · rintro ⟨w1, tc⟩ ⟨hinv1, hinv2, hinv3⟩
    dsimp only at hinv1 hinv2 hinv3
    unfold sha256.schedule_loop1.body
    simp only []
    split
    · rename_i hlt
      have htl : tc.val < 64 := by scalar_tac
      step*
      refine ⟨by scalar_tac, by scalar_tac, ?_, by scalar_tac⟩
      have hW : (Sha256.scheduleAux (tc.val - 16) M).length = tc.val := by
        rw [scheduleAux_length, hM]; omega
      have hs : tc.val + 1 - 16 = (tc.val - 16) + 1 := by omega
      rw [a_post, wordsOf_set, t1_post, take_succ_set _ _ _ (by rw [wordsOf_length]; scalar_tac),
        hs, scheduleAux_succ, Sha256.scheduleStep, hW, ← hinv3]
      congr 2
      rw [wordsOf_take_getD w1 tc.val i _ (by scalar_tac) (by omega) i1 i1_post,
        wordsOf_take_getD w1 tc.val i3 _ (by scalar_tac) (by omega) i4 i4_post,
        wordsOf_take_getD w1 tc.val i6 _ (by scalar_tac) (by omega) i7 i7_post,
        wordsOf_take_getD w1 tc.val i10 _ (by scalar_tac) (by omega) i11 i11_post,
        ← i2_post, ← i8_post, i12_post, i9_post, i5_post]
      rfl
    · simp only [WP.spec_ok]
      have h64 : tc.val = 64 := by scalar_tac
      rw [h64] at hinv3
      rw [← List.take_of_length_le (l := wordsOf w1) (i := 64) (by rw [wordsOf_length]; simp), hinv3]
      rfl
  · exact ⟨ht1, ht2, h⟩

/-- The translated message schedule is the model's `schedule` of the parsed block. -/
@[step]
theorem schedule_spec (block : Array U8 64#usize) :
    sha256.schedule block ⦃ r =>
      wordsOf r = Sha256.schedule (Sha256.parseBlock (bytesOf block)) ⦄ := by
  unfold sha256.schedule
  step with schedule_loop0_spec block (Array.repeat 64#usize 0#u32) 0#usize (by simp) (by simp)
  rename_i t
  exact schedule_loop1_spec r t _ (parseBlock_length _) (by omega) (by omega)
    (by rw [r_post1]; exact r_post2)

/-! ## The round constants -/

/-- The translated table `K`, read word by word, is the model's `K` (FIPS 180-4 §4.2.2). -/
theorem wordsOf_K : wordsOf sha256.K = Sha256.K := by
  unfold sha256.K
  decide +kernel

/-- Reading a word array's words at `j` where the translation read `x`. -/
theorem wordsOf_getD {n : Usize} (w : Array U32 n) (k : Usize) (j : Nat)
    (hk : k.val = j) {h : k.val < w.val.length} (x : U32) (hx : x = w.val[k.val]'h) :
    (wordsOf w).getD j 0 = toW x := by
  subst hk hx
  simp [wordsOf, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

/-! ## The 64 rounds -/

/-- Eight translated words as the model's working variables. -/
def varsOf (a b c d e f g hh : U32) : Sha256.Vars :=
  ⟨toW a, toW b, toW c, toW d, toW e, toW f, toW g, toW hh⟩

theorem compress_loop_spec (w : Array U32 64#usize) (a b c d e f g hh : U32) (t : Usize)
    (v0 : Sha256.Vars) (ht : t.val ≤ 64)
    (h : varsOf a b c d e f g hh = (List.range t.val).foldl (Sha256.round (wordsOf w)) v0) :
    sha256.compress_loop w a b c d e f g hh t ⦃ r =>
      varsOf r.1 r.2.1 r.2.2.1 r.2.2.2.1 r.2.2.2.2.1 r.2.2.2.2.2.1 r.2.2.2.2.2.2.1 r.2.2.2.2.2.2.2 =
        (List.range 64).foldl (Sha256.round (wordsOf w)) v0 ⦄ := by
  unfold sha256.compress_loop
  apply loop.spec_decr_nat
    (measure := fun p => 64 - p.2.2.2.2.2.2.2.2.val)
    (inv := fun p => p.2.2.2.2.2.2.2.2.val ≤ 64 ∧
      varsOf p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2.1 p.2.2.2.2.2.2.1
        p.2.2.2.2.2.2.2.1 =
        (List.range p.2.2.2.2.2.2.2.2.val).foldl (Sha256.round (wordsOf w)) v0)
  · rintro ⟨a0, b0, c0, d0, e0, f0, g0, h0, tc⟩ ⟨hinv1, hinv2⟩
    dsimp only at hinv1 hinv2
    unfold sha256.compress_loop.body
    simp only []
    split
    · rename_i hlt
      have htl : tc.val < 64 := by scalar_tac
      step*
      refine ⟨by scalar_tac, ?_, by scalar_tac⟩
      have hK : toW i4 = Sha256.K.getD tc.val 0 := by
        rw [← wordsOf_K, wordsOf_getD sha256.K tc _ rfl i4 i4_post]
      have hWt : toW i6 = (wordsOf w).getD tc.val 0 := by
        rw [wordsOf_getD w tc _ rfl i6 i6_post]
      have h3 : t3.val = tc.val + 1 := by scalar_tac
      rw [h3, List.range_succ, List.foldl_append, ← hinv2]
      simp only [List.foldl_cons, List.foldl_nil, Sha256.round, varsOf, a1_post, e1_post,
        t1_post, t2_post, i5_post, i3_post, i1_post, toW_wrapping_add, i_post, i2_post, i7_post,
        i8_post, hK, hWt]
    · simp only [WP.spec_ok]
      have h64 : tc.val = 64 := by scalar_tac
      rw [hinv2, h64]
  · exact ⟨ht, h⟩

/-! ## The compression function -/

@[step]
theorem compress_spec (h : Array U32 8#usize) (block : Array U8 64#usize) :
    sha256.compress h block ⦃ r =>
      wordsOf r = Sha256.compress (wordsOf h) (Sha256.parseBlock (bytesOf block)) ⦄ := by
  unfold sha256.compress
  step as ⟨w, hw⟩
  step as ⟨a, ha⟩
  step as ⟨b, hb⟩
  step as ⟨c, hc⟩
  step as ⟨d, hd⟩
  step as ⟨e, he⟩
  step as ⟨f, hf⟩
  step as ⟨g, hg⟩
  step as ⟨hh, hhh⟩
  have hv0 : varsOf a b c d e f g hh =
      (List.range (0#usize).val).foldl (Sha256.round (wordsOf w)) (Sha256.initVars (wordsOf h)) := by
    simp only [varsOf, Sha256.initVars]
    rw [wordsOf_getD h 0#usize 0 rfl a ha, wordsOf_getD h 1#usize 1 rfl b hb,
      wordsOf_getD h 2#usize 2 rfl c hc, wordsOf_getD h 3#usize 3 rfl d hd,
      wordsOf_getD h 4#usize 4 rfl e he, wordsOf_getD h 5#usize 5 rfl f hf,
      wordsOf_getD h 6#usize 6 rfl g hg, wordsOf_getD h 7#usize 7 rfl hh hhh]
    rfl
  step with compress_loop_spec w a b c d e f g hh 0#usize _ (by simp) hv0
    as ⟨a1, b1, c1, d1, e1, f1, g1, hh1, hr⟩
  step*
  have q0 := (wordsOf_getD h 0#usize 0 rfl i i_post).symm
  have q1 := (wordsOf_getD h 1#usize 1 rfl i2 i2_post).symm
  have q2 := (wordsOf_getD h 2#usize 2 rfl i4 i4_post).symm
  have q3 := (wordsOf_getD h 3#usize 3 rfl i6 i6_post).symm
  have q4 := (wordsOf_getD h 4#usize 4 rfl i8 i8_post).symm
  have q5 := (wordsOf_getD h 5#usize 5 rfl i10 i10_post).symm
  have q6 := (wordsOf_getD h 6#usize 6 rfl i12 i12_post).symm
  have q7 := (wordsOf_getD h 7#usize 7 rfl i14 i14_post).symm
  simp only [Sha256.compress]
  rw [← hw, ← hr]
  simp only [wordsOf, Array.make, List.map_cons, List.map_nil, i1_post, i3_post, i5_post, i7_post,
    i9_post, i11_post, i13_post, i15_post, toW_wrapping_add, varsOf, q0, q1, q2, q3, q4, q5, q6,
    q7]

end Tacenta.KdfProof
