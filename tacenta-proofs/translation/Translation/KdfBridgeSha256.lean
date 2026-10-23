/- Copied from a separate, unpublished repository, written by the maintainer with tool assistance, that
holds a SHA-256, HMAC-SHA256 and HKDF-SHA256 with their proofs, the source of `tacenta-core/kdf/src` (pinned there by
commit and file digests): its bridge file `Sha256.lean`, at commit `646fcdadb943`. Elaborated
here against the Session unit's own translation of those bodies. Changes from the source: the
translated crate's namespace is `tacenta_session_unit.tacenta_kdf`, the Session unit's
translation of `tacenta-kdf`; the source's other namespaces are renamed `KdfStandardModel`,
`Tacenta.KdfProof` and `KdfBridge`; its imports name this package's `Kdf*` modules.
Of the source's model only the SHA-256, HMAC and HKDF files were copied. "This repository" in the
prose below means that implementation, and a path such as `scripts/...` or `std/...` names one of
its files. -/
import Translation.KdfModelSha256
import Model.Sha256

/-!
# Bridge: SHA-256

`KdfStandardModel.sha256 m = Model.Sha256.hash m` for every byte string `m`.

The two models compute the same FIPS 180-4 algorithm in different styles:
this repository's model on lists (`pad`, `parse` into `chunks 64`, a
`foldl compress H0` over `List UInt32`), tacenta-model's on arrays with
`Id.run do` loops. The proof goes component by component:

* `compress_normal`: tacenta-model's `compress` is three list folds (the
  legacy `Std.Range` `for` loops rewritten with
  `Std.Legacy.Range.forIn_eq_forIn_range'` and
  `List.forIn_pure_yield_eq_foldl`);
* `sched1_toList`, `sched2_toList`: the two schedule loops build
  `parseBlock B ++ 0^48` and then `schedule (parseBlock B)`;
* `toVars_rounds`: the 64-round loop on the `MProd` state is the `round`
  fold on `Vars`;
* `compress_toList`: one block, the two compression functions agree;
* `pad_eq`: the paddings agree (as lists, for every length, including the
  length-block reduction mod 2^64);
* `chunks_eq_map`, `hash_eq`: the block split and the outer fold agree.
-/

namespace KdfBridge.Sha256

open KdfStandardModel.Sha256 (ROTR SHR Sigma0 Sigma1 sigma0 sigma1 Ch Maj Vars
  initVars round schedule scheduleAux scheduleStep parseBlock word)

/-! ## Small facts about arrays, lists and `UInt32` addition -/

theorem arr_getElem!_eq_getD {α} [Inhabited α] (a : Array α) (i : Nat) :
    a[i]! = a.toList.getD i default := by
  rw [← Array.getElem!_toList, List.getElem!_eq_getElem?_getD,
    List.getD_eq_getElem?_getD]

theorem u32_add4_rev (a b c d : UInt32) : a + b + c + d = d + c + b + a := by
  rw [UInt32.add_comm a b, UInt32.add_comm (b + a) c, UInt32.add_comm (c + (b + a)) d]
  simp only [UInt32.add_assoc]

/-! ## tacenta-model's `compress` as list folds -/

/-- The first schedule loop's body (`for i in [0:16]`). -/
def step1 (block : Array UInt8) (w : Array UInt32) (i : Nat) : Array UInt32 :=
  w.set! i (Model.Sha256.beWord block[i * 4]! block[i * 4 + 1]! block[i * 4 + 2]!
    block[i * 4 + 3]!)

/-- The second schedule loop's body (`for t in [16:64]`). -/
def step2 (w : Array UInt32) (t : Nat) : Array UInt32 :=
  w.set! t (w[t - 16]! +
    (Model.Sha256.rotr w[t - 15]! 7 ^^^ Model.Sha256.rotr w[t - 15]! 18 ^^^ w[t - 15]! >>> 3) +
    w[t - 7]! +
    (Model.Sha256.rotr w[t - 2]! 17 ^^^ Model.Sha256.rotr w[t - 2]! 19 ^^^ w[t - 2]! >>> 10))

/-- The loop state of the round loop, as the `do` elaborator builds it. -/
abbrev St := MProd UInt32 (MProd UInt32 (MProd UInt32 (MProd UInt32
  (MProd UInt32 (MProd UInt32 (MProd UInt32 UInt32))))))

/-- The round loop's body (`for t in [0:64]`). -/
def rstep (w : Array UInt32) (b : St) (t : Nat) : St :=
  ⟨b.2.2.2.2.2.2.2 +
      (Model.Sha256.rotr b.2.2.2.2.1 6 ^^^ Model.Sha256.rotr b.2.2.2.2.1 11 ^^^
        Model.Sha256.rotr b.2.2.2.2.1 25) +
      (b.2.2.2.2.1 &&& b.2.2.2.2.2.1 ^^^ ~~~b.2.2.2.2.1 &&& b.2.2.2.2.2.2.1) +
      Model.Sha256.roundConstants[t]! + w[t]! +
      ((Model.Sha256.rotr b.1 2 ^^^ Model.Sha256.rotr b.1 13 ^^^ Model.Sha256.rotr b.1 22) +
        (b.1 &&& b.2.1 ^^^ b.1 &&& b.2.2.1 ^^^ b.2.1 &&& b.2.2.1)),
    b.1, b.2.1, b.2.2.1,
    b.2.2.2.1 +
      (b.2.2.2.2.2.2.2 +
        (Model.Sha256.rotr b.2.2.2.2.1 6 ^^^ Model.Sha256.rotr b.2.2.2.2.1 11 ^^^
          Model.Sha256.rotr b.2.2.2.2.1 25) +
        (b.2.2.2.2.1 &&& b.2.2.2.2.2.1 ^^^ ~~~b.2.2.2.2.1 &&& b.2.2.2.2.2.2.1) +
        Model.Sha256.roundConstants[t]! + w[t]!),
    b.2.2.2.2.1, b.2.2.2.2.2.1, b.2.2.2.2.2.2.1⟩

/-- tacenta-model's message schedule, as two folds. -/
def sched (block : Array UInt8) : Array UInt32 :=
  (List.range' 16 48).foldl step2
    ((List.range' 0 16).foldl (step1 block) (Array.replicate 64 0))

/-- tacenta-model's `compress`, with its loops as folds. -/
def compressF (h : Array UInt32) (block : Array UInt8) : Array UInt32 :=
  let s := (List.range' 0 64).foldl (rstep (sched block))
    ⟨h[0]!, h[1]!, h[2]!, h[3]!, h[4]!, h[5]!, h[6]!, h[7]!⟩
  #[h[0]! + s.1, h[1]! + s.2.1, h[2]! + s.2.2.1, h[3]! + s.2.2.2.1,
    h[4]! + s.2.2.2.2.1, h[5]! + s.2.2.2.2.2.1, h[6]! + s.2.2.2.2.2.2.1,
    h[7]! + s.2.2.2.2.2.2.2]

theorem compress_normal (h : Array UInt32) (block : Array UInt8) :
    Model.Sha256.compress h block = compressF h block := by
  simp only [Model.Sha256.compress, Std.Legacy.Range.forIn_eq_forIn_range',
    Std.Legacy.Range.size, Id.run, List.forIn_pure_yield_eq_foldl,
    bind_pure_comp, map_pure, Nat.reduceSub, Nat.reduceAdd, Nat.reduceDiv,
    compressF, sched]
  generalize List.range' 0 16 = l1
  generalize List.range' 16 48 = l2
  generalize List.range' 0 64 = l3
  rfl


/-! ## The message schedule -/

theorem getD_append_left {α} (l l' : List α) (i : Nat) (d : α) (h : i < l.length) :
    (l ++ l').getD i d = l.getD i d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_append_left h]

theorem set_after_prefix {α} (S : List α) (n : Nat) (z v : α) :
    (S ++ List.replicate (n + 1) z).set S.length v = S ++ v :: List.replicate n z := by
  rw [List.set_append_right _ _ (Nat.le_refl _), Nat.sub_self, List.replicate_succ,
    List.set_cons_zero]

/-- Word `j` of a 64-byte block, as this repository's `parseBlock` reads it. -/
def blockWord (B : List UInt8) (j : Nat) : UInt32 :=
  word (B.getD (4 * j) 0) (B.getD (4 * j + 1) 0) (B.getD (4 * j + 2) 0)
    (B.getD (4 * j + 3) 0)

theorem parseBlock_eq (B : List UInt8) :
    parseBlock B = (List.range' 0 16).map (blockWord B) := by
  rw [← List.range_eq_range']; rfl

theorem step1_eq (block : Array UInt8) (w : Array UInt32) (i : Nat) :
    step1 block w i = w.set! i (blockWord block.toList i) := by
  simp only [step1, blockWord, arr_getElem!_eq_getD, Nat.mul_comm i 4]
  rfl

theorem sched1_toList (block : Array UInt8) (k : Nat) (hk : k ≤ 64) :
    ((List.range' 0 k).foldl (step1 block) (Array.replicate 64 0)).toList =
      (List.range' 0 k).map (blockWord block.toList) ++ List.replicate (64 - k) 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.range'_1_concat, List.foldl_append, List.foldl_cons, List.foldl_nil,
      step1_eq, Array.set!_eq_setIfInBounds, Array.toList_setIfInBounds,
      ih (by omega), Nat.zero_add]
    have h64 : 64 - k = (64 - (k + 1)) + 1 := by omega
    have hlen : ((List.range' 0 k).map (blockWord block.toList)).length = k := by simp
    conv => lhs; rw [h64]; arg 2; rw [← hlen]
    rw [set_after_prefix, List.map_append, List.append_assoc]
    rfl

theorem scheduleAux_succ (k : Nat) (W : List UInt32) :
    scheduleAux (k + 1) W = scheduleStep (scheduleAux k W) := by
  induction k generalizing W with
  | zero => rfl
  | succ k ih => exact ih (scheduleStep W)

theorem scheduleStep_length (W : List UInt32) :
    (scheduleStep W).length = W.length + 1 := by
  simp [scheduleStep]

theorem scheduleAux_length (k : Nat) (W : List UInt32) :
    (scheduleAux k W).length = W.length + k := by
  induction k generalizing W with
  | zero => rfl
  | succ k ih =>
    show (scheduleAux k (scheduleStep W)).length = _
    rw [ih, scheduleStep_length]; omega

theorem step2_eq (w : Array UInt32) (S : List UInt32) (n : Nat)
    (hw : w.toList = S ++ List.replicate (n + 1) 0) (hS : 16 ≤ S.length) :
    (step2 w S.length).toList = scheduleStep S ++ List.replicate n 0 := by
  have g : ∀ i, 1 ≤ i → i ≤ 16 → w[S.length - i]! = S.getD (S.length - i) 0 := by
    intro i h1 h2
    rw [arr_getElem!_eq_getD, hw, getD_append_left _ _ _ _ (by omega)]
    rfl
  simp only [step2, Array.set!_eq_setIfInBounds, Array.toList_setIfInBounds,
    g 16 (by omega) (by omega), g 15 (by omega) (by omega), g 7 (by omega) (by omega),
    g 2 (by omega) (by omega), hw, set_after_prefix, scheduleStep, List.append_assoc,
    List.singleton_append]
  congr 2
  exact u32_add4_rev _ _ _ _

theorem sched2_toList (w : Array UInt32) (M : List UInt32) (hM : M.length = 16)
    (hw : w.toList = M ++ List.replicate 48 0) (k : Nat) (hk : k ≤ 48) :
    ((List.range' 16 k).foldl step2 w).toList = scheduleAux k M ++ List.replicate (48 - k) 0 := by
  induction k with
  | zero => exact hw
  | succ k ih =>
    rw [List.range'_1_concat, List.foldl_append, List.foldl_cons, List.foldl_nil,
      scheduleAux_succ]
    have hlen : (scheduleAux k M).length = 16 + k := by rw [scheduleAux_length, hM]
    have h48 : 48 - k = (48 - (k + 1)) + 1 := by omega
    rw [← hlen]
    exact step2_eq _ _ _ (by rw [ih (by omega), h48]) (by omega)

theorem sched_toList (block : Array UInt8) :
    (sched block).toList = schedule (parseBlock block.toList) := by
  have h1 := sched1_toList block 16 (by omega)
  rw [← parseBlock_eq] at h1
  have h2 := sched2_toList _ _ (by simp [parseBlock]) h1 48 (by omega)
  simpa [sched, schedule] using h2


/-! ## The 64 rounds and one block -/

theorem roundConstants_toList : Model.Sha256.roundConstants.toList = KdfStandardModel.Sha256.K := by
  decide +kernel

theorem initialHash_toList : Model.Sha256.initialHash.toList = KdfStandardModel.Sha256.H0 := by
  decide +kernel

/-- The round loop's `MProd` state read as this repository's `Vars`. -/
def toVars (b : St) : Vars :=
  ⟨b.1, b.2.1, b.2.2.1, b.2.2.2.1, b.2.2.2.2.1, b.2.2.2.2.2.1, b.2.2.2.2.2.2.1,
    b.2.2.2.2.2.2.2⟩

theorem toVars_rstep (w : Array UInt32) (b : St) (t : Nat) :
    toVars (rstep w b t) = round w.toList (toVars b) t := by
  simp only [rstep, arr_getElem!_eq_getD, roundConstants_toList]
  rfl

theorem toVars_rounds (w : Array UInt32) (b : St) (l : List Nat) :
    toVars (l.foldl (rstep w) b) = l.foldl (round w.toList) (toVars b) :=
  (List.foldl_hom toVars (fun x y => (toVars_rstep w x y).symm)).symm

theorem default_u32 : (default : UInt32) = 0 := rfl

theorem compress_toList (h : Array UInt32) (block : Array UInt8) :
    (Model.Sha256.compress h block).toList =
      KdfStandardModel.Sha256.compress h.toList (parseBlock block.toList) := by
  have hinit : toVars ⟨h[0]!, h[1]!, h[2]!, h[3]!, h[4]!, h[5]!, h[6]!, h[7]!⟩ =
      initVars h.toList := by
    simp only [toVars, initVars, arr_getElem!_eq_getD]; rfl
  have key : toVars (List.foldl (rstep (sched block))
      ⟨h[0]!, h[1]!, h[2]!, h[3]!, h[4]!, h[5]!, h[6]!, h[7]!⟩ (List.range' 0 64)) =
      List.foldl (round (schedule (parseBlock block.toList))) (initVars h.toList)
        (List.range 64) := by
    rw [toVars_rounds, sched_toList, hinit, List.range_eq_range']
  rw [compress_normal]
  simp only [KdfStandardModel.Sha256.compress, ← key]
  simp only [compressF, toVars, List.toList_toArray]
  simp only [List.cons.injEq, and_true, arr_getElem!_eq_getD, default_u32]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> exact UInt32.add_comm _ _

/-! ## Padding, the block split, and the whole hash -/

theorem pad_eq (M : List UInt8) : KdfStandardModel.Sha256.pad M = Model.Sha256.pad M := by
  simp only [KdfStandardModel.Sha256.pad, Model.Sha256.pad, KdfStandardModel.Sha256.lengthBlock,
    KdfStandardModel.Sha256.be64, KdfStandardModel.Sha256.padZeroBits]
  have hz : ((448 + 512 - (8 * M.length + 1) % 512) % 512 - 7) / 8 =
      (56 + 64 - (M.length + 1) % 64) % 64 := by omega
  rw [hz]
  congr 1
  simp [List.range_succ]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · apply UInt8.toNat_inj.mp
    simp [UInt64.toNat_shiftRight, UInt64.toNat_mul, Nat.shiftRight_eq_div_pow]
    omega

theorem chunks_eq_map (size n : Nat) (xs : List UInt8) :
    KdfStandardModel.chunks size n xs =
      (List.range n).map (fun k => (xs.drop (k * size)).take size) := by
  induction n generalizing xs with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ_eq_map, List.map_cons, List.map_map]
    simp only [KdfStandardModel.chunks, ih, Nat.zero_mul, List.drop_zero, List.cons.injEq,
      true_and]
    apply List.map_congr_left
    intro k _
    simp only [Function.comp, List.drop_drop, Nat.succ_mul]
    congr 2
    omega

theorem wordBytes_eq : KdfStandardModel.Sha256.wordBytes = Model.Sha256.wordBytes := rfl

theorem hash_eq (M : List UInt8) : KdfStandardModel.Sha256.hash M = Model.Sha256.hash M := by
  simp only [KdfStandardModel.Sha256.hash, Model.Sha256.hash, KdfStandardModel.Sha256.parse, pad_eq,
    wordBytes_eq, List.size_toArray]
  congr 1
  generalize Model.Sha256.pad M = P
  rw [chunks_eq_map, List.map_map, List.foldl_map, ← initialHash_toList]
  refine List.foldl_hom Array.toList (fun H k => ?_)
  rw [compress_toList, Array.toList_extract, List.toList_toArray, List.extract_eq_take_drop,
    Nat.add_sub_cancel_left]
  rfl

end KdfBridge.Sha256

/-- **SHA-256 bridge.** This repository's clean-room SHA-256 equals
tacenta-model's, for every byte string. -/
theorem KdfBridge.sha256_eq (m : List UInt8) : KdfStandardModel.sha256 m = Model.Sha256.hash m :=
  KdfBridge.Sha256.hash_eq m
