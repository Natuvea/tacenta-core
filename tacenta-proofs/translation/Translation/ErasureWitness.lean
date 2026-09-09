import Translation.BraidT3
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.LinearAlgebra.Lagrange

/-!
# A model of the Braid's erasure boundary

`BraidT3.lean` assumes, as `ErasureAgrees`, that the opaque erasure encoder
and decoder simulate `Model.Braid`'s: an encoder emits chunks indexed from
zero, and a decoder fed codewords of one message of its own size reconstructs
that message once it holds enough of them. An assumption of that kind can be
refutable without any downstream proof noticing, so this file exhibits a
model of it: an implementation of the five opaque operations, over the
concrete 32-byte `tacenta_erasure.Chunk`, that satisfies the assumption.

The implementation is a Reed-Solomon code over `GF(2^256)`, one symbol per
chunk: a message is padded to whole 32-byte blocks, each block is a field
element (a bijection, since both sides have `2^256` inhabitants), the blocks
are the coefficients of a polynomial, and codeword `i` is that polynomial's
value at the `i`-th field element. Any `k` distinct codewords determine a
polynomial of degree below `k` (Lagrange), so a decoder that holds enough of
them reconstructs the blocks and, from them, the message. That is the
maximum-distance-separable property the assumption needs, and it is what the
real crate is too (sixteen Reed-Solomon lanes over `GF(2^16)`).

Everything here is noncomputable -- the field and the bijection come from
Mathlib's existence theorems -- which is fine for a witness: the point is
that the assumption has a model, not that this code runs.

Nothing here says the real crate *is* this code. `ErasureAgrees` remains an
assumption about the real crate; this file says only that it is a
consistent one.
-/

open Aeneas Aeneas.Std Result Polynomial

namespace Tacenta.ErasureWitness

open Tacenta.BraidT3 tacenta_braid

/-! ## The shape: `BraidT3.lean`'s erasure definitions over any implementation -/

/-- The five opaque operations, as data. -/
structure Api (Enc Dec : Type) where
  new : Slice Std.U8 → Result Enc
  next : Enc → Result (Option tacenta_erasure.Chunk × Enc)
  dnew : Usize → Result Dec
  add : Dec → tacenta_erasure.Chunk → Result (Bool × Dec)
  msg : Dec → Result (Option (alloc.vec.Vec Std.U8))
  cloneEnc : Enc → Result Enc
  cloneDec : Dec → Result Dec

section Shape
variable {Enc Dec : Type} (A : Api Enc Dec)

def EncoderSim : Nat → Enc → Model.Braid.Encoder → Prop
  | 0, _, _ => True
  | n + 1, real, model =>
    ∃ chunk real', A.next real = ok (some chunk, real') ∧
      chunk.index.val = model.nextChunk.1.index ∧ EncoderSim n real' model.nextChunk.2

def NthChunk : Nat → Enc → tacenta_erasure.Chunk → Prop
  | 0, enc, chunk => ∃ enc', A.next enc = ok (some chunk, enc')
  | i + 1, enc, chunk => ∃ c enc', A.next enc = ok (some c, enc') ∧ NthChunk i enc' chunk

def Stepped : Nat → Enc → Enc → Prop
  | 0, enc0, real => real = enc0
  | k + 1, enc0, real => ∃ c enc', A.next enc0 = ok (some c, enc') ∧ Stepped k enc' real

def CodewordOf (m : Bytes) (chunk : tacenta_erasure.Chunk) : Prop :=
  ∃ (s : Slice Std.U8) (enc0 : Enc), sliceOf s = m ∧ A.new s = ok enc0 ∧
    NthChunk A chunk.index.val enc0 chunk

def DecoderSim (m : Bytes) : Nat → Dec → Model.Braid.Decoder → Prop
  | 0, _, _ => True
  | n + 1, real, model =>
    (∀ (chunk : tacenta_erasure.Chunk) (advanced : Bool) (real' : Dec),
      CodewordOf A m chunk → A.add real chunk = ok (advanced, real') →
      DecoderSim m n real' (model.addChunk ⟨m, chunk.index.val⟩)) ∧
    (∀ msg, A.msg real = ok msg → msg.map vecOf = model.message)

def EncoderRefines (real : Enc) (model : Model.Braid.Encoder) : Prop :=
  (∃ (s : Slice Std.U8) (enc0 : Enc), sliceOf s = model.source ∧
      A.new s = ok enc0 ∧ Stepped A model.next enc0 real) ∧
  ∀ n, model.next + n ≤ 65536 → EncoderSim A n real model

def DecoderRefines (real : Dec) (model : Model.Braid.Decoder) : Prop :=
  ∀ m : Bytes, m.length = model.size → (∀ c ∈ model.chunks, c.source = m) →
    ∀ n, DecoderSim A m n real model

def ErasureAgrees : Prop :=
  (∀ (s : Slice Std.U8), ∃ real, A.new s = ok real ∧
    EncoderRefines A real (Model.Braid.encode (sliceOf s))) ∧
  (∀ (n : Usize), ∃ real, A.dnew n = ok real ∧
    DecoderRefines A real (Model.Braid.Decoder.new n.val))

def ErasureCloneAgrees : Prop :=
  (∀ (real real' : Enc), A.cloneEnc real = ok real' → real' = real) ∧
  (∀ (real real' : Dec), A.cloneDec real = ok real' → real' = real)

/-- `BraidT1.lean`'s seven erasure totality assumptions. -/
def ErasureTotals : Prop :=
  (∀ (s : Slice Std.U8), ∃ r, A.new s = ok r) ∧
  (∀ (e : Enc), ∃ r, A.next e = ok r) ∧
  (∀ (e : Enc), ∃ r, A.cloneEnc e = ok r) ∧
  (∀ (n : Usize), ∃ r, A.dnew n = ok r) ∧
  (∀ (d : Dec) (c : tacenta_erasure.Chunk), ∃ r, A.add d c = ok r) ∧
  (∀ (d : Dec), ∃ r, A.msg d = ok r) ∧
  (∀ (d : Dec), ∃ r, A.cloneDec d = ok r)

end Shape

/-- The real operations, as an `Api`. -/
noncomputable def realApi : Api tacenta_erasure.Encoder tacenta_erasure.Decoder where
  new := tacenta_erasure.Encoder.new
  next := tacenta_erasure.Encoder.next_chunk
  dnew := tacenta_erasure.Decoder.new
  add := tacenta_erasure.Decoder.add_chunk
  msg := tacenta_erasure.Decoder.message
  cloneEnc := tacenta_erasure.Encoder.Insts.CoreCloneClone.clone
  cloneDec := tacenta_erasure.Decoder.Insts.CoreCloneClone.clone

/-! ### The concrete definitions are the shape at the real operations -/

theorem encoderSim_iff (n : Nat) (real : tacenta_erasure.Encoder) (model : Model.Braid.Encoder) :
    Tacenta.BraidT3.EncoderSim n real model ↔ EncoderSim realApi n real model := by
  induction n generalizing real model with
  | zero => exact Iff.rfl
  | succ n ih =>
    simp only [Tacenta.BraidT3.EncoderSim, EncoderSim, realApi]
    constructor
    · rintro ⟨c, r, h, hi, hs⟩; exact ⟨c, r, h, hi, (ih r _).mp hs⟩
    · rintro ⟨c, r, h, hi, hs⟩; exact ⟨c, r, h, hi, (ih r _).mpr hs⟩

theorem nthChunk_iff (i : Nat) (enc : tacenta_erasure.Encoder) (chunk : tacenta_erasure.Chunk) :
    Tacenta.BraidT3.NthChunk i enc chunk ↔ NthChunk realApi i enc chunk := by
  induction i generalizing enc with
  | zero => exact Iff.rfl
  | succ i ih =>
    simp only [Tacenta.BraidT3.NthChunk, NthChunk, realApi]
    constructor
    · rintro ⟨c, e, h, hs⟩; exact ⟨c, e, h, (ih e).mp hs⟩
    · rintro ⟨c, e, h, hs⟩; exact ⟨c, e, h, (ih e).mpr hs⟩

theorem stepped_iff (k : Nat) (enc0 real : tacenta_erasure.Encoder) :
    Tacenta.BraidT3.Stepped k enc0 real ↔ Stepped realApi k enc0 real := by
  induction k generalizing enc0 with
  | zero => exact Iff.rfl
  | succ k ih =>
    simp only [Tacenta.BraidT3.Stepped, Stepped, realApi]
    constructor
    · rintro ⟨c, e, h, hs⟩; exact ⟨c, e, h, (ih e).mp hs⟩
    · rintro ⟨c, e, h, hs⟩; exact ⟨c, e, h, (ih e).mpr hs⟩

theorem codewordOf_iff (m : Bytes) (chunk : tacenta_erasure.Chunk) :
    Tacenta.BraidT3.CodewordOf m chunk ↔ CodewordOf realApi m chunk := by
  simp only [Tacenta.BraidT3.CodewordOf, CodewordOf, realApi, nthChunk_iff]

theorem decoderSim_iff (m : Bytes) (n : Nat) (real : tacenta_erasure.Decoder)
    (model : Model.Braid.Decoder) :
    Tacenta.BraidT3.DecoderSim m n real model ↔ DecoderSim realApi m n real model := by
  induction n generalizing real model with
  | zero => exact Iff.rfl
  | succ n ih =>
    simp only [Tacenta.BraidT3.DecoderSim, DecoderSim, realApi, codewordOf_iff]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨fun c a r hc ha => (ih r _).mp (h1 c a r hc ha), h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨fun c a r hc ha => (ih r _).mpr (h1 c a r hc ha), h2⟩

theorem encoderRefines_iff (real : tacenta_erasure.Encoder) (model : Model.Braid.Encoder) :
    Tacenta.BraidT3.EncoderRefines real model ↔ EncoderRefines realApi real model := by
  simp only [Tacenta.BraidT3.EncoderRefines, EncoderRefines, realApi, stepped_iff, encoderSim_iff]

theorem decoderRefines_iff (real : tacenta_erasure.Decoder) (model : Model.Braid.Decoder) :
    Tacenta.BraidT3.DecoderRefines real model ↔ DecoderRefines realApi real model := by
  simp only [Tacenta.BraidT3.DecoderRefines, DecoderRefines, decoderSim_iff]

/-- `BraidT3.lean`'s `ErasureAgrees` is exactly the shape at the real
operations, so a model of the shape is a model of the hypothesis. -/
theorem erasureAgrees_iff : Tacenta.BraidT3.ErasureAgrees ↔ ErasureAgrees realApi := by
  simp only [Tacenta.BraidT3.ErasureAgrees, ErasureAgrees, realApi, encoderRefines_iff,
    decoderRefines_iff]

theorem erasureCloneAgrees_iff :
    Tacenta.BraidT3.ErasureCloneAgrees ↔ ErasureCloneAgrees realApi := Iff.rfl

theorem erasureTotals_iff :
    (Tacenta.BraidT1.EncoderNewTotal ∧ Tacenta.BraidT1.EncoderNextChunkTotal ∧
      Tacenta.BraidT1.EncoderCloneTotal ∧ Tacenta.BraidT1.DecoderNewTotal ∧
      Tacenta.BraidT1.DecoderAddChunkTotal ∧ Tacenta.BraidT1.DecoderMessageTotal ∧
      Tacenta.BraidT1.DecoderCloneTotal) ↔ ErasureTotals realApi := Iff.rfl

/-! ## Symbols: 32-byte chunk data as elements of `GF(2^256)` -/

instance : Fintype (BitVec 8) :=
  Fintype.ofEquiv (Fin (2 ^ 8)) ⟨BitVec.ofFin, BitVec.toFin, fun _ => rfl, fun _ => rfl⟩

theorem card_bitvec8 : Fintype.card (BitVec 8) = 256 := by
  rw [Fintype.card_congr ⟨BitVec.toFin, BitVec.ofFin, fun _ => rfl, fun _ => rfl⟩]; simp

instance : Fintype Std.U8 :=
  Fintype.ofEquiv (BitVec 8) ⟨fun b => ⟨b⟩, fun u => u.bv, fun _ => rfl, fun _ => rfl⟩

theorem card_u8 : Fintype.card Std.U8 = 256 := by
  rw [Fintype.card_congr ⟨fun (u : Std.U8) => u.bv, fun b => ⟨b⟩, fun _ => rfl, fun _ => rfl⟩]
  exact card_bitvec8

/-- A chunk's data. -/
abbrev Data32 := Array Std.U8 32#usize

def data32Equiv : Data32 ≃ List.Vector Std.U8 32 where
  toFun a := ⟨a.val, by simp⟩
  invFun v := ⟨v.val, by simp⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : Fintype Data32 := Fintype.ofEquiv _ data32Equiv.symm

theorem card_data32 : Fintype.card Data32 = 2 ^ 256 := by
  rw [Fintype.card_congr data32Equiv, card_vector, card_u8]; norm_num

/-- The symbol field. -/
abbrev F := GaloisField 2 256

noncomputable instance : Fintype F := Fintype.ofFinite F

theorem card_F : Fintype.card F = 2 ^ 256 := by
  rw [← Nat.card_eq_fintype_card]; exact GaloisField.card 2 256 (by norm_num)

/-- Chunk data and field elements are in bijection. -/
noncomputable def sym : Data32 ≃ F := Fintype.equivOfCardEq (by rw [card_data32, card_F])

/-- The evaluation points: distinct field elements for every index below `2^256`. -/
noncomputable def pt (i : ℕ) : F :=
  if h : i < 2 ^ 256 then (Fintype.equivFin F).symm ⟨i, by rw [card_F]; exact h⟩ else 0

theorem pt_injOn (s : Finset ℕ) (hs : ∀ i ∈ s, i < 65536) : Set.InjOn pt s := by
  intro i hi j hj hij
  have hi' : i < 2 ^ 256 := lt_of_lt_of_le (hs i hi) (by norm_num)
  have hj' : j < 2 ^ 256 := lt_of_lt_of_le (hs j hj) (by norm_num)
  simp only [pt, dif_pos hi', dif_pos hj'] at hij
  have := (Fintype.equivFin F).symm.injective hij
  simpa using congrArg Fin.val this

/-! ## Polynomials: coefficients survive interpolation from any `k` values -/

noncomputable def poly (k : ℕ) (c : ℕ → F) : F[X] := ∑ j ∈ Finset.range k, C (c j) * X ^ j

theorem poly_degree_lt (k : ℕ) (c : ℕ → F) (_hk : 0 < k) : (poly k c).degree < k := by
  unfold poly
  apply lt_of_le_of_lt (Polynomial.degree_sum_le _ _)
  rw [Finset.sup_lt_iff (by exact WithBot.bot_lt_coe k)]
  intro j hj
  apply lt_of_le_of_lt (Polynomial.degree_C_mul_X_pow_le _ _)
  exact WithBot.coe_lt_coe.mpr (Finset.mem_range.mp hj)

theorem poly_coeff (k : ℕ) (c : ℕ → F) (j : ℕ) (hj : j < k) : (poly k c).coeff j = c j := by
  unfold poly
  rw [Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single j]
  · simp
  · intro b _ hb; simp [Ne.symm hb]
  · intro h; exact absurd (Finset.mem_range.mpr hj) h

theorem recover (k : ℕ) (hk : 0 < k) (c : ℕ → F) (s : Finset ℕ)
    (hx : Set.InjOn pt s) (hs : k ≤ s.card) (r : ℕ → F)
    (hr : ∀ i ∈ s, r i = (poly k c).eval (pt i)) (j : ℕ) (hj : j < k) :
    (Lagrange.interpolate s pt r).coeff j = c j := by
  have hdeg : (poly k c).degree < (s.card : WithBot ℕ) :=
    lt_of_lt_of_le (poly_degree_lt k c hk) (WithBot.coe_le_coe.mpr hs)
  have := Lagrange.eq_interpolate_of_eval_eq (r := r) hx hdeg (fun i hi => (hr i hi).symm)
  rw [← this]
  exact poly_coeff k c j hj

/-! ## Blocks: a byte string as whole 32-byte blocks and back -/

/-- Blocks needed for `n` bytes. -/
def blocksOf (n : ℕ) : ℕ := (n + 31) / 32

theorem le_blocks (n : ℕ) : n ≤ 32 * blocksOf n := by unfold blocksOf; omega

theorem blocks_le (n c : ℕ) (h : n ≤ c * 32) : blocksOf n ≤ c := by unfold blocksOf; omega

/-- `l` padded with zeros to whole blocks. -/
def padded (l : List Std.U8) : List Std.U8 :=
  l ++ List.replicate (32 * blocksOf l.length - l.length) 0#u8

theorem padded_length (l : List Std.U8) : (padded l).length = 32 * blocksOf l.length := by
  simp [padded]; have := le_blocks l.length; omega

theorem padded_take (l : List Std.U8) : (padded l).take l.length = l := by
  simp [padded]

/-- Any 32-byte window of a list, zero-filled if it runs off the end. -/
def window (l : List Std.U8) (j : ℕ) : Data32 :=
  ⟨((l.drop (32 * j)).take 32 ++ List.replicate 32 0#u8).take 32, by simp⟩

theorem window_val (l : List Std.U8) (j : ℕ) (h : 32 * j + 32 ≤ l.length) :
    (window l j).val = (l.drop (32 * j)).take 32 := by
  simp only [window]
  have : ((l.drop (32 * j)).take 32).length = 32 := by simp; omega
  rw [List.take_append_of_le_length (by omega)]
  simp [this]

/-- The `j`-th block of a message. -/
def block (l : List Std.U8) (j : ℕ) : Data32 := window (padded l) j

theorem block_val (l : List Std.U8) (j : ℕ) (hj : j < blocksOf l.length) :
    (block l j).val = ((padded l).drop (32 * j)).take 32 := by
  apply window_val
  rw [padded_length]; omega

/-- Consecutive 32-byte windows reassemble a list of whole blocks. -/
theorem unblock (k : ℕ) (L : List Std.U8) (hL : L.length = 32 * k) :
    (List.range k).flatMap (fun j => (L.drop (32 * j)).take 32) = L := by
  induction k generalizing L with
  | zero =>
    simp only [List.range_zero, List.flatMap_nil]
    exact (List.eq_nil_of_length_eq_zero (by omega)).symm
  | succ k ih =>
    rw [List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]
    have hrest : (List.range k).flatMap (fun a => (L.drop (32 * a.succ)).take 32)
        = (List.range k).flatMap (fun j => ((L.drop 32).drop (32 * j)).take 32) := by
      apply List.flatMap_congr
      intro j _
      simp only [List.drop_drop]
      congr 2; omega
    rw [hrest, ih (L.drop 32) (by simp; omega)]
    simp

theorem unblock_message (l : List Std.U8) :
    ((List.range (blocksOf l.length)).flatMap (fun j => (block l j).val)).take l.length = l := by
  have : (List.range (blocksOf l.length)).flatMap (fun j => (block l j).val) = padded l := by
    rw [← unblock (blocksOf l.length) (padded l) (padded_length l)]
    apply List.flatMap_congr
    intro j hj
    exact block_val l j (List.mem_range.mp hj)
  rw [this, padded_take]

/-! ## The code -/

/-- The polynomial of a message: its blocks are the coefficients. -/
noncomputable def polyOf (l : List Std.U8) : F[X] :=
  poly (blocksOf l.length) (fun j => sym (block l j))

/-- Codeword `i`: the polynomial's value at the `i`-th point, as chunk data. -/
noncomputable def codeword (l : List Std.U8) (i : ℕ) : Data32 :=
  sym.symm ((polyOf l).eval (pt i))

/-- The `u16` index of a codeword. -/
def idx (i : ℕ) : Std.U16 := ⟨BitVec.ofNat 16 i⟩

theorem idx_val (i : ℕ) (h : i < 65536) : (idx i).val = i := by
  simp only [idx, UScalar.val]
  exact Nat.mod_eq_of_lt (by simpa using h)

noncomputable def mkChunk (l : List Std.U8) (i : ℕ) : tacenta_erasure.Chunk :=
  ⟨idx i, codeword l i⟩

/-- An encoder: the message and how many codewords it has emitted. -/
structure Enc where
  src : List Std.U8
  next : ℕ

/-- A decoder: the size it was built for and the codewords it holds, newest
first, one per index. -/
structure Dec where
  size : ℕ
  chunks : List (ℕ × Data32)

noncomputable def encNew (s : Slice Std.U8) : Result Enc := ok ⟨s.val, 0⟩

noncomputable def encNext (e : Enc) : Result (Option tacenta_erasure.Chunk × Enc) :=
  if e.next < 65536 then ok (some (mkChunk e.src e.next), ⟨e.src, e.next + 1⟩)
  else ok (none, e)

def decNew (n : Usize) : Result Dec := ok ⟨n.val, []⟩

def decAdd (d : Dec) (c : tacenta_erasure.Chunk) : Result (Bool × Dec) :=
  if d.chunks.any (fun p => p.1 == c.index.val) then ok (false, d)
  else ok (true, ⟨d.size, (c.index.val, c.data) :: d.chunks⟩)

/-- Interpolate the held codewords and read the blocks off the result. -/
noncomputable def decode (d : Dec) : List Std.U8 :=
  let s : Finset ℕ := (d.chunks.map Prod.fst).toFinset
  let r : ℕ → F := fun i =>
    match d.chunks.find? (fun p => p.1 == i) with
    | some p => sym p.2
    | none => 0
  let q := Lagrange.interpolate s pt r
  ((List.range (blocksOf d.size)).flatMap (fun j => (sym.symm (q.coeff j)).val)).take d.size

noncomputable def decMsg (d : Dec) : Result (Option (alloc.vec.Vec Std.U8)) :=
  if d.chunks.length * 32 ≥ d.size then
    if h : d.size ≤ Usize.max then
      ok (some ⟨decode d, by
        simp only [decode, List.length_take]
        exact le_trans (Nat.min_le_left _ _) h⟩)
    else ok none
  else ok none

noncomputable def api : Api Enc Dec :=
  ⟨encNew, encNext, decNew, decAdd, decMsg, fun e => ok e, fun d => ok d⟩

/-! ## The witness satisfies the shape -/

/-- Stepping `k` times from a fresh encoder lands at position `k`. -/
theorem stepped_iff_pos (k : ℕ) (l : List Std.U8) (e : Enc) (hk : k ≤ 65536) :
    Stepped api k ⟨l, 0⟩ e ↔ e = ⟨l, k⟩ := by
  suffices h : ∀ k0, k0 + k ≤ 65536 → (Stepped api k ⟨l, k0⟩ e ↔ e = ⟨l, k0 + k⟩) by
    simpa using h 0 (by omega)
  clear hk
  induction k with
  | zero => intro k0 _; simp [Stepped]
  | succ k ih =>
    intro k0 hk0
    simp only [Stepped, api, encNext]
    rw [if_pos (by omega)]
    constructor
    · rintro ⟨c, e', he', hs⟩
      simp only [ok.injEq, Prod.mk.injEq] at he'
      obtain ⟨-, rfl⟩ := he'
      have := (ih (k0 + 1) (by omega)).mp hs
      rw [this]; congr 1; omega
    · intro he
      refine ⟨mkChunk l k0, ⟨l, k0 + 1⟩, rfl, (ih (k0 + 1) (by omega)).mpr ?_⟩
      rw [he]; congr 1; omega

/-- The `i`-th chunk of a fresh encoder is codeword `i`, and exists only while
`i` fits a `u16`. -/
theorem nthChunk_iff_codeword (i : ℕ) (l : List Std.U8) (c : tacenta_erasure.Chunk) :
    NthChunk api i ⟨l, 0⟩ c ↔ i < 65536 ∧ c = mkChunk l i := by
  suffices h : ∀ k0 i, (NthChunk api i ⟨l, k0⟩ c ↔ k0 + i < 65536 ∧ c = mkChunk l (k0 + i)) by
    simpa using h 0 i
  intro k0 i
  induction i generalizing k0 with
  | zero =>
    simp only [NthChunk, api, encNext, Nat.add_zero]
    constructor
    · rintro ⟨e', he'⟩
      split at he'
      · rename_i hlt
        simp only [ok.injEq, Prod.mk.injEq, Option.some.injEq] at he'
        exact ⟨hlt, he'.1.symm⟩
      · simp at he'
    · rintro ⟨hlt, rfl⟩
      exact ⟨⟨l, k0 + 1⟩, by rw [if_pos hlt]⟩
  | succ i ih =>
    simp only [NthChunk, api, encNext]
    constructor
    · rintro ⟨c', e', he', hs⟩
      split at he'
      · simp only [ok.injEq, Prod.mk.injEq, Option.some.injEq] at he'
        obtain ⟨-, rfl⟩ := he'
        have := (ih (k0 + 1)).mp hs
        refine ⟨by omega, ?_⟩
        rw [this.2]; congr 1; omega
      · simp at he'
    · rintro ⟨hlt, rfl⟩
      refine ⟨mkChunk l k0, ⟨l, k0 + 1⟩, by rw [if_pos (by omega)], ?_⟩
      refine (ih (k0 + 1)).mpr ⟨by omega, ?_⟩
      congr 1; omega

/-- `sliceOf` determines the slice's bytes. -/
theorem sliceOf_inj {s t : Slice Std.U8} (h : sliceOf s = sliceOf t) : s.val = t.val := by
  simp only [sliceOf] at h
  exact List.map_injective_iff.mpr (fun _ _ hxy => u8_injective hxy) h

/-- A codeword of `m`, in the witness, is `mkChunk` of the bytes reading `m`. -/
theorem codewordOf_api (m : Bytes) (c : tacenta_erasure.Chunk) (h : CodewordOf api m c) :
    ∃ l : List Std.U8, l.map u8 = m ∧ c.index.val < 65536 ∧ c = mkChunk l c.index.val := by
  simp only [CodewordOf, api, encNew, ok.injEq] at h
  obtain ⟨s, e0, hs, he0, hn⟩ := h
  subst he0
  have := (nthChunk_iff_codeword _ _ _).mp hn
  exact ⟨s.val, by simpa [sliceOf] using hs, this.1, this.2⟩

/-! ## The decoder simulates the model decoder -/

/-- A `UInt8` as a translated byte, the inverse of `u8`. -/
def ofU8 (b : UInt8) : Std.U8 := ⟨BitVec.ofNat 8 b.toNat⟩

theorem u8_ofU8 (b : UInt8) : u8 (ofU8 b) = b := by
  show UInt8.ofNat ((BitVec.ofNat 8 b.toNat).toNat) = b
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := b.toNat_lt; omega)]
  exact UInt8.ofNat_toNat

theorem map_u8_injective {l l' : List Std.U8} (h : l.map u8 = l'.map u8) : l = l' :=
  List.map_injective_iff.mpr (fun _ _ hxy => u8_injective hxy) h

/-- What the witness decoder holds, relative to the model decoder collecting
`m` (read from the bytes `l`): the same size, the same indices in the same
order (each once), each held codeword the codeword of `l` at its index, and
every model chunk sourced from `m`. -/
structure Inv (m : Bytes) (l : List Std.U8) (d : Dec) (model : Model.Braid.Decoder) : Prop where
  bytes : l.map u8 = m
  len : l.length = model.size
  size : d.size = model.size
  bound : model.size ≤ Usize.max
  idx : d.chunks.map Prod.fst = model.chunks.map Model.Braid.Chunk.index
  held : ∀ p ∈ d.chunks, p.1 < 65536 ∧ p.2 = codeword l p.1
  nodup : (d.chunks.map Prod.fst).Nodup
  sources : ∀ c ∈ model.chunks, c.source = m

theorem any_index_eq (d : Dec) (model : Model.Braid.Decoder) (i : ℕ)
    (h : d.chunks.map Prod.fst = model.chunks.map Model.Braid.Chunk.index) :
    d.chunks.any (fun p => p.1 == i) = model.chunks.any (fun x => x.index == i) := by
  have h1 : d.chunks.any (fun p => p.1 == i) = (d.chunks.map Prod.fst).any (fun j => j == i) := by
    rw [List.any_map]; rfl
  have h2 : model.chunks.any (fun x => x.index == i)
      = (model.chunks.map Model.Braid.Chunk.index).any (fun j => j == i) := by
    rw [List.any_map]; rfl
  rw [h1, h2, h]

/-- Interpolating enough codewords of `l` recovers `l`. -/
theorem decode_correct (l : List Std.U8) (d : Dec) (hsize : d.size = l.length)
    (hcw : ∀ p ∈ d.chunks, p.1 < 65536 ∧ p.2 = codeword l p.1)
    (hnodup : (d.chunks.map Prod.fst).Nodup)
    (hcount : d.chunks.length * 32 ≥ d.size) : decode d = l := by
  simp only [decode]
  rw [hsize]
  by_cases hk : blocksOf l.length = 0
  · have hl : l = [] := by
      apply List.eq_nil_of_length_eq_zero
      have := le_blocks l.length; omega
    subst hl; simp
  · have hkpos : 0 < blocksOf l.length := Nat.pos_of_ne_zero hk
    have hcard : (d.chunks.map Prod.fst).toFinset.card = d.chunks.length := by
      rw [List.toFinset_card_of_nodup hnodup, List.length_map]
    have hks : blocksOf l.length ≤ (d.chunks.map Prod.fst).toFinset.card := by
      rw [hcard]; exact blocks_le _ _ (by omega)
    have hlt : ∀ i ∈ (d.chunks.map Prod.fst).toFinset, i < 65536 := by
      intro i hi
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hi)
      exact (hcw p hp).1
    have hr : ∀ i ∈ (d.chunks.map Prod.fst).toFinset,
        (match d.chunks.find? (fun p => p.1 == i) with
          | some p => sym p.2
          | none => 0) = (polyOf l).eval (pt i) := by
      intro i hi
      obtain ⟨p, hp, hpi⟩ := List.mem_map.mp (List.mem_toFinset.mp hi)
      cases hf : d.chunks.find? (fun p => p.1 == i) with
      | none =>
        exfalso
        have := List.find?_eq_none.mp hf p hp
        simp [hpi] at this
      | some q =>
        have hq := List.mem_of_find?_eq_some hf
        have hqi : q.1 = i := by simpa using List.find?_some hf
        simp only
        rw [(hcw q hq).2, hqi, codeword, Equiv.apply_symm_apply]
    have hcoef : ∀ j, j < blocksOf l.length →
        sym.symm ((Lagrange.interpolate (d.chunks.map Prod.fst).toFinset pt
          (fun i => match d.chunks.find? (fun p => p.1 == i) with
            | some p => sym p.2
            | none => 0)).coeff j) = block l j := by
      intro j hj
      rw [recover (blocksOf l.length) hkpos (fun j => sym (block l j)) _
        (pt_injOn _ hlt) hks _ hr j hj]
      exact Equiv.symm_apply_apply _ _
    have hflat : (List.range (blocksOf l.length)).flatMap
        (fun j => (sym.symm ((Lagrange.interpolate (d.chunks.map Prod.fst).toFinset pt
          (fun i => match d.chunks.find? (fun p => p.1 == i) with
            | some p => sym p.2
            | none => 0)).coeff j)).val)
        = (List.range (blocksOf l.length)).flatMap (fun j => (block l j).val) := by
      apply List.flatMap_congr
      intro j hj
      rw [hcoef j (List.mem_range.mp hj)]
    rw [hflat]
    exact unblock_message l

theorem sim_of_inv (m : Bytes) (l : List Std.U8) :
    ∀ (n : ℕ) (d : Dec) (model : Model.Braid.Decoder), Inv m l d model →
      DecoderSim api m n d model := by
  intro n
  induction n with
  | zero => intro _ _ _; trivial
  | succ n ih =>
    intro d model hinv
    refine ⟨?_, ?_⟩
    · -- add_chunk
      intro c advanced d' hcw hadd
      obtain ⟨l', hl', hlt, hc⟩ := codewordOf_api m c hcw
      have hll : l' = l := map_u8_injective (hl'.trans hinv.bytes.symm)
      subst hll
      simp only [api, decAdd] at hadd
      rw [any_index_eq d model c.index.val hinv.idx] at hadd
      simp only [Model.Braid.Decoder.addChunk]
      split at hadd
      · rename_i hdup
        rw [if_pos hdup]
        simp only [ok.injEq, Prod.mk.injEq] at hadd
        obtain ⟨-, rfl⟩ := hadd
        exact ih d model hinv
      · rename_i hdup
        rw [if_neg hdup]
        simp only [ok.injEq, Prod.mk.injEq] at hadd
        obtain ⟨-, rfl⟩ := hadd
        apply ih
        refine ⟨hinv.bytes, hinv.len, hinv.size, hinv.bound, ?_, ?_, ?_, ?_⟩
        · simp [hinv.idx]
        · intro p hp
          simp only [List.mem_cons] at hp
          rcases hp with rfl | hp
          · exact ⟨hlt, congrArg tacenta_erasure.Chunk.data hc⟩
          · exact hinv.held p hp
        · simp only [List.map_cons, List.nodup_cons]
          refine ⟨?_, hinv.nodup⟩
          intro hmem
          apply hdup
          rw [← any_index_eq d model c.index.val hinv.idx]
          simp only [List.any_eq_true, beq_iff_eq]
          obtain ⟨p, hp, hpi⟩ := List.mem_map.mp hmem
          exact ⟨p, hp, hpi⟩
        · intro x hx
          simp only [List.mem_cons] at hx
          rcases hx with rfl | hx
          · rfl
          · exact hinv.sources x hx
    · -- message
      intro msg hmsg
      simp only [api, decMsg] at hmsg
      have hlens : d.chunks.length = model.chunks.length := by
        have := congrArg List.length hinv.idx; simpa using this
      have hsize := hinv.size
      simp only [Model.Braid.Decoder.message, Model.Braid.Decoder.hasMessage]
      split at hmsg
      · rename_i hcount
        rw [dif_pos (hsize ▸ hinv.bound)] at hmsg
        simp only [ok.injEq] at hmsg
        subst hmsg
        have hcountM : model.chunks.length * Model.Braid.chunkBytes ≥ model.size := by
          simp only [Model.Braid.chunkBytes]; omega
        rw [if_pos (by simpa using hcountM)]
        have hdec := decode_correct l d (by rw [hsize, ← hinv.len]) hinv.held hinv.nodup hcount
        rcases hchunks : model.chunks with _ | ⟨c0, rest⟩
        · -- no chunks: the decoder was sized for zero bytes
          dsimp only
          have h0 : d.chunks.length = 0 := by rw [hlens, hchunks]; rfl
          have hl : l = [] := by
            apply List.eq_nil_of_length_eq_zero
            rw [hinv.len, ← hsize]
            omega
          simp only [hdec, hl]
          rfl
        dsimp only
        have hsrc : c0.source = m := hinv.sources c0 (by rw [hchunks]; simp)
        have hall : rest.all (fun x => x.source == c0.source) = true := by
          simp only [List.all_eq_true, beq_iff_eq]
          intro x hx
          rw [hinv.sources x (by rw [hchunks]; exact List.mem_cons_of_mem _ hx), hsrc]
        have hlenM : (c0.source.length == model.size) = true := by
          simp only [beq_iff_eq, hsrc, ← hinv.bytes, List.length_map]
          exact hinv.len
        rw [hall, hlenM]
        simp only [Bool.and_self, ite_true, Option.map_some, Option.some.injEq]
        simp only [vecOf, hdec, hsrc, ← hinv.bytes]
      · rename_i hcount
        simp only [ok.injEq] at hmsg
        subst hmsg
        simp only [Option.map_none]
        have hcountM : ¬ model.chunks.length * Model.Braid.chunkBytes ≥ model.size := by
          simp only [Model.Braid.chunkBytes]; omega
        rw [if_neg (by simpa using hcountM)]

/-! ## The witness satisfies `ErasureAgrees` -/

theorem encSim (l : List Std.U8) (src : Bytes) :
    ∀ (n k0 : ℕ), k0 + n ≤ 65536 → EncoderSim api n ⟨l, k0⟩ ⟨src, k0⟩ := by
  intro n
  induction n with
  | zero => intro _ _; trivial
  | succ n ih =>
    intro k0 hk
    refine ⟨mkChunk l k0, ⟨l, k0 + 1⟩, ?_, ?_, ?_⟩
    · simp only [api, encNext]; rw [if_pos (by omega)]
    · simp only [mkChunk, Model.Braid.Encoder.nextChunk]; exact idx_val k0 (by omega)
    · exact ih (k0 + 1) (by omega)

theorem api_agrees : ErasureAgrees api := by
  refine ⟨?_, ?_⟩
  · intro s
    refine ⟨⟨s.val, 0⟩, rfl, ⟨s, ⟨s.val, 0⟩, rfl, rfl, rfl⟩, ?_⟩
    intro n hn
    exact encSim s.val (sliceOf s) n 0 (by simpa [Model.Braid.encode] using hn)
  · intro n
    refine ⟨⟨n.val, []⟩, rfl, ?_⟩
    intro m hm _ k
    apply sim_of_inv m (m.map ofU8)
    refine ⟨?_, ?_, rfl, ?_, rfl, ?_, ?_, ?_⟩
    · rw [List.map_map]
      conv_rhs => rw [← List.map_id m]
      apply List.map_congr_left
      intro b _
      exact u8_ofU8 b
    · simpa [Model.Braid.Decoder.new] using hm
    · simp only [Model.Braid.Decoder.new]; scalar_tac
    · intro p hp; simp at hp
    · simp
    · intro c hc; simp [Model.Braid.Decoder.new] at hc

theorem api_cloneAgrees : ErasureCloneAgrees api := by
  refine ⟨?_, ?_⟩ <;> intro r r' h <;> simp only [api, ok.injEq] at h <;> exact h.symm

theorem api_totals : ErasureTotals api := by
  refine ⟨fun _ => ⟨_, rfl⟩, ?_, fun _ => ⟨_, rfl⟩, fun _ => ⟨_, rfl⟩, ?_, ?_, fun _ => ⟨_, rfl⟩⟩
  · intro e
    simp only [api, encNext]
    split <;> exact ⟨_, rfl⟩
  · intro d c
    simp only [api, decAdd]
    split <;> exact ⟨_, rfl⟩
  · intro d
    simp only [api, decMsg]
    split
    · split <;> exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩

/-- **The Braid's erasure boundary has a model.** An implementation of the
opaque erasure operations over the concrete 32-byte chunk exists that
satisfies, exactly as `BraidT3.lean` and `BraidT1.lean` state them and all
at once, `ErasureAgrees`, `ErasureCloneAgrees` and the seven erasure
totality assumptions. Jointly matters: a relation can be refutable *together
with* totality assumptions that are each satisfiable alone
(`Satisfiability.lean`'s `decoderSim_allSources_refutable` has exactly that
shape). A model of the hypotheses is not a proof that the real
crate satisfies them; it is proof that assuming them is not assuming
`False`. -/
theorem erasure_hypotheses_satisfiable :
    ∃ (Enc Dec : Type) (A : Api Enc Dec),
      ErasureAgrees A ∧ ErasureCloneAgrees A ∧ ErasureTotals A :=
  ⟨Enc, Dec, api, api_agrees, api_cloneAgrees, api_totals⟩

/-- The erasure agreement alone, for reference. -/
theorem erasureAgrees_satisfiable :
    ∃ (Enc Dec : Type) (A : Api Enc Dec), ErasureAgrees A :=
  ⟨Enc, Dec, api, api_agrees⟩

end Tacenta.ErasureWitness
