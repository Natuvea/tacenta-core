import Translation.UnitErasureRsKernel
import Translation.UnitErasureRsAlgebra
import Translation.UnitSatisfiabilityErasureAgrees
import Translation.UnitSatisfiabilityBraidAgreements

/-!
# The translated encoder of the unit builds the model's chunks and codewords

Two statements about the translated `Encoder` of the complete Session unit.

* `E_new`: `Encoder::new` stores the first `min (chunk_count len) 65536` zero-padded 32-byte blocks
  of the message, with `next = 0` and `exhausted = false`.  The outer loop `new_loop0` keeps the
  first `t` blocks after `t` turns (`new_outer_spec`); the inner loop `new_loop0_loop0` keeps the
  first `b` bytes of the block and zeros after them (`new_inner_spec`).  The one opaque operation
  is `usize::div_ceil`, through the hypothesis `DivCeilValue`.
* `E_next`: `Encoder::next_chunk` of a live encoder holding at most 65536 chunks emits
  `Model.Erasure.codeword` at `next`.  The systematic branch copies the stored chunk.  The parity
  branch builds the nodes `0 .. k - 1` (`nodes_spec`), gathers lane `j` of every stored chunk
  (`vals_spec`, `lane_spec`) and writes the two big-endian bytes of each lane (`lanes_spec`).
  The kernels `weights`, `coefficients`, `evaluate` and the Lagrange algebra enter only through
  their statements (`KWeights`, `KCoefficients`, `KEvaluate`, `KAlgebra`).  `E_next_of` takes
  them as hypotheses and has no other assumption; `E_next` discharges them with
  `UnitErasureRsKernel.K_weights`, `K_coefficients`, `K_evaluate` and
  `UnitErasureRsAlgebra.K_algebra`.

## What it does not show

* That `usize::div_ceil` returns the rounded-up quotient: `DivCeilValue` is a hypothesis of
  `E_new`.
* That the emitted codewords decode to the message: that is `UnitErasureRsModel.M_recover`, and
  the link to `Model.Braid` is `UnitErasureRsGlue.lean`.
* The model's field lemmas behind the kernel statements.  They are kernel proofs, so `E_next` rests
  on the kernel's three axioms; `E_new` adds the opaque constant `usize::div_ceil`, which its
  hypothesis `DivCeilValue` is about.
-/

open Aeneas Aeneas.Std Result
open tacenta_session_unit.tacenta_erasure

namespace Tacenta.UnitErasureRs.Encoder

open Tacenta.UnitErasureRs
open Tacenta.SessionUnitBraidT3 (u8 sliceOf)

/-! ## `Encoder::new` -/

/-- The bytes `start .. start + 32` of `m`, the first `b` of them kept and the rest zero. -/
def prefixBlock (m : List UInt8) (start b : ℕ) : List UInt8 :=
  (List.range 32).map fun i => if i < b then m.getD (start + i) 0 else 0

theorem sliceOf_getD (s : Slice U8) (i : ℕ) (h : i < s.val.length) :
    (sliceOf s).getD i 0 = u8 (s.val[i]) := by
  simp [sliceOf, List.getD_eq_getElem?_getD, h]

theorem sliceOf_getD_out (s : Slice U8) (i : ℕ) (h : s.val.length ≤ i) :
    (sliceOf s).getD i 0 = 0 := by
  simp [sliceOf, List.getD_eq_getElem?_getD, h]

theorem prefixBlock_length (m : List UInt8) (start b : ℕ) :
    (prefixBlock m start b).length = 32 := by
  simp [prefixBlock]

theorem prefixBlock_set (m : List UInt8) (start b : ℕ) :
    (prefixBlock m start b).set b (m.getD (start + b) 0) = prefixBlock m start (b + 1) := by
  apply List.ext_getElem
  · simp [prefixBlock]
  · intro i h1 h2
    simp only [List.getElem_set, prefixBlock, List.getElem_map, List.getElem_range]
    by_cases hi : b = i
    · subst hi; simp
    · simp only [hi, if_false]
      by_cases hib : i < b
      · simp [hib, show i < b + 1 by omega]
      · simp [hib, show ¬ i < b + 1 by omega]

theorem prefixBlock_zero (m : List UInt8) (start b : ℕ) (hz : m.getD (start + b) 0 = 0) :
    prefixBlock m start b = prefixBlock m start (b + 1) := by
  apply List.ext_getElem
  · simp [prefixBlock]
  · intro i h1 h2
    simp only [prefixBlock, List.getElem_map, List.getElem_range]
    by_cases hi : i = b
    · subst hi; simp only [Nat.lt_irrefl, if_false, Nat.lt_succ_self, if_true]
      rw [hz]
    · by_cases hib : i < b
      · simp [hib, show i < b + 1 by omega]
      · simp [hib, show ¬ i < b + 1 by omega]

/-- The inner loop of `Encoder::new` copies the block at `start`, zero padded. -/
theorem new_inner_spec (s : Slice U8) (buf : Array U8 32#usize) (start b : Usize)
    (hb : b.val ≤ 32) (hs : start.val + 32 ≤ Usize.max)
    (hbuf : buf.val.map u8 = prefixBlock (sliceOf s) start.val b.val) :
    Encoder.new_loop0_loop0 s buf start b ⦃ r =>
      r.val.map u8 = prefixBlock (sliceOf s) start.val 32 ⦄ := by
  unfold Encoder.new_loop0_loop0
  apply loop.spec_decr_nat
    (measure := fun p => 32 - (Prod.snd p).val)
    (inv := fun p => (Prod.snd p).val ≤ 32 ∧
      (Prod.fst p).val.map u8 = prefixBlock (sliceOf s) start.val (Prod.snd p).val)
  · rintro ⟨a1, c1⟩ ⟨hinv1, hinv2⟩
    simp only [] at hinv1 hinv2
    unfold Encoder.new_loop0_loop0.body
    simp only [CHUNK_BYTES]
    split
    · rename_i hlt
      have hb1 : c1.val < 32 := by scalar_tac
      step*
      split
      · rename_i hin
        step*
        refine ⟨by scalar_tac, ?_, by scalar_tac⟩
        rw [b1_post, buf1_post, Array.set_val_eq, List.map_set, hinv2]
        have hsl : (sliceOf s).getD (start.val + c1.val) 0 = u8 x := by
          rw [x_post]; simp only [← i_post]; exact sliceOf_getD s _ (by scalar_tac)
        rw [← hsl, prefixBlock_set]
      · rename_i hout
        step*
        refine ⟨by scalar_tac, ?_, by scalar_tac⟩
        rw [hinv2, b1_post]
        apply prefixBlock_zero
        rw [← i_post]; exact sliceOf_getD_out s _ (by scalar_tac)
    · rename_i hge
      simp only [WP.spec_ok]
      have : c1.val = 32 := by scalar_tac
      rw [hinv2, this]
  · exact ⟨hb, hbuf⟩

/-- Block `t` of a message as `Model.Erasure.chunks` cuts it. -/
def mblock (m : List UInt8) (t : ℕ) : List UInt8 :=
  let c := (m.drop (t * 32)).take 32
  c ++ List.replicate (32 - c.length) 0

theorem chunks_eq (m : List UInt8) :
    Model.Erasure.chunks m = (List.range (Model.Erasure.chunkCount m.length)).map (mblock m) := by
  rfl

theorem prefixBlock_full (m : List UInt8) (t : ℕ) : prefixBlock m (t * 32) 32 = mblock m t := by
  apply List.ext_getElem
  · simp [prefixBlock, mblock]
  · intro i h1 h2
    have hi : i < 32 := by simpa [prefixBlock] using h1
    simp only [prefixBlock, mblock, List.getElem_map, List.getElem_range, hi, if_true]
    rw [List.getElem_append]
    split
    · rename_i hc
      have : t * 32 + i < m.length := by simp at hc; omega
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem this]
    · rename_i hc
      have : m.length ≤ t * 32 + i := by simp at hc; omega
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none this]

/-- The outer loop of `Encoder::new` appends the blocks `t .. k - 1`. -/
theorem new_outer_spec (s : Slice U8) (k : Usize)
    (chunks : alloc.vec.Vec (Array U8 32#usize)) (t : Usize)
    (hk : k.val ≤ 65536) (ht : t.val ≤ k.val)
    (hc : storeBytes chunks = (List.range t.val).map (mblock (sliceOf s))) :
    Encoder.new_loop0 s k chunks t ⦃ r =>
      storeBytes r = (List.range k.val).map (mblock (sliceOf s)) ⦄ := by
  unfold Encoder.new_loop0
  apply loop.spec_decr_nat
    (measure := fun p => k.val - (Prod.snd p).val)
    (inv := fun p => (Prod.snd p).val ≤ k.val ∧
      storeBytes (Prod.fst p) = (List.range (Prod.snd p).val).map (mblock (sliceOf s)))
  · rintro ⟨c1, t1⟩ ⟨hinv1, hinv2⟩
    simp only [] at hinv1 hinv2
    unfold Encoder.new_loop0.body
    simp only []
    split
    · rename_i hlt
      have hbig : Usize.max ≥ 4294967295 := by scalar_tac
      have hlen : c1.val.length = t1.val := by
        have := congrArg List.length hinv2
        simpa [storeBytes] using this
      simp only [CHUNK_BYTES]
      step*
      have hinner := new_inner_spec s (Array.repeat 32#usize 0#u8) start 0#usize (by simp)
        (by scalar_tac) (by simp [prefixBlock, u8])
      obtain ⟨buf1, hb1, hbpost⟩ := WP.spec_imp_exists hinner
      rw [hb1]
      simp only [bind_tc_ok]
      step*
      refine ⟨by scalar_tac, ?_, by scalar_tac⟩
      rw [t1_post, List.range_succ, List.map_append, ← hinv2]
      simp only [storeBytes, chunks1_post, List.map_append, List.map_cons, List.map_nil]
      rw [hbpost, start_post, prefixBlock_full]
    · rename_i hge
      simp only [WP.spec_ok]
      have : t1.val = k.val := by scalar_tac
      rw [hinv2, this]
  · exact ⟨ht, hc⟩

theorem chunks_take (m : List UInt8) (n : ℕ) (hn : (m.length + 31) / 32 = n) :
    (Model.Erasure.chunks m).take 65536 = (List.range (min n 65536)).map (mblock m) := by
  rw [chunks_eq, ← List.map_take, List.take_range]
  have : Model.Erasure.chunkCount m.length = n := by
    simp only [Model.Erasure.chunkCount, Model.Erasure.chunkBytes]; omega
  rw [this, Nat.min_comm]

theorem sliceOf_length (s : Slice U8) : (sliceOf s).length = s.val.length := by
  simp [sliceOf]

/-- **`Encoder::new` builds the padded chunks of the message, at most `MAX_CODEWORDS` of them.** -/
theorem E_new (hdiv : Tacenta.SessionUnitDecoderBound.DivCeilValue) (s : Slice Std.U8) :
    Encoder.new s ⦃ e => e.next = 0#u16 ∧ e.exhausted = false ∧
      storeBytes e.chunks = (Model.Erasure.chunks (Tacenta.SessionUnitBraidT3.sliceOf s)).take 65536 ⦄ := by
  obtain ⟨r, hr, hrv⟩ := hdiv s.len
  have hmax : MAX_CODEWORDS.val = 65536 := by simp [MAX_CODEWORDS]
  have hlen : (s.len).val = (sliceOf s).length := by simp [sliceOf_length]
  have hk1 : ∀ k1 : Usize, k1.val = min r.val 65536 →
      Encoder.new_loop0 s k1 (alloc.vec.Vec.with_capacity (Std.Array U8 32#usize) k1) 0#usize ⦃ c =>
        storeBytes c = (Model.Erasure.chunks (sliceOf s)).take 65536 ⦄ := by
    intro k1 hk1
    have := new_outer_spec s k1 (alloc.vec.Vec.with_capacity (Std.Array U8 32#usize) k1) 0#usize
      (by omega) (by simp) (by simp [storeBytes, alloc.vec.Vec.with_capacity, alloc.vec.Vec.new])
    rw [chunks_take (sliceOf s) r.val (by omega), ← hk1]
    exact this
  unfold Encoder.new
  simp only [Tacenta.UnitSatisfiabilityErasure.chunk_count_eq, hr, bind_tc_ok]
  by_cases hx : r > MAX_CODEWORDS
  · simp only [hx, if_true, bind_tc_ok]
    obtain ⟨c, hc, hcp⟩ := WP.spec_imp_exists (hk1 MAX_CODEWORDS (by scalar_tac))
    rw [hc]
    simp only [bind_tc_ok, WP.spec_ok]
    exact ⟨trivial, trivial, hcp⟩
  · simp only [hx, if_false, bind_tc_ok]
    obtain ⟨c, hc, hcp⟩ := WP.spec_imp_exists (hk1 r (by scalar_tac))
    rw [hc]
    simp only [bind_tc_ok, WP.spec_ok]
    exact ⟨trivial, trivial, hcp⟩

/-! ## `Encoder::next_chunk` -/

theorem eps_eq (x : U16) : eps x = BitVec.ofNat 16 x.val := by
  unfold eps
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, UScalar.bv_toNat]
  have : x.val ≤ 65535 := by scalar_tac
  omega

theorem u8_toNat (x : U8) : (u8 x).toNat = x.val := by
  have : x.val ≤ 255 := by scalar_tac
  simp [u8]

theorem getD_map_u8 (data : Array U8 32#usize) (i : ℕ) (h : i < data.val.length) :
    (data.val.map u8).getD i 0 = u8 (data.val[i]) := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

theorem lane_spec (data : Array U8 32#usize) (j : Usize) (h : j.val < 16) :
    lane data j ⦃ r => eps r = Model.Erasure.element (data.val.map u8) j.val ⦄ := by
  have hl : data.val.length = 32 := data.property
  unfold lane
  step*
  have h1 : i1.val < 256 := by scalar_tac
  have h3 : i3.val < 256 := by scalar_tac
  have hi_v : hi.val = i1.val := by rw [hi_post]; simp
  have lo_v : lo.val = i3.val := by rw [lo_post]; simp
  have hi4 : i4.val = i1.val <<< 8 := by
    rw [i4_post1, hi_v]
    apply Nat.mod_eq_of_lt
    have hs : U16.size = 65536 := by simp [U16.size, U16.numBits]
    rw [Nat.shiftLeft_eq, hs]; omega
  have hv : (i4 ||| lo).val = i1.val * 256 + i3.val := by
    rw [UScalar.val_or, hi4, lo_v, ← Nat.shiftLeft_add_eq_or_of_lt (by omega), Nat.shiftLeft_eq]
  rw [eps_eq, hv]
  unfold Model.Erasure.element
  rw [getD_map_u8 data _ (by omega), getD_map_u8 data _ (by omega), u8_toNat, u8_toNat]
  simp only [i1_post, i3_post, i2_post, i_post]

theorem eps_cast_usize (s : Usize) (h : s.val < 65536) :
    eps (UScalar.cast .U16 s) = Model.Erasure.node s.val := by
  rw [eps_eq, UScalar.cast_val_eq]
  unfold Model.Erasure.node
  congr 1
  apply Nat.mod_eq_of_lt
  simpa [UScalarTy.numBits] using h

/-- The node loop of `next_chunk` builds the nodes `0 .. k - 1`. -/
theorem nodes_spec (k : Usize) (nodes : alloc.vec.Vec U16) (s : Usize) (hk : k.val ≤ 65536)
    (hs : s.val ≤ k.val) (hn : nodes.val.map eps = (List.range s.val).map Model.Erasure.node) :
    Encoder.next_chunk_loop0 k nodes s ⦃ r =>
      r.val.map eps = (List.range k.val).map Model.Erasure.node ⦄ := by
  unfold Encoder.next_chunk_loop0
  apply loop.spec_decr_nat
    (measure := fun p => k.val - (Prod.snd p).val)
    (inv := fun p => (Prod.snd p).val ≤ k.val ∧
      (Prod.fst p).val.map eps = (List.range (Prod.snd p).val).map Model.Erasure.node)
  · rintro ⟨n1, u1⟩ ⟨hinv1, hinv2⟩
    simp only [] at hinv1 hinv2
    unfold Encoder.next_chunk_loop0.body
    simp only []
    have hbig : Usize.max ≥ 4294967295 := by scalar_tac
    have hlen : n1.val.length = u1.val := by
      have := congrArg List.length hinv2
      simpa using this
    split
    · rename_i hlt
      step*
      refine ⟨by scalar_tac, ?_, by scalar_tac⟩
      rw [nodes1_post, s1_post, List.map_append, hinv2, List.range_succ, List.map_append]
      simp only [List.map_cons, List.map_nil, i_post]
      rw [eps_cast_usize u1 (by scalar_tac)]
    · rename_i hge
      simp only [WP.spec_ok]
      have : u1.val = k.val := by scalar_tac
      rw [hinv2, this]
  · exact ⟨hs, hn⟩

/-- Lane `j` of every chunk of a store. -/
def laneVals (cs : List (List UInt8)) (j : ℕ) : List E :=
  cs.map fun c => Model.Erasure.element c j

theorem storeBytes_take_succ (v : alloc.vec.Vec (Array U8 32#usize)) (s : ℕ)
    (h : s < v.val.length) :
    (storeBytes v).take (s + 1) = (storeBytes v).take s ++ [(v.val[s]).val.map u8] := by
  simp [storeBytes, List.take_add_one, List.getElem?_eq_getElem h]

/-- The value loop of `next_chunk` gathers lane `j` of every stored chunk. -/
theorem vals_spec (v : alloc.vec.Vec (Array U8 32#usize)) (k j : Usize)
    (vals : alloc.vec.Vec U16) (s : Usize)
    (hk : k.val = v.val.length) (hk2 : k.val ≤ 65536) (hj : j.val < 16) (hs : s.val ≤ k.val)
    (hv : vals.val.map eps = laneVals ((storeBytes v).take s.val) j.val) :
    Encoder.next_chunk_loop1_loop0 v k j vals s ⦃ r =>
      r.val.map eps = laneVals (storeBytes v) j.val ⦄ := by
  unfold Encoder.next_chunk_loop1_loop0
  apply loop.spec_decr_nat
    (measure := fun p => k.val - (Prod.snd p).val)
    (inv := fun p => (Prod.snd p).val ≤ k.val ∧
      (Prod.fst p).val.map eps = laneVals ((storeBytes v).take (Prod.snd p).val) j.val)
  · rintro ⟨w1, u1⟩ ⟨hinv1, hinv2⟩
    simp only [] at hinv1 hinv2
    unfold Encoder.next_chunk_loop1_loop0.body
    simp only []
    have hbig : Usize.max ≥ 4294967295 := by scalar_tac
    have hlen : w1.val.length = u1.val := by
      have := congrArg List.length hinv2
      simp [laneVals, storeBytes] at this
      omega
    split
    · rename_i hlt
      have hu : u1.val < v.val.length := by scalar_tac
      step*
      split
      · step
        step with lane_spec
        step*
        refine ⟨by scalar_tac, ?_, by scalar_tac⟩
        rw [vals1_post, s1_post, storeBytes_take_succ v _ hu, List.map_append, hinv2]
        simp only [laneVals, List.map_append, List.map_cons, List.map_nil, x_post]
        subst_vars
        rfl
      · exfalso
        rename_i hn
        apply hn
        scalar_tac
    · rename_i hge
      simp only [WP.spec_ok]
      have : u1.val = v.val.length := by scalar_tac
      rw [hinv2, this, List.take_of_length_le (by simp [storeBytes])]
  · exact ⟨hs, hv⟩

/-! The four kernel statements, as propositions.  The proofs below take them as hypotheses, and
`E_next` discharges them with `Kernel.K_weights`, `Kernel.K_coefficients`, `Kernel.K_evaluate`
and `Algebra.K_algebra`, so that `E_next_of` shows by its axiom list that nothing else is
assumed. -/

/-- The statement of `K_weights`. -/
abbrev KWeights : Prop :=
  ∀ s : Slice U16, weights s ⦃ w => w.val.map eps = weightsSpec (s.val.map eps) ⦄

/-- The statement of `K_coefficients`. -/
abbrev KCoefficients : Prop :=
  ∀ (s sw : Slice U16) (x : U16),
    coefficients s sw x ⦃ c => c.val.map eps = coeffSpec (s.val.map eps) (sw.val.map eps) (eps x) ⦄

/-- The statement of `K_evaluate`. -/
abbrev KEvaluate : Prop :=
  ∀ s sv : Slice U16, evaluate s sv ⦃ r => eps r = evalSpec (s.val.map eps) (sv.val.map eps) ⦄

/-- The statement of `K_algebra`. -/
abbrev KAlgebra : Prop :=
  ∀ (xs ys : List E) (x : E), xs.Nodup → ys.length = xs.length →
    evalSpec (coeffSpec xs (weightsSpec xs) x) ys = Model.Polynomial.interp (xs.zip ys) x

/-- The value of lane `j` that the lane loop writes: the coefficients against lane `j` of the
store. -/
def laneOut (cm : List E) (cs : List (List UInt8)) (j : ℕ) : E := evalSpec cm (laneVals cs j)

/-- The output chunk after `j` lanes: their bytes, then zeros. -/
def outPrefix (f : ℕ → E) (j : ℕ) : List UInt8 :=
  ((List.range j).map fun i => Model.Erasure.elementBytes (f i)).flatten ++
    List.replicate (32 - 2 * j) 0

theorem lanesBytes_length (f : ℕ → E) (j : ℕ) :
    ((List.range j).map fun i => Model.Erasure.elementBytes (f i)).flatten.length = 2 * j := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [List.range_succ, List.map_append, List.flatten_append, List.length_append, ih]
    simp [Model.Erasure.elementBytes]
    omega

theorem set_set_append (L : List UInt8) (n : ℕ) (x y : UInt8) :
    ((L ++ List.replicate (n + 2) 0).set L.length x).set (L.length + 1) y =
      L ++ [x, y] ++ List.replicate n 0 := by
  rw [List.set_append_right _ _ (le_refl _), List.set_append_right _ _ (by omega)]
  simp [List.replicate_succ]

theorem outPrefix_succ (f : ℕ → E) (j : ℕ) (hj : j < 16) (x y : UInt8)
    (hxy : [x, y] = Model.Erasure.elementBytes (f j)) :
    ((outPrefix f j).set (2 * j) x).set (2 * j + 1) y = outPrefix f (j + 1) := by
  unfold outPrefix
  have h1 : 32 - 2 * j = (32 - 2 * (j + 1)) + 2 := by omega
  rw [h1, ← lanesBytes_length f j, set_set_append, hxy, List.range_succ, List.map_append,
    List.flatten_append]
  simp

theorem outPrefix_zero (f : ℕ → E) : outPrefix f 0 = List.replicate 32 0 := by
  simp [outPrefix]

theorem outPrefix_full (f : ℕ → E) : outPrefix f 16 = Model.Erasure.ofLanes f := by
  simp [outPrefix, Model.Erasure.ofLanes, Model.Erasure.lanes]

/-- The lane loop of `next_chunk` writes the big-endian bytes of every lane. -/
theorem lanes_spec (hE : KEvaluate) (v : alloc.vec.Vec (Array U8 32#usize)) (k : Usize)
    (c : alloc.vec.Vec U16)
    (out : Array U8 32#usize) (j : Usize)
    (hk : k.val = v.val.length) (hk2 : k.val ≤ 65536) (hj : j.val ≤ 16)
    (ho : out.val.map u8 = outPrefix (laneOut (c.val.map eps) (storeBytes v)) j.val) :
    Encoder.next_chunk_loop1 v k c out j ⦃ r =>
      r.val.map u8 = Model.Erasure.ofLanes (laneOut (c.val.map eps) (storeBytes v)) ⦄ := by
  unfold Encoder.next_chunk_loop1
  apply loop.spec_decr_nat
    (measure := fun p => 16 - (Prod.snd p).val)
    (inv := fun p => (Prod.snd p).val ≤ 16 ∧
      (Prod.fst p).val.map u8 = outPrefix (laneOut (c.val.map eps) (storeBytes v)) (Prod.snd p).val)
  · rintro ⟨o1, u1⟩ ⟨hinv1, hinv2⟩
    simp only [] at hinv1 hinv2
    unfold Encoder.next_chunk_loop1.body
    simp only [LANES, CHUNK_BYTES]
    step
    split
    · rename_i hlt
      have hu : u1.val < 16 := by scalar_tac
      have hvals := vals_spec v k u1 (alloc.vec.Vec.with_capacity U16 k) 0#usize hk hk2 hu
        (by simp) (by simp [alloc.vec.Vec.with_capacity, alloc.vec.Vec.new, laneVals])
      obtain ⟨vals1, hv1, hvp⟩ := WP.spec_imp_exists hvals
      simp only [hv1, bind_tc_ok]
      have hE' : ∀ s sv : Slice U16,
          evaluate s sv ⦃ r => eps r = evalSpec (s.val.map eps) (sv.val.map eps) ⦄ := hE
      step with hE'
      step*
      refine ⟨by scalar_tac, ?_, by scalar_tac⟩
      rw [a_post, out1_post, Array.set_val_eq, Array.set_val_eq, List.map_set, List.map_set, hinv2,
        i4_post, i2_post, j1_post]
      apply outPrefix_succ _ _ hu
      have hlo : laneOut (c.val.map eps) (storeBytes v) u1.val = eps v1 := by
        rw [v1_post, laneOut, ← hvp]; rfl
      have hv1 : v1.val ≤ 65535 := by scalar_tac
      have htn : (eps v1).toNat = v1.val := by simp [eps]
      rw [hlo, Model.Erasure.elementBytes, htn, i3_post, i5_post]
      simp only [u8, UScalar.cast_val_eq, i1_post1, Nat.shiftRight_eq_div_pow]
      have h8 : UScalarTy.U8.numBits = 8 := rfl
      rw [h8]
      congr 2
      omega
    · rename_i hge
      simp only [WP.spec_ok]
      have : u1.val = 16 := by scalar_tac
      rw [hinv2, this, outPrefix_full]
  · exact ⟨hj, ho⟩

theorem node_nodup (k : ℕ) (hk : k ≤ 65536) : ((List.range k).map Model.Erasure.node).Nodup := by
  apply List.Nodup.map_on
  · intro x hx y hy hxy
    simp only [List.mem_range] at hx hy
    unfold Model.Erasure.node at hxy
    have := congrArg BitVec.toNat hxy
    simp only [BitVec.toNat_ofNat] at this
    omega
  · exact List.nodup_range

theorem storeBytes_length (v : alloc.vec.Vec (Array U8 32#usize)) :
    (storeBytes v).length = v.val.length := by
  simp [storeBytes]

/-- The parity lanes the kernels compute are the model's interpolants. -/
theorem parity_lanes (hA : KAlgebra) (cs : List (List UInt8)) (hk : cs.length ≤ 65536) (x : U16) :
    (laneOut (coeffSpec ((List.range cs.length).map Model.Erasure.node)
        (weightsSpec ((List.range cs.length).map Model.Erasure.node)) (eps x)) cs) =
      fun j => Model.Polynomial.interp
        (((List.range cs.length).zip cs).map fun p =>
          (Model.Erasure.node p.1, Model.Erasure.element p.2 j)) (Model.Erasure.node x.val) := by
  funext j
  unfold laneOut
  rw [hA _ _ _ (node_nodup _ hk) (by simp [laneVals])]
  have hx : eps x = Model.Erasure.node x.val := by rw [eps_eq]; rfl
  rw [hx, laneVals, List.zip_map]
  rfl

theorem u16_succ_le {x : U16} (h : ¬x = core.num.U16.MAX) : x.val + 1 ≤ U16.max := by
  have hne : x.val ≠ U16.max := by
    intro e
    exact h (UScalar.eq_of_val_eq (by simpa [core.num.U16.MAX, U16.max, U16.rMax, U16.numBits] using e))
  scalar_tac

/-- The common end of both branches of `next_chunk`: the chunk returned carries `data`. -/
theorem next_chunk_tail (e : Encoder) (data : Array U8 32#usize) (X : List UInt8)
    (h : data.val.map u8 = X) :
    (if e.next = core.num.U16.MAX then
        ok (some ({ index := e.next, data := data } : Chunk),
          ({ chunks := e.chunks, next := e.next, exhausted := true } : Encoder))
      else do
        let i1 ← e.next + 1#u16
        ok (some ({ index := e.next, data := data } : Chunk),
          ({ chunks := e.chunks, next := i1, exhausted := false } : Encoder))) ⦃
      r => ∀ ch, r.1 = some ch → cbytes ch = X ⦄ := by
  split
  · simp only [WP.spec_ok]
    rintro ch ⟨⟩
    exact h
  · rename_i hm
    have := u16_succ_le hm
    step*
    rintro ch ⟨⟩
    exact h

/-- `E_next` from the four kernel statements, taken as hypotheses. -/
theorem E_next_of (hW : KWeights) (hC : KCoefficients) (hE : KEvaluate) (hA : KAlgebra)
    (e : Encoder) (hne : e.exhausted = false) (hlen : e.chunks.val.length ≤ 65536) :
    Encoder.next_chunk e ⦃ r => ∀ ch, r.1 = some ch →
      cbytes ch = Model.Erasure.codeword (storeBytes e.chunks) e.next.val ⦄ := by
  have hbig : Usize.max ≥ 4294967295 := by scalar_tac
  have hlv : (e.chunks.len).val = e.chunks.val.length := alloc.vec.Vec.len_val _
  have hcast : (UScalar.cast .Usize e.next).val = e.next.val := U16.cast_Usize_val_eq e.next
  unfold Encoder.next_chunk
  simp only [hne, Bool.false_eq_true, if_false, lift, bind_tc_ok]
  split
  · rename_i hlt
    have ht : e.next.val < e.chunks.val.length := by scalar_tac
    step as ⟨data, hdata⟩
    apply next_chunk_tail
    rw [Model.Erasure.codeword_systematic _ _ (by rw [storeBytes_length]; exact ht), hdata]
    simp [storeBytes, List.getD_eq_getElem?_getD, hcast, List.getElem?_eq_getElem ht]
  · rename_i hge
    have ht : e.chunks.val.length ≤ e.next.val := by scalar_tac
    step with nodes_spec e.chunks.len (alloc.vec.Vec.with_capacity U16 e.chunks.len) 0#usize
      (by omega) (by simp)
      (by simp [alloc.vec.Vec.with_capacity, alloc.vec.Vec.new]) as ⟨nodes1, hn1⟩
    have hW' : ∀ s : Slice U16, weights s ⦃ w => w.val.map eps = weightsSpec (s.val.map eps) ⦄ := hW
    have hC' : ∀ (s sw : Slice U16) (x : U16), coefficients s sw x ⦃ c =>
        c.val.map eps = coeffSpec (s.val.map eps) (sw.val.map eps) (eps x) ⦄ := hC
    step with hW' as ⟨w, hw⟩
    step with hC' as ⟨c, hc⟩
    step with lanes_spec hE e.chunks e.chunks.len c (Array.repeat 32#usize 0#u8) 0#usize hlv
      (by omega) (by simp)
      (by simp [outPrefix_zero, u8]) as ⟨data, hd⟩
    apply next_chunk_tail
    rw [hd]
    have hL : (storeBytes e.chunks).length = e.chunks.val.length := storeBytes_length _
    have hcm : c.val.map eps = coeffSpec ((List.range (storeBytes e.chunks).length).map
        Model.Erasure.node) (weightsSpec ((List.range (storeBytes e.chunks).length).map
        Model.Erasure.node)) (eps e.next) := by
      have hd1 : (nodes1.deref).val = nodes1.val := rfl
      have hd2 : (w.deref).val = w.val := rfl
      rw [hd1] at hw hc
      rw [hd2, hw] at hc
      rw [hL, ← hlv, ← hn1]
      exact hc
    unfold Model.Erasure.codeword
    rw [if_neg (by omega), hcm, parity_lanes hA _ (by omega)]

/-- **`Encoder::next_chunk` of a live encoder with at most `MAX_CODEWORDS` chunks emits
`Model.Erasure.codeword` at the index `next`.**  The kernels are the statements
`Kernel.K_weights`, `Kernel.K_coefficients`, `Kernel.K_evaluate` and `Algebra.K_algebra`. -/
theorem E_next (e : Encoder) (hne : e.exhausted = false) (hlen : e.chunks.val.length ≤ 65536) :
    Encoder.next_chunk e ⦃ r => ∀ ch, r.1 = some ch →
      cbytes ch = Model.Erasure.codeword (storeBytes e.chunks) e.next.val ⦄ :=
  E_next_of Kernel.K_weights Kernel.K_coefficients Kernel.K_evaluate
    (fun xs ys x hnd hl => Algebra.K_algebra xs ys x hnd hl) e hne hlen

end Tacenta.UnitErasureRs.Encoder
