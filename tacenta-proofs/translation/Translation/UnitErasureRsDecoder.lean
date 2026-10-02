import Translation.UnitErasureRsKernel
import Translation.UnitErasureRsAlgebra
import Translation.UnitSatisfiabilityBraidAgreements

/-!
# The translated decoder of the unit refines `Model.Erasure.Decoder`

Two statements about the translated `Decoder` of the complete Session unit.

* `D_add`: `Decoder::add_chunk` refines `Model.Erasure.Decoder.add`.  One loop, the duplicate
  scan, whose invariant is that no index scanned so far equals the offered one.  When the held
  vector has length `Usize.max` the early return fires, because `needed` is a `usize`.
* `D_message`: `Decoder::message` refines `Model.Erasure.Decoder.message` under `DWf`.  Each of
  the five loops gets a value specification (`nodes_spec`, `direct_spec`, `vals_spec`,
  `lanes_spec`, `targets_spec`).  The kernels `weights`, `coefficients`, `evaluate` and the
  algebra identifying their output with `Model.Polynomial.interp` are used through the
  statements `UnitErasureRsKernel.K_weights`, `K_coefficients`, `K_evaluate` and
  `UnitErasureRsAlgebra.K_algebra`.  `Vec::truncate` is used through the hypothesis
  `TruncatePrefix` of `UnitSatisfiabilityBraidAgreements.lean`.

## What it does not show

* That `Vec::truncate` keeps the prefix: `TruncatePrefix` is a hypothesis of `D_message`, a law
  about an opaque standard-library function.
* That a reachable decoder keeps `DWf`, or that the model's `message` of the held codewords is
  the original message: those are `UnitErasureRsGlue.lean` and `UnitErasureRsModel.M_recover`.
* The model's field lemmas behind the kernel statements.  They are kernel proofs, so `D_add` rests
  on the kernel's three axioms and `D_message` adds the opaque constant `Vec::truncate`, which its
  hypothesis `TruncatePrefix` is about.
-/

open Aeneas Aeneas.Std Result
open tacenta_session_unit.tacenta_erasure

namespace Tacenta.UnitErasureRs.Decoder

open Tacenta.UnitErasureRs
open Tacenta.UnitErasureRs.Kernel (K_weights K_coefficients K_evaluate)
open Tacenta.UnitErasureRs.Algebra (K_algebra)

/-! ## `add_chunk` -/

/-- The duplicate scan of `add_chunk`: started at a position before which no held index equals
the offered one, it refuses exactly when some held index equals it, and otherwise appends. -/
theorem add_chunk_loop_spec (v : alloc.vec.Vec Chunk) (chunk : Chunk) (i : Usize)
    (hlen : v.val.length < Usize.max) (hi : i.val ≤ v.val.length)
    (hpre : ∀ idx (h : idx < v.val.length), idx < i.val → (v.val[idx]'h).index ≠ chunk.index) :
    Decoder.add_chunk_loop v chunk i ⦃ r =>
      (v.val.any (fun c => c.index == chunk.index) = true → r = (false, v)) ∧
      (v.val.any (fun c => c.index == chunk.index) = false → r.1 = true ∧ r.2.val = v.val ++ [chunk]) ⦄ := by
  unfold Decoder.add_chunk_loop
  apply loop.spec_decr_nat
    (measure := fun j => v.val.length - (j : Usize).val)
    (inv := fun j => j.val ≤ v.val.length ∧ ∀ idx (h : idx < v.val.length), idx < j.val → (v.val[idx]'h).index ≠ chunk.index)
  · rintro j ⟨hj, hpre⟩
    unfold Decoder.add_chunk_loop.body
    simp only []
    split
    · rename_i hjl
      have hjl' : j.val < v.val.length := by scalar_tac
      step*
      · refine ⟨fun _ => trivial, fun hany => ?_⟩
        exfalso
        have : (v.val.any (fun c => c.index == chunk.index)) = true :=
          List.any_eq_true.mpr ⟨v.val[j.val], List.getElem_mem _, by simp_all⟩
        simp_all
      · refine ⟨by scalar_tac, fun idx h hidx => ?_, by scalar_tac⟩
        by_cases e : idx = j.val
        · subst e; simp_all
        · exact hpre idx h (by omega)
    · rename_i hjl
      have hjl' : v.val.length ≤ j.val := by scalar_tac
      step*
      refine ⟨fun hany => ?_, fun _ => v1_post⟩
      exfalso
      obtain ⟨x, hx, hxe⟩ := List.any_eq_true.mp hany
      obtain ⟨idx, hidx, rfl⟩ := List.getElem_of_mem hx
      exact hpre idx hidx (by omega) (by simpa using hxe)
  · exact ⟨hi, hpre⟩

theorem haveHeld_length (d : Decoder) : (haveHeld d).length = d.«have».val.length := by
  simp [haveHeld]

theorem haveHeld_any (d : Decoder) (c : Chunk) :
    (haveHeld d).any (fun h => h.1 == c.index.val) =
      d.«have».val.any (fun x => x.index == c.index) := by
  simp only [haveHeld, List.any_map]
  congr 1
  funext x
  simp only [Function.comp]
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq]
  exact ⟨fun h => UScalar.eq_of_val_eq h, fun h => by rw [h]⟩

/-- **`Decoder::add_chunk` refines `Model.Erasure.Decoder.add`**: the held codewords are the
model's, `size` and `needed` are kept, and the returned flag says whether a codeword was added. -/
theorem D_add (d : Decoder) (c : Chunk) :
    Decoder.add_chunk d c ⦃ r =>
      haveHeld r.2 = (Model.Erasure.Decoder.add ⟨d.size.val, d.needed.val, haveHeld d⟩
        (c.index.val, cbytes c)).held ∧ r.2.size = d.size ∧ r.2.needed = d.needed ∧
      (r.1 = true ↔ r.2.«have».val.length ≠ d.«have».val.length) ⦄ := by
  unfold Decoder.add_chunk
  by_cases hge : d.«have».len ≥ d.needed
  · have hge' : d.needed.val ≤ d.«have».val.length := by
      have := alloc.vec.Vec.len_val d.«have»
      scalar_tac
    simp only [hge, if_true, WP.spec_ok]
    refine ⟨?_, by simp, by simp, by simp⟩
    simp [Model.Erasure.Decoder.add, haveHeld_length, hge']
  · have hlt : d.«have».val.length < d.needed.val := by
      have := alloc.vec.Vec.len_val d.«have»
      scalar_tac
    have hlen : d.«have».val.length < Usize.max := by
      have := d.needed.hBounds; scalar_tac
    simp only [hge, if_false]
    apply WP.spec_bind (add_chunk_loop_spec d.«have» c 0#usize hlen (by simp)
      (fun _ _ h => by simp at h))
    rintro ⟨b, v⟩ ⟨hdup, hnew⟩
    refine (WP.spec_ok (b, { d with «have» := v })).mpr ?_
    have hlt' : ¬ (d.«have».val.length ≥ d.needed.val) := by omega
    cases hany : d.«have».val.any (fun x => x.index == c.index)
    · obtain ⟨hb, hv⟩ := hnew hany
      simp only at hb hv
      subst hb
      refine ⟨?_, rfl, rfl, by simp [hv]⟩
      simp only [Model.Erasure.Decoder.add, haveHeld_length, hlt', if_false]
      rw [haveHeld_any, hany]
      simp [haveHeld, hv, cbytes]
    · have := hdup hany
      simp only [Prod.mk.injEq] at this
      obtain ⟨rfl, rfl⟩ := this
      refine ⟨?_, rfl, rfl, by simp⟩
      simp only [Model.Erasure.Decoder.add, haveHeld_length, hlt', if_false]
      rw [haveHeld_any, hany]
      simp [haveHeld]

/-! ## `message`: the lane helper and the lane value loop -/

theorem u8_toNat (x : U8) : (Tacenta.SessionUnitBraidT3.u8 x).toNat = x.val := by
  have := x.hBounds
  simp only [Tacenta.SessionUnitBraidT3.u8, UInt8.toNat_ofNat']
  scalar_tac

theorem getD_map_u8 (l : List U8) (n : ℕ) (h : n < l.length) :
    (l.map Tacenta.SessionUnitBraidT3.u8).getD n 0 = Tacenta.SessionUnitBraidT3.u8 (l[n]'h) := by
  simp [List.getD_eq_getElem?_getD, h]

/-- `lane` reads the model's `element`: bytes `2j` and `2j + 1`, big-endian. -/
theorem lane_spec (data : Array U8 32#usize) (j : Usize) (hj : j.val < 16) :
    lane data j ⦃ x => eps x = Model.Erasure.element (data.val.map Tacenta.SessionUnitBraidT3.u8) j.val ⦄ := by
  unfold lane
  step*
  have hlen : data.val.length = 32 := data.property
  have h1 : i1.val < 256 := by scalar_tac
  have h3 : i3.val < 256 := by scalar_tac
  have hhi : hi.val = i1.val := by rw [hi_post]; scalar_tac
  have hlo : lo.val = i3.val := by rw [lo_post]; scalar_tac
  have hi4 : i4.val = i1.val * 256 := by
    rw [i4_post1, hhi, Nat.shiftLeft_eq]; scalar_tac
  apply BitVec.eq_of_toNat_eq
  simp only [eps, UScalar.bv_or, BitVec.toNat_or, Model.Erasure.element, BitVec.toNat_ofNat]
  rw [getD_map_u8 _ _ (by omega), getD_map_u8 _ _ (by omega), u8_toNat, u8_toNat]
  have e4 : i4.bv.toNat = i4.val := rfl
  have el : lo.bv.toNat = lo.val := rfl
  rw [e4, el, hi4, hlo, i1_post, i3_post]
  simp only [i2_post, i_post]
  have hb : (↑(data.val)[2 * j.val + 1] : ℕ) < 2 ^ 8 := by
    have := (data.val[2 * j.val + 1]).hBounds; scalar_tac
  have := Nat.two_pow_add_eq_or_of_lt hb (data.val[2 * j.val]).val
  rw [show 2 ^ 8 * (data.val[2 * j.val]).val = (data.val[2 * j.val]).val * 256 from by omega] at this
  have ha : (↑(data.val)[2 * j.val] : ℕ) < 2 ^ 8 := by
    have := (data.val[2 * j.val]).hBounds; scalar_tac
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

theorem lanes_ok : LANES = ok 16#usize := by
  simp only [LANES, CHUNK_BYTES]
  rfl

/-- The lane value loop gathers lane `j` of every held chunk, in order. -/
theorem vals_spec (k : Usize) (v : alloc.vec.Vec Chunk) (j : Usize) (vals : alloc.vec.Vec U16)
    (hk : k.val = v.val.length) (hj : j.val < 16) (hroom : vals.val.length + k.val < Usize.max) :
    Decoder.message_loop1_loop1_loop0 k v j vals 0#usize ⦃ r =>
      r.val.map eps = vals.val.map eps ++ v.val.map (fun c => Model.Erasure.element (cbytes c) j.val) ⦄ := by
  unfold Decoder.message_loop1_loop1_loop0
  apply loop.spec_decr_nat
    (measure := fun p => k.val - (Prod.snd p).val)
    (inv := fun p => (Prod.snd p).val ≤ k.val ∧
      (Prod.fst p).val.map eps = vals.val.map eps ++
        (v.val.map (fun c => Model.Erasure.element (cbytes c) j.val)).take (Prod.snd p).val ∧
      (Prod.fst p).val.length = vals.val.length + (Prod.snd p).val)
  · rintro ⟨w1, i1⟩ ⟨hi1, hw1, hl1⟩
    simp only [] at hi1 hw1 hl1
    unfold Decoder.message_loop1_loop1_loop0.body
    simp only []
    split
    · rename_i hlt
      have hlt' : i1.val < v.val.length := by scalar_tac
      have hv : i1 < v.len := by scalar_tac
      simp only [hv, if_true]
      step as ⟨c, hc⟩
      step with lane_spec as ⟨x, hx⟩
      step as ⟨w2, hw2⟩
      step as ⟨i2, hi2⟩
      refine ⟨by scalar_tac, ?_, by simp [hw2, hl1, hi2]; omega, by scalar_tac⟩
      rw [hi2, List.take_add_one, List.getElem?_map, List.getElem?_eq_getElem hlt', hw2,
        List.map_append, hw1]
      simp [hx, hc, cbytes]
    · rename_i hge
      have hik : i1.val = k.val := by scalar_tac
      simp only [WP.spec_ok]
      rw [hw1, hik, hk, ← List.length_map (f := fun c => Model.Erasure.element (cbytes c) j.val),
        List.take_length]
  · refine ⟨by simp, by simp, by simp⟩

/-- The two bytes pushed per lane are the model's `elementBytes`. -/
theorem elementBytes_eps (r : U16) (i1 : U16) (hi1 : i1.val = r.val >>> 8) :
    Model.Erasure.elementBytes (eps r) =
      [Tacenta.SessionUnitBraidT3.u8 (UScalar.cast .U8 i1),
        Tacenta.SessionUnitBraidT3.u8 (UScalar.cast .U8 r)] := by
  have hr := r.hBounds
  have hv : (eps r).toNat = r.val := rfl
  simp only [Model.Erasure.elementBytes, hv, Tacenta.SessionUnitBraidT3.u8, List.cons.injEq,
    and_true]
  constructor
  · congr 1
    rw [UScalar.cast_val_eq, hi1, Nat.shiftRight_eq_div_pow]
    (try scalar_tac)
  · congr 1

/-- The lane values a decoder holding `v` interpolates, lane `j`. -/
def laneVals (v : alloc.vec.Vec Chunk) (j : ℕ) : List E :=
  v.val.map (fun c => Model.Erasure.element (cbytes c) j)

/-- The lane loop appends `ofLanes` of the evaluations of the given coefficients. -/
theorem lanes_spec (k : Usize) (v : alloc.vec.Vec Chunk) (out : alloc.vec.Vec U8)
    (c : alloc.vec.Vec U16)
    (hk : k.val = v.val.length) (hkmax : k.val < Usize.max)
    (hout : out.val.length + 32 ≤ Usize.max) :
    Decoder.message_loop1_loop1 k v out c 0#usize ⦃ r =>
      r.val.map Tacenta.SessionUnitBraidT3.u8 = out.val.map Tacenta.SessionUnitBraidT3.u8 ++
        Model.Erasure.ofLanes (fun j => evalSpec (c.val.map eps) (laneVals v j)) ∧
      r.val.length = out.val.length + 32 ⦄ := by
  unfold Decoder.message_loop1_loop1
  apply loop.spec_decr_nat
    (measure := fun p => 16 - (Prod.snd p).val)
    (inv := fun p => (Prod.snd p).val ≤ 16 ∧
      (Prod.fst p).val.map Tacenta.SessionUnitBraidT3.u8 = out.val.map Tacenta.SessionUnitBraidT3.u8 ++
        ((List.range (Prod.snd p).val).map
          (fun j => Model.Erasure.elementBytes (evalSpec (c.val.map eps) (laneVals v j)))).flatten ∧
      (Prod.fst p).val.length = out.val.length + 2 * (Prod.snd p).val)
  · rintro ⟨o1, jj⟩ ⟨hj1, ho1, hl1⟩
    simp only [] at hj1 ho1 hl1
    unfold Decoder.message_loop1_loop1.body
    simp only [lanes_ok, bind_tc_ok]
    split
    · rename_i hlt
      have hj16 : jj.val < 16 := by scalar_tac
      step with vals_spec as ⟨vals1, hvals1⟩
      · simp [alloc.vec.Vec.with_capacity]; omega
      simp only [alloc.vec.Vec.with_capacity, List.map_nil, List.nil_append] at hvals1
      step with K_evaluate as ⟨r, hr⟩
      step*
      · simp only [out1_post, List.length_append, List.length_singleton]; omega
      · have hev : evalSpec (c.val.map eps) (laneVals v jj.val) = eps r := by
          rw [hr]; simp only [alloc.vec.Vec.deref, laneVals]; rw [hvals1]
        refine ⟨by scalar_tac, ?_, by simp [out2_post, out1_post, hl1, j1_post]; omega,
          by scalar_tac⟩
        rw [j1_post, List.range_succ, List.map_append, List.flatten_append, out2_post, out1_post,
          List.map_append, List.map_append, ho1, List.append_assoc, List.append_assoc]
        congr 2
        simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
          List.append_nil, hev]
        rw [elementBytes_eps r i1 i1_post1, i2_post, i3_post]
        rfl
    · rename_i hge
      have hj : jj.val = 16 := by scalar_tac
      simp only [WP.spec_ok]
      refine ⟨?_, by omega⟩
      rw [ho1, hj]
      rfl
  · refine ⟨by simp, by simp, by simp⟩

/-! ## `message`: the direct search and the identification with the model's chunk -/

/-- One step of the direct search: the last held chunk at the target wins. -/
def pick (target : U16) (acc : Option Chunk) (c : Chunk) : Option Chunk :=
  if c.index = target then some c else acc

/-- The direct search returns the last held chunk whose index is the target. -/
theorem direct_spec (k : Usize) (v : alloc.vec.Vec Chunk) (target : U16) (direct : Option Chunk)
    (hk : k.val = v.val.length) :
    Decoder.message_loop1_loop0 k v target direct 0#usize ⦃ r =>
      r = v.val.foldl (pick target) direct ⦄ := by
  unfold Decoder.message_loop1_loop0
  apply loop.spec_decr_nat
    (measure := fun p => k.val - (Prod.snd p).val)
    (inv := fun p => (Prod.snd p).val ≤ k.val ∧
      (Prod.fst p) = (v.val.take (Prod.snd p).val).foldl (pick target) direct)
  · rintro ⟨d1, i1⟩ ⟨hi1, hd1⟩
    simp only [] at hi1 hd1
    unfold Decoder.message_loop1_loop0.body
    simp only []
    split
    · rename_i hlt
      have hlt' : i1.val < v.val.length := by scalar_tac
      have hv : i1 < v.len := by scalar_tac
      simp only [hv, if_true]
      step as ⟨c, hc⟩
      split
      · rename_i heq
        step as ⟨i2, hi2⟩
        refine ⟨by scalar_tac, ?_, by scalar_tac⟩
        rw [hi2, List.take_add_one, List.getElem?_eq_getElem hlt', List.foldl_append]
        simp [pick, ← hc, heq]
      · rename_i hne
        step as ⟨i2, hi2⟩
        refine ⟨by scalar_tac, ?_, by scalar_tac⟩
        rw [hi2, List.take_add_one, List.getElem?_eq_getElem hlt', List.foldl_append, ← hd1]
        simp [pick, ← hc, hne]
    · rename_i hge
      have hik : i1.val = k.val := by scalar_tac
      simp only [WP.spec_ok]
      rw [hd1, hik, hk, List.take_length]
  · exact ⟨by simp, by simp⟩

/-- With distinct indices, the last match is the first match. -/
theorem foldl_pick (target : U16) :
    ∀ (l : List Chunk) (acc : Option Chunk), (l.map (fun c => c.index.val)).Nodup →
      l.foldl (pick target) acc = (l.find? (fun c => c.index == target)).or acc
  | [], acc, _ => by simp
  | c :: l, acc, hnd => by
    simp only [List.map_cons, List.nodup_cons] at hnd
    simp only [List.foldl_cons, List.find?_cons]
    by_cases h : c.index = target
    · have hnone : ∀ c' ∈ l, c'.index ≠ target := by
        intro c' hc' e
        apply hnd.1
        rw [List.mem_map]
        exact ⟨c', hc', by rw [e, h]⟩
      have : ∀ acc', l.foldl (pick target) acc' = acc' := by
        intro acc'
        induction l generalizing acc' with
        | nil => rfl
        | cons c' l ih =>
          simp only [List.foldl_cons]
          rw [show pick target acc' c' = acc' by simp [pick, hnone c' (by simp)]]
          exact ih (by simp_all) (fun c'' hc'' => hnone c'' (by simp [hc''])) acc'
      simp [pick, h, this]
    · have hb : (c.index == target) = false := by simp [h]
      rw [foldl_pick target l _ hnd.2, hb]
      simp [pick, h]

theorem eps_eq_node (x : U16) : eps x = Model.Erasure.node x.val := by
  apply BitVec.eq_of_toNat_eq
  have h := x.hBounds
  have e : x.bv.toNat = x.val := rfl
  simp only [eps, Model.Erasure.node, BitVec.toNat_ofNat, e]
  scalar_tac

theorem eps_injective {x y : U16} (h : eps x = eps y) : x = y := by
  have hx : (eps x).toNat = x.val := rfl
  have hy : (eps y).toNat = y.val := rfl
  apply UScalar.eq_of_val_eq
  rw [← hx, ← hy, h]

/-- The held list a chunk vector stands for. -/
def heldOf (v : alloc.vec.Vec Chunk) : List (ℕ × List UInt8) :=
  v.val.map (fun c => (c.index.val, cbytes c))

theorem find_held (v : alloc.vec.Vec Chunk) (target : U16) (t : ℕ) (ht : target.val = t) :
    (heldOf v).find? (fun h => h.1 == t) =
      (v.val.find? (fun c => c.index == target)).map (fun c => (c.index.val, cbytes c)) := by
  simp only [heldOf, List.find?_map]
  congr 2
  funext c
  simp only [Function.comp, ← ht]
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq]
  exact ⟨fun h => UScalar.eq_of_val_eq h, fun h => by rw [h]⟩

/-- A target the decoder holds: the model's chunk is the held bytes. -/
theorem chunk_direct (M : Model.Erasure.Decoder) (v : alloc.vec.Vec Chunk)
    (hM : M.held = heldOf v) (target : U16) (t : ℕ) (ht : target.val = t) (c : Chunk)
    (h : v.val.find? (fun c => c.index == target) = some c) :
    M.chunk t = cbytes c := by
  simp only [Model.Erasure.Decoder.chunk, hM, find_held v target t ht, h, Option.map_some]

/-- A target the decoder does not hold: the model's chunk is what the kernels compute, by
`K_algebra` over the held indices, which are distinct. -/
theorem chunk_interp (M : Model.Erasure.Decoder) (v : alloc.vec.Vec Chunk)
    (hM : M.held = heldOf v) (target : U16) (t : ℕ) (ht : target.val = t)
    (hnd : (v.val.map (fun c => c.index.val)).Nodup)
    (h : v.val.find? (fun c => c.index == target) = none) :
    M.chunk t = Model.Erasure.ofLanes (fun j =>
      evalSpec (coeffSpec (v.val.map (fun c => eps c.index))
        (weightsSpec (v.val.map (fun c => eps c.index))) (eps target)) (laneVals v j)) := by
  simp only [Model.Erasure.Decoder.chunk, hM, find_held v target t ht, h, Option.map_none]
  congr 1
  funext j
  have hxs : v.val.map (fun c => eps c.index) =
      (v.val.map (fun c => c.index.val)).map (fun n => (BitVec.ofNat 16 n : E)) := by
    simp only [List.map_map]
    congr 1
    funext c
    simp [eps_eq_node, Model.Erasure.node]
  have hnd' : (v.val.map (fun c => eps c.index)).Nodup := by
    rw [hxs]
    refine List.Nodup.map_on ?_ hnd
    intro x hx y hy e
    obtain ⟨cx, -, rfl⟩ := List.mem_map.mp hx
    obtain ⟨cy, -, rfl⟩ := List.mem_map.mp hy
    have h1 := cx.index.hBounds
    have h2 := cy.index.hBounds
    have := congrArg BitVec.toNat e
    simp only [BitVec.toNat_ofNat] at this
    scalar_tac
  rw [K_algebra _ _ _ hnd' (by simp [laneVals]), laneVals, List.zip_map', eps_eq_node, ht]
  simp only [heldOf, List.map_map]
  congr 2
  funext c
  simp [eps_eq_node]

/-! ## `message`: the target loop -/

/-- The target loop appends the model's chunks `0, ..., k - 1`. -/
theorem targets_spec (k : Usize) (v : alloc.vec.Vec Chunk) (nodes : alloc.vec.Vec U16)
    (out : alloc.vec.Vec U8) (w : alloc.vec.Vec U16) (M : Model.Erasure.Decoder)
    (hk : k.val = v.val.length) (hk16 : k.val ≤ 65536)
    (hnd : (v.val.map (fun c => c.index.val)).Nodup)
    (hnodes : nodes.val = v.val.map (fun c => c.index))
    (hw : w.val.map eps = weightsSpec (nodes.val.map eps))
    (hM : M.held = heldOf v)
    (hout : out.val.length + 32 * k.val ≤ Usize.max) :
    Decoder.message_loop1 k v nodes out w 0#usize ⦃ r =>
      r.val.map Tacenta.SessionUnitBraidT3.u8 = out.val.map Tacenta.SessionUnitBraidT3.u8 ++
        ((List.range k.val).map M.chunk).flatten ⦄ := by
  unfold Decoder.message_loop1
  apply loop.spec_decr_nat
    (measure := fun p => k.val - (Prod.snd p).val)
    (inv := fun p => (Prod.snd p).val ≤ k.val ∧
      (Prod.fst p).val.map Tacenta.SessionUnitBraidT3.u8 = out.val.map Tacenta.SessionUnitBraidT3.u8 ++
        ((List.range (Prod.snd p).val).map M.chunk).flatten ∧
      (Prod.fst p).val.length = out.val.length + 32 * (Prod.snd p).val)
  · rintro ⟨o1, tt⟩ ⟨ht1, ho1, hl1⟩
    simp only [] at ht1 ho1 hl1
    unfold Decoder.message_loop1.body
    simp only []
    split
    · rename_i hlt
      have htk : tt.val < k.val := by scalar_tac
      step as ⟨target, htarget⟩
      step with direct_spec as ⟨direct, hdirect⟩
      have htv : target.val = tt.val := by rw [htarget, UScalar.cast_val_eq]; scalar_tac
      have hfind : direct = v.val.find? (fun c => c.index == target) := by
        rw [hdirect, foldl_pick target _ none hnd, Option.or_none]
      have hroom : o1.val.length + 32 ≤ Usize.max := by
        have : 32 * tt.val + 32 ≤ 32 * k.val := by omega
        omega
      rw [hfind]
      cases hf : v.val.find? (fun c => c.index == target) with
      | none =>
        simp only []
        step with K_coefficients as ⟨c, hc⟩
        step with lanes_spec as ⟨o2, ho2, hl2⟩
        step as ⟨t1, ht1'⟩
        have hch : M.chunk tt.val =
            Model.Erasure.ofLanes (fun j => evalSpec (c.val.map eps) (laneVals v j)) := by
          rw [chunk_interp M v hM target tt.val htv hnd hf, hc]
          simp only [alloc.vec.Vec.deref, hw, hnodes, List.map_map]
          rfl
        refine ⟨by omega, ?_, by omega, by omega⟩
        rw [ht1', List.range_succ, List.map_append, List.flatten_append, ho2, ho1,
          List.append_assoc]
        simp [hch]
      | some c =>
        simp only [lift, bind_tc_ok]
        step with Tacenta.SessionUnitErasureT1.extend_u8_spec as ⟨o2, ho2⟩
        step as ⟨t1, ht1'⟩
        have hch : M.chunk tt.val = cbytes c := chunk_direct M v hM target tt.val htv c hf
        have hl2 : o2.val.length = o1.val.length + 32 := by
          rw [ho2, List.length_append, Tacenta.SessionUnitErasureT1.to_slice_length_32]
        refine ⟨by omega, ?_, by omega, by omega⟩
        rw [ht1', List.range_succ, List.map_append, List.flatten_append, ho2, List.map_append, ho1,
          List.append_assoc]
        simp [hch, cbytes, Array.to_slice]
    · rename_i hge
      have hik : tt.val = k.val := by scalar_tac
      simp only [WP.spec_ok]
      rw [ho1, hik]
  · exact ⟨by simp, by simp, by simp⟩

/-! ## `message`: the node loop and the whole function -/

/-- The node loop collects the held indices, in order. -/
theorem nodes_spec (k : Usize) (v : alloc.vec.Vec Chunk) (nodes : alloc.vec.Vec U16)
    (hk : k.val = v.val.length) (hroom : nodes.val.length + k.val < Usize.max) :
    Decoder.message_loop0 k v nodes 0#usize ⦃ r =>
      r.val = nodes.val ++ v.val.map (fun c => c.index) ⦄ := by
  unfold Decoder.message_loop0
  apply loop.spec_decr_nat
    (measure := fun p => k.val - (Prod.snd p).val)
    (inv := fun p => (Prod.snd p).val ≤ k.val ∧
      (Prod.fst p).val = nodes.val ++ (v.val.map (fun c => c.index)).take (Prod.snd p).val ∧
      (Prod.fst p).val.length = nodes.val.length + (Prod.snd p).val)
  · rintro ⟨n1, i1⟩ ⟨hi1, hn1, hl1⟩
    simp only [] at hi1 hn1 hl1
    unfold Decoder.message_loop0.body
    simp only []
    split
    · rename_i hlt
      have hlt' : i1.val < v.val.length := by scalar_tac
      have hv : i1 < v.len := by scalar_tac
      simp only [hv, if_true]
      step as ⟨c, hc⟩
      step as ⟨n2, hn2⟩
      step as ⟨i2, hi2⟩
      refine ⟨by omega, ?_, by simp [hn2, hl1, hi2]; omega, by omega⟩
      rw [hi2, List.take_add_one, List.getElem?_map, List.getElem?_eq_getElem hlt', hn2, hn1]
      simp [hc]
    · rename_i hge
      have hik : i1.val = k.val := by scalar_tac
      simp only [WP.spec_ok]
      rw [hn1, hik, hk, ← List.length_map (f := fun c => c.index), List.take_length]
  · exact ⟨by simp, by simp, by simp⟩

/-- **`Decoder::message` refines `Model.Erasure.Decoder.message`** for a decoder that keeps the
invariant `DWf`, given that `Vec::truncate` keeps the prefix (`TruncatePrefix`). -/
theorem D_message (htr : Tacenta.UnitSatisfiabilityBraidAgreements.TruncatePrefix) (d : Decoder)
    (hwf : DWf d) :
    Decoder.message d ⦃ r =>
      r.map vbytes = Model.Erasure.Decoder.message ⟨d.size.val, d.needed.val, haveHeld d⟩ ⦄ := by
  obtain ⟨hnd, hle, hn16⟩ := hwf
  unfold Decoder.message
  simp only [Decoder.has_message, bind_tc_ok]
  by_cases hge : d.«have».len ≥ d.needed
  · have hk : d.needed.val = d.«have».val.length := by
      have := alloc.vec.Vec.len_val d.«have»
      scalar_tac
    have hmax : (2 : ℕ) ^ 21 ≤ Usize.max :=
      Tacenta.UnitSatisfiabilityBraidAgreements.usize_max_ge _ (by norm_num)
    rw [if_pos (by simp [hge])]
    step with nodes_spec as ⟨nodes1, hn1⟩
    · simp [alloc.vec.Vec.with_capacity]; omega
    simp only [alloc.vec.Vec.with_capacity, List.nil_append] at hn1
    step with K_weights as ⟨w, hw⟩
    step with targets_spec (M := ⟨d.size.val, d.needed.val, haveHeld d⟩) as ⟨out1, ho1⟩
    case hw => exact hw
    case hM => rfl
    case hout => simp only [alloc.vec.Vec.with_capacity, List.length_nil]; omega
    obtain ⟨out2, htr2, hv2⟩ := htr out1 d.size
    rw [htr2]
    simp only [bind_tc_ok, WP.spec_ok, Option.map_some]
    simp only [alloc.vec.Vec.with_capacity, List.map_nil, List.nil_append] at ho1
    have hnlt : ¬ (haveHeld d).length < d.needed.val := by simp [haveHeld]; omega
    simp only [Model.Erasure.Decoder.message, hnlt, if_false, vbytes, hv2]
    rw [List.map_take, ho1]
  · have hlt : d.«have».val.length < d.needed.val := by
      have := alloc.vec.Vec.len_val d.«have»
      scalar_tac
    rw [if_neg (by simp [hge])]
    simp [Model.Erasure.Decoder.message, haveHeld, hlt]

end Tacenta.UnitErasureRs.Decoder
