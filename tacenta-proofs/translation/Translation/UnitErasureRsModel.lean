import Model.Erasure
import Model.Polynomial
import Mathlib.Data.Nat.Notation
import Mathlib.Data.List.Nodup

/-!
# Reed-Solomon recovery in the byte-level model of the erasure code

`M_recover`: the decoder of `Model.Erasure`, holding the codewords of a message `m` at
`k = chunkCount m.length` distinct indices below 65536, in any order, returns `m`.  It is a
statement about the model only and does not mention the translated code.

The argument.  Let `cs = chunks m`.  For each lane `j < 16`, `P_j = interpP (sys cs j)` is the
polynomial through the systematic points `(node t, element cs[t] j)`, of degree at most `k`
(`deg_interpP`).  Every codeword's lane `j` is `P_j` at the codeword's node (`codeword_lane`):
for an index below `k` by the delta property `interp_eq`, otherwise by the definition of
`codeword` and the lane round trip `element_ofLanes`.  Nodes below 65536 are distinct
(`node_inj`), so `unisolvence` makes the interpolant through the `k` held lanes equal to `P_j`
everywhere, and `Decoder.chunk` returns chunk `t` for every `t < k` (`chunk_recover`), with the
chunk round trip `ofLanes_element`.  The chunks flatten to `m` followed by zero bytes
(`chunks_flatten_take`), and `Decoder.message` truncates to `m.length`.

## What it does not show

* That the translated decoder computes `Model.Erasure.Decoder.message`: that is
  `UnitErasureRsDecoder.D_message`.
* The field facts of `Model.Gf65536` and `Model.Polynomial` that `unisolvence` and `interp_eq` rest
  on.  The kernel proves them, so the axiom footprint of `M_recover` is `propext`,
  `Classical.choice` and `Quot.sound`.  This module adds no axiom.
-/

namespace Tacenta.UnitErasureRs.Recovery

open Model.Erasure
open Model.Polynomial
open Model.Gf65536 (Elem)

/-! ## Nodes -/

theorem node_inj {a b : ℕ} (ha : a < 65536) (hb : b < 65536) (h : node a = node b) : a = b := by
  have := congrArg BitVec.toNat h
  simp only [node, BitVec.toNat_ofNat] at this
  rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this
  exact this

theorem nodup_map_node {l : List ℕ} (hnd : l.Nodup) (hlt : ∀ i ∈ l, i < 65536) :
    (l.map node).Nodup :=
  hnd.map_on (fun a ha b hb h => node_inj (hlt a ha) (hlt b hb) h)

/-! ## Bytes and lanes -/

/-- Indexing into a flattened list of two-element lists. -/
theorem flatten_getD_two {α : Type} (L : List (List α)) (hL : ∀ l ∈ L, l.length = 2)
    (j r : ℕ) (hr : r < 2) (d : α) :
    L.flatten.getD (2 * j + r) d = (L.getD j []).getD r d := by
  induction L generalizing j with
  | nil => simp
  | cons l L ih =>
    have hl : l.length = 2 := hL l (by simp)
    have ih' := ih (fun l' hl' => hL l' (by simp [hl']))
    cases j with
    | zero =>
      simp only [List.flatten_cons, Nat.mul_zero, Nat.zero_add, List.getD_cons_zero]
      simp only [List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    | succ j =>
      simp only [List.flatten_cons, List.getD_cons_succ]
      simp only [List.getD_eq_getElem?_getD] at ih' ⊢
      rw [List.getElem?_append_right (by omega), hl]
      have : 2 * (j + 1) + r - 2 = 2 * j + r := by omega
      rw [this, ih' j]

theorem length_flatten_two {α : Type} (L : List (List α)) (hL : ∀ l ∈ L, l.length = 2) :
    L.flatten.length = 2 * L.length := by
  induction L with
  | nil => simp
  | cons l L ih =>
    have hl : l.length = 2 := hL l (by simp)
    simp only [List.flatten_cons, List.length_append, hl, List.length_cons,
      ih (fun l' hl' => hL l' (by simp [hl']))]
    omega

theorem elementBytes_length (e : Elem) : (elementBytes e).length = 2 := rfl

theorem ofLanes_getD (f : ℕ → Elem) (j r : ℕ) (hj : j < lanes) (hr : r < 2) :
    (ofLanes f).getD (2 * j + r) 0 = (elementBytes (f j)).getD r 0 := by
  unfold ofLanes
  rw [flatten_getD_two _ (by simp [elementBytes]) j r hr]
  simp [List.getD_eq_getElem?_getD, hj]

/-- Lane `j` of a codeword written from lanes is that lane. -/
theorem element_ofLanes (f : ℕ → Elem) (j : ℕ) (hj : j < lanes) :
    element (ofLanes f) j = f j := by
  unfold element
  have h0 := ofLanes_getD f j 0 hj (by omega)
  have h1 := ofLanes_getD f j 1 hj (by omega)
  simp only [Nat.add_zero] at h0
  rw [h0, h1]
  simp only [elementBytes, List.getD_cons_zero, List.getD_cons_succ]
  have hx := (f j).isLt
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, UInt8.toNat_ofNat', Nat.reducePow] at hx ⊢
  omega

/-- The two bytes of a lane read from a chunk are those bytes. -/
theorem elementBytes_element (c : Bytes) (j : ℕ) :
    elementBytes (element c j) = [c.getD (2 * j) 0, c.getD (2 * j + 1) 0] := by
  unfold elementBytes element
  have ha := (c.getD (2 * j) 0).toNat_lt
  have hb := (c.getD (2 * j + 1) 0).toNat_lt
  have hv : (BitVec.ofNat 16 ((c.getD (2 * j) 0).toNat * 256 + (c.getD (2 * j + 1) 0).toNat)).toNat
      = (c.getD (2 * j) 0).toNat * 256 + (c.getD (2 * j + 1) 0).toNat := by
    simp only [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  rw [hv]
  congr 2
  · apply UInt8.toNat_inj.mp
    simp only [UInt8.toNat_ofNat', Nat.reducePow]
    omega
  · apply UInt8.toNat_inj.mp
    simp only [UInt8.toNat_ofNat', Nat.reducePow]
    omega

/-- A 32-byte chunk read as lanes and written back is itself. -/
theorem ofLanes_element (c : Bytes) (hc : c.length = chunkBytes) :
    ofLanes (fun j => element c j) = c := by
  have hlen : (ofLanes (fun j => element c j)).length = c.length := by
    unfold ofLanes
    rw [length_flatten_two _ (by simp [elementBytes])]
    simp [hc, lanes, chunkBytes]
  apply List.ext_getElem hlen
  intro i h1 h2
  have hi : i = 2 * (i / 2) + i % 2 := by omega
  have hq : i / 2 < lanes := by simp only [lanes]; simp only [hc, chunkBytes] at h2; omega
  have key := ofLanes_getD (fun j => element c j) (i / 2) (i % 2) hq (Nat.mod_lt _ (by omega))
  rw [← hi, elementBytes_element] at key
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1] at key
  simp only [Option.getD_some] at key
  rw [key]
  rcases Nat.mod_two_eq_zero_or_one i with h | h
  · rw [h]
    simp only [List.getD_cons_zero]
    have : 2 * (i / 2) = i := by omega
    rw [this, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]
    rfl
  · rw [h]
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    have : 2 * (i / 2) + 1 = i := by omega
    rw [this, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]
    rfl

theorem ofLanes_congr (f g : ℕ → Elem) (h : ∀ j < lanes, f j = g j) : ofLanes f = ofLanes g := by
  unfold ofLanes
  congr 1
  apply List.map_congr_left
  intro j hj
  rw [h j (List.mem_range.mp hj)]

/-! ## The padded blocks of a message flatten to the message -/

/-- A block padded with zero bytes to a chunk. -/
def pad (c : Bytes) : Bytes := c ++ List.replicate (chunkBytes - c.length) 0

/-- The first `t` padded blocks of `m`. -/
def blocks (m : Bytes) (t : ℕ) : List Bytes :=
  (List.range t).map fun s => pad ((m.drop (s * chunkBytes)).take chunkBytes)

theorem chunks_eq_blocks (m : Bytes) : chunks m = blocks m (chunkCount m.length) := rfl

theorem blocks_succ (m : Bytes) (t : ℕ) :
    blocks m (t + 1) = pad (m.take chunkBytes) :: blocks (m.drop chunkBytes) t := by
  simp only [blocks, List.range_succ_eq_map, List.map_cons, List.map_map]
  congr 1
  apply List.map_congr_left
  intro s _
  simp only [Function.comp, List.drop_drop]
  congr 3
  simp only [chunkBytes]
  omega

theorem blocks_flatten_take (t : ℕ) : ∀ m : Bytes, m.length ≤ t * chunkBytes →
    (blocks m t).flatten.take m.length = m := by
  induction t with
  | zero =>
    intro m hm
    have : m = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    simp
  | succ t ih =>
    intro m hm
    rw [blocks_succ, List.flatten_cons]
    by_cases hs : m.length ≤ chunkBytes
    · rw [List.take_of_length_le hs, pad, List.append_assoc]
      exact List.take_left' rfl
    · have htl : (m.take chunkBytes).length = chunkBytes := by
        rw [List.length_take]; omega
      have hp : pad (m.take chunkBytes) = m.take chunkBytes := by
        rw [pad, htl, Nat.sub_self, List.replicate_zero, List.append_nil]
      rw [hp, List.take_append, List.take_of_length_le (by omega), htl]
      have hrest : (m.drop chunkBytes).length ≤ t * chunkBytes := by
        rw [List.length_drop]; rw [Nat.succ_mul] at hm; omega
      have := ih (m.drop chunkBytes) hrest
      rw [List.length_drop] at this
      rw [this, List.take_append_drop]

theorem chunks_flatten_take (m : Bytes) : (chunks m).flatten.take m.length = m := by
  rw [chunks_eq_blocks]
  apply blocks_flatten_take
  simp only [chunkCount, chunkBytes]
  omega

/-! ## The lane polynomials -/

/-- The systematic points of lane `j`: chunk `t`'s element `j` at node `t`. -/
def sys (cs : List Bytes) (j : ℕ) : List (Elem × Elem) :=
  ((List.range cs.length).zip cs).map fun p => (node p.1, element p.2 j)

theorem sys_length (cs : List Bytes) (j : ℕ) : (sys cs j).length = cs.length := by
  simp [sys]

theorem sys_nodup (cs : List Bytes) (j : ℕ) (h : cs.length ≤ 65536) :
    ((sys cs j).map Prod.fst).Nodup := by
  have : (sys cs j).map Prod.fst = (List.range cs.length).map node := by
    have hz := List.map_fst_zip (l₁ := List.range cs.length) (l₂ := cs) (by simp)
    rw [← hz, List.map_map]
    simp only [sys, List.map_map]
    rfl
  rw [this]
  exact nodup_map_node List.nodup_range (fun i hi => by simp at hi; omega)

theorem sys_mem (cs : List Bytes) (j t : ℕ) (ht : t < cs.length) :
    (node t, element cs[t] j) ∈ sys cs j := by
  unfold sys
  apply List.mem_map.mpr
  refine ⟨(t, cs[t]), ?_, rfl⟩
  have hz : t < ((List.range cs.length).zip cs).length := by simp [ht]
  have := List.getElem_mem hz
  simpa [List.getElem_zip] using this

/-- Lane `j` of every codeword is the lane polynomial at the codeword's node. -/
theorem codeword_lane (cs : List Bytes) (i j : ℕ) (hcs : cs.length ≤ 65536) (hj : j < lanes) :
    element (codeword cs i) j = eval (interpP (sys cs j)) (node i) := by
  rw [eval_interpP]
  by_cases h : i < cs.length
  · rw [codeword_systematic cs i h]
    have : cs.getD i [] = cs[i] := by simp [List.getD_eq_getElem?_getD, h]
    rw [this]
    exact (interp_eq _ _ _ (sys_mem cs j i h) (sys_nodup cs j hcs)).symm
  · have : codeword cs i = ofLanes fun j => interp (sys cs j) (node i) := by
      simp [codeword, h, sys]
    rw [this, element_ofLanes _ _ hj]

/-! ## Recovery of each chunk -/

/-- The decoder holding the codewords of `cs` at `k = cs.length` distinct indices below 65536
returns chunk `t` for every `t < k`: the held codeword when `t` is held, and otherwise the
interpolant of the held lanes, which is the lane polynomial by unisolvence. -/
theorem chunk_recover (cs : List Bytes) (hc : ∀ c ∈ cs, c.length = chunkBytes)
    (hcs : cs.length ≤ 65536) (n k : ℕ)
    (idxs : List ℕ) (hnd : idxs.Nodup) (hlt : ∀ i ∈ idxs, i < 65536)
    (hlen : idxs.length = cs.length) (t : ℕ) (ht : t < cs.length) :
    Decoder.chunk ⟨n, k, idxs.map (fun i => (i, codeword cs i))⟩ t = cs[t] := by
  unfold Decoder.chunk
  split
  · rename_i h hfind
    have hmem := List.mem_of_find?_eq_some hfind
    have hp := List.find?_some hfind
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hmem
    simp only [beq_iff_eq] at hp
    subst hp
    simp [codeword_systematic _ _ ht, List.getD_eq_getElem?_getD, ht]
  · rw [← ofLanes_element cs[t] (hc _ (List.getElem_mem ht))]
    apply ofLanes_congr
    intro j hj
    have hpts : ((idxs.map (fun i => (i, codeword cs i))).map
        fun h => (node h.1, element h.2 j)) =
        idxs.map (fun i => (node i, element (codeword cs i) j)) := by
      simp [Function.comp]
    rw [hpts]
    rw [unisolvence (interpP (sys cs j)) _ (node t) ?nd ?deg ?pts, eval_interpP]
    · exact interp_eq _ _ _ (sys_mem cs j t ht) (sys_nodup cs j hcs)
    case nd =>
      rw [List.map_map]
      exact nodup_map_node hnd hlt
    case deg =>
      have := deg_interpP (sys cs j)
      rw [sys_length] at this
      simp only [List.length_map]
      omega
    case pts =>
      intro pt hpt
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp hpt
      exact codeword_lane cs i j hcs hj

/-! ## Reed-Solomon recovery -/

/-- **Reed-Solomon recovery in the model.**  The decoder of `Model.Erasure`, holding the
codewords of `m` at `chunkCount m.length` distinct indices below `65536`, in any order, returns
`m`. -/
theorem M_recover (m : List UInt8) (hk : Model.Erasure.chunkCount m.length ≤ 65536)
    (idxs : List ℕ) (hnd : idxs.Nodup) (hlt : ∀ i ∈ idxs, i < 65536)
    (hlen : idxs.length = Model.Erasure.chunkCount m.length) :
    Model.Erasure.Decoder.message
      ⟨m.length, Model.Erasure.chunkCount m.length,
        idxs.map (fun i => (i, Model.Erasure.codeword (Model.Erasure.chunks m) i))⟩ = some m := by
  have hcl : (chunks m).length = chunkCount m.length := by simp [chunks]
  unfold Decoder.message
  simp only [List.length_map, hlen, Nat.lt_irrefl, if_false]
  congr 1
  have hrec : (List.range (chunkCount m.length)).map
      (Decoder.chunk ⟨m.length, chunkCount m.length,
        idxs.map (fun i => (i, codeword (chunks m) i))⟩) = chunks m := by
    apply List.ext_getElem (by simp [hcl])
    intro t h1 h2
    rw [List.getElem_map, List.getElem_range]
    exact chunk_recover (chunks m) (chunks_length m) (by omega) _ _ idxs hnd hlt
      (by omega) t h2
  rw [hrec]
  exact chunks_flatten_take m

end Tacenta.UnitErasureRs.Recovery
