/-
Proofs.SparseReplacementBound: the sparse ratchet's total bound counts the store
a skip leaves (proof tier T2, about the model).

`sparse-pq-ratchet.md`, The store also has a total bound, states the order of a
skip from the chain's counter `c` to `upto`: refuse above `maxSkip`; delete the
keys stored for the epoch under a number `n` with `c < n ≤ upto`; refuse when
what remains plus `upto - c` passes `maxSkippedStore`; otherwise store the
derived keys after what remains. `Model.SparseRatchet.skipMessageKeys` states
it with `skipSurvivors`. This file proves what the page says of it:

* the range of the deletion: a key survives unless it is stored for the epoch at
  a number past the counter and no higher than `upto`, so a key at the counter
  itself survives and a key at `upto` does not;
* the refusal is exactly the resulting count, within the per-chain bound, and
  nothing else;
* a skip that succeeds leaves exactly the survivors followed by the derived
  keys, so its size is the resulting count, which is within the bound;
* a key outside the range is kept as it was, and no earlier key remains inside
  the range;
* the change is not vacuous: a store of `maxSkippedStore - 1` keys, two of which
  lie in the range of a skip that stores two, is accepted, where the count made
  before the deletion would refuse it.

Nothing here is a hypothesis of another theorem. The last statement exists so
that "the two counts differ" is shown for a state the model can hold, rather
than asserted.
-/
import Proofs.SparseRatchetCorrectness

namespace Proofs.SparseReplacementBound

open Model.SparseRatchet
open Model.State (Key)

/-! ## The range of the deletion -/

/-- A stored key survives a skip unless it is stored for the epoch under a number
past the chain's counter and no higher than `upto`. The lower end is strict and
the upper end is included. -/
theorem mem_skipSurvivors_iff (st : State) (e start upto : Nat) (x : Nat × Nat × Key) :
    x ∈ skipSurvivors st e start upto ↔
      x ∈ st.skipped ∧ ¬ (x.1 = e ∧ start < x.2.1 ∧ x.2.1 ≤ upto) := by
  simp only [skipSurvivors, List.mem_filter, Bool.not_eq_true', Bool.and_eq_false_iff,
    beq_eq_false_iff_ne, decide_eq_false_iff_not]
  constructor
  · rintro ⟨hx, hk⟩
    refine ⟨hx, ?_⟩
    rintro ⟨h1, h2, h3⟩
    rcases hk with hk | hk
    · rcases hk with hk | hk
      · exact hk h1
      · exact hk h2
    · exact hk h3
  · rintro ⟨hx, hk⟩
    refine ⟨hx, ?_⟩
    by_cases h1 : x.1 = e
    · by_cases h2 : start < x.2.1
      · by_cases h3 : x.2.1 ≤ upto
        · exact absurd ⟨h1, h2, h3⟩ hk
        · exact Or.inr h3
      · exact Or.inl (Or.inr h2)
    · exact Or.inl (Or.inl h1)

/-- Deleting never adds: the survivors are no more than what was stored. -/
theorem skipSurvivors_length_le (st : State) (e start upto : Nat) :
    (skipSurvivors st e start upto).length ≤ st.skipped.length := by
  unfold skipSurvivors
  exact List.length_filter_le _ _

/-! ## The refusal is the resulting count -/

/-- Within the per-chain bound, a skip that steps the chain is refused exactly
when the keys that survive the deletion, plus the keys to store, pass
`maxSkippedStore`.

`hc` and `hr` say the epoch has a chain and its receiving chain is present, `hlo`
that the request steps the chain forward, and `hhi` that it is within `maxSkip`.
The other refusals (no chain, a retired chain, too many skipped) are outside
those premises. -/
theorem skipMessageKeys_refused_iff (st : State) (e upto : Nat) (cs : Chains) (ch : Chain)
    (hc : findChains st e = some cs) (hr : cs.receive = some ch)
    (hlo : ch.n < upto) (hhi : upto ≤ ch.n + maxSkip) :
    skipMessageKeys st e upto = none ↔
      maxSkippedStore < (skipSurvivors st e ch.n upto).length + (upto - ch.n) := by
  have hnle : ¬ upto ≤ ch.n := Nat.not_le.mpr hlo
  have hnhi : ¬ upto > ch.n + maxSkip := Nat.not_lt.mpr hhi
  unfold skipMessageKeys
  rw [hc]
  simp only [hr, if_neg hnle, if_neg hnhi, gt_iff_lt]
  by_cases hbound : maxSkippedStore < (skipSurvivors st e ch.n upto).length + (upto - ch.n)
  · simp [hbound]
  · simp [hbound]

/-- A skip that steps the chain and succeeds leaves exactly the survivors
followed by the keys it derives, in number order, and so exactly the resulting
count, which is within `maxSkippedStore`. -/
theorem skipMessageKeys_leaves_survivors_then_batch (st st' : State) (e upto : Nat)
    (cs : Chains) (ch : Chain)
    (hc : findChains st e = some cs) (hr : cs.receive = some ch)
    (hlo : ch.n < upto)
    (h : skipMessageKeys st e upto = some st') :
    st'.skipped = skipSurvivors st e ch.n upto ++
        (skipMessageKeys.deriveInto ch.ck ch.n (upto - ch.n)).2.map
          (fun p => (e, p.1, p.2)) ∧
      st'.skipped.length = (skipSurvivors st e ch.n upto).length + (upto - ch.n) ∧
      st'.skipped.length ≤ maxSkippedStore := by
  have hnle : ¬ upto ≤ ch.n := Nat.not_le.mpr hlo
  unfold skipMessageKeys at h
  rw [hc] at h
  simp only [hr, if_neg hnle] at h
  by_cases hhi : upto > ch.n + maxSkip
  · simp [hhi] at h
  · by_cases hbound : (skipSurvivors st e ch.n upto).length + (upto - ch.n) > maxSkippedStore
    · simp [hhi, hbound] at h
    · simp only [hhi, hbound, if_false] at h
      injection h with h'
      subst h'
      have hs : (setChains
          { st with
            skipped := skipSurvivors st e ch.n upto ++
              (skipMessageKeys.deriveInto ch.ck ch.n (upto - ch.n)).2.map
                (fun p => (e, p.1, p.2)) }
          e { cs with receive := some { ck := (skipMessageKeys.deriveInto ch.ck ch.n (upto - ch.n)).1, n := upto } }).skipped
          = skipSurvivors st e ch.n upto ++
              (skipMessageKeys.deriveInto ch.ck ch.n (upto - ch.n)).2.map
                (fun p => (e, p.1, p.2)) := rfl
      refine ⟨hs, ?_, ?_⟩
      · rw [hs, List.length_append, List.length_map,
          Proofs.SparseRatchetCorrectness.deriveInto_length]
      · rw [hs, List.length_append, List.length_map,
          Proofs.SparseRatchetCorrectness.deriveInto_length]
        omega

/-! ## What is kept and what is replaced -/

/-- A stored key outside the replaced range is still stored, unchanged, after a
skip that steps the chain and succeeds. That covers every key of another epoch,
every key of this epoch at a number no higher than the counter, and every key of
this epoch above `upto`. -/
theorem skipMessageKeys_keeps_outside_range (st st' : State) (e upto : Nat)
    (cs : Chains) (ch : Chain)
    (hc : findChains st e = some cs) (hr : cs.receive = some ch)
    (hlo : ch.n < upto)
    (h : skipMessageKeys st e upto = some st')
    (x : Nat × Nat × Key) (hx : x ∈ st.skipped)
    (hout : ¬ (x.1 = e ∧ ch.n < x.2.1 ∧ x.2.1 ≤ upto)) :
    x ∈ st'.skipped := by
  obtain ⟨hs, -, -⟩ := skipMessageKeys_leaves_survivors_then_batch st st' e upto cs ch hc hr hlo h
  rw [hs]
  exact List.mem_append_left _ ((mem_skipSurvivors_iff st e ch.n upto x).mpr ⟨hx, hout⟩)

/-- The lower end of the range: a key stored at the chain's counter itself, which
for the chain's own epoch is the key just below the first number the skip stores,
is not replaced. It is still stored, unchanged, after the skip. -/
theorem skipMessageKeys_keeps_the_key_at_the_counter (st st' : State) (e upto : Nat)
    (cs : Chains) (ch : Chain)
    (hc : findChains st e = some cs) (hr : cs.receive = some ch)
    (hlo : ch.n < upto)
    (h : skipMessageKeys st e upto = some st')
    (x : Nat × Nat × Key) (hx : x ∈ st.skipped) (hn : x.2.1 = ch.n) :
    x ∈ st'.skipped := by
  refine skipMessageKeys_keeps_outside_range st st' e upto cs ch hc hr hlo h x hx ?_
  rintro ⟨-, hgt, -⟩
  omega

/-- No earlier key remains inside the replaced range: every key a skip leaves for
the epoch under a number past the counter and no higher than `upto` is one the
skip derived. -/
theorem skipMessageKeys_replaces_the_range (st st' : State) (e upto : Nat)
    (cs : Chains) (ch : Chain)
    (hc : findChains st e = some cs) (hr : cs.receive = some ch)
    (hlo : ch.n < upto)
    (h : skipMessageKeys st e upto = some st')
    (y : Nat × Nat × Key) (hy : y ∈ st'.skipped)
    (he : y.1 = e) (hlow : ch.n < y.2.1) (hhigh : y.2.1 ≤ upto) :
    y ∈ (skipMessageKeys.deriveInto ch.ck ch.n (upto - ch.n)).2.map
          (fun p => (e, p.1, p.2)) := by
  obtain ⟨hs, -, -⟩ := skipMessageKeys_leaves_survivors_then_batch st st' e upto cs ch hc hr hlo h
  rw [hs, List.mem_append] at hy
  rcases hy with hy | hy
  · exact absurd ⟨he, hlow, hhigh⟩ ((mem_skipSurvivors_iff st e ch.n upto y).mp hy).2
  · exact hy

/-! ## The two counts differ -/

/-- A store of `maxSkippedStore - 1` keys, two of which lie in the range of a
skip that stores two, is accepted, although the count made before the deletion,
`1999 + 2`, passes the bound. Stated for any chain key `ck`, any key `k` and any
root key and direction, so no key is evaluated.

The state is the one the vectors and the differential test build: epoch `0`, a
receiving chain at counter `0`, the held keys `(0, 1)` and `(0, 2)`, and
`maxSkippedStore - 3` further keys at numbers above `upto`. -/
theorem replacement_accepts_where_the_count_before_the_deletion_refuses
    (rk ck k : Key) (dir : Direction) :
    let st : State :=
      { rk := rk, epoch := 0
        chains := [(0, { send := none, receive := some { ck := ck, n := 0 } })]
        skipped := [(0, 1, k), (0, 2, k)] ++
          (List.range (maxSkippedStore - 3)).map fun i => (0, 5000 + i, k)
        direction := dir }
    maxSkippedStore < st.skipped.length + (2 - 0) ∧
      (skipMessageKeys st 0 2).isSome = true := by
  intro st
  have hmax : maxSkippedStore = 2000 := rfl
  have hlen : st.skipped.length = maxSkippedStore - 1 := by
    simp only [st, List.length_append, List.length_map, List.length_range,
      List.length_cons, List.length_nil, hmax]
  have hsurv : (skipSurvivors st 0 0 2).length = maxSkippedStore - 3 := by
    have hfil : skipSurvivors st 0 0 2 =
        (List.range (maxSkippedStore - 3)).map fun i => (0, 5000 + i, k) := by
      simp only [skipSurvivors, st, List.filter_append]
      have h1 : List.filter
          (fun x : Nat × Nat × Key =>
            !(x.1 == 0 && decide (0 < x.2.1) && decide (x.2.1 ≤ 2)))
          [(0, 1, k), (0, 2, k)] = [] := by
        simp
      have h2 : List.filter
          (fun x : Nat × Nat × Key =>
            !(x.1 == 0 && decide (0 < x.2.1) && decide (x.2.1 ≤ 2)))
          ((List.range (maxSkippedStore - 3)).map fun i => (0, 5000 + i, k))
          = (List.range (maxSkippedStore - 3)).map fun i => (0, 5000 + i, k) := by
        rw [List.filter_eq_self]
        intro a ha
        obtain ⟨i, -, rfl⟩ := List.mem_map.mp ha
        simp only [Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not]
        right
        omega
      rw [h1, h2, List.nil_append]
    rw [hfil, List.length_map, List.length_range]
  refine ⟨by rw [hlen, hmax]; decide, ?_⟩
  have hc : findChains st 0 = some
      { send := none, receive := some { ck := ck, n := 0 } } := by
    simp [findChains, st]
  have hnot : ¬ (maxSkippedStore < (skipSurvivors st 0 0 2).length + (2 - 0)) := by
    rw [hsurv, hmax]; decide
  have hsome : skipMessageKeys st 0 2 ≠ none := by
    intro hn
    have hiff := skipMessageKeys_refused_iff st 0 2
      { send := none, receive := some { ck := ck, n := 0 } } { ck := ck, n := 0 }
      hc rfl (by show 0 < 2; omega) (by show 2 ≤ 0 + maxSkip; simp [maxSkip, Model.State.maxSkip])
    exact hnot (hiff.mp hn)
  cases hres : skipMessageKeys st 0 2 with
  | none => exact absurd hres hsome
  | some _ => rfl

end Proofs.SparseReplacementBound

/--
info: 'Proofs.SparseReplacementBound.mem_skipSurvivors_iff' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Proofs.SparseReplacementBound.mem_skipSurvivors_iff

/--
info: 'Proofs.SparseReplacementBound.skipSurvivors_length_le' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Proofs.SparseReplacementBound.skipSurvivors_length_le

/--
info: 'Proofs.SparseReplacementBound.skipMessageKeys_refused_iff' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Proofs.SparseReplacementBound.skipMessageKeys_refused_iff

/--
info: 'Proofs.SparseReplacementBound.skipMessageKeys_leaves_survivors_then_batch' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Proofs.SparseReplacementBound.skipMessageKeys_leaves_survivors_then_batch

/--
info: 'Proofs.SparseReplacementBound.skipMessageKeys_keeps_outside_range' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Proofs.SparseReplacementBound.skipMessageKeys_keeps_outside_range

/--
info: 'Proofs.SparseReplacementBound.skipMessageKeys_keeps_the_key_at_the_counter' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Proofs.SparseReplacementBound.skipMessageKeys_keeps_the_key_at_the_counter

/--
info: 'Proofs.SparseReplacementBound.skipMessageKeys_replaces_the_range' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Proofs.SparseReplacementBound.skipMessageKeys_replaces_the_range

/--
info: 'Proofs.SparseReplacementBound.replacement_accepts_where_the_count_before_the_deletion_refuses' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Proofs.SparseReplacementBound.replacement_accepts_where_the_count_before_the_deletion_refuses

/--
info: Proofs.SparseReplacementBound.skipMessageKeys_refused_iff (st : Model.SparseRatchet.State) (e upto : Nat)
  (cs : Model.SparseRatchet.Chains) (ch : Model.SparseRatchet.Chain)
  (hc : Model.SparseRatchet.findChains st e = some cs) (hr : cs.receive = some ch) (hlo : ch.n < upto)
  (hhi : upto ≤ ch.n + Model.SparseRatchet.maxSkip) :
  Model.SparseRatchet.skipMessageKeys st e upto = none ↔
    Model.SparseRatchet.maxSkippedStore < (Model.SparseRatchet.skipSurvivors st e ch.n upto).length + (upto - ch.n)
-/
#guard_msgs in
#check Proofs.SparseReplacementBound.skipMessageKeys_refused_iff

/--
info: Proofs.SparseReplacementBound.skipMessageKeys_leaves_survivors_then_batch (st st' : Model.SparseRatchet.State)
  (e upto : Nat) (cs : Model.SparseRatchet.Chains) (ch : Model.SparseRatchet.Chain)
  (hc : Model.SparseRatchet.findChains st e = some cs) (hr : cs.receive = some ch) (hlo : ch.n < upto)
  (h : Model.SparseRatchet.skipMessageKeys st e upto = some st') :
  st'.skipped =
      Model.SparseRatchet.skipSurvivors st e ch.n upto ++
        List.map (fun p => (e, p.fst, p.snd))
          (Model.SparseRatchet.skipMessageKeys.deriveInto ch.ck ch.n (upto - ch.n)).snd ∧
    st'.skipped.length = (Model.SparseRatchet.skipSurvivors st e ch.n upto).length + (upto - ch.n) ∧
      st'.skipped.length ≤ Model.SparseRatchet.maxSkippedStore
-/
#guard_msgs in
#check Proofs.SparseReplacementBound.skipMessageKeys_leaves_survivors_then_batch

/--
info: Proofs.SparseReplacementBound.replacement_accepts_where_the_count_before_the_deletion_refuses
  (rk ck k : Model.State.Key) (dir : Model.SparseRatchet.Direction) :
  have st :=
    { rk := rk, epoch := 0, chains := [(0, { send := none, receive := some { ck := ck, n := 0 } })],
      skipped :=
        [(0, 1, k), (0, 2, k)] ++
          List.map (fun i => (0, 5000 + i, k)) (List.range (Model.SparseRatchet.maxSkippedStore - 3)),
      direction := dir };
  Model.SparseRatchet.maxSkippedStore < st.skipped.length + (2 - 0) ∧
    (Model.SparseRatchet.skipMessageKeys st 0 2).isSome = true
-/
#guard_msgs in
#check Proofs.SparseReplacementBound.replacement_accepts_where_the_count_before_the_deletion_refuses
