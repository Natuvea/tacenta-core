import Translation.SessionUnitSpqrT3
import Translation.SessionUnitSpqrT1
import Translation.UnitSatisfiabilityJoint

/-!
# The sparse ratchet's hypotheses about translated functions, from laws about opaque constants

Most boundary hypotheses of the leaf sparse ratchet's T1 and T3 theorems are statements about
opaque constants (`Vec::pop`, `Zeroizing::new`, the HKDF). Six are statements about functions the
translation defines, with a body: `SpqrT1.RemoveSkippedAtTotal`, `SpqrT1.KdfRkTotal`,
`SpqrT1.KdfCkTotal`, `SpqrT1.VecRetainTotal` (with its three loop contracts),
`SpqrT3.RemoveSkippedAtAgrees` and `SpqrT3.VecRetainAgrees`. A model of the opaque constants cannot
change what they say, and until this module the tree showed none of them holds: the witness
`Satisfiability.lean` keeps for the first and the last bridges it by `Iff.rfl` to a shape applied
to the defined function, which is satisfiable for any function and says nothing about the body, and
`VecRetainTotal` and `VecRetainAgrees` had no witness. `SpqrT3.set_chains_refines` and
`clear_old_epochs_refines` are `VecRetainAgrees` restated (each is the hypothesis applied to its
arguments), so the sparse refinements built on them, `send_refines` and `receive_refines` among
them, rested on an agreement of two translated functions with the model that nothing showed.

This module proves each of the six, by stepping through the translated code, from a small set of
laws about the opaque constants the bodies reach. The laws are `Laws`: `Vec::pop` of a non-empty
vector returns the vector without its last element (`LawPop`), `Option::as_mut` returns
(`LawAsMut`), `Vec::capacity` returns (`LawCapacity`), the `Vec` `Zeroize` implementation returns
(`LawVecZeroize`), the array `Zeroize` implementation returns (the existing hypothesis
`SpqrT1.ZeroizeTotal`), the HKDF returns for output lengths up to 8160 bytes (`LawHkdf`), and the
`Zeroizing` wrapper reads back what it wraps at 96 and 64 bytes (`LawZeroizing`).

* `defined_fields_hold`: the four T1 hypotheses follow from `Laws`.
* `defined_hyps_from_axiom_hyps`: the same, from the hypotheses the sparse theorems already take
  (`ZeroizeTotal`, `SpqrHkdfAgrees` and the two round trips) and four laws.
* `removeSkippedAtAgrees`, `vecRetainAgreesOfLaws`, `vecRetainAgrees`: the two T3 agreements, as
  statements about the translated functions for all inputs (including a chain table at the maximum
  length, duplicate epochs, and `current` at `u64::MAX`).
* `laws_jointly_satisfiable`: the laws, over arbitrary functions of the constants' types, hold of
  one assignment. Each law is tied to the statement about the real constant by `Iff.rfl`
  (`LawPop_is` and its siblings), so the build compares them.

Nothing here shows that the real standard-library and `zeroize` functions satisfy the laws. They
are assumptions about standard-library and `zeroize` operations, tested against the real
functions only by reading. `SpqrT1.ZeroizeTotal` is stronger than the crate: it quantifies over
every `Zeroize` record, so it cannot hold of a wipe that propagates a failing element
(`spqr_zeroizeTotal_conflicts`). The proofs in this module apply it at one instance only, the byte
instance on 32-byte arrays. That hypothesis is documented and unchanged here.

The proofs are generic in the platform width: they use `Usize.max >= 2^32 - 1` or split on
`Usize.bounds_eq`. The module restates the session unit's `UnitSatisfiabilityRatchet.lean` for the
standalone sparse crate (the specifications of the swap-then-pop removal helper, the loops and the
key derivations are the same proofs under the leaf's constants), and adds the value-level
specifications of the retain loops and the two agreements.
-/

open Aeneas Aeneas.Std Result ControlFlow Error
open tacenta_session_unit
open tacenta_session_unit.tacenta_spqr

noncomputable section

namespace Tacenta.SessionUnitSatisfiabilitySpqrLaws



/-- The opaque HKDF returns on every triple of slices, for an output length within RFC 5869's
bound. -/
def LawHkdf : Prop :=
  ∀ (N : Usize) (salt ikm info : Slice U8), N.val ≤ 8160 →
    ∃ r, tacenta_kdf.hkdf_sha256 N salt ikm info = ok r


/-- The `Zeroize` instance the sparse ratchet passes to `Zeroizing` for an `N`-byte array. -/
abbrev arrInst (N : Usize) : zeroize.Zeroize (Array U8 N) :=
  Array.Insts.ZeroizeZeroize N (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)


/-- Wrapping an `N`-byte array in `Zeroizing` returns a wrapper that reads back to it. -/
def LawZeroizing (N : Usize) : Prop :=
  ∀ z : Array U8 N, ∃ w, zeroize.Zeroizing.new (arrInst N) z = ok w ∧
    zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref (arrInst N) w = ok z


theorem protocol_info_len : (tacenta_session_unit.tacenta_spqr.PROTOCOL_INFO : Slice U8).length = 12 := by
  simp only [global_simps, Array.length_to_slice]; scalar_tac


theorem chain_start_len : (tacenta_session_unit.tacenta_spqr.CHAIN_START_LABEL : Slice U8).length = 11 := by
  simp only [global_simps, Array.length_to_slice]; scalar_tac


theorem root_label_len : (tacenta_session_unit.tacenta_spqr.ROOT_LABEL : Slice U8).length = 4 := by
  simp only [global_simps, Array.length_to_slice]; scalar_tac


theorem chain_label_len : (tacenta_session_unit.tacenta_spqr.CHAIN_LABEL : Slice U8).length = 5 := by
  simp only [global_simps, Array.length_to_slice]; scalar_tac


theorem extend_from_slice_spec (v : alloc.vec.Vec U8) (s : Slice U8)
    (h : v.val.length + s.val.length ≤ Usize.max) :
    alloc.vec.Vec.extend_from_slice core.clone.CloneU8 v s ⦃ fun r =>
      r.val = v.val ++ s.val ⦄ := by
  unfold alloc.vec.Vec.extend_from_slice
  have hclone : ∀ x ∈ s.val, (core.clone.CloneU8.clone) x = ok x := by
    intro x _; rfl
  obtain ⟨s', hs'eq, hs'val⟩ := Std.WP.spec_imp_exists (Slice.clone_spec hclone)
  rw [← hs'val] at hs'eq
  have h' : v.length + s.length ≤ Usize.max := h
  rw [dif_pos h']
  split
  · rename_i s'' heq
    rw [hs'eq] at heq
    injection heq with heq
    subst heq
    rw [Std.WP.spec_ok]
  · rename_i e heq
    rw [hs'eq] at heq
    exact absurd heq (by simp)
  · rename_i heq
    rw [hs'eq] at heq
    exact absurd heq (by simp)


attribute [local step] extend_from_slice_spec


theorem info_spec (suffix : Slice U8) (h : suffix.length + 12 ≤ Usize.max) :
    tacenta_session_unit.tacenta_spqr.info suffix ⦃ fun _ => True ⦄ := by
  unfold tacenta_session_unit.tacenta_spqr.info
  have hpi := protocol_info_len
  step*
  all_goals (try (simp_all [alloc.vec.Vec.with_capacity, alloc.vec.Vec.new]))
  all_goals (try scalar_tac)



/-- Existence from a `WP` spec. -/
private theorem ex_of_spec {α : Type} {x : Result α} {p : α → Prop} (h : x ⦃ p ⦄) : ∃ r, x = ok r := by
  obtain ⟨r, hr, _⟩ := Std.WP.spec_imp_exists h
  exact ⟨r, hr⟩


theorem hkdf_step (hH : LawHkdf) (N : Usize) (salt ikm info : Slice U8) (hN : N.val ≤ 8160) :
    tacenta_kdf.hkdf_sha256 N salt ikm info ⦃ fun _ => True ⦄ := by
  obtain ⟨r, hr⟩ := hH N salt ikm info hN
  simp [hr]


theorem zeroizing_new_step (N : Usize) (hZ : LawZeroizing N) (z : Array U8 N) :
    zeroize.Zeroizing.new (arrInst N) z ⦃ fun w =>
      zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref (arrInst N) w = ok z ⦄ := by
  obtain ⟨w, hw, hd⟩ := hZ z
  simp [hw, hd]


theorem split3_spec (out : Array U8 96#usize) : tacenta_session_unit.tacenta_spqr.split3 out ⦃ fun _ => True ⦄ := by
  unfold tacenta_session_unit.tacenta_spqr.split3
  step*
  all_goals (try simp_all [Slice.length, Array.repeat, List.slice])



/-- `KdfRkTotal`, proved from the HKDF law and the wrapper law at 96 bytes. -/
theorem kdfRkTotal (hH : LawHkdf) (hZ : LawZeroizing 96#usize) :
    Tacenta.SessionUnitSpqrT1.KdfRkTotal := by
  intro rk k
  apply ex_of_spec (p := fun _ => True)
  unfold tacenta_session_unit.tacenta_spqr.kdf_rk
  have h4 : (tacenta_session_unit.tacenta_spqr.ROOT_LABEL : Slice U8).length + 12 ≤ Usize.max := by
    rw [root_label_len]; scalar_tac
  step
  step
  step with info_spec _ h4
  step with hkdf_step hH 96#usize _ _ _ (by scalar_tac)
  step with zeroizing_new_step _ hZ as ⟨out, hout⟩
  rw [hout]
  simp only [bind_tc_ok]
  step with split3_spec


/-- `KdfCkTotal`, proved from the HKDF law and the wrapper law at 64 bytes. -/
theorem kdfCkTotal (hH : LawHkdf) (hZ : LawZeroizing 64#usize) :
    Tacenta.SessionUnitSpqrT1.KdfCkTotal := by
  intro ck n
  apply ex_of_spec (p := fun _ => True)
  unfold tacenta_session_unit.tacenta_spqr.kdf_ck tacenta_session_unit.tacenta_spqr.be64
  have h4 : (tacenta_session_unit.tacenta_spqr.CHAIN_LABEL : Slice U8).length + 12 ≤ Usize.max := by
    rw [chain_label_len]; scalar_tac
  step
  step
  step with info_spec _ h4
  step with hkdf_step hH 64#usize _ _ _ (by scalar_tac)
  step with zeroizing_new_step _ hZ as ⟨out, hout⟩
  step
  rw [hout]
  simp only [bind_tc_ok]
  step*
  all_goals (try simp_all [Slice.length, Array.repeat, List.slice])



/-- The body of the "bubble the element to the end" loop that `remove_skipped_at` and
`remove_chains_at` share, at a generic element type. -/
def rotBody {T : Type} (skipped : alloc.vec.Vec T) (i : Usize) :
    Result (ControlFlow ((alloc.vec.Vec T) × Usize) ((alloc.vec.Vec T) × Usize)) := do
  let i1 ← i + 1#usize
  let i2 := alloc.vec.Vec.len skipped
  if i1 < i2 then
    let (s, deref_mut_back) ← lift (alloc.vec.Vec.deref_mut skipped)
    let s1 ← core.slice.Slice.swap s i i1
    let skipped1 := deref_mut_back s1
    ok (cont (skipped1, i1))
  else ok (done (skipped, i))


def rotLoop {T : Type} (skipped : alloc.vec.Vec T) (i : Usize) :
    Result ((alloc.vec.Vec T) × Usize) := do
  loop (fun (skipped1, i1) => rotBody skipped1 i1) (skipped, i)


theorem spqr_loop_eq : @tacenta_session_unit.tacenta_spqr.State.remove_skipped_at_loop = @rotLoop tacenta_session_unit.tacenta_spqr.Skipped := rfl

theorem chains_loop_eq :
    @tacenta_session_unit.tacenta_spqr.State.remove_chains_at_loop = @rotLoop (U64 × tacenta_session_unit.tacenta_spqr.Chains) := rfl



/-- Swapping the two adjacent cells `|P|` and `|P|+1` of `P ++ x :: q :: Q'`. -/
theorem swap_adjacent {T : Type} [Inhabited T] (P Q' : List T) (x q : T) (s' : List T)
    (hlen : s'.length = (P ++ x :: q :: Q').length)
    (ha : s'[P.length]! = q) (hb : s'[P.length + 1]! = x)
    (hrest : ∀ k, k ≠ P.length → k ≠ P.length + 1 → s'[k]! = (P ++ x :: q :: Q')[k]!) :
    s' = P ++ q :: x :: Q' := by
  apply List.ext_getElem
  · simpa using hlen
  · intro k h1 h2
    have h1' : k < s'.length := h1
    by_cases hk0 : k = P.length
    · subst hk0
      rw [← getElem!_pos s' _ h1', ha]
      simp
    · by_cases hk1 : k = P.length + 1
      · subst hk1
        rw [← getElem!_pos s' _ h1', hb]
        simp
      · have := hrest k hk0 hk1
        have h3 : k < (P ++ x :: q :: Q').length := by simpa using h2
        rw [← getElem!_pos s' k h1', this, getElem!_pos (P ++ x :: q :: Q') k h3]
        rcases Nat.lt_or_ge k P.length with hlt | hge
        · rw [List.getElem_append_left hlt, List.getElem_append_left hlt]
        · have hk2 : P.length + 2 ≤ k := by omega
          obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk2
          rw [List.getElem_append_right (by omega), List.getElem_append_right (by omega)]
          have e : P.length + 2 + m - P.length = m + 2 := by omega
          simp only [e]
          simp



theorem rotLoop_spec_aux {T : Type} [Inhabited T] (v : alloc.vec.Vec T) (i0 : Usize)
    (hi0 : i0.val < v.val.length) :
    rotLoop v i0 ⦃ fun r =>
      r.1.val = v.val.eraseIdx i0.val ++ [v.val[i0.val]'hi0] ∧ r.2.val = v.val.length - 1 ⦄ := by
  unfold rotLoop
  apply loop.spec_decr_nat
    (measure := fun p => v.val.length - p.2.val)
    (inv := fun p => ∃ P Q : List T,
      p.1.val = P ++ v.val[i0.val]'hi0 :: Q ∧ P ++ Q = v.val.eraseIdx i0.val ∧
        P.length = p.2.val)
  · rintro ⟨w, j⟩ ⟨P, Q, hw, hPQ, hPl⟩
    simp only at hw hPl
    simp only [rotBody]
    have hL : v.val.length = P.length + 1 + Q.length := by
      have h1 : (v.val.eraseIdx i0.val).length = v.val.length - 1 := by
        simp [List.length_eraseIdx, hi0]
      have h2 : (P ++ Q).length = P.length + Q.length := by simp
      rw [hPQ] at h2
      omega
    have hwl : w.val.length = v.val.length := by rw [hw]; simp only [List.length_append, List.length_cons]; omega
    have hjlt : j.val < v.val.length := by omega
    have hmax : v.val.length ≤ Usize.max := v.property
    step as ⟨i1, hi1⟩
    split
    · rename_i hlt
      have hlen : i1.val < w.val.length := by
        have : w.len.val = w.val.length := alloc.vec.Vec.len_val w
        scalar_tac
      obtain ⟨q, Q', rfl⟩ : ∃ q Q', Q = q :: Q' := by
        cases Q with
        | nil => exfalso; simp at hL; omega
        | cons q Q' => exact ⟨q, Q', rfl⟩
      simp only [lift, bind_tc_ok]
      obtain ⟨s0, back, hdm⟩ : ∃ s0 back, alloc.vec.Vec.deref_mut w = (s0, back) := ⟨_, _, rfl⟩
      have hs0 : s0.val = w.val := by
        rw [show s0 = (alloc.vec.Vec.deref_mut w).1 by rw [hdm]]; rfl
      have hback : ∀ s, (back s).val = s.val := by
        intro s; rw [show back = (alloc.vec.Vec.deref_mut w).2 by rw [hdm]]; rfl
      simp only [hdm]
      have hjs : j.val < s0.length := by simp [Slice.length, hs0]; omega
      have his : i1.val < s0.length := by simp [Slice.length, hs0]; omega
      step with core.slice.Slice.swap_spec s0 j i1 hjs his as ⟨s1, hs1a, hs1b, hs1c, hs1d⟩
      have hjP : j.val = P.length := hPl.symm
      have e1 : i1.val = P.length + 1 := by omega
      have hs0w : s0.val = P ++ (v.val[i0.val]'hi0) :: q :: Q' := by rw [hs0, hw]
      have hswap : s1.val = P ++ q :: (v.val[i0.val]'hi0) :: Q' := by
        apply swap_adjacent P Q' (v.val[i0.val]'hi0) q s1.val
        · have := hs1a
          simp only [Slice.length] at this
          rw [this, hs0w]
        · have h2 : (P ++ (v.val[i0.val]'hi0) :: q :: Q')[P.length + 1]! = q := by
            rw [getElem!_pos _ _ (by simp)]; simp
          simpa [hjP, e1, hs0w, h2] using hs1b
        · have h2 : (P ++ (v.val[i0.val]'hi0) :: q :: Q')[P.length]! = (v.val[i0.val]'hi0) := by
            rw [getElem!_pos _ _ (by simp)]; simp
          simpa [hjP, e1, hs0w, h2] using hs1c
        · intro k hk0 hk1
          have h := hs1d k (by omega) (by omega)
          exact h.trans (congrArg (fun l => l[k]!) hs0w)
      refine ⟨⟨P ++ [q], Q', ?_, ?_, ?_⟩, ?_⟩
      · rw [hback, hswap]; simp
      · rw [← hPQ]; simp
      · simp; omega
      · omega
    · rename_i hge
      have hlen : ¬ (i1.val < w.val.length) := by
        have : w.len.val = w.val.length := alloc.vec.Vec.len_val w
        scalar_tac
      have hQ : Q = [] := by
        cases Q with
        | nil => rfl
        | cons q Q' => exfalso; simp at hL; omega
      subst hQ
      refine ⟨?_, ?_⟩
      · rw [hw, ← hPQ]; simp
      · show j.val = v.val.length - 1
        simp at hL; omega
  · refine ⟨v.val.take i0.val, v.val.drop (i0.val + 1), ?_, ?_, ?_⟩
    · show v.val = _
      rw [List.getElem_cons_drop]; simp
    · rw [List.eraseIdx_eq_take_drop_succ]
    · simp; omega



theorem rotLoop_spec {T : Type} (v : alloc.vec.Vec T) (i0 : Usize) (hi0 : i0.val < v.val.length) :
    rotLoop v i0 ⦃ fun r =>
      r.1.val = v.val.eraseIdx i0.val ++ [v.val[i0.val]'hi0] ∧ r.2.val = v.val.length - 1 ⦄ := by
  haveI : Inhabited T := Classical.inhabited_of_nonempty ⟨v.val[i0.val]'hi0⟩
  exact rotLoop_spec_aux v i0 hi0




/-- **`LawPop`.**  `Vec::pop` on a non-empty vector returns the vector without its last element.
This is all the defined-function hypotheses need of `pop`; the real operation also returns the
element and handles the empty vector. No theorem hypothesis states this law. -/
def LawPop : Prop :=
  ∀ (T : Type) (v : alloc.vec.Vec T), v.val ≠ [] →
    ∃ o w, alloc.vec.Vec.pop Global v = ok (o, w) ∧ w.val = v.val.dropLast


theorem skipped_zeroize_spec (hZ : Tacenta.SessionUnitSpqrT1.ZeroizeTotal) (s : tacenta_session_unit.tacenta_spqr.Skipped) :
    tacenta_session_unit.tacenta_spqr.Skipped.Insts.ZeroizeZeroize.zeroize s ⦃ fun r => r.epoch = s.epoch ∧ r.n = s.n ⦄ := by
  unfold tacenta_session_unit.tacenta_spqr.Skipped.Insts.ZeroizeZeroize.zeroize
  obtain ⟨r, hr⟩ := hZ (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes) s.key
  simp [hr]


/-- The sparse ratchet's `remove_skipped_at`, at an in-range index: returns the key at that index
and the vector with that index erased. -/
theorem spqr_remove_skipped_at_spec (hZ : Tacenta.SessionUnitSpqrT1.ZeroizeTotal) (hP : LawPop)
    (v : alloc.vec.Vec tacenta_session_unit.tacenta_spqr.Skipped) (i : Usize) (hi : i.val < v.val.length) :
    tacenta_session_unit.tacenta_spqr.State.remove_skipped_at v i ⦃ fun r =>
      r.1 = (v.val[i.val]'hi).key ∧ r.2.val = v.val.eraseIdx i.val ⦄ := by
  unfold tacenta_session_unit.tacenta_spqr.State.remove_skipped_at
  rw [spqr_loop_eq]
  step with rotLoop_spec v i hi as ⟨v1, i1, hv1, hi1⟩
  have hL : (v.val.eraseIdx i.val).length = v.val.length - 1 := by
    simp [List.length_eraseIdx, hi]
  have hlen1 : v1.val.length = v.val.length := by
    rw [hv1]; simp; omega
  have hb : i1.val < v1.val.length := by omega
  have hget : v1.val[i1.val]'hb = v.val[i.val]'hi := by
    simp only [hv1]
    rw [List.getElem_append_right (by omega)]
    simp [hi1, hL]
  step with alloc.vec.Vec.index_usize_spec v1 i1 hb as ⟨x, hx⟩
  step with alloc.vec.Vec.index_mut_usize_spec v1 i1 hb as ⟨x', back, hx', hback⟩
  step with skipped_zeroize_spec hZ as ⟨s2, hs2⟩
  have hne : (back s2).val ≠ [] := by
    intro h
    have h0 : (back s2).val.length = 0 := by rw [h]; rfl
    rw [hback, alloc.vec.Vec.set_val_eq, List.length_set] at h0
    omega
  obtain ⟨o, w, hw1, hw2⟩ := hP _ (back s2) hne
  rw [hw1]
  simp only [bind_tc_ok]
  refine ⟨by rw [hx, hget], ?_⟩
  rw [hw2, hback]
  simp only [alloc.vec.Vec.set_val_eq, hv1]
  have : i1.val = (v.val.eraseIdx i.val).length := by rw [hi1, hL]
  rw [this, List.set_append_right _ _ (by omega)]
  simp



/-- `SpqrT1.RemoveSkippedAtTotal`, from the pop law and the array zeroize law. -/
theorem spqrRemoveSkippedAtTotal (hZ : Tacenta.SessionUnitSpqrT1.ZeroizeTotal) (hP : LawPop) :
    Tacenta.SessionUnitSpqrT1.RemoveSkippedAtTotal := by
  intro v i hi
  obtain ⟨r, hr, -, hv⟩ := Std.WP.spec_imp_exists (spqr_remove_skipped_at_spec hZ hP v i hi)
  refine ⟨r, hr, ?_⟩
  rw [hv]
  simp [List.length_eraseIdx, hi]
  omega


/-- **`LawAsMut`.**  `Option::as_mut` returns. No theorem hypothesis states it. -/
def LawAsMut : Prop :=
  ∀ (T : Type) (o : Option T), ∃ r, core.option.Option.as_mut o = ok r


theorem chain_zeroize_spec (hZ : Tacenta.SessionUnitSpqrT1.ZeroizeTotal) (c : tacenta_session_unit.tacenta_spqr.Chain) :
    tacenta_session_unit.tacenta_spqr.Chain.Insts.ZeroizeZeroize.zeroize c ⦃ fun _ => True ⦄ := by
  unfold tacenta_session_unit.tacenta_spqr.Chain.Insts.ZeroizeZeroize.zeroize
  obtain ⟨r, hr⟩ := hZ (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes) c.ck
  simp [hr]


theorem as_mut_step (hA : LawAsMut) {T : Type} (o : Option T) :
    core.option.Option.as_mut o ⦃ fun _ => True ⦄ := by
  obtain ⟨r, hr⟩ := hA T o
  simp [hr]


theorem chains_zeroize_spec (hZ : Tacenta.SessionUnitSpqrT1.ZeroizeTotal) (hA : LawAsMut)
    (c : tacenta_session_unit.tacenta_spqr.Chains) :
    tacenta_session_unit.tacenta_spqr.Chains.Insts.ZeroizeZeroize.zeroize c ⦃ fun _ => True ⦄ := by
  unfold tacenta_session_unit.tacenta_spqr.Chains.Insts.ZeroizeZeroize.zeroize
  step with as_mut_step hA as ⟨o, back⟩
  rcases o with _ | ch
  · simp only [bind_tc_ok]
    step with as_mut_step hA as ⟨o2, back2⟩
    rcases o2 with _ | ch2
    · simp
    · step with chain_zeroize_spec hZ
  · simp only []
    step with chain_zeroize_spec hZ
    step with as_mut_step hA as ⟨o2, back2⟩
    rcases o2 with _ | ch2
    · simp
    · step with chain_zeroize_spec hZ


theorem set_last {α : Type} (e : List α) (z y : α) : (e ++ [z]).set e.length y = e ++ [y] := by
  rw [List.set_append_right _ _ (by omega)]
  simp



/-- `remove_chains_at` at an in-range index returns the table with that entry erased. -/
theorem remove_chains_at_spec (hZ : Tacenta.SessionUnitSpqrT1.ZeroizeTotal) (hA : LawAsMut)
    (hP : LawPop)
    (v : alloc.vec.Vec (U64 × tacenta_session_unit.tacenta_spqr.Chains)) (i : Usize) (hi : i.val < v.val.length) :
    tacenta_session_unit.tacenta_spqr.State.remove_chains_at v i ⦃ fun r => r.val = v.val.eraseIdx i.val ⦄ := by
  unfold tacenta_session_unit.tacenta_spqr.State.remove_chains_at
  rw [chains_loop_eq]
  step with rotLoop_spec v i hi as ⟨v1, i1, hv1, hi1⟩
  have hL : (v.val.eraseIdx i.val).length = v.val.length - 1 := by
    simp [List.length_eraseIdx, hi]
  have hlen1 : v1.val.length = v.val.length := by
    rw [hv1]; simp; omega
  have hb : i1.val < v1.val.length := by omega
  have hi1e : i1.val = (v.val.eraseIdx i.val).length := by rw [hi1, hL]
  step with alloc.vec.Vec.index_mut_usize_spec v1 i1 hb as ⟨a, c, back, hx', hback⟩
  step with chains_zeroize_spec hZ hA as ⟨c1⟩
  have h2 : (back (a, c1)).val = v.val.eraseIdx i.val ++ [(a, c1)] := by
    rw [hback, alloc.vec.Vec.set_val_eq, hv1, hi1e]; exact set_last _ _ _
  have hb2 : i1.val < (back (a, c1)).val.length := by rw [h2]; simp; omega
  step with alloc.vec.Vec.index_mut_usize_spec (back (a, c1)) i1 hb2 as ⟨a2, c2, back2, hx2, hback2⟩
  have h3 : (back2 (a2, { send := none, receive := c2.receive })).val
      = v.val.eraseIdx i.val ++ [(a2, { send := none, receive := c2.receive })] := by
    rw [hback2, alloc.vec.Vec.set_val_eq, h2, hi1e]; exact set_last _ _ _
  have hb3 : i1.val < (back2 (a2, { send := none, receive := c2.receive })).val.length := by
    rw [h3]; simp; omega
  step with alloc.vec.Vec.index_mut_usize_spec (back2 (a2, { send := none, receive := c2.receive })) i1 hb3
    as ⟨a3, c3, back3, hx3, hback3⟩
  have h4 : (back3 (a3, { send := c3.send, receive := none })).val
      = v.val.eraseIdx i.val ++ [(a3, { send := c3.send, receive := none })] := by
    rw [hback3, alloc.vec.Vec.set_val_eq, h3, hi1e]; exact set_last _ _ _
  have hne : (back3 (a3, { send := c3.send, receive := none })).val ≠ [] := by
    rw [h4]; simp
  obtain ⟨o, w, hw1, hw2⟩ := hP _ (back3 (a3, { send := c3.send, receive := none })) hne
  rw [hw1]
  simp only [bind_tc_ok]
  show w.val = _
  rw [hw2, h4]
  simp



theorem set_chains_loop_spec (hZ : Tacenta.SessionUnitSpqrT1.ZeroizeTotal) (hA : LawAsMut)
    (hP : LawPop) (st : tacenta_session_unit.tacenta_spqr.State) (e : U64) (i : Usize) :
    tacenta_session_unit.tacenta_spqr.State.set_chains_loop st e i ⦃ fun r =>
      r.2.2.1.length ≤ st.chains.length ∧ r.2.2.2.1 = st.skipped ⦄ := by
  unfold tacenta_session_unit.tacenta_spqr.State.set_chains_loop
  apply loop.spec_decr_nat
    (measure := fun p => p.1.chains.length - p.2.val)
    (inv := fun p => p.1.skipped = st.skipped ∧ p.1.chains.length ≤ st.chains.length)
  · rintro ⟨self, j⟩ ⟨hsk, hlen⟩
    simp only at hsk hlen
    simp only [tacenta_session_unit.tacenta_spqr.State.set_chains_loop.body]
    by_cases hj : j.val < self.chains.length
    · have hjl : j < alloc.vec.Vec.len self.chains := by
        have := alloc.vec.Vec.len_val self.chains
        scalar_tac
      rw [if_pos hjl]
      step with alloc.vec.Vec.index_usize_spec self.chains j hj as ⟨pr, hpr⟩
      split
      · step with remove_chains_at_spec hZ hA hP self.chains j hj as ⟨v, hv⟩
        have hvl : v.length = self.chains.length - 1 := by
          have h1 : v.val.length = (self.chains.val.eraseIdx j.val).length := by rw [hv]
          rw [List.length_eraseIdx] at h1
          have h2 : j.val < self.chains.val.length := hj
          simp only [h2, if_true] at h1
          exact h1
        refine ⟨hsk, ?_, ?_⟩
        · omega
        · omega
      · have hmax : self.chains.length ≤ Usize.max := self.chains.property
        step as ⟨i3, hi3⟩
        refine ⟨hsk, hlen, ?_⟩
        omega
    · have hjl : ¬ (j < alloc.vec.Vec.len self.chains) := by
        have := alloc.vec.Vec.len_val self.chains
        scalar_tac
      rw [if_neg hjl]
      simp only [WP.spec_ok]
      exact ⟨hlen, hsk⟩
  · exact ⟨rfl, le_refl _⟩



theorem clear_chains_loop0_spec (hZ : Tacenta.SessionUnitSpqrT1.ZeroizeTotal) (hA : LawAsMut)
    (hP : LawPop) (st : tacenta_session_unit.tacenta_spqr.State) (current : U64) (i : Usize) :
    tacenta_session_unit.tacenta_spqr.State.clear_old_epochs_loop0 st current i ⦃ fun r =>
      r.2.2.1.length ≤ st.chains.length ∧ r.2.2.2.1 = st.skipped ⦄ := by
  unfold tacenta_session_unit.tacenta_spqr.State.clear_old_epochs_loop0
  apply loop.spec_decr_nat
    (measure := fun p => p.1.chains.length - p.2.val)
    (inv := fun p => p.1.skipped = st.skipped ∧ p.1.chains.length ≤ st.chains.length)
  · rintro ⟨self, j⟩ ⟨hsk, hlen⟩
    simp only at hsk hlen
    simp only [tacenta_session_unit.tacenta_spqr.State.clear_old_epochs_loop0.body]
    by_cases hj : j.val < self.chains.length
    · have hjl : j < alloc.vec.Vec.len self.chains := by
        have := alloc.vec.Vec.len_val self.chains
        scalar_tac
      rw [if_pos hjl]
      step with alloc.vec.Vec.index_usize_spec self.chains j hj as ⟨pr, hpr⟩
      simp only [lift, bind_tc_ok]
      split
      · have hmax : self.chains.length ≤ Usize.max := self.chains.property
        step as ⟨i4, hi4⟩
        refine ⟨hsk, hlen, ?_⟩
        omega
      · step with remove_chains_at_spec hZ hA hP self.chains j hj as ⟨v, hv⟩
        have hvl : v.length = self.chains.length - 1 := by
          have h1 : v.val.length = (self.chains.val.eraseIdx j.val).length := by rw [hv]
          rw [List.length_eraseIdx] at h1
          have h2 : j.val < self.chains.val.length := hj
          simp only [h2, if_true] at h1
          exact h1
        refine ⟨hsk, ?_, ?_⟩
        · omega
        · omega
    · have hjl : ¬ (j < alloc.vec.Vec.len self.chains) := by
        have := alloc.vec.Vec.len_val self.chains
        scalar_tac
      rw [if_neg hjl]
      exact ⟨hlen, hsk⟩
  · exact ⟨rfl, le_refl _⟩



theorem array_zeroize_step (hZ : Tacenta.SessionUnitSpqrT1.ZeroizeTotal) (a : Array U8 32#usize) :
    Array.Insts.ZeroizeZeroize.zeroize
      (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes) a ⦃ fun _ => True ⦄ := by
  obtain ⟨r, hr⟩ := hZ (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes) a
  simp [hr]


theorem clear_skipped_loop1_spec (hZ : Tacenta.SessionUnitSpqrT1.ZeroizeTotal)
    (hP : LawPop) (v0 : alloc.vec.Vec tacenta_session_unit.tacenta_spqr.Skipped) (current : U64) (i : Usize) :
    tacenta_session_unit.tacenta_spqr.State.clear_old_epochs_loop1 v0 current i ⦃ fun r =>
      r.length ≤ v0.length ⦄ := by
  unfold tacenta_session_unit.tacenta_spqr.State.clear_old_epochs_loop1
  apply loop.spec_decr_nat
    (measure := fun p => p.1.length - p.2.val)
    (inv := fun p => p.1.length ≤ v0.length)
  · rintro ⟨v, j⟩ hinv
    simp only at hinv
    simp only [tacenta_session_unit.tacenta_spqr.State.clear_old_epochs_loop1.body]
    by_cases hj : j.val < v.length
    · have hjl : j < alloc.vec.Vec.len v := by
        have := alloc.vec.Vec.len_val v
        scalar_tac
      rw [if_pos hjl]
      step with alloc.vec.Vec.index_usize_spec v j hj as ⟨pr, hpr⟩
      simp only [lift, bind_tc_ok]
      split
      · have hmax : v.length ≤ Usize.max := v.property
        step as ⟨j1, hj1⟩
        refine ⟨hinv, ?_⟩
        omega
      · step with spqr_remove_skipped_at_spec hZ hP v j hj as ⟨d, v1, hd, hv1⟩
        step with array_zeroize_step hZ
        have hvl : v1.length = v.length - 1 := by
          have h1 : v1.val.length = (v.val.eraseIdx j.val).length := by rw [hv1]
          rw [List.length_eraseIdx] at h1
          have h2 : j.val < v.val.length := hj
          simp only [h2, if_true] at h1
          exact h1
        refine ⟨?_, ?_⟩
        · omega
        · omega
    · have hjl : ¬ (j < alloc.vec.Vec.len v) := by
        have := alloc.vec.Vec.len_val v
        scalar_tac
      rw [if_neg hjl]
      exact hinv
  · exact le_refl _



theorem setChainsLoopTotal (hZ : Tacenta.SessionUnitSpqrT1.ZeroizeTotal) (hA : LawAsMut)
    (hP : LawPop) : Tacenta.SessionUnitSpqrT1.SetChainsLoopTotal := by
  intro st e i _
  obtain ⟨r, hr, h⟩ := Std.WP.spec_imp_exists (set_chains_loop_spec hZ hA hP st e i)
  obtain ⟨a, b, c, d, f⟩ := r
  exact ⟨_, hr, h⟩


theorem clearChainsLoop0Total (hZ : Tacenta.SessionUnitSpqrT1.ZeroizeTotal) (hA : LawAsMut)
    (hP : LawPop) : Tacenta.SessionUnitSpqrT1.ClearChainsLoop0Total := by
  intro st current i _
  obtain ⟨r, hr, h⟩ := Std.WP.spec_imp_exists (clear_chains_loop0_spec hZ hA hP st current i)
  obtain ⟨a, b, c, d, f⟩ := r
  exact ⟨_, hr, h⟩


theorem clearSkippedLoopTotal (hZ : Tacenta.SessionUnitSpqrT1.ZeroizeTotal)
    (hP : LawPop) : Tacenta.SessionUnitSpqrT1.ClearSkippedLoopTotal := by
  intro v current i _
  obtain ⟨r, hr, h⟩ := Std.WP.spec_imp_exists (clear_skipped_loop1_spec hZ hP v current i)
  exact ⟨r, hr, h⟩


/-- `Vec::capacity` returns.  The first conjunct of `VecRetainTotal`. -/
def LawCapacity : Prop :=
  ∀ {T : Type} (A : Type) (v : alloc.vec.Vec T), ∃ r, alloc.vec.Vec.capacity A v = ok r


/-- The `Zeroize` implementation for `Vec` returns, for every instance record. The second conjunct of
`VecRetainTotal`. It is stronger than the crate: the real `Vec::zeroize` zeroizes each element and
propagates a failure, so no such function satisfies it for a failing record (`vec_zeroize_conflicts`), as
for the array wipe. The crate calls it only at the instances for `(u64, Chains)` and `Skipped`, whose
element wipes return. It is documented and unchanged here. -/
def LawVecZeroize : Prop :=
  ∀ {T : Type} (inst : zeroize.Zeroize T) (v : alloc.vec.Vec T),
    ∃ r, alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize inst v = ok r


theorem vecRetainTotal (hCap : LawCapacity) (hVZ : LawVecZeroize)
    (hZ : Tacenta.SessionUnitSpqrT1.ZeroizeTotal) (hA : LawAsMut) (hP : LawPop) :
    Tacenta.SessionUnitSpqrT1.VecRetainTotal :=
  ⟨hCap, hVZ, setChainsLoopTotal hZ hA hP, clearChainsLoop0Total hZ hA hP,
    clearSkippedLoopTotal hZ hP⟩



/-- The laws, on the leaf crate's opaque constants, that make its defined-function hypotheses true. -/
structure Laws : Prop where
  pop : LawPop
  asMut : LawAsMut
  capacity : LawCapacity
  vecZeroize : LawVecZeroize
  arrayZeroize : Tacenta.SessionUnitSpqrT1.ZeroizeTotal
  hkdf : LawHkdf
  zeroizing96 : LawZeroizing 96#usize
  zeroizing64 : LawZeroizing 64#usize

theorem defined_fields_hold (L : Laws) :
    Tacenta.SessionUnitSpqrT1.RemoveSkippedAtTotal ∧
    Tacenta.SessionUnitSpqrT1.KdfRkTotal ∧
    Tacenta.SessionUnitSpqrT1.KdfCkTotal ∧
    Tacenta.SessionUnitSpqrT1.VecRetainTotal :=
  ⟨spqrRemoveSkippedAtTotal L.arrayZeroize L.pop,
   kdfRkTotal L.hkdf L.zeroizing96,
   kdfCkTotal L.hkdf L.zeroizing64,
   vecRetainTotal L.capacity L.vecZeroize L.arrayZeroize L.asMut L.pop⟩


/-! ## Value-level specs for the retain loops

The totality specs above prove only a length bound.  The statements below pin the value: each loop
removes exactly the entries its guard names, keeps the order of the rest, and leaves the other four
fields of the state alone. -/

theorem keep_step {α : Type} (l : List α) (j : Nat) (hj : j < l.length) (P : α → Bool)
    (hP : P (l[j]'hj) = true) :
    l.take (j + 1) ++ (l.drop (j + 1)).filter P = l.take j ++ (l.drop j).filter P := by
  rw [List.drop_eq_getElem_cons hj, List.filter_cons_of_pos hP, List.take_add_one,
    List.getElem?_eq_getElem hj]
  simp only [Option.toList_some, List.append_assoc, List.singleton_append]


theorem remove_step {α : Type} (l : List α) (j : Nat) (hj : j < l.length) (P : α → Bool)
    (hP : P (l[j]'hj) = false) :
    (l.eraseIdx j).take j ++ ((l.eraseIdx j).drop j).filter P
      = l.take j ++ (l.drop j).filter P := by
  rw [List.eraseIdx_eq_take_drop_succ, List.drop_eq_getElem_cons hj,
    List.filter_cons_of_neg (by simp [hP])]
  have h1 : (l.take j).length = j := by simp; omega
  rw [List.take_append_of_le_length (by omega), List.drop_append_of_le_length (by omega)]
  simp


theorem finish_step {α : Type} (l : List α) (j : Nat) (hj : l.length ≤ j) (P : α → Bool) :
    l.take j ++ (l.drop j).filter P = l := by
  rw [List.take_of_length_le hj, List.drop_of_length_le hj]
  simp


theorem set_chains_loop_val (hZ : Tacenta.SessionUnitSpqrT1.ZeroizeTotal) (hA : LawAsMut)
    (hP : LawPop) (st : tacenta_session_unit.tacenta_spqr.State) (e : U64) (i : Usize) :
    tacenta_session_unit.tacenta_spqr.State.set_chains_loop st e i ⦃ fun r =>
      r.1 = st.rk ∧ r.2.1 = st.epoch ∧ r.2.2.2.1 = st.skipped ∧ r.2.2.2.2 = st.direction ∧
      r.2.2.1.val = st.chains.val.take i.val ++
        (st.chains.val.drop i.val).filter (fun p => !(p.1.val == e.val)) ⦄ := by
  unfold tacenta_session_unit.tacenta_spqr.State.set_chains_loop
  apply loop.spec_decr_nat
    (measure := fun p => p.1.chains.length - p.2.val)
    (inv := fun p => p.1.rk = st.rk ∧ p.1.epoch = st.epoch ∧ p.1.skipped = st.skipped ∧
      p.1.direction = st.direction ∧
      p.1.chains.val.take p.2.val ++
        (p.1.chains.val.drop p.2.val).filter (fun q => !(q.1.val == e.val))
      = st.chains.val.take i.val ++
        (st.chains.val.drop i.val).filter (fun q => !(q.1.val == e.val)))
  · rintro ⟨self, j⟩ ⟨hrk, hep, hsk, hdir, hL⟩
    simp only at hrk hep hsk hdir hL
    simp only [tacenta_session_unit.tacenta_spqr.State.set_chains_loop.body]
    by_cases hj : j.val < self.chains.length
    · have hjl : j < alloc.vec.Vec.len self.chains := by
        have := alloc.vec.Vec.len_val self.chains
        scalar_tac
      rw [if_pos hjl]
      step with alloc.vec.Vec.index_usize_spec self.chains j hj as ⟨pr, ch, hpr⟩
      have hget : self.chains.val[j.val]'hj = (pr, ch) := hpr.symm
      split
      · rename_i heq
        step with remove_chains_at_spec hZ hA hP self.chains j hj as ⟨v, hv⟩
        have hvl : v.length = self.chains.length - 1 := by
          have h1 : v.val.length = (self.chains.val.eraseIdx j.val).length := by rw [hv]
          rw [List.length_eraseIdx] at h1
          have h2 : j.val < self.chains.val.length := hj
          simp only [h2, if_true] at h1
          exact h1
        have hP0 : (fun q : U64 × tacenta_session_unit.tacenta_spqr.Chains => !(q.1.val == e.val))
            (self.chains.val[j.val]'hj) = false := by
          rw [hget]
          have : pr.val = e.val := by rw [heq]
          simp [this]
        refine ⟨hrk, hep, hsk, hdir, ?_, ?_⟩
        · show v.val.take j.val ++ _ = _
          rw [hv, remove_step _ _ hj _ hP0]
          exact hL
        · show v.length - j.val < self.chains.length - j.val
          omega
      · rename_i hne
        have hmax : self.chains.length ≤ Usize.max := self.chains.property
        step as ⟨i3, hi3⟩
        have hP1 : (fun q : U64 × tacenta_session_unit.tacenta_spqr.Chains => !(q.1.val == e.val))
            (self.chains.val[j.val]'hj) = true := by
          rw [hget]
          have : pr.val ≠ e.val := fun h => hne (UScalar.eq_of_val_eq h)
          simp [this]
        refine ⟨hrk, hep, hsk, hdir, ?_, ?_⟩
        · show self.chains.val.take i3.val ++ _ = _
          rw [hi3, keep_step _ _ hj _ hP1]
          exact hL
        · show self.chains.length - i3.val < self.chains.length - j.val
          omega
    · have hjl : ¬ (j < alloc.vec.Vec.len self.chains) := by
        have := alloc.vec.Vec.len_val self.chains
        scalar_tac
      rw [if_neg hjl]
      simp only [WP.spec_ok]
      refine ⟨hrk, hep, hsk, hdir, ?_⟩
      have hj' : self.chains.val.length ≤ j.val := by scalar_tac
      rw [← hL]
      exact (finish_step _ _ hj' _).symm
  · exact ⟨rfl, rfl, rfl, rfl, rfl⟩


theorem set_chains_val (hret : Tacenta.SessionUnitSpqrT1.VecRetainTotal) (hZ : Tacenta.SessionUnitSpqrT1.ZeroizeTotal)
    (hA : LawAsMut) (hP : LawPop) (st : tacenta_session_unit.tacenta_spqr.State) (e : U64) (c : tacenta_session_unit.tacenta_spqr.Chains)
    (hroom : st.chains.val.length < Usize.max) :
    tacenta_session_unit.tacenta_spqr.State.set_chains st e c ⦃ fun r =>
      r.rk = st.rk ∧ r.epoch = st.epoch ∧ r.skipped.val = st.skipped.val ∧
      r.direction = st.direction ∧
      r.chains.val = st.chains.val.filter (fun p => !(p.1.val == e.val)) ++ [(e, c)] ⦄ := by
  unfold tacenta_session_unit.tacenta_spqr.State.set_chains
  step with set_chains_loop_val hZ hA hP st e 0#usize as ⟨a, i1, v, v1, d, ha, hi1, hv1, hd, hv⟩
  have hv' : v.val = st.chains.val.filter (fun p => !(p.1.val == e.val)) := by simpa using hv
  have hvl : v.val.length ≤ st.chains.val.length := by
    rw [hv']; exact List.length_filter_le _ _
  step with Tacenta.SessionUnitSpqrT3.prepare_chains_capacity_copies
    { rk := a, epoch := i1, chains := v, skipped := v1, direction := d } 1#usize hret
    (by show v.val.length + (1#usize).val ≤ Usize.max; scalar_tac) as ⟨self1, hrk, hep, hch, hsk, hdir⟩
  have hch' : self1.chains.val = v.val := hch
  have hlt : self1.chains.val.length < Usize.max := by
    rw [hch']; omega
  step with alloc.vec.Vec.push_spec self1.chains (e, c) hlt as ⟨v2, hv2⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact hrk.trans ha
  · exact hep.trans hi1
  · show self1.skipped.val = st.skipped.val
    rw [hsk, hv1]
  · exact hdir.trans hd
  · show v2.val = _
    rw [hv2, hch', hv']


/-- The guard of the chain-table scan in `clear_old_epochs`, as a Boolean on a table entry. -/
def keepChain (current : U64) (p : U64 × tacenta_session_unit.tacenta_spqr.Chains) : Bool :=
  decide (current.val < (core.num.U64.saturating_add p.1 tacenta_session_unit.tacenta_spqr.EPOCHS_KEPT).val)


/-- The guard of the skipped-key scan in `clear_old_epochs`, as a Boolean on a skipped entry. -/
def keepSkipped (current : U64) (s : tacenta_session_unit.tacenta_spqr.Skipped) : Bool :=
  decide (current.val < (core.num.U64.saturating_add s.epoch tacenta_session_unit.tacenta_spqr.EPOCHS_KEPT).val)


theorem clear_chains_loop0_val (hZ : Tacenta.SessionUnitSpqrT1.ZeroizeTotal) (hA : LawAsMut)
    (hP : LawPop) (st : tacenta_session_unit.tacenta_spqr.State) (current : U64) (i : Usize) :
    tacenta_session_unit.tacenta_spqr.State.clear_old_epochs_loop0 st current i ⦃ fun r =>
      r.1 = st.rk ∧ r.2.1 = st.epoch ∧ r.2.2.2.1 = st.skipped ∧ r.2.2.2.2 = st.direction ∧
      r.2.2.1.val = st.chains.val.take i.val ++
        (st.chains.val.drop i.val).filter (keepChain current) ⦄ := by
  unfold tacenta_session_unit.tacenta_spqr.State.clear_old_epochs_loop0
  apply loop.spec_decr_nat
    (measure := fun p => p.1.chains.length - p.2.val)
    (inv := fun p => p.1.rk = st.rk ∧ p.1.epoch = st.epoch ∧ p.1.skipped = st.skipped ∧
      p.1.direction = st.direction ∧
      p.1.chains.val.take p.2.val ++ (p.1.chains.val.drop p.2.val).filter (keepChain current)
      = st.chains.val.take i.val ++ (st.chains.val.drop i.val).filter (keepChain current))
  · rintro ⟨self, j⟩ ⟨hrk, hep, hsk, hdir, hL⟩
    simp only at hrk hep hsk hdir hL
    simp only [tacenta_session_unit.tacenta_spqr.State.clear_old_epochs_loop0.body]
    by_cases hj : j.val < self.chains.length
    · have hjl : j < alloc.vec.Vec.len self.chains := by
        have := alloc.vec.Vec.len_val self.chains
        scalar_tac
      rw [if_pos hjl]
      step with alloc.vec.Vec.index_usize_spec self.chains j hj as ⟨pr, ch, hpr⟩
      have hget : self.chains.val[j.val]'hj = (pr, ch) := hpr.symm
      simp only [lift, bind_tc_ok]
      split
      · rename_i hlt
        have hmax : self.chains.length ≤ Usize.max := self.chains.property
        step as ⟨i4, hi4⟩
        have hP1 : keepChain current (self.chains.val[j.val]'hj) = true := by
          rw [hget]
          unfold keepChain
          simpa [UScalar.lt_equiv] using hlt
        refine ⟨hrk, hep, hsk, hdir, ?_, ?_⟩
        · show self.chains.val.take i4.val ++ _ = _
          rw [hi4, keep_step _ _ hj _ hP1]
          exact hL
        · show self.chains.length - i4.val < self.chains.length - j.val
          omega
      · rename_i hnlt
        step with remove_chains_at_spec hZ hA hP self.chains j hj as ⟨v, hv⟩
        have hvl : v.length = self.chains.length - 1 := by
          have h1 : v.val.length = (self.chains.val.eraseIdx j.val).length := by rw [hv]
          rw [List.length_eraseIdx] at h1
          have h2 : j.val < self.chains.val.length := hj
          simp only [h2, if_true] at h1
          exact h1
        have hP0 : keepChain current (self.chains.val[j.val]'hj) = false := by
          rw [hget]
          unfold keepChain
          simpa [UScalar.lt_equiv] using hnlt
        refine ⟨hrk, hep, hsk, hdir, ?_, ?_⟩
        · show v.val.take j.val ++ _ = _
          rw [hv, remove_step _ _ hj _ hP0]
          exact hL
        · show v.length - j.val < self.chains.length - j.val
          omega
    · have hjl : ¬ (j < alloc.vec.Vec.len self.chains) := by
        have := alloc.vec.Vec.len_val self.chains
        scalar_tac
      rw [if_neg hjl]
      simp only [WP.spec_ok]
      refine ⟨hrk, hep, hsk, hdir, ?_⟩
      have hj' : self.chains.val.length ≤ j.val := by scalar_tac
      rw [← hL]
      exact (finish_step _ _ hj' _).symm
  · exact ⟨rfl, rfl, rfl, rfl, rfl⟩


theorem clear_skipped_loop1_val (hZ : Tacenta.SessionUnitSpqrT1.ZeroizeTotal)
    (hP : LawPop) (v0 : alloc.vec.Vec tacenta_session_unit.tacenta_spqr.Skipped) (current : U64) (i : Usize) :
    tacenta_session_unit.tacenta_spqr.State.clear_old_epochs_loop1 v0 current i ⦃ fun r =>
      r.val = v0.val.take i.val ++ (v0.val.drop i.val).filter (keepSkipped current) ⦄ := by
  unfold tacenta_session_unit.tacenta_spqr.State.clear_old_epochs_loop1
  apply loop.spec_decr_nat
    (measure := fun p => p.1.length - p.2.val)
    (inv := fun p => p.1.val.take p.2.val ++ (p.1.val.drop p.2.val).filter (keepSkipped current)
      = v0.val.take i.val ++ (v0.val.drop i.val).filter (keepSkipped current))
  · rintro ⟨v, j⟩ hinv
    simp only at hinv
    simp only [tacenta_session_unit.tacenta_spqr.State.clear_old_epochs_loop1.body]
    by_cases hj : j.val < v.length
    · have hjl : j < alloc.vec.Vec.len v := by
        have := alloc.vec.Vec.len_val v
        scalar_tac
      rw [if_pos hjl]
      step with alloc.vec.Vec.index_usize_spec v j hj as ⟨pr, hpr⟩
      have hget : v.val[j.val]'hj = pr := hpr.symm
      simp only [lift, bind_tc_ok]
      split
      · rename_i hlt
        have hmax : v.length ≤ Usize.max := v.property
        step as ⟨j1, hj1⟩
        have hP1 : keepSkipped current (v.val[j.val]'hj) = true := by
          rw [hget]
          unfold keepSkipped
          simpa [UScalar.lt_equiv] using hlt
        refine ⟨?_, ?_⟩
        · show v.val.take j1.val ++ _ = _
          rw [hj1, keep_step _ _ hj _ hP1]
          exact hinv
        · show v.length - j1.val < v.length - j.val
          omega
      · rename_i hnlt
        step with spqr_remove_skipped_at_spec hZ hP v j hj as ⟨d, v1, hd, hv1⟩
        step with array_zeroize_step hZ
        have hvl : v1.length = v.length - 1 := by
          have h1 : v1.val.length = (v.val.eraseIdx j.val).length := by rw [hv1]
          rw [List.length_eraseIdx] at h1
          have h2 : j.val < v.val.length := hj
          simp only [h2, if_true] at h1
          exact h1
        have hP0 : keepSkipped current (v.val[j.val]'hj) = false := by
          rw [hget]
          unfold keepSkipped
          simpa [UScalar.lt_equiv] using hnlt
        refine ⟨?_, ?_⟩
        · show v1.val.take j.val ++ _ = _
          rw [hv1, remove_step _ _ hj _ hP0]
          exact hinv
        · show v1.length - j.val < v.length - j.val
          omega
    · have hjl : ¬ (j < alloc.vec.Vec.len v) := by
        have := alloc.vec.Vec.len_val v
        scalar_tac
      rw [if_neg hjl]
      simp only [WP.spec_ok]
      have hj' : v.val.length ≤ j.val := by scalar_tac
      rw [← hinv]
      exact (finish_step _ _ hj' _).symm
  · exact rfl


theorem clear_old_epochs_val (hZ : Tacenta.SessionUnitSpqrT1.ZeroizeTotal) (hA : LawAsMut)
    (hP : LawPop) (st : tacenta_session_unit.tacenta_spqr.State) (current : U64) :
    tacenta_session_unit.tacenta_spqr.State.clear_old_epochs st current ⦃ fun r =>
      r.rk = st.rk ∧ r.epoch = st.epoch ∧ r.direction = st.direction ∧
      r.chains.val = st.chains.val.filter (keepChain current) ∧
      r.skipped.val = st.skipped.val.filter (keepSkipped current) ⦄ := by
  unfold tacenta_session_unit.tacenta_spqr.State.clear_old_epochs
  step with clear_chains_loop0_val hZ hA hP st current 0#usize as
    ⟨a, i1, v, v1, d, ha, hi1, hv1, hd, hv⟩
  step with clear_skipped_loop1_val hZ hP v1 current 0#usize as ⟨v2, hv2⟩
  have hv' : v.val = st.chains.val.filter (keepChain current) := by simpa using hv
  have hv2' : v2.val = st.skipped.val.filter (keepSkipped current) := by
    have h := hv2
    rw [hv1] at h
    simpa using h
  exact ⟨ha, hi1, hd, hv', hv2'⟩


theorem epochs_kept_val :
    tacenta_session_unit.tacenta_spqr.EPOCHS_KEPT.val = Model.SparseRatchet.epochsKept := by
  unfold Model.SparseRatchet.epochsKept
  simp only [global_simps]
  rfl


theorem sat_val (x : U64) (hx : x.val + Model.SparseRatchet.epochsKept ≤ Std.U64.max) :
    (core.num.U64.saturating_add x tacenta_session_unit.tacenta_spqr.EPOCHS_KEPT).val
      = x.val + Model.SparseRatchet.epochsKept := by
  show (UScalar.saturating_add x tacenta_session_unit.tacenta_spqr.EPOCHS_KEPT).val = _
  rw [Tacenta.SessionUnitSpqrT3.saturating_add_val, epochs_kept_val]
  omega


/-- `RemoveSkippedAtAgrees`, from the array zeroize law and the pop law. -/
theorem removeSkippedAtAgrees (hZ : Tacenta.SessionUnitSpqrT1.ZeroizeTotal) (hP : LawPop) :
    Tacenta.SessionUnitSpqrT3.RemoveSkippedAtAgrees := by
  intro v i h
  obtain ⟨r, hr, hk, hv⟩ := Std.WP.spec_imp_exists (spqr_remove_skipped_at_spec hZ hP v i h)
  exact ⟨r, hr, hk, hv⟩


theorem setChainsAgrees (hret : Tacenta.SessionUnitSpqrT1.VecRetainTotal) (hZ : Tacenta.SessionUnitSpqrT1.ZeroizeTotal)
    (hA : LawAsMut) (hP : LawPop) :
    ∀ {s : tacenta_session_unit.tacenta_spqr.State} {m : Model.SparseRatchet.State}
      (_hrel : Tacenta.SessionUnitSpqrT3.StateRefines s m) (e : Std.U64) (c : tacenta_session_unit.tacenta_spqr.Chains)
      (_hroom : s.chains.val.length < Usize.max),
    ∃ r, tacenta_session_unit.tacenta_spqr.State.set_chains s e c = ok r ∧
      Tacenta.SessionUnitSpqrT3.StateRefines r (Model.SparseRatchet.setChains m e.val (Tacenta.SessionUnitSpqrT3.chainsOf c)) := by
  intro s m hrel e c hroom
  obtain ⟨r, hr, hrk, hep, hsk, hdir, hch⟩ :=
    Std.WP.spec_imp_exists (set_chains_val hret hZ hA hP s e c hroom)
  refine ⟨r, hr, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hrk]; exact hrel.rk
  · rw [hep]; exact hrel.epoch
  · have hm : (Model.SparseRatchet.setChains m e.val (Tacenta.SessionUnitSpqrT3.chainsOf c)).chains
        = (m.chains.filter (fun p => !(p.1 == e.val))) ++ [(e.val, Tacenta.SessionUnitSpqrT3.chainsOf c)] :=
      rfl
    show r.chains.val.map Tacenta.SessionUnitSpqrT3.chainsEntryOf = _
    rw [hm, ← hrel.chains, hch, List.map_append, List.filter_map]
    rfl
  · rw [hsk]; exact hrel.skipped
  · rw [hdir]; exact hrel.direction


theorem clearOldEpochsAgrees (hZ : Tacenta.SessionUnitSpqrT1.ZeroizeTotal) (hA : LawAsMut) (hP : LawPop) :
    ∀ {s : tacenta_session_unit.tacenta_spqr.State} {m : Model.SparseRatchet.State}
      (_hrel : Tacenta.SessionUnitSpqrT3.StateRefines s m) (current : Std.U64)
      (_hcb : ∀ p ∈ s.chains.val,
        p.1.val + Model.SparseRatchet.epochsKept ≤ Std.U64.max)
      (_hsb : ∀ sk ∈ s.skipped.val,
        sk.epoch.val + Model.SparseRatchet.epochsKept ≤ Std.U64.max),
    ∃ r, tacenta_session_unit.tacenta_spqr.State.clear_old_epochs s current = ok r ∧
      Tacenta.SessionUnitSpqrT3.StateRefines r (Model.SparseRatchet.clearOldEpochs m current.val) := by
  intro s m hrel current hcb hsb
  obtain ⟨r, hr, hrk, hep, hdir, hch, hsk⟩ :=
    Std.WP.spec_imp_exists (clear_old_epochs_val hZ hA hP s current)
  refine ⟨r, hr, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hrk]; exact hrel.rk
  · rw [hep]; exact hrel.epoch
  · have hm : (Model.SparseRatchet.clearOldEpochs m current.val).chains
        = m.chains.filter (fun p => decide (current.val < p.1 + Model.SparseRatchet.epochsKept)) :=
      rfl
    show r.chains.val.map Tacenta.SessionUnitSpqrT3.chainsEntryOf = _
    rw [hm, ← hrel.chains, hch, List.filter_map]
    congr 1
    apply List.filter_congr
    intro p hp
    unfold keepChain
    simp [Function.comp, Tacenta.SessionUnitSpqrT3.chainsEntryOf, sat_val p.1 (hcb p hp)]
  · have hm : (Model.SparseRatchet.clearOldEpochs m current.val).skipped
        = m.skipped.filter (fun x => decide (current.val < x.1 + Model.SparseRatchet.epochsKept)) :=
      rfl
    show r.skipped.val.map Tacenta.SessionUnitSpqrT3.skippedOf = _
    rw [hm, ← hrel.skipped, hsk, List.filter_map]
    congr 1
    apply List.filter_congr
    intro p hp
    unfold keepSkipped
    simp [Function.comp, Tacenta.SessionUnitSpqrT3.skippedOf, sat_val p.epoch (hsb p hp)]
  · rw [hdir]; exact hrel.direction


/-- **`VecRetainAgrees`**, proved from exactly the five laws it uses: `LawCapacity`, `LawVecZeroize`,
the array `Zeroize` law (`SpqrT1.ZeroizeTotal`), `LawAsMut` and `LawPop`.  The two chain-table scans,
the skipped-key scan and the capacity copy are proved from the translated bodies.  This form takes
the laws one by one so that its axiom footprint is only the constants those laws are about (plus
`Pair.Insts.ZeroizeZeroize.zeroize`, which occurs in the statement through
`State.prepare_chains_capacity` and is never used). -/
theorem vecRetainAgreesOfLaws (hCap : LawCapacity) (hVZ : LawVecZeroize)
    (hZ : Tacenta.SessionUnitSpqrT1.ZeroizeTotal) (hA : LawAsMut) (hP : LawPop) :
    Tacenta.SessionUnitSpqrT3.VecRetainAgrees :=
  ⟨setChainsAgrees (vecRetainTotal hCap hVZ hZ hA hP) hZ hA hP,
   clearOldEpochsAgrees hZ hA hP⟩


/-- **`VecRetainAgrees`**, from the bundle of laws.  Its `#print axioms` also lists the constants the
other fields of `Laws` are about (`hkdf_sha256`, `Zeroizing`), because they occur in the type of `L`;
the proof does not use them (see `vecRetainAgreesOfLaws`). -/
theorem vecRetainAgrees (L : Laws) : Tacenta.SessionUnitSpqrT3.VecRetainAgrees :=
  vecRetainAgreesOfLaws L.capacity L.vecZeroize L.arrayZeroize L.asMut L.pop


/-! ## The laws the defined hypotheses need are satisfiable, and the defined hypotheses reduce to
axiom-level ones

Each law is about one opaque constant of the leaf crate.  The shape states it over an arbitrary
function of the constant's type, `*_is` ties the shape to the law about the real constant by
`Iff.rfl` (so the build compares them), and `*_satisfiable` gives a function.  `LawPop` and
`LawAsMut` are not hypotheses of any leaf theorem; they constrain constants that no other
hypothesis of these theorems mentions, so adding them to a model costs nothing.  `LawCapacity` and
`LawVecZeroize` are the first two conjuncts of `SpqrT1.VecRetainTotal` itself. -/

abbrev PopFn := {T : Type} → Type → alloc.vec.Vec T → Result (Option T × alloc.vec.Vec T)

def PopShape (f : PopFn) : Prop :=
  ∀ (T : Type) (v : alloc.vec.Vec T), v.val ≠ [] →
    ∃ o w, f Global v = ok (o, w) ∧ w.val = v.val.dropLast

theorem LawPop_is : LawPop ↔ PopShape @alloc.vec.Vec.pop := Iff.rfl

/-- The real `Vec::pop`: the last element and the vector without it. -/
def popWitness : PopFn := fun {_T} _ v =>
  ok (v.val.getLast?, ⟨v.val.dropLast, by have := v.property; rw [List.length_dropLast]; omega⟩)

theorem pop_satisfiable : ∃ f : PopFn, PopShape f :=
  ⟨@popWitness, fun _ _ _ => ⟨_, _, rfl, rfl⟩⟩

abbrev AsMutFn := {T : Type} → Option T → Result (Option T × (Option T → Option T))

def AsMutShape (f : AsMutFn) : Prop := ∀ (T : Type) (o : Option T), ∃ r, f o = ok r

theorem LawAsMut_is : LawAsMut ↔ AsMutShape @core.option.Option.as_mut := Iff.rfl

theorem as_mut_satisfiable : ∃ f : AsMutFn, AsMutShape f :=
  ⟨fun o => ok (o, id), fun _ _ => ⟨_, rfl⟩⟩

abbrev CapacityFn := {T : Type} → Type → alloc.vec.Vec T → Result Usize

def CapacityShape (f : CapacityFn) : Prop :=
  ∀ {T : Type} (A : Type) (v : alloc.vec.Vec T), ∃ r, f A v = ok r

theorem LawCapacity_is : LawCapacity ↔ CapacityShape @alloc.vec.Vec.capacity := Iff.rfl

theorem capacity_satisfiable : ∃ f : CapacityFn, CapacityShape f :=
  ⟨fun _ _ => ok 0#usize, fun _ _ => ⟨_, rfl⟩⟩

abbrev VecZeroizeFn := {Z : Type} → zeroize.Zeroize Z → alloc.vec.Vec Z → Result (alloc.vec.Vec Z)

def VecZeroizeShape (f : VecZeroizeFn) : Prop :=
  ∀ {T : Type} (inst : zeroize.Zeroize T) (v : alloc.vec.Vec T), ∃ r, f inst v = ok r

theorem LawVecZeroize_is :
    LawVecZeroize ↔ VecZeroizeShape @alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize := Iff.rfl

theorem vec_zeroize_satisfiable : ∃ f : VecZeroizeFn, VecZeroizeShape f :=
  ⟨fun _ v => ok v, fun _ v => ⟨v, rfl⟩⟩

/-- The four defined-function hypotheses of the leaf sparse-ratchet theorems follow from the
axiom-level hypotheses those theorems also take (`ZeroizeTotal`, `SpqrHkdfAgrees`, the two round
trips) and the four laws above. -/
theorem defined_hyps_from_axiom_hyps
    (hz : Tacenta.SessionUnitSpqrT1.ZeroizeTotal) (hk : Tacenta.SessionUnitSpqrT3.SpqrHkdfAgrees)
    (h96 : Tacenta.SessionUnitSpqrT3.ZeroizingRoundTrips96) (h64 : Tacenta.SessionUnitSpqrT3.ZeroizingRoundTrips64)
    (hcap : LawCapacity) (hvz : LawVecZeroize) (hpop : LawPop) (has : LawAsMut) :
    Tacenta.SessionUnitSpqrT1.RemoveSkippedAtTotal ∧ Tacenta.SessionUnitSpqrT1.KdfRkTotal ∧
    Tacenta.SessionUnitSpqrT1.KdfCkTotal ∧ Tacenta.SessionUnitSpqrT1.VecRetainTotal :=
  defined_fields_hold
    ⟨hpop, has, hcap, hvz, hz,
     fun N salt ikm info hN => by
       obtain ⟨r, hr, -⟩ := hk N salt ikm info hN
       exact ⟨r, hr⟩,
     fun z => h96 (arrInst 96#usize) z, fun z => h64 (arrInst 64#usize) z⟩

/-! ## The session-unit agreement provider

`UnitSatisfiabilityJoint` already carries faithful behaviour for the standard-library operations
and the session unit's vector-zeroize axiom shape.  This bridge feeds exactly those facts into the
body-level agreement derivation above.  It is deliberately parameterised by the real-operation
shapes: it proves that the two agreements are consequences of named laws, but it does not assert
that the external standard library or `zeroize` implementation satisfies those laws. -/

open Tacenta.UnitSatisfiabilityJoint

theorem session_sparse_agreements_of_shapes
    (std : StdLaws Interp.real)
    (vecAxiom : VecRetainAxiomShape Interp.real)
    (arrayZeroize : SpqrZeroizeShape Interp.real) :
    Tacenta.SessionUnitSpqrT3.VecRetainAgrees ∧
      Tacenta.SessionUnitSpqrT3.RemoveSkippedAtAgrees := by
  have hpop : LawPop := by
    intro T v hv
    exact std.pop T v hv
  have hasMut : LawAsMut := by
    intro T o
    exact std.asMut T o
  have hcapacity : LawCapacity := by
    intro T A v
    simpa [Interp.real] using
      (Exists.imp (fun _ h => h) (vecAxiom.1 A v))
  have hvecZeroize : LawVecZeroize := by
    intro T inst v
    obtain ⟨r, hr⟩ := vecAxiom.2 inst v
    exact ⟨r, by simpa [Interp.real] using hr⟩
  have harrayZeroize : Tacenta.SessionUnitSpqrT1.ZeroizeTotal := by
    intro Z N inst a
    obtain ⟨r, hr⟩ := arrayZeroize inst a
    exact ⟨r, by simpa [Interp.real] using hr⟩
  exact ⟨
    vecRetainAgreesOfLaws hcapacity hvecZeroize harrayZeroize hasMut hpop,
    removeSkippedAtAgrees harrayZeroize hpop⟩

end Tacenta.SessionUnitSatisfiabilitySpqrLaws

end
