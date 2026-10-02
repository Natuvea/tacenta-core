import Translation.UnitSatisfiabilityTriple

/-!
# The three-leaf unit's hypotheses about translated functions, from laws about opaque constants

The Triple Ratchet's discharged refinement theorems (`UnitTripleT3.send_refines_discharged`,
`receive_refines_discharged`) and the unit's copies of the classical and sparse ratchet theorems take
hypotheses that are statements about functions the translation defines, with a body, not about
opaque constants: `UnitT1.RemoveSkippedAtTotal`, `UnitSpqrT1.RemoveSkippedAtTotal`,
`UnitSpqrT1.KdfRkTotal`, `UnitSpqrT1.KdfCkTotal`, `UnitTripleT1.KdfInitTotal`,
`UnitSpqrT1.VecRetainTotal` (with its three loop contracts), `UnitSpqrT3.RemoveSkippedAtAgrees` and
`UnitSpqrT3.VecRetainAgrees`. A model of the opaque constants cannot change what they say.
`UnitSatisfiabilityTriple.lean` bridges the two removal hypotheses to shapes applied to the defined
helpers (`vec_remove_joint_is`), which are satisfiable for any function and say nothing about the
bodies; the rest had no witness, and `VecRetainAgrees` is restated, not proved, by
`UnitSpqrT3.set_chains_refines` and `clear_old_epochs_refines`.

This module proves each of them, by stepping through the translated code, from a small set of laws
about the opaque constants the bodies reach. The laws are `Laws`: `Vec::pop` of a non-empty vector
returns the vector without its last element (`LawPop`), `Option::as_mut` returns (`LawAsMut`), the
blanket `Zeroize` implementation returns at `u32` (`LawBlanketU32`), `Vec::capacity` returns
(`LawCapacity`), the `Vec` `Zeroize` implementation returns (`LawVecZeroize`), the array `Zeroize`
implementation returns (the existing hypothesis `UnitSpqrT1.ZeroizeTotal`), the HKDF returns for
output lengths up to 8160 bytes (`LawHkdf`), and the `Zeroizing` wrapper reads back what it wraps at
96 and 64 bytes (`LawZeroizing`). The classical and sparse ratchets share these constants in the
unit, so one set of laws serves both.

* `defined_fields_hold`: the six T1 hypotheses follow from `Laws`.
* `defined_hyps_from_axiom_hyps`: the same, from the hypotheses the theorems already take
  (`ZeroizeTotal`, `SpqrHkdfAgrees` and the two round trips) and five laws.
* `removeSkippedAtAgrees`, `vecRetainAgreesOfLaws`, `vecRetainAgrees`: the two T3 agreements, as
  statements about the translated functions for all inputs.
* `laws_jointly_satisfiable`: the nine laws, over arbitrary functions of the constants' types, hold
  of one assignment, each tied to the statement about the real constant by `Iff.rfl`.
* `roundTrips80_satisfiable` and `arrZ32_satisfiable`: witnesses for `UnitT3.ZeroizingRoundTrips80`
  and `UnitTripleT3.ZeroizeTotal`, which had none.

Nothing here shows that the real standard-library and `zeroize` functions satisfy the laws. They
are assumptions about standard-library and `zeroize` operations, tested against the real functions
only by reading. `UnitSpqrT1.ZeroizeTotal` is stronger than the crate: it quantifies over every
`Zeroize` record, so it cannot hold of a wipe that propagates a failing element
(`spqrZeroizeTotal_conflicts`). The proofs in this module apply it at the byte instance on 32-byte
arrays only. That hypothesis is documented and unchanged here.

The proofs are generic in the platform width: they use `Usize.max >= 2^32 - 1` or split on
`Usize.bounds_eq`. This module restates the session unit's `UnitSatisfiabilityRatchet.lean`
for the three-leaf unit (the specifications of the removal helpers, the loops and the key
derivations are the same proofs under the unit's constants) and adds the value-level
specifications of the retain loops and the two agreements.
-/

open Aeneas Aeneas.Std Result ControlFlow Error
open tacenta_triple_unit

noncomputable section

namespace Tacenta.UnitSatisfiabilityTripleLaws




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

theorem protocol_info_len : (tacenta_spqr.PROTOCOL_INFO : Slice U8).length = 12 := by
  simp only [global_simps, Array.length_to_slice]; scalar_tac

theorem chain_start_len : (tacenta_spqr.CHAIN_START_LABEL : Slice U8).length = 11 := by
  simp only [global_simps, Array.length_to_slice]; scalar_tac

theorem root_label_len : (tacenta_spqr.ROOT_LABEL : Slice U8).length = 4 := by
  simp only [global_simps, Array.length_to_slice]; scalar_tac

theorem chain_label_len : (tacenta_spqr.CHAIN_LABEL : Slice U8).length = 5 := by
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
    tacenta_spqr.info suffix ⦃ fun _ => True ⦄ := by
  unfold tacenta_spqr.info
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

theorem split3_spec (out : Array U8 96#usize) : tacenta_spqr.split3 out ⦃ fun _ => True ⦄ := by
  unfold tacenta_spqr.split3
  step*
  all_goals (try simp_all [Slice.length, Array.repeat, List.slice])


/-- `KdfRkTotal`, proved from the HKDF law and the wrapper law at 96 bytes. -/
theorem kdfRkTotal (hH : LawHkdf) (hZ : LawZeroizing 96#usize) :
    Tacenta.UnitSpqrT1.KdfRkTotal := by
  intro rk k
  apply ex_of_spec (p := fun _ => True)
  unfold tacenta_spqr.kdf_rk
  have h4 : (tacenta_spqr.ROOT_LABEL : Slice U8).length + 12 ≤ Usize.max := by
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
    Tacenta.UnitSpqrT1.KdfCkTotal := by
  intro ck n
  apply ex_of_spec (p := fun _ => True)
  unfold tacenta_spqr.kdf_ck tacenta_spqr.be64
  have h4 : (tacenta_spqr.CHAIN_LABEL : Slice U8).length + 12 ≤ Usize.max := by
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


/-- `KdfInitTotal`: for EVERY slice `sk`, proved from the HKDF law (all slice lengths) and the
wrapper law at 96 bytes. -/
theorem kdfInitTotal (hH : LawHkdf) (hZ : LawZeroizing 96#usize) :
    Tacenta.UnitTripleT1.KdfInitTotal := by
  intro sk
  apply ex_of_spec (p := fun _ => True)
  unfold tacenta_spqr.kdf_init
  have h4 : (tacenta_spqr.CHAIN_START_LABEL : Slice U8).length + 12 ≤ Usize.max := by
    rw [chain_start_len]; scalar_tac
  step
  step with info_spec _ h4
  step with hkdf_step hH 96#usize _ _ _ (by scalar_tac)
  step with zeroizing_new_step _ hZ as ⟨out, hout⟩
  rw [hout]
  simp only [bind_tc_ok]
  step with split3_spec




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

theorem ratchet_loop_eq : @tacenta_ratchet.remove_skipped_at_loop = @rotLoop tacenta_ratchet.SkippedKey := rfl
theorem spqr_loop_eq : @tacenta_spqr.State.remove_skipped_at_loop = @rotLoop tacenta_spqr.Skipped := rfl
theorem chains_loop_eq :
    @tacenta_spqr.State.remove_chains_at_loop = @rotLoop (U64 × tacenta_spqr.Chains) := rfl


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

theorem skipped_zeroize_spec (hZ : Tacenta.UnitSpqrT1.ZeroizeTotal) (s : tacenta_spqr.Skipped) :
    tacenta_spqr.Skipped.Insts.ZeroizeZeroize.zeroize s ⦃ fun r => r.epoch = s.epoch ∧ r.n = s.n ⦄ := by
  unfold tacenta_spqr.Skipped.Insts.ZeroizeZeroize.zeroize
  obtain ⟨r, hr⟩ := hZ (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes) s.key
  simp [hr]

/-- The sparse ratchet's `remove_skipped_at`, at an in-range index: returns the key at that index
and the vector with that index erased. -/
theorem spqr_remove_skipped_at_spec (hZ : Tacenta.UnitSpqrT1.ZeroizeTotal) (hP : LawPop)
    (v : alloc.vec.Vec tacenta_spqr.Skipped) (i : Usize) (hi : i.val < v.val.length) :
    tacenta_spqr.State.remove_skipped_at v i ⦃ fun r =>
      r.1 = (v.val[i.val]'hi).key ∧ r.2.val = v.val.eraseIdx i.val ⦄ := by
  unfold tacenta_spqr.State.remove_skipped_at
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


/-- `UnitSpqrT1.RemoveSkippedAtTotal`, from the pop law and the array zeroize law. -/
theorem spqrRemoveSkippedAtTotal (hZ : Tacenta.UnitSpqrT1.ZeroizeTotal) (hP : LawPop) :
    Tacenta.UnitSpqrT1.RemoveSkippedAtTotal := by
  intro v i hi
  obtain ⟨r, hr, -, hv⟩ := Std.WP.spec_imp_exists (spqr_remove_skipped_at_spec hZ hP v i hi)
  refine ⟨r, hr, ?_⟩
  rw [hv]
  simp [List.length_eraseIdx, hi]
  omega

/-- **`LawBlanketU32`.**  The `Zeroize` blanket implementation returns at `u32`. No theorem
hypothesis states it. -/
def LawBlanketU32 : Prop :=
  ∀ x : U32, ∃ r, zeroize.Zeroize.Blanket.zeroize U32.Insts.ZeroizeDefaultIsZeroes x = ok r

theorem skippedKey_zeroize_spec (hZ : Tacenta.UnitSpqrT1.ZeroizeTotal) (hB : LawBlanketU32)
    (s : tacenta_ratchet.SkippedKey) :
    tacenta_ratchet.SkippedKey.Insts.ZeroizeZeroize.zeroize s ⦃ fun _ => True ⦄ := by
  unfold tacenta_ratchet.SkippedKey.Insts.ZeroizeZeroize.zeroize
  obtain ⟨r1, h1⟩ := hZ (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes) s.dh
  obtain ⟨r2, h2⟩ := hB s.n
  obtain ⟨r3, h3⟩ := hB s.stored_at
  obtain ⟨r4, h4⟩ := hZ (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes) s.key
  simp [h1, h2, h3, h4]

/-- The classical ratchet's `remove_skipped_at`, at an in-range index. -/
theorem ratchet_remove_skipped_at_spec (hZ : Tacenta.UnitSpqrT1.ZeroizeTotal)
    (hB : LawBlanketU32) (hP : LawPop)
    (v : alloc.vec.Vec tacenta_ratchet.SkippedKey) (i : Usize) (hi : i.val < v.val.length) :
    tacenta_ratchet.remove_skipped_at v i ⦃ fun r =>
      r.1 = (v.val[i.val]'hi).key ∧ r.2.val = v.val.eraseIdx i.val ⦄ := by
  unfold tacenta_ratchet.remove_skipped_at
  rw [ratchet_loop_eq]
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
  step with skippedKey_zeroize_spec hZ hB as ⟨s2⟩
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


/-- `UnitT1.RemoveSkippedAtTotal`, from the pop law, the array zeroize law and the `u32`
blanket zeroize law. -/
theorem ratchetRemoveSkippedAtTotal (hZ : Tacenta.UnitSpqrT1.ZeroizeTotal)
    (hB : LawBlanketU32) (hP : LawPop) : Tacenta.UnitT1.RemoveSkippedAtTotal := by
  intro A v i hi
  obtain ⟨r, hr, h1, h2⟩ := Std.WP.spec_imp_exists (ratchet_remove_skipped_at_spec hZ hB hP v i hi)
  exact ⟨r, hr, h1, h2⟩


/-- **`LawAsMut`.**  `Option::as_mut` returns. No theorem hypothesis states it. -/
def LawAsMut : Prop :=
  ∀ (T : Type) (o : Option T), ∃ r, core.option.Option.as_mut o = ok r

theorem chain_zeroize_spec (hZ : Tacenta.UnitSpqrT1.ZeroizeTotal) (c : tacenta_spqr.Chain) :
    tacenta_spqr.Chain.Insts.ZeroizeZeroize.zeroize c ⦃ fun _ => True ⦄ := by
  unfold tacenta_spqr.Chain.Insts.ZeroizeZeroize.zeroize
  obtain ⟨r, hr⟩ := hZ (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes) c.ck
  simp [hr]

theorem as_mut_step (hA : LawAsMut) {T : Type} (o : Option T) :
    core.option.Option.as_mut o ⦃ fun _ => True ⦄ := by
  obtain ⟨r, hr⟩ := hA T o
  simp [hr]

theorem chains_zeroize_spec (hZ : Tacenta.UnitSpqrT1.ZeroizeTotal) (hA : LawAsMut)
    (c : tacenta_spqr.Chains) :
    tacenta_spqr.Chains.Insts.ZeroizeZeroize.zeroize c ⦃ fun _ => True ⦄ := by
  unfold tacenta_spqr.Chains.Insts.ZeroizeZeroize.zeroize
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
theorem remove_chains_at_spec (hZ : Tacenta.UnitSpqrT1.ZeroizeTotal) (hA : LawAsMut)
    (hP : LawPop)
    (v : alloc.vec.Vec (U64 × tacenta_spqr.Chains)) (i : Usize) (hi : i.val < v.val.length) :
    tacenta_spqr.State.remove_chains_at v i ⦃ fun r => r.val = v.val.eraseIdx i.val ⦄ := by
  unfold tacenta_spqr.State.remove_chains_at
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


theorem set_chains_loop_spec (hZ : Tacenta.UnitSpqrT1.ZeroizeTotal) (hA : LawAsMut)
    (hP : LawPop) (st : tacenta_spqr.State) (e : U64) (i : Usize) :
    tacenta_spqr.State.set_chains_loop st e i ⦃ fun r =>
      r.2.2.1.length ≤ st.chains.length ∧ r.2.2.2.1 = st.skipped ⦄ := by
  unfold tacenta_spqr.State.set_chains_loop
  apply loop.spec_decr_nat
    (measure := fun p => p.1.chains.length - p.2.val)
    (inv := fun p => p.1.skipped = st.skipped ∧ p.1.chains.length ≤ st.chains.length)
  · rintro ⟨self, j⟩ ⟨hsk, hlen⟩
    simp only at hsk hlen
    simp only [tacenta_spqr.State.set_chains_loop.body]
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


theorem clear_chains_loop0_spec (hZ : Tacenta.UnitSpqrT1.ZeroizeTotal) (hA : LawAsMut)
    (hP : LawPop) (st : tacenta_spqr.State) (current : U64) (i : Usize) :
    tacenta_spqr.State.clear_old_epochs_loop0 st current i ⦃ fun r =>
      r.2.2.1.length ≤ st.chains.length ∧ r.2.2.2.1 = st.skipped ⦄ := by
  unfold tacenta_spqr.State.clear_old_epochs_loop0
  apply loop.spec_decr_nat
    (measure := fun p => p.1.chains.length - p.2.val)
    (inv := fun p => p.1.skipped = st.skipped ∧ p.1.chains.length ≤ st.chains.length)
  · rintro ⟨self, j⟩ ⟨hsk, hlen⟩
    simp only at hsk hlen
    simp only [tacenta_spqr.State.clear_old_epochs_loop0.body]
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


theorem array_zeroize_step (hZ : Tacenta.UnitSpqrT1.ZeroizeTotal) (a : Array U8 32#usize) :
    Array.Insts.ZeroizeZeroize.zeroize
      (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes) a ⦃ fun _ => True ⦄ := by
  obtain ⟨r, hr⟩ := hZ (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes) a
  simp [hr]

theorem clear_skipped_loop1_spec (hZ : Tacenta.UnitSpqrT1.ZeroizeTotal)
    (hP : LawPop) (v0 : alloc.vec.Vec tacenta_spqr.Skipped) (current : U64) (i : Usize) :
    tacenta_spqr.State.clear_old_epochs_loop1 v0 current i ⦃ fun r =>
      r.length ≤ v0.length ⦄ := by
  unfold tacenta_spqr.State.clear_old_epochs_loop1
  apply loop.spec_decr_nat
    (measure := fun p => p.1.length - p.2.val)
    (inv := fun p => p.1.length ≤ v0.length)
  · rintro ⟨v, j⟩ hinv
    simp only at hinv
    simp only [tacenta_spqr.State.clear_old_epochs_loop1.body]
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


theorem setChainsLoopTotal (hZ : Tacenta.UnitSpqrT1.ZeroizeTotal) (hA : LawAsMut)
    (hP : LawPop) : Tacenta.UnitSpqrT1.SetChainsLoopTotal := by
  intro st e i _
  obtain ⟨r, hr, h⟩ := Std.WP.spec_imp_exists (set_chains_loop_spec hZ hA hP st e i)
  obtain ⟨a, b, c, d, f⟩ := r
  exact ⟨_, hr, h⟩

theorem clearChainsLoop0Total (hZ : Tacenta.UnitSpqrT1.ZeroizeTotal) (hA : LawAsMut)
    (hP : LawPop) : Tacenta.UnitSpqrT1.ClearChainsLoop0Total := by
  intro st current i _
  obtain ⟨r, hr, h⟩ := Std.WP.spec_imp_exists (clear_chains_loop0_spec hZ hA hP st current i)
  obtain ⟨a, b, c, d, f⟩ := r
  exact ⟨_, hr, h⟩

theorem clearSkippedLoopTotal (hZ : Tacenta.UnitSpqrT1.ZeroizeTotal)
    (hP : LawPop) : Tacenta.UnitSpqrT1.ClearSkippedLoopTotal := by
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
    (hZ : Tacenta.UnitSpqrT1.ZeroizeTotal) (hA : LawAsMut) (hP : LawPop) :
    Tacenta.UnitSpqrT1.VecRetainTotal :=
  ⟨hCap, hVZ, setChainsLoopTotal hZ hA hP, clearChainsLoop0Total hZ hA hP,
    clearSkippedLoopTotal hZ hP⟩



/-- The laws, on the opaque constants, that make the defined-function fields true. -/
structure Laws : Prop where
  pop : LawPop
  asMut : LawAsMut
  blanketU32 : LawBlanketU32
  capacity : LawCapacity
  vecZeroize : LawVecZeroize
  arrayZeroize : Tacenta.UnitSpqrT1.ZeroizeTotal
  hkdf : LawHkdf
  zeroizing96 : LawZeroizing 96#usize
  zeroizing64 : LawZeroizing 64#usize

theorem defined_fields_hold (L : Laws) :
    Tacenta.UnitT1.RemoveSkippedAtTotal ∧
    Tacenta.UnitSpqrT1.RemoveSkippedAtTotal ∧
    Tacenta.UnitSpqrT1.KdfRkTotal ∧
    Tacenta.UnitSpqrT1.KdfCkTotal ∧
    Tacenta.UnitTripleT1.KdfInitTotal ∧
    Tacenta.UnitSpqrT1.VecRetainTotal :=
  ⟨ratchetRemoveSkippedAtTotal L.arrayZeroize L.blanketU32 L.pop,
   spqrRemoveSkippedAtTotal L.arrayZeroize L.pop,
   kdfRkTotal L.hkdf L.zeroizing96,
   kdfCkTotal L.hkdf L.zeroizing64,
   kdfInitTotal L.hkdf L.zeroizing96,
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


theorem set_chains_loop_val (hZ : Tacenta.UnitSpqrT1.ZeroizeTotal) (hA : LawAsMut)
    (hP : LawPop) (st : tacenta_spqr.State) (e : U64) (i : Usize) :
    tacenta_spqr.State.set_chains_loop st e i ⦃ fun r =>
      r.1 = st.rk ∧ r.2.1 = st.epoch ∧ r.2.2.2.1 = st.skipped ∧ r.2.2.2.2 = st.direction ∧
      r.2.2.1.val = st.chains.val.take i.val ++
        (st.chains.val.drop i.val).filter (fun p => !(p.1.val == e.val)) ⦄ := by
  unfold tacenta_spqr.State.set_chains_loop
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
    simp only [tacenta_spqr.State.set_chains_loop.body]
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
        have hP0 : (fun q : U64 × tacenta_spqr.Chains => !(q.1.val == e.val))
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
        have hP1 : (fun q : U64 × tacenta_spqr.Chains => !(q.1.val == e.val))
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


theorem set_chains_val (hret : Tacenta.UnitSpqrT1.VecRetainTotal) (hZ : Tacenta.UnitSpqrT1.ZeroizeTotal)
    (hA : LawAsMut) (hP : LawPop) (st : tacenta_spqr.State) (e : U64) (c : tacenta_spqr.Chains)
    (hroom : st.chains.val.length < Usize.max) :
    tacenta_spqr.State.set_chains st e c ⦃ fun r =>
      r.rk = st.rk ∧ r.epoch = st.epoch ∧ r.skipped.val = st.skipped.val ∧
      r.direction = st.direction ∧
      r.chains.val = st.chains.val.filter (fun p => !(p.1.val == e.val)) ++ [(e, c)] ⦄ := by
  unfold tacenta_spqr.State.set_chains
  step with set_chains_loop_val hZ hA hP st e 0#usize as ⟨a, i1, v, v1, d, ha, hi1, hv1, hd, hv⟩
  have hv' : v.val = st.chains.val.filter (fun p => !(p.1.val == e.val)) := by simpa using hv
  have hvl : v.val.length ≤ st.chains.val.length := by
    rw [hv']; exact List.length_filter_le _ _
  step with Tacenta.UnitSpqrT3.prepare_chains_capacity_copies
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
def keepChain (current : U64) (p : U64 × tacenta_spqr.Chains) : Bool :=
  decide (current.val < (core.num.U64.saturating_add p.1 tacenta_spqr.EPOCHS_KEPT).val)


/-- The guard of the skipped-key scan in `clear_old_epochs`, as a Boolean on a skipped entry. -/
def keepSkipped (current : U64) (s : tacenta_spqr.Skipped) : Bool :=
  decide (current.val < (core.num.U64.saturating_add s.epoch tacenta_spqr.EPOCHS_KEPT).val)


theorem clear_chains_loop0_val (hZ : Tacenta.UnitSpqrT1.ZeroizeTotal) (hA : LawAsMut)
    (hP : LawPop) (st : tacenta_spqr.State) (current : U64) (i : Usize) :
    tacenta_spqr.State.clear_old_epochs_loop0 st current i ⦃ fun r =>
      r.1 = st.rk ∧ r.2.1 = st.epoch ∧ r.2.2.2.1 = st.skipped ∧ r.2.2.2.2 = st.direction ∧
      r.2.2.1.val = st.chains.val.take i.val ++
        (st.chains.val.drop i.val).filter (keepChain current) ⦄ := by
  unfold tacenta_spqr.State.clear_old_epochs_loop0
  apply loop.spec_decr_nat
    (measure := fun p => p.1.chains.length - p.2.val)
    (inv := fun p => p.1.rk = st.rk ∧ p.1.epoch = st.epoch ∧ p.1.skipped = st.skipped ∧
      p.1.direction = st.direction ∧
      p.1.chains.val.take p.2.val ++ (p.1.chains.val.drop p.2.val).filter (keepChain current)
      = st.chains.val.take i.val ++ (st.chains.val.drop i.val).filter (keepChain current))
  · rintro ⟨self, j⟩ ⟨hrk, hep, hsk, hdir, hL⟩
    simp only at hrk hep hsk hdir hL
    simp only [tacenta_spqr.State.clear_old_epochs_loop0.body]
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


theorem clear_skipped_loop1_val (hZ : Tacenta.UnitSpqrT1.ZeroizeTotal)
    (hP : LawPop) (v0 : alloc.vec.Vec tacenta_spqr.Skipped) (current : U64) (i : Usize) :
    tacenta_spqr.State.clear_old_epochs_loop1 v0 current i ⦃ fun r =>
      r.val = v0.val.take i.val ++ (v0.val.drop i.val).filter (keepSkipped current) ⦄ := by
  unfold tacenta_spqr.State.clear_old_epochs_loop1
  apply loop.spec_decr_nat
    (measure := fun p => p.1.length - p.2.val)
    (inv := fun p => p.1.val.take p.2.val ++ (p.1.val.drop p.2.val).filter (keepSkipped current)
      = v0.val.take i.val ++ (v0.val.drop i.val).filter (keepSkipped current))
  · rintro ⟨v, j⟩ hinv
    simp only at hinv
    simp only [tacenta_spqr.State.clear_old_epochs_loop1.body]
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


theorem clear_old_epochs_val (hZ : Tacenta.UnitSpqrT1.ZeroizeTotal) (hA : LawAsMut)
    (hP : LawPop) (st : tacenta_spqr.State) (current : U64) :
    tacenta_spqr.State.clear_old_epochs st current ⦃ fun r =>
      r.rk = st.rk ∧ r.epoch = st.epoch ∧ r.direction = st.direction ∧
      r.chains.val = st.chains.val.filter (keepChain current) ∧
      r.skipped.val = st.skipped.val.filter (keepSkipped current) ⦄ := by
  unfold tacenta_spqr.State.clear_old_epochs
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
    tacenta_spqr.EPOCHS_KEPT.val = Model.SparseRatchet.epochsKept := by
  unfold Model.SparseRatchet.epochsKept
  simp only [global_simps]
  rfl


theorem sat_val (x : U64) (hx : x.val + Model.SparseRatchet.epochsKept ≤ Std.U64.max) :
    (core.num.U64.saturating_add x tacenta_spqr.EPOCHS_KEPT).val
      = x.val + Model.SparseRatchet.epochsKept := by
  show (UScalar.saturating_add x tacenta_spqr.EPOCHS_KEPT).val = _
  rw [Tacenta.UnitSpqrT3.saturating_add_val, epochs_kept_val]
  omega


/-- `RemoveSkippedAtAgrees`, from the array zeroize law and the pop law. -/
theorem removeSkippedAtAgrees (hZ : Tacenta.UnitSpqrT1.ZeroizeTotal) (hP : LawPop) :
    Tacenta.UnitSpqrT3.RemoveSkippedAtAgrees := by
  intro v i h
  obtain ⟨r, hr, hk, hv⟩ := Std.WP.spec_imp_exists (spqr_remove_skipped_at_spec hZ hP v i h)
  exact ⟨r, hr, hk, hv⟩


theorem setChainsAgrees (hret : Tacenta.UnitSpqrT1.VecRetainTotal) (hZ : Tacenta.UnitSpqrT1.ZeroizeTotal)
    (hA : LawAsMut) (hP : LawPop) :
    ∀ {s : tacenta_spqr.State} {m : Model.SparseRatchet.State}
      (_hrel : Tacenta.UnitSpqrT3.StateRefines s m) (e : Std.U64) (c : tacenta_spqr.Chains)
      (_hroom : s.chains.val.length < Usize.max),
    ∃ r, tacenta_spqr.State.set_chains s e c = ok r ∧
      Tacenta.UnitSpqrT3.StateRefines r (Model.SparseRatchet.setChains m e.val (Tacenta.UnitSpqrT3.chainsOf c)) := by
  intro s m hrel e c hroom
  obtain ⟨r, hr, hrk, hep, hsk, hdir, hch⟩ :=
    Std.WP.spec_imp_exists (set_chains_val hret hZ hA hP s e c hroom)
  refine ⟨r, hr, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hrk]; exact hrel.rk
  · rw [hep]; exact hrel.epoch
  · have hm : (Model.SparseRatchet.setChains m e.val (Tacenta.UnitSpqrT3.chainsOf c)).chains
        = (m.chains.filter (fun p => !(p.1 == e.val))) ++ [(e.val, Tacenta.UnitSpqrT3.chainsOf c)] :=
      rfl
    show r.chains.val.map Tacenta.UnitSpqrT3.chainsEntryOf = _
    rw [hm, ← hrel.chains, hch, List.map_append, List.filter_map]
    rfl
  · rw [hsk]; exact hrel.skipped
  · rw [hdir]; exact hrel.direction


theorem clearOldEpochsAgrees (hZ : Tacenta.UnitSpqrT1.ZeroizeTotal) (hA : LawAsMut) (hP : LawPop) :
    ∀ {s : tacenta_spqr.State} {m : Model.SparseRatchet.State}
      (_hrel : Tacenta.UnitSpqrT3.StateRefines s m) (current : Std.U64)
      (_hcb : ∀ p ∈ s.chains.val,
        p.1.val + Model.SparseRatchet.epochsKept ≤ Std.U64.max)
      (_hsb : ∀ sk ∈ s.skipped.val,
        sk.epoch.val + Model.SparseRatchet.epochsKept ≤ Std.U64.max),
    ∃ r, tacenta_spqr.State.clear_old_epochs s current = ok r ∧
      Tacenta.UnitSpqrT3.StateRefines r (Model.SparseRatchet.clearOldEpochs m current.val) := by
  intro s m hrel current hcb hsb
  obtain ⟨r, hr, hrk, hep, hdir, hch, hsk⟩ :=
    Std.WP.spec_imp_exists (clear_old_epochs_val hZ hA hP s current)
  refine ⟨r, hr, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hrk]; exact hrel.rk
  · rw [hep]; exact hrel.epoch
  · have hm : (Model.SparseRatchet.clearOldEpochs m current.val).chains
        = m.chains.filter (fun p => decide (current.val < p.1 + Model.SparseRatchet.epochsKept)) :=
      rfl
    show r.chains.val.map Tacenta.UnitSpqrT3.chainsEntryOf = _
    rw [hm, ← hrel.chains, hch, List.filter_map]
    congr 1
    apply List.filter_congr
    intro p hp
    unfold keepChain
    simp [Function.comp, Tacenta.UnitSpqrT3.chainsEntryOf, sat_val p.1 (hcb p hp)]
  · have hm : (Model.SparseRatchet.clearOldEpochs m current.val).skipped
        = m.skipped.filter (fun x => decide (current.val < x.1 + Model.SparseRatchet.epochsKept)) :=
      rfl
    show r.skipped.val.map Tacenta.UnitSpqrT3.skippedOf = _
    rw [hm, ← hrel.skipped, hsk, List.filter_map]
    congr 1
    apply List.filter_congr
    intro p hp
    unfold keepSkipped
    simp [Function.comp, Tacenta.UnitSpqrT3.skippedOf, sat_val p.epoch (hsb p hp)]
  · rw [hdir]; exact hrel.direction


/-- **`VecRetainAgrees`**, proved from exactly the five laws it uses: `LawCapacity`, `LawVecZeroize`,
the array `Zeroize` law (`SpqrT1.ZeroizeTotal`), `LawAsMut` and `LawPop`.  The two chain-table scans,
the skipped-key scan and the capacity copy are proved from the translated bodies.  This form takes
the laws one by one so that its axiom footprint is only the constants those laws are about (plus
`Pair.Insts.ZeroizeZeroize.zeroize`, which occurs in the statement through
`State.prepare_chains_capacity` and is never used). -/
theorem vecRetainAgreesOfLaws (hCap : LawCapacity) (hVZ : LawVecZeroize)
    (hZ : Tacenta.UnitSpqrT1.ZeroizeTotal) (hA : LawAsMut) (hP : LawPop) :
    Tacenta.UnitSpqrT3.VecRetainAgrees :=
  ⟨setChainsAgrees (vecRetainTotal hCap hVZ hZ hA hP) hZ hA hP,
   clearOldEpochsAgrees hZ hA hP⟩


/-- **`VecRetainAgrees`**, from the bundle of laws.  Its `#print axioms` also lists the constants the
other fields of `Laws` are about (`hkdf_sha256`, `Zeroizing`), because they occur in the type of `L`;
the proof does not use them (see `vecRetainAgreesOfLaws`). -/
theorem vecRetainAgrees (L : Laws) : Tacenta.UnitSpqrT3.VecRetainAgrees :=
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

/-- The six defined-function hypotheses of the Triple-unit theorems follow from the
axiom-level hypotheses those theorems also take (`ZeroizeTotal`, `SpqrHkdfAgrees`, the two round
trips) and the four laws above. -/
theorem defined_hyps_from_axiom_hyps
    (hz : Tacenta.UnitSpqrT1.ZeroizeTotal) (hk : Tacenta.UnitSpqrT3.SpqrHkdfAgrees)
    (h96 : Tacenta.UnitSpqrT3.ZeroizingRoundTrips96) (h64 : Tacenta.UnitSpqrT3.ZeroizingRoundTrips64)
    (hcap : LawCapacity) (hvz : LawVecZeroize) (hpop : LawPop) (has : LawAsMut)
    (hblanket : LawBlanketU32) :
    Tacenta.UnitSpqrT1.RemoveSkippedAtTotal ∧ Tacenta.UnitSpqrT1.KdfRkTotal ∧
    Tacenta.UnitSpqrT1.KdfCkTotal ∧ Tacenta.UnitSpqrT1.VecRetainTotal ∧
    Tacenta.UnitT1.RemoveSkippedAtTotal ∧ Tacenta.UnitTripleT1.KdfInitTotal := by
  have L : Laws := ⟨hpop, has, hblanket, hcap, hvz, hz,
     fun N salt ikm info hN => by
       obtain ⟨r, hr, -⟩ := hk N salt ikm info hN
       exact ⟨r, hr⟩,
     fun z => h96 (arrInst 96#usize) z, fun z => h64 (arrInst 64#usize) z⟩
  obtain ⟨a, b, c, d, e, f⟩ := defined_fields_hold L
  exact ⟨b, c, d, f, a, e⟩



abbrev BlanketFn := {Z : Type} → zeroize.DefaultIsZeroes Z → Z → Result Z

def BlanketU32Shape (f : BlanketFn) : Prop :=
  ∀ x : U32, ∃ r, f U32.Insts.ZeroizeDefaultIsZeroes x = ok r

theorem LawBlanketU32_is :
    LawBlanketU32 ↔ BlanketU32Shape @zeroize.Zeroize.Blanket.zeroize := Iff.rfl

theorem blanket_satisfiable : ∃ f : BlanketFn, BlanketU32Shape f :=
  ⟨fun _ x => ok x, fun x => ⟨x, rfl⟩⟩


/-! ## The nine laws are jointly satisfiable

One structure over arbitrary functions of the constants' types, with the width-polymorphic wrapper
round trip and the HKDF totality in their general (every instance) form, which implies the specific
instances `Laws` uses.  One assignment satisfies all nine at once, and the same assignment serves the
whole unit because the classical and sparse ratchets share these constants here. -/

abbrev ZNewFn (W : Type → Type) := {Z : Type} → zeroize.Zeroize Z → Z → Result (W Z)
abbrev ZDerefFn (W : Type → Type) := {Z : Type} → zeroize.Zeroize Z → W Z → Result Z
abbrev HkdfFn := (N : Usize) → Slice U8 → Slice U8 → Slice U8 → Result (Std.Array U8 N)

structure LawsShape (pop : PopFn) (asMut : AsMutFn) (blanket : BlanketFn) (cap : CapacityFn)
    (vz : VecZeroizeFn)
    (arrZ : {Z : Type} → {N : Usize} → zeroize.Zeroize Z → Std.Array Z N → Result (Std.Array Z N))
    (hkdf : HkdfFn) {W : Type → Type} (new : ZNewFn W) (deref : ZDerefFn W) : Prop where
  pop_ : PopShape pop
  asMut_ : AsMutShape asMut
  blanket_ : BlanketU32Shape blanket
  cap_ : CapacityShape cap
  vz_ : VecZeroizeShape vz
  arrZ_ : ∀ {Z : Type} {N : Usize} (inst : zeroize.Zeroize Z) (a : Std.Array Z N), ∃ r, arrZ inst a = ok r
  hkdf_ : ∀ (N : Usize) (salt ikm info : Slice U8), N.val ≤ 8160 → ∃ r, hkdf N salt ikm info = ok r
  z96 : ∀ (inst : zeroize.Zeroize (Std.Array U8 96#usize)) (z : Std.Array U8 96#usize),
    ∃ w, new inst z = ok w ∧ deref inst w = ok z
  z64 : ∀ (inst : zeroize.Zeroize (Std.Array U8 64#usize)) (z : Std.Array U8 64#usize),
    ∃ w, new inst z = ok w ∧ deref inst w = ok z

theorem laws_jointly_satisfiable :
    ∃ (pop : PopFn) (asMut : AsMutFn) (blanket : BlanketFn) (cap : CapacityFn) (vz : VecZeroizeFn)
      (arrZ : {Z : Type} → {N : Usize} → zeroize.Zeroize Z → Std.Array Z N → Result (Std.Array Z N))
      (hkdf : HkdfFn) (W : Type → Type) (new : ZNewFn W) (deref : ZDerefFn W),
      LawsShape pop asMut blanket cap vz arrZ hkdf new deref :=
  ⟨@popWitness, fun o => ok (o, id), fun _ x => ok x, fun _ _ => ok 0#usize, fun _ v => ok v,
   fun _ a => ok a, fun N _ _ _ => ok (Std.Array.repeat N 0#u8), fun Z => Z, fun _ z => ok z,
   fun _ w => ok w,
   ⟨fun _ _ _ => ⟨_, _, rfl, rfl⟩, fun _ _ => ⟨_, rfl⟩, fun x => ⟨x, rfl⟩, fun _ _ => ⟨_, rfl⟩,
    fun _ v => ⟨v, rfl⟩, fun _ a => ⟨a, rfl⟩, fun N _ _ _ _ => ⟨_, rfl⟩, fun _ z => ⟨z, rfl, rfl⟩,
    fun _ z => ⟨z, rfl, rfl⟩⟩⟩

/-! ## Hypotheses with no witness in `UnitSatisfiabilityTriple.lean` -/

/-- Shape of `UnitT3.ZeroizingRoundTrips80`: the round trip and the total projection, at eighty bytes. -/
def RoundTrips80Shape {W : Type → Type}
    (new : {Z : Type} → zeroize.Zeroize Z → Z → Result (W Z))
    (deref : {Z : Type} → zeroize.Zeroize Z → W Z → Result Z) : Prop :=
  ∀ inst : zeroize.Zeroize (Array U8 80#usize),
    (∀ z, ∃ w, new inst z = ok w ∧ deref inst w = ok z) ∧ (∀ w, ∃ z, deref inst w = ok z)

theorem RoundTrips80_is :
    Tacenta.UnitT3.ZeroizingRoundTrips80 ↔
      RoundTrips80Shape (W := zeroize.Zeroizing) @zeroize.Zeroizing.new
        @zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref := Iff.rfl

theorem roundTrips80_satisfiable :
    ∃ (W : Type → Type) (new : {Z : Type} → zeroize.Zeroize Z → Z → Result (W Z))
      (deref : {Z : Type} → zeroize.Zeroize Z → W Z → Result Z), RoundTrips80Shape new deref :=
  ⟨fun Z => Z, fun _ z => ok z, fun _ w => ok w,
    fun _ => ⟨fun z => ⟨z, rfl, rfl⟩, fun w => ⟨w, rfl⟩⟩⟩

/-- Shape of `UnitTripleT3.ZeroizeTotal`: the wipe returns at the one byte instance and width. -/
def ArrZ32Shape (f : {Z : Type} → {N : Usize} → zeroize.Zeroize Z → Array Z N → Result (Array Z N)) : Prop :=
  ∀ a : Array U8 32#usize,
    ∃ r, f (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes) a = ok r

theorem TripleZeroizeTotal_is :
    Tacenta.UnitTripleT3.ZeroizeTotal ↔ ArrZ32Shape @Array.Insts.ZeroizeZeroize.zeroize := Iff.rfl

theorem arrZ32_satisfiable :
    ∃ f : {Z : Type} → {N : Usize} → zeroize.Zeroize Z → Array Z N → Result (Array Z N), ArrZ32Shape f :=
  ⟨fun _ a => ok a, fun a => ⟨a, rfl⟩⟩

/-- The scoped wipe follows from the general one. -/
theorem arrZ32_of_general (h : Tacenta.UnitSpqrT1.ZeroizeTotal) : Tacenta.UnitTripleT3.ZeroizeTotal :=
  fun a => h (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes) a
/-- The assignment above is a statement of the same form about the real constants: if the real
constants satisfied `LawsShape`, then `Laws` holds. `laws_jointly_satisfiable` shows `LawsShape`
is satisfiable by some functions, so the laws of `Laws` do not conflict with one another. The premise is
false of the real constants, because `LawsShape` contains the array and vector wipes for every instance
record, so this theorem is a statement about consistency, not a route to `Laws` for the real functions. -/
theorem laws_of_shape
    (h : LawsShape @alloc.vec.Vec.pop @core.option.Option.as_mut @zeroize.Zeroize.Blanket.zeroize
      @alloc.vec.Vec.capacity @alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize
      @Array.Insts.ZeroizeZeroize.zeroize tacenta_kdf.hkdf_sha256 (W := zeroize.Zeroizing)
      @zeroize.Zeroizing.new @zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref) : Laws :=
  ⟨h.pop_, h.asMut_, h.blanket_, h.cap_, h.vz_, h.arrZ_, h.hkdf_,
    fun z => h.z96 (arrInst 96#usize) z, fun z => h.z64 (arrInst 64#usize) z⟩

/-- The HKDF totality shape over an arbitrary function. -/
def HkdfTotalShape (f : HkdfFn) : Prop :=
  ∀ (N : Usize) (salt ikm info : Slice U8), N.val ≤ 8160 → ∃ r, f N salt ikm info = ok r

theorem LawHkdf_is : LawHkdf ↔ HkdfTotalShape tacenta_kdf.hkdf_sha256 := Iff.rfl

theorem hkdf_total_satisfiable : ∃ f : HkdfFn, HkdfTotalShape f :=
  ⟨fun N _ _ _ => ok (Std.Array.repeat N 0#u8), fun _ _ _ _ _ => ⟨_, rfl⟩⟩

/-- What the real `Array::zeroize` does with a failing element (it calls `inst.zeroize` on each
element and propagates the failure). -/
def PropagatesFailure : Prop :=
  ∀ {Z : Type} (inst : zeroize.Zeroize Z) (a : Std.Array Z 1#usize) (x : Z), a.val = [x] →
    inst.zeroize x = fail Error.panic → Array.Insts.ZeroizeZeroize.zeroize inst a = fail Error.panic

/-- `UnitSpqrT1.ZeroizeTotal` quantifies over every `Zeroize` record, so it cannot hold of a function
that propagates the failure of a failing record: it is consistent (`UnitSatisfiabilityTriple.lean`
witnesses it) and stronger than the crate. -/
theorem spqrZeroizeTotal_conflicts (h : Tacenta.UnitSpqrT1.ZeroizeTotal) (hp : PropagatesFailure) :
    False := by
  obtain ⟨r, hr⟩ := @h Unit 1#usize ⟨fun _ => fail Error.panic⟩ ⟨[()], rfl⟩
  have := hp (Z := Unit) ⟨fun _ => fail Error.panic⟩ ⟨[()], rfl⟩ () rfl rfl
  rw [this] at hr
  cases hr

/-- What the real `Vec::zeroize` does with a failing element (it calls `inst.zeroize` on each element and
propagates the failure). -/
def PropagatesFailureVec : Prop :=
  ∀ {Z : Type} (inst : zeroize.Zeroize Z) (v : alloc.vec.Vec Z) (x : Z), v.val = [x] →
    inst.zeroize x = fail Error.panic →
    alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize inst v = fail Error.panic

/-- `LawVecZeroize` quantifies over every `Zeroize` record, so it cannot hold of a function that
propagates the failure of a failing record: it is consistent and stronger than the crate. -/
theorem vec_zeroize_conflicts (h : LawVecZeroize) (hp : PropagatesFailureVec) : False := by
  obtain ⟨r, hr⟩ := @h Unit ⟨fun _ => fail Error.panic⟩ ⟨[()], by simp; scalar_tac⟩
  have := hp (Z := Unit) ⟨fun _ => fail Error.panic⟩ ⟨[()], by simp; scalar_tac⟩ () rfl rfl
  rw [this] at hr
  cases hr

end Tacenta.UnitSatisfiabilityTripleLaws

end

/--
info: 'Tacenta.UnitSatisfiabilityTripleLaws.kdfRkTotal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_kdf.hkdf_sha256,
 zeroize.Zeroizing,
 zeroize.Zeroizing.new,
 Array.Insts.ZeroizeZeroize.zeroize,
 zeroize.Zeroize.Blanket.zeroize,
 zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref]
-/
#guard_msgs in
#print axioms Tacenta.UnitSatisfiabilityTripleLaws.kdfRkTotal

/--
info: Tacenta.UnitSatisfiabilityTripleLaws.kdfRkTotal (hH : Tacenta.UnitSatisfiabilityTripleLaws.LawHkdf)
  (hZ : Tacenta.UnitSatisfiabilityTripleLaws.LawZeroizing 96#usize) : Tacenta.UnitSpqrT1.KdfRkTotal
-/
#guard_msgs in
#check Tacenta.UnitSatisfiabilityTripleLaws.kdfRkTotal

/--
info: 'Tacenta.UnitSatisfiabilityTripleLaws.kdfCkTotal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_kdf.hkdf_sha256,
 zeroize.Zeroizing,
 zeroize.Zeroizing.new,
 Array.Insts.ZeroizeZeroize.zeroize,
 zeroize.Zeroize.Blanket.zeroize,
 zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref]
-/
#guard_msgs in
#print axioms Tacenta.UnitSatisfiabilityTripleLaws.kdfCkTotal

/--
info: Tacenta.UnitSatisfiabilityTripleLaws.kdfCkTotal (hH : Tacenta.UnitSatisfiabilityTripleLaws.LawHkdf)
  (hZ : Tacenta.UnitSatisfiabilityTripleLaws.LawZeroizing 64#usize) : Tacenta.UnitSpqrT1.KdfCkTotal
-/
#guard_msgs in
#check Tacenta.UnitSatisfiabilityTripleLaws.kdfCkTotal

/--
info: 'Tacenta.UnitSatisfiabilityTripleLaws.kdfInitTotal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_kdf.hkdf_sha256,
 zeroize.Zeroizing,
 zeroize.Zeroizing.new,
 Array.Insts.ZeroizeZeroize.zeroize,
 zeroize.Zeroize.Blanket.zeroize,
 zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref]
-/
#guard_msgs in
#print axioms Tacenta.UnitSatisfiabilityTripleLaws.kdfInitTotal

/--
info: Tacenta.UnitSatisfiabilityTripleLaws.kdfInitTotal (hH : Tacenta.UnitSatisfiabilityTripleLaws.LawHkdf)
  (hZ : Tacenta.UnitSatisfiabilityTripleLaws.LawZeroizing 96#usize) : Tacenta.UnitTripleT1.KdfInitTotal
-/
#guard_msgs in
#check Tacenta.UnitSatisfiabilityTripleLaws.kdfInitTotal

/--
info: 'Tacenta.UnitSatisfiabilityTripleLaws.spqrRemoveSkippedAtTotal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Array.Insts.ZeroizeZeroize.zeroize,
 alloc.vec.Vec.pop,
 zeroize.Zeroize.Blanket.zeroize]
-/
#guard_msgs in
#print axioms Tacenta.UnitSatisfiabilityTripleLaws.spqrRemoveSkippedAtTotal

/--
info: Tacenta.UnitSatisfiabilityTripleLaws.spqrRemoveSkippedAtTotal (hZ : Tacenta.UnitSpqrT1.ZeroizeTotal)
  (hP : Tacenta.UnitSatisfiabilityTripleLaws.LawPop) : Tacenta.UnitSpqrT1.RemoveSkippedAtTotal
-/
#guard_msgs in
#check Tacenta.UnitSatisfiabilityTripleLaws.spqrRemoveSkippedAtTotal

/--
info: 'Tacenta.UnitSatisfiabilityTripleLaws.ratchetRemoveSkippedAtTotal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Array.Insts.ZeroizeZeroize.zeroize,
 alloc.vec.Vec.pop,
 zeroize.Zeroize.Blanket.zeroize]
-/
#guard_msgs in
#print axioms Tacenta.UnitSatisfiabilityTripleLaws.ratchetRemoveSkippedAtTotal

/--
info: Tacenta.UnitSatisfiabilityTripleLaws.ratchetRemoveSkippedAtTotal (hZ : Tacenta.UnitSpqrT1.ZeroizeTotal)
  (hB : Tacenta.UnitSatisfiabilityTripleLaws.LawBlanketU32) (hP : Tacenta.UnitSatisfiabilityTripleLaws.LawPop) :
  Tacenta.UnitT1.RemoveSkippedAtTotal
-/
#guard_msgs in
#check Tacenta.UnitSatisfiabilityTripleLaws.ratchetRemoveSkippedAtTotal

/--
info: 'Tacenta.UnitSatisfiabilityTripleLaws.setChainsLoopTotal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Array.Insts.ZeroizeZeroize.zeroize,
 alloc.vec.Vec.pop,
 core.option.Option.as_mut,
 zeroize.Zeroize.Blanket.zeroize]
-/
#guard_msgs in
#print axioms Tacenta.UnitSatisfiabilityTripleLaws.setChainsLoopTotal

/--
info: Tacenta.UnitSatisfiabilityTripleLaws.setChainsLoopTotal (hZ : Tacenta.UnitSpqrT1.ZeroizeTotal)
  (hA : Tacenta.UnitSatisfiabilityTripleLaws.LawAsMut) (hP : Tacenta.UnitSatisfiabilityTripleLaws.LawPop) :
  Tacenta.UnitSpqrT1.SetChainsLoopTotal
-/
#guard_msgs in
#check Tacenta.UnitSatisfiabilityTripleLaws.setChainsLoopTotal

/--
info: 'Tacenta.UnitSatisfiabilityTripleLaws.clearChainsLoop0Total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Array.Insts.ZeroizeZeroize.zeroize,
 alloc.vec.Vec.pop,
 core.option.Option.as_mut,
 zeroize.Zeroize.Blanket.zeroize]
-/
#guard_msgs in
#print axioms Tacenta.UnitSatisfiabilityTripleLaws.clearChainsLoop0Total

/--
info: Tacenta.UnitSatisfiabilityTripleLaws.clearChainsLoop0Total (hZ : Tacenta.UnitSpqrT1.ZeroizeTotal)
  (hA : Tacenta.UnitSatisfiabilityTripleLaws.LawAsMut) (hP : Tacenta.UnitSatisfiabilityTripleLaws.LawPop) :
  Tacenta.UnitSpqrT1.ClearChainsLoop0Total
-/
#guard_msgs in
#check Tacenta.UnitSatisfiabilityTripleLaws.clearChainsLoop0Total

/--
info: 'Tacenta.UnitSatisfiabilityTripleLaws.clearSkippedLoopTotal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Array.Insts.ZeroizeZeroize.zeroize,
 alloc.vec.Vec.pop,
 zeroize.Zeroize.Blanket.zeroize]
-/
#guard_msgs in
#print axioms Tacenta.UnitSatisfiabilityTripleLaws.clearSkippedLoopTotal

/--
info: Tacenta.UnitSatisfiabilityTripleLaws.clearSkippedLoopTotal (hZ : Tacenta.UnitSpqrT1.ZeroizeTotal)
  (hP : Tacenta.UnitSatisfiabilityTripleLaws.LawPop) : Tacenta.UnitSpqrT1.ClearSkippedLoopTotal
-/
#guard_msgs in
#check Tacenta.UnitSatisfiabilityTripleLaws.clearSkippedLoopTotal

/--
info: 'Tacenta.UnitSatisfiabilityTripleLaws.vecRetainTotal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Array.Insts.ZeroizeZeroize.zeroize,
 alloc.vec.Vec.capacity,
 alloc.vec.Vec.pop,
 core.option.Option.as_mut,
 zeroize.Zeroize.Blanket.zeroize,
 alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize]
-/
#guard_msgs in
#print axioms Tacenta.UnitSatisfiabilityTripleLaws.vecRetainTotal

/--
info: Tacenta.UnitSatisfiabilityTripleLaws.vecRetainTotal (hCap : Tacenta.UnitSatisfiabilityTripleLaws.LawCapacity)
  (hVZ : Tacenta.UnitSatisfiabilityTripleLaws.LawVecZeroize) (hZ : Tacenta.UnitSpqrT1.ZeroizeTotal)
  (hA : Tacenta.UnitSatisfiabilityTripleLaws.LawAsMut) (hP : Tacenta.UnitSatisfiabilityTripleLaws.LawPop) :
  Tacenta.UnitSpqrT1.VecRetainTotal
-/
#guard_msgs in
#check Tacenta.UnitSatisfiabilityTripleLaws.vecRetainTotal

/--
info: 'Tacenta.UnitSatisfiabilityTripleLaws.defined_fields_hold' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_kdf.hkdf_sha256,
 zeroize.Zeroizing,
 zeroize.Zeroizing.new,
 Array.Insts.ZeroizeZeroize.zeroize,
 alloc.vec.Vec.capacity,
 alloc.vec.Vec.pop,
 core.option.Option.as_mut,
 zeroize.Zeroize.Blanket.zeroize,
 zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize]
-/
#guard_msgs in
#print axioms Tacenta.UnitSatisfiabilityTripleLaws.defined_fields_hold

/--
info: Tacenta.UnitSatisfiabilityTripleLaws.defined_fields_hold (L : Tacenta.UnitSatisfiabilityTripleLaws.Laws) :
  Tacenta.UnitT1.RemoveSkippedAtTotal ∧
    Tacenta.UnitSpqrT1.RemoveSkippedAtTotal ∧
      Tacenta.UnitSpqrT1.KdfRkTotal ∧
        Tacenta.UnitSpqrT1.KdfCkTotal ∧ Tacenta.UnitTripleT1.KdfInitTotal ∧ Tacenta.UnitSpqrT1.VecRetainTotal
-/
#guard_msgs in
#check Tacenta.UnitSatisfiabilityTripleLaws.defined_fields_hold

/--
info: 'Tacenta.UnitSatisfiabilityTripleLaws.removeSkippedAtAgrees' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Array.Insts.ZeroizeZeroize.zeroize,
 alloc.vec.Vec.pop,
 zeroize.Zeroize.Blanket.zeroize]
-/
#guard_msgs in
#print axioms Tacenta.UnitSatisfiabilityTripleLaws.removeSkippedAtAgrees

/--
info: Tacenta.UnitSatisfiabilityTripleLaws.removeSkippedAtAgrees (hZ : Tacenta.UnitSpqrT1.ZeroizeTotal)
  (hP : Tacenta.UnitSatisfiabilityTripleLaws.LawPop) : Tacenta.UnitSpqrT3.RemoveSkippedAtAgrees
-/
#guard_msgs in
#check Tacenta.UnitSatisfiabilityTripleLaws.removeSkippedAtAgrees

/--
info: 'Tacenta.UnitSatisfiabilityTripleLaws.setChainsAgrees' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Array.Insts.ZeroizeZeroize.zeroize,
 Pair.Insts.ZeroizeZeroize.zeroize,
 alloc.vec.Vec.capacity,
 alloc.vec.Vec.pop,
 core.option.Option.as_mut,
 zeroize.Zeroize.Blanket.zeroize,
 alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize]
-/
#guard_msgs in
#print axioms Tacenta.UnitSatisfiabilityTripleLaws.setChainsAgrees

/--
info: Tacenta.UnitSatisfiabilityTripleLaws.setChainsAgrees (hret : Tacenta.UnitSpqrT1.VecRetainTotal)
  (hZ : Tacenta.UnitSpqrT1.ZeroizeTotal) (hA : Tacenta.UnitSatisfiabilityTripleLaws.LawAsMut)
  (hP : Tacenta.UnitSatisfiabilityTripleLaws.LawPop) {s : tacenta_spqr.State} {m : Model.SparseRatchet.State}
  (_hrel : Tacenta.UnitSpqrT3.StateRefines s m) (e : U64) (c : tacenta_spqr.Chains)
  (_hroom : (↑s.chains).length < Usize.max) :
  ∃ r,
    s.set_chains e c = ok r ∧
      Tacenta.UnitSpqrT3.StateRefines r (Model.SparseRatchet.setChains m (↑e) (Tacenta.UnitSpqrT3.chainsOf c))
-/
#guard_msgs in
#check Tacenta.UnitSatisfiabilityTripleLaws.setChainsAgrees

/--
info: 'Tacenta.UnitSatisfiabilityTripleLaws.clearOldEpochsAgrees' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Array.Insts.ZeroizeZeroize.zeroize,
 alloc.vec.Vec.pop,
 core.option.Option.as_mut,
 zeroize.Zeroize.Blanket.zeroize]
-/
#guard_msgs in
#print axioms Tacenta.UnitSatisfiabilityTripleLaws.clearOldEpochsAgrees

/--
info: Tacenta.UnitSatisfiabilityTripleLaws.clearOldEpochsAgrees (hZ : Tacenta.UnitSpqrT1.ZeroizeTotal)
  (hA : Tacenta.UnitSatisfiabilityTripleLaws.LawAsMut) (hP : Tacenta.UnitSatisfiabilityTripleLaws.LawPop)
  {s : tacenta_spqr.State} {m : Model.SparseRatchet.State} (_hrel : Tacenta.UnitSpqrT3.StateRefines s m) (current : U64)
  (_hcb : ∀ p ∈ ↑s.chains, ↑p.1 + Model.SparseRatchet.epochsKept ≤ U64.max)
  (_hsb : ∀ sk ∈ ↑s.skipped, ↑sk.epoch + Model.SparseRatchet.epochsKept ≤ U64.max) :
  ∃ r,
    s.clear_old_epochs current = ok r ∧
      Tacenta.UnitSpqrT3.StateRefines r (Model.SparseRatchet.clearOldEpochs m ↑current)
-/
#guard_msgs in
#check Tacenta.UnitSatisfiabilityTripleLaws.clearOldEpochsAgrees

/--
info: 'Tacenta.UnitSatisfiabilityTripleLaws.vecRetainAgreesOfLaws' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Array.Insts.ZeroizeZeroize.zeroize,
 Pair.Insts.ZeroizeZeroize.zeroize,
 alloc.vec.Vec.capacity,
 alloc.vec.Vec.pop,
 core.option.Option.as_mut,
 zeroize.Zeroize.Blanket.zeroize,
 alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize]
-/
#guard_msgs in
#print axioms Tacenta.UnitSatisfiabilityTripleLaws.vecRetainAgreesOfLaws

/--
info: Tacenta.UnitSatisfiabilityTripleLaws.vecRetainAgreesOfLaws (hCap : Tacenta.UnitSatisfiabilityTripleLaws.LawCapacity)
  (hVZ : Tacenta.UnitSatisfiabilityTripleLaws.LawVecZeroize) (hZ : Tacenta.UnitSpqrT1.ZeroizeTotal)
  (hA : Tacenta.UnitSatisfiabilityTripleLaws.LawAsMut) (hP : Tacenta.UnitSatisfiabilityTripleLaws.LawPop) :
  Tacenta.UnitSpqrT3.VecRetainAgrees
-/
#guard_msgs in
#check Tacenta.UnitSatisfiabilityTripleLaws.vecRetainAgreesOfLaws

/--
info: 'Tacenta.UnitSatisfiabilityTripleLaws.vecRetainAgrees' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_kdf.hkdf_sha256,
 zeroize.Zeroizing,
 zeroize.Zeroizing.new,
 Array.Insts.ZeroizeZeroize.zeroize,
 Pair.Insts.ZeroizeZeroize.zeroize,
 alloc.vec.Vec.capacity,
 alloc.vec.Vec.pop,
 core.option.Option.as_mut,
 zeroize.Zeroize.Blanket.zeroize,
 zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize]
-/
#guard_msgs in
#print axioms Tacenta.UnitSatisfiabilityTripleLaws.vecRetainAgrees

/--
info: Tacenta.UnitSatisfiabilityTripleLaws.vecRetainAgrees (L : Tacenta.UnitSatisfiabilityTripleLaws.Laws) :
  Tacenta.UnitSpqrT3.VecRetainAgrees
-/
#guard_msgs in
#check Tacenta.UnitSatisfiabilityTripleLaws.vecRetainAgrees

/--
info: 'Tacenta.UnitSatisfiabilityTripleLaws.LawPop_is' depends on axioms: [propext, alloc.vec.Vec.pop]
-/
#guard_msgs in
#print axioms Tacenta.UnitSatisfiabilityTripleLaws.LawPop_is

/--
info: Tacenta.UnitSatisfiabilityTripleLaws.LawPop_is :
  Tacenta.UnitSatisfiabilityTripleLaws.LawPop ↔ Tacenta.UnitSatisfiabilityTripleLaws.PopShape @alloc.vec.Vec.pop
-/
#guard_msgs in
#check Tacenta.UnitSatisfiabilityTripleLaws.LawPop_is

/--
info: 'Tacenta.UnitSatisfiabilityTripleLaws.LawAsMut_is' depends on axioms: [core.option.Option.as_mut]
-/
#guard_msgs in
#print axioms Tacenta.UnitSatisfiabilityTripleLaws.LawAsMut_is

/--
info: Tacenta.UnitSatisfiabilityTripleLaws.LawAsMut_is :
  Tacenta.UnitSatisfiabilityTripleLaws.LawAsMut ↔
    Tacenta.UnitSatisfiabilityTripleLaws.AsMutShape @core.option.Option.as_mut
-/
#guard_msgs in
#check Tacenta.UnitSatisfiabilityTripleLaws.LawAsMut_is

/--
info: 'Tacenta.UnitSatisfiabilityTripleLaws.LawCapacity_is' depends on axioms: [propext, alloc.vec.Vec.capacity]
-/
#guard_msgs in
#print axioms Tacenta.UnitSatisfiabilityTripleLaws.LawCapacity_is

/--
info: Tacenta.UnitSatisfiabilityTripleLaws.LawCapacity_is :
  Tacenta.UnitSatisfiabilityTripleLaws.LawCapacity ↔
    Tacenta.UnitSatisfiabilityTripleLaws.CapacityShape @alloc.vec.Vec.capacity
-/
#guard_msgs in
#check Tacenta.UnitSatisfiabilityTripleLaws.LawCapacity_is

/--
info: 'Tacenta.UnitSatisfiabilityTripleLaws.LawVecZeroize_is' depends on axioms: [propext,
 alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize]
-/
#guard_msgs in
#print axioms Tacenta.UnitSatisfiabilityTripleLaws.LawVecZeroize_is

/--
info: Tacenta.UnitSatisfiabilityTripleLaws.LawVecZeroize_is :
  Tacenta.UnitSatisfiabilityTripleLaws.LawVecZeroize ↔
    Tacenta.UnitSatisfiabilityTripleLaws.VecZeroizeShape @alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize
-/
#guard_msgs in
#check Tacenta.UnitSatisfiabilityTripleLaws.LawVecZeroize_is

/--
info: 'Tacenta.UnitSatisfiabilityTripleLaws.LawBlanketU32_is' depends on axioms: [propext, zeroize.Zeroize.Blanket.zeroize]
-/
#guard_msgs in
#print axioms Tacenta.UnitSatisfiabilityTripleLaws.LawBlanketU32_is

/--
info: Tacenta.UnitSatisfiabilityTripleLaws.LawBlanketU32_is :
  Tacenta.UnitSatisfiabilityTripleLaws.LawBlanketU32 ↔
    Tacenta.UnitSatisfiabilityTripleLaws.BlanketU32Shape @zeroize.Zeroize.Blanket.zeroize
-/
#guard_msgs in
#check Tacenta.UnitSatisfiabilityTripleLaws.LawBlanketU32_is

/--
info: 'Tacenta.UnitSatisfiabilityTripleLaws.LawHkdf_is' depends on axioms: [propext, tacenta_kdf.hkdf_sha256]
-/
#guard_msgs in
#print axioms Tacenta.UnitSatisfiabilityTripleLaws.LawHkdf_is

/--
info: Tacenta.UnitSatisfiabilityTripleLaws.LawHkdf_is :
  Tacenta.UnitSatisfiabilityTripleLaws.LawHkdf ↔
    Tacenta.UnitSatisfiabilityTripleLaws.HkdfTotalShape tacenta_kdf.hkdf_sha256
-/
#guard_msgs in
#check Tacenta.UnitSatisfiabilityTripleLaws.LawHkdf_is

/--
info: 'Tacenta.UnitSatisfiabilityTripleLaws.laws_jointly_satisfiable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitSatisfiabilityTripleLaws.laws_jointly_satisfiable

/--
info: Tacenta.UnitSatisfiabilityTripleLaws.laws_jointly_satisfiable :
  ∃ pop asMut blanket cap vz arrZ hkdf W new deref,
    Tacenta.UnitSatisfiabilityTripleLaws.LawsShape (fun {T} => pop) (fun {T} => asMut) (fun {Z} => blanket)
      (fun {T} => cap) (fun {Z} => vz) (fun {Z} {N} => arrZ) hkdf (fun {Z} => new) fun {Z} => deref
-/
#guard_msgs in
#check Tacenta.UnitSatisfiabilityTripleLaws.laws_jointly_satisfiable

/--
info: 'Tacenta.UnitSatisfiabilityTripleLaws.laws_of_shape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_kdf.hkdf_sha256,
 zeroize.Zeroizing,
 zeroize.Zeroizing.new,
 Array.Insts.ZeroizeZeroize.zeroize,
 alloc.vec.Vec.capacity,
 alloc.vec.Vec.pop,
 core.option.Option.as_mut,
 zeroize.Zeroize.Blanket.zeroize,
 zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize]
-/
#guard_msgs in
#print axioms Tacenta.UnitSatisfiabilityTripleLaws.laws_of_shape

/--
info: Tacenta.UnitSatisfiabilityTripleLaws.laws_of_shape
  (h :
    Tacenta.UnitSatisfiabilityTripleLaws.LawsShape (@alloc.vec.Vec.pop) (@core.option.Option.as_mut)
      (@zeroize.Zeroize.Blanket.zeroize) (@alloc.vec.Vec.capacity) (@alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize)
      (@Array.Insts.ZeroizeZeroize.zeroize) tacenta_kdf.hkdf_sha256 @zeroize.Zeroizing.new
      @zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref) :
  Tacenta.UnitSatisfiabilityTripleLaws.Laws
-/
#guard_msgs in
#check Tacenta.UnitSatisfiabilityTripleLaws.laws_of_shape

/--
info: 'Tacenta.UnitSatisfiabilityTripleLaws.defined_hyps_from_axiom_hyps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_kdf.hkdf_sha256,
 zeroize.Zeroizing,
 zeroize.Zeroizing.new,
 Array.Insts.ZeroizeZeroize.zeroize,
 alloc.vec.Vec.capacity,
 alloc.vec.Vec.pop,
 core.option.Option.as_mut,
 zeroize.Zeroize.Blanket.zeroize,
 zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize]
-/
#guard_msgs in
#print axioms Tacenta.UnitSatisfiabilityTripleLaws.defined_hyps_from_axiom_hyps

/--
info: Tacenta.UnitSatisfiabilityTripleLaws.defined_hyps_from_axiom_hyps (hz : Tacenta.UnitSpqrT1.ZeroizeTotal)
  (hk : Tacenta.UnitSpqrT3.SpqrHkdfAgrees) (h96 : Tacenta.UnitSpqrT3.ZeroizingRoundTrips96)
  (h64 : Tacenta.UnitSpqrT3.ZeroizingRoundTrips64) (hcap : Tacenta.UnitSatisfiabilityTripleLaws.LawCapacity)
  (hvz : Tacenta.UnitSatisfiabilityTripleLaws.LawVecZeroize) (hpop : Tacenta.UnitSatisfiabilityTripleLaws.LawPop)
  (has : Tacenta.UnitSatisfiabilityTripleLaws.LawAsMut)
  (hblanket : Tacenta.UnitSatisfiabilityTripleLaws.LawBlanketU32) :
  Tacenta.UnitSpqrT1.RemoveSkippedAtTotal ∧
    Tacenta.UnitSpqrT1.KdfRkTotal ∧
      Tacenta.UnitSpqrT1.KdfCkTotal ∧
        Tacenta.UnitSpqrT1.VecRetainTotal ∧ Tacenta.UnitT1.RemoveSkippedAtTotal ∧ Tacenta.UnitTripleT1.KdfInitTotal
-/
#guard_msgs in
#check Tacenta.UnitSatisfiabilityTripleLaws.defined_hyps_from_axiom_hyps

/--
info: 'Tacenta.UnitSatisfiabilityTripleLaws.RoundTrips80_is' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 zeroize.Zeroizing,
 zeroize.Zeroizing.new,
 zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref]
-/
#guard_msgs in
#print axioms Tacenta.UnitSatisfiabilityTripleLaws.RoundTrips80_is

/--
info: Tacenta.UnitSatisfiabilityTripleLaws.RoundTrips80_is :
  Tacenta.UnitT3.ZeroizingRoundTrips80 ↔
    Tacenta.UnitSatisfiabilityTripleLaws.RoundTrips80Shape @zeroize.Zeroizing.new
      @zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref
-/
#guard_msgs in
#check Tacenta.UnitSatisfiabilityTripleLaws.RoundTrips80_is

/--
info: 'Tacenta.UnitSatisfiabilityTripleLaws.roundTrips80_satisfiable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitSatisfiabilityTripleLaws.roundTrips80_satisfiable

/--
info: Tacenta.UnitSatisfiabilityTripleLaws.roundTrips80_satisfiable :
  ∃ W new deref, Tacenta.UnitSatisfiabilityTripleLaws.RoundTrips80Shape (fun {Z} => new) fun {Z} => deref
-/
#guard_msgs in
#check Tacenta.UnitSatisfiabilityTripleLaws.roundTrips80_satisfiable

/--
info: 'Tacenta.UnitSatisfiabilityTripleLaws.TripleZeroizeTotal_is' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Array.Insts.ZeroizeZeroize.zeroize,
 zeroize.Zeroize.Blanket.zeroize]
-/
#guard_msgs in
#print axioms Tacenta.UnitSatisfiabilityTripleLaws.TripleZeroizeTotal_is

/--
info: Tacenta.UnitSatisfiabilityTripleLaws.TripleZeroizeTotal_is :
  Tacenta.UnitTripleT3.ZeroizeTotal ↔
    Tacenta.UnitSatisfiabilityTripleLaws.ArrZ32Shape @Array.Insts.ZeroizeZeroize.zeroize
-/
#guard_msgs in
#check Tacenta.UnitSatisfiabilityTripleLaws.TripleZeroizeTotal_is

/--
info: 'Tacenta.UnitSatisfiabilityTripleLaws.arrZ32_satisfiable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 zeroize.Zeroize.Blanket.zeroize]
-/
#guard_msgs in
#print axioms Tacenta.UnitSatisfiabilityTripleLaws.arrZ32_satisfiable

/--
info: Tacenta.UnitSatisfiabilityTripleLaws.arrZ32_satisfiable :
  ∃ f, Tacenta.UnitSatisfiabilityTripleLaws.ArrZ32Shape fun {Z} {N} => f
-/
#guard_msgs in
#check Tacenta.UnitSatisfiabilityTripleLaws.arrZ32_satisfiable

/--
info: 'Tacenta.UnitSatisfiabilityTripleLaws.arrZ32_of_general' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Array.Insts.ZeroizeZeroize.zeroize,
 zeroize.Zeroize.Blanket.zeroize]
-/
#guard_msgs in
#print axioms Tacenta.UnitSatisfiabilityTripleLaws.arrZ32_of_general

/--
info: Tacenta.UnitSatisfiabilityTripleLaws.arrZ32_of_general (h : Tacenta.UnitSpqrT1.ZeroizeTotal) :
  Tacenta.UnitTripleT3.ZeroizeTotal
-/
#guard_msgs in
#check Tacenta.UnitSatisfiabilityTripleLaws.arrZ32_of_general

/--
info: 'Tacenta.UnitSatisfiabilityTripleLaws.spqrZeroizeTotal_conflicts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Array.Insts.ZeroizeZeroize.zeroize]
-/
#guard_msgs in
#print axioms Tacenta.UnitSatisfiabilityTripleLaws.spqrZeroizeTotal_conflicts

/--
info: Tacenta.UnitSatisfiabilityTripleLaws.spqrZeroizeTotal_conflicts (h : Tacenta.UnitSpqrT1.ZeroizeTotal)
  (hp : Tacenta.UnitSatisfiabilityTripleLaws.PropagatesFailure) : False
-/
#guard_msgs in
#check Tacenta.UnitSatisfiabilityTripleLaws.spqrZeroizeTotal_conflicts

/--
info: structure Tacenta.UnitSatisfiabilityTripleLaws.Laws : Prop
number of parameters: 0
fields:
  Tacenta.UnitSatisfiabilityTripleLaws.Laws.pop : Tacenta.UnitSatisfiabilityTripleLaws.LawPop
  Tacenta.UnitSatisfiabilityTripleLaws.Laws.asMut : Tacenta.UnitSatisfiabilityTripleLaws.LawAsMut
  Tacenta.UnitSatisfiabilityTripleLaws.Laws.blanketU32 : Tacenta.UnitSatisfiabilityTripleLaws.LawBlanketU32
  Tacenta.UnitSatisfiabilityTripleLaws.Laws.capacity : Tacenta.UnitSatisfiabilityTripleLaws.LawCapacity
  Tacenta.UnitSatisfiabilityTripleLaws.Laws.vecZeroize : Tacenta.UnitSatisfiabilityTripleLaws.LawVecZeroize
  Tacenta.UnitSatisfiabilityTripleLaws.Laws.arrayZeroize : Tacenta.UnitSpqrT1.ZeroizeTotal
  Tacenta.UnitSatisfiabilityTripleLaws.Laws.hkdf : Tacenta.UnitSatisfiabilityTripleLaws.LawHkdf
  Tacenta.UnitSatisfiabilityTripleLaws.Laws.zeroizing96 : Tacenta.UnitSatisfiabilityTripleLaws.LawZeroizing 96#usize
  Tacenta.UnitSatisfiabilityTripleLaws.Laws.zeroizing64 : Tacenta.UnitSatisfiabilityTripleLaws.LawZeroizing 64#usize
constructor:
  Tacenta.UnitSatisfiabilityTripleLaws.Laws.mk (pop : Tacenta.UnitSatisfiabilityTripleLaws.LawPop)
    (asMut : Tacenta.UnitSatisfiabilityTripleLaws.LawAsMut)
    (blanketU32 : Tacenta.UnitSatisfiabilityTripleLaws.LawBlanketU32)
    (capacity : Tacenta.UnitSatisfiabilityTripleLaws.LawCapacity)
    (vecZeroize : Tacenta.UnitSatisfiabilityTripleLaws.LawVecZeroize) (arrayZeroize : Tacenta.UnitSpqrT1.ZeroizeTotal)
    (hkdf : Tacenta.UnitSatisfiabilityTripleLaws.LawHkdf)
    (zeroizing96 : Tacenta.UnitSatisfiabilityTripleLaws.LawZeroizing 96#usize)
    (zeroizing64 : Tacenta.UnitSatisfiabilityTripleLaws.LawZeroizing 64#usize) :
    Tacenta.UnitSatisfiabilityTripleLaws.Laws
-/
#guard_msgs in
#print Tacenta.UnitSatisfiabilityTripleLaws.Laws

/--
info: structure Tacenta.UnitSatisfiabilityTripleLaws.LawsShape (pop : Tacenta.UnitSatisfiabilityTripleLaws.PopFn)
  (asMut : Tacenta.UnitSatisfiabilityTripleLaws.AsMutFn) (blanket : Tacenta.UnitSatisfiabilityTripleLaws.BlanketFn)
  (cap : Tacenta.UnitSatisfiabilityTripleLaws.CapacityFn) (vz : Tacenta.UnitSatisfiabilityTripleLaws.VecZeroizeFn)
  (arrZ : {Z : Type} → {N : Usize} → zeroize.Zeroize Z → Std.Array Z N → Result (Std.Array Z N))
  (hkdf : Tacenta.UnitSatisfiabilityTripleLaws.HkdfFn) {W : Type → Type}
  (new : Tacenta.UnitSatisfiabilityTripleLaws.ZNewFn W) (deref : Tacenta.UnitSatisfiabilityTripleLaws.ZDerefFn W) : Prop
number of parameters: 10
fields:
  Tacenta.UnitSatisfiabilityTripleLaws.LawsShape.pop_ : Tacenta.UnitSatisfiabilityTripleLaws.PopShape fun {T} => pop
  Tacenta.UnitSatisfiabilityTripleLaws.LawsShape.asMut_ : Tacenta.UnitSatisfiabilityTripleLaws.AsMutShape fun {T} =>
      asMut
  Tacenta.UnitSatisfiabilityTripleLaws.LawsShape.blanket_ : Tacenta.UnitSatisfiabilityTripleLaws.BlanketU32Shape
      fun {Z} => blanket
  Tacenta.UnitSatisfiabilityTripleLaws.LawsShape.cap_ : Tacenta.UnitSatisfiabilityTripleLaws.CapacityShape fun {T} =>
      cap
  Tacenta.UnitSatisfiabilityTripleLaws.LawsShape.vz_ : Tacenta.UnitSatisfiabilityTripleLaws.VecZeroizeShape fun {Z} =>
      vz
  Tacenta.UnitSatisfiabilityTripleLaws.LawsShape.arrZ_ : ∀ {Z : Type} {N : Usize} (inst : zeroize.Zeroize Z)
      (a : Std.Array Z N), ∃ r, arrZ inst a = ok r
  Tacenta.UnitSatisfiabilityTripleLaws.LawsShape.hkdf_ : ∀ (N : Usize) (salt ikm info : Slice U8),
      ↑N ≤ 8160 → ∃ r, hkdf N salt ikm info = ok r
  Tacenta.UnitSatisfiabilityTripleLaws.LawsShape.z96 : ∀ (inst : zeroize.Zeroize (Std.Array U8 96#usize))
      (z : Std.Array U8 96#usize), ∃ w, new inst z = ok w ∧ deref inst w = ok z
  Tacenta.UnitSatisfiabilityTripleLaws.LawsShape.z64 : ∀ (inst : zeroize.Zeroize (Std.Array U8 64#usize))
      (z : Std.Array U8 64#usize), ∃ w, new inst z = ok w ∧ deref inst w = ok z
constructor:
  Tacenta.UnitSatisfiabilityTripleLaws.LawsShape.mk {pop : Tacenta.UnitSatisfiabilityTripleLaws.PopFn}
    {asMut : Tacenta.UnitSatisfiabilityTripleLaws.AsMutFn} {blanket : Tacenta.UnitSatisfiabilityTripleLaws.BlanketFn}
    {cap : Tacenta.UnitSatisfiabilityTripleLaws.CapacityFn} {vz : Tacenta.UnitSatisfiabilityTripleLaws.VecZeroizeFn}
    {arrZ : {Z : Type} → {N : Usize} → zeroize.Zeroize Z → Std.Array Z N → Result (Std.Array Z N)}
    {hkdf : Tacenta.UnitSatisfiabilityTripleLaws.HkdfFn} {W : Type → Type}
    {new : Tacenta.UnitSatisfiabilityTripleLaws.ZNewFn W} {deref : Tacenta.UnitSatisfiabilityTripleLaws.ZDerefFn W}
    (pop_ : Tacenta.UnitSatisfiabilityTripleLaws.PopShape fun {T} => pop)
    (asMut_ : Tacenta.UnitSatisfiabilityTripleLaws.AsMutShape fun {T} => asMut)
    (blanket_ : Tacenta.UnitSatisfiabilityTripleLaws.BlanketU32Shape fun {Z} => blanket)
    (cap_ : Tacenta.UnitSatisfiabilityTripleLaws.CapacityShape fun {T} => cap)
    (vz_ : Tacenta.UnitSatisfiabilityTripleLaws.VecZeroizeShape fun {Z} => vz)
    (arrZ_ : ∀ {Z : Type} {N : Usize} (inst : zeroize.Zeroize Z) (a : Std.Array Z N), ∃ r, arrZ inst a = ok r)
    (hkdf_ : ∀ (N : Usize) (salt ikm info : Slice U8), ↑N ≤ 8160 → ∃ r, hkdf N salt ikm info = ok r)
    (z96 :
      ∀ (inst : zeroize.Zeroize (Std.Array U8 96#usize)) (z : Std.Array U8 96#usize),
        ∃ w, new inst z = ok w ∧ deref inst w = ok z)
    (z64 :
      ∀ (inst : zeroize.Zeroize (Std.Array U8 64#usize)) (z : Std.Array U8 64#usize),
        ∃ w, new inst z = ok w ∧ deref inst w = ok z) :
    Tacenta.UnitSatisfiabilityTripleLaws.LawsShape pop asMut blanket cap vz arrZ hkdf new deref
-/
#guard_msgs in
#print Tacenta.UnitSatisfiabilityTripleLaws.LawsShape

/--
info: def Tacenta.UnitSatisfiabilityTripleLaws.PropagatesFailure : Prop :=
∀ {Z : Type} (inst : zeroize.Zeroize Z) (a : Std.Array Z 1#usize) (x : Z),
  ↑a = [x] → inst.zeroize x = fail Error.panic → Array.Insts.ZeroizeZeroize.zeroize inst a = fail Error.panic
-/
#guard_msgs in
#print Tacenta.UnitSatisfiabilityTripleLaws.PropagatesFailure

/--
info: 'Tacenta.UnitSatisfiabilityTripleLaws.hkdf_total_satisfiable' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitSatisfiabilityTripleLaws.hkdf_total_satisfiable

/--
info: Tacenta.UnitSatisfiabilityTripleLaws.hkdf_total_satisfiable : ∃ f, Tacenta.UnitSatisfiabilityTripleLaws.HkdfTotalShape f
-/
#guard_msgs in
#check Tacenta.UnitSatisfiabilityTripleLaws.hkdf_total_satisfiable

/--
info: def Tacenta.UnitSatisfiabilityTripleLaws.HkdfTotalShape : Tacenta.UnitSatisfiabilityTripleLaws.HkdfFn → Prop :=
fun f => ∀ (N : Usize) (salt ikm info : Slice U8), ↑N ≤ 8160 → ∃ r, f N salt ikm info = ok r
-/
#guard_msgs in
#print Tacenta.UnitSatisfiabilityTripleLaws.HkdfTotalShape

/--
info: 'Tacenta.UnitSatisfiabilityTripleLaws.pop_satisfiable' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitSatisfiabilityTripleLaws.pop_satisfiable

/--
info: Tacenta.UnitSatisfiabilityTripleLaws.pop_satisfiable : ∃ f, Tacenta.UnitSatisfiabilityTripleLaws.PopShape fun {T} => f
-/
#guard_msgs in
#check Tacenta.UnitSatisfiabilityTripleLaws.pop_satisfiable

/--
info: Tacenta.UnitSatisfiabilityTripleLaws.as_mut_satisfiable :
  ∃ f, Tacenta.UnitSatisfiabilityTripleLaws.AsMutShape fun {T} => f
-/
#guard_msgs in
#check Tacenta.UnitSatisfiabilityTripleLaws.as_mut_satisfiable

/--
info: 'Tacenta.UnitSatisfiabilityTripleLaws.capacity_satisfiable' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitSatisfiabilityTripleLaws.capacity_satisfiable

/--
info: Tacenta.UnitSatisfiabilityTripleLaws.capacity_satisfiable :
  ∃ f, Tacenta.UnitSatisfiabilityTripleLaws.CapacityShape fun {T} => f
-/
#guard_msgs in
#check Tacenta.UnitSatisfiabilityTripleLaws.capacity_satisfiable

/--
info: 'Tacenta.UnitSatisfiabilityTripleLaws.vec_zeroize_satisfiable' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Tacenta.UnitSatisfiabilityTripleLaws.vec_zeroize_satisfiable

/--
info: Tacenta.UnitSatisfiabilityTripleLaws.vec_zeroize_satisfiable :
  ∃ f, Tacenta.UnitSatisfiabilityTripleLaws.VecZeroizeShape fun {Z} => f
-/
#guard_msgs in
#check Tacenta.UnitSatisfiabilityTripleLaws.vec_zeroize_satisfiable

/--
info: 'Tacenta.UnitSatisfiabilityTripleLaws.blanket_satisfiable' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Tacenta.UnitSatisfiabilityTripleLaws.blanket_satisfiable

/--
info: Tacenta.UnitSatisfiabilityTripleLaws.blanket_satisfiable :
  ∃ f, Tacenta.UnitSatisfiabilityTripleLaws.BlanketU32Shape fun {Z} => f
-/
#guard_msgs in
#check Tacenta.UnitSatisfiabilityTripleLaws.blanket_satisfiable

/--
info: 'Tacenta.UnitSatisfiabilityTripleLaws.vec_zeroize_conflicts' depends on axioms: [propext,
 Quot.sound,
 alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize]
-/
#guard_msgs in
#print axioms Tacenta.UnitSatisfiabilityTripleLaws.vec_zeroize_conflicts

/--
info: Tacenta.UnitSatisfiabilityTripleLaws.vec_zeroize_conflicts (h : Tacenta.UnitSatisfiabilityTripleLaws.LawVecZeroize)
  (hp : Tacenta.UnitSatisfiabilityTripleLaws.PropagatesFailureVec) : False
-/
#guard_msgs in
#check Tacenta.UnitSatisfiabilityTripleLaws.vec_zeroize_conflicts

/--
info: def Tacenta.UnitSatisfiabilityTripleLaws.PropagatesFailureVec : Prop :=
∀ {Z : Type} (inst : zeroize.Zeroize Z) (v : alloc.vec.Vec Z) (x : Z),
  ↑v = [x] → inst.zeroize x = fail Error.panic → alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize inst v = fail Error.panic
-/
#guard_msgs in
#print Tacenta.UnitSatisfiabilityTripleLaws.PropagatesFailureVec

/--
info: def Tacenta.UnitSatisfiabilityTripleLaws.LawPop : Prop :=
∀ (T : Type) (v : alloc.vec.Vec T), ↑v ≠ [] → ∃ o w, alloc.vec.Vec.pop Global v = ok (o, w) ∧ ↑w = (↑v).dropLast
-/
#guard_msgs in
#print Tacenta.UnitSatisfiabilityTripleLaws.LawPop

/--
info: def Tacenta.UnitSatisfiabilityTripleLaws.LawAsMut : Prop :=
∀ (T : Type) (o : Option T), ∃ r, core.option.Option.as_mut o = ok r
-/
#guard_msgs in
#print Tacenta.UnitSatisfiabilityTripleLaws.LawAsMut

/--
info: def Tacenta.UnitSatisfiabilityTripleLaws.LawCapacity : Prop :=
∀ {T : Type} (A : Type) (v : alloc.vec.Vec T), ∃ r, alloc.vec.Vec.capacity A v = ok r
-/
#guard_msgs in
#print Tacenta.UnitSatisfiabilityTripleLaws.LawCapacity

/--
info: def Tacenta.UnitSatisfiabilityTripleLaws.LawVecZeroize : Prop :=
∀ {T : Type} (inst : zeroize.Zeroize T) (v : alloc.vec.Vec T),
  ∃ r, alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize inst v = ok r
-/
#guard_msgs in
#print Tacenta.UnitSatisfiabilityTripleLaws.LawVecZeroize

/--
info: def Tacenta.UnitSatisfiabilityTripleLaws.LawBlanketU32 : Prop :=
∀ (x : U32), ∃ r, zeroize.Zeroize.Blanket.zeroize U32.Insts.ZeroizeDefaultIsZeroes x = ok r
-/
#guard_msgs in
#print Tacenta.UnitSatisfiabilityTripleLaws.LawBlanketU32

/--
info: def Tacenta.UnitSatisfiabilityTripleLaws.LawHkdf : Prop :=
∀ (N : Usize) (salt ikm info : Slice U8), ↑N ≤ 8160 → ∃ r, tacenta_kdf.hkdf_sha256 N salt ikm info = ok r
-/
#guard_msgs in
#print Tacenta.UnitSatisfiabilityTripleLaws.LawHkdf

/--
info: def Tacenta.UnitSatisfiabilityTripleLaws.LawZeroizing : Usize → Prop :=
fun N =>
  ∀ (z : Std.Array U8 N),
    ∃ w,
      zeroize.Zeroizing.new (Tacenta.UnitSatisfiabilityTripleLaws.arrInst N) z = ok w ∧
        zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref (Tacenta.UnitSatisfiabilityTripleLaws.arrInst N) w = ok z
-/
#guard_msgs in
#print Tacenta.UnitSatisfiabilityTripleLaws.LawZeroizing

/--
info: def Tacenta.UnitSatisfiabilityTripleLaws.PopShape : Tacenta.UnitSatisfiabilityTripleLaws.PopFn → Prop :=
fun f => ∀ (T : Type) (v : alloc.vec.Vec T), ↑v ≠ [] → ∃ o w, f Global v = ok (o, w) ∧ ↑w = (↑v).dropLast
-/
#guard_msgs in
#print Tacenta.UnitSatisfiabilityTripleLaws.PopShape

/--
info: def Tacenta.UnitSatisfiabilityTripleLaws.AsMutShape : Tacenta.UnitSatisfiabilityTripleLaws.AsMutFn → Prop :=
fun f => ∀ (T : Type) (o : Option T), ∃ r, f o = ok r
-/
#guard_msgs in
#print Tacenta.UnitSatisfiabilityTripleLaws.AsMutShape

/--
info: def Tacenta.UnitSatisfiabilityTripleLaws.CapacityShape : Tacenta.UnitSatisfiabilityTripleLaws.CapacityFn → Prop :=
fun f => ∀ {T : Type} (A : Type) (v : alloc.vec.Vec T), ∃ r, f A v = ok r
-/
#guard_msgs in
#print Tacenta.UnitSatisfiabilityTripleLaws.CapacityShape

/--
info: def Tacenta.UnitSatisfiabilityTripleLaws.VecZeroizeShape : Tacenta.UnitSatisfiabilityTripleLaws.VecZeroizeFn → Prop :=
fun f => ∀ {T : Type} (inst : zeroize.Zeroize T) (v : alloc.vec.Vec T), ∃ r, f inst v = ok r
-/
#guard_msgs in
#print Tacenta.UnitSatisfiabilityTripleLaws.VecZeroizeShape

/--
info: def Tacenta.UnitSatisfiabilityTripleLaws.BlanketU32Shape : Tacenta.UnitSatisfiabilityTripleLaws.BlanketFn → Prop :=
fun f => ∀ (x : U32), ∃ r, f U32.Insts.ZeroizeDefaultIsZeroes x = ok r
-/
#guard_msgs in
#print Tacenta.UnitSatisfiabilityTripleLaws.BlanketU32Shape
