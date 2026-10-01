import Translation.UnitLifecyclePublicT1

/-!
# The ratchet and key-derivation fields of the session contract records

Six fields of the contract records are statements about functions the Session unit translates
with a body, not about opaque constants: `SessionUnitT1.RemoveSkippedAtTotal` and
`SessionUnitSpqrT1.RemoveSkippedAtTotal` (the stores' removal helpers), `SessionUnitSpqrT1.KdfRkTotal`,
`KdfCkTotal` and `SessionUnitTripleT1.KdfInitTotal` (the key derivations), and
`SessionUnitSpqrT1.VecRetainTotal` with its three loop contracts.  A model cannot change what
they say.  This module proves each from a small set of laws about the opaque constants the
bodies reach (`defined_fields_hold`), by stepping through the translated code.

The laws are `Laws`: `Vec::pop`, `Option::as_mut`, the blanket `Zeroize` implementation at `u32`,
`Vec::capacity` and `Vec::zeroize` return, `Array::zeroize` returns (the existing field
`SessionUnitSpqrT1.ZeroizeTotal`), the HKDF returns for output lengths up to 8160 bytes, and the
`Zeroizing` wrapper reads back what it wraps at 96 and 64 bytes.  Four of them are fields of the
records, two are conjuncts of the field `VecRetainTotal`, and three are not: `LawPop` (`Vec::pop` of a non-empty vector returns the vector
without its last element), `LawAsMut` and `LawBlanketU32`.  A record that is to be inhabited needs
them, and none states them.  Three results show they are not spare strength:

* `ratchetRemoveSkippedAtTotal_forces_blanketU32`: the classical removal field together with
  `ZeroizeTotal` implies `LawBlanketU32`.
* `setChainsLoopTotal_forces_asMut`: `SetChainsLoopTotal` implies that `Option::as_mut` returns at
  `Option<Chain>`, the one type the proofs use `LawAsMut` at.
* `spqrRemoveSkippedAtTotal_false_of_noop_pop`, `ratchetRemoveSkippedAtTotal_false_of_noop_pop`:
  a `Vec::pop` that returns `(none, v)` for every vector falsifies both removal fields, given
  `ZeroizeTotal` and, for the classical one, `LawBlanketU32`; whether every `pop` that does not
  shorten the vector does is not checked.  The witness the tree used for `VecPopTotal` was that
  function, so it could not be part of a model of the records (`UnitSatisfiabilitySession.lean` now uses a `pop` that shortens).

Nothing here shows that the real standard-library and `zeroize` functions satisfy the laws.  The laws are
recorded in `LIMITATIONS.md`.
-/

open Aeneas Aeneas.Std Result ControlFlow Error
open tacenta_session_unit

noncomputable section

namespace Tacenta.UnitSatisfiabilityRatchet


/-- The opaque HKDF returns on every triple of slices, for an output length within RFC 5869's
bound.  This is the field `HkdfTotal` of the records. -/
def LawHkdf : Prop :=
  ∀ (N : Usize) (salt ikm info : Slice U8), N.val ≤ 8160 →
    ∃ r, tacenta_kdf.hkdf_sha256 N salt ikm info = ok r

/-- The `Zeroize` instance the sparse ratchet passes to `Zeroizing` for an `N`-byte array. -/
abbrev arrInst (N : Usize) : zeroize.Zeroize (Array U8 N) :=
  Array.Insts.ZeroizeZeroize N (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)

/-- Wrapping an `N`-byte array in `Zeroizing` returns a wrapper that reads back to it.  This is
the field `ZeroizingArrayRoundTrip` of the records, at one length. -/
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
    Tacenta.SessionUnitSpqrT1.KdfRkTotal := by
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
    Tacenta.SessionUnitSpqrT1.KdfCkTotal := by
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
    Tacenta.SessionUnitTripleT1.KdfInitTotal := by
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
This is all the defined-function fields need of `pop`; the real operation also returns the
element and handles the empty vector, and `VecPopTotal` (which only says `pop` returns) is not
enough.  No record states it. -/
def LawPop : Prop :=
  ∀ (T : Type) (v : alloc.vec.Vec T), v.val ≠ [] →
    ∃ o w, alloc.vec.Vec.pop Global v = ok (o, w) ∧ w.val = v.val.dropLast

theorem skipped_zeroize_spec (hZ : Tacenta.SessionUnitSpqrT1.ZeroizeTotal) (s : tacenta_spqr.Skipped) :
    tacenta_spqr.Skipped.Insts.ZeroizeZeroize.zeroize s ⦃ fun r => r.epoch = s.epoch ∧ r.n = s.n ⦄ := by
  unfold tacenta_spqr.Skipped.Insts.ZeroizeZeroize.zeroize
  obtain ⟨r, hr⟩ := hZ (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes) s.key
  simp [hr]

/-- The sparse ratchet's `remove_skipped_at`, at an in-range index: returns the key at that index
and the vector with that index erased. -/
theorem spqr_remove_skipped_at_spec (hZ : Tacenta.SessionUnitSpqrT1.ZeroizeTotal) (hP : LawPop)
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


/-- `SessionUnitSpqrT1.RemoveSkippedAtTotal`, from the pop law and the array zeroize law. -/
theorem spqrRemoveSkippedAtTotal (hZ : Tacenta.SessionUnitSpqrT1.ZeroizeTotal) (hP : LawPop) :
    Tacenta.SessionUnitSpqrT1.RemoveSkippedAtTotal := by
  intro v i hi
  obtain ⟨r, hr, -, hv⟩ := Std.WP.spec_imp_exists (spqr_remove_skipped_at_spec hZ hP v i hi)
  refine ⟨r, hr, ?_⟩
  rw [hv]
  simp [List.length_eraseIdx, hi]
  omega

/-- **`LawBlanketU32`.**  The `Zeroize` blanket implementation returns at `u32`.  No record states
it. -/
def LawBlanketU32 : Prop :=
  ∀ x : U32, ∃ r, zeroize.Zeroize.Blanket.zeroize U32.Insts.ZeroizeDefaultIsZeroes x = ok r

theorem skippedKey_zeroize_spec (hZ : Tacenta.SessionUnitSpqrT1.ZeroizeTotal) (hB : LawBlanketU32)
    (s : tacenta_ratchet.SkippedKey) :
    tacenta_ratchet.SkippedKey.Insts.ZeroizeZeroize.zeroize s ⦃ fun _ => True ⦄ := by
  unfold tacenta_ratchet.SkippedKey.Insts.ZeroizeZeroize.zeroize
  obtain ⟨r1, h1⟩ := hZ (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes) s.dh
  obtain ⟨r2, h2⟩ := hB s.n
  obtain ⟨r3, h3⟩ := hB s.stored_at
  obtain ⟨r4, h4⟩ := hZ (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes) s.key
  simp [h1, h2, h3, h4]

/-- The classical ratchet's `remove_skipped_at`, at an in-range index. -/
theorem ratchet_remove_skipped_at_spec (hZ : Tacenta.SessionUnitSpqrT1.ZeroizeTotal)
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


/-- `SessionUnitT1.RemoveSkippedAtTotal`, from the pop law, the array zeroize law and the `u32`
blanket zeroize law. -/
theorem ratchetRemoveSkippedAtTotal (hZ : Tacenta.SessionUnitSpqrT1.ZeroizeTotal)
    (hB : LawBlanketU32) (hP : LawPop) : Tacenta.SessionUnitT1.RemoveSkippedAtTotal := by
  intro A v i hi
  obtain ⟨r, hr, h1, h2⟩ := Std.WP.spec_imp_exists (ratchet_remove_skipped_at_spec hZ hB hP v i hi)
  exact ⟨r, hr, h1, h2⟩


/-- **`LawAsMut`.**  `Option::as_mut` returns.  No record states it. -/
def LawAsMut : Prop :=
  ∀ (T : Type) (o : Option T), ∃ r, core.option.Option.as_mut o = ok r

theorem chain_zeroize_spec (hZ : Tacenta.SessionUnitSpqrT1.ZeroizeTotal) (c : tacenta_spqr.Chain) :
    tacenta_spqr.Chain.Insts.ZeroizeZeroize.zeroize c ⦃ fun _ => True ⦄ := by
  unfold tacenta_spqr.Chain.Insts.ZeroizeZeroize.zeroize
  obtain ⟨r, hr⟩ := hZ (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes) c.ck
  simp [hr]

theorem as_mut_step (hA : LawAsMut) {T : Type} (o : Option T) :
    core.option.Option.as_mut o ⦃ fun _ => True ⦄ := by
  obtain ⟨r, hr⟩ := hA T o
  simp [hr]

theorem chains_zeroize_spec (hZ : Tacenta.SessionUnitSpqrT1.ZeroizeTotal) (hA : LawAsMut)
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
theorem remove_chains_at_spec (hZ : Tacenta.SessionUnitSpqrT1.ZeroizeTotal) (hA : LawAsMut)
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


theorem set_chains_loop_spec (hZ : Tacenta.SessionUnitSpqrT1.ZeroizeTotal) (hA : LawAsMut)
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


theorem clear_chains_loop0_spec (hZ : Tacenta.SessionUnitSpqrT1.ZeroizeTotal) (hA : LawAsMut)
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


theorem array_zeroize_step (hZ : Tacenta.SessionUnitSpqrT1.ZeroizeTotal) (a : Array U8 32#usize) :
    Array.Insts.ZeroizeZeroize.zeroize
      (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes) a ⦃ fun _ => True ⦄ := by
  obtain ⟨r, hr⟩ := hZ (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes) a
  simp [hr]

theorem clear_skipped_loop1_spec (hZ : Tacenta.SessionUnitSpqrT1.ZeroizeTotal)
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

/-- The `Zeroize` implementation for `Vec` returns.  The second conjunct of `VecRetainTotal`. -/
def LawVecZeroize : Prop :=
  ∀ {T : Type} (inst : zeroize.Zeroize T) (v : alloc.vec.Vec T),
    ∃ r, alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize inst v = ok r

theorem vecRetainTotal (hCap : LawCapacity) (hVZ : LawVecZeroize)
    (hZ : Tacenta.SessionUnitSpqrT1.ZeroizeTotal) (hA : LawAsMut) (hP : LawPop) :
    Tacenta.SessionUnitSpqrT1.VecRetainTotal :=
  ⟨hCap, hVZ, setChainsLoopTotal hZ hA hP, clearChainsLoop0Total hZ hA hP,
    clearSkippedLoopTotal hZ hP⟩


/-! ## The field is a law about `Vec::pop` in disguise

The no-op `pop` (`fun v => ok (none, v)`) was the witness `UnitSatisfiabilitySession.lean` used for
`VecPopTotal` before it was replaced by a `pop` that shortens the vector.  It is not a model of the
session contracts: with it, the sparse ratchet's
`remove_skipped_at` does not shorten the vector, so `SessionUnitSpqrT1.RemoveSkippedAtTotal` is
false. -/

theorem spqr_remove_skipped_at_noop_pop (hZ : Tacenta.SessionUnitSpqrT1.ZeroizeTotal)
    (hnoop : ∀ (T : Type) (v : alloc.vec.Vec T), alloc.vec.Vec.pop Global v = ok (none, v))
    (v : alloc.vec.Vec tacenta_spqr.Skipped) (i : Usize) (hi : i.val < v.val.length) :
    tacenta_spqr.State.remove_skipped_at v i ⦃ fun r => r.2.val.length = v.val.length ⦄ := by
  unfold tacenta_spqr.State.remove_skipped_at
  rw [spqr_loop_eq]
  step with rotLoop_spec v i hi as ⟨v1, i1, hv1, hi1⟩
  have hL : (v.val.eraseIdx i.val).length = v.val.length - 1 := by
    simp [List.length_eraseIdx, hi]
  have hlen1 : v1.val.length = v.val.length := by
    rw [hv1]; simp; omega
  have hb : i1.val < v1.val.length := by omega
  step with alloc.vec.Vec.index_usize_spec v1 i1 hb as ⟨x, hx⟩
  step with alloc.vec.Vec.index_mut_usize_spec v1 i1 hb as ⟨x', back, hx', hback⟩
  step with skipped_zeroize_spec hZ as ⟨s2⟩
  rw [hnoop]
  simp only [bind_tc_ok]
  show (back s2).val.length = v.val.length
  rw [hback, alloc.vec.Vec.set_val_eq]
  simp [hlen1]

/-- With the no-op `pop`, the sparse ratchet's field is false. -/
theorem spqrRemoveSkippedAtTotal_false_of_noop_pop (hZ : Tacenta.SessionUnitSpqrT1.ZeroizeTotal)
    (hnoop : ∀ (T : Type) (v : alloc.vec.Vec T), alloc.vec.Vec.pop Global v = ok (none, v)) :
    ¬ Tacenta.SessionUnitSpqrT1.RemoveSkippedAtTotal := by
  intro hF
  let s : tacenta_spqr.Skipped := { epoch := 0#u64, n := 0#u64, key := Array.repeat 32#usize 0#u8 }
  let v : alloc.vec.Vec tacenta_spqr.Skipped := ⟨[s], by simp; scalar_tac⟩
  have hi : (0#usize).val < v.val.length := by simp [v]
  obtain ⟨r, hr, hlen⟩ := hF v 0#usize hi
  obtain ⟨r', hr', hlen'⟩ := Std.WP.spec_imp_exists (spqr_remove_skipped_at_noop_pop hZ hnoop v 0#usize hi)
  rw [hr] at hr'
  have : r = r' := by injection hr'
  subst this
  omega


theorem ratchet_remove_skipped_at_noop_pop (hZ : Tacenta.SessionUnitSpqrT1.ZeroizeTotal)
    (hB : LawBlanketU32)
    (hnoop : ∀ (T : Type) (v : alloc.vec.Vec T), alloc.vec.Vec.pop Global v = ok (none, v))
    (v : alloc.vec.Vec tacenta_ratchet.SkippedKey) (i : Usize) (hi : i.val < v.val.length) :
    tacenta_ratchet.remove_skipped_at v i ⦃ fun r => r.2.val.length = v.val.length ⦄ := by
  unfold tacenta_ratchet.remove_skipped_at
  rw [ratchet_loop_eq]
  step with rotLoop_spec v i hi as ⟨v1, i1, hv1, hi1⟩
  have hL : (v.val.eraseIdx i.val).length = v.val.length - 1 := by
    simp [List.length_eraseIdx, hi]
  have hlen1 : v1.val.length = v.val.length := by
    rw [hv1]; simp; omega
  have hb : i1.val < v1.val.length := by omega
  step with alloc.vec.Vec.index_usize_spec v1 i1 hb as ⟨x, hx⟩
  step with alloc.vec.Vec.index_mut_usize_spec v1 i1 hb as ⟨x', back, hx', hback⟩
  step with skippedKey_zeroize_spec hZ hB as ⟨s2⟩
  rw [hnoop]
  simp only [bind_tc_ok]
  show (back s2).val.length = v.val.length
  rw [hback, alloc.vec.Vec.set_val_eq]
  simp [hlen1]

/-- With the no-op `pop`, the classical ratchet's field is false too. -/
theorem ratchetRemoveSkippedAtTotal_false_of_noop_pop (hZ : Tacenta.SessionUnitSpqrT1.ZeroizeTotal)
    (hB : LawBlanketU32)
    (hnoop : ∀ (T : Type) (v : alloc.vec.Vec T), alloc.vec.Vec.pop Global v = ok (none, v)) :
    ¬ Tacenta.SessionUnitT1.RemoveSkippedAtTotal := by
  intro hF
  let s : tacenta_ratchet.SkippedKey :=
    { dh := Array.repeat 32#usize 0#u8, n := 0#u32, stored_at := 0#u32, key := Array.repeat 32#usize 0#u8 }
  let v : alloc.vec.Vec tacenta_ratchet.SkippedKey := ⟨[s], by simp; scalar_tac⟩
  have hi : (0#usize).val < v.val.length := by simp [v]
  obtain ⟨r, hr, -, hlen⟩ := hF Unit v 0#usize hi
  obtain ⟨r', hr', hlen'⟩ :=
    Std.WP.spec_imp_exists (ratchet_remove_skipped_at_noop_pop hZ hB hnoop v 0#usize hi)
  rw [hr] at hr'
  have : r = r' := by injection hr'
  subst this
  have h1 : (v.val.eraseIdx (0#usize).val) = [] := by simp [v]
  rw [h1] at hlen
  have h2 : r.2.val.length = 0 := by simpa using hlen
  have h3 : v.val.length = 1 := by simp [v]
  omega


/-- The classical field also forces the `u32` blanket zeroize law: if that call did not return on
some `x`, the field would be false at the one-element store whose key counts `x`. -/
theorem ratchetRemoveSkippedAtTotal_forces_blanketU32 (hZ : Tacenta.SessionUnitSpqrT1.ZeroizeTotal)
    (hF : Tacenta.SessionUnitT1.RemoveSkippedAtTotal) : LawBlanketU32 := by
  intro x
  by_contra hbad
  simp only [not_exists] at hbad
  let s : tacenta_ratchet.SkippedKey :=
    { dh := Array.repeat 32#usize 0#u8, n := x, stored_at := 0#u32, key := Array.repeat 32#usize 0#u8 }
  let v : alloc.vec.Vec tacenta_ratchet.SkippedKey := ⟨[s], by simp; scalar_tac⟩
  have hi : (0#usize).val < v.val.length := by simp [v]
  obtain ⟨r, hr, -, -⟩ := hF Unit v 0#usize hi
  obtain ⟨⟨v1, i1⟩, hloop, hv1, hi1⟩ := Std.WP.spec_imp_exists (rotLoop_spec v 0#usize hi)
  unfold tacenta_ratchet.remove_skipped_at at hr
  rw [ratchet_loop_eq, hloop] at hr
  simp only [bind_tc_ok] at hr
  have hv1' : v1.val = [s] := by simpa [v] using hv1
  have hi1' : i1.val = 0 := by simpa [v] using hi1
  have hb : i1.val < v1.val.length := by simp [hv1', hi1']
  have hget : v1.val[i1.val]'hb = s := by simp [hv1', hi1']
  obtain ⟨x1, hx1⟩ := Std.WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec v1 i1 hb)
  obtain ⟨⟨x2, back⟩, hx2, hx2a, hx2b⟩ := Std.WP.spec_imp_exists (alloc.vec.Vec.index_mut_usize_spec v1 i1 hb)
  simp only [alloc.vec.Vec.index_slice_index, alloc.vec.Vec.index_mut_slice_index] at hr
  have hr' : (do
      let sk ← v1.index_usize i1
      let (sk1, index_mut_back) ← v1.index_mut_usize i1
      let sk2 ← tacenta_ratchet.SkippedKey.Insts.ZeroizeZeroize.zeroize sk1
      let (_, skipped3) ← alloc.vec.Vec.pop Global (index_mut_back sk2)
      ok (sk.key, skipped3)) = ok r := hr
  clear hr
  rw [hx1.1] at hr'
  simp only [bind_tc_ok] at hr'
  rw [hx2] at hr'
  simp only [bind_tc_ok] at hr'
  have hx2s : x2 = s := by rw [hx2a, hget]
  subst hx2s
  have hr2 : (do
      let sk2 ← tacenta_ratchet.SkippedKey.Insts.ZeroizeZeroize.zeroize s
      let (_, skipped3) ← alloc.vec.Vec.pop Global (back sk2)
      ok (x1.key, skipped3)) = ok r := hr'
  clear hr'
  unfold tacenta_ratchet.SkippedKey.Insts.ZeroizeZeroize.zeroize at hr2
  obtain ⟨d, hd⟩ := hZ (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes) s.dh
  rw [hd] at hr2
  simp only [bind_tc_ok] at hr2
  cases hB : zeroize.Zeroize.Blanket.zeroize U32.Insts.ZeroizeDefaultIsZeroes s.n with
  | ok a => exact hbad a (by simpa [s] using hB)
  | fail e => rw [hB] at hr2; simp at hr2
  | div => rw [hB] at hr2; simp at hr2


/-! ## `SetChainsLoopTotal` forces `Option::as_mut` to return

No contract record mentions `Option::as_mut`, yet `Chains::zeroize` calls it on both slots and
`remove_chains_at` calls `Chains::zeroize`. So the field, at a one-entry table whose epoch matches,
already asks `as_mut` to return at every `Option<Chain>`. -/

theorem setChainsLoopTotal_forces_asMut
    (hF : Tacenta.SessionUnitSpqrT1.SetChainsLoopTotal) :
    ∀ o : Option tacenta_spqr.Chain, ∃ r, core.option.Option.as_mut o = ok r := by
  intro o
  by_contra hbad
  simp only [not_exists] at hbad
  let c : tacenta_spqr.Chains := { send := o, receive := none }
  let chains : alloc.vec.Vec (U64 × tacenta_spqr.Chains) := ⟨[(0#u64, c)], by simp; scalar_tac⟩
  let st : tacenta_spqr.State :=
    { rk := Array.repeat 32#usize 0#u8, epoch := 0#u64, chains := chains,
      skipped := alloc.vec.Vec.new tacenta_spqr.Skipped, direction := tacenta_spqr.Direction.A2b }
  obtain ⟨r, hr, -⟩ := hF st 0#u64 0#usize (by simp [st, chains])
  unfold tacenta_spqr.State.set_chains_loop at hr
  rw [loop.eq_1] at hr
  have hbody : tacenta_spqr.State.set_chains_loop.body 0#u64 st 0#usize
      = (do let v ← tacenta_spqr.State.remove_chains_at chains 0#usize
            ok (cont ({ st with chains := v }, 0#usize))) := by
    simp [tacenta_spqr.State.set_chains_loop.body, st, chains, alloc.vec.Vec.index_usize,
      alloc.vec.Vec.len]
  dsimp only at hr
  rw [hbody] at hr
  cases hrc : tacenta_spqr.State.remove_chains_at chains 0#usize with
  | fail e => rw [hrc] at hr; simp at hr
  | div => rw [hrc] at hr; simp at hr
  | ok v =>
    have hi0 : (0#usize).val < chains.val.length := by simp [chains]
    obtain ⟨⟨v1, i1⟩, hloop, hv1, hi1⟩ := Std.WP.spec_imp_exists (rotLoop_spec chains 0#usize hi0)
    unfold tacenta_spqr.State.remove_chains_at at hrc
    rw [chains_loop_eq, hloop] at hrc
    simp only [bind_tc_ok] at hrc
    have hv1' : v1.val = [(0#u64, c)] := by simpa [chains] using hv1
    have hi1' : i1.val = 0 := by simpa [chains] using hi1
    have hb : i1.val < v1.val.length := by simp [hv1', hi1']
    have hget : v1.val[i1.val]'hb = (0#u64, c) := by simp [hv1', hi1']
    obtain ⟨⟨x2, back⟩, hx2, hx2a, hx2b⟩ :=
      Std.WP.spec_imp_exists (alloc.vec.Vec.index_mut_usize_spec v1 i1 hb)
    simp only [alloc.vec.Vec.index_mut_slice_index] at hrc
    have hrc2 : (do
        let ((i1', c'), index_mut_back) ← v1.index_mut_usize i1
        let c1 ← tacenta_spqr.Chains.Insts.ZeroizeZeroize.zeroize c'
        let chains2 := index_mut_back (i1', c1)
        let ((i2, c2), index_mut_back1) ←
          alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice (Std.U64 × tacenta_spqr.Chains)) chains2 i1
        let chains3 := index_mut_back1 (i2, { c2 with send := none })
        let ((i3, c3), index_mut_back2) ←
          alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice (Std.U64 × tacenta_spqr.Chains)) chains3 i1
        let chains4 := index_mut_back2 (i3, { c3 with receive := none })
        let (_, chains5) ← alloc.vec.Vec.pop Global chains4
        ok chains5) = ok v := hrc
    clear hrc
    rw [hx2] at hrc2
    simp only [bind_tc_ok] at hrc2
    have hx2s : x2 = (0#u64, c) := by rw [hx2a, hget]
    subst hx2s
    have hrc3 : (do
        let c1 ← tacenta_spqr.Chains.Insts.ZeroizeZeroize.zeroize c
        let ((i2, c2), index_mut_back1) ←
          alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice (Std.U64 × tacenta_spqr.Chains))
            (back (0#u64, c1)) i1
        let ((i3, c3), index_mut_back2) ←
          alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice (Std.U64 × tacenta_spqr.Chains))
            (index_mut_back1 (i2, { send := none, receive := c2.receive })) i1
        let (_, chains5) ← alloc.vec.Vec.pop Global (index_mut_back2 (i3, { send := c3.send, receive := none }))
        ok chains5) = ok v := hrc2
    clear hrc2
    cases hz : tacenta_spqr.Chains.Insts.ZeroizeZeroize.zeroize c with
    | fail e => rw [hz] at hrc3; simp at hrc3
    | div => rw [hz] at hrc3; simp at hrc3
    | ok c1 =>
      unfold tacenta_spqr.Chains.Insts.ZeroizeZeroize.zeroize at hz
      cases has : core.option.Option.as_mut o with
      | ok x => exact hbad x has
      | fail e => simp [c, has] at hz
      | div => simp [c, has] at hz

/-! ## Bridges to the fields the records already carry, and the whole result in one statement -/

theorem lawHkdf_of_T1 (h : Tacenta.SessionUnitT1.HkdfTotal) : LawHkdf := h

theorem lawHkdf_of_braid (h : Tacenta.SessionUnitBraidT1.HkdfSha256Total) : LawHkdf := h

theorem lawZeroizing_of_braid (h : Tacenta.SessionUnitBraidT1.ZeroizingArrayRoundTrip)
    (N : Usize) : LawZeroizing N :=
  fun z => h N (arrInst N) z

/-- The laws, on the opaque constants, that make the defined-function fields true. -/
structure Laws : Prop where
  pop : LawPop
  asMut : LawAsMut
  blanketU32 : LawBlanketU32
  capacity : LawCapacity
  vecZeroize : LawVecZeroize
  arrayZeroize : Tacenta.SessionUnitSpqrT1.ZeroizeTotal
  hkdf : LawHkdf
  zeroizing96 : LawZeroizing 96#usize
  zeroizing64 : LawZeroizing 64#usize

theorem defined_fields_hold (L : Laws) :
    Tacenta.SessionUnitT1.RemoveSkippedAtTotal ∧
    Tacenta.SessionUnitSpqrT1.RemoveSkippedAtTotal ∧
    Tacenta.SessionUnitSpqrT1.KdfRkTotal ∧
    Tacenta.SessionUnitSpqrT1.KdfCkTotal ∧
    Tacenta.SessionUnitTripleT1.KdfInitTotal ∧
    Tacenta.SessionUnitSpqrT1.VecRetainTotal :=
  ⟨ratchetRemoveSkippedAtTotal L.arrayZeroize L.blanketU32 L.pop,
   spqrRemoveSkippedAtTotal L.arrayZeroize L.pop,
   kdfRkTotal L.hkdf L.zeroizing96,
   kdfCkTotal L.hkdf L.zeroizing64,
   kdfInitTotal L.hkdf L.zeroizing96,
   vecRetainTotal L.capacity L.vecZeroize L.arrayZeroize L.asMut L.pop⟩

end Tacenta.UnitSatisfiabilityRatchet

end

/-! ## Axiom pins

The axiom bases of the results above, held by the build.  A list names the opaque constants that
occur in the statement of a result or that its hypotheses are about (`Array::zeroize`, `Vec::pop`,
`Option::as_mut`, the blanket `Zeroize` implementation, the HKDF, the `Zeroizing` wrapper); the
proofs assume about them exactly the named laws that appear as hypotheses, and nothing else.  The
four `*_false_of_noop_pop` and `*_forces_*` results are the evidence that three of the laws are
needed. -/

/--
info: 'Tacenta.UnitSatisfiabilityRatchet.kdfRkTotal' depends on axioms: [propext,
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
#print axioms Tacenta.UnitSatisfiabilityRatchet.kdfRkTotal

/--
info: 'Tacenta.UnitSatisfiabilityRatchet.kdfCkTotal' depends on axioms: [propext,
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
#print axioms Tacenta.UnitSatisfiabilityRatchet.kdfCkTotal

/--
info: 'Tacenta.UnitSatisfiabilityRatchet.kdfInitTotal' depends on axioms: [propext,
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
#print axioms Tacenta.UnitSatisfiabilityRatchet.kdfInitTotal

/--
info: 'Tacenta.UnitSatisfiabilityRatchet.spqrRemoveSkippedAtTotal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Array.Insts.ZeroizeZeroize.zeroize,
 alloc.vec.Vec.pop,
 zeroize.Zeroize.Blanket.zeroize]
-/
#guard_msgs in
#print axioms Tacenta.UnitSatisfiabilityRatchet.spqrRemoveSkippedAtTotal

/--
info: 'Tacenta.UnitSatisfiabilityRatchet.ratchetRemoveSkippedAtTotal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Array.Insts.ZeroizeZeroize.zeroize,
 alloc.vec.Vec.pop,
 zeroize.Zeroize.Blanket.zeroize]
-/
#guard_msgs in
#print axioms Tacenta.UnitSatisfiabilityRatchet.ratchetRemoveSkippedAtTotal

/--
info: 'Tacenta.UnitSatisfiabilityRatchet.setChainsLoopTotal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Array.Insts.ZeroizeZeroize.zeroize,
 alloc.vec.Vec.pop,
 core.option.Option.as_mut,
 zeroize.Zeroize.Blanket.zeroize]
-/
#guard_msgs in
#print axioms Tacenta.UnitSatisfiabilityRatchet.setChainsLoopTotal

/--
info: 'Tacenta.UnitSatisfiabilityRatchet.clearChainsLoop0Total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Array.Insts.ZeroizeZeroize.zeroize,
 alloc.vec.Vec.pop,
 core.option.Option.as_mut,
 zeroize.Zeroize.Blanket.zeroize]
-/
#guard_msgs in
#print axioms Tacenta.UnitSatisfiabilityRatchet.clearChainsLoop0Total

/--
info: 'Tacenta.UnitSatisfiabilityRatchet.clearSkippedLoopTotal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Array.Insts.ZeroizeZeroize.zeroize,
 alloc.vec.Vec.pop,
 zeroize.Zeroize.Blanket.zeroize]
-/
#guard_msgs in
#print axioms Tacenta.UnitSatisfiabilityRatchet.clearSkippedLoopTotal

/--
info: 'Tacenta.UnitSatisfiabilityRatchet.vecRetainTotal' depends on axioms: [propext,
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
#print axioms Tacenta.UnitSatisfiabilityRatchet.vecRetainTotal

/--
info: 'Tacenta.UnitSatisfiabilityRatchet.defined_fields_hold' depends on axioms: [propext,
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
#print axioms Tacenta.UnitSatisfiabilityRatchet.defined_fields_hold

/--
info: 'Tacenta.UnitSatisfiabilityRatchet.spqrRemoveSkippedAtTotal_false_of_noop_pop' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Array.Insts.ZeroizeZeroize.zeroize,
 alloc.vec.Vec.pop,
 zeroize.Zeroize.Blanket.zeroize]
-/
#guard_msgs in
#print axioms Tacenta.UnitSatisfiabilityRatchet.spqrRemoveSkippedAtTotal_false_of_noop_pop

/--
info: 'Tacenta.UnitSatisfiabilityRatchet.ratchetRemoveSkippedAtTotal_false_of_noop_pop' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Array.Insts.ZeroizeZeroize.zeroize,
 alloc.vec.Vec.pop,
 zeroize.Zeroize.Blanket.zeroize]
-/
#guard_msgs in
#print axioms Tacenta.UnitSatisfiabilityRatchet.ratchetRemoveSkippedAtTotal_false_of_noop_pop

/--
info: 'Tacenta.UnitSatisfiabilityRatchet.ratchetRemoveSkippedAtTotal_forces_blanketU32' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Array.Insts.ZeroizeZeroize.zeroize,
 alloc.vec.Vec.pop,
 zeroize.Zeroize.Blanket.zeroize]
-/
#guard_msgs in
#print axioms Tacenta.UnitSatisfiabilityRatchet.ratchetRemoveSkippedAtTotal_forces_blanketU32

/--
info: 'Tacenta.UnitSatisfiabilityRatchet.setChainsLoopTotal_forces_asMut' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Array.Insts.ZeroizeZeroize.zeroize,
 alloc.vec.Vec.pop,
 core.option.Option.as_mut,
 zeroize.Zeroize.Blanket.zeroize]
-/
#guard_msgs in
#print axioms Tacenta.UnitSatisfiabilityRatchet.setChainsLoopTotal_forces_asMut
