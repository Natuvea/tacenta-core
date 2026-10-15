import Translation.UnitSatisfiabilityRatchet
import Translation.UnitSatisfiabilityJoint
import Translation.SessionUnitSpqrT3

/-!
# The Session unit's two sparse agreements, from laws about opaque operations

`SessionUnitSpqrT3.VecRetainAgrees` and `SessionUnitSpqrT3.RemoveSkippedAtAgrees` are statements about
functions the Session unit translates with a body (`State.set_chains`, `State.clear_old_epochs`,
`State.remove_skipped_at`): that the chain-table and skipped-key scans keep exactly the entries the
model keeps, and that the removal helper returns the key at the index it removes and the vector with
that index erased.  A model of the opaque constants cannot change what they say, so they had no
witness; the decrypt refinement took them as assumptions.

This module proves both, by stepping through the translated code, from five laws about the opaque
constants the bodies reach.  Each law is stated once as a named definition, elsewhere, and named
here; the copies are bound to it by the kernel (`spqrSessionLaws_iff` by unfolding, and a contract
conjunct or a `StdLaws` field passed where the named law is expected):

* `UnitSatisfiabilityRatchet.LawPop`: `Vec::pop` of a non-empty vector returns the vector without its
  last element.
* `UnitSatisfiabilityRatchet.LawAsMut`: `Option::as_mut` returns.
* `UnitSatisfiabilityRatchet.LawCapacity`: `Vec::capacity` returns.
* `UnitSatisfiabilityRatchet.LawVecZeroize`: `Vec::zeroize` returns at the three instance records the
  unit passes to it (the chain table, the sparse skipped-key store, the classical one).
* `SessionUnitSpqrT1.ZeroizeTotal`: `Array::zeroize` returns at the blanket `u8` instance on a
  32-byte array.

`LawCapacity` and `LawVecZeroize` are the first two conjuncts of the contract field
`SessionUnitSpqrT1.VecRetainTotal`, and `ZeroizeTotal` is the contract field itself; `LawPop` and
`LawAsMut` are stated by no contract record.  `SpqrSessionLaws` bundles the five.

* `removeSkippedAtAgrees_of_laws`: `RemoveSkippedAtAgrees` from `ZeroizeTotal` and `LawPop`.
* `vecRetainAgrees_of_laws`: `VecRetainAgrees` from all five.
* `sparse_agreements_of_laws`: both, from the bundle.
* `spqrSessionLaws_iff`: the bundle at the real constants is the shape `SpqrSessionLawsShape` over
  the joint interpretation of `UnitSatisfiabilityJoint.lean` at `Interp.real`, checked by the kernel
  by unfolding.
* `spqrSessionLaws_model`: the shape holds at `Interp.model`, the interpretation that satisfies every
  axiom-level field of the four contract records, so the five laws are consistent with each other
  and with those fields.  `UnitSatisfiabilityZeroizeScope.faithful_SpqrSessionLaws` shows the same
  shape at `Interp.faithful`, whose `Array::zeroize` and `Vec::zeroize` propagate a failing
  element's failure as the crate's do.
* `spqrSessionLawsShape_fails_of_noop_pop`: an interpretation whose `Vec::pop` leaves the vector
  unchanged fails the shape, so the shape is not met by every interpretation.

The step from "the shape holds in an interpretation" to "the laws do not derive `False`" is the
substitution argument of `UnitSatisfiabilityJoint.lean`, about derivations and not a theorem inside
Lean.  Nothing here shows that the real standard-library and `zeroize` functions satisfy the laws:
they are assumptions, recorded in `LIMITATIONS.md`, and are not proved of the real functions.

The value-level loop specifications are the three-leaf unit's (`UnitSatisfiabilityTripleLaws.lean`)
under the Session unit's constants; the removal and loop totality specifications they build on are
`UnitSatisfiabilityRatchet.lean`'s.  The proofs are generic in the platform width.
-/

open Aeneas Aeneas.Std Result ControlFlow Error
open tacenta_session_unit

noncomputable section

namespace Tacenta.UnitSatisfiabilitySpqrSessionLaws

open Tacenta.UnitSatisfiabilityRatchet

/-- The five laws the two sparse agreements are derived from, at the real constants. -/
structure SpqrSessionLaws : Prop where
  pop : LawPop
  asMut : LawAsMut
  capacity : LawCapacity
  vecZeroize : LawVecZeroize
  arrayZeroize : Tacenta.SessionUnitSpqrT1.ZeroizeTotal

/-! ## Value-level specs for the scan loops

`UnitSatisfiabilityRatchet.lean` proves only a length bound for the loops.  The statements below pin
the value: each loop removes exactly the entries its guard names, keeps the order of the rest, and
leaves the other fields of the state alone. -/

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

theorem set_chains_val (hret : Tacenta.SessionUnitSpqrT1.VecRetainTotal)
    (hZ : Tacenta.SessionUnitSpqrT1.ZeroizeTotal)
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
def keepChain (current : U64) (p : U64 × tacenta_spqr.Chains) : Bool :=
  decide (current.val < (core.num.U64.saturating_add p.1 tacenta_spqr.EPOCHS_KEPT).val)

/-- The guard of the skipped-key scan in `clear_old_epochs`, as a Boolean on a skipped entry. -/
def keepSkipped (current : U64) (s : tacenta_spqr.Skipped) : Bool :=
  decide (current.val < (core.num.U64.saturating_add s.epoch tacenta_spqr.EPOCHS_KEPT).val)

theorem clear_chains_loop0_val (hZ : Tacenta.SessionUnitSpqrT1.ZeroizeTotal) (hA : LawAsMut)
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

theorem clear_skipped_loop1_val (hZ : Tacenta.SessionUnitSpqrT1.ZeroizeTotal)
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

theorem clear_old_epochs_val (hZ : Tacenta.SessionUnitSpqrT1.ZeroizeTotal) (hA : LawAsMut)
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
  rw [Tacenta.SessionUnitSpqrT3.saturating_add_val, epochs_kept_val]
  omega

/-! ## The two agreements -/

/-- **`RemoveSkippedAtAgrees`**, from the array `Zeroize` law and the pop law. -/
theorem removeSkippedAtAgrees_of_laws (hZ : Tacenta.SessionUnitSpqrT1.ZeroizeTotal) (hP : LawPop) :
    Tacenta.SessionUnitSpqrT3.RemoveSkippedAtAgrees := by
  intro v i h
  obtain ⟨r, hr, hk, hv⟩ := Std.WP.spec_imp_exists (spqr_remove_skipped_at_spec hZ hP v i h)
  exact ⟨r, hr, hk, hv⟩

theorem setChainsAgrees (hret : Tacenta.SessionUnitSpqrT1.VecRetainTotal)
    (hZ : Tacenta.SessionUnitSpqrT1.ZeroizeTotal) (hA : LawAsMut) (hP : LawPop) :
    ∀ {s : tacenta_spqr.State} {m : Model.SparseRatchet.State}
      (_hrel : Tacenta.SessionUnitSpqrT3.StateRefines s m) (e : Std.U64) (c : tacenta_spqr.Chains)
      (_hroom : s.chains.val.length < Usize.max),
    ∃ r, tacenta_spqr.State.set_chains s e c = ok r ∧
      Tacenta.SessionUnitSpqrT3.StateRefines r
        (Model.SparseRatchet.setChains m e.val (Tacenta.SessionUnitSpqrT3.chainsOf c)) := by
  intro s m hrel e c hroom
  obtain ⟨r, hr, hrk, hep, hsk, hdir, hch⟩ :=
    Std.WP.spec_imp_exists (set_chains_val hret hZ hA hP s e c hroom)
  refine ⟨r, hr, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hrk]; exact hrel.rk
  · rw [hep]; exact hrel.epoch
  · have hm : (Model.SparseRatchet.setChains m e.val (Tacenta.SessionUnitSpqrT3.chainsOf c)).chains
        = (m.chains.filter (fun p => !(p.1 == e.val))) ++
          [(e.val, Tacenta.SessionUnitSpqrT3.chainsOf c)] :=
      rfl
    show r.chains.val.map Tacenta.SessionUnitSpqrT3.chainsEntryOf = _
    rw [hm, ← hrel.chains, hch, List.map_append, List.filter_map]
    rfl
  · rw [hsk]; exact hrel.skipped
  · rw [hdir]; exact hrel.direction

theorem clearOldEpochsAgrees (hZ : Tacenta.SessionUnitSpqrT1.ZeroizeTotal) (hA : LawAsMut)
    (hP : LawPop) :
    ∀ {s : tacenta_spqr.State} {m : Model.SparseRatchet.State}
      (_hrel : Tacenta.SessionUnitSpqrT3.StateRefines s m) (current : Std.U64)
      (_hcb : ∀ p ∈ s.chains.val,
        p.1.val + Model.SparseRatchet.epochsKept ≤ Std.U64.max)
      (_hsb : ∀ sk ∈ s.skipped.val,
        sk.epoch.val + Model.SparseRatchet.epochsKept ≤ Std.U64.max),
    ∃ r, tacenta_spqr.State.clear_old_epochs s current = ok r ∧
      Tacenta.SessionUnitSpqrT3.StateRefines r
        (Model.SparseRatchet.clearOldEpochs m current.val) := by
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

/-- **`VecRetainAgrees`**, from the five laws.  The two chain-table scans, the skipped-key scan and
the capacity copy are proved from the translated bodies; `VecRetainTotal`, which the capacity copy
takes, is itself built from the laws (`UnitSatisfiabilityRatchet.vecRetainTotal`). -/
theorem vecRetainAgrees_of_laws (hCap : LawCapacity) (hVZ : LawVecZeroize)
    (hZ : Tacenta.SessionUnitSpqrT1.ZeroizeTotal) (hA : LawAsMut) (hP : LawPop) :
    Tacenta.SessionUnitSpqrT3.VecRetainAgrees :=
  ⟨setChainsAgrees (vecRetainTotal hCap hVZ hZ hA hP) hZ hA hP,
   clearOldEpochsAgrees hZ hA hP⟩

/-- Both agreements, from the bundle. -/
theorem sparse_agreements_of_laws (L : SpqrSessionLaws) :
    Tacenta.SessionUnitSpqrT3.VecRetainAgrees ∧ Tacenta.SessionUnitSpqrT3.RemoveSkippedAtAgrees :=
  ⟨vecRetainAgrees_of_laws L.capacity L.vecZeroize L.arrayZeroize L.asMut L.pop,
   removeSkippedAtAgrees_of_laws L.arrayZeroize L.pop⟩

/-! ## The laws hold in an interpretation

`SpqrSessionLawsShape` states the five laws over an interpretation of `UnitSatisfiabilityJoint.lean`,
reusing that module's shapes for the three laws the contract records already carry
(`VecRetainAxiomShape`, `SpqrZeroizeShape`) and stating the other two as `StdLaws` does.
`spqrSessionLaws_iff` binds it to the bundle at `Interp.real`; the kernel accepts the binding only
if the two unfold to the same propositions. -/

open Tacenta.UnitSatisfiabilityJoint in
structure SpqrSessionLawsShape (I : Interp) : Prop where
  pop : ∀ (T : Type) (v : alloc.vec.Vec T), v.val ≠ [] →
    ∃ o w, I.vecPop Global v = ok (o, w) ∧ w.val = v.val.dropLast
  asMut : ∀ (T : Type) (o : Option T), ∃ r, I.optionAsMut o = ok r
  retainAxiom : VecRetainAxiomShape I
  arrayZeroize : SpqrZeroizeShape I

open Tacenta.UnitSatisfiabilityJoint in
theorem spqrSessionLaws_iff : SpqrSessionLaws ↔ SpqrSessionLawsShape Interp.real :=
  ⟨fun L => ⟨L.pop, L.asMut, ⟨L.capacity, L.vecZeroize⟩, L.arrayZeroize⟩,
   fun S => ⟨S.pop, S.asMut, S.retainAxiom.1, S.retainAxiom.2, S.arrayZeroize⟩⟩

open Tacenta.UnitSatisfiabilityJoint in
/-- The shape is `StdLaws`' first two laws together with two axiom-level shapes of the records. -/
theorem spqrSessionLawsShape_of_parts (I : Interp) (l : StdLaws I) (vr : VecRetainAxiomShape I)
    (z : SpqrZeroizeShape I) : SpqrSessionLawsShape I :=
  ⟨l.pop, l.asMut, vr, z⟩

open Tacenta.UnitSatisfiabilityJoint in
/-- **The five laws hold in the joint model**, the interpretation in which every axiom-level field
of the four contract records holds. -/
theorem spqrSessionLaws_model : SpqrSessionLawsShape Interp.model :=
  spqrSessionLawsShape_of_parts Interp.model model_StdLaws model_VecRetainAxiom model_SpqrZeroize

open Tacenta.UnitSatisfiabilityJoint in
/-- **The shape is not met by every interpretation.**  One whose `Vec::pop` returns the vector
unchanged (the no-op `pop`) fails `pop`, so a model of the shape has a `pop` that shortens a
non-empty vector. -/
theorem spqrSessionLawsShape_fails_of_noop_pop (I : Interp)
    (hnoop : ∀ (T : Type) (v : alloc.vec.Vec T), I.vecPop Global v = ok (none, v)) :
    ¬ SpqrSessionLawsShape I := by
  intro S
  let v : alloc.vec.Vec Unit := ⟨[()], by simp; scalar_tac⟩
  obtain ⟨o, w, hpop, hw⟩ := S.pop Unit v (by simp [v])
  rw [hnoop] at hpop
  injection hpop with hpop
  injection hpop with _ hvw
  subst hvw
  simp [v] at hw

end Tacenta.UnitSatisfiabilitySpqrSessionLaws

end

/-! ## Pins

The axiom bases and statements of the results above, held by the build.  An axiom list names the
opaque constants that occur in the statement of a result or that its hypotheses are about; the proofs
assume about them exactly the named laws that appear as hypotheses.  The four laws this module names
from `UnitSatisfiabilityRatchet.lean` are printed in full here, because `DecryptRatchetAgreements`
now states two of them and the derivation reads the other two; `SessionUnitSpqrT1.ZeroizeTotal` is
printed in `UnitSatisfiabilityZeroizeScope.lean`. -/

/--
info: 'Tacenta.UnitSatisfiabilitySpqrSessionLaws.removeSkippedAtAgrees_of_laws' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Array.Insts.ZeroizeZeroize.zeroize,
 alloc.vec.Vec.pop,
 zeroize.Zeroize.Blanket.zeroize]
-/
#guard_msgs in
#print axioms Tacenta.UnitSatisfiabilitySpqrSessionLaws.removeSkippedAtAgrees_of_laws

/--
info: Tacenta.UnitSatisfiabilitySpqrSessionLaws.removeSkippedAtAgrees_of_laws (hZ : Tacenta.SessionUnitSpqrT1.ZeroizeTotal)
  (hP : Tacenta.UnitSatisfiabilityRatchet.LawPop) : Tacenta.SessionUnitSpqrT3.RemoveSkippedAtAgrees
-/
#guard_msgs in
#check Tacenta.UnitSatisfiabilitySpqrSessionLaws.removeSkippedAtAgrees_of_laws

/--
info: 'Tacenta.UnitSatisfiabilitySpqrSessionLaws.setChainsAgrees' depends on axioms: [propext,
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
#print axioms Tacenta.UnitSatisfiabilitySpqrSessionLaws.setChainsAgrees

/--
info: Tacenta.UnitSatisfiabilitySpqrSessionLaws.setChainsAgrees (hret : Tacenta.SessionUnitSpqrT1.VecRetainTotal)
  (hZ : Tacenta.SessionUnitSpqrT1.ZeroizeTotal) (hA : Tacenta.UnitSatisfiabilityRatchet.LawAsMut)
  (hP : Tacenta.UnitSatisfiabilityRatchet.LawPop) {s : tacenta_spqr.State} {m : Model.SparseRatchet.State}
  (_hrel : Tacenta.SessionUnitSpqrT3.StateRefines s m) (e : U64) (c : tacenta_spqr.Chains)
  (_hroom : (↑s.chains).length < Usize.max) :
  ∃ r,
    s.set_chains e c = ok r ∧
      Tacenta.SessionUnitSpqrT3.StateRefines r
        (Model.SparseRatchet.setChains m (↑e) (Tacenta.SessionUnitSpqrT3.chainsOf c))
-/
#guard_msgs in
#check Tacenta.UnitSatisfiabilitySpqrSessionLaws.setChainsAgrees

/--
info: 'Tacenta.UnitSatisfiabilitySpqrSessionLaws.clearOldEpochsAgrees' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Array.Insts.ZeroizeZeroize.zeroize,
 alloc.vec.Vec.pop,
 core.option.Option.as_mut,
 zeroize.Zeroize.Blanket.zeroize]
-/
#guard_msgs in
#print axioms Tacenta.UnitSatisfiabilitySpqrSessionLaws.clearOldEpochsAgrees

/--
info: Tacenta.UnitSatisfiabilitySpqrSessionLaws.clearOldEpochsAgrees (hZ : Tacenta.SessionUnitSpqrT1.ZeroizeTotal)
  (hA : Tacenta.UnitSatisfiabilityRatchet.LawAsMut) (hP : Tacenta.UnitSatisfiabilityRatchet.LawPop)
  {s : tacenta_spqr.State} {m : Model.SparseRatchet.State} (_hrel : Tacenta.SessionUnitSpqrT3.StateRefines s m)
  (current : U64) (_hcb : ∀ p ∈ ↑s.chains, ↑p.1 + Model.SparseRatchet.epochsKept ≤ U64.max)
  (_hsb : ∀ sk ∈ ↑s.skipped, ↑sk.epoch + Model.SparseRatchet.epochsKept ≤ U64.max) :
  ∃ r,
    s.clear_old_epochs current = ok r ∧
      Tacenta.SessionUnitSpqrT3.StateRefines r (Model.SparseRatchet.clearOldEpochs m ↑current)
-/
#guard_msgs in
#check Tacenta.UnitSatisfiabilitySpqrSessionLaws.clearOldEpochsAgrees

/--
info: 'Tacenta.UnitSatisfiabilitySpqrSessionLaws.vecRetainAgrees_of_laws' depends on axioms: [propext,
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
#print axioms Tacenta.UnitSatisfiabilitySpqrSessionLaws.vecRetainAgrees_of_laws

/--
info: Tacenta.UnitSatisfiabilitySpqrSessionLaws.vecRetainAgrees_of_laws (hCap : Tacenta.UnitSatisfiabilityRatchet.LawCapacity)
  (hVZ : Tacenta.UnitSatisfiabilityRatchet.LawVecZeroize) (hZ : Tacenta.SessionUnitSpqrT1.ZeroizeTotal)
  (hA : Tacenta.UnitSatisfiabilityRatchet.LawAsMut) (hP : Tacenta.UnitSatisfiabilityRatchet.LawPop) :
  Tacenta.SessionUnitSpqrT3.VecRetainAgrees
-/
#guard_msgs in
#check Tacenta.UnitSatisfiabilitySpqrSessionLaws.vecRetainAgrees_of_laws

/--
info: 'Tacenta.UnitSatisfiabilitySpqrSessionLaws.sparse_agreements_of_laws' depends on axioms: [propext,
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
#print axioms Tacenta.UnitSatisfiabilitySpqrSessionLaws.sparse_agreements_of_laws

/--
info: Tacenta.UnitSatisfiabilitySpqrSessionLaws.sparse_agreements_of_laws
  (L : Tacenta.UnitSatisfiabilitySpqrSessionLaws.SpqrSessionLaws) :
  Tacenta.SessionUnitSpqrT3.VecRetainAgrees ∧ Tacenta.SessionUnitSpqrT3.RemoveSkippedAtAgrees
-/
#guard_msgs in
#check Tacenta.UnitSatisfiabilitySpqrSessionLaws.sparse_agreements_of_laws

/--
info: 'Tacenta.UnitSatisfiabilitySpqrSessionLaws.spqrSessionLaws_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_kdf.hkdf_sha256,
 tacenta_kdf.hmac_sha256,
 tacenta_kem.CT1_LEN,
 tacenta_kem.CT2_LEN,
 tacenta_kem.EK_VECTOR_LEN,
 tacenta_kem.EncapsState,
 tacenta_kem.HEADER_LEN,
 tacenta_kem.IncrementalKeyPair,
 tacenta_kem.encapsulate1,
 tacenta_kem.encapsulate2,
 tacenta_kem.validate_ek,
 zeroize.Zeroizing,
 rand_core_1.error.Error,
 tacenta_boundary.aead.decrypt,
 tacenta_boundary.aead.encrypt,
 tacenta_boundary.dh.PrivateKey,
 tacenta_boundary.dh.PublicKeyBytes,
 tacenta_boundary.dh.is_prime_order_public,
 tacenta_boundary.kem.KeyPair,
 tacenta_boundary.kem.decapsulate,
 tacenta_boundary.kem.encapsulate,
 tacenta_boundary.xeddsa.verify,
 tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_kem.IncrementalKeyPair.generate,
 tacenta_kem.IncrementalKeyPair.header,
 zeroize.Zeroizing.new,
 Array.Insts.ZeroizeZeroize.zeroize,
 Pair.Insts.ZeroizeZeroize.zeroize,
 TupleABC.Insts.ZeroizeZeroize.zeroize,
 alloc.vec.Vec.capacity,
 alloc.vec.Vec.pop,
 alloc.vec.Vec.truncate,
 core.num.Usize.div_ceil,
 core.option.Option.as_mut,
 tacenta_boundary.dh.PrivateKey.agree,
 tacenta_boundary.dh.PrivateKey.from_bytes,
 tacenta_boundary.dh.PrivateKey.public_key,
 tacenta_boundary.dh.PrivateKey.to_bytes,
 tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_boundary.dh.PublicKeyBytes.from_bytes,
 zeroize.Zeroize.Blanket.zeroize,
 tacenta_kem.EncapsState.Insts.CoreCloneClone.clone,
 tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone,
 zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 core.option.Option.Insts.CoreCloneClone.clone,
 tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes.eq,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index]
-/
#guard_msgs in
#print axioms Tacenta.UnitSatisfiabilitySpqrSessionLaws.spqrSessionLaws_iff

/--
info: Tacenta.UnitSatisfiabilitySpqrSessionLaws.spqrSessionLaws_iff :
  Tacenta.UnitSatisfiabilitySpqrSessionLaws.SpqrSessionLaws ↔
    Tacenta.UnitSatisfiabilitySpqrSessionLaws.SpqrSessionLawsShape Tacenta.UnitSatisfiabilityJoint.Interp.real
-/
#guard_msgs in
#check Tacenta.UnitSatisfiabilitySpqrSessionLaws.spqrSessionLaws_iff

/--
info: 'Tacenta.UnitSatisfiabilitySpqrSessionLaws.spqrSessionLawsShape_of_parts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 rand_core_1.error.Error]
-/
#guard_msgs in
#print axioms Tacenta.UnitSatisfiabilitySpqrSessionLaws.spqrSessionLawsShape_of_parts

/--
info: Tacenta.UnitSatisfiabilitySpqrSessionLaws.spqrSessionLawsShape_of_parts (I : Tacenta.UnitSatisfiabilityJoint.Interp)
  (l : Tacenta.UnitSatisfiabilityJoint.StdLaws I) (vr : Tacenta.UnitSatisfiabilityJoint.VecRetainAxiomShape I)
  (z : Tacenta.UnitSatisfiabilityJoint.SpqrZeroizeShape I) :
  Tacenta.UnitSatisfiabilitySpqrSessionLaws.SpqrSessionLawsShape I
-/
#guard_msgs in
#check Tacenta.UnitSatisfiabilitySpqrSessionLaws.spqrSessionLawsShape_of_parts

/--
info: 'Tacenta.UnitSatisfiabilitySpqrSessionLaws.spqrSessionLaws_model' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 rand_core_1.error.Error]
-/
#guard_msgs in
#print axioms Tacenta.UnitSatisfiabilitySpqrSessionLaws.spqrSessionLaws_model

/--
info: Tacenta.UnitSatisfiabilitySpqrSessionLaws.spqrSessionLaws_model :
  Tacenta.UnitSatisfiabilitySpqrSessionLaws.SpqrSessionLawsShape Tacenta.UnitSatisfiabilityJoint.Interp.model
-/
#guard_msgs in
#check Tacenta.UnitSatisfiabilitySpqrSessionLaws.spqrSessionLaws_model

/--
info: 'Tacenta.UnitSatisfiabilitySpqrSessionLaws.spqrSessionLawsShape_fails_of_noop_pop' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 rand_core_1.error.Error]
-/
#guard_msgs in
#print axioms Tacenta.UnitSatisfiabilitySpqrSessionLaws.spqrSessionLawsShape_fails_of_noop_pop

/--
info: Tacenta.UnitSatisfiabilitySpqrSessionLaws.spqrSessionLawsShape_fails_of_noop_pop
  (I : Tacenta.UnitSatisfiabilityJoint.Interp)
  (hnoop : ∀ (T : Type) (v : alloc.vec.Vec T), I.vecPop Global v = ok (none, v)) :
  ¬Tacenta.UnitSatisfiabilitySpqrSessionLaws.SpqrSessionLawsShape I
-/
#guard_msgs in
#check Tacenta.UnitSatisfiabilitySpqrSessionLaws.spqrSessionLawsShape_fails_of_noop_pop

/--
info: structure Tacenta.UnitSatisfiabilitySpqrSessionLaws.SpqrSessionLaws : Prop
number of parameters: 0
fields:
  Tacenta.UnitSatisfiabilitySpqrSessionLaws.SpqrSessionLaws.pop : Tacenta.UnitSatisfiabilityRatchet.LawPop
  Tacenta.UnitSatisfiabilitySpqrSessionLaws.SpqrSessionLaws.asMut : Tacenta.UnitSatisfiabilityRatchet.LawAsMut
  Tacenta.UnitSatisfiabilitySpqrSessionLaws.SpqrSessionLaws.capacity : Tacenta.UnitSatisfiabilityRatchet.LawCapacity
  Tacenta.UnitSatisfiabilitySpqrSessionLaws.SpqrSessionLaws.vecZeroize : Tacenta.UnitSatisfiabilityRatchet.LawVecZeroize
  Tacenta.UnitSatisfiabilitySpqrSessionLaws.SpqrSessionLaws.arrayZeroize : Tacenta.SessionUnitSpqrT1.ZeroizeTotal
constructor:
  Tacenta.UnitSatisfiabilitySpqrSessionLaws.SpqrSessionLaws.mk (pop : Tacenta.UnitSatisfiabilityRatchet.LawPop)
    (asMut : Tacenta.UnitSatisfiabilityRatchet.LawAsMut) (capacity : Tacenta.UnitSatisfiabilityRatchet.LawCapacity)
    (vecZeroize : Tacenta.UnitSatisfiabilityRatchet.LawVecZeroize)
    (arrayZeroize : Tacenta.SessionUnitSpqrT1.ZeroizeTotal) : Tacenta.UnitSatisfiabilitySpqrSessionLaws.SpqrSessionLaws
-/
#guard_msgs in
#print Tacenta.UnitSatisfiabilitySpqrSessionLaws.SpqrSessionLaws

/--
info: structure Tacenta.UnitSatisfiabilitySpqrSessionLaws.SpqrSessionLawsShape (I : Tacenta.UnitSatisfiabilityJoint.Interp) :
  Prop
number of parameters: 1
fields:
  Tacenta.UnitSatisfiabilitySpqrSessionLaws.SpqrSessionLawsShape.pop : ∀ (T : Type) (v : alloc.vec.Vec T),
      ↑v ≠ [] → ∃ o w, I.vecPop Global v = ok (o, w) ∧ ↑w = (↑v).dropLast
  Tacenta.UnitSatisfiabilitySpqrSessionLaws.SpqrSessionLawsShape.asMut : ∀ (T : Type) (o : Option T),
      ∃ r, I.optionAsMut o = ok r
  Tacenta.UnitSatisfiabilitySpqrSessionLaws.SpqrSessionLawsShape.retainAxiom : Tacenta.UnitSatisfiabilityJoint.VecRetainAxiomShape
      I
  Tacenta.UnitSatisfiabilitySpqrSessionLaws.SpqrSessionLawsShape.arrayZeroize : Tacenta.UnitSatisfiabilityJoint.SpqrZeroizeShape
      I
constructor:
  Tacenta.UnitSatisfiabilitySpqrSessionLaws.SpqrSessionLawsShape.mk {I : Tacenta.UnitSatisfiabilityJoint.Interp}
    (pop : ∀ (T : Type) (v : alloc.vec.Vec T), ↑v ≠ [] → ∃ o w, I.vecPop Global v = ok (o, w) ∧ ↑w = (↑v).dropLast)
    (asMut : ∀ (T : Type) (o : Option T), ∃ r, I.optionAsMut o = ok r)
    (retainAxiom : Tacenta.UnitSatisfiabilityJoint.VecRetainAxiomShape I)
    (arrayZeroize : Tacenta.UnitSatisfiabilityJoint.SpqrZeroizeShape I) :
    Tacenta.UnitSatisfiabilitySpqrSessionLaws.SpqrSessionLawsShape I
-/
#guard_msgs in
#print Tacenta.UnitSatisfiabilitySpqrSessionLaws.SpqrSessionLawsShape

/--
info: def Tacenta.UnitSatisfiabilityRatchet.LawPop : Prop :=
∀ (T : Type) (v : alloc.vec.Vec T), ↑v ≠ [] → ∃ o w, alloc.vec.Vec.pop Global v = ok (o, w) ∧ ↑w = (↑v).dropLast
-/
#guard_msgs in
#print Tacenta.UnitSatisfiabilityRatchet.LawPop

/--
info: def Tacenta.UnitSatisfiabilityRatchet.LawAsMut : Prop :=
∀ (T : Type) (o : Option T), ∃ r, core.option.Option.as_mut o = ok r
-/
#guard_msgs in
#print Tacenta.UnitSatisfiabilityRatchet.LawAsMut

/--
info: def Tacenta.UnitSatisfiabilityRatchet.LawCapacity : Prop :=
∀ {T : Type} (A : Type) (v : alloc.vec.Vec T), ∃ r, alloc.vec.Vec.capacity A v = ok r
-/
#guard_msgs in
#print Tacenta.UnitSatisfiabilityRatchet.LawCapacity

/--
info: def Tacenta.UnitSatisfiabilityRatchet.LawVecZeroize : Prop :=
(∀ (v : alloc.vec.Vec (U64 × tacenta_spqr.Chains)),
    ∃ r,
      alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize
          (Pair.Insts.ZeroizeZeroize (zeroize.Zeroize.Blanket U64.Insts.ZeroizeDefaultIsZeroes)
            tacenta_spqr.Chains.Insts.ZeroizeZeroize)
          v =
        ok r) ∧
  (∀ (v : alloc.vec.Vec tacenta_spqr.Skipped),
      ∃ r, alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize tacenta_spqr.Skipped.Insts.ZeroizeZeroize v = ok r) ∧
    ∀ (v : alloc.vec.Vec tacenta_ratchet.SkippedKey),
      ∃ r, alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize tacenta_ratchet.SkippedKey.Insts.ZeroizeZeroize v = ok r
-/
#guard_msgs in
#print Tacenta.UnitSatisfiabilityRatchet.LawVecZeroize

