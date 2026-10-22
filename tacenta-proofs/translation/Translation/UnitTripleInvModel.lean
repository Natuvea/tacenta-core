import Translation.SessionUnitTripleT3
import Translation.SessionUnitRatchetImportInv
import Translation.SessionUnitWireT3

/-!
# `Triple::invariant` read through the Triple relation

The Triple relation the session refinement uses (`SessionUnitTripleT3.StateRefines` at the two field-for-field
abstractions `ratchetAbs` and `spqrAbs`) is an equality with an abstraction of the code state: it fixes every field of
the model Triple.  So the translated `Triple::invariant` is a property of the model state the code state refines, and
this module states it there.

## What it shows

* `ModelRatchetInv`, `ModelSpqrInv`, `ModelTripleInv`: the clauses of the classical ratchet's, the sparse ratchet's
  and the Triple's `invariant` (`ratchet/src/lib.rs`, `spqr/src/lib.rs`, `session-unit/src/tacenta_triple.rs`),
  restated about the model states: the stored-key bound, the clock below `u32::MAX`, every stored key no newer than
  the clock, the store a map on `(key, number)`, a receiving chain only with a sending chain and a peer key, the three
  kinds of curve key canonical (`Model.Messages.canonicalKey`); the sparse store bound, the epoch window of every chain
  (read with the code's saturating sum, `min u64::MAX (epoch + EPOCHS_KEPT)`), distinct chain epochs, the current
  epoch's chain present, every stored sparse key on a chain, the sparse store a map on `(epoch, number)`; and the
  roles clause (a sender that has not received sends `A2b`, a party with neither chain is `B2a`).
* `ratchet_inv_iff_model`, `spqr_inv_iff_model`: the existing `Inv` of each leaf (`SessionUnitRatchetImportInv`) holds
  of a translated state exactly when the model predicate holds of its abstraction.
* `triple_invariant_true_iff`: the translated `Triple::invariant` returns `true` exactly when both leaf invariants
  return `true` and the roles clause holds of the code state.
* `triple_invariant_iff_model`: **at every code Triple that refines a model Triple, `Triple::invariant` returns
  `true` exactly when `ModelTripleInv` holds of the model Triple.**  Both directions, no hypothesis beyond the relation.

## How

`invariant_true_iff` of each leaf turns the code's Boolean invariant into its `Inv`; each clause of `Inv` is carried
across the abstraction field by field.  The canonicity of a curve key goes through `canonicalKey_bytesOf`
(`SessionUnitWireT3`), an equality between the model's numeric check and the code's byte pattern; the store maps go
through injectivity of the byte reading and of the scalar values; the epoch window through `saturating_add_val`
(`SessionUnitSpqrT3`), the saturating sum's value.

## Trust

Every result here rests on the kernel alone (at most `propext`, `Classical.choice` and `Quot.sound`; the pins below list which); none calls a
refinement theorem and none rests on an opaque constant of the unit.

## What it does not show

* That any operation keeps `ModelTripleInv`: `UnitLifecycleSendPreserve` shows it for the model's send without an
  agreement output; no receive is covered.
* Anything about the session's own clauses (`Session::structural_invariant`) or the Braid's invariant.
* Anything about the counter ceilings the refinement theorems take (`CounterHeadroom`), which no `invariant` gives.
-/

open Aeneas Aeneas.Std Result
open tacenta_session_unit

namespace Tacenta.UnitTripleInvModel

/-! ## The model predicates -/

/-- The classical ratchet's `invariant`, about the model state: field for field with `SessionUnitRatchetImportInv.Ratchet.Inv`.
A stored key is `(ratchet key, number, stored at, message key)`. -/
structure ModelRatchetInv (m : Model.State.State) : Prop where
  store_bound : m.skipped.length ≤ Model.State.maxSkippedStore
  clock_room : m.events < Model.State.u32Max
  fresh : ∀ e ∈ m.skipped, e.2.2.1 ≤ m.events
  store_map : m.skipped.Pairwise (fun a t => ¬ (a.1 = t.1 ∧ a.2.1 = t.2.1))
  chains : m.ckr.isSome = true → m.cks.isSome = true ∧ m.dhrPub.isSome = true
  dhs_canonical : Model.Messages.canonicalKey m.dhsPub = true
  dhr_canonical : ∀ k, m.dhrPub = some k → Model.Messages.canonicalKey k = true
  store_canonical : ∀ e ∈ m.skipped, Model.Messages.canonicalKey e.1 = true

/-- The sparse ratchet's `invariant`, about the model state: field for field with `SessionUnitRatchetImportInv.Spqr.Inv`.
The window's upper end is the code's saturating sum, `min u64::MAX (epoch + EPOCHS_KEPT)`. -/
structure ModelSpqrInv (m : Model.SparseRatchet.State) : Prop where
  store_bound : m.skipped.length ≤ Model.SparseRatchet.maxSkippedStore
  epoch_window : ∀ q ∈ m.chains, q.1 ≤ m.epoch ∧
    m.epoch < min Model.SparseRatchet.u64Max (q.1 + Model.SparseRatchet.epochsKept)
  chains_distinct : m.chains.Pairwise (fun a b => a.1 ≠ b.1)
  current_present : ∃ q ∈ m.chains, q.1 = m.epoch
  skipped_chained : ∀ a ∈ m.skipped, ∃ q ∈ m.chains, q.1 = a.1
  skipped_map : m.skipped.Pairwise (fun a b => ¬ (a.1 = b.1 ∧ a.2.1 = b.2.1))

/-- The roles clause of `Triple::invariant`, about the model: a party with a sending chain and no receiving chain
started as the sender and sends `a2b`; a party with neither started as the receiver, `b2a`; otherwise nothing. -/
def ModelRolesAgree (m : Model.Triple.State) : Prop :=
  match m.classical.cks, m.classical.ckr with
  | some _, none => m.postQuantum.direction = .a2b
  | none, none => m.postQuantum.direction = .b2a
  | _, _ => True

/-- `Triple::invariant`, about the model Triple: both leaf invariants and the roles clause. -/
def ModelTripleInv (m : Model.Triple.State) : Prop :=
  ModelRatchetInv m.classical ∧ ModelSpqrInv m.postQuantum ∧ ModelRolesAgree m

/-- The roles clause of `Triple::invariant`, about the code Triple. -/
def RolesAgree (t : tacenta_triple.State) : Prop :=
  match t.classical.cks, t.classical.ckr with
  | some _, none => t.post_quantum.direction = .A2b
  | none, none => t.post_quantum.direction = .B2a
  | _, _ => True

/-! ## Carrying the leaf clauses across the abstraction -/

/-- The classical byte reading is injective on fixed-size arrays. -/
theorem keyOf_injective {n : Usize} {a b : Array Std.U8 n}
    (h : Tacenta.SessionUnitT3.keyOf a = Tacenta.SessionUnitT3.keyOf b) : a = b := by
  apply Subtype.ext
  refine (List.map_injective_iff.mpr ?_) h
  intro x y hxy
  have hx : x.val < 256 := by scalar_tac
  have hy : y.val < 256 := by scalar_tac
  have := congrArg UInt8.toNat hxy
  simp [Tacenta.SessionUnitT3.u8] at this
  scalar_tac

theorem keyOf_inj_iff {n : Usize} (a b : Array Std.U8 n) :
    Tacenta.SessionUnitT3.keyOf a = Tacenta.SessionUnitT3.keyOf b ↔ a = b :=
  ⟨keyOf_injective, fun h => h ▸ rfl⟩

/-- The model's canonicity of the byte reading of an array is the code's check of the array. -/
theorem canonicalKey_keyOf (k : Array Std.U8 32#usize) :
    Model.Messages.canonicalKey (Tacenta.SessionUnitT3.keyOf k) = Tacenta.SessionUnitT1.canonicalX25519 k := by
  have h := Tacenta.SessionUnitWireT3.canonicalKey_bytesOf k
  exact h

/-- `u32::MAX` is the model's `u32Max`. -/
theorem u32_max_eq_model : Std.U32.max = Model.State.u32Max := by
  simp [Std.U32.max_eq, Model.State.u32Max]

/-- `u64::MAX` is the model's `u64Max`. -/
theorem u64_max_eq_model : Std.U64.max = Model.SparseRatchet.u64Max := by
  simp [Std.U64.max_eq, Model.SparseRatchet.u64Max]

/-- **The classical `Inv` of a translated state is `ModelRatchetInv` of its abstraction.** -/
theorem ratchet_inv_iff_model (s : tacenta_ratchet.State) :
    Tacenta.SessionUnitRatchetImportInv.Ratchet.Inv s ↔
      ModelRatchetInv (Tacenta.SessionUnitTripleT3.ratchetAbs s) := by
  have hstore : tacenta_ratchet.MAX_SKIPPED_STORE.val = Model.State.maxSkippedStore := by
    simp [tacenta_ratchet.MAX_SKIPPED_STORE, Model.State.maxSkippedStore]
  have hpw : s.skipped.val.Pairwise (fun a t => ¬ (a.dh = t.dh ∧ a.n = t.n)) ↔
      (s.skipped.val.map Tacenta.SessionUnitT3.skippedOf).Pairwise
        (fun a t => ¬ (a.1 = t.1 ∧ a.2.1 = t.2.1)) := by
    rw [List.pairwise_map]
    apply List.Pairwise.iff
    intro a t
    simp only [Tacenta.SessionUnitT3.skippedOf, keyOf_inj_iff]
    constructor
    · intro h ⟨h1, h2⟩; exact h ⟨h1, by scalar_tac⟩
    · intro h ⟨h1, h2⟩; exact h ⟨h1, by rw [h2]⟩
  constructor
  · rintro ⟨hb, hr, hfresh, hp, hc, hdhs, hdhr, hcan⟩
    refine ⟨?_, ?_, ?_, hpw.mp hp, ?_, ?_, ?_, ?_⟩
    · simpa [Tacenta.SessionUnitTripleT3.ratchetAbs, hstore] using hb
    · simpa [Tacenta.SessionUnitTripleT3.ratchetAbs, u32_max_eq_model] using hr
    · simp only [Tacenta.SessionUnitTripleT3.ratchetAbs, List.mem_map]
      rintro _ ⟨e, he, rfl⟩
      exact hfresh e he
    · simpa [Tacenta.SessionUnitTripleT3.ratchetAbs] using hc
    · simpa [Tacenta.SessionUnitTripleT3.ratchetAbs, canonicalKey_keyOf] using hdhs
    · simp only [Tacenta.SessionUnitTripleT3.ratchetAbs, Option.map_eq_some_iff]
      rintro _ ⟨k, hk, rfl⟩
      rw [canonicalKey_keyOf]; exact hdhr k hk
    · simp only [Tacenta.SessionUnitTripleT3.ratchetAbs, List.mem_map]
      rintro _ ⟨e, he, rfl⟩
      simp only [Tacenta.SessionUnitT3.skippedOf]
      rw [canonicalKey_keyOf]; exact hcan e he
  · rintro ⟨hb, hr, hfresh, hp, hc, hdhs, hdhr, hcan⟩
    refine ⟨?_, ?_, ?_, hpw.mpr hp, ?_, ?_, ?_, ?_⟩
    · simpa [Tacenta.SessionUnitTripleT3.ratchetAbs, hstore] using hb
    · simpa [Tacenta.SessionUnitTripleT3.ratchetAbs, u32_max_eq_model] using hr
    · intro e he
      exact hfresh _ (List.mem_map.mpr ⟨e, he, rfl⟩)
    · simpa [Tacenta.SessionUnitTripleT3.ratchetAbs] using hc
    · simpa [Tacenta.SessionUnitTripleT3.ratchetAbs, canonicalKey_keyOf] using hdhs
    · intro k hk
      have := hdhr (Tacenta.SessionUnitT3.keyOf k) (by simp [Tacenta.SessionUnitTripleT3.ratchetAbs, hk])
      rwa [canonicalKey_keyOf] at this
    · intro e he
      have := hcan _ (List.mem_map.mpr ⟨e, he, rfl⟩)
      simp only [Tacenta.SessionUnitT3.skippedOf] at this
      rwa [canonicalKey_keyOf] at this

/-- The code's saturating window end, read as a natural. -/
theorem window_end_val (e : Std.U64) :
    (core.num.U64.saturating_add e tacenta_spqr.EPOCHS_KEPT).val =
      min Model.SparseRatchet.u64Max (e.val + Model.SparseRatchet.epochsKept) := by
  have h := Tacenta.SessionUnitSpqrT3.saturating_add_val e tacenta_spqr.EPOCHS_KEPT
  have hk : tacenta_spqr.EPOCHS_KEPT.val = Model.SparseRatchet.epochsKept := by
    simp [tacenta_spqr.EPOCHS_KEPT, Model.SparseRatchet.epochsKept]
  rw [← u64_max_eq_model, ← hk]
  exact h

/-- **The sparse `Inv` of a translated state is `ModelSpqrInv` of its abstraction.** -/
theorem spqr_inv_iff_model (s : tacenta_spqr.State) :
    Tacenta.SessionUnitRatchetImportInv.Spqr.Inv s ↔
      ModelSpqrInv (Tacenta.SessionUnitTripleT3.spqrAbs s) := by
  have hstore : tacenta_spqr.MAX_SKIPPED_STORE.val = Model.SparseRatchet.maxSkippedStore := by
    simp [tacenta_spqr.MAX_SKIPPED_STORE, Model.SparseRatchet.maxSkippedStore, Model.State.maxSkippedStore]
  have hd : s.chains.val.Pairwise (fun a b => a.1 ≠ b.1) ↔
      (s.chains.val.map Tacenta.SessionUnitSpqrT3.chainsEntryOf).Pairwise (fun a b => a.1 ≠ b.1) := by
    rw [List.pairwise_map]
    apply List.Pairwise.iff
    intro a b
    simp only [Tacenta.SessionUnitSpqrT3.chainsEntryOf, ne_eq]
    constructor
    · intro h h'; exact h (by scalar_tac)
    · intro h h'; exact h (by rw [h'])
  have hm : s.skipped.val.Pairwise (fun a b => ¬ (a.epoch = b.epoch ∧ a.n = b.n)) ↔
      (s.skipped.val.map Tacenta.SessionUnitSpqrT3.skippedOf).Pairwise
        (fun a b => ¬ (a.1 = b.1 ∧ a.2.1 = b.2.1)) := by
    rw [List.pairwise_map]
    apply List.Pairwise.iff
    intro a b
    simp only [Tacenta.SessionUnitSpqrT3.skippedOf]
    constructor
    · intro h ⟨h1, h2⟩; exact h ⟨by scalar_tac, by scalar_tac⟩
    · intro h ⟨h1, h2⟩; exact h ⟨by rw [h1], by rw [h2]⟩
  constructor
  · rintro ⟨hb, hw, hdist, ⟨q, hq, hqe⟩, hsc, hsm⟩
    refine ⟨?_, ?_, hd.mp hdist, ?_, ?_, hm.mp hsm⟩
    · simpa [Tacenta.SessionUnitTripleT3.spqrAbs, hstore] using hb
    · simp only [Tacenta.SessionUnitTripleT3.spqrAbs, List.mem_map]
      rintro _ ⟨q, hq, rfl⟩
      obtain ⟨h1, h2⟩ := hw q hq
      simp only [Tacenta.SessionUnitSpqrT3.chainsEntryOf]
      rw [← window_end_val]
      exact ⟨h1, h2⟩
    · exact ⟨Tacenta.SessionUnitSpqrT3.chainsEntryOf q, List.mem_map.mpr ⟨q, hq, rfl⟩,
        by simp [Tacenta.SessionUnitSpqrT3.chainsEntryOf, Tacenta.SessionUnitTripleT3.spqrAbs, hqe]⟩
    · simp only [Tacenta.SessionUnitTripleT3.spqrAbs, List.mem_map]
      rintro _ ⟨a, ha, rfl⟩
      obtain ⟨q, hq, hqa⟩ := hsc a ha
      exact ⟨Tacenta.SessionUnitSpqrT3.chainsEntryOf q, ⟨q, hq, rfl⟩,
        by simp [Tacenta.SessionUnitSpqrT3.chainsEntryOf, Tacenta.SessionUnitSpqrT3.skippedOf, hqa]⟩
  · rintro ⟨hb, hw, hdist, ⟨q, hq, hqe⟩, hsc, hsm⟩
    refine ⟨?_, ?_, hd.mpr hdist, ?_, ?_, hm.mpr hsm⟩
    · simpa [Tacenta.SessionUnitTripleT3.spqrAbs, hstore] using hb
    · intro q hq
      have := hw _ (List.mem_map.mpr ⟨q, hq, rfl⟩)
      simp only [Tacenta.SessionUnitSpqrT3.chainsEntryOf, Tacenta.SessionUnitTripleT3.spqrAbs] at this
      rw [window_end_val]
      exact this
    · simp only [Tacenta.SessionUnitTripleT3.spqrAbs, List.mem_map] at hq hqe
      obtain ⟨q', hq', rfl⟩ := hq
      exact ⟨q', hq', by simp [Tacenta.SessionUnitSpqrT3.chainsEntryOf] at hqe; scalar_tac⟩
    · intro a ha
      obtain ⟨q, hq, hqa⟩ := hsc _ (List.mem_map.mpr ⟨a, ha, rfl⟩)
      simp only [Tacenta.SessionUnitTripleT3.spqrAbs, List.mem_map] at hq
      obtain ⟨q', hq', rfl⟩ := hq
      exact ⟨q', hq', by
        simp [Tacenta.SessionUnitSpqrT3.chainsEntryOf, Tacenta.SessionUnitSpqrT3.skippedOf] at hqa; scalar_tac⟩

/-! ## The Triple's invariant -/

/-- **The translated `Triple::invariant` returns `true` exactly when both leaf invariants return `true` and the roles
clause holds.** -/
theorem triple_invariant_true_iff (t : tacenta_triple.State) :
    tacenta_triple.State.invariant t = ok true ↔
      tacenta_ratchet.State.invariant t.classical = ok true ∧
        tacenta_spqr.State.invariant t.post_quantum = ok true ∧ RolesAgree t := by
  have h1 := Tacenta.SessionUnitRatchetImportInv.Ratchet.invariant_eq t.classical
  have h2 := Tacenta.SessionUnitRatchetImportInv.Spqr.invariant_eq t.post_quantum
  unfold tacenta_triple.State.invariant RolesAgree
  rw [h1, h2]
  simp only [tacenta_spqr.State.impl.direction, tacenta_ratchet.State.started_as_sender, bind_tc_ok]
  rcases t with ⟨⟨_, _, _, cks, ckr, _, _, _, _, _, _⟩, ⟨_, _, _, _, dir⟩⟩
  rcases cks with _ | _ <;> rcases ckr with _ | _ <;> cases dir <;>
    cases Tacenta.SessionUnitRatchetImportInv.Ratchet.InvB _ <;>
    cases Tacenta.SessionUnitRatchetImportInv.Spqr.InvB _ <;> simp

/-- The roles clause of the code Triple is the model's of the Triple it refines. -/
theorem rolesAgree_iff_model {t : tacenta_triple.State} {m : Model.Triple.State}
    (h : Tacenta.SessionUnitTripleT3.StateRefines Tacenta.SessionUnitTripleT3.ratchetAbs
      Tacenta.SessionUnitTripleT3.spqrAbs t m) :
    RolesAgree t ↔ ModelRolesAgree m := by
  obtain ⟨hc, hq⟩ := h
  obtain ⟨mc, mq⟩ := m
  simp only at hc hq
  subst hc hq
  unfold RolesAgree ModelRolesAgree
  rcases t with ⟨⟨_, _, _, cks, ckr, _, _, _, _, _, _⟩, ⟨_, _, _, _, dir⟩⟩
  rcases cks with _ | _ <;> rcases ckr with _ | _ <;> cases dir <;>
    simp [Tacenta.SessionUnitTripleT3.ratchetAbs, Tacenta.SessionUnitTripleT3.spqrAbs,
      Tacenta.SessionUnitSpqrT3.directionOf]

/-- **At every code Triple that refines a model Triple, `Triple::invariant` returns `true` exactly when
`ModelTripleInv` holds of the model Triple.**  The relation is the one `SessionRefines` carries; nothing else is
assumed. -/
theorem triple_invariant_iff_model {t : tacenta_triple.State} {m : Model.Triple.State}
    (h : Tacenta.SessionUnitTripleT3.StateRefines Tacenta.SessionUnitTripleT3.ratchetAbs
      Tacenta.SessionUnitTripleT3.spqrAbs t m) :
    tacenta_triple.State.invariant t = ok true ↔ ModelTripleInv m := by
  rw [triple_invariant_true_iff, rolesAgree_iff_model h,
    Tacenta.SessionUnitRatchetImportInv.Ratchet.invariant_true_iff,
    Tacenta.SessionUnitRatchetImportInv.Spqr.invariant_true_iff,
    ratchet_inv_iff_model, spqr_inv_iff_model]
  obtain ⟨hc, hq⟩ := h
  rw [hc, hq]
  rfl

end Tacenta.UnitTripleInvModel

/-! ## Pins

The constants each result depends on, and the statement of each result and definition, held by the
build.  `attest.py` requires every one of them (`REQUIRED_PINS`, `REQUIRED_STATEMENT_PINS`,
`REQUIRED_PRINT_FORM`). -/

/--
info: 'Tacenta.UnitTripleInvModel.keyOf_injective' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitTripleInvModel.keyOf_injective

/--
info: 'Tacenta.UnitTripleInvModel.keyOf_inj_iff' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitTripleInvModel.keyOf_inj_iff

/--
info: 'Tacenta.UnitTripleInvModel.canonicalKey_keyOf' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitTripleInvModel.canonicalKey_keyOf

/--
info: 'Tacenta.UnitTripleInvModel.u32_max_eq_model' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Tacenta.UnitTripleInvModel.u32_max_eq_model

/--
info: 'Tacenta.UnitTripleInvModel.u64_max_eq_model' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Tacenta.UnitTripleInvModel.u64_max_eq_model

/--
info: 'Tacenta.UnitTripleInvModel.ratchet_inv_iff_model' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitTripleInvModel.ratchet_inv_iff_model

/--
info: 'Tacenta.UnitTripleInvModel.window_end_val' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitTripleInvModel.window_end_val

/--
info: 'Tacenta.UnitTripleInvModel.spqr_inv_iff_model' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitTripleInvModel.spqr_inv_iff_model

/--
info: 'Tacenta.UnitTripleInvModel.triple_invariant_true_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitTripleInvModel.triple_invariant_true_iff

/--
info: 'Tacenta.UnitTripleInvModel.rolesAgree_iff_model' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitTripleInvModel.rolesAgree_iff_model

/--
info: 'Tacenta.UnitTripleInvModel.triple_invariant_iff_model' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitTripleInvModel.triple_invariant_iff_model

/--
info: @Tacenta.UnitTripleInvModel.keyOf_injective : ∀ {n : Usize} {a b : Std.Array U8 n},
  Tacenta.SessionUnitT3.keyOf a = Tacenta.SessionUnitT3.keyOf b → a = b
-/
#guard_msgs in
#check @Tacenta.UnitTripleInvModel.keyOf_injective

/--
info: @Tacenta.UnitTripleInvModel.keyOf_inj_iff : ∀ {n : Usize} (a b : Std.Array U8 n),
  Tacenta.SessionUnitT3.keyOf a = Tacenta.SessionUnitT3.keyOf b ↔ a = b
-/
#guard_msgs in
#check @Tacenta.UnitTripleInvModel.keyOf_inj_iff

/--
info: Tacenta.UnitTripleInvModel.canonicalKey_keyOf : ∀ (k : Std.Array U8 32#usize),
  Model.Messages.canonicalKey (Tacenta.SessionUnitT3.keyOf k) = Tacenta.SessionUnitT1.canonicalX25519 k
-/
#guard_msgs in
#check @Tacenta.UnitTripleInvModel.canonicalKey_keyOf

/--
info: Tacenta.UnitTripleInvModel.u32_max_eq_model : U32.max = Model.State.u32Max
-/
#guard_msgs in
#check @Tacenta.UnitTripleInvModel.u32_max_eq_model

/--
info: Tacenta.UnitTripleInvModel.u64_max_eq_model : U64.max = Model.SparseRatchet.u64Max
-/
#guard_msgs in
#check @Tacenta.UnitTripleInvModel.u64_max_eq_model

/--
info: Tacenta.UnitTripleInvModel.ratchet_inv_iff_model : ∀ (s : tacenta_ratchet.State),
  Tacenta.SessionUnitRatchetImportInv.Ratchet.Inv s ↔
    Tacenta.UnitTripleInvModel.ModelRatchetInv (Tacenta.SessionUnitTripleT3.ratchetAbs s)
-/
#guard_msgs in
#check @Tacenta.UnitTripleInvModel.ratchet_inv_iff_model

/--
info: Tacenta.UnitTripleInvModel.window_end_val : ∀ (e : U64),
  ↑(core.num.U64.saturating_add e tacenta_spqr.EPOCHS_KEPT) =
    min Model.SparseRatchet.u64Max (↑e + Model.SparseRatchet.epochsKept)
-/
#guard_msgs in
#check @Tacenta.UnitTripleInvModel.window_end_val

/--
info: Tacenta.UnitTripleInvModel.spqr_inv_iff_model : ∀ (s : tacenta_spqr.State),
  Tacenta.SessionUnitRatchetImportInv.Spqr.Inv s ↔
    Tacenta.UnitTripleInvModel.ModelSpqrInv (Tacenta.SessionUnitTripleT3.spqrAbs s)
-/
#guard_msgs in
#check @Tacenta.UnitTripleInvModel.spqr_inv_iff_model

/--
info: Tacenta.UnitTripleInvModel.triple_invariant_true_iff : ∀ (t : tacenta_triple.State),
  t.invariant = ok true ↔
    t.classical.invariant = ok true ∧ t.post_quantum.invariant = ok true ∧ Tacenta.UnitTripleInvModel.RolesAgree t
-/
#guard_msgs in
#check @Tacenta.UnitTripleInvModel.triple_invariant_true_iff

/--
info: @Tacenta.UnitTripleInvModel.rolesAgree_iff_model : ∀ {t : tacenta_triple.State} {m : Model.Triple.State},
  Tacenta.SessionUnitTripleT3.StateRefines Tacenta.SessionUnitTripleT3.ratchetAbs Tacenta.SessionUnitTripleT3.spqrAbs t
      m →
    (Tacenta.UnitTripleInvModel.RolesAgree t ↔ Tacenta.UnitTripleInvModel.ModelRolesAgree m)
-/
#guard_msgs in
#check @Tacenta.UnitTripleInvModel.rolesAgree_iff_model

/--
info: @Tacenta.UnitTripleInvModel.triple_invariant_iff_model : ∀ {t : tacenta_triple.State} {m : Model.Triple.State},
  Tacenta.SessionUnitTripleT3.StateRefines Tacenta.SessionUnitTripleT3.ratchetAbs Tacenta.SessionUnitTripleT3.spqrAbs t
      m →
    (t.invariant = ok true ↔ Tacenta.UnitTripleInvModel.ModelTripleInv m)
-/
#guard_msgs in
#check @Tacenta.UnitTripleInvModel.triple_invariant_iff_model

/--
info: structure Tacenta.UnitTripleInvModel.ModelRatchetInv (m : Model.State.State) : Prop
number of parameters: 1
fields:
  Tacenta.UnitTripleInvModel.ModelRatchetInv.store_bound : m.skipped.length ≤ Model.State.maxSkippedStore
  Tacenta.UnitTripleInvModel.ModelRatchetInv.clock_room : m.events < Model.State.u32Max
  Tacenta.UnitTripleInvModel.ModelRatchetInv.fresh : ∀ e ∈ m.skipped, e.2.2.1 ≤ m.events
  Tacenta.UnitTripleInvModel.ModelRatchetInv.store_map : List.Pairwise (fun a t => ¬(a.1 = t.1 ∧ a.2.1 = t.2.1))
      m.skipped
  Tacenta.UnitTripleInvModel.ModelRatchetInv.chains : m.ckr.isSome = true → m.cks.isSome = true ∧ m.dhrPub.isSome = true
  Tacenta.UnitTripleInvModel.ModelRatchetInv.dhs_canonical : Model.Messages.canonicalKey m.dhsPub = true
  Tacenta.UnitTripleInvModel.ModelRatchetInv.dhr_canonical : ∀ (k : Model.State.Key),
      m.dhrPub = some k → Model.Messages.canonicalKey k = true
  Tacenta.UnitTripleInvModel.ModelRatchetInv.store_canonical : ∀ e ∈ m.skipped, Model.Messages.canonicalKey e.1 = true
constructor:
  Tacenta.UnitTripleInvModel.ModelRatchetInv.mk {m : Model.State.State}
    (store_bound : m.skipped.length ≤ Model.State.maxSkippedStore) (clock_room : m.events < Model.State.u32Max)
    (fresh : ∀ e ∈ m.skipped, e.2.2.1 ≤ m.events)
    (store_map : List.Pairwise (fun a t => ¬(a.1 = t.1 ∧ a.2.1 = t.2.1)) m.skipped)
    (chains : m.ckr.isSome = true → m.cks.isSome = true ∧ m.dhrPub.isSome = true)
    (dhs_canonical : Model.Messages.canonicalKey m.dhsPub = true)
    (dhr_canonical : ∀ (k : Model.State.Key), m.dhrPub = some k → Model.Messages.canonicalKey k = true)
    (store_canonical : ∀ e ∈ m.skipped, Model.Messages.canonicalKey e.1 = true) :
    Tacenta.UnitTripleInvModel.ModelRatchetInv m
-/
#guard_msgs in
#print Tacenta.UnitTripleInvModel.ModelRatchetInv

/--
info: structure Tacenta.UnitTripleInvModel.ModelSpqrInv (m : Model.SparseRatchet.State) : Prop
number of parameters: 1
fields:
  Tacenta.UnitTripleInvModel.ModelSpqrInv.store_bound : m.skipped.length ≤ Model.SparseRatchet.maxSkippedStore
  Tacenta.UnitTripleInvModel.ModelSpqrInv.epoch_window : ∀ q ∈ m.chains,
      q.1 ≤ m.epoch ∧ m.epoch < min Model.SparseRatchet.u64Max (q.1 + Model.SparseRatchet.epochsKept)
  Tacenta.UnitTripleInvModel.ModelSpqrInv.chains_distinct : List.Pairwise (fun a b => a.1 ≠ b.1) m.chains
  Tacenta.UnitTripleInvModel.ModelSpqrInv.current_present : ∃ q ∈ m.chains, q.1 = m.epoch
  Tacenta.UnitTripleInvModel.ModelSpqrInv.skipped_chained : ∀ a ∈ m.skipped, ∃ q ∈ m.chains, q.1 = a.1
  Tacenta.UnitTripleInvModel.ModelSpqrInv.skipped_map : List.Pairwise (fun a b => ¬(a.1 = b.1 ∧ a.2.1 = b.2.1))
      m.skipped
constructor:
  Tacenta.UnitTripleInvModel.ModelSpqrInv.mk {m : Model.SparseRatchet.State}
    (store_bound : m.skipped.length ≤ Model.SparseRatchet.maxSkippedStore)
    (epoch_window :
      ∀ q ∈ m.chains, q.1 ≤ m.epoch ∧ m.epoch < min Model.SparseRatchet.u64Max (q.1 + Model.SparseRatchet.epochsKept))
    (chains_distinct : List.Pairwise (fun a b => a.1 ≠ b.1) m.chains) (current_present : ∃ q ∈ m.chains, q.1 = m.epoch)
    (skipped_chained : ∀ a ∈ m.skipped, ∃ q ∈ m.chains, q.1 = a.1)
    (skipped_map : List.Pairwise (fun a b => ¬(a.1 = b.1 ∧ a.2.1 = b.2.1)) m.skipped) :
    Tacenta.UnitTripleInvModel.ModelSpqrInv m
-/
#guard_msgs in
#print Tacenta.UnitTripleInvModel.ModelSpqrInv

/--
info: def Tacenta.UnitTripleInvModel.ModelRolesAgree : Model.Triple.State → Prop :=
fun m =>
  match m.classical.cks, m.classical.ckr with
  | some val, none => m.postQuantum.direction = Model.SparseRatchet.Direction.a2b
  | none, none => m.postQuantum.direction = Model.SparseRatchet.Direction.b2a
  | x, x_1 => True
-/
#guard_msgs in
#print Tacenta.UnitTripleInvModel.ModelRolesAgree

/--
info: def Tacenta.UnitTripleInvModel.ModelTripleInv : Model.Triple.State → Prop :=
fun m =>
  Tacenta.UnitTripleInvModel.ModelRatchetInv m.classical ∧
    Tacenta.UnitTripleInvModel.ModelSpqrInv m.postQuantum ∧ Tacenta.UnitTripleInvModel.ModelRolesAgree m
-/
#guard_msgs in
#print Tacenta.UnitTripleInvModel.ModelTripleInv

/--
info: def Tacenta.UnitTripleInvModel.RolesAgree : tacenta_triple.State → Prop :=
fun t =>
  match t.classical.cks, t.classical.ckr with
  | some val, none => t.post_quantum.direction = tacenta_spqr.Direction.A2b
  | none, none => t.post_quantum.direction = tacenta_spqr.Direction.B2a
  | x, x_1 => True
-/
#guard_msgs in
#print Tacenta.UnitTripleInvModel.RolesAgree
