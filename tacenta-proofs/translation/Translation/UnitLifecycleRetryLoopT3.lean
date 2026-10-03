import Translation.UnitLifecycleInitialDispatch
import Batteries.Tactic.OpenPrivate

/-!
# The eviction retry loop refines the model loop, for every fuel

`receive_with_eviction` retries a Triple receive that a full skipped-key store refused: it evicts
the oldest stored keys from a working copy of the half that complained and receives again,
doubling the batch while the same half complains and recomputing it when the other half does,
until a receive succeeds, refuses for another reason, or an eviction removes nothing.  The model's
twin is the fuel-indexed `Model.Lifecycle.receiveWithEvictionLoop`, observed through the public
relation `ReceiveWithEvictionLoopResult`.

`receive_with_eviction_loop_refines` is the induction: for every fuel larger than the number of
keys the model state holds, from related states the generated loop returns, and its outcome is
related to the model loop's result at that fuel.  A success is the model's success with related
state and key, and a refusal on an empty eviction is the pending full-store refusal on both sides.
A retry that refuses for a reason other than a full store is reduced to one Triple receive: the
generated attempt refused at a working state related to the model's, and if that single refusal is
the model's detailed refusal, the loop results agree (`OpenRefusal`).  No theorem of this tree
relates such a refusal to the model, so that case is left open, named.

## The batch

The generated loop doubles a `usize` with `saturating_add` and computes the first batch of each half
with saturating arithmetic; the model uses natural numbers.  `BatchCovers len c m` says the two
batches are equal, or both at least `len`, the length of the half's store, so the two evictions
remove the same keys (an eviction of at least the store's length removes all of it).  This relation
needs no bound on the header's counters: the store bounds of `LoopRel` (each store at most
`2^32 - 1 - 2000`) are enough for the saturated first batch to cover the store.

## The private model loop

The one model fact not exposed by `Model/Lifecycle.lean` is that a retry refused for a reason that is
not a full store ends the loop with that refusal.  `receiveWithEvictionLoopResult_stop` proves it by
naming the private loop through `open private`; no model definition changes.
-/

namespace Tacenta.UnitLifecycleRetryLoopT3

open Aeneas Aeneas.Std Result
open tacenta_session_unit
open Tacenta.UnitLifecycleT3

/-! ## The model loop stops on a refusal that is not a full store -/

open private receiveWithEvictionLoop from Model.Lifecycle in
theorem receiveWithEvictionLoopResult_stop
    (state : Model.Triple.State)
    (composite : Model.CompositeHeader.Composite) (header : Model.Triple.Header)
    (dhOutRecv dhOutSend newDhsPub : Model.Lifecycle.Key)
    (output : Option Model.SparseRatchet.Output)
    (pending reason : Model.Triple.ReceiveRefusal)
    (half : Model.Lifecycle.FullStore) (batch fuel : Nat)
    (evictedState : Model.Triple.State) (evicted : Nat)
    (hEvict : (match half with
      | .classical => Model.Triple.evictOldestClassical state batch
      | .postQuantum => Model.Triple.evictOldestPostQuantum state batch) =
        (evictedState, evicted))
    (hNonzero : evicted ≠ 0)
    (hRetry : Model.Triple.receiveDetailed evictedState header
      dhOutRecv dhOutSend newDhsPub output = .error reason)
    (hFull : Model.Lifecycle.fullStore reason = none) :
    Model.Lifecycle.ReceiveWithEvictionLoopResult state composite header dhOutRecv dhOutSend
      newDhsPub output pending half batch (fuel + 1) (.error reason) := by
  unfold Model.Lifecycle.ReceiveWithEvictionLoopResult
  cases half <;> simp [receiveWithEvictionLoop, hEvict, hNonzero, hRetry, hFull]

/-- The public relation is functional. -/
theorem loopResult_functional
    {state : Model.Triple.State}
    {composite : Model.CompositeHeader.Composite} {header : Model.Triple.Header}
    {dhOutRecv dhOutSend newDhsPub : Model.Lifecycle.Key}
    {output : Option Model.SparseRatchet.Output}
    {pending : Model.Triple.ReceiveRefusal} {half : Model.Lifecycle.FullStore}
    {batch fuel : Nat}
    {left right : Except Model.Triple.ReceiveRefusal (Model.Triple.State × Model.Lifecycle.Key)}
    (hl : Model.Lifecycle.ReceiveWithEvictionLoopResult state composite header dhOutRecv dhOutSend
      newDhsPub output pending half batch fuel left)
    (hr : Model.Lifecycle.ReceiveWithEvictionLoopResult state composite header dhOutRecv dhOutSend
      newDhsPub output pending half batch fuel right) : left = right := by
  unfold Model.Lifecycle.ReceiveWithEvictionLoopResult at hl hr
  exact hl.symm.trans hr

/-- The relation has a value at every argument. -/
theorem loopResult_exists
    (state : Model.Triple.State)
    (composite : Model.CompositeHeader.Composite) (header : Model.Triple.Header)
    (dhOutRecv dhOutSend newDhsPub : Model.Lifecycle.Key)
    (output : Option Model.SparseRatchet.Output)
    (pending : Model.Triple.ReceiveRefusal) (half : Model.Lifecycle.FullStore)
    (batch fuel : Nat) :
    ∃ result, Model.Lifecycle.ReceiveWithEvictionLoopResult state composite header dhOutRecv
      dhOutSend newDhsPub output pending half batch fuel result :=
  ⟨_, rfl⟩

/-! ## Arithmetic of the generated helpers -/

theorem usize_sat_sub_val (left right : Std.Usize) :
    (core.num.Usize.saturating_sub left right).val = left.val - right.val := by
  unfold core.num.Usize.saturating_sub UScalar.saturating_sub UScalar.val
  simp only [BitVec.toNat_ofNat, Nat.zero_max]
  rw [Nat.mod_eq_of_lt]
  exact Nat.lt_of_le_of_lt (Nat.sub_le left.bv.toNat right.bv.toNat) left.bv.isLt

theorem u64_sat_sub_val (left right : Std.U64) :
    (core.num.U64.saturating_sub left right).val = left.val - right.val := by
  unfold core.num.U64.saturating_sub UScalar.saturating_sub UScalar.val
  simp only [BitVec.toNat_ofNat, Nat.zero_max]
  rw [Nat.mod_eq_of_lt]
  exact Nat.lt_of_le_of_lt (Nat.sub_le left.bv.toNat right.bv.toNat) left.bv.isLt

theorem cast_u32_usize (value : Std.U32) :
    (UScalar.cast .Usize value).val = value.val := by
  rw [UScalar.cast_val_eq]
  exact Nat.mod_eq_of_lt (by scalar_tac)

theorem saturating_usize_from_u64_val (value : Std.U64) :
    ∃ result, lifecycle.saturating_usize_from_u64 value = ok result ∧
      result.val = min Usize.max value.val := by
  unfold lifecycle.saturating_usize_from_u64
  simp [lift]
  split
  · rename_i hlarge
    refine ⟨core.num.Usize.MAX, rfl, ?_⟩
    rw [Nat.min_eq_left (Nat.le_of_lt hlarge)]
    simp [core.num.Usize.MAX, UScalar.ofNatCore_val_eq]
  · rename_i hsmall
    refine ⟨UScalar.cast .Usize value, rfl, ?_⟩
    rw [UScalar.cast_val_eq]
    have hle : value.val ≤ Usize.max := by omega
    rw [Nat.mod_eq_of_lt]
    · exact (Nat.min_eq_right hle).symm
    · exact lt_of_le_of_lt hle (by simp [Usize.max, Usize.numBits])

theorem cMax_le_usize_max : UScalar.cMax UScalarTy.Usize ≤ Usize.max := by
  have h : UScalar.cMax UScalarTy.Usize = 4294967295 := by decide
  rw [h]
  exact Tacenta.SessionUnitSessionT1.small_le_usize_max le_rfl

theorem cMax_usize_eq : UScalar.cMax UScalarTy.Usize = 4294967295 := by decide

/-! ## Batches -/

/-- The length of the store of one half. -/
def halfLength : lifecycle.FullStore → Model.Triple.State → Nat
  | .Classical, m => Model.Triple.classicalSkippedLength m
  | .PostQuantum, m => Model.Triple.postQuantumSkippedLength m

/-- The model's eviction from one half. -/
def evictHalf : Model.Lifecycle.FullStore → Model.Triple.State → Nat → Model.Triple.State × Nat
  | .classical, m, count => Model.Triple.evictOldestClassical m count
  | .postQuantum, m, count => Model.Triple.evictOldestPostQuantum m count

theorem evictHalf_eq_match (half : Model.Lifecycle.FullStore) (m : Model.Triple.State)
    (count : Nat) :
    evictHalf half m count = (match half with
      | .classical => Model.Triple.evictOldestClassical m count
      | .postQuantum => Model.Triple.evictOldestPostQuantum m count) := by
  cases half <;> rfl

/-- The concrete and model batches remove the same keys: they are equal, or both cover the
half's store. -/
def BatchCovers (len : Nat) (concrete : Std.Usize) (model : Nat) : Prop :=
  concrete.val = model ∨ (len ≤ concrete.val ∧ len ≤ model)

theorem evictHalf_congr_of_covers (half : lifecycle.FullStore) (m : Model.Triple.State)
    (batch : Std.Usize) (modelBatch : Nat)
    (h : BatchCovers (halfLength half m) batch modelBatch) :
    evictHalf (fullStoreOfReal half) m batch.val =
      evictHalf (fullStoreOfReal half) m modelBatch := by
  rcases h with heq | ⟨hc, hm⟩
  · rw [heq]
  · cases half
    · simp only [fullStoreOfReal, evictHalf, Model.Triple.evictOldestClassical]
      rw [Model.Ratchet.evictOldest_congr_of_length_le m.classical batch.val modelBatch hc hm]
    · simp only [fullStoreOfReal, evictHalf, Model.Triple.evictOldestPostQuantum]
      rw [Model.SparseRatchet.evictOldest_congr_of_length_le m.postQuantum batch.val
        modelBatch hc hm]

/-- Doubling keeps the relation, at a store that has not grown. -/
theorem batchCovers_double {len len' : Nat} {batch : Std.Usize} {modelBatch : Nat}
    (h : BatchCovers len batch modelBatch) (hlen : len' ≤ len) (hmax : len ≤ Usize.max) :
    BatchCovers len' (core.num.Usize.saturating_add batch batch) (modelBatch * 2) := by
  have hval := Tacenta.UnitLifecycleT3.usize_saturating_add_val batch batch
  unfold BatchCovers at h ⊢
  rcases h with heq | ⟨hc, hm⟩
  · by_cases hfit : batch.val + batch.val ≤ Usize.max
    · left; omega
    · right; omega
  · right; omega

/-! ## The first batch of each half covers its store -/

theorem shortfall_classical_covers
    (state : tacenta_triple.State) (modelState : Model.Triple.State)
    (composite : tacenta_wire.Composite) (modelComposite : Model.CompositeHeader.Composite)
    (hstate : Tacenta.SessionUnitTripleT3.StateRefines
      Tacenta.SessionUnitTripleT3.ratchetAbs Tacenta.SessionUnitTripleT3.spqrAbs state modelState)
    (hcomposite : CompositeRefines composite modelComposite)
    (hstore : Model.Triple.classicalSkippedLength modelState + Model.State.maxSkippedStore ≤
      UScalar.cMax UScalarTy.Usize) :
    ∃ batch, lifecycle.receive_shortfall lifecycle.FullStore.Classical state composite = ok batch ∧
      BatchCovers (halfLength .Classical modelState) batch
        (Model.Lifecycle.receiveShortfall .classical modelState modelComposite) := by
  have hcm := cMax_le_usize_max
  have hheld := congrArg (fun s : Model.State.State => s.skipped.length) hstate.1
  simp [Tacenta.SessionUnitTripleT3.ratchetAbs] at hheld
  have hreceive := congrArg (fun s : Model.State.State => s.nr) hstate.1
  simp [Tacenta.SessionUnitTripleT3.ratchetAbs] at hreceive
  simp only [lifecycle.receive_shortfall, tacenta_triple.State.classical_skipped_len,
    tacenta_ratchet.State.skipped_len, tacenta_triple.State.receive_count,
    tacenta_ratchet.State.receive_count, lift, bind_tc_ok]
  have hm := Tacenta.SessionUnitT3.max_skipped_store_agrees
  have hlen : state.classical.skipped.len.val = state.classical.skipped.val.length := by
    simp [alloc.vec.Vec.len]
  have h4 : 4294967295 ≤ Usize.max := Tacenta.SessionUnitSessionT1.small_le_usize_max le_rfl
  have hc := cMax_usize_eq
  have hsat := Tacenta.UnitLifecycleT3.usize_saturating_add_val
  split
  · rename_i hlt
    refine ⟨1#usize, rfl, Or.inl ?_⟩
    have hlt' := (UScalar.lt_equiv _ _).mp hlt
    simp only [usize_sat_sub_val, hsat, cast_u32_usize] at hlt'
    simp only [Model.Lifecycle.receiveShortfall, Model.Triple.classicalSkippedLength,
      Model.Triple.receiveCount] at hstore ⊢
    simp only [UScalar.ofNatCore_val_eq] at hlt' ⊢
    have hn := hcomposite.n
    simp only [Model.State.maxSkippedStore] at hlt' hstore hm ⊢
    omega
  · rename_i hge
    refine ⟨_, rfl, ?_⟩
    have hge' : ¬ _ := fun h => hge ((UScalar.lt_equiv _ _).mpr h)
    simp only [usize_sat_sub_val, hsat, cast_u32_usize] at hge' ⊢
    simp only [BatchCovers, halfLength, Model.Lifecycle.receiveShortfall,
      Model.Triple.classicalSkippedLength, Model.Triple.receiveCount] at hstore ⊢
    simp only [UScalar.ofNatCore_val_eq] at hge'
    have hn := hcomposite.n
    have hb := usize_sat_sub_val (core.num.Usize.saturating_add state.classical.skipped.len
      (core.num.Usize.saturating_sub (UScalar.cast .Usize composite.n)
        (UScalar.cast .Usize state.classical.nr))) tacenta_ratchet.MAX_SKIPPED_STORE
    have ha := hsat state.classical.skipped.len (core.num.Usize.saturating_sub
      (UScalar.cast .Usize composite.n) (UScalar.cast .Usize state.classical.nr))
    have hn2 := usize_sat_sub_val (UScalar.cast .Usize composite.n)
      (UScalar.cast .Usize state.classical.nr)
    have hc1 := cast_u32_usize composite.n
    have hc2 := cast_u32_usize state.classical.nr
    simp only [Model.State.maxSkippedStore] at hge' hstore hm ⊢
    omega

theorem shortfall_post_quantum_covers
    (state : tacenta_triple.State) (modelState : Model.Triple.State)
    (composite : tacenta_wire.Composite) (modelComposite : Model.CompositeHeader.Composite)
    (hstate : Tacenta.SessionUnitTripleT3.StateRefines
      Tacenta.SessionUnitTripleT3.ratchetAbs Tacenta.SessionUnitTripleT3.spqrAbs state modelState)
    (hcomposite : CompositeRefines composite modelComposite)
    (hstore : Model.Triple.postQuantumSkippedLength modelState +
      Model.SparseRatchet.maxSkippedStore ≤ UScalar.cMax UScalarTy.Usize) :
    ∃ batch, lifecycle.receive_shortfall lifecycle.FullStore.PostQuantum state composite =
        ok batch ∧
      BatchCovers (halfLength .PostQuantum modelState) batch
        (Model.Lifecycle.receiveShortfall .postQuantum modelState modelComposite) := by
  have hcm := cMax_le_usize_max
  have hc := cMax_usize_eq
  have h4 : 4294967295 ≤ Usize.max := Tacenta.SessionUnitSessionT1.small_le_usize_max le_rfl
  have hsparse : Tacenta.SessionUnitSpqrT3.StateRefines state.post_quantum
      modelState.postQuantum := by
    rw [← hstate.2]
    exact Tacenta.SessionUnitTripleT3.spqrAbs_refines state.post_quantum
  have hheld := congrArg
    (fun s : Model.SparseRatchet.State => s.skipped.length) hstate.2
  simp [Tacenta.SessionUnitTripleT3.spqrAbs] at hheld
  obtain ⟨found, hfindCall, hfindModel⟩ := Std.WP.spec_imp_exists
    (Tacenta.SessionUnitSpqrT3.findChains_refines hsparse composite.pq_epoch)
  cases found with
  | none =>
      have hmodelFind : Model.SparseRatchet.findChains modelState.postQuantum
          modelComposite.pqEpoch.toNat = none := by
        rw [← hcomposite.pqEpoch]
        exact hfindModel.symm
      refine ⟨1#usize, ?_, Or.inl ?_⟩
      · simp [lifecycle.receive_shortfall,
          tacenta_triple.State.post_quantum_receive_count,
          tacenta_spqr.State.receive_count, hfindCall]
      · simp [Model.Lifecycle.receiveShortfall,
          Model.Triple.postQuantumReceiveCount, hmodelFind]
  | some chains =>
      have hmodelFind : Model.SparseRatchet.findChains modelState.postQuantum
          modelComposite.pqEpoch.toNat =
          some (Tacenta.SessionUnitSpqrT3.chainsOf chains) := by
        rw [← hcomposite.pqEpoch]
        exact hfindModel.symm
      cases hreceive : chains.receive with
      | none =>
          refine ⟨1#usize, ?_, Or.inl ?_⟩
          · simp [lifecycle.receive_shortfall,
              tacenta_triple.State.post_quantum_receive_count,
              tacenta_spqr.State.receive_count, hfindCall, hreceive]
          · simp [Model.Lifecycle.receiveShortfall,
              Model.Triple.postQuantumReceiveCount, hmodelFind,
              Tacenta.SessionUnitSpqrT3.chainsOf, hreceive]
      | some chain =>
          have hmodelCount : Model.Triple.postQuantumReceiveCount modelState
              modelComposite.pqEpoch.toNat = some chain.n.val := by
            simp [Model.Triple.postQuantumReceiveCount, hmodelFind,
              Tacenta.SessionUnitSpqrT3.chainsOf,
              Tacenta.SessionUnitSpqrT3.chainOf, hreceive]
          have hneed64 : (core.num.U64.saturating_sub
              (core.num.U64.saturating_sub composite.pq_n 1#u64) chain.n).val =
              modelComposite.pqN.toNat - 1 - chain.n.val := by
            simp [u64_sat_sub_val, hcomposite.pqN]
          obtain ⟨need, hneedCall, hneedValue⟩ := saturating_usize_from_u64_val
            (core.num.U64.saturating_sub (core.num.U64.saturating_sub composite.pq_n 1#u64) chain.n)
          have hlen : state.post_quantum.skipped.len.val =
              state.post_quantum.skipped.val.length := by
            simp [alloc.vec.Vec.len]
          have hm : tacenta_spqr.MAX_SKIPPED_STORE.val = Model.SparseRatchet.maxSkippedStore := by
            simp [tacenta_spqr.MAX_SKIPPED_STORE, Model.SparseRatchet.maxSkippedStore,
              Model.State.maxSkippedStore]
          simp only [lifecycle.receive_shortfall,
            tacenta_triple.State.post_quantum_receive_count,
            tacenta_spqr.State.receive_count, hfindCall, hreceive, bind_tc_ok,
            tacenta_triple.State.post_quantum_skipped_len,
            tacenta_spqr.State.skipped_len, lift]
          rw [hneedCall]
          simp only [bind_tc_ok]
          have hsat := Tacenta.UnitLifecycleT3.usize_saturating_add_val
            state.post_quantum.skipped.len need
          have hb := usize_sat_sub_val (core.num.Usize.saturating_add
            state.post_quantum.skipped.len need) tacenta_spqr.MAX_SKIPPED_STORE
          simp only [Model.Triple.postQuantumSkippedLength, Model.SparseRatchet.maxSkippedStore,
            Model.State.maxSkippedStore] at hstore hm
          split
          · rename_i hlt
            refine ⟨1#usize, rfl, Or.inl ?_⟩
            have hlt' := (UScalar.lt_equiv _ _).mp hlt
            simp only [Model.Lifecycle.receiveShortfall, hmodelCount,
              Model.Triple.postQuantumSkippedLength, Model.SparseRatchet.maxSkippedStore,
              Model.State.maxSkippedStore, UScalar.ofNatCore_val_eq] at hlt' ⊢
            omega
          · rename_i hge
            refine ⟨_, rfl, ?_⟩
            have hge' : ¬ _ := fun h => hge ((UScalar.lt_equiv _ _).mpr h)
            simp only [UScalar.ofNatCore_val_eq] at hge'
            simp only [BatchCovers, halfLength, Model.Lifecycle.receiveShortfall, hmodelCount,
              Model.Triple.postQuantumSkippedLength, Model.SparseRatchet.maxSkippedStore,
              Model.State.maxSkippedStore]
            omega

theorem shortfall_covers (half : lifecycle.FullStore)
    (state : tacenta_triple.State) (modelState : Model.Triple.State)
    (composite : tacenta_wire.Composite) (modelComposite : Model.CompositeHeader.Composite)
    (hstate : Tacenta.SessionUnitTripleT3.StateRefines
      Tacenta.SessionUnitTripleT3.ratchetAbs Tacenta.SessionUnitTripleT3.spqrAbs state modelState)
    (hcomposite : CompositeRefines composite modelComposite)
    (hcstore : Model.Triple.classicalSkippedLength modelState + Model.State.maxSkippedStore ≤
      UScalar.cMax UScalarTy.Usize)
    (hpstore : Model.Triple.postQuantumSkippedLength modelState +
      Model.SparseRatchet.maxSkippedStore ≤ UScalar.cMax UScalarTy.Usize) :
    ∃ batch, lifecycle.receive_shortfall half state composite = ok batch ∧
      BatchCovers (halfLength half modelState) batch
        (Model.Lifecycle.receiveShortfall (fullStoreOfReal half) modelState modelComposite) := by
  cases half
  · exact shortfall_classical_covers state modelState composite modelComposite hstate hcomposite
      hcstore
  · exact shortfall_post_quantum_covers state modelState composite modelComposite hstate
      hcomposite hpstore

/-! ## Eviction -/

theorem evictHalf_lengths (half : Model.Lifecycle.FullStore) (m : Model.Triple.State)
    (count : Nat) :
    Model.Triple.classicalSkippedLength (evictHalf half m count).1 ≤
        Model.Triple.classicalSkippedLength m ∧
      Model.Triple.postQuantumSkippedLength (evictHalf half m count).1 ≤
        Model.Triple.postQuantumSkippedLength m ∧
      Model.Triple.classicalSkippedLength (evictHalf half m count).1 +
          Model.Triple.postQuantumSkippedLength (evictHalf half m count).1 +
          (evictHalf half m count).2 =
        Model.Triple.classicalSkippedLength m + Model.Triple.postQuantumSkippedLength m := by
  cases half
  · have h := Model.Ratchet.evictOldest_length_add_count m.classical count
    simp only [evictHalf, Model.Triple.evictOldestClassical, Model.Triple.classicalSkippedLength,
      Model.Triple.postQuantumSkippedLength]
    omega
  · simp only [evictHalf, Model.Triple.evictOldestPostQuantum, Model.SparseRatchet.evictOldest,
      Model.Triple.classicalSkippedLength, Model.Triple.postQuantumSkippedLength, List.length_drop]
    omega

theorem halfLength_evict_le (half : lifecycle.FullStore) (h : Model.Lifecycle.FullStore)
    (m : Model.Triple.State) (count : Nat) :
    halfLength half (evictHalf h m count).1 ≤ halfLength half m := by
  have := evictHalf_lengths h m count
  cases half <;> simp only [halfLength] <;> omega

theorem retryReceiveBounds_evictHalf {m : Model.Triple.State} {header : tacenta_triple.Header}
    {mh : Model.State.Header} {output : Option tacenta_spqr.Output}
    (bounds : RetryReceiveBounds m header mh output) (half : Model.Lifecycle.FullStore)
    (count : Nat) :
    RetryReceiveBounds (evictHalf half m count).1 header mh output := by
  cases half
  · exact bounds.classical_evict count
  · exact bounds.post_quantum_evict count

/-- One eviction at a batch that covers the model's: the generated call returns, the working copy
refines the model's eviction at the model batch, the counts agree, the headroom is kept and the
retry measure does not grow (and shrinks when a key was removed). -/
theorem evict_for_retry_covers
    (tc : Tacenta.UnitLifecycleT1.TripleReceiveContracts)
    (hrm : Tacenta.SessionUnitSpqrT3.RemoveSkippedAtAgrees)
    (half : lifecycle.FullStore) (s : tacenta_triple.State) (m : Model.Triple.State)
    (batch : Std.Usize) (modelBatch : Nat)
    (hrel : Tacenta.SessionUnitTripleT3.StateRefines
      Tacenta.SessionUnitTripleT3.ratchetAbs Tacenta.SessionUnitTripleT3.spqrAbs s m)
    (hcovers : BatchCovers (halfLength half m) batch modelBatch)
    (hroom : Tacenta.UnitLifecycleT1.ReceiveHeadroom s)
    (hcstore : Model.Triple.classicalSkippedLength m + Model.State.maxSkippedStore ≤
      UScalar.cMax UScalarTy.Usize) :
    ∃ s1 evicted, lifecycle.evict_for_retry s half batch = ok (s1, evicted) ∧
      Tacenta.SessionUnitTripleT3.StateRefines
        Tacenta.SessionUnitTripleT3.ratchetAbs Tacenta.SessionUnitTripleT3.spqrAbs s1
        (evictHalf (fullStoreOfReal half) m modelBatch).1 ∧
      evicted.val = (evictHalf (fullStoreOfReal half) m modelBatch).2 ∧
      Tacenta.UnitLifecycleT1.ReceiveHeadroom s1 ∧
      Tacenta.UnitLifecycleT1.skippedTotal s1 ≤ Tacenta.UnitLifecycleT1.skippedTotal s ∧
      (0 < evicted.val →
        Tacenta.UnitLifecycleT1.skippedTotal s1 < Tacenta.UnitLifecycleT1.skippedTotal s) := by
  obtain ⟨⟨s1, evicted⟩, hcall, hpost⟩ := Std.WP.spec_imp_exists
    (Tacenta.UnitLifecycleT1.evict_for_retry_no_panic tc.ratchetRemove tc.spqrRemove
      tc.spqrZeroize s half batch hroom)
  have hcongr := evictHalf_congr_of_covers half m batch modelBatch hcovers
  refine ⟨s1, evicted, hcall, ?_⟩
  cases half
  · have hclass : Tacenta.SessionUnitT3.StateR s.classical m.classical := by
      rw [← hrel.1]
      exact Tacenta.SessionUnitTripleT3.ratchetAbs_stateR s.classical
    have hwidth : s.classical.skipped.val.length ≤ UScalar.cMax UScalarTy.Usize := by
      have hl := congrArg (fun st : Model.State.State => st.skipped.length) hrel.1
      simp [Tacenta.SessionUnitTripleT3.ratchetAbs] at hl
      simp only [Model.Triple.classicalSkippedLength] at hcstore
      omega
    have hratchetDirect := concrete_classical_evict_oldest_refines
      tc.ratchetRemove s.classical m.classical batch hclass hwidth
    have hratchet : tacenta_ratchet.State.evict_oldest s.classical batch
        ⦃ fun r => ∃ mstate, Tacenta.SessionUnitT3.StateR r.2 mstate ∧
          Model.Ratchet.evictOldest m.classical batch.val = (mstate, r.1.val) ⦄ := by
      apply Std.WP.spec_mono hratchetDirect
      intro r hr
      refine ⟨(Model.Ratchet.evictOldest m.classical batch.val).1, hr.1, ?_⟩
      apply Prod.ext
      · rfl
      · exact hr.2.symm
    obtain ⟨mstate, hstate, hpair⟩ :=
      model_evict_for_retry_classical_of_concrete s m batch s1 evicted hrel hratchet hcall
    have hpair' : evictHalf (fullStoreOfReal .Classical) m modelBatch = (mstate, evicted.val) := by
      rw [← hcongr]
      exact hpair
    rw [hpair']
    exact ⟨hstate, rfl, hpost.1, hpost.2.1, hpost.2.2⟩
  · have hsparse : Tacenta.SessionUnitSpqrT3.StateRefines s.post_quantum m.postQuantum := by
      rw [← hrel.2]
      exact Tacenta.SessionUnitTripleT3.spqrAbs_refines s.post_quantum
    have hspqr := Tacenta.SessionUnitSpqrT3.evict_oldest_refines hrm tc.spqrZeroize hsparse batch
    obtain ⟨mstate, hstate, hpair⟩ :=
      model_evict_for_retry_post_quantum_of_concrete s m batch s1 evicted hrel hspqr hcall
    have hpair' : evictHalf (fullStoreOfReal .PostQuantum) m modelBatch =
        (mstate, evicted.val) := by
      rw [← hcongr]
      exact hpair
    rw [hpair']
    exact ⟨hstate, rfl, hpost.1, hpost.2.1, hpost.2.2⟩

/-! ## One iteration of the generated loop, in each of its five arms -/

theorem body_zero_evict
    (composite : tacenta_wire.Composite) (header : tacenta_triple.Header)
    (dhOutRecv dhOutSend newDhsPub : Array Std.U8 32#usize)
    (output : Option tacenta_spqr.Output) (half : lifecycle.FullStore)
    (state evictedState : tacenta_triple.State) (batch evicted : Std.Usize)
    (pending : tacenta_triple.TripleError)
    (hEvict : lifecycle.evict_for_retry state half batch = ok (evictedState, evicted))
    (hZero : evicted = 0#usize) :
    lifecycle.receive_with_eviction_loop.body composite header dhOutRecv dhOutSend
      newDhsPub output half state batch pending none =
      ok (ControlFlow.cont (half, evictedState, batch, pending,
        some (core.result.Result.Err pending))) := by
  subst hZero
  simp [lifecycle.receive_with_eviction_loop.body, hEvict]

theorem body_retry_ok
    (composite : tacenta_wire.Composite) (header : tacenta_triple.Header)
    (dhOutRecv dhOutSend newDhsPub : Array Std.U8 32#usize)
    (output : Option tacenta_spqr.Output) (half : lifecycle.FullStore)
    (state evictedState : tacenta_triple.State) (batch evicted : Std.Usize)
    (pending : tacenta_triple.TripleError)
    (result : tacenta_triple.State × Array Std.U8 32#usize)
    (hEvict : lifecycle.evict_for_retry state half batch = ok (evictedState, evicted))
    (hNonzero : evicted ≠ 0#usize)
    (hRetry : lifecycle.receive_attempt evictedState header dhOutRecv dhOutSend
      newDhsPub output = ok (.Ok result)) :
    lifecycle.receive_with_eviction_loop.body composite header dhOutRecv dhOutSend
      newDhsPub output half state batch pending none =
      ok (ControlFlow.cont (half, evictedState, core.num.Usize.saturating_add batch batch,
        pending, some (core.result.Result.Ok result))) := by
  simp [lifecycle.receive_with_eviction_loop.body, Aeneas.Std.lift, hEvict, hNonzero, hRetry]

theorem body_retry_stop
    (composite : tacenta_wire.Composite) (header : tacenta_triple.Header)
    (dhOutRecv dhOutSend newDhsPub : Array Std.U8 32#usize)
    (output : Option tacenta_spqr.Output) (half : lifecycle.FullStore)
    (state evictedState : tacenta_triple.State) (batch evicted : Std.Usize)
    (pending reason : tacenta_triple.TripleError)
    (hEvict : lifecycle.evict_for_retry state half batch = ok (evictedState, evicted))
    (hNonzero : evicted ≠ 0#usize)
    (hRetry : lifecycle.receive_attempt evictedState header dhOutRecv dhOutSend
      newDhsPub output = ok (.Err reason))
    (hFull : lifecycle.full_store reason = ok none) :
    lifecycle.receive_with_eviction_loop.body composite header dhOutRecv dhOutSend
      newDhsPub output half state batch pending none =
      ok (ControlFlow.cont (half, evictedState, core.num.Usize.saturating_add batch batch,
        pending, some (core.result.Result.Err reason))) := by
  simp [lifecycle.receive_with_eviction_loop.body, Aeneas.Std.lift, hEvict, hNonzero, hRetry,
    hFull]

theorem body_done
    (composite : tacenta_wire.Composite) (header : tacenta_triple.Header)
    (dhOutRecv dhOutSend newDhsPub : Array Std.U8 32#usize)
    (output : Option tacenta_spqr.Output) (half : lifecycle.FullStore)
    (state : tacenta_triple.State) (batch : Std.Usize)
    (pending : tacenta_triple.TripleError)
    (out : core.result.Result (tacenta_triple.State × Array Std.U8 32#usize)
      tacenta_triple.TripleError) :
    lifecycle.receive_with_eviction_loop.body composite header dhOutRecv dhOutSend
      newDhsPub output half state batch pending (some out) =
      ok (ControlFlow.done (pending, some out)) := by
  simp [lifecycle.receive_with_eviction_loop.body, core.option.Option.is_none]

/-! ## The relation the loop keeps, and the outcomes -/

/-- The loop's invariant between a generated loop state (half, working copy, batch, pending
refusal) and a model one. -/
structure LoopRel (header : tacenta_triple.Header) (mh : Model.State.Header)
    (output : Option tacenta_spqr.Output) (half : lifecycle.FullStore)
    (work : tacenta_triple.State) (batch : Std.Usize) (pending : tacenta_triple.TripleError)
    (m : Model.Triple.State) (modelBatch : Nat) (modelPending : Model.Triple.ReceiveRefusal) :
    Prop where
  state : Tacenta.SessionUnitTripleT3.StateRefines
    Tacenta.SessionUnitTripleT3.ratchetAbs Tacenta.SessionUnitTripleT3.spqrAbs work m
  batch : BatchCovers (halfLength half m) batch modelBatch
  pending : tripleReceiveRefusalOfReal pending = some modelPending
  headroom : Tacenta.UnitLifecycleT1.ReceiveHeadroom work
  bounds : RetryReceiveBounds m header mh output
  classicalStore : Model.Triple.classicalSkippedLength m + Model.State.maxSkippedStore ≤
    UScalar.cMax UScalarTy.Usize
  sparseStore : Model.Triple.postQuantumSkippedLength m + Model.SparseRatchet.maxSkippedStore ≤
    UScalar.cMax UScalarTy.Usize

/-- A generated outcome and a model result agree: a success with related state and key, or a
refusal whose public mapping is the model's. -/
def OutcomeRefines
    (out : core.result.Result (tacenta_triple.State × Array Std.U8 32#usize)
      tacenta_triple.TripleError)
    (res : Except Model.Triple.ReceiveRefusal (Model.Triple.State × Model.Lifecycle.Key)) :
    Prop :=
  match out, res with
  | .Ok value, .ok modelValue =>
      Tacenta.SessionUnitTripleT3.StateRefines
        Tacenta.SessionUnitTripleT3.ratchetAbs Tacenta.SessionUnitTripleT3.spqrAbs
        value.1 modelValue.1 ∧
      Tacenta.SessionUnitTripleT3.keyOf value.2 = modelValue.2
  | .Err reason, .error modelReason => tripleReceiveRefusalOfReal reason = some modelReason
  | _, _ => False

/-- The open case: the outcome is a refusal that is not a full store, returned by one Triple
receive at a working state related to a model state; if that one refusal is the model's detailed
refusal, the loop results agree. -/
def OpenRefusal (header : tacenta_triple.Header) (mh : Model.State.Header)
    (output : Option tacenta_spqr.Output)
    (dhOutRecv dhOutSend newDhsPub : Array Std.U8 32#usize)
    (out : core.result.Result (tacenta_triple.State × Array Std.U8 32#usize)
      tacenta_triple.TripleError)
    (res : Except Model.Triple.ReceiveRefusal (Model.Triple.State × Model.Lifecycle.Key)) :
    Prop :=
  ∃ reason work m,
    out = .Err reason ∧ lifecycle.full_store reason = ok none ∧
    Tacenta.SessionUnitTripleT3.StateRefines
      Tacenta.SessionUnitTripleT3.ratchetAbs Tacenta.SessionUnitTripleT3.spqrAbs work m ∧
    RetryReceiveBounds m header mh output ∧
    Tacenta.UnitLifecycleT1.ReceiveHeadroom work ∧
    lifecycle.receive_attempt work header dhOutRecv dhOutSend newDhsPub output =
      ok (.Err reason) ∧
    ∀ modelReason, tripleReceiveRefusalOfReal reason = some modelReason →
      Model.Triple.receiveDetailed m
          { dr := mh, epoch := header.epoch.val, pqN := header.pq_n.val }
          (Tacenta.SessionUnitTripleT3.keyOf dhOutRecv)
          (Tacenta.SessionUnitTripleT3.keyOf dhOutSend)
          (Tacenta.SessionUnitTripleT3.keyOf newDhsPub)
          (output.map Tacenta.SessionUnitTripleT3.spqrOutputOf) = .error modelReason →
      res = .error modelReason

/-- A refusal that `full_store` does not classify maps to a model refusal `fullStore` does not
classify. -/
theorem fullStore_none_of_real {reason : tacenta_triple.TripleError}
    {modelReason : Model.Triple.ReceiveRefusal}
    (hmap : tripleReceiveRefusalOfReal reason = some modelReason)
    (hfull : lifecycle.full_store reason = ok none) :
    Model.Lifecycle.fullStore modelReason = none := by
  cases reason with
  | Classical r =>
      cases r <;> simp [tripleReceiveRefusalOfReal, ratchetReceiveRefusalOfReal,
        lifecycle.full_store] at hmap hfull <;> subst hmap <;> rfl
  | PostQuantum r =>
      cases r <;> simp [tripleReceiveRefusalOfReal, sparseReceiveRefusalOfReal,
        lifecycle.full_store] at hmap hfull <;> subst hmap <;> rfl

/-! ## The induction -/

/-- **The generated retry loop refines the model loop, for every fuel above the keys the model
state holds.**  From a loop state related by `LoopRel` to a model state, the generated loop
returns an outcome, and the model loop's result at that fuel is related to it: a success with
related state and key, the pending full-store refusal after an empty eviction, a full-store
refusal of a retry handed on to the next turn, and, for a retry refused for another reason, the
reduction `OpenRefusal` to one Triple receive.  The proof is a loop invariant over the
generated `loop`, with the model's result at the starting fuel as a fixed ghost value, and the
retry measure of `UnitLifecycleT1` as the decreasing quantity. -/
theorem receive_with_eviction_loop_refines
    (tc : Tacenta.UnitLifecycleT1.TripleReceiveContracts)
    [Tacenta.SessionUnitT1.DerivedKeysModel]
    (hmac : Tacenta.SessionUnitT3.HmacAgrees)
    (hkdf : Tacenta.SessionUnitT3.HkdfAgrees)
    (hzr : Tacenta.SessionUnitT3.ZeroizingRoundTrips)
    (hz96 : Tacenta.SessionUnitSpqrT3.ZeroizingRoundTrips96)
    (hz64 : Tacenta.SessionUnitSpqrT3.ZeroizingRoundTrips64)
    (hret : Tacenta.SessionUnitSpqrT3.VecRetainAgrees)
    (hrm : Tacenta.SessionUnitSpqrT3.RemoveSkippedAtAgrees)
    (composite : tacenta_wire.Composite) (modelComposite : Model.CompositeHeader.Composite)
    (hcomposite : CompositeRefines composite modelComposite)
    (header : tacenta_triple.Header) (mh : Model.State.Header)
    (hheader : Tacenta.SessionUnitTripleT3.RatchetHeaderR header.dr mh)
    (dhOutRecv dhOutSend newDhsPub : Array Std.U8 32#usize)
    (output : Option tacenta_spqr.Output)
    (fuel : Nat) (half : lifecycle.FullStore) (work : tacenta_triple.State)
    (batch : Std.Usize) (pending : tacenta_triple.TripleError)
    (m : Model.Triple.State) (modelBatch : Nat) (modelPending : Model.Triple.ReceiveRefusal)
    (hrel : LoopRel header mh output half work batch pending m modelBatch modelPending)
    (hfuel : Model.Triple.classicalSkippedLength m + Model.Triple.postQuantumSkippedLength m <
      fuel) :
    ∃ pendingOut out,
      lifecycle.receive_with_eviction_loop composite header dhOutRecv dhOutSend newDhsPub output
          half work batch pending none = ok (pendingOut, some out) ∧
      ∃ res,
        Model.Lifecycle.ReceiveWithEvictionLoopResult m modelComposite
          { dr := mh, epoch := header.epoch.val, pqN := header.pq_n.val }
          (Tacenta.SessionUnitTripleT3.keyOf dhOutRecv)
          (Tacenta.SessionUnitTripleT3.keyOf dhOutSend)
          (Tacenta.SessionUnitTripleT3.keyOf newDhsPub)
          (output.map Tacenta.SessionUnitTripleT3.spqrOutputOf)
          modelPending (fullStoreOfReal half) modelBatch fuel res ∧
        (OutcomeRefines out res ∨
          OpenRefusal header mh output dhOutRecv dhOutSend newDhsPub out res) := by
  -- the model's result at the starting point, a fixed ghost value
  obtain ⟨res, hres⟩ := loopResult_exists m modelComposite
    { dr := mh, epoch := header.epoch.val, pqN := header.pq_n.val }
    (Tacenta.SessionUnitTripleT3.keyOf dhOutRecv)
    (Tacenta.SessionUnitTripleT3.keyOf dhOutSend)
    (Tacenta.SessionUnitTripleT3.keyOf newDhsPub)
    (output.map Tacenta.SessionUnitTripleT3.spqrOutputOf)
    modelPending (fullStoreOfReal half) modelBatch fuel
  let MH : Model.Triple.Header := { dr := mh, epoch := header.epoch.val, pqN := header.pq_n.val }
  let R := Tacenta.SessionUnitTripleT3.keyOf dhOutRecv
  let S := Tacenta.SessionUnitTripleT3.keyOf dhOutSend
  let N := Tacenta.SessionUnitTripleT3.keyOf newDhsPub
  let O := output.map Tacenta.SessionUnitTripleT3.spqrOutputOf
  let Final := fun out => OutcomeRefines out res ∨
    OpenRefusal header mh output dhOutRecv dhOutSend newDhsPub out res
  let inv : lifecycle.FullStore × tacenta_triple.State × Std.Usize × tacenta_triple.TripleError ×
      Option (core.result.Result (tacenta_triple.State × Array Std.U8 32#usize)
        tacenta_triple.TripleError) → Prop := fun x =>
    match x.2.2.2.2 with
    | none => ∃ m mb mp fuel', LoopRel header mh output x.1 x.2.1 x.2.2.1 x.2.2.2.1 m mb mp ∧
        Model.Triple.classicalSkippedLength m + Model.Triple.postQuantumSkippedLength m < fuel' ∧
        Model.Lifecycle.ReceiveWithEvictionLoopResult m modelComposite MH R S N O mp
          (fullStoreOfReal x.1) mb fuel' res
    | some out => Final out
  have hspec : lifecycle.receive_with_eviction_loop composite header dhOutRecv dhOutSend newDhsPub
      output half work batch pending none ⦃ fun r => ∃ out, r.2 = some out ∧ Final out ⦄ := by
    unfold lifecycle.receive_with_eviction_loop
    apply loop.spec_decr_nat (measure := Tacenta.UnitLifecycleT1.retryMeasure) (inv := inv)
    · rintro ⟨h, w, b, p, o⟩ hinv
      dsimp only
      cases o with
      | some out =>
          rw [body_done]
          simp only [Std.WP.spec_ok]
          exact ⟨out, rfl, hinv⟩
      | none =>
          obtain ⟨m, mb, mp, fuel', hr, hf, hres'⟩ := hinv
          obtain ⟨fuel'', rfl⟩ : ∃ k, fuel' = k + 1 := ⟨fuel' - 1, by omega⟩
          obtain ⟨s1, ev, hcall, hst, hev, hroom1, hle, hlt⟩ :=
            evict_for_retry_covers tc hrm h w m b mb hr.state hr.batch hr.headroom
              hr.classicalStore
          -- the model's eviction
          have hlens := evictHalf_lengths (fullStoreOfReal h) m mb
          have hEvictM : (match fullStoreOfReal h with
              | .classical => Model.Triple.evictOldestClassical m mb
              | .postQuantum => Model.Triple.evictOldestPostQuantum m mb) =
              ((evictHalf (fullStoreOfReal h) m mb).1, ev.val) := by
            rw [← evictHalf_eq_match, hev]
          have hbounds1 := retryReceiveBounds_evictHalf hr.bounds (fullStoreOfReal h) mb
          have hcs1 : Model.Triple.classicalSkippedLength (evictHalf (fullStoreOfReal h) m mb).1 +
              Model.State.maxSkippedStore ≤ UScalar.cMax UScalarTy.Usize := by
            have := hr.classicalStore; omega
          have hps1 : Model.Triple.postQuantumSkippedLength (evictHalf (fullStoreOfReal h) m mb).1 +
              Model.SparseRatchet.maxSkippedStore ≤ UScalar.cMax UScalarTy.Usize := by
            have := hr.sparseStore; omega
          by_cases hzero : ev = 0#usize
          · -- an empty eviction returns the pending refusal
            rw [body_zero_evict composite header dhOutRecv dhOutSend newDhsPub output h w s1 b ev p
              hcall hzero]
            simp only [Std.WP.spec_ok]
            have hev0 : ev.val = 0 := by subst hzero; rfl
            rw [hev0] at hEvictM
            have hmodel := Model.Lifecycle.receiveWithEvictionLoopResult_zero_evict m modelComposite
              MH R S N O mp (fullStoreOfReal h) mb fuel'' (evictHalf (fullStoreOfReal h) m mb).1
              hEvictM
            have hres0 := loopResult_functional hres' hmodel
            refine ⟨Or.inl ?_, ?_⟩
            · rw [hres0]
              exact hr.pending
            · simp only [Tacenta.UnitLifecycleT1.retryMeasure]
              omega
          · have hevpos : 0 < ev.val := by
              have : ev.val ≠ 0 := fun h0 => hzero (by scalar_tac)
              omega
            have hevne : ev.val ≠ 0 := by omega
            obtain ⟨r, hattempt, -⟩ := Std.WP.spec_imp_exists
              (Tacenta.UnitLifecycleT1.receive_attempt_no_panic tc.hmac tc.hkdf tc.zeroizing
                tc.spqrZeroize tc.vecRetain tc.kdfRk tc.kdfCk tc.optionClone tc.ratchetRemove
                tc.spqrRemove tc.vecAppend s1 header dhOutRecv dhOutSend newDhsPub output hroom1)
            have hdec := hlt hevpos
            cases r with
            | Ok value =>
                rw [body_retry_ok composite header dhOutRecv dhOutSend newDhsPub output h w s1 b ev p
                  value hcall hzero hattempt]
                simp only [Std.WP.spec_ok]
                obtain ⟨mc, mk, hmodelRecv, hstc, hkey⟩ :=
                  concrete_receive_attempt_success_from_retry_bounds hmac hkdf hzr tc.ratchetRemove
                    hz96 hz64 hret tc.vecRetain hrm tc.spqrZeroize tc.optionClone hst header mh
                    hheader dhOutRecv dhOutSend newDhsPub output hbounds1 value.1 value.2 hattempt
                have hdetail := (Model.Triple.receiveDetailed_ok_iff _ _ _ _ _ _ _).mpr hmodelRecv
                have hmodel := Model.Lifecycle.receiveWithEvictionLoopResult_one_retry m
                  modelComposite MH R S N O mp (fullStoreOfReal h) mb fuel''
                  (evictHalf (fullStoreOfReal h) m mb).1 mc ev.val mk hEvictM hevne hdetail
                have hres0 := loopResult_functional hres' hmodel
                refine ⟨Or.inl ?_, ?_⟩
                · rw [hres0]
                  exact ⟨hstc, hkey⟩
                · simp only [Tacenta.UnitLifecycleT1.retryMeasure]
                  omega
            | Err e =>
                obtain ⟨fs, hfs, -⟩ := Std.WP.spec_imp_exists
                  (Tacenta.UnitLifecycleT1.full_store_no_panic e)
                cases fs with
                | none =>
                    rw [body_retry_stop composite header dhOutRecv dhOutSend newDhsPub output h w s1 b
                      ev p e hcall hzero hattempt hfs]
                    simp only [Std.WP.spec_ok]
                    refine ⟨Or.inr ⟨e, s1, (evictHalf (fullStoreOfReal h) m mb).1, rfl, hfs, hst,
                      hbounds1, hroom1, hattempt, ?_⟩, ?_⟩
                    · intro mr hmap hdet
                      have hmodel := receiveWithEvictionLoopResult_stop m modelComposite MH R S N O
                        mp mr (fullStoreOfReal h) mb fuel'' (evictHalf (fullStoreOfReal h) m mb).1
                        ev.val hEvictM hevne hdet (fullStore_none_of_real hmap hfs)
                      exact loopResult_functional hres' hmodel
                    · simp only [Tacenta.UnitLifecycleT1.retryMeasure]
                      omega
                | some next =>
                    obtain ⟨mr, hdet, hmap, hmfull⟩ :=
                      concrete_receive_attempt_store_full_from_retry_bounds hmac hkdf hzr
                        tc.ratchetRemove hz96 hz64 hret tc.vecRetain hrm tc.spqrZeroize
                        tc.optionClone hst header mh hheader dhOutRecv dhOutSend newDhsPub output
                        hbounds1 e next hattempt hfs
                    obtain ⟨bne, hne, -⟩ := Std.WP.spec_imp_exists
                      (Tacenta.UnitLifecycleT1.full_store_ne_no_panic next h)
                    have hfuel1 : Model.Triple.classicalSkippedLength
                          (evictHalf (fullStoreOfReal h) m mb).1 +
                        Model.Triple.postQuantumSkippedLength
                          (evictHalf (fullStoreOfReal h) m mb).1 < fuel'' := by
                      omega
                    cases bne with
                    | true =>
                        obtain ⟨b2, hb2, hcov2⟩ := shortfall_covers next s1
                          (evictHalf (fullStoreOfReal h) m mb).1 composite modelComposite hst
                          hcomposite hcs1 hps1
                        rw [concrete_receive_with_eviction_loop_switch_half_step composite header
                          dhOutRecv dhOutSend newDhsPub output h next w s1 b b2 ev p e hcall hzero
                          hattempt hfs hne hb2]
                        simp only [Std.WP.spec_ok]
                        have hdiff := fullStoreOfReal_ne_of_generated_ne hne
                        obtain ⟨res1, hres1⟩ := loopResult_exists
                          (evictHalf (fullStoreOfReal h) m mb).1 modelComposite MH R S N O mr
                          (fullStoreOfReal next)
                          (Model.Lifecycle.receiveShortfall (fullStoreOfReal next)
                            (evictHalf (fullStoreOfReal h) m mb).1 modelComposite) fuel''
                        have hmodel := Model.Lifecycle.receiveWithEvictionLoopResult_continue_switch_half
                          m modelComposite MH R S N O mp mr (fullStoreOfReal h) (fullStoreOfReal next)
                          mb fuel'' (evictHalf (fullStoreOfReal h) m mb).1 ev.val res1 hEvictM hevne
                          hdet hmfull hdiff hres1
                        have hres0 := loopResult_functional hres' hmodel
                        refine ⟨⟨(evictHalf (fullStoreOfReal h) m mb).1,
                          Model.Lifecycle.receiveShortfall (fullStoreOfReal next)
                            (evictHalf (fullStoreOfReal h) m mb).1 modelComposite, mr, fuel'',
                          ⟨hst, hcov2, hmap, hroom1, hbounds1, hcs1, hps1⟩, hfuel1, ?_⟩, ?_⟩
                        · rw [hres0]
                          exact hres1
                        · simp only [Tacenta.UnitLifecycleT1.retryMeasure]
                          omega
                    | false =>
                        have heqh : next = h :=
                          fullStoreOfReal_injective (fullStoreOfReal_eq_of_generated_ne_false hne)
                        subst heqh
                        rw [concrete_receive_with_eviction_loop_same_half_step composite header
                          dhOutRecv dhOutSend newDhsPub output next w s1 b
                          (core.num.Usize.saturating_add b b) ev p e hcall hzero rfl hattempt hfs hne]
                        simp only [Std.WP.spec_ok]
                        obtain ⟨res1, hres1⟩ := loopResult_exists
                          (evictHalf (fullStoreOfReal next) m mb).1 modelComposite MH R S N O mr
                          (fullStoreOfReal next) (mb * 2) fuel''
                        have hmodel := Model.Lifecycle.receiveWithEvictionLoopResult_continue_same_half
                          m modelComposite MH R S N O mp mr (fullStoreOfReal next) mb fuel''
                          (evictHalf (fullStoreOfReal next) m mb).1 ev.val res1 hEvictM hevne hdet
                          hmfull hres1
                        have hres0 := loopResult_functional hres' hmodel
                        have hhalfle := halfLength_evict_le next (fullStoreOfReal next) m mb
                        have hhalfmax : halfLength next m ≤ Usize.max := by
                          have h1 := hr.classicalStore
                          have h2 := hr.sparseStore
                          have h3 := cMax_le_usize_max
                          cases next <;> simp only [halfLength] <;> omega
                        refine ⟨⟨(evictHalf (fullStoreOfReal next) m mb).1, mb * 2, mr, fuel'',
                          ⟨hst, batchCovers_double hr.batch hhalfle hhalfmax, hmap, hroom1,
                            hbounds1, hcs1, hps1⟩, hfuel1, ?_⟩, ?_⟩
                        · rw [hres0]
                          exact hres1
                        · simp only [Tacenta.UnitLifecycleT1.retryMeasure]
                          omega
    · exact ⟨m, modelBatch, modelPending, fuel, hrel, hfuel, hres⟩
  obtain ⟨⟨pendingOut, outcome⟩, hcall, out, hout, hfinal⟩ := Std.WP.spec_imp_exists hspec
  simp only at hout
  subst hout
  exact ⟨pendingOut, out, hcall, res, hres, hfinal⟩

/-! ## The whole receive with eviction -/

/-- **`receive_with_eviction` refines `Model.Lifecycle.receiveWithEviction`.**  At related Triple
states with the receive bounds and the store bounds, the generated function returns, and its
result is the model's (a success with related state and key, or a refusal whose public mapping is
the model's), or it is a refusal that is not a full store, returned by one Triple receive at related
states, reduced as in `OpenRefusal`: if that one refusal is the model's detailed refusal, the two
results agree.  A direct refusal of that kind is the first attempt; one returned inside the loop
is a retry.  The model runs its loop at the fuel it chooses, one more than the keys held, and the
loop theorem holds at every fuel above that number. -/
theorem receive_with_eviction_refines
    (tc : Tacenta.UnitLifecycleT1.TripleReceiveContracts)
    [Tacenta.SessionUnitT1.DerivedKeysModel]
    (hmac : Tacenta.SessionUnitT3.HmacAgrees)
    (hkdf : Tacenta.SessionUnitT3.HkdfAgrees)
    (hzr : Tacenta.SessionUnitT3.ZeroizingRoundTrips)
    (hz96 : Tacenta.SessionUnitSpqrT3.ZeroizingRoundTrips96)
    (hz64 : Tacenta.SessionUnitSpqrT3.ZeroizingRoundTrips64)
    (hret : Tacenta.SessionUnitSpqrT3.VecRetainAgrees)
    (hrm : Tacenta.SessionUnitSpqrT3.RemoveSkippedAtAgrees)
    (composite : tacenta_wire.Composite) (modelComposite : Model.CompositeHeader.Composite)
    (hcomposite : CompositeRefines composite modelComposite)
    (header : tacenta_triple.Header) (mh : Model.State.Header)
    (hheader : Tacenta.SessionUnitTripleT3.RatchetHeaderR header.dr mh)
    (dhOutRecv dhOutSend newDhsPub : Array Std.U8 32#usize)
    (output : Option tacenta_spqr.Output)
    (state : tacenta_triple.State) (m : Model.Triple.State)
    (hstate : Tacenta.SessionUnitTripleT3.StateRefines
      Tacenta.SessionUnitTripleT3.ratchetAbs Tacenta.SessionUnitTripleT3.spqrAbs state m)
    (hroom : Tacenta.UnitLifecycleT1.ReceiveHeadroom state)
    (bounds : RetryReceiveBounds m header mh output)
    (hcstore : Model.Triple.classicalSkippedLength m + Model.State.maxSkippedStore ≤
      UScalar.cMax UScalarTy.Usize)
    (hpstore : Model.Triple.postQuantumSkippedLength m + Model.SparseRatchet.maxSkippedStore ≤
      UScalar.cMax UScalarTy.Usize) :
    ∃ out,
      lifecycle.receive_with_eviction state composite header dhOutRecv dhOutSend newDhsPub
        output = ok out ∧
      (OutcomeRefines out
          (Model.Lifecycle.receiveWithEviction m modelComposite
            { dr := mh, epoch := header.epoch.val, pqN := header.pq_n.val }
            (Tacenta.SessionUnitTripleT3.keyOf dhOutRecv)
            (Tacenta.SessionUnitTripleT3.keyOf dhOutSend)
            (Tacenta.SessionUnitTripleT3.keyOf newDhsPub)
            (output.map Tacenta.SessionUnitTripleT3.spqrOutputOf)) ∨
        OpenRefusal header mh output dhOutRecv dhOutSend newDhsPub out
          (Model.Lifecycle.receiveWithEviction m modelComposite
            { dr := mh, epoch := header.epoch.val, pqN := header.pq_n.val }
            (Tacenta.SessionUnitTripleT3.keyOf dhOutRecv)
            (Tacenta.SessionUnitTripleT3.keyOf dhOutSend)
            (Tacenta.SessionUnitTripleT3.keyOf newDhsPub)
            (output.map Tacenta.SessionUnitTripleT3.spqrOutputOf))) := by
  obtain ⟨r, hattempt, -⟩ := Std.WP.spec_imp_exists
    (Tacenta.UnitLifecycleT1.receive_attempt_no_panic tc.hmac tc.hkdf tc.zeroizing
      tc.spqrZeroize tc.vecRetain tc.kdfRk tc.kdfCk tc.optionClone tc.ratchetRemove
      tc.spqrRemove tc.vecAppend state header dhOutRecv dhOutSend newDhsPub output hroom)
  cases r with
  | Ok value =>
      refine ⟨.Ok value, ?_, Or.inl ?_⟩
      · unfold lifecycle.receive_with_eviction
        simp [hattempt]
      · obtain ⟨mc, mk, hmodelRecv, hstc, hkey⟩ :=
          concrete_receive_attempt_success_from_retry_bounds hmac hkdf hzr tc.ratchetRemove
            hz96 hz64 hret tc.vecRetain hrm tc.spqrZeroize tc.optionClone hstate header mh
            hheader dhOutRecv dhOutSend newDhsPub output bounds value.1 value.2 hattempt
        rw [model_receive_with_eviction_of_receive _ _ _ _ _ _ _ _ hmodelRecv]
        exact ⟨hstc, hkey⟩
  | Err e =>
      obtain ⟨fs, hfs, -⟩ := Std.WP.spec_imp_exists
        (Tacenta.UnitLifecycleT1.full_store_no_panic e)
      cases fs with
      | none =>
          refine ⟨.Err e, ?_, Or.inr ⟨e, state, m, rfl, hfs, hstate, bounds, hroom, hattempt, ?_⟩⟩
          · unfold lifecycle.receive_with_eviction
            simp [hattempt, hfs]
          · intro mr hmap hdet
            simp [Model.Lifecycle.receiveWithEviction, hdet, fullStore_none_of_real hmap hfs]
      | some half =>
          obtain ⟨mr, hdet, hmap, hmfull⟩ :=
            concrete_receive_attempt_store_full_from_retry_bounds hmac hkdf hzr
              tc.ratchetRemove hz96 hz64 hret tc.vecRetain hrm tc.spqrZeroize
              tc.optionClone hstate header mh hheader dhOutRecv dhOutSend newDhsPub output
              bounds e half hattempt hfs
          obtain ⟨cloned, hclone, hclonedEq⟩ := Std.WP.spec_imp_exists
            (Tacenta.SessionUnitTripleT1.State.clone_spec tc.optionClone state)
          subst hclonedEq
          obtain ⟨b, hb, hcov⟩ := shortfall_covers half cloned m composite modelComposite hstate
            hcomposite hcstore hpstore
          obtain ⟨pendingOut, out, hloop, res, hres, hfinal⟩ :=
            receive_with_eviction_loop_refines tc hmac hkdf hzr hz96 hz64 hret hrm composite
              modelComposite hcomposite header mh hheader dhOutRecv dhOutSend newDhsPub output
              (Model.Triple.classicalSkippedLength m + Model.Triple.postQuantumSkippedLength m + 1)
              half cloned b e m
              (Model.Lifecycle.receiveShortfall (fullStoreOfReal half) m modelComposite) mr
              ⟨hstate, hcov, hmap, hroom, bounds, hcstore, hpstore⟩ (by omega)
          have hmodel := Model.Lifecycle.receiveWithEviction_of_loop_result m modelComposite
            { dr := mh, epoch := header.epoch.val, pqN := header.pq_n.val }
            (Tacenta.SessionUnitTripleT3.keyOf dhOutRecv)
            (Tacenta.SessionUnitTripleT3.keyOf dhOutSend)
            (Tacenta.SessionUnitTripleT3.keyOf newDhsPub)
            (output.map Tacenta.SessionUnitTripleT3.spqrOutputOf) mr (fullStoreOfReal half) res
            hdet hmfull hres
          refine ⟨out, ?_, ?_⟩
          · unfold lifecycle.receive_with_eviction
            simp [hattempt, hfs, hclone, hb, hloop]
          · rw [hmodel]
            exact hfinal

end Tacenta.UnitLifecycleRetryLoopT3

/-! ## Pins

The axiom lists and the statements of the five results, and the bodies of the definitions their
statements are written in. -/

/--
info: 'Tacenta.UnitLifecycleRetryLoopT3.receive_with_eviction_loop_refines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kdf.hkdf_sha256,
 tacenta_session_unit.tacenta_kdf.hmac_sha256,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.zeroize.Zeroizing.new,
 tacenta_session_unit.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.Pair.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.alloc.vec.Vec.capacity,
 tacenta_session_unit.alloc.vec.Vec.pop,
 tacenta_session_unit.core.option.Option.as_mut,
 tacenta_session_unit.zeroize.Zeroize.Blanket.zeroize,
 Tacenta.SessionUnitSpqrT3.chain_label_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.chain_start_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.max_skip_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.max_skip_val._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.max_skipped_store_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.protocol_info_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.receive_refines_continuation._native.native_decide.ax_1_29,
 Tacenta.SessionUnitSpqrT3.root_label_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitTripleT3.combine_info_agrees._native.native_decide.ax_1_1,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 tacenta_session_unit.alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.core.option.Option.Insts.CoreCloneClone.clone]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleRetryLoopT3.receive_with_eviction_loop_refines

/--
info: 'Tacenta.UnitLifecycleRetryLoopT3.receive_with_eviction_refines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kdf.hkdf_sha256,
 tacenta_session_unit.tacenta_kdf.hmac_sha256,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.zeroize.Zeroizing.new,
 tacenta_session_unit.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.Pair.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.alloc.vec.Vec.capacity,
 tacenta_session_unit.alloc.vec.Vec.pop,
 tacenta_session_unit.core.option.Option.as_mut,
 tacenta_session_unit.zeroize.Zeroize.Blanket.zeroize,
 Tacenta.SessionUnitSpqrT3.chain_label_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.chain_start_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.max_skip_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.max_skip_val._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.max_skipped_store_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.protocol_info_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.receive_refines_continuation._native.native_decide.ax_1_29,
 Tacenta.SessionUnitSpqrT3.root_label_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitTripleT3.combine_info_agrees._native.native_decide.ax_1_1,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 tacenta_session_unit.alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.core.option.Option.Insts.CoreCloneClone.clone]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleRetryLoopT3.receive_with_eviction_refines

/--
info: 'Tacenta.UnitLifecycleRetryLoopT3.receiveWithEvictionLoopResult_stop' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleRetryLoopT3.receiveWithEvictionLoopResult_stop

/--
info: 'Tacenta.UnitLifecycleRetryLoopT3.shortfall_covers' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleRetryLoopT3.shortfall_covers

/--
info: 'Tacenta.UnitLifecycleRetryLoopT3.evict_for_retry_covers' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kdf.hkdf_sha256,
 tacenta_session_unit.tacenta_kdf.hmac_sha256,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.zeroize.Zeroizing.new,
 tacenta_session_unit.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.alloc.vec.Vec.capacity,
 tacenta_session_unit.alloc.vec.Vec.pop,
 tacenta_session_unit.core.option.Option.as_mut,
 tacenta_session_unit.zeroize.Zeroize.Blanket.zeroize,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 tacenta_session_unit.alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.core.option.Option.Insts.CoreCloneClone.clone]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleRetryLoopT3.evict_for_retry_covers

/--
info: Tacenta.UnitLifecycleRetryLoopT3.receive_with_eviction_loop_refines : Tacenta.UnitLifecycleT1.TripleReceiveContracts →
  ∀ [Tacenta.SessionUnitT1.DerivedKeysModel],
    Tacenta.SessionUnitT3.HmacAgrees →
      Tacenta.SessionUnitT3.HkdfAgrees →
        Tacenta.SessionUnitT3.ZeroizingRoundTrips →
          Tacenta.SessionUnitSpqrT3.ZeroizingRoundTrips96 →
            Tacenta.SessionUnitSpqrT3.ZeroizingRoundTrips64 →
              Tacenta.SessionUnitSpqrT3.VecRetainAgrees →
                Tacenta.SessionUnitSpqrT3.RemoveSkippedAtAgrees →
                  ∀ (composite : tacenta_session_unit.tacenta_wire.Composite)
                    (modelComposite : Model.CompositeHeader.Composite),
                    Tacenta.UnitLifecycleT3.CompositeRefines composite modelComposite →
                      ∀ (header : tacenta_session_unit.tacenta_triple.Header) (mh : Model.State.Header),
                        Tacenta.SessionUnitTripleT3.RatchetHeaderR header.dr mh →
                          ∀ (dhOutRecv dhOutSend newDhsPub : Aeneas.Std.Array Aeneas.Std.U8 32#usize)
                            (output : Option tacenta_session_unit.tacenta_spqr.Output) (fuel : ℕ)
                            (half : tacenta_session_unit.lifecycle.FullStore)
                            (work : tacenta_session_unit.tacenta_triple.State) (batch : Aeneas.Std.Usize)
                            (pending : tacenta_session_unit.tacenta_triple.TripleError) (m : Model.Triple.State)
                            (modelBatch : ℕ) (modelPending : Model.Triple.ReceiveRefusal),
                            Tacenta.UnitLifecycleRetryLoopT3.LoopRel header mh output half work batch pending m
                                modelBatch modelPending →
                              Model.Triple.classicalSkippedLength m + Model.Triple.postQuantumSkippedLength m < fuel →
                                ∃ pendingOut out,
                                  tacenta_session_unit.lifecycle.receive_with_eviction_loop composite header dhOutRecv
                                        dhOutSend newDhsPub output half work batch pending none =
                                      Aeneas.Std.Result.ok (pendingOut, some out) ∧
                                    ∃ res,
                                      Model.Lifecycle.ReceiveWithEvictionLoopResult m modelComposite
                                          { dr := mh, epoch := ↑header.epoch, pqN := ↑header.pq_n }
                                          (Tacenta.SessionUnitTripleT3.keyOf dhOutRecv)
                                          (Tacenta.SessionUnitTripleT3.keyOf dhOutSend)
                                          (Tacenta.SessionUnitTripleT3.keyOf newDhsPub)
                                          (Option.map Tacenta.SessionUnitTripleT3.spqrOutputOf output) modelPending
                                          (Tacenta.UnitLifecycleT3.fullStoreOfReal half) modelBatch fuel res ∧
                                        (Tacenta.UnitLifecycleRetryLoopT3.OutcomeRefines out res ∨
                                          Tacenta.UnitLifecycleRetryLoopT3.OpenRefusal header mh output dhOutRecv
                                            dhOutSend newDhsPub out res)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleRetryLoopT3.receive_with_eviction_loop_refines

/--
info: Tacenta.UnitLifecycleRetryLoopT3.receive_with_eviction_refines : Tacenta.UnitLifecycleT1.TripleReceiveContracts →
  ∀ [Tacenta.SessionUnitT1.DerivedKeysModel],
    Tacenta.SessionUnitT3.HmacAgrees →
      Tacenta.SessionUnitT3.HkdfAgrees →
        Tacenta.SessionUnitT3.ZeroizingRoundTrips →
          Tacenta.SessionUnitSpqrT3.ZeroizingRoundTrips96 →
            Tacenta.SessionUnitSpqrT3.ZeroizingRoundTrips64 →
              Tacenta.SessionUnitSpqrT3.VecRetainAgrees →
                Tacenta.SessionUnitSpqrT3.RemoveSkippedAtAgrees →
                  ∀ (composite : tacenta_session_unit.tacenta_wire.Composite)
                    (modelComposite : Model.CompositeHeader.Composite),
                    Tacenta.UnitLifecycleT3.CompositeRefines composite modelComposite →
                      ∀ (header : tacenta_session_unit.tacenta_triple.Header) (mh : Model.State.Header),
                        Tacenta.SessionUnitTripleT3.RatchetHeaderR header.dr mh →
                          ∀ (dhOutRecv dhOutSend newDhsPub : Aeneas.Std.Array Aeneas.Std.U8 32#usize)
                            (output : Option tacenta_session_unit.tacenta_spqr.Output)
                            (state : tacenta_session_unit.tacenta_triple.State) (m : Model.Triple.State),
                            Tacenta.SessionUnitTripleT3.StateRefines Tacenta.SessionUnitTripleT3.ratchetAbs
                                Tacenta.SessionUnitTripleT3.spqrAbs state m →
                              Tacenta.UnitLifecycleT1.ReceiveHeadroom state →
                                Tacenta.UnitLifecycleT3.RetryReceiveBounds m header mh output →
                                  Model.Triple.classicalSkippedLength m + Model.State.maxSkippedStore ≤
                                      Aeneas.Std.UScalar.cMax Aeneas.Std.UScalarTy.Usize →
                                    Model.Triple.postQuantumSkippedLength m + Model.SparseRatchet.maxSkippedStore ≤
                                        Aeneas.Std.UScalar.cMax Aeneas.Std.UScalarTy.Usize →
                                      ∃ out,
                                        tacenta_session_unit.lifecycle.receive_with_eviction state composite header
                                              dhOutRecv dhOutSend newDhsPub output =
                                            Aeneas.Std.Result.ok out ∧
                                          (Tacenta.UnitLifecycleRetryLoopT3.OutcomeRefines out
                                              (Model.Lifecycle.receiveWithEviction m modelComposite
                                                { dr := mh, epoch := ↑header.epoch, pqN := ↑header.pq_n }
                                                (Tacenta.SessionUnitTripleT3.keyOf dhOutRecv)
                                                (Tacenta.SessionUnitTripleT3.keyOf dhOutSend)
                                                (Tacenta.SessionUnitTripleT3.keyOf newDhsPub)
                                                (Option.map Tacenta.SessionUnitTripleT3.spqrOutputOf output)) ∨
                                            Tacenta.UnitLifecycleRetryLoopT3.OpenRefusal header mh output dhOutRecv
                                              dhOutSend newDhsPub out
                                              (Model.Lifecycle.receiveWithEviction m modelComposite
                                                { dr := mh, epoch := ↑header.epoch, pqN := ↑header.pq_n }
                                                (Tacenta.SessionUnitTripleT3.keyOf dhOutRecv)
                                                (Tacenta.SessionUnitTripleT3.keyOf dhOutSend)
                                                (Tacenta.SessionUnitTripleT3.keyOf newDhsPub)
                                                (Option.map Tacenta.SessionUnitTripleT3.spqrOutputOf output)))
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleRetryLoopT3.receive_with_eviction_refines

/--
info: Tacenta.UnitLifecycleRetryLoopT3.receiveWithEvictionLoopResult_stop : ∀ (state : Model.Triple.State)
  (composite : Model.CompositeHeader.Composite) (header : Model.Triple.Header)
  (dhOutRecv dhOutSend newDhsPub : Model.Lifecycle.Key) (output : Option Model.SparseRatchet.Output)
  (pending reason : Model.Triple.ReceiveRefusal) (half : Model.Lifecycle.FullStore) (batch fuel : ℕ)
  (evictedState : Model.Triple.State) (evicted : ℕ),
  (match half with
      | Model.Lifecycle.FullStore.classical => Model.Triple.evictOldestClassical state batch
      | Model.Lifecycle.FullStore.postQuantum => Model.Triple.evictOldestPostQuantum state batch) =
      (evictedState, evicted) →
    evicted ≠ 0 →
      Model.Triple.receiveDetailed evictedState header dhOutRecv dhOutSend newDhsPub output = Except.error reason →
        Model.Lifecycle.fullStore reason = none →
          Model.Lifecycle.ReceiveWithEvictionLoopResult state composite header dhOutRecv dhOutSend newDhsPub output
            pending half batch (fuel + 1) (Except.error reason)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleRetryLoopT3.receiveWithEvictionLoopResult_stop

/--
info: Tacenta.UnitLifecycleRetryLoopT3.shortfall_covers : ∀ (half : tacenta_session_unit.lifecycle.FullStore)
  (state : tacenta_session_unit.tacenta_triple.State) (modelState : Model.Triple.State)
  (composite : tacenta_session_unit.tacenta_wire.Composite) (modelComposite : Model.CompositeHeader.Composite),
  Tacenta.SessionUnitTripleT3.StateRefines Tacenta.SessionUnitTripleT3.ratchetAbs Tacenta.SessionUnitTripleT3.spqrAbs
      state modelState →
    Tacenta.UnitLifecycleT3.CompositeRefines composite modelComposite →
      Model.Triple.classicalSkippedLength modelState + Model.State.maxSkippedStore ≤
          Aeneas.Std.UScalar.cMax Aeneas.Std.UScalarTy.Usize →
        Model.Triple.postQuantumSkippedLength modelState + Model.SparseRatchet.maxSkippedStore ≤
            Aeneas.Std.UScalar.cMax Aeneas.Std.UScalarTy.Usize →
          ∃ batch,
            tacenta_session_unit.lifecycle.receive_shortfall half state composite = Aeneas.Std.Result.ok batch ∧
              Tacenta.UnitLifecycleRetryLoopT3.BatchCovers (Tacenta.UnitLifecycleRetryLoopT3.halfLength half modelState)
                batch
                (Model.Lifecycle.receiveShortfall (Tacenta.UnitLifecycleT3.fullStoreOfReal half) modelState
                  modelComposite)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleRetryLoopT3.shortfall_covers

/--
info: Tacenta.UnitLifecycleRetryLoopT3.evict_for_retry_covers : Tacenta.UnitLifecycleT1.TripleReceiveContracts →
  Tacenta.SessionUnitSpqrT3.RemoveSkippedAtAgrees →
    ∀ (half : tacenta_session_unit.lifecycle.FullStore) (s : tacenta_session_unit.tacenta_triple.State)
      (m : Model.Triple.State) (batch : Aeneas.Std.Usize) (modelBatch : ℕ),
      Tacenta.SessionUnitTripleT3.StateRefines Tacenta.SessionUnitTripleT3.ratchetAbs
          Tacenta.SessionUnitTripleT3.spqrAbs s m →
        Tacenta.UnitLifecycleRetryLoopT3.BatchCovers (Tacenta.UnitLifecycleRetryLoopT3.halfLength half m) batch
            modelBatch →
          Tacenta.UnitLifecycleT1.ReceiveHeadroom s →
            Model.Triple.classicalSkippedLength m + Model.State.maxSkippedStore ≤
                Aeneas.Std.UScalar.cMax Aeneas.Std.UScalarTy.Usize →
              ∃ s1 evicted,
                tacenta_session_unit.lifecycle.evict_for_retry s half batch = Aeneas.Std.Result.ok (s1, evicted) ∧
                  Tacenta.SessionUnitTripleT3.StateRefines Tacenta.SessionUnitTripleT3.ratchetAbs
                      Tacenta.SessionUnitTripleT3.spqrAbs s1
                      (Tacenta.UnitLifecycleRetryLoopT3.evictHalf (Tacenta.UnitLifecycleT3.fullStoreOfReal half) m
                          modelBatch).1 ∧
                    ↑evicted =
                        (Tacenta.UnitLifecycleRetryLoopT3.evictHalf (Tacenta.UnitLifecycleT3.fullStoreOfReal half) m
                            modelBatch).2 ∧
                      Tacenta.UnitLifecycleT1.ReceiveHeadroom s1 ∧
                        Tacenta.UnitLifecycleT1.skippedTotal s1 ≤ Tacenta.UnitLifecycleT1.skippedTotal s ∧
                          (0 < ↑evicted →
                            Tacenta.UnitLifecycleT1.skippedTotal s1 < Tacenta.UnitLifecycleT1.skippedTotal s)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleRetryLoopT3.evict_for_retry_covers

/--
info: structure Tacenta.UnitLifecycleRetryLoopT3.LoopRel (header : tacenta_session_unit.tacenta_triple.Header)
  (mh : Model.State.Header) (output : Option tacenta_session_unit.tacenta_spqr.Output)
  (half : tacenta_session_unit.lifecycle.FullStore) (work : tacenta_session_unit.tacenta_triple.State)
  (batch : Aeneas.Std.Usize) (pending : tacenta_session_unit.tacenta_triple.TripleError) (m : Model.Triple.State)
  (modelBatch : ℕ) (modelPending : Model.Triple.ReceiveRefusal) : Prop
number of parameters: 10
fields:
  Tacenta.UnitLifecycleRetryLoopT3.LoopRel.state : Tacenta.SessionUnitTripleT3.StateRefines
      Tacenta.SessionUnitTripleT3.ratchetAbs Tacenta.SessionUnitTripleT3.spqrAbs work m
  Tacenta.UnitLifecycleRetryLoopT3.LoopRel.batch : Tacenta.UnitLifecycleRetryLoopT3.BatchCovers
      (Tacenta.UnitLifecycleRetryLoopT3.halfLength half m) batch modelBatch
  Tacenta.UnitLifecycleRetryLoopT3.LoopRel.pending : Tacenta.UnitLifecycleT3.tripleReceiveRefusalOfReal pending =
      some modelPending
  Tacenta.UnitLifecycleRetryLoopT3.LoopRel.headroom : Tacenta.UnitLifecycleT1.ReceiveHeadroom work
  Tacenta.UnitLifecycleRetryLoopT3.LoopRel.bounds : Tacenta.UnitLifecycleT3.RetryReceiveBounds m header mh output
  Tacenta.UnitLifecycleRetryLoopT3.LoopRel.classicalStore : Model.Triple.classicalSkippedLength m +
        Model.State.maxSkippedStore ≤
      Aeneas.Std.UScalar.cMax Aeneas.Std.UScalarTy.Usize
  Tacenta.UnitLifecycleRetryLoopT3.LoopRel.sparseStore : Model.Triple.postQuantumSkippedLength m +
        Model.SparseRatchet.maxSkippedStore ≤
      Aeneas.Std.UScalar.cMax Aeneas.Std.UScalarTy.Usize
constructor:
  Tacenta.UnitLifecycleRetryLoopT3.LoopRel.mk {header : tacenta_session_unit.tacenta_triple.Header}
    {mh : Model.State.Header} {output : Option tacenta_session_unit.tacenta_spqr.Output}
    {half : tacenta_session_unit.lifecycle.FullStore} {work : tacenta_session_unit.tacenta_triple.State}
    {batch : Aeneas.Std.Usize} {pending : tacenta_session_unit.tacenta_triple.TripleError} {m : Model.Triple.State}
    {modelBatch : ℕ} {modelPending : Model.Triple.ReceiveRefusal}
    (state :
      Tacenta.SessionUnitTripleT3.StateRefines Tacenta.SessionUnitTripleT3.ratchetAbs
        Tacenta.SessionUnitTripleT3.spqrAbs work m) :
    Tacenta.UnitLifecycleRetryLoopT3.BatchCovers (Tacenta.UnitLifecycleRetryLoopT3.halfLength half m) batch modelBatch →
      Tacenta.UnitLifecycleT3.tripleReceiveRefusalOfReal pending = some modelPending →
        ∀ (headroom : Tacenta.UnitLifecycleT1.ReceiveHeadroom work)
          (bounds : Tacenta.UnitLifecycleT3.RetryReceiveBounds m header mh output)
          (classicalStore :
            Model.Triple.classicalSkippedLength m + Model.State.maxSkippedStore ≤
              Aeneas.Std.UScalar.cMax Aeneas.Std.UScalarTy.Usize)
          (sparseStore :
            Model.Triple.postQuantumSkippedLength m + Model.SparseRatchet.maxSkippedStore ≤
              Aeneas.Std.UScalar.cMax Aeneas.Std.UScalarTy.Usize),
          Tacenta.UnitLifecycleRetryLoopT3.LoopRel header mh output half work batch pending m modelBatch modelPending
-/
#guard_msgs in
#print Tacenta.UnitLifecycleRetryLoopT3.LoopRel

/--
info: def Tacenta.UnitLifecycleRetryLoopT3.OutcomeRefines : Aeneas.Std.core.result.Result
    (tacenta_session_unit.tacenta_triple.State × Aeneas.Std.Array Aeneas.Std.U8 32#usize)
    tacenta_session_unit.tacenta_triple.TripleError →
  Except Model.Triple.ReceiveRefusal (Model.Triple.State × Model.Lifecycle.Key) → Prop :=
fun out res =>
  match out, res with
  | Aeneas.Std.core.result.Result.Ok value, Except.ok modelValue =>
    Tacenta.SessionUnitTripleT3.StateRefines Tacenta.SessionUnitTripleT3.ratchetAbs Tacenta.SessionUnitTripleT3.spqrAbs
        value.1 modelValue.1 ∧
      Tacenta.SessionUnitTripleT3.keyOf value.2 = modelValue.2
  | Aeneas.Std.core.result.Result.Err reason, Except.error modelReason =>
    Tacenta.UnitLifecycleT3.tripleReceiveRefusalOfReal reason = some modelReason
  | x, x_1 => False
-/
#guard_msgs in
#print Tacenta.UnitLifecycleRetryLoopT3.OutcomeRefines

/--
info: def Tacenta.UnitLifecycleRetryLoopT3.OpenRefusal : tacenta_session_unit.tacenta_triple.Header →
  Model.State.Header →
    Option tacenta_session_unit.tacenta_spqr.Output →
      Aeneas.Std.Array Aeneas.Std.U8 32#usize →
        Aeneas.Std.Array Aeneas.Std.U8 32#usize →
          Aeneas.Std.Array Aeneas.Std.U8 32#usize →
            Aeneas.Std.core.result.Result
                (tacenta_session_unit.tacenta_triple.State × Aeneas.Std.Array Aeneas.Std.U8 32#usize)
                tacenta_session_unit.tacenta_triple.TripleError →
              Except Model.Triple.ReceiveRefusal (Model.Triple.State × Model.Lifecycle.Key) → Prop :=
fun header mh output dhOutRecv dhOutSend newDhsPub out res =>
  ∃ reason work m,
    out = Aeneas.Std.core.result.Result.Err reason ∧
      tacenta_session_unit.lifecycle.full_store reason = Aeneas.Std.Result.ok none ∧
        Tacenta.SessionUnitTripleT3.StateRefines Tacenta.SessionUnitTripleT3.ratchetAbs
            Tacenta.SessionUnitTripleT3.spqrAbs work m ∧
          Tacenta.UnitLifecycleT3.RetryReceiveBounds m header mh output ∧
            Tacenta.UnitLifecycleT1.ReceiveHeadroom work ∧
              tacenta_session_unit.lifecycle.receive_attempt work header dhOutRecv dhOutSend newDhsPub output =
                  Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Err reason) ∧
                ∀ (modelReason : Model.Triple.ReceiveRefusal),
                  Tacenta.UnitLifecycleT3.tripleReceiveRefusalOfReal reason = some modelReason →
                    Model.Triple.receiveDetailed m { dr := mh, epoch := ↑header.epoch, pqN := ↑header.pq_n }
                          (Tacenta.SessionUnitTripleT3.keyOf dhOutRecv) (Tacenta.SessionUnitTripleT3.keyOf dhOutSend)
                          (Tacenta.SessionUnitTripleT3.keyOf newDhsPub)
                          (Option.map Tacenta.SessionUnitTripleT3.spqrOutputOf output) =
                        Except.error modelReason →
                      res = Except.error modelReason
-/
#guard_msgs in
#print Tacenta.UnitLifecycleRetryLoopT3.OpenRefusal

/--
info: def Tacenta.UnitLifecycleRetryLoopT3.BatchCovers : ℕ → Aeneas.Std.Usize → ℕ → Prop :=
fun len concrete model => ↑concrete = model ∨ len ≤ ↑concrete ∧ len ≤ model
-/
#guard_msgs in
#print Tacenta.UnitLifecycleRetryLoopT3.BatchCovers

/--
info: def Tacenta.UnitLifecycleRetryLoopT3.halfLength : tacenta_session_unit.lifecycle.FullStore → Model.Triple.State → ℕ :=
fun x x_1 =>
  match x, x_1 with
  | tacenta_session_unit.lifecycle.FullStore.Classical, m => Model.Triple.classicalSkippedLength m
  | tacenta_session_unit.lifecycle.FullStore.PostQuantum, m => Model.Triple.postQuantumSkippedLength m
-/
#guard_msgs in
#print Tacenta.UnitLifecycleRetryLoopT3.halfLength

/--
info: def Tacenta.UnitLifecycleRetryLoopT3.evictHalf : Model.Lifecycle.FullStore →
  Model.Triple.State → ℕ → Model.Triple.State × ℕ :=
fun x x_1 x_2 =>
  match x, x_1, x_2 with
  | Model.Lifecycle.FullStore.classical, m, count => Model.Triple.evictOldestClassical m count
  | Model.Lifecycle.FullStore.postQuantum, m, count => Model.Triple.evictOldestPostQuantum m count
-/
#guard_msgs in
#print Tacenta.UnitLifecycleRetryLoopT3.evictHalf
