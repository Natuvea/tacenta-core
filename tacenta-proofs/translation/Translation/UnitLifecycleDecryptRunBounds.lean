import Translation.UnitLifecycleDecryptScreen
import Translation.SessionUnitDecodedStateDischarge

/-!
# The per-run receive bounds of `decrypt_ratchet`, from `Session::invariant`

`UnitLifecycleDecryptRatchetCompleteT3.decrypt_ratchet_refines_complete` takes `DecryptRatchetHeadroom` and
`DecryptRatchetRun`.  The run record's `retry` field asks the eleven fields of `RetryRunBounds` of the
model Triple state, at the header and the sparse output of the run, and its `braidEpoch` field asks a
Braid epoch ceiling; a caller had to supply all twelve.  This module derives `RetryRunBounds` from
`Session::invariant`, the session relation and four counter ceilings (`CounterHeadroom`), and restates
the complete theorem with the invariant and those ceilings in place of `retry`, `braidEpoch` and
`DecryptRatchetHeadroom` (the last is `decryptHeadroom_of_invariant`).  Of the eleven fields, the invariant
alone gives five, the invariant with the assumed sparse epoch ceiling two more, and the model one; the
ceilings give the remaining three and the run's Braid epoch bound.

## Where each field of `RetryRunBounds` comes from

* `classicalMatch`: the classical ratchet's invariant, its clause that no two stored keys share
  `(dh, n)` (`Ratchet.Inv.store_map`), carried through the state relation.
* `classicalEvents`: `CounterHeadroom.classicalEvents`.  The invariant gives `events < u32::MAX` only.
* `sparseEpoch`: `CounterHeadroom.sparseEpoch`.  The invariant gives `epoch < u64::MAX` only
  (`Spqr.inv_gives_epoch_room`).
* `sparseChainsRoom`: the sparse ratchet's invariant, which keeps at most two chain-table entries
  (`Spqr.inv_gives_chain_room`).
* `sparseChainEpochs`, `sparseSkippedEpochs`: the sparse invariant's epoch window and its clause that
  every stored key's epoch has a chain-table entry, together with `CounterHeadroom.sparseEpoch`
  (`SessionUnitDecodedStateDischarge.session_unit_spqr_epoch_family`).
* `sparseOutputEpoch`: the model alone.  A key `Model.Braid.receive` outputs is labelled with an epoch
  of at most `u64::MAX - 2`, for every Braid state and message (`Model.Braid.receive_output_epoch_lt`),
  so nothing about the session is used.
* `sparseMatch`: the sparse invariant's clause that no two stored keys share `(epoch, n)`.
* `sparseCounters`: `CounterHeadroom.sparseCounters`.  No clause of the sparse invariant bounds a chain's
  message counter.
* `classicalStore`, `sparseStore`: each invariant's `skipped.len() <= MAX_SKIPPED_STORE` (2000), and
  `2000 + 2000 <= 2^32 - 1`, the bound Aeneas gives every `usize` at both platform widths.

The run's Braid epoch ceiling is `CounterHeadroom.braidEpoch`: the Braid invariant states `epoch >= 1` and
no upper bound, and the decoder's bound `epoch < u64::MAX` is one step short of it.

## `CounterHeadroom` is assumed, and excludes reachable states

Each of its four fields is one step below a ceiling the invariant states or the code keeps, so each
refuses a state `Session::invariant` accepts: a classical clock at `MAX_EVENTS = u32::MAX - 1`, where the
crate's clamp parks it; a sparse epoch at `u64::MAX - 1`; a sparse chain counter at `u64::MAX`; a Braid
epoch at `u64::MAX - 1`.  They are counter ceilings, not capacity bounds, and a long enough session
reaches each, and an exclusion is permanent for a session: a parked clock stays parked, and one exhausted
chain counter, a send chain's included, excludes every receive until its epoch retires.  By reading only,
the Braid epoch ceiling covers the sparse one wherever the bounds are used (the invariant's Braid-epoch
relation, and the terminal guard before the Triple step); the sparse field is kept because the run record
asks `RetryRunBounds` of every run.  `invariant_does_not_give_counterHeadroom` proves the first case: a session with the
clock at `u32::MAX - 1` passes `Session::invariant` and fails `CounterHeadroom`.  For the other three the
exclusion is by reading the Rust (the sparse ratchet's and the Braid's `invariant` docs), not checked in
Lean here.

## What is shown

* `retryRunBounds_of_triple_invariant`, `retryRunBounds_of_invariant`: the derivation, at the Triple and at
  the session level, for every header and every sparse output a Braid receive returns.
* `decryptRatchetRun_of_invariant`, `decrypt_ratchet_refines_of_invariant` (statement
  `DecryptRatchetRefinesOfInvariantStatement`): the run record from the invariant, `CounterHeadroom` and
  the run's three remaining conditions (`DecryptRatchetRunInputs`: the chunk relation, `HonestChunk` and
  one draw), and the complete refinement under those hypotheses.  `decrypt_ratchet_refines_complete` is
  unchanged.
* `counterHeadroom_sessionOf`, `decrypt_of_invariant_hypotheses_jointly_satisfiable`: the ceilings hold at
  a session over fresh states, and the whole hypothesis set of the restated theorem holds at the joint
  witness of `UnitLifecycleDecryptScreen`, under its named laws.
* `parkedSession_invariant`, `parkedSession_not_counterHeadroom`, `invariant_does_not_give_counterHeadroom`:
  the excluded state above.

## What it does not show

* That `CounterHeadroom` holds of any session a caller holds: it is a per-run hypothesis.
* That the crate's operations produce `parkedSession`; that a parked clock is reachable is the Rust
  clamp's documented behaviour (`tacenta-core/ratchet/src/lib.rs`, `MAX_EVENTS`), not a theorem here.
* Whether the four ceilings could be dropped from the refinement theorems that take them: not checked.
* Anything about the run's chunk, `HonestChunk` or draw conditions, which stay the caller's.

No proof here chooses a width of `usize`, so each result holds at both.  The restated theorem rests on the
constants `decrypt_ratchet_refines_complete` rests on, which its pin lists.
-/

namespace Tacenta.UnitLifecycleDecryptRunBounds

open Aeneas Aeneas.Std Result
open tacenta_session_unit
open Tacenta.UnitLifecycleT3
open Tacenta.UnitLifecycleDecryptRatchetT3

/-- **The counter ceilings `decrypt_ratchet`'s refinement takes that `Session::invariant` does not give.**
Assumed per run.  Each field is one step below a ceiling and so excludes a state the invariant accepts and
a long session reaches: `classicalEvents` the clock parked at `u32::MAX - 1`, `sparseEpoch` the epoch
`u64::MAX - 1`, `sparseCounters` a chain counter at `u64::MAX`, `braidEpoch` the Braid epoch `u64::MAX - 1`.
These are not capacity bounds.  Stated of the translated session, whose fields carry the machine widths
the ceilings are about; `retryRunBounds_of_invariant` carries them to the model state. -/
structure CounterHeadroom (real : lifecycle.Session) : Prop where
  classicalEvents : real.triple.classical.events.val + 1 < Std.U32.max
  sparseEpoch : real.triple.post_quantum.epoch.val + 1 < Std.U64.max
  sparseCounters : ∀ p ∈ real.triple.post_quantum.chains.val, ∀ ch : tacenta_spqr.Chain,
    (p.2.send = some ch ∨ p.2.receive = some ch) → ch.n.val < Std.U64.max
  braidEpoch : (Tacenta.SessionUnitBraidT1.State.epoch_val real.braid.state).val + 1 <
    Std.U64.max

/-- The classical invariant's map clause gives `RetryRunBounds.classicalMatch`'s filter form. -/
theorem classicalMatch_of_inv {s : tacenta_ratchet.State} {m : Model.State.State}
    (hR : Tacenta.SessionUnitT3.StateR s m)
    (hi : Tacenta.SessionUnitRatchetImportInv.Ratchet.Inv s) (mh : Model.State.Header) :
    (m.skipped.filter (fun x => x.1 == mh.dh && x.2.1 == mh.n)).length ≤ 1 := by
  have h := Tacenta.SessionUnitRatchetImportInv.Ratchet.inv_gives_store_is_map s m hR hi mh
  have heq : m.skipped.filter (fun x => x.1 == mh.dh && x.2.1 == mh.n) =
      m.skipped.filter (Tacenta.SessionUnitT3.matchesHeader mh) := by
    apply List.filter_congr
    rintro ⟨dh, n, t, k⟩ _
    rfl
  rw [heq]
  exact h

/-- The sparse invariant's map clause gives at most one stored key for any `(epoch, n)`, read as naturals. -/
theorem sparseMatch_of_inv {s : tacenta_spqr.State} {m : Model.SparseRatchet.State}
    (hR : Tacenta.SessionUnitSpqrT3.StateRefines s m)
    (hi : Tacenta.SessionUnitRatchetImportInv.Spqr.Inv s) (e n : Nat) :
    (m.skipped.filter (fun x => x.1 == e && x.2.1 == n)).length ≤ 1 := by
  have hpm : m.skipped.Pairwise (fun a b =>
      (Prod.fst a, Prod.fst (Prod.snd a)) ≠ (Prod.fst b, Prod.fst (Prod.snd b))) := by
    rw [← hR.skipped, List.pairwise_map]
    refine hi.skipped_map.imp ?_
    intro a b hab
    simp only [Tacenta.SessionUnitSpqrT3.skippedOf, ne_eq, Prod.mk.injEq, not_and]
    intro h1 h2
    exact hab ⟨by scalar_tac, by scalar_tac⟩
  refine Tacenta.SessionUnitRatchetImportInv.length_filter_le_one_of_pairwise
    (k := (e, n)) hpm ?_
  rintro ⟨a, b, c⟩ _ hpe
  simp only [Bool.and_eq_true, beq_iff_eq] at hpe
  simp [hpe.1, hpe.2]

/-- A counter ceiling on the translated chain table is the same ceiling on the model's. -/
theorem sparseCounters_transport {s : tacenta_spqr.State} {m : Model.SparseRatchet.State}
    (hR : Tacenta.SessionUnitSpqrT3.StateRefines s m)
    (hc : ∀ p ∈ s.chains.val, ∀ ch : tacenta_spqr.Chain,
      (p.2.send = some ch ∨ p.2.receive = some ch) → ch.n.val < Std.U64.max) :
    ∀ p ∈ m.chains, ∀ ch : Model.SparseRatchet.Chain,
      (p.2.send = some ch ∨ p.2.receive = some ch) → ch.n < Std.U64.max := by
  intro p hp ch hch
  rw [← hR.chains, List.mem_map] at hp
  obtain ⟨q, hq, rfl⟩ := hp
  simp only [Tacenta.SessionUnitSpqrT3.chainsEntryOf, Tacenta.SessionUnitSpqrT3.chainsOf,
    Option.map_eq_some_iff] at hch
  rcases hch with ⟨c, hc', rfl⟩ | ⟨c, hc', rfl⟩
  · exact hc q hq c (Or.inl hc')
  · exact hc q hq c (Or.inr hc')

/-- A store of at most 2000 keys leaves the room `RetryRunBounds` asks under `cMax Usize`. -/
theorem store_room (L : Nat) (h : L ≤ 2000) :
    L + Model.State.maxSkippedStore ≤ UScalar.cMax UScalarTy.Usize := by
  rw [cMax_usize]
  simp only [Model.State.maxSkippedStore]
  omega

/-- **`RetryRunBounds` from `Triple::invariant`, the Triple relation and three counter ceilings**, for every
header and every sparse output labelled below `u64::MAX - 1`. -/
theorem retryRunBounds_of_triple_invariant {t : tacenta_triple.State} {m : Model.Triple.State}
    (hinv : tacenta_triple.State.invariant t = ok true)
    (hrel : Tacenta.SessionUnitTripleT3.StateRefines
      Tacenta.SessionUnitTripleT3.ratchetAbs Tacenta.SessionUnitTripleT3.spqrAbs t m)
    (hevents : t.classical.events.val + 1 < Std.U32.max)
    (hepoch : t.post_quantum.epoch.val + 1 < Std.U64.max)
    (hcounters : ∀ p ∈ t.post_quantum.chains.val, ∀ ch : tacenta_spqr.Chain,
      (p.2.send = some ch ∨ p.2.receive = some ch) → ch.n.val < Std.U64.max)
    (header : Model.Triple.Header) (output : Option Model.SparseRatchet.Output)
    (houtput : ∀ o, output = some o → o.keyEpoch + 1 < Model.Braid.u64Max) :
    RetryRunBounds m header output := by
  have hspqInv : Tacenta.SessionUnitRatchetImportInv.Spqr.Inv t.post_quantum :=
    (Tacenta.SessionUnitRatchetImportInv.Spqr.invariant_true_iff _).mp
      (Tacenta.UnitHeadroomInvariant.triple_invariant_gives_spqr t hinv)
  have hratInv : Tacenta.SessionUnitRatchetImportInv.Ratchet.Inv t.classical := by
    apply (Tacenta.SessionUnitRatchetImportInv.Ratchet.invariant_true_iff _).mp
    unfold tacenta_triple.State.invariant at hinv
    repeat' first
      | (replace hinv := Tacenta.SessionUnitRatchetImportInv.bind_eq_ok_inv hinv;
         obtain ⟨_, _, hinv⟩ := hinv)
      | split at hinv
      | simp at hinv
    all_goals simp_all
  obtain ⟨hcl, hpq⟩ := hrel
  have hR : Tacenta.SessionUnitT3.StateR t.classical m.classical :=
    hcl ▸ Tacenta.SessionUnitTripleT3.ratchetAbs_stateR t.classical
  have hS : Tacenta.SessionUnitSpqrT3.StateRefines t.post_quantum m.postQuantum :=
    hpq ▸ Tacenta.SessionUnitTripleT3.spqrAbs_refines t.post_quantum
  have hfam := Tacenta.SessionUnitDecodedStateDischarge.session_unit_spqr_epoch_family hspqInv hepoch
  have hroom := Tacenta.SessionUnitRatchetImportInv.Spqr.inv_gives_chain_room _ hspqInv
  have hcs := hratInv.store_bound
  have hss := hspqInv.store_bound
  have hmax1 : (tacenta_ratchet.MAX_SKIPPED_STORE : Usize).val = 2000 := by
    simp [tacenta_ratchet.MAX_SKIPPED_STORE]
  have hmax2 : (tacenta_spqr.MAX_SKIPPED_STORE : Usize).val = 2000 := by
    simp [tacenta_spqr.MAX_SKIPPED_STORE]
  refine
    { classicalMatch := classicalMatch_of_inv hR hratInv header.dr
      classicalEvents := ?_
      sparseEpoch := ?_
      sparseChainsRoom := ?_
      sparseChainEpochs := ?_
      sparseSkippedEpochs := ?_
      sparseOutputEpoch := ?_
      sparseMatch := sparseMatch_of_inv hS hspqInv header.epoch header.pqN
      sparseCounters := sparseCounters_transport hS hcounters
      classicalStore := ?_
      sparseStore := ?_ }
  · rw [← hR.events]; exact hevents
  · rw [← hS.epoch]; exact hepoch
  · rw [← hS.chains, List.length_map]; exact hroom
  · intro p hp
    rw [← hS.chains, List.mem_map] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    exact hfam.1 q hq
  · intro sk hsk
    rw [← hS.skipped, List.mem_map] at hsk
    obtain ⟨q, hq, rfl⟩ := hsk
    exact hfam.2 q hq
  · intro o ho
    have h := houtput o ho
    simp only [Model.SparseRatchet.epochsKept, Model.Braid.u64Max, U64.max_eq] at h ⊢
    omega
  · rw [← hR.skipped, List.length_map]
    exact store_room _ (by omega)
  · rw [← hS.skipped, List.length_map]
    exact store_room _ (by omega)

/-- The sparse output of any Braid receive is labelled with an epoch below `u64::MAX - 1`
(`Model.Braid.receive_output_epoch_lt`). -/
theorem sparseOutputOf_epoch (K : Model.Braid.Kem) (st : Model.Braid.BraidState)
    (msg : Model.Braid.Msg) :
    ∀ o, Model.Lifecycle.sparseOutputOf (Model.Braid.receive K st msg).2.1 = some o →
      o.keyEpoch + 1 < Model.Braid.u64Max := by
  intro o ho
  simp only [Model.Lifecycle.sparseOutputOf, Option.map_eq_some_iff] at ho
  obtain ⟨b, hb, rfl⟩ := ho
  exact Model.Braid.receive_output_epoch_lt K st msg b hb

/-- **`RetryRunBounds` of the model Triple state from `Session::invariant`, `SessionRefines` and
`CounterHeadroom`**, for every header and the sparse output of every Braid receive. -/
theorem retryRunBounds_of_invariant {dh : DhView} {K : Model.Braid.Kem}
    {real : lifecycle.Session} {model : Model.Lifecycle.Session}
    (hinv : lifecycle.Session.invariant real = ok true)
    (hrel : SessionRefines dh K real model)
    (hc : CounterHeadroom real)
    (header : Model.Triple.Header) (K' : Model.Braid.Kem) (st : Model.Braid.BraidState)
    (msg : Model.Braid.Msg) :
    RetryRunBounds model.triple header
      (Model.Lifecycle.sparseOutputOf (Model.Braid.receive K' st msg).2.1) := by
  obtain ⟨htriple, -⟩ := Tacenta.UnitLifecycleT1.leaf_check_gives_leaf_invariants real
    (Tacenta.UnitLifecycleT1.session_invariant_gives_leaf_check real hinv)
  exact retryRunBounds_of_triple_invariant htriple hrel.triple hc.classicalEvents hc.sparseEpoch
    hc.sparseCounters header _ (sparseOutputOf_epoch K' st msg)


/-- The fields of `DecryptRatchetRun` this module does not derive: the chunk relation, `HonestChunk` and one
draw left in the trace, word for word. -/
structure DecryptRatchetRunInputs {R : Type} (view : Model.Lifecycle.CodewordView)
    (oracle : Model.Lifecycle.Oracle) (trace : R → List Model.Lifecycle.Key)
    (real : lifecycle.Session) (model : Model.Lifecycle.Session)
    (message : Slice Std.U8) (rng : R) : Prop where
  chunk : ∀ (realComposite : tacenta_wire.Composite)
      (modelComposite : Model.CompositeHeader.Composite) (ciphertext : Bytes),
      Model.CompositeHeader.decodeDetailed (sliceOf message) =
        .ok (modelComposite, ciphertext) →
      CompositeRefines realComposite modelComposite →
      IncomingChunkRefines view model.braid realComposite modelComposite
  honest : ∀ (modelComposite : Model.CompositeHeader.Composite) (ciphertext : Bytes),
      Model.CompositeHeader.decodeDetailed (sliceOf message) =
        .ok (modelComposite, ciphertext) →
      Tacenta.SessionUnitBraidT3.HonestChunk model.braid
        (Model.Lifecycle.braidMessageOf view model.braid modelComposite)
  draw : ∃ draw rest, trace rng = draw :: rest

/-- `DecryptRatchetRun` from the invariant, the relation, `CounterHeadroom` and the three remaining
conditions. -/
theorem decryptRatchetRun_of_invariant {R : Type} {dh : DhView}
    {view : Model.Lifecycle.CodewordView} {oracle : Model.Lifecycle.Oracle}
    {trace : R → List Model.Lifecycle.Key} {real : lifecycle.Session}
    {model : Model.Lifecycle.Session} {message : Slice Std.U8} {rng : R}
    (hinv : lifecycle.Session.invariant real = ok true)
    (hrel : SessionRefines dh oracle.braidKem real model)
    (hc : CounterHeadroom real)
    (inputs : DecryptRatchetRunInputs view oracle trace real model message rng) :
    DecryptRatchetRun view oracle trace real model message rng :=
  { chunk := inputs.chunk
    honest := inputs.honest
    braidEpoch := hc.braidEpoch
    draw := inputs.draw
    retry := fun _ _ _ =>
      retryRunBounds_of_invariant hinv hrel hc _ _ _ _ }

/-- The statement of `decrypt_ratchet_refines_of_invariant`: the hypotheses of
`DecryptRatchetRefinesCompleteStatement` with `DecryptRatchetHeadroom` replaced by `Session::invariant` and
`DecryptRatchetRun` by `CounterHeadroom` and `DecryptRatchetRunInputs`, and the same conclusion. -/
def DecryptRatchetRefinesOfInvariantStatement : Prop :=
  ∀ {R : Type} (rngCore : rand_core_1.RngCore R) (cryptoRng : rand_core_1.CryptoRng R)
    (trace : R → List Model.Lifecycle.Key) (dh : DhView)
    (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle),
    DecryptOracleOf rngCore cryptoRng dh trace oracle →
    DhCodecOf dh →
    Tacenta.UnitLifecycleT1.DecryptRatchetContracts rngCore →
    ∀ [Tacenta.SessionUnitT1.DerivedKeysModel],
    DecryptRatchetAgreements oracle.braidKem →
    ∀ (real : lifecycle.Session) (model : Model.Lifecycle.Session)
      (message : Slice Std.U8) (rng : R),
      lifecycle.Session.invariant real = ok true →
      SessionRefines dh oracle.braidKem real model →
      CounterHeadroom real →
      trace rng = oracle.draws →
      DecryptRatchetRunInputs view oracle trace real model message rng →
      ∃ output,
        lifecycle.Session.decrypt_ratchet rngCore cryptoRng real message rng = ok output ∧
        StepRefines trace dh oracle.braidKem output
          (Model.Lifecycle.decryptRatchet view oracle model (sliceOf message))

/-- **The complete `decrypt_ratchet` refinement, with the per-run receive bounds derived.**  Under the oracle,
codec, contract, derived-key and agreement hypotheses of `decrypt_ratchet_refines_complete`,
`Session::invariant`, `SessionRefines`, `CounterHeadroom`, the trace equation and `DecryptRatchetRunInputs`,
the generated `decrypt_ratchet` returns and its result refines the model's step.  It applies
`decrypt_ratchet_refines_complete`, with `DecryptRatchetHeadroom` from `decryptHeadroom_of_invariant` and the
run record from `decryptRatchetRun_of_invariant`. -/
theorem decrypt_ratchet_refines_of_invariant {R : Type}
    (rngCore : rand_core_1.RngCore R) (cryptoRng : rand_core_1.CryptoRng R)
    (trace : R → List Model.Lifecycle.Key) (dh : DhView)
    (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle)
    (oracleOf : DecryptOracleOf rngCore cryptoRng dh trace oracle)
    (codec : DhCodecOf dh)
    (contracts : Tacenta.UnitLifecycleT1.DecryptRatchetContracts rngCore)
    [Tacenta.SessionUnitT1.DerivedKeysModel]
    (agreements : DecryptRatchetAgreements oracle.braidKem)
    (real : lifecycle.Session) (model : Model.Lifecycle.Session)
    (message : Slice Std.U8) (rng : R)
    (hinv : lifecycle.Session.invariant real = ok true)
    (hrel : SessionRefines dh oracle.braidKem real model)
    (hc : CounterHeadroom real)
    (htrace : trace rng = oracle.draws)
    (inputs : DecryptRatchetRunInputs view oracle trace real model message rng) :
    ∃ output,
      lifecycle.Session.decrypt_ratchet rngCore cryptoRng real message rng = ok output ∧
      StepRefines trace dh oracle.braidKem output
        (Model.Lifecycle.decryptRatchet view oracle model (sliceOf message)) :=
  Tacenta.UnitLifecycleDecryptRatchetCompleteT3.decrypt_ratchet_refines_complete rngCore cryptoRng
    trace dh view oracle oracleOf codec contracts agreements real model message rng hrel
    (Tacenta.UnitHeadroomInvariant.decryptHeadroom_of_invariant contracts.dhCodec
      contracts.braid.ct1Len real hinv)
    htrace (decryptRatchetRun_of_invariant hinv hrel hc inputs)

/-- The theorem has exactly the statement recorded in `DecryptRatchetRefinesOfInvariantStatement`. -/
theorem decrypt_ratchet_refines_of_invariant_statement :
    DecryptRatchetRefinesOfInvariantStatement :=
  @decrypt_ratchet_refines_of_invariant

/-! ## Non-vacuity -/

/-- **`CounterHeadroom` holds at a session over fresh states**: clock 0, sparse epoch 0, no chain counter,
Braid epoch 1. -/
theorem counterHeadroom_sessionOf (sk our peer ad dhs pending) :
    CounterHeadroom (Tacenta.UnitHeadroomSatisfiable.sessionOf sk our peer ad dhs pending) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [Tacenta.UnitHeadroomSatisfiable.sessionOf, Tacenta.UnitHeadroomSatisfiable.freshTriple,
      U32.max_eq]
  · simp [Tacenta.UnitHeadroomSatisfiable.sessionOf, Tacenta.UnitHeadroomSatisfiable.freshTriple,
      U64.max_eq]
  · intro p hp ch hch
    simp [Tacenta.UnitHeadroomSatisfiable.sessionOf, Tacenta.UnitHeadroomSatisfiable.freshTriple,
      Tacenta.UnitHeadroomSatisfiable.vecOf] at hp
    subst hp
    simp at hch
  · simp only [Tacenta.UnitHeadroomSatisfiable.sessionOf, Tacenta.UnitHeadroomSatisfiable.freshBraid,
      Tacenta.SessionUnitBraidT1.State.epoch_val]
    scalar_tac

/-- The three remaining run conditions at the joint witness, read off `invReal_run`. -/
theorem decrypt_inputs_at_invReal (K : Model.Braid.Kem) (dh : DhView) (k pkb ad a)
    (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle)
    (hK : oracle.braidKem = K) :
    DecryptRatchetRunInputs view oracle Tacenta.UnitLifecycleIntegrationScreen.byteTrace
      (Tacenta.UnitLifecycleDecryptScreen.invReal k pkb ad a)
      (Tacenta.UnitLifecycleDecryptRatchetScreen.modelOf dh
        (Tacenta.UnitLifecycleDecryptScreen.invReal k pkb ad a))
      Tacenta.UnitLifecycleDecryptRatchetScreen.sampleMessage
      Tacenta.UnitLifecycleDecryptRatchetScreen.sampleRng :=
  have run := Tacenta.UnitLifecycleDecryptScreen.invReal_run K dh k pkb ad a view oracle hK
  ⟨run.chunk, run.honest, run.draw⟩


/-- The hypotheses of `decrypt_ratchet_refines_of_invariant` at one choice of every binder. -/
structure DecryptOfInvariantHypotheses {R : Type} (rngCore : rand_core_1.RngCore R)
    (cryptoRng : rand_core_1.CryptoRng R) (trace : R → List Model.Lifecycle.Key) (dh : DhView)
    (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle)
    (real : lifecycle.Session) (model : Model.Lifecycle.Session) (message : Slice Std.U8)
    (rng : R) : Prop where
  oracleOf : DecryptOracleOf rngCore cryptoRng dh trace oracle
  codec : DhCodecOf dh
  contracts : Tacenta.UnitLifecycleT1.DecryptRatchetContracts rngCore
  derivedKeys : Nonempty Tacenta.SessionUnitT1.DerivedKeysModel
  agreements : DecryptRatchetAgreements oracle.braidKem
  invariant : lifecycle.Session.invariant real = ok true
  related : SessionRefines dh oracle.braidKem real model
  counters : CounterHeadroom real
  trace_eq : trace rng = oracle.draws
  inputs : DecryptRatchetRunInputs view oracle trace real model message rng

/-- The record is the theorem's hypothesis list: from it, `decrypt_ratchet_refines_of_invariant` applies. -/
theorem DecryptOfInvariantHypotheses.refines {R : Type} {rngCore : rand_core_1.RngCore R}
    {cryptoRng : rand_core_1.CryptoRng R} {trace : R → List Model.Lifecycle.Key} {dh : DhView}
    {view : Model.Lifecycle.CodewordView} {oracle : Model.Lifecycle.Oracle}
    {real : lifecycle.Session} {model : Model.Lifecycle.Session} {message : Slice Std.U8} {rng : R}
    (h : DecryptOfInvariantHypotheses rngCore cryptoRng trace dh view oracle real model message rng) :
    ∃ output,
      lifecycle.Session.decrypt_ratchet rngCore cryptoRng real message rng = ok output ∧
      StepRefines trace dh oracle.braidKem output
        (Model.Lifecycle.decryptRatchet view oracle model (sliceOf message)) := by
  obtain ⟨inst⟩ := h.derivedKeys
  exact decrypt_ratchet_refines_of_invariant rngCore cryptoRng trace dh view oracle h.oracleOf
    h.codec h.contracts h.agreements real model message rng h.invariant h.related h.counters
    h.trace_eq h.inputs

/-- **The hypotheses of the restated theorem hold together at the real constants, under the named laws of
`UnitLifecycleDecryptScreen`**, at its witness session (built for the hypotheses, not shown to be produced by
establishment or `import`), for every codeword view.  The laws are assumed, as there. -/
theorem decrypt_of_invariant_hypotheses_jointly_satisfiable (K : Model.Braid.Kem) (dh : DhView)
    (L : Tacenta.UnitLifecycleDecryptScreen.DecryptJointLaws K dh) :
    ∃ (oracle : Model.Lifecycle.Oracle) (real : lifecycle.Session)
      (model : Model.Lifecycle.Session) (message : Slice Std.U8) (rng : List Std.U8),
      oracle.braidKem = K ∧
      Model.Lifecycle.messageType (sliceOf message) = some .ratchet ∧
      ∀ view : Model.Lifecycle.CodewordView,
        DecryptOfInvariantHypotheses Tacenta.UnitLifecycleIntegrationScreen.byteRng
          Tacenta.UnitLifecycleIntegrationScreen.byteCrc
          Tacenta.UnitLifecycleIntegrationScreen.byteTrace dh view oracle real model message
          rng := by
  obtain ⟨oracle, hdraws, hK, horacle⟩ :=
    Tacenta.UnitOracleDecrypt.decryptOracleOf_of_laws dh L.dhCodec L.dhAgree L.aeadOpen
      L.viewInjective
      (Tacenta.UnitLifecycleIntegrationScreen.byteTrace
        Tacenta.UnitLifecycleDecryptRatchetScreen.sampleRng) K
  obtain ⟨k, pkb, a, hpub, hbytes, hcan, hprime⟩ := L.validKey
  obtain ⟨ad, had, hlen⟩ :=
    Std.WP.spec_imp_exists (Tacenta.UnitLifecycleT1.identity_ad_length L.dhCodec pkb pkb)
  refine ⟨oracle, Tacenta.UnitLifecycleDecryptScreen.invReal k pkb ad a,
    Tacenta.UnitLifecycleDecryptRatchetScreen.modelOf dh
      (Tacenta.UnitLifecycleDecryptScreen.invReal k pkb ad a),
    Tacenta.UnitLifecycleDecryptRatchetScreen.sampleMessage,
    Tacenta.UnitLifecycleDecryptRatchetScreen.sampleRng, hK,
    Tacenta.UnitLifecycleDecryptScreen.sampleMessage_type, fun view => ?_⟩
  have h0 := Tacenta.UnitLifecycleDecryptScreen.decrypt_hypotheses_at_invReal K dh L
    oracle hK hdraws horacle k pkb a hpub hbytes hcan hprime ad had hlen view
  exact ⟨h0.oracleOf, h0.codec, h0.contracts, h0.derivedKeys, h0.agreements, h0.invariant,
    h0.related, counterHeadroom_sessionOf _ _ _ _ _ _, h0.trace_eq,
    decrypt_inputs_at_invReal K dh k pkb ad a view oracle hK⟩

/-! ## A state the invariant accepts and `CounterHeadroom` refuses -/

/-- `freshTriple` with the classical clock at `MAX_EVENTS = u32::MAX - 1`, the value the crate's clamp holds it
at. -/
def parkedTriple (dhs : Array U8 32#usize) : tacenta_triple.State :=
  { Tacenta.UnitHeadroomSatisfiable.freshTriple dhs with
    classical := { (Tacenta.UnitHeadroomSatisfiable.freshTriple dhs).classical with
      events := 4294967294#u32 } }

/-- `sessionOf` over `parkedTriple`. -/
def parkedSession (k : tacenta_boundary.dh.PrivateKey) (pkb : tacenta_boundary.dh.PublicKeyBytes)
    (ad : alloc.vec.Vec U8) (a : Array U8 32#usize) : lifecycle.Session :=
  { Tacenta.UnitHeadroomSatisfiable.sessionOf k pkb pkb ad a none with triple := parkedTriple a }

/-- `Triple::invariant` accepts the parked clock. -/
theorem parkedTriple_invariant (a : Array U8 32#usize)
    (hcan : Tacenta.SessionUnitT1.canonicalX25519 a = true) :
    tacenta_triple.State.invariant (parkedTriple a) = ok true := by
  have h1 : tacenta_ratchet.State.invariant (parkedTriple a).classical = ok true := by
    rw [Tacenta.SessionUnitRatchetImportInv.Ratchet.invariant_true_iff]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [parkedTriple, Tacenta.UnitHeadroomSatisfiable.freshTriple,
        Tacenta.UnitHeadroomSatisfiable.vecOf, tacenta_ratchet.MAX_SKIPPED_STORE]
    · simp [parkedTriple, Tacenta.UnitHeadroomSatisfiable.freshTriple, U32.max_eq]
    · simp [parkedTriple, Tacenta.UnitHeadroomSatisfiable.freshTriple,
        Tacenta.UnitHeadroomSatisfiable.vecOf]
    · simp [parkedTriple, Tacenta.UnitHeadroomSatisfiable.freshTriple,
        Tacenta.UnitHeadroomSatisfiable.vecOf]
    · simp [parkedTriple, Tacenta.UnitHeadroomSatisfiable.freshTriple]
    · simpa [parkedTriple, Tacenta.UnitHeadroomSatisfiable.freshTriple] using hcan
    · simp [parkedTriple, Tacenta.UnitHeadroomSatisfiable.freshTriple]
    · simp [parkedTriple, Tacenta.UnitHeadroomSatisfiable.freshTriple,
        Tacenta.UnitHeadroomSatisfiable.vecOf]
  have h2 : (parkedTriple a).post_quantum =
      (Tacenta.UnitHeadroomSatisfiable.freshTriple a).post_quantum := rfl
  have h3 := Tacenta.UnitHeadroomInvariant.triple_invariant_gives_spqr _
    (Tacenta.UnitHeadroomInvariant.freshTriple_invariant a hcan)
  rw [← h2] at h3
  simp only [parkedTriple, Tacenta.UnitHeadroomSatisfiable.freshTriple] at h1 h3
  unfold tacenta_triple.State.invariant
  simp [h1, h3, parkedTriple, Tacenta.UnitHeadroomSatisfiable.freshTriple,
    tacenta_spqr.State.impl.direction, tacenta_ratchet.State.started_as_sender]

/-- `Session::structural_invariant` of the parked session, as of `sessionOf` (`structural_sessionOf`). -/
theorem structural_parkedSession
    (k : tacenta_boundary.dh.PrivateKey) (pkb : tacenta_boundary.dh.PublicKeyBytes)
    (a : Array U8 32#usize)
    (hpub : tacenta_boundary.dh.PrivateKey.public_key k = ok pkb)
    (hbytes : tacenta_boundary.dh.PublicKeyBytes.as_bytes pkb = ok a)
    (hcan : Tacenta.SessionUnitT1.canonicalX25519 a = true)
    (hprime : tacenta_boundary.dh.is_prime_order_public pkb = ok true)
    (hoeq : Tacenta.UnitHeadroomInvariant.OptionEqU64Shape
      (@core.option.Option.Insts.CoreCmpPartialEqOption.eq))
    (ad : alloc.vec.Vec U8) (had : lifecycle.identity_ad pkb pkb = ok ad) :
    lifecycle.Session.structural_invariant (parkedSession k pkb ad a) = ok true := by
  have hv := Tacenta.UnitHeadroomInvariant.is_valid_identity_key_eq pkb a hbytes hcan hprime
  unfold lifecycle.Session.structural_invariant
  simp [parkedSession, parkedTriple, Tacenta.UnitHeadroomSatisfiable.sessionOf, hpub, hbytes,
    tacenta_triple.State.sending_public, Tacenta.UnitHeadroomSatisfiable.freshTriple,
    tacenta_ratchet.State.sending_public, Tacenta.UnitHeadroomInvariant.array_ne_self,
    Tacenta.UnitHeadroomSatisfiable.freshBraid, tacenta_braid.Braid.failed,
    tacenta_braid.Braid.is_initiator, tacenta_braid.State.epoch, lifecycle.Session.is_responder,
    had, Tacenta.UnitHeadroomInvariant.vec_ne_self, tacenta_triple.State.direction,
    tacenta_spqr.State.impl.direction, hv,
    tacenta_braid.Braid.epoch, tacenta_triple.State.epoch, tacenta_spqr.State.impl.epoch,
    tacenta_braid.Braid.state_tag, lift, tacenta_spqr.Direction.Insts.CoreCmpPartialEqDirection.eq]
  have h01 : U64.checked_add 0#u64 1#u64 = some 1#u64 := by decide
  rw [h01, hoeq]
  rfl

/-- **`Session::invariant` accepts the parked session**, under the assumptions of `sessionOf_invariant`. -/
theorem parkedSession_invariant
    (k : tacenta_boundary.dh.PrivateKey) (pkb : tacenta_boundary.dh.PublicKeyBytes)
    (a : Array U8 32#usize)
    (hpub : tacenta_boundary.dh.PrivateKey.public_key k = ok pkb)
    (hbytes : tacenta_boundary.dh.PublicKeyBytes.as_bytes pkb = ok a)
    (hcan : Tacenta.SessionUnitT1.canonicalX25519 a = true)
    (hprime : tacenta_boundary.dh.is_prime_order_public pkb = ok true)
    (hoeq : Tacenta.UnitHeadroomInvariant.OptionEqU64Shape
      (@core.option.Option.Insts.CoreCmpPartialEqOption.eq))
    (ad : alloc.vec.Vec U8) (had : lifecycle.identity_ad pkb pkb = ok ad) :
    lifecycle.Session.invariant (parkedSession k pkb ad a) = ok true := by
  unfold lifecycle.Session.invariant
  rw [structural_parkedSession k pkb a hpub hbytes hcan hprime hoeq ad had]
  simp only [Aeneas.Std.bind_tc_ok, if_true]
  unfold lifecycle.Session.leaf_invariants
  simp only [parkedSession]
  rw [parkedTriple_invariant a hcan]
  simp [Tacenta.UnitHeadroomSatisfiable.sessionOf, Tacenta.UnitHeadroomInvariant.freshBraid_invariant]

/-- **`CounterHeadroom` refuses the parked session**: `events + 1 < u32::MAX` fails at `u32::MAX - 1`. -/
theorem parkedSession_not_counterHeadroom (k pkb ad a) :
    ¬ CounterHeadroom (parkedSession k pkb ad a) := by
  intro h
  have := h.classicalEvents
  simp [parkedSession, parkedTriple, Tacenta.UnitHeadroomSatisfiable.freshTriple, U32.max_eq] at this

/-- **`Session::invariant` does not give `CounterHeadroom`**: under `ValidKeyShape`, `OptionEqU64Shape` and
`DhCodecTotal`, a session with the clock at `u32::MAX - 1` passes the invariant and fails the ceilings. -/
theorem invariant_does_not_give_counterHeadroom (hv : Tacenta.UnitHeadroomInvariant.ValidKeyShape
      Tacenta.UnitSatisfiabilityJoint.Interp.real)
    (hoeq : Tacenta.UnitHeadroomInvariant.OptionEqU64Shape
      (@core.option.Option.Insts.CoreCmpPartialEqOption.eq))
    (hdh : Tacenta.UnitLifecycleT1.DhCodecTotal) :
    ∃ real : lifecycle.Session, lifecycle.Session.invariant real = ok true ∧
      real.triple.classical.events.val = 4294967294 ∧ ¬ CounterHeadroom real := by
  obtain ⟨k, pkb, a, hpub, hbytes, hcan, hprime⟩ := hv
  obtain ⟨ad, had, -⟩ :=
    Std.WP.spec_imp_exists (Tacenta.UnitLifecycleT1.identity_ad_length hdh pkb pkb)
  exact ⟨parkedSession k pkb ad a,
    parkedSession_invariant k pkb a hpub hbytes hcan hprime hoeq ad had, by
      simp [parkedSession, parkedTriple],
    parkedSession_not_counterHeadroom k pkb ad a⟩

end Tacenta.UnitLifecycleDecryptRunBounds

/-! ## Pins

The constants each result depends on, and the statement of each result and definition, held by the
build.  `attest.py` requires every one of them (`REQUIRED_PINS`, `REQUIRED_STATEMENT_PINS`). -/

/--
info: 'Tacenta.UnitLifecycleDecryptRunBounds.classicalMatch_of_inv' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleDecryptRunBounds.classicalMatch_of_inv

/--
info: 'Tacenta.UnitLifecycleDecryptRunBounds.sparseMatch_of_inv' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleDecryptRunBounds.sparseMatch_of_inv

/--
info: 'Tacenta.UnitLifecycleDecryptRunBounds.sparseCounters_transport' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleDecryptRunBounds.sparseCounters_transport

/--
info: 'Tacenta.UnitLifecycleDecryptRunBounds.store_room' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleDecryptRunBounds.store_room

/--
info: 'Tacenta.UnitLifecycleDecryptRunBounds.retryRunBounds_of_triple_invariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleDecryptRunBounds.retryRunBounds_of_triple_invariant

/--
info: 'Tacenta.UnitLifecycleDecryptRunBounds.sparseOutputOf_epoch' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleDecryptRunBounds.sparseOutputOf_epoch

/--
info: 'Tacenta.UnitLifecycleDecryptRunBounds.retryRunBounds_of_invariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kem.CT1_LEN,
 tacenta_session_unit.tacenta_kem.CT2_LEN,
 tacenta_session_unit.tacenta_kem.EK_VECTOR_LEN,
 tacenta_session_unit.tacenta_kem.EncapsState,
 tacenta_session_unit.tacenta_kem.HEADER_LEN,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair,
 tacenta_session_unit.tacenta_kem.encapsulate2,
 tacenta_session_unit.tacenta_kem.validate_ek,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_boundary.dh.is_prime_order_public,
 tacenta_session_unit.tacenta_boundary.kem.ciphertext_len,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.header,
 tacenta_session_unit.alloc.vec.Vec.truncate,
 tacenta_session_unit.core.num.Usize.div_ceil,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.public_key,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.from_bytes,
 tacenta_session_unit.core.option.Option.Insts.CoreCmpPartialEqOption.eq]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleDecryptRunBounds.retryRunBounds_of_invariant

/--
info: 'Tacenta.UnitLifecycleDecryptRunBounds.decryptRatchetRun_of_invariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kem.CT1_LEN,
 tacenta_session_unit.tacenta_kem.CT2_LEN,
 tacenta_session_unit.tacenta_kem.EK_VECTOR_LEN,
 tacenta_session_unit.tacenta_kem.EncapsState,
 tacenta_session_unit.tacenta_kem.HEADER_LEN,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair,
 tacenta_session_unit.tacenta_kem.encapsulate2,
 tacenta_session_unit.tacenta_kem.validate_ek,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_boundary.dh.is_prime_order_public,
 tacenta_session_unit.tacenta_boundary.kem.ciphertext_len,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.header,
 tacenta_session_unit.alloc.vec.Vec.truncate,
 tacenta_session_unit.core.num.Usize.div_ceil,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.public_key,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.from_bytes,
 tacenta_session_unit.core.option.Option.Insts.CoreCmpPartialEqOption.eq]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleDecryptRunBounds.decryptRatchetRun_of_invariant

/--
info: 'Tacenta.UnitLifecycleDecryptRunBounds.decrypt_ratchet_refines_of_invariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kdf.hkdf_sha256,
 tacenta_session_unit.tacenta_kdf.hmac_sha256,
 tacenta_session_unit.tacenta_kem.CT1_LEN,
 tacenta_session_unit.tacenta_kem.CT2_LEN,
 tacenta_session_unit.tacenta_kem.EK_VECTOR_LEN,
 tacenta_session_unit.tacenta_kem.EncapsState,
 tacenta_session_unit.tacenta_kem.HEADER_LEN,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair,
 tacenta_session_unit.tacenta_kem.encapsulate1,
 tacenta_session_unit.tacenta_kem.encapsulate2,
 tacenta_session_unit.tacenta_kem.validate_ek,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.rand_core_1.error.Error,
 tacenta_session_unit.tacenta_boundary.aead.decrypt,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_boundary.dh.is_prime_order_public,
 tacenta_session_unit.tacenta_boundary.kem.ciphertext_len,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.generate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.header,
 tacenta_session_unit.zeroize.Zeroizing.new,
 tacenta_session_unit.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.Pair.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.TupleABC.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.alloc.vec.Vec.capacity,
 tacenta_session_unit.alloc.vec.Vec.pop,
 tacenta_session_unit.alloc.vec.Vec.truncate,
 tacenta_session_unit.core.num.Usize.div_ceil,
 tacenta_session_unit.core.option.Option.as_mut,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.agree,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.from_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.public_key,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.to_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.from_bytes,
 tacenta_session_unit.zeroize.Zeroize.Blanket.zeroize,
 tacenta_session_unit.tacenta_kem.EncapsState.Insts.CoreCloneClone.clone,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 tacenta_session_unit.alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.core.option.Option.Insts.CoreCloneClone.clone,
 tacenta_session_unit.core.option.Option.Insts.CoreCmpPartialEqOption.eq,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes.eq,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleDecryptRunBounds.decrypt_ratchet_refines_of_invariant

/--
info: 'Tacenta.UnitLifecycleDecryptRunBounds.decrypt_ratchet_refines_of_invariant_statement' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kdf.hkdf_sha256,
 tacenta_session_unit.tacenta_kdf.hmac_sha256,
 tacenta_session_unit.tacenta_kem.CT1_LEN,
 tacenta_session_unit.tacenta_kem.CT2_LEN,
 tacenta_session_unit.tacenta_kem.EK_VECTOR_LEN,
 tacenta_session_unit.tacenta_kem.EncapsState,
 tacenta_session_unit.tacenta_kem.HEADER_LEN,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair,
 tacenta_session_unit.tacenta_kem.encapsulate1,
 tacenta_session_unit.tacenta_kem.encapsulate2,
 tacenta_session_unit.tacenta_kem.validate_ek,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.rand_core_1.error.Error,
 tacenta_session_unit.tacenta_boundary.aead.decrypt,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_boundary.dh.is_prime_order_public,
 tacenta_session_unit.tacenta_boundary.kem.ciphertext_len,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.generate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.header,
 tacenta_session_unit.zeroize.Zeroizing.new,
 tacenta_session_unit.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.Pair.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.TupleABC.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.alloc.vec.Vec.capacity,
 tacenta_session_unit.alloc.vec.Vec.pop,
 tacenta_session_unit.alloc.vec.Vec.truncate,
 tacenta_session_unit.core.num.Usize.div_ceil,
 tacenta_session_unit.core.option.Option.as_mut,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.agree,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.from_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.public_key,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.to_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.from_bytes,
 tacenta_session_unit.zeroize.Zeroize.Blanket.zeroize,
 tacenta_session_unit.tacenta_kem.EncapsState.Insts.CoreCloneClone.clone,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 tacenta_session_unit.alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.core.option.Option.Insts.CoreCloneClone.clone,
 tacenta_session_unit.core.option.Option.Insts.CoreCmpPartialEqOption.eq,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes.eq,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleDecryptRunBounds.decrypt_ratchet_refines_of_invariant_statement

/--
info: 'Tacenta.UnitLifecycleDecryptRunBounds.counterHeadroom_sessionOf' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kem.EncapsState,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleDecryptRunBounds.counterHeadroom_sessionOf

/--
info: 'Tacenta.UnitLifecycleDecryptRunBounds.decrypt_inputs_at_invReal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kem.EncapsState,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.core.num.Usize.div_ceil]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleDecryptRunBounds.decrypt_inputs_at_invReal

/--
info: 'Tacenta.UnitLifecycleDecryptRunBounds.DecryptOfInvariantHypotheses.refines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kdf.hkdf_sha256,
 tacenta_session_unit.tacenta_kdf.hmac_sha256,
 tacenta_session_unit.tacenta_kem.CT1_LEN,
 tacenta_session_unit.tacenta_kem.CT2_LEN,
 tacenta_session_unit.tacenta_kem.EK_VECTOR_LEN,
 tacenta_session_unit.tacenta_kem.EncapsState,
 tacenta_session_unit.tacenta_kem.HEADER_LEN,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair,
 tacenta_session_unit.tacenta_kem.encapsulate1,
 tacenta_session_unit.tacenta_kem.encapsulate2,
 tacenta_session_unit.tacenta_kem.validate_ek,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.rand_core_1.error.Error,
 tacenta_session_unit.tacenta_boundary.aead.decrypt,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_boundary.dh.is_prime_order_public,
 tacenta_session_unit.tacenta_boundary.kem.ciphertext_len,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.generate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.header,
 tacenta_session_unit.zeroize.Zeroizing.new,
 tacenta_session_unit.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.Pair.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.TupleABC.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.alloc.vec.Vec.capacity,
 tacenta_session_unit.alloc.vec.Vec.pop,
 tacenta_session_unit.alloc.vec.Vec.truncate,
 tacenta_session_unit.core.num.Usize.div_ceil,
 tacenta_session_unit.core.option.Option.as_mut,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.agree,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.from_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.public_key,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.to_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.from_bytes,
 tacenta_session_unit.zeroize.Zeroize.Blanket.zeroize,
 tacenta_session_unit.tacenta_kem.EncapsState.Insts.CoreCloneClone.clone,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 tacenta_session_unit.alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.core.option.Option.Insts.CoreCloneClone.clone,
 tacenta_session_unit.core.option.Option.Insts.CoreCmpPartialEqOption.eq,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes.eq,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleDecryptRunBounds.DecryptOfInvariantHypotheses.refines

/--
info: 'Tacenta.UnitLifecycleDecryptRunBounds.decrypt_of_invariant_hypotheses_jointly_satisfiable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kdf.hkdf_sha256,
 tacenta_session_unit.tacenta_kdf.hmac_sha256,
 tacenta_session_unit.tacenta_kem.CT1_LEN,
 tacenta_session_unit.tacenta_kem.CT2_LEN,
 tacenta_session_unit.tacenta_kem.EK_VECTOR_LEN,
 tacenta_session_unit.tacenta_kem.EncapsState,
 tacenta_session_unit.tacenta_kem.HEADER_LEN,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair,
 tacenta_session_unit.tacenta_kem.encapsulate1,
 tacenta_session_unit.tacenta_kem.encapsulate2,
 tacenta_session_unit.tacenta_kem.validate_ek,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.rand_core_1.error.Error,
 tacenta_session_unit.tacenta_boundary.aead.decrypt,
 tacenta_session_unit.tacenta_boundary.aead.encrypt,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_boundary.dh.is_prime_order_public,
 tacenta_session_unit.tacenta_boundary.kem.KeyPair,
 tacenta_session_unit.tacenta_boundary.kem.ciphertext_len,
 tacenta_session_unit.tacenta_boundary.kem.decapsulate,
 tacenta_session_unit.tacenta_boundary.kem.encapsulate,
 tacenta_session_unit.tacenta_boundary.xeddsa.verify,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.generate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.header,
 tacenta_session_unit.zeroize.Zeroizing.new,
 tacenta_session_unit.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.Pair.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.TupleABC.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.alloc.vec.Vec.capacity,
 tacenta_session_unit.alloc.vec.Vec.pop,
 tacenta_session_unit.alloc.vec.Vec.truncate,
 tacenta_session_unit.core.num.Usize.div_ceil,
 tacenta_session_unit.core.option.Option.as_mut,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.agree,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.from_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.public_key,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.to_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.from_bytes,
 tacenta_session_unit.zeroize.Zeroize.Blanket.zeroize,
 tacenta_session_unit.tacenta_kem.EncapsState.Insts.CoreCloneClone.clone,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 tacenta_session_unit.alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.core.option.Option.Insts.CoreCloneClone.clone,
 tacenta_session_unit.core.option.Option.Insts.CoreCmpPartialEqOption.eq,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes.eq,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleDecryptRunBounds.decrypt_of_invariant_hypotheses_jointly_satisfiable

/--
info: 'Tacenta.UnitLifecycleDecryptRunBounds.parkedTriple_invariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleDecryptRunBounds.parkedTriple_invariant

/--
info: 'Tacenta.UnitLifecycleDecryptRunBounds.structural_parkedSession' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kem.EncapsState,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_boundary.dh.is_prime_order_public,
 tacenta_session_unit.tacenta_boundary.kem.ciphertext_len,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.public_key,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.from_bytes,
 tacenta_session_unit.core.option.Option.Insts.CoreCmpPartialEqOption.eq]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleDecryptRunBounds.structural_parkedSession

/--
info: 'Tacenta.UnitLifecycleDecryptRunBounds.parkedSession_invariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kem.CT1_LEN,
 tacenta_session_unit.tacenta_kem.CT2_LEN,
 tacenta_session_unit.tacenta_kem.EK_VECTOR_LEN,
 tacenta_session_unit.tacenta_kem.EncapsState,
 tacenta_session_unit.tacenta_kem.HEADER_LEN,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair,
 tacenta_session_unit.tacenta_kem.validate_ek,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_boundary.dh.is_prime_order_public,
 tacenta_session_unit.tacenta_boundary.kem.ciphertext_len,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.header,
 tacenta_session_unit.core.num.Usize.div_ceil,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.public_key,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.from_bytes,
 tacenta_session_unit.core.option.Option.Insts.CoreCmpPartialEqOption.eq]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleDecryptRunBounds.parkedSession_invariant

/--
info: 'Tacenta.UnitLifecycleDecryptRunBounds.parkedSession_not_counterHeadroom' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kem.EncapsState,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleDecryptRunBounds.parkedSession_not_counterHeadroom

/--
info: 'Tacenta.UnitLifecycleDecryptRunBounds.invariant_does_not_give_counterHeadroom' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kdf.hkdf_sha256,
 tacenta_session_unit.tacenta_kdf.hmac_sha256,
 tacenta_session_unit.tacenta_kem.CT1_LEN,
 tacenta_session_unit.tacenta_kem.CT2_LEN,
 tacenta_session_unit.tacenta_kem.EK_VECTOR_LEN,
 tacenta_session_unit.tacenta_kem.EncapsState,
 tacenta_session_unit.tacenta_kem.HEADER_LEN,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair,
 tacenta_session_unit.tacenta_kem.encapsulate1,
 tacenta_session_unit.tacenta_kem.encapsulate2,
 tacenta_session_unit.tacenta_kem.validate_ek,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.rand_core_1.error.Error,
 tacenta_session_unit.tacenta_boundary.aead.decrypt,
 tacenta_session_unit.tacenta_boundary.aead.encrypt,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_boundary.dh.is_prime_order_public,
 tacenta_session_unit.tacenta_boundary.kem.KeyPair,
 tacenta_session_unit.tacenta_boundary.kem.ciphertext_len,
 tacenta_session_unit.tacenta_boundary.kem.decapsulate,
 tacenta_session_unit.tacenta_boundary.kem.encapsulate,
 tacenta_session_unit.tacenta_boundary.xeddsa.verify,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.generate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.header,
 tacenta_session_unit.zeroize.Zeroizing.new,
 tacenta_session_unit.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.Pair.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.TupleABC.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.alloc.vec.Vec.capacity,
 tacenta_session_unit.alloc.vec.Vec.pop,
 tacenta_session_unit.alloc.vec.Vec.truncate,
 tacenta_session_unit.core.num.Usize.div_ceil,
 tacenta_session_unit.core.option.Option.as_mut,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.agree,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.from_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.public_key,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.to_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.from_bytes,
 tacenta_session_unit.zeroize.Zeroize.Blanket.zeroize,
 tacenta_session_unit.tacenta_kem.EncapsState.Insts.CoreCloneClone.clone,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 tacenta_session_unit.alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.core.option.Option.Insts.CoreCloneClone.clone,
 tacenta_session_unit.core.option.Option.Insts.CoreCmpPartialEqOption.eq,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes.eq,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleDecryptRunBounds.invariant_does_not_give_counterHeadroom

/--
info: @Tacenta.UnitLifecycleDecryptRunBounds.classicalMatch_of_inv : ∀ {s : tacenta_session_unit.tacenta_ratchet.State}
  {m : Model.State.State},
  Tacenta.SessionUnitT3.StateR s m →
    Tacenta.SessionUnitRatchetImportInv.Ratchet.Inv s →
      ∀ (mh : Model.State.Header), (List.filter (fun x => x.1 == mh.dh && x.2.1 == mh.n) m.skipped).length ≤ 1
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptRunBounds.classicalMatch_of_inv

/--
info: @Tacenta.UnitLifecycleDecryptRunBounds.sparseMatch_of_inv : ∀ {s : tacenta_session_unit.tacenta_spqr.State}
  {m : Model.SparseRatchet.State},
  Tacenta.SessionUnitSpqrT3.StateRefines s m →
    Tacenta.SessionUnitRatchetImportInv.Spqr.Inv s →
      ∀ (e n : ℕ), (List.filter (fun x => x.1 == e && x.2.1 == n) m.skipped).length ≤ 1
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptRunBounds.sparseMatch_of_inv

/--
info: @Tacenta.UnitLifecycleDecryptRunBounds.sparseCounters_transport : ∀ {s : tacenta_session_unit.tacenta_spqr.State}
  {m : Model.SparseRatchet.State},
  Tacenta.SessionUnitSpqrT3.StateRefines s m →
    (∀ p ∈ ↑s.chains,
        ∀ (ch : tacenta_session_unit.tacenta_spqr.Chain),
          p.2.send = some ch ∨ p.2.receive = some ch → ↑ch.n < Aeneas.Std.U64.max) →
      ∀ p ∈ m.chains,
        ∀ (ch : Model.SparseRatchet.Chain), p.2.send = some ch ∨ p.2.receive = some ch → ch.n < Aeneas.Std.U64.max
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptRunBounds.sparseCounters_transport

/--
info: Tacenta.UnitLifecycleDecryptRunBounds.store_room : ∀ L ≤ 2000,
  L + Model.State.maxSkippedStore ≤ Aeneas.Std.UScalar.cMax Aeneas.Std.UScalarTy.Usize
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptRunBounds.store_room

/--
info: @Tacenta.UnitLifecycleDecryptRunBounds.retryRunBounds_of_triple_invariant : ∀
  {t : tacenta_session_unit.tacenta_triple.State} {m : Model.Triple.State},
  t.invariant = Aeneas.Std.Result.ok true →
    Tacenta.SessionUnitTripleT3.StateRefines Tacenta.SessionUnitTripleT3.ratchetAbs Tacenta.SessionUnitTripleT3.spqrAbs
        t m →
      ↑t.classical.events + 1 < Aeneas.Std.U32.max →
        ↑t.post_quantum.epoch + 1 < Aeneas.Std.U64.max →
          (∀ p ∈ ↑t.post_quantum.chains,
              ∀ (ch : tacenta_session_unit.tacenta_spqr.Chain),
                p.2.send = some ch ∨ p.2.receive = some ch → ↑ch.n < Aeneas.Std.U64.max) →
            ∀ (header : Model.Triple.Header) (output : Option Model.SparseRatchet.Output),
              (∀ (o : Model.SparseRatchet.Output), output = some o → o.keyEpoch + 1 < Model.Braid.u64Max) →
                Tacenta.UnitLifecycleDecryptRatchetT3.RetryRunBounds m header output
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptRunBounds.retryRunBounds_of_triple_invariant

/--
info: Tacenta.UnitLifecycleDecryptRunBounds.sparseOutputOf_epoch : ∀ (K : Model.Braid.Kem) (st : Model.Braid.BraidState)
  (msg : Model.Braid.Msg) (o : Model.SparseRatchet.Output),
  Model.Lifecycle.sparseOutputOf (Model.Braid.receive K st msg).2.1 = some o → o.keyEpoch + 1 < Model.Braid.u64Max
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptRunBounds.sparseOutputOf_epoch

/--
info: @Tacenta.UnitLifecycleDecryptRunBounds.retryRunBounds_of_invariant : ∀ {dh : Tacenta.UnitLifecycleT3.DhView}
  {K : Model.Braid.Kem} {real : tacenta_session_unit.lifecycle.Session} {model : Model.Lifecycle.Session},
  real.invariant = Aeneas.Std.Result.ok true →
    Tacenta.UnitLifecycleT3.SessionRefines dh K real model →
      Tacenta.UnitLifecycleDecryptRunBounds.CounterHeadroom real →
        ∀ (header : Model.Triple.Header) (K' : Model.Braid.Kem) (st : Model.Braid.BraidState) (msg : Model.Braid.Msg),
          Tacenta.UnitLifecycleDecryptRatchetT3.RetryRunBounds model.triple header
            (Model.Lifecycle.sparseOutputOf (Model.Braid.receive K' st msg).2.1)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptRunBounds.retryRunBounds_of_invariant

/--
info: @Tacenta.UnitLifecycleDecryptRunBounds.decryptRatchetRun_of_invariant : ∀ {R : Type}
  {dh : Tacenta.UnitLifecycleT3.DhView} {view : Model.Lifecycle.CodewordView} {oracle : Model.Lifecycle.Oracle}
  {trace : R → List Model.Lifecycle.Key} {real : tacenta_session_unit.lifecycle.Session}
  {model : Model.Lifecycle.Session} {message : Aeneas.Std.Slice Aeneas.Std.U8} {rng : R},
  real.invariant = Aeneas.Std.Result.ok true →
    Tacenta.UnitLifecycleT3.SessionRefines dh oracle.braidKem real model →
      Tacenta.UnitLifecycleDecryptRunBounds.CounterHeadroom real →
        Tacenta.UnitLifecycleDecryptRunBounds.DecryptRatchetRunInputs view oracle trace real model message rng →
          Tacenta.UnitLifecycleDecryptRatchetT3.DecryptRatchetRun view oracle trace real model message rng
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptRunBounds.decryptRatchetRun_of_invariant

/--
info: @Tacenta.UnitLifecycleDecryptRunBounds.decrypt_ratchet_refines_of_invariant : ∀ {R : Type}
  (rngCore : tacenta_session_unit.rand_core_1.RngCore R) (cryptoRng : tacenta_session_unit.rand_core_1.CryptoRng R)
  (trace : R → List Model.Lifecycle.Key) (dh : Tacenta.UnitLifecycleT3.DhView) (view : Model.Lifecycle.CodewordView)
  (oracle : Model.Lifecycle.Oracle),
  Tacenta.UnitLifecycleDecryptRatchetT3.DecryptOracleOf rngCore cryptoRng dh trace oracle →
    Tacenta.UnitLifecycleT3.DhCodecOf dh →
      Tacenta.UnitLifecycleT1.DecryptRatchetContracts rngCore →
        ∀ [Tacenta.SessionUnitT1.DerivedKeysModel],
          Tacenta.UnitLifecycleDecryptRatchetT3.DecryptRatchetAgreements oracle.braidKem →
            ∀ (real : tacenta_session_unit.lifecycle.Session) (model : Model.Lifecycle.Session)
              (message : Aeneas.Std.Slice Aeneas.Std.U8) (rng : R),
              real.invariant = Aeneas.Std.Result.ok true →
                Tacenta.UnitLifecycleT3.SessionRefines dh oracle.braidKem real model →
                  Tacenta.UnitLifecycleDecryptRunBounds.CounterHeadroom real →
                    trace rng = oracle.draws →
                      Tacenta.UnitLifecycleDecryptRunBounds.DecryptRatchetRunInputs view oracle trace real model message
                          rng →
                        ∃ output,
                          tacenta_session_unit.lifecycle.Session.decrypt_ratchet rngCore cryptoRng real message rng =
                              Aeneas.Std.Result.ok output ∧
                            Tacenta.UnitLifecycleT3.StepRefines trace dh oracle.braidKem output
                              (Model.Lifecycle.decryptRatchet view oracle model
                                (Tacenta.UnitLifecycleT3.sliceOf message))
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptRunBounds.decrypt_ratchet_refines_of_invariant

/--
info: @Tacenta.UnitLifecycleDecryptRunBounds.decrypt_ratchet_refines_of_invariant_statement : Tacenta.UnitLifecycleDecryptRunBounds.DecryptRatchetRefinesOfInvariantStatement
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptRunBounds.decrypt_ratchet_refines_of_invariant_statement

/--
info: Tacenta.UnitLifecycleDecryptRunBounds.counterHeadroom_sessionOf : ∀
  (sk : tacenta_session_unit.tacenta_boundary.dh.PrivateKey)
  (our peer : tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes) (ad : Aeneas.Std.alloc.vec.Vec Aeneas.Std.U8)
  (dhs : Aeneas.Std.Array Aeneas.Std.U8 32#usize) (pending : Option tacenta_session_unit.lifecycle.PendingInitial),
  Tacenta.UnitLifecycleDecryptRunBounds.CounterHeadroom
    (Tacenta.UnitHeadroomSatisfiable.sessionOf sk our peer ad dhs pending)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptRunBounds.counterHeadroom_sessionOf

/--
info: Tacenta.UnitLifecycleDecryptRunBounds.decrypt_inputs_at_invReal : ∀ (K : Model.Braid.Kem)
  (dh : Tacenta.UnitLifecycleT3.DhView) (k : tacenta_session_unit.tacenta_boundary.dh.PrivateKey)
  (pkb : tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes) (ad : Aeneas.Std.alloc.vec.Vec Aeneas.Std.U8)
  (a : Aeneas.Std.Array Aeneas.Std.U8 32#usize) (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle),
  oracle.braidKem = K →
    Tacenta.UnitLifecycleDecryptRunBounds.DecryptRatchetRunInputs view oracle
      Tacenta.UnitLifecycleIntegrationScreen.byteTrace (Tacenta.UnitLifecycleDecryptScreen.invReal k pkb ad a)
      (Tacenta.UnitLifecycleDecryptRatchetScreen.modelOf dh (Tacenta.UnitLifecycleDecryptScreen.invReal k pkb ad a))
      Tacenta.UnitLifecycleDecryptRatchetScreen.sampleMessage Tacenta.UnitLifecycleDecryptRatchetScreen.sampleRng
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptRunBounds.decrypt_inputs_at_invReal

/--
info: @Tacenta.UnitLifecycleDecryptRunBounds.DecryptOfInvariantHypotheses.refines : ∀ {R : Type}
  {rngCore : tacenta_session_unit.rand_core_1.RngCore R} {cryptoRng : tacenta_session_unit.rand_core_1.CryptoRng R}
  {trace : R → List Model.Lifecycle.Key} {dh : Tacenta.UnitLifecycleT3.DhView} {view : Model.Lifecycle.CodewordView}
  {oracle : Model.Lifecycle.Oracle} {real : tacenta_session_unit.lifecycle.Session} {model : Model.Lifecycle.Session}
  {message : Aeneas.Std.Slice Aeneas.Std.U8} {rng : R},
  Tacenta.UnitLifecycleDecryptRunBounds.DecryptOfInvariantHypotheses rngCore cryptoRng trace dh view oracle real model
      message rng →
    ∃ output,
      tacenta_session_unit.lifecycle.Session.decrypt_ratchet rngCore cryptoRng real message rng =
          Aeneas.Std.Result.ok output ∧
        Tacenta.UnitLifecycleT3.StepRefines trace dh oracle.braidKem output
          (Model.Lifecycle.decryptRatchet view oracle model (Tacenta.UnitLifecycleT3.sliceOf message))
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptRunBounds.DecryptOfInvariantHypotheses.refines

/--
info: Tacenta.UnitLifecycleDecryptRunBounds.decrypt_of_invariant_hypotheses_jointly_satisfiable : ∀ (K : Model.Braid.Kem)
  (dh : Tacenta.UnitLifecycleT3.DhView),
  Tacenta.UnitLifecycleDecryptScreen.DecryptJointLaws K dh →
    ∃ oracle real model message rng,
      oracle.braidKem = K ∧
        Model.Lifecycle.messageType (Tacenta.UnitLifecycleT3.sliceOf message) =
            some Model.Lifecycle.MessageType.ratchet ∧
          ∀ (view : Model.Lifecycle.CodewordView),
            Tacenta.UnitLifecycleDecryptRunBounds.DecryptOfInvariantHypotheses
              Tacenta.UnitLifecycleIntegrationScreen.byteRng Tacenta.UnitLifecycleIntegrationScreen.byteCrc
              Tacenta.UnitLifecycleIntegrationScreen.byteTrace dh view oracle real model message rng
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptRunBounds.decrypt_of_invariant_hypotheses_jointly_satisfiable

/--
info: Tacenta.UnitLifecycleDecryptRunBounds.parkedTriple_invariant : ∀ (a : Aeneas.Std.Array Aeneas.Std.U8 32#usize),
  Tacenta.SessionUnitT1.canonicalX25519 a = true →
    (Tacenta.UnitLifecycleDecryptRunBounds.parkedTriple a).invariant = Aeneas.Std.Result.ok true
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptRunBounds.parkedTriple_invariant

/--
info: Tacenta.UnitLifecycleDecryptRunBounds.structural_parkedSession : ∀
  (k : tacenta_session_unit.tacenta_boundary.dh.PrivateKey)
  (pkb : tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes) (a : Aeneas.Std.Array Aeneas.Std.U8 32#usize),
  k.public_key = Aeneas.Std.Result.ok pkb →
    pkb.as_bytes = Aeneas.Std.Result.ok a →
      Tacenta.SessionUnitT1.canonicalX25519 a = true →
        tacenta_session_unit.tacenta_boundary.dh.is_prime_order_public pkb = Aeneas.Std.Result.ok true →
          Tacenta.UnitHeadroomInvariant.OptionEqU64Shape
              @tacenta_session_unit.core.option.Option.Insts.CoreCmpPartialEqOption.eq →
            ∀ (ad : Aeneas.Std.alloc.vec.Vec Aeneas.Std.U8),
              tacenta_session_unit.lifecycle.identity_ad pkb pkb = Aeneas.Std.Result.ok ad →
                (Tacenta.UnitLifecycleDecryptRunBounds.parkedSession k pkb ad a).structural_invariant =
                  Aeneas.Std.Result.ok true
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptRunBounds.structural_parkedSession

/--
info: Tacenta.UnitLifecycleDecryptRunBounds.parkedSession_invariant : ∀
  (k : tacenta_session_unit.tacenta_boundary.dh.PrivateKey)
  (pkb : tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes) (a : Aeneas.Std.Array Aeneas.Std.U8 32#usize),
  k.public_key = Aeneas.Std.Result.ok pkb →
    pkb.as_bytes = Aeneas.Std.Result.ok a →
      Tacenta.SessionUnitT1.canonicalX25519 a = true →
        tacenta_session_unit.tacenta_boundary.dh.is_prime_order_public pkb = Aeneas.Std.Result.ok true →
          Tacenta.UnitHeadroomInvariant.OptionEqU64Shape
              @tacenta_session_unit.core.option.Option.Insts.CoreCmpPartialEqOption.eq →
            ∀ (ad : Aeneas.Std.alloc.vec.Vec Aeneas.Std.U8),
              tacenta_session_unit.lifecycle.identity_ad pkb pkb = Aeneas.Std.Result.ok ad →
                (Tacenta.UnitLifecycleDecryptRunBounds.parkedSession k pkb ad a).invariant = Aeneas.Std.Result.ok true
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptRunBounds.parkedSession_invariant

/--
info: Tacenta.UnitLifecycleDecryptRunBounds.parkedSession_not_counterHeadroom : ∀
  (k : tacenta_session_unit.tacenta_boundary.dh.PrivateKey)
  (pkb : tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes) (ad : Aeneas.Std.alloc.vec.Vec Aeneas.Std.U8)
  (a : Aeneas.Std.Array Aeneas.Std.U8 32#usize),
  ¬Tacenta.UnitLifecycleDecryptRunBounds.CounterHeadroom
      (Tacenta.UnitLifecycleDecryptRunBounds.parkedSession k pkb ad a)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptRunBounds.parkedSession_not_counterHeadroom

/--
info: Tacenta.UnitLifecycleDecryptRunBounds.invariant_does_not_give_counterHeadroom : Tacenta.UnitHeadroomInvariant.ValidKeyShape
    Tacenta.UnitSatisfiabilityJoint.Interp.real →
  Tacenta.UnitHeadroomInvariant.OptionEqU64Shape
      @tacenta_session_unit.core.option.Option.Insts.CoreCmpPartialEqOption.eq →
    Tacenta.UnitLifecycleT1.DhCodecTotal →
      ∃ real,
        real.invariant = Aeneas.Std.Result.ok true ∧
          ↑real.triple.classical.events = 4294967294 ∧ ¬Tacenta.UnitLifecycleDecryptRunBounds.CounterHeadroom real
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptRunBounds.invariant_does_not_give_counterHeadroom

/--
info: structure Tacenta.UnitLifecycleDecryptRunBounds.CounterHeadroom (real : tacenta_session_unit.lifecycle.Session) : Prop
number of parameters: 1
fields:
  Tacenta.UnitLifecycleDecryptRunBounds.CounterHeadroom.classicalEvents : ↑real.triple.classical.events + 1 <
      Aeneas.Std.U32.max
  Tacenta.UnitLifecycleDecryptRunBounds.CounterHeadroom.sparseEpoch : ↑real.triple.post_quantum.epoch + 1 <
      Aeneas.Std.U64.max
  Tacenta.UnitLifecycleDecryptRunBounds.CounterHeadroom.sparseCounters : ∀ p ∈ ↑real.triple.post_quantum.chains,
      ∀ (ch : tacenta_session_unit.tacenta_spqr.Chain),
        p.2.send = some ch ∨ p.2.receive = some ch → ↑ch.n < Aeneas.Std.U64.max
  Tacenta.UnitLifecycleDecryptRunBounds.CounterHeadroom.braidEpoch : ↑(Tacenta.SessionUnitBraidT1.State.epoch_val
            real.braid.state) +
        1 <
      Aeneas.Std.U64.max
constructor:
  Tacenta.UnitLifecycleDecryptRunBounds.CounterHeadroom.mk {real : tacenta_session_unit.lifecycle.Session}
    (classicalEvents : ↑real.triple.classical.events + 1 < Aeneas.Std.U32.max)
    (sparseEpoch : ↑real.triple.post_quantum.epoch + 1 < Aeneas.Std.U64.max)
    (sparseCounters :
      ∀ p ∈ ↑real.triple.post_quantum.chains,
        ∀ (ch : tacenta_session_unit.tacenta_spqr.Chain),
          p.2.send = some ch ∨ p.2.receive = some ch → ↑ch.n < Aeneas.Std.U64.max)
    (braidEpoch : ↑(Tacenta.SessionUnitBraidT1.State.epoch_val real.braid.state) + 1 < Aeneas.Std.U64.max) :
    Tacenta.UnitLifecycleDecryptRunBounds.CounterHeadroom real
-/
#guard_msgs in
#print Tacenta.UnitLifecycleDecryptRunBounds.CounterHeadroom

/--
info: structure Tacenta.UnitLifecycleDecryptRunBounds.DecryptRatchetRunInputs {R : Type} (view : Model.Lifecycle.CodewordView)
  (oracle : Model.Lifecycle.Oracle) (trace : R → List Model.Lifecycle.Key)
  (real : tacenta_session_unit.lifecycle.Session) (model : Model.Lifecycle.Session)
  (message : Aeneas.Std.Slice Aeneas.Std.U8) (rng : R) : Prop
number of parameters: 8
fields:
  Tacenta.UnitLifecycleDecryptRunBounds.DecryptRatchetRunInputs.chunk : ∀
      (realComposite : tacenta_session_unit.tacenta_wire.Composite) (modelComposite : Model.CompositeHeader.Composite)
      (ciphertext : Tacenta.UnitLifecycleT3.Bytes),
      Model.CompositeHeader.decodeDetailed (Tacenta.UnitLifecycleT3.sliceOf message) =
          Except.ok (modelComposite, ciphertext) →
        Tacenta.UnitLifecycleT3.CompositeRefines realComposite modelComposite →
          Tacenta.UnitLifecycleT3.IncomingChunkRefines view model.braid realComposite modelComposite
  Tacenta.UnitLifecycleDecryptRunBounds.DecryptRatchetRunInputs.honest : ∀
      (modelComposite : Model.CompositeHeader.Composite) (ciphertext : Tacenta.UnitLifecycleT3.Bytes),
      Model.CompositeHeader.decodeDetailed (Tacenta.UnitLifecycleT3.sliceOf message) =
          Except.ok (modelComposite, ciphertext) →
        Tacenta.SessionUnitBraidT3.HonestChunk model.braid
          (Model.Lifecycle.braidMessageOf view model.braid modelComposite)
  Tacenta.UnitLifecycleDecryptRunBounds.DecryptRatchetRunInputs.draw : ∃ draw rest, trace rng = draw :: rest
constructor:
  Tacenta.UnitLifecycleDecryptRunBounds.DecryptRatchetRunInputs.mk {R : Type} {view : Model.Lifecycle.CodewordView}
    {oracle : Model.Lifecycle.Oracle} {trace : R → List Model.Lifecycle.Key}
    {real : tacenta_session_unit.lifecycle.Session} {model : Model.Lifecycle.Session}
    {message : Aeneas.Std.Slice Aeneas.Std.U8} {rng : R}
    (chunk :
      ∀ (realComposite : tacenta_session_unit.tacenta_wire.Composite) (modelComposite : Model.CompositeHeader.Composite)
        (ciphertext : Tacenta.UnitLifecycleT3.Bytes),
        Model.CompositeHeader.decodeDetailed (Tacenta.UnitLifecycleT3.sliceOf message) =
            Except.ok (modelComposite, ciphertext) →
          Tacenta.UnitLifecycleT3.CompositeRefines realComposite modelComposite →
            Tacenta.UnitLifecycleT3.IncomingChunkRefines view model.braid realComposite modelComposite)
    (honest :
      ∀ (modelComposite : Model.CompositeHeader.Composite) (ciphertext : Tacenta.UnitLifecycleT3.Bytes),
        Model.CompositeHeader.decodeDetailed (Tacenta.UnitLifecycleT3.sliceOf message) =
            Except.ok (modelComposite, ciphertext) →
          Tacenta.SessionUnitBraidT3.HonestChunk model.braid
            (Model.Lifecycle.braidMessageOf view model.braid modelComposite))
    (draw : ∃ draw rest, trace rng = draw :: rest) :
    Tacenta.UnitLifecycleDecryptRunBounds.DecryptRatchetRunInputs view oracle trace real model message rng
-/
#guard_msgs in
#print Tacenta.UnitLifecycleDecryptRunBounds.DecryptRatchetRunInputs

/--
info: def Tacenta.UnitLifecycleDecryptRunBounds.DecryptRatchetRefinesOfInvariantStatement : Prop :=
∀ {R : Type} (rngCore : tacenta_session_unit.rand_core_1.RngCore R)
  (cryptoRng : tacenta_session_unit.rand_core_1.CryptoRng R) (trace : R → List Model.Lifecycle.Key)
  (dh : Tacenta.UnitLifecycleT3.DhView) (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle),
  Tacenta.UnitLifecycleDecryptRatchetT3.DecryptOracleOf rngCore cryptoRng dh trace oracle →
    Tacenta.UnitLifecycleT3.DhCodecOf dh →
      Tacenta.UnitLifecycleT1.DecryptRatchetContracts rngCore →
        ∀ [Tacenta.SessionUnitT1.DerivedKeysModel],
          Tacenta.UnitLifecycleDecryptRatchetT3.DecryptRatchetAgreements oracle.braidKem →
            ∀ (real : tacenta_session_unit.lifecycle.Session) (model : Model.Lifecycle.Session)
              (message : Aeneas.Std.Slice Aeneas.Std.U8) (rng : R),
              real.invariant = Aeneas.Std.Result.ok true →
                Tacenta.UnitLifecycleT3.SessionRefines dh oracle.braidKem real model →
                  Tacenta.UnitLifecycleDecryptRunBounds.CounterHeadroom real →
                    trace rng = oracle.draws →
                      Tacenta.UnitLifecycleDecryptRunBounds.DecryptRatchetRunInputs view oracle trace real model message
                          rng →
                        ∃ output,
                          tacenta_session_unit.lifecycle.Session.decrypt_ratchet rngCore cryptoRng real message rng =
                              Aeneas.Std.Result.ok output ∧
                            Tacenta.UnitLifecycleT3.StepRefines trace dh oracle.braidKem output
                              (Model.Lifecycle.decryptRatchet view oracle model
                                (Tacenta.UnitLifecycleT3.sliceOf message))
-/
#guard_msgs in
#print Tacenta.UnitLifecycleDecryptRunBounds.DecryptRatchetRefinesOfInvariantStatement

/--
info: structure Tacenta.UnitLifecycleDecryptRunBounds.DecryptOfInvariantHypotheses {R : Type}
  (rngCore : tacenta_session_unit.rand_core_1.RngCore R) (cryptoRng : tacenta_session_unit.rand_core_1.CryptoRng R)
  (trace : R → List Model.Lifecycle.Key) (dh : Tacenta.UnitLifecycleT3.DhView) (view : Model.Lifecycle.CodewordView)
  (oracle : Model.Lifecycle.Oracle) (real : tacenta_session_unit.lifecycle.Session) (model : Model.Lifecycle.Session)
  (message : Aeneas.Std.Slice Aeneas.Std.U8) (rng : R) : Prop
number of parameters: 11
fields:
  Tacenta.UnitLifecycleDecryptRunBounds.DecryptOfInvariantHypotheses.oracleOf : Tacenta.UnitLifecycleDecryptRatchetT3.DecryptOracleOf
      rngCore cryptoRng dh trace oracle
  Tacenta.UnitLifecycleDecryptRunBounds.DecryptOfInvariantHypotheses.codec : Tacenta.UnitLifecycleT3.DhCodecOf dh
  Tacenta.UnitLifecycleDecryptRunBounds.DecryptOfInvariantHypotheses.contracts : Tacenta.UnitLifecycleT1.DecryptRatchetContracts
      rngCore
  Tacenta.UnitLifecycleDecryptRunBounds.DecryptOfInvariantHypotheses.derivedKeys : Nonempty
      Tacenta.SessionUnitT1.DerivedKeysModel
  Tacenta.UnitLifecycleDecryptRunBounds.DecryptOfInvariantHypotheses.agreements : Tacenta.UnitLifecycleDecryptRatchetT3.DecryptRatchetAgreements
      oracle.braidKem
  Tacenta.UnitLifecycleDecryptRunBounds.DecryptOfInvariantHypotheses.invariant : real.invariant =
      Aeneas.Std.Result.ok true
  Tacenta.UnitLifecycleDecryptRunBounds.DecryptOfInvariantHypotheses.related : Tacenta.UnitLifecycleT3.SessionRefines dh
      oracle.braidKem real model
  Tacenta.UnitLifecycleDecryptRunBounds.DecryptOfInvariantHypotheses.counters : Tacenta.UnitLifecycleDecryptRunBounds.CounterHeadroom
      real
  Tacenta.UnitLifecycleDecryptRunBounds.DecryptOfInvariantHypotheses.trace_eq : trace rng = oracle.draws
  Tacenta.UnitLifecycleDecryptRunBounds.DecryptOfInvariantHypotheses.inputs : Tacenta.UnitLifecycleDecryptRunBounds.DecryptRatchetRunInputs
      view oracle trace real model message rng
constructor:
  Tacenta.UnitLifecycleDecryptRunBounds.DecryptOfInvariantHypotheses.mk {R : Type}
    {rngCore : tacenta_session_unit.rand_core_1.RngCore R} {cryptoRng : tacenta_session_unit.rand_core_1.CryptoRng R}
    {trace : R → List Model.Lifecycle.Key} {dh : Tacenta.UnitLifecycleT3.DhView} {view : Model.Lifecycle.CodewordView}
    {oracle : Model.Lifecycle.Oracle} {real : tacenta_session_unit.lifecycle.Session} {model : Model.Lifecycle.Session}
    {message : Aeneas.Std.Slice Aeneas.Std.U8} {rng : R}
    (oracleOf : Tacenta.UnitLifecycleDecryptRatchetT3.DecryptOracleOf rngCore cryptoRng dh trace oracle)
    (codec : Tacenta.UnitLifecycleT3.DhCodecOf dh) (contracts : Tacenta.UnitLifecycleT1.DecryptRatchetContracts rngCore)
    (derivedKeys : Nonempty Tacenta.SessionUnitT1.DerivedKeysModel)
    (agreements : Tacenta.UnitLifecycleDecryptRatchetT3.DecryptRatchetAgreements oracle.braidKem)
    (invariant : real.invariant = Aeneas.Std.Result.ok true)
    (related : Tacenta.UnitLifecycleT3.SessionRefines dh oracle.braidKem real model)
    (counters : Tacenta.UnitLifecycleDecryptRunBounds.CounterHeadroom real) (trace_eq : trace rng = oracle.draws)
    (inputs : Tacenta.UnitLifecycleDecryptRunBounds.DecryptRatchetRunInputs view oracle trace real model message rng) :
    Tacenta.UnitLifecycleDecryptRunBounds.DecryptOfInvariantHypotheses rngCore cryptoRng trace dh view oracle real model
      message rng
-/
#guard_msgs in
#print Tacenta.UnitLifecycleDecryptRunBounds.DecryptOfInvariantHypotheses

/--
info: def Tacenta.UnitLifecycleDecryptRunBounds.parkedTriple : Aeneas.Std.Array Aeneas.Std.U8 32#usize →
  tacenta_session_unit.tacenta_triple.State :=
fun dhs =>
  have __src := Tacenta.UnitHeadroomSatisfiable.freshTriple dhs;
  {
    classical :=
      have __src := (Tacenta.UnitHeadroomSatisfiable.freshTriple dhs).classical;
      { dhs_pub := __src.dhs_pub, dhr_pub := __src.dhr_pub, rk := __src.rk, cks := __src.cks, ckr := __src.ckr,
        ns := __src.ns, nr := __src.nr, pn := __src.pn, skipped := __src.skipped, events := 4294967294#u32,
        labels := __src.labels },
    post_quantum := __src.post_quantum }
-/
#guard_msgs in
#print Tacenta.UnitLifecycleDecryptRunBounds.parkedTriple

/--
info: def Tacenta.UnitLifecycleDecryptRunBounds.parkedSession : tacenta_session_unit.tacenta_boundary.dh.PrivateKey →
  tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes →
    Aeneas.Std.alloc.vec.Vec Aeneas.Std.U8 →
      Aeneas.Std.Array Aeneas.Std.U8 32#usize → tacenta_session_unit.lifecycle.Session :=
fun k pkb ad a =>
  have __src := Tacenta.UnitHeadroomSatisfiable.sessionOf k pkb pkb ad a none;
  { triple := Tacenta.UnitLifecycleDecryptRunBounds.parkedTriple a, braid := __src.braid,
    ratchet_private := __src.ratchet_private, identity_ad := __src.identity_ad,
    our_identity_public := __src.our_identity_public, peer_identity_public := __src.peer_identity_public,
    pending_initial := __src.pending_initial, established_ephemeral := __src.established_ephemeral }
-/
#guard_msgs in
#print Tacenta.UnitLifecycleDecryptRunBounds.parkedSession
