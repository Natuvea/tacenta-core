import Translation.UnitLifecycleInitialDispatch

/-!
# Restated dispatch records, and when the restated fields can be met

Three records the lifecycle T3 and dispatch layer takes ask more than a run can supply, on the
reading given for each below, so the theorems that take them are not claims. Each is restated
here under a new name, with the consumers switched to it and the old definition kept unchanged.

* `CodewordViewOf` carries a `receive` clause that asks a view to name one source for each wire
  chunk. No consumer uses it: the encrypt-side theorems use only `send`. `CodewordViewSendOf`
  (`UnitLifecycleT3.lean`) is the send direction alone, and `codewordViewSendOf_satisfiable` shows
  that some view meets it. The witness is chosen classically and assumes nothing about any opaque
  operation: the translated encoder is a function, so two codewords of one source at one index are
  equal. The result holds for any deterministic encoder; it shows that the clause is consistent and
  says nothing about a property of the shipped one.
* `InitialRatchetBraidEvidenceContracts` asked, for every composite, that its chunk be a codeword of
  the one source a decoder's held chunks carry. It already carried the message it is about; the
  scoped record asks it of the one composite that message decodes to.
  `scoped_chunk_fields_iff_consistent` says when a view meeting the two scoped fields exists: the
  received chunk is a codeword of one source, and that source fits the decoder the chunk is fed to.
  That is a normalisation of the left side, specialised to a view that names the source: it is
  stated of a Braid state, a wire composite and a model composite, and neither the record nor the
  message nor `decodeDetailed` appears in it. A well-formed chunk from a dishonest sender meets it
  as well as an honest one does.
* `InitialRatchetTripleConcreteEvidence` and `InitialRatchetAeadConcreteEvidence` carried two fields
  quantified over every draw. Both are dropped: the consumers hold the run's own model refusal as a
  premise, and the public-key equation is the theorem `candidate_public_eq_draw` of
  `UnitLifecycleT3.lean`, from the oracle's `random32` and `dhPublic` clauses and the key codec.

What this does not show. That the other hypotheses of the dispatch theorems are met: `OracleOf`'s
KEM success clause is not shown to hold of the shipped `encapsulate`, the same-ephemeral evidence
records are not shown satisfiable, and the Braid agreements are the hypothesis screen H1's to
decide. That `InitialRatchetConcreteBranchEvidence`, which asks the scoped Braid record of every
inner message that reaches a refusal, is satisfiable. It is read as unsatisfiable at states whose
decoder holds a chunk, because an inconsistent message can reach a refusal (`decrypt_ratchet`
checks nothing about the agreement chunk before the AEAD tag) and cannot meet both
`IncomingChunkRefines` and `HonestChunk`; `scoped_record_gives_consistent` is the formal handle,
and no Lean statement says more because no `Session` value can be built in the tree. The theorems
that take these records are not claims.

A view that meets the send clause and the scoped chunk fields of one consistent run together
exists (`send_and_scoped_chunk_fields_joint`), because the two constrain different fields of a
`CodewordView`. Whether one view meets the scoped fields for every inner message is the
consumer-structure item above.
-/

namespace Tacenta.UnitLifecycleRepair

open Aeneas Aeneas.Std Result
open tacenta_session_unit
open Tacenta.UnitLifecycleT3

abbrev BCodewordOf := Tacenta.SessionUnitBraidT3.CodewordOf
abbrev BNthChunk := Tacenta.SessionUnitBraidT3.NthChunk

/-! ## The codeword view -/

theorem u8_inj {a b : Std.U8}
    (h : Tacenta.SessionUnitBraidT3.u8 a = Tacenta.SessionUnitBraidT3.u8 b) : a = b := by
  have ha : a.val < 256 := by scalar_tac
  have hb : b.val < 256 := by scalar_tac
  unfold Tacenta.SessionUnitBraidT3.u8 at h
  have h' := congrArg UInt8.toNat h
  rw [UInt8.toNat_ofNat', UInt8.toNat_ofNat'] at h'
  apply UScalar.eq_of_val_eq
  omega

theorem sliceOf_inj {s1 s2 : Slice Std.U8}
    (h : Tacenta.SessionUnitBraidT3.sliceOf s1 = Tacenta.SessionUnitBraidT3.sliceOf s2) :
    s1 = s2 := by
  unfold Tacenta.SessionUnitBraidT3.sliceOf at h
  have hl : s1.val = s2.val :=
    (List.map_injective_iff.mpr (fun a b hab => u8_inj hab)) h
  exact Subtype.ext hl

/-- `NthChunk` is functional in the chunk, for a fixed starting encoder. -/
theorem nthChunk_functional :
    ∀ (n : Nat) (enc : tacenta_erasure.Encoder) (c1 c2 : tacenta_erasure.Chunk),
      BNthChunk n enc c1 → BNthChunk n enc c2 → c1 = c2 := by
  intro n
  induction n with
  | zero =>
    intro enc c1 c2 h1 h2
    obtain ⟨e1, h1⟩ := h1
    obtain ⟨e2, h2⟩ := h2
    rw [h1] at h2
    have := Result.ok.inj h2
    have := (Prod.mk.inj this).1
    exact (Option.some.inj this)
  | succ n ih =>
    intro enc c1 c2 h1 h2
    obtain ⟨c, e1, hc1, h1⟩ := h1
    obtain ⟨c', e2, hc2, h2⟩ := h2
    rw [hc1] at hc2
    have hh := Result.ok.inj hc2
    have hpair := Prod.mk.inj hh
    have hcc : c = c' := Option.some.inj hpair.1
    have hee : e1 = e2 := hpair.2
    subst hcc; subst hee
    exact ih e1 c1 c2 h1 h2

/-- For a fixed source and index the codeword is unique: the translated encoder is a function. -/
theorem codewordOf_functional (m : List UInt8) (c1 c2 : tacenta_erasure.Chunk)
    (h1 : BCodewordOf m c1) (h2 : BCodewordOf m c2) (hi : c1.index.val = c2.index.val) :
    c1 = c2 := by
  obtain ⟨s1, e1, hs1, hn1, hth1⟩ := h1
  obtain ⟨s2, e2, hs2, hn2, hth2⟩ := h2
  have hs : s1 = s2 := sliceOf_inj (hs1.trans hs2.symm)
  subst hs
  rw [hn1] at hn2
  have he : e1 = e2 := Result.ok.inj hn2
  subst he
  rw [← hi] at hth2
  exact nthChunk_functional _ _ _ _ hth1 hth2

open Classical in
/-- A view that sends a model chunk as the wire codeword of the chunk the encoder emits for that
source and index, when there is one. -/
noncomputable def witnessView : Model.Lifecycle.CodewordView where
  receive := fun _ idx _ => { source := [], index := idx.toNat }
  send := fun _ mc =>
    if h : ∃ chunk, BCodewordOf mc.source chunk ∧ chunk.index.val = mc.index then
      modelCodewordOf (Classical.choose h)
    else { index := 0, data := [] }

theorem witnessView_send : CodewordViewSendOf witnessView := by
  refine ⟨fun state source chunk hc => ?_⟩
  have h : ∃ c, BCodewordOf (modelChunkOf source chunk).source c ∧
      c.index.val = (modelChunkOf source chunk).index := ⟨chunk, hc, rfl⟩
  simp only [witnessView, dif_pos h]
  have hspec := Classical.choose_spec h
  have heq := codewordOf_functional source _ _ hspec.1 hc hspec.2
  rw [heq]

/-- A view meets the send direction of the codeword relation. The old two-sided statement is false
(`CodewordViewOf`, `UnitLifecycleT3.lean`); the encrypt-side theorems use only this direction. -/
theorem codewordViewSendOf_satisfiable : ∃ view, CodewordViewSendOf view :=
  ⟨witnessView, witnessView_send⟩

/-! ## The scoped chunk fields -/

/-- A view that names one source for every incoming chunk. -/
def constView (source : List UInt8) : Model.Lifecycle.CodewordView where
  receive := fun _ idx _ => { source := source, index := idx.toNat }
  send := fun _ _ => { index := 0, data := [] }

/-- A run is consistent when the one chunk it receives is a codeword of one source and that source
fits the decoder the chunk is fed to (`HonestChunk` says which decoder, and when). A chunk from a
dishonest sender that is well formed is consistent in this sense; the name says nothing about the
sender. -/
def ConsistentChunkRun (st : Model.Braid.BraidState) (real : tacenta_wire.Composite)
    (model : Model.CompositeHeader.Composite) : Prop :=
  ∃ source,
    (match real.ag_chunk with
      | none => True
      | some chunk => BCodewordOf source { index := chunk.index, data := chunk.data }) ∧
    Tacenta.SessionUnitBraidT3.HonestChunk st
      (Model.Lifecycle.braidMessageOf (constView source) st model)

/-- The two chunk fields of the scoped Braid evidence record, as a statement about a Braid state, a
wire composite and a model composite, are met by some view exactly when the run is consistent. It
is a normalisation lemma: the right side is the left side specialised to `constView`. -/
theorem scoped_chunk_fields_iff_consistent
    (st : Model.Braid.BraidState) (real : tacenta_wire.Composite)
    (model : Model.CompositeHeader.Composite) (hcomp : CompositeRefines real model) :
    (∃ view, IncomingChunkRefines view st real model ∧
      Tacenta.SessionUnitBraidT3.HonestChunk st (Model.Lifecycle.braidMessageOf view st model)) ↔
    ConsistentChunkRun st real model := by
  have hagChunk := hcomp.agChunk
  constructor
  · rintro ⟨view, hinc, hhonest⟩
    unfold IncomingChunkRefines at hinc
    cases hr : real.ag_chunk with
    | none =>
        cases hm : model.agChunk with
        | none =>
            refine ⟨[], by simp [hr], ?_⟩
            intro mc hmc
            simp [Model.Lifecycle.braidMessageOf, hm] at hmc
        | some mc => simp [hr, hm] at hagChunk
    | some rc =>
        cases hm : model.agChunk with
        | none => simp [hr, hm] at hagChunk
        | some mc =>
            rw [hr, hm] at hinc
            obtain ⟨source, hcode, hrecv⟩ := hinc
            refine ⟨source, by simpa [hr] using hcode, ?_⟩
            have hw : WireCodewordRefines rc mc := by simpa [hr, hm] using hagChunk
            have hidx : rc.index.val = mc.index.toNat := hw.1
            have hmsg : Model.Lifecycle.braidMessageOf (constView source) st model =
                Model.Lifecycle.braidMessageOf view st model := by
              simp only [Model.Lifecycle.braidMessageOf, hm, Option.map_some, constView, hrecv,
                modelChunkOf, hidx]
            rw [hmsg]
            exact hhonest
  · rintro ⟨source, hcode, hhonest⟩
    refine ⟨constView source, ?_, hhonest⟩
    unfold IncomingChunkRefines
    cases hr : real.ag_chunk with
    | none =>
        cases hm : model.agChunk with
        | none => trivial
        | some mc => simp [hr, hm] at hagChunk
    | some rc =>
        cases hm : model.agChunk with
        | none => simp [hr, hm] at hagChunk
        | some mc =>
            refine ⟨source, by simpa [hr] using hcode, ?_⟩
            have hw : WireCodewordRefines rc mc := by simpa [hr, hm] using hagChunk
            have hidx : rc.index.val = mc.index.toNat := hw.1
            simp [constView, modelChunkOf, hidx]

/-! ## The send clause and the scoped fields together, and what the record gives

These two results carry no axiom pin and are not on `REQUIRED_PINS`. -/

/-- A view that meets the send clause and the scoped chunk fields of one consistent run exists,
because the two constrain different fields of a `CodewordView`: the send clause mentions only
`view.send`, and the chunk fields only `view.receive`. -/
theorem send_and_scoped_chunk_fields_joint (st : Model.Braid.BraidState)
    (real : tacenta_wire.Composite) (model : Model.CompositeHeader.Composite)
    (hcomp : CompositeRefines real model) (h : ConsistentChunkRun st real model) :
    ∃ view, CodewordViewSendOf view ∧ IncomingChunkRefines view st real model ∧
      Tacenta.SessionUnitBraidT3.HonestChunk st (Model.Lifecycle.braidMessageOf view st model) := by
  obtain ⟨view, hinc, hhon⟩ := (scoped_chunk_fields_iff_consistent st real model hcomp).mpr h
  refine ⟨{ receive := view.receive, send := witnessView.send }, ⟨witnessView_send.send⟩, ?_, ?_⟩
  · unfold IncomingChunkRefines at hinc ⊢; exact hinc
  · exact hhon

/-- From the scoped record, a message that decodes to a composite related to the wire composite
gives a consistent run. So the consumer structure `InitialRatchetConcreteBranchEvidence`, which asks
the record of every inner message that reaches a refusal, is satisfiable only if every such message
that decodes in that way is a consistent run. -/
theorem scoped_record_gives_consistent {K : Model.Braid.Kem}
    {view : Model.Lifecycle.CodewordView} {real : lifecycle.Session}
    {model : Model.Lifecycle.Session} {message : Slice Std.U8}
    (r : InitialRatchetBraidEvidenceContractsScoped (K := K) view real model message)
    (realC : tacenta_wire.Composite) (modelC : Model.CompositeHeader.Composite) (ct : Bytes)
    (hdec : Model.CompositeHeader.decodeDetailed (sliceOf message) = .ok (modelC, ct))
    (hc : CompositeRefines realC modelC) :
    ConsistentChunkRun model.braid realC modelC :=
  (scoped_chunk_fields_iff_consistent model.braid realC modelC hc).mp
    ⟨view, r.hchunk realC modelC ct hdec hc, r.hhonest modelC ct hdec⟩

end Tacenta.UnitLifecycleRepair

/--
info: 'Tacenta.UnitLifecycleRepair.codewordViewSendOf_satisfiable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.core.num.Usize.div_ceil]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleRepair.codewordViewSendOf_satisfiable

/--
info: 'Tacenta.UnitLifecycleRepair.scoped_chunk_fields_iff_consistent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.core.num.Usize.div_ceil]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleRepair.scoped_chunk_fields_iff_consistent

/-! ## Statement pins

The axiom pins above hold the constants a result depends on and not what it says. These hold the
statements of the two results. -/

/--
info: Tacenta.UnitLifecycleRepair.codewordViewSendOf_satisfiable : ∃ view, Tacenta.UnitLifecycleT3.CodewordViewSendOf view
-/
#guard_msgs in
#check Tacenta.UnitLifecycleRepair.codewordViewSendOf_satisfiable

/--
info: Tacenta.UnitLifecycleRepair.scoped_chunk_fields_iff_consistent (st : Model.Braid.BraidState)
  (real : tacenta_session_unit.tacenta_wire.Composite) (model : Model.CompositeHeader.Composite)
  (hcomp : Tacenta.UnitLifecycleT3.CompositeRefines real model) :
  (∃ view,
      Tacenta.UnitLifecycleT3.IncomingChunkRefines view st real model ∧
        Tacenta.SessionUnitBraidT3.HonestChunk st (Model.Lifecycle.braidMessageOf view st model)) ↔
    Tacenta.UnitLifecycleRepair.ConsistentChunkRun st real model
-/
#guard_msgs in
#check Tacenta.UnitLifecycleRepair.scoped_chunk_fields_iff_consistent
