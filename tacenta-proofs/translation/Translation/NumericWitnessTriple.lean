import Translation.UnitT1
import Translation.UnitT3
import Translation.UnitSpqrT1
import Translation.UnitSpqrT3
import Translation.UnitTripleT1
import Translation.UnitTripleT3

/-!
# The numeric premises of the central theorems hold together at a concrete state: the three-leaf unit

Theorems covered: the receive and send panic-freedom and refinement theorems on the unit that compiles
the classical ratchet, the sparse ratchet and the Triple Ratchet as one crate, including the Triple's
two discharged refinements. The unit has no decoder-invariant module, so the states here are shown
to relate to the model and to meet the premises, and nothing is said about the decoder.

For each theorem `T` below, `Premises.T` is the statement that one choice of `T`'s data satisfies
every premise of `T` that is numeric (a bound on a length, a counter or an epoch, written against
`Usize.max`, `U32.max` or `U64.max`), every numeric predicate about a state (`ct1_bounded`,
`EncodersLive`, ...) and every relation between a translated value and a model value
(`StateRefines`, `StateR`, `HeaderR`) at the same time. `sat_T` proves it at a concrete state. A
theorem whose premises no state meets is true and says nothing; this is the check that these are not
that.

* The statement is checked against the theorem and not trusted. `tacenta-proofs/scripts/check-precondition-witnesses.sh` reads
  `T`'s type from the built environment, builds the conjunction of the premises its table puts inside
  the witness, and requires `Premises.T` to equal it. It also requires every other premise of `T` to be
  classified in the table, as `boundary` or as `unwitnessed`, so a premise added to `T` later is not
  silently outside the witness, and it requires `sat_T` to prove exactly `Premises.T`. The check is a
  script and not part of this module because `check-lean-constructs.sh` refuses elaboration-time code
  in this package.
* Both platform widths. `Usize.max` is `2^System.Platform.numBits - 1` and Lean knows only that
  `numBits` is 32 or 64. Every proof here is about the constant, so it holds at both widths and none
  appeals to a width. The ceilings are discussed in `NumericBoundary.lean`.
* The states are small, not extremal: one chain and one skipped key, one stored skipped key, a counter
  at 1 or 5. That the bounds hold up to their caps, and what each ceiling excludes, is
  `NumericBoundary.lean`.

What is not shown here.

* The `boundary` premises of each theorem: statements about opaque operations or translated
  functions (`HmacAgrees`, `VecRetainTotal`, `KemAgreesFor`, ...). They are not part of `Premises.T`.
  Some have models (`Satisfiability.lean`), and the rest are recorded in `LIMITATIONS.md`.
* The `unwitnessed` premises: premises that relate a translated Braid to a model Braid
  (`StateRefines`, `MsgRefines`, `HonestChunk`), which need a value of an opaque type, and the premise
  `hdec` of `decoded_receive_refines`, that a byte string decodes to the state. They stay open here.
* That a reachable state meets the premises. A witness says a premise is not vacuous; it does not say
  every reachable state meets it. Among the values the decoder's invariant allows,
  `events + 1 < u32::MAX` fails only at `u32::MAX - 1` and `epoch + 1 < u64::MAX` only at
  `u64::MAX - 1`, and each of those is an ordinary state (`NumericBoundary.lean`).
-/

namespace Tacenta.NumericWitnessTriple

open Aeneas Aeneas.Std
open tacenta_triple_unit


@[simp] def vec1 {α : Type} (x : α) : alloc.vec.Vec α := ⟨[x], by simp; scalar_tac⟩
@[simp] def key0 : Array U8 32#usize := Array.repeat 32#usize 0#u8
@[simp] def skipK : tacenta_ratchet.SkippedKey := ⟨key0, 0#u32, 3#u32, key0⟩
@[simp] def ratS : tacenta_ratchet.State :=
  ⟨key0, some key0, key0, some key0, some key0, 1#u32, 1#u32, 0#u32, vec1 skipK, 5#u32, .Tacenta⟩
@[simp] def chain0 : tacenta_spqr.Chain := ⟨key0, 0#u64⟩
@[simp] def chains0 : tacenta_spqr.Chains := ⟨some chain0, none⟩
@[simp] def skip0 : tacenta_spqr.Skipped := ⟨1#u64, 0#u64, key0⟩
@[simp] def out0 : tacenta_spqr.Output := ⟨1#u64, key0⟩
@[simp] def spqrS : tacenta_spqr.State := ⟨key0, 1#u64, vec1 (1#u64, chains0), vec1 skip0, .A2b⟩
@[simp] def hdr0 : tacenta_ratchet.Header := ⟨key0, 0#u32, 0#u32⟩
@[simp] def mh0 : Model.State.Header := ⟨UnitT3.keyOf key0, 0, 0⟩
@[simp] def ratM : Model.State.State :=
  ⟨UnitT3.keyOf key0, some (UnitT3.keyOf key0), UnitT3.keyOf key0, some (UnitT3.keyOf key0), some (UnitT3.keyOf key0),
   1, 1, 0, [UnitT3.skippedOf skipK], 5, UnitT3.labelsOf .Tacenta⟩
theorem ratRel : UnitT3.StateR ratS ratM := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
theorem hdrRel : UnitT3.HeaderR hdr0 mh0 := ⟨rfl, rfl, rfl⟩
@[simp] def spqrM : Model.SparseRatchet.State :=
  ⟨UnitSpqrT3.keyOf key0, 1, [UnitSpqrT3.chainsEntryOf (1#u64, chains0)], [UnitSpqrT3.skippedOf skip0], .a2b⟩
theorem spqrRel : UnitSpqrT3.StateRefines spqrS spqrM := ⟨rfl, rfl, rfl, rfl, rfl⟩

abbrev Premises.UnitT1.receive_no_panic : Prop :=
  ∃ (state : tacenta_triple_unit.tacenta_ratchet.State),
    max state.skipped.val.length
          tacenta_triple_unit.tacenta_ratchet.MAX_SKIPPED_STORE.val +
        tacenta_triple_unit.tacenta_ratchet.MAX_SKIP.val ≤
      Usize.max

/-- The premises of `UnitT1.receive_no_panic` that the table of `check-precondition-witnesses.sh` puts inside the witness hold at one state. -/
theorem sat_UnitT1_receive_no_panic : Premises.UnitT1.receive_no_panic :=
  ⟨ratS, by simp [tacenta_ratchet.MAX_SKIPPED_STORE, tacenta_ratchet.MAX_SKIP]; scalar_tac⟩

abbrev Premises.UnitT3.receive_refines : Prop :=
  ∃ (s : tacenta_triple_unit.tacenta_ratchet.State) (m : Model.State.State) (hdr :
    tacenta_triple_unit.tacenta_ratchet.Header) (mh : Model.State.Header),
    UnitT3.StateR s m ∧
      UnitT3.HeaderR hdr mh ∧
        (List.filter (UnitT3.matchesHeader mh) m.skipped).length ≤ 1 ∧
          max s.skipped.val.length
                  tacenta_triple_unit.tacenta_ratchet.MAX_SKIPPED_STORE.val +
                tacenta_triple_unit.tacenta_ratchet.MAX_SKIP.val ≤
              Usize.max ∧
            s.events.val + 1 < U32.max

/-- The premises of `UnitT3.receive_refines` that the table of `check-precondition-witnesses.sh` puts inside the witness hold at one state. -/
theorem sat_UnitT3_receive_refines : Premises.UnitT3.receive_refines := by
  refine ⟨ratS, ratM, hdr0, mh0, ratRel, hdrRel, ?_, ?_, ?_⟩
  · simp [Tacenta.UnitT3.matchesHeader, Tacenta.UnitT3.skippedOf, skipK]
  · simp [tacenta_ratchet.MAX_SKIPPED_STORE, tacenta_ratchet.MAX_SKIP]; scalar_tac
  · simp; scalar_tac

abbrev Premises.UnitSpqrT1.receive_no_panic : Prop :=
  ∃ (st : tacenta_triple_unit.tacenta_spqr.State),
    st.chains.length + 2 < Usize.max ∧ st.skipped.length + tacenta_triple_unit.tacenta_spqr.MAX_SKIP.val ≤ Usize.max

/-- The premises of `UnitSpqrT1.receive_no_panic` that the table of `check-precondition-witnesses.sh` puts inside the witness hold at one state. -/
theorem sat_UnitSpqrT1_receive_no_panic : Premises.UnitSpqrT1.receive_no_panic :=
  ⟨spqrS, by simp; scalar_tac, by simp [tacenta_spqr.MAX_SKIP]; scalar_tac⟩

abbrev Premises.UnitSpqrT1.send_no_panic : Prop :=
  ∃ (st : tacenta_triple_unit.tacenta_spqr.State), st.chains.length + 1 < Usize.max

/-- The premises of `UnitSpqrT1.send_no_panic` that the table of `check-precondition-witnesses.sh` puts inside the witness hold at one state. -/
theorem sat_UnitSpqrT1_send_no_panic : Premises.UnitSpqrT1.send_no_panic :=
  ⟨spqrS, by simp; scalar_tac⟩

abbrev Premises.UnitSpqrT3.receive_refines : Prop :=
  ∃ (s : tacenta_triple_unit.tacenta_spqr.State) (m : Model.SparseRatchet.State) (receiving_epoch : U64) (out :
    Option tacenta_triple_unit.tacenta_spqr.Output) (n : U64),
    UnitSpqrT3.StateRefines s m ∧
      s.epoch.val + 1 < U64.max ∧
        s.chains.val.length + 2 < Usize.max ∧
          (∀ p ∈ s.chains.val,
              p.1.val + Model.SparseRatchet.epochsKept ≤ U64.max) ∧
            (∀ sk ∈ s.skipped.val,
                sk.epoch.val + Model.SparseRatchet.epochsKept ≤ U64.max) ∧
              (∀ (o : tacenta_triple_unit.tacenta_spqr.Output),
                  out = some o → o.key_epoch.val + Model.SparseRatchet.epochsKept ≤ U64.max) ∧
                s.skipped.val.length +
                      tacenta_triple_unit.tacenta_spqr.MAX_SKIP.val ≤
                    Usize.max ∧
                  (List.filter (fun (x : ℕ × ℕ × Model.State.Key) => x.1 == receiving_epoch.val && x.2.1 == n.val)
                          m.skipped).length ≤
                      1 ∧
                    ∀ p ∈ s.chains.val,
                      ∀ (ch : tacenta_triple_unit.tacenta_spqr.Chain),
                        p.2.send = some ch ∨ p.2.receive = some ch → ch.n.val < U64.max

/-- The premises of `UnitSpqrT3.receive_refines` that the table of `check-precondition-witnesses.sh` puts inside the witness hold at one state. -/
theorem sat_UnitSpqrT3_receive_refines : Premises.UnitSpqrT3.receive_refines := by
  refine ⟨spqrS, spqrM, 0#u64, some out0, 0#u64, spqrRel, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp; scalar_tac
  · simp; scalar_tac
  · simp [Model.SparseRatchet.epochsKept]; scalar_tac
  · simp [Model.SparseRatchet.epochsKept]; scalar_tac
  · simp [Model.SparseRatchet.epochsKept]; scalar_tac
  · simp [tacenta_spqr.MAX_SKIP]; scalar_tac
  · simp [Tacenta.UnitSpqrT3.skippedOf]
  · simp; scalar_tac

abbrev Premises.UnitSpqrT3.send_refines : Prop :=
  ∃ (s : tacenta_triple_unit.tacenta_spqr.State) (m : Model.SparseRatchet.State) (out :
    Option tacenta_triple_unit.tacenta_spqr.Output),
    UnitSpqrT3.StateRefines s m ∧
      s.epoch.val + 1 < U64.max ∧
        s.chains.val.length + 1 < Usize.max ∧
          (∀ p ∈ s.chains.val,
              p.1.val + Model.SparseRatchet.epochsKept ≤ U64.max) ∧
            (∀ sk ∈ s.skipped.val,
                sk.epoch.val + Model.SparseRatchet.epochsKept ≤ U64.max) ∧
              (∀ (o : tacenta_triple_unit.tacenta_spqr.Output),
                  out = some o → o.key_epoch.val + Model.SparseRatchet.epochsKept ≤ U64.max) ∧
                ∀ p ∈ s.chains.val,
                  ∀ (ch : tacenta_triple_unit.tacenta_spqr.Chain),
                    p.2.send = some ch ∨ p.2.receive = some ch → ch.n.val < U64.max

/-- The premises of `UnitSpqrT3.send_refines` that the table of `check-precondition-witnesses.sh` puts inside the witness hold at one state. -/
theorem sat_UnitSpqrT3_send_refines : Premises.UnitSpqrT3.send_refines := by
  refine ⟨spqrS, spqrM, some out0, spqrRel, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [Model.SparseRatchet.epochsKept] <;> scalar_tac

abbrev Premises.UnitTripleT1.State.receive_no_panic : Prop :=
  ∃ (self : tacenta_triple_unit.tacenta_triple.State),
    max self.classical.skipped.val.length
            tacenta_triple_unit.tacenta_ratchet.MAX_SKIPPED_STORE.val +
          tacenta_triple_unit.tacenta_ratchet.MAX_SKIP.val ≤
        Usize.max ∧
      self.post_quantum.chains.length + 2 < Usize.max ∧
        self.post_quantum.skipped.length + tacenta_triple_unit.tacenta_spqr.MAX_SKIP.val ≤ Usize.max

/-- The premises of `UnitTripleT1.State.receive_no_panic` that the table of `check-precondition-witnesses.sh` puts inside the witness hold at one state. -/
theorem sat_UnitTripleT1_State_receive_no_panic : Premises.UnitTripleT1.State.receive_no_panic :=
  ⟨⟨ratS, spqrS⟩, by simp [tacenta_ratchet.MAX_SKIPPED_STORE, tacenta_ratchet.MAX_SKIP]; scalar_tac,
    by simp; scalar_tac, by simp [tacenta_spqr.MAX_SKIP]; scalar_tac⟩

abbrev Premises.UnitTripleT1.State.send_no_panic : Prop :=
  ∃ (self : tacenta_triple_unit.tacenta_triple.State), self.post_quantum.chains.length + 1 < Usize.max

/-- The premises of `UnitTripleT1.State.send_no_panic` that the table of `check-precondition-witnesses.sh` puts inside the witness hold at one state. -/
theorem sat_UnitTripleT1_State_send_no_panic : Premises.UnitTripleT1.State.send_no_panic :=
  ⟨⟨ratS, spqrS⟩, by simp; scalar_tac⟩

abbrev Premises.UnitTripleT3.receive_refines : Prop :=
  ∃ (α : tacenta_triple_unit.tacenta_ratchet.State → Model.State.State) (β :
    tacenta_triple_unit.tacenta_spqr.State → Model.SparseRatchet.State) (s : tacenta_triple_unit.tacenta_triple.State) (m
    : Model.Triple.State) (header : tacenta_triple_unit.tacenta_triple.Header) (mh : Model.State.Header) (output :
    Option tacenta_triple_unit.tacenta_spqr.Output),
    UnitTripleT3.StateRefines α β s m ∧
      UnitTripleT3.RatchetHeaderR header.dr mh ∧
        (List.filter (fun (x : Model.State.Key × ℕ × ℕ × Model.State.Key) => x.1 == mh.dh && x.2.1 == mh.n)
                m.classical.skipped).length ≤
            1 ∧
          max m.classical.skipped.length Model.State.maxSkippedStore + Model.State.maxSkip ≤ Usize.max ∧
            m.classical.events + 1 < U32.max ∧
              m.postQuantum.epoch + 1 < U64.max ∧
                m.postQuantum.chains.length + 2 < Usize.max ∧
                  (∀ p ∈ m.postQuantum.chains, p.1 + Model.SparseRatchet.epochsKept ≤ U64.max) ∧
                    (∀ sk ∈ m.postQuantum.skipped, sk.1 + Model.SparseRatchet.epochsKept ≤ U64.max) ∧
                      (∀ (o : tacenta_triple_unit.tacenta_spqr.Output),
                          output = some o → o.key_epoch.val + Model.SparseRatchet.epochsKept ≤ U64.max) ∧
                        m.postQuantum.skipped.length + Model.SparseRatchet.maxSkip ≤ Usize.max ∧
                          (List.filter
                                  (fun (x : ℕ × ℕ × Model.State.Key) =>
                                    x.1 == header.epoch.val && x.2.1 == header.pq_n.val)
                                  m.postQuantum.skipped).length ≤
                              1 ∧
                            ∀ p ∈ m.postQuantum.chains,
                              ∀ (ch : Model.SparseRatchet.Chain),
                                p.2.send = some ch ∨ p.2.receive = some ch → ch.n < U64.max

/-- The premises of `UnitTripleT3.receive_refines` that the table of `check-precondition-witnesses.sh` puts inside the witness hold at one state. -/
theorem sat_UnitTripleT3_receive_refines : Premises.UnitTripleT3.receive_refines := by
  refine ⟨UnitTripleT3.ratchetAbs, UnitTripleT3.spqrAbs, ⟨ratS, spqrS⟩,
    ⟨UnitTripleT3.ratchetAbs ratS, UnitTripleT3.spqrAbs spqrS⟩, ⟨hdr0, 0#u64, 0#u64⟩, mh0, some out0,
    ⟨rfl, rfl⟩, ⟨rfl, rfl, rfl⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [UnitTripleT3.ratchetAbs, UnitT3.skippedOf, skipK]
  · simp [UnitTripleT3.ratchetAbs, Model.State.maxSkippedStore, Model.State.maxSkip]; scalar_tac
  · simp [UnitTripleT3.ratchetAbs]; scalar_tac
  · simp [UnitTripleT3.spqrAbs]; scalar_tac
  · simp [UnitTripleT3.spqrAbs]; scalar_tac
  · simp [UnitTripleT3.spqrAbs, Model.SparseRatchet.epochsKept, UnitSpqrT3.chainsEntryOf]; scalar_tac
  · simp [UnitTripleT3.spqrAbs, Model.SparseRatchet.epochsKept, UnitSpqrT3.skippedOf]; scalar_tac
  · simp [Model.SparseRatchet.epochsKept]; scalar_tac
  · simp [UnitTripleT3.spqrAbs, Model.SparseRatchet.maxSkip, Model.State.maxSkip]; scalar_tac
  · simp [UnitTripleT3.spqrAbs, UnitSpqrT3.skippedOf]
  · simp [UnitTripleT3.spqrAbs, UnitSpqrT3.chainsEntryOf, UnitSpqrT3.chainsOf, UnitSpqrT3.chainOf]; scalar_tac

abbrev Premises.UnitTripleT3.receive_refines_discharged : Prop :=
  ∃ (s : tacenta_triple_unit.tacenta_triple.State) (m : Model.Triple.State) (header :
    tacenta_triple_unit.tacenta_triple.Header) (mh : Model.State.Header) (output :
    Option tacenta_triple_unit.tacenta_spqr.Output),
    UnitTripleT3.StateRefines UnitTripleT3.ratchetAbs UnitTripleT3.spqrAbs s m ∧
      UnitTripleT3.RatchetHeaderR header.dr mh ∧
        (List.filter (fun (x : Model.State.Key × ℕ × ℕ × Model.State.Key) => x.1 == mh.dh && x.2.1 == mh.n)
                m.classical.skipped).length ≤
            1 ∧
          max m.classical.skipped.length Model.State.maxSkippedStore + Model.State.maxSkip ≤ Usize.max ∧
            m.classical.events + 1 < U32.max ∧
              m.postQuantum.epoch + 1 < U64.max ∧
                m.postQuantum.chains.length + 2 < Usize.max ∧
                  (∀ p ∈ m.postQuantum.chains, p.1 + Model.SparseRatchet.epochsKept ≤ U64.max) ∧
                    (∀ sk ∈ m.postQuantum.skipped, sk.1 + Model.SparseRatchet.epochsKept ≤ U64.max) ∧
                      (∀ (o : tacenta_triple_unit.tacenta_spqr.Output),
                          output = some o → o.key_epoch.val + Model.SparseRatchet.epochsKept ≤ U64.max) ∧
                        m.postQuantum.skipped.length + Model.SparseRatchet.maxSkip ≤ Usize.max ∧
                          (List.filter
                                  (fun (x : ℕ × ℕ × Model.State.Key) =>
                                    x.1 == header.epoch.val && x.2.1 == header.pq_n.val)
                                  m.postQuantum.skipped).length ≤
                              1 ∧
                            ∀ p ∈ m.postQuantum.chains,
                              ∀ (ch : Model.SparseRatchet.Chain),
                                p.2.send = some ch ∨ p.2.receive = some ch → ch.n < U64.max

/-- The premises of `UnitTripleT3.receive_refines_discharged` that the table of `check-precondition-witnesses.sh` puts inside the witness hold at one state. -/
theorem sat_UnitTripleT3_receive_refines_discharged : Premises.UnitTripleT3.receive_refines_discharged := by
  refine ⟨⟨ratS, spqrS⟩,
    ⟨UnitTripleT3.ratchetAbs ratS, UnitTripleT3.spqrAbs spqrS⟩, ⟨hdr0, 0#u64, 0#u64⟩, mh0, some out0,
    ⟨rfl, rfl⟩, ⟨rfl, rfl, rfl⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [UnitTripleT3.ratchetAbs, UnitT3.skippedOf, skipK]
  · simp [UnitTripleT3.ratchetAbs, Model.State.maxSkippedStore, Model.State.maxSkip]; scalar_tac
  · simp [UnitTripleT3.ratchetAbs]; scalar_tac
  · simp [UnitTripleT3.spqrAbs]; scalar_tac
  · simp [UnitTripleT3.spqrAbs]; scalar_tac
  · simp [UnitTripleT3.spqrAbs, Model.SparseRatchet.epochsKept, UnitSpqrT3.chainsEntryOf]; scalar_tac
  · simp [UnitTripleT3.spqrAbs, Model.SparseRatchet.epochsKept, UnitSpqrT3.skippedOf]; scalar_tac
  · simp [Model.SparseRatchet.epochsKept]; scalar_tac
  · simp [UnitTripleT3.spqrAbs, Model.SparseRatchet.maxSkip, Model.State.maxSkip]; scalar_tac
  · simp [UnitTripleT3.spqrAbs, UnitSpqrT3.skippedOf]
  · simp [UnitTripleT3.spqrAbs, UnitSpqrT3.chainsEntryOf, UnitSpqrT3.chainsOf, UnitSpqrT3.chainOf]; scalar_tac

abbrev Premises.UnitTripleT3.send_refines : Prop :=
  ∃ (α : tacenta_triple_unit.tacenta_ratchet.State → Model.State.State) (β :
    tacenta_triple_unit.tacenta_spqr.State → Model.SparseRatchet.State) (s : tacenta_triple_unit.tacenta_triple.State) (m
    : Model.Triple.State) (output : Option tacenta_triple_unit.tacenta_spqr.Output),
    UnitTripleT3.StateRefines α β s m ∧
      m.postQuantum.chains.length + 1 < Usize.max ∧
        (∀ p ∈ m.postQuantum.chains, p.1 + Model.SparseRatchet.epochsKept ≤ U64.max) ∧
          (∀ sk ∈ m.postQuantum.skipped, sk.1 + Model.SparseRatchet.epochsKept ≤ U64.max) ∧
            (∀ (o : tacenta_triple_unit.tacenta_spqr.Output),
                output = some o → o.key_epoch.val + Model.SparseRatchet.epochsKept ≤ U64.max) ∧
              m.postQuantum.epoch + 1 < U64.max ∧
                ∀ p ∈ m.postQuantum.chains,
                  ∀ (ch : Model.SparseRatchet.Chain), p.2.send = some ch ∨ p.2.receive = some ch → ch.n < U64.max

/-- The premises of `UnitTripleT3.send_refines` that the table of `check-precondition-witnesses.sh` puts inside the witness hold at one state. -/
theorem sat_UnitTripleT3_send_refines : Premises.UnitTripleT3.send_refines := by
  refine ⟨UnitTripleT3.ratchetAbs, UnitTripleT3.spqrAbs, ⟨ratS, spqrS⟩,
    ⟨UnitTripleT3.ratchetAbs ratS, UnitTripleT3.spqrAbs spqrS⟩, some out0, ⟨rfl, rfl⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [UnitTripleT3.spqrAbs]; scalar_tac
  · simp [UnitTripleT3.spqrAbs, Model.SparseRatchet.epochsKept, UnitSpqrT3.chainsEntryOf]; scalar_tac
  · simp [UnitTripleT3.spqrAbs, Model.SparseRatchet.epochsKept, UnitSpqrT3.skippedOf]; scalar_tac
  · simp [Model.SparseRatchet.epochsKept]; scalar_tac
  · simp [UnitTripleT3.spqrAbs]; scalar_tac
  · simp [UnitTripleT3.spqrAbs, UnitSpqrT3.chainsEntryOf, UnitSpqrT3.chainsOf, UnitSpqrT3.chainOf]; scalar_tac

abbrev Premises.UnitTripleT3.send_refines_discharged : Prop :=
  ∃ (s : tacenta_triple_unit.tacenta_triple.State) (m : Model.Triple.State) (output :
    Option tacenta_triple_unit.tacenta_spqr.Output),
    UnitTripleT3.StateRefines UnitTripleT3.ratchetAbs UnitTripleT3.spqrAbs s m ∧
      m.postQuantum.chains.length + 1 < Usize.max ∧
        (∀ p ∈ m.postQuantum.chains, p.1 + Model.SparseRatchet.epochsKept ≤ U64.max) ∧
          (∀ sk ∈ m.postQuantum.skipped, sk.1 + Model.SparseRatchet.epochsKept ≤ U64.max) ∧
            (∀ (o : tacenta_triple_unit.tacenta_spqr.Output),
                output = some o → o.key_epoch.val + Model.SparseRatchet.epochsKept ≤ U64.max) ∧
              m.postQuantum.epoch + 1 < U64.max ∧
                ∀ p ∈ m.postQuantum.chains,
                  ∀ (ch : Model.SparseRatchet.Chain), p.2.send = some ch ∨ p.2.receive = some ch → ch.n < U64.max

/-- The premises of `UnitTripleT3.send_refines_discharged` that the table of `check-precondition-witnesses.sh` puts inside the witness hold at one state. -/
theorem sat_UnitTripleT3_send_refines_discharged : Premises.UnitTripleT3.send_refines_discharged := by
  refine ⟨⟨ratS, spqrS⟩, ⟨UnitTripleT3.ratchetAbs ratS, UnitTripleT3.spqrAbs spqrS⟩, some out0, ⟨rfl, rfl⟩,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [UnitTripleT3.spqrAbs]; scalar_tac
  · simp [UnitTripleT3.spqrAbs, Model.SparseRatchet.epochsKept, UnitSpqrT3.chainsEntryOf]; scalar_tac
  · simp [UnitTripleT3.spqrAbs, Model.SparseRatchet.epochsKept, UnitSpqrT3.skippedOf]; scalar_tac
  · simp [Model.SparseRatchet.epochsKept]; scalar_tac
  · simp [UnitTripleT3.spqrAbs]; scalar_tac
  · simp [UnitTripleT3.spqrAbs, UnitSpqrT3.chainsEntryOf, UnitSpqrT3.chainsOf, UnitSpqrT3.chainOf]; scalar_tac



end Tacenta.NumericWitnessTriple

/--
info: 'Tacenta.NumericWitnessTriple.sat_UnitT1_receive_no_panic' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.NumericWitnessTriple.sat_UnitT1_receive_no_panic

/--
info: 'Tacenta.NumericWitnessTriple.sat_UnitT3_receive_refines' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.NumericWitnessTriple.sat_UnitT3_receive_refines

/--
info: 'Tacenta.NumericWitnessTriple.sat_UnitSpqrT1_receive_no_panic' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.NumericWitnessTriple.sat_UnitSpqrT1_receive_no_panic

/--
info: 'Tacenta.NumericWitnessTriple.sat_UnitSpqrT1_send_no_panic' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.NumericWitnessTriple.sat_UnitSpqrT1_send_no_panic

/--
info: 'Tacenta.NumericWitnessTriple.sat_UnitSpqrT3_receive_refines' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.NumericWitnessTriple.sat_UnitSpqrT3_receive_refines

/--
info: 'Tacenta.NumericWitnessTriple.sat_UnitSpqrT3_send_refines' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.NumericWitnessTriple.sat_UnitSpqrT3_send_refines

/--
info: 'Tacenta.NumericWitnessTriple.sat_UnitTripleT1_State_receive_no_panic' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.NumericWitnessTriple.sat_UnitTripleT1_State_receive_no_panic

/--
info: 'Tacenta.NumericWitnessTriple.sat_UnitTripleT1_State_send_no_panic' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.NumericWitnessTriple.sat_UnitTripleT1_State_send_no_panic

/--
info: 'Tacenta.NumericWitnessTriple.sat_UnitTripleT3_receive_refines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.NumericWitnessTriple.sat_UnitTripleT3_receive_refines

/--
info: 'Tacenta.NumericWitnessTriple.sat_UnitTripleT3_receive_refines_discharged' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.NumericWitnessTriple.sat_UnitTripleT3_receive_refines_discharged

/--
info: 'Tacenta.NumericWitnessTriple.sat_UnitTripleT3_send_refines' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.NumericWitnessTriple.sat_UnitTripleT3_send_refines

/--
info: 'Tacenta.NumericWitnessTriple.sat_UnitTripleT3_send_refines_discharged' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.NumericWitnessTriple.sat_UnitTripleT3_send_refines_discharged
