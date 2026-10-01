import Translation.T1
import Translation.T3
import Translation.ImportInv
import Translation.SpqrT1
import Translation.SpqrT3
import Translation.BraidT1
import Translation.BraidT3
import Translation.PreconditionShapes

/-!
# The numeric premises of the central theorems hold together at a concrete state: the standalone leaves

Theorems covered: the receive and send panic-freedom and refinement theorems of the classical ratchet,
the sparse ratchet and the ML-KEM Braid, and `Ratchet.decoded_receive_refines`, in the standalone
translations. The three-leaf unit and the eight-leaf session unit have their own copies of the theorems
and cannot share an environment with these, so they have `NumericWitnessTriple.lean` and
`NumericWitnessSession.lean`.

For each theorem `T` below, `Premises.T` is the statement that one choice of `T`'s data satisfies
every premise of `T` that is numeric (a bound on a length, a counter or an epoch, written against
`Usize.max`, `U32.max` or `U64.max`), every numeric predicate about a state (`ct1_bounded`,
`EncodersLive`, ...) and every relation between a translated value and a model value
(`StateRefines`, `StateR`, `HeaderR`) at the same time. `sat_T` proves it at a concrete state. A
theorem whose premises no state meets is true and says nothing; this is the check that these are not
that.

* The statement is not written twice. `tacenta-proofs/scripts/check-precondition-witnesses.sh` reads
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
  every reachable state meets it. `events + 1 < u32::MAX` and `epoch + 1 < u64::MAX` are met by
  every state but one honest value, and that value is an ordinary state (`NumericBoundary.lean`).

Two things specific to the leaves.

* The Braid witnesses are at `KeysUnsampled`, where `ct1_bounded` holds by its `True` arm. The arms of
  `ct1_bounded` that bound a stored ciphertext are in states that hold values of the opaque KEM and
  erasure types, which cannot be written down here, so `ct1_bounded` is shown to hold at one state and
  not at any state that carries a ciphertext. That is open. (On the session unit the erasure coder is
  translated, and `NumericWitnessSession.lean` witnesses `decoders_bounded` at a decoder at its cap.)
* `spqrS_inv` and `ratS_inv` show the two ratchet states the witnesses use satisfy the decoder
  invariant (`ImportInv.Spqr.Inv`, `ImportInv.Ratchet.Inv`), the predicate every state `from_bytes`
  returns satisfies. That is one direction: it does not say a decoder returns these states.
-/

namespace Tacenta.NumericWitnessLeaf

open Aeneas Aeneas.Std


@[simp] def vec1 {α : Type} (x : α) : alloc.vec.Vec α := ⟨[x], by simp; scalar_tac⟩
@[simp] def key0 : Array U8 32#usize := Array.repeat 32#usize 0#u8
@[simp] def skipK : tacenta_ratchet.SkippedKey := ⟨key0, 0#u32, 3#u32, key0⟩
@[simp] def ratS : tacenta_ratchet.State :=
  ⟨key0, some key0, key0, some key0, some key0, 1#u32, 1#u32, 0#u32, vec1 skipK, 5#u32, .Tacenta⟩
@[simp] def chain0 : tacenta_spqr.Chain := ⟨key0, 0#u64⟩
@[simp] def chains0 : tacenta_spqr.Chains := ⟨some chain0, none⟩
@[simp] def skip0 : tacenta_spqr.Skipped := ⟨1#u64, 0#u64, key0⟩
@[simp] def out0 : tacenta_spqr.Output := ⟨1#u64, key0⟩
@[simp] def spqrS : tacenta_spqr.State :=
  ⟨key0, 1#u64, vec1 (1#u64, chains0), vec1 skip0, .A2b⟩
@[simp] def spqrM : Model.SparseRatchet.State :=
  ⟨SpqrT3.keyOf key0, 1, [SpqrT3.chainsEntryOf (1#u64, chains0)], [SpqrT3.skippedOf skip0], .a2b⟩
theorem spqrRel : SpqrT3.StateRefines spqrS spqrM := ⟨rfl, rfl, rfl, rfl, rfl⟩
@[simp] def ratM : Model.State.State :=
  ⟨T3.keyOf key0, some (T3.keyOf key0), T3.keyOf key0, some (T3.keyOf key0), some (T3.keyOf key0),
   1, 1, 0, [T3.skippedOf skipK], 5, T3.labelsOf .Tacenta⟩
theorem ratRel : T3.StateR ratS ratM := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
@[simp] def hdr0 : tacenta_ratchet.Header := ⟨key0, 0#u32, 0#u32⟩
@[simp] def mh0 : Model.State.Header := ⟨T3.keyOf key0, 0, 0⟩
theorem hdrRel : T3.HeaderR hdr0 mh0 := ⟨rfl, rfl, rfl⟩
@[simp] def auth0 : tacenta_braid.Auth := ⟨key0, key0⟩
@[simp] def braidS : tacenta_braid.Braid := ⟨.KeysUnsampled 1#u64 auth0⟩
@[simp] def modelEnc : Model.Braid.Encoder := ⟨[], 0⟩
@[simp] def modelLive : Model.Braid.BraidState :=
  .keysSampled 0 ⟨[], []⟩ [] [] modelEnc

abbrev Premises.T1.receive_no_panic : Prop :=
  ∃ (state : tacenta_ratchet.State),
    max state.skipped.val.length tacenta_ratchet.MAX_SKIPPED_STORE.val +
        tacenta_ratchet.MAX_SKIP.val ≤
      Usize.max

/-- The premises of `T1.receive_no_panic` that the table of `check-precondition-witnesses.sh` puts inside the witness hold at one state. -/
theorem sat_T1_receive_no_panic : Premises.T1.receive_no_panic :=
  ⟨ratS, by simp [tacenta_ratchet.MAX_SKIPPED_STORE, tacenta_ratchet.MAX_SKIP]; scalar_tac⟩

abbrev Premises.T3.receive_refines : Prop :=
  ∃ (s : tacenta_ratchet.State) (m : Model.State.State) (hdr : tacenta_ratchet.Header) (mh : Model.State.Header),
    T3.StateR s m ∧
      T3.HeaderR hdr mh ∧
        (List.filter (T3.matchesHeader mh) m.skipped).length ≤ 1 ∧
          max s.skipped.val.length tacenta_ratchet.MAX_SKIPPED_STORE.val +
                tacenta_ratchet.MAX_SKIP.val ≤
              Usize.max ∧
            s.events.val + 1 < U32.max

/-- The premises of `T3.receive_refines` that the table of `check-precondition-witnesses.sh` puts inside the witness hold at one state. -/
theorem sat_T3_receive_refines : Premises.T3.receive_refines := by
  refine ⟨ratS, ratM, hdr0, mh0, ratRel, hdrRel, ?_, ?_, ?_⟩
  · simp [T3.matchesHeader, T3.skippedOf, skipK]
  · simp [tacenta_ratchet.MAX_SKIPPED_STORE, tacenta_ratchet.MAX_SKIP]; scalar_tac
  · simp; scalar_tac

abbrev Premises.ImportInv.Ratchet.decoded_receive_refines : Prop :=
  ∃ (s : tacenta_ratchet.State) (m : Model.State.State) (hdr : tacenta_ratchet.Header) (mh : Model.State.Header),
    s.events.val + 1 < U32.max ∧ T3.StateR s m ∧ T3.HeaderR hdr mh

/-- The premises of `ImportInv.Ratchet.decoded_receive_refines` that the table of `check-precondition-witnesses.sh` puts inside the witness hold at one state. -/
theorem sat_ImportInv_Ratchet_decoded_receive_refines : Premises.ImportInv.Ratchet.decoded_receive_refines :=
  ⟨ratS, ratM, hdr0, mh0, by simp; scalar_tac, ratRel, hdrRel⟩

abbrev Premises.SpqrT1.receive_no_panic : Prop :=
  ∃ (st : tacenta_spqr.State),
    st.chains.length + 2 < Usize.max ∧ st.skipped.length + tacenta_spqr.MAX_SKIP.val ≤ Usize.max

/-- The premises of `SpqrT1.receive_no_panic` that the table of `check-precondition-witnesses.sh` puts inside the witness hold at one state. -/
theorem sat_SpqrT1_receive_no_panic : Premises.SpqrT1.receive_no_panic :=
  ⟨spqrS, by simp; scalar_tac, by simp [tacenta_spqr.MAX_SKIP]; scalar_tac⟩

abbrev Premises.SpqrT1.send_no_panic : Prop :=
  ∃ (st : tacenta_spqr.State), st.chains.length + 1 < Usize.max

/-- The premises of `SpqrT1.send_no_panic` that the table of `check-precondition-witnesses.sh` puts inside the witness hold at one state. -/
theorem sat_SpqrT1_send_no_panic : Premises.SpqrT1.send_no_panic :=
  ⟨spqrS, by simp; scalar_tac⟩

abbrev Premises.SpqrT3.receive_refines : Prop :=
  ∃ (s : tacenta_spqr.State) (m : Model.SparseRatchet.State) (receiving_epoch : U64) (out : Option tacenta_spqr.Output) (n
    : U64),
    SpqrT3.StateRefines s m ∧
      s.epoch.val + 1 < U64.max ∧
        s.chains.val.length + 2 < Usize.max ∧
          (∀ p ∈ s.chains.val, p.1.val + Model.SparseRatchet.epochsKept ≤ U64.max) ∧
            (∀ sk ∈ s.skipped.val,
                sk.epoch.val + Model.SparseRatchet.epochsKept ≤ U64.max) ∧
              (∀ (o : tacenta_spqr.Output),
                  out = some o → o.key_epoch.val + Model.SparseRatchet.epochsKept ≤ U64.max) ∧
                s.skipped.val.length + tacenta_spqr.MAX_SKIP.val ≤ Usize.max ∧
                  (List.filter (fun (x : ℕ × ℕ × Model.State.Key) => x.1 == receiving_epoch.val && x.2.1 == n.val)
                          m.skipped).length ≤
                      1 ∧
                    ∀ p ∈ s.chains.val,
                      ∀ (ch : tacenta_spqr.Chain), p.2.send = some ch ∨ p.2.receive = some ch → ch.n.val < U64.max

/-- The premises of `SpqrT3.receive_refines` that the table of `check-precondition-witnesses.sh` puts inside the witness hold at one state. -/
theorem sat_SpqrT3_receive_refines : Premises.SpqrT3.receive_refines := by
  refine ⟨spqrS, spqrM, 0#u64, some out0, 0#u64, spqrRel, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp; scalar_tac
  · simp; scalar_tac
  · simp [Model.SparseRatchet.epochsKept]; scalar_tac
  · simp [Model.SparseRatchet.epochsKept]; scalar_tac
  · simp [Model.SparseRatchet.epochsKept]; scalar_tac
  · simp [tacenta_spqr.MAX_SKIP]; scalar_tac
  · simp [SpqrT3.skippedOf]
  · simp; scalar_tac

abbrev Premises.SpqrT3.send_refines : Prop :=
  ∃ (s : tacenta_spqr.State) (m : Model.SparseRatchet.State) (out : Option tacenta_spqr.Output),
    SpqrT3.StateRefines s m ∧
      s.epoch.val + 1 < U64.max ∧
        s.chains.val.length + 1 < Usize.max ∧
          (∀ p ∈ s.chains.val, p.1.val + Model.SparseRatchet.epochsKept ≤ U64.max) ∧
            (∀ sk ∈ s.skipped.val,
                sk.epoch.val + Model.SparseRatchet.epochsKept ≤ U64.max) ∧
              (∀ (o : tacenta_spqr.Output),
                  out = some o → o.key_epoch.val + Model.SparseRatchet.epochsKept ≤ U64.max) ∧
                ∀ p ∈ s.chains.val,
                  ∀ (ch : tacenta_spqr.Chain), p.2.send = some ch ∨ p.2.receive = some ch → ch.n.val < U64.max

/-- The premises of `SpqrT3.send_refines` that the table of `check-precondition-witnesses.sh` puts inside the witness hold at one state. -/
theorem sat_SpqrT3_send_refines : Premises.SpqrT3.send_refines := by
  refine ⟨spqrS, spqrM, some out0, spqrRel, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [Model.SparseRatchet.epochsKept] <;> scalar_tac

abbrev Premises.BraidT1.Braid.receive_no_panic : Prop :=
  ∃ (self : tacenta_braid.Braid), BraidT1.State.ct1_bounded self.state

/-- The premises of `BraidT1.Braid.receive_no_panic` that the table of `check-precondition-witnesses.sh` puts inside the witness hold at one state. -/
theorem sat_BraidT1_Braid_receive_no_panic : Premises.BraidT1.Braid.receive_no_panic :=
  ⟨braidS, by simp [BraidT1.State.ct1_bounded]⟩

abbrev Premises.BraidT1.Braid.step_receive_no_panic : Prop :=
  ∃ (state : tacenta_braid.State), BraidT1.State.ct1_bounded state

/-- The premises of `BraidT1.Braid.step_receive_no_panic` that the table of `check-precondition-witnesses.sh` puts inside the witness hold at one state. -/
theorem sat_BraidT1_Braid_step_receive_no_panic : Premises.BraidT1.Braid.step_receive_no_panic :=
  ⟨.KeysUnsampled 1#u64 auth0, by simp [BraidT1.State.ct1_bounded]⟩

abbrev Premises.BraidT3.Braid.receive_refines : Prop :=
  ∃ (self : tacenta_braid.Braid),
    BraidT1.State.ct1_bounded self.state ∧ (BraidT1.State.epoch_val self.state).val + 1 < U64.max

/-- The premises of `BraidT3.Braid.receive_refines` that the table of `check-precondition-witnesses.sh` puts inside the witness hold at one state. -/
theorem sat_BraidT3_Braid_receive_refines : Premises.BraidT3.Braid.receive_refines :=
  ⟨braidS, by simp [BraidT1.State.ct1_bounded], by simp [BraidT1.State.epoch_val]; scalar_tac⟩

abbrev Premises.BraidT3.step_receive_refines : Prop :=
  ∃ (state : tacenta_braid.State), BraidT1.State.ct1_bounded state ∧ (BraidT1.State.epoch_val state).val + 1 < U64.max

/-- The premises of `BraidT3.step_receive_refines` that the table of `check-precondition-witnesses.sh` puts inside the witness hold at one state. -/
theorem sat_BraidT3_step_receive_refines : Premises.BraidT3.step_receive_refines :=
  ⟨.KeysUnsampled 1#u64 auth0, by simp [BraidT1.State.ct1_bounded],
    by simp [BraidT1.State.epoch_val]; scalar_tac⟩

abbrev Premises.BraidT3.Braid.send_refines : Prop :=
  ∃ (model : Model.Braid.BraidState), BraidT3.EncodersLive model

/-- The premises of `BraidT3.Braid.send_refines` that the table of `check-precondition-witnesses.sh` puts inside the witness hold at one state. -/
theorem sat_BraidT3_Braid_send_refines : Premises.BraidT3.Braid.send_refines :=
  ⟨modelLive, by simp [BraidT3.EncodersLive, BraidT3.EncoderOf]⟩

abbrev Premises.BraidT3.step_send_refines : Prop :=
  ∃ (model : Model.Braid.BraidState), BraidT3.EncodersLive model

/-- The premises of `BraidT3.step_send_refines` that the table of `check-precondition-witnesses.sh` puts inside the witness hold at one state. -/
theorem sat_BraidT3_step_send_refines : Premises.BraidT3.step_send_refines :=
  ⟨modelLive, by simp [BraidT3.EncodersLive, BraidT3.EncoderOf]⟩


/-- The sparse-ratchet state the witnesses use satisfies the decoder's invariant. -/
theorem spqrS_inv : ImportInv.Spqr.Inv spqrS := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [tacenta_spqr.MAX_SKIPPED_STORE]
  · intro q hq
    simp at hq
    subst hq
    simp [tacenta_spqr.EPOCHS_KEPT, Aeneas.Std.core.num.U64.saturating_add,
      Aeneas.Std.UScalar.saturating_add, U64.max_eq]
    decide
  · simp
  · exact ⟨(1#u64, chains0), by simp, by simp⟩
  · intro a ha
    simp at ha
    subst ha
    exact ⟨(1#u64, chains0), by simp, by simp⟩
  · simp

/-- The classical-ratchet state the witnesses use satisfies the decoder's invariant. -/
theorem ratS_inv : ImportInv.Ratchet.Inv ratS := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [tacenta_ratchet.MAX_SKIPPED_STORE]
  · simp; scalar_tac
  · intro e he; simp at he; subst he; simp
  · simp
  · simp
  · simp [T1.canonicalX25519]
  · intro k hk; simp at hk; subst hk; simp [T1.canonicalX25519]
  · intro e he; simp at he; subst he; simp [T1.canonicalX25519]

end Tacenta.NumericWitnessLeaf

/--
info: 'Tacenta.NumericWitnessLeaf.sat_T1_receive_no_panic' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.NumericWitnessLeaf.sat_T1_receive_no_panic

/--
info: 'Tacenta.NumericWitnessLeaf.sat_T3_receive_refines' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.NumericWitnessLeaf.sat_T3_receive_refines

/--
info: 'Tacenta.NumericWitnessLeaf.sat_ImportInv_Ratchet_decoded_receive_refines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.NumericWitnessLeaf.sat_ImportInv_Ratchet_decoded_receive_refines

/--
info: 'Tacenta.NumericWitnessLeaf.sat_SpqrT1_receive_no_panic' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.NumericWitnessLeaf.sat_SpqrT1_receive_no_panic

/--
info: 'Tacenta.NumericWitnessLeaf.sat_SpqrT1_send_no_panic' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.NumericWitnessLeaf.sat_SpqrT1_send_no_panic

/--
info: 'Tacenta.NumericWitnessLeaf.sat_SpqrT3_receive_refines' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.NumericWitnessLeaf.sat_SpqrT3_receive_refines

/--
info: 'Tacenta.NumericWitnessLeaf.sat_SpqrT3_send_refines' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.NumericWitnessLeaf.sat_SpqrT3_send_refines

/--
info: 'Tacenta.NumericWitnessLeaf.sat_BraidT1_Braid_receive_no_panic' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_braid.tacenta_erasure.Decoder,
 tacenta_braid.tacenta_erasure.Encoder,
 tacenta_braid.tacenta_kem.EncapsState,
 tacenta_braid.tacenta_kem.IncrementalKeyPair]
-/
#guard_msgs in
#print axioms Tacenta.NumericWitnessLeaf.sat_BraidT1_Braid_receive_no_panic

/--
info: 'Tacenta.NumericWitnessLeaf.sat_BraidT1_Braid_step_receive_no_panic' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_braid.tacenta_erasure.Decoder,
 tacenta_braid.tacenta_erasure.Encoder,
 tacenta_braid.tacenta_kem.EncapsState,
 tacenta_braid.tacenta_kem.IncrementalKeyPair]
-/
#guard_msgs in
#print axioms Tacenta.NumericWitnessLeaf.sat_BraidT1_Braid_step_receive_no_panic

/--
info: 'Tacenta.NumericWitnessLeaf.sat_BraidT3_Braid_receive_refines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_braid.tacenta_erasure.Decoder,
 tacenta_braid.tacenta_erasure.Encoder,
 tacenta_braid.tacenta_kem.EncapsState,
 tacenta_braid.tacenta_kem.IncrementalKeyPair]
-/
#guard_msgs in
#print axioms Tacenta.NumericWitnessLeaf.sat_BraidT3_Braid_receive_refines

/--
info: 'Tacenta.NumericWitnessLeaf.sat_BraidT3_step_receive_refines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_braid.tacenta_erasure.Decoder,
 tacenta_braid.tacenta_erasure.Encoder,
 tacenta_braid.tacenta_kem.EncapsState,
 tacenta_braid.tacenta_kem.IncrementalKeyPair]
-/
#guard_msgs in
#print axioms Tacenta.NumericWitnessLeaf.sat_BraidT3_step_receive_refines

/--
info: 'Tacenta.NumericWitnessLeaf.sat_BraidT3_Braid_send_refines' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.NumericWitnessLeaf.sat_BraidT3_Braid_send_refines

/--
info: 'Tacenta.NumericWitnessLeaf.sat_BraidT3_step_send_refines' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.NumericWitnessLeaf.sat_BraidT3_step_send_refines

/--
info: 'Tacenta.NumericWitnessLeaf.spqrS_inv' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.NumericWitnessLeaf.spqrS_inv

/--
info: 'Tacenta.NumericWitnessLeaf.ratS_inv' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.NumericWitnessLeaf.ratS_inv
