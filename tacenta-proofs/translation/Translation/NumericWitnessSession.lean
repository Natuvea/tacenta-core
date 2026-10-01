import Translation.SessionUnitDecodedStateDischarge
import Translation.SessionUnitT1
import Translation.SessionUnitT3
import Translation.SessionUnitRatchetImportInv
import Translation.SessionUnitSpqrT1
import Translation.SessionUnitSpqrT3
import Translation.SessionUnitTripleT1
import Translation.SessionUnitTripleT3
import Translation.SessionUnitBraidT1
import Translation.SessionUnitBraidT3

/-!
# The numeric premises of the central theorems hold together at a concrete state: the session unit

Theorems covered: the receive and send panic-freedom and refinement theorems on the eight-leaf
session unit, for the classical ratchet, the sparse ratchet, the Triple Ratchet (including its
discharged refinements), the ML-KEM Braid, and `Ratchet.decoded_receive_refines`. The lifecycle
theorems (`encrypt_no_panic` and the others, whose headroom records hold values of opaque
boundary types) are not here.

For each theorem `T` below, `Premises.T` is the statement that one choice of `T`'s data satisfies
every premise of `T` that is numeric (a bound on a length, a counter or an epoch, written against
`Usize.max`, `U32.max` or `U64.max`), every numeric predicate about a state (`ct1_bounded`,
`EncodersLive`, ...) and every relation between a translated value and a model value
(`StateRefines`, `StateR`, `HeaderR`; for the Braid theorems the relations are left out, as set out below)
at the same time. `sat_T` proves it at a concrete state. A
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
* The states are small, not extremal: one chain and one skipped key, one stored skipped key, a
  counter at 1 or 5. That is what the proofs below use; no gate checks it, and no gate checks that
  the state a `sat_` proof uses is the one `session_unit_spqrS_inv` and `session_unit_ratS_inv` are
  about. That the bounds hold up to their caps, and what each ceiling excludes, is
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

Two things specific to the session unit.

* The Braid witnesses are at `NoHeaderReceived` with a decoder at the cap its invariant admits
  (`needed = 65536`, `MAX_CODEWORDS`), so `decoders_bounded` is witnessed in its real arm. The other
  arms of `ct1_bounded` and `decoders_bounded` that hold a KEM value stay open, as in the leaves.
* `session_unit_spqrS_inv` and `session_unit_ratS_inv` show the two ratchet states the witnesses use satisfy the decoder
  invariant. That is one direction: it does not say a decoder returns these states.
-/

namespace Tacenta.NumericWitnessSession

open Aeneas Aeneas.Std
open tacenta_session_unit


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
@[simp] def mh0 : Model.State.Header := ⟨SessionUnitT3.keyOf key0, 0, 0⟩
@[simp] def ratM : Model.State.State :=
  ⟨SessionUnitT3.keyOf key0, some (SessionUnitT3.keyOf key0), SessionUnitT3.keyOf key0, some (SessionUnitT3.keyOf key0), some (SessionUnitT3.keyOf key0),
   1, 1, 0, [SessionUnitT3.skippedOf skipK], 5, SessionUnitT3.labelsOf .Tacenta⟩
theorem ratRel : SessionUnitT3.StateR ratS ratM := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
theorem hdrRel : SessionUnitT3.HeaderR hdr0 mh0 := ⟨rfl, rfl, rfl⟩
@[simp] def spqrM : Model.SparseRatchet.State :=
  ⟨SessionUnitSpqrT3.keyOf key0, 1, [SessionUnitSpqrT3.chainsEntryOf (1#u64, chains0)], [SessionUnitSpqrT3.skippedOf skip0], .a2b⟩
theorem spqrRel : SessionUnitSpqrT3.StateRefines spqrS spqrM := ⟨rfl, rfl, rfl, rfl, rfl⟩
@[simp] def chunk0 : tacenta_erasure.Chunk := ⟨0#u16, key0⟩
/-- A decoder at the largest `needed` its invariant admits, `MAX_CODEWORDS`, holding one chunk. -/
@[simp] def decMax : tacenta_erasure.Decoder := ⟨2097152#usize, 65536#usize, vec1 chunk0⟩
@[simp] def auth0 : tacenta_braid.Auth := ⟨key0, key0⟩
@[simp] def braidS : tacenta_braid.Braid := ⟨.NoHeaderReceived 1#u64 auth0 decMax⟩
@[simp] def modelEnc : Model.Braid.Encoder := ⟨[], 0⟩
@[simp] def modelLive : Model.Braid.BraidState := .keysSampled 0 ⟨[], []⟩ [] [] modelEnc

abbrev Premises.SessionUnitT1.receive_no_panic : Prop :=
  ∃ (state : tacenta_session_unit.tacenta_ratchet.State),
    max state.skipped.val.length
          tacenta_session_unit.tacenta_ratchet.MAX_SKIPPED_STORE.val +
        tacenta_session_unit.tacenta_ratchet.MAX_SKIP.val ≤
      Usize.max

/-- The premises of `SessionUnitT1.receive_no_panic` that the table of `check-precondition-witnesses.sh` puts inside the witness hold at one state. -/
theorem sat_SessionUnitT1_receive_no_panic : Premises.SessionUnitT1.receive_no_panic :=
  ⟨ratS, by simp [tacenta_ratchet.MAX_SKIPPED_STORE, tacenta_ratchet.MAX_SKIP]; scalar_tac⟩

abbrev Premises.SessionUnitT3.receive_refines : Prop :=
  ∃ (s : tacenta_session_unit.tacenta_ratchet.State) (m : Model.State.State) (hdr :
    tacenta_session_unit.tacenta_ratchet.Header) (mh : Model.State.Header),
    SessionUnitT3.StateR s m ∧
      SessionUnitT3.HeaderR hdr mh ∧
        (List.filter (SessionUnitT3.matchesHeader mh) m.skipped).length ≤ 1 ∧
          max s.skipped.val.length
                  tacenta_session_unit.tacenta_ratchet.MAX_SKIPPED_STORE.val +
                tacenta_session_unit.tacenta_ratchet.MAX_SKIP.val ≤
              Usize.max ∧
            s.events.val + 1 < U32.max

/-- The premises of `SessionUnitT3.receive_refines` that the table of `check-precondition-witnesses.sh` puts inside the witness hold at one state. -/
theorem sat_SessionUnitT3_receive_refines : Premises.SessionUnitT3.receive_refines := by
  refine ⟨ratS, ratM, hdr0, mh0, ratRel, hdrRel, ?_, ?_, ?_⟩
  · simp [Tacenta.SessionUnitT3.matchesHeader, Tacenta.SessionUnitT3.skippedOf, skipK]
  · simp [tacenta_ratchet.MAX_SKIPPED_STORE, tacenta_ratchet.MAX_SKIP]; scalar_tac
  · simp; scalar_tac

abbrev Premises.SessionUnitRatchetImportInv.Ratchet.decoded_receive_refines : Prop :=
  ∃ (s : tacenta_session_unit.tacenta_ratchet.State) (m : Model.State.State) (hdr :
    tacenta_session_unit.tacenta_ratchet.Header) (mh : Model.State.Header),
    s.events.val + 1 < U32.max ∧ SessionUnitT3.StateR s m ∧ SessionUnitT3.HeaderR hdr mh

/-- The premises of `SessionUnitRatchetImportInv.Ratchet.decoded_receive_refines` that the table of `check-precondition-witnesses.sh` puts inside the witness hold at one state. -/
theorem sat_SessionUnitRatchetImportInv_Ratchet_decoded_receive_refines : Premises.SessionUnitRatchetImportInv.Ratchet.decoded_receive_refines :=
  ⟨ratS, ratM, hdr0, mh0, by simp; scalar_tac, ratRel, hdrRel⟩

abbrev Premises.SessionUnitSpqrT1.receive_no_panic : Prop :=
  ∃ (st : tacenta_session_unit.tacenta_spqr.State),
    st.chains.length + 2 < Usize.max ∧ st.skipped.length + tacenta_session_unit.tacenta_spqr.MAX_SKIP.val ≤ Usize.max

/-- The premises of `SessionUnitSpqrT1.receive_no_panic` that the table of `check-precondition-witnesses.sh` puts inside the witness hold at one state. -/
theorem sat_SessionUnitSpqrT1_receive_no_panic : Premises.SessionUnitSpqrT1.receive_no_panic :=
  ⟨spqrS, by simp; scalar_tac, by simp [tacenta_spqr.MAX_SKIP]; scalar_tac⟩

abbrev Premises.SessionUnitSpqrT1.send_no_panic : Prop :=
  ∃ (st : tacenta_session_unit.tacenta_spqr.State), st.chains.length + 1 < Usize.max

/-- The premises of `SessionUnitSpqrT1.send_no_panic` that the table of `check-precondition-witnesses.sh` puts inside the witness hold at one state. -/
theorem sat_SessionUnitSpqrT1_send_no_panic : Premises.SessionUnitSpqrT1.send_no_panic :=
  ⟨spqrS, by simp; scalar_tac⟩

abbrev Premises.SessionUnitSpqrT3.receive_refines : Prop :=
  ∃ (s : tacenta_session_unit.tacenta_spqr.State) (m : Model.SparseRatchet.State) (receiving_epoch : U64) (out :
    Option tacenta_session_unit.tacenta_spqr.Output) (n : U64),
    SessionUnitSpqrT3.StateRefines s m ∧
      s.epoch.val + 1 < U64.max ∧
        s.chains.val.length + 2 < Usize.max ∧
          (∀ p ∈ s.chains.val,
              p.1.val + Model.SparseRatchet.epochsKept ≤ U64.max) ∧
            (∀ sk ∈ s.skipped.val,
                sk.epoch.val + Model.SparseRatchet.epochsKept ≤ U64.max) ∧
              (∀ (o : tacenta_session_unit.tacenta_spqr.Output),
                  out = some o → o.key_epoch.val + Model.SparseRatchet.epochsKept ≤ U64.max) ∧
                s.skipped.val.length +
                      tacenta_session_unit.tacenta_spqr.MAX_SKIP.val ≤
                    Usize.max ∧
                  (List.filter (fun (x : ℕ × ℕ × Model.State.Key) => x.1 == receiving_epoch.val && x.2.1 == n.val)
                          m.skipped).length ≤
                      1 ∧
                    ∀ p ∈ s.chains.val,
                      ∀ (ch : tacenta_session_unit.tacenta_spqr.Chain),
                        p.2.send = some ch ∨ p.2.receive = some ch → ch.n.val < U64.max

/-- The premises of `SessionUnitSpqrT3.receive_refines` that the table of `check-precondition-witnesses.sh` puts inside the witness hold at one state. -/
theorem sat_SessionUnitSpqrT3_receive_refines : Premises.SessionUnitSpqrT3.receive_refines := by
  refine ⟨spqrS, spqrM, 0#u64, some out0, 0#u64, spqrRel, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp; scalar_tac
  · simp; scalar_tac
  · simp [Model.SparseRatchet.epochsKept]; scalar_tac
  · simp [Model.SparseRatchet.epochsKept]; scalar_tac
  · simp [Model.SparseRatchet.epochsKept]; scalar_tac
  · simp [tacenta_spqr.MAX_SKIP]; scalar_tac
  · simp [Tacenta.SessionUnitSpqrT3.skippedOf]
  · simp; scalar_tac

abbrev Premises.SessionUnitSpqrT3.send_refines : Prop :=
  ∃ (s : tacenta_session_unit.tacenta_spqr.State) (m : Model.SparseRatchet.State) (out :
    Option tacenta_session_unit.tacenta_spqr.Output),
    SessionUnitSpqrT3.StateRefines s m ∧
      s.epoch.val + 1 < U64.max ∧
        s.chains.val.length + 1 < Usize.max ∧
          (∀ p ∈ s.chains.val,
              p.1.val + Model.SparseRatchet.epochsKept ≤ U64.max) ∧
            (∀ sk ∈ s.skipped.val,
                sk.epoch.val + Model.SparseRatchet.epochsKept ≤ U64.max) ∧
              (∀ (o : tacenta_session_unit.tacenta_spqr.Output),
                  out = some o → o.key_epoch.val + Model.SparseRatchet.epochsKept ≤ U64.max) ∧
                ∀ p ∈ s.chains.val,
                  ∀ (ch : tacenta_session_unit.tacenta_spqr.Chain),
                    p.2.send = some ch ∨ p.2.receive = some ch → ch.n.val < U64.max

/-- The premises of `SessionUnitSpqrT3.send_refines` that the table of `check-precondition-witnesses.sh` puts inside the witness hold at one state. -/
theorem sat_SessionUnitSpqrT3_send_refines : Premises.SessionUnitSpqrT3.send_refines := by
  refine ⟨spqrS, spqrM, some out0, spqrRel, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [Model.SparseRatchet.epochsKept] <;> scalar_tac

abbrev Premises.SessionUnitTripleT1.State.receive_no_panic : Prop :=
  ∃ (self : tacenta_session_unit.tacenta_triple.State),
    max self.classical.skipped.val.length
            tacenta_session_unit.tacenta_ratchet.MAX_SKIPPED_STORE.val +
          tacenta_session_unit.tacenta_ratchet.MAX_SKIP.val ≤
        Usize.max ∧
      self.post_quantum.chains.length + 2 < Usize.max ∧
        self.post_quantum.skipped.length + tacenta_session_unit.tacenta_spqr.MAX_SKIP.val ≤ Usize.max

/-- The premises of `SessionUnitTripleT1.State.receive_no_panic` that the table of `check-precondition-witnesses.sh` puts inside the witness hold at one state. -/
theorem sat_SessionUnitTripleT1_State_receive_no_panic : Premises.SessionUnitTripleT1.State.receive_no_panic :=
  ⟨⟨ratS, spqrS⟩, by simp [tacenta_ratchet.MAX_SKIPPED_STORE, tacenta_ratchet.MAX_SKIP]; scalar_tac,
    by simp; scalar_tac, by simp [tacenta_spqr.MAX_SKIP]; scalar_tac⟩

abbrev Premises.SessionUnitTripleT1.State.send_no_panic : Prop :=
  ∃ (self : tacenta_session_unit.tacenta_triple.State), self.post_quantum.chains.length + 1 < Usize.max

/-- The premises of `SessionUnitTripleT1.State.send_no_panic` that the table of `check-precondition-witnesses.sh` puts inside the witness hold at one state. -/
theorem sat_SessionUnitTripleT1_State_send_no_panic : Premises.SessionUnitTripleT1.State.send_no_panic :=
  ⟨⟨ratS, spqrS⟩, by simp; scalar_tac⟩

abbrev Premises.SessionUnitTripleT3.receive_refines : Prop :=
  ∃ (α : tacenta_session_unit.tacenta_ratchet.State → Model.State.State) (β :
    tacenta_session_unit.tacenta_spqr.State → Model.SparseRatchet.State) (s : tacenta_session_unit.tacenta_triple.State)
    (m : Model.Triple.State) (header : tacenta_session_unit.tacenta_triple.Header) (mh : Model.State.Header) (output :
    Option tacenta_session_unit.tacenta_spqr.Output),
    SessionUnitTripleT3.StateRefines α β s m ∧
      SessionUnitTripleT3.RatchetHeaderR header.dr mh ∧
        (List.filter (fun (x : Model.State.Key × ℕ × ℕ × Model.State.Key) => x.1 == mh.dh && x.2.1 == mh.n)
                m.classical.skipped).length ≤
            1 ∧
          max m.classical.skipped.length Model.State.maxSkippedStore + Model.State.maxSkip ≤ Usize.max ∧
            m.classical.events + 1 < U32.max ∧
              m.postQuantum.epoch + 1 < U64.max ∧
                m.postQuantum.chains.length + 2 < Usize.max ∧
                  (∀ p ∈ m.postQuantum.chains, p.1 + Model.SparseRatchet.epochsKept ≤ U64.max) ∧
                    (∀ sk ∈ m.postQuantum.skipped, sk.1 + Model.SparseRatchet.epochsKept ≤ U64.max) ∧
                      (∀ (o : tacenta_session_unit.tacenta_spqr.Output),
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

/-- The premises of `SessionUnitTripleT3.receive_refines` that the table of `check-precondition-witnesses.sh` puts inside the witness hold at one state. -/
theorem sat_SessionUnitTripleT3_receive_refines : Premises.SessionUnitTripleT3.receive_refines := by
  refine ⟨SessionUnitTripleT3.ratchetAbs, SessionUnitTripleT3.spqrAbs, ⟨ratS, spqrS⟩,
    ⟨SessionUnitTripleT3.ratchetAbs ratS, SessionUnitTripleT3.spqrAbs spqrS⟩, ⟨hdr0, 0#u64, 0#u64⟩, mh0, some out0,
    ⟨rfl, rfl⟩, ⟨rfl, rfl, rfl⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [SessionUnitTripleT3.ratchetAbs, SessionUnitT3.skippedOf, skipK]
  · simp [SessionUnitTripleT3.ratchetAbs, Model.State.maxSkippedStore, Model.State.maxSkip]; scalar_tac
  · simp [SessionUnitTripleT3.ratchetAbs]; scalar_tac
  · simp [SessionUnitTripleT3.spqrAbs]; scalar_tac
  · simp [SessionUnitTripleT3.spqrAbs]; scalar_tac
  · simp [SessionUnitTripleT3.spqrAbs, Model.SparseRatchet.epochsKept, SessionUnitSpqrT3.chainsEntryOf]; scalar_tac
  · simp [SessionUnitTripleT3.spqrAbs, Model.SparseRatchet.epochsKept, SessionUnitSpqrT3.skippedOf]; scalar_tac
  · simp [Model.SparseRatchet.epochsKept]; scalar_tac
  · simp [SessionUnitTripleT3.spqrAbs, Model.SparseRatchet.maxSkip, Model.State.maxSkip]; scalar_tac
  · simp [SessionUnitTripleT3.spqrAbs, SessionUnitSpqrT3.skippedOf]
  · simp [SessionUnitTripleT3.spqrAbs, SessionUnitSpqrT3.chainsEntryOf, SessionUnitSpqrT3.chainsOf, SessionUnitSpqrT3.chainOf]; scalar_tac

abbrev Premises.SessionUnitTripleT3.receive_refines_discharged : Prop :=
  ∃ (s : tacenta_session_unit.tacenta_triple.State) (m : Model.Triple.State) (header :
    tacenta_session_unit.tacenta_triple.Header) (mh : Model.State.Header) (output :
    Option tacenta_session_unit.tacenta_spqr.Output),
    SessionUnitTripleT3.StateRefines SessionUnitTripleT3.ratchetAbs SessionUnitTripleT3.spqrAbs s m ∧
      SessionUnitTripleT3.RatchetHeaderR header.dr mh ∧
        (List.filter (fun (x : Model.State.Key × ℕ × ℕ × Model.State.Key) => x.1 == mh.dh && x.2.1 == mh.n)
                m.classical.skipped).length ≤
            1 ∧
          max m.classical.skipped.length Model.State.maxSkippedStore + Model.State.maxSkip ≤ Usize.max ∧
            m.classical.events + 1 < U32.max ∧
              m.postQuantum.epoch + 1 < U64.max ∧
                m.postQuantum.chains.length + 2 < Usize.max ∧
                  (∀ p ∈ m.postQuantum.chains, p.1 + Model.SparseRatchet.epochsKept ≤ U64.max) ∧
                    (∀ sk ∈ m.postQuantum.skipped, sk.1 + Model.SparseRatchet.epochsKept ≤ U64.max) ∧
                      (∀ (o : tacenta_session_unit.tacenta_spqr.Output),
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

/-- The premises of `SessionUnitTripleT3.receive_refines_discharged` that the table of `check-precondition-witnesses.sh` puts inside the witness hold at one state. -/
theorem sat_SessionUnitTripleT3_receive_refines_discharged : Premises.SessionUnitTripleT3.receive_refines_discharged := by
  refine ⟨⟨ratS, spqrS⟩,
    ⟨SessionUnitTripleT3.ratchetAbs ratS, SessionUnitTripleT3.spqrAbs spqrS⟩, ⟨hdr0, 0#u64, 0#u64⟩, mh0, some out0,
    ⟨rfl, rfl⟩, ⟨rfl, rfl, rfl⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [SessionUnitTripleT3.ratchetAbs, SessionUnitT3.skippedOf, skipK]
  · simp [SessionUnitTripleT3.ratchetAbs, Model.State.maxSkippedStore, Model.State.maxSkip]; scalar_tac
  · simp [SessionUnitTripleT3.ratchetAbs]; scalar_tac
  · simp [SessionUnitTripleT3.spqrAbs]; scalar_tac
  · simp [SessionUnitTripleT3.spqrAbs]; scalar_tac
  · simp [SessionUnitTripleT3.spqrAbs, Model.SparseRatchet.epochsKept, SessionUnitSpqrT3.chainsEntryOf]; scalar_tac
  · simp [SessionUnitTripleT3.spqrAbs, Model.SparseRatchet.epochsKept, SessionUnitSpqrT3.skippedOf]; scalar_tac
  · simp [Model.SparseRatchet.epochsKept]; scalar_tac
  · simp [SessionUnitTripleT3.spqrAbs, Model.SparseRatchet.maxSkip, Model.State.maxSkip]; scalar_tac
  · simp [SessionUnitTripleT3.spqrAbs, SessionUnitSpqrT3.skippedOf]
  · simp [SessionUnitTripleT3.spqrAbs, SessionUnitSpqrT3.chainsEntryOf, SessionUnitSpqrT3.chainsOf, SessionUnitSpqrT3.chainOf]; scalar_tac

abbrev Premises.SessionUnitTripleT3.send_refines : Prop :=
  ∃ (α : tacenta_session_unit.tacenta_ratchet.State → Model.State.State) (β :
    tacenta_session_unit.tacenta_spqr.State → Model.SparseRatchet.State) (s : tacenta_session_unit.tacenta_triple.State)
    (m : Model.Triple.State) (output : Option tacenta_session_unit.tacenta_spqr.Output),
    SessionUnitTripleT3.StateRefines α β s m ∧
      m.postQuantum.chains.length + 1 < Usize.max ∧
        (∀ p ∈ m.postQuantum.chains, p.1 + Model.SparseRatchet.epochsKept ≤ U64.max) ∧
          (∀ sk ∈ m.postQuantum.skipped, sk.1 + Model.SparseRatchet.epochsKept ≤ U64.max) ∧
            (∀ (o : tacenta_session_unit.tacenta_spqr.Output),
                output = some o → o.key_epoch.val + Model.SparseRatchet.epochsKept ≤ U64.max) ∧
              m.postQuantum.epoch + 1 < U64.max ∧
                ∀ p ∈ m.postQuantum.chains,
                  ∀ (ch : Model.SparseRatchet.Chain), p.2.send = some ch ∨ p.2.receive = some ch → ch.n < U64.max

/-- The premises of `SessionUnitTripleT3.send_refines` that the table of `check-precondition-witnesses.sh` puts inside the witness hold at one state. -/
theorem sat_SessionUnitTripleT3_send_refines : Premises.SessionUnitTripleT3.send_refines := by
  refine ⟨SessionUnitTripleT3.ratchetAbs, SessionUnitTripleT3.spqrAbs, ⟨ratS, spqrS⟩,
    ⟨SessionUnitTripleT3.ratchetAbs ratS, SessionUnitTripleT3.spqrAbs spqrS⟩, some out0, ⟨rfl, rfl⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [SessionUnitTripleT3.spqrAbs]; scalar_tac
  · simp [SessionUnitTripleT3.spqrAbs, Model.SparseRatchet.epochsKept, SessionUnitSpqrT3.chainsEntryOf]; scalar_tac
  · simp [SessionUnitTripleT3.spqrAbs, Model.SparseRatchet.epochsKept, SessionUnitSpqrT3.skippedOf]; scalar_tac
  · simp [Model.SparseRatchet.epochsKept]; scalar_tac
  · simp [SessionUnitTripleT3.spqrAbs]; scalar_tac
  · simp [SessionUnitTripleT3.spqrAbs, SessionUnitSpqrT3.chainsEntryOf, SessionUnitSpqrT3.chainsOf, SessionUnitSpqrT3.chainOf]; scalar_tac

abbrev Premises.SessionUnitTripleT3.send_refines_discharged : Prop :=
  ∃ (s : tacenta_session_unit.tacenta_triple.State) (m : Model.Triple.State) (output :
    Option tacenta_session_unit.tacenta_spqr.Output),
    SessionUnitTripleT3.StateRefines SessionUnitTripleT3.ratchetAbs SessionUnitTripleT3.spqrAbs s m ∧
      m.postQuantum.chains.length + 1 < Usize.max ∧
        (∀ p ∈ m.postQuantum.chains, p.1 + Model.SparseRatchet.epochsKept ≤ U64.max) ∧
          (∀ sk ∈ m.postQuantum.skipped, sk.1 + Model.SparseRatchet.epochsKept ≤ U64.max) ∧
            (∀ (o : tacenta_session_unit.tacenta_spqr.Output),
                output = some o → o.key_epoch.val + Model.SparseRatchet.epochsKept ≤ U64.max) ∧
              m.postQuantum.epoch + 1 < U64.max ∧
                ∀ p ∈ m.postQuantum.chains,
                  ∀ (ch : Model.SparseRatchet.Chain), p.2.send = some ch ∨ p.2.receive = some ch → ch.n < U64.max

/-- The premises of `SessionUnitTripleT3.send_refines_discharged` that the table of `check-precondition-witnesses.sh` puts inside the witness hold at one state. -/
theorem sat_SessionUnitTripleT3_send_refines_discharged : Premises.SessionUnitTripleT3.send_refines_discharged := by
  refine ⟨⟨ratS, spqrS⟩, ⟨SessionUnitTripleT3.ratchetAbs ratS, SessionUnitTripleT3.spqrAbs spqrS⟩, some out0, ⟨rfl, rfl⟩,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [SessionUnitTripleT3.spqrAbs]; scalar_tac
  · simp [SessionUnitTripleT3.spqrAbs, Model.SparseRatchet.epochsKept, SessionUnitSpqrT3.chainsEntryOf]; scalar_tac
  · simp [SessionUnitTripleT3.spqrAbs, Model.SparseRatchet.epochsKept, SessionUnitSpqrT3.skippedOf]; scalar_tac
  · simp [Model.SparseRatchet.epochsKept]; scalar_tac
  · simp [SessionUnitTripleT3.spqrAbs]; scalar_tac
  · simp [SessionUnitTripleT3.spqrAbs, SessionUnitSpqrT3.chainsEntryOf, SessionUnitSpqrT3.chainsOf, SessionUnitSpqrT3.chainOf]; scalar_tac

abbrev Premises.SessionUnitBraidT1.Braid.receive_no_panic : Prop :=
  ∃ (self : tacenta_session_unit.tacenta_braid.Braid),
    SessionUnitBraidT1.State.ct1_bounded self.state ∧ SessionUnitBraidT1.State.decoders_bounded self.state

/-- The premises of `SessionUnitBraidT1.Braid.receive_no_panic` that the table of `check-precondition-witnesses.sh` puts inside the witness hold at one state. -/
theorem sat_SessionUnitBraidT1_Braid_receive_no_panic : Premises.SessionUnitBraidT1.Braid.receive_no_panic :=
  ⟨braidS, by simp [Tacenta.SessionUnitBraidT1.State.ct1_bounded, Tacenta.SessionUnitBraidT1.State.decoders_bounded]⟩

abbrev Premises.SessionUnitBraidT1.Braid.step_receive_no_panic : Prop :=
  ∃ (state : tacenta_session_unit.tacenta_braid.State),
    SessionUnitBraidT1.State.ct1_bounded state ∧ SessionUnitBraidT1.State.decoders_bounded state

/-- The premises of `SessionUnitBraidT1.Braid.step_receive_no_panic` that the table of `check-precondition-witnesses.sh` puts inside the witness hold at one state. -/
theorem sat_SessionUnitBraidT1_Braid_step_receive_no_panic : Premises.SessionUnitBraidT1.Braid.step_receive_no_panic :=
  ⟨.NoHeaderReceived 1#u64 auth0 decMax, by simp [Tacenta.SessionUnitBraidT1.State.ct1_bounded,
    Tacenta.SessionUnitBraidT1.State.decoders_bounded]⟩

abbrev Premises.SessionUnitBraidT3.Braid.receive_refines : Prop :=
  ∃ (self : tacenta_session_unit.tacenta_braid.Braid),
    SessionUnitBraidT1.State.ct1_bounded self.state ∧
      SessionUnitBraidT1.State.decoders_bounded self.state ∧
        (SessionUnitBraidT1.State.epoch_val self.state).val + 1 < U64.max

/-- The premises of `SessionUnitBraidT3.Braid.receive_refines` that the table of `check-precondition-witnesses.sh` puts inside the witness hold at one state. -/
theorem sat_SessionUnitBraidT3_Braid_receive_refines : Premises.SessionUnitBraidT3.Braid.receive_refines :=
  ⟨braidS, by (simp [Tacenta.SessionUnitBraidT1.State.ct1_bounded,
      Tacenta.SessionUnitBraidT1.State.decoders_bounded,
      Tacenta.SessionUnitBraidT1.State.epoch_val]; scalar_tac)⟩

abbrev Premises.SessionUnitBraidT3.step_receive_refines : Prop :=
  ∃ (state : tacenta_session_unit.tacenta_braid.State),
    SessionUnitBraidT1.State.ct1_bounded state ∧
      SessionUnitBraidT1.State.decoders_bounded state ∧ (SessionUnitBraidT1.State.epoch_val state).val + 1 < U64.max

/-- The premises of `SessionUnitBraidT3.step_receive_refines` that the table of `check-precondition-witnesses.sh` puts inside the witness hold at one state. -/
theorem sat_SessionUnitBraidT3_step_receive_refines : Premises.SessionUnitBraidT3.step_receive_refines :=
  ⟨.NoHeaderReceived 1#u64 auth0 decMax, by (simp [Tacenta.SessionUnitBraidT1.State.ct1_bounded,
      Tacenta.SessionUnitBraidT1.State.decoders_bounded,
      Tacenta.SessionUnitBraidT1.State.epoch_val]; scalar_tac)⟩

abbrev Premises.SessionUnitBraidT3.Braid.send_refines : Prop :=
  ∃ (model : Model.Braid.BraidState), SessionUnitBraidT3.EncodersLive model

/-- The premises of `SessionUnitBraidT3.Braid.send_refines` that the table of `check-precondition-witnesses.sh` puts inside the witness hold at one state. -/
theorem sat_SessionUnitBraidT3_Braid_send_refines : Premises.SessionUnitBraidT3.Braid.send_refines :=
  ⟨modelLive, by simp [Tacenta.SessionUnitBraidT3.EncodersLive, Tacenta.SessionUnitBraidT3.EncoderOf]⟩

abbrev Premises.SessionUnitBraidT3.step_send_refines : Prop :=
  ∃ (model : Model.Braid.BraidState), SessionUnitBraidT3.EncodersLive model

/-- The premises of `SessionUnitBraidT3.step_send_refines` that the table of `check-precondition-witnesses.sh` puts inside the witness hold at one state. -/
theorem sat_SessionUnitBraidT3_step_send_refines : Premises.SessionUnitBraidT3.step_send_refines :=
  ⟨modelLive, by simp [Tacenta.SessionUnitBraidT3.EncodersLive, Tacenta.SessionUnitBraidT3.EncoderOf]⟩


/-- The sparse-ratchet state the witnesses use satisfies the decoder's invariant. -/
theorem session_unit_spqrS_inv : SessionUnitRatchetImportInv.Spqr.Inv spqrS := by
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
theorem session_unit_ratS_inv : SessionUnitRatchetImportInv.Ratchet.Inv ratS := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [tacenta_ratchet.MAX_SKIPPED_STORE]
  · simp; scalar_tac
  · intro e he; simp at he; subst he; simp
  · simp
  · simp
  · simp [SessionUnitT1.canonicalX25519]
  · intro k hk; simp at hk; subst hk; simp [SessionUnitT1.canonicalX25519]
  · intro e he; simp at he; subst he; simp [SessionUnitT1.canonicalX25519]

/-! ## The discharge theorems are not vacuous

`SessionUnitDecodedStateDischarge.lean` proves that some premises of the refinement theorems follow from the
decoder invariant `Inv` and the premises its theorems take. A discharge theorem whose own premises no state
meets would be true and empty, and the premise `Inv` is one this package adds. Each theorem below is a
discharge theorem applied to the witness state, with its type read off that application (`type_of%`), so
that it holds exactly when the theorem's premises (the state relation, the epoch step and the invariant) are
met together at that state, and it breaks if a premise is added to the discharge theorem or made
unsatisfiable. -/

theorem session_unit_spqrS_epoch_room : spqrS.epoch.val + 1 < U64.max := by simp; scalar_tac
theorem session_unit_braidS_inv : SessionUnitBraidImportInv.Braid.Inv braidS := ⟨by simp [SessionUnitBraidT1.State.ct1_bounded], by simp [SessionUnitBraidT1.State.decoders_bounded]⟩

theorem session_unit_spqr_receive_premises_at_witness :
    type_of% (SessionUnitDecodedStateDischarge.session_unit_spqr_receive_premises 0#u64 0#u64 spqrRel session_unit_spqrS_epoch_room session_unit_spqrS_inv) :=
  SessionUnitDecodedStateDischarge.session_unit_spqr_receive_premises 0#u64 0#u64 spqrRel session_unit_spqrS_epoch_room session_unit_spqrS_inv

theorem session_unit_spqr_send_premises_at_witness :
    type_of% (SessionUnitDecodedStateDischarge.session_unit_spqr_send_premises session_unit_spqrS_epoch_room session_unit_spqrS_inv) :=
  SessionUnitDecodedStateDischarge.session_unit_spqr_send_premises session_unit_spqrS_epoch_room session_unit_spqrS_inv

theorem session_unit_spqr_advance_premises_at_witness :
    type_of% (SessionUnitDecodedStateDischarge.session_unit_spqr_advance_premises session_unit_spqrS_epoch_room session_unit_spqrS_inv) :=
  SessionUnitDecodedStateDischarge.session_unit_spqr_advance_premises session_unit_spqrS_epoch_room session_unit_spqrS_inv

theorem session_unit_spqr_maybe_advance_premises_at_witness :
    type_of% (SessionUnitDecodedStateDischarge.session_unit_spqr_maybe_advance_premises session_unit_spqrS_epoch_room session_unit_spqrS_inv) :=
  SessionUnitDecodedStateDischarge.session_unit_spqr_maybe_advance_premises session_unit_spqrS_epoch_room session_unit_spqrS_inv

theorem session_unit_spqr_clear_old_epochs_premises_at_witness :
    type_of% (SessionUnitDecodedStateDischarge.session_unit_spqr_clear_old_epochs_premises session_unit_spqrS_epoch_room session_unit_spqrS_inv) :=
  SessionUnitDecodedStateDischarge.session_unit_spqr_clear_old_epochs_premises session_unit_spqrS_epoch_room session_unit_spqrS_inv

theorem session_unit_ratchet_receive_premises_at_witness :
    type_of% (SessionUnitDecodedStateDischarge.session_unit_ratchet_receive_premises ratS ratM mh0 ratRel session_unit_ratS_inv) :=
  SessionUnitDecodedStateDischarge.session_unit_ratchet_receive_premises ratS ratM mh0 ratRel session_unit_ratS_inv

theorem session_unit_braid_receive_premises_at_witness :
    type_of% (SessionUnitDecodedStateDischarge.session_unit_braid_receive_premises braidS session_unit_braidS_inv) :=
  SessionUnitDecodedStateDischarge.session_unit_braid_receive_premises braidS session_unit_braidS_inv

theorem session_unit_braid_step_receive_premises_at_witness :
    type_of% (SessionUnitDecodedStateDischarge.session_unit_braid_step_receive_premises braidS.state ⟨session_unit_braidS_inv.ct1_bounded, session_unit_braidS_inv.decoders_bounded⟩) :=
  SessionUnitDecodedStateDischarge.session_unit_braid_step_receive_premises braidS.state ⟨session_unit_braidS_inv.ct1_bounded, session_unit_braidS_inv.decoders_bounded⟩

theorem session_unit_tripleS_events_room :
    (SessionUnitTripleT3.ratchetAbs ratS).events + 1 < U32.max := by
  simp [SessionUnitTripleT3.ratchetAbs]; scalar_tac
theorem session_unit_tripleS_epoch_room :
    (SessionUnitTripleT3.spqrAbs spqrS).epoch + 1 < U64.max := by
  simp [SessionUnitTripleT3.spqrAbs]; scalar_tac

theorem triple_receive_premises_at_witness :
    type_of% (SessionUnitDecodedStateDischarge.triple_receive_premises
      (s := ⟨ratS, spqrS⟩) (m := ⟨SessionUnitTripleT3.ratchetAbs ratS, SessionUnitTripleT3.spqrAbs spqrS⟩)
      ⟨hdr0, 0#u64, 0#u64⟩ mh0 ⟨rfl, rfl⟩ session_unit_tripleS_events_room session_unit_tripleS_epoch_room
      ⟨session_unit_ratS_inv, session_unit_spqrS_inv⟩) :=
  SessionUnitDecodedStateDischarge.triple_receive_premises
      (s := ⟨ratS, spqrS⟩) (m := ⟨SessionUnitTripleT3.ratchetAbs ratS, SessionUnitTripleT3.spqrAbs spqrS⟩)
      ⟨hdr0, 0#u64, 0#u64⟩ mh0 ⟨rfl, rfl⟩ session_unit_tripleS_events_room session_unit_tripleS_epoch_room
      ⟨session_unit_ratS_inv, session_unit_spqrS_inv⟩

theorem triple_send_premises_at_witness :
    type_of% (SessionUnitDecodedStateDischarge.triple_send_premises
      (s := ⟨ratS, spqrS⟩) (m := ⟨SessionUnitTripleT3.ratchetAbs ratS, SessionUnitTripleT3.spqrAbs spqrS⟩)
      ⟨rfl, rfl⟩ session_unit_tripleS_epoch_room session_unit_spqrS_inv) :=
  SessionUnitDecodedStateDischarge.triple_send_premises
      (s := ⟨ratS, spqrS⟩) (m := ⟨SessionUnitTripleT3.ratchetAbs ratS, SessionUnitTripleT3.spqrAbs spqrS⟩)
      ⟨rfl, rfl⟩ session_unit_tripleS_epoch_room session_unit_spqrS_inv

end Tacenta.NumericWitnessSession

/--
info: 'Tacenta.NumericWitnessSession.sat_SessionUnitT1_receive_no_panic' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.NumericWitnessSession.sat_SessionUnitT1_receive_no_panic

/--
info: 'Tacenta.NumericWitnessSession.sat_SessionUnitT3_receive_refines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.NumericWitnessSession.sat_SessionUnitT3_receive_refines

/--
info: 'Tacenta.NumericWitnessSession.sat_SessionUnitRatchetImportInv_Ratchet_decoded_receive_refines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.NumericWitnessSession.sat_SessionUnitRatchetImportInv_Ratchet_decoded_receive_refines

/--
info: 'Tacenta.NumericWitnessSession.sat_SessionUnitSpqrT1_receive_no_panic' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.NumericWitnessSession.sat_SessionUnitSpqrT1_receive_no_panic

/--
info: 'Tacenta.NumericWitnessSession.sat_SessionUnitSpqrT1_send_no_panic' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.NumericWitnessSession.sat_SessionUnitSpqrT1_send_no_panic

/--
info: 'Tacenta.NumericWitnessSession.sat_SessionUnitSpqrT3_receive_refines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.NumericWitnessSession.sat_SessionUnitSpqrT3_receive_refines

/--
info: 'Tacenta.NumericWitnessSession.sat_SessionUnitSpqrT3_send_refines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.NumericWitnessSession.sat_SessionUnitSpqrT3_send_refines

/--
info: 'Tacenta.NumericWitnessSession.sat_SessionUnitTripleT1_State_receive_no_panic' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.NumericWitnessSession.sat_SessionUnitTripleT1_State_receive_no_panic

/--
info: 'Tacenta.NumericWitnessSession.sat_SessionUnitTripleT1_State_send_no_panic' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.NumericWitnessSession.sat_SessionUnitTripleT1_State_send_no_panic

/--
info: 'Tacenta.NumericWitnessSession.sat_SessionUnitTripleT3_receive_refines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.NumericWitnessSession.sat_SessionUnitTripleT3_receive_refines

/--
info: 'Tacenta.NumericWitnessSession.sat_SessionUnitTripleT3_receive_refines_discharged' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.NumericWitnessSession.sat_SessionUnitTripleT3_receive_refines_discharged

/--
info: 'Tacenta.NumericWitnessSession.sat_SessionUnitTripleT3_send_refines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.NumericWitnessSession.sat_SessionUnitTripleT3_send_refines

/--
info: 'Tacenta.NumericWitnessSession.sat_SessionUnitTripleT3_send_refines_discharged' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.NumericWitnessSession.sat_SessionUnitTripleT3_send_refines_discharged

/--
info: 'Tacenta.NumericWitnessSession.sat_SessionUnitBraidT1_Braid_receive_no_panic' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kem.EncapsState,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair]
-/
#guard_msgs in
#print axioms Tacenta.NumericWitnessSession.sat_SessionUnitBraidT1_Braid_receive_no_panic

/--
info: 'Tacenta.NumericWitnessSession.sat_SessionUnitBraidT1_Braid_step_receive_no_panic' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kem.EncapsState,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair]
-/
#guard_msgs in
#print axioms Tacenta.NumericWitnessSession.sat_SessionUnitBraidT1_Braid_step_receive_no_panic

/--
info: 'Tacenta.NumericWitnessSession.sat_SessionUnitBraidT3_Braid_receive_refines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kem.EncapsState,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair]
-/
#guard_msgs in
#print axioms Tacenta.NumericWitnessSession.sat_SessionUnitBraidT3_Braid_receive_refines

/--
info: 'Tacenta.NumericWitnessSession.sat_SessionUnitBraidT3_step_receive_refines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kem.EncapsState,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair]
-/
#guard_msgs in
#print axioms Tacenta.NumericWitnessSession.sat_SessionUnitBraidT3_step_receive_refines

/--
info: 'Tacenta.NumericWitnessSession.sat_SessionUnitBraidT3_Braid_send_refines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.NumericWitnessSession.sat_SessionUnitBraidT3_Braid_send_refines

/--
info: 'Tacenta.NumericWitnessSession.sat_SessionUnitBraidT3_step_send_refines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.NumericWitnessSession.sat_SessionUnitBraidT3_step_send_refines

/--
info: 'Tacenta.NumericWitnessSession.session_unit_spqrS_inv' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.NumericWitnessSession.session_unit_spqrS_inv

/--
info: 'Tacenta.NumericWitnessSession.session_unit_ratS_inv' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.NumericWitnessSession.session_unit_ratS_inv

/--
info: 'Tacenta.NumericWitnessSession.session_unit_spqr_receive_premises_at_witness' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.NumericWitnessSession.session_unit_spqr_receive_premises_at_witness

/--
info: 'Tacenta.NumericWitnessSession.session_unit_spqr_send_premises_at_witness' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.NumericWitnessSession.session_unit_spqr_send_premises_at_witness

/--
info: 'Tacenta.NumericWitnessSession.session_unit_spqr_advance_premises_at_witness' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.NumericWitnessSession.session_unit_spqr_advance_premises_at_witness

/--
info: 'Tacenta.NumericWitnessSession.session_unit_spqr_maybe_advance_premises_at_witness' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.NumericWitnessSession.session_unit_spqr_maybe_advance_premises_at_witness

/--
info: 'Tacenta.NumericWitnessSession.session_unit_spqr_clear_old_epochs_premises_at_witness' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.NumericWitnessSession.session_unit_spqr_clear_old_epochs_premises_at_witness

/--
info: 'Tacenta.NumericWitnessSession.session_unit_ratchet_receive_premises_at_witness' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.NumericWitnessSession.session_unit_ratchet_receive_premises_at_witness

/--
info: 'Tacenta.NumericWitnessSession.session_unit_braid_receive_premises_at_witness' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kem.EncapsState,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair]
-/
#guard_msgs in
#print axioms Tacenta.NumericWitnessSession.session_unit_braid_receive_premises_at_witness

/--
info: 'Tacenta.NumericWitnessSession.session_unit_braid_step_receive_premises_at_witness' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kem.EncapsState,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair]
-/
#guard_msgs in
#print axioms Tacenta.NumericWitnessSession.session_unit_braid_step_receive_premises_at_witness

/--
info: 'Tacenta.NumericWitnessSession.triple_receive_premises_at_witness' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.NumericWitnessSession.triple_receive_premises_at_witness

/--
info: 'Tacenta.NumericWitnessSession.triple_send_premises_at_witness' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.NumericWitnessSession.triple_send_premises_at_witness
