import Translation.UnitErasureRsDefs
import Translation.UnitErasureRsKernel
import Translation.UnitErasureRsAlgebra
import Translation.UnitErasureRsEncoder
import Translation.UnitErasureRsDecoder
import Translation.UnitErasureRsModel
import Translation.UnitSatisfiabilityErasureAgrees
import Translation.UnitSatisfiabilityBraidAgreements

/-!
# The nine statements of the Reed-Solomon proof of the unit's `ErasureAgrees`

The decoder half of `SessionUnitBraidT3.ErasureAgrees` is cut into nine statements, fixed before
their proofs and proved independently:

* kernels: `K_weights`, `K_coefficients`, `K_evaluate` (`UnitErasureRsKernel.lean`: the translated
  `weights`, `coefficients` and `evaluate` compute their pure specifications) and `K_algebra`
  (`UnitErasureRsAlgebra.lean`: the Lagrange evaluation they compute is the model's interpolant);
* encoder: `E_new`, `E_next` (`UnitErasureRsEncoder.lean`);
* decoder: `D_add`, `D_message` (`UnitErasureRsDecoder.lean`);
* recovery: `M_recover` (`UnitErasureRsModel.lean`).

Here each statement is written out again and proved by the theorem of that module, so the kernel
checks that each proved theorem has exactly the statement its consumers (the encoder and decoder
modules for the four kernel statements, `UnitErasureRsGlue.lean` for all nine) were written
against.  This module proves nothing new.

## What it does not show

* The hypotheses are the proved theorems' hypotheses: `E_new` takes `DivCeilValue`, a law about
  `usize::div_ceil`, and `D_message` takes `TruncatePrefix`, a law about `Vec::truncate`.  Neither
  law is proved here.
* Anything beyond the kernel's three axioms and the two opaque constants the laws are about.  The
  axiom footprint of each statement is that of its proof, and the model's field and polynomial
  lemmas are kernel proofs, so none of the nine carries a compiler-trust axiom.
-/

open Aeneas Aeneas.Std Result
open tacenta_session_unit.tacenta_erasure

namespace Tacenta.UnitErasureRs

/-! ## The kernels -/

theorem K_weights (s : Slice Std.U16) :
    weights s ⦃ w => w.val.map eps = weightsSpec (s.val.map eps) ⦄ :=
  Kernel.K_weights s

theorem K_coefficients (s sw : Slice Std.U16) (x : Std.U16) :
    coefficients s sw x ⦃ c => c.val.map eps = coeffSpec (s.val.map eps) (sw.val.map eps) (eps x) ⦄ :=
  Kernel.K_coefficients s sw x

theorem K_evaluate (s sv : Slice Std.U16) :
    evaluate s sv ⦃ r => eps r = evalSpec (s.val.map eps) (sv.val.map eps) ⦄ :=
  Kernel.K_evaluate s sv

theorem K_algebra (xs ys : List E) (x : E) (hnd : xs.Nodup) (hl : ys.length = xs.length) :
    evalSpec (coeffSpec xs (weightsSpec xs) x) ys = Model.Polynomial.interp (xs.zip ys) x :=
  Algebra.K_algebra xs ys x hnd hl

/-! ## The encoder, the decoder and recovery -/

theorem E_new (hdiv : Tacenta.SessionUnitDecoderBound.DivCeilValue) (s : Slice Std.U8) :
    Encoder.new s ⦃ e => e.next = 0#u16 ∧ e.exhausted = false ∧
      storeBytes e.chunks = (Model.Erasure.chunks (Tacenta.SessionUnitBraidT3.sliceOf s)).take 65536 ⦄ :=
  Encoder.E_new hdiv s

theorem E_next (e : Encoder) (hne : e.exhausted = false) (hlen : e.chunks.val.length ≤ 65536) :
    Encoder.next_chunk e ⦃ r => ∀ ch, r.1 = some ch →
      cbytes ch = Model.Erasure.codeword (storeBytes e.chunks) e.next.val ⦄ :=
  Encoder.E_next e hne hlen

theorem D_add (d : Decoder) (c : Chunk) :
    Decoder.add_chunk d c ⦃ r =>
      haveHeld r.2 = (Model.Erasure.Decoder.add ⟨d.size.val, d.needed.val, haveHeld d⟩
        (c.index.val, cbytes c)).held ∧ r.2.size = d.size ∧ r.2.needed = d.needed ∧
      (r.1 = true ↔ r.2.«have».val.length ≠ d.«have».val.length) ⦄ :=
  Decoder.D_add d c

theorem D_message (htr : Tacenta.UnitSatisfiabilityBraidAgreements.TruncatePrefix) (d : Decoder)
    (hwf : DWf d) :
    Decoder.message d ⦃ r =>
      r.map vbytes = Model.Erasure.Decoder.message ⟨d.size.val, d.needed.val, haveHeld d⟩ ⦄ :=
  Decoder.D_message htr d hwf

theorem M_recover (m : List UInt8) (hk : Model.Erasure.chunkCount m.length ≤ 65536)
    (idxs : List ℕ) (hnd : idxs.Nodup) (hlt : ∀ i ∈ idxs, i < 65536)
    (hlen : idxs.length = Model.Erasure.chunkCount m.length) :
    Model.Erasure.Decoder.message
      ⟨m.length, Model.Erasure.chunkCount m.length,
        idxs.map (fun i => (i, Model.Erasure.codeword (Model.Erasure.chunks m) i))⟩ = some m :=
  Recovery.M_recover m hk idxs hnd hlt hlen

end Tacenta.UnitErasureRs

/--
info: 'Tacenta.UnitErasureRs.K_weights' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitErasureRs.K_weights

/--
info: 'Tacenta.UnitErasureRs.K_coefficients' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitErasureRs.K_coefficients

/--
info: 'Tacenta.UnitErasureRs.K_evaluate' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitErasureRs.K_evaluate

/--
info: 'Tacenta.UnitErasureRs.K_algebra' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitErasureRs.K_algebra

/--
info: 'Tacenta.UnitErasureRs.E_new' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.core.num.Usize.div_ceil]
-/
#guard_msgs in
#print axioms Tacenta.UnitErasureRs.E_new

/--
info: 'Tacenta.UnitErasureRs.E_next' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitErasureRs.E_next

/--
info: 'Tacenta.UnitErasureRs.D_add' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitErasureRs.D_add

/--
info: 'Tacenta.UnitErasureRs.D_message' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.alloc.vec.Vec.truncate]
-/
#guard_msgs in
#print axioms Tacenta.UnitErasureRs.D_message

/--
info: 'Tacenta.UnitErasureRs.M_recover' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitErasureRs.M_recover

/--
info: Tacenta.UnitErasureRs.K_weights (s : Slice U16) :
  weights s ⦃ w =>
    List.map Tacenta.UnitErasureRs.eps ↑w = Tacenta.UnitErasureRs.weightsSpec (List.map Tacenta.UnitErasureRs.eps ↑s) ⦄
-/
#guard_msgs in
#check Tacenta.UnitErasureRs.K_weights

/--
info: Tacenta.UnitErasureRs.K_coefficients (s sw : Slice U16) (x : U16) :
  coefficients s sw x ⦃ c =>
    List.map Tacenta.UnitErasureRs.eps ↑c =
      Tacenta.UnitErasureRs.coeffSpec (List.map Tacenta.UnitErasureRs.eps ↑s) (List.map Tacenta.UnitErasureRs.eps ↑sw)
        (Tacenta.UnitErasureRs.eps x) ⦄
-/
#guard_msgs in
#check Tacenta.UnitErasureRs.K_coefficients

/--
info: Tacenta.UnitErasureRs.K_evaluate (s sv : Slice U16) :
  evaluate s sv ⦃ r =>
    Tacenta.UnitErasureRs.eps r =
      Tacenta.UnitErasureRs.evalSpec (List.map Tacenta.UnitErasureRs.eps ↑s) (List.map Tacenta.UnitErasureRs.eps ↑sv) ⦄
-/
#guard_msgs in
#check Tacenta.UnitErasureRs.K_evaluate

/--
info: Tacenta.UnitErasureRs.K_algebra (xs ys : List Tacenta.UnitErasureRs.E) (x : Tacenta.UnitErasureRs.E) (hnd : xs.Nodup)
  (hl : ys.length = xs.length) :
  Tacenta.UnitErasureRs.evalSpec (Tacenta.UnitErasureRs.coeffSpec xs (Tacenta.UnitErasureRs.weightsSpec xs) x) ys =
    Model.Polynomial.interp (xs.zip ys) x
-/
#guard_msgs in
#check Tacenta.UnitErasureRs.K_algebra

/--
info: Tacenta.UnitErasureRs.E_new (hdiv : Tacenta.SessionUnitDecoderBound.DivCeilValue) (s : Slice U8) :
  Encoder.new s ⦃ e =>
    e.next = 0#u16 ∧
      e.exhausted = false ∧
        Tacenta.UnitErasureRs.storeBytes e.chunks =
          List.take 65536 (Model.Erasure.chunks (Tacenta.SessionUnitBraidT3.sliceOf s)) ⦄
-/
#guard_msgs in
#check Tacenta.UnitErasureRs.E_new

/--
info: Tacenta.UnitErasureRs.E_next (e : Encoder) (hne : e.exhausted = false) (hlen : (↑e.chunks).length ≤ 65536) :
  e.next_chunk ⦃ r =>
    ∀ (ch : Chunk),
      r.1 = some ch →
        Tacenta.UnitErasureRs.cbytes ch = Model.Erasure.codeword (Tacenta.UnitErasureRs.storeBytes e.chunks) ↑e.next ⦄
-/
#guard_msgs in
#check Tacenta.UnitErasureRs.E_next

/--
info: Tacenta.UnitErasureRs.D_add (d : Decoder) (c : Chunk) :
  d.add_chunk c ⦃ r =>
    Tacenta.UnitErasureRs.haveHeld r.2 =
        ({ size := ↑d.size, needed := ↑d.needed, held := Tacenta.UnitErasureRs.haveHeld d }.add
            (↑c.index, Tacenta.UnitErasureRs.cbytes c)).held ∧
      r.2.size = d.size ∧ r.2.needed = d.needed ∧ (r.1 = true ↔ (↑r.2.have).length ≠ (↑d.have).length) ⦄
-/
#guard_msgs in
#check Tacenta.UnitErasureRs.D_add

/--
info: Tacenta.UnitErasureRs.D_message (htr : Tacenta.UnitSatisfiabilityBraidAgreements.TruncatePrefix) (d : Decoder)
  (hwf : Tacenta.UnitErasureRs.DWf d) :
  d.message ⦃ r =>
    Option.map Tacenta.UnitErasureRs.vbytes r =
      { size := ↑d.size, needed := ↑d.needed, held := Tacenta.UnitErasureRs.haveHeld d }.message ⦄
-/
#guard_msgs in
#check Tacenta.UnitErasureRs.D_message

/--
info: Tacenta.UnitErasureRs.M_recover (m : List UInt8) (hk : Model.Erasure.chunkCount m.length ≤ 65536) (idxs : List ℕ)
  (hnd : idxs.Nodup) (hlt : ∀ i ∈ idxs, i < 65536) (hlen : idxs.length = Model.Erasure.chunkCount m.length) :
  { size := m.length, needed := Model.Erasure.chunkCount m.length,
        held := List.map (fun i => (i, Model.Erasure.codeword (Model.Erasure.chunks m) i)) idxs }.message =
    some m
-/
#guard_msgs in
#check Tacenta.UnitErasureRs.M_recover
