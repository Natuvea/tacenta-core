import Model.Erasure
import Model.Polynomial
import Translation.SessionUnitBraidT3
import Translation.TacentaSessionUnit

/-!
# The Reed-Solomon proof of the unit's `ErasureAgrees`: shared definitions

`SessionUnitBraidT3.ErasureAgrees` is, in the complete Session unit, a statement about the
translated erasure coder.  Its encoder half is `UnitSatisfiabilityErasureAgrees.erasureAgrees_encoder`.
The decoder half needs the coder's arithmetic: the Reed-Solomon decode of codewords of a message is
the message.

This module holds only definitions: the pure specification functions of the coder's kernels and
the view of a chunk, a chunk store and a decoder as model bytes.  It proves nothing.  The proof
that uses them is cut into nine statements, collected in `UnitErasureRsStatements.lean`:

* kernels (`UnitErasureRsKernel.lean`, `UnitErasureRsAlgebra.lean`): the translated `gf`,
  `weights`, `coefficients`, `evaluate` compute `weightsSpec`, `coeffSpec`, `evalSpec` over
  `Model.Gf65536.Elem`; and `evalSpec (coeffSpec xs (weightsSpec xs) x) ys` is
  `Model.Polynomial.interp (xs.zip ys) x` for distinct nodes.
* encoder (`UnitErasureRsEncoder.lean`): `Encoder::new` builds the padded chunks of
  `Model.Erasure.chunks`; `next_chunk` emits `Model.Erasure.codeword` at index `next`.
* decoder (`UnitErasureRsDecoder.lean`): `add_chunk` refines `Model.Erasure.Decoder.add`;
  `message` refines `Model.Erasure.Decoder.message`.
* recovery (`UnitErasureRsModel.lean`): `Model.Erasure.Decoder.message` of the codewords of `m`
  at distinct indices is `m`.
* `UnitErasureRsGlue.lean`: the simulation of `Model.Braid`'s decoder by the translated decoder,
  and `ErasureAgrees`.
-/

open Aeneas Aeneas.Std Result
open tacenta_session_unit.tacenta_erasure

namespace Tacenta.UnitErasureRs

abbrev E := Model.Gf65536.Elem

/-- A translated field element as a model element. -/
def eps (x : Std.U16) : E := x.bv

/-- The bytes of a translated byte vector, as model bytes. -/
def vbytes (v : alloc.vec.Vec Std.U8) : List UInt8 := v.val.map Tacenta.SessionUnitBraidT3.u8

/-- The 32 bytes of a chunk. -/
def cbytes (c : Chunk) : List UInt8 := c.data.val.map Tacenta.SessionUnitBraidT3.u8

/-- The chunk store of an encoder, as bytes. -/
def storeBytes (v : alloc.vec.Vec (Array Std.U8 32#usize)) : List (List UInt8) :=
  v.val.map (fun a => a.val.map Tacenta.SessionUnitBraidT3.u8)

/-- The held codewords of a decoder, as the model's `(index, bytes)` pairs. -/
def haveHeld (d : Decoder) : List (ℕ × List UInt8) :=
  d.«have».val.map (fun c => (c.index.val, cbytes c))

/-! ## The pure specification functions of the kernels -/

/-- The product, in index order, of `f j` over the positions `j < n` other than `i`. -/
def prodNe (f : ℕ → E) (n i : ℕ) : E :=
  (List.range n).foldl (fun acc j => if j = i then acc else Model.Gf65536.mul acc (f j))
    Model.Gf65536.one

/-- `weights`: `w_i = inv (Π_{j ≠ i} (x_i + x_j))`. -/
def weightsSpec (xs : List E) : List E :=
  (List.range xs.length).map fun i =>
    Model.Gf65536.inv (prodNe (fun j => Model.Gf65536.add (xs.getD i 0#16) (xs.getD j 0#16))
      xs.length i)

/-- `coefficients`: `c_i = w_i * Π_{j ≠ i} (x + x_j)`, where a missing weight is `0`. -/
def coeffSpec (xs ws : List E) (x : E) : List E :=
  (List.range xs.length).map fun i =>
    Model.Gf65536.mul (ws.getD i 0#16)
      (prodNe (fun j => Model.Gf65536.add x (xs.getD j 0#16)) xs.length i)

/-- `evaluate`: `Σ_i c_i * v_i` over as many terms as both lists carry, added in order. -/
def evalSpec (cs vs : List E) : E :=
  (List.zipWith Model.Gf65536.mul cs vs).foldl Model.Gf65536.add Model.Gf65536.zero

/-- The decoder invariant a reachable decoder keeps: at most `needed` codewords, distinct
indices, and `needed` within `MAX_CODEWORDS`. -/
def DWf (d : Decoder) : Prop :=
  (d.«have».val.map (fun c => c.index.val)).Nodup ∧ d.«have».val.length ≤ d.needed.val ∧
  d.needed.val ≤ 65536

end Tacenta.UnitErasureRs
