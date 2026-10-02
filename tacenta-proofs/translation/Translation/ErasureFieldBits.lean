import Model.Gf65536

/-!
# The partial forms of the field's two loops, as bitvector facts

`ErasureT3.lean` relates the translated erasure crate's field arithmetic to `Model.Gf65536`. Its loops
carry a partial result, and the model writes a finished one, so each loop needs the partial form named:
`clmulUpto` is the carry-less product accumulated over the low `n` bits, and `reduceUpto` is the reduction
after `n` folds. Their closing lemmas, at sixteen bits and at sixteen folds, are statements about
`BitVec` and the model alone. They live here, in their own module, so that the proof about the standalone
crate (`ErasureT3.lean`) and the proof about the Session unit's copy of it (`UnitErasureRsKernel.lean`) use the
same declarations without either module importing the other's generated translation: the unit re-declares the
standalone crate's generated names, and a module of one must not enter the environment of the other's audit.
The declarations keep the namespace `Tacenta.ErasureT3` they were written in.
-/

namespace Tacenta.ErasureT3

/-- The product accumulated over the low `n` bits.

The loop carries a partial result and the model writes a finished one, so
neither can be rewritten into the other directly. This names the partial form,
so the loop has an invariant to preserve and the model has something to be the
sixteenth case of. -/
def clmulUpto (b : BitVec 16) (x : BitVec 32) : Nat → BitVec 32
  | 0 => 0#32
  | n + 1 =>
    clmulUpto b x n ^^^ (if (b >>> n) &&& 1#16 == 1#16 then x <<< n else 0#32)

/-- One more bit. Stated so the loop's invariant can step without unfolding the
whole recursion, which does not terminate under `simp`. -/
theorem clmulUpto_succ (b : BitVec 16) (x : BitVec 32) (n : Nat) :
    clmulUpto b x (n + 1)
      = clmulUpto b x n ^^^ (if (b >>> n) &&& 1#16 == 1#16 then x <<< n else 0#32) :=
  rfl

/-- Sixteen bits in, the partial form is the model's. Sixteen unfoldings on one
side and none on the other: the two are the same exclusive or of the same sixteen
conditional terms, so unfolding both and simplifying settles it. -/
theorem clmulUpto_sixteen (a b : BitVec 16) :
    clmulUpto b (a.zeroExtend 32) 16 = Model.Gf65536.clmul a b := by
  simp only [clmulUpto, Model.Gf65536.clmul]
  simp

/-- The reduction applied at bits thirty-one down to `32 - n`, which is `n`
folds. Counting folds rather than bit positions is what keeps the recursion
going the same way the model's `let` chain does, while the loop goes the other
way. -/
def reduceUpto (v : BitVec 32) : Nat → BitVec 32
  | 0 => v
  | n + 1 => Model.Gf65536.redAt (reduceUpto v n) (31 - n)

/-- One more fold. Same purpose as `clmulUpto_succ`: a step the loop can take
without the definition reaching a simp set. -/
theorem reduceUpto_succ (v : BitVec 32) (n : Nat) :
    reduceUpto v (n + 1) = Model.Gf65536.redAt (reduceUpto v n) (31 - n) := rfl

/-- Sixteen folds in, truncated, the partial form is the model's reduction. -/
theorem reduceUpto_sixteen (v : BitVec 32) :
    (reduceUpto v 16).truncate 16 = Model.Gf65536.reduce v := rfl

end Tacenta.ErasureT3
