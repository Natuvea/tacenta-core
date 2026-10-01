import Translation.BraidT1

/-!
# `BraidT1.ArrayZeroizeTotal` is stronger than the crate

`BraidT1.ArrayZeroizeTotal` says that `Array::zeroize` returns for every instance record
`inst : Zeroize U8`, including one whose `zeroize` fails. The real function calls `inst.zeroize` on
each element and propagates a failure, so for a failing instance the statement is false of the
crate. `Satisfiability.lean` shows the hypothesis is satisfiable (an identity wipe), so it does not
make the Braid theorems that take it empty; this module shows it cannot be satisfied by a wipe that
propagates the failure of a failing instance (`braid_arrayZeroizeTotal_conflicts`), so it is stronger
than the code supports. The leaf proofs apply it only through `BraidT1.array_zeroize_spec`, at the
`Blanket U8` instance, whose element wipe returns. This module changes no hypothesis and no theorem; the sparse
ratchet's `SpqrT1.ZeroizeTotal` and the three-leaf unit's `UnitSpqrT1.ZeroizeTotal` have the same
result in `SatisfiabilitySpqrLaws.lean` and `UnitSatisfiabilityTripleLaws.lean`, and the session
unit's three fields in `UnitSatisfiabilityZeroizeScope.lean`.

`PropagatesFailureBraid` is an assumption about the real `Array::zeroize`, tested against the real
function only by reading.
-/

open Aeneas Aeneas.Std Result ControlFlow Error

noncomputable section

namespace Tacenta.SatisfiabilityBraidZeroize

open tacenta_braid

/-- What the real `Array::zeroize` does with a failing element: it calls `inst.zeroize` on each
element and propagates the failure. -/
def PropagatesFailureBraid : Prop :=
  ∀ (inst : zeroize.Zeroize U8) (a : Std.Array U8 1#usize) (x : U8), a.val = [x] →
    inst.zeroize x = fail Error.panic →
    Array.Insts.ZeroizeZeroize.zeroize inst a = fail Error.panic

/-- `BraidT1.ArrayZeroizeTotal` quantifies over every `Zeroize U8` record, so it cannot hold of a
wipe that propagates the failure of a failing record. -/
theorem braid_arrayZeroizeTotal_conflicts (h : Tacenta.BraidT1.ArrayZeroizeTotal)
    (hp : PropagatesFailureBraid) : False := by
  obtain ⟨r, hr⟩ := h 1#usize ⟨fun _ => fail Error.panic⟩ ⟨[0#u8], rfl⟩
  have := hp ⟨fun _ => fail Error.panic⟩ ⟨[0#u8], rfl⟩ 0#u8 rfl rfl
  rw [this] at hr
  cases hr

end Tacenta.SatisfiabilityBraidZeroize

end

/--
info: 'Tacenta.SatisfiabilityBraidZeroize.braid_arrayZeroizeTotal_conflicts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_braid.Array.Insts.ZeroizeZeroize.zeroize]
-/
#guard_msgs in
#print axioms Tacenta.SatisfiabilityBraidZeroize.braid_arrayZeroizeTotal_conflicts

/--
info: Tacenta.SatisfiabilityBraidZeroize.braid_arrayZeroizeTotal_conflicts (h : Tacenta.BraidT1.ArrayZeroizeTotal)
  (hp : Tacenta.SatisfiabilityBraidZeroize.PropagatesFailureBraid) : False
-/
#guard_msgs in
#check Tacenta.SatisfiabilityBraidZeroize.braid_arrayZeroizeTotal_conflicts

/--
info: def Tacenta.SatisfiabilityBraidZeroize.PropagatesFailureBraid : Prop :=
∀ (inst : tacenta_braid.zeroize.Zeroize U8) (a : Std.Array U8 1#usize) (x : U8),
  ↑a = [x] →
    inst.zeroize x = fail Error.panic → tacenta_braid.Array.Insts.ZeroizeZeroize.zeroize inst a = fail Error.panic
-/
#guard_msgs in
#print Tacenta.SatisfiabilityBraidZeroize.PropagatesFailureBraid
