import Translation.UnitT1
import Translation.UnitSpqrT1

/-!
# The three-leaf unit's axiom pins

`Translation/UnitT1.lean` and `Translation/UnitSpqrT1.lean` are the leaf
panic-freedom proofs restated about the three-leaf translation unit, generated
by `tacenta-proofs/scripts/port-unit-proofs.sh`. Their `#print axioms` pins are
here rather than in the generated files, because a pin's expected text is
Lean's pretty-printer's output and reproducing its line breaking with a textual
substitution would be guesswork. Written once, by hand, against what the
compiler actually prints.

**What these pins are for.** Not to record a new trust base -- to state that
there is no new trust base. Each theorem below must depend on exactly the
axioms its leaf twin depends on, name for name, with `tacenta_triple_unit.`
in front of every translated one and nothing else changed. That is the claim
the port rests on: compiling the three crates as one changes which constants
the theorems are about and changes nothing about what they assume.

It is worth saying what would show up here if the port were wrong. An axiom
that appears in the unit's list and not the leaf's would mean the unit reaches
a boundary the leaf does not, and the two are then not translations of the same
Rust. One that disappears would mean the unit's translation of some operation
is a definition where the leaf's is an opaque external, which is exactly what
the unit does for the *Triple's* calls into its leaves -- but must not do
inside a leaf, where nothing changed. And a `_native` axiom appearing where the
leaf had none would mean a proof that was kernel-only became
compiler-trusted. `#guard_msgs` refuses each of these at build time.

The sparse ratchet's `receive_no_panic` carries a `native_decide` axiom in the
leaf as well; `LIMITATIONS.md` records why, under "The proofs are trusted by
evaluation, not only by the kernel". It is the one entry below that is not
kernel-only, and it is not kernel-only in the leaf either.
-/

/--
info: 'Tacenta.UnitT1.kdf_ck_no_panic' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_triple_unit.tacenta_kdf.hmac_sha256]
-/
#guard_msgs in
#print axioms Tacenta.UnitT1.kdf_ck_no_panic

/--
info: 'Tacenta.UnitT1.send_no_panic' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_triple_unit.tacenta_kdf.hmac_sha256]
-/
#guard_msgs in
#print axioms Tacenta.UnitT1.send_no_panic

/--
info: 'Tacenta.UnitT1.receive_no_panic' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_triple_unit.tacenta_kdf.hkdf_sha256,
 tacenta_triple_unit.tacenta_kdf.hmac_sha256,
 tacenta_triple_unit.zeroize.Zeroizing,
 tacenta_triple_unit.zeroize.Zeroizing.new,
 tacenta_triple_unit.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_triple_unit.Pair.Insts.ZeroizeZeroize.zeroize,
 tacenta_triple_unit.alloc.vec.Vec.remove,
 tacenta_triple_unit.zeroize.Zeroize.Blanket.zeroize,
 tacenta_triple_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 tacenta_triple_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 tacenta_triple_unit.alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize]
-/
#guard_msgs in
#print axioms Tacenta.UnitT1.receive_no_panic

/--
info: 'Tacenta.UnitSpqrT1.receive_no_panic' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_triple_unit.tacenta_kdf.hkdf_sha256,
 tacenta_triple_unit.zeroize.Zeroizing,
 tacenta_triple_unit.zeroize.Zeroizing.new,
 tacenta_triple_unit.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_triple_unit.alloc.vec.Vec.append,
 tacenta_triple_unit.alloc.vec.Vec.remove,
 tacenta_triple_unit.alloc.vec.Vec.retain,
 tacenta_triple_unit.zeroize.Zeroize.Blanket.zeroize,
 Tacenta.UnitSpqrT1.receive_no_panic._native.native_decide.ax_1_1,
 tacenta_triple_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 tacenta_triple_unit.core.option.Option.Insts.CoreCloneClone.clone]
-/
#guard_msgs in
#print axioms Tacenta.UnitSpqrT1.receive_no_panic
