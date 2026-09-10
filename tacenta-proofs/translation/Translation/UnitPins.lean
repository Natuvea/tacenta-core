import Translation.UnitT1
import Translation.UnitSpqrT1
import Translation.UnitT3
import Translation.UnitTripleT1
import Translation.UnitTripleT3

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
in front of every translated one and nothing else changed. That is a statement
about the printed lists: a leaf file opens its crate's namespace, so its pins
print a translated axiom without the crate's own prefix (`tacenta_kdf.hmac_sha256`
for what is fully `tacenta_ratchet.tacenta_kdf.hmac_sha256`). That is the claim
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

/-!
## The Triple's own theorems on the unit

`Translation/UnitTripleT1.lean` is a different kind of file from the two
above. It is not generated, and its pins are not claims that nothing changed:
its whole point is that the seventeen `*Total` bundles `TripleT1.lean` assumes
are theorems here, so the trust base *does* change, and these pins are where
that change is recorded rather than described.

**Report it honestly, because one half of it is a regression.**
`Tacenta.TripleT1.State.receive_no_panic` depends on twelve axioms and is
kernel-only. The ported theorem below depends on eighteen and is **not**
kernel-only: it inherits
`Tacenta.UnitSpqrT1.receive_no_panic._native.native_decide.ax_1_1`, the one
compiler-trusted numeric fact the sparse ratchet's own `receive` proof rests
on (`LIMITATIONS.md`, "The proofs are trusted by evaluation, not only by the
kernel").

Both halves belong in the same sentence. The current theorem is kernel-only
because it *assumes* the sparse ratchet's receive is total instead of proving
it -- its kernel-only status is bought by assuming the hard part. The ported
one proves that part, and inherits the one compiler-trusted fact proving it
rests on. Which is the better trade is the reader's to judge; what is not
open to judgement is that the axiom count went from twelve to eighteen and
that a kernel-only proof stopped being kernel-only.

Six axioms go and twelve arrive. What goes is the bare operation axioms --
`tacenta_ratchet.State`, `tacenta_ratchet.receive`, `tacenta_spqr.State`,
`tacenta_spqr.State.receive` and the two states' clones, six constants standing
for "this call returns, because we say so".

Eleven of the twelve that arrive are a substitution rather than an addition in
kind: KDF, `zeroize` and `Vec` boundary axioms that other proofs in this tree
already carry. They are `hmac_sha256` beside the `hkdf_sha256` that was already
there; `zeroize.Zeroizing` with its constructor and its two projections;
`Vec.append`, `Vec.remove` and `Vec.retain`; the `Zeroize` instances for `Pair`
and `Vec`; and `Option`'s clone. `Array`'s `Zeroize` instance and the blanket
one are on both sides and arrive nowhere; naming them here would repeat the
miscount this paragraph was rewritten to fix.

The twelfth is the `native_decide` axiom named above. It is neither a boundary
axiom nor shared with the rest of the tree, and it is the whole of the
regression. Counting it among the others would be the kind of summary that
contradicts its own evidence.

`send` is the quieter case: twelve axioms before and twelve after, kernel-only
on both sides, with the same substitution underneath.
-/

/--
info: 'Tacenta.UnitTripleT1.State.send_no_panic' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_triple_unit.tacenta_kdf.hkdf_sha256,
 tacenta_triple_unit.tacenta_kdf.hmac_sha256,
 tacenta_triple_unit.zeroize.Zeroizing,
 tacenta_triple_unit.zeroize.Zeroizing.new,
 tacenta_triple_unit.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_triple_unit.alloc.vec.Vec.retain,
 tacenta_triple_unit.zeroize.Zeroize.Blanket.zeroize,
 tacenta_triple_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 tacenta_triple_unit.core.option.Option.Insts.CoreCloneClone.clone]
-/
#guard_msgs in
#print axioms Tacenta.UnitTripleT1.State.send_no_panic

/--
info: 'Tacenta.UnitTripleT1.State.receive_no_panic' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_triple_unit.tacenta_kdf.hkdf_sha256,
 tacenta_triple_unit.tacenta_kdf.hmac_sha256,
 tacenta_triple_unit.zeroize.Zeroizing,
 tacenta_triple_unit.zeroize.Zeroizing.new,
 tacenta_triple_unit.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_triple_unit.Pair.Insts.ZeroizeZeroize.zeroize,
 tacenta_triple_unit.alloc.vec.Vec.append,
 tacenta_triple_unit.alloc.vec.Vec.remove,
 tacenta_triple_unit.alloc.vec.Vec.retain,
 tacenta_triple_unit.zeroize.Zeroize.Blanket.zeroize,
 Tacenta.UnitSpqrT1.receive_no_panic._native.native_decide.ax_1_1,
 tacenta_triple_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 tacenta_triple_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 tacenta_triple_unit.alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 tacenta_triple_unit.core.option.Option.Insts.CoreCloneClone.clone]
-/
#guard_msgs in
#print axioms Tacenta.UnitTripleT1.State.receive_no_panic

/-! The clone, which is what carries the three preconditions from `self` to the
`candidate` the body calls into. One axiom beyond Lean's three: `Option`'s
clone, the only field-wise clone the unit does not define. -/

/--
info: 'Tacenta.UnitTripleT1.State.clone_no_panic' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_triple_unit.core.option.Option.Insts.CoreCloneClone.clone]
-/
#guard_msgs in
#print axioms Tacenta.UnitTripleT1.State.clone_no_panic

/-! The three accessors `TripleT1.lean` lists as unproved. Each is kernel-only,
with no boundary axiom at all: the inner operation each wraps is opaque there
and a definition here, so what was a missing assumption becomes a one-liner. -/

/--
info: 'Tacenta.UnitTripleT1.State.classical_skipped_len_no_panic' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitTripleT1.State.classical_skipped_len_no_panic

/--
info: 'Tacenta.UnitTripleT1.State.post_quantum_skipped_len_no_panic' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitTripleT1.State.post_quantum_skipped_len_no_panic

/--
info: 'Tacenta.UnitTripleT1.State.post_quantum_receive_count_no_panic' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitTripleT1.State.post_quantum_receive_count_no_panic

/-! ## The classical ratchet's refinement, restated about the unit

`Translation/UnitT3.lean` is `T3.lean` generated onto the three-leaf unit by
`scripts/port-unit-proofs.sh`. The three theorems `T3.lean` pins are pinned
here. Each prints exactly the axioms its leaf twin prints, name for name, with
`tacenta_triple_unit.` in front of every translated axiom and nothing else
changed. `send_refines` wraps onto several lines here where the leaf's fits on
one, only because the longer names push it past the pretty-printer's width. -/

/--
info: 'Tacenta.UnitT3.send_refines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_triple_unit.tacenta_kdf.hmac_sha256]
-/
#guard_msgs in
#print axioms Tacenta.UnitT3.send_refines

/--
info: 'Tacenta.UnitT3.receive_refines' depends on axioms: [propext,
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
#print axioms Tacenta.UnitT3.receive_refines

/--
info: 'Tacenta.UnitT3.message_keys_refines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_triple_unit.tacenta_kdf.hkdf_sha256,
 tacenta_triple_unit.zeroize.Zeroizing,
 tacenta_triple_unit.zeroize.Zeroizing.new,
 tacenta_triple_unit.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_triple_unit.zeroize.Zeroize.Blanket.zeroize,
 tacenta_triple_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref]
-/
#guard_msgs in
#print axioms Tacenta.UnitT3.message_keys_refines

/-! ## The Triple's refinement on the unit, with both bundles discharged

`Translation/UnitTripleT3.lean` restates `TripleT3.lean` about the unit and proves
the two bundles that file has to assume. These four are the theorems that change
what is assumed: the two bundle proofs, and `send_refines` and `receive_refines`
with both bundles discharged. Unlike the pins above they have no leaf twin to
match, since `TripleT3.lean` states no such theorems, so they record a new trust
base rather than hold one to an old one. Against `TripleT3.send_refines`, the
sixteen opaque inner-crate declarations it rests on are absent, and the eight
`native_decide` axioms `UnitSpqrT3.lean` carries are present; `LIMITATIONS.md`
says what that trade is. -/

/--
info: 'Tacenta.UnitTripleT3.ratchet_agrees_for' depends on axioms: [propext,
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
 tacenta_triple_unit.alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 tacenta_triple_unit.core.option.Option.Insts.CoreCloneClone.clone]
-/
#guard_msgs in
#print axioms Tacenta.UnitTripleT3.ratchet_agrees_for

/--
info: 'Tacenta.UnitTripleT3.spqr_agrees_for' depends on axioms: [propext,
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
 Tacenta.UnitSpqrT3.chain_label_agrees._native.native_decide.ax_1_1,
 Tacenta.UnitSpqrT3.chain_start_agrees._native.native_decide.ax_1_1,
 Tacenta.UnitSpqrT3.max_skip_agrees._native.native_decide.ax_1_1,
 Tacenta.UnitSpqrT3.max_skip_val._native.native_decide.ax_1_1,
 Tacenta.UnitSpqrT3.max_skipped_store_agrees._native.native_decide.ax_1_1,
 Tacenta.UnitSpqrT3.protocol_info_agrees._native.native_decide.ax_1_1,
 Tacenta.UnitSpqrT3.receive_refines_continuation._native.native_decide.ax_1_29,
 Tacenta.UnitSpqrT3.root_label_agrees._native.native_decide.ax_1_1,
 tacenta_triple_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 tacenta_triple_unit.core.option.Option.Insts.CoreCloneClone.clone]
-/
#guard_msgs in
#print axioms Tacenta.UnitTripleT3.spqr_agrees_for

/--
info: 'Tacenta.UnitTripleT3.send_refines_discharged' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_triple_unit.tacenta_kdf.hkdf_sha256,
 tacenta_triple_unit.tacenta_kdf.hmac_sha256,
 tacenta_triple_unit.zeroize.Zeroizing,
 tacenta_triple_unit.zeroize.Zeroizing.new,
 tacenta_triple_unit.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_triple_unit.Pair.Insts.ZeroizeZeroize.zeroize,
 tacenta_triple_unit.alloc.vec.Vec.append,
 tacenta_triple_unit.alloc.vec.Vec.remove,
 tacenta_triple_unit.alloc.vec.Vec.retain,
 tacenta_triple_unit.zeroize.Zeroize.Blanket.zeroize,
 Tacenta.UnitSpqrT3.chain_label_agrees._native.native_decide.ax_1_1,
 Tacenta.UnitSpqrT3.chain_start_agrees._native.native_decide.ax_1_1,
 Tacenta.UnitSpqrT3.max_skip_agrees._native.native_decide.ax_1_1,
 Tacenta.UnitSpqrT3.max_skip_val._native.native_decide.ax_1_1,
 Tacenta.UnitSpqrT3.max_skipped_store_agrees._native.native_decide.ax_1_1,
 Tacenta.UnitSpqrT3.protocol_info_agrees._native.native_decide.ax_1_1,
 Tacenta.UnitSpqrT3.receive_refines_continuation._native.native_decide.ax_1_29,
 Tacenta.UnitSpqrT3.root_label_agrees._native.native_decide.ax_1_1,
 Tacenta.UnitTripleT3.combine_info_agrees._native.native_decide.ax_1_1,
 tacenta_triple_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 tacenta_triple_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 tacenta_triple_unit.alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 tacenta_triple_unit.core.option.Option.Insts.CoreCloneClone.clone]
-/
#guard_msgs in
#print axioms Tacenta.UnitTripleT3.send_refines_discharged

/--
info: 'Tacenta.UnitTripleT3.receive_refines_discharged' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_triple_unit.tacenta_kdf.hkdf_sha256,
 tacenta_triple_unit.tacenta_kdf.hmac_sha256,
 tacenta_triple_unit.zeroize.Zeroizing,
 tacenta_triple_unit.zeroize.Zeroizing.new,
 tacenta_triple_unit.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_triple_unit.Pair.Insts.ZeroizeZeroize.zeroize,
 tacenta_triple_unit.alloc.vec.Vec.append,
 tacenta_triple_unit.alloc.vec.Vec.remove,
 tacenta_triple_unit.alloc.vec.Vec.retain,
 tacenta_triple_unit.zeroize.Zeroize.Blanket.zeroize,
 Tacenta.UnitSpqrT3.chain_label_agrees._native.native_decide.ax_1_1,
 Tacenta.UnitSpqrT3.chain_start_agrees._native.native_decide.ax_1_1,
 Tacenta.UnitSpqrT3.max_skip_agrees._native.native_decide.ax_1_1,
 Tacenta.UnitSpqrT3.max_skip_val._native.native_decide.ax_1_1,
 Tacenta.UnitSpqrT3.max_skipped_store_agrees._native.native_decide.ax_1_1,
 Tacenta.UnitSpqrT3.protocol_info_agrees._native.native_decide.ax_1_1,
 Tacenta.UnitSpqrT3.receive_refines_continuation._native.native_decide.ax_1_29,
 Tacenta.UnitSpqrT3.root_label_agrees._native.native_decide.ax_1_1,
 Tacenta.UnitTripleT3.combine_info_agrees._native.native_decide.ax_1_1,
 tacenta_triple_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 tacenta_triple_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 tacenta_triple_unit.alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 tacenta_triple_unit.core.option.Option.Insts.CoreCloneClone.clone]
-/
#guard_msgs in
#print axioms Tacenta.UnitTripleT3.receive_refines_discharged
