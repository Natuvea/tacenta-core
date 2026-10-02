import Translation.UnitT1
import Translation.UnitSpqrT1
import Translation.UnitSpqrT3
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

The sparse ratchet's `receive_no_panic` carries no compiler-trust axiom, in the
leaf or in the unit. Until 2026-09-30 it carried a `native_decide` axiom for one
closed numeric fact (that `(1 : U64)` has value one), which `decide` now
settles; `LIMITATIONS.md` records it under "The proofs are trusted by
evaluation, not only by the kernel". No panic-freedom pin below lists a
compiler-trust axiom. The sparse ratchet's refinements and the Triple's
discharged refinements do carry such axioms, each stated where it is pinned.
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
 tacenta_triple_unit.alloc.vec.Vec.pop,
 tacenta_triple_unit.zeroize.Zeroize.Blanket.zeroize,
 tacenta_triple_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 tacenta_triple_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 tacenta_triple_unit.alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize]
-/
#guard_msgs in
#print axioms Tacenta.UnitT1.receive_no_panic

/--
info: 'Tacenta.UnitSpqrT1.send_no_panic' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_triple_unit.tacenta_kdf.hkdf_sha256,
 tacenta_triple_unit.zeroize.Zeroizing,
 tacenta_triple_unit.zeroize.Zeroizing.new,
 tacenta_triple_unit.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_triple_unit.Pair.Insts.ZeroizeZeroize.zeroize,
 tacenta_triple_unit.alloc.vec.Vec.capacity,
 tacenta_triple_unit.alloc.vec.Vec.pop,
 tacenta_triple_unit.core.option.Option.as_mut,
 tacenta_triple_unit.zeroize.Zeroize.Blanket.zeroize,
 tacenta_triple_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 tacenta_triple_unit.alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 tacenta_triple_unit.core.option.Option.Insts.CoreCloneClone.clone]
-/
#guard_msgs in
#print axioms Tacenta.UnitSpqrT1.send_no_panic

/--
info: 'Tacenta.UnitSpqrT1.receive_no_panic' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_triple_unit.tacenta_kdf.hkdf_sha256,
 tacenta_triple_unit.zeroize.Zeroizing,
 tacenta_triple_unit.zeroize.Zeroizing.new,
 tacenta_triple_unit.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_triple_unit.Pair.Insts.ZeroizeZeroize.zeroize,
 tacenta_triple_unit.alloc.vec.Vec.capacity,
 tacenta_triple_unit.alloc.vec.Vec.pop,
 tacenta_triple_unit.core.option.Option.as_mut,
 tacenta_triple_unit.zeroize.Zeroize.Blanket.zeroize,
 tacenta_triple_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 tacenta_triple_unit.alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 tacenta_triple_unit.core.option.Option.Insts.CoreCloneClone.clone]
-/
#guard_msgs in
#print axioms Tacenta.UnitSpqrT1.receive_no_panic

/-!
## The Triple's own theorems on the unit

`Translation/UnitTripleT1.lean` is a different kind of file from the two
above. It is not generated, and its pins are not claims that nothing changed:
its whole point is that the seventeen `*Total` bundles the standalone
`TripleT1.lean` assumed are theorems here, so the trust base *does* change, and these pins are where
that change is recorded rather than described.

**Report it, because the trust base changes.**
The standalone `Tacenta.TripleT1.State.receive_no_panic`, deleted after
2a89a7f, depended on twelve axioms. The ported theorem below depends on
seventeen axioms, and none is a compiler-trust axiom: the one closed numeric fact in the
sparse ratchet's own `receive_no_panic` proof (that `(1 : U64)` has value one) was settled
by `native_decide` until 2026-09-30 and is now settled by `decide`, so the Lean
compiler's evaluation is no longer trusted for it (`LIMITATIONS.md`, "The proofs
are trusted by evaluation, not only by the kernel").

Both halves belong in the same sentence. The standalone theorem had fewer axioms
because it *assumed* the sparse ratchet's receive is total instead of proving it.
The ported one proves that part, and the boundary axioms that proving it needs
are the extra. Which is the better trade is the reader's to judge; what is not
open to judgement is that the axiom count went from twelve to seventeen.

Six axioms go and eleven arrive. What goes is the bare operation axioms --
`tacenta_ratchet.State`, `tacenta_ratchet.receive`, `tacenta_spqr.State`,
`tacenta_spqr.State.receive` and the two states' clones, six constants standing
for "this call returns, because we say so".

All eleven that arrive are a substitution rather than an addition in kind: KDF,
`zeroize`, `Vec` and `Option` boundary axioms that other proofs in this tree
already carry. They are `hmac_sha256` beside the `hkdf_sha256` that was already
there; `zeroize.Zeroizing` with its constructor and its two projections;
`Vec.capacity` and `Vec.pop`; `Option`'s `as_mut`; the `Zeroize` instances for
`Pair` and `Vec`; and `Option`'s clone. `Array`'s `Zeroize` instance and the blanket one are on both
sides and arrive nowhere.

`send` is the quieter case: twelve axioms before (measured on 2026-09-10) and
sixteen after, none of them compiler-trusted. Six go and ten arrive, the same
substitution as for `receive` without `Zeroizing`'s mutable projection.
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
 tacenta_triple_unit.Pair.Insts.ZeroizeZeroize.zeroize,
 tacenta_triple_unit.alloc.vec.Vec.capacity,
 tacenta_triple_unit.alloc.vec.Vec.pop,
 tacenta_triple_unit.core.option.Option.as_mut,
 tacenta_triple_unit.zeroize.Zeroize.Blanket.zeroize,
 tacenta_triple_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 tacenta_triple_unit.alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
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
 tacenta_triple_unit.alloc.vec.Vec.capacity,
 tacenta_triple_unit.alloc.vec.Vec.pop,
 tacenta_triple_unit.core.option.Option.as_mut,
 tacenta_triple_unit.zeroize.Zeroize.Blanket.zeroize,
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

/-! The three accessors `TripleT1.lean` listed as unproved. Each is kernel-only,
with no boundary axiom at all: the inner operation each wraps was opaque there
and is a definition here, so what was a missing assumption becomes a one-liner. -/

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
 tacenta_triple_unit.alloc.vec.Vec.pop,
 tacenta_triple_unit.zeroize.Zeroize.Blanket.zeroize,
 tacenta_triple_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 tacenta_triple_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 tacenta_triple_unit.alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize]
-/
#guard_msgs in
#print axioms Tacenta.UnitT3.receive_refines

/--
info: 'Tacenta.UnitT3.receive_store_full_refines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_triple_unit.tacenta_kdf.hkdf_sha256,
 tacenta_triple_unit.tacenta_kdf.hmac_sha256,
 tacenta_triple_unit.zeroize.Zeroizing,
 tacenta_triple_unit.zeroize.Zeroizing.new,
 tacenta_triple_unit.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_triple_unit.Pair.Insts.ZeroizeZeroize.zeroize,
 tacenta_triple_unit.alloc.vec.Vec.pop,
 tacenta_triple_unit.zeroize.Zeroize.Blanket.zeroize,
 tacenta_triple_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 tacenta_triple_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 tacenta_triple_unit.alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize]
-/
#guard_msgs in
#print axioms Tacenta.UnitT3.receive_store_full_refines

/--
info: Tacenta.UnitT3.receive_store_full_refines : Tacenta.UnitT3.HmacAgrees →
  Tacenta.UnitT3.HkdfAgrees →
    Tacenta.UnitT3.ZeroizingRoundTrips →
      Tacenta.UnitT1.RemoveSkippedAtTotal →
        ∀ [Tacenta.UnitT1.DerivedKeysModel] (s : tacenta_triple_unit.tacenta_ratchet.State) (m : Model.State.State),
          Tacenta.UnitT3.StateR s m →
            ∀ (hdr : tacenta_triple_unit.tacenta_ratchet.Header) (mh : Model.State.Header),
              Tacenta.UnitT3.HeaderR hdr mh →
                ∀ (dh_out_recv dh_out_send new_dhs_pub : Aeneas.Std.Array Aeneas.Std.U8 32#usize),
                  (List.filter (Tacenta.UnitT3.matchesHeader mh) m.skipped).length ≤ 1 →
                    max (↑s.skipped).length ↑tacenta_triple_unit.tacenta_ratchet.MAX_SKIPPED_STORE +
                          ↑tacenta_triple_unit.tacenta_ratchet.MAX_SKIP ≤
                        Aeneas.Std.Usize.max →
                      ↑s.events + 1 < Aeneas.Std.U32.max →
                        Aeneas.Std.WP.spec
                          (tacenta_triple_unit.tacenta_ratchet.receive s hdr dh_out_recv dh_out_send new_dhs_pub)
                          fun r =>
                          r.1 =
                              Aeneas.Std.core.result.Result.Err
                                tacenta_triple_unit.tacenta_ratchet.RatchetError.SkippedStoreFull →
                            Model.Ratchet.receiveDetailed m mh (Tacenta.UnitT3.keyOf dh_out_recv)
                                (Tacenta.UnitT3.keyOf dh_out_send) (Tacenta.UnitT3.keyOf new_dhs_pub) =
                              Except.error Model.Ratchet.ReceiveRefusal.skippedStoreFull
-/
#guard_msgs in
#check @Tacenta.UnitT3.receive_store_full_refines

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

/-! ## The sparse ratchet's refinement, restated about the unit

`Translation/UnitSpqrT3.lean` is `SpqrT3.lean` generated onto the three-leaf
unit. The two theorems `SpqrT3.lean` pins are pinned here, and each prints
exactly the axioms its leaf twin prints, name for name: `tacenta_triple_unit.`
in front of every translated axiom, and each `native_decide` axiom under the
unit's copy of the lemma that carries it in the leaf. Nothing else changed. -/

/--
info: 'Tacenta.UnitSpqrT3.send_refines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_triple_unit.tacenta_kdf.hkdf_sha256,
 tacenta_triple_unit.zeroize.Zeroizing,
 tacenta_triple_unit.zeroize.Zeroizing.new,
 tacenta_triple_unit.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_triple_unit.Pair.Insts.ZeroizeZeroize.zeroize,
 tacenta_triple_unit.alloc.vec.Vec.capacity,
 tacenta_triple_unit.alloc.vec.Vec.pop,
 tacenta_triple_unit.core.option.Option.as_mut,
 tacenta_triple_unit.zeroize.Zeroize.Blanket.zeroize,
 Tacenta.UnitSpqrT3.chain_label_agrees._native.native_decide.ax_1_1,
 Tacenta.UnitSpqrT3.protocol_info_agrees._native.native_decide.ax_1_1,
 Tacenta.UnitSpqrT3.root_label_agrees._native.native_decide.ax_1_1,
 tacenta_triple_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 tacenta_triple_unit.alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 tacenta_triple_unit.core.option.Option.Insts.CoreCloneClone.clone]
-/
#guard_msgs in
#print axioms Tacenta.UnitSpqrT3.send_refines

/--
info: 'Tacenta.UnitSpqrT3.receive_refines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_triple_unit.tacenta_kdf.hkdf_sha256,
 tacenta_triple_unit.zeroize.Zeroizing,
 tacenta_triple_unit.zeroize.Zeroizing.new,
 tacenta_triple_unit.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_triple_unit.Pair.Insts.ZeroizeZeroize.zeroize,
 tacenta_triple_unit.alloc.vec.Vec.capacity,
 tacenta_triple_unit.alloc.vec.Vec.pop,
 tacenta_triple_unit.core.option.Option.as_mut,
 tacenta_triple_unit.zeroize.Zeroize.Blanket.zeroize,
 Tacenta.UnitSpqrT3.chain_label_agrees._native.native_decide.ax_1_1,
 Tacenta.UnitSpqrT3.max_skip_agrees._native.native_decide.ax_1_1,
 Tacenta.UnitSpqrT3.max_skip_val._native.native_decide.ax_1_1,
 Tacenta.UnitSpqrT3.max_skipped_store_agrees._native.native_decide.ax_1_1,
 Tacenta.UnitSpqrT3.protocol_info_agrees._native.native_decide.ax_1_1,
 Tacenta.UnitSpqrT3.receive_refines_continuation._native.native_decide.ax_1_29,
 Tacenta.UnitSpqrT3.root_label_agrees._native.native_decide.ax_1_1,
 tacenta_triple_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 tacenta_triple_unit.alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 tacenta_triple_unit.core.option.Option.Insts.CoreCloneClone.clone]
-/
#guard_msgs in
#print axioms Tacenta.UnitSpqrT3.receive_refines

/--
info: 'Tacenta.UnitSpqrT3.receive_store_full_refines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_triple_unit.tacenta_kdf.hkdf_sha256,
 tacenta_triple_unit.zeroize.Zeroizing,
 tacenta_triple_unit.zeroize.Zeroizing.new,
 tacenta_triple_unit.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_triple_unit.Pair.Insts.ZeroizeZeroize.zeroize,
 tacenta_triple_unit.alloc.vec.Vec.capacity,
 tacenta_triple_unit.alloc.vec.Vec.pop,
 tacenta_triple_unit.core.option.Option.as_mut,
 tacenta_triple_unit.zeroize.Zeroize.Blanket.zeroize,
 Tacenta.UnitSpqrT3.chain_label_agrees._native.native_decide.ax_1_1,
 Tacenta.UnitSpqrT3.max_skip_agrees._native.native_decide.ax_1_1,
 Tacenta.UnitSpqrT3.max_skip_val._native.native_decide.ax_1_1,
 Tacenta.UnitSpqrT3.max_skipped_store_agrees._native.native_decide.ax_1_1,
 Tacenta.UnitSpqrT3.protocol_info_agrees._native.native_decide.ax_1_1,
 Tacenta.UnitSpqrT3.receive_refines_continuation._native.native_decide.ax_1_29,
 Tacenta.UnitSpqrT3.root_label_agrees._native.native_decide.ax_1_1,
 tacenta_triple_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 tacenta_triple_unit.alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 tacenta_triple_unit.core.option.Option.Insts.CoreCloneClone.clone]
-/
#guard_msgs in
#print axioms Tacenta.UnitSpqrT3.receive_store_full_refines

/--
info: Tacenta.UnitSpqrT3.receive_store_full_refines : Tacenta.UnitSpqrT3.SpqrHkdfAgrees →
  Tacenta.UnitSpqrT3.ZeroizingRoundTrips96 →
    Tacenta.UnitSpqrT3.ZeroizingRoundTrips64 →
      Tacenta.UnitSpqrT3.VecRetainAgrees →
        Tacenta.UnitSpqrT1.VecRetainTotal →
          Tacenta.UnitSpqrT3.RemoveSkippedAtAgrees →
            Tacenta.UnitSpqrT1.ZeroizeTotal →
              Tacenta.UnitSpqrT1.OptionCloneTotal →
                ∀ {s : tacenta_triple_unit.tacenta_spqr.State} {m : Model.SparseRatchet.State},
                  Tacenta.UnitSpqrT3.StateRefines s m →
                    ∀ (receiving_epoch : Aeneas.Std.U64) (out : Option tacenta_triple_unit.tacenta_spqr.Output)
                      (n : Aeneas.Std.U64),
                      ↑s.epoch + 1 < Aeneas.Std.U64.max →
                        (↑s.chains).length + 2 < Aeneas.Std.Usize.max →
                          (∀ p ∈ ↑s.chains, ↑p.1 + Model.SparseRatchet.epochsKept ≤ Aeneas.Std.U64.max) →
                            (∀ sk ∈ ↑s.skipped, ↑sk.epoch + Model.SparseRatchet.epochsKept ≤ Aeneas.Std.U64.max) →
                              (∀ (o : tacenta_triple_unit.tacenta_spqr.Output),
                                  out = some o → ↑o.key_epoch + Model.SparseRatchet.epochsKept ≤ Aeneas.Std.U64.max) →
                                (↑s.skipped).length + ↑tacenta_triple_unit.tacenta_spqr.MAX_SKIP ≤
                                    Aeneas.Std.Usize.max →
                                  (List.filter (fun x => x.1 == ↑receiving_epoch && x.2.1 == ↑n) m.skipped).length ≤ 1 →
                                    (∀ p ∈ ↑s.chains,
                                        ∀ (ch : tacenta_triple_unit.tacenta_spqr.Chain),
                                          p.2.send = some ch ∨ p.2.receive = some ch → ↑ch.n < Aeneas.Std.U64.max) →
                                      Aeneas.Std.WP.spec (s.receive receiving_epoch out n) fun r =>
                                        r.1 =
                                            Aeneas.Std.core.result.Result.Err
                                              tacenta_triple_unit.tacenta_spqr.SpqrError.SkippedStoreFull →
                                          Model.SparseRatchet.receiveDetailed m (↑receiving_epoch)
                                              (Option.map Tacenta.UnitSpqrT3.outputOf out) ↑n =
                                            Except.error Model.SparseRatchet.ReceiveRefusal.skippedStoreFull
-/
#guard_msgs in
#check @Tacenta.UnitSpqrT3.receive_store_full_refines

/-! ## The Triple's refinement on the unit, with both bundles discharged

`Translation/UnitTripleT3.lean` proves the Triple's refinement on the unit,
including the two bundles the standalone `TripleT3.lean` had to assume. These four are the theorems that change
what is assumed: the two bundle proofs, and `send_refines` and `receive_refines`
with both bundles discharged. Unlike the pins above they have no leaf twin to
match, since no other file states such theorems, so they record a new trust
base rather than hold one to an old one. Against the standalone
`TripleT3.send_refines`, measured before its deletion, the sixteen opaque
inner-crate declarations it rested on are absent, but that is the
unit's doing: `UnitTripleT3.send_refines`, with the bundles still as hypotheses,
already rests on none of them. What discharging adds is the eight
`native_decide` axioms `UnitSpqrT3.lean` carries; `LIMITATIONS.md` says what
that trade is. -/

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
 tacenta_triple_unit.alloc.vec.Vec.pop,
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
 tacenta_triple_unit.Pair.Insts.ZeroizeZeroize.zeroize,
 tacenta_triple_unit.alloc.vec.Vec.capacity,
 tacenta_triple_unit.alloc.vec.Vec.pop,
 tacenta_triple_unit.core.option.Option.as_mut,
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
 tacenta_triple_unit.alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
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
 tacenta_triple_unit.alloc.vec.Vec.capacity,
 tacenta_triple_unit.alloc.vec.Vec.pop,
 tacenta_triple_unit.core.option.Option.as_mut,
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
 tacenta_triple_unit.alloc.vec.Vec.capacity,
 tacenta_triple_unit.alloc.vec.Vec.pop,
 tacenta_triple_unit.core.option.Option.as_mut,
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

/--
info: 'Tacenta.UnitTripleT3.receive_store_full_refines_discharged' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_triple_unit.tacenta_kdf.hkdf_sha256,
 tacenta_triple_unit.tacenta_kdf.hmac_sha256,
 tacenta_triple_unit.zeroize.Zeroizing,
 tacenta_triple_unit.zeroize.Zeroizing.new,
 tacenta_triple_unit.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_triple_unit.Pair.Insts.ZeroizeZeroize.zeroize,
 tacenta_triple_unit.alloc.vec.Vec.capacity,
 tacenta_triple_unit.alloc.vec.Vec.pop,
 tacenta_triple_unit.core.option.Option.as_mut,
 tacenta_triple_unit.zeroize.Zeroize.Blanket.zeroize,
 Tacenta.UnitSpqrT3.chain_label_agrees._native.native_decide.ax_1_1,
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
#print axioms Tacenta.UnitTripleT3.receive_store_full_refines_discharged

/--
info: Tacenta.UnitTripleT3.receive_store_full_refines_discharged : Tacenta.UnitT3.HmacAgrees →
  Tacenta.UnitT3.HkdfAgrees →
    Tacenta.UnitT3.ZeroizingRoundTrips →
      Tacenta.UnitT1.RemoveSkippedAtTotal →
        ∀ [Tacenta.UnitT1.DerivedKeysModel],
          Tacenta.UnitSpqrT3.ZeroizingRoundTrips96 →
            Tacenta.UnitSpqrT3.ZeroizingRoundTrips64 →
              Tacenta.UnitSpqrT3.VecRetainAgrees →
                Tacenta.UnitSpqrT1.VecRetainTotal →
                  Tacenta.UnitSpqrT3.RemoveSkippedAtAgrees →
                    Tacenta.UnitSpqrT1.ZeroizeTotal →
                      Tacenta.UnitSpqrT1.OptionCloneTotal →
                        ∀ {s : tacenta_triple_unit.tacenta_triple.State} {m : Model.Triple.State},
                          Tacenta.UnitTripleT3.StateRefines Tacenta.UnitTripleT3.ratchetAbs Tacenta.UnitTripleT3.spqrAbs
                              s m →
                            ∀ (header : tacenta_triple_unit.tacenta_triple.Header) (mh : Model.State.Header),
                              Tacenta.UnitTripleT3.RatchetHeaderR header.dr mh →
                                ∀ (dh_out_recv dh_out_send new_dhs_pub : Aeneas.Std.Array Aeneas.Std.U8 32#usize)
                                  (output : Option tacenta_triple_unit.tacenta_spqr.Output),
                                  (List.filter (fun x => x.1 == mh.dh && x.2.1 == mh.n) m.classical.skipped).length ≤
                                      1 →
                                    max m.classical.skipped.length Model.State.maxSkippedStore + Model.State.maxSkip ≤
                                        Aeneas.Std.Usize.max →
                                      m.classical.events + 1 < Aeneas.Std.U32.max →
                                        m.postQuantum.epoch + 1 < Aeneas.Std.U64.max →
                                          m.postQuantum.chains.length + 2 < Aeneas.Std.Usize.max →
                                            (∀ p ∈ m.postQuantum.chains,
                                                p.1 + Model.SparseRatchet.epochsKept ≤ Aeneas.Std.U64.max) →
                                              (∀ sk ∈ m.postQuantum.skipped,
                                                  sk.1 + Model.SparseRatchet.epochsKept ≤ Aeneas.Std.U64.max) →
                                                (∀ (o : tacenta_triple_unit.tacenta_spqr.Output),
                                                    output = some o →
                                                      ↑o.key_epoch + Model.SparseRatchet.epochsKept ≤
                                                        Aeneas.Std.U64.max) →
                                                  m.postQuantum.skipped.length + Model.SparseRatchet.maxSkip ≤
                                                      Aeneas.Std.Usize.max →
                                                    (List.filter
                                                            (fun x => x.1 == ↑header.epoch && x.2.1 == ↑header.pq_n)
                                                            m.postQuantum.skipped).length ≤
                                                        1 →
                                                      (∀ p ∈ m.postQuantum.chains,
                                                          ∀ (ch : Model.SparseRatchet.Chain),
                                                            p.2.send = some ch ∨ p.2.receive = some ch →
                                                              ch.n < Aeneas.Std.U64.max) →
                                                        Aeneas.Std.WP.spec
                                                          (s.receive header dh_out_recv dh_out_send new_dhs_pub output)
                                                          fun result =>
                                                          ∀
                                                            (realReason :
                                                              tacenta_triple_unit.tacenta_triple.TripleError)
                                                            (modelReason : Model.Triple.ReceiveRefusal),
                                                            result = Aeneas.Std.core.result.Result.Err realReason →
                                                              Tacenta.UnitTripleT3.receiveStoreFullRefusalOfReal
                                                                    realReason =
                                                                  some modelReason →
                                                                Model.Triple.receiveDetailed m
                                                                    { dr := mh, epoch := ↑header.epoch,
                                                                      pqN := ↑header.pq_n }
                                                                    (Tacenta.UnitTripleT3.keyOf dh_out_recv)
                                                                    (Tacenta.UnitTripleT3.keyOf dh_out_send)
                                                                    (Tacenta.UnitTripleT3.keyOf new_dhs_pub)
                                                                    (Option.map Tacenta.UnitTripleT3.spqrOutputOf
                                                                      output) =
                                                                  Except.error modelReason
-/
#guard_msgs in
#check @Tacenta.UnitTripleT3.receive_store_full_refines_discharged
