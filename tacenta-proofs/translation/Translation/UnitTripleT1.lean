import Translation.TacentaTripleUnit
import Translation.UnitT1
import Translation.UnitSpqrT1

/-!
# T1 for the Triple Ratchet, restated about the three-leaf translation unit

This is `Translation/TripleT1.lean` restated about
`Translation/TacentaTripleUnit.lean` -- the translation of
`tacenta-core/triple-unit`, where the Triple Ratchet and both inner ratchets
compile as one crate. The difference that matters is not the names. In
`TripleT1.lean` every operation on `tacenta_ratchet.State` or
`tacenta_spqr.State` is an opaque external, so that file **assumes**
seventeen `*Total : Prop` bundles about them. Here those operations are real
definitions, and the leaves' own panic-freedom proofs
(`Translation/UnitT1.lean`, `Translation/UnitSpqrT1.lean`) are about exactly
these constants. So the seventeen bundles are declared here and then
**proved**, and the theorems ported from `TripleT1.lean` take the leaves'
boundary hypotheses instead.

## This does not replace `TripleT1.lean`, and both files exist

`Translation/TripleT3.lean` and `Translation/SatisfiabilityTriple.lean` depend
on `TripleT1.lean`'s definitions, and they live in the other island: the
unit's translation cannot share a Lean environment with the leaves' (the
instances collide), which is why `Translation/AxiomAuditTripleUnit.lean` is a
separate audit module. Deleting `TripleT1.lean` would take those two files
with it. This is **duplication, not replacement**, and `LIMITATIONS.md` says
so under "The three-leaf translation unit".

## Why the generator cannot write this file

`scripts/port-unit-proofs.sh` derives `UnitT1.lean` and `UnitSpqrT1.lean` from
their leaves by rewriting the import, the namespace and the `open`, and
copying every proof body unchanged. Its premise is that the leaf proofs never
write a translated name in qualified form. That premise fails here:
`TripleT1.lean` writes forty-nine qualified `tacenta_ratchet.*` and
`tacenta_spqr.*` occurrences (fifty-nine counting `tacenta_kdf.` and
`zeroize.`). Under `open tacenta_triple_unit` those prefixes
happen to resolve correctly anyway, but the proof bodies genuinely change,
which is the harder half:

* about twenty `@[step]` rules from the two leaf files are newly in scope, so
  several bodies need *pruning* rather than substitution -- `combine`'s and
  `split_secret`'s explicit HKDF steps become "no goals to be solved" because
  `UnitT1.hkdf_step` now fires on its own;
* `tacenta_spqr.State.epoch` is `tacenta_spqr.State.impl.epoch` here (only
  `TacentaTriple.lean`'s axiom uses the unprefixed form, which on the unit
  would resolve to the structure field);
* three of `TripleT1.lean`'s boundary copies collapse into the leaves'
  (`HkdfSha256Total` and `ZeroizingTotal` are `rfl`-equal to `UnitT1.HkdfTotal`
  and `UnitT1.ZeroizingTotal`; its `ZeroizeTotal` is a narrowing of
  `UnitSpqrT1.ZeroizeTotal` at one instance, which has to be written out at
  every use), and its two `@[step]` `zeroize.Zeroizing` helpers are duplicates
  of `UnitT1`'s, so none of the five is redeclared. Two of the three collapses
  are exact and the third is not: the two constructor theorems below take
  `UnitSpqrT1.ZeroizeTotal`, which quantifies over the element type, the width
  and the instance, where `TripleT1.ZeroizeTotal` fixes all three at
  `Array U8 32`. They assume strictly more than their twins do, which makes
  them strictly weaker theorems. The narrow form is what the two constructors
  need -- each wipes two 32-byte arrays and nothing else -- so the generality
  is a convenience of reusing the leaf's constant, not a requirement;
* three bundles gain preconditions, and the theorems that use them gain those
  preconditions too.

So this file is hand-written, and unlike the generated leaf copies it can
drift from `TripleT1.lean`. `LIMITATIONS.md` names that as the cost.

## The three preconditions, which are the substance of the exercise

`TripleT1.lean`'s bundles are stated with no hypothesis: unconditional
totality of every ratchet call. That is stronger than what the leaves prove,
and it is what `CLAIMS.md` flags by putting `TripleT1.lean` under "Proved
conditionally". Proving the bundles instead of assuming them means carrying
the leaves' real preconditions, and there are three:

* `RatchetReceiveTotal` needs
  `max state.skipped.val.length MAX_SKIPPED_STORE.val + MAX_SKIP.val ≤
  Usize.max`, the store at its largest plus the gap one skip can add. Both
  addends are bounded by constants, so it is satisfiable at either width
  Aeneas models `usize` at.
* `SpqrSendTotal` needs `st.chains.length + 1 < Usize.max`.
* `SpqrReceiveTotal` needs `st.chains.length + 2 < Usize.max` and
  `st.skipped.length + MAX_SKIP.val ≤ Usize.max`.

Two more bundles bottom out in `tacenta_spqr.kdf_init`, which no leaf proof
covers, so `KdfInitTotal` is declared here, in the same shape as
`UnitSpqrT1.KdfRkTotal`: a translated function bottoming out in the opaque
`hkdf_sha256`, at 96 bytes. That trade is worth naming -- it replaces two
opaque-crate-boundary assumptions (`SpqrInitAliceTotal`, `SpqrInitBobTotal`
as `TripleT1.lean` states them) with one assumption of a kind other proofs in
this tree already rely on. "Trusted KDF" undersells what it bundles: besides
`hkdf_sha256` it covers the `zeroize` wrapper at a width nothing else states
and the `info` builder, exactly as `UnitSpqrT1.KdfRkTotal` does.

Like every other hypothesis on this island, it has no satisfiability witness.
`Translation/Satisfiability.lean` and `Translation/SatisfiabilityTriple.lean`
exhibit witnesses for the leaf islands' assumptions; nothing does so here, and
`KdfInitTotal` joins `UnitT1.DerivedKeysModel`, `UnitSpqrT1.OptionCloneTotal`,
`KdfRkTotal` and `KdfCkTotal` in that. Calling that inherited would be too
kind: `KdfRkTotal` and `KdfCkTotal` are at least derived on the leaf side from
`SpqrT3.SpqrHkdfAgrees`, and `KdfInitTotal` has no leaf twin at all, so it is
introduced here. `LIMITATIONS.md` records what the guard does and does not
cover.

## Why the preconditions transport for free

The Triple calls each leaf on `candidate`, a clone of `self`, so a
precondition about `self` is useless unless something says the clone preserves
it. `TripleT1.State.clone_no_panic` proves only that the clone *returns*,
which is all it can prove where the inner states are opaque; a precondition
could not be transported through it. On the unit the clone is a real
definition and every field is an array, a scalar, an `Option` under
`UnitSpqrT1.OptionCloneTotal`, or a `Vec` whose elements clone as the
identity, so `State.Insts.CoreCloneClone.clone s = ok s` is provable outright
(`triple_state_clone_id`). That is what `State.clone_spec` below carries into
`State.send` and `State.receive`, and it is the one place this file is
strictly stronger than `TripleT1.lean` rather than merely differently stated.

## Three functions `TripleT1.lean` lists as unproved

`State.classical_skipped_len`, `State.post_quantum_skipped_len` and
`State.post_quantum_receive_count` are one-liners here: each wraps an inner
operation that is opaque in `TripleT1.lean` and a definition in the unit. The
other four on that file's not-proved list (`State.evict_oldest_classical`,
`State.evict_oldest_post_quantum`, `State.to_bytes`, `State.from_bytes`) do
**not** fall out and are not claimed.

Axiom pins for the headline theorems are in `Translation/UnitPins.lean`,
beside the leaves', for the same reason: a pin's expected text is Lean's
pretty-printer's output, written once by hand against what the compiler
actually prints.
-/

open Aeneas Aeneas.Std Result

namespace Tacenta.UnitTripleT1

open tacenta_triple_unit tacenta_triple_unit.tacenta_triple

/-! ## The clone-identity plumbing -/

/-- A vector clones as the identity when every element does. -/
theorem vec_clone_id {T : Type} (inst : core.clone.Clone T)
    (v : alloc.vec.Vec T) (h : ∀ x ∈ v.val, inst.clone x = ok x) :
    alloc.vec.CloneVec.clone inst v = ok v := by
  have hs := Slice.clone_spec (clone := inst.clone) (s := v) h
  obtain ⟨y, hy, hxy⟩ := WP.spec_imp_exists hs
  unfold alloc.vec.CloneVec.clone
  rw [hy, ← hxy]
  rfl

/-- A fixed-size array clones as the identity when every element does. -/
theorem array_clone_id {T : Type} {N : Usize} (inst : core.clone.Clone T)
    (a : Array T N) (h : ∀ x ∈ a.val, inst.clone x = ok x) :
    core.array.CloneArray.clone inst a = ok a := by
  obtain ⟨y, hy, hxy⟩ := WP.spec_imp_exists (core.array.CloneArray.clone_spec inst a h)
  simp only [hy, ← hxy]

theorem byte_array_clone_id {N : Usize} (a : Array U8 N) :
    core.array.CloneArray.clone core.clone.CloneU8 a = ok a :=
  array_clone_id _ a (by intro x _; simp [liftFun1])

/-- An `Option` clones as the identity when its payload does. -/
theorem option_clone_id (hopt : UnitSpqrT1.OptionCloneTotal) {T : Type}
    (inst : core.clone.Clone T) (o : Option T)
    (h : ∀ x, o = some x → inst.clone x = ok x) :
    core.option.Option.Insts.CoreCloneClone.clone inst o = ok o := by
  obtain ⟨y, hy, hxy⟩ :=
    WP.spec_imp_exists (hopt inst o (fun x hx => by simp [h x hx]))
  rw [hy, hxy]

theorem option_byte_array_clone_id (hopt : UnitSpqrT1.OptionCloneTotal) {N : Usize}
    (o : Option (Array U8 N)) :
    core.option.Option.Insts.CoreCloneClone.clone (core.clone.CloneArray N core.clone.CloneU8) o
      = ok o :=
  option_clone_id hopt _ o (fun x _ => byte_array_clone_id x)

theorem skipped_key_clone_id (k : tacenta_ratchet.SkippedKey) :
    tacenta_ratchet.SkippedKey.Insts.CoreCloneClone.clone k = ok k := by
  unfold tacenta_ratchet.SkippedKey.Insts.CoreCloneClone.clone
  simp [byte_array_clone_id, lift]

theorem spqr_skipped_clone_id (k : tacenta_spqr.Skipped) :
    tacenta_spqr.Skipped.Insts.CoreCloneClone.clone k = ok k := by
  unfold tacenta_spqr.Skipped.Insts.CoreCloneClone.clone
  simp [byte_array_clone_id, lift]

theorem ratchet_skipped_clone_id (v : alloc.vec.Vec tacenta_ratchet.SkippedKey) :
    alloc.vec.CloneVec.clone tacenta_ratchet.SkippedKey.Insts.CoreCloneClone v = ok v :=
  vec_clone_id _ v (fun x _ => skipped_key_clone_id x)

theorem spqr_skipped_clone_id' (v : alloc.vec.Vec tacenta_spqr.Skipped) :
    alloc.vec.CloneVec.clone tacenta_spqr.Skipped.Insts.CoreCloneClone v = ok v :=
  vec_clone_id _ v (fun x _ => spqr_skipped_clone_id x)

theorem builtin_vec_clone_id {T : Type} (v : alloc.vec.Vec T) :
    alloc.vec.CloneVec.clone (BuiltinClone T) v = ok v :=
  vec_clone_id _ v (fun _ _ => rfl)

theorem ratchet_state_clone_id (hopt : UnitSpqrT1.OptionCloneTotal)
    (s : tacenta_ratchet.State) :
    tacenta_ratchet.State.Insts.CoreCloneClone.clone s = ok s := by
  unfold tacenta_ratchet.State.Insts.CoreCloneClone.clone
  simp [byte_array_clone_id, option_byte_array_clone_id hopt, ratchet_skipped_clone_id,
    tacenta_ratchet.LabelSet.Insts.CoreCloneClone.clone, lift]

theorem spqr_state_clone_id (s : tacenta_spqr.State) :
    tacenta_spqr.State.Insts.CoreCloneClone.clone s = ok s := by
  unfold tacenta_spqr.State.Insts.CoreCloneClone.clone
  simp [byte_array_clone_id, builtin_vec_clone_id, spqr_skipped_clone_id',
    tacenta_spqr.Direction.Insts.CoreCloneClone.clone, lift]

theorem triple_state_clone_id (hopt : UnitSpqrT1.OptionCloneTotal) (s : State) :
    State.Insts.CoreCloneClone.clone s = ok s := by
  unfold State.Insts.CoreCloneClone.clone
  simp [ratchet_state_clone_id hopt, spqr_state_clone_id]

/-! ## The seventeen bundles, and their discharge lemmas -/

def KdfInitTotal : Prop :=
  ∀ (sk : Slice U8), ∃ r, tacenta_spqr.kdf_init sk = ok r

def RatchetStateCloneTotal : Prop :=
  ∀ (s : tacenta_ratchet.State),
    ∃ r, tacenta_ratchet.State.Insts.CoreCloneClone.clone s = ok r

theorem ratchetStateCloneTotal (hopt : UnitSpqrT1.OptionCloneTotal) :
    RatchetStateCloneTotal := fun s => ⟨s, ratchet_state_clone_id hopt s⟩

def RatchetSendingPublicTotal : Prop :=
  ∀ (s : tacenta_ratchet.State), ∃ r, tacenta_ratchet.State.sending_public s = ok r

theorem ratchetSendingPublicTotal : RatchetSendingPublicTotal := by
  intro s; unfold tacenta_ratchet.State.sending_public; simp

def RatchetSendCountTotal : Prop :=
  ∀ (s : tacenta_ratchet.State), ∃ r, tacenta_ratchet.State.send_count s = ok r

theorem ratchetSendCountTotal : RatchetSendCountTotal := by
  intro s; unfold tacenta_ratchet.State.send_count; simp

def RatchetReceiveCountTotal : Prop :=
  ∀ (s : tacenta_ratchet.State), ∃ r, tacenta_ratchet.State.receive_count s = ok r

theorem ratchetReceiveCountTotal : RatchetReceiveCountTotal := by
  intro s; unfold tacenta_ratchet.State.receive_count; simp

def RatchetInitSenderTotal : Prop :=
  ∀ (ec our_pub peer_pub dh_out : Array U8 32#usize) (labels : tacenta_ratchet.LabelSet),
    ∃ r, tacenta_ratchet.init_sender ec our_pub peer_pub dh_out labels = ok r

theorem ratchetInitSenderTotal (hk : UnitT1.HkdfTotal) (hzw : UnitT1.ZeroizingTotal) :
    RatchetInitSenderTotal := by
  intro ec our_pub peer_pub dh_out labels
  obtain ⟨⟨rk, cks⟩, hr⟩ :=
    (UnitT1.noPanic_iff _).1 (UnitT1.kdf_rk_no_panic hk hzw ec dh_out labels)
  unfold tacenta_ratchet.init_sender
  simp [hr]

def RatchetInitReceiverTotal : Prop :=
  ∀ (ec our_pub : Array U8 32#usize) (labels : tacenta_ratchet.LabelSet),
    ∃ r, tacenta_ratchet.init_receiver ec our_pub labels = ok r

theorem ratchetInitReceiverTotal : RatchetInitReceiverTotal := by
  intro ec our_pub labels; unfold tacenta_ratchet.init_receiver; simp

def RatchetSendTotal : Prop :=
  ∀ (s : tacenta_ratchet.State), ∃ r, tacenta_ratchet.send s = ok r

theorem ratchetSendTotal (h : UnitT1.HmacTotal) : RatchetSendTotal :=
  fun s => UnitT1.send_no_panic h s

def RatchetReceiveTotal : Prop :=
  ∀ (s : tacenta_ratchet.State) (hdr : tacenta_ratchet.Header)
    (a b c : Array U8 32#usize),
    max s.skipped.val.length tacenta_ratchet.MAX_SKIPPED_STORE.val
      + tacenta_ratchet.MAX_SKIP.val ≤ Usize.max →
    ∃ r, tacenta_ratchet.receive s hdr a b c = ok r

theorem ratchetReceiveTotal (h : UnitT1.HmacTotal) (hk : UnitT1.HkdfTotal)
    (hzw : UnitT1.ZeroizingTotal) (hrm : UnitT1.VecRemoveTotal)
    [UnitT1.DerivedKeysModel] : RatchetReceiveTotal := by
  intro s hdr a b c hs
  exact (UnitT1.noPanic_iff _).1 (UnitT1.receive_no_panic h hk hzw hrm s hdr a b c hs)

def RatchetHeaderEqTotal : Prop :=
  ∀ (a b : tacenta_ratchet.Header),
    ∃ r, tacenta_ratchet.Header.Insts.CoreCmpPartialEqHeader.eq a b = ok r

theorem ratchetHeaderEqTotal : RatchetHeaderEqTotal := by
  intro a b
  unfold tacenta_ratchet.Header.Insts.CoreCmpPartialEqHeader.eq
  split
  · split
    · exact (UnitT1.noPanic_iff _).1 (UnitT1.array_eq_total a.dh b.dh)
    · simp
  · simp

def RatchetErrorEqTotal : Prop :=
  ∀ (a b : tacenta_ratchet.RatchetError),
    ∃ r, tacenta_ratchet.RatchetError.Insts.CoreCmpPartialEqRatchetError.eq a b = ok r

theorem ratchetErrorEqTotal : RatchetErrorEqTotal := by
  intro a b
  unfold tacenta_ratchet.RatchetError.Insts.CoreCmpPartialEqRatchetError.eq; simp

def SpqrErrorEqTotal : Prop :=
  ∀ (a b : tacenta_spqr.SpqrError),
    ∃ r, tacenta_spqr.SpqrError.Insts.CoreCmpPartialEqSpqrError.eq a b = ok r

theorem spqrErrorEqTotal : SpqrErrorEqTotal := by
  intro a b
  unfold tacenta_spqr.SpqrError.Insts.CoreCmpPartialEqSpqrError.eq; simp

def SpqrStateCloneTotal : Prop :=
  ∀ (s : tacenta_spqr.State), ∃ r, tacenta_spqr.State.Insts.CoreCloneClone.clone s = ok r

theorem spqrStateCloneTotal : SpqrStateCloneTotal := fun s => ⟨s, spqr_state_clone_id s⟩

def SpqrInitAliceTotal : Prop :=
  ∀ (s : Slice U8), ∃ r, tacenta_spqr.State.init_alice s = ok r

def SpqrInitBobTotal : Prop :=
  ∀ (s : Slice U8), ∃ r, tacenta_spqr.State.init_bob s = ok r

theorem spqrInitTotal (hki : KdfInitTotal) (sk : Slice U8) (d : tacenta_spqr.Direction) :
    ∃ r, tacenta_spqr.State.init sk d = ok r := by
  obtain ⟨⟨rk, k1, k2⟩, hr⟩ := hki sk
  unfold tacenta_spqr.State.init
  cases d <;> simp [hr, lift]

theorem spqrInitAliceTotal (hki : KdfInitTotal) : SpqrInitAliceTotal := by
  intro s; unfold tacenta_spqr.State.init_alice; exact spqrInitTotal hki s _

theorem spqrInitBobTotal (hki : KdfInitTotal) : SpqrInitBobTotal := by
  intro s; unfold tacenta_spqr.State.init_bob; exact spqrInitTotal hki s _

def SpqrEpochTotal : Prop :=
  ∀ (s : tacenta_spqr.State), ∃ r, tacenta_spqr.State.impl.epoch s = ok r

theorem spqrEpochTotal : SpqrEpochTotal := by
  intro s; unfold tacenta_spqr.State.impl.epoch; simp

def SpqrSendTotal : Prop :=
  ∀ (s : tacenta_spqr.State) (epoch : U64) (out : Option tacenta_spqr.Output),
    s.chains.length + 1 < Usize.max →
    ∃ r, tacenta_spqr.State.send s epoch out = ok r

theorem spqrSendTotal (hret : UnitSpqrT1.VecRetainTotal) (hrk : UnitSpqrT1.KdfRkTotal)
    (hz : UnitSpqrT1.ZeroizeTotal) (hck : UnitSpqrT1.KdfCkTotal)
    (hopt : UnitSpqrT1.OptionCloneTotal) : SpqrSendTotal := by
  intro s epoch out hroom
  exact (UnitT1.noPanic_iff _).1
    (UnitSpqrT1.send_no_panic hret hrk hz hck hopt s epoch out hroom)

def SpqrReceiveTotal : Prop :=
  ∀ (s : tacenta_spqr.State) (epoch : U64) (out : Option tacenta_spqr.Output) (n : U64),
    s.chains.length + 2 < Usize.max →
    s.skipped.length + tacenta_spqr.MAX_SKIP.val ≤ Usize.max →
    ∃ r, tacenta_spqr.State.receive s epoch out n = ok r

theorem spqrReceiveTotal (hret : UnitSpqrT1.VecRetainTotal) (hrk : UnitSpqrT1.KdfRkTotal)
    (hz : UnitSpqrT1.ZeroizeTotal) (hck : UnitSpqrT1.KdfCkTotal)
    (hopt : UnitSpqrT1.OptionCloneTotal) (hrm : UnitSpqrT1.VecRemoveTotal)
    (happ : UnitSpqrT1.VecAppendTotal) : SpqrReceiveTotal := by
  intro s epoch out n hroom hskiproom
  exact (UnitT1.noPanic_iff _).1
    (UnitSpqrT1.receive_no_panic hret hrk hz hck hopt hrm happ s epoch n out hroom hskiproom)

/-! ## This crate's own types: `Header`, `TripleError` -/

theorem Header.clone_no_panic (self : Header) :
    Header.Insts.CoreCloneClone.clone self ⦃ fun _ => True ⦄ := by
  unfold Header.Insts.CoreCloneClone.clone; simp

theorem Header.eq_no_panic (self other : Header) :
    Header.Insts.CoreCmpPartialEqHeader.eq self other ⦃ fun _ => True ⦄ := by
  unfold Header.Insts.CoreCmpPartialEqHeader.eq
  split
  · split
    · obtain ⟨r, hr⟩ := ratchetHeaderEqTotal self.dr other.dr
      simp [hr]
    · simp
  · simp

theorem Header.assert_fields_are_eq_no_panic (self : Header) :
    Header.Insts.CoreCmpEq.assert_fields_are_eq self ⦃ fun _ => True ⦄ := by
  unfold Header.Insts.CoreCmpEq.assert_fields_are_eq; simp

theorem TripleError.clone_no_panic (self : TripleError) :
    TripleError.Insts.CoreCloneClone.clone self ⦃ fun _ => True ⦄ := by
  unfold TripleError.Insts.CoreCloneClone.clone; simp

theorem TripleError.assert_fields_are_eq_no_panic (self : TripleError) :
    TripleError.Insts.CoreCmpEq.assert_fields_are_eq self ⦃ fun _ => True ⦄ := by
  unfold TripleError.Insts.CoreCmpEq.assert_fields_are_eq; simp

theorem TripleError.eq_no_panic (self other : TripleError) :
    TripleError.Insts.CoreCmpPartialEqTripleError.eq self other ⦃ fun _ => True ⦄ := by
  unfold TripleError.Insts.CoreCmpPartialEqTripleError.eq
  simp only [TripleError.read_discriminant]
  rcases self with a | a <;> rcases other with b | b <;> simp
  · obtain ⟨r, hr⟩ := ratchetErrorEqTotal a b; simp [hr]
  · obtain ⟨r, hr⟩ := spqrErrorEqTotal a b; simp [hr]

/-! ## The two module-level functions: `split_secret`, `combine` -/

theorem split_secret_no_panic (hkdf : UnitT1.HkdfTotal) (hzw : UnitT1.ZeroizingTotal)
    (sk : Slice U8) : split_secret sk ⦃ fun _ => True ⦄ := by
  unfold split_secret
  step*
  all_goals (try simp_all [Slice.length])

theorem combine_no_panic (hkdf : UnitT1.HkdfTotal) (mk_classical mk_pq : Array U8 32#usize) :
    combine mk_classical mk_pq ⦃ fun _ => True ⦄ := by
  unfold combine
  step*

/-! ## `State`'s clone and small accessors -/

theorem State.clone_no_panic (hopt : UnitSpqrT1.OptionCloneTotal) (self : State) :
    State.Insts.CoreCloneClone.clone self ⦃ fun _ => True ⦄ := by
  simp [triple_state_clone_id hopt]

theorem State.sending_public_no_panic (self : State) :
    State.sending_public self ⦃ fun _ => True ⦄ := by
  unfold State.sending_public
  obtain ⟨r, hr⟩ := ratchetSendingPublicTotal self.classical
  simp [hr]

theorem State.send_count_no_panic (self : State) :
    State.send_count self ⦃ fun _ => True ⦄ := by
  unfold State.send_count
  obtain ⟨r, hr⟩ := ratchetSendCountTotal self.classical
  simp [hr]

theorem State.receive_count_no_panic (self : State) :
    State.receive_count self ⦃ fun _ => True ⦄ := by
  unfold State.receive_count
  obtain ⟨r, hr⟩ := ratchetReceiveCountTotal self.classical
  simp [hr]

theorem State.epoch_no_panic (self : State) :
    State.epoch self ⦃ fun _ => True ⦄ := by
  unfold State.epoch
  obtain ⟨r, hr⟩ := spqrEpochTotal self.post_quantum
  simp [hr]

/-! ## `State.init_sender`, `State.init_receiver` -/

theorem State.init_sender_no_panic (hss : UnitT1.HkdfTotal) (hzw : UnitT1.ZeroizingTotal)
    (hki : KdfInitTotal) (hz : UnitSpqrT1.ZeroizeTotal) (sk : Slice U8)
    (our_pub peer_pub dh_out : Array U8 32#usize) (labels : tacenta_ratchet.LabelSet) :
    State.init_sender sk our_pub peer_pub dh_out labels ⦃ fun _ => True ⦄ := by
  unfold State.init_sender
  step with split_secret_no_panic hss hzw sk
  all_goals (try (obtain ⟨s, hs⟩ := ratchetInitSenderTotal hss hzw ec our_pub peer_pub dh_out labels; simp only [hs]))
  all_goals (try step*)
  all_goals (try (obtain ⟨s2, hs2⟩ := spqrInitAliceTotal hki s1; simp only [hs2]))
  all_goals (try step*)
  all_goals (try (obtain ⟨r, hr⟩ := hz (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes) ec; simp only [hr]))
  all_goals (try step*)
  all_goals (try (obtain ⟨r1, hr1⟩ := hz (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes) pq; simp only [hr1]))
  all_goals (try step*)

theorem State.init_receiver_no_panic (hss : UnitT1.HkdfTotal) (hzw : UnitT1.ZeroizingTotal)
    (hki : KdfInitTotal) (hz : UnitSpqrT1.ZeroizeTotal) (sk : Slice U8)
    (our_pub : Array U8 32#usize) (labels : tacenta_ratchet.LabelSet) :
    State.init_receiver sk our_pub labels ⦃ fun _ => True ⦄ := by
  unfold State.init_receiver
  step with split_secret_no_panic hss hzw sk
  all_goals (try (obtain ⟨s, hs⟩ := ratchetInitReceiverTotal ec our_pub labels; simp only [hs]))
  all_goals (try step*)
  all_goals (try (obtain ⟨s2, hs2⟩ := spqrInitBobTotal hki s1; simp only [hs2]))
  all_goals (try step*)
  all_goals (try (obtain ⟨r, hr⟩ := hz (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes) ec; simp only [hr]))
  all_goals (try step*)
  all_goals (try (obtain ⟨r1, hr1⟩ := hz (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes) pq; simp only [hr1]))
  all_goals (try step*)

/-! ## `State.send`, `State.receive`, `State.commit` -/

/-- The clone in the spec form the two composed paths step through: it returns,
and what it returns *is* `self`. This is what carries the three preconditions
below across the clone, and it is the one place this file is stronger than
`TripleT1.lean`, which can only say the clone returns. -/
theorem State.clone_spec (hopt : UnitSpqrT1.OptionCloneTotal) (self : State) :
    State.Insts.CoreCloneClone.clone self ⦃ fun c => c = self ⦄ := by
  simp [triple_state_clone_id hopt]

/-- Wiping a byte buffer returns, as a stepping rule. Written out with the
instance argument because `UnitSpqrT1.ZeroizeTotal` quantifies over it and the
stepping tactic has nothing to infer it from. -/
@[step]
theorem zeroize_step (hz : UnitSpqrT1.ZeroizeTotal) {Z : Type} {N : Usize}
    (inst : zeroize.Zeroize Z) (a : Array Z N) :
    Array.Insts.ZeroizeZeroize.zeroize inst a ⦃ fun _ => True ⦄ := by
  obtain ⟨r, hr⟩ := hz inst a; simp [hr]

/-- `combine` as a stepping rule, so the two composed paths walk through it. -/
@[step]
theorem combine_step (hkdf : UnitT1.HkdfTotal) (a b : Array U8 32#usize) :
    combine a b ⦃ fun _ => True ⦄ := combine_no_panic hkdf a b

/-- The composed send path cannot panic, under one precondition: the sparse
ratchet's chain table must have room for the one epoch `maybe_advance` can add
plus the one `set_chains` writes. The precondition is stated about `self`, not
about the clone the body actually calls into, and `State.clone_spec` is what
lets it be: on the unit the clone is provably the identity. -/
theorem State.send_no_panic (hhmac : UnitT1.HmacTotal) (hkdf : UnitT1.HkdfTotal)
    (hz : UnitSpqrT1.ZeroizeTotal) (hret : UnitSpqrT1.VecRetainTotal)
    (hrk : UnitSpqrT1.KdfRkTotal) (hck : UnitSpqrT1.KdfCkTotal)
    (hopt : UnitSpqrT1.OptionCloneTotal)
    (self : State) (sending_epoch : U64) (output : Option tacenta_spqr.Output)
    (hroom : self.post_quantum.chains.length + 1 < Usize.max) :
    State.send self sending_epoch output ⦃ fun _ => True ⦄ := by
  obtain ⟨⟨r, s⟩, hrs⟩ := ratchetSendTotal hhmac self.classical
  obtain ⟨⟨r1, s1⟩, hrq⟩ :=
    spqrSendTotal hret hrk hz hck hopt self.post_quantum sending_epoch output hroom
  unfold State.send
  step with State.clone_spec hopt self
  subst candidate_post
  rcases r with ⟨dr, mk_ec⟩ | e <;> rcases r1 with ⟨pq_n, mk_pq⟩ | e1 <;>
    simp only [hrs, hrq] <;> step*

/-- The composed receive path cannot panic, under three preconditions: the
classical ratchet's skipped-key store bound, and the sparse ratchet's chain-table
and skipped-store bounds. All three are stated about `self`; `State.clone_spec`
carries them to the clone the body calls into. -/
theorem State.receive_no_panic (hhmac : UnitT1.HmacTotal) (hkdf : UnitT1.HkdfTotal)
    (hzw : UnitT1.ZeroizingTotal) [UnitT1.DerivedKeysModel]
    (hz : UnitSpqrT1.ZeroizeTotal) (hret : UnitSpqrT1.VecRetainTotal)
    (hrk : UnitSpqrT1.KdfRkTotal) (hck : UnitSpqrT1.KdfCkTotal)
    (hopt : UnitSpqrT1.OptionCloneTotal) (hrm : UnitSpqrT1.VecRemoveTotal)
    (happ : UnitSpqrT1.VecAppendTotal)
    (self : State) (header : Header)
    (dh_out_recv dh_out_send new_dhs_pub : Array U8 32#usize)
    (output : Option tacenta_spqr.Output)
    (hs : max self.classical.skipped.val.length tacenta_ratchet.MAX_SKIPPED_STORE.val
      + tacenta_ratchet.MAX_SKIP.val ≤ Usize.max)
    (hroom : self.post_quantum.chains.length + 2 < Usize.max)
    (hskiproom : self.post_quantum.skipped.length + tacenta_spqr.MAX_SKIP.val ≤ Usize.max) :
    State.receive self header dh_out_recv dh_out_send new_dhs_pub output ⦃ fun _ => True ⦄ := by
  obtain ⟨⟨r, s⟩, hrs⟩ :=
    ratchetReceiveTotal hhmac hkdf hzw hrm self.classical header.dr dh_out_recv
      dh_out_send new_dhs_pub hs
  obtain ⟨⟨r1, s1⟩, hrq⟩ :=
    spqrReceiveTotal hret hrk hz hck hopt hrm happ self.post_quantum header.epoch output
      header.pq_n hroom hskiproom
  unfold State.receive
  step with State.clone_spec hopt self
  subst candidate_post
  rcases r with v | e <;> rcases r1 with v1 | e1 <;> simp only [hrs, hrq] <;> step*

theorem State.commit_no_panic (self next : State) : State.commit self next ⦃ fun _ => True ⦄ := by
  unfold State.commit; simp

/-! ## Three accessors `TripleT1.lean` leaves unproved -/

theorem State.classical_skipped_len_no_panic (self : State) :
    State.classical_skipped_len self ⦃ fun _ => True ⦄ := by
  unfold State.classical_skipped_len tacenta_ratchet.State.skipped_len; simp

theorem State.post_quantum_skipped_len_no_panic (self : State) :
    State.post_quantum_skipped_len self ⦃ fun _ => True ⦄ := by
  unfold State.post_quantum_skipped_len tacenta_spqr.State.skipped_len; simp

theorem State.post_quantum_receive_count_no_panic (self : State) (epoch : U64) :
    State.post_quantum_receive_count self epoch ⦃ fun _ => True ⦄ := by
  unfold State.post_quantum_receive_count tacenta_spqr.State.receive_count
  step*

/-! ## Where this stands

**Proved:** everything `TripleT1.lean` proves, plus the three accessors it
lists as unproved -- `split_secret`, `combine`, `Header`'s and `TripleError`'s
clone and equality, `State`'s clone (as an identity, not merely as total), the
four accessors that read a counter or a key off the state, the two
constructors, `State.send`, `State.receive`, `State.commit`,
`State.classical_skipped_len`, `State.post_quantum_skipped_len` and
`State.post_quantum_receive_count`. Above those, the seventeen bundles
`TripleT1.lean` assumes.

**Not proved:** `State.evict_oldest_classical`,
`State.evict_oldest_post_quantum`, `State.to_bytes` and `State.from_bytes`,
the four remaining entries on `TripleT1.lean`'s not-proved list. Being inside
the unit does not make them fall out: the eviction loops and the
length-prefixed framing are their own proof obligations, unrelated to the
crate boundary this file removes.

**What the trust base becomes.** `TripleT1.lean`'s `State.receive_no_panic`
depends on twelve axioms and is kernel-only. This file's depends on eighteen
and is not: it inherits
`Tacenta.UnitSpqrT1.receive_no_panic._native.native_decide.ax_1_1`, the one
compiler-trusted numeric fact the sparse ratchet's own receive proof rests on.
Both halves of that are worth stating plainly, and `Translation/UnitPins.lean`
states them: the current theorem is kernel-only because it *assumes* the
sparse ratchet's receive is total rather than proving it, so its kernel-only
status is bought by assuming the hard part; this one proves that part and
inherits what proving it costs. Underneath, six axioms go and twelve arrive:
the bare operation axioms (`tacenta_ratchet.receive`,
`tacenta_spqr.State.receive`, the two states and their clones) are replaced by
KDF, zeroize and `Vec` boundary axioms already shared with other proofs in this
tree. That accounts for eleven of the twelve. The twelfth is the
`native_decide` axiom named above, which is neither, and saying otherwise would
be a summary at odds with its own lead. -/

end Tacenta.UnitTripleT1
