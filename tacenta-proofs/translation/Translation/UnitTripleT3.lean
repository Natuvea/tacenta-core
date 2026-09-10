import Translation.TacentaTripleUnit
import Translation.UnitTripleT1
import Translation.UnitT3
import Translation.UnitSpqrT3
import Model.Triple

/-!
# T3 for the Triple Ratchet, on the three-leaf unit

`TripleT3.lean` proves the translated Triple Ratchet refines `Model.Triple`,
about the Triple translated on its own. This file restates that proof about the
three-leaf translation unit (`Translation/TacentaTripleUnit.lean`), where the
Triple and both inner ratchets are compiled as one crate, as `UnitTripleT1.lean`
did for panic-freedom. Then it goes a step further than its original can.

## The bundles are proved here

`TripleT3.lean` cannot cite the inner ratchets' refinement theorems. The
Triple's standalone translation declares each inner state as a bare opaque type
and collides with the inner crates' own translations, so the fact it needs is
proved in files it cannot import. It works around that with two hand-written
bundles, `RatchetAgreesFor` and `SpqrAgreesFor`, each an assumed abstraction
under which every inner call the Triple makes agrees with the model, and its
header says what that costs.

None of that holds on the unit. The inner states are concrete structures, and
`Tacenta.UnitT3` and `Tacenta.UnitSpqrT3`, the inner refinements restated about
the unit, import into this file. Each inner refinement relation fixes every
field of its model state, so the abstraction can be written down, and every
clause of both bundles follows from a theorem already proved.
`ratchet_agrees_for` and `spqr_agrees_for`, near the end of this file, prove the
bundles, and `send_refines_discharged` and `receive_refines_discharged` are the
composed `send` and `receive` with both discharged. Nothing those two assume
about either inner ratchet's behaviour is written by hand; what they state about
the inner states is the numeric preconditions the inner theorems need, carried
through the abstraction. What they do assume is the boundary the inner
refinements themselves take: the HMAC and HKDF agreements,
the `zeroize` round trips, three `Vec` agreements, `VecRemoveTotal`,
`DerivedKeysModel`, `OptionCloneTotal` and the general `ZeroizeTotal`.

Three things are worth knowing about that trade.

* **Most of the trust-base change is the unit's doing, not the discharge's.**
  `TripleT3.send_refines` rests on sixteen opaque declarations of the inner
  crates, the two state types and fourteen calls. On the unit those are defined
  rather than opaque, so `send_refines` here, with the bundles still as
  hypotheses, already rests on none of them, and on the external primitives the
  inner refinements rest on instead. Discharging the bundles removes them as
  hypotheses and adds one thing at the axiom level: the eight `native_decide`
  compiler-trust axioms `UnitSpqrT3.lean` carries, on top of the one of this
  file's three that they already rest on. `UnitPins.lean` pins the discharged
  theorems' lists.
* **Each bundle covers its ratchet's whole calling surface**, so
  `send_refines_discharged` assumes the receive path's boundary too.
* **`send_refines` and `receive_refines` are kept as `TripleT3.lean` states
  them**, taking the bundles as hypotheses, so this file reads against its
  original line for line. The `-- mirrors:` comments on the bundles now name the
  unit's copies, and in one direction they are no longer the only thing tying a
  clause to its inner theorem: a clause that asked less than that theorem needs,
  or promised more than it proves, would break the bundle's proof. The other
  direction is unguarded. A clause that asked more or promised less would still
  prove, and the accessor, initialiser and `epoch` clauses, which `send_refines`
  and `receive_refines` never use, could be weakened with no proof noticing. That
  leaves what the discharged theorems mean untouched, since their statements do
  not mention the bundles.

## Every difference from `TripleT3.lean` above the bundle proofs

This file is hand-written, not generated: not every difference is a rename, so
`port-unit-proofs.sh` cannot derive it, and nothing but a reader checks that it
keeps saying what its original says. Each difference was made to get the
original text to elaborate on the unit:

* the imports: `TacentaTripleUnit`, `UnitTripleT1`, `UnitT3` and `UnitSpqrT3` in
  place of `TacentaTriple` and `TripleT1`;
* the namespace, `Tacenta.UnitTripleT3`, and the `open`, which names the unit's
  outer namespace and the Triple crate inside it;
* `TripleT1`'s boundary copies point at the leaf constants they collapse into, as
  in `UnitTripleT1.lean`: `HkdfSha256Total` at `UnitT1.HkdfTotal` and
  `ZeroizingTotal` at `UnitT1.ZeroizingTotal`. `TripleT1`'s narrow `ZeroizeTotal`
  has no unit twin of the same strength, so it is copied here as written, below
  the `open` so that its names resolve on the unit;
* `tacenta_spqr.State.epoch`, the accessor, is `tacenta_spqr.State.impl.epoch`
  on the unit, where the unprefixed name is the structure's field;
* qualified references to `T3.lean`'s and `SpqrT3.lean`'s theorems name the unit
  copies, in the `-- mirrors:` comments as well;
* the erasure of `TripleT1.zeroizing_deref_step` names
  `UnitT1.zeroizing_deref_step`. The erasures in `UnitT3.lean` and
  `UnitSpqrT3.lean` do not carry into a module that imports them, so this file
  needs its own;
* `UnitTripleT1.combine_step` and `UnitTripleT1.zeroize_step` are erased too.
  `TripleT1.lean` never registered them. Left in, `step*` consumes the `combine`
  and `zeroize` calls with them and leaves `UnitT1.HkdfTotal` and the general
  `UnitSpqrT1.ZeroizeTotal` as goals before the proofs can apply
  `combine_refines` and the narrow `ZeroizeTotal`;
* this header and the bundles' docstrings, which in `TripleT3.lean` explain why
  the inner theorems cannot be cited.
-/

open Aeneas Aeneas.Std Result

namespace Tacenta.UnitTripleT3

open tacenta_triple_unit tacenta_triple_unit.tacenta_triple

-- Carried from TripleT1.lean verbatim: the NARROW form, one element type,
-- one width, one instance. Swapping in UnitSpqrT1's general form would make
-- every theorem taking it assume strictly more, which a cold read of phase
-- two caught once already.
def ZeroizeTotal : Prop :=
  ∀ (a : Array U8 32#usize),
    ∃ r, Array.Insts.ZeroizeZeroize.zeroize
      (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes) a = ok r

/-- A translated byte as the model's. -/
def u8 (b : Std.U8) : UInt8 := UInt8.ofNat b.val

/-- A slice of translated bytes as the model's byte list. -/
def sliceOf (s : Slice Std.U8) : List UInt8 := s.val.map u8

/-- A fixed-size array of translated bytes as the model's key. -/
def keyOf {n : Usize} (a : Array Std.U8 n) : Model.State.Key := a.val.map u8

/-! ## The trusted boundary, restated as agreement

`TripleT1.lean` assumed `hkdf_sha256` (via `HkdfSha256Total`) cannot fail
within RFC 5869's output bound. Refinement needs more: that when it returns,
it returns what `Model.Kdf.hkdf` computes. Argument order follows the Rust
and the model alike: salt, then the input keying material, then the info
string -- `split_secret`/`combine` both call `hkdf_sha256` this way, and
`Model.TripleRatchet.splitSecret`/`combine` both call `Model.Kdf.hkdf` the
same way. The premise is the same bound, 8160 bytes, which the crate's own
`expect` enforces (`T1.HkdfTotal` says why). -/
def TripleHkdfAgrees : Prop :=
  ∀ N salt ikm info, N.val ≤ 8160 → ∃ r, tacenta_kdf.hkdf_sha256 N salt ikm info = ok r ∧
    keyOf r = Model.Kdf.hkdf (sliceOf salt) (sliceOf ikm) (sliceOf info) N.val

@[step]
theorem hkdf_step (h : TripleHkdfAgrees) (N : Usize) (salt ikm info : Slice Std.U8)
    (hN : N.val ≤ 8160) :
    tacenta_kdf.hkdf_sha256 N salt ikm info ⦃ fun r =>
      keyOf r = Model.Kdf.hkdf (sliceOf salt) (sliceOf ikm) (sliceOf info) N.val ⦄ := by
  obtain ⟨r, hr, hv⟩ := h N salt ikm info hN; simp [hr, hv]

/-- Strictly stronger than `TripleT1.lean`'s totality-only assumption, so
that file needs no edits: this crate's `HkdfSha256Total` follows as a
corollary. -/
theorem TripleHkdfAgrees.total (h : TripleHkdfAgrees) : Tacenta.UnitT1.HkdfTotal :=
  fun N a b c hN => by obtain ⟨r, hr, _⟩ := h N a b c hN; exact ⟨r, hr⟩

/-! ## The `zeroize` wrapper round-trips, at the one width this crate wraps at

`split_secret` wraps its sixty-four-byte expansion in `Zeroizing` before
copying the two ratchets' secrets out of it (CR-15). `TripleT1.lean` needed
only that neither the wrapper's constructor nor its projection can fail
(`ZeroizingTotal`). Refinement needs the value to survive the wrapper, as
`T3.lean`'s `ZeroizingRoundTrips` does for the classical ratchet's root-key
step at the same width: without it nothing connects the expansion's output to
the halves copied out of it. It is true of the crate for the same reason: a
newtype constructor and its projection. Same two-conjunct shape as
`T3.lean`'s, and for **this crate's constants**, which are not the ratchet's
(`SpqrT1.lean`'s counting trap). -/
def ZeroizingRoundTrips : Prop :=
  ∀ inst : zeroize.Zeroize (Array Std.U8 64#usize),
    (∀ z, ∃ w, zeroize.Zeroizing.new inst z = ok w ∧
       zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref inst w = ok z) ∧
    (∀ w, ∃ z, zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref inst w = ok z)

/-- The round trip subsumes what T1 assumed, so a caller holding it does not
carry both; the second conjunct is what makes that so, exactly as in
`T3.lean`. -/
theorem ZeroizingRoundTrips.total (h : ZeroizingRoundTrips) :
    Tacenta.UnitT1.ZeroizingTotal := by
  intro inst
  exact ⟨fun z => let ⟨w, hw, _⟩ := (h inst).1 z; ⟨w, hw⟩, (h inst).2⟩

-- `TripleT1.lean` registered a stepping rule for the wrapper's projection
-- whose postcondition is only that it returned. Here that is too weak, as in
-- `T3.lean`: it would introduce the unwrapped value with nothing tying it to
-- what was wrapped. Removing it locally makes the tactic stop at the
-- projection so the round trip the wrapper's rule hands back can be applied
-- by hand.
-- `TripleT3.lean` erases `TripleT1.zeroizing_deref_step`. On the unit the one
-- copy of that rule is `UnitT1.zeroizing_deref_step`. `UnitT3.lean` and
-- `UnitSpqrT3.lean` erase it for themselves, but an erasure does not carry into
-- a module that imports them, so this file erases it again.
attribute [-step] Tacenta.UnitT1.zeroizing_deref_step

-- Not in `TripleT3.lean`: on the unit this file also sees `UnitTripleT1.lean`'s
-- two stepping rules, which `TripleT1.lean` never registered. `combine_step`
-- takes `UnitT1.HkdfTotal` and `zeroize_step` the general
-- `UnitSpqrT1.ZeroizeTotal`, and both say only that the call returned. Left in,
-- `step*` consumes the `combine` and `zeroize` calls with them before the proofs
-- below can apply `combine_refines` and the narrow `ZeroizeTotal` they carry,
-- and leaves those two totality facts as goals nothing here provides. Removing
-- the rules restores the stepping `TripleT3.lean`'s proofs were written against.
attribute [-step] Tacenta.UnitTripleT1.combine_step Tacenta.UnitTripleT1.zeroize_step

@[step]
theorem zeroizing_new_step (hz : ZeroizingRoundTrips)
    (inst : zeroize.Zeroize (Array Std.U8 64#usize)) (z : Array Std.U8 64#usize) :
    zeroize.Zeroizing.new inst z ⦃ fun w =>
      zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref inst w = ok z ⦄ := by
  obtain ⟨w, hw, hd⟩ := (hz inst).1 z; simp [hw, hd]

/-! ## The labels agree -/

theorem split_info_agrees : sliceOf SPLIT_INFO = Model.TripleRatchet.splitInfo := by
  native_decide

theorem combine_info_agrees : sliceOf COMBINE_INFO = Model.TripleRatchet.combineInfo := by
  native_decide

theorem split_info_len : (SPLIT_INFO : Slice Std.U8).length = 42 := by
  simp only [SPLIT_INFO, global_simps, Array.length_to_slice]; scalar_tac

theorem combine_info_len : (COMBINE_INFO : Slice Std.U8).length = 36 := by
  simp only [COMBINE_INFO, global_simps, Array.length_to_slice]; scalar_tac

/-! ## `split_secret`/`combine` refine the model's -/

theorem split_secret_refines (h : TripleHkdfAgrees) (hz : ZeroizingRoundTrips) (sk : Slice Std.U8) :
    split_secret sk ⦃ fun r =>
      (keyOf r.1, keyOf r.2) = Model.TripleRatchet.splitSecret (sliceOf sk) ⦄ := by
  unfold split_secret
  step*
  simp only [out_post]
  step*
  all_goals (try (simp_all only []; scalar_tac))
  all_goals (try (
    have hzero : List.map u8 (Array.repeat 32#usize 0#u8 : Array Std.U8 32#usize).val
        = List.replicate 32 (0 : UInt8) := by native_decide
    simp only [Model.TripleRatchet.splitSecret, ← split_info_agrees]
    simp_all [keyOf, sliceOf, u8, List.slice, List.map_take, List.map_drop]))

theorem combine_refines (h : TripleHkdfAgrees) (mk_classical mk_pq : Array Std.U8 32#usize) :
    combine mk_classical mk_pq ⦃ fun r =>
      keyOf r = Model.TripleRatchet.combine (keyOf mk_classical) (keyOf mk_pq) ⦄ := by
  unfold combine
  step*
  simp only [Model.TripleRatchet.combine]
  rw [← combine_info_agrees]
  simp_all [keyOf, sliceOf]

/-! ## The two inner ratchets, bundled as agreement

The bundles as `TripleT3.lean` states them, kept so that the theorems below read
the same as their originals. There each is an assumption. Here both are proved,
by `ratchet_agrees_for` and `spqr_agrees_for` at the end of the file, and each
clause's `-- mirrors:` comment names the unit theorem that proof uses for it, or
says why there is none. -/

/-- A translated ratchet header as the model's -- concrete on both sides, so
this is a plain field-by-field fact, not part of the bundle below. -/
structure RatchetHeaderR (hdr : tacenta_ratchet.Header) (mh : Model.State.Header) : Prop where
  dh : keyOf hdr.dh = mh.dh
  pn : hdr.pn.val = mh.pn
  n  : hdr.n.val = mh.n

/-- A translated ratchet label set as the model's. One constructor on each
side today. -/
def ratchetLabelsOf : tacenta_ratchet.LabelSet → Model.State.LabelSet
  | .Tacenta => .tacenta

/-- A translated sparse-ratchet output as the model's. -/
def spqrOutputOf (o : tacenta_spqr.Output) : Model.SparseRatchet.Output :=
  ⟨o.key_epoch.val, keyOf o.key⟩

/-- Bundled agreement for the classical ratchet's calling surface, through an
abstraction `α`. Covers exactly what this file's theorems need: `clone`, the two
initialisers, the three small accessors `TripleT1.lean` already treats as this
state's public interface, and `send`/`receive`. The crate calls more than that;
nothing here speaks for the rest.

The `send`/`receive` clauses carry the preconditions `UnitT3.lean`'s
`send_refines`/`receive_refines` carry -- `send` none at all, `receive` the three
below -- transported through `α`: the at-most-one-stored-key bound is that
theorem's `matchesHeader mh` written with projections (definitionally the same
predicate, `UnitT3.matchesHeader_eta`), the store bound reads
`Model.State.maxSkippedStore` for `MAX_SKIPPED_STORE.val`
(`UnitT3.max_skipped_store_agrees`), and the clock bound reads `(α s).events` for
`s.events.val` at `+ 1`. On the unit `ratchet_agrees_for` carries out each of
those steps, so a clause that asked less than `UnitT3.receive_refines` needs
would not prove.

No inner theorem covers the `clone` and accessor clauses; `ratchet_agrees_for`
proves them from `UnitTripleT1.ratchet_state_clone_id` and the accessors'
definitions. The two initialisers are `UnitT3.init_sender_refines` and
`init_receiver_refines`. -/
def RatchetAgreesFor (α : tacenta_ratchet.State → Model.State.State) : Prop :=
  -- mirrors: nothing -- no inner theorem; `ratchet_agrees_for` uses `UnitTripleT1.ratchet_state_clone_id`
  (∀ s, ∃ r, tacenta_ratchet.State.Insts.CoreCloneClone.clone s = ok r ∧ α r = α s) ∧
  -- mirrors: nothing -- an accessor no inner theorem covers; `ratchet_agrees_for` reads the field
  (∀ s, ∃ r, tacenta_ratchet.State.sending_public s = ok r ∧ keyOf r = (α s).dhsPub) ∧
  -- mirrors: nothing -- an accessor no inner theorem covers; `ratchet_agrees_for` reads the field
  (∀ s, ∃ r, tacenta_ratchet.State.send_count s = ok r ∧ r.val = (α s).ns) ∧
  -- mirrors: nothing -- an accessor no inner theorem covers; `ratchet_agrees_for` reads the field
  (∀ s, ∃ r, tacenta_ratchet.State.receive_count s = ok r ∧ r.val = (α s).nr) ∧
  -- mirrors: Tacenta.UnitT3.init_sender_refines in UnitT3.lean
  (∀ (ec our_pub peer_pub dh_out : Array Std.U8 32#usize) (labels : tacenta_ratchet.LabelSet),
    ∃ r, tacenta_ratchet.init_sender ec our_pub peer_pub dh_out labels = ok r ∧
      α r = Model.Ratchet.initSender (keyOf ec) (keyOf our_pub) (keyOf peer_pub) (keyOf dh_out)
        (ratchetLabelsOf labels)) ∧
  -- mirrors: Tacenta.UnitT3.init_receiver_refines in UnitT3.lean
  (∀ (ec our_pub : Array Std.U8 32#usize) (labels : tacenta_ratchet.LabelSet),
    ∃ r, tacenta_ratchet.init_receiver ec our_pub labels = ok r ∧
      α r = Model.Ratchet.initReceiver (keyOf ec) (keyOf our_pub) (ratchetLabelsOf labels)) ∧
  -- mirrors: Tacenta.UnitT3.send_refines in UnitT3.lean
  (∀ s, ∃ r, tacenta_ratchet.send s = ok r ∧
    (∀ hdr mk, r.1 = core.result.Result.Ok (hdr, mk) →
      ∃ m' mh, Model.Ratchet.send (α s) = some (m', mh, keyOf mk) ∧
        α r.2 = m' ∧ RatchetHeaderR hdr mh) ∧
    (r.1 = core.result.Result.Err tacenta_ratchet.RatchetError.NoSendingChain →
      Model.Ratchet.send (α s) = none)) ∧
  -- mirrors: Tacenta.UnitT3.receive_refines in UnitT3.lean
  (∀ (s : tacenta_ratchet.State) (hdr : tacenta_ratchet.Header) (mh : Model.State.Header),
    RatchetHeaderR hdr mh →
    ∀ (dh_out_recv dh_out_send new_dhs_pub : Array Std.U8 32#usize),
    ((α s).skipped.filter (fun x => x.1 == mh.dh && x.2.1 == mh.n)).length ≤ 1 →
    max (α s).skipped.length Model.State.maxSkippedStore + Model.State.maxSkip ≤ Usize.max →
    (α s).events + 1 < Std.U32.max →
    ∃ r, tacenta_ratchet.receive s hdr dh_out_recv dh_out_send new_dhs_pub = ok r ∧
      ∀ mk, r.1 = core.result.Result.Ok mk →
        ∃ m', Model.Ratchet.receive (α s) mh (keyOf dh_out_recv) (keyOf dh_out_send)
              (keyOf new_dhs_pub) = some (m', keyOf mk) ∧ α r.2 = m')

def RatchetAgrees : Prop := ∃ α, RatchetAgreesFor α

/-- Bundled agreement for the sparse ratchet's calling surface, through an
abstraction `β`. Covers `clone`, the two initialisers, `epoch`, and
`send`/`receive`.

The `send`/`receive` clauses carry the preconditions `UnitSpqrT3.lean`'s
`send_refines`/`receive_refines` carry, transported through `β`: the epoch bound
at the reserved ceiling, the chain room at `+ 1` for `send` and `+ 2` for
`receive`, the epoch-window bounds on the chain table, the stored keys and the
incoming output, the skip room read as `Model.SparseRatchet.maxSkip` for
`MAX_SKIP.val` (`UnitSpqrT3.max_skip_agrees`), the at-most-one stored key for
`(epoch, n)`, and the chain-counter bound. That last one is stated here over
`(β s).chains` and the model's `Chain`, where `UnitSpqrT3.lean` states it over the
real state's own chain table; `spqr_agrees_for` crosses that gap, since each real
chain is a model chain with the same counter.

No inner theorem covers `clone`, `epoch`, `init_alice` or `init_bob`.
`spqr_agrees_for` proves the first two from `UnitTripleT1.spqr_state_clone_id` and
the accessor's definition, and the initialisers from `spqr_init_refines`, which
this file proves from the key derivation's refinement. -/
def SpqrAgreesFor (β : tacenta_spqr.State → Model.SparseRatchet.State) : Prop :=
  -- mirrors: nothing -- no inner theorem; `spqr_agrees_for` uses `UnitTripleT1.spqr_state_clone_id`
  (∀ s, ∃ r, tacenta_spqr.State.Insts.CoreCloneClone.clone s = ok r ∧ β r = β s) ∧
  -- mirrors: nothing -- an accessor no inner theorem covers; `spqr_agrees_for` reads the field
  (∀ s, ∃ r, tacenta_spqr.State.impl.epoch s = ok r ∧ r.val = (β s).epoch) ∧
  -- mirrors: nothing -- no inner theorem; `spqr_agrees_for` uses `spqr_init_refines`
  (∀ sk : Slice Std.U8, ∃ r, tacenta_spqr.State.init_alice sk = ok r ∧
    β r = Model.SparseRatchet.initAlice (sliceOf sk)) ∧
  -- mirrors: nothing -- no inner theorem; `spqr_agrees_for` uses `spqr_init_refines`
  (∀ sk : Slice Std.U8, ∃ r, tacenta_spqr.State.init_bob sk = ok r ∧
    β r = Model.SparseRatchet.initBob (sliceOf sk)) ∧
  -- mirrors: Tacenta.UnitSpqrT3.send_refines in UnitSpqrT3.lean
  (∀ (s : tacenta_spqr.State) (e : Std.U64) (out : Option tacenta_spqr.Output),
    (β s).epoch + 1 < Std.U64.max →
    (β s).chains.length + 1 < Usize.max →
    (∀ p ∈ (β s).chains, p.1 + Model.SparseRatchet.epochsKept ≤ Std.U64.max) →
    (∀ sk ∈ (β s).skipped, sk.1 + Model.SparseRatchet.epochsKept ≤ Std.U64.max) →
    (∀ o : tacenta_spqr.Output, out = some o →
      o.key_epoch.val + Model.SparseRatchet.epochsKept ≤ Std.U64.max) →
    (∀ p ∈ (β s).chains, ∀ ch : Model.SparseRatchet.Chain,
      (p.2.send = some ch ∨ p.2.receive = some ch) → ch.n < Std.U64.max) →
    ∃ r, tacenta_spqr.State.send s e out = ok r ∧
      (∀ n mk, r.1 = core.result.Result.Ok (n, mk) →
        ∃ m', Model.SparseRatchet.send (β s) e.val (out.map spqrOutputOf)
            = some (m', n.val, keyOf mk) ∧ β r.2 = m') ∧
      (∀ err, r.1 = core.result.Result.Err err →
        Model.SparseRatchet.send (β s) e.val (out.map spqrOutputOf) = none)) ∧
  -- mirrors: Tacenta.UnitSpqrT3.receive_refines in UnitSpqrT3.lean
  (∀ (s : tacenta_spqr.State) (receiving_epoch : Std.U64) (out : Option tacenta_spqr.Output)
      (n : Std.U64),
    (β s).epoch + 1 < Std.U64.max →
    (β s).chains.length + 2 < Usize.max →
    (∀ p ∈ (β s).chains, p.1 + Model.SparseRatchet.epochsKept ≤ Std.U64.max) →
    (∀ sk ∈ (β s).skipped, sk.1 + Model.SparseRatchet.epochsKept ≤ Std.U64.max) →
    (∀ o : tacenta_spqr.Output, out = some o →
      o.key_epoch.val + Model.SparseRatchet.epochsKept ≤ Std.U64.max) →
    (β s).skipped.length + Model.SparseRatchet.maxSkip ≤ Usize.max →
    ((β s).skipped.filter
      (fun x => x.1 == receiving_epoch.val && x.2.1 == n.val)).length ≤ 1 →
    (∀ p ∈ (β s).chains, ∀ ch : Model.SparseRatchet.Chain,
      (p.2.send = some ch ∨ p.2.receive = some ch) → ch.n < Std.U64.max) →
    ∃ r, tacenta_spqr.State.receive s receiving_epoch out n = ok r ∧
      match Model.SparseRatchet.receive (β s) receiving_epoch.val (out.map spqrOutputOf) n.val with
      | none => ∃ err, r.1 = core.result.Result.Err err
      | some (m', k) => ∃ key, r.1 = core.result.Result.Ok key ∧ keyOf key = k ∧ β r.2 = m')

def SpqrAgrees : Prop := ∃ β, SpqrAgreesFor β

/-! ## The composed state relation -/

/-- The translated triple state refines the model's, given the two inner
abstractions. -/
def StateRefines (α : tacenta_ratchet.State → Model.State.State)
    (β : tacenta_spqr.State → Model.SparseRatchet.State)
    (s : State) (m : Model.Triple.State) : Prop :=
  α s.classical = m.classical ∧ β s.post_quantum = m.postQuantum

/-- The translated composite header refines the model's: the classical half
via `RatchetHeaderR`, the other two fields a plain equality since both sides
are already just a `U64`/`Nat`. -/
structure TripleHeaderR (hdr : Header) (mh : Model.Triple.Header) : Prop where
  dr    : RatchetHeaderR hdr.dr mh.dr
  epoch : hdr.epoch.val = mh.epoch
  pq_n  : hdr.pq_n.val = mh.pqN

/-! ## `send` refines the model's

The failure branch is not a blanket "either ratchet failing means the model
fails", because that does not hold. The post-quantum side's failure
clause is unconditional (`SpqrAgreesFor`, backed by `UnitSpqrT3.lean`'s own
`hcounter`-guarded `send_refines`), but the classical ratchet's is not:
`UnitT3.lean`'s own `send_refines` proves the model-failure correspondence only
for `RatchetError.NoSendingChain`, not for `ChainExhausted` (the real `u32`
send counter wrapping), because `Model.Ratchet.send` counts in `Nat` and so
has no failure mode to correspond to that overflow. `RatchetAgreesFor`
states exactly that -- `NoSendingChain` only -- rather than an unrestricted
`∀ e`.
The theorem's stated postcondition below is scoped to match: it only claims
the failure-implies-`none` correspondence when the reported error is either
a post-quantum one or specifically `Classical NoSendingChain`, and proves
nothing at all about a `Classical ChainExhausted` failure -- the same
finite-width boundary `UnitT3.lean` already excludes, one layer up rather than
newly introduced here. -/

theorem send_refines {α : tacenta_ratchet.State → Model.State.State}
    {β : tacenta_spqr.State → Model.SparseRatchet.State}
    (hra : RatchetAgreesFor α) (hsa : SpqrAgreesFor β) (hthk : TripleHkdfAgrees)
    (hz : ZeroizeTotal)
    {s : State} {m : Model.Triple.State} (hrel : StateRefines α β s m)
    (sending_epoch : Std.U64) (output : Option tacenta_spqr.Output)
    (hroom : m.postQuantum.chains.length + 1 < Usize.max)
    (hcb : ∀ p ∈ m.postQuantum.chains, p.1 + Model.SparseRatchet.epochsKept ≤ Std.U64.max)
    (hsb : ∀ sk ∈ m.postQuantum.skipped, sk.1 + Model.SparseRatchet.epochsKept ≤ Std.U64.max)
    (hnewb : ∀ o : tacenta_spqr.Output, output = some o →
      o.key_epoch.val + Model.SparseRatchet.epochsKept ≤ Std.U64.max)
    (hepoch : m.postQuantum.epoch + 1 < Std.U64.max)
    (hcounter : ∀ p ∈ m.postQuantum.chains, ∀ ch : Model.SparseRatchet.Chain,
      (p.2.send = some ch ∨ p.2.receive = some ch) → ch.n < Std.U64.max) :
    State.send s sending_epoch output ⦃ fun r =>
      (∀ hdr mk, r.1 = core.result.Result.Ok (hdr, mk) →
        ∃ m' mh key, Model.Triple.send m sending_epoch.val (output.map spqrOutputOf)
            = some (m', mh, key)
          ∧ StateRefines α β r.2 m' ∧ TripleHeaderR hdr mh ∧ keyOf mk = key)
      ∧ (∀ e, r.1 = core.result.Result.Err e →
          (e = TripleError.Classical tacenta_ratchet.RatchetError.NoSendingChain ∨
            ∃ e', e = TripleError.PostQuantum e') →
          Model.Triple.send m sending_epoch.val (output.map spqrOutputOf) = none) ⦄ := by
  obtain ⟨hrClone, _, _, _, _, _, hrSend, _⟩ := hra
  obtain ⟨hsClone, _, _, _, hsSend, _⟩ := hsa
  obtain ⟨hrelC, hrelQ⟩ := hrel
  unfold State.send State.Insts.CoreCloneClone.clone Model.Triple.send
  obtain ⟨sc, hsc, hscEq⟩ := hrClone s.classical
  obtain ⟨sq, hsq, hsqEq⟩ := hsClone s.post_quantum
  simp only [hsc, hsq]
  step*
  obtain ⟨r, hr, hrPost⟩ := hrSend sc
  simp only [hr]
  step*
  obtain ⟨r1, sr⟩ := r
  rcases r1 with v | e
  · step*
    obtain ⟨dr, mk_ec⟩ := v
    rw [← hrelQ, ← hsqEq] at hroom hcb hsb hepoch hcounter
    obtain ⟨m1, mh, hsendEq, hstateEq, hheader⟩ := hrPost.1 dr mk_ec rfl
    rw [hscEq, hrelC] at hsendEq
    simp only [hsendEq]
    obtain ⟨r1', hr1, hr1Post⟩ := hsSend sq sending_epoch output hepoch hroom hcb hsb hnewb hcounter
    simp only [hr1]
    step*
    obtain ⟨r1'', s1⟩ := r1'
    rcases r1'' with v1 | e1
    · step*
      obtain ⟨n', mk_pq⟩ := v1
      obtain ⟨m2, hspqEq, hstateEq2⟩ := hr1Post.1 n' mk_pq rfl
      rw [hsqEq, hrelQ] at hspqEq
      simp only [hspqEq]
      step*
      step with combine_refines hthk mk_ec mk_pq
      obtain ⟨_, hkbz⟩ := hz mk_ec
      obtain ⟨_, hkbz1⟩ := hz mk_pq
      simp only [hkbz, hkbz1]
      refine ⟨?_, ?_⟩
      · intro hdr mk hcon
        injection hcon with hcon
        obtain ⟨hdreq, hkeq⟩ := Prod.mk.injEq .. |>.mp hcon
        refine ⟨_, _, _, rfl, ⟨hstateEq, hstateEq2⟩,
          ⟨by rw [← hdreq]; exact hheader, by rw [← hdreq], by rw [← hdreq]⟩, ?_⟩
        rw [← hkeq]
        exact key_post
      · intro e' hcon; injection hcon
    · step*
      have hspqNone := hr1Post.2 e1 rfl
      rw [hsqEq, hrelQ] at hspqNone
      simp only [hspqNone]
      obtain ⟨_, hkbz2⟩ := hz mk_ec
      simp only [hkbz2]
      refine ⟨?_, ?_⟩
      · intro hdr mk hcon; injection hcon
      · intro e' he' hcov; trivial
  · step*
    rcases e with _ | _ | _ | _ | _
    · refine ⟨?_, ?_⟩
      · intro hdr mk hcon; injection hcon
      · intro e' he' hcov
        injection he' with heq
        rcases hcov with hcov | ⟨e'', hcov⟩
        · rw [← heq] at hcov; injection hcov with hcov; injection hcov
        · rw [← heq] at hcov; injection hcov
    · refine ⟨?_, ?_⟩
      · intro hdr mk hcon; injection hcon
      · intro e' he' hcov
        injection he' with heq
        rcases hcov with hcov | ⟨e'', hcov⟩
        · rw [← heq] at hcov; injection hcov with hcov; injection hcov
        · rw [← heq] at hcov; injection hcov
    · have hnone := hrPost.2 rfl
      rw [hscEq] at hnone
      rw [hrelC] at hnone
      simp only [hnone]
      refine ⟨?_, ?_⟩
      · intro hdr mk hcon; injection hcon
      · intro e' he' hcov; trivial
    · refine ⟨?_, ?_⟩
      · intro hdr mk hcon; injection hcon
      · intro e' he' hcov
        injection he' with heq
        rcases hcov with hcov | ⟨e'', hcov⟩
        · rw [← heq] at hcov; injection hcov with hcov; injection hcov
        · rw [← heq] at hcov; injection hcov
    · refine ⟨?_, ?_⟩
      · intro hdr mk hcon; injection hcon
      · intro e' he' hcov
        injection he' with heq
        rcases hcov with hcov | ⟨e'', hcov⟩
        · rw [← heq] at hcov; injection hcov with hcov; injection hcov
        · rw [← heq] at hcov; injection hcov

/-! ## `receive` refines the model's -/

/-- `State.receive` refines `Model.Triple.receive`. Success-case only, mirroring
`Translation/UnitT3.lean`'s own `receive_refines` for the classical ratchet: that
theorem states no failure-branch fact at all, so there is nothing to compose
a triple-level failure claim from -- this is not a new weakening, it is the
same limitation the leaf crate's own claim already carries. -/
theorem receive_refines {α : tacenta_ratchet.State → Model.State.State}
    {β : tacenta_spqr.State → Model.SparseRatchet.State}
    (hra : RatchetAgreesFor α) (hsa : SpqrAgreesFor β) (hthk : TripleHkdfAgrees)
    (hz : ZeroizeTotal)
    {s : State} {m : Model.Triple.State} (hrel : StateRefines α β s m)
    (header : Header) (mh : Model.State.Header) (hheader : RatchetHeaderR header.dr mh)
    (dh_out_recv dh_out_send new_dhs_pub : Array Std.U8 32#usize)
    (output : Option tacenta_spqr.Output)
    (hone : (m.classical.skipped.filter (fun x => x.1 == mh.dh && x.2.1 == mh.n)).length ≤ 1)
    (hs : max m.classical.skipped.length Model.State.maxSkippedStore + Model.State.maxSkip ≤ Usize.max)
    (hevents : m.classical.events + 1 < Std.U32.max)
    (hepoch : m.postQuantum.epoch + 1 < Std.U64.max)
    (hroom : m.postQuantum.chains.length + 2 < Usize.max)
    (hcb : ∀ p ∈ m.postQuantum.chains, p.1 + Model.SparseRatchet.epochsKept ≤ Std.U64.max)
    (hsb : ∀ sk ∈ m.postQuantum.skipped, sk.1 + Model.SparseRatchet.epochsKept ≤ Std.U64.max)
    (hnewb : ∀ o : tacenta_spqr.Output, output = some o →
      o.key_epoch.val + Model.SparseRatchet.epochsKept ≤ Std.U64.max)
    (hskiproom : m.postQuantum.skipped.length + Model.SparseRatchet.maxSkip ≤ Usize.max)
    (hone2 : (m.postQuantum.skipped.filter (fun x => x.1 == header.epoch.val && x.2.1 == header.pq_n.val)).length ≤ 1)
    (hcounter : ∀ p ∈ m.postQuantum.chains, ∀ ch : Model.SparseRatchet.Chain,
      (p.2.send = some ch ∨ p.2.receive = some ch) → ch.n < Std.U64.max) :
    State.receive s header dh_out_recv dh_out_send new_dhs_pub output ⦃ fun r =>
      ∀ st key, r = core.result.Result.Ok (st, key) →
        ∃ m' k, Model.Triple.receive m { dr := mh, epoch := header.epoch.val, pqN := header.pq_n.val }
            (keyOf dh_out_recv) (keyOf dh_out_send) (keyOf new_dhs_pub) (output.map spqrOutputOf) = some (m', k)
          ∧ StateRefines α β st m' ∧ keyOf key = k ⦄ := by
  obtain ⟨hrClone, -, -, -, -, -, -, hrRecv⟩ := hra
  obtain ⟨hsClone, -, -, -, -, hsRecv⟩ := hsa
  obtain ⟨hrelC, hrelQ⟩ := hrel
  unfold State.receive State.Insts.CoreCloneClone.clone Model.Triple.receive
  obtain ⟨sc, hsc, hscEq⟩ := hrClone s.classical
  obtain ⟨sq, hsq, hsqEq⟩ := hsClone s.post_quantum
  simp only [hsc, hsq]
  step*
  rw [← hrelQ, ← hsqEq] at hroom hcb hsb hone2 hskiproom hcounter
  rw [← hrelC, ← hscEq] at hone hs hevents
  obtain ⟨r, hr, hrPost⟩ := hrRecv sc header.dr mh hheader dh_out_recv dh_out_send new_dhs_pub hone hs hevents
  simp only [hr]
  step*
  obtain ⟨r1, sr⟩ := r
  rcases r1 with v | e
  · step*
    rw [hscEq, hrelC] at hrPost
    obtain ⟨m1, hrecvEq, hstateEq⟩ := hrPost v rfl
    simp only [hrecvEq]
    rw [← hrelQ, ← hsqEq] at hepoch
    obtain ⟨r1', hr1, hr1Post⟩ := hsRecv sq header.epoch output header.pq_n
      hepoch hroom hcb hsb hnewb hskiproom hone2 hcounter
    simp only [hr1]
    step*
    obtain ⟨r1'', s1⟩ := r1'
    rcases r1'' with v1 | e1
    · step*
      rw [hsqEq, hrelQ] at hr1Post
      rcases hcase2 : Model.SparseRatchet.receive m.postQuantum header.epoch.val
          (Option.map spqrOutputOf output) header.pq_n.val with _ | vm2
      · exfalso
        rw [hcase2] at hr1Post
        obtain ⟨err, herr⟩ := hr1Post
        simp at herr
      · rw [hcase2] at hr1Post
        obtain ⟨keyw, hspqEq1, hspqEq2, hspqStateEq⟩ := hr1Post
        step*
        step with combine_refines hthk v v1
        obtain ⟨_, hkbz⟩ := hz v
        obtain ⟨_, hkbz1⟩ := hz v1
        simp only [hkbz, hkbz1]
        intro st key hcon
        injection hcon with hcon
        obtain ⟨hsteq, hkeq⟩ := Prod.mk.injEq .. |>.mp hcon
        subst hsteq
        refine ⟨_, _, rfl, ⟨hstateEq, hspqStateEq⟩, ?_⟩
        simp only [] at hspqEq1
        injection hspqEq1 with hv1eq
        rw [← hv1eq] at hspqEq2
        rw [← hkeq, ← hspqEq2]
        exact key_post
    · step*
      obtain ⟨_, hkbz2⟩ := hz v
      simp only [hkbz2]
      intro st key hcon; injection hcon
  · step*

/-! ## `commit` refines the model's -/

/-- Trivial on both sides: a bare projection, not a step either model needed
to prove anything about until now. -/
theorem commit_refines {α : tacenta_ratchet.State → Model.State.State}
    {β : tacenta_spqr.State → Model.SparseRatchet.State}
    (self next : State) {m mNext : Model.Triple.State}
    (hrelNext : StateRefines α β next mNext) :
    State.commit self next ⦃ fun r => StateRefines α β r (Model.Triple.commit m mNext) ⦄ := by
  unfold State.commit Model.Triple.commit
  exact hrelNext

/-! ## The two inner bundles, discharged on the unit

`TripleT3.lean` has to assume `RatchetAgreesFor α` and `SpqrAgreesFor β`: in the
Triple's standalone translation the inner states are opaque, so no abstraction
can be written down and no inner theorem can be cited. On the unit neither
obstacle exists. Each inner refinement relation fixes every field of its model
state, so reading it field by field gives the abstraction, and the inner
refinements, restated about the unit in `UnitT3.lean` and `UnitSpqrT3.lean`,
prove the clauses. What remains assumed is the boundary those theorems take,
which `ratchet_agrees_for` and `spqr_agrees_for` list as their hypotheses. -/

/-- The classical abstraction: `UnitT3.StateR`, read field by field. -/
def ratchetAbs (s : tacenta_ratchet.State) : Model.State.State where
  dhsPub  := Tacenta.UnitT3.keyOf s.dhs_pub
  dhrPub  := s.dhr_pub.map Tacenta.UnitT3.keyOf
  rk      := Tacenta.UnitT3.keyOf s.rk
  cks     := s.cks.map Tacenta.UnitT3.keyOf
  ckr     := s.ckr.map Tacenta.UnitT3.keyOf
  ns      := s.ns.val
  nr      := s.nr.val
  pn      := s.pn.val
  skipped := s.skipped.val.map Tacenta.UnitT3.skippedOf
  events  := s.events.val
  labels  := Tacenta.UnitT3.labelsOf s.labels

theorem ratchetAbs_stateR (s : tacenta_ratchet.State) :
    Tacenta.UnitT3.StateR s (ratchetAbs s) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `UnitT3.StateR` pins every field, so the model state it relates a real
state to is that state's abstraction. -/
theorem ratchetAbs_eq {s : tacenta_ratchet.State} {m : Model.State.State}
    (h : Tacenta.UnitT3.StateR s m) : ratchetAbs s = m := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  cases m
  dsimp only at h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  subst h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  rfl

/-- The sparse abstraction: `UnitSpqrT3.StateRefines`, read field by field. -/
def spqrAbs (s : tacenta_spqr.State) : Model.SparseRatchet.State where
  rk        := Tacenta.UnitSpqrT3.keyOf s.rk
  epoch     := s.epoch.val
  chains    := s.chains.val.map Tacenta.UnitSpqrT3.chainsEntryOf
  skipped   := s.skipped.val.map Tacenta.UnitSpqrT3.skippedOf
  direction := Tacenta.UnitSpqrT3.directionOf s.direction

theorem spqrAbs_refines (s : tacenta_spqr.State) :
    Tacenta.UnitSpqrT3.StateRefines s (spqrAbs s) :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem spqrAbs_eq {s : tacenta_spqr.State} {m : Model.SparseRatchet.State}
    (h : Tacenta.UnitSpqrT3.StateRefines s m) : spqrAbs s = m := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  cases m
  dsimp only at h1 h2 h3 h4 h5
  subst h1 h2 h3 h4 h5
  rfl

/-- The sparse initialiser refines the model's. No inner file proves this: it
is the key derivation's refinement followed by building a one-entry chain
table, which the library's slice and vector constructors do without failing. -/
theorem spqr_init_refines (h : Tacenta.UnitSpqrT3.SpqrHkdfAgrees)
    (hz : Tacenta.UnitSpqrT3.ZeroizingRoundTrips96) (sk : Slice Std.U8)
    (d : tacenta_spqr.Direction) :
    ∃ r, tacenta_spqr.State.init sk d = ok r ∧
      spqrAbs r = Model.SparseRatchet.init (Tacenta.UnitSpqrT3.sliceOf sk)
        (Tacenta.UnitSpqrT3.directionOf d) := by
  obtain ⟨⟨rk, k1, k2⟩, hr, heq⟩ :=
    Std.WP.spec_imp_exists (Tacenta.UnitSpqrT3.kdf_init_refines h hz sk)
  unfold tacenta_spqr.State.init
  cases d <;> simp [hr, lift, alloc.slice.Slice.into_vec, Array.to_slice, Array.make,
    spqrAbs, Model.SparseRatchet.init, ← heq, Tacenta.UnitSpqrT3.chainsEntryOf,
    Tacenta.UnitSpqrT3.chainsOf, Tacenta.UnitSpqrT3.chainOf,
    Tacenta.UnitSpqrT3.directionOf, alloc.vec.Vec.new]

/-- `RatchetAgreesFor`, proved. Every clause is `UnitT3.lean`'s theorem for that
call, a field read, or `UnitTripleT1.lean`'s clone lemma, and the hypotheses are
the boundary those take: `HmacAgrees`, `HkdfAgrees`, `ZeroizingRoundTrips`,
`VecRemoveTotal` and `DerivedKeysModel` for the classical calls, and
`OptionCloneTotal` for `clone`. -/
theorem ratchet_agrees_for (hopt : Tacenta.UnitSpqrT1.OptionCloneTotal)
    (hmac : Tacenta.UnitT3.HmacAgrees) (hkdf : Tacenta.UnitT3.HkdfAgrees)
    (hzr : Tacenta.UnitT3.ZeroizingRoundTrips) (hvr : Tacenta.UnitT1.VecRemoveTotal)
    [Tacenta.UnitT1.DerivedKeysModel] :
    RatchetAgreesFor ratchetAbs := by
  unfold RatchetAgreesFor
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s
    exact ⟨s, Tacenta.UnitTripleT1.ratchet_state_clone_id hopt s, rfl⟩
  · intro s
    exact ⟨s.dhs_pub, rfl, rfl⟩
  · intro s
    exact ⟨s.ns, rfl, rfl⟩
  · intro s
    exact ⟨s.nr, rfl, rfl⟩
  · intro ec our_pub peer_pub dh_out labels
    obtain ⟨r, hr, hR⟩ := Std.WP.spec_imp_exists
      (Tacenta.UnitT3.init_sender_refines hkdf hzr ec our_pub peer_pub dh_out labels)
    refine ⟨r, hr, ?_⟩
    rw [ratchetAbs_eq hR]
    cases labels; rfl
  · intro ec our_pub labels
    obtain ⟨r, hr, hR⟩ := Std.WP.spec_imp_exists
      (Tacenta.UnitT3.init_receiver_refines ec our_pub labels)
    refine ⟨r, hr, ?_⟩
    rw [ratchetAbs_eq hR]
    cases labels; rfl
  · intro s
    obtain ⟨r, hr, hok, herr⟩ := Std.WP.spec_imp_exists
      (Tacenta.UnitT3.send_refines hmac s (ratchetAbs s) (ratchetAbs_stateR s))
    refine ⟨r, hr, fun hdr mk hmk => ?_, herr⟩
    obtain ⟨m', mh, hsend, hR', hH⟩ := hok hdr mk hmk
    exact ⟨m', mh, hsend, ratchetAbs_eq hR', ⟨hH.dh, hH.pn, hH.n⟩⟩
  · intro s hdr mh hH dh_out_recv dh_out_send new_dhs_pub hone hs hroom
    obtain ⟨r, hr, hpost⟩ := Std.WP.spec_imp_exists
      (Tacenta.UnitT3.receive_refines hmac hkdf hzr hvr s (ratchetAbs s) (ratchetAbs_stateR s)
        hdr mh ⟨hH.dh, hH.pn, hH.n⟩ dh_out_recv dh_out_send new_dhs_pub
        (by rw [← Tacenta.UnitT3.matchesHeader_eta]; exact hone)
        (by simpa [ratchetAbs, Tacenta.UnitT3.max_skipped_store_agrees,
              Tacenta.UnitT3.max_skip_agrees] using hs)
        hroom)
    refine ⟨r, hr, fun mk hmk => ?_⟩
    obtain ⟨m', hrecv, hR'⟩ := hpost mk hmk
    exact ⟨m', hrecv, ratchetAbs_eq hR'⟩

/-- `SpqrAgreesFor`, proved. The initialisers are `spqr_init_refines`; `send` and
`receive` are `UnitSpqrT3.lean`'s theorems, with each precondition carried from
the model state to the real one through the abstraction; `clone` and `epoch` are
`UnitTripleT1.lean`'s clone lemma and a field read. The hypotheses are the
boundary `UnitSpqrT3.lean`'s theorems take. -/
theorem spqr_agrees_for (hkr : Tacenta.UnitSpqrT3.SpqrHkdfAgrees)
    (hz96 : Tacenta.UnitSpqrT3.ZeroizingRoundTrips96)
    (hz64 : Tacenta.UnitSpqrT3.ZeroizingRoundTrips64)
    (hret : Tacenta.UnitSpqrT3.VecRetainAgrees) (happ : Tacenta.UnitSpqrT3.VecAppendAgrees)
    (hrm : Tacenta.UnitSpqrT3.VecRemoveAgrees) (hzs : Tacenta.UnitSpqrT1.ZeroizeTotal)
    (hopt : Tacenta.UnitSpqrT1.OptionCloneTotal) :
    SpqrAgreesFor spqrAbs := by
  -- The chain-counter bound: the bundle states it over the model's chain table,
  -- the inner theorems over the real one, and each real chain is a model chain
  -- with the same counter.
  have counter : ∀ s : tacenta_spqr.State,
      (∀ p ∈ (spqrAbs s).chains, ∀ ch : Model.SparseRatchet.Chain,
        (p.2.send = some ch ∨ p.2.receive = some ch) → ch.n < Std.U64.max) →
      ∀ p ∈ s.chains.val, ∀ ch : tacenta_spqr.Chain,
        (p.2.send = some ch ∨ p.2.receive = some ch) → ch.n.val < Std.U64.max := by
    intro s h p hp ch hch
    exact h (Tacenta.UnitSpqrT3.chainsEntryOf p) (List.mem_map.2 ⟨p, hp, rfl⟩)
      (Tacenta.UnitSpqrT3.chainOf ch)
      (by rcases hch with hch | hch <;>
            simp [Tacenta.UnitSpqrT3.chainsEntryOf, Tacenta.UnitSpqrT3.chainsOf, hch])
  unfold SpqrAgreesFor
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s
    exact ⟨s, Tacenta.UnitTripleT1.spqr_state_clone_id s, rfl⟩
  · intro s
    exact ⟨s.epoch, rfl, rfl⟩
  · intro sk
    obtain ⟨r, hr, he⟩ := spqr_init_refines hkr hz96 sk .A2b
    exact ⟨r, hr, he⟩
  · intro sk
    obtain ⟨r, hr, he⟩ := spqr_init_refines hkr hz96 sk .B2a
    exact ⟨r, hr, he⟩
  · intro s e out hepoch hroom hcb hsb hnewb hcounter
    obtain ⟨r, hr, hok, herr⟩ := Std.WP.spec_imp_exists
      (Tacenta.UnitSpqrT3.send_refines hkr hz96 hz64 hret hzs hopt (spqrAbs_refines s) e out
        hepoch (by simpa [spqrAbs] using hroom)
        (fun p hp => hcb _ (List.mem_map.2 ⟨p, hp, rfl⟩))
        (fun sk hsk => hsb _ (List.mem_map.2 ⟨sk, hsk, rfl⟩))
        hnewb (counter s hcounter))
    refine ⟨r, hr, fun n mk hmk => ?_, herr⟩
    obtain ⟨m', hsend, hR'⟩ := hok n mk hmk
    exact ⟨m', hsend, spqrAbs_eq hR'⟩
  · intro s re out n hepoch hroom hcb hsb hnewb hskip hone hcounter
    obtain ⟨r, hr, hpost⟩ := Std.WP.spec_imp_exists
      (Tacenta.UnitSpqrT3.receive_refines hkr hz96 hz64 hret happ hrm hzs hopt
        (spqrAbs_refines s) re out n
        hepoch (by simpa [spqrAbs] using hroom)
        (fun p hp => hcb _ (List.mem_map.2 ⟨p, hp, rfl⟩))
        (fun sk hsk => hsb _ (List.mem_map.2 ⟨sk, hsk, rfl⟩))
        hnewb (by simpa [spqrAbs, Tacenta.UnitSpqrT3.max_skip_agrees] using hskip)
        hone (counter s hcounter))
    refine ⟨r, hr, ?_⟩
    have hmap : out.map spqrOutputOf = out.map Tacenta.UnitSpqrT3.outputOf := rfl
    rw [hmap]
    generalize Model.SparseRatchet.receive (spqrAbs s) re.val
      (out.map Tacenta.UnitSpqrT3.outputOf) n.val = res at hpost ⊢
    rcases res with _ | ⟨m', k⟩
    · exact hpost
    · obtain ⟨key, h1, h2, h3⟩ := hpost
      exact ⟨key, h1, h2, spqrAbs_eq h3⟩

/-! ## `send` and `receive`, with the bundles discharged

`send_refines` and `receive_refines` above are `TripleT3.lean`'s theorems, still
taking `RatchetAgreesFor α` and `SpqrAgreesFor β`. These are the same two
theorems at the abstractions `ratchet_agrees_for` and `spqr_agrees_for` prove the
bundles for, so what they assume is the inner ratchets' boundary and nothing
written by hand about either ratchet.

Two collapses keep that boundary from being listed twice. `UnitT3.HkdfAgrees`,
`UnitSpqrT3.SpqrHkdfAgrees` and this file's `TripleHkdfAgrees` say the same thing
about the one `tacenta_kdf.hkdf_sha256` the unit declares, differing only in bound
variable names and in which file's copy of `keyOf` and `sliceOf` they use, so Lean
accepts one for all three. And the general `UnitSpqrT1.ZeroizeTotal` the sparse
ratchet needs gives this file's narrow `ZeroizeTotal` at its one instance.

One cost is not collapsed. Each bundle covers its ratchet's whole calling surface,
so `send_refines_discharged` assumes the boundary of the receive path as well
(`VecRemoveTotal`, `DerivedKeysModel`, `VecAppendAgrees`, `VecRemoveAgrees`), which
its own proof never reaches. -/

theorem send_refines_discharged
    (hmac : Tacenta.UnitT3.HmacAgrees) (hkdf : Tacenta.UnitT3.HkdfAgrees)
    (hzr : Tacenta.UnitT3.ZeroizingRoundTrips) (hvr : Tacenta.UnitT1.VecRemoveTotal)
    [Tacenta.UnitT1.DerivedKeysModel]
    (hz96 : Tacenta.UnitSpqrT3.ZeroizingRoundTrips96)
    (hz64 : Tacenta.UnitSpqrT3.ZeroizingRoundTrips64)
    (hret : Tacenta.UnitSpqrT3.VecRetainAgrees) (happ : Tacenta.UnitSpqrT3.VecAppendAgrees)
    (hrm : Tacenta.UnitSpqrT3.VecRemoveAgrees) (hzs : Tacenta.UnitSpqrT1.ZeroizeTotal)
    (hopt : Tacenta.UnitSpqrT1.OptionCloneTotal)
    {s : State} {m : Model.Triple.State} (hrel : StateRefines ratchetAbs spqrAbs s m)
    (sending_epoch : Std.U64) (output : Option tacenta_spqr.Output)
    (hroom : m.postQuantum.chains.length + 1 < Usize.max)
    (hcb : ∀ p ∈ m.postQuantum.chains, p.1 + Model.SparseRatchet.epochsKept ≤ Std.U64.max)
    (hsb : ∀ sk ∈ m.postQuantum.skipped, sk.1 + Model.SparseRatchet.epochsKept ≤ Std.U64.max)
    (hnewb : ∀ o : tacenta_spqr.Output, output = some o →
      o.key_epoch.val + Model.SparseRatchet.epochsKept ≤ Std.U64.max)
    (hepoch : m.postQuantum.epoch + 1 < Std.U64.max)
    (hcounter : ∀ p ∈ m.postQuantum.chains, ∀ ch : Model.SparseRatchet.Chain,
      (p.2.send = some ch ∨ p.2.receive = some ch) → ch.n < Std.U64.max) :
    State.send s sending_epoch output ⦃ fun r =>
      (∀ hdr mk, r.1 = core.result.Result.Ok (hdr, mk) →
        ∃ m' mh key, Model.Triple.send m sending_epoch.val (output.map spqrOutputOf)
            = some (m', mh, key)
          ∧ StateRefines ratchetAbs spqrAbs r.2 m' ∧ TripleHeaderR hdr mh ∧ keyOf mk = key)
      ∧ (∀ e, r.1 = core.result.Result.Err e →
          (e = TripleError.Classical tacenta_ratchet.RatchetError.NoSendingChain ∨
            ∃ e', e = TripleError.PostQuantum e') →
          Model.Triple.send m sending_epoch.val (output.map spqrOutputOf) = none) ⦄ :=
  send_refines (ratchet_agrees_for hopt hmac hkdf hzr hvr)
    (spqr_agrees_for hkdf hz96 hz64 hret happ hrm hzs hopt) hkdf
    (fun a => hzs _ a) hrel sending_epoch output hroom hcb hsb hnewb hepoch hcounter

theorem receive_refines_discharged
    (hmac : Tacenta.UnitT3.HmacAgrees) (hkdf : Tacenta.UnitT3.HkdfAgrees)
    (hzr : Tacenta.UnitT3.ZeroizingRoundTrips) (hvr : Tacenta.UnitT1.VecRemoveTotal)
    [Tacenta.UnitT1.DerivedKeysModel]
    (hz96 : Tacenta.UnitSpqrT3.ZeroizingRoundTrips96)
    (hz64 : Tacenta.UnitSpqrT3.ZeroizingRoundTrips64)
    (hret : Tacenta.UnitSpqrT3.VecRetainAgrees) (happ : Tacenta.UnitSpqrT3.VecAppendAgrees)
    (hrm : Tacenta.UnitSpqrT3.VecRemoveAgrees) (hzs : Tacenta.UnitSpqrT1.ZeroizeTotal)
    (hopt : Tacenta.UnitSpqrT1.OptionCloneTotal)
    {s : State} {m : Model.Triple.State} (hrel : StateRefines ratchetAbs spqrAbs s m)
    (header : Header) (mh : Model.State.Header) (hheader : RatchetHeaderR header.dr mh)
    (dh_out_recv dh_out_send new_dhs_pub : Array Std.U8 32#usize)
    (output : Option tacenta_spqr.Output)
    (hone : (m.classical.skipped.filter (fun x => x.1 == mh.dh && x.2.1 == mh.n)).length ≤ 1)
    (hs : max m.classical.skipped.length Model.State.maxSkippedStore + Model.State.maxSkip ≤ Usize.max)
    (hevents : m.classical.events + 1 < Std.U32.max)
    (hepoch : m.postQuantum.epoch + 1 < Std.U64.max)
    (hroom : m.postQuantum.chains.length + 2 < Usize.max)
    (hcb : ∀ p ∈ m.postQuantum.chains, p.1 + Model.SparseRatchet.epochsKept ≤ Std.U64.max)
    (hsb : ∀ sk ∈ m.postQuantum.skipped, sk.1 + Model.SparseRatchet.epochsKept ≤ Std.U64.max)
    (hnewb : ∀ o : tacenta_spqr.Output, output = some o →
      o.key_epoch.val + Model.SparseRatchet.epochsKept ≤ Std.U64.max)
    (hskiproom : m.postQuantum.skipped.length + Model.SparseRatchet.maxSkip ≤ Usize.max)
    (hone2 : (m.postQuantum.skipped.filter (fun x => x.1 == header.epoch.val && x.2.1 == header.pq_n.val)).length ≤ 1)
    (hcounter : ∀ p ∈ m.postQuantum.chains, ∀ ch : Model.SparseRatchet.Chain,
      (p.2.send = some ch ∨ p.2.receive = some ch) → ch.n < Std.U64.max) :
    State.receive s header dh_out_recv dh_out_send new_dhs_pub output ⦃ fun r =>
      ∀ st key, r = core.result.Result.Ok (st, key) →
        ∃ m' k, Model.Triple.receive m { dr := mh, epoch := header.epoch.val, pqN := header.pq_n.val }
            (keyOf dh_out_recv) (keyOf dh_out_send) (keyOf new_dhs_pub) (output.map spqrOutputOf) = some (m', k)
          ∧ StateRefines ratchetAbs spqrAbs st m' ∧ keyOf key = k ⦄ :=
  receive_refines (ratchet_agrees_for hopt hmac hkdf hzr hvr)
    (spqr_agrees_for hkdf hz96 hz64 hret happ hrm hzs hopt) hkdf
    (fun a => hzs _ a) hrel header mh hheader dh_out_recv dh_out_send new_dhs_pub output
    hone hs hevents hepoch hroom hcb hsb hnewb hskiproom hone2 hcounter

end Tacenta.UnitTripleT3
