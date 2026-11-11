import Translation.UnitLifecycleRestoredSession
import Translation.UnitLifecycleEncryptPreserve

/-!
# The counter ceilings `Session::import` enforces, and the budget it does not give

`Session::import` is the root every persisted session comes back through.  `import_ok_gives_invariant`
(`UnitLifecycleRestoredSession`) shows that every accepted session passes `Session::invariant`; the step theorems of
`UnitLifecycleEncryptPreserve` and `UnitLifecycleDecryptPreserve` also take a budget, `CounterRoom s (k + 1)`.  This
module states which counter ceilings acceptance enforces, for every byte string, and shows that acceptance gives no
budget.

## What it shows

* `counterRoom_iff_roomCheck`, `roomCheck_zero`: `roomCheck` is `CounterRoom` written as a decidable check on the
  session's four counters (the classical clock, the sparse epoch, every sparse chain counter and the Braid epoch);
  the equivalence holds of every session, by construction, and says nothing about `import`.  At `k = 0` the check is
  `headroomCheck`.  No hypothesis.
* `import_ok_ceilings`: what acceptance itself adds about the counters: every session `import` accepts, from every
  byte string, passes the invariant, has its classical clock below `u32::MAX` (so at most `MAX_EVENTS =
  u32::MAX - 1`), its sparse epoch below `u64::MAX` and its Braid epoch below `u64::MAX`.  Each of the three ceilings
  is one step above what room for zero operations asks, so none is a budget.  No hypothesis.  `import_ok_budget`
  bundles it with the equivalence above, which takes nothing from the import.
* `read_epoch_ne`, `decode_state_epoch`, `braid_from_bytes_epoch`, `import_ok_unchecked`, `import_unchecked_braid`,
  `import_ok_braid_epoch`: the Braid epoch's ceiling at acceptance, which the invariant does not give: the persisted
  epoch reader refuses `u64::MAX`, every state the Braid's state decoder returns is `Failed` or reads its epoch with
  it, every session `import` accepts is the field decoder's, whose Braid is one `Braid::from_bytes` accepted.
* `export_import_parked_clock`, `export_import_exhausted_chain`: for every session of the round trip's covered shape
  (`CodecShape`) that passes the invariant, the copy with its classical clock at `MAX_EVENTS` (`withClock`), and the
  copy with its sparse send chain at counter `u64::MAX` (`withExhaustedSend`), each export to bytes `import` accepts,
  returning that copy, and neither copy has room for any operation.  The invariant does not read the clock beyond its
  ceiling and the stored keys' times (`invariant_withClock`, `structural_withClock`), nor any chain counter
  (`invariant_withExhaustedSend`, `structural_withExhaustedSend`); `codecShape_withClock`,
  `codecShape_withExhaustedSend`, `withClock_parked_no_room` and `withExhaustedSend_no_room` are the leaf facts.
* `established_parked_clock_accepted`, `established_exhausted_chain_accepted`: the same for every success output of
  `establish_initiator_for`, through `establish_initiator_for_admissible` and `codecShape_parts`.
* `acceptance_does_not_give_headroom`: if `establish_initiator_for` succeeds once, it is false that every session
  `import` accepts meets `CounterHeadroom`, which is room for zero operations (`counterRoom_zero`).

So acceptance adds the three ceilings and no budget: whether an accepted session has room for `k` operations depends
on its counters, which acceptance bounds only one step above the ceilings and not at all for a chain counter.
`Session::import`'s documentation says as much (a saturated counter is accepted, and its check belongs at the use
site); these are the theorems.  "No budget" is meant in the sense of `CounterRoom`, the uniform premise every step
theorem takes: it asks all four counters, including counters the operation does not move (a send does not move the
receive clock, a receive does not read the send chain), so a session with no budget is one no step theorem applies
to, not one shown unusable; whether a premise per operation would cover a send at a parked clock, or a receive at an
exhausted send chain, is not checked.  An honest session also reaches the parked clock, after 2^32 accepted receives;
there the ratchet stops expiring by age the skipped keys stored within `MAX_SKIPPED_AGE` of the stop, as the
specification states (LIM-18) and as the model's `ageStore` does too, and no theorem about the session covers the
operations there.  What the code does at the ceilings is read, not proved here: the classical clock is clamped at `MAX_EVENTS`
(`tacenta-core/ratchet/src/lib.rs`), so a parked session goes on working outside the refinement theorems, which take
`CounterHeadroom` (since the model clamps the clock the same way, whether that clock clause is needed for refinement
at the stop, or is an artefact of how the proofs were written, is not checked); a step past a sparse chain counter of `u64::MAX` is refused with `ChainExhausted`
(`tacenta-core/spqr/src/lib.rs`).  Proved, elsewhere: every refused `encrypt`, `decrypt` and `decrypt_ratchet` keeps
the invariant and every budget (`UnitLifecycleEncryptPreserve.encrypt_err_keeps_invariant` and its two siblings).

## The laws and premises

* No new law.  The budget characterisation and the three ceilings take no hypothesis.  The round-trip results take the
  five laws of `UnitLifecycleSessionRoundTrip.export_import_of_shape` (`ZeroizingVecRoundTrip`, `OptionBranchSome`,
  `VecAsSlice`, `DhPrivateBytesRoundTrip`, `DhPublicBytesRoundTrip`); the establishment forms add the four of
  `export_import_established` (`DhPublicValid`, `KemCiphertextLenOf`, `KemCiphertextLenBound`, `OptionEqU64Shape`).
  All nine are existing and assumed.
* Every result that names `Session::import` or `Session::export` lists the one compiler-trust axiom of the generated
  `export`'s panic message (`UnitLifecycleSessionRoundTrip`, "The one compiler-evaluated fact under `export`").

## Non-vacuity

* The nine laws hold together in one interpretation (`UnitLifecycleRestoredSession.restored_laws_model`), which
  shows them consistent and says nothing of the shipping functions.  The establishment forms take one success of
  `establish_initiator_for`; `restored_established_inhabited` shows one exists under the initiator axiom base and
  `InitiatorSuccessShape`.
* The parked and exhausted copies are edits of a session's counters, made here; no run in the tree reaches them by
  operations.

## What it does not show

* That a session the operations reach has a parked clock or an exhausted chain: the copies are built by editing
  counters, and that a long session reaches them is by reading of the clamp and the counter.
* What `encrypt` or `decrypt` does at a session with no budget: no preservation or refinement theorem applies there,
  beyond the refused calls keeping the invariant.
* That `import` checks the budget: it does not, and no Rust is changed here.
* Whether a premise per operation, asking only the counters that operation moves, would cover a send at a parked clock
  or a receive at an exhausted send chain: not checked.
* That the shipping functions meet the nine laws.
-/

namespace Tacenta.UnitLifecycleImportBudget

open Aeneas Aeneas.Std Result
open tacenta_session_unit
open Tacenta.UnitLifecycleSendPreserve (CounterRoom counterRoom_zero session_invariant_iff)
open Tacenta.UnitLifecycleDecryptRunBounds (CounterHeadroom)
open Tacenta.UnitLifecycleRestoredSession (import_ok_gives_invariant headroomCheck counterHeadroom_iff_check
  KemCiphertextLenBound)
open Tacenta.UnitLifecycleEstablishInitiatorShape (DhPublicValid KemCiphertextLenOf)
open Tacenta.UnitLifecycleSessionCodec
open Tacenta.UnitLifecycleSessionRoundTrip

/-! ## The budget as a decidable check (of every session) -/

/-- **Room for `k` operations as one decidable check on a session's counters**: the classical clock, the
sparse epoch, every sparse chain counter (each operation may move it by up to `MAX_SKIP + 1 = 1001`) and the
Braid epoch, each `k` operations below its ceiling.  `roomCheck s 0` is `headroomCheck s`
(`roomCheck_zero`). -/
def roomCheck (s : lifecycle.Session) (k : Nat) : Bool :=
  decide (s.triple.classical.events.val + k + 1 < Std.U32.max) &&
  decide (s.triple.post_quantum.epoch.val + k + 1 < Std.U64.max) &&
  s.triple.post_quantum.chains.val.all (fun p =>
    (match p.2.send with | some ch => decide (ch.n.val + 1001 * k < Std.U64.max) | none => true) &&
    (match p.2.receive with | some ch => decide (ch.n.val + 1001 * k < Std.U64.max) | none => true)) &&
  decide ((Tacenta.SessionUnitBraidT1.State.epoch_val s.braid.state).val + k + 1 < Std.U64.max)

/-- **`roomCheck` is `CounterRoom` as a decidable check**, for every session and every `k`: `CounterRoom s k` holds
exactly when the check on the session's four counters passes.  True by construction; no hypothesis, and nothing
about `import`. -/
theorem counterRoom_iff_roomCheck (s : lifecycle.Session) (k : Nat) :
    CounterRoom s k ↔ roomCheck s k = true := by
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    simp only [roomCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
    refine ⟨⟨⟨h1, h2⟩, ?_⟩, h4⟩
    intro p hp
    refine ⟨?_, ?_⟩
    · cases hs : p.2.send with
      | none => rfl
      | some ch => simpa using h3 p hp ch (Or.inl hs)
    · cases hr : p.2.receive with
      | none => rfl
      | some ch => simpa using h3 p hp ch (Or.inr hr)
  · intro h
    simp only [roomCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
    refine ⟨h1, h2, ?_, h4⟩
    intro p hp ch hch
    obtain ⟨hs, hr⟩ := h3 p hp
    rcases hch with hch | hch
    · rw [hch] at hs; simpa using hs
    · rw [hch] at hr; simpa using hr

/-- At `k = 0` the check is `headroomCheck`, the four ceilings of `CounterHeadroom`. -/
theorem roomCheck_zero (s : lifecycle.Session) : roomCheck s 0 = headroomCheck s := by
  have h : roomCheck s 0 = true ↔ headroomCheck s = true :=
    (counterRoom_iff_roomCheck s 0).symm.trans ((counterRoom_zero s).trans (counterHeadroom_iff_check s))
  cases h1 : roomCheck s 0 <;> cases h2 : headroomCheck s <;> simp_all

/-! ## What acceptance enforces of the Braid epoch -/

/-- **The persisted-epoch reader refuses `u64::MAX`**: every epoch `read_epoch` returns is below it. -/
theorem read_epoch_ne (bytes : Slice U8) (pos : Usize) (e : U64)
    (h : tacenta_braid.read_epoch bytes pos = ok (some e)) : e ≠ core.num.U64.MAX := by
  unfold tacenta_braid.read_epoch at h
  obtain ⟨o, -, h⟩ := Tacenta.SessionUnitRatchetImportInv.bind_eq_ok_inv h
  rcases o with _ | e'
  · simp at h
  · simp only at h
    split at h
    · simp at h
    · simp at h; subst h; assumption

set_option maxHeartbeats 4000000 in
/-- **Every Braid state the state decoder returns is `Failed` or has an epoch below `u64::MAX`**: each of the eleven
arms that carries an epoch reads it with `read_epoch`. -/
theorem decode_state_epoch (tag : U8) (bytes : Slice U8) (pos : Usize) (st : tacenta_braid.State) (p : Usize)
    (h : tacenta_braid.decode_state tag bytes pos = ok (some (st, p))) :
    st = tacenta_braid.State.Failed ∨ Tacenta.SessionUnitBraidT1.State.epoch_val st ≠ core.num.U64.MAX := by
  unfold tacenta_braid.decode_state at h
  split at h <;>
  repeat' first
    | (replace h := Tacenta.SessionUnitRatchetImportInv.bind_eq_ok_inv h; obtain ⟨_, _, h⟩ := h)
    | split at h
    | simp at h
  all_goals (
    obtain ⟨rfl, -⟩ := h
    first
      | exact Or.inl rfl
      | (right
         simp only [Tacenta.SessionUnitBraidT1.State.epoch_val]
         exact read_epoch_ne _ _ _ (by assumption)))

/-- **Every Braid `Braid::from_bytes` accepts is `Failed` or has an epoch below `u64::MAX`.** -/
theorem braid_from_bytes_epoch (bytes : Slice U8) (b : tacenta_braid.Braid)
    (h : tacenta_braid.Braid.from_bytes bytes = ok (core.result.Result.Ok b)) :
    b.state = tacenta_braid.State.Failed ∨
      Tacenta.SessionUnitBraidT1.State.epoch_val b.state ≠ core.num.U64.MAX := by
  rw [tacenta_braid.Braid.from_bytes] at h
  split at h
  · simp at h
  · replace h := Tacenta.SessionUnitRatchetImportInv.bind_eq_ok_inv h
    obtain ⟨_, _, h⟩ := h
    split at h
    · simp at h
    · replace h := Tacenta.SessionUnitRatchetImportInv.bind_eq_ok_inv h
      obtain ⟨tag, _, h⟩ := h
      replace h := Tacenta.SessionUnitRatchetImportInv.bind_eq_ok_inv h
      obtain ⟨o, ho, h⟩ := h
      rcases o with _ | ⟨st, pos⟩
      · simp at h
      · simp at h
        split at h
        · replace h := Tacenta.SessionUnitRatchetImportInv.bind_eq_ok_inv h
          obtain ⟨bb, hbb, h⟩ := h
          split at h
          · simp only [ok.injEq, core.result.Result.Ok.injEq] at h
            subst h
            exact decode_state_epoch _ _ _ _ _ ho
          · simp at h
        · simp at h

/-- **A session `Session::import` accepts is one the field decoder returned**: `import` returns the session
`import_unchecked` decoded, after its two checks. -/
theorem import_ok_unchecked (b : Slice U8) (s : lifecycle.Session)
    (h : lifecycle.Session.import b = ok (core.result.Result.Ok s)) :
    lifecycle.Session.import_unchecked b = ok (core.result.Result.Ok s) := by
  unfold lifecycle.Session.import at h
  obtain ⟨r, hr, h⟩ := Tacenta.SessionUnitRatchetImportInv.bind_eq_ok_inv h
  rcases r with val | e
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok] at h
    obtain ⟨z, -, h⟩ := Tacenta.SessionUnitRatchetImportInv.bind_eq_ok_inv h
    obtain ⟨v, -, h⟩ := Tacenta.SessionUnitRatchetImportInv.bind_eq_ok_inv h
    obtain ⟨sl, -, h⟩ := Tacenta.SessionUnitRatchetImportInv.bind_eq_ok_inv h
    obtain ⟨c, -, h⟩ := Tacenta.SessionUnitRatchetImportInv.bind_eq_ok_inv h
    split at h
    · simp at h
    · obtain ⟨b1, hb1, h⟩ := Tacenta.SessionUnitRatchetImportInv.bind_eq_ok_inv h
      split at h
      · simp only [ok.injEq, core.result.Result.Ok.injEq] at h
        subst h
        exact hr
      · simp at h
  · simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual] at h

set_option maxHeartbeats 4000000 in
/-- **The Braid of a decoded session is one `Braid::from_bytes` accepted**, from some slice of the bytes. -/
theorem import_unchecked_braid (bytes : Slice U8) (s : lifecycle.Session)
    (h : lifecycle.Session.import_unchecked bytes = ok (core.result.Result.Ok s)) :
    ∃ bsl, tacenta_braid.Braid.from_bytes bsl = ok (core.result.Result.Ok s.braid) := by
  unfold lifecycle.Session.import_unchecked at h
  obtain ⟨b0, -, h⟩ := Tacenta.SessionUnitRatchetImportInv.bind_eq_ok_inv h
  split at h
  · simp at h
  obtain ⟨i, -, h⟩ := Tacenta.SessionUnitRatchetImportInv.bind_eq_ok_inv h
  split at h
  · simp at h
  obtain ⟨o, -, h⟩ := Tacenta.SessionUnitRatchetImportInv.bind_eq_ok_inv h
  rcases o with _ | ⟨tb, pos⟩
  · simp at h
  simp only at h
  obtain ⟨r, -, h⟩ := Tacenta.SessionUnitRatchetImportInv.bind_eq_ok_inv h
  rcases r with t | e
  swap
  · simp at h
  simp only at h
  obtain ⟨o1, -, h⟩ := Tacenta.SessionUnitRatchetImportInv.bind_eq_ok_inv h
  rcases o1 with _ | ⟨bsl, pos1⟩
  · simp at h
  simp only at h
  obtain ⟨r1, hr1, h⟩ := Tacenta.SessionUnitRatchetImportInv.bind_eq_ok_inv h
  rcases r1 with br | e
  swap
  · simp at h
  simp only at h
  refine ⟨bsl, ?_⟩
  rw [hr1]
  suffices hb : s.braid = br by rw [hb]
  repeat' first
    | (replace h := Tacenta.SessionUnitRatchetImportInv.bind_eq_ok_inv h; obtain ⟨_, _, h⟩ := h)
    | split at h
    | (simp only [ok.injEq, core.result.Result.Ok.injEq] at h; subst h; rfl)
    | simp at h

/-- **Every session `Session::import` accepts has its Braid epoch below `u64::MAX`** (a failed Braid counts its
epoch as zero), for every byte string: the Braid decoder's `read_epoch` refuses `u64::MAX`.  One step above what
`CounterHeadroom` asks of the Braid epoch.  No hypothesis. -/
theorem import_ok_braid_epoch (b : Slice U8) (s : lifecycle.Session)
    (h : lifecycle.Session.import b = ok (core.result.Result.Ok s)) :
    (Tacenta.SessionUnitBraidT1.State.epoch_val s.braid.state).val < Std.U64.max := by
  obtain ⟨bsl, hb⟩ := import_unchecked_braid b s (import_ok_unchecked b s h)
  rcases braid_from_bytes_epoch bsl s.braid hb with hf | hne
  · rw [hf]; simp [Tacenta.SessionUnitBraidT1.State.epoch_val, U64.max_eq]
  · have hle := (Tacenta.SessionUnitBraidT1.State.epoch_val s.braid.state).hBounds
    have : (Tacenta.SessionUnitBraidT1.State.epoch_val s.braid.state).val ≠ core.num.U64.MAX.val := by
      intro h'; exact hne (UScalar.eq_of_val_eq h')
    simp [core.num.U64.MAX, U64.rMax, U64.max_eq] at this ⊢
    scalar_tac

/-! ## What acceptance enforces -/

/-- **What a successful `Session::import` enforces of the counters**, for every byte string: the session passes
`Session::invariant`, its classical clock is below `u32::MAX` (at most `MAX_EVENTS = u32::MAX - 1`), its sparse
epoch is below `u64::MAX` and its Braid epoch is below `u64::MAX`.  Each is one step above the ceiling
`CounterHeadroom` asks for, so none of them is a budget.  The first two are read off the invariant `import` checks
last (the ratchet's clock clause, the sparse ratchet's epoch window), the third off the Braid decoder
(`import_ok_braid_epoch`); no hypothesis. -/
theorem import_ok_ceilings (b : Slice U8) (s : lifecycle.Session)
    (h : lifecycle.Session.import b = ok (core.result.Result.Ok s)) :
    lifecycle.Session.invariant s = ok true ∧ s.triple.classical.events.val < Std.U32.max ∧
      s.triple.post_quantum.epoch.val < Std.U64.max ∧
      (Tacenta.SessionUnitBraidT1.State.epoch_val s.braid.state).val < Std.U64.max := by
  have hinv := import_ok_gives_invariant b s h
  obtain ⟨-, ht, -⟩ := (session_invariant_iff s).mp hinv
  obtain ⟨hr, hq, -⟩ := (Tacenta.UnitTripleInvModel.triple_invariant_true_iff s.triple).mp ht
  have hr' := (Tacenta.SessionUnitRatchetImportInv.Ratchet.invariant_true_iff _).mp hr
  have hq' := (Tacenta.SessionUnitRatchetImportInv.Spqr.invariant_true_iff _).mp hq
  exact ⟨hinv, hr'.clock_room, Tacenta.SessionUnitRatchetImportInv.Spqr.inv_gives_epoch_room _ hq',
    import_ok_braid_epoch b s h⟩

/-- **`import_ok_ceilings` bundled with `counterRoom_iff_roomCheck`**: an accepted session passes the invariant and the
three ceilings, and, as every session does, has room for `k` operations exactly when `roomCheck` passes on its
counters.  The last conjunct takes nothing from the import; `import` makes no such check. -/
theorem import_ok_budget (b : Slice U8) (s : lifecycle.Session)
    (h : lifecycle.Session.import b = ok (core.result.Result.Ok s)) :
    lifecycle.Session.invariant s = ok true ∧ s.triple.classical.events.val < Std.U32.max ∧
      s.triple.post_quantum.epoch.val < Std.U64.max ∧
      (Tacenta.SessionUnitBraidT1.State.epoch_val s.braid.state).val < Std.U64.max ∧
      ∀ k, CounterRoom s k ↔ roomCheck s k = true :=
  let ⟨h1, h2, h3, h4⟩ := import_ok_ceilings b s h
  ⟨h1, h2, h3, h4, counterRoom_iff_roomCheck s⟩

/-! ## What acceptance does not give: a parked clock -/

/-- The session with its classical clock set to `c`, every other field as it was. -/
def withClock (s : lifecycle.Session) (c : U32) : lifecycle.Session :=
  { s with triple := { s.triple with classical := { s.triple.classical with events := c } } }

/-- `Session::structural_invariant` does not read the clock. -/
theorem structural_withClock (s : lifecycle.Session) (c : U32) :
    lifecycle.Session.structural_invariant (withClock s c) = lifecycle.Session.structural_invariant s :=
  rfl

/-- **The invariant accepts any clock below `u32::MAX` not before a stored key's time**: setting the clock to such a
value keeps `Session::invariant`. -/
theorem invariant_withClock (s : lifecycle.Session) (c : U32) (hc : c.val < Std.U32.max)
    (hfresh : ∀ e ∈ s.triple.classical.skipped.val, e.stored_at.val ≤ c.val)
    (h : lifecycle.Session.invariant s = ok true) :
    lifecycle.Session.invariant (withClock s c) = ok true := by
  obtain ⟨hs, ht, hb⟩ := (session_invariant_iff s).mp h
  refine (session_invariant_iff _).mpr ⟨by rw [structural_withClock]; exact hs, ?_, hb⟩
  rw [Tacenta.UnitTripleInvModel.triple_invariant_true_iff] at ht ⊢
  obtain ⟨hr, hq, hroles⟩ := ht
  refine ⟨?_, hq, hroles⟩
  rw [Tacenta.SessionUnitRatchetImportInv.Ratchet.invariant_true_iff] at hr ⊢
  obtain ⟨h1, -, -, h4, h5, h6, h7, h8⟩ := hr
  exact ⟨h1, hc, hfresh, h4, h5, h6, h7, h8⟩

/-- A session of the covered shape keeps it with its clock moved. -/
theorem codecShape_withClock {s : lifecycle.Session} {epoch : U64} {auth : tacenta_braid.Auth} {e : U64}
    {c1 c2 : tacenta_spqr.Chain} {p : lifecycle.PendingInitial} (c : U32)
    (h : CodecShape s epoch auth e c1 c2 p) : CodecShape (withClock s c) epoch auth e c1 c2 p :=
  ⟨h.braid, h.epochNotMax, h.classicalSkipped, h.chains, h.sparseSkipped, h.identityAd, h.pending,
    h.ciphertext, h.established⟩

/-- **A session with the clock at `MAX_EVENTS = u32::MAX - 1` has no budget**: `CounterRoom` fails at every
`k`. -/
theorem withClock_parked_no_room (s : lifecycle.Session) (k : Nat) :
    ¬ CounterRoom (withClock s 4294967294#u32) k := by
  intro h
  have := h.classicalEvents
  simp [withClock, U32.max_eq] at this
  omega

/-- **`import` accepts a parked clock**: for every session of the covered shape that passes `Session::invariant`,
the copy with the classical clock at `MAX_EVENTS = u32::MAX - 1` exports to bytes that `Session::import` accepts,
returning that copy, which has room for no operation (`CounterRoom` fails at every `k`).  Under the five laws of
`export_import_of_shape`. -/
theorem export_import_parked_clock (hz : ZeroizingVecRoundTrip) (hbr : OptionBranchSome)
    (hsl : VecAsSlice) (hpriv : DhPrivateBytesRoundTrip) (hpub : DhPublicBytesRoundTrip)
    (s : lifecycle.Session) (epoch : U64) (auth : tacenta_braid.Auth) (e : U64)
    (c1 c2 : tacenta_spqr.Chain) (p : lifecycle.PendingInitial) (shape : CodecShape s epoch auth e c1 c2 p)
    (hinv : lifecycle.Session.invariant s = ok true) :
    ∃ z v, lifecycle.Session.export (withClock s 4294967294#u32) = ok z ∧
      zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref vecInst z = ok v ∧
      lifecycle.Session.import (alloc.vec.Vec.deref v) =
        ok (core.result.Result.Ok (withClock s 4294967294#u32)) ∧
      ∀ k, ¬ CounterRoom (withClock s 4294967294#u32) k := by
  obtain ⟨z, v, h1, h2, h3⟩ := export_import_of_shape hz hbr hsl hpriv hpub (withClock s 4294967294#u32)
    epoch auth e c1 c2 p (codecShape_withClock _ shape)
    (invariant_withClock s _ (by simp [U32.max_eq]) (by rw [shape.classicalSkipped]; simp) hinv)
  exact ⟨z, v, h1, h2, h3, withClock_parked_no_room s⟩

/-! ## What acceptance does not give: an exhausted chain -/

/-- A chain-table entry with its send chain's counter at `u64::MAX`, if it has a send chain. -/
def exhaustSend (q : U64 × tacenta_spqr.Chains) : U64 × tacenta_spqr.Chains :=
  (q.1, { q.2 with send := q.2.send.map (fun ch => { ch with n := core.num.U64.MAX }) })

/-- The session with every send chain of the sparse chain table at counter `u64::MAX`. -/
def withExhaustedSend (s : lifecycle.Session) : lifecycle.Session :=
  { s with triple := { s.triple with post_quantum := { s.triple.post_quantum with
    chains := ⟨s.triple.post_quantum.chains.val.map exhaustSend, by
      simpa using s.triple.post_quantum.chains.property⟩ } } }

/-- `Session::structural_invariant` does not read the chain counters. -/
theorem structural_withExhaustedSend (s : lifecycle.Session) :
    lifecycle.Session.structural_invariant (withExhaustedSend s) = lifecycle.Session.structural_invariant s :=
  rfl

/-- **The invariant does not read a chain counter**: moving every send chain to `u64::MAX` keeps
`Session::invariant`. -/
theorem invariant_withExhaustedSend (s : lifecycle.Session) (h : lifecycle.Session.invariant s = ok true) :
    lifecycle.Session.invariant (withExhaustedSend s) = ok true := by
  obtain ⟨hs, ht, hb⟩ := (session_invariant_iff s).mp h
  refine (session_invariant_iff _).mpr ⟨by rw [structural_withExhaustedSend]; exact hs, ?_, hb⟩
  rw [Tacenta.UnitTripleInvModel.triple_invariant_true_iff] at ht ⊢
  obtain ⟨hr, hq, hroles⟩ := ht
  refine ⟨hr, ?_, hroles⟩
  rw [Tacenta.SessionUnitRatchetImportInv.Spqr.invariant_true_iff] at hq ⊢
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hq
  refine ⟨h1, ?_, ?_, ?_, ?_, h6⟩
  · intro q hq
    simp only [withExhaustedSend, List.mem_map] at hq
    obtain ⟨q', hq', rfl⟩ := hq
    exact h2 q' hq'
  · simp only [withExhaustedSend]
    rw [List.pairwise_map]
    exact h3
  · obtain ⟨q, hq, hqe⟩ := h4
    exact ⟨exhaustSend q, List.mem_map.mpr ⟨q, hq, rfl⟩, hqe⟩
  · intro a ha
    obtain ⟨q, hq, hqe⟩ := h5 a ha
    exact ⟨exhaustSend q, List.mem_map.mpr ⟨q, hq, rfl⟩, hqe⟩

/-- A session of the covered shape keeps it with its send chain exhausted, the send chain now at `u64::MAX`. -/
theorem codecShape_withExhaustedSend {s : lifecycle.Session} {epoch : U64} {auth : tacenta_braid.Auth}
    {e : U64} {c1 c2 : tacenta_spqr.Chain} {p : lifecycle.PendingInitial}
    (h : CodecShape s epoch auth e c1 c2 p) :
    CodecShape (withExhaustedSend s) epoch auth e { c1 with n := core.num.U64.MAX } c2 p :=
  ⟨h.braid, h.epochNotMax, h.classicalSkipped, by simp [withExhaustedSend, h.chains, exhaustSend],
    h.sparseSkipped, h.identityAd, h.pending, h.ciphertext, h.established⟩

/-- **A session of the covered shape with its send chain exhausted has no budget**: `CounterRoom` fails at every
`k`, at the chain counter. -/
theorem withExhaustedSend_no_room {s : lifecycle.Session} {epoch : U64} {auth : tacenta_braid.Auth}
    {e : U64} {c1 c2 : tacenta_spqr.Chain} {p : lifecycle.PendingInitial}
    (h : CodecShape s epoch auth e c1 c2 p) (k : Nat) :
    ¬ CounterRoom (withExhaustedSend s) k := by
  intro hr
  have := hr.sparseCounters _ (by rw [(codecShape_withExhaustedSend h).chains]; exact List.mem_singleton_self _)
    { c1 with n := core.num.U64.MAX } (Or.inl rfl)
  simp [core.num.U64.MAX, U64.rMax, U64.max_eq] at this

/-- **`import` accepts an exhausted chain**: for every session of the covered shape that passes
`Session::invariant`, the copy with its send chain at counter `u64::MAX` exports to bytes that `Session::import`
accepts, returning that copy, which has room for no operation.  Under the five laws of
`export_import_of_shape`. -/
theorem export_import_exhausted_chain (hz : ZeroizingVecRoundTrip) (hbr : OptionBranchSome)
    (hsl : VecAsSlice) (hpriv : DhPrivateBytesRoundTrip) (hpub : DhPublicBytesRoundTrip)
    (s : lifecycle.Session) (epoch : U64) (auth : tacenta_braid.Auth) (e : U64)
    (c1 c2 : tacenta_spqr.Chain) (p : lifecycle.PendingInitial) (shape : CodecShape s epoch auth e c1 c2 p)
    (hinv : lifecycle.Session.invariant s = ok true) :
    ∃ z v, lifecycle.Session.export (withExhaustedSend s) = ok z ∧
      zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref vecInst z = ok v ∧
      lifecycle.Session.import (alloc.vec.Vec.deref v) = ok (core.result.Result.Ok (withExhaustedSend s)) ∧
      ∀ k, ¬ CounterRoom (withExhaustedSend s) k := by
  obtain ⟨z, v, h1, h2, h3⟩ := export_import_of_shape hz hbr hsl hpriv hpub (withExhaustedSend s)
    epoch auth e _ c2 p (codecShape_withExhaustedSend shape) (invariant_withExhaustedSend s hinv)
  exact ⟨z, v, h1, h2, h3, withExhaustedSend_no_room shape⟩

/-! ## Derived from a real establishment: the persisted copies an initiator's session can be edited to -/

open Tacenta.UnitLifecycleEstablishInitiatorShape (establish_initiator_for_admissible establish_initiator_for_parts)
open Tacenta.UnitLifecycleRestoredSession (codecShape_parts)

/-- **A parked copy of an established initiator is accepted and has no budget**: for every success output `s` of
`establish_initiator_for`, the copy of `s` with its classical clock at `MAX_EVENTS` exports to bytes that
`Session::import` accepts, returning that copy, at which `CounterRoom` fails for every `k`.  The clock is the value
the ratchet's own clamp holds a long session at.  Under the nine laws of `export_import_established`. -/
theorem established_parked_clock_accepted (hz : ZeroizingVecRoundTrip) (hbr : OptionBranchSome)
    (hsl : VecAsSlice) (hpriv : DhPrivateBytesRoundTrip) (hpubb : DhPublicBytesRoundTrip)
    (hpub : DhPublicValid) (hct : KemCiphertextLenOf) (hbound : KemCiphertextLenBound)
    (hoeq : Tacenta.UnitHeadroomInvariant.OptionEqU64Shape
      (@core.option.Option.Insts.CoreCmpPartialEqOption.eq))
    {E : Type} (rc : rand_core_1.RngCore E) (crc : rand_core_1.CryptoRng E)
    (our : lifecycle.Identity) (bundle : lifecycle.PublishedBundle)
    (expected : tacenta_boundary.dh.PublicKeyBytes) (rng0 rng1 : E) (s : lifecycle.Session)
    (h : lifecycle.establish_initiator_for rc crc our bundle expected rng0 =
      ok (core.result.Result.Ok s, rng1)) :
    ∃ z v, lifecycle.Session.export (withClock s 4294967294#u32) = ok z ∧
      zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref vecInst z = ok v ∧
      lifecycle.Session.import (alloc.vec.Vec.deref v) =
        ok (core.result.Result.Ok (withClock s 4294967294#u32)) ∧
      ∀ k, ¬ CounterRoom (withClock s 4294967294#u32) k := by
  have hinv := establish_initiator_for_admissible rc crc hpub hct hoeq our bundle expected rng0 rng1 s h
  obtain ⟨p, rfl⟩ := establish_initiator_for_parts rc crc our bundle expected rng0 rng1 s h
  exact export_import_parked_clock hz hbr hsl hpriv hpubb p.session _ _ _ _ _ _
    (codecShape_parts hpubb hct hbound p) hinv

/-- **An exhausted copy of an established initiator is accepted and has no budget**: for every success output `s`
of `establish_initiator_for`, the copy of `s` with its sparse send chain at counter `u64::MAX` exports to bytes
that `Session::import` accepts, returning that copy, at which `CounterRoom` fails for every `k`.  Under the nine
laws of `export_import_established`. -/
theorem established_exhausted_chain_accepted (hz : ZeroizingVecRoundTrip) (hbr : OptionBranchSome)
    (hsl : VecAsSlice) (hpriv : DhPrivateBytesRoundTrip) (hpubb : DhPublicBytesRoundTrip)
    (hpub : DhPublicValid) (hct : KemCiphertextLenOf) (hbound : KemCiphertextLenBound)
    (hoeq : Tacenta.UnitHeadroomInvariant.OptionEqU64Shape
      (@core.option.Option.Insts.CoreCmpPartialEqOption.eq))
    {E : Type} (rc : rand_core_1.RngCore E) (crc : rand_core_1.CryptoRng E)
    (our : lifecycle.Identity) (bundle : lifecycle.PublishedBundle)
    (expected : tacenta_boundary.dh.PublicKeyBytes) (rng0 rng1 : E) (s : lifecycle.Session)
    (h : lifecycle.establish_initiator_for rc crc our bundle expected rng0 =
      ok (core.result.Result.Ok s, rng1)) :
    ∃ z v, lifecycle.Session.export (withExhaustedSend s) = ok z ∧
      zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref vecInst z = ok v ∧
      lifecycle.Session.import (alloc.vec.Vec.deref v) = ok (core.result.Result.Ok (withExhaustedSend s)) ∧
      ∀ k, ¬ CounterRoom (withExhaustedSend s) k := by
  have hinv := establish_initiator_for_admissible rc crc hpub hct hoeq our bundle expected rng0 rng1 s h
  obtain ⟨p, rfl⟩ := establish_initiator_for_parts rc crc our bundle expected rng0 rng1 s h
  exact export_import_exhausted_chain hz hbr hsl hpriv hpubb p.session _ _ _ _ _ _
    (codecShape_parts hpubb hct hbound p) hinv

/-- **Acceptance does not give the ceilings**: under the nine laws of `export_import_established`, if
`establish_initiator_for` succeeds once, then it is false that every session `Session::import` accepts meets
`CounterHeadroom` (room for zero further operations, `counterRoom_zero`).  The bytes are the parked copy's of
`established_parked_clock_accepted`. -/
theorem acceptance_does_not_give_headroom (hz : ZeroizingVecRoundTrip) (hbr : OptionBranchSome)
    (hsl : VecAsSlice) (hpriv : DhPrivateBytesRoundTrip) (hpubb : DhPublicBytesRoundTrip)
    (hpub : DhPublicValid) (hct : KemCiphertextLenOf) (hbound : KemCiphertextLenBound)
    (hoeq : Tacenta.UnitHeadroomInvariant.OptionEqU64Shape
      (@core.option.Option.Insts.CoreCmpPartialEqOption.eq))
    {E : Type} (rc : rand_core_1.RngCore E) (crc : rand_core_1.CryptoRng E)
    (our : lifecycle.Identity) (bundle : lifecycle.PublishedBundle)
    (expected : tacenta_boundary.dh.PublicKeyBytes) (rng0 rng1 : E) (s : lifecycle.Session)
    (h : lifecycle.establish_initiator_for rc crc our bundle expected rng0 =
      ok (core.result.Result.Ok s, rng1)) :
    ¬ ∀ (b : Slice U8) (s' : lifecycle.Session),
      lifecycle.Session.import b = ok (core.result.Result.Ok s') → CounterHeadroom s' := by
  intro hall
  obtain ⟨z, v, -, -, himp, hno⟩ := established_parked_clock_accepted hz hbr hsl hpriv hpubb hpub hct hbound
    hoeq rc crc our bundle expected rng0 rng1 s h
  exact hno 0 ((counterRoom_zero _).mpr (hall _ _ himp))

end Tacenta.UnitLifecycleImportBudget

-- The pins `genpins.py` writes after this line print each statement whole: with no cut at depth 50
-- (`pp.deepTerms`) and each omitted proof with its proposition, `(⋯ : P)` (`pp.proofs.withType`). `attest.py`
-- refuses a statement pin that prints a bare `⋯`, and every other `pp` option.
set_option pp.deepTerms true
set_option pp.proofs.withType true

/-! ## Pins

The constants each result depends on, and the statement of each result and definition, held by the
build.  `attest.py` requires every one of them (`REQUIRED_PINS`, `REQUIRED_STATEMENT_PINS`,
`REQUIRED_PRINT_FORM`). -/

/--
info: 'Tacenta.UnitLifecycleImportBudget.counterRoom_iff_roomCheck' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kem.EncapsState,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleImportBudget.counterRoom_iff_roomCheck

/--
info: 'Tacenta.UnitLifecycleImportBudget.roomCheck_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kem.EncapsState,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleImportBudget.roomCheck_zero

/--
info: 'Tacenta.UnitLifecycleImportBudget.read_epoch_ne' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleImportBudget.read_epoch_ne

/--
info: 'Tacenta.UnitLifecycleImportBudget.decode_state_epoch' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kem.EncapsState,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair,
 tacenta_session_unit.tacenta_kem.EncapsState.from_bytes,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.from_bytes,
 tacenta_session_unit.core.num.Usize.div_ceil]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleImportBudget.decode_state_epoch

/--
info: 'Tacenta.UnitLifecycleImportBudget.braid_from_bytes_epoch' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kem.CT1_LEN,
 tacenta_session_unit.tacenta_kem.CT2_LEN,
 tacenta_session_unit.tacenta_kem.EK_VECTOR_LEN,
 tacenta_session_unit.tacenta_kem.EncapsState,
 tacenta_session_unit.tacenta_kem.HEADER_LEN,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair,
 tacenta_session_unit.tacenta_kem.validate_ek,
 tacenta_session_unit.tacenta_kem.EncapsState.from_bytes,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.from_bytes,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.header,
 tacenta_session_unit.core.num.Usize.div_ceil]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleImportBudget.braid_from_bytes_epoch

/--
info: 'Tacenta.UnitLifecycleImportBudget.import_ok_unchecked' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kem.CT1_LEN,
 tacenta_session_unit.tacenta_kem.CT2_LEN,
 tacenta_session_unit.tacenta_kem.EK_VECTOR_LEN,
 tacenta_session_unit.tacenta_kem.EncapsState,
 tacenta_session_unit.tacenta_kem.HEADER_LEN,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair,
 tacenta_session_unit.tacenta_kem.validate_ek,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_boundary.dh.is_prime_order_public,
 tacenta_session_unit.tacenta_boundary.kem.ciphertext_len,
 tacenta_session_unit.tacenta_kem.EncapsState.from_bytes,
 tacenta_session_unit.tacenta_kem.EncapsState.to_bytes,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.from_bytes,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.header,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.to_bytes,
 tacenta_session_unit.zeroize.Zeroizing.new,
 tacenta_session_unit.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.alloc.vec.Vec.as_slice,
 tacenta_session_unit.core.num.Usize.div_ceil,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.from_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.public_key,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.to_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.from_bytes,
 tacenta_session_unit.zeroize.Zeroize.Blanket.zeroize,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 tacenta_session_unit.alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.core.option.Option.Insts.CoreCmpPartialEqOption.eq,
 tacenta_session_unit.core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual,
 tacenta_session_unit.core.option.Option.Insts.CoreOpsTry_traitTry.branch,
 tacenta_session_unit.lifecycle.PrekeyStore.to_bytes._native.decide.ax_1]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleImportBudget.import_ok_unchecked

/--
info: 'Tacenta.UnitLifecycleImportBudget.import_unchecked_braid' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kem.CT1_LEN,
 tacenta_session_unit.tacenta_kem.CT2_LEN,
 tacenta_session_unit.tacenta_kem.EK_VECTOR_LEN,
 tacenta_session_unit.tacenta_kem.EncapsState,
 tacenta_session_unit.tacenta_kem.HEADER_LEN,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair,
 tacenta_session_unit.tacenta_kem.validate_ek,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_kem.EncapsState.from_bytes,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.from_bytes,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.header,
 tacenta_session_unit.core.num.Usize.div_ceil,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.from_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.from_bytes,
 tacenta_session_unit.core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual,
 tacenta_session_unit.core.option.Option.Insts.CoreOpsTry_traitTry.branch]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleImportBudget.import_unchecked_braid

/--
info: 'Tacenta.UnitLifecycleImportBudget.import_ok_braid_epoch' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kem.CT1_LEN,
 tacenta_session_unit.tacenta_kem.CT2_LEN,
 tacenta_session_unit.tacenta_kem.EK_VECTOR_LEN,
 tacenta_session_unit.tacenta_kem.EncapsState,
 tacenta_session_unit.tacenta_kem.HEADER_LEN,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair,
 tacenta_session_unit.tacenta_kem.validate_ek,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_boundary.dh.is_prime_order_public,
 tacenta_session_unit.tacenta_boundary.kem.ciphertext_len,
 tacenta_session_unit.tacenta_kem.EncapsState.from_bytes,
 tacenta_session_unit.tacenta_kem.EncapsState.to_bytes,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.from_bytes,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.header,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.to_bytes,
 tacenta_session_unit.zeroize.Zeroizing.new,
 tacenta_session_unit.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.alloc.vec.Vec.as_slice,
 tacenta_session_unit.core.num.Usize.div_ceil,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.from_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.public_key,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.to_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.from_bytes,
 tacenta_session_unit.zeroize.Zeroize.Blanket.zeroize,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 tacenta_session_unit.alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.core.option.Option.Insts.CoreCmpPartialEqOption.eq,
 tacenta_session_unit.core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual,
 tacenta_session_unit.core.option.Option.Insts.CoreOpsTry_traitTry.branch,
 tacenta_session_unit.lifecycle.PrekeyStore.to_bytes._native.decide.ax_1]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleImportBudget.import_ok_braid_epoch

/--
info: 'Tacenta.UnitLifecycleImportBudget.import_ok_ceilings' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kem.CT1_LEN,
 tacenta_session_unit.tacenta_kem.CT2_LEN,
 tacenta_session_unit.tacenta_kem.EK_VECTOR_LEN,
 tacenta_session_unit.tacenta_kem.EncapsState,
 tacenta_session_unit.tacenta_kem.HEADER_LEN,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair,
 tacenta_session_unit.tacenta_kem.validate_ek,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_boundary.dh.is_prime_order_public,
 tacenta_session_unit.tacenta_boundary.kem.ciphertext_len,
 tacenta_session_unit.tacenta_kem.EncapsState.from_bytes,
 tacenta_session_unit.tacenta_kem.EncapsState.to_bytes,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.from_bytes,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.header,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.to_bytes,
 tacenta_session_unit.zeroize.Zeroizing.new,
 tacenta_session_unit.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.alloc.vec.Vec.as_slice,
 tacenta_session_unit.core.num.Usize.div_ceil,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.from_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.public_key,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.to_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.from_bytes,
 tacenta_session_unit.zeroize.Zeroize.Blanket.zeroize,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 tacenta_session_unit.alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.core.option.Option.Insts.CoreCmpPartialEqOption.eq,
 tacenta_session_unit.core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual,
 tacenta_session_unit.core.option.Option.Insts.CoreOpsTry_traitTry.branch,
 tacenta_session_unit.lifecycle.PrekeyStore.to_bytes._native.decide.ax_1]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleImportBudget.import_ok_ceilings

/--
info: 'Tacenta.UnitLifecycleImportBudget.import_ok_budget' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kem.CT1_LEN,
 tacenta_session_unit.tacenta_kem.CT2_LEN,
 tacenta_session_unit.tacenta_kem.EK_VECTOR_LEN,
 tacenta_session_unit.tacenta_kem.EncapsState,
 tacenta_session_unit.tacenta_kem.HEADER_LEN,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair,
 tacenta_session_unit.tacenta_kem.validate_ek,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_boundary.dh.is_prime_order_public,
 tacenta_session_unit.tacenta_boundary.kem.ciphertext_len,
 tacenta_session_unit.tacenta_kem.EncapsState.from_bytes,
 tacenta_session_unit.tacenta_kem.EncapsState.to_bytes,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.from_bytes,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.header,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.to_bytes,
 tacenta_session_unit.zeroize.Zeroizing.new,
 tacenta_session_unit.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.alloc.vec.Vec.as_slice,
 tacenta_session_unit.core.num.Usize.div_ceil,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.from_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.public_key,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.to_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.from_bytes,
 tacenta_session_unit.zeroize.Zeroize.Blanket.zeroize,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 tacenta_session_unit.alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.core.option.Option.Insts.CoreCmpPartialEqOption.eq,
 tacenta_session_unit.core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual,
 tacenta_session_unit.core.option.Option.Insts.CoreOpsTry_traitTry.branch,
 tacenta_session_unit.lifecycle.PrekeyStore.to_bytes._native.decide.ax_1]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleImportBudget.import_ok_budget

/--
info: 'Tacenta.UnitLifecycleImportBudget.structural_withClock' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kem.EncapsState,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_boundary.dh.is_prime_order_public,
 tacenta_session_unit.tacenta_boundary.kem.ciphertext_len,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.public_key,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.from_bytes,
 tacenta_session_unit.core.option.Option.Insts.CoreCmpPartialEqOption.eq]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleImportBudget.structural_withClock

/--
info: 'Tacenta.UnitLifecycleImportBudget.invariant_withClock' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kem.CT1_LEN,
 tacenta_session_unit.tacenta_kem.CT2_LEN,
 tacenta_session_unit.tacenta_kem.EK_VECTOR_LEN,
 tacenta_session_unit.tacenta_kem.EncapsState,
 tacenta_session_unit.tacenta_kem.HEADER_LEN,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair,
 tacenta_session_unit.tacenta_kem.validate_ek,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_boundary.dh.is_prime_order_public,
 tacenta_session_unit.tacenta_boundary.kem.ciphertext_len,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.header,
 tacenta_session_unit.core.num.Usize.div_ceil,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.public_key,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.from_bytes,
 tacenta_session_unit.core.option.Option.Insts.CoreCmpPartialEqOption.eq]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleImportBudget.invariant_withClock

/--
info: 'Tacenta.UnitLifecycleImportBudget.codecShape_withClock' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kem.EncapsState,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleImportBudget.codecShape_withClock

/--
info: 'Tacenta.UnitLifecycleImportBudget.withClock_parked_no_room' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kem.EncapsState,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleImportBudget.withClock_parked_no_room

/--
info: 'Tacenta.UnitLifecycleImportBudget.export_import_parked_clock' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kem.CT1_LEN,
 tacenta_session_unit.tacenta_kem.CT2_LEN,
 tacenta_session_unit.tacenta_kem.EK_VECTOR_LEN,
 tacenta_session_unit.tacenta_kem.EncapsState,
 tacenta_session_unit.tacenta_kem.HEADER_LEN,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair,
 tacenta_session_unit.tacenta_kem.encapsulate1,
 tacenta_session_unit.tacenta_kem.encapsulate2,
 tacenta_session_unit.tacenta_kem.validate_ek,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.rand_core_1.error.Error,
 tacenta_session_unit.tacenta_boundary.aead.decrypt,
 tacenta_session_unit.tacenta_boundary.aead.encrypt,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_boundary.dh.is_prime_order_public,
 tacenta_session_unit.tacenta_boundary.kem.KeyPair,
 tacenta_session_unit.tacenta_boundary.kem.ciphertext_len,
 tacenta_session_unit.tacenta_boundary.kem.decapsulate,
 tacenta_session_unit.tacenta_boundary.kem.encapsulate,
 tacenta_session_unit.tacenta_boundary.xeddsa.verify,
 tacenta_session_unit.tacenta_kem.EncapsState.from_bytes,
 tacenta_session_unit.tacenta_kem.EncapsState.to_bytes,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.from_bytes,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.generate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.header,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.to_bytes,
 tacenta_session_unit.zeroize.Zeroizing.new,
 tacenta_session_unit.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.Pair.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.TupleABC.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.alloc.vec.Vec.as_slice,
 tacenta_session_unit.alloc.vec.Vec.capacity,
 tacenta_session_unit.alloc.vec.Vec.pop,
 tacenta_session_unit.alloc.vec.Vec.truncate,
 tacenta_session_unit.core.num.Usize.div_ceil,
 tacenta_session_unit.core.option.Option.as_mut,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.agree,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.from_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.public_key,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.to_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.from_bytes,
 tacenta_session_unit.zeroize.Zeroize.Blanket.zeroize,
 tacenta_session_unit.tacenta_kem.EncapsState.Insts.CoreCloneClone.clone,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 tacenta_session_unit.alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.core.option.Option.Insts.CoreCloneClone.clone,
 tacenta_session_unit.core.option.Option.Insts.CoreCmpPartialEqOption.eq,
 tacenta_session_unit.core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual,
 tacenta_session_unit.core.option.Option.Insts.CoreOpsTry_traitTry.branch,
 tacenta_session_unit.lifecycle.PrekeyStore.to_bytes._native.decide.ax_1,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes.eq,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleImportBudget.export_import_parked_clock

/--
info: 'Tacenta.UnitLifecycleImportBudget.structural_withExhaustedSend' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kem.EncapsState,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_boundary.dh.is_prime_order_public,
 tacenta_session_unit.tacenta_boundary.kem.ciphertext_len,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.public_key,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.from_bytes,
 tacenta_session_unit.core.option.Option.Insts.CoreCmpPartialEqOption.eq]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleImportBudget.structural_withExhaustedSend

/--
info: 'Tacenta.UnitLifecycleImportBudget.invariant_withExhaustedSend' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kem.CT1_LEN,
 tacenta_session_unit.tacenta_kem.CT2_LEN,
 tacenta_session_unit.tacenta_kem.EK_VECTOR_LEN,
 tacenta_session_unit.tacenta_kem.EncapsState,
 tacenta_session_unit.tacenta_kem.HEADER_LEN,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair,
 tacenta_session_unit.tacenta_kem.validate_ek,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_boundary.dh.is_prime_order_public,
 tacenta_session_unit.tacenta_boundary.kem.ciphertext_len,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.header,
 tacenta_session_unit.core.num.Usize.div_ceil,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.public_key,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.from_bytes,
 tacenta_session_unit.core.option.Option.Insts.CoreCmpPartialEqOption.eq]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleImportBudget.invariant_withExhaustedSend

/--
info: 'Tacenta.UnitLifecycleImportBudget.codecShape_withExhaustedSend' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kem.EncapsState,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleImportBudget.codecShape_withExhaustedSend

/--
info: 'Tacenta.UnitLifecycleImportBudget.withExhaustedSend_no_room' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kem.EncapsState,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleImportBudget.withExhaustedSend_no_room

/--
info: 'Tacenta.UnitLifecycleImportBudget.export_import_exhausted_chain' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kem.CT1_LEN,
 tacenta_session_unit.tacenta_kem.CT2_LEN,
 tacenta_session_unit.tacenta_kem.EK_VECTOR_LEN,
 tacenta_session_unit.tacenta_kem.EncapsState,
 tacenta_session_unit.tacenta_kem.HEADER_LEN,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair,
 tacenta_session_unit.tacenta_kem.encapsulate1,
 tacenta_session_unit.tacenta_kem.encapsulate2,
 tacenta_session_unit.tacenta_kem.validate_ek,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.rand_core_1.error.Error,
 tacenta_session_unit.tacenta_boundary.aead.decrypt,
 tacenta_session_unit.tacenta_boundary.aead.encrypt,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_boundary.dh.is_prime_order_public,
 tacenta_session_unit.tacenta_boundary.kem.KeyPair,
 tacenta_session_unit.tacenta_boundary.kem.ciphertext_len,
 tacenta_session_unit.tacenta_boundary.kem.decapsulate,
 tacenta_session_unit.tacenta_boundary.kem.encapsulate,
 tacenta_session_unit.tacenta_boundary.xeddsa.verify,
 tacenta_session_unit.tacenta_kem.EncapsState.from_bytes,
 tacenta_session_unit.tacenta_kem.EncapsState.to_bytes,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.from_bytes,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.generate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.header,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.to_bytes,
 tacenta_session_unit.zeroize.Zeroizing.new,
 tacenta_session_unit.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.Pair.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.TupleABC.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.alloc.vec.Vec.as_slice,
 tacenta_session_unit.alloc.vec.Vec.capacity,
 tacenta_session_unit.alloc.vec.Vec.pop,
 tacenta_session_unit.alloc.vec.Vec.truncate,
 tacenta_session_unit.core.num.Usize.div_ceil,
 tacenta_session_unit.core.option.Option.as_mut,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.agree,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.from_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.public_key,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.to_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.from_bytes,
 tacenta_session_unit.zeroize.Zeroize.Blanket.zeroize,
 tacenta_session_unit.tacenta_kem.EncapsState.Insts.CoreCloneClone.clone,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 tacenta_session_unit.alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.core.option.Option.Insts.CoreCloneClone.clone,
 tacenta_session_unit.core.option.Option.Insts.CoreCmpPartialEqOption.eq,
 tacenta_session_unit.core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual,
 tacenta_session_unit.core.option.Option.Insts.CoreOpsTry_traitTry.branch,
 tacenta_session_unit.lifecycle.PrekeyStore.to_bytes._native.decide.ax_1,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes.eq,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleImportBudget.export_import_exhausted_chain

/--
info: 'Tacenta.UnitLifecycleImportBudget.established_parked_clock_accepted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kem.CT1_LEN,
 tacenta_session_unit.tacenta_kem.CT2_LEN,
 tacenta_session_unit.tacenta_kem.EK_VECTOR_LEN,
 tacenta_session_unit.tacenta_kem.EncapsState,
 tacenta_session_unit.tacenta_kem.HEADER_LEN,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair,
 tacenta_session_unit.tacenta_kem.encapsulate1,
 tacenta_session_unit.tacenta_kem.encapsulate2,
 tacenta_session_unit.tacenta_kem.validate_ek,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.rand_core_1.error.Error,
 tacenta_session_unit.tacenta_boundary.aead.decrypt,
 tacenta_session_unit.tacenta_boundary.aead.encrypt,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_boundary.dh.is_prime_order_public,
 tacenta_session_unit.tacenta_boundary.kem.KeyPair,
 tacenta_session_unit.tacenta_boundary.kem.ciphertext_len,
 tacenta_session_unit.tacenta_boundary.kem.decapsulate,
 tacenta_session_unit.tacenta_boundary.kem.encapsulate,
 tacenta_session_unit.tacenta_boundary.xeddsa.verify,
 tacenta_session_unit.tacenta_kem.EncapsState.from_bytes,
 tacenta_session_unit.tacenta_kem.EncapsState.to_bytes,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.from_bytes,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.generate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.header,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.to_bytes,
 tacenta_session_unit.zeroize.Zeroizing.new,
 tacenta_session_unit.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.Pair.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.TupleABC.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.alloc.vec.Vec.as_slice,
 tacenta_session_unit.alloc.vec.Vec.capacity,
 tacenta_session_unit.alloc.vec.Vec.pop,
 tacenta_session_unit.alloc.vec.Vec.truncate,
 tacenta_session_unit.core.num.Usize.div_ceil,
 tacenta_session_unit.core.option.Option.as_mut,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.agree,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.from_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.public_key,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.to_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.from_bytes,
 tacenta_session_unit.zeroize.Zeroize.Blanket.zeroize,
 tacenta_session_unit.tacenta_kem.EncapsState.Insts.CoreCloneClone.clone,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 tacenta_session_unit.alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.core.option.Option.Insts.CoreCloneClone.clone,
 tacenta_session_unit.core.option.Option.Insts.CoreCmpPartialEqOption.eq,
 tacenta_session_unit.core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual,
 tacenta_session_unit.core.option.Option.Insts.CoreOpsTry_traitTry.branch,
 tacenta_session_unit.lifecycle.PrekeyStore.to_bytes._native.decide.ax_1,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes.eq,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleImportBudget.established_parked_clock_accepted

/--
info: 'Tacenta.UnitLifecycleImportBudget.established_exhausted_chain_accepted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kem.CT1_LEN,
 tacenta_session_unit.tacenta_kem.CT2_LEN,
 tacenta_session_unit.tacenta_kem.EK_VECTOR_LEN,
 tacenta_session_unit.tacenta_kem.EncapsState,
 tacenta_session_unit.tacenta_kem.HEADER_LEN,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair,
 tacenta_session_unit.tacenta_kem.encapsulate1,
 tacenta_session_unit.tacenta_kem.encapsulate2,
 tacenta_session_unit.tacenta_kem.validate_ek,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.rand_core_1.error.Error,
 tacenta_session_unit.tacenta_boundary.aead.decrypt,
 tacenta_session_unit.tacenta_boundary.aead.encrypt,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_boundary.dh.is_prime_order_public,
 tacenta_session_unit.tacenta_boundary.kem.KeyPair,
 tacenta_session_unit.tacenta_boundary.kem.ciphertext_len,
 tacenta_session_unit.tacenta_boundary.kem.decapsulate,
 tacenta_session_unit.tacenta_boundary.kem.encapsulate,
 tacenta_session_unit.tacenta_boundary.xeddsa.verify,
 tacenta_session_unit.tacenta_kem.EncapsState.from_bytes,
 tacenta_session_unit.tacenta_kem.EncapsState.to_bytes,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.from_bytes,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.generate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.header,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.to_bytes,
 tacenta_session_unit.zeroize.Zeroizing.new,
 tacenta_session_unit.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.Pair.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.TupleABC.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.alloc.vec.Vec.as_slice,
 tacenta_session_unit.alloc.vec.Vec.capacity,
 tacenta_session_unit.alloc.vec.Vec.pop,
 tacenta_session_unit.alloc.vec.Vec.truncate,
 tacenta_session_unit.core.num.Usize.div_ceil,
 tacenta_session_unit.core.option.Option.as_mut,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.agree,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.from_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.public_key,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.to_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.from_bytes,
 tacenta_session_unit.zeroize.Zeroize.Blanket.zeroize,
 tacenta_session_unit.tacenta_kem.EncapsState.Insts.CoreCloneClone.clone,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 tacenta_session_unit.alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.core.option.Option.Insts.CoreCloneClone.clone,
 tacenta_session_unit.core.option.Option.Insts.CoreCmpPartialEqOption.eq,
 tacenta_session_unit.core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual,
 tacenta_session_unit.core.option.Option.Insts.CoreOpsTry_traitTry.branch,
 tacenta_session_unit.lifecycle.PrekeyStore.to_bytes._native.decide.ax_1,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes.eq,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleImportBudget.established_exhausted_chain_accepted

/--
info: 'Tacenta.UnitLifecycleImportBudget.acceptance_does_not_give_headroom' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kem.CT1_LEN,
 tacenta_session_unit.tacenta_kem.CT2_LEN,
 tacenta_session_unit.tacenta_kem.EK_VECTOR_LEN,
 tacenta_session_unit.tacenta_kem.EncapsState,
 tacenta_session_unit.tacenta_kem.HEADER_LEN,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair,
 tacenta_session_unit.tacenta_kem.encapsulate1,
 tacenta_session_unit.tacenta_kem.encapsulate2,
 tacenta_session_unit.tacenta_kem.validate_ek,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.rand_core_1.error.Error,
 tacenta_session_unit.tacenta_boundary.aead.decrypt,
 tacenta_session_unit.tacenta_boundary.aead.encrypt,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_boundary.dh.is_prime_order_public,
 tacenta_session_unit.tacenta_boundary.kem.KeyPair,
 tacenta_session_unit.tacenta_boundary.kem.ciphertext_len,
 tacenta_session_unit.tacenta_boundary.kem.decapsulate,
 tacenta_session_unit.tacenta_boundary.kem.encapsulate,
 tacenta_session_unit.tacenta_boundary.xeddsa.verify,
 tacenta_session_unit.tacenta_kem.EncapsState.from_bytes,
 tacenta_session_unit.tacenta_kem.EncapsState.to_bytes,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.from_bytes,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.generate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.header,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.to_bytes,
 tacenta_session_unit.zeroize.Zeroizing.new,
 tacenta_session_unit.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.Pair.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.TupleABC.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.alloc.vec.Vec.as_slice,
 tacenta_session_unit.alloc.vec.Vec.capacity,
 tacenta_session_unit.alloc.vec.Vec.pop,
 tacenta_session_unit.alloc.vec.Vec.truncate,
 tacenta_session_unit.core.num.Usize.div_ceil,
 tacenta_session_unit.core.option.Option.as_mut,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.agree,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.from_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.public_key,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.to_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.from_bytes,
 tacenta_session_unit.zeroize.Zeroize.Blanket.zeroize,
 tacenta_session_unit.tacenta_kem.EncapsState.Insts.CoreCloneClone.clone,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 tacenta_session_unit.alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.core.option.Option.Insts.CoreCloneClone.clone,
 tacenta_session_unit.core.option.Option.Insts.CoreCmpPartialEqOption.eq,
 tacenta_session_unit.core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual,
 tacenta_session_unit.core.option.Option.Insts.CoreOpsTry_traitTry.branch,
 tacenta_session_unit.lifecycle.PrekeyStore.to_bytes._native.decide.ax_1,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes.eq,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleImportBudget.acceptance_does_not_give_headroom

/--
info: Tacenta.UnitLifecycleImportBudget.counterRoom_iff_roomCheck : ∀ (s : tacenta_session_unit.lifecycle.Session) (k : ℕ),
  Tacenta.UnitLifecycleSendPreserve.CounterRoom s k ↔ Tacenta.UnitLifecycleImportBudget.roomCheck s k = true
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleImportBudget.counterRoom_iff_roomCheck

/--
info: Tacenta.UnitLifecycleImportBudget.roomCheck_zero : ∀ (s : tacenta_session_unit.lifecycle.Session),
  Tacenta.UnitLifecycleImportBudget.roomCheck s 0 = Tacenta.UnitLifecycleRestoredSession.headroomCheck s
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleImportBudget.roomCheck_zero

/--
info: Tacenta.UnitLifecycleImportBudget.read_epoch_ne : ∀ (bytes : Aeneas.Std.Slice Aeneas.Std.U8) (pos : Aeneas.Std.Usize)
  (e : Aeneas.Std.U64),
  tacenta_session_unit.tacenta_braid.read_epoch bytes pos = Aeneas.Std.Result.ok (some e) →
    e ≠ Aeneas.Std.core.num.U64.MAX
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleImportBudget.read_epoch_ne

/--
info: Tacenta.UnitLifecycleImportBudget.decode_state_epoch : ∀ (tag : Aeneas.Std.U8) (bytes : Aeneas.Std.Slice Aeneas.Std.U8)
  (pos : Aeneas.Std.Usize) (st : tacenta_session_unit.tacenta_braid.State) (p : Aeneas.Std.Usize),
  tacenta_session_unit.tacenta_braid.decode_state tag bytes pos = Aeneas.Std.Result.ok (some (st, p)) →
    st = tacenta_session_unit.tacenta_braid.State.Failed ∨
      Tacenta.SessionUnitBraidT1.State.epoch_val st ≠ Aeneas.Std.core.num.U64.MAX
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleImportBudget.decode_state_epoch

/--
info: Tacenta.UnitLifecycleImportBudget.braid_from_bytes_epoch : ∀ (bytes : Aeneas.Std.Slice Aeneas.Std.U8)
  (b : tacenta_session_unit.tacenta_braid.Braid),
  tacenta_session_unit.tacenta_braid.Braid.from_bytes bytes =
      Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok b) →
    b.state = tacenta_session_unit.tacenta_braid.State.Failed ∨
      Tacenta.SessionUnitBraidT1.State.epoch_val b.state ≠ Aeneas.Std.core.num.U64.MAX
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleImportBudget.braid_from_bytes_epoch

/--
info: Tacenta.UnitLifecycleImportBudget.import_ok_unchecked : ∀ (b : Aeneas.Std.Slice Aeneas.Std.U8)
  (s : tacenta_session_unit.lifecycle.Session),
  tacenta_session_unit.lifecycle.Session.import b = Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok s) →
    tacenta_session_unit.lifecycle.Session.import_unchecked b =
      Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok s)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleImportBudget.import_ok_unchecked

/--
info: Tacenta.UnitLifecycleImportBudget.import_unchecked_braid : ∀ (bytes : Aeneas.Std.Slice Aeneas.Std.U8)
  (s : tacenta_session_unit.lifecycle.Session),
  tacenta_session_unit.lifecycle.Session.import_unchecked bytes =
      Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok s) →
    ∃ bsl,
      tacenta_session_unit.tacenta_braid.Braid.from_bytes bsl =
        Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok s.braid)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleImportBudget.import_unchecked_braid

/--
info: Tacenta.UnitLifecycleImportBudget.import_ok_braid_epoch : ∀ (b : Aeneas.Std.Slice Aeneas.Std.U8)
  (s : tacenta_session_unit.lifecycle.Session),
  tacenta_session_unit.lifecycle.Session.import b = Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok s) →
    ↑(Tacenta.SessionUnitBraidT1.State.epoch_val s.braid.state) < Aeneas.Std.U64.max
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleImportBudget.import_ok_braid_epoch

/--
info: Tacenta.UnitLifecycleImportBudget.import_ok_ceilings : ∀ (b : Aeneas.Std.Slice Aeneas.Std.U8)
  (s : tacenta_session_unit.lifecycle.Session),
  tacenta_session_unit.lifecycle.Session.import b = Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok s) →
    s.invariant = Aeneas.Std.Result.ok true ∧
      ↑s.triple.classical.events < Aeneas.Std.U32.max ∧
        ↑s.triple.post_quantum.epoch < Aeneas.Std.U64.max ∧
          ↑(Tacenta.SessionUnitBraidT1.State.epoch_val s.braid.state) < Aeneas.Std.U64.max
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleImportBudget.import_ok_ceilings

/--
info: Tacenta.UnitLifecycleImportBudget.import_ok_budget : ∀ (b : Aeneas.Std.Slice Aeneas.Std.U8)
  (s : tacenta_session_unit.lifecycle.Session),
  tacenta_session_unit.lifecycle.Session.import b = Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok s) →
    s.invariant = Aeneas.Std.Result.ok true ∧
      ↑s.triple.classical.events < Aeneas.Std.U32.max ∧
        ↑s.triple.post_quantum.epoch < Aeneas.Std.U64.max ∧
          ↑(Tacenta.SessionUnitBraidT1.State.epoch_val s.braid.state) < Aeneas.Std.U64.max ∧
            ∀ (k : ℕ),
              Tacenta.UnitLifecycleSendPreserve.CounterRoom s k ↔ Tacenta.UnitLifecycleImportBudget.roomCheck s k = true
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleImportBudget.import_ok_budget

/--
info: Tacenta.UnitLifecycleImportBudget.structural_withClock : ∀ (s : tacenta_session_unit.lifecycle.Session)
  (c : Aeneas.Std.U32), (Tacenta.UnitLifecycleImportBudget.withClock s c).structural_invariant = s.structural_invariant
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleImportBudget.structural_withClock

/--
info: Tacenta.UnitLifecycleImportBudget.invariant_withClock : ∀ (s : tacenta_session_unit.lifecycle.Session)
  (c : Aeneas.Std.U32),
  ↑c < Aeneas.Std.U32.max →
    (∀ e ∈ ↑s.triple.classical.skipped, ↑e.stored_at ≤ ↑c) →
      s.invariant = Aeneas.Std.Result.ok true →
        (Tacenta.UnitLifecycleImportBudget.withClock s c).invariant = Aeneas.Std.Result.ok true
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleImportBudget.invariant_withClock

/--
info: @Tacenta.UnitLifecycleImportBudget.codecShape_withClock : ∀ {s : tacenta_session_unit.lifecycle.Session}
  {epoch : Aeneas.Std.U64} {auth : tacenta_session_unit.tacenta_braid.Auth} {e : Aeneas.Std.U64}
  {c1 c2 : tacenta_session_unit.tacenta_spqr.Chain} {p : tacenta_session_unit.lifecycle.PendingInitial}
  (c : Aeneas.Std.U32),
  Tacenta.UnitLifecycleSessionRoundTrip.CodecShape s epoch auth e c1 c2 p →
    Tacenta.UnitLifecycleSessionRoundTrip.CodecShape (Tacenta.UnitLifecycleImportBudget.withClock s c) epoch auth e c1
      c2 p
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleImportBudget.codecShape_withClock

/--
info: Tacenta.UnitLifecycleImportBudget.withClock_parked_no_room : ∀ (s : tacenta_session_unit.lifecycle.Session) (k : ℕ),
  ¬Tacenta.UnitLifecycleSendPreserve.CounterRoom (Tacenta.UnitLifecycleImportBudget.withClock s 4294967294#u32) k
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleImportBudget.withClock_parked_no_room

/--
info: Tacenta.UnitLifecycleImportBudget.export_import_parked_clock : Tacenta.UnitLifecycleSessionCodec.ZeroizingVecRoundTrip →
  Tacenta.UnitLifecycleSessionCodec.OptionBranchSome →
    Tacenta.UnitLifecycleSessionCodec.VecAsSlice →
      Tacenta.UnitLifecycleSessionCodec.DhPrivateBytesRoundTrip →
        Tacenta.UnitLifecycleSessionCodec.DhPublicBytesRoundTrip →
          ∀ (s : tacenta_session_unit.lifecycle.Session) (epoch : Aeneas.Std.U64)
            (auth : tacenta_session_unit.tacenta_braid.Auth) (e : Aeneas.Std.U64)
            (c1 c2 : tacenta_session_unit.tacenta_spqr.Chain) (p : tacenta_session_unit.lifecycle.PendingInitial),
            Tacenta.UnitLifecycleSessionRoundTrip.CodecShape s epoch auth e c1 c2 p →
              s.invariant = Aeneas.Std.Result.ok true →
                ∃ z v,
                  (Tacenta.UnitLifecycleImportBudget.withClock s 4294967294#u32).export = Aeneas.Std.Result.ok z ∧
                    tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref
                          Tacenta.UnitLifecycleSessionCodec.vecInst z =
                        Aeneas.Std.Result.ok v ∧
                      tacenta_session_unit.lifecycle.Session.import v.deref =
                          Aeneas.Std.Result.ok
                            (Aeneas.Std.core.result.Result.Ok
                              (Tacenta.UnitLifecycleImportBudget.withClock s 4294967294#u32)) ∧
                        ∀ (k : ℕ),
                          ¬Tacenta.UnitLifecycleSendPreserve.CounterRoom
                              (Tacenta.UnitLifecycleImportBudget.withClock s 4294967294#u32) k
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleImportBudget.export_import_parked_clock

/--
info: Tacenta.UnitLifecycleImportBudget.structural_withExhaustedSend : ∀ (s : tacenta_session_unit.lifecycle.Session),
  (Tacenta.UnitLifecycleImportBudget.withExhaustedSend s).structural_invariant = s.structural_invariant
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleImportBudget.structural_withExhaustedSend

/--
info: Tacenta.UnitLifecycleImportBudget.invariant_withExhaustedSend : ∀ (s : tacenta_session_unit.lifecycle.Session),
  s.invariant = Aeneas.Std.Result.ok true →
    (Tacenta.UnitLifecycleImportBudget.withExhaustedSend s).invariant = Aeneas.Std.Result.ok true
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleImportBudget.invariant_withExhaustedSend

/--
info: @Tacenta.UnitLifecycleImportBudget.codecShape_withExhaustedSend : ∀ {s : tacenta_session_unit.lifecycle.Session}
  {epoch : Aeneas.Std.U64} {auth : tacenta_session_unit.tacenta_braid.Auth} {e : Aeneas.Std.U64}
  {c1 c2 : tacenta_session_unit.tacenta_spqr.Chain} {p : tacenta_session_unit.lifecycle.PendingInitial},
  Tacenta.UnitLifecycleSessionRoundTrip.CodecShape s epoch auth e c1 c2 p →
    Tacenta.UnitLifecycleSessionRoundTrip.CodecShape (Tacenta.UnitLifecycleImportBudget.withExhaustedSend s) epoch auth
      e { ck := c1.ck, n := Aeneas.Std.core.num.U64.MAX } c2 p
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleImportBudget.codecShape_withExhaustedSend

/--
info: @Tacenta.UnitLifecycleImportBudget.withExhaustedSend_no_room : ∀ {s : tacenta_session_unit.lifecycle.Session}
  {epoch : Aeneas.Std.U64} {auth : tacenta_session_unit.tacenta_braid.Auth} {e : Aeneas.Std.U64}
  {c1 c2 : tacenta_session_unit.tacenta_spqr.Chain} {p : tacenta_session_unit.lifecycle.PendingInitial},
  Tacenta.UnitLifecycleSessionRoundTrip.CodecShape s epoch auth e c1 c2 p →
    ∀ (k : ℕ), ¬Tacenta.UnitLifecycleSendPreserve.CounterRoom (Tacenta.UnitLifecycleImportBudget.withExhaustedSend s) k
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleImportBudget.withExhaustedSend_no_room

/--
info: Tacenta.UnitLifecycleImportBudget.export_import_exhausted_chain : Tacenta.UnitLifecycleSessionCodec.ZeroizingVecRoundTrip →
  Tacenta.UnitLifecycleSessionCodec.OptionBranchSome →
    Tacenta.UnitLifecycleSessionCodec.VecAsSlice →
      Tacenta.UnitLifecycleSessionCodec.DhPrivateBytesRoundTrip →
        Tacenta.UnitLifecycleSessionCodec.DhPublicBytesRoundTrip →
          ∀ (s : tacenta_session_unit.lifecycle.Session) (epoch : Aeneas.Std.U64)
            (auth : tacenta_session_unit.tacenta_braid.Auth) (e : Aeneas.Std.U64)
            (c1 c2 : tacenta_session_unit.tacenta_spqr.Chain) (p : tacenta_session_unit.lifecycle.PendingInitial),
            Tacenta.UnitLifecycleSessionRoundTrip.CodecShape s epoch auth e c1 c2 p →
              s.invariant = Aeneas.Std.Result.ok true →
                ∃ z v,
                  (Tacenta.UnitLifecycleImportBudget.withExhaustedSend s).export = Aeneas.Std.Result.ok z ∧
                    tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref
                          Tacenta.UnitLifecycleSessionCodec.vecInst z =
                        Aeneas.Std.Result.ok v ∧
                      tacenta_session_unit.lifecycle.Session.import v.deref =
                          Aeneas.Std.Result.ok
                            (Aeneas.Std.core.result.Result.Ok (Tacenta.UnitLifecycleImportBudget.withExhaustedSend s)) ∧
                        ∀ (k : ℕ),
                          ¬Tacenta.UnitLifecycleSendPreserve.CounterRoom
                              (Tacenta.UnitLifecycleImportBudget.withExhaustedSend s) k
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleImportBudget.export_import_exhausted_chain

/--
info: Tacenta.UnitLifecycleImportBudget.established_parked_clock_accepted : Tacenta.UnitLifecycleSessionCodec.ZeroizingVecRoundTrip →
  Tacenta.UnitLifecycleSessionCodec.OptionBranchSome →
    Tacenta.UnitLifecycleSessionCodec.VecAsSlice →
      Tacenta.UnitLifecycleSessionCodec.DhPrivateBytesRoundTrip →
        Tacenta.UnitLifecycleSessionCodec.DhPublicBytesRoundTrip →
          Tacenta.UnitLifecycleEstablishInitiatorShape.DhPublicValid →
            Tacenta.UnitLifecycleEstablishInitiatorShape.KemCiphertextLenOf →
              Tacenta.UnitLifecycleRestoredSession.KemCiphertextLenBound →
                Tacenta.UnitHeadroomInvariant.OptionEqU64Shape
                    @tacenta_session_unit.core.option.Option.Insts.CoreCmpPartialEqOption.eq →
                  ∀ {E : Type} (rc : tacenta_session_unit.rand_core_1.RngCore E)
                    (crc : tacenta_session_unit.rand_core_1.CryptoRng E) (our : tacenta_session_unit.lifecycle.Identity)
                    (bundle : tacenta_session_unit.lifecycle.PublishedBundle)
                    (expected : tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes) (rng0 rng1 : E)
                    (s : tacenta_session_unit.lifecycle.Session),
                    tacenta_session_unit.lifecycle.establish_initiator_for rc crc our bundle expected rng0 =
                        Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok s, rng1) →
                      ∃ z v,
                        (Tacenta.UnitLifecycleImportBudget.withClock s 4294967294#u32).export = Aeneas.Std.Result.ok z ∧
                          tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref
                                Tacenta.UnitLifecycleSessionCodec.vecInst z =
                              Aeneas.Std.Result.ok v ∧
                            tacenta_session_unit.lifecycle.Session.import v.deref =
                                Aeneas.Std.Result.ok
                                  (Aeneas.Std.core.result.Result.Ok
                                    (Tacenta.UnitLifecycleImportBudget.withClock s 4294967294#u32)) ∧
                              ∀ (k : ℕ),
                                ¬Tacenta.UnitLifecycleSendPreserve.CounterRoom
                                    (Tacenta.UnitLifecycleImportBudget.withClock s 4294967294#u32) k
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleImportBudget.established_parked_clock_accepted

/--
info: Tacenta.UnitLifecycleImportBudget.established_exhausted_chain_accepted : Tacenta.UnitLifecycleSessionCodec.ZeroizingVecRoundTrip →
  Tacenta.UnitLifecycleSessionCodec.OptionBranchSome →
    Tacenta.UnitLifecycleSessionCodec.VecAsSlice →
      Tacenta.UnitLifecycleSessionCodec.DhPrivateBytesRoundTrip →
        Tacenta.UnitLifecycleSessionCodec.DhPublicBytesRoundTrip →
          Tacenta.UnitLifecycleEstablishInitiatorShape.DhPublicValid →
            Tacenta.UnitLifecycleEstablishInitiatorShape.KemCiphertextLenOf →
              Tacenta.UnitLifecycleRestoredSession.KemCiphertextLenBound →
                Tacenta.UnitHeadroomInvariant.OptionEqU64Shape
                    @tacenta_session_unit.core.option.Option.Insts.CoreCmpPartialEqOption.eq →
                  ∀ {E : Type} (rc : tacenta_session_unit.rand_core_1.RngCore E)
                    (crc : tacenta_session_unit.rand_core_1.CryptoRng E) (our : tacenta_session_unit.lifecycle.Identity)
                    (bundle : tacenta_session_unit.lifecycle.PublishedBundle)
                    (expected : tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes) (rng0 rng1 : E)
                    (s : tacenta_session_unit.lifecycle.Session),
                    tacenta_session_unit.lifecycle.establish_initiator_for rc crc our bundle expected rng0 =
                        Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok s, rng1) →
                      ∃ z v,
                        (Tacenta.UnitLifecycleImportBudget.withExhaustedSend s).export = Aeneas.Std.Result.ok z ∧
                          tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref
                                Tacenta.UnitLifecycleSessionCodec.vecInst z =
                              Aeneas.Std.Result.ok v ∧
                            tacenta_session_unit.lifecycle.Session.import v.deref =
                                Aeneas.Std.Result.ok
                                  (Aeneas.Std.core.result.Result.Ok
                                    (Tacenta.UnitLifecycleImportBudget.withExhaustedSend s)) ∧
                              ∀ (k : ℕ),
                                ¬Tacenta.UnitLifecycleSendPreserve.CounterRoom
                                    (Tacenta.UnitLifecycleImportBudget.withExhaustedSend s) k
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleImportBudget.established_exhausted_chain_accepted

/--
info: Tacenta.UnitLifecycleImportBudget.acceptance_does_not_give_headroom : Tacenta.UnitLifecycleSessionCodec.ZeroizingVecRoundTrip →
  Tacenta.UnitLifecycleSessionCodec.OptionBranchSome →
    Tacenta.UnitLifecycleSessionCodec.VecAsSlice →
      Tacenta.UnitLifecycleSessionCodec.DhPrivateBytesRoundTrip →
        Tacenta.UnitLifecycleSessionCodec.DhPublicBytesRoundTrip →
          Tacenta.UnitLifecycleEstablishInitiatorShape.DhPublicValid →
            Tacenta.UnitLifecycleEstablishInitiatorShape.KemCiphertextLenOf →
              Tacenta.UnitLifecycleRestoredSession.KemCiphertextLenBound →
                Tacenta.UnitHeadroomInvariant.OptionEqU64Shape
                    @tacenta_session_unit.core.option.Option.Insts.CoreCmpPartialEqOption.eq →
                  ∀ {E : Type} (rc : tacenta_session_unit.rand_core_1.RngCore E)
                    (crc : tacenta_session_unit.rand_core_1.CryptoRng E) (our : tacenta_session_unit.lifecycle.Identity)
                    (bundle : tacenta_session_unit.lifecycle.PublishedBundle)
                    (expected : tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes) (rng0 rng1 : E)
                    (s : tacenta_session_unit.lifecycle.Session),
                    tacenta_session_unit.lifecycle.establish_initiator_for rc crc our bundle expected rng0 =
                        Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok s, rng1) →
                      ¬∀ (b : Aeneas.Std.Slice Aeneas.Std.U8) (s' : tacenta_session_unit.lifecycle.Session),
                          tacenta_session_unit.lifecycle.Session.import b =
                              Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok s') →
                            Tacenta.UnitLifecycleDecryptRunBounds.CounterHeadroom s'
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleImportBudget.acceptance_does_not_give_headroom

/--
info: def Tacenta.UnitLifecycleImportBudget.roomCheck : tacenta_session_unit.lifecycle.Session → ℕ → Bool :=
fun s k =>
  (decide (↑s.triple.classical.events + k + 1 < Aeneas.Std.U32.max) &&
        decide (↑s.triple.post_quantum.epoch + k + 1 < Aeneas.Std.U64.max) &&
      (↑s.triple.post_quantum.chains).all fun p =>
        (match p.2.send with
          | some ch => decide (↑ch.n + 1001 * k < Aeneas.Std.U64.max)
          | none => true) &&
          match p.2.receive with
          | some ch => decide (↑ch.n + 1001 * k < Aeneas.Std.U64.max)
          | none => true) &&
    decide (↑(Tacenta.SessionUnitBraidT1.State.epoch_val s.braid.state) + k + 1 < Aeneas.Std.U64.max)
-/
#guard_msgs in
#print Tacenta.UnitLifecycleImportBudget.roomCheck

/--
info: def Tacenta.UnitLifecycleImportBudget.withClock : tacenta_session_unit.lifecycle.Session →
  Aeneas.Std.U32 → tacenta_session_unit.lifecycle.Session :=
fun s c =>
  {
    triple :=
      have __src := s.triple;
      {
        classical :=
          have __src := s.triple.classical;
          { dhs_pub := __src.dhs_pub, dhr_pub := __src.dhr_pub, rk := __src.rk, cks := __src.cks, ckr := __src.ckr,
            ns := __src.ns, nr := __src.nr, pn := __src.pn, skipped := __src.skipped, events := c,
            labels := __src.labels },
        post_quantum := __src.post_quantum },
    braid := s.braid, ratchet_private := s.ratchet_private, identity_ad := s.identity_ad,
    our_identity_public := s.our_identity_public, peer_identity_public := s.peer_identity_public,
    pending_initial := s.pending_initial, established_ephemeral := s.established_ephemeral }
-/
#guard_msgs in
#print Tacenta.UnitLifecycleImportBudget.withClock

/--
info: def Tacenta.UnitLifecycleImportBudget.exhaustSend : Aeneas.Std.U64 × tacenta_session_unit.tacenta_spqr.Chains →
  Aeneas.Std.U64 × tacenta_session_unit.tacenta_spqr.Chains :=
fun q =>
  (q.1,
    have __src := q.2;
    { send := Option.map (fun ch => { ck := ch.ck, n := Aeneas.Std.core.num.U64.MAX }) q.2.send,
      receive := __src.receive })
-/
#guard_msgs in
#print Tacenta.UnitLifecycleImportBudget.exhaustSend

/--
info: def Tacenta.UnitLifecycleImportBudget.withExhaustedSend : tacenta_session_unit.lifecycle.Session →
  tacenta_session_unit.lifecycle.Session :=
fun s =>
  {
    triple :=
      have __src := s.triple;
      { classical := __src.classical,
        post_quantum :=
          have __src := s.triple.post_quantum;
          { rk := __src.rk, epoch := __src.epoch,
            chains :=
              ⟨List.map Tacenta.UnitLifecycleImportBudget.exhaustSend ↑s.triple.post_quantum.chains,
                (⋯ :
                  (List.map Tacenta.UnitLifecycleImportBudget.exhaustSend ↑s.triple.post_quantum.chains).length ≤
                    Aeneas.Std.Usize.max)⟩,
            skipped := __src.skipped, direction := __src.direction } },
    braid := s.braid, ratchet_private := s.ratchet_private, identity_ad := s.identity_ad,
    our_identity_public := s.our_identity_public, peer_identity_public := s.peer_identity_public,
    pending_initial := s.pending_initial, established_ephemeral := s.established_ephemeral }
-/
#guard_msgs in
#print Tacenta.UnitLifecycleImportBudget.withExhaustedSend
