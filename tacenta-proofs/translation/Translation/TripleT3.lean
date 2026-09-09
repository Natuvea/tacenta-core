import Translation.TacentaTriple
import Translation.TripleT1
import Model.Triple

/-!
# T3 for the Triple Ratchet: the translated composition refines the model

`TripleT1.lean` proved this crate's translated Rust cannot panic. This file
goes further: the translated composition computes what `Model.Triple`
computes, not merely that it returns.

## The opaque boundary is bigger than one KDF call, and why

One might expect the two inner ratchets' own refinement theorems
(`Tacenta.T3.send_refines`/`receive_refines` and
`Tacenta.SpqrT3.send_refines`/`receive_refines`) to be imported and composed
directly, the way `TripleT1.lean` composes their *totality* facts. They
cannot be, for a reason worth recording: `import Translation.TacentaTriple`
together with
`import Translation.T3` (or `Translation.SpqrT3`) fails outright --
Charon translates `tacenta-triple` as a self-contained unit and re-emits a
same-named instance (`instDiscriminantRatchetErrorIsize`,
`instDiscriminantSpqrErrorIsize`) that collides with the inner crates' own
standalone translations. It goes deeper than the name clash: inside
`TacentaTriple.lean`, `tacenta_ratchet.State` and `tacenta_spqr.State` are
each declared as a **bare opaque axiom** (`axiom ... : Type`, no fields),
because Charon translating `tacenta-triple` alone has no visibility across
the crate boundary into either inner crate's real struct. In
`Translation.TacentaRatchet`/`Translation.TacentaSpqr` (each crate's own
standalone translation, which `T3.lean`/`SpqrT3.lean` are built against),
the same names are concrete structures. They are different declarations that
happen to share a name, and there is no way to write a field-by-field
`StateR`-style relation against the opaque one -- there is nothing to
project.

So this file cannot cite `T3.lean`'s/`SpqrT3.lean`'s own proofs, even though
both already establish exactly the fact needed. What it does instead:
`RatchetAgreesFor`/`SpqrAgreesFor` below each bundle one existential
abstraction function (`tacenta_ratchet.State`/`tacenta_spqr.State` to
`Model.State.State`/`Model.SparseRatchet.State`) under which every function
this crate actually calls (`clone`, the two initialisers, `send`, `receive`,
and the small accessors `TripleT1.lean` already treats as this state's public
interface) agrees with the corresponding model function -- the same bundled-
existential shape `BraidT3.lean`'s `KemAgreesFor` already uses for its KEM
boundary, for a different reason: a KEM is inherently uninterpreted by
design, where here the inner ratchets are already fully proven, just
unreachable from this file by a toolchain limit, not by design. Naming that
difference is the point of this note: `RatchetAgreesFor`/`SpqrAgreesFor` are
not cryptographic trust assumptions the way `HmacAgrees`/`SpqrHkdfAgrees` are
-- they hold if and only if `T3.lean`'s/`SpqrT3.lean`'s own theorems hold of
the real code, which they do, proved elsewhere; this file just cannot make
Lean say so directly.

Beyond that boundary, this crate calls exactly one opaque primitive that is
genuinely its own: `hkdf_sha256`, inside the translated (non-opaque)
`split_secret` and `combine`. -/

open Aeneas Aeneas.Std Result

namespace Tacenta.TripleT3

open tacenta_triple

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
theorem TripleHkdfAgrees.total (h : TripleHkdfAgrees) : Tacenta.TripleT1.HkdfSha256Total :=
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
    Tacenta.TripleT1.ZeroizingTotal := by
  intro inst
  exact ⟨fun z => let ⟨w, hw, _⟩ := (h inst).1 z; ⟨w, hw⟩, (h inst).2⟩

-- `TripleT1.lean` registered a stepping rule for the wrapper's projection
-- whose postcondition is only that it returned. Here that is too weak, as in
-- `T3.lean`: it would introduce the unwrapped value with nothing tying it to
-- what was wrapped. Removing it locally makes the tactic stop at the
-- projection so the round trip the wrapper's rule hands back can be applied
-- by hand.
attribute [-step] Tacenta.TripleT1.zeroizing_deref_step

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

Neither inner state can be related to its model field by field from here --
see the file header. What each bundle below states is exactly what
`Translation/T3.lean`'s `send_refines`/`receive_refines` and
`Translation/SpqrT3.lean`'s `send_refines`/`receive_refines` already prove
about the real code, transported through an assumed abstraction function
rather than derived from those proofs directly. Same shape as
`BraidT3.lean`'s `KemAgreesFor`, for the reason given above. -/

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
assumed abstraction `α`. Covers exactly what this crate calls: `clone`, the
two initialisers, the three small accessors `TripleT1.lean` already treats as
this state's public interface, and `send`/`receive` -- the last two carrying
the same preconditions `T3.lean`'s own `send_refines`/`receive_refines` do,
transported through `α` rather than stated on the real state's own fields,
since there are none to state them on here. -/
def RatchetAgreesFor (α : tacenta_ratchet.State → Model.State.State) : Prop :=
  (∀ s, ∃ r, tacenta_ratchet.State.Insts.CoreCloneClone.clone s = ok r ∧ α r = α s) ∧
  (∀ s, ∃ r, tacenta_ratchet.State.sending_public s = ok r ∧ keyOf r = (α s).dhsPub) ∧
  (∀ s, ∃ r, tacenta_ratchet.State.send_count s = ok r ∧ r.val = (α s).ns) ∧
  (∀ s, ∃ r, tacenta_ratchet.State.receive_count s = ok r ∧ r.val = (α s).nr) ∧
  (∀ (ec our_pub peer_pub dh_out : Array Std.U8 32#usize) (labels : tacenta_ratchet.LabelSet),
    ∃ r, tacenta_ratchet.init_sender ec our_pub peer_pub dh_out labels = ok r ∧
      α r = Model.Ratchet.initSender (keyOf ec) (keyOf our_pub) (keyOf peer_pub) (keyOf dh_out)
        (ratchetLabelsOf labels)) ∧
  (∀ (ec our_pub : Array Std.U8 32#usize) (labels : tacenta_ratchet.LabelSet),
    ∃ r, tacenta_ratchet.init_receiver ec our_pub labels = ok r ∧
      α r = Model.Ratchet.initReceiver (keyOf ec) (keyOf our_pub) (ratchetLabelsOf labels)) ∧
  (∀ s, ∃ r, tacenta_ratchet.send s = ok r ∧
    (∀ hdr mk, r.1 = core.result.Result.Ok (hdr, mk) →
      ∃ m' mh, Model.Ratchet.send (α s) = some (m', mh, keyOf mk) ∧
        α r.2 = m' ∧ RatchetHeaderR hdr mh) ∧
    (r.1 = core.result.Result.Err tacenta_ratchet.RatchetError.NoSendingChain →
      Model.Ratchet.send (α s) = none)) ∧
  (∀ (s : tacenta_ratchet.State) (hdr : tacenta_ratchet.Header) (mh : Model.State.Header),
    RatchetHeaderR hdr mh →
    ∀ (dh_out_recv dh_out_send new_dhs_pub : Array Std.U8 32#usize),
    ((α s).skipped.filter (fun x => x.1 == mh.dh && x.2.1 == mh.n)).length ≤ 1 →
    max (α s).skipped.length Model.State.maxSkippedStore + Std.U32.max ≤ Usize.max →
    (α s).events < Std.U32.max →
    ∃ r, tacenta_ratchet.receive s hdr dh_out_recv dh_out_send new_dhs_pub = ok r ∧
      ∀ mk, r.1 = core.result.Result.Ok mk →
        ∃ m', Model.Ratchet.receive (α s) mh (keyOf dh_out_recv) (keyOf dh_out_send)
              (keyOf new_dhs_pub) = some (m', keyOf mk) ∧ α r.2 = m')

def RatchetAgrees : Prop := ∃ α, RatchetAgreesFor α

/-- Bundled agreement for the sparse ratchet's calling surface, through an
assumed abstraction `β`. Covers `clone`, the two initialisers, `epoch`, and
`send`/`receive` -- the last two carrying the same preconditions
`SpqrT3.lean`'s own `send_refines`/`receive_refines` do (including
`hcounter` scoped to the real state's own chain table, exactly as
`SpqrT3.lean` states it). -/
def SpqrAgreesFor (β : tacenta_spqr.State → Model.SparseRatchet.State) : Prop :=
  (∀ s, ∃ r, tacenta_spqr.State.Insts.CoreCloneClone.clone s = ok r ∧ β r = β s) ∧
  (∀ s, ∃ r, tacenta_spqr.State.epoch s = ok r ∧ r.val = (β s).epoch) ∧
  (∀ sk : Slice Std.U8, ∃ r, tacenta_spqr.State.init_alice sk = ok r ∧
    β r = Model.SparseRatchet.initAlice (sliceOf sk)) ∧
  (∀ sk : Slice Std.U8, ∃ r, tacenta_spqr.State.init_bob sk = ok r ∧
    β r = Model.SparseRatchet.initBob (sliceOf sk)) ∧
  (∀ (s : tacenta_spqr.State) (e : Std.U64) (out : Option tacenta_spqr.Output),
    (β s).epoch < Std.U64.max →
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
  (∀ (s : tacenta_spqr.State) (receiving_epoch : Std.U64) (out : Option tacenta_spqr.Output)
      (n : Std.U64),
    (β s).epoch < Std.U64.max →
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
clause is unconditional (`SpqrAgreesFor`, backed by `SpqrT3.lean`'s own
`hcounter`-guarded `send_refines`), but the classical ratchet's is not:
`T3.lean`'s own `send_refines` proves the model-failure correspondence only
for `RatchetError.NoSendingChain`, not for `ChainExhausted` (the real `u32`
send counter wrapping), because `Model.Ratchet.send` counts in `Nat` and so
has no failure mode to correspond to that overflow. `RatchetAgreesFor`
states exactly that -- `NoSendingChain` only -- rather than an unrestricted
`∀ e`.
The theorem's stated postcondition below is scoped to match: it only claims
the failure-implies-`none` correspondence when the reported error is either
a post-quantum one or specifically `Classical NoSendingChain`, and proves
nothing at all about a `Classical ChainExhausted` failure -- the same
finite-width boundary `T3.lean` already excludes, one layer up rather than
newly introduced here. -/

theorem send_refines {α : tacenta_ratchet.State → Model.State.State}
    {β : tacenta_spqr.State → Model.SparseRatchet.State}
    (hra : RatchetAgreesFor α) (hsa : SpqrAgreesFor β) (hthk : TripleHkdfAgrees)
    (hz : Tacenta.TripleT1.ZeroizeTotal)
    {s : State} {m : Model.Triple.State} (hrel : StateRefines α β s m)
    (sending_epoch : Std.U64) (output : Option tacenta_spqr.Output)
    (hroom : m.postQuantum.chains.length + 1 < Usize.max)
    (hcb : ∀ p ∈ m.postQuantum.chains, p.1 + Model.SparseRatchet.epochsKept ≤ Std.U64.max)
    (hsb : ∀ sk ∈ m.postQuantum.skipped, sk.1 + Model.SparseRatchet.epochsKept ≤ Std.U64.max)
    (hnewb : ∀ o : tacenta_spqr.Output, output = some o →
      o.key_epoch.val + Model.SparseRatchet.epochsKept ≤ Std.U64.max)
    (hepoch : m.postQuantum.epoch < Std.U64.max)
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
`Translation/T3.lean`'s own `receive_refines` for the classical ratchet: that
theorem states no failure-branch fact at all, so there is nothing to compose
a triple-level failure claim from -- this is not a new weakening, it is the
same limitation the leaf crate's own claim already carries. -/
theorem receive_refines {α : tacenta_ratchet.State → Model.State.State}
    {β : tacenta_spqr.State → Model.SparseRatchet.State}
    (hra : RatchetAgreesFor α) (hsa : SpqrAgreesFor β) (hthk : TripleHkdfAgrees)
    (hz : Tacenta.TripleT1.ZeroizeTotal)
    {s : State} {m : Model.Triple.State} (hrel : StateRefines α β s m)
    (header : Header) (mh : Model.State.Header) (hheader : RatchetHeaderR header.dr mh)
    (dh_out_recv dh_out_send new_dhs_pub : Array Std.U8 32#usize)
    (output : Option tacenta_spqr.Output)
    (hone : (m.classical.skipped.filter (fun x => x.1 == mh.dh && x.2.1 == mh.n)).length ≤ 1)
    (hs : max m.classical.skipped.length Model.State.maxSkippedStore + Std.U32.max ≤ Usize.max)
    (hevents : m.classical.events < Std.U32.max)
    (hepoch : m.postQuantum.epoch < Std.U64.max)
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

end Tacenta.TripleT3
