import Translation.TacentaTriple

/-!
# T1 for the Triple Ratchet: totality on the composed session send/receive path

`tacenta-triple` is the crate the product put on the session's actual send
and receive path, composing the classical Double Ratchet (`tacenta-ratchet`)
and the sparse post-quantum ratchet (`tacenta-spqr`) so that breaking either
alone yields nothing. This file is where the composition itself gets a
theorem: `T1.lean` proves the classical ratchet total, `SpqrT1.lean` proves
the sparse ratchet total, and this file puts them together over the
translated `tacenta-triple` (see `run-aeneas.sh` and `LIMITATIONS.md`) -- a
proof that `State.send` and `State.receive`, the two functions the session
actually calls, cannot panic.

## Why this crate is smaller than it looks

`tacenta-triple` adds no protocol logic of its own beyond splitting a shared
secret in two and combining two message keys back into one, both single HKDF
calls. Its own `State` is just a pair, `{ classical, post_quantum }`, and
`send`/`receive` are almost entirely a matter of calling into each ratchet in
turn and matching on whether it succeeded. Both `tacenta_ratchet.State` and
`tacenta_spqr.State` are opaque here (this crate only sees their public
calling surface, exactly as `T1.lean` and `SpqrT1.lean` translate them), so
every operation on them is an assumption below, not a proof obligation this
file discharges itself -- that work already happened in the other two files,
against the *real* definitions of those types. What is proved here is that the
composition built on top of those assumptions cannot panic.
-/

open Aeneas Aeneas.Std Result

namespace Tacenta.TripleT1

open tacenta_triple

/-! ## The opaque surface: two ratchets' calling surfaces, and one KDF call

Every operation this crate calls on `tacenta_ratchet.State` or
`tacenta_spqr.State` is opaque here, and every one gets its own totality
assumption, per this project's established rule: one axiom per crate that
touches an unmodelled operation, not one per name. None of these is the same
proposition as `T1.lean`'s or `SpqrT1.lean`'s own theorems about the *real*
definitions of these types -- this crate only sees the calling surface,
exactly as `tacenta-triple`'s own source does. -/

def RatchetStateCloneTotal : Prop :=
  ∀ (s : tacenta_ratchet.State),
    ∃ r, tacenta_ratchet.State.Insts.CoreCloneClone.clone s = ok r

def RatchetSendingPublicTotal : Prop :=
  ∀ (s : tacenta_ratchet.State), ∃ r, tacenta_ratchet.State.sending_public s = ok r

def RatchetSendCountTotal : Prop :=
  ∀ (s : tacenta_ratchet.State), ∃ r, tacenta_ratchet.State.send_count s = ok r

def RatchetReceiveCountTotal : Prop :=
  ∀ (s : tacenta_ratchet.State), ∃ r, tacenta_ratchet.State.receive_count s = ok r

def RatchetInitSenderTotal : Prop :=
  ∀ (ec our_pub peer_pub dh_out : Array U8 32#usize) (labels : tacenta_ratchet.LabelSet),
    ∃ r, tacenta_ratchet.init_sender ec our_pub peer_pub dh_out labels = ok r

def RatchetInitReceiverTotal : Prop :=
  ∀ (ec our_pub : Array U8 32#usize) (labels : tacenta_ratchet.LabelSet),
    ∃ r, tacenta_ratchet.init_receiver ec our_pub labels = ok r

/-- The *outer* `Result` is what this states is total; the *inner*
`core.result.Result _ RatchetError` it returns is a real value the source
already branches on, `Ok` or `Err` both handled. -/
def RatchetSendTotal : Prop :=
  ∀ (s : tacenta_ratchet.State), ∃ r, tacenta_ratchet.send s = ok r

def RatchetReceiveTotal : Prop :=
  ∀ (s : tacenta_ratchet.State) (hdr : tacenta_ratchet.Header)
    (a b c : Array U8 32#usize), ∃ r, tacenta_ratchet.receive s hdr a b c = ok r

def RatchetHeaderEqTotal : Prop :=
  ∀ (a b : tacenta_ratchet.Header),
    ∃ r, tacenta_ratchet.Header.Insts.CoreCmpPartialEqHeader.eq a b = ok r

def RatchetErrorEqTotal : Prop :=
  ∀ (a b : tacenta_ratchet.RatchetError),
    ∃ r, tacenta_ratchet.RatchetError.Insts.CoreCmpPartialEqRatchetError.eq a b = ok r

def SpqrErrorEqTotal : Prop :=
  ∀ (a b : tacenta_spqr.SpqrError),
    ∃ r, tacenta_spqr.SpqrError.Insts.CoreCmpPartialEqSpqrError.eq a b = ok r

def SpqrStateCloneTotal : Prop :=
  ∀ (s : tacenta_spqr.State), ∃ r, tacenta_spqr.State.Insts.CoreCloneClone.clone s = ok r

def SpqrInitAliceTotal : Prop :=
  ∀ (s : Slice U8), ∃ r, tacenta_spqr.State.init_alice s = ok r

def SpqrInitBobTotal : Prop :=
  ∀ (s : Slice U8), ∃ r, tacenta_spqr.State.init_bob s = ok r

def SpqrEpochTotal : Prop :=
  ∀ (s : tacenta_spqr.State), ∃ r, tacenta_spqr.State.epoch s = ok r

def SpqrSendTotal : Prop :=
  ∀ (s : tacenta_spqr.State) (epoch : U64) (out : Option tacenta_spqr.Output),
    ∃ r, tacenta_spqr.State.send s epoch out = ok r

def SpqrReceiveTotal : Prop :=
  ∀ (s : tacenta_spqr.State) (epoch : U64) (out : Option tacenta_spqr.Output) (n : U64),
    ∃ r, tacenta_spqr.State.receive s epoch out n = ok r

/-- This crate's own copy of the opaque KDF and `Zeroize` axioms, distinct
constants from `T1.lean`'s and `SpqrT1.lean`'s copies of the same operations.
The HKDF premise is RFC 5869's output bound of 8160 bytes, the bound the
crate's own `expect` enforces, so the hypothesis is stated exactly where the
real operation returns (`T1.HkdfTotal` says why); this crate asks for 32 or
64 bytes. -/
def HkdfSha256Total : Prop :=
  ∀ (N : Usize) (a b c : Slice U8), N.val ≤ 8160 →
    ∃ r, tacenta_kdf.hkdf_sha256 N a b c = ok r

def ZeroizeTotal : Prop :=
  ∀ (a : Array U8 32#usize),
    ∃ r, Array.Insts.ZeroizeZeroize.zeroize
      (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes) a = ok r

/-- The `zeroize` wrapper itself, this crate's own copy of `T1.lean`'s
`ZeroizingTotal`: `split_secret` now passes its sixty-four-byte expansion
through `Zeroizing` on the way to the two ratchets' secrets (CR-15), and the
wrapper's constructor and projection are both opaque here, as they are in
every crate that touches the external `zeroize` crate. In the crate they are
a newtype constructor and its projection, neither of which can fail. Stated
at the one width this crate wraps at, so the assumption is no wider than the
use, and a distinct constant from the ratchet's and the sparse ratchet's
copies, per the counting rule below. -/
def ZeroizingTotal : Prop :=
  ∀ inst : zeroize.Zeroize (Array U8 64#usize),
    (∀ z, ∃ r, zeroize.Zeroizing.new inst z = ok r) ∧
    (∀ z, ∃ r, zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref inst z = ok r)

@[step]
theorem zeroizing_new_step (hz : ZeroizingTotal)
    (inst : zeroize.Zeroize (Array U8 64#usize)) (z : Array U8 64#usize) :
    zeroize.Zeroizing.new inst z ⦃ fun _ => True ⦄ := by
  obtain ⟨r, hr⟩ := (hz inst).1 z; simp [hr]

@[step]
theorem zeroizing_deref_step (hz : ZeroizingTotal)
    (inst : zeroize.Zeroize (Array U8 64#usize))
    (z : zeroize.Zeroizing (Array U8 64#usize)) :
    zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref inst z ⦃ fun _ => True ⦄ := by
  obtain ⟨r, hr⟩ := (hz inst).2 z; simp [hr]

/-! ## This crate's own types: `Header`, `TripleError` -/

theorem Header.clone_no_panic (self : Header) :
    Header.Insts.CoreCloneClone.clone self ⦃ fun _ => True ⦄ := by
  unfold Header.Insts.CoreCloneClone.clone; simp

theorem Header.eq_no_panic (hreq : RatchetHeaderEqTotal) (self other : Header) :
    Header.Insts.CoreCmpPartialEqHeader.eq self other ⦃ fun _ => True ⦄ := by
  unfold Header.Insts.CoreCmpPartialEqHeader.eq
  split
  · split
    · obtain ⟨r, hr⟩ := hreq self.dr other.dr
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

/-- The two "impossible" `fail panic` branches (`Classical` matched against
`PostQuantum` and back) are exactly that: the discriminant check just above
each already ruled out a cross-constructor match, so case-splitting on both
`self` and `other` up front closes every branch before either `fail` is ever
reached. -/
theorem TripleError.eq_no_panic (hrateq : RatchetErrorEqTotal) (hspqreq : SpqrErrorEqTotal)
    (self other : TripleError) :
    TripleError.Insts.CoreCmpPartialEqTripleError.eq self other ⦃ fun _ => True ⦄ := by
  unfold TripleError.Insts.CoreCmpPartialEqTripleError.eq
  simp only [TripleError.read_discriminant]
  rcases self with a | a <;> rcases other with b | b <;> simp
  · obtain ⟨r, hr⟩ := hrateq a b; simp [hr]
  · obtain ⟨r, hr⟩ := hspqreq a b; simp [hr]

/-! ## The two module-level functions: `split_secret`, `combine` -/

theorem split_secret_no_panic (hkdf : HkdfSha256Total) (hzw : ZeroizingTotal) (sk : Slice U8) :
    split_secret sk ⦃ fun _ => True ⦄ := by
  unfold split_secret
  step*
  all_goals (try (obtain ⟨r, hr⟩ := hkdf 64#usize ‹_› sk SPLIT_INFO (by scalar_tac); simp only [hr]))
  all_goals (try step*)
  all_goals (try simp_all [Slice.length])

theorem combine_no_panic (hkdf : HkdfSha256Total) (mk_classical mk_pq : Array U8 32#usize) :
    combine mk_classical mk_pq ⦃ fun _ => True ⦄ := by
  unfold combine
  step*
  obtain ⟨r, hr⟩ := hkdf 32#usize s s1 COMBINE_INFO (by scalar_tac)
  simp [hr]

/-! ## `State`'s clone and small accessors

Both `tacenta_ratchet.State` and `tacenta_spqr.State` are opaque here, so
unlike `Auth.clone_no_panic` in `SpqrT1.lean` or `BraidT1.lean` (concretely
defined, provably identity), cloning either is only known *total*, not
value-preserving. Nothing below needs value-preservation: every assumption
about an opaque state is universally quantified over the whole type, so it
applies to whatever a clone returns exactly as it applies to `self` itself. -/

theorem State.clone_no_panic (hrc : RatchetStateCloneTotal) (hsc : SpqrStateCloneTotal)
    (self : State) :
    State.Insts.CoreCloneClone.clone self ⦃ fun _ => True ⦄ := by
  unfold State.Insts.CoreCloneClone.clone
  obtain ⟨s, hs⟩ := hrc self.classical
  simp only [hs]
  obtain ⟨s1, hs1⟩ := hsc self.post_quantum
  simp [hs1]

theorem State.sending_public_no_panic (h : RatchetSendingPublicTotal) (self : State) :
    State.sending_public self ⦃ fun _ => True ⦄ := by
  unfold State.sending_public
  obtain ⟨r, hr⟩ := h self.classical
  simp [hr]

theorem State.send_count_no_panic (h : RatchetSendCountTotal) (self : State) :
    State.send_count self ⦃ fun _ => True ⦄ := by
  unfold State.send_count
  obtain ⟨r, hr⟩ := h self.classical
  simp [hr]

theorem State.receive_count_no_panic (h : RatchetReceiveCountTotal) (self : State) :
    State.receive_count self ⦃ fun _ => True ⦄ := by
  unfold State.receive_count
  obtain ⟨r, hr⟩ := h self.classical
  simp [hr]

theorem State.epoch_no_panic (h : SpqrEpochTotal) (self : State) :
    State.epoch self ⦃ fun _ => True ⦄ := by
  unfold State.epoch
  obtain ⟨r, hr⟩ := h self.post_quantum
  simp [hr]

/-! ## `State.init_sender`, `State.init_receiver` -/

theorem State.init_sender_no_panic (hss : HkdfSha256Total) (hzw : ZeroizingTotal)
    (hris : RatchetInitSenderTotal) (hsia : SpqrInitAliceTotal) (hz : ZeroizeTotal) (sk : Slice U8)
    (our_pub peer_pub dh_out : Array U8 32#usize) (labels : tacenta_ratchet.LabelSet) :
    State.init_sender sk our_pub peer_pub dh_out labels ⦃ fun _ => True ⦄ := by
  unfold State.init_sender
  step with split_secret_no_panic hss hzw sk
  all_goals (try (obtain ⟨s, hs⟩ := hris ec our_pub peer_pub dh_out labels; simp only [hs]))
  all_goals (try step*)
  all_goals (try (obtain ⟨s2, hs2⟩ := hsia s1; simp only [hs2]))
  all_goals (try step*)
  all_goals (try (obtain ⟨r, hr⟩ := hz ec; simp only [hr]))
  all_goals (try step*)
  all_goals (try (obtain ⟨r1, hr1⟩ := hz pq; simp only [hr1]))
  all_goals (try step*)

theorem State.init_receiver_no_panic (hss : HkdfSha256Total) (hzw : ZeroizingTotal)
    (hrir : RatchetInitReceiverTotal) (hsib : SpqrInitBobTotal) (hz : ZeroizeTotal) (sk : Slice U8)
    (our_pub : Array U8 32#usize)
    (labels : tacenta_ratchet.LabelSet) :
    State.init_receiver sk our_pub labels ⦃ fun _ => True ⦄ := by
  unfold State.init_receiver
  step with split_secret_no_panic hss hzw sk
  all_goals (try (obtain ⟨s, hs⟩ := hrir ec our_pub labels; simp only [hs]))
  all_goals (try step*)
  all_goals (try (obtain ⟨s2, hs2⟩ := hsib s1; simp only [hs2]))
  all_goals (try step*)
  all_goals (try (obtain ⟨r, hr⟩ := hz ec; simp only [hr]))
  all_goals (try step*)
  all_goals (try (obtain ⟨r1, hr1⟩ := hz pq; simp only [hr1]))
  all_goals (try step*)

/-! ## `State.send`, `State.receive`, `State.commit`

The composed session send/receive path itself: clone the current state,
call into each ratchet in turn, and match on whether it succeeded. Both
`?`-style branches (`Err` from either ratchet) are handled explicitly in the
source, so nothing here needs to reason about which branch is taken -- only
that every operation along the way, in every branch, is total. -/

theorem State.send_no_panic (hrc : RatchetStateCloneTotal) (hsc : SpqrStateCloneTotal)
    (hrs : RatchetSendTotal) (hss : SpqrSendTotal) (hkdf : HkdfSha256Total) (hz : ZeroizeTotal)
    (self : State) (sending_epoch : U64) (output : Option tacenta_spqr.Output) :
    State.send self sending_epoch output ⦃ fun _ => True ⦄ := by
  unfold State.send
  step with State.clone_no_panic hrc hsc
  all_goals (try (obtain ⟨r, hr⟩ := hrs candidate.classical; simp only [hr]))
  all_goals (try step*)
  all_goals (try (rcases r with v | e))
  all_goals (try step*)
  all_goals (try (obtain ⟨dr, mk_ec⟩ := v))
  all_goals (try (obtain ⟨r1, hr1⟩ := hss candidate.post_quantum sending_epoch output; simp only [hr1]))
  all_goals (try step*)
  all_goals (try (rcases r1 with v1 | e1))
  all_goals (try step*)
  all_goals (try (obtain ⟨pq_n, mk_pq⟩ := v1))
  all_goals (try (step with combine_no_panic hkdf))
  all_goals (try (obtain ⟨r2, hr2⟩ := hz mk_ec; simp only [hr2]))
  all_goals (try step*)
  all_goals (try (obtain ⟨r3, hr3⟩ := hz mk_pq; simp only [hr3]))
  all_goals (try step*)

theorem State.receive_no_panic (hrc : RatchetStateCloneTotal) (hsc : SpqrStateCloneTotal)
    (hrr : RatchetReceiveTotal) (hsr : SpqrReceiveTotal) (hkdf : HkdfSha256Total) (hz : ZeroizeTotal)
    (self : State) (header : Header)
    (dh_out_recv dh_out_send new_dhs_pub : Array U8 32#usize)
    (output : Option tacenta_spqr.Output) :
    State.receive self header dh_out_recv dh_out_send new_dhs_pub output ⦃ fun _ => True ⦄ := by
  unfold State.receive
  step with State.clone_no_panic hrc hsc
  all_goals (try (obtain ⟨r, hr⟩ := hrr candidate.classical header.dr dh_out_recv dh_out_send new_dhs_pub; simp only [hr]))
  all_goals (try step*)
  all_goals (try (rcases r with v | e))
  all_goals (try step*)
  all_goals (try (obtain ⟨r1, hr1⟩ := hsr candidate.post_quantum header.epoch output header.pq_n; simp only [hr1]))
  all_goals (try step*)
  all_goals (try (rcases r1 with v1 | e1))
  all_goals (try step*)
  all_goals (try (step with combine_no_panic hkdf))
  all_goals (try (obtain ⟨r2, hr2⟩ := hz v; simp only [hr2]))
  all_goals (try step*)
  all_goals (try (obtain ⟨r3, hr3⟩ := hz v1; simp only [hr3]))
  all_goals (try step*)

theorem State.commit_no_panic (self next : State) : State.commit self next ⦃ fun _ => True ⦄ := by
  unfold State.commit; simp

/-! ## What this covers, and what it still does not

**Proved:** `split_secret`, `combine`, `Header`'s and `TripleError`'s
clone and equality, `State`'s clone and the four accessors that read a
counter or a public key off the state itself (`sending_public`,
`send_count`, `receive_count`, `epoch`) -- not the three that ask an inner
ratchet about its skipped-key store or its chain table, which are in the
not-proved list below -- `State.init_sender`,
`State.init_receiver`, and, the actual point of this file, `State.send`,
`State.receive` and `State.commit`. No precondition beyond totality is
needed for any of them: unlike `T1.lean`'s ratchet or `SpqrT1.lean`'s sparse
ratchet, this crate carries no room, counter, or length bound of its own to
state, because it never touches a vector, a chain, or a counter directly --
it only calls into the two ratchets that do, through their public calling
surface, and matches on whether each call succeeded.

**Not proved, so not every function the crate exposes.** Seven public
functions have no theorem here: `State.classical_skipped_len`,
`State.post_quantum_skipped_len`, `State.post_quantum_receive_count`,
`State.evict_oldest_classical`, `State.evict_oldest_post_quantum`,
`State.to_bytes` and `State.from_bytes`. The session calls all seven -- the
first five from the eviction loop in
`tacenta-core/src/sessions/lifecycle.rs`, which reads the first three to size
an eviction and then calls the two that make the room, and the last two when
it persists and restores a session. Each wraps an inner-ratchet operation
that is opaque here and that none of the constants above assumes total
(`skipped_len`, `evict_oldest`, `to_bytes` and `from_bytes` on
`tacenta_ratchet.State`, and `skipped_len`, `receive_count`, `evict_oldest`,
`to_bytes` and `from_bytes` on `tacenta_spqr.State`), and
`from_bytes` also parses its own length-prefixed framing. A theorem for each
would need nine more totality assumptions of the same shape, one per opaque
inner call, plus the `zeroize` wrapper at the `Vec` width `to_bytes` returns,
and for `from_bytes` a proof over the framing. Until then what this file
covers is the send, receive and commit path, the two constructors, the
clones, the equalities and the four accessors named above.

**This is the crate the session's send and receive path actually runs
through.** `T1.lean`'s `receive_no_panic` and
`SpqrT1.lean`'s `send_no_panic`/`receive_no_panic` were both true and both
insufficient on their own: neither says anything about what happens when the
two are composed, and the composition is what ships. This file is that
composition's own proof, not a restatement of the other two.

## Twenty assumptions, all about a calling surface rather than a definition

Seventeen of the twenty constants above are totality assumptions about
`tacenta_ratchet.State` or `tacenta_spqr.State` treated as **opaque** -- this
crate never sees their real definitions, only the public functions `T1.lean`
and `SpqrT1.lean` already proved total against those real definitions. That
is deliberate, not a gap: it mirrors exactly how `tacenta-triple`'s own Rust
source is written, calling the other two ratchets only through their public
API, and it is why none of these seventeen constants is the same proposition
as any theorem in `T1.lean` or `SpqrT1.lean` even where the names echo each
other (`RatchetSendTotal` here is not `send_no_panic` there -- one assumes
totality of a call across a crate boundary, the other proves it from the
translated body). `HkdfSha256Total`, `ZeroizeTotal` and `ZeroizingTotal`
round out the count of twenty, this crate's own copies of the same three
axioms every other translated crate that touches a KDF, a zeroize call or the
`zeroize` wrapper has had to declare separately, per the counting trap
`SpqrT1.lean` describes: one axiom per crate that touches an unmodelled
operation, not one per name. The last is new with `split_secret` wiping its
sixty-four-byte expansion on the way out (CR-15).

## What is still open

`tacenta-triple`'s own T1 says nothing about `Session::encrypt` and
`Session::decrypt` themselves: they live in `tacenta-core/src/sessions`, the
product code that calls into this crate, and that layer is not translated or
proved in its own right. Whether it should be is a separate question this
file does not answer. -/

end Tacenta.TripleT1
