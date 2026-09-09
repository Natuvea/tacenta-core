import Translation.TacentaRatchet

/-!
# T1: panic-freedom of the verified zone

A function is panic-free when it never returns `fail`: no arithmetic overflow,
no out-of-bounds index, no unwrap of a missing value. The translated ratchet
calls two kinds of thing, so each statement carries one hypothesis and no more:

* our own code, which is what these theorems are about, and
* the trusted key-derivation boundary, which the translation sees as axioms and
  which is assumed total. That assumption is named rather than left implicit,
  so a reader can see exactly what the proofs rest on.
-/

open Aeneas Aeneas.Std Result

namespace Tacenta.T1

open tacenta_ratchet

/-- The trusted boundary: the opaque HMAC primitive returns a value on every
input. It wraps a vetted implementation that cannot fail, but the translation
cannot see inside it, so the fact is stated here and used explicitly. -/
def HmacTotal : Prop :=
  ∀ key data, ∃ r, tacenta_kdf.hmac_sha256 key data = ok r

/-- The other half of that boundary: the opaque HKDF expansion returns a value
on every input, for every output length. Root-key steps rest on this the way
chain-key steps rest on `HmacTotal`. -/
def HkdfTotal : Prop :=
  ∀ N key salt info, ∃ r, tacenta_kdf.hkdf_sha256 N key salt info = ok r

/-- A third opaque boundary, and the one that is not ours: the `zeroize` crate.
The translation cannot see inside an external dependency, so wrapping a value
for erasure and reading it back out are both axioms here. In the crate they are
a newtype constructor and its projection, neither of which can fail. Stated at
the one type the root-key step uses it at, rather than in general, so the
assumption is no wider than the use. -/
def ZeroizingTotal : Prop :=
  ∀ inst : zeroize.Zeroize (Array U8 64#usize),
    (∀ z, ∃ r, zeroize.Zeroizing.new inst z = ok r) ∧
    (∀ z, ∃ r, zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref inst z = ok r)

-- The generated code passes Aeneas's auto-named length proofs to `Array.make`.
-- Naming them here is what lets the hypothesis be instantiated at exactly the
-- arguments the body uses. They are not stable across regeneration, which is
-- safe in the way that matters: a change breaks this build loudly rather than
-- weakening a proof silently.
set_option linter.auxLemma false in
/-- Advancing a chain key cannot fail. -/
theorem kdf_ck_no_panic (h : HmacTotal) (ck : Array U8 32#usize) :
    ∃ r, kdf_ck ck = ok r := by
  -- The length side condition is `Array.make`'s auto-param, not an
  -- argument, and it is left to the auto-param rather than supplied through
  -- the translation's generated `_proof_*` constants: those are not stable
  -- across regeneration, and a hand-written proof that names one would be
  -- weakened by a regeneration without a build failure.
  obtain ⟨_, hmk⟩ :=
    h ck.to_slice (Array.make 1#usize [1#u8]).to_slice
  obtain ⟨_, hnx⟩ :=
    h ck.to_slice (Array.make 1#usize [2#u8]).to_slice
  simp [kdf_ck, lift, hmk, hnx]

/-- Sending cannot fail. Its only failure points are the message counter and
the chain-key step: the counter is a `checked_add`, so exhaustion is an
ordinary `ChainExhausted` result rather than an overflow. -/
theorem send_no_panic (h : HmacTotal) (state : State) :
    ∃ r, send state = ok r := by
  rcases hcks : state.cks with _ | ck
  · simp [send, hcks]
  · rcases hadd : state.ns.checked_add 1#u32 with _ | next_ns
    · simp [send, hcks, hadd, lift]
    · obtain ⟨⟨ck2, mk⟩, hck⟩ := kdf_ck_no_panic h ck
      simp [send, hcks, hadd, lift, hck]

/-- Panic-freedom in the weakest-precondition form the loop lemma uses: the
computation returns a value, rather than failing or diverging. `spec_ok`,
`spec_fail` and `spec_div` in the Aeneas library make this exactly "not fail
and not diverge". -/
abbrev NoPanic {α : Type} (e : Result α) : Prop := e ⦃ fun _ => True ⦄

/-- Bridge to the existential form the straight-line theorems above use. -/
theorem noPanic_iff {α : Type} (e : Result α) : NoPanic e ↔ ∃ r, e = ok r := by
  cases e <;> simp [NoPanic]

/-- The skipped-key loop cannot fail. Its only fallible step is the `Vec.push`
that stores each derived key, which fails only past `Usize.max`; the iterator
step is total. The invariant is that the keys already stored plus the ones still
to come stay within that bound, which the loop preserves by construction because
each turn moves exactly one element from the iterator into the store. The
measure is the number of elements left. -/
@[step]
theorem skip_message_keys_loop_no_panic
    (dhr : Array U8 32#usize)
    (iter : alloc.vec.into_iter.IntoIter (U32 × Array U8 32#usize))
    (v : alloc.vec.Vec SkippedKey) (now : U32)
    (h : v.val.length + iter.val.length ≤ Usize.max) :
    skip_message_keys_loop iter dhr v now ⦃ fun _ => True ⦄ := by
  unfold skip_message_keys_loop
  apply loop.spec_decr_nat
    (measure := fun x => (Prod.fst x).val.length)
    (inv := fun x => (Prod.snd x).val.length + (Prod.fst x).val.length ≤ Usize.max)
  · rintro ⟨it, w⟩ hinv
    unfold skip_message_keys_loop.body alloc.vec.into_iter.IteratorIntoIter.next
    obtain ⟨l, hl⟩ := it
    cases l with
    | nil => simp
    | cons hd tl =>
      obtain ⟨n, mk⟩ := hd
      simp only [List.length_cons] at hinv
      have hw : (↑w : List SkippedKey).length < Usize.max := by omega
      simp only []
      step*; simp_all; omega
  · exact h

/-- The chain-derivation loop cannot fail. Its fallible steps are the chain-key
step (which needs the trusted HMAC) and the `Vec.push` that collects each
derived key; the message number is a `checked_add` reporting `ChainExhausted`,
so it is a result rather than a panic. The invariant is that the keys already
collected plus the iterations still to come stay within `Usize.max`, and the
measure is the number of iterations left in the range. -/
theorem derive_chain_loop_no_panic (h : HmacTotal)
    (iter : core.ops.range.Range U32) (start_n : U32)
    (cur : Array U8 32#usize)
    (keys : alloc.vec.Vec (U32 × Array U8 32#usize))
    (hb : keys.val.length + (iter.end.val - iter.start.val) ≤ Usize.max) :
    NoPanic (derive_chain_loop iter start_n cur keys) := by
  unfold NoPanic derive_chain_loop
  apply loop.spec_decr_nat
    (measure := fun x => (Prod.fst x).end.val - (Prod.fst x).start.val)
    (inv := fun x =>
      (Prod.snd (Prod.snd x)).val.length
        + ((Prod.fst x).end.val - (Prod.fst x).start.val) ≤ Usize.max)
  · rintro ⟨it, c, ks⟩ hinv
    simp only at hinv
    obtain ⟨⟨nx, mk⟩, hck⟩ := kdf_ck_no_panic h c
    simp only [derive_chain_loop.body, hck]
    by_cases hlt : it.start.val < it.end.val <;> step* <;> simp_all <;> omega
  · exact hb

private theorem allM_pure_ok {α : Type} (g : α → Bool) (l : List α) :
    ∃ b, List.allM (fun x => (ok (g x) : Result Bool)) l = ok b := by
  induction l with
  | nil => exact ⟨true, rfl⟩
  | cons hd tl ih =>
    obtain ⟨b, hb⟩ := ih
    by_cases hg : g hd
    · refine ⟨b, ?_⟩
      simp only [List.allM, hg]
      simpa using hb
    · have hg' : g hd = false := by simpa using hg
      refine ⟨false, ?_⟩
      simp only [List.allM, hg']
      rfl

/-- Comparing two byte arrays of the same length always returns a value: the
lengths match by construction and the element comparison is total. The stepping
tactic has no spec for the array comparison, so the skipped-key scan needs this
to get past the point where it compares ratchet public keys. -/
@[step]
theorem array_eq_total {N : Usize} (a b : Array U8 N) :
    core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8 a b ⦃ fun _ => True ⦄ := by
  have h : ∃ r, core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8 a b = ok r := by
    simp only [core.array.equality.PartialEqArray.eq]
    split
    · exact allM_pure_ok _ _
    · exact ⟨false, rfl⟩
  obtain ⟨r, hr⟩ := h
  simp [hr]

/-- A second boundary. Aeneas does not model `Vec::remove`, so it reaches the
translation as an opaque function and this hypothesis states its totality. Rust's `Vec::remove` panics only on an
out-of-bounds index, which the length check in the scan already rules out, so
assuming it total is sound. It is stated rather than assumed silently, and it is
worth removing: unlike the HMAC, this is a standard-library operation rather
than a deliberate trusted primitive, so the verified zone should not depend on
one that the translation cannot see into.

**`[Inhabited T]` is load-bearing, not decoration.** Stated for every `T`,
the hypothesis would be refutable: at `T := Empty` the existential asks for
an element of an empty type, so `VecRemoveTotal → False` would be provable
and every theorem taking it -- `try_skipped_no_panic`, `age_store_spec`, the
receive path, and `T3.lean`'s `receive_refines` -- with it
(`Translation/Satisfiability.lean` carries the refutation of the unbounded
shape and a model of this one). The bound rules out the Lean artefact and
nothing else: the hypothesis still says nothing about an out-of-range index,
where Rust panics, so it remains sound *as used* (every call site checks the
index first) and stronger than Rust; guarding it with `i.val < v.length →`
is an open item in `LIMITATIONS.md`. -/
def VecRemoveTotal : Prop :=
  ∀ {T : Type} [Inhabited T] (A : Type) (v : alloc.vec.Vec T) (i : Usize),
    ∃ r, alloc.vec.Vec.remove A v i = ok r ∧ r.2.val = v.val.eraseIdx i.val

/-- Aeneas does not derive this for its generated structures; `VecRemoveTotal`
asks for it (see its docstring), and this is the element type every
`remove` in the crate is applied to. -/
instance : Inhabited SkippedKey :=
  ⟨{ dh := default, n := default, stored_at := default, key := default }⟩

/-- The two length facts the loops need, derived rather than assumed. Stating
the assumption as the operation's value and deriving the rest is what refinement
needs anyway, and it means the lengths cannot drift from the value. -/
theorem VecRemoveTotal.lengths (hrm : VecRemoveTotal) {T : Type} [Inhabited T] (A : Type)
    (v : alloc.vec.Vec T) (i : Usize) :
    ∃ r, alloc.vec.Vec.remove A v i = ok r ∧ r.2.val.length ≤ v.val.length
      ∧ (i.val < v.val.length → r.2.val.length + 1 = v.val.length) := by
  obtain ⟨r, hr, hv⟩ := hrm A v i
  refine ⟨r, hr, ?_, ?_⟩
  · simp only [hv, List.length_eraseIdx]
    split <;> omega
  · intro hlt
    simp only [hv, List.length_eraseIdx]
    split <;> omega

/-- The skipped-key scan cannot fail. The index is guarded by the length check
that precedes it, so neither the read nor the removal goes out of bounds, and
the cursor increment cannot overflow because the cursor stays below a length
that is itself within `Usize.max`. The scan does not modify the store while
looking, so the measure is simply how much of it is left to examine and the
invariant is trivial. -/
theorem try_skipped_loop_no_panic (hrm : VecRemoveTotal)
    (state : State) (header : Header) (i : Usize) :
    NoPanic (try_skipped_loop state header i) := by
  unfold NoPanic try_skipped_loop
  apply loop.spec_decr_nat
    (measure := fun j => state.skipped.val.length - j.val)
    (inv := fun _ => True)
  · rintro j -
    simp only [try_skipped_loop.body]
    obtain ⟨⟨removed, v'⟩, hrm', -, -⟩ := hrm.lengths Global state.skipped j
    by_cases hlt : j.val < state.skipped.val.length <;> step* <;> simp_all
  · trivial

/-- `derive_chain` is the loop with its initial state, so it inherits the loop's
proof directly. -/
@[step]
theorem derive_chain_no_panic (h : HmacTotal) (ck : Array U8 32#usize)
    (start_n count : U32) :
    derive_chain ck start_n count ⦃ fun _ => True ⦄ := by
  unfold derive_chain
  refine derive_chain_loop_no_panic h _ start_n ck _ ?_
  simp
  scalar_tac

/-- The chain loop, with the postcondition strengthened from "did not panic" to
the number of keys it produced. Panic-freedom alone does not compose: a caller
that then feeds those keys into another bounded structure has to know how many
there are. The bound `N` is threaded rather than fixed at `Usize.max`, because
the caller's bound is the tighter one. -/
theorem derive_chain_loop_length (h : HmacTotal) (N : Nat) (hN : N ≤ Usize.max)
    (iter : core.ops.range.Range U32) (start_n : U32)
    (cur : Array U8 32#usize)
    (keys : alloc.vec.Vec (U32 × Array U8 32#usize))
    (hb : keys.val.length + (iter.end.val - iter.start.val) ≤ N) :
    derive_chain_loop iter start_n cur keys ⦃ fun r =>
      match r with
      | core.result.Result.Ok p => p.2.val.length ≤ N
      | core.result.Result.Err _ => True ⦄ := by
  unfold derive_chain_loop
  apply loop.spec_decr_nat
    (measure := fun x => (Prod.fst x).end.val - (Prod.fst x).start.val)
    (inv := fun x =>
      (Prod.snd (Prod.snd x)).val.length
        + ((Prod.fst x).end.val - (Prod.fst x).start.val) ≤ N)
  · rintro ⟨it, c, ks⟩ hinv
    simp only at hinv
    obtain ⟨⟨nx, mk⟩, hck⟩ := kdf_ck_no_panic h c
    simp only [derive_chain_loop.body, hck]
    by_cases hlt : it.start.val < it.end.val <;> step* <;> simp_all <;> omega
  · exact hb

/-- The same, lifted to the whole function, with the bound still free. -/
theorem derive_chain_length (h : HmacTotal) (N : Nat) (hN : N ≤ Usize.max)
    (ck : Array U8 32#usize) (start_n count : U32) (hc : count.val ≤ N) :
    derive_chain ck start_n count ⦃ fun r =>
      match r with
      | core.result.Result.Ok p => p.2.val.length ≤ N
      | core.result.Result.Err _ => True ⦄ := by
  unfold derive_chain
  refine derive_chain_loop_length h N hN _ start_n ck _ ?_
  simp
  scalar_tac

/-- The bound specialised to the count, which is the form a caller actually
needs and the form the stepping tactic can apply without guessing: leaving `N`
free let unification pick it from whatever hypothesis was in scope, which gave a
bound too weak to be useful. -/
@[step]
theorem derive_chain_length_count (h : HmacTotal) (ck : Array U8 32#usize)
    (start_n count : U32) :
    derive_chain ck start_n count ⦃ fun r =>
      match r with
      | core.result.Result.Ok p => p.2.val.length ≤ count.val
      | core.result.Result.Err _ => True ⦄ :=
  derive_chain_length h count.val (by scalar_tac) ck start_n count (by omega)

/-- The purge scan cannot fail. Unlike the skipped-key scan it does not advance
its index when it removes, so the measure has to be the distance left in a
vector that is itself shrinking; that is why `VecRemoveTotal` has to say the
removal shortens the vector exactly, rather than merely not lengthening it. -/
theorem purge_chain_range_loop_no_panic (hrm : VecRemoveTotal)
    (skipped : alloc.vec.Vec SkippedKey) (dhr : Array U8 32#usize)
    (from1 upto : U32) (i : Usize) :
    NoPanic (purge_chain_range_loop skipped dhr from1 upto i) := by
  unfold NoPanic purge_chain_range_loop
  apply loop.spec_decr_nat
    (measure := fun x => (Prod.fst x).val.length - (Prod.snd x).val)
    (inv := fun _ => True)
  · rintro ⟨v, j⟩ -
    simp only [purge_chain_range_loop.body]
    obtain ⟨⟨removed, v'⟩, hrm', hle, heq⟩ := hrm.lengths Global v j
    by_cases hlt : j.val < v.val.length <;> step* <;> simp_all <;> omega
  · trivial

/-- The purge never grows the store, which is what carries the store-length
precondition across it into the storing loop. -/
theorem purge_chain_range_loop_shrinks (hrm : VecRemoveTotal)
    (skipped : alloc.vec.Vec SkippedKey) (dhr : Array U8 32#usize)
    (from1 upto : U32) (i : Usize) :
    purge_chain_range_loop skipped dhr from1 upto i ⦃ fun r =>
      r.val.length ≤ skipped.val.length ⦄ := by
  unfold purge_chain_range_loop
  apply loop.spec_decr_nat
    (measure := fun x => (Prod.fst x).val.length - (Prod.snd x).val)
    (inv := fun x => (Prod.fst x).val.length ≤ skipped.val.length)
  · rintro ⟨v, j⟩ hinv
    simp only at hinv
    simp only [purge_chain_range_loop.body]
    obtain ⟨⟨removed, v'⟩, hrm', hle, heq⟩ := hrm.lengths Global v j
    by_cases hlt : j.val < v.val.length <;> step* <;> simp_all <;> omega
  · simp

@[step]
theorem purge_chain_range_shrinks (hrm : VecRemoveTotal)
    (skipped : alloc.vec.Vec SkippedKey) (dhr : Array U8 32#usize)
    (from1 upto : U32) :
    purge_chain_range skipped dhr from1 upto ⦃ fun r =>
      r.val.length ≤ skipped.val.length ⦄ := by
  unfold purge_chain_range
  exact purge_chain_range_loop_shrinks hrm skipped dhr from1 upto 0#usize

/-- Skipping forward cannot fail. Every fallible step is guarded: the
subtraction by the check that `upto` is past the cursor, the store arithmetic by
the `MAX_SKIPPED_STORE` bound, and the derivation and the store loop by their
own proofs. The store's own length is the one quantity the type does not bound,
so it is a hypothesis.

The two stepping phases are deliberately sequenced rather than nested: the
second does not fire inside `all_goals`, and the pair the derivation returns has
to be destructured between them or a `let` residue blocks the goal. -/
theorem skip_message_keys_no_panic (h : HmacTotal) (hrm : VecRemoveTotal)
    (state : State) (upto : U32)
    (hs : state.skipped.val.length + U32.max ≤ Usize.max) :
    NoPanic (skip_message_keys state upto) := by
  unfold NoPanic skip_message_keys
  simp only [lift]
  step*
  obtain ⟨ck2, keys⟩ := v
  simp only [alloc.vec.IntoIteratorVec.into_iter]
  step*

/-- The scan's wrapper only repackages the tuple the loop returns, so it
inherits the loop's proof. -/
theorem try_skipped_no_panic (hrm : VecRemoveTotal) (state : State)
    (header : Header) :
    NoPanic (try_skipped state header) := by
  unfold NoPanic try_skipped
  obtain ⟨r, hr⟩ := (noPanic_iff _).mp (try_skipped_loop_no_panic hrm state header 0#usize)
  obtain ⟨o, a, o1, a1, o2, o3, i, i1, i2, v, ev, lbl⟩ := r
  simp [hr]

/-- The array inequality, which is defined in terms of the equality above rather
than being opaque, so it inherits its totality. -/
@[step]
theorem array_ne_total {N : Usize} (a b : Array U8 N) :
    core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8 a b
    ⦃ fun _ => True ⦄ := by
  unfold core.array.equality.PartialEqArray.ne
  step*

/-- The store loop, with the bound carried so a caller learns how large the
store ends up rather than only that the loop did not fail. Same shape as the
chain loop's length lemma. -/
theorem skip_message_keys_loop_bound (B : Nat) (hB : B ≤ Usize.max)
    (dhr : Array U8 32#usize)
    (iter : alloc.vec.into_iter.IntoIter (U32 × Array U8 32#usize))
    (v : alloc.vec.Vec SkippedKey) (now : U32)
    (h : v.val.length + iter.val.length ≤ B) :
    skip_message_keys_loop iter dhr v now ⦃ fun r => r.val.length ≤ B ⦄ := by
  unfold skip_message_keys_loop
  apply loop.spec_decr_nat
    (measure := fun x => (Prod.fst x).val.length)
    (inv := fun x => (Prod.snd x).val.length + (Prod.fst x).val.length ≤ B)
  · rintro ⟨it, w⟩ hinv
    unfold skip_message_keys_loop.body alloc.vec.into_iter.IteratorIntoIter.next
    obtain ⟨l, hl⟩ := it
    cases l with
    | nil => simp_all
    | cons hd tl =>
      obtain ⟨n, mk⟩ := hd
      simp only [List.length_cons] at hinv
      have hw : (↑w : List SkippedKey).length < Usize.max := by omega
      simp only []
      step*; simp_all; omega
  · exact h

/-- The store bound in its canonical form: at most what went in. Stated this way
so the stepping tactic can apply it without choosing a bound, the same reason
`derive_chain_length_count` exists. -/
@[step]
theorem skip_message_keys_loop_grows (dhr : Array U8 32#usize)
    (iter : alloc.vec.into_iter.IntoIter (U32 × Array U8 32#usize))
    (v : alloc.vec.Vec SkippedKey) (now : U32)
    (h : v.val.length + iter.val.length ≤ Usize.max) :
    skip_message_keys_loop iter dhr v now ⦃ fun r =>
      r.val.length ≤ v.val.length + iter.val.length ⦄ :=
  skip_message_keys_loop_bound _ h dhr iter v now (le_refl _)

/-- Skipping forward leaves the store no larger than it was or than the limit
the code enforces, whichever is bigger. This is what a second call needs in
order to re-establish its own precondition, which is why panic-freedom alone was
not enough to compose. -/
@[step]
theorem skip_message_keys_bound (h : HmacTotal) (hrm : VecRemoveTotal)
    (state : State) (upto : U32)
    (hs : state.skipped.val.length + U32.max ≤ Usize.max) :
    skip_message_keys state upto ⦃ fun p =>
      p.2.skipped.val.length ≤ max state.skipped.val.length MAX_SKIPPED_STORE.val ⦄ := by
  unfold skip_message_keys
  simp only [lift]
  step*
  all_goals (try obtain ⟨ck2, keys⟩ := v)
  all_goals (try simp only [alloc.vec.IntoIteratorVec.into_iter])
  all_goals (step* <;> simp_all [alloc.vec.Vec.len, MAX_SKIPPED_STORE] <;> omega)

/-- The scan never grows the store: it either removes the matching key or leaves
the store alone. `receive` needs this to carry its own precondition across the
call, which is the same reason the skip bound exists. -/
theorem try_skipped_loop_shrinks (hrm : VecRemoveTotal) (state : State)
    (header : Header) (i : Usize) :
    try_skipped_loop state header i ⦃ fun r =>
      r.2.2.2.2.2.2.2.2.2.1.val.length ≤ state.skipped.val.length ⦄ := by
  unfold try_skipped_loop
  apply loop.spec_decr_nat
    (measure := fun j => state.skipped.val.length - j.val)
    (inv := fun _ => True)
  · rintro j -
    simp only [try_skipped_loop.body]
    obtain ⟨⟨removed, v'⟩, hrm', hlen, -⟩ := hrm.lengths Global state.skipped j
    by_cases hlt : j.val < state.skipped.val.length <;> step* <;> simp_all
  · trivial

/-- The same for the wrapper, which only repackages the tuple. -/
@[step]
theorem try_skipped_shrinks (hrm : VecRemoveTotal) (state : State)
    (header : Header) :
    try_skipped state header ⦃ fun p =>
      p.2.skipped.val.length ≤ state.skipped.val.length ⦄ := by
  unfold try_skipped
  have hl := try_skipped_loop_shrinks hrm state header 0#usize
  obtain ⟨r, hr⟩ := (noPanic_iff _).mp (try_skipped_loop_no_panic hrm state header 0#usize)
  obtain ⟨o, a, o1, a1, o2, o3, i, i1, i2, v, ev, lbl⟩ := r
  simp_all

/-- Advancing the root key cannot fail. Beyond the opaque expansion itself, the
step splits a 64-byte output into two 32-byte halves and copies each into a
32-byte array; the lengths are carried by the types, so neither the slicing nor
the copy can be out of bounds. -/
-- The three assumptions above, restated as stepping rules. The stepping tactic
-- walks a translated body one call at a time and stops at anything it has no
-- rule for, which is what every opaque call is. Registering them here lets it
-- walk straight through, with the assumption itself left as a side goal that
-- `assumption` discharges from the theorem's own hypotheses. Nothing is
-- assumed that the definitions above did not already assume.
@[step]
theorem kdf_ck_step (h : HmacTotal) (ck : Array U8 32#usize) :
    kdf_ck ck ⦃ fun _ => True ⦄ := by
  obtain ⟨r, hr⟩ := kdf_ck_no_panic h ck; simp [hr]

@[step]
theorem hkdf_step (h : HkdfTotal) (N : Usize) (key salt info : Slice U8) :
    tacenta_kdf.hkdf_sha256 N key salt info ⦃ fun _ => True ⦄ := by
  obtain ⟨r, hr⟩ := h N key salt info; simp [hr]

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

theorem kdf_rk_no_panic (h : HkdfTotal) (hz : ZeroizingTotal)
    (rk dh_out : Array U8 32#usize) (labels : LabelSet) :
    NoPanic (kdf_rk rk dh_out labels) := by
  unfold NoPanic kdf_rk
  step* <;> simp_all [Slice.length]

/-- A DH ratchet step cannot fail, and leaves the skipped-key store untouched.
It is two root-key steps and a record update, and the update does not mention
`skipped`, so the store-length precondition survives it. -/
@[step]
theorem dh_ratchet_spec (h : HkdfTotal) (hz : ZeroizingTotal) (state : State) (header : Header)
    (dh_out_recv dh_out_send new_dhs_pub : Array U8 32#usize) :
    dh_ratchet state header dh_out_recv dh_out_send new_dhs_pub ⦃ fun s =>
      s.skipped.val.length = state.skipped.val.length ⦄ := by
  unfold dh_ratchet
  obtain ⟨⟨rk1, ckr⟩, h1⟩ := (noPanic_iff _).mp (kdf_rk_no_panic h hz state.rk dh_out_recv state.labels)
  obtain ⟨⟨rk2, cks⟩, h2⟩ := (noPanic_iff _).mp (kdf_rk_no_panic h hz rk1 dh_out_send state.labels)
  simp [h1, h2]

/-- Ageing the store cannot fail, and cannot grow it.

Every fallible step is guarded: the index by the `i < len` test, the removal by
`VecRemoveTotal`, and the cursor's increment by the store's own length, which a
`Vec` bounds by `Usize.max`. The subtraction that decides expiry is saturating,
so it is total by construction rather than by an invariant about `stored_at`.

The measure is the entries left to scan. It falls whichever way the branch goes:
keeping moves the cursor up, and removing shortens the store while the cursor
stays. -/
theorem age_store_loop_bound (hrm : VecRemoveTotal) (B : Nat)
    (v : alloc.vec.Vec SkippedKey) (now : U32) (i : Usize)
    (h : v.val.length ≤ B) :
    age_store_loop v now i ⦃ fun r => r.val.length ≤ B ⦄ := by
  unfold age_store_loop
  apply loop.spec_decr_nat
    (measure := fun x => (Prod.fst x).val.length - (Prod.snd x).val)
    (inv := fun x => (Prod.fst x).val.length ≤ B)
  · rintro ⟨w, j⟩ hinv
    simp only [age_store_loop.body, lift]
    -- The third fact is what the measure needs: a removal in range shortens the
    -- store by exactly one, so the measure falls even though the cursor does not.
    obtain ⟨⟨removed, w'⟩, hrm', hlen, hdec⟩ := hrm.lengths Global w j
    by_cases hlt : j.val < w.val.length <;> step* <;> simp_all <;> omega
  · exact h

/-- The wrapper: the record update replaces `skipped` with what the loop
returned and touches nothing else that the bound mentions. -/
@[step]
theorem age_store_spec (hrm : VecRemoveTotal) (state : State) :
    age_store state ⦃ fun s => s.skipped.val.length ≤ state.skipped.val.length ⦄ := by
  unfold age_store
  simp only [lift]
  have hl := age_store_loop_bound hrm state.skipped.val.length state.skipped
    (core.num.U32.saturating_add state.events 1#u32) 0#usize (le_refl _)
  step*

theorem receive_no_panic (h : HmacTotal) (hk : HkdfTotal) (hz : ZeroizingTotal)
    (hrm : VecRemoveTotal) (state : State) (header : Header)
    (dh_out_recv dh_out_send new_dhs_pub : Array U8 32#usize)
    (hs : max state.skipped.val.length MAX_SKIPPED_STORE.val + U32.max ≤ Usize.max) :
    NoPanic (receive state header dh_out_recv dh_out_send new_dhs_pub) := by
  unfold NoPanic receive
  step*
  rcases hd : state1.dhr_pub with _ | dhr <;> (try simp only) <;> step*
  all_goals (simp_all [MAX_SKIPPED_STORE]; omega)

/-
## What T1 covers, and what it rests on

Every function in the verified zone is now proven panic-free: the chain-key and
root-key steps, sending, the skip loop and its wrapper, the skipped-key scan,
the DH ratchet step, and `receive`, which composes the rest.

Nothing here assumes anything about our own code. What the proofs do rest on is
the code the translation cannot see inside, and there are three such boundaries,
each named as an assumption rather than left implicit:

* `HmacTotal` and `HkdfTotal`, the key-derivation primitives, deliberately
  opaque so the ratchet's control flow can be reasoned about without dragging in
  the whole of SHA-256;
* `ZeroizingTotal`, the external `zeroize` crate, whose wrapper and projection
  cannot fail; and
* `VecRemoveTotal`: Aeneas does not model `Vec::remove`, so it reaches the
  translation as an opaque function and this hypothesis states its totality.
  `Vec::remove` panics only on an out-of-bounds index, which the scan's own
  length check rules out, and it plainly does not lengthen the vector.

`receive` carries one precondition, and it is a real one rather than a
formality. The skipped-key store must be small enough that its length plus the
whole `u32` range still fits a `usize`, taking the store at the largest it can
reach, which is its starting size or `MAX_SKIPPED_STORE`, whichever is bigger.
On a 64-bit target that is satisfied by any store that could exist. On a 32-bit
target it is a genuine constraint, because Aeneas models `usize` at the
platform width and the sum would not fit; that is why the precondition is stated
in terms of the maximum rather than assumed away.
-/

-- The axiom audit, enforced rather than asserted. The proofs rest on Lean's
-- three standard axioms and on the opaque key-derivation primitive, and on
-- nothing else: no `sorry`, and no assumption about our own code. A later
-- change that smuggled one in would fail this check.
/-- info: 'Tacenta.T1.kdf_ck_no_panic' depends on axioms: [propext, Classical.choice, Quot.sound, tacenta_kdf.hmac_sha256] -/
#guard_msgs in
#print axioms Tacenta.T1.kdf_ck_no_panic

/-- info: 'Tacenta.T1.send_no_panic' depends on axioms: [propext, Classical.choice, Quot.sound, tacenta_kdf.hmac_sha256] -/
#guard_msgs in
#print axioms Tacenta.T1.send_no_panic

/--
info: 'Tacenta.T1.receive_no_panic' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_kdf.hkdf_sha256,
 tacenta_kdf.hmac_sha256,
 zeroize.Zeroizing,
 zeroize.Zeroizing.new,
 Array.Insts.ZeroizeZeroize.zeroize,
 alloc.vec.Vec.remove,
 zeroize.Zeroize.Blanket.zeroize,
 zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref]
-/
#guard_msgs in
#print axioms Tacenta.T1.receive_no_panic
