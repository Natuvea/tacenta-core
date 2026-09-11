import Translation.T3
import Translation.SpqrT3
import Translation.BraidT3

/-!
# What a decoded state satisfies: the validated persistence constructor

Every leaf crate's `State::from_bytes` ends by calling the crate's own
`invariant()` and refusing the buffer when it is false, so a state that comes
back from a byte string is not merely well-formed for the parser: every clause
of that predicate holds of it. Until now nothing in this tree said so.

Read the predicate for what it is. `Inv s` is a conjunction of field
conditions, and this module proves that a decoded state satisfies it and that
it yields the preconditions the `receive` theorems take. It is **not** a
reachability statement: nothing here proves that the crate's operations
preserve `Inv`, so `Inv s` does not on its own say that some run of the crate
built `s`. Whether the two coincide -- whether the predicate is inductive, so
that the decoder refuses exactly the states no run produces -- is a property
of the Rust operations, argued in the crates' own comments beside the
counters, and is outside this file.
`CLAIMS.md`'s "Read this first" recorded the gap in the honest direction: the
T1 and T3 theorems about `receive` carry preconditions (`hs`, `hone`, `hroom`,
`hskiproom`, `ct1_bounded`), and an untrusted byte string reaching
`from_bytes` could, as far as the proofs were concerned, hand back a state
that violated them.

This module closes that gap as far as each crate's own `invariant` reaches:
for `tacenta-ratchet` and `tacenta-spqr` through the whole predicate, and for
`tacenta-braid` in the one clause its theorems need. What an `invariant` does
not reach is named below rather than glossed. Per crate it gives three things,
in a chain a reader can follow end to end:

1. `Inv`, a Lean predicate mirroring the Rust `invariant`'s clauses on the
   translated state type, together with `invariant_true_iff`, which says the
   translated Bool-valued `invariant` returns `true` exactly on states
   satisfying `Inv`. Proving it means characterising the function's index
   loops, which is the work: each is done in the loop-invariant style
   `T1.lean` already uses (`skip_message_keys_loop_bound`,
   `purge_chain_range_loop_*`), via `loop.spec_decr_nat` with a measure and an
   invariant, stepping the list one element at a time with
   `List.drop_eq_getElem_cons`.

2. `from_bytes_establishes_inv`, which walks the translated `from_bytes` to
   its final `invariant` call and concludes `Inv` of whatever state it
   returns. No totality assumption is needed for this direction: the theorem
   assumes the decoder *returned* a state, so every fallible step on the way
   already succeeded and is peeled as an equation rather than discharged.

3. `inv_gives_*`, the bridge lemmas that turn `Inv` into the preconditions the
   existing theorems take, and `decoded_*`, the composed statements. Read the
   chain as: decoded state → `Inv` → precondition → theorem.

For `tacenta-ratchet` there is a fourth thing: `witnessBytes`, a concrete
byte string the translated `from_bytes` accepts, and
`from_bytes_establishes_inv_nonvacuous`, which composes it with (2) so that
the implication in (2) is known to have a witness rather than only an
unsatisfiable premise. `Satisfiability.lean` applies that discipline to the leaves'
opaque-boundary hypotheses; this is the same discipline applied to a decoder. The
sparse ratchet and the Braid have no such witness: their `from_bytes` chains
are longer, and the Braid's runs through the opaque erasure and KEM decoders,
which no byte string can be shown to satisfy from inside this translation.

## What this does not say

* The subject is the **translated** `from_bytes`, the one Aeneas produced from
  the Rust. It is the same artefact every other theorem in this package is
  about, and the translation itself is trusted the same way (see
  `LIMITATIONS.md`).
* It is about a leaf crate's own persistence format. The session layer above
  these crates is untranslated, so nothing here says what a session's
  `from_bytes` establishes.
* Two hypotheses are carried rather than proved, both named and both satisfied
  by the real Rust:
  - a platform-width fact for the ratchet's `hs`
    (`MAX_SKIPPED_STORE + u32::MAX ≤ usize::MAX`, true on a 64-bit target and
    exactly the condition `T1.lean`'s own docstring records), passed as an
    explicit argument rather than assumed globally, and
  - `Tacenta.BraidT1.Ct1LenTotal` for the Braid, which is not new: it is the
    existing hypothesis `BraidT1` already uses, and it says
    `tacenta_kem::CT1_LEN` returns a value at most 4096. The real constant is
    1408 (`braid/src/lib.rs` says so where `ct1_bounded` is motivated).
* **A step of counter headroom is carried too, and it is not a fact of every
  state.** Each of these three crates reserves the top value of the counter it
  steps, so that no state its operations produce is one its own decoder
  refuses: the ratchet's clock clamps at `MAX_EVENTS = u32::MAX - 1`, the
  sparse ratchet's `advance` refuses the step to `epoch == u64::MAX`, and the
  Braid's `step_receive` refuses the same in transitions (5) and (13). The
  three models now reserve the same values (`Model.State.maxEvents`,
  `Model.SparseRatchet.u64Max`, `Model.Braid.u64Max`). The refinement theorems
  ask for one step of headroom (`events + 1 < u32::MAX`,
  `epoch + 1 < u64::MAX`), which dates from when the models reserved nothing
  and is kept so that the statements are unchanged; whether it could now be
  dropped has not been checked. A parked ratchet clock
  and a sparse ratchet at `epoch = u64::MAX - 1` are ordinary states: they
  satisfy the `invariant`, they decode, and their crates go on operating on
  them. So no `invariant` can supply that step, and none is asked to; the
  ratchet's is the one explicit argument `decoded_receive_refines` below still
  takes. **Panic-freedom is unaffected:** every `decoded_*_no_panic` here is
  unconditional in the counters.
* For the sparse ratchet, `SpqrT3.receive_refines`'s `hepoch`, `hcb`, `hsb`,
  `hnewb` and `hcounter` are **not** consequences of the crate's `invariant`,
  and are not claimed here. A state with `epoch = u64::MAX - 1` and a chain at
  that epoch passes `invariant` and fails both `hepoch` and `hcb`; saying
  otherwise would be false. Its `hroom`, `hskiproom` and `hone` are proved.
* For the Braid, only `ct1_bounded` is derived. The rest of the Rust
  `invariant` delegates to `tacenta-erasure`'s coder invariants, which reach
  this translation as opaque axioms and so cannot be unfolded here; and
  `BraidT3.step_receive_refines`'s `hepoch` (`epoch + 1 < u64::MAX`) is not a
  clause the Rust `invariant` checks at all -- it checks `epoch >= 1` and
  nothing above.
-/

open Aeneas Aeneas.Std Result

namespace Tacenta.ImportInv

/-! ## Peeling a translated function that returned

The three lemmas below are the whole of the `from_bytes` technique. A
translated function is a chain of `Result` binds, `if`s and `match`es; a
hypothesis that the chain equals `ok r` determines, step by step, that each
bind's left-hand side returned and which branch was taken. `bind_eq_ok_inv`
peels one bind, its two arity-specific variants peel one whose value is a
tuple (needed because a tuple-pattern `let` is not something `split` will
reduce), and `split` does the branches. Nothing here is specific to a crate. -/

/-- A bind that returned tells us its left-hand side returned. -/
theorem bind_eq_ok_inv {α β : Type} {x : Result α} {f : α → Result β} {r : β}
    (h : (do let v ← x; f v) = ok r) : ∃ v, x = ok v ∧ f v = ok r := by
  cases x with
  | ok v => exact ⟨v, rfl, h⟩
  | fail e => simp at h
  | div => simp at h

/-- The same, for a bind whose value is a pair, destructured so the
continuation is applied to a constructor and its pattern `let` reduces. -/
theorem bind2_eq_ok_inv {α β γ : Type} {x : Result (α × β)} {f : α × β → Result γ} {r : γ}
    (h : (do let v ← x; f v) = ok r) : ∃ a b, x = ok (a, b) ∧ f (a, b) = ok r := by
  cases x with
  | ok v => exact ⟨v.1, v.2, rfl, h⟩
  | fail e => simp at h
  | div => simp at h

/-- The same again, for a triple. -/
theorem bind3_eq_ok_inv {α β γ δ : Type} {x : Result (α × β × γ)}
    {f : α × β × γ → Result δ} {r : δ}
    (h : (do let v ← x; f v) = ok r) :
    ∃ a b c, x = ok (a, b, c) ∧ f (a, b, c) = ok r := by
  cases x with
  | ok v => exact ⟨v.1, v.2.1, v.2.2, rfl, h⟩
  | fail e => simp at h
  | div => simp at h

/-- A list whose elements are pairwise distinct under `key` holds at most one
element with any given key. This is what turns a store's "is a map on
`(dh, n)`" clause into the `hone` premise T3 and SpqrT3 state as a bound on a
filtered model list. -/
theorem length_filter_le_one_of_pairwise {α β : Type} {key : α → β} {k : β}
    {L : List α} {p : α → Bool}
    (hp : L.Pairwise (fun a b => key a ≠ key b))
    (hpk : ∀ a ∈ L, p a = true → key a = k) :
    (L.filter p).length ≤ 1 := by
  induction L with
  | nil => simp
  | cons a t ih =>
    rw [List.pairwise_cons] at hp
    by_cases hpa : p a = true
    · have hnil : t.filter p = [] := by
        rw [List.filter_eq_nil_iff]
        intro b hb hpb
        exact hp.1 b hb (by rw [hpk a (by simp) hpa, hpk b (by simp [hb]) hpb])
      rw [List.filter_cons_of_pos hpa, hnil]
      simp
    · rw [List.filter_cons_of_neg (by simpa using hpa)]
      exact ih hp.2 (fun b hb => hpk b (by simp [hb]))

/-- A `match` on an `Option` whose payload is a pair, in the same peeling
style. -/
theorem match_option_prod_eq_ok {α β γ : Type} {o : Option (α × β)} {X : Result γ}
    {f : α × β → Result γ} {r : γ}
    (h : (match o with | none => X | some p => f p) = ok r) :
    X = ok r ∨ ∃ a b, o = some (a, b) ∧ f (a, b) = ok r := by
  cases o with
  | none => exact Or.inl h
  | some p => exact Or.inr ⟨p.1, p.2, rfl, h⟩

/-- Indexing a vector in range returns the element. -/
theorem vec_index_eq {α : Type} (v : alloc.vec.Vec α) (i : Std.Usize) (a : α)
    (h : v.val[i.val]? = some a) :
    alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice α) v i = ok a := by
  simp only [alloc.vec.Vec.index_slice_index, alloc.vec.Vec.index_usize]
  rw [show v[i.val]? = some a from h]

/-- Indexing a slice in range returns the element, as an equation. The
counterpart of `vec_index_eq` for the byte buffer a decoder is handed, and
what lets a concrete buffer's bytes be read off one at a time. -/
theorem slice_index_eq {α : Type} (v : Slice α) (i : Std.Usize) (a : α)
    (h : v.val[i.val]? = some a) : Slice.index_usize v i = ok a := by
  unfold Slice.index_usize
  simp [h]

/-- Aeneas's `Array` is a `def` for a subtype, so the subtype's decidable
equality is not found by instance search on its own. The invariant's duplicate
test compares two 32-byte keys, so it is needed to state the Bool the
translated function computes. -/
instance instDecidableEqArray {α : Type} [DecidableEq α] {N : Std.Usize} :
    DecidableEq (Array α N) :=
  fun a b => decidable_of_iff (a.val = b.val) Subtype.ext_iff.symm

/-- The translated array comparison, as an equation rather than a
postcondition: `T3.array_eq_val` says the result is `true` exactly when the
arrays are equal, and every use below needs the value itself. -/
theorem array_eq_eq {N : Std.Usize} (a b : Array Std.U8 N) :
    core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8 a b = ok (decide (a = b)) := by
  obtain ⟨v, hv, hiff⟩ := Std.WP.spec_imp_exists (Tacenta.T3.array_eq_val a b)
  rw [hv]
  cases v <;> simp_all

/-! # `tacenta-ratchet`

`State::invariant` (ratchet/src/lib.rs) is six clauses, grouped here exactly
as the comment above the Rust function groups them and as `CLAIMS.md` repeats
them: the store is at most `MAX_SKIPPED_STORE`, the clock is below
`u32::MAX`, no stored entry is ahead of the clock, no two entries share
`(dh, n)`, the chains are present in the order the operations open them, and
every curve public key the state holds is canonical. The first two are read
straight off the final `if` chain; the middle two, and the canonicity of each
stored entry's `dh`, are what the two nested index loops compute into
`store_ok`; the fifth is the `matches!` the translation sees as `chains_ok`;
and the canonicity of `dhs_pub` and `dhr_pub` is `keys_ok`, computed after the
loops by `is_canonical_x25519`, whose value `Tacenta.T1.is_canonical_x25519_spec`
proves. -/
namespace Ratchet

open tacenta_ratchet

/-- The canonicity check as an equation, the form the invariant's proofs
rewrite with. -/
theorem canonical_eq (k : Array Std.U8 32#usize) :
    is_canonical_x25519 k = ok (Tacenta.T1.canonicalX25519 k) := by
  obtain ⟨r, hr, hre⟩ := Std.WP.spec_imp_exists (Tacenta.T1.is_canonical_x25519_spec k)
  rw [hr, hre]

/-- The inner loop's per-pair test, as the Bool the translation computes:
two entries collide when both their `dh` and their `n` agree. -/
def notDup (a t : SkippedKey) : Bool :=
  !(decide (a.dh = t.dh) && decide (a.n = t.n))

/-- The inner loop, which scans `j` from `i + 1` to the end and clears the flag
on a collision with entry `i`. Stated as: it returns the incoming flag
conjoined with "no entry from `j` onward collides with entry `i`". The list is
stepped with `List.drop`, so the loop invariant is an equation between the
flag-so-far conjoined with the suffix still to scan and the value at entry. -/
theorem invariant_inner_spec (v : alloc.vec.Vec SkippedKey) (i : Std.Usize)
    (hi : i.val < v.val.length) (b : Bool) (j : Std.Usize) :
    State.invariant_loop0_loop0 v b i j ⦃ fun r =>
      r = (b && ((v.val.drop j.val).all (notDup (v.val[i.val]'hi)))) ⦄ := by
  unfold State.invariant_loop0_loop0
  apply loop.spec_decr_nat
    (measure := fun x => v.val.length - (Prod.snd x).val)
    (inv := fun x => ((Prod.fst x) &&
        ((v.val.drop (Prod.snd x).val).all (notDup (v.val[i.val]'hi))))
      = (b && ((v.val.drop j.val).all (notDup (v.val[i.val]'hi)))))
  · rintro ⟨b', j'⟩ hinv
    simp only at hinv
    simp only [State.invariant_loop0_loop0.body]
    by_cases hlt : j'.val < v.val.length
    · step*
      cases b <;> simp only [Bool.false_eq_true, if_false, if_true] <;> step*
      all_goals (try (split <;> step*))
      all_goals (
        refine ⟨?_, by scalar_tac⟩
        rw [List.drop_eq_getElem_cons hlt] at hinv
        simp only [notDup, List.all_cons] at hinv
        simp_all)
    · step*
      have hnil : v.val.drop j'.val = [] := List.drop_eq_nil_of_le (by omega)
      rw [hnil] at hinv
      simpa using hinv
  · rfl

/-- The inner loop as an equation, which is the form the outer loop's proof
rewrites with. -/
theorem invariant_inner_eq (v : alloc.vec.Vec SkippedKey) (i : Std.Usize)
    (hi : i.val < v.val.length) (b : Bool) (j : Std.Usize) :
    State.invariant_loop0_loop0 v b i j
      = ok (b && ((v.val.drop j.val).all (notDup (v.val[i.val]'hi)))) := by
  obtain ⟨r, hr, hre⟩ := Std.WP.spec_imp_exists (invariant_inner_spec v i hi b j)
  rw [hr, hre]

/-- What the two loops compute, defined by structural recursion on the store in
exactly the order the loops visit it: for each entry, it is not ahead of the
clock, its `dh` is canonical, no later entry collides with it, and the rest of
the store is good. -/
def storeOk : List SkippedKey → Std.U32 → Bool
  | [], _ => true
  | a :: rest, ev =>
      decide (a.stored_at.val ≤ ev.val) && Tacenta.T1.canonicalX25519 a.dh
        && rest.all (notDup a) && storeOk rest ev

/-- The outer loop. It returns the six state fields it was reading unchanged,
and `store_ok` conjoined with `storeOk` of the suffix still to scan. -/
theorem invariant_outer_spec (self : State) (b : Bool) (i : Std.Usize) :
    State.invariant_loop0 self b i ⦃ fun r =>
      r = (self.dhs_pub, self.dhr_pub, self.cks, self.ckr, self.skipped, self.events,
        (b && storeOk (self.skipped.val.drop i.val) self.events)) ⦄ := by
  unfold State.invariant_loop0
  apply loop.spec_decr_nat
    (measure := fun x => self.skipped.val.length - (Prod.snd x).val)
    (inv := fun x => ((Prod.fst x) && storeOk (self.skipped.val.drop (Prod.snd x).val) self.events)
      = (b && storeOk (self.skipped.val.drop i.val) self.events))
  · rintro ⟨b', i'⟩ hinv
    simp only at hinv
    simp only [State.invariant_loop0.body]
    by_cases hlt : i'.val < self.skipped.val.length
    · step*
      have hif : (if sk.stored_at > self.events then (ok false : Result Bool) else ok b')
          = ok (b' && decide (sk.stored_at.val ≤ self.events.val)) := by
        by_cases h : sk.stored_at > self.events
        · rw [if_pos h, decide_eq_false (by scalar_tac : ¬ (sk.stored_at.val ≤ self.events.val))]
          simp
        · rw [if_neg h, decide_eq_true (by scalar_tac : sk.stored_at.val ≤ self.events.val)]
          simp
      rw [hif]
      simp only [bind_tc_ok, canonical_eq]
      rw [show ∀ (x P : Bool), (if P = true then (ok x : Result Bool) else ok false)
            = ok (x && P) from fun x P => by cases P <;> simp]
      simp only [bind_tc_ok]
      step*
      rw [invariant_inner_eq self.skipped i' hlt]
      step*
      refine ⟨?_, by scalar_tac⟩
      rw [List.drop_eq_getElem_cons hlt] at hinv
      simp only [storeOk, ← sk_post] at hinv ⊢
      simp_all [Bool.and_assoc]
    · step*
      have hnil : self.skipped.val.drop i'.val = [] := List.drop_eq_nil_of_le (by omega)
      rw [hnil] at hinv
      simpa [storeOk] using hinv
  · rfl

/-- The `chains_ok` arm: a receiving chain implies a sending chain and a peer
key. `matches!` in the Rust, a nested `match` after expansion, which is what
the translation sees. -/
def chainsOk (s : State) : Bool :=
  match s.ckr with
  | none => true
  | some _ => s.cks.isSome && s.dhr_pub.isSome

/-- The `keys_ok` arm: the state's own ratchet public key, and the peer's when
present, are canonical. -/
def keysOk (s : State) : Bool :=
  Tacenta.T1.canonicalX25519 s.dhs_pub &&
    match s.dhr_pub with
    | none => true
    | some k => Tacenta.T1.canonicalX25519 k

/-- The whole predicate as the Bool the translated `invariant` returns. -/
def InvB (s : State) : Bool :=
  decide (s.skipped.val.length ≤ MAX_SKIPPED_STORE.val)
    && decide (s.events.val < Std.U32.max)
    && storeOk s.skipped.val s.events
    && chainsOk s
    && keysOk s

/-- The outer loop as an equation. -/
theorem invariant_outer_eq (self : State) (b : Bool) (i : Std.Usize) :
    State.invariant_loop0 self b i
      = ok (self.dhs_pub, self.dhr_pub, self.cks, self.ckr, self.skipped, self.events,
        (b && storeOk (self.skipped.val.drop i.val) self.events)) := by
  obtain ⟨r, hr, hre⟩ := Std.WP.spec_imp_exists (invariant_outer_spec self b i)
  rw [hr, hre]

/-- **The translated `invariant` computes `InvB`, on every state.** It is total,
which is the strongest form this can take and is what makes the `↔` below an
equivalence rather than one implication. -/
theorem invariant_eq (s : State) : State.invariant s = ok (InvB s) := by
  have h : State.invariant s ⦃ fun r => r = InvB s ⦄ := by
    unfold State.invariant
    rw [invariant_outer_eq s true 0#usize]
    simp only [canonical_eq]
    step*
    simp only [InvB, chainsOk, keysOk, Bool.true_and]
    rcases s.ckr with _ | ck <;> rcases s.cks with _ | ck1 <;> rcases s.dhr_pub with _ | dp <;>
      simp only [bind_tc_ok, Option.isSome_none, Option.isSome_some, Bool.and_false,
        Bool.and_true] <;>
      split_ifs with h1 h2 h3 <;> simp_all [U32.rMax, U32.max_eq]
  obtain ⟨r, hr, hre⟩ := Std.WP.spec_imp_exists h
  rw [hr, hre]

/-- The Rust `invariant`'s clauses as a proposition about the translated state.
Field for field with the comment above `State::invariant` in
`ratchet/src/lib.rs`. -/
structure Inv (s : State) : Prop where
  store_bound : s.skipped.val.length ≤ MAX_SKIPPED_STORE.val
  clock_room : s.events.val < Std.U32.max
  fresh : ∀ e ∈ s.skipped.val, e.stored_at.val ≤ s.events.val
  store_map : s.skipped.val.Pairwise (fun a t => ¬ (a.dh = t.dh ∧ a.n = t.n))
  chains : s.ckr.isSome = true → s.cks.isSome = true ∧ s.dhr_pub.isSome = true
  dhs_canonical : Tacenta.T1.canonicalX25519 s.dhs_pub = true
  dhr_canonical : ∀ k, s.dhr_pub = some k → Tacenta.T1.canonicalX25519 k = true
  store_canonical : ∀ e ∈ s.skipped.val, Tacenta.T1.canonicalX25519 e.dh = true

/-- The store flag, as the two propositions it stands for. -/
theorem storeOk_iff (L : List SkippedKey) (ev : Std.U32) :
    storeOk L ev = true ↔
      ((∀ e ∈ L, e.stored_at.val ≤ ev.val) ∧
        (∀ e ∈ L, Tacenta.T1.canonicalX25519 e.dh = true) ∧
        L.Pairwise (fun a t => ¬ (a.dh = t.dh ∧ a.n = t.n))) := by
  induction L with
  | nil => simp [storeOk]
  | cons a rest ih =>
    simp only [storeOk, notDup, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq,
      Bool.not_eq_true', Bool.and_eq_false_imp, List.pairwise_cons, List.mem_cons,
      forall_eq_or_imp, ih]
    constructor
    · rintro ⟨⟨⟨ha, hc⟩, hnd⟩, hfresh, hcan, hp⟩
      refine ⟨⟨ha, hfresh⟩, ⟨hc, hcan⟩, ?_, hp⟩
      intro t ht ⟨hdh, hn⟩
      have := hnd t ht
      simp_all
    · rintro ⟨⟨ha, hfresh⟩, ⟨hc, hcan⟩, hnd, hp⟩
      refine ⟨⟨⟨ha, hc⟩, ?_⟩, hfresh, hcan, hp⟩
      intro t ht
      have := hnd t ht
      simp_all

/-- **The translated `invariant` returns `true` exactly on states satisfying
`Inv`.** -/
theorem invariant_true_iff (s : State) : State.invariant s = ok true ↔ Inv s := by
  rw [invariant_eq]
  simp only [ok.injEq, InvB, Bool.and_eq_true, decide_eq_true_eq, chainsOk, keysOk,
    storeOk_iff]
  constructor
  · rintro ⟨⟨⟨⟨hb, hr⟩, hfresh, hcan, hp⟩, hc⟩, hdhs, hdhr⟩
    refine ⟨hb, hr, hfresh, hp, ?_, hdhs, ?_, hcan⟩
    · intro hckr
      rcases hckr' : s.ckr with _ | ck
      · simp [hckr'] at hckr
      · rw [hckr'] at hc; simpa using hc
    · intro k hk
      rw [hk] at hdhr; simpa using hdhr
  · rintro ⟨hb, hr, hfresh, hp, hc, hdhs, hdhr, hcan⟩
    refine ⟨⟨⟨⟨hb, hr⟩, hfresh, hcan, hp⟩, ?_⟩, hdhs, ?_⟩
    · rcases hckr' : s.ckr with _ | ck
      · simp
      · have := hc (by simp [hckr'])
        simp [this.1, this.2]
    · rcases hdr : s.dhr_pub with _ | k
      · simp
      · simpa using hdhr k hdr

/-- **A state the translated `from_bytes` returns satisfies `Inv`.** No
assumption of any kind: the hypothesis is that the decoder returned, so every
step it took returned, and the proof is a walk down the one branch that can
produce `Ok`, which is the branch guarded by `invariant`.

Any byte string at all, hostile or corrupt: if `from_bytes` accepts it, every
clause of `Inv` holds of the state it hands back. That is a statement about
the state's fields, not about how it might have arisen; see the note at the
head of this file. -/
theorem from_bytes_establishes_inv (bytes : Slice Std.U8) (s : State)
    (h : State.from_bytes bytes = ok (core.result.Result.Ok s)) : Inv s := by
  rw [← invariant_true_iff]
  rw [State.from_bytes] at h
  repeat' first
    | (replace h := bind3_eq_ok_inv h; obtain ⟨_, _, _, _, h⟩ := h)
    | (replace h := bind_eq_ok_inv h; obtain ⟨_, _, h⟩ := h)
    | split at h
    | simp at h
  all_goals (subst h; simp_all)

/-! ### The decoder accepts something: `from_bytes_establishes_inv` is not vacuous

`from_bytes_establishes_inv` reads "if `from_bytes` returns a state, that
state satisfies `Inv`". A theorem of that shape is worth nothing if the
premise is unsatisfiable, and nothing above rules that out: a `from_bytes`
that rejected every buffer would satisfy it. `Satisfiability.lean` applies
this discipline to every boundary hypothesis; this is the same discipline
applied to a decoder's premise.

So this section exhibits one 185-byte buffer the *translated* `from_bytes`
accepts, and composes it with the theorem above into a state that both came
out of the decoder and satisfies `Inv`. The buffer is the shortest
well-formed encoding: the version byte, four keys (three of them behind an
`Option` tag byte), the four counters zero, the label byte, and a skipped-key
count of zero. Every optional key is written *present* on purpose -- a `None`
tag makes `read_optional_key` run a 32-step all-zero-tail loop, and three of
those are 96 iterations to step through for nothing this needs to say.

The proof is the walk `from_bytes_establishes_inv` does, in the other
direction: rather than peeling a chain that returned, it steps the chain
forward on a known buffer. Each translated helper gets a specification
(`read_key_returns`, `read_optional_key_present`, `read_u32_of_zeros`,
`from_bytes_loop_empty`) and `step*` composes them; the concrete byte reads
are `decide` on a list literal, which is kernel work and not compiler trust,
as the axiom pins at the foot of the file record. -/
section Witness

-- The buffer is a 185-element list literal, and `decide` walks it.
set_option maxRecDepth 100000

/-- The 185 bytes: version `1`; `dhs_pub`; `dhr_pub` present; `rk`; `cks`
present; `ckr` present; `ns`, `nr`, `pn` and `events` all zero; the label
byte; a zero skipped-key count. Every key is all-zero. The invariant's one
clause about keys asks `dhs_pub` and `dhr_pub` to be canonical, and zero is. -/
def witnessList : List Std.U8 :=
  1#u8 :: (List.replicate 32 0#u8 ++ 1#u8 :: (List.replicate 32 0#u8 ++
    (List.replicate 32 0#u8 ++ 1#u8 :: (List.replicate 32 0#u8 ++
      1#u8 :: (List.replicate 53 0#u8)))))

theorem witnessList_length : witnessList.length = 185 := by simp [witnessList]

/-- The same bytes, as the `Slice` the translated `from_bytes` takes. -/
def witnessBytes : Slice Std.U8 :=
  ⟨witnessList, by rw [witnessList_length]; scalar_tac⟩

@[local simp] theorem witnessBytes_val : witnessBytes.val = witnessList := rfl

@[local simp] theorem witnessBytes_length : witnessBytes.length = 185 :=
  witnessList_length

@[local simp] theorem witnessBytes_len : Slice.len witnessBytes = 185#usize := rfl

/-- `read_key` over thirty-two zero bytes is the zero key. Its value is needed:
the invariant asks `dhs_pub` and `dhr_pub` to be canonical, so the proof below
has to know which key was read. -/
@[local step]
theorem read_key_of_zeros (v : Slice Std.U8) (pos : Std.Usize)
    (hlen : pos.val + 32 ≤ v.length)
    (hz : List.slice pos.val (pos.val + 32) v.val = List.replicate 32 0#u8) :
    read_key v pos ⦃ fun r => r = Std.Array.repeat 32#usize 0#u8 ⦄ := by
  unfold read_key
  step*
  · scalar_tac
  · have h32 : s2.val = List.replicate 32 0#u8 := by
      rw [s2_post, s1_post1, i_post]; exact hz
    have h5 : (Std.Array.repeat 32#usize 0#u8).from_slice s2
        = Std.Array.repeat 32#usize 0#u8 := by
      apply Subtype.ext
      rw [Std.Array.from_slice_val _ _ (by rw [h32]; rfl)]
      rw [h32]; rfl
    rw [s_post2, h5]

/-- `read_optional_key` on a `1` tag over thirty-two zero bytes: the present
branch, a `read_key` and no loop, giving the zero key. -/
@[local step]
theorem read_optional_key_present (v : Slice Std.U8) (pos : Std.Usize)
    (hlen : pos.val + 33 ≤ v.length) (htag : v.val[pos.val]? = some 1#u8)
    (hz : List.slice (pos.val + 1) (pos.val + 33) v.val = List.replicate 32 0#u8) :
    read_optional_key v pos ⦃ fun r =>
      r = core.result.Result.Ok (some (Std.Array.repeat 32#usize 0#u8)) ⦄ := by
  unfold read_optional_key
  rw [slice_index_eq v pos 1#u8 htag]
  simp only [bind_tc_ok]
  show (do let i1 ← pos + 1#usize
           let a ← read_key v i1
           ok (core.result.Result.Ok (some a))) ⦃ _ ⦄
  step*

/-- `read_u32` over four zero bytes is zero. The one place a value matters:
`clock_room` is about `events`, and the skipped-key count decides whether the
store loop runs at all. -/
@[local step]
theorem read_u32_of_zeros (v : Slice Std.U8) (pos : Std.Usize)
    (hlen : pos.val + 4 ≤ v.length)
    (hz : List.slice pos.val (pos.val + 4) v.val = List.replicate 4 0#u8) :
    read_u32 v pos ⦃ fun r => r.val = 0 ⦄ := by
  unfold read_u32
  step*
  · scalar_tac
  · have h4 : s2.val = List.replicate 4 0#u8 := by
      rw [s2_post, s1_post1, i_post]; exact hz
    have h5 : (Std.Array.repeat 4#usize 0#u8).from_slice s2
        = Std.Array.repeat 4#usize 0#u8 := by
      apply Subtype.ext
      rw [Std.Array.from_slice_val _ _ (by rw [h4]; rfl)]
      rw [h4]; rfl
    rw [s_post2, h5]
    rfl

/-- The skipped-key loop over an empty range returns its accumulator
untouched: one iteration of `loop`, so the measure is constant. -/
@[local step]
theorem from_bytes_loop_empty (i : Std.Usize) (bytes : Slice Std.U8)
    (pos : Std.Usize) (v : alloc.vec.Vec SkippedKey) (b : Bool) :
    State.from_bytes_loop i { start := 0#usize, «end» := 0#usize } bytes pos v b
      ⦃ fun r => r = (pos, v, b) ⦄ := by
  unfold State.from_bytes_loop
  apply loop.spec_decr_nat
    (measure := fun _ => 0)
    (inv := fun p => p.1.end.val ≤ p.1.start.val ∧ p.2 = (pos, v, b))
  · rintro ⟨⟨st, en⟩, pos', v', b'⟩ ⟨h1, h2⟩
    simp only at h1 h2
    simp only [State.from_bytes_loop.body]
    step*
  · exact ⟨by simp, rfl⟩

/-- The three length constants, as the values they compute to. Each is
`irreducible` in the translation, so the decoder's arithmetic does not step
until they are named. -/
theorem fixed_len_eq : FIXED_LEN = ok 185#usize := by
  have h : FIXED_LEN ⦃ fun r => r = 185#usize ⦄ := by
    unfold FIXED_LEN OPTIONAL_KEY_LEN; step*
  obtain ⟨r, hr, hre⟩ := Std.WP.spec_imp_exists h
  rw [hr, hre]

theorem optional_key_len_eq : OPTIONAL_KEY_LEN = ok 33#usize := by
  have h : OPTIONAL_KEY_LEN ⦃ fun r => r = 33#usize ⦄ := by
    unfold OPTIONAL_KEY_LEN; step*
  obtain ⟨r, hr, hre⟩ := Std.WP.spec_imp_exists h
  rw [hr, hre]

theorem skipped_encoded_len_eq : SkippedKey.ENCODED_LEN = ok 72#usize := by
  have h : SkippedKey.ENCODED_LEN ⦃ fun r => r = 72#usize ⦄ := by
    unfold SkippedKey.ENCODED_LEN; step*
  obtain ⟨r, hr, hre⟩ := Std.WP.spec_imp_exists h
  rw [hr, hre]

theorem label_byte_zero : LabelSet.from_byte 0#u8 = ok (some LabelSet.Tacenta) := rfl

/-- The zero key is canonical: bit 255 clear, and its last byte is not `0x7f`. -/
theorem canonical_zeros : Tacenta.T1.canonicalX25519 (Std.Array.repeat 32#usize 0#u8) = true := by
  decide

set_option maxHeartbeats 1000000 in
/-- **The translated `from_bytes` accepts `witnessBytes`.** -/
theorem from_bytes_accepts_witness :
    ∃ s, State.from_bytes witnessBytes = ok (core.result.Result.Ok s) := by
  have h : State.from_bytes witnessBytes
      ⦃ fun r => ∃ s, r = core.result.Result.Ok s ⦄ := by
    unfold State.from_bytes
    simp only [fixed_len_eq, optional_key_len_eq, skipped_encoded_len_eq, bind_tc_ok]
    rw [if_neg (by decide), slice_index_eq witnessBytes 0#usize 1#u8 (by decide)]
    simp only [bind_tc_ok]
    rw [if_neg (by simp [STATE_VERSION])]
    step*
    all_goals first
      | (simp only [witnessBytes_val, witnessBytes_length, *]; first | omega | decide)
      | skip
    have hp : pos8.val = 180 := by omega
    have hq : witnessBytes.val[pos8.val]? = some 0#u8 := by
      simp only [witnessBytes_val, hp]; decide
    have hi4 : i4 = 0#u8 := by
      rw [i4_post]
      rw [List.getElem?_eq_getElem
        (h := by rw [hp, witnessBytes_val]; simp [witnessList_length])] at hq
      exact Option.some.inj hq
    rw [hi4, label_byte_zero]
    simp only [bind_tc_ok]
    step*
    all_goals first
      | (simp only [witnessBytes_val, witnessBytes_length, *]; first | omega | decide)
      | skip
    have hsc : skipped_count = 0#usize := by rw [skipped_count_post]; scalar_tac
    rw [hsc]
    step*
    all_goals simp only [Prod.mk.injEq] at pos11_post
    all_goals obtain ⟨h11, hsk, -⟩ := pos11_post
    all_goals subst h11
    all_goals subst hsk
    · exfalso; simp_all
    · rw [invariant_eq]
      simp only [bind_tc_ok]
      split
      · simp
      · exfalso
        -- The label byte's facts would have `simp_all` rewrite the zero byte
        -- as `witnessList[180]`, inside the keys as well, where
        -- `canonical_zeros` no longer matches. Nothing below needs them.
        try clear i4_post
        try clear hi4
        try clear hq
        simp_all [InvB, chainsOk, storeOk, keysOk, canonical_zeros, MAX_SKIPPED_STORE,
          Std.U32.max_eq]
  obtain ⟨r, hr, hre⟩ := Std.WP.spec_imp_exists h
  obtain ⟨s, rfl⟩ := hre
  exact ⟨s, hr⟩

/-- **`from_bytes_establishes_inv` is not vacuous.** Some byte string reaches
`Ok`, and the state it yields satisfies `Inv`, so the implication above has a
witness rather than an empty premise. -/
theorem from_bytes_establishes_inv_nonvacuous :
    ∃ (bytes : Slice Std.U8) (s : State),
      State.from_bytes bytes = ok (core.result.Result.Ok s) ∧ Inv s := by
  obtain ⟨s, hs⟩ := from_bytes_accepts_witness
  exact ⟨witnessBytes, s, hs, from_bytes_establishes_inv witnessBytes s hs⟩

end Witness

/-! ### From `Inv` to the theorems' preconditions -/

/-- The platform-width side of `T1.receive_no_panic`'s `hs`, discharged rather
than assumed. Both quantities are constants -- `MAX_SKIPPED_STORE` is 2000 and
`MAX_SKIP` is 1000 -- and `usize` is at least 32 bits wide on either target
Aeneas models, so the sum fits with room to spare. -/
theorem store_plus_skip_fits :
    MAX_SKIPPED_STORE.val + MAX_SKIP.val ≤ Std.Usize.max := by
  have h := Std.Usize.bounds_eq
  simp only [MAX_SKIPPED_STORE, MAX_SKIP]
  rcases h with h | h <;> simp [h] <;> scalar_tac

/-- `Inv` → `T1.receive_no_panic`'s `hs`.

`hs` asks that the store at its largest, plus the gap one skip can add, still
fits a `usize`. `Inv` collapses "at its largest" to the constant
`MAX_SKIPPED_STORE`, and what remains is `MAX_SKIPPED_STORE + MAX_SKIP`, which
`store_plus_skip_fits` settles at either width. Nothing is left for the caller
to supply. -/
theorem inv_gives_store_bound (s : State) (hi : Inv s) :
    max s.skipped.val.length MAX_SKIPPED_STORE.val + MAX_SKIP.val ≤ Std.Usize.max := by
  have := hi.store_bound
  have := store_plus_skip_fits
  omega

/-- `Inv` → the clock clause: the store's clock is below the `u32` ceiling.

**This is one step short of `T3.receive_refines`'s `hroom`, and stays that
way.** The refinement asks `events + 1 < u32::MAX`, a premise stated when the
model's clock did not stop: at the parked value, `MAX_EVENTS = u32::MAX - 1`,
the core held its clock still and the model's advanced. The model's clock now
stops at the same value (`Model.State.maxEvents`), so the two agree there too;
the premise is kept, and the refinement is still stated below it. The
`invariant` cannot close that step and must not be asked to. A parked clock is
a state the crate's own operations produce, so a clause `events < MAX_EVENTS`
would refuse a state the crate exports -- exactly the defect the clamp
removed. The missing step is taken as an explicit argument on
`decoded_receive_refines` below.

What the clamp did buy is on this side of the ledger. `age_store` now
*preserves* this clause rather than assuming it: `events < u32::MAX` holds of
the state afterwards for any state at all, so it is a property of every state
a run reaches and not only of every state the decoder accepts. -/
theorem inv_gives_clock_room (s : State) (hi : Inv s) : s.events.val < Std.U32.max :=
  hi.clock_room

/-- `Inv` → `T3.receive_refines`'s `hone`: at most one stored key answers any
one header. The store's "map on `(dh, n)`" clause, transported across the
refinement relation; `keyOf` is injective, which is what lets a model-side
collision be pulled back to a translated one. -/
theorem inv_gives_store_is_map (s : State) (m : Model.State.State)
    (hR : Tacenta.T3.StateR s m) (hi : Inv s) (mh : Model.State.Header) :
    (m.skipped.filter (Tacenta.T3.matchesHeader mh)).length ≤ 1 := by
  have hpm : m.skipped.Pairwise (fun a b =>
      (Prod.fst a, Prod.fst (Prod.snd a)) ≠ (Prod.fst b, Prod.fst (Prod.snd b))) := by
    rw [← hR.skipped, List.pairwise_map]
    refine hi.store_map.imp ?_
    intro a b hab
    simp only [Tacenta.T3.skippedOf, ne_eq, Prod.mk.injEq, not_and]
    intro h1 h2
    exact hab ⟨Tacenta.T3.keyOf_inj h1, by scalar_tac⟩
  refine length_filter_le_one_of_pairwise (k := (mh.dh, mh.n)) hpm ?_
  rintro ⟨dh, n, rest⟩ _ hpe
  simp only [Tacenta.T3.matchesHeader, Bool.and_eq_true, beq_iff_eq] at hpe
  simp [hpe.1, hpe.2]

/-! ### The chain, end to end -/

/-- **Decoded state → `Inv` → `hs` → `T1.receive_no_panic`.** A `receive` on a
state that came out of `from_bytes` does not panic. -/
theorem decoded_receive_no_panic (h : Tacenta.T1.HmacTotal) (hk : Tacenta.T1.HkdfTotal)
    (hz : Tacenta.T1.ZeroizingTotal) (hrm : Tacenta.T1.VecRemoveTotal)
    [Tacenta.T1.DerivedKeysModel]
    (bytes : Slice Std.U8) (s : State)
    (hdec : State.from_bytes bytes = ok (core.result.Result.Ok s))
    (header : Header) (dh_out_recv dh_out_send new_dhs_pub : Array Std.U8 32#usize) :
    Tacenta.T1.NoPanic (receive s header dh_out_recv dh_out_send new_dhs_pub) :=
  Tacenta.T1.receive_no_panic h hk hz hrm s header dh_out_recv dh_out_send new_dhs_pub
    (inv_gives_store_bound s (from_bytes_establishes_inv bytes s hdec))

/-- **Decoded state → `Inv` → `hone`, `hs` → `T3.receive_refines`, given a step
of clock headroom.** A `receive` on a state that came out of `from_bytes`
refines the model's, provided the store's clock has not parked.

One premise stays with the caller, and it is an explicit argument rather than
a global assumption, so a reader sees what is being asked.

`hclock_unparked` is the step of headroom `T3.receive_refines`'s `hroom` now
asks for. `age_store` clamps the clock at `MAX_EVENTS = u32::MAX - 1` so that
`invariant`'s clock clause is inductive. The model's clock now stops at the
same value, so the correspondence no longer fails at the parked value, but the
refinement is still stated one step below it. `Inv` reaches `events < u32::MAX` and
no further (`inv_gives_clock_room`), and it cannot be strengthened: a parked
clock is a state this crate's operations produce and its decoder accepts. The
premise is a real restriction and is named as one -- it excludes exactly the
one clock value the crate comes to rest at, which an honest run reaches only
after 2^32 accepted receives.

Panic-freedom carries no such premise: `decoded_receive_no_panic` above is
unconditional in the clock.

The relation to the model state is still a hypothesis too: `from_bytes` says
which translated states are reachable, not which model state a caller
means. -/
theorem decoded_receive_refines (h : Tacenta.T3.HmacAgrees) (hk : Tacenta.T3.HkdfAgrees)
    (hz : Tacenta.T3.ZeroizingRoundTrips) (hrm : Tacenta.T1.VecRemoveTotal)
    [Tacenta.T1.DerivedKeysModel]
    (bytes : Slice Std.U8) (s : State)
    (hdec : State.from_bytes bytes = ok (core.result.Result.Ok s))
    (hclock_unparked : s.events.val + 1 < Std.U32.max)
    (m : Model.State.State) (hR : Tacenta.T3.StateR s m)
    (hdr : Header) (mh : Model.State.Header) (hH : Tacenta.T3.HeaderR hdr mh)
    (dh_out_recv dh_out_send new_dhs_pub : Array Std.U8 32#usize) :
    receive s hdr dh_out_recv dh_out_send new_dhs_pub ⦃ fun r =>
      ∀ mk, r.1 = core.result.Result.Ok mk →
        ∃ m', Model.Ratchet.receive m mh (Tacenta.T3.keyOf dh_out_recv)
              (Tacenta.T3.keyOf dh_out_send) (Tacenta.T3.keyOf new_dhs_pub)
                = some (m', Tacenta.T3.keyOf mk)
          ∧ Tacenta.T3.StateR r.2 m' ⦄ :=
  have hinv := from_bytes_establishes_inv bytes s hdec
  Tacenta.T3.receive_refines h hk hz hrm s m hR hdr mh hH
    dh_out_recv dh_out_send new_dhs_pub
    (inv_gives_store_is_map s m hR hinv mh)
    (inv_gives_store_bound s hinv)
    hclock_unparked

end Ratchet

/-! # `tacenta-spqr`, the sparse ratchet

`State::invariant` (spqr/src/lib.rs) is four clauses over two pairs of nested
index loops: the skipped store is at most `MAX_SKIPPED_STORE`; every chain's
epoch is inside the window `[epoch - EPOCHS_KEPT + 1, epoch]` and no two chains
share an epoch; the current epoch is among them; and every skipped key names a
chain that is present, with no two skipped keys sharing `(epoch, n)`. Five
loops in the translation, characterised one at a time below. -/
namespace Spqr

open tacenta_spqr

/-- The chains loop's per-pair test: two entries collide when their epochs
agree. -/
def chainDup (e : Std.U64) (t : Std.U64 × Chains) : Bool := !decide (t.1 = e)

/-- What the chains loops compute into `chains_ok`, in visit order: the entry is
inside the window, no later entry shares its epoch, and the rest is good. The
window is written exactly as the Rust writes it, `saturating_add` included, so
the characterisation is of the code rather than of an idealisation of it. -/
def chainsOkFrom : List (Std.U64 × Chains) → Std.U64 → Bool
  | [], _ => true
  | q :: rest, ep =>
      decide (q.1.val ≤ ep.val)
        && decide (ep.val < (core.num.U64.saturating_add q.1 EPOCHS_KEPT).val)
        && rest.all (chainDup q.1)
        && chainsOkFrom rest ep

/-- The `current_present` test, and the skipped store's "names a present
chain" test: this entry is at that epoch. -/
def isEpoch (e : Std.U64) (q : Std.U64 × Chains) : Bool := decide (q.1 = e)

/-- The skipped store's per-pair test: two entries collide when both their
epoch and their number agree. -/
def skippedNotDup (a t : Skipped) : Bool :=
  !(decide (a.epoch = t.epoch) && decide (a.n = t.n))

/-- What the skipped loops compute into `skipped_ok`, in visit order. -/
def skippedOkFrom (C : List (Std.U64 × Chains)) : List Skipped → Bool
  | [] => true
  | a :: rest =>
      C.any (isEpoch a.epoch) && rest.all (skippedNotDup a) && skippedOkFrom C rest

/-- Chains, inner loop: no entry from `j` onward shares epoch `e`. -/
theorem chains_inner_eq (v : alloc.vec.Vec (Std.U64 × Chains)) (b : Bool) (e : Std.U64)
    (j : Std.Usize) :
    State.invariant_loop0_loop0 v b e j
      = ok (b && (v.val.drop j.val).all (chainDup e)) := by
  have hspec : State.invariant_loop0_loop0 v b e j ⦃ fun r =>
      r = (b && (v.val.drop j.val).all (chainDup e)) ⦄ := by
    unfold State.invariant_loop0_loop0
    apply loop.spec_decr_nat
      (measure := fun x => v.val.length - (Prod.snd x).val)
      (inv := fun x => ((Prod.fst x) && (v.val.drop (Prod.snd x).val).all (chainDup e))
        = (b && (v.val.drop j.val).all (chainDup e)))
    · rintro ⟨b', j'⟩ hinv
      simp only at hinv
      simp only [State.invariant_loop0_loop0.body]
      by_cases hlt : j'.val < v.val.length
      · step*
        all_goals (try (split <;> step*))
        all_goals (
          refine ⟨?_, by scalar_tac⟩
          rw [List.drop_eq_getElem_cons hlt, ← i1_post] at hinv
          simp only [chainDup, List.all_cons] at hinv
          simp_all)
      · step*
        have hnil : v.val.drop j'.val = [] := List.drop_eq_nil_of_le (by omega)
        rw [hnil] at hinv
        simpa using hinv
    · rfl
  obtain ⟨r, hr, hre⟩ := Std.WP.spec_imp_exists hspec
  rw [hr, hre]

/-- Chains, outer loop. It returns the two vectors it was reading unchanged,
`chains_ok` conjoined with `chainsOkFrom` of the suffix still to scan, and
`current_present` disjoined with whether the suffix holds the current epoch. -/
theorem chains_outer_eq (self : State) (b cp : Bool) (i : Std.Usize) :
    State.invariant_loop0 self b cp i
      = ok (self.chains, self.skipped,
          (b && chainsOkFrom (self.chains.val.drop i.val) self.epoch),
          (cp || (self.chains.val.drop i.val).any (isEpoch self.epoch))) := by
  have hspec : State.invariant_loop0 self b cp i ⦃ fun r =>
      r = (self.chains, self.skipped,
          (b && chainsOkFrom (self.chains.val.drop i.val) self.epoch),
          (cp || (self.chains.val.drop i.val).any (isEpoch self.epoch))) ⦄ := by
    unfold State.invariant_loop0
    apply loop.spec_decr_nat
      (measure := fun x => self.chains.val.length - (Prod.snd (Prod.snd x)).val)
      (inv := fun x =>
        ((Prod.fst x)
            && chainsOkFrom (self.chains.val.drop (Prod.snd (Prod.snd x)).val) self.epoch)
          = (b && chainsOkFrom (self.chains.val.drop i.val) self.epoch)
        ∧ ((Prod.fst (Prod.snd x))
            || (self.chains.val.drop (Prod.snd (Prod.snd x)).val).any (isEpoch self.epoch))
          = (cp || (self.chains.val.drop i.val).any (isEpoch self.epoch)))
    · rintro ⟨b', cp', i'⟩ ⟨hinv1, hinv2⟩
      simp only at hinv1 hinv2
      simp only [State.invariant_loop0.body]
      by_cases hlt : i'.val < self.chains.val.length
      · step*
        have h1 : (if e = self.epoch then (ok true : Result Bool) else ok cp')
            = ok (cp' || decide (e = self.epoch)) := by
          by_cases hq : e = self.epoch
          · rw [if_pos hq]; simp [hq]
          · rw [if_neg hq]; simp [hq]
        have h2 : (if e > self.epoch then (ok false : Result Bool)
              else do
                let i2 ← lift (core.num.U64.saturating_add e EPOCHS_KEPT)
                if self.epoch ≥ i2 then ok false else ok b')
            = ok (b' && decide (e.val ≤ self.epoch.val)
                && decide (self.epoch.val
                    < (core.num.U64.saturating_add e EPOCHS_KEPT).val)) := by
          by_cases hq : e > self.epoch
          · rw [if_pos hq]
            have hd : decide (e.val ≤ self.epoch.val) = false := by
              simp only [decide_eq_false_iff_not, Nat.not_le]; scalar_tac
            simp [hd]
          · rw [if_neg hq]
            simp only [lift, bind_tc_ok]
            have hle : decide (e.val ≤ self.epoch.val) = true := by
              simp only [decide_eq_true_eq]; scalar_tac
            by_cases hq2 : self.epoch ≥ core.num.U64.saturating_add e EPOCHS_KEPT
            · rw [if_pos hq2]
              have hd : decide (self.epoch.val
                  < (core.num.U64.saturating_add e EPOCHS_KEPT).val) = false := by
                simp only [decide_eq_false_iff_not, Nat.not_lt]; scalar_tac
              simp [hle, hd]
            · rw [if_neg hq2]
              have hd : decide (self.epoch.val
                  < (core.num.U64.saturating_add e EPOCHS_KEPT).val) = true := by
                simp only [decide_eq_true_eq]; scalar_tac
              simp [hle, hd]
        rw [h1]
        step*
        rw [h2]
        step*
        rw [chains_inner_eq]
        step*
        refine ⟨?_, ?_, by scalar_tac⟩
        · rw [List.drop_eq_getElem_cons hlt, ← e_post] at hinv1
          simp only [chainsOkFrom] at hinv1
          simp_all [Bool.and_assoc]
        · rw [List.drop_eq_getElem_cons hlt, ← e_post] at hinv2
          simp only [List.any_cons, isEpoch] at hinv2
          simp_all [Bool.or_assoc]
      · step*
        have hnil : self.chains.val.drop i'.val = [] := List.drop_eq_nil_of_le (by omega)
        rw [hnil] at hinv1 hinv2
        simp only [chainsOkFrom, List.any_nil, Bool.and_true, Bool.or_false] at hinv1 hinv2
        rw [hinv1, hinv2]
        exact ⟨rfl, rfl⟩
    · exact ⟨rfl, rfl⟩
  obtain ⟨r, hr, hre⟩ := Std.WP.spec_imp_exists hspec
  rw [hr, hre]

/-- Skipped store, presence loop: the flag becomes true exactly when some chain
is at this skipped key's epoch. It scans the whole chains vector from `k`, and
re-reads skipped entry `i` on every iteration, so it carries `i`'s bound. -/
theorem present_eq (v : alloc.vec.Vec (Std.U64 × Chains)) (v1 : alloc.vec.Vec Skipped)
    (i : Std.Usize) (hi : i.val < v1.val.length) (p : Bool) (k : Std.Usize) :
    State.invariant_loop1_loop0 v v1 i p k
      = ok (p || (v.val.drop k.val).any (isEpoch (v1.val[i.val]'hi).epoch)) := by
  have hspec : State.invariant_loop1_loop0 v v1 i p k ⦃ fun r =>
      r = (p || (v.val.drop k.val).any (isEpoch (v1.val[i.val]'hi).epoch)) ⦄ := by
    unfold State.invariant_loop1_loop0
    apply loop.spec_decr_nat
      (measure := fun x => v.val.length - (Prod.snd x).val)
      (inv := fun x => ((Prod.fst x)
          || (v.val.drop (Prod.snd x).val).any (isEpoch (v1.val[i.val]'hi).epoch))
        = (p || (v.val.drop k.val).any (isEpoch (v1.val[i.val]'hi).epoch)))
    · rintro ⟨p', k'⟩ hinv
      simp only at hinv
      simp only [State.invariant_loop1_loop0.body]
      by_cases hlt : k'.val < v.val.length
      · step*
        all_goals (try (split <;> step*))
        all_goals (
          refine ⟨?_, by scalar_tac⟩
          rw [List.drop_eq_getElem_cons hlt, ← i2_post] at hinv
          simp only [isEpoch, List.any_cons] at hinv
          simp_all)
      · step*
        have hnil : v.val.drop k'.val = [] := List.drop_eq_nil_of_le (by omega)
        rw [hnil] at hinv
        simpa using hinv
    · rfl
  obtain ⟨r, hr, hre⟩ := Std.WP.spec_imp_exists hspec
  rw [hr, hre]

/-- Skipped store, inner loop: no entry from `j` onward collides with entry
`i` on `(epoch, n)`. -/
theorem skipped_inner_eq (v : alloc.vec.Vec Skipped) (b : Bool) (i : Std.Usize)
    (hi : i.val < v.val.length) (j : Std.Usize) :
    State.invariant_loop1_loop1 v b i j
      = ok (b && (v.val.drop j.val).all (skippedNotDup (v.val[i.val]'hi))) := by
  have hspec : State.invariant_loop1_loop1 v b i j ⦃ fun r =>
      r = (b && (v.val.drop j.val).all (skippedNotDup (v.val[i.val]'hi))) ⦄ := by
    unfold State.invariant_loop1_loop1
    apply loop.spec_decr_nat
      (measure := fun x => v.val.length - (Prod.snd x).val)
      (inv := fun x => ((Prod.fst x)
          && (v.val.drop (Prod.snd x).val).all (skippedNotDup (v.val[i.val]'hi)))
        = (b && (v.val.drop j.val).all (skippedNotDup (v.val[i.val]'hi))))
    · rintro ⟨b', j'⟩ hinv
      simp only at hinv
      simp only [State.invariant_loop1_loop1.body]
      by_cases hlt : j'.val < v.val.length
      · step*
        all_goals (try (split <;> step*))
        all_goals (try (split <;> step*))
        all_goals (
          refine ⟨?_, by scalar_tac⟩
          rw [List.drop_eq_getElem_cons hlt] at hinv
          simp only [skippedNotDup, List.all_cons] at hinv
          simp_all)
      · step*
        have hnil : v.val.drop j'.val = [] := List.drop_eq_nil_of_le (by omega)
        rw [hnil] at hinv
        simpa using hinv
    · rfl
  obtain ⟨r, hr, hre⟩ := Std.WP.spec_imp_exists hspec
  rw [hr, hre]

/-- Skipped store, outer loop. -/
theorem skipped_outer_eq (v : alloc.vec.Vec (Std.U64 × Chains))
    (v1 : alloc.vec.Vec Skipped) (b : Bool) (i : Std.Usize) :
    State.invariant_loop1 v v1 b i
      = ok (b && skippedOkFrom v.val (v1.val.drop i.val)) := by
  have hspec : State.invariant_loop1 v v1 b i ⦃ fun r =>
      r = (b && skippedOkFrom v.val (v1.val.drop i.val)) ⦄ := by
    unfold State.invariant_loop1
    apply loop.spec_decr_nat
      (measure := fun x => v1.val.length - (Prod.snd x).val)
      (inv := fun x => ((Prod.fst x) && skippedOkFrom v.val (v1.val.drop (Prod.snd x).val))
        = (b && skippedOkFrom v.val (v1.val.drop i.val)))
    · rintro ⟨b', i'⟩ hinv
      simp only at hinv
      simp only [State.invariant_loop1.body]
      by_cases hlt : i'.val < v1.val.length
      · rw [present_eq v v1 i' hlt]
        step*
        rw [show ∀ P : Bool, (if P = true then (ok b' : Result Bool) else ok false)
              = ok (b' && P) from fun P => by cases P <;> simp]
        step*
        rw [skipped_inner_eq v1 _ i' hlt]
        step*
        refine ⟨?_, by scalar_tac⟩
        rw [List.drop_eq_getElem_cons hlt] at hinv
        simp only [skippedOkFrom] at hinv
        simp_all [Bool.and_assoc]
      · rw [if_neg (show ¬ (i' < alloc.vec.Vec.len v1) by scalar_tac)]
        have hnil : v1.val.drop i'.val = [] := List.drop_eq_nil_of_le (by omega)
        rw [hnil] at hinv
        simpa [skippedOkFrom] using hinv
    · rfl
  obtain ⟨r, hr, hre⟩ := Std.WP.spec_imp_exists hspec
  rw [hr, hre]

/-- The whole predicate as the Bool the translated `invariant` returns. -/
def InvB (s : State) : Bool :=
  decide (s.skipped.val.length ≤ MAX_SKIPPED_STORE.val)
    && chainsOkFrom s.chains.val s.epoch
    && s.chains.val.any (isEpoch s.epoch)
    && skippedOkFrom s.chains.val s.skipped.val

/-- **The translated `invariant` computes `InvB`, on every state.** -/
theorem invariant_eq (s : State) : State.invariant s = ok (InvB s) := by
  have h : State.invariant s ⦃ fun r => r = InvB s ⦄ := by
    unfold State.invariant
    rw [chains_outer_eq s true false 0#usize]
    step*
    rw [skipped_outer_eq]
    step*
    all_goals simp_all [InvB]
  obtain ⟨r, hr, hre⟩ := Std.WP.spec_imp_exists h
  rw [hr, hre]

/-- The Rust `invariant`'s clauses as a proposition about the translated
state. -/
structure Inv (s : State) : Prop where
  store_bound : s.skipped.val.length ≤ MAX_SKIPPED_STORE.val
  epoch_window : ∀ q ∈ s.chains.val, q.1.val ≤ s.epoch.val ∧
    s.epoch.val < (core.num.U64.saturating_add q.1 EPOCHS_KEPT).val
  chains_distinct : s.chains.val.Pairwise (fun a b => a.1 ≠ b.1)
  current_present : ∃ q ∈ s.chains.val, q.1 = s.epoch
  skipped_chained : ∀ a ∈ s.skipped.val, ∃ q ∈ s.chains.val, q.1 = a.epoch
  skipped_map : s.skipped.val.Pairwise (fun a b => ¬ (a.epoch = b.epoch ∧ a.n = b.n))

/-- The chains flag, as the two propositions it stands for. -/
theorem chainsOkFrom_iff (L : List (Std.U64 × Chains)) (ep : Std.U64) :
    chainsOkFrom L ep = true ↔
      ((∀ q ∈ L, q.1.val ≤ ep.val ∧
          ep.val < (core.num.U64.saturating_add q.1 EPOCHS_KEPT).val)
        ∧ L.Pairwise (fun a b => a.1 ≠ b.1)) := by
  induction L with
  | nil => simp [chainsOkFrom]
  | cons a rest ih =>
    simp only [chainsOkFrom, chainDup, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
      Bool.not_eq_true', decide_eq_false_iff_not, List.pairwise_cons, List.mem_cons,
      forall_eq_or_imp, ih]
    constructor
    · rintro ⟨⟨⟨h1, h2⟩, hnd⟩, hall, hp⟩
      exact ⟨⟨⟨h1, h2⟩, hall⟩, fun t ht => fun hEq => hnd t ht hEq.symm, hp⟩
    · rintro ⟨⟨⟨h1, h2⟩, hall⟩, hnd, hp⟩
      exact ⟨⟨⟨h1, h2⟩, fun t ht => fun hEq => hnd t ht hEq.symm⟩, hall, hp⟩

/-- The skipped flag, as the two propositions it stands for. -/
theorem skippedOkFrom_iff (C : List (Std.U64 × Chains)) (L : List Skipped) :
    skippedOkFrom C L = true ↔
      ((∀ a ∈ L, ∃ q ∈ C, q.1 = a.epoch)
        ∧ L.Pairwise (fun a b => ¬ (a.epoch = b.epoch ∧ a.n = b.n))) := by
  induction L with
  | nil => simp [skippedOkFrom]
  | cons a rest ih =>
    simp only [skippedOkFrom, skippedNotDup, isEpoch, Bool.and_eq_true, List.any_eq_true,
      List.all_eq_true, Bool.not_eq_true', Bool.and_eq_false_imp, decide_eq_true_eq,
      List.pairwise_cons, List.mem_cons, forall_eq_or_imp, ih]
    constructor
    · rintro ⟨⟨hpres, hnd⟩, hall, hp⟩
      refine ⟨⟨hpres, hall⟩, ?_, hp⟩
      intro t ht ⟨h1, h2⟩
      have := hnd t ht
      simp_all
    · rintro ⟨⟨hpres, hall⟩, hnd, hp⟩
      refine ⟨⟨hpres, ?_⟩, hall, hp⟩
      intro t ht
      have := hnd t ht
      simp_all

/-- **The translated `invariant` returns `true` exactly on states satisfying
`Inv`.** -/
theorem invariant_true_iff (s : State) : State.invariant s = ok true ↔ Inv s := by
  rw [invariant_eq]
  simp only [ok.injEq, InvB, Bool.and_eq_true, decide_eq_true_eq, chainsOkFrom_iff,
    skippedOkFrom_iff, List.any_eq_true, isEpoch]
  constructor
  · rintro ⟨⟨⟨hb, hw, hd⟩, hcp⟩, hsc, hsm⟩
    exact ⟨hb, hw, hd, hcp, hsc, hsm⟩
  · rintro ⟨hb, hw, hd, hcp, hsc, hsm⟩
    exact ⟨⟨⟨hb, hw, hd⟩, hcp⟩, hsc, hsm⟩

/-- **A state the translated `from_bytes` returns satisfies `Inv`.** As for the
ratchet: no assumption, the hypothesis is that the decoder returned. -/
theorem from_bytes_establishes_inv (bytes : Slice Std.U8) (s : State)
    (h : State.from_bytes bytes = ok (core.result.Result.Ok s)) : Inv s := by
  rw [← invariant_true_iff]
  rw [State.from_bytes] at h
  repeat' first
    | (replace h := bind3_eq_ok_inv h; obtain ⟨_, _, _, _, h⟩ := h)
    | (replace h := bind2_eq_ok_inv h; obtain ⟨_, _, _, h⟩ := h)
    | (replace h := bind_eq_ok_inv h; obtain ⟨_, _, h⟩ := h)
    | split at h
    | simp at h
  all_goals (subst h; simp_all)

/-! ### From `Inv` to the theorems' preconditions -/

/-- A saturating sum is at most the true sum. Used to read the epoch window as
an arithmetic bound: `epoch < saturating_add e EPOCHS_KEPT` gives
`epoch < e + EPOCHS_KEPT` whether or not the addition saturated. -/
theorem saturating_add_val_le {ty : Std.UScalarTy} (x y : Std.UScalar ty) :
    (Std.UScalar.saturating_add x y).val ≤ x.val + y.val := by
  simp only [Std.UScalar.saturating_add, Std.UScalar.val, BitVec.toNat_ofNat]
  exact le_trans (Nat.mod_le _ _) (min_le_right _ _)

/-- `Inv` → the epoch is below the `u64` ceiling. The current epoch is among
the chains, and every chain's epoch is strictly below its own saturating
window end, which is at most `u64::MAX`.

**This is no longer `SpqrT3.receive_refines`'s `hepoch`, and cannot be made
into it.** That premise is now `epoch + 1 < u64::MAX`, one step tighter:
`advance` refuses the step that would install `u64::MAX`, because
`clear_old_epochs`'s window would retire every chain at that epoch including
the one just opened, leaving a state this crate's own decoder refuses. The
model now refuses there too. `receive_refines`'s failure clause takes any
error, so its correspondence may hold there, but `advance_refines`, on which
its proof rests, names `EpochOutOfOrder` and fails at `epoch = u64::MAX - 1`;
whether `hepoch` could be dropped from `receive_refines` has not been checked. `Inv` admits that state -- a chain at its own epoch,
inside the window, every clause satisfied -- so the gap is in the predicate
and not in how this lemma is stated. `hepoch` therefore joins `hcb`, `hsb`,
`hnewb` and `hcounter` on the carried list; see `decoded_receive_no_panic`
below.

What this lemma is for, then, is the statement itself: it is one of the facts
about a decoded state this file records, and `SpqrT3.lean`'s closing note
names it. It discharges no premise of the corollary below, because
`SpqrT1.receive_no_panic` takes no epoch bound at all -- every epoch and
counter increment there is a `checked_add` whose `None` arm the proof walks.
The two lemmas that do feed that corollary are `inv_gives_chain_room` and
`inv_gives_skip_room`. -/
theorem inv_gives_epoch_room (s : State) (hi : Inv s) : s.epoch.val < Std.U64.max := by
  obtain ⟨q, hq, -⟩ := hi.current_present
  have h2 := (hi.epoch_window q hq).2
  have h3 : (core.num.U64.saturating_add q.1 EPOCHS_KEPT).val ≤ Std.U64.max := by scalar_tac
  omega

/-- `Inv` bounds the chains vector at two entries.

Every chain's epoch is at most the current one and strictly greater than
`epoch - EPOCHS_KEPT`, which for `EPOCHS_KEPT = 2` leaves two possible values;
the entries are pairwise distinct on epoch, so there are at most two of them.
This is the crate's retention policy, read back off the invariant. -/
theorem inv_gives_chains_len (s : State) (hi : Inv s) : s.chains.val.length ≤ 2 := by
  have hnodup : (s.chains.val.map (fun q => q.1.val)).Nodup := by
    rw [List.Nodup, List.pairwise_map]
    refine hi.chains_distinct.imp ?_
    intro a b hab hEq
    exact hab (by scalar_tac)
  have hsubset : (s.chains.val.map (fun q => q.1.val))
      ⊆ [s.epoch.val - 1, s.epoch.val] := by
    intro x hx
    simp only [List.mem_map] at hx
    obtain ⟨q, hq, rfl⟩ := hx
    obtain ⟨h1, h2⟩ := hi.epoch_window q hq
    have h3 : (core.num.U64.saturating_add q.1 EPOCHS_KEPT).val
        ≤ q.1.val + EPOCHS_KEPT.val := saturating_add_val_le q.1 EPOCHS_KEPT
    have h4 : (EPOCHS_KEPT : Std.U64).val = 2 := by simp [EPOCHS_KEPT]
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    omega
  have := (List.subperm_of_subset hnodup hsubset).length_le
  simpa using this

/-- `Inv` → `SpqrT1.receive_no_panic`'s `hroom`, with nothing left over: two
chains plus the two `set_chains` calls on the path is four, and `usize` is at
least 32 bits wide on every target Aeneas models. -/
theorem inv_gives_chain_room (s : State) (hi : Inv s) :
    s.chains.val.length + 2 < Std.Usize.max := by
  have h := inv_gives_chains_len s hi
  have h4 : 4 < Std.Usize.max := by
    rcases Std.Usize.bounds_eq with hb | hb <;> rw [hb] <;>
      simp [Std.U32.max_eq, Std.U64.max_eq]
  omega

/-- `Inv` → `SpqrT1.receive_no_panic`'s `hskiproom`, likewise with nothing left
over: 2000 stored keys plus `MAX_SKIP` is 3000. -/
theorem inv_gives_skip_room (s : State) (hi : Inv s) :
    s.skipped.val.length + MAX_SKIP.val ≤ Std.Usize.max := by
  have h := hi.store_bound
  have hm : MAX_SKIPPED_STORE.val = 2000 := by simp [MAX_SKIPPED_STORE]
  have hk : MAX_SKIP.val = 1000 := by simp [MAX_SKIP]
  have h4 : 3000 ≤ Std.Usize.max := by
    rcases Std.Usize.bounds_eq with hb | hb <;> rw [hb] <;>
      simp [Std.U32.max_eq, Std.U64.max_eq]
  omega

/-- `Inv` → `SpqrT3.receive_refines`'s `hone`: at most one stored key answers
any one `(epoch, n)`. -/
theorem inv_gives_store_is_map (s : State) (m : Model.SparseRatchet.State)
    (hR : Tacenta.SpqrT3.StateRefines s m) (hi : Inv s) (e n : Std.U64) :
    (m.skipped.filter (fun x => x.1 == e.val && x.2.1 == n.val)).length ≤ 1 := by
  have hpm : m.skipped.Pairwise (fun a b =>
      (Prod.fst a, Prod.fst (Prod.snd a)) ≠ (Prod.fst b, Prod.fst (Prod.snd b))) := by
    rw [← hR.skipped, List.pairwise_map]
    refine hi.skipped_map.imp ?_
    intro a b hab
    simp only [Tacenta.SpqrT3.skippedOf, ne_eq, Prod.mk.injEq, not_and]
    intro h1 h2
    exact hab ⟨by scalar_tac, by scalar_tac⟩
  refine length_filter_le_one_of_pairwise (k := (e.val, n.val)) hpm ?_
  rintro ⟨a, b, c⟩ _ hpe
  simp only [Bool.and_eq_true, beq_iff_eq] at hpe
  simp [hpe.1, hpe.2]

/-! ### The chain, end to end -/

/-- **Decoded state → `Inv` → `hroom`, `hskiproom` → `SpqrT1.receive_no_panic`.**
A `receive` on a state that came out of `from_bytes` does not panic, with no
side condition left for a caller to discharge.

There is deliberately no `decoded_receive_refines` beside it. `SpqrT3`'s
refinement takes eight premises, and three of them are supplied above:
`hroom` (`inv_gives_chain_room`), `hskiproom` (`inv_gives_skip_room`) and
`hone` (`inv_gives_store_is_map`). The remaining five -- `hepoch`, `hcb`,
`hsb`, `hnewb` and `hcounter` -- are not consequences of this crate's
`invariant`: a state with `epoch = u64::MAX - 1` and a chain at that epoch
passes `invariant` and fails both `hepoch` and `hcb`. `hepoch` is on that
list because it now reads `epoch + 1 < u64::MAX`: `advance` reserves
`u64::MAX` and refuses the step that would reach it, while
`epoch = u64::MAX - 1` stays a fully usable epoch that the operations produce
and the decoder accepts, so the step of headroom is the caller's to supply.
The five are recorded as open in `CLAIMS.md`. -/
theorem decoded_receive_no_panic (hret : Tacenta.SpqrT1.VecRetainTotal)
    (hrk : Tacenta.SpqrT1.KdfRkTotal) (hz : Tacenta.SpqrT1.ZeroizeTotal)
    (hkdf : Tacenta.SpqrT1.KdfCkTotal) (hopt : Tacenta.SpqrT1.OptionCloneTotal)
    (hrm : Tacenta.SpqrT1.VecRemoveTotal) (happ : Tacenta.SpqrT1.VecAppendTotal)
    (bytes : Slice Std.U8) (s : State)
    (hdec : State.from_bytes bytes = ok (core.result.Result.Ok s))
    (receiving_epoch n : Std.U64) (out : Option Output) :
    State.receive s receiving_epoch out n ⦃ fun _ => True ⦄ :=
  have hinv := from_bytes_establishes_inv bytes s hdec
  Tacenta.SpqrT1.receive_no_panic hret hrk hz hkdf hopt hrm happ s receiving_epoch n out
    (inv_gives_chain_room s hinv) (inv_gives_skip_room s hinv)

end Spqr

/-! # `tacenta-braid`

The Braid's `invariant` is a twelve-way match whose arms mostly delegate to
`tacenta-erasure`'s `Encoder::invariant` and `Decoder::invariant`. Those are a
different crate, and reach this translation as opaque axioms, so there is no
unfolding them here and no full `Inv` to state. What can be read off the arms
directly is the clause the T1 and T3 theorems actually take as a premise: the
KEM ciphertext held across the encapsulation exchange is `CT1_LEN` long, and
`CT1_LEN` is within the 4096 that `State.ct1_bounded` asks for. -/
namespace Braid

open tacenta_braid

/-- What this module derives for the Braid: a partial mirror of the Rust
`invariant`, holding the one clause the theorems need. Deliberately not the
whole predicate -- the rest of it is about the erasure coders, which are
opaque here. -/
structure Inv (b : Braid) : Prop where
  ct1_bounded : Tacenta.BraidT1.State.ct1_bounded b.state

/-- **The translated `invariant` returning `true` implies `Inv`.** One
direction, which is the direction the constructor needs; the converse would
have to characterise the opaque erasure invariants and is not available.

`Ct1LenTotal` is `BraidT1`'s existing hypothesis, not a new one: it says
`tacenta_kem::CT1_LEN` returns a value at most 4096, and the real constant is
1408. -/
theorem invariant_true_gives_inv (hct1 : Tacenta.BraidT1.Ct1LenTotal) (b : Braid)
    (h : Braid.invariant b = ok true) : Inv b := by
  obtain ⟨v, hv, hvle⟩ := hct1
  constructor
  rw [Braid.invariant] at h
  rcases hst : b.state with _|_|_|_|_|_|_|_|_|_|_|_ <;>
    rw [hst] at h <;> simp only [Tacenta.BraidT1.State.ct1_bounded]
  all_goals (
    simp only [hv, bind_tc_ok] at h
    repeat' first
      | (replace h := bind_eq_ok_inv h; obtain ⟨_, _, h⟩ := h)
      | split at h
      | simp at h
    all_goals scalar_tac)

/-- **The translated `from_bytes` only returns a state its `invariant`
accepts.** -/
theorem from_bytes_establishes_invariant (bytes : Slice Std.U8) (b : Braid)
    (h : Braid.from_bytes bytes = ok (core.result.Result.Ok b)) :
    Braid.invariant b = ok true := by
  rw [Braid.from_bytes] at h
  split at h
  · simp at h
  · replace h := bind_eq_ok_inv h
    obtain ⟨_, _, h⟩ := h
    split at h
    · simp at h
    · replace h := bind_eq_ok_inv h
      obtain ⟨_, _, h⟩ := h
      replace h := bind_eq_ok_inv h
      obtain ⟨o, _, h⟩ := h
      rcases o with _ | ⟨st, pos⟩
      · simp at h
      · simp at h
        split at h
        · replace h := bind_eq_ok_inv h
          obtain ⟨bb, hbb, h⟩ := h
          split at h
          · simp only [ok.injEq, core.result.Result.Ok.injEq] at h
            subst h
            simp_all
          · simp at h
        · simp at h

/-- **A Braid the translated `from_bytes` returns satisfies `Inv`.** -/
theorem from_bytes_establishes_inv (hct1 : Tacenta.BraidT1.Ct1LenTotal)
    (bytes : Slice Std.U8) (b : Braid)
    (h : Braid.from_bytes bytes = ok (core.result.Result.Ok b)) : Inv b :=
  invariant_true_gives_inv hct1 b (from_bytes_establishes_invariant bytes b h)

open Tacenta.BraidT1 in
/-- **Decoded Braid → `Inv` → `ct1_bounded` → `BraidT1.Braid.receive_no_panic`.**

No `decoded_step_receive_refines` beside it: `BraidT3.step_receive_refines`
also asks for `hepoch`, which the Rust `invariant` does not check -- it checks
`epoch >= 1` and nothing above. That premise stays with the caller.

`hepoch` now reads `epoch + 1 < u64::MAX`, a step of headroom rather than the
plain ceiling bound: transitions (5) and (13) refuse the step that would reach
the reserved `u64::MAX`. `Model.Braid` now refuses it too; the premise dates
from when the model took that step, and whether `step_receive_refines` holds
without it has not been checked. So
`epoch < u64::MAX` has become a property of every state a run reaches -- the
transitions keep it and `read_epoch` refuses it on the way in, which is what
makes the decoder's refusal a consistency check rather than a policy -- but it
is still not derivable from `invariant`, and it is in any case one step short
of what the refinement asks. -/
theorem decoded_receive_no_panic (hdnew : DecoderNewTotal) (hdadd : DecoderAddChunkTotal)
    (hdmsg : DecoderMessageTotal) (hct1len : Ct1LenTotal) (hct2len : Ct2LenTotal)
    (hhdrlen : HeaderLenTotal) (hekveclen : EkVectorLenTotal) (hekvec : KeyPairEkVectorTotal)
    (henew : EncoderNewTotal) (hdecap : KeyPairDecapsulateTotal) (hkdf : HkdfSha256Total)
    (hmac : HmacSha256Total) (hvalek : ValidateEkTotal) (hencaps2 : Encapsulate2Total)
    (henc : EncoderCloneTotal) (hdec : DecoderCloneTotal) (hkp : KeyPairCloneTotal)
    (hes : EncapsStateCloneTotal) (hopt : OptionCloneTotal)
    (hz : ZeroizingArrayRoundTrip) (hzz : ArrayZeroizeTotal) (hrf : RangeFullIndexTotal)
    (bytes : Slice Std.U8) (self : Braid)
    (hdec' : Braid.from_bytes bytes = ok (core.result.Result.Ok self)) (msg : Msg) :
    Braid.receive self msg ⦃ fun _ => True ⦄ :=
  Braid.receive_no_panic hdnew hdadd hdmsg hct1len hct2len hhdrlen hekveclen hekvec henew
    hdecap hkdf hmac hvalek hencaps2 henc hdec hkp hes hopt hz hzz hrf self msg
    (from_bytes_establishes_inv hct1len bytes self hdec').ct1_bounded

end Braid

/-! ## The axiom audit, enforced rather than asserted

Read the scope of each sentence off the pin it belongs to.

**The `invariant`/`from_bytes` half.** The ratchet's and the sparse ratchet's
`invariant_true_iff` and `from_bytes_establishes_inv`, and the ratchet's
witness that the second of those is not vacuous, rest on Lean's three standard
axioms and on nothing else: no opaque primitive, no compiler trust, and no
assumption about our own code. That is a statement about those five theorems.
The Braid's `from_bytes_establishes_inv` pulls in the KEM constants and the
erasure coders, which are what the translated Braid calls and cannot see
inside -- among them the key pair's `header` and `ek_vector` and the KEM's
`validate_ek`, which the `invariant`'s key-pair clause calls; that list is
pinned so a new one fails here rather than passing unnoticed.

**The end-to-end half is different, and is pinned separately.** Each
`decoded_*` corollary composes one of those theorems with a `receive` theorem
from `T1`/`T3`, and a `receive` calls the KDF, the `zeroize` wrapper and the
`Vec` operations Aeneas does not model. Every one of those reaches this
translation as an opaque axiom, so a corollary's base is the base of the
`receive` theorem it composes with: eleven `tacenta_ratchet.*` constants for
the ratchet's two, ten `tacenta_spqr.*` constants **plus one compiler-trust
axiom** for the sparse ratchet's, and the erasure coders and KEM constants for
the Braid's. Saying only the first paragraph would over-read the file, so the
corollaries carry pins of their own below and a widening anywhere along the
chain fails here.

**The one compiler-trust axiom, named rather than only listed.**
`Spqr.decoded_receive_no_panic` carries
`Tacenta.SpqrT1.receive_no_panic._native.native_decide.ax_1_1`. It is not new
and is not this file's: it is inherited from `SpqrT1.receive_no_panic`, whose
proof settles one closed numeric fact (that `(1 : U64)` has value one) with
`native_decide`, so the Lean compiler's evaluation is trusted where the kernel
would otherwise check. `LIMITATIONS.md` counts that use among the fourteen
inside translation theorems. What is new here is where it surfaces: the
end-to-end statement "a `receive` on a decoded sparse-ratchet state does not
panic" is compiler-trusted, not kernel-only, and no other statement in this
file is. -/
/-- info: 'Tacenta.ImportInv.Ratchet.invariant_true_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Tacenta.ImportInv.Ratchet.invariant_true_iff

/-- info: 'Tacenta.ImportInv.Ratchet.from_bytes_establishes_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Tacenta.ImportInv.Ratchet.from_bytes_establishes_inv

/-- info: 'Tacenta.ImportInv.Ratchet.from_bytes_accepts_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Tacenta.ImportInv.Ratchet.from_bytes_accepts_witness

/--
info: 'Tacenta.ImportInv.Ratchet.from_bytes_establishes_inv_nonvacuous' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.ImportInv.Ratchet.from_bytes_establishes_inv_nonvacuous

/-- info: 'Tacenta.ImportInv.Spqr.invariant_true_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Tacenta.ImportInv.Spqr.invariant_true_iff

/-- info: 'Tacenta.ImportInv.Spqr.from_bytes_establishes_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Tacenta.ImportInv.Spqr.from_bytes_establishes_inv

/--
info: 'Tacenta.ImportInv.Braid.from_bytes_establishes_inv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_braid.tacenta_erasure.Decoder,
 tacenta_braid.tacenta_erasure.Encoder,
 tacenta_braid.tacenta_erasure.chunk_count,
 tacenta_braid.tacenta_kem.CT1_LEN,
 tacenta_braid.tacenta_kem.CT2_LEN,
 tacenta_braid.tacenta_kem.EK_VECTOR_LEN,
 tacenta_braid.tacenta_kem.EncapsState,
 tacenta_braid.tacenta_kem.HEADER_LEN,
 tacenta_braid.tacenta_kem.IncrementalKeyPair,
 tacenta_braid.tacenta_kem.validate_ek,
 tacenta_braid.tacenta_erasure.Decoder.from_bytes,
 tacenta_braid.tacenta_erasure.Decoder.invariant,
 tacenta_braid.tacenta_erasure.Decoder.size,
 tacenta_braid.tacenta_erasure.Encoder.from_bytes,
 tacenta_braid.tacenta_erasure.Encoder.invariant,
 tacenta_braid.tacenta_erasure.Encoder.needed,
 tacenta_braid.tacenta_kem.EncapsState.from_bytes,
 tacenta_braid.tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_braid.tacenta_kem.IncrementalKeyPair.from_bytes,
 tacenta_braid.tacenta_kem.IncrementalKeyPair.header]
-/
#guard_msgs in
#print axioms Tacenta.ImportInv.Braid.from_bytes_establishes_inv

-- The end-to-end corollaries, pinned in their own right. Each is the
-- composition above, so each carries the boundary axioms its `receive`
-- theorem carries; none of these lists is a claim of kernel-only.
/--
info: 'Tacenta.ImportInv.Ratchet.decoded_receive_no_panic' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_ratchet.tacenta_kdf.hkdf_sha256,
 tacenta_ratchet.tacenta_kdf.hmac_sha256,
 tacenta_ratchet.zeroize.Zeroizing,
 tacenta_ratchet.zeroize.Zeroizing.new,
 tacenta_ratchet.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_ratchet.Pair.Insts.ZeroizeZeroize.zeroize,
 tacenta_ratchet.alloc.vec.Vec.remove,
 tacenta_ratchet.zeroize.Zeroize.Blanket.zeroize,
 tacenta_ratchet.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 tacenta_ratchet.zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 tacenta_ratchet.alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize]
-/
#guard_msgs in
#print axioms Tacenta.ImportInv.Ratchet.decoded_receive_no_panic

/--
info: 'Tacenta.ImportInv.Ratchet.decoded_receive_refines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_ratchet.tacenta_kdf.hkdf_sha256,
 tacenta_ratchet.tacenta_kdf.hmac_sha256,
 tacenta_ratchet.zeroize.Zeroizing,
 tacenta_ratchet.zeroize.Zeroizing.new,
 tacenta_ratchet.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_ratchet.Pair.Insts.ZeroizeZeroize.zeroize,
 tacenta_ratchet.alloc.vec.Vec.remove,
 tacenta_ratchet.zeroize.Zeroize.Blanket.zeroize,
 tacenta_ratchet.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 tacenta_ratchet.zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 tacenta_ratchet.alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize]
-/
#guard_msgs in
#print axioms Tacenta.ImportInv.Ratchet.decoded_receive_refines

-- The sparse ratchet's. The `_native.native_decide.ax_1_1` entry in this list
-- is the compiler-trust axiom described above: it is what makes this one
-- end-to-end statement compiler-trusted rather than kernel-only.
/--
info: 'Tacenta.ImportInv.Spqr.decoded_receive_no_panic' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_spqr.tacenta_kdf.hkdf_sha256,
 tacenta_spqr.zeroize.Zeroizing,
 tacenta_spqr.zeroize.Zeroizing.new,
 tacenta_spqr.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_spqr.alloc.vec.Vec.append,
 tacenta_spqr.alloc.vec.Vec.remove,
 tacenta_spqr.alloc.vec.Vec.retain,
 tacenta_spqr.zeroize.Zeroize.Blanket.zeroize,
 SpqrT1.receive_no_panic._native.native_decide.ax_1_1,
 tacenta_spqr.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 tacenta_spqr.core.option.Option.Insts.CoreCloneClone.clone]
-/
#guard_msgs in
#print axioms Tacenta.ImportInv.Spqr.decoded_receive_no_panic

/--
info: 'Tacenta.ImportInv.Braid.decoded_receive_no_panic' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_braid.tacenta_erasure.Decoder,
 tacenta_braid.tacenta_erasure.Encoder,
 tacenta_braid.tacenta_erasure.chunk_count,
 tacenta_braid.tacenta_kdf.hkdf_sha256,
 tacenta_braid.tacenta_kdf.hmac_sha256,
 tacenta_braid.tacenta_kem.CT1_LEN,
 tacenta_braid.tacenta_kem.CT2_LEN,
 tacenta_braid.tacenta_kem.EK_VECTOR_LEN,
 tacenta_braid.tacenta_kem.EncapsState,
 tacenta_braid.tacenta_kem.HEADER_LEN,
 tacenta_braid.tacenta_kem.IncrementalKeyPair,
 tacenta_braid.tacenta_kem.encapsulate2,
 tacenta_braid.tacenta_kem.validate_ek,
 tacenta_braid.zeroize.Zeroizing,
 tacenta_braid.tacenta_erasure.Decoder.add_chunk,
 tacenta_braid.tacenta_erasure.Decoder.from_bytes,
 tacenta_braid.tacenta_erasure.Decoder.invariant,
 tacenta_braid.tacenta_erasure.Decoder.message,
 tacenta_braid.tacenta_erasure.Decoder.new,
 tacenta_braid.tacenta_erasure.Decoder.size,
 tacenta_braid.tacenta_erasure.Encoder.from_bytes,
 tacenta_braid.tacenta_erasure.Encoder.invariant,
 tacenta_braid.tacenta_erasure.Encoder.needed,
 tacenta_braid.tacenta_erasure.Encoder.new,
 tacenta_braid.tacenta_kem.EncapsState.from_bytes,
 tacenta_braid.tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_braid.tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_braid.tacenta_kem.IncrementalKeyPair.from_bytes,
 tacenta_braid.tacenta_kem.IncrementalKeyPair.header,
 tacenta_braid.zeroize.Zeroizing.new,
 tacenta_braid.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_braid.zeroize.Zeroize.Blanket.zeroize,
 tacenta_braid.tacenta_erasure.Decoder.Insts.CoreCloneClone.clone,
 tacenta_braid.tacenta_erasure.Encoder.Insts.CoreCloneClone.clone,
 tacenta_braid.tacenta_kem.EncapsState.Insts.CoreCloneClone.clone,
 tacenta_braid.tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone,
 tacenta_braid.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 tacenta_braid.core.option.Option.Insts.CoreCloneClone.clone,
 tacenta_braid.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
 tacenta_braid.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut,
 tacenta_braid.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked,
 tacenta_braid.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
 tacenta_braid.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index,
 tacenta_braid.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut]
-/
#guard_msgs in
#print axioms Tacenta.ImportInv.Braid.decoded_receive_no_panic

end Tacenta.ImportInv
