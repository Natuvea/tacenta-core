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

/-! ## The canonicity check on a stored curve key

`is_canonical_x25519` decides whether thirty-two bytes are a curve key's
canonical encoding (message-format.md, Curve public keys). `State::invariant`
applies it to every curve public key the state holds, and so `from_bytes`
refuses a state holding one spelled any other way (session-persistence.md,
Semantic rules of the leaf formats). It is the same function as
`tacenta-session`'s and `tacenta-wire`'s, repeated because this crate depends
on nothing but the key derivation, and these are `Translation.SessionT1`'s and
`Translation.WireT1`'s lemmas about it restated against this crate's
translation: the check's value is proved, not only that it returns, because
`ImportInv` characterises the invariant by its value. -/

theorem array32_length (a : Array U8 32#usize) : a.val.length = 32 := by
  simp

/-- Whether every byte of `k` from index `i` up to, not including, thirty-one is
`0xff`: what the canonicity check's loop computes from its cursor onward. -/
def allFFFrom (k : Array U8 32#usize) (i : Nat) : Bool :=
  (List.range' i (31 - i)).all (fun j => (k.val[j]!).val == 255)

theorem allFFFrom_step (k : Array U8 32#usize) (i : Nat) (h : i < 31) :
    allFFFrom k i = (((k.val[i]!).val == 255) && allFFFrom k (i + 1)) := by
  unfold allFFFrom
  have hn : 31 - i = (31 - (i + 1)) + 1 := by omega
  rw [hn, List.range'_succ]
  simp [List.all_cons]

theorem allFFFrom_end (k : Array U8 32#usize) : allFFFrom k 31 = true := by
  simp [allFFFrom]

/-- The predicate `is_canonical_x25519` decides: bit 255 clear, and not the
pattern of a value at least p = 2^255 - 19, which is a last byte of `0x7f`,
thirty bytes of `0xff`, and a first byte of at least `0xed`. -/
def canonicalX25519 (k : Array U8 32#usize) : Bool :=
  decide ((k.val[31]!).val < 128) &&
    !(decide (k.val[31]! = 127#u8) && allFFFrom k 1 && decide (237 ≤ (k.val[0]!).val))

/-- The canonicity check's loop returns the flag it was given, cleared if any
byte from its cursor up to thirty-one is not `0xff`. -/
theorem is_canonical_x25519_loop_spec (k : Array U8 32#usize) (b : Bool) (i : Usize)
    (hi : i.val ≤ 31) :
    is_canonical_x25519_loop k b i ⦃ fun r => r = (b && allFFFrom k i.val) ⦄ := by
  unfold is_canonical_x25519_loop
  apply loop.spec_decr_nat
    (measure := fun x => 31 - (Prod.snd x).val)
    (inv := fun x => (Prod.snd x).val ≤ 31 ∧
      ((Prod.fst x) && allFFFrom k (Prod.snd x).val) = (b && allFFFrom k i.val))
  · rintro ⟨b1, j⟩ ⟨hj, hacc⟩
    simp only at hj hacc ⊢
    simp only [is_canonical_x25519_loop.body]
    by_cases hlt : j.val < 31
    · have hb : j.val < k.val.length := by rw [array32_length k]; omega
      have hstep := allFFFrom_step k j.val hlt
      simp only [getElem!_pos k.val j.val hb] at hstep
      -- The byte under the cursor decides whether the flag survives, and the
      -- tail from the next index carries the rest of the conjunction.
      by_cases hff : (k.val[j.val]'hb).val = 255
      · have h2 : allFFFrom k j.val = allFFFrom k (j.val + 1) := by simp [hstep, hff]
        rw [h2] at hacc
        step*
        all_goals (try split)
        all_goals (try step*)
      · have h2 : allFFFrom k j.val = false := by simp [hstep, hff]
        rw [h2, Bool.and_false] at hacc
        step*
        all_goals (try split)
        all_goals (try step*)
        all_goals (try simp_all)
        all_goals (try scalar_tac)
    · have hj31 : j.val = 31 := by omega
      rw [hj31, allFFFrom_end, Bool.and_true] at hacc
      step*
  · exact ⟨hi, rfl⟩

/-- The canonicity check computes exactly `canonicalX25519`. -/
@[step]
theorem is_canonical_x25519_spec (k : Array U8 32#usize) :
    is_canonical_x25519 k ⦃ fun r => r = canonicalX25519 k ⦄ := by
  unfold is_canonical_x25519 canonicalX25519
  have h31 : 31 < k.val.length := by rw [array32_length k]; omega
  have h0 : 0 < k.val.length := by rw [array32_length k]; omega
  simp only [getElem!_pos k.val 31 h31, getElem!_pos k.val 0 h0]
  have hl := is_canonical_x25519_loop_spec k true 1#usize (by simp)
  simp only [Bool.true_and] at hl
  by_cases h128 : (k.val[31]'h31).val < 128
  · by_cases h127 : k.val[31]'h31 = 127#u8
    · all_goals repeat' (first | simp only [WP.spec_ok] | (step with hl) | step | split)
      all_goals (try simp_all)
    · all_goals repeat' (first | simp only [WP.spec_ok] | (step with hl) | step | split)
      all_goals (try simp_all)
      all_goals (try scalar_tac)
  · all_goals repeat' (first | simp only [WP.spec_ok] | (step with hl) | step | split)
    all_goals (try simp_all)

/-- The trusted boundary: the opaque HMAC primitive returns a value on every
input. It wraps a vetted implementation that cannot fail, but the translation
cannot see inside it, so the fact is stated here and used explicitly. -/
def HmacTotal : Prop :=
  ∀ key data, ∃ r, tacenta_kdf.hmac_sha256 key data = ok r

/-- The other half of that boundary: the opaque HKDF expansion returns a value
on every input whose output length is within RFC 5869's `255 · HashLen`, which
for SHA-256 is 8160 bytes. That is the bound the crate's own `expect` enforces
(`tacenta-core/kdf/src/lib.rs`), so this is exactly the condition under which
the real operation returns, and not a wider one; every call in the verified
zone asks for 32, 64 or 80 bytes, and the stepping rule below discharges the
premise from the literal. Root-key steps rest on this the way chain-key steps
rest on `HmacTotal`. -/
def HkdfTotal : Prop :=
  ∀ N key salt info, N.val ≤ 8160 → ∃ r, tacenta_kdf.hkdf_sha256 N key salt info = ok r

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

/-- The same crate at the one other type the ratchet wraps: the vector of
derived keys that `derive_chain` builds and `skip_message_keys` reads back by
index. Totality is not enough here. The derivation writes through the wrapper
once per key and the store loop reads it once per key, and the `Vec::push`
inside each needs the vector's length, which a statement that only said each
call returned could not carry from one access to the next. So it is stated as
a *model*, the way `SessionT1.ZeroizingModel` is: an assumed contents function
together with the equations relating the three operations to it. In the crate
they are a newtype constructor, its projection and its mutable projection,
none of which can fail or alter what is held.

An external crate, and not our code. -/
class DerivedKeysModel where
  /-- What a wrapper holds. -/
  contents : zeroize.Zeroizing (alloc.vec.Vec (U32 × Array U8 32#usize))
    → alloc.vec.Vec (U32 × Array U8 32#usize)
  /-- Wrapping stores what it is given. -/
  new : ∀ (inst : zeroize.Zeroize (alloc.vec.Vec (U32 × Array U8 32#usize)))
      (v : alloc.vec.Vec (U32 × Array U8 32#usize)),
    zeroize.Zeroizing.new inst v ⦃ fun z => contents z = v ⦄
  /-- Reading returns the contents. -/
  deref : ∀ (inst : zeroize.Zeroize (alloc.vec.Vec (U32 × Array U8 32#usize)))
      (z : zeroize.Zeroizing (alloc.vec.Vec (U32 × Array U8 32#usize))),
    zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref inst z ⦃ fun v => v = contents z ⦄
  /-- Reading mutably returns the contents and a way to replace them. -/
  deref_mut : ∀ (inst : zeroize.Zeroize (alloc.vec.Vec (U32 × Array U8 32#usize)))
      (z : zeroize.Zeroizing (alloc.vec.Vec (U32 × Array U8 32#usize))),
    zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut inst z ⦃ fun p =>
      p.1 = contents z ∧ ∀ v', contents (p.2 v') = v' ⦄

-- The model's three equations as stepping rules, so the loops below walk
-- through the wrapper the way they walk through any other call. Registered
-- here rather than with the other rules further down because the derivation
-- and store loops are proved before those.
section DerivedKeys
variable [DerivedKeysModel]

@[step]
theorem derived_keys_new_step
    (inst : zeroize.Zeroize (alloc.vec.Vec (U32 × Array U8 32#usize)))
    (v : alloc.vec.Vec (U32 × Array U8 32#usize)) :
    zeroize.Zeroizing.new inst v ⦃ fun z => DerivedKeysModel.contents z = v ⦄ :=
  DerivedKeysModel.new inst v

@[step]
theorem derived_keys_deref_step
    (inst : zeroize.Zeroize (alloc.vec.Vec (U32 × Array U8 32#usize)))
    (z : zeroize.Zeroizing (alloc.vec.Vec (U32 × Array U8 32#usize))) :
    zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref inst z
      ⦃ fun v => v = DerivedKeysModel.contents z ⦄ := DerivedKeysModel.deref inst z

@[step]
theorem derived_keys_deref_mut_step
    (inst : zeroize.Zeroize (alloc.vec.Vec (U32 × Array U8 32#usize)))
    (z : zeroize.Zeroizing (alloc.vec.Vec (U32 × Array U8 32#usize))) :
    zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut inst z ⦃ fun p =>
      p.1 = DerivedKeysModel.contents z
        ∧ ∀ v', DerivedKeysModel.contents (p.2 v') = v' ⦄ :=
  DerivedKeysModel.deref_mut inst z

end DerivedKeys

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

/-- The skipped-key loop cannot fail. It walks the derived keys by index, so
its fallible steps are the two reads at the cursor, guarded by the length check
that precedes them, the `Vec.push` that stores each key, which fails only past
`Usize.max`, and the cursor's increment, which stays below a length. The
invariant is that the keys already stored plus the ones still to be read stay
within the bound; each turn moves exactly one key from the wrapper into the
store. The measure is the number of keys left to read. -/
@[step]
theorem skip_message_keys_loop_no_panic [DerivedKeysModel]
    (dhr : Array U8 32#usize) (v : alloc.vec.Vec SkippedKey) (now : U32)
    (keys : zeroize.Zeroizing (alloc.vec.Vec (U32 × Array U8 32#usize)))
    (i : Usize)
    (h : v.val.length + ((DerivedKeysModel.contents keys).val.length - i.val)
          ≤ Usize.max) :
    skip_message_keys_loop dhr v now keys i ⦃ fun _ => True ⦄ := by
  unfold skip_message_keys_loop
  apply loop.spec_decr_nat
    (measure := fun x =>
      (DerivedKeysModel.contents keys).val.length - (Prod.snd x).val)
    (inv := fun x => (Prod.fst x).val.length
      + ((DerivedKeysModel.contents keys).val.length - (Prod.snd x).val) ≤ Usize.max)
  · rintro ⟨w, j⟩ hinv
    simp only at hinv
    simp only [skip_message_keys_loop.body]
    -- The cursor's increment needs the wrapper's vector to be a vector: its
    -- length is within `Usize.max`, so a cursor below it has room to move.
    have hfits := (DerivedKeysModel.contents keys).property
    by_cases hlt : j.val < (DerivedKeysModel.contents keys).val.length
    · step*; simp_all [alloc.vec.Vec.len]; omega
    · step*
  · exact h

/-- The chain-derivation loop cannot fail. Its fallible steps are the chain-key
step (which needs the trusted HMAC), the write through the wrapper, and the
`Vec.push` that collects each derived key; the message number is a
`checked_add` reporting `ChainExhausted`, so it is a result rather than a panic.
The invariant is that the keys already collected plus the iterations still to
come stay within `Usize.max`, and the measure is the number of iterations left
in the range. -/
theorem derive_chain_loop_no_panic (h : HmacTotal) [DerivedKeysModel]
    (iter : core.ops.range.Range U32) (start_n : U32)
    (cur : Array U8 32#usize)
    (keys : zeroize.Zeroizing (alloc.vec.Vec (U32 × Array U8 32#usize)))
    (hb : (DerivedKeysModel.contents keys).val.length
          + (iter.end.val - iter.start.val) ≤ Usize.max) :
    NoPanic (derive_chain_loop iter start_n cur keys) := by
  unfold NoPanic derive_chain_loop
  apply loop.spec_decr_nat
    (measure := fun x => (Prod.fst x).end.val - (Prod.fst x).start.val)
    (inv := fun x =>
      (DerivedKeysModel.contents (Prod.snd (Prod.snd x))).val.length
        + ((Prod.fst x).end.val - (Prod.fst x).start.val) ≤ Usize.max)
  · rintro ⟨it, c, ks⟩ hinv
    simp only at hinv
    obtain ⟨⟨nx, mk⟩, hck⟩ := kdf_ck_no_panic h c
    simp only [derive_chain_loop.body, hck]
    by_cases hlt : it.start.val < it.end.val
    · step*; simp_all; omega
    · step*
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
translation as an opaque function and this hypothesis states what it does
**at an in-range index**: it returns, and the vector it hands back is the
input with that index erased. That is the whole of what Rust's `Vec::remove`
promises; out of range it panics, and the hypothesis says nothing there. So
this is a fact the real operation satisfies for every quantified input, not
a totality stronger than the crate, and every use of it in this file sits
under the loop guard `i < len` that the source code itself checks first --
the guard is discharged from that branch condition, in the proof, rather
than argued about the call sites in prose. It is stated rather than assumed
silently, and it is worth removing: unlike the HMAC, this is a
standard-library operation rather than a deliberate trusted primitive, so
the verified zone should not depend on one that the translation cannot see
into.

The guard is also what keeps the statement satisfiable without an
`[Inhabited T]` bound. Stated for every index, the existential would ask,
at `T := Empty` and an empty vector, for an element of an empty type, and
`VecRemoveTotal → False` would be provable -- with every theorem taking it.
Under the guard a vector of an empty type has no in-range index, so the
question does not arise (`Translation/Satisfiability.lean` keeps the
refutation of the unguarded shape, and exhibits a model of this one: the
operation that returns the element in range and panics otherwise, which is
the real one). -/
def VecRemoveTotal : Prop :=
  ∀ {T : Type} (A : Type) (v : alloc.vec.Vec T) (i : Usize), i.val < v.val.length →
    ∃ r, alloc.vec.Vec.remove A v i = ok r ∧ r.2.val = v.val.eraseIdx i.val

/-- The length fact the loops need, derived rather than assumed: a removal in
range shortens the vector by exactly one. Stating the assumption as the
operation's value and deriving the rest is what refinement needs anyway, and it
means the length cannot drift from the value. -/
theorem VecRemoveTotal.lengths (hrm : VecRemoveTotal) {T : Type} (A : Type)
    (v : alloc.vec.Vec T) (i : Usize) (hi : i.val < v.val.length) :
    ∃ r, alloc.vec.Vec.remove A v i = ok r ∧ r.2.val.length + 1 = v.val.length := by
  obtain ⟨r, hr, hv⟩ := hrm A v i hi
  refine ⟨r, hr, ?_⟩
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
    -- The removal's hypothesis is available only under the guard the body
    -- checks first, so the case split comes before the removal is named.
    by_cases hlt : j.val < state.skipped.val.length
    · obtain ⟨⟨removed, v'⟩, hrm', -⟩ := hrm.lengths Global state.skipped j hlt
      step*; simp_all
    · step*
  · trivial

/-- `derive_chain` is the loop with its initial state, so it inherits the loop's
proof directly once the wrapper is known to hold the empty vector it was
built from. -/
@[step]
theorem derive_chain_no_panic (h : HmacTotal) [DerivedKeysModel]
    (ck : Array U8 32#usize) (start_n count : U32) :
    derive_chain ck start_n count ⦃ fun _ => True ⦄ := by
  unfold derive_chain
  simp only [lift, alloc.vec.Vec.with_capacity]
  step
  refine derive_chain_loop_no_panic h _ start_n ck _ ?_
  simp_all
  scalar_tac

/-- The chain loop, with the postcondition strengthened from "did not panic" to
the number of keys it produced. Panic-freedom alone does not compose: a caller
that then feeds those keys into another bounded structure has to know how many
there are. The bound `N` is threaded rather than fixed at `Usize.max`, because
the caller's bound is the tighter one. -/
theorem derive_chain_loop_length (h : HmacTotal) [DerivedKeysModel]
    (N : Nat) (hN : N ≤ Usize.max)
    (iter : core.ops.range.Range U32) (start_n : U32)
    (cur : Array U8 32#usize)
    (keys : zeroize.Zeroizing (alloc.vec.Vec (U32 × Array U8 32#usize)))
    (hb : (DerivedKeysModel.contents keys).val.length
          + (iter.end.val - iter.start.val) ≤ N) :
    derive_chain_loop iter start_n cur keys ⦃ fun r =>
      match r with
      | core.result.Result.Ok p => (DerivedKeysModel.contents p.2).val.length ≤ N
      | core.result.Result.Err _ => True ⦄ := by
  unfold derive_chain_loop
  apply loop.spec_decr_nat
    (measure := fun x => (Prod.fst x).end.val - (Prod.fst x).start.val)
    (inv := fun x =>
      (DerivedKeysModel.contents (Prod.snd (Prod.snd x))).val.length
        + ((Prod.fst x).end.val - (Prod.fst x).start.val) ≤ N)
  · rintro ⟨it, c, ks⟩ hinv
    simp only at hinv
    obtain ⟨⟨nx, mk⟩, hck⟩ := kdf_ck_no_panic h c
    simp only [derive_chain_loop.body, hck]
    by_cases hlt : it.start.val < it.end.val
    · step*; simp_all; omega
    · step*
  · exact hb

/-- The same, lifted to the whole function, with the bound still free. -/
theorem derive_chain_length (h : HmacTotal) [DerivedKeysModel]
    (N : Nat) (hN : N ≤ Usize.max)
    (ck : Array U8 32#usize) (start_n count : U32) (hc : count.val ≤ N) :
    derive_chain ck start_n count ⦃ fun r =>
      match r with
      | core.result.Result.Ok p => (DerivedKeysModel.contents p.2).val.length ≤ N
      | core.result.Result.Err _ => True ⦄ := by
  unfold derive_chain
  simp only [lift, alloc.vec.Vec.with_capacity]
  step
  refine derive_chain_loop_length h N hN _ start_n ck _ ?_
  simp_all

/-- The bound specialised to the count, which is the form a caller actually
needs and the form the stepping tactic can apply without guessing: leaving `N`
free let unification pick it from whatever hypothesis was in scope, which gave a
bound too weak to be useful. -/
@[step]
theorem derive_chain_length_count (h : HmacTotal) [DerivedKeysModel]
    (ck : Array U8 32#usize) (start_n count : U32) :
    derive_chain ck start_n count ⦃ fun r =>
      match r with
      | core.result.Result.Ok p =>
        (DerivedKeysModel.contents p.2).val.length ≤ count.val
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
    by_cases hlt : j.val < v.val.length
    · obtain ⟨⟨removed, v'⟩, hrm', heq⟩ := hrm.lengths Global v j hlt
      step*; simp_all; omega
    · step*
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
    by_cases hlt : j.val < v.val.length
    · obtain ⟨⟨removed, v'⟩, hrm', heq⟩ := hrm.lengths Global v j hlt
      step*; simp_all; omega
    · step*
  · simp

@[step]
theorem purge_chain_range_shrinks (hrm : VecRemoveTotal)
    (skipped : alloc.vec.Vec SkippedKey) (dhr : Array U8 32#usize)
    (from1 upto : U32) :
    purge_chain_range skipped dhr from1 upto ⦃ fun r =>
      r.val.length ≤ skipped.val.length ⦄ := by
  unfold purge_chain_range
  exact purge_chain_range_loop_shrinks hrm skipped dhr from1 upto 0#usize

/-- A saturating sum is at most the true sum, whether or not it saturated.
Stated here rather than imported because `T1` sits below the modules that also
need it. -/
theorem saturating_add_val_le {ty : UScalarTy} (x y : UScalar ty) :
    (UScalar.saturating_add x y).val ≤ x.val + y.val := by
  simp only [UScalar.saturating_add, UScalar.val, BitVec.toNat_ofNat]
  exact le_trans (Nat.mod_le _ _) (min_le_right _ _)

/-- The gap the skip adds to the store is at most `MAX_SKIP`. This is the
guard the Rust checks before the store arithmetic runs: `upto` is refused
unless it is within `MAX_SKIP` of the cursor, and the check is a *saturating*
sum, so it holds at the top of the `u32` range too -- there the sum sticks at
`u32::MAX` and the gap is smaller still.

Without this the store's overflow obligation could only be discharged from the
whole `u32` range, which is a bound no 32-bit target can satisfy: `usize` is
modelled at the platform width, so `len + u32::MAX <= usize::MAX` is false
there for every state. With it the obligation is `len + MAX_SKIP`, which is
satisfiable at both widths. -/
theorem skip_gap_le (nr upto : U32)
    (hg : ¬ upto > core.num.U32.saturating_add nr MAX_SKIP) :
    upto.val - nr.val ≤ MAX_SKIP.val := by
  have h1 : upto.val ≤ (UScalar.saturating_add nr MAX_SKIP).val := by
    simpa [core.num.U32.saturating_add, UScalar.lt_equiv] using hg
  have h2 : (UScalar.saturating_add nr MAX_SKIP).val ≤ nr.val + MAX_SKIP.val :=
    saturating_add_val_le nr MAX_SKIP
  omega

/-- Skipping forward cannot fail. Every fallible step is guarded: the
subtraction by the check that `upto` is past the cursor, the store arithmetic by
the `MAX_SKIPPED_STORE` bound, and the derivation and the store loop by their
own proofs. The store's own length is the one quantity the type does not bound,
so it is a hypothesis.

The two stepping phases are deliberately sequenced rather than nested: the
second does not fire inside `all_goals`, and the pair the derivation returns has
to be destructured between them or a `let` residue blocks the goal.

The `MAX_SKIP` guard has to be split before stepping rather than after: the
store's overflow obligation arises inside the bind, and the branch that bounds
the gap is the one the stepping tactic has already walked past by then. Under
the guard the whole call is the `TooManySkipped` return and there is no
arithmetic to discharge; under its negation `skip_gap_le` supplies the bound. -/
theorem skip_message_keys_no_panic (h : HmacTotal) (hrm : VecRemoveTotal)
    [DerivedKeysModel] (state : State) (upto : U32)
    (hs : state.skipped.val.length + MAX_SKIP.val ≤ Usize.max) :
    NoPanic (skip_message_keys state upto) := by
  unfold NoPanic skip_message_keys
  simp only [lift]
  by_cases hg : upto > core.num.U32.saturating_add state.nr MAX_SKIP
  · step*
  · have hgap := skip_gap_le state.nr upto hg
    step*
    obtain ⟨ck2, keys⟩ := v
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
theorem skip_message_keys_loop_bound [DerivedKeysModel] (B : Nat) (hB : B ≤ Usize.max)
    (dhr : Array U8 32#usize) (v : alloc.vec.Vec SkippedKey) (now : U32)
    (keys : zeroize.Zeroizing (alloc.vec.Vec (U32 × Array U8 32#usize)))
    (i : Usize)
    (h : v.val.length + ((DerivedKeysModel.contents keys).val.length - i.val) ≤ B) :
    skip_message_keys_loop dhr v now keys i ⦃ fun r => r.val.length ≤ B ⦄ := by
  unfold skip_message_keys_loop
  apply loop.spec_decr_nat
    (measure := fun x =>
      (DerivedKeysModel.contents keys).val.length - (Prod.snd x).val)
    (inv := fun x => (Prod.fst x).val.length
      + ((DerivedKeysModel.contents keys).val.length - (Prod.snd x).val) ≤ B)
  · rintro ⟨w, j⟩ hinv
    simp only at hinv
    simp only [skip_message_keys_loop.body]
    -- The cursor's increment needs the wrapper's vector to be a vector: its
    -- length is within `Usize.max`, so a cursor below it has room to move.
    have hfits := (DerivedKeysModel.contents keys).property
    by_cases hlt : j.val < (DerivedKeysModel.contents keys).val.length
    · step*; simp_all [alloc.vec.Vec.len]; omega
    · step*
  · exact h

/-- The store bound in its canonical form: at most what went in. Stated this way
so the stepping tactic can apply it without choosing a bound, the same reason
`derive_chain_length_count` exists. -/
@[step]
theorem skip_message_keys_loop_grows [DerivedKeysModel]
    (dhr : Array U8 32#usize) (v : alloc.vec.Vec SkippedKey) (now : U32)
    (keys : zeroize.Zeroizing (alloc.vec.Vec (U32 × Array U8 32#usize)))
    (i : Usize)
    (h : v.val.length + ((DerivedKeysModel.contents keys).val.length - i.val)
          ≤ Usize.max) :
    skip_message_keys_loop dhr v now keys i ⦃ fun r =>
      r.val.length ≤ v.val.length
        + ((DerivedKeysModel.contents keys).val.length - i.val) ⦄ :=
  skip_message_keys_loop_bound _ h dhr v now keys i (le_refl _)

/-- Skipping forward leaves the store no larger than it was or than the limit
the code enforces, whichever is bigger. This is what a second call needs in
order to re-establish its own precondition, which is why panic-freedom alone was
not enough to compose. -/
@[step]
theorem skip_message_keys_bound (h : HmacTotal) (hrm : VecRemoveTotal)
    [DerivedKeysModel] (state : State) (upto : U32)
    (hs : state.skipped.val.length + MAX_SKIP.val ≤ Usize.max) :
    skip_message_keys state upto ⦃ fun p =>
      p.2.skipped.val.length ≤ max state.skipped.val.length MAX_SKIPPED_STORE.val ⦄ := by
  unfold skip_message_keys
  simp only [lift]
  by_cases hg : upto > core.num.U32.saturating_add state.nr MAX_SKIP
  · step*
    all_goals simp_all [MAX_SKIPPED_STORE]
  · have hgap := skip_gap_le state.nr upto hg
    step*
    all_goals (try obtain ⟨ck2, keys⟩ := v)
    all_goals ((step*; simp_all [alloc.vec.Vec.len, MAX_SKIPPED_STORE]) <;> omega)

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
    by_cases hlt : j.val < state.skipped.val.length
    · obtain ⟨⟨removed, v'⟩, hrm', hlen⟩ := hrm.lengths Global state.skipped j hlt
      step*; simp_all; omega
    · step*
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
theorem hkdf_step (h : HkdfTotal) (N : Usize) (key salt info : Slice U8)
    (hN : N.val ≤ 8160) :
    tacenta_kdf.hkdf_sha256 N key salt info ⦃ fun _ => True ⦄ := by
  obtain ⟨r, hr⟩ := h N key salt info hN; simp [hr]

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
    -- The length fact is what the measure needs: a removal in range shortens
    -- the store by exactly one, so the measure falls even though the cursor
    -- does not.
    by_cases hlt : j.val < w.val.length
    · obtain ⟨⟨removed, w'⟩, hrm', hdec⟩ := hrm.lengths Global w j hlt
      step*; simp_all; omega
    · step*
  · exact h

/-- A branch between two values, rather than between two computations, commutes
with `ok`. The clamp in `age_store` has that shape, and lifting the `ok` out of
it is what lets the stepping tactic carry on through the bind. -/
theorem ite_ok {a : Type} (c : Prop) [Decidable c] (x y : a) :
    (if c then (ok x : Result a) else ok y) = ok (if c then x else y) := by
  split <;> rfl

/-- The wrapper: the record update replaces `skipped` with what the loop
returned and touches nothing else that the bound mentions. -/
@[step]
theorem age_store_spec (hrm : VecRemoveTotal) (state : State) :
    age_store state ⦃ fun s => s.skipped.val.length ≤ state.skipped.val.length ⦄ := by
  unfold age_store
  simp only [lift]
  -- The clock is clamped one below its ceiling before the scan, so `now` is no
  -- longer syntactically the saturating step; the bound holds for whichever
  -- value the clamp produces, so it is supplied for every `now` at once.
  have hl : ∀ now : U32,
      age_store_loop state.skipped now 0#usize
        ⦃ fun r => r.val.length ≤ state.skipped.val.length ⦄ :=
    fun now =>
      age_store_loop_bound hrm state.skipped.val.length state.skipped now
        0#usize (le_refl _)
  -- The clamp is a choice between two values, not between two computations, so
  -- the `ok` comes out of the branch and the stepping tactic sees an ordinary
  -- bind again.
  simp only [ite_ok]
  step*

theorem receive_no_panic (h : HmacTotal) (hk : HkdfTotal) (hz : ZeroizingTotal)
    (hrm : VecRemoveTotal) [DerivedKeysModel] (state : State) (header : Header)
    (dh_out_recv dh_out_send new_dhs_pub : Array U8 32#usize)
    (hs : max state.skipped.val.length MAX_SKIPPED_STORE.val + MAX_SKIP.val ≤ Usize.max) :
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
* `ZeroizingTotal` and `DerivedKeysModel`, the external `zeroize` crate: the
  first says its wrapper and projection cannot fail at the root-key step's
  width, the second that at the derived-keys vector the wrapper holds what was
  put in it, since the two loops that build and read that vector need its
  length and not only a value; and
* `VecRemoveTotal`: Aeneas does not model `Vec::remove`, so it reaches the
  translation as an opaque function and this hypothesis states what it does
  at an in-range index -- returns, with that index erased -- which is what
  `Vec::remove` does. It says nothing out of range, where `Vec::remove`
  panics; each use is under the scan's own length check, and the proof
  discharges the guard from that branch.

`receive` carries one precondition, and it is a real one rather than a
formality. The skipped-key store must be small enough that its length plus
`MAX_SKIP` still fits a `usize`, taking the store at the largest it can reach,
which is its starting size or `MAX_SKIPPED_STORE`, whichever is bigger. Both
widths admit it: 2000 plus 1000 is far inside a 32-bit `usize`, and
`ImportInv.store_plus_skip_fits` proves the constant part outright rather than
assuming it.

An earlier version of this bound asked for the store's length plus the *whole*
`u32` range, and that was a mistake worth recording. Aeneas models `usize` at
the platform width, so on a 32-bit target `Usize.max` and `U32.max` are the
same number and the hypothesis reduced to "the store holds at most zero keys".
It was not a strong precondition; it was one nothing could satisfy, which made
this theorem vacuous on a platform the workspace compiles for. `MAX_SKIP` is
the honest bound because the code refuses the request before the addition
happens: `skip_message_keys` returns `TooManySkipped` when `upto` is past
`nr + MAX_SKIP`, so the gap the store must absorb is at most `MAX_SKIP` and
never the counter's full range. `skip_gap_le` is that guard, stated once.
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
 Pair.Insts.ZeroizeZeroize.zeroize,
 alloc.vec.Vec.remove,
 zeroize.Zeroize.Blanket.zeroize,
 zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize]
-/
#guard_msgs in
#print axioms Tacenta.T1.receive_no_panic
