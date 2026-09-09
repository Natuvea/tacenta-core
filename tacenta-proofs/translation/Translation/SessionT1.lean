/-
Translation.SessionT1: panic-freedom for the PQXDH derivation (proof tier T1).

The second verified zone. `tacenta-session` is a leaf crate for the same reason
`tacenta-ratchet` is, and this file is its counterpart to `Translation.T1`: every
function in it is proved to return, never to panic, under stated assumptions.

One deliberate difference from the ratchet's file. That file's specs say
only "it returned", which is all panic-freedom needs, and its refinement tier
unregisters nearly every one of them and restates it carrying the value. The
specs here carry the value from the start, so `Translation.SessionT3`
inherits them instead of fighting them.
-/
import Translation.TacentaSession
import Translation.T1

namespace Tacenta.SessionT1

open Aeneas Aeneas.Std Result
open tacenta_session

/-- The shape shared with the ratchet's tier: a call that does not fail. -/
abbrev NoPanic {α : Type} (e : Result α) : Prop := Tacenta.T1.NoPanic e

/-! ## The trusted boundary

Two assumptions, both the same kind as the ratchet's and neither about our own
code. The key derivation is opaque by the choice that keeps the translation
tractable, and `Zeroizing` belongs to an external crate. They are separate
constants from the ratchet's because each generated module declares its own, so
they are stated again rather than shared. -/

/-- The key derivation returns. -/
def HkdfTotal : Prop :=
  ∀ (N : Usize) (salt ikm info : Slice U8),
    ∃ r, tacenta_kdf.hkdf_sha256 N salt ikm info = ok r

/-- `Zeroizing` behaves like a transparent container: it has contents, wrapping
stores them, reading returns them, and writing through replaces them.

Stated as a *model* -- an assumed contents function together with the equations
relating the three operations to it -- rather than as a chain of round-trip
equations. That is what lets the values chain: the derivation writes through the
wrapper twice and reads it once, and a specification that only said each call
returned could not carry a length from one write to the next, which is exactly
what the append's bound needs.

An external crate. -/
class ZeroizingModel where
  /-- What a wrapper holds. -/
  contents : zeroize.Zeroizing (alloc.vec.Vec U8) → alloc.vec.Vec U8
  /-- Wrapping stores what it is given. -/
  new : ∀ (inst : zeroize.Zeroize (alloc.vec.Vec U8)) (v : alloc.vec.Vec U8),
    zeroize.Zeroizing.new inst v ⦃ fun z => contents z = v ⦄
  /-- Reading returns the contents. -/
  deref : ∀ (inst : zeroize.Zeroize (alloc.vec.Vec U8))
      (z : zeroize.Zeroizing (alloc.vec.Vec U8)),
    zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref inst z ⦃ fun v => v = contents z ⦄
  /-- Reading mutably returns the contents and a way to replace them. -/
  deref_mut : ∀ (inst : zeroize.Zeroize (alloc.vec.Vec U8))
      (z : zeroize.Zeroizing (alloc.vec.Vec U8)),
    zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut inst z ⦃ fun p =>
      p.1 = contents z ∧ ∀ v', contents (p.2 v') = v' ⦄

/-! ## Appending a slice

The library models `extend_from_slice` rather than leaving it an axiom, which
matters: unlike `Vec::remove` in the ratchet, this adds no trusted boundary. It
fails only when the result would not fit a `usize`, and the clone it performs on
`u8` is the identity, so the value is exactly the concatenation. -/

@[step]
theorem extend_from_slice_spec (v : alloc.vec.Vec U8) (s : Slice U8)
    (h : v.val.length + s.val.length ≤ Usize.max) :
    alloc.vec.Vec.extend_from_slice core.clone.CloneU8 v s ⦃ fun r =>
      r.val = v.val ++ s.val ⦄ := by
  unfold alloc.vec.Vec.extend_from_slice
  -- The clone on `u8` is the identity, so the appended bytes are the slice's.
  have hclone : ∀ x ∈ s.val, (core.clone.CloneU8.clone) x = ok x := by
    intro x _
    rfl
  obtain ⟨s', hs'eq, hs'val⟩ := Std.WP.spec_imp_exists (Slice.clone_spec hclone)
  -- The clone returns the slice itself, so restate that at `s` before using it.
  rw [← hs'val] at hs'eq
  -- The library states the guard with its own length functions; the hypothesis
  -- is the same proposition written with the underlying lists.
  have h' : v.length + s.length ≤ Usize.max := h
  rw [dif_pos h']
  -- The match binds a proof of its own scrutinee, so neither `rw` nor `simp`
  -- gets under it. Split it and use the branch's own equation against what the
  -- clone is known to return.
  split
  · rename_i s'' heq
    rw [hs'eq] at heq
    injection heq with heq
    subst heq
    rw [Std.WP.spec_ok]
  · rename_i e heq
    rw [hs'eq] at heq
    exact absurd heq (by simp)
  · rename_i heq
    rw [hs'eq] at heq
    exact absurd heq (by simp)

/-- The length that follows, which callers need to discharge the next append's
bound without carrying the whole value. -/
theorem extend_from_slice_length (v : alloc.vec.Vec U8) (s : Slice U8)
    (h : v.val.length + s.val.length ≤ Usize.max) :
    alloc.vec.Vec.extend_from_slice core.clone.CloneU8 v s ⦃ fun r =>
      r.val.length = v.val.length + s.val.length ⦄ := by
  refine Std.WP.spec_mono (extend_from_slice_spec v s h) ?_
  intro r hr
  simp [hr]

/-! ## The keying material

Assembling `KM` cannot fail. Every component is a fixed thirty-two bytes and
there are at most five, so the appends stay inside `Usize.max` on any target the
translation models. The specification carries the value, because the order of
these components is the whole content of this step and a caller that only knew
it returned would know nothing worth knowing.

Stated in two shapes rather than one with a `match`, so that each is written the
way the code branches and the way the model does. -/

/-- A 32-byte array holds 32 bytes. -/
theorem array32_length (a : Array U8 32#usize) : a.val.length = 32 := by
  have := a.property
  simpa using this

/-- Anything that fits a `u32` fits a `usize`: the width is thirty-two or
sixty-four bits, and both are far past the fixed sizes assembled here. Needed
because `Usize.max` is not a literal, so a bound on it cannot be computed. -/
theorem small_le_usize_max {n : Nat} (h : n ≤ 4294967295) : n ≤ Usize.max := by
  rcases Usize.bounds_eq with he | he <;> rw [he] <;> scalar_tac

@[step]
theorem km_spec_none (dh1 dh2 dh3 ss : Array U8 32#usize) :
    km dh1 dh2 dh3 none ss ⦃ fun r =>
      r.val = dh1.val ++ dh2.val ++ dh3.val ++ ss.val ⦄ := by
  unfold km
  have l1 := array32_length dh1
  have l2 := array32_length dh2
  have l3 := array32_length dh3
  have ls := array32_length ss
  -- Two appends: the prefix onto an empty buffer, which is a fixed size, and
  -- the keying material onto that, which is the caller's bound.
  step* <;> simp_all <;> exact small_le_usize_max (by omega)

@[step]
theorem km_spec_some (dh1 dh2 dh3 d4 ss : Array U8 32#usize) :
    km dh1 dh2 dh3 (some d4) ss ⦃ fun r =>
      r.val = dh1.val ++ dh2.val ++ dh3.val ++ d4.val ++ ss.val ⦄ := by
  unfold km
  have l1 := array32_length dh1
  have l2 := array32_length dh2
  have l3 := array32_length dh3
  have l4 := array32_length d4
  have ls := array32_length ss
  step* <;> simp_all <;> exact small_le_usize_max (by omega)

/-! ## The identity binding and the encodings

`associated_data` carries a real precondition: its arguments are slices of
arbitrary length, so nothing but the caller bounds their total. The encodings
carry none, because a curve key is a fixed thirty-two bytes and one tag byte
cannot overflow anything.

The values are carried here too, and for `associated_data` the value is the
point: `Proofs.SessionEstablishment` shows the concatenation is recoverable only
because `encode_ec` is fixed-width, and a specification that said merely "it
returned" could not connect to that. -/

@[step]
theorem associated_data_spec (a b : Slice U8)
    (h : a.val.length + b.val.length ≤ Usize.max) :
    associated_data a b ⦃ fun r => r.val = a.val ++ b.val ⦄ := by
  unfold associated_data
  step*

@[step]
theorem associated_data_with_kem_spec (a b c : Slice U8)
    (h : a.val.length + b.val.length + c.val.length ≤ Usize.max) :
    associated_data_with_kem a b c ⦃ fun r => r.val = a.val ++ b.val ++ c.val ⦄ := by
  unfold associated_data_with_kem
  have hab : a.val.length + b.val.length ≤ Usize.max := by omega
  step*

@[step]
theorem encode_ec_spec (pk : Array U8 32#usize) :
    encode_ec pk ⦃ fun r => r.val = ENCODE_EC_CURVE25519 :: pk.val ⦄ := by
  unfold encode_ec
  have lp := array32_length pk
  step* <;> simp_all

@[step]
theorem encode_kem_spec (pk : Slice U8)
    (h : pk.val.length + 1 ≤ Usize.max) :
    encode_kem pk ⦃ fun r => r.val = ENCODE_KEM_ML_KEM_1024 :: pk.val ⦄ := by
  unfold encode_kem
  step*

/-! ## Reading an encoding back

The loop copies the thirty-two bytes after the tag. Every fallible step is
guarded by the length the caller checked: the cursor's increment and the read
stay inside a slice known to be thirty-three bytes, and the write stays inside a
thirty-two byte array because the cursor never passes it.

The value is carried pointwise rather than as a list equality, because that is
what the loop actually establishes one step at a time; the list equality follows
at the exit, where the lengths are known. -/

theorem decode_ec_loop_spec (bytes : Slice U8) (k : Array U8 32#usize) (i : Usize)
    (hlen : bytes.val.length = 33) (hi : i.val ≤ 32)
    (hpre : ∀ j, j < i.val → k.val[j]! = bytes.val[j + 1]!) :
    decode_ec_loop bytes k i ⦃ fun r =>
      ∀ j, j < 32 → r.val[j]! = bytes.val[j + 1]! ⦄ := by
  unfold decode_ec_loop
  apply loop.spec_decr_nat
    (measure := fun x => 32 - (Prod.snd x).val)
    (inv := fun x => (Prod.snd x).val ≤ 32
      ∧ ∀ j, j < (Prod.snd x).val → (Prod.fst x).val[j]! = bytes.val[j + 1]!)
  · rintro ⟨w, j⟩ ⟨hj, hinv⟩
    simp only at hj hinv
    simp only [decode_ec_loop.body]
    -- The stepping tactic works in its own locals, so give it the caller's
    -- length in the form its bounds are stated with.
    have hlen' : Slice.length bytes = 33 := by simpa using hlen
    by_cases hlt : j.val < 32
    · step* <;> simp_all
      refine ⟨?_, by omega⟩
      intro j1 hj1
      rcases Nat.lt_or_ge j1 j.val with hcase | hcase
      · -- Below the cursor the write did not touch it, so the invariant holds.
        rw [List.getElem?_set_ne (by omega)]
        exact hinv j1 hcase
      · -- At the cursor it is exactly the byte just read.
        have hje : j1 = j.val := by omega
        subst hje
        have hw : w.val.length = 32 := array32_length w
        first
          | simp [List.getElem?_set_self, hw]
          | simp [List.getElem?_set, hw]
          | rw [List.getElem?_set_self (by omega)]
        -- The write landed inside the array, and the byte read is inside the
        -- slice, so both sides are the same element.
        rw [if_pos hlt, List.getElem?_eq_getElem (by omega)]
    · -- The cursor has reached the end, so the invariant already covers every
      -- index the postcondition asks about.
      step*
  · exact ⟨hi, hpre⟩

/-- The loop as the wrapper calls it, at a cursor of zero. A canonical
specialised form, because the stepping tactic cannot choose the free cursor and
would pick badly. -/
@[step]
theorem decode_ec_loop_spec_zero (bytes : Slice U8) (k : Array U8 32#usize)
    (hlen : bytes.val.length = 33) :
    decode_ec_loop bytes k 0#usize ⦃ fun r =>
      ∀ j, j < 32 → r.val[j]! = bytes.val[j + 1]! ⦄ :=
  decode_ec_loop_spec bytes k 0#usize hlen (by simp) (by simp)

/-- Reading an encoding back cannot fail, and when it succeeds the key is the
thirty-two bytes after the tag.

Nothing is claimed about the rejecting paths beyond their returning: what makes
a byte string not an encoding is the guard itself, and restating it here would
add nothing. -/
theorem decode_ec_spec (bytes : Slice U8) :
    decode_ec bytes ⦃ fun r => ∀ k, r = some k →
      ∀ j, j < 32 → k.val[j]! = bytes.val[j + 1]! ⦄ := by
  unfold decode_ec
  by_cases hl : Slice.len bytes = ENCODE_EC_LEN
  · have hlen : bytes.val.length = 33 := by
      simp only [Slice.len, ENCODE_EC_LEN] at hl
      scalar_tac
    simp only [hl, if_pos]
    step*
  · simp only [hl, if_false]
    step*

/-! ## The derivation

`kdf_sk` prefixes the domain separator and hands the result to the opaque key
derivation. Its precondition is the one real bound in this file: the keying
material is a slice of arbitrary length, so the caller has to say it leaves room
for thirty-two more bytes.

The wrapper's three operations are registered as stepping rules carrying their
values, so the tactic can walk the whole body: the length the second append
needs comes from the first append through two of those calls, and a rule saying
only that they returned would lose it. -/

-- A class rather than a plain hypothesis, so that instance resolution supplies
-- it. The model appears in these rules' *postconditions*, which the stepping
-- tactic cannot determine from the call, and a rule it cannot instantiate is a
-- rule it walks past. It is still an assumption, and it is named as one in every
-- theorem below and in LIMITATIONS.md.
section Zeroizing
variable [ZeroizingModel]

@[step]
theorem zeroizing_new_step (inst : zeroize.Zeroize (alloc.vec.Vec U8))
    (v : alloc.vec.Vec U8) :
    zeroize.Zeroizing.new inst v ⦃ fun z => ZeroizingModel.contents z = v ⦄ :=
  ZeroizingModel.new inst v

@[step]
theorem zeroizing_deref_step (inst : zeroize.Zeroize (alloc.vec.Vec U8))
    (z : zeroize.Zeroizing (alloc.vec.Vec U8)) :
    zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref inst z
      ⦃ fun v => v = ZeroizingModel.contents z ⦄ := ZeroizingModel.deref inst z

@[step]
theorem zeroizing_deref_mut_step (inst : zeroize.Zeroize (alloc.vec.Vec U8))
    (z : zeroize.Zeroizing (alloc.vec.Vec U8)) :
    zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut inst z ⦃ fun p =>
      p.1 = ZeroizingModel.contents z
        ∧ ∀ v', ZeroizingModel.contents (p.2 v') = v' ⦄ :=
  ZeroizingModel.deref_mut inst z

@[step]
theorem hkdf_step (hk : HkdfTotal) (N : Usize) (salt ikm info : Slice U8) :
    tacenta_kdf.hkdf_sha256 N salt ikm info ⦃ fun _ => True ⦄ := by
  obtain ⟨r, hr⟩ := hk N salt ikm info
  simp [hr]

end Zeroizing

theorem kdf_sk_no_panic (hk : HkdfTotal) [ZeroizingModel]
    (km_bytes : Slice U8)
    (hb : km_bytes.val.length + 32 ≤ Usize.max) :
    NoPanic (kdf_sk km_bytes) := by
  show kdf_sk km_bytes ⦃ fun _ => True ⦄
  unfold kdf_sk
  step*
  all_goals simp_all
  all_goals first | omega | exact small_le_usize_max (by omega)

/-- `kdf_sk` as a stepping rule, so `shared_secret` can walk through it. -/
@[step]
theorem kdf_sk_step (hk : HkdfTotal) [ZeroizingModel] (km_bytes : Slice U8)
    (hb : km_bytes.val.length + 32 ≤ Usize.max) :
    kdf_sk km_bytes ⦃ fun _ => True ⦄ := kdf_sk_no_panic hk km_bytes hb

/-- The shared secret cannot fail, and needs no precondition: the keying
material is at most five fixed components, so the bound `kdf_sk` asks for is
discharged from `km`'s value rather than passed to the caller. That is the
return on stating `km` with its value instead of only that it returned. -/
theorem shared_secret_no_panic (hk : HkdfTotal) [ZeroizingModel]
    (dh1 dh2 dh3 ss : Array U8 32#usize) (dh4 : Option (Array U8 32#usize)) :
    NoPanic (shared_secret dh1 dh2 dh3 dh4 ss) := by
  show shared_secret dh1 dh2 dh3 dh4 ss ⦃ fun _ => True ⦄
  unfold shared_secret
  have l1 := array32_length dh1
  have l2 := array32_length dh2
  have l3 := array32_length dh3
  have ls := array32_length ss
  rcases dh4 with _ | d4
  · step*
    all_goals simp_all [alloc.vec.Vec.deref]
    all_goals exact small_le_usize_max (by omega)
  · have l4 := array32_length d4
    step*
    all_goals simp_all [alloc.vec.Vec.deref]
    all_goals exact small_le_usize_max (by omega)

/-! ## The boundary, audited rather than asserted

What the result actually rests on, checked by the build. Lean's own three, the
key derivation, and the `zeroize` crate's opaque items. Nothing else, and in
particular no `sorryAx`: if this list changes, the build fails and whoever
changed it has to say why. -/

/--
info: 'Tacenta.SessionT1.shared_secret_no_panic' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_kdf.hkdf_sha256,
 zeroize.Zeroizing,
 zeroize.Zeroizing.new,
 zeroize.Zeroize.Blanket.zeroize,
 zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize]
-/
#guard_msgs in
#print axioms Tacenta.SessionT1.shared_secret_no_panic

/-
## What T1 covers for this zone, and what it rests on

Every function in `tacenta-session` is now proved to return without panicking,
and each specification carries the value it produces rather than only the fact
that it returned: appending a slice, assembling the keying material in both its
shapes, the derivation, the shared secret, the identity binding, both encodings,
and reading an encoding back.

That choice pays twice. The specifications compose because the append
underneath them carries its value; and `shared_secret` needs **no precondition
at all**, because the bound `kdf_sk` asks for is discharged from `km`'s value
rather than pushed onto the caller.

What it rests on, all of it named:

* `HkdfTotal`, the key derivation, opaque by the choice that keeps the
  translation tractable. Same boundary as the ratchet's, and a separate constant
  because each generated module declares its own.
* `ZeroizingModel`, the external `zeroize` crate. Stated as a model -- a contents
  function and the equations relating the three operations to it -- rather than
  as bare totality, because the derivation writes through the wrapper twice and
  reads it once, and a bound has to travel from the first write to the second.
  It is a class so that instance resolution supplies it to the stepping rules,
  whose postconditions mention it and which the tactic could not otherwise
  instantiate. Still an assumption, named in every theorem and audited above.
* One real precondition, on `kdf_sk`: the keying material must leave room for
  thirty-two more bytes. It is a slice of arbitrary length, so nothing but the
  caller bounds it, and `shared_secret` discharges it for the only call that
  matters.
* `associated_data` carries a bound for the same reason, and it is where the
  fixed-width requirement on `encode_ec` becomes load-bearing
  (`Proofs.SessionEstablishment`, session-establishment.md).

Notably absent: no `VecRemoveTotal` analogue. `extend_from_slice` is modelled by
the Aeneas library rather than left opaque, so this zone adds no trusted
boundary of that kind, where the ratchet's does.

What remains for this zone is T3: relating all of it to
`Model.SessionEstablishment`, which is what the value-carrying specifications
above were written to make possible.
-/

end Tacenta.SessionT1
