import Translation.SessionUnitBraidT1

/-!
# What the Braid's preservation theorems need to know about an erasure decoder, on the session unit

`SessionUnitBraidPreserve.lean` (the count-checked port of `BraidPreserve.lean`) uses a decoder
only through `Good`, `Laws` and the lemmas below.  The standalone Braid translation leaves the
erasure decoder opaque, and `BraidPreserveDecoder.lean` defines `Good n d` there through what the
decoder can become.  The session unit translates the decoder with a body, so here `Good n d` is
read off its fields:

    `Good n d` :  `d.size <= n`  and  `d.needed <= MAX_CODEWORDS` (65536).

The first conjunct is what bounds the message a decoder returns (it ends in `out.truncate(size)`),
and therefore the `ct1` that `HeaderSent` hands to `Ct1Received`.  The second is
`SessionUnitBraidT1.State.decoders_bounded`'s clause for one decoder.  `add_chunk` and `clone` keep
both fields (`SessionUnitDecoderBound`), `Decoder::new` sets `size` to its argument and `needed` to
`div_ceil(size, 32)`.

Two laws are assumed, both about standard-library operations the translation leaves opaque, and
both recorded where they are stated:

* `TruncateLen`: `Vec::truncate(v, n)` returns a vector of at most `n` elements.  Weaker than the
  prefix law the joint model of `UnitSatisfiabilityJoint.lean` already satisfies
  (`model_truncate_is_take`); `truncateLen_model` shows the model satisfies this one.
* `DivCeilValue` (`SessionUnitDecoderBound.lean`, unchanged): `usize::div_ceil a 32` returns
  `(a + 31) / 32`.

Nothing here assumes the behaviour of any other opaque operation.
-/

open Aeneas Aeneas.Std Result
open tacenta_session_unit
open tacenta_session_unit.tacenta_erasure
open Tacenta.SessionUnitDecoderBound (bind_eq_ok_inv DivCeilValue)

namespace Tacenta.SessionUnitBraidPreserveDecoder

/-- **`Vec::truncate` returns a vector of at most `n` elements**, at `Vec<u8>`, the one type
`Decoder::message` uses it at.  The real operation returns the first `n` elements (or the whole
vector when it is shorter). -/
def TruncateLen : Prop :=
  ∀ (v : alloc.vec.Vec U8) (n : Usize),
    ∃ r, tacenta_session_unit.alloc.vec.Vec.truncate Global v n = ok r ∧ r.length ≤ n.val

/-- The laws this world needs: the two named above. -/
def Laws : Prop := TruncateLen ∧ DivCeilValue

/-- **A decoder that a Braid state may hold**: sized for at most `n` bytes, and needing at most
`MAX_CODEWORDS` chunks. -/
def Good (n : Nat) (d : Decoder) : Prop := d.size.val ≤ n ∧ d.needed.val ≤ 65536

theorem Good.add {n : Nat} {d d' : Decoder} {c : Chunk} {b : Bool}
    (hg : Good n d) (h : Decoder.add_chunk d c = ok (b, d')) : Good n d' := by
  obtain ⟨h1, h2⟩ := Tacenta.SessionUnitDecoderBound.add_chunk_keeps_needed d c b d' h
  exact ⟨by rw [h2]; exact hg.1, by rw [h1]; exact hg.2⟩

theorem Good.clone {n : Nat} {d d' : Decoder}
    (hg : Good n d) (h : Decoder.Insts.CoreCloneClone.clone d = ok d') : Good n d' := by
  obtain ⟨h1, h2⟩ := Tacenta.SessionUnitDecoderBound.clone_keeps_needed d d' h
  exact ⟨by rw [h2]; exact hg.1, by rw [h1]; exact hg.2⟩

theorem Good.mono {n n' : Nat} {d : Decoder} (hg : Good n d) (h : n ≤ n') : Good n' d :=
  ⟨le_trans hg.1 h, hg.2⟩

/-- **A message `Decoder::message` returns is at most `size` bytes**, given `TruncateLen`: the
function ends in `out.truncate(self.size)`. -/
theorem message_length_le (htr : TruncateLen) {d : Decoder} {v : alloc.vec.Vec U8}
    (h : Decoder.message d = ok (some v)) : v.length ≤ d.size.val := by
  unfold Decoder.message at h
  obtain ⟨b, -, h⟩ := bind_eq_ok_inv h
  split at h
  · repeat' (obtain ⟨_, _, h⟩ := bind_eq_ok_inv h)
    simp only [ok.injEq, Option.some.injEq] at h
    subst h
    have ht := ‹alloc.vec.Vec.truncate Global _ d.size = ok _›
    obtain ⟨r, hr, hlen⟩ := htr _ d.size
    rw [hr] at ht
    cases ht
    exact hlen
  · simp at h

theorem Good.msg (hl : Laws) {n : Nat} {d : Decoder} {v : alloc.vec.Vec U8}
    (hg : Good n d) (h : Decoder.message d = ok (some v)) : v.length ≤ n :=
  le_trans (message_length_le hl.1 h) hg.1

/-- `Decoder::new(m)` stores `m` as the size, whatever `div_ceil` returned. -/
theorem new_size {m : Usize} {d : Decoder} (h : Decoder.new m = ok d) : d.size = m := by
  unfold Decoder.new at h
  obtain ⟨r, -, h⟩ := bind_eq_ok_inv h
  simp only [ok.injEq] at h
  subst h
  rfl

/-- A decoder built for a message of at most `n` bytes, `n` at most the 4128 the Braid's largest
decoder is sized for (`CT2_LEN + MAC_LEN`), is good for `n`: `DivCeilValue` puts `needed` at
`ceil(m / 32)`, far below `MAX_CODEWORDS`. -/
theorem Good.new (hl : Laws) {m : Usize} {d : Decoder} {n : Nat}
    (h : Decoder.new m = ok d) (hmn : m.val ≤ n) (hn : n ≤ 4128) : Good n d := by
  have hsz : d.size = m := new_size h
  obtain ⟨d0, hd0, hneed⟩ := Tacenta.SessionUnitDecoderBound.new_needed_le hl.2 m (by omega)
  rw [h] at hd0
  cases hd0
  exact ⟨by rw [hsz]; exact hmn, hneed⟩

end Tacenta.SessionUnitBraidPreserveDecoder

/-! ## Axiom pins

The axiom base of each result, held by the build. -/

/--
info: 'Tacenta.SessionUnitBraidPreserveDecoder.message_length_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 alloc.vec.Vec.truncate]
-/
#guard_msgs in
#print axioms Tacenta.SessionUnitBraidPreserveDecoder.message_length_le

/--
info: 'Tacenta.SessionUnitBraidPreserveDecoder.Good.new' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 alloc.vec.Vec.truncate,
 core.num.Usize.div_ceil]
-/
#guard_msgs in
#print axioms Tacenta.SessionUnitBraidPreserveDecoder.Good.new

/--
info: 'Tacenta.SessionUnitBraidPreserveDecoder.Good.msg' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 alloc.vec.Vec.truncate,
 core.num.Usize.div_ceil]
-/
#guard_msgs in
#print axioms Tacenta.SessionUnitBraidPreserveDecoder.Good.msg

/--
info: 'Tacenta.SessionUnitBraidPreserveDecoder.Good.add' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.SessionUnitBraidPreserveDecoder.Good.add

/--
info: 'Tacenta.SessionUnitBraidPreserveDecoder.Good.clone' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.SessionUnitBraidPreserveDecoder.Good.clone

/-! ## Statement pins

The axiom pins hold the constants a result depends on and not what it says.  These hold the
statements of the results below while they are present; no gate requires a statement pin to exist. -/

/--
info: Tacenta.SessionUnitBraidPreserveDecoder.Good.new (hl : Tacenta.SessionUnitBraidPreserveDecoder.Laws) {m : Usize}
  {d : Decoder} {n : ℕ} (h : Decoder.new m = ok d) (hmn : ↑m ≤ n) (hn : n ≤ 4128) :
  Tacenta.SessionUnitBraidPreserveDecoder.Good n d
-/
#guard_msgs in
#check Tacenta.SessionUnitBraidPreserveDecoder.Good.new

/-! ## Definition pins

The definitions that carry the claim.  A change to a clause, a constructor or a law fails the
build while its pin is present; no gate requires a definition pin to exist. -/

/--
info: def Tacenta.SessionUnitBraidPreserveDecoder.Good : ℕ → Decoder → Prop :=
fun n d => ↑d.size ≤ n ∧ ↑d.needed ≤ 65536
-/
#guard_msgs in
#print Tacenta.SessionUnitBraidPreserveDecoder.Good

/--
info: def Tacenta.SessionUnitBraidPreserveDecoder.TruncateLen : Prop :=
∀ (v : alloc.vec.Vec U8) (n : Usize), ∃ r, alloc.vec.Vec.truncate Global v n = ok r ∧ r.length ≤ ↑n
-/
#guard_msgs in
#print Tacenta.SessionUnitBraidPreserveDecoder.TruncateLen

/--
info: def Tacenta.SessionUnitBraidPreserveDecoder.Laws : Prop :=
Tacenta.SessionUnitBraidPreserveDecoder.TruncateLen ∧ DivCeilValue
-/
#guard_msgs in
#print Tacenta.SessionUnitBraidPreserveDecoder.Laws
