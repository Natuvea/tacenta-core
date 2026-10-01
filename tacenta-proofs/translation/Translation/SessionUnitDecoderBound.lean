import Translation.TacentaSessionUnit

/-!
# The erasure decoder's chunk count stays within `MAX_CODEWORDS`

When a decoder holds `needed` chunks, `Decoder::message` appends 32 bytes per needed chunk to a
vector, so it can return only if `32 * needed` fits a `usize`.  The decoder's field `needed` is a
free `usize` in the translation, and a decoder that needs `(Usize.max + 1) / 32` chunks and holds
that many makes the call fail (`Translation/SessionBraidReceiveVacuity.lean`).  The Braid never
builds such a decoder: its calls of `Decoder::new` pass protocol constants (`Decoder::new` itself
takes any `size`, and `Decoder::new(usize::MAX)` needs that many chunks but can never hold them),
`Decoder::from_bytes` refuses `needed > MAX_CODEWORDS`, `Decoder::add_chunk` and `Decoder::clone`
keep `needed`, and `Decoder::invariant`, which `Braid::invariant` calls on every decoder a Braid
holds, accepts `needed` only up to `MAX_CODEWORDS = 65536`.

This module proves those facts about the translated definitions, so that the Braid receive
theorems of the complete Session unit can take the bound `needed <= 65536` as a premise on the
state (`State.decoders_bounded` in `SessionUnitBraidT1.lean`) instead of assuming that
`Decoder::message` returns for every decoder.

Nothing here assumes the behaviour of an opaque operation, with one exception that is named:
`DivCeilValue`, the value of `usize::div_ceil` at divisor 32, which the translation leaves
opaque.  It is used only for a decoder that `Decoder::new` has just built.
-/

open Aeneas Aeneas.Std Result
open tacenta_session_unit.tacenta_erasure

namespace Tacenta.SessionUnitDecoderBound

theorem bind_eq_ok_inv {α β : Type} {x : Result α} {f : α → Result β} {r : β}
    (h : (do let v ← x; f v) = ok r) : ∃ v, x = ok v ∧ f v = ok r := by
  cases x with
  | ok v => exact ⟨v, rfl, h⟩
  | fail e => simp at h
  | div => simp at h

/-- Two facts about a successful `add_chunk`: the decoder it returns has the same `size` and
the same `needed`.  Only `have` changes. -/
theorem add_chunk_keeps_needed (d : Decoder) (c : Chunk) (b : Bool) (d' : Decoder)
    (h : Decoder.add_chunk d c = ok (b, d')) : d'.needed = d.needed ∧ d'.size = d.size := by
  unfold Decoder.add_chunk at h
  by_cases hge : d.«have».len ≥ d.needed
  · simp only [hge, if_true] at h
    simp at h
    obtain ⟨-, rfl⟩ := h
    exact ⟨rfl, rfl⟩
  · simp only [hge, if_false] at h
    obtain ⟨⟨b1, v1⟩, -, h2⟩ := bind_eq_ok_inv h
    simp at h2
    obtain ⟨-, rfl⟩ := h2
    exact ⟨rfl, rfl⟩

/-- A bound on `needed` read from a state still holds for the decoder after a chunk is added. -/
theorem needed_le_after_add_chunk {d d' : Decoder} {c : Chunk} {b : Bool} {n : Nat}
    (h : Decoder.add_chunk d c = ok (b, d')) (hd : d.needed.val ≤ n) : d'.needed.val ≤ n := by
  rw [(add_chunk_keeps_needed d c b d' h).1]
  exact hd

/-- `Decoder::clone` keeps `size` and `needed`. -/
theorem clone_keeps_needed (d d' : Decoder)
    (h : Decoder.Insts.CoreCloneClone.clone d = ok d') : d'.needed = d.needed ∧ d'.size = d.size := by
  unfold Decoder.Insts.CoreCloneClone.clone at h
  simp only [lift, bind_tc_ok] at h
  obtain ⟨v, -, h2⟩ := bind_eq_ok_inv h
  simp only [ok.injEq] at h2
  subst h2
  exact ⟨rfl, rfl⟩

/-- The loop in `Decoder::invariant` returns the decoder's own `size` and `needed`. -/
theorem inv_loop_post (d : Decoder) (seen : Array U8 8192#usize) (distinct : Bool)
    (i : Usize) (hi : i.val ≤ d.«have».val.length) :
    Decoder.invariant_loop d seen distinct i ⦃ fun r => r.1 = d.size ∧ r.2.1 = d.needed ⦄ := by
  unfold Decoder.invariant_loop
  apply loop.spec_decr_nat
    (measure := fun p => d.«have».val.length - p.2.2.val)
    (inv := fun p => p.2.2.val ≤ d.«have».val.length)
  · rintro ⟨sn, dd, j⟩ hj
    simp only at hj ⊢
    unfold Decoder.invariant_loop.body
    step*
    all_goals (try (split <;> step*))
  · exact hi

/-- **A decoder that passes the translated `Decoder::invariant` needs at most `MAX_CODEWORDS`
chunks.**  No assumption on any opaque operation: if the `div_ceil` inside `chunk_count` fails,
the invariant does not return `true`. -/
theorem invariant_true_needed_le (d : Decoder) (h : Decoder.invariant d = ok true) :
    d.needed.val ≤ 65536 := by
  unfold Decoder.invariant at h
  obtain ⟨⟨i, i1, v, dist⟩, hloop, h2⟩ := bind_eq_ok_inv h
  obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists
    (inv_loop_post d (Array.repeat 8192#usize 0#u8) true 0#usize (by simp))
  rw [hloop] at hr
  cases hr
  obtain ⟨hp1, hp2⟩ := hp
  simp only [] at hp1 hp2
  subst hp2
  obtain ⟨i2, hi2, h3⟩ := bind_eq_ok_inv h2
  by_cases h1 : d.needed = i2
  · subst h1
    by_cases h4 : d.needed ≤ MAX_CODEWORDS
    · have hm : MAX_CODEWORDS.val = 65536 := by simp [MAX_CODEWORDS]
      have := (UScalar.le_equiv _ _).mp h4
      omega
    · rw [if_pos rfl, if_neg h4] at h3
      simp at h3
  · rw [if_neg h1] at h3
    simp at h3

/-- **The value law of `usize::div_ceil` at divisor 32.**  The translation leaves `div_ceil`
opaque, so what a fresh `Decoder::new` stores in `needed` is known only through this law; it is
the value `(a + 31) / 32` that the real operation returns, with no overflow, including at
`a = Usize.max`.  In particular it says `div_ceil` returns at divisor 32. -/
def DivCeilValue : Prop :=
  ∀ a : Usize, ∃ r, tacenta_session_unit.core.num.Usize.div_ceil a 32#usize = ok r ∧
    r.val = (a.val + 31) / 32

/-- A fresh decoder for a message of at most 2 MiB needs at most `MAX_CODEWORDS` chunks. -/
theorem new_needed_le (hv : DivCeilValue) (n : Usize) (hn : n.val ≤ 2097152) :
    ∃ d, Decoder.new n = ok d ∧ d.needed.val ≤ 65536 := by
  obtain ⟨r, hr, hrv⟩ := hv n
  refine ⟨{ size := n, needed := r, «have» := alloc.vec.Vec.new Chunk }, ?_, ?_⟩
  · unfold Decoder.new chunk_count
    simp only [CHUNK_BYTES]
    rw [hr]
    rfl
  · show r.val ≤ 65536
    omega

/-- Two specifications of one call combine into one with the conjunction as postcondition. -/
theorem spec_and {α : Type} {x : Result α} {P Q : α → Prop} (hP : x ⦃ P ⦄) (hQ : x ⦃ Q ⦄) :
    x ⦃ fun r => P r ∧ Q r ⦄ := by
  obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists hP
  obtain ⟨r', hr', hq⟩ := WP.spec_imp_exists hQ
  rw [hr] at hr'
  cases hr'
  rw [hr]
  simp
  exact ⟨hp, hq⟩

end Tacenta.SessionUnitDecoderBound

/-! ## Axiom pins

The axiom bases of the four results other code relies on, held by the build.  The one translated
constant that appears, `div_ceil`, occurs in the statements through `chunk_count`; the proofs assume
nothing about it. -/

/--
info: 'Tacenta.SessionUnitDecoderBound.add_chunk_keeps_needed' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.SessionUnitDecoderBound.add_chunk_keeps_needed

/--
info: 'Tacenta.SessionUnitDecoderBound.clone_keeps_needed' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.SessionUnitDecoderBound.clone_keeps_needed

/--
info: 'Tacenta.SessionUnitDecoderBound.invariant_true_needed_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.core.num.Usize.div_ceil]
-/
#guard_msgs in
#print axioms Tacenta.SessionUnitDecoderBound.invariant_true_needed_le

/--
info: 'Tacenta.SessionUnitDecoderBound.new_needed_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.core.num.Usize.div_ceil]
-/
#guard_msgs in
#print axioms Tacenta.SessionUnitDecoderBound.new_needed_le
