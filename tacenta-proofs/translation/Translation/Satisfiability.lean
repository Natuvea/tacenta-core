import Translation.SpqrT3
import Translation.T3
import Translation.BraidT3

/-!
# Satisfiability of the `Vec`-family boundary hypotheses

Every `Vec` operation Aeneas does not model reaches the translation as an
axiom, and the T1/T3 files assume what they need about it as a named `Prop`
(`VecAppendTotal`, `VecRemoveAgrees`, ...). A hypothesis of that kind carries
a risk the rest of the proof cannot see: if it is **refutable** -- if no
function at all could satisfy it -- then every theorem taking it is provable
from `False`, and the kernel will happily check it.

This file is the check against that. For each hypothesis it states the
*shape* as a predicate on an arbitrary function of the axiom's type, shows
the current hypothesis is exactly that shape applied to the axiom
(`Iff.rfl`, so the two cannot drift), and exhibits a concrete function
satisfying it, so the hypothesis is consistent: at least one model of that
hypothesis makes it true. Alongside each it also states the natural over-strong
shape -- an `append` with no length guard, a `remove` over every element
type, a `remove` naming its out-of-range value through `default` -- and
proves that **no** function satisfies it, so the guards on the hypotheses
are shown to be necessary rather than merely cautious. An edit that makes a
hypothesis unsatisfiable breaks the witness here.

Consistency is all this establishes. A satisfiable hypothesis can still be
false of the real `Vec::remove` -- the `Remove` shapes say nothing about an
out-of-range index, where Rust panics (`LIMITATIONS.md`) -- and nothing
here says the axiom Aeneas generated *is* the witness. It says the theorems
downstream are not proofs of `False`.
-/

namespace Tacenta.Satisfiability

open Aeneas Aeneas.Std Result

/-! ## `Vec::append` -/

/-- The type of `tacenta_spqr.alloc.vec.Vec.append`. -/
abbrev AppendFn :=
  {T : Type} → (A : Type) → alloc.vec.Vec T → alloc.vec.Vec T →
    Result (alloc.vec.Vec T × alloc.vec.Vec T)

/-- The shape of `SpqrT1.VecAppendTotal`. -/
def AppendTotal (f : AppendFn) : Prop :=
  ∀ {T : Type} (A : Type) (v w : alloc.vec.Vec T),
    v.length + w.length ≤ Usize.max →
    ∃ r, f A v w = ok r ∧ r.1.length = v.length + w.length

/-- The shape of `SpqrT3.VecAppendAgrees`. -/
def AppendAgrees (f : AppendFn) : Prop :=
  ∀ {T : Type} (A : Type) (v w : alloc.vec.Vec T),
    v.length + w.length ≤ Usize.max →
    ∃ r, f A v w = ok r ∧ r.1.val = v.val ++ w.val

/-- The over-strong shape: `VecAppendTotal` with no length guard. -/
def AppendTotalUnguarded (f : AppendFn) : Prop :=
  ∀ {T : Type} (A : Type) (v w : alloc.vec.Vec T),
    ∃ r, f A v w = ok r ∧ r.1.length = v.length + w.length

theorem VecAppendTotal_is :
    Tacenta.SpqrT1.VecAppendTotal ↔ AppendTotal @tacenta_spqr.alloc.vec.Vec.append :=
  Iff.rfl

theorem VecAppendAgrees_is :
    Tacenta.SpqrT3.VecAppendAgrees ↔ AppendAgrees @tacenta_spqr.alloc.vec.Vec.append :=
  Iff.rfl

/-- Concatenate when the result fits, fail otherwise -- which is what the real
`Vec::append` does at the capacity boundary (it aborts). -/
def appendWitness : AppendFn := fun {_T} _A v w =>
  if h : v.val.length + w.val.length ≤ Usize.max then
    ok (⟨v.val ++ w.val, by simpa using h⟩, w)
  else fail .panic

theorem appendWitness_agrees : AppendAgrees @appendWitness := by
  intro T A v w hlen
  simp only [alloc.vec.Vec.length] at hlen
  exact ⟨(⟨v.val ++ w.val, by simpa using hlen⟩, w), by simp [appendWitness, hlen], rfl⟩

theorem append_agrees_satisfiable : ∃ f : AppendFn, AppendAgrees f :=
  ⟨@appendWitness, appendWitness_agrees⟩

theorem append_total_satisfiable : ∃ f : AppendFn, AppendTotal f := by
  refine ⟨@appendWitness, fun A v w hlen => ?_⟩
  obtain ⟨r, hr, hv⟩ := appendWitness_agrees A v w hlen
  exact ⟨r, hr, by simp [alloc.vec.Vec.length, hv]⟩

theorem usize_max_pos : 0 < Usize.max := by
  simp [Usize.max, Usize.numBits]
  cases System.Platform.numBits_eq <;> simp_all

/-- Why the guard: two vectors already at `Usize.max` have no concatenation
inside Aeneas's `Vec`, so the unguarded shape has no model at all. -/
theorem append_total_unguarded_unsatisfiable : ¬ ∃ f : AppendFn, AppendTotalUnguarded f := by
  rintro ⟨f, hf⟩
  let full : alloc.vec.Vec Unit := ⟨List.replicate Usize.max (), by simp⟩
  obtain ⟨r, -, hlen⟩ := hf Unit full full
  have hr := r.1.property
  simp only [alloc.vec.Vec.length, full, List.length_replicate] at hlen
  have := usize_max_pos
  omega

/-! ## `Vec::remove` -/

/-- The type of both crates' `alloc.vec.Vec.remove`. -/
abbrev RemoveFn :=
  {T : Type} → (A : Type) → alloc.vec.Vec T → Usize → Result (T × alloc.vec.Vec T)

/-- The shape of `T1.VecRemoveTotal` and `SpqrT1.VecRemoveTotal`. -/
def RemoveTotal (f : RemoveFn) : Prop :=
  ∀ {T : Type} [Inhabited T] (A : Type) (v : alloc.vec.Vec T) (i : Usize),
    ∃ r, f A v i = ok r ∧ r.2.val = v.val.eraseIdx i.val

/-- The shape of `SpqrT3.VecRemoveAgrees`. -/
def RemoveAgrees (f : RemoveFn) : Prop :=
  ∀ {T : Type} [Inhabited T] (A : Type) (v : alloc.vec.Vec T) (i : Usize),
    ∃ r, f A v i = ok r ∧
      (∀ h : i.val < v.val.length, r.1 = v.val[i.val]'h) ∧
      r.2.val = v.val.eraseIdx i.val

/-- The over-strong shape: `VecRemoveTotal` over every `T`, inhabited or not. -/
def RemoveTotalUnbounded (f : RemoveFn) : Prop :=
  ∀ {T : Type} (A : Type) (v : alloc.vec.Vec T) (i : Usize),
    ∃ r, f A v i = ok r ∧ r.2.val = v.val.eraseIdx i.val

/-- The over-strong shape: `VecRemoveAgrees` naming the removed element with
the `!` index. -/
def RemoveAgreesBang (f : RemoveFn) : Prop :=
  ∀ {T : Type} [Inhabited T] (A : Type) (v : alloc.vec.Vec T) (i : Usize),
    ∃ r, f A v i = ok r ∧ r.1 = v.val[i.val]! ∧ r.2.val = v.val.eraseIdx i.val

theorem T1_VecRemoveTotal_is :
    Tacenta.T1.VecRemoveTotal ↔ RemoveTotal @tacenta_ratchet.alloc.vec.Vec.remove :=
  Iff.rfl

theorem SpqrT1_VecRemoveTotal_is :
    Tacenta.SpqrT1.VecRemoveTotal ↔ RemoveTotal @tacenta_spqr.alloc.vec.Vec.remove :=
  Iff.rfl

theorem VecRemoveAgrees_is :
    Tacenta.SpqrT3.VecRemoveAgrees ↔ RemoveAgrees @tacenta_spqr.alloc.vec.Vec.remove :=
  Iff.rfl

theorem length_eraseIdx_le_max {T : Type} (v : alloc.vec.Vec T) (i : Nat) :
    (v.val.eraseIdx i).length ≤ Usize.max :=
  le_trans (List.length_eraseIdx_le _ _) v.property

open Classical in
/-- In range: the element at the index and the shortened vector. Out of range:
the real operation panics; the shapes above only ask that *some* element come
back, so any element does. Choosing one classically is what makes the witness
uniform in `T` while the shapes quantify over inhabited `T` only. -/
noncomputable def removeWitness : RemoveFn := fun {T} _A v i =>
  if h : i.val < v.val.length then
    ok (v.val[i.val], ⟨v.val.eraseIdx i.val, length_eraseIdx_le_max v i.val⟩)
  else if hT : Nonempty T then
    ok (Classical.choice hT, ⟨v.val.eraseIdx i.val, length_eraseIdx_le_max v i.val⟩)
  else fail .panic

theorem removeWitness_agrees : RemoveAgrees @removeWitness := by
  intro T _ A v i
  by_cases h : i.val < v.val.length
  · exact ⟨(v.val[i.val], ⟨v.val.eraseIdx i.val, length_eraseIdx_le_max v i.val⟩),
      by simp [removeWitness, h], fun _ => rfl, rfl⟩
  · have hT : Nonempty T := ⟨default⟩
    exact ⟨(Classical.choice hT, ⟨v.val.eraseIdx i.val, length_eraseIdx_le_max v i.val⟩),
      by simp [removeWitness, h, hT], fun h' => absurd h' h, rfl⟩

theorem remove_agrees_satisfiable : ∃ f : RemoveFn, RemoveAgrees f :=
  ⟨@removeWitness, removeWitness_agrees⟩

theorem remove_total_satisfiable : ∃ f : RemoveFn, RemoveTotal f := by
  refine ⟨@removeWitness, fun A v i => ?_⟩
  obtain ⟨r, hr, -, hv⟩ := removeWitness_agrees A v i
  exact ⟨r, hr, hv⟩

/-- Why the `Inhabited` bound: at an empty element type the existential has
nothing to offer. -/
theorem remove_total_unbounded_unsatisfiable : ¬ ∃ f : RemoveFn, RemoveTotalUnbounded f := by
  rintro ⟨f, hf⟩
  obtain ⟨r, -, -⟩ := hf Unit (alloc.vec.Vec.new Empty) 0#usize
  exact r.1.elim

/-- Why the conditional value: `[]![0]` is `default`, and two instances on
`Bool` give two defaults for one function value. -/
theorem remove_agrees_bang_unsatisfiable : ¬ ∃ f : RemoveFn, RemoveAgreesBang f := by
  rintro ⟨f, hf⟩
  obtain ⟨r₁, h₁, hv₁, -⟩ := @hf Bool ⟨true⟩ Unit (alloc.vec.Vec.new Bool) 0#usize
  obtain ⟨r₂, h₂, hv₂, -⟩ := @hf Bool ⟨false⟩ Unit (alloc.vec.Vec.new Bool) 0#usize
  rw [h₁] at h₂
  cases h₂
  simp at hv₁ hv₂
  rw [hv₁] at hv₂
  cases hv₂

/-! ## `Vec::retain` -/

/-- The type of `tacenta_spqr.alloc.vec.Vec.retain` (binder order as Aeneas
generated it: the closure's type parameter comes after `A`). -/
abbrev RetainFn :=
  {T : Type} → (A : Type) → {F : Type} → core.ops.function.FnMut F T Bool →
    alloc.vec.Vec T → F → Result (alloc.vec.Vec T)

/-- The shape of `SpqrT1.VecRetainTotal`. -/
def RetainTotal (f : RetainFn) : Prop :=
  ∀ {T F : Type} (A : Type) (inst : core.ops.function.FnMut F T Bool)
    (v : alloc.vec.Vec T) (g : F),
    ∃ r, f A inst v g = ok r ∧ r.length ≤ v.length ∧ ∀ x ∈ r.val, x ∈ v.val

/-- The shape of `SpqrT3.VecRetainAgrees`. -/
def RetainAgrees (f : RetainFn) : Prop :=
  ∀ {T F : Type} (A : Type) (inst : core.ops.function.FnMut F T Bool)
    (v : alloc.vec.Vec T) (g : F) (p : T → Bool)
    (_hp : ∀ x, inst.call_mut g x = ok (p x, g)),
    ∃ r, f A inst v g = ok r ∧ r.val = v.val.filter p

theorem VecRetainTotal_is :
    Tacenta.SpqrT1.VecRetainTotal ↔ RetainTotal @tacenta_spqr.alloc.vec.Vec.retain :=
  Iff.rfl

theorem VecRetainAgrees_is :
    Tacenta.SpqrT3.VecRetainAgrees ↔ RetainAgrees @tacenta_spqr.alloc.vec.Vec.retain :=
  Iff.rfl

theorem length_filter_le_max {T : Type} (p : T → Bool) (v : alloc.vec.Vec T) :
    (v.val.filter p).length ≤ Usize.max :=
  le_trans (List.length_filter_le _ _) v.property

open Classical in
/-- When the closure is a pure predicate that leaves its state alone -- the
only kind `VecRetainAgrees` speaks about -- filter by it; otherwise keep
everything, which `VecRetainTotal` permits. Classical, because recovering the
predicate from the closure is a choice. -/
noncomputable def retainWitness : RetainFn := fun {T} _A {F} inst v g =>
  if h : ∃ p : T → Bool, ∀ x, inst.call_mut g x = ok (p x, g) then
    ok ⟨v.val.filter (Classical.choose h), length_filter_le_max _ v⟩
  else ok v

theorem retainWitness_agrees : RetainAgrees @retainWitness := by
  intro T F A inst v g p hp
  have h : ∃ p : T → Bool, ∀ x, inst.call_mut g x = ok (p x, g) := ⟨p, hp⟩
  refine ⟨⟨v.val.filter (Classical.choose h), length_filter_le_max _ v⟩,
    by simp [retainWitness, h], ?_⟩
  apply List.filter_congr
  intro x _
  have := Classical.choose_spec h x
  rw [hp x] at this
  exact (Prod.mk.inj (Result.ok.inj this)).1.symm

theorem retain_agrees_satisfiable : ∃ f : RetainFn, RetainAgrees f :=
  ⟨@retainWitness, retainWitness_agrees⟩

theorem retain_total_satisfiable : ∃ f : RetainFn, RetainTotal f := by
  refine ⟨@retainWitness, ?_⟩
  intro T F A inst v g
  by_cases h : ∃ p : T → Bool, ∀ x, inst.call_mut g x = ok (p x, g)
  · exact ⟨⟨v.val.filter (Classical.choose h), length_filter_le_max _ v⟩,
      by simp [retainWitness, h], List.length_filter_le _ _,
      fun _ hx => List.mem_of_mem_filter hx⟩
  · exact ⟨v, by simp [retainWitness, h], le_refl _, fun _ hx => hx⟩

/-! ## The Braid's T3 boundary: over-strong shapes, and why they are not used

`BraidT3.lean`'s erasure and KEM hypotheses each have a natural stronger
statement that no implementation satisfies. This section keeps those shapes
as local copies and refutes them, so that the reasons for the weaker
statements stay checked:

- **The header split.** A `KemAgreesFor K` or `ValidateEkAgrees K` that
  quantified over every split of a header into `ekSeed ++ hek` would be
  refuted by any `K` whose `encaps1` or `hashEk` reads the split -- the
  model's own `toyKem` included -- since the real operation returns one
  value. The hypotheses fix the seed at 32 bytes, which is where the model
  itself splits.
- **Unbounded fuel.** An `EncoderRefines` demanding `EncoderSim n` for every
  `n` is false of every encoder, since a chunk index is a `u16`. The
  hypothesis demands it only while the model's position leaves room, and
  stepping requires the encoder live (`EncodersLive`, a precondition of
  `step_send_refines`).
- **One real answer, many model sources.** A `DecoderSim` quantifying over
  every model chunk sharing a real chunk's index asks one total real
  `message` (`DecoderMessageTotal`) for two different answers. `DecoderSim m`
  is parameterised by the message the decoder is collecting, and relates
  only codewords of `m`.

`DecoderMessageLenAgrees` needs no witness: the model's `Decoder.message`
checks the length, and the statement is the theorem
`Model.Braid.Decoder.message_length`.

The model of the erasure hypotheses lives in its own module,
`Translation/ErasureWitness.lean` (a Reed-Solomon code over `GF(2^256)`,
built from Mathlib, with `erasureAgrees_iff` tying the concrete hypothesis to
the shape it satisfies); it is a separate file because it is the one place
the translation package reaches for Mathlib's field theory. -/

section BraidRefutations

open Tacenta.BraidT3 tacenta_braid

/-- An RNG that never answers, enough to instantiate the `∀ {R}` clauses. -/
def dummyRng : rand_core_1.RngCore Unit where
  next_u32 _ := fail .panic
  next_u64 _ := fail .panic
  fill_bytes _ _ := fail .panic
  try_fill_bytes _ _ := fail .panic

def dummyCryptoRng : rand_core_1.CryptoRng Unit := {}

/-- The over-strong `encaps1` clause of `KemAgreesFor`: every split of the header. -/
def KemEncaps1AgreesUnsplit (K : Model.Braid.Kem) : Prop :=
  ∀ {R : Type} (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R)
      (header : Slice Std.U8) (rng : R),
    ∃ es ct1raw ssraw rng',
      tacenta_kem.encapsulate1 rc crc header rng =
        ok (core.result.Result.Ok (es, ct1raw, ssraw), rng') ∧
      (∀ ekSeed hek : Bytes, sliceOf header = ekSeed ++ hek →
        (K.encaps1 ekSeed hek).2.1 = vecOf ct1raw ∧
        (K.encaps1 ekSeed hek).2.2 = keyOf ssraw)

/-- At the model's toy KEM: the empty header has one split, `[] ++ []`,
under which the shared secret is `[]`, against a 32-byte `Array`. -/
theorem kemEncaps1_unsplit_toyKem_refutable : ¬ KemEncaps1AgreesUnsplit Model.Braid.toyKem := by
  intro henc
  obtain ⟨es, ct1, ss, rng', -, hsplit⟩ := henc dummyRng dummyCryptoRng ⟨[], by simp⟩ ()
  obtain ⟨-, hss⟩ := hsplit [] [] rfl
  have := congrArg List.length hss
  simp [keyOf, Model.Braid.toyKem, ss.property] at this

/-- The over-strong `ValidateEkAgrees`: every split of the header. -/
def ValidateEkAgreesUnsplit (K : Model.Braid.Kem) : Prop :=
  ∀ (header ekVector : Slice Std.U8) (ekSeed hek : Bytes),
    sliceOf header = ekSeed ++ hek →
    ∃ r, tacenta_kem.validate_ek header ekVector = ok r ∧
      (r = true ↔ K.hashEk ekSeed (sliceOf ekVector) = hek)

/-- The validation check, at the toy KEM: a header of 32 zero bytes
splits as `[] ++ hdr` (the hash of `[]` and `[]` is 32 zero bytes, so the
check must say `true`) and as `hdr ++ []` (no hash is empty, so it must say
`false`), and it says one thing. -/
theorem validateEk_unsplit_toyKem_refutable : ¬ ValidateEkAgreesUnsplit Model.Braid.toyKem := by
  intro h
  let hdr : Slice Std.U8 := ⟨List.replicate 32 0#u8, by
    simp [Usize.max, Usize.numBits]; cases System.Platform.numBits_eq <;> simp_all⟩
  have hs : sliceOf hdr = List.replicate 32 0 := by
    simp [sliceOf, hdr, Tacenta.BraidT3.u8]
  obtain ⟨r₁, h₁, hi₁⟩ := h hdr ⟨[], by simp⟩ [] (List.replicate 32 0) (by simp [hs])
  obtain ⟨r₂, h₂, hi₂⟩ := h hdr ⟨[], by simp⟩ (List.replicate 32 0) [] (by simp [hs])
  rw [h₁] at h₂
  cases h₂
  have t₁ : r₁ = true := hi₁.mpr (by simp [Model.Braid.toyKem, sliceOf])
  have t₂ : r₁ ≠ true := fun hr => by
    have := hi₂.mp hr
    simp [Model.Braid.toyKem] at this
  exact t₂ t₁

/-- The over-strong `EncoderRefines`: every number of steps. -/
def EncoderRefinesUnbounded (real : tacenta_erasure.Encoder) (model : Model.Braid.Encoder) : Prop :=
  ∀ n, EncoderSim n real model

theorem encoderSim_index_bound (n : Nat) (real : tacenta_erasure.Encoder) (src : List UInt8)
    (k : Nat) (h : EncoderSim (n + 1) real ⟨src, k⟩) : k ≤ 65535 := by
  obtain ⟨chunk, -, -, hidx, -⟩ := h
  have := chunk.index.hmax
  simp [Model.Braid.Encoder.nextChunk] at hidx
  simp at this
  omega

theorem encoderSim_step (real : tacenta_erasure.Encoder) (src : List UInt8) (k : Nat)
    (h : EncoderRefinesUnbounded real ⟨src, k⟩) :
    ∃ real', EncoderRefinesUnbounded real' ⟨src, k + 1⟩ := by
  obtain ⟨chunk, real', hnext, -, -⟩ := h 1
  refine ⟨real', fun n => ?_⟩
  obtain ⟨chunk', real'', hnext', -, hsim⟩ := h (n + 1)
  rw [hnext] at hnext'
  cases hnext'
  simpa [Model.Braid.Encoder.nextChunk] using hsim

/-- Walk a fresh encoder 65,536 steps; the next chunk's index does not fit a
`u16`. So no real encoder satisfies the unbounded shape, for any model
encoder at all. -/
theorem encoderRefines_unbounded_refutable (real : tacenta_erasure.Encoder) (src : List UInt8) :
    ¬ EncoderRefinesUnbounded real ⟨src, 0⟩ := by
  intro hsim
  have key : ∀ k, ∃ real, EncoderRefinesUnbounded real ⟨src, k⟩ := by
    intro k
    induction k with
    | zero => exact ⟨real, hsim⟩
    | succ k ih =>
      obtain ⟨r, hr⟩ := ih
      exact encoderSim_step r src k hr
  obtain ⟨r, hr⟩ := key 65536
  have := encoderSim_index_bound 0 r src 65536 (hr 1)
  omega

/-- The over-strong `DecoderSim`: every model chunk with the real chunk's index. -/
def DecoderSimAllSources : Nat → tacenta_erasure.Decoder → Model.Braid.Decoder → Prop
  | 0, _, _ => True
  | n + 1, real, model =>
    (∀ (chunk : tacenta_erasure.Chunk) (advanced : Bool) (real' : tacenta_erasure.Decoder),
      tacenta_erasure.Decoder.add_chunk real chunk = ok (advanced, real') →
      ∀ modelChunk : Model.Braid.Chunk, modelChunk.index = chunk.index.val →
        DecoderSimAllSources n real' (model.addChunk modelChunk)) ∧
    (∀ msg, tacenta_erasure.Decoder.message real = ok msg →
      msg.map vecOf = model.message)

/-- One real chunk, two model sources, one total `message`. Stated for a
fresh 32-byte decoder that satisfies the over-strong shape for two steps. -/
theorem decoderSim_allSources_refutable (real0 : tacenta_erasure.Decoder)
    (hsim : DecoderSimAllSources 2 real0 (Model.Braid.Decoder.new 32))
    (hdadd : Tacenta.BraidT1.DecoderAddChunkTotal)
    (hdmsg : Tacenta.BraidT1.DecoderMessageTotal) : False := by
  let c : tacenta_erasure.Chunk := ⟨0#u16, ⟨List.replicate 32 0#u8, by simp⟩⟩
  obtain ⟨⟨adv, real1⟩, hadd⟩ := hdadd real0 c
  obtain ⟨hstep, -⟩ := hsim
  let mc1 : Model.Braid.Chunk := ⟨List.replicate 32 1, 0⟩
  let mc2 : Model.Braid.Chunk := ⟨List.replicate 32 2, 0⟩
  have hs1 := hstep c adv real1 hadd mc1 rfl
  have hs2 := hstep c adv real1 hadd mc2 rfl
  obtain ⟨msg, hmsg⟩ := hdmsg real1
  have e1 := hs1.2 msg hmsg
  have e2 := hs2.2 msg hmsg
  have m1 : ((Model.Braid.Decoder.new 32).addChunk mc1).message
      = some (List.replicate 32 1) := by decide
  have m2 : ((Model.Braid.Decoder.new 32).addChunk mc2).message
      = some (List.replicate 32 2) := by decide
  rw [m1] at e1
  rw [m2] at e2
  rw [e1] at e2
  simp at e2

end BraidRefutations

end Tacenta.Satisfiability
