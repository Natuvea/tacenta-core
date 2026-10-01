import Translation.ErasureWitness
import Translation.BraidPreserveDecoder

/-!
# A model of the one law the Braid's preservation theorems add

`BraidPreserveDecoder.lean` states `NewMsgLen`, the law `BraidPreserve.lean` takes about the opaque
erasure decoder: a decoder `Decoder::new(m)` builds never returns a message longer than `m`, however
many chunks it is given and however often it is cloned.  A law about opaque operations can be
refutable without any theorem noticing, so this file shows it has a model.

`ErasureWitness.lean` already exhibits one implementation of the opaque erasure operations (a
Reed-Solomon code over `GF(2^256)`) that satisfies `ErasureAgrees`, `ErasureCloneAgrees` and the
seven erasure totality assumptions together.  `erasure_laws_satisfiable` shows the same
implementation satisfies `NewMsgLen` as well, so the four hold at once.  The statement and the proof
do not mention the platform width: they are about an arbitrary `Usize`, so they cover the 32-bit
and the 64-bit case alike (`model_for_both_widths`).

Nothing here says the real crate satisfies the law.  It does by construction (the real
`Decoder::message` ends in `out.truncate(self.size)`), and the session unit proves the analogue from
the translated body (`SessionUnitBraidPreserveDecoder.lean`).
-/

open Aeneas Aeneas.Std Result
open tacenta_braid
open Tacenta.ErasureWitness

namespace Tacenta.BraidPreserveWitness

section Shape
variable {Enc Dec : Type} (A : Api Enc Dec)

/-- `Tacenta.BraidPreserveDecoder.Reach` over any implementation of the decoder operations. -/
inductive ReachA : Dec → Dec → Prop
  | refl (d : Dec) : ReachA d d
  | add {d d' d'' : Dec} {c : tacenta_erasure.Chunk} {b : Bool} :
      A.add d c = ok (b, d') → ReachA d' d'' → ReachA d d''
  | clone {d d' d'' : Dec} : A.cloneDec d = ok d' → ReachA d' d'' → ReachA d d''

/-- `Tacenta.BraidPreserveDecoder.Good` over any implementation. -/
def GoodA (n : Nat) (d : Dec) : Prop :=
  ∀ d', ReachA A d d' → ∀ v, A.msg d' = ok (some v) → v.length ≤ n

/-- `Tacenta.BraidPreserveDecoder.NewMsgLen` over any implementation. -/
def NewMsgLenShape : Prop :=
  ∀ (m : Usize) (d : Dec), A.dnew m = ok d → GoodA A m.val d

end Shape

/-! ## The shape is the law at the real operations -/

theorem reach_iff (d d' : tacenta_erasure.Decoder) :
    Tacenta.BraidPreserveDecoder.Reach d d' ↔ ReachA realApi d d' := by
  constructor
  · intro h
    induction h with
    | refl d => exact ReachA.refl d
    | add h _ ih => exact ReachA.add h ih
    | clone h _ ih => exact ReachA.clone h ih
  · intro h
    induction h with
    | refl d => exact Tacenta.BraidPreserveDecoder.Reach.refl d
    | add h _ ih => exact Tacenta.BraidPreserveDecoder.Reach.add h ih
    | clone h _ ih => exact Tacenta.BraidPreserveDecoder.Reach.clone h ih

theorem good_iff (n : Nat) (d : tacenta_erasure.Decoder) :
    Tacenta.BraidPreserveDecoder.Good n d ↔ GoodA realApi n d := by
  simp only [Tacenta.BraidPreserveDecoder.Good, GoodA, reach_iff]
  rfl

/-- **`NewMsgLen` is the shape at the real operations**, so a model of the shape is a model of
the law, and a change to the statement of the law stops this file from building. -/
theorem newMsgLen_iff :
    Tacenta.BraidPreserveDecoder.NewMsgLen ↔ NewMsgLenShape realApi := by
  simp only [Tacenta.BraidPreserveDecoder.NewMsgLen, NewMsgLenShape, good_iff]
  rfl

/-! ## The witness satisfies it -/

/-- Adding a chunk and cloning keep the size the decoder was built for. -/
theorem reach_size {d d' : Dec} (h : ReachA api d d') : d'.size = d.size := by
  induction h with
  | refl d => rfl
  | add h _ ih =>
    rename_i d0 d1 d2 c b
    simp only [api, decAdd] at h
    split at h
    · simp only [ok.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      exact ih
    · simp only [ok.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      exact ih
  | clone h _ ih =>
    simp only [api, ok.injEq] at h
    subst h
    exact ih

/-- A message the witness decoder returns is at most as long as the size it was built for. -/
theorem msg_length_le {d : Dec} {v : alloc.vec.Vec Std.U8} (h : api.msg d = ok (some v)) :
    v.length ≤ d.size := by
  simp only [api, decMsg] at h
  split at h
  · split at h
    · simp only [ok.injEq, Option.some.injEq] at h
      subst h
      simp only [alloc.vec.Vec.length, decode, List.length_take]
      exact Nat.min_le_left _ _
    · simp at h
  · simp at h

/-- **The witness decoder never returns a message longer than the size it was built for**, however
many chunks it is given and however often it is cloned. -/
theorem api_newMsgLen : NewMsgLenShape api := by
  intro m d hd d' hr v hv
  simp only [api, decNew, ok.injEq] at hd
  subst hd
  have h1 := reach_size hr
  have h2 := msg_length_le hv
  simpa [h1] using h2

/-- **The law has a model, together with the three erasure hypotheses the Braid proofs already
take.**  One implementation of the opaque erasure operations satisfies, exactly as `BraidT3.lean`,
`BraidT1.lean` and `BraidPreserveDecoder.lean` state them and all at once, `ErasureAgrees`,
`ErasureCloneAgrees`, the seven erasure totality assumptions and `NewMsgLen`.  Jointly matters: a
law can be refutable together with hypotheses that are each satisfiable alone. -/
theorem erasure_laws_satisfiable :
    ∃ (Enc Dec : Type) (A : Api Enc Dec),
      ErasureAgrees A ∧ ErasureCloneAgrees A ∧ ErasureTotals A ∧ NewMsgLenShape A :=
  ⟨Enc, Dec, api, api_agrees, api_cloneAgrees, api_totals, api_newMsgLen⟩

/-- The width of `usize`, which the translation leaves abstract, is 32 or 64 bits
(`Usize.bounds_eq`).  The model above is built over an arbitrary `Usize` and no step uses the
width, so it is a model at each. -/
theorem model_for_both_widths :
    (Usize.max = U32.max ∨ Usize.max = U64.max) ∧ NewMsgLenShape api :=
  ⟨Usize.bounds_eq, api_newMsgLen⟩

end Tacenta.BraidPreserveWitness

/-! ## Axiom pins

The axiom base of each result, held by the build. -/

/--
info: 'Tacenta.BraidPreserveWitness.newMsgLen_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_erasure.Decoder,
 tacenta_erasure.Encoder,
 tacenta_erasure.Decoder.add_chunk,
 tacenta_erasure.Decoder.message,
 tacenta_erasure.Decoder.new,
 tacenta_erasure.Encoder.new,
 tacenta_erasure.Encoder.next_chunk,
 tacenta_erasure.Decoder.Insts.CoreCloneClone.clone,
 tacenta_erasure.Encoder.Insts.CoreCloneClone.clone]
-/
#guard_msgs in
#print axioms Tacenta.BraidPreserveWitness.newMsgLen_iff

/--
info: 'Tacenta.BraidPreserveWitness.api_newMsgLen' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.BraidPreserveWitness.api_newMsgLen

/--
info: 'Tacenta.BraidPreserveWitness.erasure_laws_satisfiable' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.BraidPreserveWitness.erasure_laws_satisfiable

/--
info: 'Tacenta.BraidPreserveWitness.model_for_both_widths' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.BraidPreserveWitness.model_for_both_widths

/-! ## Statement pins

The axiom pins hold the constants a result depends on and not what it says.  These hold the
statements of the central results. -/

/--
info: Tacenta.BraidPreserveWitness.newMsgLen_iff :
  Tacenta.BraidPreserveDecoder.NewMsgLen ↔ Tacenta.BraidPreserveWitness.NewMsgLenShape realApi
-/
#guard_msgs in
#check Tacenta.BraidPreserveWitness.newMsgLen_iff

/--
info: Tacenta.BraidPreserveWitness.erasure_laws_satisfiable :
  ∃ Enc Dec A, ErasureAgrees A ∧ ErasureCloneAgrees A ∧ ErasureTotals A ∧ Tacenta.BraidPreserveWitness.NewMsgLenShape A
-/
#guard_msgs in
#check Tacenta.BraidPreserveWitness.erasure_laws_satisfiable
