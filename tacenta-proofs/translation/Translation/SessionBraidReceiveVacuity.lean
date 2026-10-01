import Translation.UnitLifecyclePublicT1

/-!
# The Braid receive contract record is uninhabited

`BraidReceiveContracts` (`UnitLifecyclePublicT1.lean`) is a hypothesis of
`decrypt_ratchet_no_panic`, `decrypt_no_panic` and `establish_responder_no_panic`
through `DecryptRatchetContracts` and `EstablishResponderContracts`.  One of its
fields, `SessionUnitBraidT1.DecoderMessageTotal`, says `Decoder::message` returns for
every `Decoder`, with no premise on the decoder.  It is false.

A decoder that needs `K = (Usize.max + 1) / 32` chunks and holds `K` chunks has a
message, and `Decoder::message` appends 32 bytes per target chunk to a vector, so the
output would hold `32 * K = Usize.max + 1` bytes and the append that crosses
`Usize.max` fails.  The same argument gives a counterexample on either platform width:
`usize_max_facts` finds `K` by cases on `Usize.bounds_eq`, and nothing after it depends on
which case applies.

The decoder is not reachable through the crate, by reading the source (no theorem states
it).  The Braid calls `Decoder::new` only with protocol constants (the KEM and MAC lengths).
A decoder's `have` grows only through `add_chunk`, which admits one chunk per `u16` index, or
through `from_bytes`, which refuses `needed > MAX_CODEWORDS` and calls `Decoder::invariant`,
so `have` never holds more than 65536 chunks and a decoder that has a message has
`needed <= 65536`.  The witness below violates three clauses of `Decoder::invariant`.  What
this file shows is that the hypothesis, as stated, cannot hold, so the theorems that take it
hold vacuously.  It says nothing about the product.

The same field is the hypothesis `hdmsg` of `SessionUnitBraidT1.Braid.step_receive_no_panic`
and `Braid.receive_no_panic`, `SessionUnitBraidT3.step_receive_refines` and
`Braid.receive_refines`, and `SessionUnitBraidImportInv.Braid.decoded_receive_no_panic`.
Those theorems are vacuous for the same reason.

Nothing here assumes a property of any opaque axiom: the refutation does not depend on how
the unit's `Vec::truncate` behaves (section C proves it for every function in its place).
The repair is to state the field for decoders with `needed = chunk_count(size)` and
`needed <= 65536`, two of the clauses `Decoder::invariant` already checks (together they bound
`size` by two megabytes), and to supply that bound from the Braid invariant
(`GAP-REGISTER.md`, row `SESSION-CONTRACT-VACUITY`).
-/

open Aeneas Aeneas.Std Result
open tacenta_session_unit.tacenta_erasure

namespace Tacenta.SessionBraidReceiveVacuity

/-! ## A. Failure-allowing reasoning, and the refutation of `DecoderMessageTotal`

`OF x Q` says that `x` either fails or returns a value satisfying `Q`.  It is a partial
correctness statement: it is what lets a proof say "this loop cannot return normally". -/

def OF {α : Type} (x : Result α) (Q : α → Prop) : Prop :=
  (∃ e, x = Result.fail e) ∨ ∃ r, x = Result.ok r ∧ Q r

theorem OF.of_spec {α : Type} {x : Result α} {Q : α → Prop} (h : x ⦃ Q ⦄) : OF x Q := by
  obtain ⟨r, hx, hq⟩ := WP.spec_imp_exists h
  exact Or.inr ⟨r, hx, hq⟩

theorem OF.mono {α : Type} {x : Result α} {P Q : α → Prop} (h : OF x P)
    (hPQ : ∀ r, P r → Q r) : OF x Q := by
  rcases h with h | ⟨r, hr, hp⟩
  · exact Or.inl h
  · exact Or.inr ⟨r, hr, hPQ r hp⟩

theorem OF.bind {α β : Type} {x : Result α} {f : α → Result β} {P : α → Prop} {Q : β → Prop}
    (hx : OF x P) (hf : ∀ r, P r → OF (f r) Q) : OF (x >>= f) Q := by
  rcases hx with ⟨e, he⟩ | ⟨r, hr, hp⟩
  · left; exact ⟨e, by rw [he]; rfl⟩
  · rw [hr]; exact hf r hp

theorem OF.ok {α : Type} (a : α) {Q : α → Prop} (h : Q a) : OF (Result.ok a) Q :=
  Or.inr ⟨a, rfl, h⟩

/-- Loop reasoning when failure is allowed. -/
theorem loop_OF {α β : Type} (measure : α → Nat) (inv : α → Prop) (post : β → Prop)
    (body : α → Result (ControlFlow α β))
    (hBody : ∀ x, inv x → OF (body x) (fun r =>
      match r with
      | .done y => post y
      | .cont x' => inv x' ∧ measure x' < measure x)) :
    ∀ x, inv x → OF (loop body x) post := by
  suffices h : ∀ n x, measure x = n → inv x → OF (loop body x) post from
    fun x hx => h _ x rfl hx
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro x hn hx
    rw [loop]
    rcases hBody x hx with ⟨e, he⟩ | ⟨r, hr, hq⟩
    · left; exact ⟨e, by rw [he]⟩
    · cases r with
      | done y => right; exact ⟨y, by rw [hr], hq⟩
      | cont x' =>
        obtain ⟨hi', hlt⟩ := hq
        have := ih (measure x') (hn ▸ hlt) x' rfl hi'
        rw [hr]
        exact this

/-- `Vec::push` fails exactly when the vector already holds `Usize.max` elements. -/
theorem push_OF {α : Type} (v : alloc.vec.Vec α) (x : α) :
    OF (alloc.vec.Vec.push v x) (fun v' => v'.val.length = v.val.length + 1) := by
  by_cases h : v.val.length < Usize.max
  · apply OF.of_spec
    have := alloc.vec.Vec.push_spec v x h
    refine WP.spec_mono this ?_
    intro r hr
    simp [hr]
  · left
    unfold alloc.vec.Vec.push
    have hlen : v.val.length = Usize.max := le_antisymm v.property (not_lt.mp h)
    have h1 : ¬ (v.val.length + 1 ≤ U32.max) := by scalar_tac
    have h2 : ¬ (v.val.length + 1 ≤ Usize.max) := by scalar_tac
    simp [h1, h2]

/-- Sixteen lanes, two pushes each: the lane loop adds 32 bytes or fails. -/
theorem lanes_OF (k : Usize) (v : alloc.vec.Vec Chunk) (c : alloc.vec.Vec U16)
    (out0 : alloc.vec.Vec U8) (hk : k.val < Usize.max) :
    OF (Decoder.message_loop1_loop1 k v out0 c 0#usize)
      (fun y => y.val.length = out0.val.length + 32) := by
  unfold Decoder.message_loop1_loop1
  have := loop_OF
    (measure := fun p : alloc.vec.Vec U8 × Usize => 16 - p.2.val)
    (inv := fun p : alloc.vec.Vec U8 × Usize =>
      p.2.val ≤ 16 ∧ p.1.val.length = out0.val.length + 2 * p.2.val)
    (post := fun y : alloc.vec.Vec U8 => y.val.length = out0.val.length + 32)
    (fun p => Decoder.message_loop1_loop1.body k v c p.1 p.2) ?_ (out0, 0#usize)
    ⟨by simp, by simp⟩
  · exact this
  · rintro ⟨o1, j1⟩ ⟨hj, hl⟩
    simp only [] at hj hl
    unfold Decoder.message_loop1_loop1.body
    simp only [LANES, CHUNK_BYTES]
    have h16 : (32#usize / 2#usize : Result Usize) = ok 16#usize := rfl
    rw [h16]
    simp only [bind_tc_ok]
    split
    · rename_i hlt
      have hj16 : j1.val < 16 := by scalar_tac
      refine OF.bind (OF.of_spec (Tacenta.SessionUnitErasureT1.message_vals_no_panic k v j1
        (alloc.vec.Vec.with_capacity U16 k) 0#usize hj16
        (by simp [alloc.vec.Vec.with_capacity, alloc.vec.Vec.new]; scalar_tac))) ?_
      intro vals1 _
      refine OF.bind (OF.of_spec (Tacenta.SessionUnitErasureT1.evaluate_no_panic _ _)) ?_
      intro v1 _
      refine OF.bind (P := fun _ => True) (OF.of_spec (by step*)) ?_
      intro i1 _
      refine OF.bind (P := fun _ => True) (OF.ok _ (Q := fun _ => True) trivial) ?_
      intro i2 _
      refine OF.bind (push_OF o1 i2) ?_
      intro o2 ho2
      refine OF.bind (P := fun _ => True) (OF.ok _ (Q := fun _ => True) trivial) ?_
      intro i3 _
      refine OF.bind (push_OF o2 i3) ?_
      intro o3 ho3
      refine OF.bind (P := fun j2 : Usize => j2.val = j1.val + 1) (OF.of_spec (by step*)) ?_
      intro j2 hj2
      refine OF.ok _ ?_
      simp only []
      refine ⟨⟨by scalar_tac, by scalar_tac⟩, by scalar_tac⟩
    · refine OF.ok _ ?_
      simp only []
      have : j1.val = 16 := by scalar_tac
      omega

/-- `Vec::extend_from_slice` of 32 bytes fails exactly when the result would not fit. -/
theorem extend_OF (out : alloc.vec.Vec U8) (s : Slice U8) (hs : s.val.length = 32) :
    OF (alloc.vec.Vec.extend_from_slice core.clone.CloneU8 out s)
      (fun r => r.val.length = out.val.length + 32) := by
  by_cases h : out.val.length + 32 ≤ Usize.max
  · exact OF.of_spec (Tacenta.SessionUnitErasureT1.extend_slice32_spec out s hs h)
  · left
    unfold alloc.vec.Vec.extend_from_slice
    have : ¬ (out.length + s.length ≤ Usize.max) := by
      simp only [alloc.vec.Vec.length, Slice.length, hs]; exact h
    rw [dif_neg this]
    exact ⟨_, rfl⟩

/-- The target loop of `Decoder.message` either fails or returns exactly `32 * k` bytes.
Every turn, whether the chunk arrived directly or is interpolated, appends 32 bytes. -/
theorem targets_OF (k : Usize) (v : alloc.vec.Vec Chunk) (nodes w : alloc.vec.Vec U16)
    (out0 : alloc.vec.Vec U8) (hk : k.val < Usize.max) (hout : out0.val.length = 0) :
    OF (Decoder.message_loop1 k v nodes out0 w 0#usize)
      (fun y => y.val.length = 32 * k.val) := by
  unfold Decoder.message_loop1
  have := loop_OF
    (measure := fun p : alloc.vec.Vec U8 × Usize => k.val - p.2.val)
    (inv := fun p : alloc.vec.Vec U8 × Usize => p.2.val ≤ k.val ∧ p.1.val.length = 32 * p.2.val)
    (post := fun y : alloc.vec.Vec U8 => y.val.length = 32 * k.val)
    (fun p => Decoder.message_loop1.body k v nodes w p.1 p.2) ?_ (out0, 0#usize)
    ⟨by simp, by simpa using hout⟩
  · exact this
  · rintro ⟨o1, t1⟩ ⟨ht, hl⟩
    simp only [] at ht hl
    unfold Decoder.message_loop1.body
    simp only []
    split
    · rename_i hlt
      refine OF.bind (P := fun _ => True) (OF.ok _ (Q := fun _ => True) trivial) ?_
      intro target _
      refine OF.bind (P := fun _ => True) (OF.of_spec
        (Tacenta.SessionUnitErasureT1.message_direct_no_panic k v target none 0#usize)) ?_
      intro direct _
      cases direct with
      | none =>
        refine OF.bind (P := fun _ => True) (OF.of_spec
          (Tacenta.SessionUnitErasureT1.coefficients_no_panic _ _ _)) ?_
        intro c _
        refine OF.bind (lanes_OF k v c o1 hk) ?_
        intro o2 ho2
        refine OF.bind (P := fun t2 : Usize => t2.val = t1.val + 1) (OF.of_spec (by step*)) ?_
        intro t2 ht2
        refine OF.ok _ ?_
        simp only []
        refine ⟨⟨by scalar_tac, by scalar_tac⟩, by scalar_tac⟩
      | some c =>
        refine OF.bind (P := fun s : Slice U8 => s.val.length = 32)
          (OF.ok _ (Q := fun s : Slice U8 => s.val.length = 32)
            (Tacenta.SessionUnitErasureT1.to_slice_length_32 c.data)) ?_
        intro s hs
        refine OF.bind (extend_OF o1 s hs) ?_
        intro o2 ho2
        refine OF.bind (P := fun t2 : Usize => t2.val = t1.val + 1) (OF.of_spec (by step*)) ?_
        intro t2 ht2
        refine OF.ok _ ?_
        simp only []
        refine ⟨⟨by scalar_tac, by scalar_tac⟩, by scalar_tac⟩
    · refine OF.ok _ ?_
      simp only []
      have : t1.val = k.val := by scalar_tac
      omega

/-- **`Decoder.message` cannot return a value** when the decoder holds at least `needed`
chunks and `32 * needed` does not fit a `usize`.  This holds for every interpretation of the
unit's axioms: the failing step is before `Vec.truncate`. -/
theorem message_OF_false (d : Decoder) (hh : d.needed.val ≤ d.«have».val.length)
    (hk : d.needed.val < Usize.max) (hbig : Usize.max < 32 * d.needed.val) :
    OF (Decoder.message d) (fun _ => False) := by
  have hm : Decoder.has_message d = ok true := by
    have : d.needed ≤ d.«have».len := by
      rw [UScalar.le_equiv]; simpa using hh
    simp [Decoder.has_message, this]
  unfold Decoder.message
  rw [hm]
  simp only [bind_tc_ok, if_true]
  refine OF.bind (P := fun _ => True) (OF.of_spec
    (Tacenta.SessionUnitErasureT1.message_nodes_no_panic d.needed d.«have»
      (alloc.vec.Vec.with_capacity U16 d.needed) 0#usize
      (by simp [alloc.vec.Vec.with_capacity, alloc.vec.Vec.new]; exact hk))) ?_
  intro nodes1 _
  refine OF.bind (P := fun _ => True) (OF.of_spec
    (Tacenta.SessionUnitErasureT1.weights_no_panic _)) ?_
  intro w _
  refine OF.bind (P := fun _ => False) (OF.mono
    (targets_OF d.needed d.«have» nodes1 w (alloc.vec.Vec.with_capacity U8 d.size) hk
      (by simp [alloc.vec.Vec.with_capacity, alloc.vec.Vec.new])) ?_) ?_
  · intro y hy
    have := y.property
    scalar_tac
  · intro out1 h
    exact h.elim

/-- A number `K` with `32 * K = Usize.max + 1`, on whichever width the platform has. -/
theorem usize_max_facts : ∃ K : Nat, 32 * K = Usize.max + 1 ∧ K < Usize.max := by
  rcases Usize.bounds_eq with h | h
  · refine ⟨2^27, ?_, ?_⟩
    · rw [h]; simp [U32.max, U32.numBits]
    · rw [h]; simp [U32.max, U32.numBits]
  · refine ⟨2^59, ?_, ?_⟩
    · rw [h]; simp [U64.max, U64.numBits]
    · rw [h]; simp [U64.max, U64.numBits]

/-- **`DecoderMessageTotal` is false.**  The witness is a decoder of size 0 that needs
`K = (Usize.max + 1) / 32` chunks (2^27 on a 32-bit target, 2^59 on a 64-bit one) and holds
`K` copies of one chunk.  `message` would have to write `32 * K = Usize.max + 1` bytes. -/
theorem decoderMessage_not_total : ¬ Tacenta.SessionUnitBraidT1.DecoderMessageTotal := by
  intro H
  obtain ⟨K, hK32, hKlt⟩ := usize_max_facts
  have hKb : K < 2 ^ UScalarTy.Usize.numBits := by
    have : Usize.max < 2 ^ UScalarTy.Usize.numBits := by
      scalar_tac
    omega
  let needed : Usize := Usize.ofNatCore K hKb
  let c : Chunk := ⟨0#u16, Array.repeat 32#usize 0#u8⟩
  let hv : alloc.vec.Vec Chunk := ⟨List.replicate K c, by simp; omega⟩
  let d : Decoder := ⟨0#usize, needed, hv⟩
  obtain ⟨r, hr⟩ := H d
  have hneed : d.needed.val = K := Usize.ofNatCore_val_eq hKb
  have hh : d.needed.val ≤ d.«have».val.length := by
    simp [d, hv, hneed]
  have := message_OF_false d hh (by omega) (by omega)
  rcases this with ⟨e, he⟩ | ⟨r', hr', hf⟩
  · rw [he] at hr; cases hr
  · exact hf

/-! ## B. What the refutation does to the contract records -/

theorem braidReceiveContracts_false : ¬ Tacenta.UnitLifecycleT1.BraidReceiveContracts :=
  fun h => decoderMessage_not_total h.decoderMessage

theorem decryptRatchetContracts_false {R : Type} (rc : tacenta_session_unit.rand_core_1.RngCore R) :
    ¬ Tacenta.UnitLifecycleT1.DecryptRatchetContracts rc :=
  fun h => braidReceiveContracts_false h.braid

theorem establishResponderContracts_empty {R : Type}
    (rc : tacenta_session_unit.rand_core_1.RngCore R) :
    ¬ Nonempty (Tacenta.UnitLifecycleT1.EstablishResponderContracts rc) :=
  fun ⟨h⟩ => decryptRatchetContracts_false rc h.decrypt

/-! ## C. Independence from `Vec::truncate`

`Decoder::message` calls the unit's `Vec::truncate` last, on the vector it has built.  Here the
call is replaced by an arbitrary function `tr`; the refutation goes through for every `tr`, so
no property of that opaque operation is assumed. -/

/-- `Decoder.message` with `Vec.truncate` replaced by an arbitrary function `tr`. -/
def messageP (tr : alloc.vec.Vec U8 → Usize → Result (alloc.vec.Vec U8)) (self : Decoder) :
    Result (Option (alloc.vec.Vec U8)) := do
  let b ← Decoder.has_message self
  if b = true then
    let nodes := alloc.vec.Vec.with_capacity U16 self.needed
    let nodes1 ← Decoder.message_loop0 self.needed self.«have» nodes 0#usize
    let out : alloc.vec.Vec U8 := alloc.vec.Vec.with_capacity U8 self.size
    let s : Slice U16 := nodes1.deref
    let w ← weights s
    let out1 ← Decoder.message_loop1 self.needed self.«have» nodes1 out w 0#usize
    let out2 ← tr out1 self.size
    ok (some out2)
  else ok none

/-- The real `Decoder::message` is `messageP` at the unit's `Vec::truncate`. -/
theorem message_eq_messageP (d : Decoder) :
    Decoder.message d = messageP (tacenta_session_unit.alloc.vec.Vec.truncate Global) d := by
  unfold Decoder.message messageP
  rfl

theorem messageP_OF_false (tr : alloc.vec.Vec U8 → Usize → Result (alloc.vec.Vec U8))
    (d : Decoder) (hh : d.needed.val ≤ d.«have».val.length)
    (hk : d.needed.val < Usize.max) (hbig : Usize.max < 32 * d.needed.val) :
    OF (messageP tr d) (fun _ => False) := by
  have hm : Decoder.has_message d = ok true := by
    have : d.needed ≤ d.«have».len := by
      rw [UScalar.le_equiv]; simpa using hh
    simp [Decoder.has_message, this]
  unfold messageP
  rw [hm]
  simp only [bind_tc_ok, if_true]
  refine OF.bind (P := fun _ => True) (OF.of_spec
    (Tacenta.SessionUnitErasureT1.message_nodes_no_panic d.needed d.«have»
      (alloc.vec.Vec.with_capacity U16 d.needed) 0#usize
      (by simp [alloc.vec.Vec.with_capacity, alloc.vec.Vec.new]; exact hk))) ?_
  intro nodes1 _
  refine OF.bind (P := fun _ => True) (OF.of_spec
    (Tacenta.SessionUnitErasureT1.weights_no_panic _)) ?_
  intro w _
  refine OF.bind (P := fun _ => False) (OF.mono
    (targets_OF d.needed d.«have» nodes1 w (alloc.vec.Vec.with_capacity U8 d.size) hk
      (by simp [alloc.vec.Vec.with_capacity, alloc.vec.Vec.new])) ?_) ?_
  · intro y hy
    have := y.property
    scalar_tac
  · intro out1 h
    exact h.elim

/-- With `Vec::truncate` replaced by any function whatever, `Decoder::message` still fails to
return for some decoder.  So the refutation does not depend on how the unit's `Vec::truncate`
behaves. -/
theorem all_tr_refute : ∀ tr : alloc.vec.Vec U8 → Usize → Result (alloc.vec.Vec U8),
    ¬ (∀ d : Decoder, ∃ r, messageP tr d = ok r) := by
  intro tr H
  obtain ⟨K, hK32, hKlt⟩ := usize_max_facts
  have hKb : K < 2 ^ UScalarTy.Usize.numBits := by
    have : Usize.max < 2 ^ UScalarTy.Usize.numBits := by scalar_tac
    omega
  let needed : Usize := Usize.ofNatCore K hKb
  let c : Chunk := ⟨0#u16, Array.repeat 32#usize 0#u8⟩
  let hv : alloc.vec.Vec Chunk := ⟨List.replicate K c, by simp; omega⟩
  let d : Decoder := ⟨0#usize, needed, hv⟩
  obtain ⟨r, hr⟩ := H d
  have hneed : d.needed.val = K := Usize.ofNatCore_val_eq hKb
  have hh : d.needed.val ≤ d.«have».val.length := by simp [d, hv, hneed]
  have := messageP_OF_false tr d hh (by omega) (by omega)
  rcases this with ⟨e, he⟩ | ⟨r', hr', hf⟩
  · rw [he] at hr; cases hr
  · exact hf


end Tacenta.SessionBraidReceiveVacuity


/-! ## Axiom pins

The axiom bases of the six results, held by the build. Except for `all_tr_refute`, which lists
the three standard axioms only, the lists name constants that occur in the statements of the
results, not assumptions the proofs make: `decoderMessage_not_total` does not depend on any opaque
operation's behaviour (`Vec::truncate` occurs in it only as a term in the statement of the field
it refutes, and `all_tr_refute` holds for every function in its place). The corollaries list the
constants their record types mention, and `message_eq_messageP` lists `Vec::truncate`, which
occurs on both sides of the equation. -/

/--
info: 'Tacenta.SessionBraidReceiveVacuity.decoderMessage_not_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.alloc.vec.Vec.truncate]
-/
#guard_msgs in
#print axioms Tacenta.SessionBraidReceiveVacuity.decoderMessage_not_total

/--
info: 'Tacenta.SessionBraidReceiveVacuity.braidReceiveContracts_false' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kdf.hkdf_sha256,
 tacenta_session_unit.tacenta_kdf.hmac_sha256,
 tacenta_session_unit.tacenta_kem.CT1_LEN,
 tacenta_session_unit.tacenta_kem.CT2_LEN,
 tacenta_session_unit.tacenta_kem.EK_VECTOR_LEN,
 tacenta_session_unit.tacenta_kem.EncapsState,
 tacenta_session_unit.tacenta_kem.HEADER_LEN,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair,
 tacenta_session_unit.tacenta_kem.encapsulate2,
 tacenta_session_unit.tacenta_kem.validate_ek,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_session_unit.zeroize.Zeroizing.new,
 tacenta_session_unit.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.alloc.vec.Vec.truncate,
 tacenta_session_unit.core.num.Usize.div_ceil,
 tacenta_session_unit.tacenta_kem.EncapsState.Insts.CoreCloneClone.clone,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 tacenta_session_unit.core.option.Option.Insts.CoreCloneClone.clone,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index]
-/
#guard_msgs in
#print axioms Tacenta.SessionBraidReceiveVacuity.braidReceiveContracts_false

/--
info: 'Tacenta.SessionBraidReceiveVacuity.decryptRatchetContracts_false' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kdf.hkdf_sha256,
 tacenta_session_unit.tacenta_kdf.hmac_sha256,
 tacenta_session_unit.tacenta_kem.CT1_LEN,
 tacenta_session_unit.tacenta_kem.CT2_LEN,
 tacenta_session_unit.tacenta_kem.EK_VECTOR_LEN,
 tacenta_session_unit.tacenta_kem.EncapsState,
 tacenta_session_unit.tacenta_kem.HEADER_LEN,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair,
 tacenta_session_unit.tacenta_kem.encapsulate2,
 tacenta_session_unit.tacenta_kem.validate_ek,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.rand_core_1.error.Error,
 tacenta_session_unit.tacenta_boundary.aead.decrypt,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_session_unit.zeroize.Zeroizing.new,
 tacenta_session_unit.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.TupleABC.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.alloc.vec.Vec.capacity,
 tacenta_session_unit.alloc.vec.Vec.pop,
 tacenta_session_unit.alloc.vec.Vec.truncate,
 tacenta_session_unit.core.num.Usize.div_ceil,
 tacenta_session_unit.core.option.Option.as_mut,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.agree,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.from_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.public_key,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.to_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.from_bytes,
 tacenta_session_unit.zeroize.Zeroize.Blanket.zeroize,
 tacenta_session_unit.tacenta_kem.EncapsState.Insts.CoreCloneClone.clone,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 tacenta_session_unit.alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.core.option.Option.Insts.CoreCloneClone.clone,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes.eq,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index]
-/
#guard_msgs in
#print axioms Tacenta.SessionBraidReceiveVacuity.decryptRatchetContracts_false

/--
info: 'Tacenta.SessionBraidReceiveVacuity.establishResponderContracts_empty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kdf.hkdf_sha256,
 tacenta_session_unit.tacenta_kdf.hmac_sha256,
 tacenta_session_unit.tacenta_kem.CT1_LEN,
 tacenta_session_unit.tacenta_kem.CT2_LEN,
 tacenta_session_unit.tacenta_kem.EK_VECTOR_LEN,
 tacenta_session_unit.tacenta_kem.EncapsState,
 tacenta_session_unit.tacenta_kem.HEADER_LEN,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair,
 tacenta_session_unit.tacenta_kem.encapsulate2,
 tacenta_session_unit.tacenta_kem.validate_ek,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.rand_core_1.error.Error,
 tacenta_session_unit.tacenta_boundary.aead.decrypt,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_boundary.dh.is_prime_order_public,
 tacenta_session_unit.tacenta_boundary.kem.KeyPair,
 tacenta_session_unit.tacenta_boundary.kem.decapsulate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_session_unit.zeroize.Zeroizing.new,
 tacenta_session_unit.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.TupleABC.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.alloc.vec.Vec.capacity,
 tacenta_session_unit.alloc.vec.Vec.pop,
 tacenta_session_unit.alloc.vec.Vec.truncate,
 tacenta_session_unit.core.num.Usize.div_ceil,
 tacenta_session_unit.core.option.Option.as_mut,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.agree,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.from_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.public_key,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.to_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.from_bytes,
 tacenta_session_unit.zeroize.Zeroize.Blanket.zeroize,
 tacenta_session_unit.tacenta_kem.EncapsState.Insts.CoreCloneClone.clone,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 tacenta_session_unit.alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.core.option.Option.Insts.CoreCloneClone.clone,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes.eq,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index]
-/
#guard_msgs in
#print axioms Tacenta.SessionBraidReceiveVacuity.establishResponderContracts_empty

/--
info: 'Tacenta.SessionBraidReceiveVacuity.message_eq_messageP' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.alloc.vec.Vec.truncate]
-/
#guard_msgs in
#print axioms Tacenta.SessionBraidReceiveVacuity.message_eq_messageP

/--
info: 'Tacenta.SessionBraidReceiveVacuity.all_tr_refute' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.SessionBraidReceiveVacuity.all_tr_refute
