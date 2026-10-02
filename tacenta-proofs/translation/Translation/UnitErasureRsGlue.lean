import Translation.UnitErasureRsStatements

/-!
# `ErasureAgrees` of the complete Session unit, from the Reed-Solomon statements

Assembles the nine statements of `UnitErasureRsStatements.lean` into the decoder half of
`SessionUnitBraidT3.ErasureAgrees`, and then the whole of it with the encoder half
`UnitSatisfiabilityErasureAgrees.erasureAgrees_encoder`, under the two laws `DivCeilValue` and
`TruncatePrefix`.

* `codeword_bytes`: a chunk the translated encoder emits is the model's codeword of the message.
* `DInv` and `decoderSim_of_inv`: the simulation of the model decoder by the translated decoder,
  by induction on the number of steps, from an invariant that ties the translated decoder's held
  chunks to `Model.Erasure` and the `Model.Braid` decoder's chunk list.
* `erasureAgrees_decoder`: for every size, `Decoder::new` returns a decoder that refines the
  model's fresh decoder.
* `erasureAgrees`: `ErasureAgrees` itself.

## What it does not show

* The two laws.  `DivCeilValue` (that `usize::div_ceil` at divisor 32 returns the rounded-up
  quotient) and `TruncatePrefix` (that `Vec::truncate` keeps the prefix) are hypotheses about
  opaque standard-library functions.  `UnitSatisfiabilityBraidAgreements.lean` shows that both
  hold in one model of the unit's opaque constants together with the other agreements; it does
  not show that the real functions meet them.
* Anything beyond the kernel's three axioms and the two opaque constants the laws are about
  (`usize::div_ceil` and `Vec::truncate`): the model's field and polynomial lemmas that the kernel
  and recovery statements use are kernel proofs, so `erasureAgrees_decoder` and `erasureAgrees`
  carry no compiler-trust axiom.
-/

open Aeneas Aeneas.Std Result
open tacenta_session_unit.tacenta_erasure

namespace Tacenta.UnitErasureRs.Glue

open Tacenta.UnitErasureRs
open Tacenta.SessionUnitBraidT3 (CodewordOf NthChunk EncoderSim DecoderSim DecoderRefines
  ErasureAgrees EncoderRefines Stepped u8 sliceOf vecOf)
open Tacenta.UnitSatisfiabilityErasureAgrees (next_chunk_shape' u16max_val)
open Tacenta.UnitSatisfiabilityBraidAgreements (TruncatePrefix)

/-! ## A chunk of the translated encoder is the model's codeword -/

/-- `NthChunk i enc chunk` for a live encoder whose chunk store is `store`: the chunk is the
model's codeword at index `enc.next + i`, and has that index. -/
theorem nthChunk_value (store : alloc.vec.Vec (Array Std.U8 32#usize))
    (hlen : store.val.length ≤ 65536) :
    ∀ (i : ℕ) (enc : Encoder) (chunk : Chunk), enc.chunks = store → enc.exhausted = false →
      enc.next.val + i ≤ 65535 → NthChunk i enc chunk →
      chunk.index.val = enc.next.val + i ∧
      cbytes chunk = Model.Erasure.codeword (storeBytes store) (enc.next.val + i) := by
  intro i
  induction i with
  | zero =>
    intro enc chunk hst hex hle hnth
    obtain ⟨enc', hn⟩ := hnth
    obtain ⟨r, hr, hshape⟩ := WP.spec_imp_exists (next_chunk_shape' enc hex)
    obtain ⟨r2, hr2, hbytes⟩ := WP.spec_imp_exists
      (E_next enc hex (by rw [hst]; exact hlen))
    rw [hr] at hn; cases hn
    rw [hr] at hr2; cases hr2
    obtain ⟨⟨data, hd⟩, -, -, -⟩ := hshape
    simp only at hd hbytes
    have hch : chunk = { index := enc.next, data := data } := by
      have := hd; simp at this; exact this
    refine ⟨?_, ?_⟩
    · rw [hch]; simp
    · have := hbytes chunk (by rw [hd])
      rw [hst] at this
      simpa using this
  | succ i ih =>
    intro enc chunk hst hex hle hnth
    obtain ⟨c, enc', hn, hrest⟩ := hnth
    obtain ⟨r, hr, hshape⟩ := WP.spec_imp_exists (next_chunk_shape' enc hex)
    rw [hr] at hn; cases hn
    obtain ⟨-, hch, hmax, hnmax⟩ := hshape
    simp only at hch hmax hnmax
    have hne : enc.next ≠ core.num.U16.MAX := by
      intro h
      have := u16max_val
      rw [← h] at this
      omega
    obtain ⟨hex', hnext'⟩ := hnmax hne
    obtain ⟨h1, h2⟩ := ih enc' chunk (by rw [hch, hst]) hex' (by omega) hrest
    refine ⟨by omega, ?_⟩
    have : enc'.next.val + i = enc.next.val + (i + 1) := by omega
    rw [this] at h2
    exact h2

/-- **A chunk the translated encoder emits is the model's codeword of the message**, at the
chunk's own index. -/
theorem codeword_bytes (hdiv : Tacenta.SessionUnitDecoderBound.DivCeilValue) (m : List UInt8)
    (c : Chunk) (h : CodewordOf m c) :
    cbytes c = Model.Erasure.codeword (Model.Erasure.chunks m) c.index.val := by
  obtain ⟨s, enc0, hs, hnew, hnth⟩ := h
  obtain ⟨r, hr, hpost⟩ := WP.spec_imp_exists (E_new hdiv s)
  rw [hnew] at hr; cases hr
  obtain ⟨hnext, hex, hstore⟩ := hpost
  have hlen : enc0.chunks.val.length ≤ 65536 := by
    have := congrArg List.length hstore
    simp [storeBytes] at this
    omega
  have hidx := c.index.hBounds
  have hidx' : c.index.val ≤ 65535 := by scalar_tac
  obtain ⟨-, hv⟩ := nthChunk_value enc0.chunks hlen c.index.val enc0 c rfl hex
    (by rw [hnext]; simpa using hidx') hnth
  have h0 : enc0.next.val = 0 := by rw [hnext]; rfl
  rw [h0, Nat.zero_add, hstore] at hv
  rw [hv, hs]
  exact Model.Erasure.codeword_take_maxCodewords _ (by simp [Model.Erasure.maxCodewords]; omega)

/-! ## The two models of the decoder, and the invariant that ties them to the translated decoder -/

theorem nodup_length_le (L : List ℕ) (hn : L.Nodup) (N : ℕ) (hl : ∀ i ∈ L, i < N) :
    L.length ≤ N := by
  have h1 : L.toFinset ⊆ Finset.range N := fun i hi => by
    simpa using hl i (List.mem_toFinset.mp hi)
  have h2 := Finset.card_le_card h1
  rw [List.toFinset_card_of_nodup hn] at h2
  simpa using h2

/-- The model decoder of `Model.Braid` has no message while it holds fewer chunks than it needs. -/
theorem model_message_none (md : Model.Braid.Decoder)
    (h : md.chunks.length < (md.size + 31) / 32) : md.message = none := by
  unfold Model.Braid.Decoder.message Model.Braid.Decoder.hasMessage
  have : ¬ (md.chunks.length * Model.Braid.chunkBytes ≥ md.size) := by
    simp only [Model.Braid.chunkBytes]; omega
  simp [this]

/-- And it has the source as its message once it holds enough chunks of one message. -/
theorem model_message_some (md : Model.Braid.Decoder) (m : List UInt8)
    (hsrc : ∀ c ∈ md.chunks, c.source = m) (hsz : m.length = md.size)
    (h : (md.size + 31) / 32 ≤ md.chunks.length) : md.message = some m := by
  have hhas : md.chunks.length * Model.Braid.chunkBytes ≥ md.size := by
    simp only [Model.Braid.chunkBytes]; omega
  unfold Model.Braid.Decoder.message Model.Braid.Decoder.hasMessage
  simp only [ge_iff_le, decide_eq_true_eq] at hhas ⊢
  rw [if_pos hhas]
  cases hc : md.chunks with
  | nil =>
    have : md.size = 0 := by rw [hc] at h; simp at h; omega
    have hm : m = [] := by
      apply List.eq_nil_of_length_eq_zero; omega
    simp [hm]
  | cons c rest =>
    have hcs : c.source = m := hsrc c (by rw [hc]; simp)
    simp only [hcs, hsz, beq_self_eq_true, Bool.and_true, List.all_eq_true, beq_iff_eq]
    rw [if_pos]
    intro x hx
    exact hsrc x (by rw [hc]; simp [hx])

/-- With fewer held chunks than needed, the translated `message` returns `none`. -/
theorem message_not_full (d : Decoder) (h : d.«have».val.length < d.needed.val) :
    Decoder.message d = ok none := by
  unfold Decoder.message Decoder.has_message
  have : ¬ (d.«have».len ≥ d.needed) := by
    intro hh
    have h1 : (d.«have».len).val = d.«have».val.length := alloc.vec.Vec.len_val d.«have»
    have h2 : d.needed ≤ d.«have».len := hh
    have h3 := (UScalar.le_equiv _ _).mp h2
    omega
  simp [this]

/-- The invariant of a translated decoder `d` and a model decoder `md` collecting the message `m`.

The translated decoder holds the first `needed` distinct indices it was offered, in order; the
model decoder holds every distinct index it was offered, newest first; and each held codeword is
the model's codeword of `m` at its index. -/
structure DInv (m : List UInt8) (d : Decoder) (md : Model.Braid.Decoder) : Prop where
  size_eq : d.size.val = md.size
  size_len : md.size = m.length
  needed_eq : d.needed.val = (md.size + 31) / 32
  nodup : ((haveHeld d).map Prod.fst).Nodup
  le : (haveHeld d).length ≤ d.needed.val
  lt : ∀ p ∈ haveHeld d, p.1 < 65536
  bytes : ∀ p ∈ haveHeld d, p.2 = Model.Erasure.codeword (Model.Erasure.chunks m) p.1
  src : ∀ c ∈ md.chunks, c.source = m
  mnodup : (md.chunks.map (·.index)).Nodup
  mlt : ∀ c ∈ md.chunks, c.index < 65536
  rel : (haveHeld d).map Prod.fst = ((md.chunks.map (·.index)).reverse).take d.needed.val

theorem haveHeld_len (d : Decoder) : (haveHeld d).length = d.«have».val.length := by
  simp [haveHeld]

/-- The `message` clause of the simulation, from the invariant. -/
theorem message_clause (htr : TruncatePrefix) {m : List UInt8} {d : Decoder}
    {md : Model.Braid.Decoder} (h : DInv m d md) :
    ∀ msg, Decoder.message d = ok msg → msg.map vecOf = md.message := by
  intro msg hmsg
  have hlen : md.chunks.length = (md.chunks.map (·.index)).length := by simp
  by_cases hfull : (haveHeld d).length < d.needed.val
  · -- fewer held than needed: both sides are `none`
    have hnf : d.«have».val.length < d.needed.val := by rwa [← haveHeld_len]
    rw [message_not_full d hnf] at hmsg
    cases hmsg
    have hrel := h.rel
    have hL : (haveHeld d).length = min d.needed.val (md.chunks.length) := by
      have := congrArg List.length hrel
      simpa [List.length_take, List.length_reverse] using this
    have hlt' : md.chunks.length < (md.size + 31) / 32 := by
      have := h.needed_eq
      omega
    simp [model_message_none md hlt']
  · -- exactly `needed` held: the model recovers the message
    have heq : (haveHeld d).length = d.needed.val := le_antisymm h.le (not_lt.mp hfull)
    have hneed : d.needed.val ≤ 65536 := by
      rw [← heq]
      have := nodup_length_le _ h.nodup 65536 (by
        intro i hi
        obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hi
        exact h.lt p hp)
      simpa using this
    have hwf : DWf d := by
      refine ⟨?_, ?_, hneed⟩
      · have := h.nodup
        simpa [haveHeld, List.map_map, Function.comp_def] using this
      · rw [← haveHeld_len]; exact h.le
    obtain ⟨r, hr, hpost⟩ := WP.spec_imp_exists (D_message htr d hwf)
    rw [hmsg] at hr; cases hr
    -- the model decoder of Model.Erasure recovers `m`
    have hM : Model.Erasure.Decoder.message ⟨d.size.val, d.needed.val, haveHeld d⟩ = some m := by
      have hhh : haveHeld d = ((haveHeld d).map Prod.fst).map
          (fun i => (i, Model.Erasure.codeword (Model.Erasure.chunks m) i)) := by
        apply List.ext_getElem
        · simp
        · intro i h1 h2
          have := h.bytes (haveHeld d)[i] (List.getElem_mem h1)
          simp only [List.getElem_map]
          exact Prod.ext rfl this
      have hcount : Model.Erasure.chunkCount m.length = d.needed.val := by
        unfold Model.Erasure.chunkCount
        simp only [Model.Erasure.chunkBytes]
        have := h.needed_eq; have := h.size_len; omega
      rw [hhh]
      have hsz : d.size.val = m.length := by rw [h.size_eq, h.size_len]
      rw [hsz, ← hcount]
      exact M_recover m (by rw [hcount]; exact hneed) _ (by simpa using h.nodup)
        (by intro i hi; obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hi; exact h.lt p hp)
        (by simp [hcount, heq])
    rw [hM] at hpost
    -- msg is `some v` with the bytes of `m`
    cases hmsg' : msg with
    | none => rw [hmsg'] at hpost; simp at hpost
    | some v =>
      rw [hmsg'] at hpost
      simp only [Option.map_some, Option.some.injEq] at hpost
      have hvec : vecOf v = m := hpost
      have hhm : (md.size + 31) / 32 ≤ md.chunks.length := by
        have := h.rel
        have h3 := congrArg List.length this
        simp only [List.length_map, List.length_take, List.length_reverse] at h3
        have := h.needed_eq
        rw [heq] at h3
        omega
      rw [model_message_some md m h.src h.size_len.symm hhm]
      simp [hvec]

theorem erasureAdd_held (S N : ℕ) (H : List (ℕ × List UInt8)) (cw : ℕ × List UInt8) :
    (Model.Erasure.Decoder.add ⟨S, N, H⟩ cw).held =
      if N ≤ H.length ∨ cw.1 ∈ H.map Prod.fst then H else H ++ [cw] := by
  unfold Model.Erasure.Decoder.add
  by_cases h1 : H.length ≥ N
  · simp [h1]
  · by_cases h2 : cw.1 ∈ H.map Prod.fst
    · have : H.any (fun h => h.1 == cw.1) = true := by
        simp only [List.any_eq_true, beq_iff_eq]
        obtain ⟨p, hp, hpe⟩ := List.mem_map.mp h2
        exact ⟨p, hp, hpe⟩
      simp [h1, this, h2]
    · have : H.any (fun h => h.1 == cw.1) = false := by
        simp only [List.any_eq_false, beq_iff_eq]
        intro p hp hpe
        exact h2 (List.mem_map.mpr ⟨p, hp, hpe⟩)
      simp [h1, this, h2]

theorem braidAdd_chunks (md : Model.Braid.Decoder) (m : List UInt8) (I : ℕ) :
    (md.addChunk ⟨m, I⟩).chunks =
      if I ∈ md.chunks.map (·.index) then md.chunks else ⟨m, I⟩ :: md.chunks := by
  unfold Model.Braid.Decoder.addChunk
  by_cases h : I ∈ md.chunks.map (·.index)
  · have : md.chunks.any (fun x => x.index == I) = true := by
      simp only [List.any_eq_true, beq_iff_eq]
      obtain ⟨p, hp, hpe⟩ := List.mem_map.mp h
      exact ⟨p, hp, hpe⟩
    simp [this, h]
  · have : md.chunks.any (fun x => x.index == I) = false := by
      simp only [List.any_eq_false, beq_iff_eq]
      intro p hp hpe
      exact h (List.mem_map.mpr ⟨p, hp, hpe⟩)
    simp [this, h]

theorem braidAdd_size (md : Model.Braid.Decoder) (m : List UInt8) (I : ℕ) :
    (md.addChunk ⟨m, I⟩).size = md.size := by
  unfold Model.Braid.Decoder.addChunk
  split <;> rfl

theorem dinv_add (hdiv : Tacenta.SessionUnitDecoderBound.DivCeilValue) {m : List UInt8}
    {d : Decoder} {md : Model.Braid.Decoder} (h : DInv m d md) (chunk : Chunk)
    (hcw : CodewordOf m chunk) {b : Bool} {d' : Decoder}
    (hadd : Decoder.add_chunk d chunk = ok (b, d')) :
    DInv m d' (md.addChunk ⟨m, chunk.index.val⟩) := by
  obtain ⟨r, hr, hheld, hsize, hneeded, hb⟩ := WP.spec_imp_exists (D_add d chunk)
  rw [hadd] at hr; cases hr
  simp only at hheld hsize hneeded hb
  have hcb := codeword_bytes hdiv m chunk hcw
  have hI : chunk.index.val < 65536 := by have := chunk.index.hBounds; scalar_tac
  generalize chunk.index.val = I at hheld hcb hI ⊢
  rw [erasureAdd_held] at hheld
  have hsz' := braidAdd_size md m I
  have hch' := braidAdd_chunks md m I
  have hrel := h.rel
  have hLlen : (haveHeld d).length = min d.needed.val md.chunks.length := by
    have := congrArg List.length hrel
    simpa [List.length_take, List.length_reverse] using this
  by_cases hfull : d.needed.val ≤ (haveHeld d).length
  · -- the translated decoder is full, so it ignores the chunk
    have hfl : (haveHeld d).length = d.needed.val := le_antisymm h.le hfull
    have hneedle : d.needed.val ≤ md.chunks.length := by omega
    have hheld' : haveHeld d' = haveHeld d := by
      rw [hheld]; simp [hfull]
    by_cases hmem : I ∈ md.chunks.map (·.index)
    · rw [if_pos hmem] at hch'
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hsize, hsz']; exact h.size_eq
      · rw [hsz']; exact h.size_len
      · rw [hneeded, hsz']; exact h.needed_eq
      · rw [hheld']; exact h.nodup
      · rw [hheld', hneeded]; exact h.le
      · rw [hheld']; exact h.lt
      · rw [hheld']; exact h.bytes
      · rw [hch']; exact h.src
      · rw [hch']; exact h.mnodup
      · rw [hch']; exact h.mlt
      · rw [hheld', hneeded, hch']; exact h.rel
    · rw [if_neg hmem] at hch'
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hsize, hsz']; exact h.size_eq
      · rw [hsz']; exact h.size_len
      · rw [hneeded, hsz']; exact h.needed_eq
      · rw [hheld']; exact h.nodup
      · rw [hheld', hneeded]; exact h.le
      · rw [hheld']; exact h.lt
      · rw [hheld']; exact h.bytes
      · rw [hch']
        intro c hc
        rcases List.mem_cons.mp hc with rfl | hc
        · rfl
        · exact h.src c hc
      · rw [hch']
        simp only [List.map_cons, List.nodup_cons]
        exact ⟨hmem, h.mnodup⟩
      · rw [hch']
        intro c hc
        rcases List.mem_cons.mp hc with rfl | hc
        · exact hI
        · exact h.mlt c hc
      · rw [hheld', hneeded, hch']
        simp only [List.map_cons, List.reverse_cons]
        rw [List.take_append_of_le_length (by simp; omega)]
        exact h.rel
  · -- not full: the held indices are all the model's, oldest first
    have hnf : (haveHeld d).length < d.needed.val := by omega
    have hmlt : md.chunks.length < d.needed.val := by omega
    have hLeq : (haveHeld d).map Prod.fst = (md.chunks.map (·.index)).reverse := by
      rw [hrel]
      apply List.take_of_length_le
      simp; omega
    by_cases hmem : I ∈ md.chunks.map (·.index)
    · -- a repeated index: both ignore it
      have hIL : I ∈ (haveHeld d).map Prod.fst := by
        rw [hLeq]; exact List.mem_reverse.mpr hmem
      have hheld' : haveHeld d' = haveHeld d := by
        rw [hheld]; simp [hIL]
      rw [if_pos hmem] at hch'
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hsize, hsz']; exact h.size_eq
      · rw [hsz']; exact h.size_len
      · rw [hneeded, hsz']; exact h.needed_eq
      · rw [hheld']; exact h.nodup
      · rw [hheld', hneeded]; exact h.le
      · rw [hheld']; exact h.lt
      · rw [hheld']; exact h.bytes
      · rw [hch']; exact h.src
      · rw [hch']; exact h.mnodup
      · rw [hch']; exact h.mlt
      · rw [hheld', hneeded, hch']; exact h.rel
    · -- a new index: both add it
      have hIL : I ∉ (haveHeld d).map Prod.fst := by
        rw [hLeq]; intro hh; exact hmem (List.mem_reverse.mp hh)
      have hheld' : haveHeld d' = haveHeld d ++ [(I, cbytes chunk)] := by
        rw [hheld, if_neg]
        simp only [not_or, not_le]
        exact ⟨hnf, hIL⟩
      rw [if_neg hmem] at hch'
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hsize, hsz']; exact h.size_eq
      · rw [hsz']; exact h.size_len
      · rw [hneeded, hsz']; exact h.needed_eq
      · rw [hheld', List.map_append, List.nodup_append]
        refine ⟨h.nodup, by simp, ?_⟩
        intro x hx y hy
        simp at hy
        subst hy
        intro hxy; subst hxy; exact hIL hx
      · rw [hheld', hneeded]; simp; omega
      · rw [hheld']
        intro p hp
        rcases List.mem_append.mp hp with hp | hp
        · exact h.lt p hp
        · simp only [List.mem_singleton] at hp; subst hp; exact hI
      · rw [hheld']
        intro p hp
        rcases List.mem_append.mp hp with hp | hp
        · exact h.bytes p hp
        · simp only [List.mem_singleton] at hp; subst hp; exact hcb
      · rw [hch']
        intro c hc
        rcases List.mem_cons.mp hc with rfl | hc
        · rfl
        · exact h.src c hc
      · rw [hch']
        simp only [List.map_cons, List.nodup_cons]
        exact ⟨hmem, h.mnodup⟩
      · rw [hch']
        intro c hc
        rcases List.mem_cons.mp hc with rfl | hc
        · exact hI
        · exact h.mlt c hc
      · rw [hheld', hneeded, hch', List.map_append, hLeq]
        simp only [List.map_cons, List.reverse_cons]
        rw [List.take_of_length_le (by simp; omega)]
        simp

/-- The simulation, by induction on the number of steps, from the invariant. -/
theorem decoderSim_of_inv (hdiv : Tacenta.SessionUnitDecoderBound.DivCeilValue)
    (htr : TruncatePrefix) :
    ∀ (k : ℕ) (m : List UInt8) (d : Decoder) (md : Model.Braid.Decoder),
      DInv m d md → DecoderSim m k d md := by
  intro k
  induction k with
  | zero => intro m d md _; trivial
  | succ k ih =>
    intro m d md h
    refine ⟨?_, message_clause htr h⟩
    intro chunk advanced d' hcw hadd
    exact ih m d' _ (dinv_add hdiv h chunk hcw hadd)

/-- A fresh decoder: `needed` is `(size + 31) / 32` and nothing is held. -/
theorem decoder_new_shape (hdiv : Tacenta.SessionUnitDecoderBound.DivCeilValue) (n : Usize) :
    ∃ d : Decoder, Decoder.new n = ok d ∧ d.size = n ∧ d.needed.val = (n.val + 31) / 32 ∧
      d.«have».val = [] := by
  obtain ⟨r, hr, hv⟩ := hdiv n
  refine ⟨{ size := n, needed := r, «have» := alloc.vec.Vec.new Chunk }, ?_, rfl, hv, rfl⟩
  unfold Decoder.new chunk_count
  simp only [CHUNK_BYTES]
  rw [hr]
  rfl

/-- A fresh decoder and the model's fresh decoder of the same size keep the invariant, for every
message of that size. -/
theorem dinv_new (n : Usize) (d : Decoder) (hs : d.size = n)
    (hn : d.needed.val = (n.val + 31) / 32) (hh : d.«have».val = []) (m : List UInt8)
    (hm : m.length = n.val) :
    DInv m d (Model.Braid.Decoder.new n.val) := by
  have hheld : haveHeld d = [] := by simp [haveHeld, hh]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hs]; rfl
  · simpa [Model.Braid.Decoder.new] using hm.symm
  · simpa [Model.Braid.Decoder.new] using hn
  · rw [hheld]; simp
  · rw [hheld]; simp
  · rw [hheld]; simp
  · rw [hheld]; simp
  · simp [Model.Braid.Decoder.new]
  · simp [Model.Braid.Decoder.new]
  · simp [Model.Braid.Decoder.new]
  · rw [hheld]; simp [Model.Braid.Decoder.new]

/-- **The decoder half of `ErasureAgrees`, for the translated unit, under the two laws.** -/
theorem erasureAgrees_decoder (hdiv : Tacenta.SessionUnitDecoderBound.DivCeilValue)
    (htr : TruncatePrefix) :
    ∀ n : Usize, ∃ real, Decoder.new n = ok real ∧
      DecoderRefines real (Model.Braid.Decoder.new n.val) := by
  intro n
  obtain ⟨d, hd, hs, hn, hh⟩ := decoder_new_shape hdiv n
  refine ⟨d, hd, ?_⟩
  intro m hm _ k
  exact decoderSim_of_inv hdiv htr k m d _ (dinv_new n d hs hn hh m hm)

/-- **`ErasureAgrees` of the complete Session unit holds, under `DivCeilValue` and
`TruncatePrefix`.**  The encoder half is `UnitSatisfiabilityErasureAgrees.erasureAgrees_encoder`
(through `DivCeil32`, which `DivCeilValue` implies); the decoder half is
`erasureAgrees_decoder`. -/
theorem erasureAgrees (hdiv : Tacenta.SessionUnitDecoderBound.DivCeilValue)
    (htr : TruncatePrefix) : ErasureAgrees :=
  ⟨Tacenta.UnitSatisfiabilityErasureAgrees.erasureAgrees_encoder
      (Tacenta.UnitSatisfiabilityErasure.divCeil32_of_value hdiv),
    erasureAgrees_decoder hdiv htr⟩

end Tacenta.UnitErasureRs.Glue

/--
info: 'Tacenta.UnitErasureRs.Glue.erasureAgrees_decoder' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.alloc.vec.Vec.truncate,
 tacenta_session_unit.core.num.Usize.div_ceil]
-/
#guard_msgs in
#print axioms Tacenta.UnitErasureRs.Glue.erasureAgrees_decoder

/--
info: 'Tacenta.UnitErasureRs.Glue.erasureAgrees' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.alloc.vec.Vec.truncate,
 tacenta_session_unit.core.num.Usize.div_ceil]
-/
#guard_msgs in
#print axioms Tacenta.UnitErasureRs.Glue.erasureAgrees

/--
info: Tacenta.UnitErasureRs.Glue.erasureAgrees_decoder (hdiv : Tacenta.SessionUnitDecoderBound.DivCeilValue)
  (htr : Tacenta.UnitSatisfiabilityBraidAgreements.TruncatePrefix) (n : Usize) :
  ∃ real, Decoder.new n = ok real ∧ Tacenta.SessionUnitBraidT3.DecoderRefines real (Model.Braid.Decoder.new ↑n)
-/
#guard_msgs in
#check Tacenta.UnitErasureRs.Glue.erasureAgrees_decoder

/--
info: Tacenta.UnitErasureRs.Glue.erasureAgrees (hdiv : Tacenta.SessionUnitDecoderBound.DivCeilValue)
  (htr : Tacenta.UnitSatisfiabilityBraidAgreements.TruncatePrefix) : Tacenta.SessionUnitBraidT3.ErasureAgrees
-/
#guard_msgs in
#check Tacenta.UnitErasureRs.Glue.erasureAgrees
