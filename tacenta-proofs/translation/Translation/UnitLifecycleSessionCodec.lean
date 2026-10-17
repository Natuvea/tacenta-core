import Translation.UnitLifecycleEstablishedDecrypt

/-!
# The leaf codecs a persisted established initiator session goes through

`Session::export` composes the leaf encoders and `Session::import` the leaf decoders
(`tacenta-spec/protocol/session-persistence.md`, "Composed bottom-up").  This module proves, for the
shapes a freshly established initiator session has, that each translated decoder returns exactly the
value its translated encoder wrote:

* the classical ratchet state with no stored key (`ratchet_to_bytes_spec`, `ratchet_from_bytes_of`);
* the sparse ratchet state with one chain-table entry, both chains present, and no stored key
  (`spqr_to_bytes_spec`, `spqr_from_bytes_of`);
* the Triple state built from those two (`triple_to_bytes_spec`, `triple_from_bytes_of`);
* the Braid in `KeysUnsampled` below epoch `u64::MAX`, which its reader refuses (`braid_to_bytes_spec`,
  `braid_from_bytes_of`);
* the pending initial message (`pending_to_bytes_spec`, `pending_from_bytes_of`).

Each encoder lemma gives the bytes as a list (`ratchetEnc`, `spqrEnc`, `tripleEnc`, `braidEnc`, `pendEnc`);
each decoder lemma takes a slice holding exactly those bytes and the leaf's own invariant (which each
leaf decoder re-checks) and returns the value.  The reading lemmas (`read_key_of`, `read_u32_of`,
`read_optional_key_of`, `decode_chain_of`, the two `take_len_prefixed` lemmas, ...) take the bytes from a
position as `List.drop` facts.

## Laws

Five functions on the path have no body in the translation, and each is taken through a named law, stated
over a shape with a model:
* `ZeroizingVecRoundTrip`: `Zeroizing::new` then `Zeroizing::deref` on a byte vector gives it back.  Model:
  `model_zeroizingVecRoundTrip`.
* `OptionBranchSome`: `Option::branch` on `Some x` continues with `x` (used by the session-level
  `take_len_prefixed` and by `PendingInitial::from_bytes`).  Model: `optionBranchImpl`
  (`UnitLifecycleRestoredSession.restored_laws_model`).
* `VecAsSlice`: `Vec::as_slice` is the vector's slice view (used by `import`'s canonical re-encode
  check).  Model: `vecAsSliceImpl_shape`.
* `DhPrivateBytesRoundTrip`: `PrivateKey::to_bytes`, read out of its `Zeroizing`, then
  `PrivateKey::from_bytes` gives the key back.  Model: `model_dhPrivateBytesRoundTrip`.
* `DhPublicBytesRoundTrip`: `PublicKeyBytes::as_bytes` then `PublicKeyBytes::from_bytes` gives the key
  back.  Model: `model_dhPublicBytesRoundTrip`.
All are assumed at the real constants and not checked in Lean; each is true of the Rust by reading
(`zeroize`, `core`, `alloc`, `tacenta-core/boundary/src/dh.rs`).

## What it does not show

* Any other shape: stored skipped keys, a sparse table of another size or with an absent chain, any other
  Braid state (in particular none that holds a KEM value, an encoder or a decoder), an absent pending
  initial message or a present established ephemeral.
* That a decoder refuses what it should refuse: only the acceptance of encoder output is shown here.
-/

namespace Tacenta.UnitLifecycleSessionCodec

open Aeneas Aeneas.Std Result
open tacenta_session_unit

/-- `extend_from_slice` on bytes appends the slice, as a value. -/
@[step]
theorem efs_val (v : alloc.vec.Vec U8) (s : Slice U8) (h : v.val.length + s.val.length ≤ Usize.max) :
    alloc.vec.Vec.extend_from_slice core.clone.CloneU8 v s ⦃ r => r.val = v.val ++ s.val ⦄ :=
  Tacenta.SessionUnitSessionT1.extend_from_slice_spec v s h

def be32 (x : U32) : List U8 := (core.num.U32.to_be_bytes x).val
def be64 (x : U64) : List U8 := (core.num.U64.to_be_bytes x).val
theorem be32_length (x : U32) : (be32 x).length = 4 := (core.num.U32.to_be_bytes x).property
theorem be64_length (x : U64) : (be64 x).length = 8 := (core.num.U64.to_be_bytes x).property

def optKeyEnc : Option (Array U8 32#usize) → List U8
  | none => 0#u8 :: List.replicate 32 0#u8
  | some k => 1#u8 :: k.val

theorem fromBEBytes_toNat_congr {l1 l2 : List Byte} (h : l1 = l2) :
    (BitVec.fromBEBytes l1).toNat = (BitVec.fromBEBytes l2).toNat := by subst h; rfl

theorem fromLEBytes_toNat_congr {l1 l2 : List Byte} (h : l1 = l2) :
    (BitVec.fromLEBytes l1).toNat = (BitVec.fromLEBytes l2).toNat := by subst h; rfl

theorem fromBEBytes_toBEBytes_toNat {w : Nat} (hw : w % 8 = 0) (b : BitVec w) :
    (BitVec.fromBEBytes b.toBEBytes).toNat = b.toNat := by
  unfold BitVec.fromBEBytes BitVec.toBEBytes
  rw [BitVec.toNat_cast, fromLEBytes_toNat_congr (List.reverse_reverse _),
    BitVec.fromLEBytes_toLEBytes hw, BitVec.toNat_cast]

theorem from_be32 (x : U32) (a : Array U8 4#usize) (h : a.val = be32 x) :
    core.num.U32.from_be_bytes a = x := by
  have hl : (List.map U8.bv a.val) = x.bv.toBEBytes := by
    rw [h]; simp [be32, core.num.U32.to_be_bytes]
  obtain ⟨xb⟩ := x
  simp only [core.num.U32.from_be_bytes]
  congr 1
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_cast, fromBEBytes_toNat_congr hl, fromBEBytes_toBEBytes_toNat (by decide)]

theorem drop_next {α : Type} {L seg rest : List α} {p : Nat} (h : L.drop p = seg ++ rest) :
    L.drop (p + seg.length) = rest := by
  rw [← List.drop_drop, h, List.drop_left]

theorem slice_of_drop {α : Type} {L seg rest : List α} {p e : Nat} (h : L.drop p = seg ++ rest)
    (he : e = p + seg.length) : List.slice p e L = seg := by
  subst he
  simp [List.slice, h]

theorem length_of_drop {α : Type} {L seg rest : List α} {p : Nat} (h : L.drop p = seg ++ rest)
    (hs : 0 < seg.length) : p + seg.length ≤ L.length := by
  have := congrArg List.length h
  simp only [List.length_drop, List.length_append] at this
  omega

theorem getElem_of_drop {α : Type} {L rest : List α} {x : α} {p : Nat} (h : L.drop p = x :: rest) :
    L[p]? = some x := by
  have := congrArg (·[0]?) h
  simpa using this

theorem from_slice_eq {N : Usize} (a : Array U8 N) (s : Slice U8) (k : Array U8 N) (h : s.val = k.val) :
    Array.from_slice a s = k := by
  apply Subtype.ext
  rw [Array.from_slice_val _ _ (by rw [h]; exact k.property)]
  exact h

theorem index_usize_of (bytes : Slice U8) (pos : Usize) (x : U8) (rest : List U8)
    (h : bytes.val.drop pos.val = x :: rest) : Slice.index_usize bytes pos = ok x := by
  unfold Slice.index_usize
  have := getElem_of_drop h
  simp only [Slice.getElem?_Usize_eq] at *
  rw [this]

theorem read_key_of (bytes : Slice U8) (pos : Usize) (k : Array U8 32#usize) (rest : List U8)
    (h : bytes.val.drop pos.val = k.val ++ rest) :
    tacenta_ratchet.read_key bytes pos = ok k := by
  have hk : k.val.length = 32 := k.property
  have hl := length_of_drop h (by rw [hk]; decide)
  have hs : tacenta_ratchet.read_key bytes pos ⦃ r => r = k ⦄ := by
    unfold tacenta_ratchet.read_key
    step*
    · simp [s_post1, s1_post2, i_post, Slice.length]
    rw [s_post2]
    apply from_slice_eq
    rw [s2_post, s1_post1, i_post]
    exact slice_of_drop h (by rw [hk])
  obtain ⟨r, hr, rfl⟩ := Std.WP.spec_imp_exists hs
  exact hr

theorem read_u32_of (bytes : Slice U8) (pos : Usize) (x : U32) (rest : List U8)
    (h : bytes.val.drop pos.val = be32 x ++ rest) :
    tacenta_ratchet.read_u32 bytes pos = ok x := by
  have hk : (be32 x).length = 4 := be32_length x
  have hl := length_of_drop h (by rw [hk]; decide)
  have hs : tacenta_ratchet.read_u32 bytes pos ⦃ r => r = x ⦄ := by
    unfold tacenta_ratchet.read_u32
    step*
    · simp [s_post1, s1_post2, i_post, Slice.length]
    rw [s_post2]
    apply from_be32
    rw [Array.from_slice_val _ _ (by rw [s2_post, s1_post1, i_post, slice_of_drop h (by rw [hk])]; exact hk)]
    rw [s2_post, s1_post1, i_post]
    exact slice_of_drop h (by rw [hk])
  obtain ⟨r, hr, rfl⟩ := Std.WP.spec_imp_exists hs
  exact hr


theorem read_optional_key_loop_zero (bytes : Slice U8) (pos i : Usize)
    (hi : i.val ≤ pos.val + 33) (hlen : pos.val + 33 ≤ bytes.length)
    (hz : ∀ j, i.val ≤ j → j < pos.val + 33 → bytes.val[j]? = some 0#u8) :
    tacenta_ratchet.read_optional_key_loop bytes pos true i ⦃ c => c = true ⦄ := by
  unfold tacenta_ratchet.read_optional_key_loop
  apply loop.spec_decr_nat
    (measure := fun p => pos.val + 33 - p.2.val)
    (inv := fun p => p.1 = true ∧ i.val ≤ p.2.val ∧ p.2.val ≤ pos.val + 33)
  · rintro ⟨c, j⟩ ⟨hc, hj1, hj2⟩
    simp only at hc hj1 hj2 ⊢
    unfold tacenta_ratchet.read_optional_key_loop.body
    step*
    · have h0 := hz j.val hj1 (by scalar_tac)
      have : i2 = 0#u8 := by
        rw [i2_post]
        rw [List.getElem?_eq_getElem (by scalar_tac)] at h0
        exact Option.some.inj h0
      subst this
      simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
      step*
  · exact ⟨rfl, le_refl _, hi⟩

theorem read_optional_key_of (bytes : Slice U8) (pos : Usize) (o : Option (Array U8 32#usize))
    (rest : List U8) (h : bytes.val.drop pos.val = optKeyEnc o ++ rest) :
    tacenta_ratchet.read_optional_key bytes pos = ok (core.result.Result.Ok o) := by
  have h33 : (optKeyEnc o).length = 33 := by cases o <;> simp [optKeyEnc]
  have hl := length_of_drop h (by rw [h33]; decide)
  rcases o with _ | k
  · have hi := index_usize_of bytes pos 0#u8 _ (by rw [h]; rfl)
    have hs : tacenta_ratchet.read_optional_key bytes pos ⦃ r => r = core.result.Result.Ok none ⦄ := by
      unfold tacenta_ratchet.read_optional_key
      rw [hi]
      simp only [bind_tc_ok]
      show (do
        let i1 ← pos + 1#usize
        let clean ← tacenta_ratchet.read_optional_key_loop bytes pos true i1
        if clean then ok (core.result.Result.Ok none)
        else ok (core.result.Result.Err tacenta_ratchet.RatchetDecodeError.Malformed)) ⦃ _ ⦄
      step*
      have hz : ∀ j, i1.val ≤ j → j < pos.val + 33 → bytes.val[j]? = some 0#u8 := by
        intro j hj1 hj2
        have e : bytes.val[j]? = (bytes.val.drop pos.val)[j - pos.val]? := by
          rw [List.getElem?_drop]; congr 1; omega
        rw [e, h]
        simp only [optKeyEnc, List.cons_append]
        obtain ⟨k, hk⟩ : ∃ k, j - pos.val = k + 1 := ⟨j - pos.val - 1, by omega⟩
        rw [hk, List.getElem?_cons_succ, List.getElem?_append_left (by rw [List.length_replicate]; omega),
          List.getElem?_replicate, if_pos (by omega)]
      step with read_optional_key_loop_zero bytes pos i1 (by scalar_tac) (by rw [h33] at hl; scalar_tac) hz
      rw [if_pos clean_post, Std.WP.spec_ok]
    obtain ⟨r, hr, rfl⟩ := Std.WP.spec_imp_exists hs
    exact hr
  · have hi := index_usize_of bytes pos 1#u8 _ (by rw [h]; rfl)
    have hs : tacenta_ratchet.read_optional_key bytes pos ⦃ r => r = core.result.Result.Ok (some k) ⦄ := by
      unfold tacenta_ratchet.read_optional_key
      rw [hi]
      simp only [bind_tc_ok]
      show (do
        let i1 ← pos + 1#usize
        let a ← tacenta_ratchet.read_key bytes i1
        ok (core.result.Result.Ok (some a))) ⦃ _ ⦄
      step*
      have hk := read_key_of bytes i1 k rest (by
        rw [i1_post, ← List.drop_drop, h]; rfl)
      rw [hk]
      simp
    obtain ⟨r, hr, rfl⟩ := Std.WP.spec_imp_exists hs
    exact hr


theorem usize_add_eq (a b c : Usize) (h : a.val + b.val = c.val) : a + b = ok c := by
  have hc : c.val ≤ Usize.max := by scalar_tac
  have hspec : (a + b) ⦃ z => z.val = a.val + b.val ⦄ := by step*
  obtain ⟨z, hz, hzv⟩ := Std.WP.spec_imp_exists hspec
  rw [hz]
  congr 1
  rw [UScalar.eq_equiv]; omega

theorem usize_div_eq (a b c : Usize) (hb : b.val ≠ 0) (h : a.val / b.val = c.val) : a / b = ok c := by
  have hspec : (a / b) ⦃ z => z.val = a.val / b.val ⦄ := by step*
  obtain ⟨z, hz, hzv⟩ := Std.WP.spec_imp_exists hspec
  rw [hz]
  congr 1
  rw [UScalar.eq_equiv]; omega

theorem slice_len_eq (bytes : Slice U8) (n : Usize) (h : bytes.val.length = n.val) :
    Slice.len bytes = n := by
  rw [UScalar.eq_equiv]; simpa [Slice.len] using h

theorem arr32_len (a : Array U8 32#usize) : a.val.length = 32 := by
  simp

def ratchetEnc (r : tacenta_ratchet.State) : List U8 :=
  1#u8 :: (r.dhs_pub.val ++ (optKeyEnc r.dhr_pub ++ (r.rk.val ++ (optKeyEnc r.cks ++
    (optKeyEnc r.ckr ++ (be32 r.ns ++ (be32 r.nr ++ (be32 r.pn ++ (be32 r.events ++
    (0#u8 :: be32 0#u32))))))))))

theorem optKeyEnc_length (o : Option (Array U8 32#usize)) : (optKeyEnc o).length = 33 := by
  cases o <;> simp [optKeyEnc]

theorem ratchetEnc_length (r : tacenta_ratchet.State) : (ratchetEnc r).length = 185 := by
  simp [ratchetEnc, optKeyEnc_length, be32_length]

def ZeroizingVecRoundTrip : Prop :=
  ∀ (inst : zeroize.Zeroize (alloc.vec.Vec U8)) (v : alloc.vec.Vec U8),
    ∃ z, zeroize.Zeroizing.new inst v = ok z ∧
      zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref inst z = ok v

@[local step]
theorem push_optional_key_enc (out : alloc.vec.Vec U8) (k : Option (Array U8 32#usize))
    (h : out.val.length + 33 ≤ Usize.max) :
    tacenta_ratchet.push_optional_key out k ⦃ w => w.val = out.val ++ optKeyEnc k ⦄ := by
  unfold tacenta_ratchet.push_optional_key
  rcases k with _ | k <;> simp only [] <;> step*
  all_goals (try simp_all [Array.to_slice, Array.repeat, optKeyEnc])

theorem ratchet_to_bytes_loop_empty (v : alloc.vec.Vec tacenta_ratchet.SkippedKey)
    (out : alloc.vec.Vec U8) (hv : v.val = []) :
    tacenta_ratchet.State.to_bytes_loop v out 0#usize = ok out := by
  unfold tacenta_ratchet.State.to_bytes_loop
  rw [loop.eq_def]
  simp [tacenta_ratchet.State.to_bytes_loop.body, alloc.vec.Vec.len, hv]

@[local step]
theorem ratchet_to_bytes_loop_empty_spec (v : alloc.vec.Vec tacenta_ratchet.SkippedKey)
    (out : alloc.vec.Vec U8) (hv : v.val = []) :
    tacenta_ratchet.State.to_bytes_loop v out 0#usize ⦃ w => w = out ⦄ := by
  rw [ratchet_to_bytes_loop_empty v out hv]; simp

@[local step]
theorem label_to_byte_spec (l : tacenta_ratchet.LabelSet) :
    tacenta_ratchet.LabelSet.to_byte l ⦃ b => b = 0#u8 ⦄ := by
  simp [tacenta_ratchet.LabelSet.to_byte]


/-- The `Zeroize` instance the codecs wrap byte vectors with. -/
noncomputable abbrev vecInst : zeroize.Zeroize (alloc.vec.Vec U8) :=
  alloc.vec.Vec.Insts.ZeroizeZeroize (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)

@[step]
theorem zeroizing_new_spec (hz : ZeroizingVecRoundTrip) (inst : zeroize.Zeroize (alloc.vec.Vec U8))
    (v : alloc.vec.Vec U8) :
    zeroize.Zeroizing.new inst v ⦃ z => zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref inst z = ok v ⦄ := by
  obtain ⟨z, h1, h2⟩ := hz inst v
  rw [h1]; simpa using h2

theorem ratchet_to_bytes_spec (hz : ZeroizingVecRoundTrip) (r : tacenta_ratchet.State)
    (hsk : r.skipped.val = []) :
    tacenta_ratchet.State.to_bytes r ⦃ z => ∃ v,
      zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref vecInst z = ok v ∧ v.val = ratchetEnc r ⦄ := by
  unfold tacenta_ratchet.State.to_bytes
  simp only [Tacenta.SessionUnitRatchetImportInv.Ratchet.fixed_len_eq,
    Tacenta.SessionUnitRatchetImportInv.Ratchet.skipped_encoded_len_eq, bind_tc_ok,
    alloc.vec.Vec.with_capacity]
  step*
  all_goals try (simp_all [Array.to_slice, optKeyEnc_length]; scalar_tac)
  refine ⟨out13, z_post, ?_⟩
  have hlen : r.skipped.len = 0#usize := by
    simp only [alloc.vec.Vec.len]; scalar_tac
  have hc : UScalar.cast UScalarTy.U32 (0#usize) = 0#u32 := by
    rw [UScalar.eq_equiv, UScalar.cast_val_eq]; simp
  simp only [out13_post, out12_post, out11_post, out10_post, out9_post, out8_post, out7_post,
    out6_post, out5_post, out4_post, out3_post, out2_post, out1_post, s_post, s1_post, s2_post,
    s3_post, s4_post, s5_post, s6_post, a_post, a1_post, a2_post, a3_post, a4_post, i5_post,
    i7_post, hlen, hc, Array.to_slice, ratchetEnc, be32, core.num.U32.to_be_bytes,
    tacenta_ratchet.STATE_VERSION, List.append_assoc, List.nil_append, List.cons_append]

set_option maxHeartbeats 1000000 in
theorem ratchet_from_bytes_of (bytes : Slice U8) (r : tacenta_ratchet.State)
    (hb : bytes.val = ratchetEnc r) (hsk : r.skipped.val = [])
    (hinv : tacenta_ratchet.State.invariant r = ok true) :
    tacenta_ratchet.State.from_bytes bytes = ok (core.result.Result.Ok r) := by
  have hlen : bytes.val.length = 185 := by rw [hb, ratchetEnc_length]
  -- the drop chain
  have d0 : bytes.val.drop (0#usize).val = 1#u8 :: (ratchetEnc r).tail := by
    simp only [hb, ratchetEnc]; rfl
  have d1 : bytes.val.drop 1 = (ratchetEnc r).tail := by rw [hb]; rfl
  simp only [ratchetEnc, List.tail_cons] at d1
  have d2 := drop_next d1
  simp only [arr32_len, Nat.reduceAdd] at d2
  have d3 := drop_next d2
  simp only [optKeyEnc_length, Nat.reduceAdd] at d3
  have d4 := drop_next d3
  simp only [arr32_len, Nat.reduceAdd] at d4
  have d5 := drop_next d4
  simp only [optKeyEnc_length, Nat.reduceAdd] at d5
  have d6 := drop_next d5
  simp only [optKeyEnc_length, Nat.reduceAdd] at d6
  have d7 := drop_next d6
  simp only [be32_length, Nat.reduceAdd] at d7
  have d8 := drop_next d7
  simp only [be32_length, Nat.reduceAdd] at d8
  have d9 := drop_next d8
  simp only [be32_length, Nat.reduceAdd] at d9
  have d10 := drop_next d9
  simp only [be32_length, Nat.reduceAdd] at d10
  have d11 : bytes.val.drop 181 = be32 0#u32 ++ [] := by
    have := drop_next (seg := [0#u8]) (rest := be32 0#u32) d10
    simpa using this
  have hlenU : Slice.len bytes = 185#usize := slice_len_eq bytes _ (by simp [hlen])
  have e_v : Slice.index_usize bytes 0#usize = ok 1#u8 := index_usize_of _ _ _ _ d0
  have e_dhs : tacenta_ratchet.read_key bytes 1#usize = ok r.dhs_pub :=
    read_key_of _ _ _ _ (by simpa using d1)
  have a33 : (1#usize + 32#usize : Result Usize) = ok 33#usize := usize_add_eq _ _ _ (by simp)
  have e_dhr : tacenta_ratchet.read_optional_key bytes 33#usize = ok (core.result.Result.Ok r.dhr_pub) :=
    read_optional_key_of _ _ _ _ (by simpa using d2)
  have a66 : (33#usize + 33#usize : Result Usize) = ok 66#usize := usize_add_eq _ _ _ (by simp)
  have e_rk : tacenta_ratchet.read_key bytes 66#usize = ok r.rk :=
    read_key_of _ _ _ _ (by simpa using d3)
  have a98 : (66#usize + 32#usize : Result Usize) = ok 98#usize := usize_add_eq _ _ _ (by simp)
  have e_cks : tacenta_ratchet.read_optional_key bytes 98#usize = ok (core.result.Result.Ok r.cks) :=
    read_optional_key_of _ _ _ _ (by simpa using d4)
  have a131 : (98#usize + 33#usize : Result Usize) = ok 131#usize := usize_add_eq _ _ _ (by simp)
  have e_ckr : tacenta_ratchet.read_optional_key bytes 131#usize = ok (core.result.Result.Ok r.ckr) :=
    read_optional_key_of _ _ _ _ (by simpa using d5)
  have a164 : (131#usize + 33#usize : Result Usize) = ok 164#usize := usize_add_eq _ _ _ (by simp)
  have e_ns : tacenta_ratchet.read_u32 bytes 164#usize = ok r.ns := read_u32_of _ _ _ _ (by simpa using d6)
  have a168 : (164#usize + 4#usize : Result Usize) = ok 168#usize := usize_add_eq _ _ _ (by simp)
  have e_nr : tacenta_ratchet.read_u32 bytes 168#usize = ok r.nr := read_u32_of _ _ _ _ (by simpa using d7)
  have a172 : (168#usize + 4#usize : Result Usize) = ok 172#usize := usize_add_eq _ _ _ (by simp)
  have e_pn : tacenta_ratchet.read_u32 bytes 172#usize = ok r.pn := read_u32_of _ _ _ _ (by simpa using d8)
  have a176 : (172#usize + 4#usize : Result Usize) = ok 176#usize := usize_add_eq _ _ _ (by simp)
  have e_ev : tacenta_ratchet.read_u32 bytes 176#usize = ok r.events :=
    read_u32_of _ _ _ _ (by simpa using d9)
  have a180 : (176#usize + 4#usize : Result Usize) = ok 180#usize := usize_add_eq _ _ _ (by simp)
  have e_lab : Slice.index_usize bytes 180#usize = ok 0#u8 := index_usize_of _ _ _ _ (by simpa using d10)
  have a181 : (180#usize + 1#usize : Result Usize) = ok 181#usize := usize_add_eq _ _ _ (by simp)
  have e_cnt : tacenta_ratchet.read_u32 bytes 181#usize = ok 0#u32 :=
    read_u32_of _ _ _ [] (by rw [show (181#usize).val = 181 by simp]; exact d11)
  have hcast : UScalar.cast UScalarTy.Usize (0#u32) = 0#usize := by
    rw [UScalar.eq_equiv, UScalar.cast_val_eq]; simp
  have a185 : (181#usize + 4#usize : Result Usize) = ok 185#usize := usize_add_eq _ _ _ (by simp)
  have q2 : (185#usize / 72#usize : Result Usize) = ok 2#usize := usize_div_eq _ _ _ (by simp) (by simp)
  have c1 : ¬ (185#usize < 185#usize) := by scalar_tac
  have c2 : ¬ (0#usize > 2#usize) := by scalar_tac
  obtain ⟨lp, hlp, hlpv⟩ := Std.WP.spec_imp_exists
    (Tacenta.SessionUnitRatchetImportInv.Ratchet.from_bytes_loop_empty 72#usize bytes 185#usize
      (alloc.vec.Vec.with_capacity tacenta_ratchet.SkippedKey 0#usize) true)
  subst hlpv
  clear d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11
  obtain ⟨dhs, dhr, rk, cks, ckr, ns, nr, pn, sk, ev, lab⟩ := r
  cases lab
  have hsk' : sk = alloc.vec.Vec.with_capacity tacenta_ratchet.SkippedKey 0#usize := Subtype.ext hsk
  subst hsk'
  have hs : tacenta_ratchet.State.from_bytes bytes ⦃ x => x = core.result.Result.Ok
      { dhs_pub := dhs, dhr_pub := dhr, rk := rk, cks := cks, ckr := ckr, ns := ns, nr := nr, pn := pn,
        skipped := alloc.vec.Vec.with_capacity tacenta_ratchet.SkippedKey 0#usize, events := ev,
        labels := tacenta_ratchet.LabelSet.Tacenta } ⦄ := by
   unfold tacenta_ratchet.State.from_bytes
   simp only [hlenU, Tacenta.SessionUnitRatchetImportInv.Ratchet.fixed_len_eq, bind_tc_ok, c1,
    e_v, tacenta_ratchet.STATE_VERSION, bne_self_eq_false, e_dhs, a33, e_dhr,
    Tacenta.SessionUnitRatchetImportInv.Ratchet.optional_key_len_eq, a66, e_rk, a98, e_cks, a131,
    e_ckr, a164, e_ns, a168, e_nr, a172, e_pn, a176, e_ev, a180, e_lab,
    Tacenta.SessionUnitRatchetImportInv.Ratchet.label_byte_zero, a181, e_cnt, lift, hcast, a185,
    Tacenta.SessionUnitRatchetImportInv.Ratchet.skipped_encoded_len_eq, q2, c2, hlp,
    Bool.false_eq_true, ↓reduceIte]
   step*
   rw [hinv]
   simp
  obtain ⟨x, hx, rfl⟩ := Std.WP.spec_imp_exists hs
  exact hx


/-! ## The sparse ratchet state -/

theorem chain_len_eq : tacenta_spqr.CHAIN_LEN = ok 41#usize := by
  have h : tacenta_spqr.CHAIN_LEN ⦃ r => r = 41#usize ⦄ := by
    unfold tacenta_spqr.CHAIN_LEN; step*
  obtain ⟨r, hr, hre⟩ := Std.WP.spec_imp_exists h
  rw [hr, hre]

theorem chains_len_eq : tacenta_spqr.CHAINS_LEN = ok 90#usize := by
  have h : tacenta_spqr.CHAINS_LEN ⦃ r => r = 90#usize ⦄ := by
    unfold tacenta_spqr.CHAINS_LEN; rw [chain_len_eq]; step*
  obtain ⟨r, hr, hre⟩ := Std.WP.spec_imp_exists h
  rw [hr, hre]

theorem skipped_len_eq : tacenta_spqr.SKIPPED_LEN = ok 48#usize := by
  have h : tacenta_spqr.SKIPPED_LEN ⦃ r => r = 48#usize ⦄ := by
    unfold tacenta_spqr.SKIPPED_LEN; step*
  obtain ⟨r, hr, hre⟩ := Std.WP.spec_imp_exists h
  rw [hr, hre]

theorem fixed_prefix_eq : tacenta_spqr.FIXED_PREFIX = ok 46#usize := by
  have h : tacenta_spqr.FIXED_PREFIX ⦃ r => r = 46#usize ⦄ := by
    unfold tacenta_spqr.FIXED_PREFIX; step*
  obtain ⟨r, hr, hre⟩ := Std.WP.spec_imp_exists h
  rw [hr, hre]

/-- The direction byte `Direction::to_byte` writes. -/
def dirByte : tacenta_spqr.Direction → U8
  | .A2b => 0#u8
  | .B2a => 1#u8

/-- A present chain: the presence byte, the chain key, the counter. -/
def chainEnc (c : tacenta_spqr.Chain) : List U8 := 1#u8 :: (c.ck.val ++ be64 c.n)

theorem chainEnc_length (c : tacenta_spqr.Chain) : (chainEnc c).length = 41 := by
  simp [chainEnc, be64_length]

/-- The bytes `tacenta_spqr::State::to_bytes` writes for a state with one chain-table entry `(e, c1, c2)`,
both chains present, and no stored key. -/
def spqrEnc (q : tacenta_spqr.State) (e : U64) (c1 c2 : tacenta_spqr.Chain) : List U8 :=
  1#u8 :: (q.rk.val ++ (be64 q.epoch ++ (dirByte q.direction :: (be32 1#u32 ++ (be64 e ++
    (chainEnc c1 ++ (chainEnc c2 ++ be32 0#u32)))))))

theorem spqrEnc_length (q : tacenta_spqr.State) (e : U64) (c1 c2 : tacenta_spqr.Chain) :
    (spqrEnc q e c1 c2).length = 140 := by
  simp [spqrEnc, be64_length, be32_length, chainEnc_length]

@[local step]
theorem push_optional_chain_some (out : alloc.vec.Vec U8) (c : tacenta_spqr.Chain)
    (h : out.val.length + 41 ≤ Usize.max) :
    tacenta_spqr.push_optional_chain out (some c) ⦃ w => w.val = out.val ++ chainEnc c ⦄ := by
  unfold tacenta_spqr.push_optional_chain
  simp only []
  step*
  all_goals (try simp_all [Array.to_slice, chainEnc, be64, core.num.U64.to_be_bytes])
  all_goals scalar_tac


@[local step]
theorem spqr_to_bytes_loop0_one (v : alloc.vec.Vec (U64 × tacenta_spqr.Chains)) (out : alloc.vec.Vec U8)
    (e : U64) (c1 c2 : tacenta_spqr.Chain)
    (hv : v.val = [(e, { send := some c1, receive := some c2 })])
    (h : out.val.length + 90 ≤ Usize.max) :
    tacenta_spqr.State.to_bytes_loop0 v out 0#usize ⦃ w =>
      w.val = out.val ++ (be64 e ++ (chainEnc c1 ++ chainEnc c2)) ⦄ := by
  unfold tacenta_spqr.State.to_bytes_loop0
  apply loop.spec_decr_nat
    (measure := fun p => 1 - p.2.val)
    (inv := fun p => (p.2.val = 0 ∧ p.1 = out) ∨
      (p.2.val = 1 ∧ p.1.val = out.val ++ (be64 e ++ (chainEnc c1 ++ chainEnc c2))))
  · rintro ⟨o, j⟩ hinv
    simp only at hinv ⊢
    unfold tacenta_spqr.State.to_bytes_loop0.body
    have hlen : v.len = 1#usize := by
      rw [UScalar.eq_equiv]; simp [alloc.vec.Vec.len, hv]
    rcases hinv with ⟨hj, ho⟩ | ⟨hj, ho⟩
    · subst ho
      have hj0 : j = 0#usize := by rw [UScalar.eq_equiv]; simpa using hj
      subst hj0
      have hidx : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice (U64 × tacenta_spqr.Chains))
          v 0#usize = ok (e, { send := some c1, receive := some c2 }) :=
        Tacenta.SessionUnitRatchetImportInv.vec_index_eq _ _ _ (by simp [hv])
      simp only [hlen, hidx]
      step*
      all_goals (try simp_all [Array.to_slice, be64, core.num.U64.to_be_bytes, chainEnc_length])
      all_goals (try scalar_tac)
    · simp only [hlen]
      step*
  · exact Or.inl ⟨by simp, rfl⟩


@[local step]
theorem spqr_to_bytes_loop1_empty (v : alloc.vec.Vec tacenta_spqr.Skipped) (out : alloc.vec.Vec U8)
    (hv : v.val = []) : tacenta_spqr.State.to_bytes_loop1 v out 0#usize ⦃ w => w = out ⦄ := by
  unfold tacenta_spqr.State.to_bytes_loop1
  rw [loop.eq_def]
  simp [tacenta_spqr.State.to_bytes_loop1.body, alloc.vec.Vec.len, hv]

@[local step]
theorem direction_to_byte_spec (d : tacenta_spqr.Direction) :
    tacenta_spqr.Direction.to_byte d ⦃ b => b = dirByte d ⦄ := by
  match d with
  | .A2b => simp [tacenta_spqr.Direction.to_byte, dirByte]
  | .B2a => simp [tacenta_spqr.Direction.to_byte, dirByte]

theorem spqr_encoded_len_eq (q : tacenta_spqr.State) (hch : q.chains.val.length = 1)
    (hsk : q.skipped.val = []) : tacenta_spqr.State.encoded_len q = ok 140#usize := by
  have h : tacenta_spqr.State.encoded_len q ⦃ r => r = 140#usize ⦄ := by
    unfold tacenta_spqr.State.encoded_len
    simp only [chains_len_eq, fixed_prefix_eq, skipped_len_eq, bind_tc_ok]
    step*
  obtain ⟨r, hr, hre⟩ := Std.WP.spec_imp_exists h
  rw [hr, hre]

theorem spqr_to_bytes_spec (hz : ZeroizingVecRoundTrip) (q : tacenta_spqr.State) (e : U64)
    (c1 c2 : tacenta_spqr.Chain) (hch : q.chains.val = [(e, { send := some c1, receive := some c2 })])
    (hsk : q.skipped.val = []) :
    tacenta_spqr.State.to_bytes q ⦃ z => ∃ v,
      zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref vecInst z = ok v ∧ v.val = spqrEnc q e c1 c2 ⦄ := by
  unfold tacenta_spqr.State.to_bytes
  rw [spqr_encoded_len_eq q (by simp [hch]) hsk]
  simp only [bind_tc_ok, alloc.vec.Vec.with_capacity]
  step*
  all_goals try (simp_all [Array.to_slice, chainEnc_length, be64_length, be32_length]; scalar_tac)
  refine ⟨out8, z_post, ?_⟩
  have hl1 : q.chains.len = 1#usize := by rw [UScalar.eq_equiv]; simp [alloc.vec.Vec.len, hch]
  have hl0 : q.skipped.len = 0#usize := by rw [UScalar.eq_equiv]; simp [alloc.vec.Vec.len, hsk]
  have hc1 : UScalar.cast UScalarTy.U32 (1#usize) = 1#u32 := by
    rw [UScalar.eq_equiv, UScalar.cast_val_eq]; simp
  have hc0 : UScalar.cast UScalarTy.U32 (0#usize) = 0#u32 := by
    rw [UScalar.eq_equiv, UScalar.cast_val_eq]; simp
  simp only [out8_post, out7_post, out6_post, out5_post, out4_post, out3_post, out2_post, out1_post,
    s_post, s1_post, s2_post, s3_post, a_post, a1_post, a2_post, i_post, i2_post, i4_post, hl1, hl0,
    hc1, hc0, Array.to_slice, spqrEnc, be32, be64, core.num.U32.to_be_bytes,
    core.num.U64.to_be_bytes, tacenta_spqr.STATE_VERSION, List.append_assoc, List.nil_append,
    List.cons_append]


theorem from_be64 (x : U64) (a : Array U8 8#usize) (h : a.val = be64 x) :
    core.num.U64.from_be_bytes a = x := by
  have hl : (List.map U8.bv a.val) = x.bv.toBEBytes := by
    rw [h]; simp [be64, core.num.U64.to_be_bytes]
  obtain ⟨xb⟩ := x
  simp only [core.num.U64.from_be_bytes]
  congr 1
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_cast, fromBEBytes_toNat_congr hl, fromBEBytes_toBEBytes_toNat (by decide)]

theorem u64_eq_of_bv (i x : U64) (a : Array U8 8#usize)
    (hi : i.bv = (core.num.U64.from_be_bytes a).bv) (ha : a.val = be64 x) : i = x := by
  rw [← from_be64 x a ha, UScalar.eq_equiv_bv_eq]; exact hi

theorem u32_eq_of_bv (i x : U32) (a : Array U8 4#usize)
    (hi : i.bv = (core.num.U32.from_be_bytes a).bv) (ha : a.val = be32 x) : i = x := by
  rw [← from_be32 x a ha, UScalar.eq_equiv_bv_eq]; exact hi

theorem decode_chain_of (bytes : Slice U8) (pos : Usize) (c : tacenta_spqr.Chain) (rest : List U8)
    (h : bytes.val.drop pos.val = chainEnc c ++ rest) :
    tacenta_spqr.decode_chain bytes pos = ok (some (some c)) := by
  have hl := length_of_drop h (by rw [chainEnc_length]; decide)
  rw [chainEnc_length] at hl
  have hi := index_usize_of bytes pos 1#u8 _ (by rw [h]; rfl)
  have hck : bytes.val.drop (pos.val + 1) = c.ck.val ++ (be64 c.n ++ rest) := by
    rw [← List.drop_drop, h]; simp [chainEnc]
  have hn : bytes.val.drop (pos.val + 33) = be64 c.n ++ rest := by
    have := drop_next hck
    rw [arr32_len] at this
    simpa [Nat.add_assoc] using this
  have hs : tacenta_spqr.decode_chain bytes pos ⦃ r => r = some (some c) ⦄ := by
    unfold tacenta_spqr.decode_chain
    simp only [chain_len_eq, bind_tc_ok]
    step as ⟨i2, hi2⟩
    rw [if_neg (by simp only [Slice.len]; scalar_tac)]
    rw [hi]
    simp only [bind_tc_ok]
    show (do
      let (s, to_slice_mut_back) ← lift (Array.to_slice_mut (Array.repeat 32#usize 0#u8))
      let i4 ← pos + 1#usize
      let i5 ← pos + 33#usize
      let s1 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8) bytes
        { start := i4, «end» := i5 }
      let s2 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s s1
      let (s3, to_slice_mut_back1) ← lift (Array.to_slice_mut (Array.repeat 8#usize 0#u8))
      let i6 ← pos + 41#usize
      let s4 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8) bytes
        { start := i5, «end» := i6 }
      let s5 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s3 s4
      let ck1 := to_slice_mut_back s2
      let n_bytes1 := to_slice_mut_back1 s5
      let i7 ← lift (core.num.U64.from_be_bytes n_bytes1)
      ok (some (some ({ ck := ck1, n := i7 } : tacenta_spqr.Chain)))) ⦃ _ ⦄
    step*
    · rw [s1_post2]; simp [Slice.length, s_post1, i4_post, i5_post]
    · rw [s4_post2]; simp [Slice.length, s3_post1, i5_post, i6_post]
    have hck' : to_slice_mut_back s2 = c.ck := by
      rw [s_post2]
      exact from_slice_eq _ _ _ (by
        rw [s2_post, s1_post1, i4_post, i5_post]; exact slice_of_drop hck (by rw [arr32_len]))
    have hs4 : s4.val = be64 c.n := by
      rw [s4_post1, i5_post, i6_post]; exact slice_of_drop hn (by rw [be64_length]; try omega)
    have hb5 : (to_slice_mut_back1 s5).val = be64 c.n := by
      rw [s3_post2, s5_post, Array.from_slice_val _ _ (by rw [hs4, be64_length]; simp), hs4]
    have hi7 : i7 = c.n := by
      rw [← from_be64 c.n _ hb5]
      obtain ⟨b7⟩ := i7
      simp only [core.num.U64.from_be_bytes]
      congr 1
    rw [hck', hi7]
  obtain ⟨r, hr, rfl⟩ := Std.WP.spec_imp_exists hs
  exact hr


theorem decode_chains_entry_of (bytes : Slice U8) (pos : Usize) (e : U64) (c1 c2 : tacenta_spqr.Chain)
    (rest : List U8) (h : bytes.val.drop pos.val = be64 e ++ (chainEnc c1 ++ (chainEnc c2 ++ rest))) :
    tacenta_spqr.decode_chains_entry bytes pos =
      ok (some (e, { send := some c1, receive := some c2 })) := by
  have hl := length_of_drop h (by rw [be64_length]; decide)
  rw [be64_length] at hl
  have h1 : bytes.val.drop (pos.val + 8) = chainEnc c1 ++ (chainEnc c2 ++ rest) := by
    have := drop_next h; rwa [be64_length] at this
  have h2 : bytes.val.drop (pos.val + 8 + 41) = chainEnc c2 ++ rest := by
    have := drop_next h1; rwa [chainEnc_length] at this
  have hl2 := length_of_drop h2 (by rw [chainEnc_length]; decide)
  rw [chainEnc_length] at hl2
  have hs : tacenta_spqr.decode_chains_entry bytes pos ⦃ r =>
      r = some (e, { send := some c1, receive := some c2 }) ⦄ := by
    unfold tacenta_spqr.decode_chains_entry
    step as ⟨i1, hi1⟩
    rw [if_neg (by simp only [Slice.len]; scalar_tac)]
    step as ⟨s, back, hs1, hs2⟩
    step as ⟨s1, hs11, hs12⟩
    step as ⟨s2, hs2'⟩
    · rw [hs12]; simp [Slice.length, hs1, hi1]
    rw [decode_chain_of bytes i1 c1 _ (by rw [hi1]; exact h1)]
    simp only [bind_tc_ok, chain_len_eq]
    step as ⟨i3, hi3⟩
    rw [decode_chain_of bytes i3 c2 _ (by rw [hi3, hi1]; exact h2)]
    simp only [bind_tc_ok]
    step*
    have hs1' : s1.val = be64 e := by
      rw [hs11, hi1]; exact slice_of_drop h (by rw [be64_length])
    have hb : (back s2).val = be64 e := by
      rw [hs2, hs2', Array.from_slice_val _ _ (by rw [hs1', be64_length]; simp), hs1']
    rw [u64_eq_of_bv i4 e _ i4_post hb]
  obtain ⟨r, hr, rfl⟩ := Std.WP.spec_imp_exists hs
  exact hr


theorem spqr_from_bytes_loop0_one (bytes : Slice U8) (pos : Usize) (e : U64)
    (c1 c2 : tacenta_spqr.Chain) (rest : List U8)
    (h : bytes.val.drop pos.val = be64 e ++ (chainEnc c1 ++ (chainEnc c2 ++ rest)))
    (v : alloc.vec.Vec (U64 × tacenta_spqr.Chains)) (hv : v.val = []) :
    tacenta_spqr.State.from_bytes_loop0 90#usize { start := 0#usize, «end» := 1#usize } bytes pos v true
      ⦃ r => r.1.val = pos.val + 90 ∧ r.2.1.val = [(e, { send := some c1, receive := some c2 })] ∧
        r.2.2 = true ⦄ := by
  have hl := length_of_drop h (by rw [be64_length]; decide)
  have hent := decode_chains_entry_of bytes pos e c1 c2 rest h
  have hfit : pos.val + 90 ≤ bytes.val.length := by
    have := congrArg List.length h
    simp only [List.length_drop, List.length_append, be64_length, chainEnc_length] at this
    omega
  unfold tacenta_spqr.State.from_bytes_loop0
  apply loop.spec_decr_nat
    (measure := fun p => 1 - p.1.start.val)
    (inv := fun p => p.1.end = 1#usize ∧ p.2.2.2 = true ∧
      ((p.1.start.val = 0 ∧ p.2.1 = pos ∧ p.2.2.1 = v) ∨
       (p.1.start.val = 1 ∧ p.2.1.val = pos.val + 90 ∧
        p.2.2.1.val = [(e, { send := some c1, receive := some c2 })])))
  · rintro ⟨⟨st, en⟩, p', ch, ok'⟩ ⟨hend, hok, hcase⟩
    simp only at hend hok hcase ⊢
    unfold tacenta_spqr.State.from_bytes_loop0.body
    rcases hcase with ⟨hs, hp, hc⟩ | ⟨hs, hp, hc⟩
    · subst hp hc
      step*
      rw [hent]
      simp only [bind_tc_ok]
      step*
    · step*
  · exact ⟨rfl, rfl, Or.inl ⟨by simp, rfl, rfl⟩⟩


theorem spqr_from_bytes_loop1_empty (bytes : Slice U8) (pos : Usize)
    (v : alloc.vec.Vec tacenta_spqr.Skipped) (b : Bool) :
    tacenta_spqr.State.from_bytes_loop1 48#usize { start := 0#usize, «end» := 0#usize } bytes pos v b
      ⦃ r => r = (pos, v, b) ⦄ := by
  unfold tacenta_spqr.State.from_bytes_loop1
  apply loop.spec_decr_nat
    (measure := fun _ => 0)
    (inv := fun p => p.1.end.val ≤ p.1.start.val ∧ p.2 = (pos, v, b))
  · rintro ⟨⟨st, en⟩, pos', v', b'⟩ ⟨h1, h2⟩
    simp only at h1 h2
    simp only [tacenta_spqr.State.from_bytes_loop1.body]
    step*
  · exact ⟨by simp, rfl⟩

theorem direction_from_byte_dirByte (d : tacenta_spqr.Direction) :
    tacenta_spqr.Direction.from_byte (dirByte d) = ok (some d) := by
  match d with
  | .A2b => rfl
  | .B2a => rfl

set_option maxHeartbeats 1000000 in
theorem spqr_from_bytes_of (bytes : Slice U8) (q : tacenta_spqr.State) (e : U64)
    (c1 c2 : tacenta_spqr.Chain) (hb : bytes.val = spqrEnc q e c1 c2)
    (hch : q.chains.val = [(e, { send := some c1, receive := some c2 })])
    (hsk : q.skipped.val = []) (hinv : tacenta_spqr.State.invariant q = ok true) :
    tacenta_spqr.State.from_bytes bytes = ok (core.result.Result.Ok q) := by
  have hlen : bytes.val.length = 140 := by rw [hb, spqrEnc_length]
  have d0 : bytes.val.drop (0#usize).val = 1#u8 :: (spqrEnc q e c1 c2).tail := by
    simp only [hb, spqrEnc]; rfl
  have d1 : bytes.val.drop 1 = (spqrEnc q e c1 c2).tail := by rw [hb]; rfl
  simp only [spqrEnc, List.tail_cons] at d1
  have d33 := drop_next d1
  simp only [arr32_len, Nat.reduceAdd] at d33
  have d41 := drop_next d33
  simp only [be64_length, Nat.reduceAdd] at d41
  have d42 : bytes.val.drop 42 = be32 1#u32 ++ (be64 e ++ (chainEnc c1 ++ (chainEnc c2 ++ be32 0#u32))) := by
    have := drop_next (seg := [dirByte q.direction]) d41
    simpa using this
  have d46 := drop_next d42
  simp only [be32_length, Nat.reduceAdd] at d46
  have d136 : bytes.val.drop 136 = be32 0#u32 ++ [] := by
    have h1 := drop_next d46
    have h2 := drop_next h1
    have h3 := drop_next h2
    simp only [be64_length, chainEnc_length, Nat.reduceAdd] at h3
    simpa using h3
  have hs : tacenta_spqr.State.from_bytes bytes ⦃ x => x = core.result.Result.Ok q ⦄ := by
    unfold tacenta_spqr.State.from_bytes
    simp only [fixed_prefix_eq, bind_tc_ok]
    rw [if_neg (by simp only [Slice.len]; scalar_tac)]
    rw [index_usize_of _ _ _ _ d0]
    simp only [bind_tc_ok, tacenta_spqr.STATE_VERSION, bne_self_eq_false, Bool.false_eq_true,
      ↓reduceIte]
    step*
    all_goals try (simp only [Slice.length] at *; simp only [*, Array.repeat, List.length_replicate]; scalar_tac)
    have hi4 : i4.val = 41 := by rw [i4_post, i3_post]
    have hi5 : i5 = dirByte q.direction := by
      have := getElem_of_drop d41
      rw [List.getElem?_eq_getElem (by rw [hlen]; omega)] at this
      rw [i5_post]; simp only [hi4]; exact Option.some.inj this
    rw [hi5, direction_from_byte_dirByte]
    simp only [bind_tc_ok, chains_len_eq]
    step*
    all_goals try (simp only [Slice.length] at *; simp only [*, Array.repeat, List.length_replicate]; scalar_tac)
    all_goals
      have hs7 : s7.val = be32 1#u32 := by
        rw [s7_post1, i6_post, pos_post, hi4]; exact slice_of_drop d42 (by rw [be32_length])
      have hb8 : (to_slice_mut_back2 s8).val = be32 1#u32 := by
        rw [s6_post2, s8_post, Array.from_slice_val _ _ (by rw [hs7, be32_length]; simp), hs7]
      have hi7 : i7 = 1#u32 := u32_eq_of_bv i7 1#u32 _ i7_post hb8
      have hcc : chains_count = 1#usize := by
        rw [chains_count_post, hi7, UScalar.eq_equiv, UScalar.cast_val_eq]; simp
      have hi10 : i10.val = 1 := by rw [i10_post]; simp [Slice.len, hlen]
    · exfalso; rename_i hc; rw [hcc] at hc; scalar_tac
    rw [hcc]
    have hi6 : i6.val = 46 := by rw [i6_post, pos_post, hi4]
    step with spqr_from_bytes_loop0_one bytes i6 e c1 c2 (be32 0#u32) (by rw [hi6]; exact d46)
      (alloc.vec.Vec.with_capacity (U64 × tacenta_spqr.Chains) 1#usize) rfl
    rw [if_pos pos1_post3]
    simp only [skipped_len_eq, bind_tc_ok]
    step*
    all_goals try (simp only [Slice.length] at *; simp only [*, Array.repeat, List.length_replicate]; scalar_tac)
    all_goals
      have hp1 : pos1.val = 136 := by rw [pos1_post1, hi6]
      have hs10 : s10.val = be32 0#u32 := by
        rw [s10_post1, i12_post, hp1]; exact slice_of_drop d136 (by rw [be32_length])
      have hb11 : (to_slice_mut_back3 s11).val = be32 0#u32 := by
        rw [s9_post2, s11_post, Array.from_slice_val _ _ (by rw [hs10, be32_length]; simp), hs10]
      have hi13 : i13 = 0#u32 := u32_eq_of_bv i13 0#u32 _ i13_post hb11
      have hsc : skipped_count = 0#usize := by
        rw [skipped_count_post, hi13, UScalar.eq_equiv, UScalar.cast_val_eq]; simp
      have hi16 : i16.val = 2 := by rw [i16_post]; simp [Slice.len, hlen]
    · exfalso; rename_i hc; rw [hsc] at hc; scalar_tac
    rw [hsc]
    step with spqr_from_bytes_loop1_empty
    simp only [Prod.mk.injEq] at pos2_post
    obtain ⟨hq1, hq2, hq3⟩ := pos2_post
    have hlenU : pos2 = bytes.len := by
      rw [hq1, UScalar.eq_equiv, i12_post, hp1]; simp [Slice.len, hlen]
    have hrk : to_slice_mut_back s2 = q.rk := by
      rw [s_post2]
      exact from_slice_eq _ _ _ (by rw [s2_post, s1_post1, i3_post]; exact slice_of_drop d1 (by rw [arr32_len]))
    have hs4 : s4.val = be64 q.epoch := by
      rw [s4_post1, hi4, i3_post]; exact slice_of_drop d33 (by rw [be64_length])
    have hb5 : (to_slice_mut_back1 s5).val = be64 q.epoch := by
      rw [s3_post2, s5_post, Array.from_slice_val _ _ (by rw [hs4, be64_length]; simp), hs4]
    have hep : epoch = q.epoch := u64_eq_of_bv epoch q.epoch _ epoch_post hb5
    have hc1 : chains1 = q.chains := Subtype.ext (pos1_post2.trans hch.symm)
    have hsk1 : alloc.vec.Vec.with_capacity tacenta_spqr.Skipped 0#usize = q.skipped :=
      Subtype.ext (by rw [hsk]; rfl)
    have hrec : (⟨to_slice_mut_back s2, epoch, chains1, skipped1, q.direction⟩ : tacenta_spqr.State) = q := by
      rw [hrk, hep, hc1, hq2, hsk1]
    simp only [hq3, ↓reduceIte]
    rw [hrec, hlenU]
    simp only [↓reduceIte, bne_self_eq_false, Bool.false_eq_true, hinv, bind_tc_ok]
    simp
  obtain ⟨x, hx, rfl⟩ := Std.WP.spec_imp_exists hs
  exact hx


/-! ## The Triple state -/

/-- The bytes `tacenta_triple::State::to_bytes` writes for a Triple whose classical ratchet holds no
stored key and whose sparse ratchet has the one chain-table entry `(e, c1, c2)` and no stored key. -/
def tripleEnc (t : tacenta_triple.State) (e : U64) (c1 c2 : tacenta_spqr.Chain) : List U8 :=
  1#u8 :: (be32 185#u32 ++ (ratchetEnc t.classical ++ (be32 140#u32 ++ spqrEnc t.post_quantum e c1 c2)))

theorem tripleEnc_length (t : tacenta_triple.State) (e : U64) (c1 c2 : tacenta_spqr.Chain) :
    (tripleEnc t e c1 c2).length = 334 := by
  simp [tripleEnc, be32_length, ratchetEnc_length, spqrEnc_length]

theorem triple_to_bytes_spec (hz : ZeroizingVecRoundTrip) (t : tacenta_triple.State) (e : U64)
    (c1 c2 : tacenta_spqr.Chain) (hrs : t.classical.skipped.val = [])
    (hch : t.post_quantum.chains.val = [(e, { send := some c1, receive := some c2 })])
    (hsk : t.post_quantum.skipped.val = []) :
    tacenta_triple.State.to_bytes t ⦃ z => ∃ v,
      zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref vecInst z = ok v ∧ v.val = tripleEnc t e c1 c2 ⦄ := by
  unfold tacenta_triple.State.to_bytes
  step with ratchet_to_bytes_spec hz t.classical hrs as ⟨zc, vc, hvc, hvcv⟩
  step with spqr_to_bytes_spec hz t.post_quantum e c1 c2 hch hsk as ⟨zq, vq, hvq, hvqv⟩
  step as ⟨i, hi⟩
  simp only [hvc, hvq, bind_tc_ok]
  have hzc : zc.val.length = 185 := by rw [hvcv, ratchetEnc_length]
  have hzq : zq.val.length = 140 := by rw [hvqv, spqrEnc_length]
  step*
  · simp [alloc.vec.Vec.with_capacity, alloc.vec.Vec.new]; scalar_tac
  · simp only [out1_post, s_post, Array.to_slice, alloc.vec.Vec.deref, alloc.vec.Vec.with_capacity, alloc.vec.Vec.new,
      List.length_append, List.length_nil, List.length_cons, List.length_singleton, hzc, hzq,
      Std.Array.length]; scalar_tac
  · simp only [out2_post, out1_post, s_post, Array.to_slice, alloc.vec.Vec.deref, alloc.vec.Vec.with_capacity, alloc.vec.Vec.new,
      List.length_append, List.length_nil, List.length_cons, List.length_singleton, hzc, hzq,
      Std.Array.length]; scalar_tac
  · simp only [out3_post, out2_post, out1_post, s_post, s2_post, Array.to_slice, alloc.vec.Vec.deref, alloc.vec.Vec.with_capacity, alloc.vec.Vec.new,
      List.length_append, List.length_nil, List.length_cons, List.length_singleton, hzc, hzq,
      Std.Array.length]; scalar_tac
  · simp only [out4_post, out3_post, out2_post, out1_post, s_post, s2_post, Array.to_slice, alloc.vec.Vec.deref, alloc.vec.Vec.with_capacity, alloc.vec.Vec.new,
      List.length_append, List.length_nil, List.length_cons, List.length_singleton, hzc, hzq,
      Std.Array.length]; scalar_tac
  · rw [UScalar.eq_equiv]
    simp only [alloc.vec.Vec.len, out5_post, out4_post, out3_post, out2_post, out1_post, s_post, s2_post,
      len_post, i3_post, i2_post, hi, Array.to_slice, alloc.vec.Vec.deref, alloc.vec.Vec.with_capacity, alloc.vec.Vec.new,
      List.length_append, List.length_nil, List.length_cons, List.length_singleton, hzc, hzq,
      Std.Array.length]
    simp [alloc.vec.Vec.len, hzc, hzq]
  refine ⟨out5, z_post, ?_⟩
  have hl1 : zc.len = 185#usize := by rw [UScalar.eq_equiv]; simp [alloc.vec.Vec.len, hzc]
  have hl2 : zq.len = 140#usize := by rw [UScalar.eq_equiv]; simp [alloc.vec.Vec.len, hzq]
  have hc1 : UScalar.cast UScalarTy.U32 (185#usize) = 185#u32 := by
    rw [UScalar.eq_equiv, UScalar.cast_val_eq]; simp
  have hc2 : UScalar.cast UScalarTy.U32 (140#usize) = 140#u32 := by
    rw [UScalar.eq_equiv, UScalar.cast_val_eq]; simp
  simp only [out5_post, out4_post, out3_post, out2_post, out1_post, s_post, s2_post, a_post, a1_post,
    i6_post, i8_post, hl1, hl2, hc1, hc2, alloc.vec.Vec.deref, hvcv, hvqv, Array.to_slice,
    alloc.vec.Vec.with_capacity, alloc.vec.Vec.new, tripleEnc, be32, core.num.U32.to_be_bytes,
    tacenta_triple.STATE_VERSION, List.append_assoc, List.nil_append, List.cons_append]


theorem triple_take_len_prefixed_of (bytes : Slice U8) (pos : Usize) (n : U32) (payload rest : List U8)
    (hn : n.val = payload.length) (h : bytes.val.drop pos.val = be32 n ++ (payload ++ rest)) :
    tacenta_triple.take_len_prefixed bytes pos ⦃ r => ∃ sl p', r = some (sl, p') ∧ sl.val = payload ∧
      p'.val = pos.val + 4 + payload.length ⦄ := by
  have hfit : pos.val + 4 + payload.length ≤ bytes.val.length := by
    have := congrArg List.length h
    simp only [List.length_drop, List.length_append, be32_length] at this
    have := length_of_drop h (by rw [be32_length]; decide)
    rw [be32_length] at this
    omega
  have hmax : bytes.val.length ≤ Usize.max := bytes.property
  have hlenp := length_of_drop h (by rw [be32_length]; decide)
  rw [be32_length] at hlenp
  have hp : bytes.val.drop (pos.val + 4) = payload ++ rest := by
    have := drop_next h; rwa [be32_length] at this
  unfold tacenta_triple.take_len_prefixed
  step as ⟨o, ho⟩
  obtain ⟨s, rfl, hsv⟩ : ∃ s : Usize, o = some s ∧ s.val = pos.val + 4 := by
    rcases o with _ | s
    · simp at ho; scalar_tac
    · simp only at ho; exact ⟨s, rfl, ho.2.1⟩
  simp only
  rw [if_neg (by simp only [Slice.len]; scalar_tac)]
  step as ⟨s1, back, hs11, hs12⟩
  step as ⟨s2, hs21, hs22⟩
  step as ⟨s3, hs3⟩
  · rw [hs22]; simp [Slice.length, hs11, hsv]
  step as ⟨i1, hi1⟩
  have hs2v : s2.val = be32 n := by rw [hs21, hsv]; exact slice_of_drop h (by rw [be32_length])
  have hb3 : (back s3).val = be32 n := by
    rw [hs12, hs3, Array.from_slice_val _ _ (by rw [hs2v, be32_length]; simp), hs2v]
  have hi1n : i1 = n := u32_eq_of_bv i1 n _ hi1 hb3
  step as ⟨len, hlen⟩
  have hlenv : len.val = payload.length := by
    rw [hlen, hi1n, UScalar.cast_val_eq, ← hn]
    have : n.val < 2 ^ UScalarTy.Usize.numBits := by
      have h1 := n.hBounds; have h2 : 2 ^ UScalarTy.U32.numBits ≤ 2 ^ UScalarTy.Usize.numBits := by
        apply Nat.pow_le_pow_right (by decide); simp [UScalarTy.numBits]
      omega
    exact Nat.mod_eq_of_lt this
  step as ⟨o1, ho1⟩
  obtain ⟨e, rfl, hev⟩ : ∃ e : Usize, o1 = some e ∧ e.val = s.val + len.val := by
    rcases o1 with _ | e
    · simp at ho1; scalar_tac
    · simp only at ho1; exact ⟨e, rfl, ho1.2.1⟩
  simp only
  rw [if_neg (by simp only [Slice.len]; scalar_tac)]
  step as ⟨s4, hs41, hs42⟩
  refine ⟨s4, e, rfl, ?_, by rw [hev, hsv, hlenv]⟩
  rw [hs41, hsv, hev, hsv, hlenv]
  exact slice_of_drop hp rfl


open Tacenta.SessionUnitRatchetImportInv (bind_eq_ok_inv)

/-- The Triple's invariant holds only if both ratchets' invariants hold. -/
theorem triple_invariant_parts (t : tacenta_triple.State)
    (h : tacenta_triple.State.invariant t = ok true) :
    tacenta_ratchet.State.invariant t.classical = ok true ∧
      tacenta_spqr.State.invariant t.post_quantum = ok true := by
  unfold tacenta_triple.State.invariant at h
  obtain ⟨d, -, h⟩ := bind_eq_ok_inv h
  obtain ⟨ra, -, h⟩ := bind_eq_ok_inv h
  obtain ⟨o, -, h⟩ := bind_eq_ok_inv h
  obtain ⟨ra1, -, h⟩ := bind_eq_ok_inv h
  obtain ⟨b, hb, h⟩ := bind_eq_ok_inv h
  split at h
  · rename_i hbt
    obtain ⟨b1, hb1, h⟩ := bind_eq_ok_inv h
    split at h
    · rename_i hb1t
      subst hbt hb1t
      exact ⟨hb, hb1⟩
    · simp at h
  · simp at h

set_option maxHeartbeats 1000000 in
theorem triple_from_bytes_of (bytes : Slice U8) (t : tacenta_triple.State) (e : U64)
    (c1 c2 : tacenta_spqr.Chain) (hb : bytes.val = tripleEnc t e c1 c2)
    (hrs : t.classical.skipped.val = [])
    (hch : t.post_quantum.chains.val = [(e, { send := some c1, receive := some c2 })])
    (hsk : t.post_quantum.skipped.val = []) (hinv : tacenta_triple.State.invariant t = ok true) :
    tacenta_triple.State.from_bytes bytes = ok (core.result.Result.Ok t) := by
  obtain ⟨hinvr, hinvq⟩ := triple_invariant_parts t hinv
  have hlen : bytes.val.length = 334 := by rw [hb, tripleEnc_length]
  have d0 : bytes.val.drop (0#usize).val = 1#u8 :: (tripleEnc t e c1 c2).tail := by
    simp only [hb, tripleEnc]; rfl
  have d1 : bytes.val.drop (1#usize).val = (tripleEnc t e c1 c2).tail := by rw [hb]; rfl
  simp only [tripleEnc, List.tail_cons] at d1
  have hs : tacenta_triple.State.from_bytes bytes ⦃ x => x = core.result.Result.Ok t ⦄ := by
    unfold tacenta_triple.State.from_bytes
    simp only [core.slice.Slice.is_empty, bind_tc_ok]
    rw [if_neg (by simp [Slice.length, hlen])]
    rw [index_usize_of _ _ _ _ d0]
    simp only [bind_tc_ok, tacenta_triple.STATE_VERSION, bne_self_eq_false, Bool.false_eq_true,
      ↓reduceIte]
    step with triple_take_len_prefixed_of bytes 1#usize 185#u32 (ratchetEnc t.classical)
      (be32 140#u32 ++ spqrEnc t.post_quantum e c1 c2) (by rw [ratchetEnc_length]; rfl) d1
      as ⟨sl, p1, o, ho, hsl, hp1⟩
    simp only [ho]
    step with (show tacenta_ratchet.State.from_bytes sl ⦃ x => x = core.result.Result.Ok t.classical ⦄ by
      rw [ratchet_from_bytes_of sl t.classical hsl hrs hinvr]; simp) as ⟨r, hr⟩
    simp only [hr]
    have d2 : bytes.val.drop p1.val = be32 140#u32 ++ (spqrEnc t.post_quantum e c1 c2 ++ []) := by
      rw [hp1, ratchetEnc_length]
      have := drop_next (drop_next d1)
      simp only [be32_length, ratchetEnc_length] at this
      simpa using this
    step with triple_take_len_prefixed_of bytes p1 140#u32 (spqrEnc t.post_quantum e c1 c2) []
      (by rw [spqrEnc_length]; rfl) d2 as ⟨sl1, p2, o1, ho1, hsl1, hp2⟩
    simp only [ho1]
    step with (show tacenta_spqr.State.from_bytes sl1 ⦃ x => x = core.result.Result.Ok t.post_quantum ⦄ by
      rw [spqr_from_bytes_of sl1 t.post_quantum e c1 c2 hsl1 hch hsk hinvq]; simp) as ⟨r1, hr1⟩
    simp only [hr1]
    have hp2v : p2 = Slice.len bytes := by
      rw [UScalar.eq_equiv, hp2, hp1, ratchetEnc_length, spqrEnc_length]; simp [Slice.len, hlen]
    rw [hp2v]
    simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, hinv, bind_tc_ok]
    simp
  obtain ⟨x, hx, rfl⟩ := Std.WP.spec_imp_exists hs
  exact hx


/-! ## The Braid at `KeysUnsampled` -/

/-- The 64 bytes of an authenticator: the root key, then the MAC key. -/
def authEnc (a : tacenta_braid.Auth) : List U8 := a.root_key.val ++ a.mac_key.val

theorem authEnc_length (a : tacenta_braid.Auth) : (authEnc a).length = 64 := by
  simp [authEnc, arr32_len]

theorem setSlice_app {α : Type} (pre mid post s' : List α) (h : s'.length = mid.length) :
    (pre ++ mid ++ post).setSlice! pre.length s' = pre ++ s' ++ post := by
  simp only [List.setSlice!, List.length_append]
  have hmin : min s'.length (pre.length + mid.length + post.length - pre.length) = mid.length := by
    omega
  rw [hmin]
  simp [List.take_append, List.drop_append, h, List.take_of_length_le]

@[local step]
theorem auth_to_bytes_spec (a : tacenta_braid.Auth) :
    tacenta_braid.Auth.to_bytes a ⦃ r => r.val = authEnc a ⦄ := by
  unfold tacenta_braid.Auth.to_bytes
  step*
  have hr : (Array.repeat 64#usize 0#u8).val = [] ++ List.replicate 32 0#u8 ++ List.replicate 32 0#u8 := by
    simp [Array.repeat, List.replicate_add]
  rw [s3_post3, s_post3, s5_post, s4_post, s2_post, s1_post, hr]
  have e1 : (([] : List U8) ++ List.replicate 32 0#u8 ++ List.replicate 32 0#u8).setSlice! 0
      a.root_key.to_slice.val = [] ++ a.root_key.val ++ List.replicate 32 0#u8 :=
    setSlice_app [] _ _ _ (by simp [Array.to_slice, arr32_len])
  have e2 := setSlice_app ([] ++ a.root_key.val) (List.replicate 32 0#u8) [] a.mac_key.to_slice.val
    (by simp [Array.to_slice, arr32_len])
  have hl : ([] ++ a.root_key.val).length = 32 := by simp [arr32_len]
  rw [hl, List.append_nil] at e2
  rw [e1, e2]
  simp [authEnc, Array.to_slice]


theorem auth_from_bytes_of (arr : Array U8 64#usize) (a : tacenta_braid.Auth) (h : arr.val = authEnc a) :
    tacenta_braid.Auth.from_bytes arr = ok a := by
  have hs : tacenta_braid.Auth.from_bytes arr ⦃ r => r = a ⦄ := by
    unfold tacenta_braid.Auth.from_bytes
    step*
    · rw [s1_post2]; simp [Slice.length, s_post1]
    · rw [s4_post2]; simp [Slice.length, s3_post1, Array.to_slice]
    have hrk : to_slice_mut_back s2 = a.root_key := by
      rw [s_post2]
      apply from_slice_eq
      rw [s2_post, s1_post1, Array.to_slice]
      simp only [h, authEnc, List.slice]
      simp [List.take_append_of_le_length, arr32_len]
    have hmk : to_slice_mut_back1 s5 = a.mac_key := by
      rw [s3_post2]
      apply from_slice_eq
      rw [s5_post, s4_post1, Array.to_slice]
      simp only [h, authEnc]
      simp [arr32_len]
    rw [hrk, hmk]
  obtain ⟨r, hr, rfl⟩ := Std.WP.spec_imp_exists hs
  exact hr


theorem head_len_eq : tacenta_braid.HEAD_LEN = ok 2#usize := by
  have h : tacenta_braid.HEAD_LEN ⦃ r => r = 2#usize ⦄ := by unfold tacenta_braid.HEAD_LEN; step*
  obtain ⟨r, hr, hre⟩ := Std.WP.spec_imp_exists h
  rw [hr, hre]

theorem epoch_and_auth_len_eq : tacenta_braid.EPOCH_AND_AUTH_LEN = ok 72#usize := by
  have h : tacenta_braid.EPOCH_AND_AUTH_LEN ⦃ r => r = 72#usize ⦄ := by
    unfold tacenta_braid.EPOCH_AND_AUTH_LEN; step*
  obtain ⟨r, hr, hre⟩ := Std.WP.spec_imp_exists h
  rw [hr, hre]

/-- The bytes `tacenta_braid::Braid::to_bytes` writes for a Braid in `KeysUnsampled`: the version byte,
the state tag 0, the epoch, the authenticator. -/
def braidEnc (epoch : U64) (auth : tacenta_braid.Auth) : List U8 :=
  1#u8 :: 0#u8 :: (be64 epoch ++ authEnc auth)

theorem braidEnc_length (epoch : U64) (auth : tacenta_braid.Auth) : (braidEnc epoch auth).length = 74 := by
  simp [braidEnc, be64_length, authEnc_length]

theorem braid_to_bytes_spec (hz : ZeroizingVecRoundTrip) (epoch : U64) (auth : tacenta_braid.Auth) :
    tacenta_braid.Braid.to_bytes ⟨tacenta_braid.State.KeysUnsampled epoch auth⟩ ⦃ z => ∃ v,
      zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref vecInst z = ok v ∧ v.val = braidEnc epoch auth ⦄ := by
  unfold tacenta_braid.Braid.to_bytes tacenta_braid.Braid.encoded_len tacenta_braid.Braid.state_tag
  simp only [head_len_eq, epoch_and_auth_len_eq, bind_tc_ok, alloc.vec.Vec.with_capacity]
  step*
  · simp_all [Array.to_slice, authEnc_length, alloc.vec.Vec.new]; scalar_tac
  · rw [UScalar.eq_equiv]; simp_all [Array.to_slice, authEnc_length, alloc.vec.Vec.new, alloc.vec.Vec.len]
  · refine ⟨out3, z_post, ?_⟩
    simp_all [Array.to_slice, braidEnc, be64, core.num.U64.to_be_bytes, alloc.vec.Vec.new,
      tacenta_braid.STATE_VERSION]


theorem read_u64_of (bytes : Slice U8) (pos : Usize) (x : U64) (rest : List U8)
    (h : bytes.val.drop pos.val = be64 x ++ rest) :
    tacenta_braid.read_u64 bytes pos = ok (some x) := by
  have hl := length_of_drop h (by rw [be64_length]; decide)
  rw [be64_length] at hl
  have hs : tacenta_braid.read_u64 bytes pos ⦃ r => r = some x ⦄ := by
    unfold tacenta_braid.read_u64
    step as ⟨i1, hi1⟩
    rw [if_neg (by simp only [Slice.len]; scalar_tac)]
    step*
    · simp [Slice.length, s_post1, s1_post2, hi1]
    have hs1 : s1.val = be64 x := by rw [s1_post1, hi1]; exact slice_of_drop h (by rw [be64_length])
    have hb : (to_slice_mut_back s2).val = be64 x := by
      rw [s_post2, s2_post, Array.from_slice_val _ _ (by rw [hs1, be64_length]; simp), hs1]
    rw [u64_eq_of_bv i2 x _ i2_post hb]
  obtain ⟨r, hr, rfl⟩ := Std.WP.spec_imp_exists hs
  exact hr

theorem read_epoch_of (bytes : Slice U8) (pos : Usize) (epoch : U64) (rest : List U8)
    (h : bytes.val.drop pos.val = be64 epoch ++ rest) (hmax : epoch ≠ core.num.U64.MAX) :
    tacenta_braid.read_epoch bytes pos = ok (some epoch) := by
  unfold tacenta_braid.read_epoch
  rw [read_u64_of bytes pos epoch rest h]
  simp [hmax]

theorem read_auth_of (bytes : Slice U8) (pos : Usize) (a : tacenta_braid.Auth) (rest : List U8)
    (h : bytes.val.drop pos.val = authEnc a ++ rest) :
    tacenta_braid.read_auth bytes pos ⦃ r => ∃ p, r = some (a, p) ∧ p.val = pos.val + 64 ⦄ := by
  have hl := length_of_drop h (by rw [authEnc_length]; decide)
  rw [authEnc_length] at hl
  unfold tacenta_braid.read_auth
  step as ⟨i1, hi1⟩
  rw [if_neg (by simp only [Slice.len]; scalar_tac)]
  step*
  · simp [Slice.length, s_post1, s1_post2, hi1]
  have hs1 : s1.val = authEnc a := by rw [s1_post1, hi1]; exact slice_of_drop h (by rw [authEnc_length])
  rw [auth_from_bytes_of _ a (by rw [s_post2, s2_post, Array.from_slice_val _ _ (by rw [hs1, authEnc_length]; simp), hs1])]
  simp [hi1]


theorem decode_state_unsampled_of (bytes : Slice U8) (pos : Usize) (epoch : U64)
    (auth : tacenta_braid.Auth) (rest : List U8)
    (h : bytes.val.drop pos.val = be64 epoch ++ (authEnc auth ++ rest)) (hmax : epoch ≠ core.num.U64.MAX) :
    tacenta_braid.decode_state 0#u8 bytes pos ⦃ r => ∃ p,
      r = some (tacenta_braid.State.KeysUnsampled epoch auth, p) ∧ p.val = pos.val + 72 ⦄ := by
  have hl := length_of_drop h (by rw [be64_length]; decide)
  rw [be64_length] at hl
  have ha : bytes.val.drop (pos.val + 8) = authEnc auth ++ rest := by
    have := drop_next h; rwa [be64_length] at this
  unfold tacenta_braid.decode_state
  show (do
    let o ← tacenta_braid.read_epoch bytes pos
    match o with
    | none => ok none
    | some epoch =>
      let i ← pos + 8#usize
      let o1 ← tacenta_braid.read_auth bytes i
      match o1 with
      | none => ok none
      | some p =>
        let (auth, pos1) := p
        ok (some (tacenta_braid.State.KeysUnsampled epoch auth, pos1))) ⦃ _ ⦄
  rw [read_epoch_of bytes pos epoch _ h hmax]
  simp only [bind_tc_ok]
  step as ⟨i, hi⟩
  step with read_auth_of bytes i auth rest (by rw [hi]; exact ha) as ⟨p, o1, ho1, hp⟩
  simp only [ho1]
  step*


theorem braid_from_bytes_of (bytes : Slice U8) (epoch : U64) (auth : tacenta_braid.Auth)
    (hb : bytes.val = braidEnc epoch auth) (hmax : epoch ≠ core.num.U64.MAX)
    (hinv : tacenta_braid.Braid.invariant ⟨tacenta_braid.State.KeysUnsampled epoch auth⟩ = ok true) :
    tacenta_braid.Braid.from_bytes bytes =
      ok (core.result.Result.Ok ⟨tacenta_braid.State.KeysUnsampled epoch auth⟩) := by
  have hlen : bytes.val.length = 74 := by rw [hb, braidEnc_length]
  have d0 : bytes.val.drop (0#usize).val = 1#u8 :: (braidEnc epoch auth).tail := by
    simp only [hb, braidEnc]; rfl
  have d1 : bytes.val.drop (1#usize).val = 0#u8 :: (be64 epoch ++ authEnc auth) := by
    simp only [hb, braidEnc]; rfl
  have d2 : bytes.val.drop (2#usize).val = be64 epoch ++ (authEnc auth ++ []) := by
    simp only [hb, braidEnc, List.append_nil]; rfl
  have hs : tacenta_braid.Braid.from_bytes bytes ⦃ x =>
      x = core.result.Result.Ok ⟨tacenta_braid.State.KeysUnsampled epoch auth⟩ ⦄ := by
    unfold tacenta_braid.Braid.from_bytes
    rw [if_neg (by simp only [Slice.len]; scalar_tac)]
    rw [index_usize_of _ _ _ _ d0]
    simp only [bind_tc_ok, tacenta_braid.STATE_VERSION, bne_self_eq_false, Bool.false_eq_true,
      ↓reduceIte]
    rw [index_usize_of _ _ _ _ d1]
    simp only [bind_tc_ok]
    step with decode_state_unsampled_of bytes 2#usize epoch auth [] d2 hmax as ⟨p, o, ho, hp⟩
    simp only [ho]
    have hpl : p = Slice.len bytes := by rw [UScalar.eq_equiv, hp]; simp [Slice.len, hlen]
    simp only [hpl, ↓reduceIte, hinv, bind_tc_ok]
    step*
    rw [hinv]
    simp
  obtain ⟨x, hx, rfl⟩ := Std.WP.spec_imp_exists hs
  exact hx


/-! ## Two laws about opaque library functions on the session's path -/

/-- `Option::branch` on `Some x` continues with `x`, as a shape over the constant (the translation declares
`core::option::Option::branch` without a body).  True of the standard library by reading
(`core/src/option.rs`: `Some(v) => ControlFlow::Continue(v)`). -/
def OptionBranchSomeShape
    (br : {T : Type} → Option T → Result (core.ops.control_flow.ControlFlow (Option core.convert.Infallible) T)) :
    Prop :=
  ∀ (T : Type) (x : T), br (some x) = ok (core.ops.control_flow.ControlFlow.Continue x)

/-- The law at the real constant. -/
def OptionBranchSome : Prop := OptionBranchSomeShape @core.option.Option.Insts.CoreOpsTry_traitTry.branch

/-- A model of `Option::branch`: the standard library's own definition. -/
def optionBranchImpl {T : Type} :
    Option T → Result (core.ops.control_flow.ControlFlow (Option core.convert.Infallible) T)
  | some x => ok (core.ops.control_flow.ControlFlow.Continue x)
  | none => ok (core.ops.control_flow.ControlFlow.Break none)

theorem lifecycle_take_len_prefixed_of (hbr : OptionBranchSome) (bytes : Slice U8) (pos : Usize)
    (n : U32) (payload rest : List U8)
    (hn : n.val = payload.length) (h : bytes.val.drop pos.val = be32 n ++ (payload ++ rest)) :
    lifecycle.take_len_prefixed bytes pos ⦃ r => ∃ sl p', r = some (sl, p') ∧ sl.val = payload ∧
      p'.val = pos.val + 4 + payload.length ⦄ := by
  have hfit : pos.val + 4 + payload.length ≤ bytes.val.length := by
    have := congrArg List.length h
    simp only [List.length_drop, List.length_append, be32_length] at this
    have := length_of_drop h (by rw [be32_length]; decide)
    rw [be32_length] at this
    omega
  have hmax : bytes.val.length ≤ Usize.max := bytes.property
  have hlenp := length_of_drop h (by rw [be32_length]; decide)
  rw [be32_length] at hlenp
  have hp : bytes.val.drop (pos.val + 4) = payload ++ rest := by
    have := drop_next h; rwa [be32_length] at this
  unfold lifecycle.take_len_prefixed
  step as ⟨o, ho⟩
  obtain ⟨s, rfl, hsv⟩ : ∃ s : Usize, o = some s ∧ s.val = pos.val + 4 := by
    rcases o with _ | s
    · simp at ho; scalar_tac
    · simp only at ho; exact ⟨s, rfl, ho.2.1⟩
  rw [hbr]
  simp only [bind_tc_ok]
  rw [if_neg (by simp only [Slice.len]; scalar_tac)]
  step as ⟨s1, back, hs11, hs12⟩
  step as ⟨s2, hs21, hs22⟩
  step as ⟨s3, hs3⟩
  · rw [hs22]; simp [Slice.length, hs11, hsv]
  step as ⟨i1, hi1⟩
  have hs2v : s2.val = be32 n := by rw [hs21, hsv]; exact slice_of_drop h (by rw [be32_length])
  have hb3 : (back s3).val = be32 n := by
    rw [hs12, hs3, Array.from_slice_val _ _ (by rw [hs2v, be32_length]; simp), hs2v]
  have hi1n : i1 = n := u32_eq_of_bv i1 n _ hi1 hb3
  step as ⟨len, hlen⟩
  have hlenv : len.val = payload.length := by
    rw [hlen, hi1n, UScalar.cast_val_eq, ← hn]
    have : n.val < 2 ^ UScalarTy.Usize.numBits := by
      have h1 := n.hBounds; have h2 : 2 ^ UScalarTy.U32.numBits ≤ 2 ^ UScalarTy.Usize.numBits := by
        apply Nat.pow_le_pow_right (by decide); simp [UScalarTy.numBits]
      omega
    exact Nat.mod_eq_of_lt this
  step as ⟨o1, ho1⟩
  obtain ⟨e, rfl, hev⟩ : ∃ e : Usize, o1 = some e ∧ e.val = s.val + len.val := by
    rcases o1 with _ | e
    · simp at ho1; scalar_tac
    · simp only at ho1; exact ⟨e, rfl, ho1.2.1⟩
  rw [hbr]
  simp only [bind_tc_ok]
  rw [if_neg (by simp only [Slice.len]; scalar_tac)]
  step as ⟨s4, hs41, hs42⟩
  refine ⟨s4, e, rfl, ?_, by rw [hev, hsv, hlenv]⟩
  rw [hs41, hsv, hev, hsv, hlenv]
  exact slice_of_drop hp rfl


/-- `Vec::as_slice` returns the vector's own slice view, as a shape over the constant (the translation
declares it without a body).  True of the standard library by reading (`alloc/src/vec/mod.rs`: `as_slice`
is the deref of the vector). -/
def VecAsSliceShape (asSlice : {T : Type} → (A : Type) → alloc.vec.Vec T → Result (Slice T)) : Prop :=
  ∀ (v : alloc.vec.Vec U8), asSlice Global v = ok (alloc.vec.Vec.deref v)

/-- The law at the real constant. -/
def VecAsSlice : Prop := VecAsSliceShape @alloc.vec.Vec.as_slice

/-- A model of `Vec::as_slice`: the deref. -/
def vecAsSliceImpl {T : Type} (_A : Type) (v : alloc.vec.Vec T) : Result (Slice T) :=
  ok (alloc.vec.Vec.deref v)

theorem vecAsSliceImpl_shape : VecAsSliceShape @vecAsSliceImpl := fun _ => rfl

/-! ## Three laws about the boundary's byte codecs, over an interpretation -/

open Tacenta.UnitSatisfiabilityJoint (Interp Interp.real Interp.model)

/-- Reading a public key's bytes and rebuilding a key from them gives the key back. -/
def DhPublicBytesRoundTripShape (I : Interp) : Prop :=
  ∀ pk : I.PublicKeyBytes, ∃ a, I.dhPubAsBytes pk = ok a ∧ I.dhPubFromBytes a = ok pk

/-- The law at the real constants: `PublicKeyBytes::as_bytes` then `PublicKeyBytes::from_bytes`. -/
def DhPublicBytesRoundTrip : Prop := DhPublicBytesRoundTripShape Interp.real

theorem dhPublicBytesRoundTrip_is : DhPublicBytesRoundTrip ↔
    ∀ pk, ∃ a, tacenta_boundary.dh.PublicKeyBytes.as_bytes pk = ok a ∧
      tacenta_boundary.dh.PublicKeyBytes.from_bytes a = ok pk := Iff.rfl

theorem model_dhPublicBytesRoundTrip : DhPublicBytesRoundTripShape Interp.model :=
  fun _ => ⟨_, rfl, rfl⟩

/-- The `Zeroize` instance `PrivateKey::to_bytes` wraps its 32 bytes with. -/
noncomputable abbrev arrInst : zeroize.Zeroize (Array U8 32#usize) :=
  Array.Insts.ZeroizeZeroize 32#usize (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)

/-- Exporting a private key's bytes, reading them out of the `Zeroizing` wrapper and rebuilding a key from
them gives the key back. -/
def DhPrivateBytesRoundTripShape (I : Interp) : Prop :=
  ∀ k : I.PrivateKey, ∃ z a, I.dhPrivToBytes k = ok z ∧ I.zDeref arrInst z = ok a ∧
    I.dhPrivFromBytes a = ok k

/-- The law at the real constants: `PrivateKey::to_bytes`, `Zeroizing::deref`, `PrivateKey::from_bytes`. -/
def DhPrivateBytesRoundTrip : Prop := DhPrivateBytesRoundTripShape Interp.real

theorem dhPrivateBytesRoundTrip_is : DhPrivateBytesRoundTrip ↔
    ∀ k, ∃ z a, tacenta_boundary.dh.PrivateKey.to_bytes k = ok z ∧
      zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref arrInst z = ok a ∧
      tacenta_boundary.dh.PrivateKey.from_bytes a = ok k := Iff.rfl

theorem model_dhPrivateBytesRoundTrip : DhPrivateBytesRoundTripShape Interp.model :=
  fun _ => ⟨_, _, rfl, rfl, rfl⟩

/-- Wrapping a byte vector in `Zeroizing` and reading it back gives the vector. -/
def ZeroizingVecRoundTripShape (I : Interp) : Prop :=
  ∀ (inst : zeroize.Zeroize (alloc.vec.Vec U8)) (v : alloc.vec.Vec U8),
    ∃ z, I.zNew inst v = ok z ∧ I.zDeref inst z = ok v

theorem zeroizingVecRoundTrip_is : ZeroizingVecRoundTrip ↔ ZeroizingVecRoundTripShape Interp.real :=
  Iff.rfl

theorem model_zeroizingVecRoundTrip : ZeroizingVecRoundTripShape Interp.model :=
  fun _ _ => ⟨_, rfl, rfl⟩


/-! ## The pending initial message -/

/-- A length-prefixed field: the four-byte big-endian length (cast to `u32`), then the bytes. -/
def lenEnc (s : Slice U8) : List U8 := be32 (UScalar.cast UScalarTy.U32 (Slice.len s)) ++ s.val

theorem cast_len_val (s : Slice U8) (h : s.val.length < 4294967296) :
    (UScalar.cast UScalarTy.U32 (Slice.len s)).val = s.val.length := by
  rw [UScalar.cast_val_eq]
  simp only [Slice.len, UScalarTy.numBits]
  exact Nat.mod_eq_of_lt (by simpa [Slice.length] using h)

theorem lenEnc_length (s : Slice U8) : (lenEnc s).length = 4 + s.val.length := by
  simp [lenEnc, be32_length]

@[step]
theorem lifecycle_push_len_prefixed_spec (out : alloc.vec.Vec U8) (s : Slice U8)
    (h : out.val.length + 4 + s.val.length ≤ Usize.max) :
    lifecycle.push_len_prefixed out s ⦃ w => w.val = out.val ++ lenEnc s ⦄ := by
  unfold lifecycle.push_len_prefixed
  step*
  all_goals (try simp_all [Array.to_slice, lenEnc, be32, core.num.U32.to_be_bytes])

/-- The bytes `PendingInitial::to_bytes` writes, with `a` the ephemeral key's bytes. -/
def pendEnc (p : lifecycle.PendingInitial) (a : Array U8 32#usize) : List U8 :=
  a.val ++ (lenEnc (alloc.vec.Vec.deref p.kem_ciphertext) ++ (be32 p.signed_prekey_id ++
    (be32 p.one_time_prekey_id ++ be32 p.kem_prekey_id)))

theorem pendEnc_length (p : lifecycle.PendingInitial) (a : Array U8 32#usize) :
    (pendEnc p a).length = 48 + p.kem_ciphertext.val.length := by
  simp [pendEnc, lenEnc_length, be32_length, arr32_len, alloc.vec.Vec.deref]; omega

theorem pending_to_bytes_spec (p : lifecycle.PendingInitial) (a : Array U8 32#usize)
    (ha : tacenta_boundary.dh.PublicKeyBytes.as_bytes p.ephemeral_public = ok a)
    (hct : p.kem_ciphertext.val.length ≤ 65536) :
    lifecycle.PendingInitial.to_bytes p ⦃ v => v.val = pendEnc p a ⦄ := by
  unfold lifecycle.PendingInitial.to_bytes
  rw [ha]
  simp only [bind_tc_ok]
  step*
  all_goals try (simp_all [Array.to_slice, alloc.vec.Vec.deref, lenEnc_length, arr32_len]; scalar_tac)
  simp_all [Array.to_slice, pendEnc, be32, core.num.U32.to_be_bytes]


theorem pending_from_bytes_of (hbr : OptionBranchSome) (bytes : Slice U8) (p : lifecycle.PendingInitial)
    (a : Array U8 32#usize) (hb : bytes.val = pendEnc p a)
    (hfb : tacenta_boundary.dh.PublicKeyBytes.from_bytes a = ok p.ephemeral_public)
    (hct : p.kem_ciphertext.val.length ≤ 65536) :
    lifecycle.PendingInitial.from_bytes bytes = ok (some p) := by
  have hlen : bytes.val.length = 48 + p.kem_ciphertext.val.length := by rw [hb, pendEnc_length]
  have d0 : bytes.val.drop 0 = a.val ++ (lenEnc (alloc.vec.Vec.deref p.kem_ciphertext) ++
      (be32 p.signed_prekey_id ++ (be32 p.one_time_prekey_id ++ be32 p.kem_prekey_id))) := by
    simp only [hb, pendEnc, List.drop_zero]
  have d32 := drop_next d0
  simp only [arr32_len, Nat.zero_add, lenEnc, List.append_assoc] at d32
  have hn : (UScalar.cast UScalarTy.U32 (Slice.len (alloc.vec.Vec.deref p.kem_ciphertext))).val =
      (alloc.vec.Vec.deref p.kem_ciphertext).val.length :=
    cast_len_val _ (by simp [alloc.vec.Vec.deref]; omega)
  have hs : lifecycle.PendingInitial.from_bytes bytes ⦃ r => r = some p ⦄ := by
    unfold lifecycle.PendingInitial.from_bytes
    rw [if_neg (by simp only [Slice.len]; scalar_tac)]
    step as ⟨s, back, hs1, hs2⟩
    step as ⟨s1, hs11, hs12⟩
    step as ⟨s2, hs2'⟩
    · rw [hs12]; simp [Slice.length, hs1]
    step with lifecycle_take_len_prefixed_of hbr bytes 32#usize _ (alloc.vec.Vec.deref p.kem_ciphertext).val
      _ hn (by simpa using d32) as ⟨sl, pos, o, ho, hsl, hpos⟩
    rw [ho, hbr]
    simp only [bind_tc_ok]
    have hmaxb : bytes.val.length ≤ Usize.max := bytes.property
    have hda : bytes.val.drop pos.val = be32 p.signed_prekey_id ++ (be32 p.one_time_prekey_id ++
        be32 p.kem_prekey_id) := by
      have := drop_next (drop_next d32)
      rw [hpos]; simp only [be32_length] at this; simpa [Nat.add_assoc] using this
    step as ⟨kc, hkc⟩
    have hposv : pos.val + 12 = bytes.val.length := by
      rw [hpos, hlen]; simp [alloc.vec.Vec.deref]; omega
    step as ⟨i2, hi2⟩
    rw [if_neg (by
      simp only [bne_iff_ne, ne_eq, Decidable.not_not]
      rw [UScalar.eq_equiv, hi2, hpos]; simp [Slice.len, hlen, alloc.vec.Vec.deref]; omega)]
    step as ⟨s3, back1, hs31, hs32⟩
    step as ⟨i3, hi3⟩
    step as ⟨s4, hs41, hs42⟩
    step as ⟨s5, hs5⟩
    · rw [hs42]; simp [Slice.length, hs31, hi3]
    step as ⟨s6, back2, hs61, hs62⟩
    step as ⟨i4, hi4⟩
    step as ⟨s7, hs71, hs72⟩
    step as ⟨s8, hs8⟩
    · rw [hs72]; simp [Slice.length, hs61, hi3, hi4]
    step as ⟨s9, back3, hs91, hs92⟩
    step as ⟨s10, hs101, hs102⟩
    step as ⟨s11, hs11'⟩
    · rw [hs102]; simp [Slice.length, hs91, hi2, hi4]
    have hba : back s2 = a := by
      rw [hs2]; exact from_slice_eq _ _ _ (by rw [hs2', hs11]; exact slice_of_drop d0 (by rw [arr32_len]))
    simp only [hba, hfb, bind_tc_ok]
    step*
    have hd4 : bytes.val.drop (pos.val + 4) = be32 p.one_time_prekey_id ++ be32 p.kem_prekey_id := by
      have := drop_next hda; rwa [be32_length] at this
    have hd8 : bytes.val.drop (pos.val + 8) = be32 p.kem_prekey_id ++ [] := by
      have := drop_next hd4; rw [be32_length] at this; simpa [Nat.add_assoc] using this
    have hb5 : (back1 s5).val = be32 p.signed_prekey_id := by
      have h4 : s4.val = be32 p.signed_prekey_id := by
        rw [hs41, hi3]; exact slice_of_drop hda (by rw [be32_length])
      rw [hs32, hs5, Array.from_slice_val _ _ (by rw [h4, be32_length]; simp), h4]
    have hb8 : (back2 s8).val = be32 p.one_time_prekey_id := by
      have h7 : s7.val = be32 p.one_time_prekey_id := by
        rw [hs71, hi3, hi4]; exact slice_of_drop hd4 (by rw [be32_length]; try omega)
      rw [hs62, hs8, Array.from_slice_val _ _ (by rw [h7, be32_length]; simp), h7]
    have hb11 : (back3 s11).val = be32 p.kem_prekey_id := by
      have h10 : s10.val = be32 p.kem_prekey_id := by
        rw [hs101, hi4, hi2]; exact slice_of_drop hd8 (by rw [be32_length]; try omega)
      rw [hs92, hs11', Array.from_slice_val _ _ (by rw [h10, be32_length]; simp), h10]
    have hkc' : kc = p.kem_ciphertext := by
      rw [← hkc]; exact Subtype.ext hsl
    rw [u32_eq_of_bv _ _ _ i5_post hb5, u32_eq_of_bv _ _ _ i6_post hb8,
      u32_eq_of_bv _ _ _ i7_post hb11, hkc']
  obtain ⟨r, hr, rfl⟩ := Std.WP.spec_imp_exists hs
  exact hr


end Tacenta.UnitLifecycleSessionCodec

/-! ## Pins

The constants each result depends on, and the statement of each result and definition, held by the
build.  `attest.py` requires every one of them (`REQUIRED_PINS`, `REQUIRED_STATEMENT_PINS`,
`REQUIRED_PRINT_FORM`). -/

/--
info: 'Tacenta.UnitLifecycleSessionCodec.efs_val' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleSessionCodec.efs_val

/--
info: 'Tacenta.UnitLifecycleSessionCodec.be32_length' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleSessionCodec.be32_length

/--
info: 'Tacenta.UnitLifecycleSessionCodec.be64_length' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleSessionCodec.be64_length

/--
info: 'Tacenta.UnitLifecycleSessionCodec.fromBEBytes_toNat_congr' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleSessionCodec.fromBEBytes_toNat_congr

/--
info: 'Tacenta.UnitLifecycleSessionCodec.fromLEBytes_toNat_congr' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleSessionCodec.fromLEBytes_toNat_congr

/--
info: 'Tacenta.UnitLifecycleSessionCodec.fromBEBytes_toBEBytes_toNat' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleSessionCodec.fromBEBytes_toBEBytes_toNat

/--
info: 'Tacenta.UnitLifecycleSessionCodec.from_be32' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleSessionCodec.from_be32

/--
info: 'Tacenta.UnitLifecycleSessionCodec.drop_next' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleSessionCodec.drop_next

/--
info: 'Tacenta.UnitLifecycleSessionCodec.slice_of_drop' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleSessionCodec.slice_of_drop

/--
info: 'Tacenta.UnitLifecycleSessionCodec.length_of_drop' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleSessionCodec.length_of_drop

/--
info: 'Tacenta.UnitLifecycleSessionCodec.getElem_of_drop' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleSessionCodec.getElem_of_drop

/--
info: 'Tacenta.UnitLifecycleSessionCodec.from_slice_eq' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleSessionCodec.from_slice_eq

/--
info: 'Tacenta.UnitLifecycleSessionCodec.index_usize_of' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleSessionCodec.index_usize_of

/--
info: 'Tacenta.UnitLifecycleSessionCodec.read_key_of' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleSessionCodec.read_key_of

/--
info: 'Tacenta.UnitLifecycleSessionCodec.read_u32_of' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleSessionCodec.read_u32_of

/--
info: 'Tacenta.UnitLifecycleSessionCodec.read_optional_key_loop_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleSessionCodec.read_optional_key_loop_zero

/--
info: 'Tacenta.UnitLifecycleSessionCodec.read_optional_key_of' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleSessionCodec.read_optional_key_of

/--
info: 'Tacenta.UnitLifecycleSessionCodec.usize_add_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleSessionCodec.usize_add_eq

/--
info: 'Tacenta.UnitLifecycleSessionCodec.usize_div_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleSessionCodec.usize_div_eq

/--
info: 'Tacenta.UnitLifecycleSessionCodec.slice_len_eq' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleSessionCodec.slice_len_eq

/--
info: 'Tacenta.UnitLifecycleSessionCodec.arr32_len' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleSessionCodec.arr32_len

/--
info: 'Tacenta.UnitLifecycleSessionCodec.optKeyEnc_length' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleSessionCodec.optKeyEnc_length

/--
info: 'Tacenta.UnitLifecycleSessionCodec.ratchetEnc_length' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleSessionCodec.ratchetEnc_length

/--
info: 'Tacenta.UnitLifecycleSessionCodec.push_optional_key_enc' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleSessionCodec.push_optional_key_enc

/--
info: 'Tacenta.UnitLifecycleSessionCodec.ratchet_to_bytes_loop_empty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleSessionCodec.ratchet_to_bytes_loop_empty

/--
info: 'Tacenta.UnitLifecycleSessionCodec.ratchet_to_bytes_loop_empty_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleSessionCodec.ratchet_to_bytes_loop_empty_spec

/--
info: 'Tacenta.UnitLifecycleSessionCodec.label_to_byte_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleSessionCodec.label_to_byte_spec

/--
info: 'Tacenta.UnitLifecycleSessionCodec.zeroizing_new_spec' depends on axioms: [propext,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.zeroize.Zeroizing.new,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleSessionCodec.zeroizing_new_spec

/--
info: 'Tacenta.UnitLifecycleSessionCodec.ratchet_to_bytes_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.zeroize.Zeroizing.new,
 tacenta_session_unit.zeroize.Zeroize.Blanket.zeroize,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 tacenta_session_unit.alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleSessionCodec.ratchet_to_bytes_spec

/--
info: 'Tacenta.UnitLifecycleSessionCodec.ratchet_from_bytes_of' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleSessionCodec.ratchet_from_bytes_of

/--
info: 'Tacenta.UnitLifecycleSessionCodec.chain_len_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleSessionCodec.chain_len_eq

/--
info: 'Tacenta.UnitLifecycleSessionCodec.chains_len_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleSessionCodec.chains_len_eq

/--
info: 'Tacenta.UnitLifecycleSessionCodec.skipped_len_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleSessionCodec.skipped_len_eq

/--
info: 'Tacenta.UnitLifecycleSessionCodec.fixed_prefix_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleSessionCodec.fixed_prefix_eq

/--
info: 'Tacenta.UnitLifecycleSessionCodec.chainEnc_length' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleSessionCodec.chainEnc_length

/--
info: 'Tacenta.UnitLifecycleSessionCodec.spqrEnc_length' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleSessionCodec.spqrEnc_length

/--
info: 'Tacenta.UnitLifecycleSessionCodec.push_optional_chain_some' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleSessionCodec.push_optional_chain_some

/--
info: 'Tacenta.UnitLifecycleSessionCodec.spqr_to_bytes_loop0_one' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleSessionCodec.spqr_to_bytes_loop0_one

/--
info: 'Tacenta.UnitLifecycleSessionCodec.spqr_to_bytes_loop1_empty' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleSessionCodec.spqr_to_bytes_loop1_empty

/--
info: 'Tacenta.UnitLifecycleSessionCodec.direction_to_byte_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleSessionCodec.direction_to_byte_spec

/--
info: 'Tacenta.UnitLifecycleSessionCodec.spqr_encoded_len_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleSessionCodec.spqr_encoded_len_eq

/--
info: 'Tacenta.UnitLifecycleSessionCodec.spqr_to_bytes_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.zeroize.Zeroizing.new,
 tacenta_session_unit.zeroize.Zeroize.Blanket.zeroize,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 tacenta_session_unit.alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleSessionCodec.spqr_to_bytes_spec

/--
info: 'Tacenta.UnitLifecycleSessionCodec.from_be64' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleSessionCodec.from_be64

/--
info: 'Tacenta.UnitLifecycleSessionCodec.u64_eq_of_bv' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleSessionCodec.u64_eq_of_bv

/--
info: 'Tacenta.UnitLifecycleSessionCodec.u32_eq_of_bv' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleSessionCodec.u32_eq_of_bv

/--
info: 'Tacenta.UnitLifecycleSessionCodec.decode_chain_of' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleSessionCodec.decode_chain_of

/--
info: 'Tacenta.UnitLifecycleSessionCodec.decode_chains_entry_of' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleSessionCodec.decode_chains_entry_of

/--
info: 'Tacenta.UnitLifecycleSessionCodec.spqr_from_bytes_loop0_one' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleSessionCodec.spqr_from_bytes_loop0_one

/--
info: 'Tacenta.UnitLifecycleSessionCodec.spqr_from_bytes_loop1_empty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleSessionCodec.spqr_from_bytes_loop1_empty

/--
info: 'Tacenta.UnitLifecycleSessionCodec.direction_from_byte_dirByte' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleSessionCodec.direction_from_byte_dirByte

/--
info: 'Tacenta.UnitLifecycleSessionCodec.spqr_from_bytes_of' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleSessionCodec.spqr_from_bytes_of

/--
info: 'Tacenta.UnitLifecycleSessionCodec.tripleEnc_length' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleSessionCodec.tripleEnc_length

/--
info: 'Tacenta.UnitLifecycleSessionCodec.triple_to_bytes_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.zeroize.Zeroizing.new,
 tacenta_session_unit.zeroize.Zeroize.Blanket.zeroize,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 tacenta_session_unit.alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleSessionCodec.triple_to_bytes_spec

/--
info: 'Tacenta.UnitLifecycleSessionCodec.triple_take_len_prefixed_of' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleSessionCodec.triple_take_len_prefixed_of

/--
info: 'Tacenta.UnitLifecycleSessionCodec.triple_invariant_parts' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleSessionCodec.triple_invariant_parts

/--
info: 'Tacenta.UnitLifecycleSessionCodec.triple_from_bytes_of' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleSessionCodec.triple_from_bytes_of

/--
info: 'Tacenta.UnitLifecycleSessionCodec.authEnc_length' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleSessionCodec.authEnc_length

/--
info: 'Tacenta.UnitLifecycleSessionCodec.setSlice_app' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleSessionCodec.setSlice_app

/--
info: 'Tacenta.UnitLifecycleSessionCodec.auth_to_bytes_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleSessionCodec.auth_to_bytes_spec

/--
info: 'Tacenta.UnitLifecycleSessionCodec.auth_from_bytes_of' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleSessionCodec.auth_from_bytes_of

/--
info: 'Tacenta.UnitLifecycleSessionCodec.head_len_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleSessionCodec.head_len_eq

/--
info: 'Tacenta.UnitLifecycleSessionCodec.epoch_and_auth_len_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleSessionCodec.epoch_and_auth_len_eq

/--
info: 'Tacenta.UnitLifecycleSessionCodec.braidEnc_length' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleSessionCodec.braidEnc_length

/--
info: 'Tacenta.UnitLifecycleSessionCodec.braid_to_bytes_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kem.EncapsState,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.tacenta_kem.EncapsState.to_bytes,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.to_bytes,
 tacenta_session_unit.zeroize.Zeroizing.new,
 tacenta_session_unit.zeroize.Zeroize.Blanket.zeroize,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 tacenta_session_unit.alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleSessionCodec.braid_to_bytes_spec

/--
info: 'Tacenta.UnitLifecycleSessionCodec.read_u64_of' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleSessionCodec.read_u64_of

/--
info: 'Tacenta.UnitLifecycleSessionCodec.read_epoch_of' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleSessionCodec.read_epoch_of

/--
info: 'Tacenta.UnitLifecycleSessionCodec.read_auth_of' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleSessionCodec.read_auth_of

/--
info: 'Tacenta.UnitLifecycleSessionCodec.decode_state_unsampled_of' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kem.EncapsState,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair,
 tacenta_session_unit.tacenta_kem.EncapsState.from_bytes,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.from_bytes,
 tacenta_session_unit.core.num.Usize.div_ceil]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleSessionCodec.decode_state_unsampled_of

/--
info: 'Tacenta.UnitLifecycleSessionCodec.braid_from_bytes_of' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kem.CT1_LEN,
 tacenta_session_unit.tacenta_kem.CT2_LEN,
 tacenta_session_unit.tacenta_kem.EK_VECTOR_LEN,
 tacenta_session_unit.tacenta_kem.EncapsState,
 tacenta_session_unit.tacenta_kem.HEADER_LEN,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair,
 tacenta_session_unit.tacenta_kem.validate_ek,
 tacenta_session_unit.tacenta_kem.EncapsState.from_bytes,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.from_bytes,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.header,
 tacenta_session_unit.core.num.Usize.div_ceil]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleSessionCodec.braid_from_bytes_of

/--
info: 'Tacenta.UnitLifecycleSessionCodec.lifecycle_take_len_prefixed_of' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual,
 tacenta_session_unit.core.option.Option.Insts.CoreOpsTry_traitTry.branch]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleSessionCodec.lifecycle_take_len_prefixed_of

/--
info: 'Tacenta.UnitLifecycleSessionCodec.vecAsSliceImpl_shape' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleSessionCodec.vecAsSliceImpl_shape

/--
info: 'Tacenta.UnitLifecycleSessionCodec.dhPublicBytesRoundTrip_is' depends on axioms: [propext,
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
 tacenta_session_unit.tacenta_kem.encapsulate1,
 tacenta_session_unit.tacenta_kem.encapsulate2,
 tacenta_session_unit.tacenta_kem.validate_ek,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.rand_core_1.error.Error,
 tacenta_session_unit.tacenta_boundary.aead.decrypt,
 tacenta_session_unit.tacenta_boundary.aead.encrypt,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_boundary.dh.is_prime_order_public,
 tacenta_session_unit.tacenta_boundary.kem.KeyPair,
 tacenta_session_unit.tacenta_boundary.kem.decapsulate,
 tacenta_session_unit.tacenta_boundary.kem.encapsulate,
 tacenta_session_unit.tacenta_boundary.xeddsa.verify,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.generate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.header,
 tacenta_session_unit.zeroize.Zeroizing.new,
 tacenta_session_unit.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.Pair.Insts.ZeroizeZeroize.zeroize,
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
#print axioms Tacenta.UnitLifecycleSessionCodec.dhPublicBytesRoundTrip_is

/--
info: 'Tacenta.UnitLifecycleSessionCodec.model_dhPublicBytesRoundTrip' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.rand_core_1.error.Error]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleSessionCodec.model_dhPublicBytesRoundTrip

/--
info: 'Tacenta.UnitLifecycleSessionCodec.dhPrivateBytesRoundTrip_is' depends on axioms: [propext,
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
 tacenta_session_unit.tacenta_kem.encapsulate1,
 tacenta_session_unit.tacenta_kem.encapsulate2,
 tacenta_session_unit.tacenta_kem.validate_ek,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.rand_core_1.error.Error,
 tacenta_session_unit.tacenta_boundary.aead.decrypt,
 tacenta_session_unit.tacenta_boundary.aead.encrypt,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_boundary.dh.is_prime_order_public,
 tacenta_session_unit.tacenta_boundary.kem.KeyPair,
 tacenta_session_unit.tacenta_boundary.kem.decapsulate,
 tacenta_session_unit.tacenta_boundary.kem.encapsulate,
 tacenta_session_unit.tacenta_boundary.xeddsa.verify,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.generate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.header,
 tacenta_session_unit.zeroize.Zeroizing.new,
 tacenta_session_unit.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.Pair.Insts.ZeroizeZeroize.zeroize,
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
#print axioms Tacenta.UnitLifecycleSessionCodec.dhPrivateBytesRoundTrip_is

/--
info: 'Tacenta.UnitLifecycleSessionCodec.model_dhPrivateBytesRoundTrip' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.rand_core_1.error.Error,
 tacenta_session_unit.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.zeroize.Zeroize.Blanket.zeroize]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleSessionCodec.model_dhPrivateBytesRoundTrip

/--
info: 'Tacenta.UnitLifecycleSessionCodec.zeroizingVecRoundTrip_is' depends on axioms: [propext,
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
 tacenta_session_unit.tacenta_kem.encapsulate1,
 tacenta_session_unit.tacenta_kem.encapsulate2,
 tacenta_session_unit.tacenta_kem.validate_ek,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.rand_core_1.error.Error,
 tacenta_session_unit.tacenta_boundary.aead.decrypt,
 tacenta_session_unit.tacenta_boundary.aead.encrypt,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_boundary.dh.is_prime_order_public,
 tacenta_session_unit.tacenta_boundary.kem.KeyPair,
 tacenta_session_unit.tacenta_boundary.kem.decapsulate,
 tacenta_session_unit.tacenta_boundary.kem.encapsulate,
 tacenta_session_unit.tacenta_boundary.xeddsa.verify,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.generate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.header,
 tacenta_session_unit.zeroize.Zeroizing.new,
 tacenta_session_unit.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.Pair.Insts.ZeroizeZeroize.zeroize,
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
#print axioms Tacenta.UnitLifecycleSessionCodec.zeroizingVecRoundTrip_is

/--
info: 'Tacenta.UnitLifecycleSessionCodec.model_zeroizingVecRoundTrip' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.rand_core_1.error.Error]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleSessionCodec.model_zeroizingVecRoundTrip

/--
info: 'Tacenta.UnitLifecycleSessionCodec.cast_len_val' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleSessionCodec.cast_len_val

/--
info: 'Tacenta.UnitLifecycleSessionCodec.lenEnc_length' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleSessionCodec.lenEnc_length

/--
info: 'Tacenta.UnitLifecycleSessionCodec.lifecycle_push_len_prefixed_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleSessionCodec.lifecycle_push_len_prefixed_spec

/--
info: 'Tacenta.UnitLifecycleSessionCodec.pendEnc_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleSessionCodec.pendEnc_length

/--
info: 'Tacenta.UnitLifecycleSessionCodec.pending_to_bytes_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.as_bytes]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleSessionCodec.pending_to_bytes_spec

/--
info: 'Tacenta.UnitLifecycleSessionCodec.pending_from_bytes_of' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.from_bytes,
 tacenta_session_unit.core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual,
 tacenta_session_unit.core.option.Option.Insts.CoreOpsTry_traitTry.branch]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleSessionCodec.pending_from_bytes_of

/--
info: Tacenta.UnitLifecycleSessionCodec.efs_val : ∀ (v : Aeneas.Std.alloc.vec.Vec Aeneas.Std.U8)
  (s : Aeneas.Std.Slice Aeneas.Std.U8),
  (↑v).length + (↑s).length ≤ Aeneas.Std.Usize.max →
    Aeneas.Std.WP.spec (Aeneas.Std.alloc.vec.Vec.extend_from_slice Aeneas.Std.core.clone.CloneU8 v s) fun r =>
      ↑r = ↑v ++ ↑s
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleSessionCodec.efs_val

/--
info: Tacenta.UnitLifecycleSessionCodec.be32_length : ∀ (x : Aeneas.Std.U32),
  (Tacenta.UnitLifecycleSessionCodec.be32 x).length = 4
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleSessionCodec.be32_length

/--
info: Tacenta.UnitLifecycleSessionCodec.be64_length : ∀ (x : Aeneas.Std.U64),
  (Tacenta.UnitLifecycleSessionCodec.be64 x).length = 8
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleSessionCodec.be64_length

/--
info: @Tacenta.UnitLifecycleSessionCodec.fromBEBytes_toNat_congr : ∀ {l1 l2 : List Byte},
  l1 = l2 → (BitVec.fromBEBytes l1).toNat = (BitVec.fromBEBytes l2).toNat
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleSessionCodec.fromBEBytes_toNat_congr

/--
info: @Tacenta.UnitLifecycleSessionCodec.fromLEBytes_toNat_congr : ∀ {l1 l2 : List Byte},
  l1 = l2 → (BitVec.fromLEBytes l1).toNat = (BitVec.fromLEBytes l2).toNat
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleSessionCodec.fromLEBytes_toNat_congr

/--
info: @Tacenta.UnitLifecycleSessionCodec.fromBEBytes_toBEBytes_toNat : ∀ {w : ℕ},
  w % 8 = 0 → ∀ (b : BitVec w), (BitVec.fromBEBytes b.toBEBytes).toNat = b.toNat
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleSessionCodec.fromBEBytes_toBEBytes_toNat

/--
info: Tacenta.UnitLifecycleSessionCodec.from_be32 : ∀ (x : Aeneas.Std.U32) (a : Aeneas.Std.Array Aeneas.Std.U8 4#usize),
  ↑a = Tacenta.UnitLifecycleSessionCodec.be32 x → Aeneas.Std.core.num.U32.from_be_bytes a = x
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleSessionCodec.from_be32

/--
info: @Tacenta.UnitLifecycleSessionCodec.drop_next : ∀ {α : Type} {L seg rest : List α} {p : ℕ},
  List.drop p L = seg ++ rest → List.drop (p + seg.length) L = rest
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleSessionCodec.drop_next

/--
info: @Tacenta.UnitLifecycleSessionCodec.slice_of_drop : ∀ {α : Type} {L seg rest : List α} {p e : ℕ},
  List.drop p L = seg ++ rest → e = p + seg.length → List.slice p e L = seg
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleSessionCodec.slice_of_drop

/--
info: @Tacenta.UnitLifecycleSessionCodec.length_of_drop : ∀ {α : Type} {L seg rest : List α} {p : ℕ},
  List.drop p L = seg ++ rest → 0 < seg.length → p + seg.length ≤ L.length
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleSessionCodec.length_of_drop

/--
info: @Tacenta.UnitLifecycleSessionCodec.getElem_of_drop : ∀ {α : Type} {L rest : List α} {x : α} {p : ℕ},
  List.drop p L = x :: rest → L[p]? = some x
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleSessionCodec.getElem_of_drop

/--
info: @Tacenta.UnitLifecycleSessionCodec.from_slice_eq : ∀ {N : Aeneas.Std.Usize} (a : Aeneas.Std.Array Aeneas.Std.U8 N)
  (s : Aeneas.Std.Slice Aeneas.Std.U8) (k : Aeneas.Std.Array Aeneas.Std.U8 N), ↑s = ↑k → a.from_slice s = k
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleSessionCodec.from_slice_eq

/--
info: Tacenta.UnitLifecycleSessionCodec.index_usize_of : ∀ (bytes : Aeneas.Std.Slice Aeneas.Std.U8) (pos : Aeneas.Std.Usize)
  (x : Aeneas.Std.U8) (rest : List Aeneas.Std.U8),
  List.drop ↑pos ↑bytes = x :: rest → bytes.index_usize pos = Aeneas.Std.Result.ok x
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleSessionCodec.index_usize_of

/--
info: Tacenta.UnitLifecycleSessionCodec.read_key_of : ∀ (bytes : Aeneas.Std.Slice Aeneas.Std.U8) (pos : Aeneas.Std.Usize)
  (k : Aeneas.Std.Array Aeneas.Std.U8 32#usize) (rest : List Aeneas.Std.U8),
  List.drop ↑pos ↑bytes = ↑k ++ rest → tacenta_session_unit.tacenta_ratchet.read_key bytes pos = Aeneas.Std.Result.ok k
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleSessionCodec.read_key_of

/--
info: Tacenta.UnitLifecycleSessionCodec.read_u32_of : ∀ (bytes : Aeneas.Std.Slice Aeneas.Std.U8) (pos : Aeneas.Std.Usize)
  (x : Aeneas.Std.U32) (rest : List Aeneas.Std.U8),
  List.drop ↑pos ↑bytes = Tacenta.UnitLifecycleSessionCodec.be32 x ++ rest →
    tacenta_session_unit.tacenta_ratchet.read_u32 bytes pos = Aeneas.Std.Result.ok x
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleSessionCodec.read_u32_of

/--
info: Tacenta.UnitLifecycleSessionCodec.read_optional_key_loop_zero : ∀ (bytes : Aeneas.Std.Slice Aeneas.Std.U8)
  (pos i : Aeneas.Std.Usize),
  ↑i ≤ ↑pos + 33 →
    ↑pos + 33 ≤ bytes.length →
      (∀ (j : ℕ), ↑i ≤ j → j < ↑pos + 33 → (↑bytes)[j]? = some 0#u8) →
        Aeneas.Std.WP.spec (tacenta_session_unit.tacenta_ratchet.read_optional_key_loop bytes pos true i) fun c =>
          c = true
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleSessionCodec.read_optional_key_loop_zero

/--
info: Tacenta.UnitLifecycleSessionCodec.read_optional_key_of : ∀ (bytes : Aeneas.Std.Slice Aeneas.Std.U8)
  (pos : Aeneas.Std.Usize) (o : Option (Aeneas.Std.Array Aeneas.Std.U8 32#usize)) (rest : List Aeneas.Std.U8),
  List.drop ↑pos ↑bytes = Tacenta.UnitLifecycleSessionCodec.optKeyEnc o ++ rest →
    tacenta_session_unit.tacenta_ratchet.read_optional_key bytes pos =
      Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok o)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleSessionCodec.read_optional_key_of

/--
info: Tacenta.UnitLifecycleSessionCodec.usize_add_eq : ∀ (a b c : Aeneas.Std.Usize),
  ↑a + ↑b = ↑c → a + b = Aeneas.Std.Result.ok c
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleSessionCodec.usize_add_eq

/--
info: Tacenta.UnitLifecycleSessionCodec.usize_div_eq : ∀ (a b c : Aeneas.Std.Usize),
  ↑b ≠ 0 → ↑a / ↑b = ↑c → a / b = Aeneas.Std.Result.ok c
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleSessionCodec.usize_div_eq

/--
info: Tacenta.UnitLifecycleSessionCodec.slice_len_eq : ∀ (bytes : Aeneas.Std.Slice Aeneas.Std.U8) (n : Aeneas.Std.Usize),
  (↑bytes).length = ↑n → bytes.len = n
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleSessionCodec.slice_len_eq

/--
info: Tacenta.UnitLifecycleSessionCodec.arr32_len : ∀ (a : Aeneas.Std.Array Aeneas.Std.U8 32#usize), (↑a).length = 32
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleSessionCodec.arr32_len

/--
info: Tacenta.UnitLifecycleSessionCodec.optKeyEnc_length : ∀ (o : Option (Aeneas.Std.Array Aeneas.Std.U8 32#usize)),
  (Tacenta.UnitLifecycleSessionCodec.optKeyEnc o).length = 33
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleSessionCodec.optKeyEnc_length

/--
info: Tacenta.UnitLifecycleSessionCodec.ratchetEnc_length : ∀ (r : tacenta_session_unit.tacenta_ratchet.State),
  (Tacenta.UnitLifecycleSessionCodec.ratchetEnc r).length = 185
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleSessionCodec.ratchetEnc_length

/--
info: Tacenta.UnitLifecycleSessionCodec.push_optional_key_enc : ∀ (out : Aeneas.Std.alloc.vec.Vec Aeneas.Std.U8)
  (k : Option (Aeneas.Std.Array Aeneas.Std.U8 32#usize)),
  (↑out).length + 33 ≤ Aeneas.Std.Usize.max →
    Aeneas.Std.WP.spec (tacenta_session_unit.tacenta_ratchet.push_optional_key out k) fun w =>
      ↑w = ↑out ++ Tacenta.UnitLifecycleSessionCodec.optKeyEnc k
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleSessionCodec.push_optional_key_enc

/--
info: Tacenta.UnitLifecycleSessionCodec.ratchet_to_bytes_loop_empty : ∀
  (v : Aeneas.Std.alloc.vec.Vec tacenta_session_unit.tacenta_ratchet.SkippedKey)
  (out : Aeneas.Std.alloc.vec.Vec Aeneas.Std.U8),
  ↑v = [] → tacenta_session_unit.tacenta_ratchet.State.to_bytes_loop v out 0#usize = Aeneas.Std.Result.ok out
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleSessionCodec.ratchet_to_bytes_loop_empty

/--
info: Tacenta.UnitLifecycleSessionCodec.ratchet_to_bytes_loop_empty_spec : ∀
  (v : Aeneas.Std.alloc.vec.Vec tacenta_session_unit.tacenta_ratchet.SkippedKey)
  (out : Aeneas.Std.alloc.vec.Vec Aeneas.Std.U8),
  ↑v = [] → Aeneas.Std.WP.spec (tacenta_session_unit.tacenta_ratchet.State.to_bytes_loop v out 0#usize) fun w => w = out
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleSessionCodec.ratchet_to_bytes_loop_empty_spec

/--
info: Tacenta.UnitLifecycleSessionCodec.label_to_byte_spec : ∀ (l : tacenta_session_unit.tacenta_ratchet.LabelSet),
  Aeneas.Std.WP.spec l.to_byte fun b => b = 0#u8
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleSessionCodec.label_to_byte_spec

/--
info: Tacenta.UnitLifecycleSessionCodec.zeroizing_new_spec : Tacenta.UnitLifecycleSessionCodec.ZeroizingVecRoundTrip →
  ∀ (inst : tacenta_session_unit.zeroize.Zeroize (Aeneas.Std.alloc.vec.Vec Aeneas.Std.U8))
    (v : Aeneas.Std.alloc.vec.Vec Aeneas.Std.U8),
    Aeneas.Std.WP.spec (tacenta_session_unit.zeroize.Zeroizing.new inst v) fun z =>
      tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref inst z = Aeneas.Std.Result.ok v
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleSessionCodec.zeroizing_new_spec

/--
info: Tacenta.UnitLifecycleSessionCodec.ratchet_to_bytes_spec : Tacenta.UnitLifecycleSessionCodec.ZeroizingVecRoundTrip →
  ∀ (r : tacenta_session_unit.tacenta_ratchet.State),
    ↑r.skipped = [] →
      Aeneas.Std.WP.spec r.to_bytes fun z =>
        ∃ v,
          tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref Tacenta.UnitLifecycleSessionCodec.vecInst
                z =
              Aeneas.Std.Result.ok v ∧
            ↑v = Tacenta.UnitLifecycleSessionCodec.ratchetEnc r
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleSessionCodec.ratchet_to_bytes_spec

/--
info: Tacenta.UnitLifecycleSessionCodec.ratchet_from_bytes_of : ∀ (bytes : Aeneas.Std.Slice Aeneas.Std.U8)
  (r : tacenta_session_unit.tacenta_ratchet.State),
  ↑bytes = Tacenta.UnitLifecycleSessionCodec.ratchetEnc r →
    ↑r.skipped = [] →
      r.invariant = Aeneas.Std.Result.ok true →
        tacenta_session_unit.tacenta_ratchet.State.from_bytes bytes =
          Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok r)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleSessionCodec.ratchet_from_bytes_of

/--
info: Tacenta.UnitLifecycleSessionCodec.chain_len_eq : tacenta_session_unit.tacenta_spqr.CHAIN_LEN =
  Aeneas.Std.Result.ok 41#usize
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleSessionCodec.chain_len_eq

/--
info: Tacenta.UnitLifecycleSessionCodec.chains_len_eq : tacenta_session_unit.tacenta_spqr.CHAINS_LEN =
  Aeneas.Std.Result.ok 90#usize
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleSessionCodec.chains_len_eq

/--
info: Tacenta.UnitLifecycleSessionCodec.skipped_len_eq : tacenta_session_unit.tacenta_spqr.SKIPPED_LEN =
  Aeneas.Std.Result.ok 48#usize
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleSessionCodec.skipped_len_eq

/--
info: Tacenta.UnitLifecycleSessionCodec.fixed_prefix_eq : tacenta_session_unit.tacenta_spqr.FIXED_PREFIX =
  Aeneas.Std.Result.ok 46#usize
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleSessionCodec.fixed_prefix_eq

/--
info: Tacenta.UnitLifecycleSessionCodec.chainEnc_length : ∀ (c : tacenta_session_unit.tacenta_spqr.Chain),
  (Tacenta.UnitLifecycleSessionCodec.chainEnc c).length = 41
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleSessionCodec.chainEnc_length

/--
info: Tacenta.UnitLifecycleSessionCodec.spqrEnc_length : ∀ (q : tacenta_session_unit.tacenta_spqr.State) (e : Aeneas.Std.U64)
  (c1 c2 : tacenta_session_unit.tacenta_spqr.Chain), (Tacenta.UnitLifecycleSessionCodec.spqrEnc q e c1 c2).length = 140
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleSessionCodec.spqrEnc_length

/--
info: Tacenta.UnitLifecycleSessionCodec.push_optional_chain_some : ∀ (out : Aeneas.Std.alloc.vec.Vec Aeneas.Std.U8)
  (c : tacenta_session_unit.tacenta_spqr.Chain),
  (↑out).length + 41 ≤ Aeneas.Std.Usize.max →
    Aeneas.Std.WP.spec (tacenta_session_unit.tacenta_spqr.push_optional_chain out (some c)) fun w =>
      ↑w = ↑out ++ Tacenta.UnitLifecycleSessionCodec.chainEnc c
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleSessionCodec.push_optional_chain_some

/--
info: Tacenta.UnitLifecycleSessionCodec.spqr_to_bytes_loop0_one : ∀
  (v : Aeneas.Std.alloc.vec.Vec (Aeneas.Std.U64 × tacenta_session_unit.tacenta_spqr.Chains))
  (out : Aeneas.Std.alloc.vec.Vec Aeneas.Std.U8) (e : Aeneas.Std.U64) (c1 c2 : tacenta_session_unit.tacenta_spqr.Chain),
  ↑v = [(e, { send := some c1, receive := some c2 })] →
    (↑out).length + 90 ≤ Aeneas.Std.Usize.max →
      Aeneas.Std.WP.spec (tacenta_session_unit.tacenta_spqr.State.to_bytes_loop0 v out 0#usize) fun w =>
        ↑w =
          ↑out ++
            (Tacenta.UnitLifecycleSessionCodec.be64 e ++
              (Tacenta.UnitLifecycleSessionCodec.chainEnc c1 ++ Tacenta.UnitLifecycleSessionCodec.chainEnc c2))
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleSessionCodec.spqr_to_bytes_loop0_one

/--
info: Tacenta.UnitLifecycleSessionCodec.spqr_to_bytes_loop1_empty : ∀
  (v : Aeneas.Std.alloc.vec.Vec tacenta_session_unit.tacenta_spqr.Skipped)
  (out : Aeneas.Std.alloc.vec.Vec Aeneas.Std.U8),
  ↑v = [] → Aeneas.Std.WP.spec (tacenta_session_unit.tacenta_spqr.State.to_bytes_loop1 v out 0#usize) fun w => w = out
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleSessionCodec.spqr_to_bytes_loop1_empty

/--
info: Tacenta.UnitLifecycleSessionCodec.direction_to_byte_spec : ∀ (d : tacenta_session_unit.tacenta_spqr.Direction),
  Aeneas.Std.WP.spec d.to_byte fun b => b = Tacenta.UnitLifecycleSessionCodec.dirByte d
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleSessionCodec.direction_to_byte_spec

/--
info: Tacenta.UnitLifecycleSessionCodec.spqr_encoded_len_eq : ∀ (q : tacenta_session_unit.tacenta_spqr.State),
  (↑q.chains).length = 1 → ↑q.skipped = [] → q.encoded_len = Aeneas.Std.Result.ok 140#usize
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleSessionCodec.spqr_encoded_len_eq

/--
info: Tacenta.UnitLifecycleSessionCodec.spqr_to_bytes_spec : Tacenta.UnitLifecycleSessionCodec.ZeroizingVecRoundTrip →
  ∀ (q : tacenta_session_unit.tacenta_spqr.State) (e : Aeneas.Std.U64)
    (c1 c2 : tacenta_session_unit.tacenta_spqr.Chain),
    ↑q.chains = [(e, { send := some c1, receive := some c2 })] →
      ↑q.skipped = [] →
        Aeneas.Std.WP.spec q.to_bytes fun z =>
          ∃ v,
            tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref
                  Tacenta.UnitLifecycleSessionCodec.vecInst z =
                Aeneas.Std.Result.ok v ∧
              ↑v = Tacenta.UnitLifecycleSessionCodec.spqrEnc q e c1 c2
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleSessionCodec.spqr_to_bytes_spec

/--
info: Tacenta.UnitLifecycleSessionCodec.from_be64 : ∀ (x : Aeneas.Std.U64) (a : Aeneas.Std.Array Aeneas.Std.U8 8#usize),
  ↑a = Tacenta.UnitLifecycleSessionCodec.be64 x → Aeneas.Std.core.num.U64.from_be_bytes a = x
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleSessionCodec.from_be64

/--
info: Tacenta.UnitLifecycleSessionCodec.u64_eq_of_bv : ∀ (i x : Aeneas.Std.U64) (a : Aeneas.Std.Array Aeneas.Std.U8 8#usize),
  i.bv = (Aeneas.Std.core.num.U64.from_be_bytes a).bv → ↑a = Tacenta.UnitLifecycleSessionCodec.be64 x → i = x
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleSessionCodec.u64_eq_of_bv

/--
info: Tacenta.UnitLifecycleSessionCodec.u32_eq_of_bv : ∀ (i x : Aeneas.Std.U32) (a : Aeneas.Std.Array Aeneas.Std.U8 4#usize),
  i.bv = (Aeneas.Std.core.num.U32.from_be_bytes a).bv → ↑a = Tacenta.UnitLifecycleSessionCodec.be32 x → i = x
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleSessionCodec.u32_eq_of_bv

/--
info: Tacenta.UnitLifecycleSessionCodec.decode_chain_of : ∀ (bytes : Aeneas.Std.Slice Aeneas.Std.U8) (pos : Aeneas.Std.Usize)
  (c : tacenta_session_unit.tacenta_spqr.Chain) (rest : List Aeneas.Std.U8),
  List.drop ↑pos ↑bytes = Tacenta.UnitLifecycleSessionCodec.chainEnc c ++ rest →
    tacenta_session_unit.tacenta_spqr.decode_chain bytes pos = Aeneas.Std.Result.ok (some (some c))
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleSessionCodec.decode_chain_of

/--
info: Tacenta.UnitLifecycleSessionCodec.decode_chains_entry_of : ∀ (bytes : Aeneas.Std.Slice Aeneas.Std.U8)
  (pos : Aeneas.Std.Usize) (e : Aeneas.Std.U64) (c1 c2 : tacenta_session_unit.tacenta_spqr.Chain)
  (rest : List Aeneas.Std.U8),
  List.drop ↑pos ↑bytes =
      Tacenta.UnitLifecycleSessionCodec.be64 e ++
        (Tacenta.UnitLifecycleSessionCodec.chainEnc c1 ++ (Tacenta.UnitLifecycleSessionCodec.chainEnc c2 ++ rest)) →
    tacenta_session_unit.tacenta_spqr.decode_chains_entry bytes pos =
      Aeneas.Std.Result.ok (some (e, { send := some c1, receive := some c2 }))
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleSessionCodec.decode_chains_entry_of

/--
info: Tacenta.UnitLifecycleSessionCodec.spqr_from_bytes_loop0_one : ∀ (bytes : Aeneas.Std.Slice Aeneas.Std.U8)
  (pos : Aeneas.Std.Usize) (e : Aeneas.Std.U64) (c1 c2 : tacenta_session_unit.tacenta_spqr.Chain)
  (rest : List Aeneas.Std.U8),
  List.drop ↑pos ↑bytes =
      Tacenta.UnitLifecycleSessionCodec.be64 e ++
        (Tacenta.UnitLifecycleSessionCodec.chainEnc c1 ++ (Tacenta.UnitLifecycleSessionCodec.chainEnc c2 ++ rest)) →
    ∀ (v : Aeneas.Std.alloc.vec.Vec (Aeneas.Std.U64 × tacenta_session_unit.tacenta_spqr.Chains)),
      ↑v = [] →
        Aeneas.Std.WP.spec
          (tacenta_session_unit.tacenta_spqr.State.from_bytes_loop0 90#usize { start := 0#usize, «end» := 1#usize }
            bytes pos v true)
          fun r => ↑r.1 = ↑pos + 90 ∧ ↑r.2.1 = [(e, { send := some c1, receive := some c2 })] ∧ r.2.2 = true
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleSessionCodec.spqr_from_bytes_loop0_one

/--
info: Tacenta.UnitLifecycleSessionCodec.spqr_from_bytes_loop1_empty : ∀ (bytes : Aeneas.Std.Slice Aeneas.Std.U8)
  (pos : Aeneas.Std.Usize) (v : Aeneas.Std.alloc.vec.Vec tacenta_session_unit.tacenta_spqr.Skipped) (b : Bool),
  Aeneas.Std.WP.spec
    (tacenta_session_unit.tacenta_spqr.State.from_bytes_loop1 48#usize { start := 0#usize, «end» := 0#usize } bytes pos
      v b)
    fun r => r = (pos, v, b)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleSessionCodec.spqr_from_bytes_loop1_empty

/--
info: Tacenta.UnitLifecycleSessionCodec.direction_from_byte_dirByte : ∀ (d : tacenta_session_unit.tacenta_spqr.Direction),
  tacenta_session_unit.tacenta_spqr.Direction.from_byte (Tacenta.UnitLifecycleSessionCodec.dirByte d) =
    Aeneas.Std.Result.ok (some d)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleSessionCodec.direction_from_byte_dirByte

/--
info: Tacenta.UnitLifecycleSessionCodec.spqr_from_bytes_of : ∀ (bytes : Aeneas.Std.Slice Aeneas.Std.U8)
  (q : tacenta_session_unit.tacenta_spqr.State) (e : Aeneas.Std.U64) (c1 c2 : tacenta_session_unit.tacenta_spqr.Chain),
  ↑bytes = Tacenta.UnitLifecycleSessionCodec.spqrEnc q e c1 c2 →
    ↑q.chains = [(e, { send := some c1, receive := some c2 })] →
      ↑q.skipped = [] →
        q.invariant = Aeneas.Std.Result.ok true →
          tacenta_session_unit.tacenta_spqr.State.from_bytes bytes =
            Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok q)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleSessionCodec.spqr_from_bytes_of

/--
info: Tacenta.UnitLifecycleSessionCodec.tripleEnc_length : ∀ (t : tacenta_session_unit.tacenta_triple.State)
  (e : Aeneas.Std.U64) (c1 c2 : tacenta_session_unit.tacenta_spqr.Chain),
  (Tacenta.UnitLifecycleSessionCodec.tripleEnc t e c1 c2).length = 334
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleSessionCodec.tripleEnc_length

/--
info: Tacenta.UnitLifecycleSessionCodec.triple_to_bytes_spec : Tacenta.UnitLifecycleSessionCodec.ZeroizingVecRoundTrip →
  ∀ (t : tacenta_session_unit.tacenta_triple.State) (e : Aeneas.Std.U64)
    (c1 c2 : tacenta_session_unit.tacenta_spqr.Chain),
    ↑t.classical.skipped = [] →
      ↑t.post_quantum.chains = [(e, { send := some c1, receive := some c2 })] →
        ↑t.post_quantum.skipped = [] →
          Aeneas.Std.WP.spec t.to_bytes fun z =>
            ∃ v,
              tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref
                    Tacenta.UnitLifecycleSessionCodec.vecInst z =
                  Aeneas.Std.Result.ok v ∧
                ↑v = Tacenta.UnitLifecycleSessionCodec.tripleEnc t e c1 c2
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleSessionCodec.triple_to_bytes_spec

/--
info: Tacenta.UnitLifecycleSessionCodec.triple_take_len_prefixed_of : ∀ (bytes : Aeneas.Std.Slice Aeneas.Std.U8)
  (pos : Aeneas.Std.Usize) (n : Aeneas.Std.U32) (payload rest : List Aeneas.Std.U8),
  ↑n = payload.length →
    List.drop ↑pos ↑bytes = Tacenta.UnitLifecycleSessionCodec.be32 n ++ (payload ++ rest) →
      Aeneas.Std.WP.spec (tacenta_session_unit.tacenta_triple.take_len_prefixed bytes pos) fun r =>
        ∃ sl p', r = some (sl, p') ∧ ↑sl = payload ∧ ↑p' = ↑pos + 4 + payload.length
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleSessionCodec.triple_take_len_prefixed_of

/--
info: Tacenta.UnitLifecycleSessionCodec.triple_invariant_parts : ∀ (t : tacenta_session_unit.tacenta_triple.State),
  t.invariant = Aeneas.Std.Result.ok true →
    t.classical.invariant = Aeneas.Std.Result.ok true ∧ t.post_quantum.invariant = Aeneas.Std.Result.ok true
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleSessionCodec.triple_invariant_parts

/--
info: Tacenta.UnitLifecycleSessionCodec.triple_from_bytes_of : ∀ (bytes : Aeneas.Std.Slice Aeneas.Std.U8)
  (t : tacenta_session_unit.tacenta_triple.State) (e : Aeneas.Std.U64)
  (c1 c2 : tacenta_session_unit.tacenta_spqr.Chain),
  ↑bytes = Tacenta.UnitLifecycleSessionCodec.tripleEnc t e c1 c2 →
    ↑t.classical.skipped = [] →
      ↑t.post_quantum.chains = [(e, { send := some c1, receive := some c2 })] →
        ↑t.post_quantum.skipped = [] →
          t.invariant = Aeneas.Std.Result.ok true →
            tacenta_session_unit.tacenta_triple.State.from_bytes bytes =
              Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok t)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleSessionCodec.triple_from_bytes_of

/--
info: Tacenta.UnitLifecycleSessionCodec.authEnc_length : ∀ (a : tacenta_session_unit.tacenta_braid.Auth),
  (Tacenta.UnitLifecycleSessionCodec.authEnc a).length = 64
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleSessionCodec.authEnc_length

/--
info: @Tacenta.UnitLifecycleSessionCodec.setSlice_app : ∀ {α : Type} (pre mid post s' : List α),
  s'.length = mid.length → (pre ++ mid ++ post).setSlice! pre.length s' = pre ++ s' ++ post
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleSessionCodec.setSlice_app

/--
info: Tacenta.UnitLifecycleSessionCodec.auth_to_bytes_spec : ∀ (a : tacenta_session_unit.tacenta_braid.Auth),
  Aeneas.Std.WP.spec a.to_bytes fun r => ↑r = Tacenta.UnitLifecycleSessionCodec.authEnc a
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleSessionCodec.auth_to_bytes_spec

/--
info: Tacenta.UnitLifecycleSessionCodec.auth_from_bytes_of : ∀ (arr : Aeneas.Std.Array Aeneas.Std.U8 64#usize)
  (a : tacenta_session_unit.tacenta_braid.Auth),
  ↑arr = Tacenta.UnitLifecycleSessionCodec.authEnc a →
    tacenta_session_unit.tacenta_braid.Auth.from_bytes arr = Aeneas.Std.Result.ok a
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleSessionCodec.auth_from_bytes_of

/--
info: Tacenta.UnitLifecycleSessionCodec.head_len_eq : tacenta_session_unit.tacenta_braid.HEAD_LEN =
  Aeneas.Std.Result.ok 2#usize
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleSessionCodec.head_len_eq

/--
info: Tacenta.UnitLifecycleSessionCodec.epoch_and_auth_len_eq : tacenta_session_unit.tacenta_braid.EPOCH_AND_AUTH_LEN =
  Aeneas.Std.Result.ok 72#usize
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleSessionCodec.epoch_and_auth_len_eq

/--
info: Tacenta.UnitLifecycleSessionCodec.braidEnc_length : ∀ (epoch : Aeneas.Std.U64)
  (auth : tacenta_session_unit.tacenta_braid.Auth), (Tacenta.UnitLifecycleSessionCodec.braidEnc epoch auth).length = 74
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleSessionCodec.braidEnc_length

/--
info: Tacenta.UnitLifecycleSessionCodec.braid_to_bytes_spec : Tacenta.UnitLifecycleSessionCodec.ZeroizingVecRoundTrip →
  ∀ (epoch : Aeneas.Std.U64) (auth : tacenta_session_unit.tacenta_braid.Auth),
    Aeneas.Std.WP.spec { state := tacenta_session_unit.tacenta_braid.State.KeysUnsampled epoch auth }.to_bytes fun z =>
      ∃ v,
        tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref Tacenta.UnitLifecycleSessionCodec.vecInst
              z =
            Aeneas.Std.Result.ok v ∧
          ↑v = Tacenta.UnitLifecycleSessionCodec.braidEnc epoch auth
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleSessionCodec.braid_to_bytes_spec

/--
info: Tacenta.UnitLifecycleSessionCodec.read_u64_of : ∀ (bytes : Aeneas.Std.Slice Aeneas.Std.U8) (pos : Aeneas.Std.Usize)
  (x : Aeneas.Std.U64) (rest : List Aeneas.Std.U8),
  List.drop ↑pos ↑bytes = Tacenta.UnitLifecycleSessionCodec.be64 x ++ rest →
    tacenta_session_unit.tacenta_braid.read_u64 bytes pos = Aeneas.Std.Result.ok (some x)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleSessionCodec.read_u64_of

/--
info: Tacenta.UnitLifecycleSessionCodec.read_epoch_of : ∀ (bytes : Aeneas.Std.Slice Aeneas.Std.U8) (pos : Aeneas.Std.Usize)
  (epoch : Aeneas.Std.U64) (rest : List Aeneas.Std.U8),
  List.drop ↑pos ↑bytes = Tacenta.UnitLifecycleSessionCodec.be64 epoch ++ rest →
    epoch ≠ Aeneas.Std.core.num.U64.MAX →
      tacenta_session_unit.tacenta_braid.read_epoch bytes pos = Aeneas.Std.Result.ok (some epoch)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleSessionCodec.read_epoch_of

/--
info: Tacenta.UnitLifecycleSessionCodec.read_auth_of : ∀ (bytes : Aeneas.Std.Slice Aeneas.Std.U8) (pos : Aeneas.Std.Usize)
  (a : tacenta_session_unit.tacenta_braid.Auth) (rest : List Aeneas.Std.U8),
  List.drop ↑pos ↑bytes = Tacenta.UnitLifecycleSessionCodec.authEnc a ++ rest →
    Aeneas.Std.WP.spec (tacenta_session_unit.tacenta_braid.read_auth bytes pos) fun r =>
      ∃ p, r = some (a, p) ∧ ↑p = ↑pos + 64
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleSessionCodec.read_auth_of

/--
info: Tacenta.UnitLifecycleSessionCodec.decode_state_unsampled_of : ∀ (bytes : Aeneas.Std.Slice Aeneas.Std.U8)
  (pos : Aeneas.Std.Usize) (epoch : Aeneas.Std.U64) (auth : tacenta_session_unit.tacenta_braid.Auth)
  (rest : List Aeneas.Std.U8),
  List.drop ↑pos ↑bytes =
      Tacenta.UnitLifecycleSessionCodec.be64 epoch ++ (Tacenta.UnitLifecycleSessionCodec.authEnc auth ++ rest) →
    epoch ≠ Aeneas.Std.core.num.U64.MAX →
      Aeneas.Std.WP.spec (tacenta_session_unit.tacenta_braid.decode_state 0#u8 bytes pos) fun r =>
        ∃ p, r = some (tacenta_session_unit.tacenta_braid.State.KeysUnsampled epoch auth, p) ∧ ↑p = ↑pos + 72
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleSessionCodec.decode_state_unsampled_of

/--
info: Tacenta.UnitLifecycleSessionCodec.braid_from_bytes_of : ∀ (bytes : Aeneas.Std.Slice Aeneas.Std.U8)
  (epoch : Aeneas.Std.U64) (auth : tacenta_session_unit.tacenta_braid.Auth),
  ↑bytes = Tacenta.UnitLifecycleSessionCodec.braidEnc epoch auth →
    epoch ≠ Aeneas.Std.core.num.U64.MAX →
      { state := tacenta_session_unit.tacenta_braid.State.KeysUnsampled epoch auth }.invariant =
          Aeneas.Std.Result.ok true →
        tacenta_session_unit.tacenta_braid.Braid.from_bytes bytes =
          Aeneas.Std.Result.ok
            (Aeneas.Std.core.result.Result.Ok
              { state := tacenta_session_unit.tacenta_braid.State.KeysUnsampled epoch auth })
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleSessionCodec.braid_from_bytes_of

/--
info: Tacenta.UnitLifecycleSessionCodec.lifecycle_take_len_prefixed_of : Tacenta.UnitLifecycleSessionCodec.OptionBranchSome →
  ∀ (bytes : Aeneas.Std.Slice Aeneas.Std.U8) (pos : Aeneas.Std.Usize) (n : Aeneas.Std.U32)
    (payload rest : List Aeneas.Std.U8),
    ↑n = payload.length →
      List.drop ↑pos ↑bytes = Tacenta.UnitLifecycleSessionCodec.be32 n ++ (payload ++ rest) →
        Aeneas.Std.WP.spec (tacenta_session_unit.lifecycle.take_len_prefixed bytes pos) fun r =>
          ∃ sl p', r = some (sl, p') ∧ ↑sl = payload ∧ ↑p' = ↑pos + 4 + payload.length
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleSessionCodec.lifecycle_take_len_prefixed_of

/--
info: Tacenta.UnitLifecycleSessionCodec.vecAsSliceImpl_shape : Tacenta.UnitLifecycleSessionCodec.VecAsSliceShape
  @Tacenta.UnitLifecycleSessionCodec.vecAsSliceImpl
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleSessionCodec.vecAsSliceImpl_shape

/--
info: Tacenta.UnitLifecycleSessionCodec.dhPublicBytesRoundTrip_is : Tacenta.UnitLifecycleSessionCodec.DhPublicBytesRoundTrip ↔
  ∀ (pk : tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes),
    ∃ a,
      pk.as_bytes = Aeneas.Std.Result.ok a ∧
        tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.from_bytes a = Aeneas.Std.Result.ok pk
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleSessionCodec.dhPublicBytesRoundTrip_is

/--
info: Tacenta.UnitLifecycleSessionCodec.model_dhPublicBytesRoundTrip : Tacenta.UnitLifecycleSessionCodec.DhPublicBytesRoundTripShape
  Tacenta.UnitSatisfiabilityJoint.Interp.model
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleSessionCodec.model_dhPublicBytesRoundTrip

/--
info: Tacenta.UnitLifecycleSessionCodec.dhPrivateBytesRoundTrip_is : Tacenta.UnitLifecycleSessionCodec.DhPrivateBytesRoundTrip ↔
  ∀ (k : tacenta_session_unit.tacenta_boundary.dh.PrivateKey),
    ∃ z a,
      k.to_bytes = Aeneas.Std.Result.ok z ∧
        tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref Tacenta.UnitLifecycleSessionCodec.arrInst
              z =
            Aeneas.Std.Result.ok a ∧
          tacenta_session_unit.tacenta_boundary.dh.PrivateKey.from_bytes a = Aeneas.Std.Result.ok k
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleSessionCodec.dhPrivateBytesRoundTrip_is

/--
info: Tacenta.UnitLifecycleSessionCodec.model_dhPrivateBytesRoundTrip : Tacenta.UnitLifecycleSessionCodec.DhPrivateBytesRoundTripShape
  Tacenta.UnitSatisfiabilityJoint.Interp.model
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleSessionCodec.model_dhPrivateBytesRoundTrip

/--
info: Tacenta.UnitLifecycleSessionCodec.zeroizingVecRoundTrip_is : Tacenta.UnitLifecycleSessionCodec.ZeroizingVecRoundTrip ↔
  Tacenta.UnitLifecycleSessionCodec.ZeroizingVecRoundTripShape Tacenta.UnitSatisfiabilityJoint.Interp.real
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleSessionCodec.zeroizingVecRoundTrip_is

/--
info: Tacenta.UnitLifecycleSessionCodec.model_zeroizingVecRoundTrip : Tacenta.UnitLifecycleSessionCodec.ZeroizingVecRoundTripShape
  Tacenta.UnitSatisfiabilityJoint.Interp.model
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleSessionCodec.model_zeroizingVecRoundTrip

/--
info: Tacenta.UnitLifecycleSessionCodec.cast_len_val : ∀ (s : Aeneas.Std.Slice Aeneas.Std.U8),
  (↑s).length < 4294967296 → ↑(Aeneas.Std.UScalar.cast Aeneas.Std.UScalarTy.U32 s.len) = (↑s).length
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleSessionCodec.cast_len_val

/--
info: Tacenta.UnitLifecycleSessionCodec.lenEnc_length : ∀ (s : Aeneas.Std.Slice Aeneas.Std.U8),
  (Tacenta.UnitLifecycleSessionCodec.lenEnc s).length = 4 + (↑s).length
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleSessionCodec.lenEnc_length

/--
info: Tacenta.UnitLifecycleSessionCodec.lifecycle_push_len_prefixed_spec : ∀ (out : Aeneas.Std.alloc.vec.Vec Aeneas.Std.U8)
  (s : Aeneas.Std.Slice Aeneas.Std.U8),
  (↑out).length + 4 + (↑s).length ≤ Aeneas.Std.Usize.max →
    Aeneas.Std.WP.spec (tacenta_session_unit.lifecycle.push_len_prefixed out s) fun w =>
      ↑w = ↑out ++ Tacenta.UnitLifecycleSessionCodec.lenEnc s
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleSessionCodec.lifecycle_push_len_prefixed_spec

/--
info: Tacenta.UnitLifecycleSessionCodec.pendEnc_length : ∀ (p : tacenta_session_unit.lifecycle.PendingInitial)
  (a : Aeneas.Std.Array Aeneas.Std.U8 32#usize),
  (Tacenta.UnitLifecycleSessionCodec.pendEnc p a).length = 48 + (↑p.kem_ciphertext).length
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleSessionCodec.pendEnc_length

/--
info: Tacenta.UnitLifecycleSessionCodec.pending_to_bytes_spec : ∀ (p : tacenta_session_unit.lifecycle.PendingInitial)
  (a : Aeneas.Std.Array Aeneas.Std.U8 32#usize),
  p.ephemeral_public.as_bytes = Aeneas.Std.Result.ok a →
    (↑p.kem_ciphertext).length ≤ 65536 →
      Aeneas.Std.WP.spec p.to_bytes fun v => ↑v = Tacenta.UnitLifecycleSessionCodec.pendEnc p a
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleSessionCodec.pending_to_bytes_spec

/--
info: Tacenta.UnitLifecycleSessionCodec.pending_from_bytes_of : Tacenta.UnitLifecycleSessionCodec.OptionBranchSome →
  ∀ (bytes : Aeneas.Std.Slice Aeneas.Std.U8) (p : tacenta_session_unit.lifecycle.PendingInitial)
    (a : Aeneas.Std.Array Aeneas.Std.U8 32#usize),
    ↑bytes = Tacenta.UnitLifecycleSessionCodec.pendEnc p a →
      tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.from_bytes a = Aeneas.Std.Result.ok p.ephemeral_public →
        (↑p.kem_ciphertext).length ≤ 65536 →
          tacenta_session_unit.lifecycle.PendingInitial.from_bytes bytes = Aeneas.Std.Result.ok (some p)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleSessionCodec.pending_from_bytes_of

/--
info: def Tacenta.UnitLifecycleSessionCodec.be32 : Aeneas.Std.U32 → List Aeneas.Std.U8 :=
fun x => ↑(Aeneas.Std.core.num.U32.to_be_bytes x)
-/
#guard_msgs in
#print Tacenta.UnitLifecycleSessionCodec.be32

/--
info: def Tacenta.UnitLifecycleSessionCodec.be64 : Aeneas.Std.U64 → List Aeneas.Std.U8 :=
fun x => ↑(Aeneas.Std.core.num.U64.to_be_bytes x)
-/
#guard_msgs in
#print Tacenta.UnitLifecycleSessionCodec.be64

/--
info: def Tacenta.UnitLifecycleSessionCodec.optKeyEnc : Option (Aeneas.Std.Array Aeneas.Std.U8 32#usize) →
  List Aeneas.Std.U8 :=
fun x =>
  match x with
  | none => 0#u8 :: List.replicate 32 0#u8
  | some k => 1#u8 :: ↑k
-/
#guard_msgs in
#print Tacenta.UnitLifecycleSessionCodec.optKeyEnc

/--
info: def Tacenta.UnitLifecycleSessionCodec.ratchetEnc : tacenta_session_unit.tacenta_ratchet.State → List Aeneas.Std.U8 :=
fun r =>
  1#u8 ::
    (↑r.dhs_pub ++
      (Tacenta.UnitLifecycleSessionCodec.optKeyEnc r.dhr_pub ++
        (↑r.rk ++
          (Tacenta.UnitLifecycleSessionCodec.optKeyEnc r.cks ++
            (Tacenta.UnitLifecycleSessionCodec.optKeyEnc r.ckr ++
              (Tacenta.UnitLifecycleSessionCodec.be32 r.ns ++
                (Tacenta.UnitLifecycleSessionCodec.be32 r.nr ++
                  (Tacenta.UnitLifecycleSessionCodec.be32 r.pn ++
                    (Tacenta.UnitLifecycleSessionCodec.be32 r.events ++
                      0#u8 :: Tacenta.UnitLifecycleSessionCodec.be32 0#u32)))))))))
-/
#guard_msgs in
#print Tacenta.UnitLifecycleSessionCodec.ratchetEnc

/--
info: def Tacenta.UnitLifecycleSessionCodec.ZeroizingVecRoundTrip : Prop :=
∀ (inst : tacenta_session_unit.zeroize.Zeroize (Aeneas.Std.alloc.vec.Vec Aeneas.Std.U8))
  (v : Aeneas.Std.alloc.vec.Vec Aeneas.Std.U8),
  ∃ z,
    tacenta_session_unit.zeroize.Zeroizing.new inst v = Aeneas.Std.Result.ok z ∧
      tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref inst z = Aeneas.Std.Result.ok v
-/
#guard_msgs in
#print Tacenta.UnitLifecycleSessionCodec.ZeroizingVecRoundTrip

/--
info: @[reducible] def Tacenta.UnitLifecycleSessionCodec.vecInst : tacenta_session_unit.zeroize.Zeroize
  (Aeneas.Std.alloc.vec.Vec Aeneas.Std.U8) :=
tacenta_session_unit.alloc.vec.Vec.Insts.ZeroizeZeroize
  (tacenta_session_unit.zeroize.Zeroize.Blanket tacenta_session_unit.U8.Insts.ZeroizeDefaultIsZeroes)
-/
#guard_msgs in
#print Tacenta.UnitLifecycleSessionCodec.vecInst

/--
info: def Tacenta.UnitLifecycleSessionCodec.dirByte : tacenta_session_unit.tacenta_spqr.Direction → Aeneas.Std.U8 :=
fun x =>
  match x with
  | tacenta_session_unit.tacenta_spqr.Direction.A2b => 0#u8
  | tacenta_session_unit.tacenta_spqr.Direction.B2a => 1#u8
-/
#guard_msgs in
#print Tacenta.UnitLifecycleSessionCodec.dirByte

/--
info: def Tacenta.UnitLifecycleSessionCodec.chainEnc : tacenta_session_unit.tacenta_spqr.Chain → List Aeneas.Std.U8 :=
fun c => 1#u8 :: (↑c.ck ++ Tacenta.UnitLifecycleSessionCodec.be64 c.n)
-/
#guard_msgs in
#print Tacenta.UnitLifecycleSessionCodec.chainEnc

/--
info: def Tacenta.UnitLifecycleSessionCodec.spqrEnc : tacenta_session_unit.tacenta_spqr.State →
  Aeneas.Std.U64 →
    tacenta_session_unit.tacenta_spqr.Chain → tacenta_session_unit.tacenta_spqr.Chain → List Aeneas.Std.U8 :=
fun q e c1 c2 =>
  1#u8 ::
    (↑q.rk ++
      (Tacenta.UnitLifecycleSessionCodec.be64 q.epoch ++
        Tacenta.UnitLifecycleSessionCodec.dirByte q.direction ::
          (Tacenta.UnitLifecycleSessionCodec.be32 1#u32 ++
            (Tacenta.UnitLifecycleSessionCodec.be64 e ++
              (Tacenta.UnitLifecycleSessionCodec.chainEnc c1 ++
                (Tacenta.UnitLifecycleSessionCodec.chainEnc c2 ++ Tacenta.UnitLifecycleSessionCodec.be32 0#u32))))))
-/
#guard_msgs in
#print Tacenta.UnitLifecycleSessionCodec.spqrEnc

/--
info: def Tacenta.UnitLifecycleSessionCodec.tripleEnc : tacenta_session_unit.tacenta_triple.State →
  Aeneas.Std.U64 →
    tacenta_session_unit.tacenta_spqr.Chain → tacenta_session_unit.tacenta_spqr.Chain → List Aeneas.Std.U8 :=
fun t e c1 c2 =>
  1#u8 ::
    (Tacenta.UnitLifecycleSessionCodec.be32 185#u32 ++
      (Tacenta.UnitLifecycleSessionCodec.ratchetEnc t.classical ++
        (Tacenta.UnitLifecycleSessionCodec.be32 140#u32 ++
          Tacenta.UnitLifecycleSessionCodec.spqrEnc t.post_quantum e c1 c2)))
-/
#guard_msgs in
#print Tacenta.UnitLifecycleSessionCodec.tripleEnc

/--
info: def Tacenta.UnitLifecycleSessionCodec.authEnc : tacenta_session_unit.tacenta_braid.Auth → List Aeneas.Std.U8 :=
fun a => ↑a.root_key ++ ↑a.mac_key
-/
#guard_msgs in
#print Tacenta.UnitLifecycleSessionCodec.authEnc

/--
info: def Tacenta.UnitLifecycleSessionCodec.braidEnc : Aeneas.Std.U64 →
  tacenta_session_unit.tacenta_braid.Auth → List Aeneas.Std.U8 :=
fun epoch auth =>
  1#u8 :: 0#u8 :: (Tacenta.UnitLifecycleSessionCodec.be64 epoch ++ Tacenta.UnitLifecycleSessionCodec.authEnc auth)
-/
#guard_msgs in
#print Tacenta.UnitLifecycleSessionCodec.braidEnc

/--
info: def Tacenta.UnitLifecycleSessionCodec.OptionBranchSomeShape : ({T : Type} →
    Option T →
      Aeneas.Std.Result (Aeneas.Std.core.ops.control_flow.ControlFlow (Option Aeneas.Std.core.convert.Infallible) T)) →
  Prop :=
fun br =>
  ∀ (T : Type) (x : T), br (some x) = Aeneas.Std.Result.ok (Aeneas.Std.core.ops.control_flow.ControlFlow.Continue x)
-/
#guard_msgs in
#print Tacenta.UnitLifecycleSessionCodec.OptionBranchSomeShape

/--
info: def Tacenta.UnitLifecycleSessionCodec.OptionBranchSome : Prop :=
Tacenta.UnitLifecycleSessionCodec.OptionBranchSomeShape
  @tacenta_session_unit.core.option.Option.Insts.CoreOpsTry_traitTry.branch
-/
#guard_msgs in
#print Tacenta.UnitLifecycleSessionCodec.OptionBranchSome

/--
info: def Tacenta.UnitLifecycleSessionCodec.optionBranchImpl : {T : Type} →
  Option T →
    Aeneas.Std.Result (Aeneas.Std.core.ops.control_flow.ControlFlow (Option Aeneas.Std.core.convert.Infallible) T) :=
fun {T} x =>
  match x with
  | some x => Aeneas.Std.Result.ok (Aeneas.Std.core.ops.control_flow.ControlFlow.Continue x)
  | none => Aeneas.Std.Result.ok (Aeneas.Std.core.ops.control_flow.ControlFlow.Break none)
-/
#guard_msgs in
#print Tacenta.UnitLifecycleSessionCodec.optionBranchImpl

/--
info: def Tacenta.UnitLifecycleSessionCodec.VecAsSliceShape : ({T : Type} →
    Type → Aeneas.Std.alloc.vec.Vec T → Aeneas.Std.Result (Aeneas.Std.Slice T)) →
  Prop :=
fun asSlice =>
  ∀ (v : Aeneas.Std.alloc.vec.Vec Aeneas.Std.U8), asSlice Aeneas.Std.Global v = Aeneas.Std.Result.ok v.deref
-/
#guard_msgs in
#print Tacenta.UnitLifecycleSessionCodec.VecAsSliceShape

/--
info: def Tacenta.UnitLifecycleSessionCodec.VecAsSlice : Prop :=
Tacenta.UnitLifecycleSessionCodec.VecAsSliceShape @tacenta_session_unit.alloc.vec.Vec.as_slice
-/
#guard_msgs in
#print Tacenta.UnitLifecycleSessionCodec.VecAsSlice

/--
info: def Tacenta.UnitLifecycleSessionCodec.vecAsSliceImpl : {T : Type} →
  Type → Aeneas.Std.alloc.vec.Vec T → Aeneas.Std.Result (Aeneas.Std.Slice T) :=
fun {T} _A v => Aeneas.Std.Result.ok v.deref
-/
#guard_msgs in
#print Tacenta.UnitLifecycleSessionCodec.vecAsSliceImpl

/--
info: def Tacenta.UnitLifecycleSessionCodec.DhPublicBytesRoundTripShape : Tacenta.UnitSatisfiabilityJoint.Interp → Prop :=
fun I =>
  ∀ (pk : I.PublicKeyBytes),
    ∃ a, I.dhPubAsBytes pk = Aeneas.Std.Result.ok a ∧ I.dhPubFromBytes a = Aeneas.Std.Result.ok pk
-/
#guard_msgs in
#print Tacenta.UnitLifecycleSessionCodec.DhPublicBytesRoundTripShape

/--
info: def Tacenta.UnitLifecycleSessionCodec.DhPublicBytesRoundTrip : Prop :=
Tacenta.UnitLifecycleSessionCodec.DhPublicBytesRoundTripShape Tacenta.UnitSatisfiabilityJoint.Interp.real
-/
#guard_msgs in
#print Tacenta.UnitLifecycleSessionCodec.DhPublicBytesRoundTrip

/--
info: @[reducible] def Tacenta.UnitLifecycleSessionCodec.arrInst : tacenta_session_unit.zeroize.Zeroize
  (Aeneas.Std.Array Aeneas.Std.U8 32#usize) :=
tacenta_session_unit.Array.Insts.ZeroizeZeroize 32#usize
  (tacenta_session_unit.zeroize.Zeroize.Blanket tacenta_session_unit.U8.Insts.ZeroizeDefaultIsZeroes)
-/
#guard_msgs in
#print Tacenta.UnitLifecycleSessionCodec.arrInst

/--
info: def Tacenta.UnitLifecycleSessionCodec.DhPrivateBytesRoundTripShape : Tacenta.UnitSatisfiabilityJoint.Interp → Prop :=
fun I =>
  ∀ (k : I.PrivateKey),
    ∃ z a,
      I.dhPrivToBytes k = Aeneas.Std.Result.ok z ∧
        I.zDeref Tacenta.UnitLifecycleSessionCodec.arrInst z = Aeneas.Std.Result.ok a ∧
          I.dhPrivFromBytes a = Aeneas.Std.Result.ok k
-/
#guard_msgs in
#print Tacenta.UnitLifecycleSessionCodec.DhPrivateBytesRoundTripShape

/--
info: def Tacenta.UnitLifecycleSessionCodec.DhPrivateBytesRoundTrip : Prop :=
Tacenta.UnitLifecycleSessionCodec.DhPrivateBytesRoundTripShape Tacenta.UnitSatisfiabilityJoint.Interp.real
-/
#guard_msgs in
#print Tacenta.UnitLifecycleSessionCodec.DhPrivateBytesRoundTrip

/--
info: def Tacenta.UnitLifecycleSessionCodec.ZeroizingVecRoundTripShape : Tacenta.UnitSatisfiabilityJoint.Interp → Prop :=
fun I =>
  ∀ (inst : tacenta_session_unit.zeroize.Zeroize (Aeneas.Std.alloc.vec.Vec Aeneas.Std.U8))
    (v : Aeneas.Std.alloc.vec.Vec Aeneas.Std.U8),
    ∃ z, I.zNew inst v = Aeneas.Std.Result.ok z ∧ I.zDeref inst z = Aeneas.Std.Result.ok v
-/
#guard_msgs in
#print Tacenta.UnitLifecycleSessionCodec.ZeroizingVecRoundTripShape

/--
info: def Tacenta.UnitLifecycleSessionCodec.lenEnc : Aeneas.Std.Slice Aeneas.Std.U8 → List Aeneas.Std.U8 :=
fun s => Tacenta.UnitLifecycleSessionCodec.be32 (Aeneas.Std.UScalar.cast Aeneas.Std.UScalarTy.U32 s.len) ++ ↑s
-/
#guard_msgs in
#print Tacenta.UnitLifecycleSessionCodec.lenEnc

/--
info: def Tacenta.UnitLifecycleSessionCodec.pendEnc : tacenta_session_unit.lifecycle.PendingInitial →
  Aeneas.Std.Array Aeneas.Std.U8 32#usize → List Aeneas.Std.U8 :=
fun p a =>
  ↑a ++
    (Tacenta.UnitLifecycleSessionCodec.lenEnc p.kem_ciphertext.deref ++
      (Tacenta.UnitLifecycleSessionCodec.be32 p.signed_prekey_id ++
        (Tacenta.UnitLifecycleSessionCodec.be32 p.one_time_prekey_id ++
          Tacenta.UnitLifecycleSessionCodec.be32 p.kem_prekey_id)))
-/
#guard_msgs in
#print Tacenta.UnitLifecycleSessionCodec.pendEnc
