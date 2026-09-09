import Translation.TacentaSpqr
import Translation.SpqrT1
import Model.SparseRatchet

/-!
# T3 for the sparse post-quantum ratchet: the translated code refines the model

`SpqrT1.lean` proved this crate's translated Rust cannot panic. This file goes
further: the translated code computes what `Model.SparseRatchet` computes, not
merely that it returns.

## The opaque boundary, once

Unlike the ML-KEM Braid, this crate carries no key-encapsulation boundary and no
erasure-coding boundary: `Output` arrives as a value from whichever crate
produced it, and this crate does nothing with it but fold it in. The opaque
calls this file assumes anything *about the value of* are `hkdf_sha256` and
the `zeroize` wrapper its expansion goes through, both inside the translated
(non-opaque) `kdf_init`, `kdf_rk`, and `kdf_ck`, so there is one KDF
assumption below and one wrapper round trip per width rather than a family of
them, and every `_refines` theorem for translated code is proved outright
against those, not assumed.

That is not the whole trusted base, and this file does not pretend it is:
`Vec::retain`, `Vec::remove`, `Vec::append`, `Zeroize`, and `Option::clone`
are each their own opaque call too, carried over as assumptions from
`SpqrT1.lean` (three of them strengthened past bare totality, one genuinely
new) rather than reproved here. See the closing section for the full count
and why it is eight, not one. -/

open Aeneas Aeneas.Std Result

namespace Tacenta.SpqrT3

open tacenta_spqr

/-- A translated byte as the model's. -/
def u8 (b : Std.U8) : UInt8 := UInt8.ofNat b.val

/-- A fixed-size array of translated bytes as the model's key. -/
def keyOf {n : Usize} (a : Array Std.U8 n) : Model.State.Key := a.val.map u8

/-- A slice of translated bytes as the model's byte list. -/
def sliceOf (s : Slice Std.U8) : List UInt8 := s.val.map u8

/-! ## The trusted boundary, restated as agreement

`SpqrT1.lean` assumed `kdf_rk`/`kdf_ck` (the translated wrapping functions)
cannot fail. Refinement needs more, and states it one level down, at the
opaque primitive itself: that when `hkdf_sha256` returns, it returns what
`Model.Kdf.hkdf` computes. Argument order follows the Rust and the model
alike: salt, then the input keying material, then the info string --
`kdf_init`/`kdf_rk`/`kdf_ck` all call `hkdf_sha256` this way, and
`Model.SparseRatchet.kdfInit`/`kdfRk`/`kdfCk` all call `Model.Kdf.hkdf` the
same way. -/
def SpqrHkdfAgrees : Prop :=
  ∀ N salt ikm info, ∃ r, tacenta_kdf.hkdf_sha256 N salt ikm info = ok r ∧
    keyOf r = Model.Kdf.hkdf (sliceOf salt) (sliceOf ikm) (sliceOf info) N.val

@[step]
theorem hkdf_step (h : SpqrHkdfAgrees) (N : Usize) (salt ikm info : Slice Std.U8) :
    tacenta_kdf.hkdf_sha256 N salt ikm info ⦃ fun r =>
      keyOf r = Model.Kdf.hkdf (sliceOf salt) (sliceOf ikm) (sliceOf info) N.val ⦄ := by
  obtain ⟨r, hr, hv⟩ := h N salt ikm info; simp [hr, hv]

/-! ## The `zeroize` wrapper round-trips, at the two widths this crate wraps at

`kdf_init` and `kdf_rk` wrap their ninety-six-byte expansion in `Zeroizing`
before splitting it, and `kdf_ck` its sixty-four-byte one. Wrapper and
projection are both opaque, so, as in `T3.lean`, refinement needs the value to
survive the wrapper: without that nothing connects the expansion's output to
the pieces copied out of it. It is true of the crate for the same reason:
a newtype constructor and its projection.

Stated at each width separately, as `T3.lean` does at sixty-four and eighty,
so that neither hypothesis is wider than its use -- and for **this crate's
constants**, which are not the ratchet's (`SpqrT1.lean`'s counting trap).
`SpqrT1.lean` needs neither: its `KdfRkTotal`/`KdfCkTotal` are stated at the
translated wrapping functions, above the wrapper, so there is no
wrapper-only totality clause here for the round trip to subsume, and the
second conjunct `T3.lean`'s carries for that purpose is left off. -/
def ZeroizingRoundTrips96 : Prop :=
  ∀ inst : zeroize.Zeroize (Array Std.U8 96#usize),
    ∀ z, ∃ w, zeroize.Zeroizing.new inst z = ok w ∧
      zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref inst w = ok z

def ZeroizingRoundTrips64 : Prop :=
  ∀ inst : zeroize.Zeroize (Array Std.U8 64#usize),
    ∀ z, ∃ w, zeroize.Zeroizing.new inst z = ok w ∧
      zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref inst w = ok z

-- No stepping rule is registered for the projection: with none, `step*` stops
-- at it, and the round trip the wrapper's rule hands back is applied by hand.
@[step]
theorem zeroizing_new_step96 (hz : ZeroizingRoundTrips96)
    (inst : zeroize.Zeroize (Array Std.U8 96#usize)) (z : Array Std.U8 96#usize) :
    zeroize.Zeroizing.new inst z ⦃ fun w =>
      zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref inst w = ok z ⦄ := by
  obtain ⟨w, hw, hd⟩ := hz inst z; simp [hw, hd]

@[step]
theorem zeroizing_new_step64 (hz : ZeroizingRoundTrips64)
    (inst : zeroize.Zeroize (Array Std.U8 64#usize)) (z : Array Std.U8 64#usize) :
    zeroize.Zeroizing.new inst z ⦃ fun w =>
      zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref inst w = ok z ⦄ := by
  obtain ⟨w, hw, hd⟩ := hz inst z; simp [hw, hd]

/-! ## The labels agree

The four wire-sensitive byte strings are struck once here, byte for byte,
rather than left to `simp` to rediscover at every call site. -/

theorem protocol_info_agrees : sliceOf PROTOCOL_INFO = Model.SparseRatchet.protocolInfo := by
  native_decide

theorem chain_start_agrees : sliceOf CHAIN_START_LABEL = Model.SparseRatchet.chainStart := by
  native_decide

theorem root_label_agrees : sliceOf ROOT_LABEL = Model.SparseRatchet.rootLabel := by
  native_decide

theorem chain_label_agrees : sliceOf CHAIN_LABEL = Model.SparseRatchet.chainLabel := by
  native_decide

theorem protocol_info_len : (PROTOCOL_INFO : Slice Std.U8).length = 12 := by
  simp only [global_simps, Array.length_to_slice]; scalar_tac

theorem chain_start_len : (CHAIN_START_LABEL : Slice Std.U8).length = 11 := by
  simp only [global_simps, Array.length_to_slice]; scalar_tac

theorem root_label_len : (ROOT_LABEL : Slice Std.U8).length = 4 := by
  simp only [global_simps, Array.length_to_slice]; scalar_tac

theorem chain_label_len : (CHAIN_LABEL : Slice Std.U8).length = 5 := by
  simp only [global_simps, Array.length_to_slice]; scalar_tac

/-- `Vec::extend_from_slice` is modelled concretely by the Aeneas library
rather than left an axiom, so this is provable outright: the clone on `u8` is
the identity, and the only way it fails is a length past `Usize.max`. -/
@[step]
theorem extend_from_slice_spec (v : alloc.vec.Vec Std.U8) (s : Slice Std.U8)
    (h : v.val.length + s.val.length ≤ Usize.max) :
    alloc.vec.Vec.extend_from_slice core.clone.CloneU8 v s ⦃ fun r =>
      r.val = v.val ++ s.val ⦄ := by
  unfold alloc.vec.Vec.extend_from_slice
  have hclone : ∀ x ∈ s.val, (core.clone.CloneU8.clone) x = ok x := by
    intro x _; rfl
  obtain ⟨s', hs'eq, hs'val⟩ := Std.WP.spec_imp_exists (Slice.clone_spec hclone)
  rw [← hs'val] at hs'eq
  have h' : v.length + s.length ≤ Usize.max := h
  rw [dif_pos h']
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

/-- Concatenating the fixed protocol prefix with a suffix returns the
concatenation, given room. Every caller passes one of the three fixed labels
(11, 4, and 5 bytes), all far under the twelve-byte prefix's own room, so the
bound is never in doubt in practice; it is stated rather than baked in so nothing
here depends on the labels' exact lengths. -/
@[step]
theorem info_agrees (suffix : Slice Std.U8) (hlen : suffix.length + 12 ≤ Usize.max) :
    tacenta_spqr.info suffix ⦃ fun v =>
      v.val.map u8 = Model.SparseRatchet.protocolInfo ++ sliceOf suffix ⦄ := by
  unfold tacenta_spqr.info
  have hpi := protocol_info_len
  step*
  all_goals (try (simp_all [alloc.vec.Vec.with_capacity, alloc.vec.Vec.new]))
  all_goals (try scalar_tac)
  all_goals (try simp [sliceOf])
  all_goals (try exact protocol_info_agrees)

/-! ## The three derivations refine the model's -/

/-- `Vec::deref` reads back exactly the bytes assembled, with nothing left to
track: the coercion to a byte list sees straight through the wrapper. -/
theorem vec_deref_coe (v : alloc.vec.Vec Std.U8) :
    (↑(alloc.vec.Vec.deref v) : List Std.U8) = ↑v := rfl

/-- The `i`-th big-endian byte of a 64-bit value, as a `setWidth`/shift rather
than the raw recursive `toLEBytes` definition. The recursive form unfolds into
an unreadable nested tower of `setWidth`/`>>>` that neither `simp` nor
`scalar_tac` closes; this closed form is what both sides can actually be
compared against. -/
private theorem beByte_eq (v : BitVec 64) (i : Nat) (hi : i < 8) :
    v.toBEBytes[i]! = (v >>> (8 * (7 - i))).setWidth 8 := by
  rw [BitVec.eq_iff]
  intro j hj
  have hlen : v.toLEBytes.length = 8 := by simp [BitVec.toLEBytes_length]
  have hib : i < v.toBEBytes.length := by simp [BitVec.toBEBytes_length]; omega
  have hb : 7 - i < v.toLEBytes.length := by omega
  have hrw : v.toBEBytes[i]! = v.toLEBytes[7 - i]! := by
    rw [← List.Inhabited_getElem_eq_getElem! v.toBEBytes i hib]
    unfold BitVec.toBEBytes
    rw [List.getElem_reverse]
    simp only [hlen]
    exact List.Inhabited_getElem_eq_getElem! v.toLEBytes (7 - i) hb
  have hbit := BitVec.toLEBytes_getElem!_testBit v (7 - i) j hj
  simp only [Byte.testBit, BitVec.getElem!_eq_testBit_toNat] at hbit
  rw [hrw, BitVec.getElem!_setWidth 8 _ j hj, BitVec.getElem!_eq_testBit_toNat,
    BitVec.getElem!_eq_testBit_toNat, BitVec.toNat_ushiftRight, hbit, Nat.testBit_shiftRight]

private theorem setWidth8_toNat (x : BitVec 64) : (x.setWidth 8).toNat = x.toNat % 2 ^ 8 := by
  rw [BitVec.toNat_setWidth]

/-- The real code's eight-byte big-endian encoding of a message/epoch counter
agrees with the model's. -/
theorem be64_agrees (n : Std.U64) :
    sliceOf (Array.to_slice (core.num.U64.to_be_bytes n)) = Model.SparseRatchet.be64 n.val := by
  apply List.ext_getElem
  · simp [sliceOf, Array.to_slice, core.num.U64.to_be_bytes, Model.SparseRatchet.be64]
  · intro i h1 h2
    have hi : i < 8 := by
      simp only [Model.SparseRatchet.be64, List.length_map, List.length_range] at h2; omega
    simp only [sliceOf, Array.to_slice, List.getElem_map, Model.SparseRatchet.be64,
      List.getElem_range]
    have hib8 : i < n.bv.toBEBytes.length := by simp [BitVec.toBEBytes_length]; omega
    simp only [u8, core.num.U64.to_be_bytes, List.getElem_map]
    rw [← getElem!_pos _ i hib8, beByte_eq n.bv i hi]
    apply UInt8.toNat.inj
    simp only [UInt8.toNat_ofNat', UScalar.val, setWidth8_toNat,
      BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    have h256 : (256 : Nat) = 2 ^ 8 := by norm_num
    rw [h256, ← pow_mul]

theorem kdf_init_refines (h : SpqrHkdfAgrees) (hz : ZeroizingRoundTrips96) (sk : Slice Std.U8) :
    tacenta_spqr.kdf_init sk ⦃ fun r =>
      (keyOf r.1, keyOf r.2.1, keyOf r.2.2) = Model.SparseRatchet.kdfInit (sliceOf sk) ⦄ := by
  have hcs : List.map u8 (↑CHAIN_START_LABEL : List Std.U8) = Model.SparseRatchet.chainStart :=
    chain_start_agrees
  unfold tacenta_spqr.kdf_init tacenta_spqr.split3
  step*
  all_goals (try (simp only [chain_start_len]; scalar_tac))
  all_goals (try simp only [out_post])
  all_goals (try step*)
  all_goals (try simp_all [Model.SparseRatchet.kdfInit, Model.SparseRatchet.split3,
    keyOf, sliceOf, u8, vec_deref_coe, Array.repeat, List.slice, List.map_take, List.map_drop])

theorem kdf_rk_refines (h : SpqrHkdfAgrees) (hz : ZeroizingRoundTrips96)
    (rk k : Array Std.U8 32#usize) :
    tacenta_spqr.kdf_rk rk k ⦃ fun r =>
      (keyOf r.1, keyOf r.2.1, keyOf r.2.2) = Model.SparseRatchet.kdfRk (keyOf rk) (keyOf k) ⦄ := by
  have hrl : List.map u8 (↑ROOT_LABEL : List Std.U8) = Model.SparseRatchet.rootLabel :=
    root_label_agrees
  unfold tacenta_spqr.kdf_rk tacenta_spqr.split3
  step*
  all_goals (try (simp only [root_label_len]; scalar_tac))
  all_goals (try simp only [out_post])
  all_goals (try step*)
  all_goals (try simp_all [Model.SparseRatchet.kdfRk, Model.SparseRatchet.split3,
    keyOf, sliceOf, vec_deref_coe, List.slice, List.map_take, List.map_drop])

theorem kdf_ck_refines (h : SpqrHkdfAgrees) (hz : ZeroizingRoundTrips64)
    (ck : Array Std.U8 32#usize) (n : Std.U64) :
    tacenta_spqr.kdf_ck ck n ⦃ fun r =>
      (keyOf r.1, keyOf r.2) = Model.SparseRatchet.kdfCk (keyOf ck) n.val ⦄ := by
  have hbe := be64_agrees n
  have hcl : List.map u8 (↑CHAIN_LABEL : List Std.U8) = Model.SparseRatchet.chainLabel :=
    chain_label_agrees
  unfold tacenta_spqr.kdf_ck tacenta_spqr.be64
  step*
  all_goals (try (simp only [chain_label_len]; scalar_tac))
  all_goals (try simp only [out_post])
  all_goals (try step*)
  all_goals (try simp_all [Model.SparseRatchet.kdfCk, keyOf, sliceOf, vec_deref_coe, Array.to_slice, List.slice, List.map_take, List.map_drop])

/-- Agreement, with the wrapper's round trip at the width each derivation
wraps at, subsumes the totality `SpqrT1.lean` assumed for these two, so a
caller holding these need not carry that hypothesis as well. -/
theorem SpqrHkdfAgrees.kdfRkTotal (h : SpqrHkdfAgrees) (hz : ZeroizingRoundTrips96) :
    Tacenta.SpqrT1.KdfRkTotal := by
  intro rk k
  obtain ⟨r, hr, _⟩ := Std.WP.spec_imp_exists (kdf_rk_refines h hz rk k)
  exact ⟨r, hr⟩

theorem SpqrHkdfAgrees.kdfCkTotal (h : SpqrHkdfAgrees) (hz : ZeroizingRoundTrips64) :
    Tacenta.SpqrT1.KdfCkTotal := by
  intro ck n
  obtain ⟨r, hr, _⟩ := Std.WP.spec_imp_exists (kdf_ck_refines h hz ck n)
  exact ⟨r, hr⟩

/-! ## The state relation

Field by field, with the shape difference (an association list vs a real
`Vec`/`List` pair) absorbed here and nowhere else. -/

/-- A translated chain as the model's. -/
def chainOf (c : Chain) : Model.SparseRatchet.Chain := ⟨keyOf c.ck, c.n.val⟩

/-- A translated chain pair as the model's. -/
def chainsOf (cs : Chains) : Model.SparseRatchet.Chains :=
  ⟨cs.send.map chainOf, cs.receive.map chainOf⟩

/-- A translated chain-table entry as the model's. -/
def chainsEntryOf (p : Std.U64 × Chains) : Nat × Model.SparseRatchet.Chains :=
  (p.1.val, chainsOf p.2)

/-- A translated skipped-key entry as the model's. -/
def skippedOf (s : Skipped) : Nat × Nat × Model.State.Key :=
  (s.epoch.val, s.n.val, keyOf s.key)

/-- A translated direction as the model's. -/
def directionOf : Direction → Model.SparseRatchet.Direction
  | .A2b => .a2b
  | .B2a => .b2a

/-- The translated state refines the model state. -/
structure StateRefines (s : State) (m : Model.SparseRatchet.State) : Prop where
  rk        : keyOf s.rk = m.rk
  epoch     : s.epoch.val = m.epoch
  chains    : s.chains.val.map chainsEntryOf = m.chains
  skipped   : s.skipped.val.map skippedOf = m.skipped
  direction : directionOf s.direction = m.direction

/-! ## Two facts about scanning a list from the front

Both loops below (`find_chains`, `try_skipped`) walk a `Vec` by index looking
for the first entry a predicate accepts, which is exactly what the model's
`List.find?` does. These two lemmas bridge an index-scan's invariant (nothing
in the scanned prefix matched) to a `find?` conclusion, generically enough to
serve both loops. -/

/-- Nothing before the entry matches and the entry does, so the model's
first-match lookup finds exactly it. Stated on an explicit split rather than an
index, because rewriting a list under a dependent index breaks the motive. -/
theorem find?_eq_of_split {α : Type} (p : α → Bool) (pre : List α) (a : α)
    (post : List α) (hpre : pre.filter p = []) (hpa : p a = true) :
    (pre ++ a :: post).find? p = some a := by
  have hnone : pre.find? p = none := by
    rw [List.find?_eq_none]
    intro x hx hpx
    have : x ∈ pre.filter p := List.mem_filter.mpr ⟨hx, hpx⟩
    rw [hpre] at this
    exact absurd this List.not_mem_nil
  rw [List.find?_append, hnone]
  simp [List.find?_cons_of_pos hpa]

/-- Nothing before the index matches and the index is past the end, so nothing
matches at all. -/
theorem find?_eq_none_of_scanned {α : Type} (p : α → Bool) (L : List α) (j : Nat)
    (hge : L.length ≤ j) (hpre : (L.take j).filter p = []) :
    L.find? p = none := by
  rw [List.take_of_length_le hge] at hpre
  rw [List.find?_eq_none]
  intro x hx hpx
  have : x ∈ L.filter p := List.mem_filter.mpr ⟨hx, hpx⟩
  rw [hpre] at this
  exact absurd this List.not_mem_nil

/-! ## `find_chains` refines the model's -/

theorem find_chains_loop_refines (s : State) (e : Std.U64) (i : Usize)
    (hpre : ((s.chains.val.map chainsEntryOf).take i.val).filter
              (fun p => p.1 == e.val) = []) :
    State.find_chains_loop s e i ⦃ fun o =>
      o.map chainsOf = ((s.chains.val.map chainsEntryOf).find?
        (fun p => p.1 == e.val)).map Prod.snd ⦄ := by
  unfold State.find_chains_loop
  apply loop.spec_decr_nat
    (measure := fun j => s.chains.val.length - j.val)
    (inv := fun j => ((s.chains.val.map chainsEntryOf).take j.val).filter
      (fun p => p.1 == e.val) = [])
  · rintro j hinv
    simp only [State.find_chains_loop.body]
    by_cases hlt : j.val < s.chains.val.length <;> step*
    · -- The entry at this index matches, so the scan (and the model's
      -- `find?`) stop here.
      rename_i heq
      have hjm : j.val < (s.chains.val.map chainsEntryOf).length := by simpa using hlt
      have hi1 : ((s.chains.val)[j.val]'(by simpa using hlt)).1 = i2 :=
        (Prod.ext_iff.mp i2_post.symm).1
      have hi2 : ((s.chains.val)[j.val]'(by simpa using hlt)).2 = c :=
        (Prod.ext_iff.mp i2_post.symm).2
      have hpj : (fun p : Nat × Model.SparseRatchet.Chains => p.1 == e.val)
          (s.chains.val.map chainsEntryOf)[j.val] = true := by
        rw [List.getElem_map, chainsEntryOf, hi1, heq]
        simp
      have hsp : (s.chains.val.map chainsEntryOf)
          = ((s.chains.val.map chainsEntryOf).take j.val)
            ++ (s.chains.val.map chainsEntryOf)[j.val]
              :: (s.chains.val.map chainsEntryOf).drop (j.val + 1) := by
        rw [← List.drop_eq_getElem_cons hjm, List.take_append_drop]
      rw [hsp, find?_eq_of_split _ _ _ _ hinv hpj, List.getElem_map, chainsEntryOf, hi2]
      simp
    · -- No match here, so the scan (and `find?`) keep going past it.
      rename_i heq
      have hjm : j.val < (s.chains.val.map chainsEntryOf).length := by simpa using hlt
      have hi1 : ((s.chains.val)[j.val]'(by simpa using hlt)).1 = i2 :=
        (Prod.ext_iff.mp i2_post.symm).1
      have hnm : (i2.val == e.val) = false := by
        simp only [beq_eq_false_iff_ne, ne_eq]
        intro hc
        exact heq (by scalar_tac)
      rw [i3_post]
      rw [List.take_add_one, List.getElem?_eq_getElem hjm, List.filter_append, hinv]
      simp [chainsEntryOf, hi1, hnm]
      scalar_tac
    · -- The scan is spent, so nothing matched anywhere.
      simp [find?_eq_none_of_scanned _ _ j.val (by simpa using hlt) hinv]
  · exact hpre

@[step]
theorem find_chains_refines (s : State) (e : Std.U64) :
    State.find_chains s e ⦃ fun o =>
      o.map chainsOf = ((s.chains.val.map chainsEntryOf).find?
        (fun p => p.1 == e.val)).map Prod.snd ⦄ :=
  find_chains_loop_refines s e 0#usize (by simp)

theorem findChains_refines {s : State} {m : Model.SparseRatchet.State}
    (hrel : StateRefines s m) (e : Std.U64) :
    State.find_chains s e ⦃ fun o =>
      o.map chainsOf = Model.SparseRatchet.findChains m e.val ⦄ := by
  have h := find_chains_refines s e
  have heq : Model.SparseRatchet.findChains m e.val
      = ((s.chains.val.map chainsEntryOf).find? (fun p => p.1 == e.val)).map Prod.snd := by
    rw [Model.SparseRatchet.findChains, ← hrel.chains]
  simpa only [heq] using h

/-! ## `retain` and `remove`, restated as agreement

`SpqrT1.lean` assumed these two opaque Aeneas library primitives merely
return (`VecRetainTotal`, `VecRemoveTotal`). Refinement needs the value too:
that `retain` keeps exactly what a *pure* test function accepts (`hp` pins the
closure down to one, which every call site here satisfies -- none of this
crate's retain closures capture or mutate anything), and that `remove`
returns the element actually at the index it removed, not merely a vector one
shorter. Both are strictly stronger than `SpqrT1.lean`'s totality, so this
file does not also carry that hypothesis.

`VecRemoveAgrees` names the removed element only under the index bound the
call site has anyway. Naming it as `v.val[i.val]!`, whose out-of-range value
is the `Inhabited` instance's `default`, quantified over every instance,
would be refutable (two instances on `Bool`, one empty vector, one axiom
returning one value), and `try_skipped_refines` and `receive_refines` would
be provable from `False`; `Translation/Satisfiability.lean` refutes that
shape and models this one. -/

def VecRetainAgrees : Prop :=
  ∀ {T F : Type} (A : Type) (inst : core.ops.function.FnMut F T Bool)
    (v : alloc.vec.Vec T) (f : F) (p : T → Bool)
    (_hp : ∀ x, inst.call_mut f x = ok (p x, f)),
    ∃ r, alloc.vec.Vec.retain A inst v f = ok r ∧ r.val = v.val.filter p

def VecRemoveAgrees : Prop :=
  ∀ {T : Type} [Inhabited T] (A : Type) (v : alloc.vec.Vec T) (i : Usize),
    ∃ r, alloc.vec.Vec.remove A v i = ok r ∧
      (∀ h : i.val < v.val.length, r.1 = v.val[i.val]'h) ∧
      r.2.val = v.val.eraseIdx i.val

/-- Filtering commutes with a map whose predicate factors through it. Needed
every time a chain- or skipped-table entry's translated form is filtered on
one side and its model form on the other. -/
theorem List.filter_map_comm {α β : Type} (l : List α) (f : α → β) (p : α → Bool)
    (q : β → Bool) (hpq : ∀ x, p x = q (f x)) :
    (l.filter p).map f = (l.map f).filter q := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.filter_cons, List.map_cons, hpq hd]
    split <;> simp [ih]

/-- The membership-scoped version: the predicates need only agree on the
list's own entries, which is what a room bound stated over that same list
gives. -/
theorem List.filter_map_comm_mem {α β : Type} (l : List α) (f : α → β) (p : α → Bool)
    (q : β → Bool) (hpq : ∀ x ∈ l, p x = q (f x)) :
    (l.filter p).map f = (l.map f).filter q := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.filter_cons, List.map_cons, hpq hd (by simp)]
    split <;> simp [ih (fun x hx => hpq x (by simp [hx]))]

/-- Deleting every match, given at most one, is erasing at the one index that
matched: `T3.lean`'s own lemma of this shape, for the ratchet's skipped-key
store, restated here since each translation unit's list is its own term. -/
theorem filter_not_eq_eraseIdx {α : Type} (p : α → Bool) (l : List α) (k : Nat)
    (hk : k < l.length) (hpk : p l[k] = true)
    (hone : (l.filter p).length ≤ 1) :
    l.filter (fun x => !p x) = l.eraseIdx k := by
  have hsplit : l = l.take k ++ l[k] :: l.drop (k + 1) := by
    rw [← List.drop_eq_getElem_cons hk, List.take_append_drop]
  have hfil : (l.filter p).length
      = ((l.take k).filter p).length + 1 + ((l.drop (k + 1)).filter p).length := by
    nth_rewrite 1 [hsplit]
    simp only [List.filter_append, List.filter_cons_of_pos hpk,
      List.length_append, List.length_cons]
    omega
  have hpre : (l.take k).filter p = [] := by
    have : ((l.take k).filter p).length = 0 := by omega
    exact List.length_eq_zero_iff.mp this
  have hpost : (l.drop (k + 1)).filter p = [] := by
    have : ((l.drop (k + 1)).filter p).length = 0 := by omega
    exact List.length_eq_zero_iff.mp this
  have hkeep : ∀ (m : List α), m.filter p = [] → m.filter (fun x => !p x) = m := by
    intro m hm
    apply List.filter_eq_self.mpr
    intro x hx
    simp only [Bool.not_eq_true']
    by_contra hc
    simp only [Bool.not_eq_false] at hc
    have : x ∈ m.filter p := List.mem_filter.mpr ⟨hx, hc⟩
    rw [hm] at this
    exact absurd this (List.not_mem_nil)
  rw [List.eraseIdx_eq_take_drop_succ]
  nth_rewrite 1 [hsplit]
  rw [List.filter_append, List.filter_cons_of_neg (by simp [hpk]),
    hkeep _ hpre, hkeep _ hpost]

/-- Mapping commutes with erasing at an index. -/
theorem map_eraseIdx {α β : Type} (f : α → β) (l : List α) (i : Nat) :
    (l.eraseIdx i).map f = (l.map f).eraseIdx i := by
  induction l generalizing i with
  | nil => simp
  | cons a t ih => cases i <;> simp [ih]

/-- The room bound `set_chains`/`setChains` needs propagated: every entry
either survived the retain (so it already satisfied the bound) or is the one
freshly added (whose own bound is given directly). -/
theorem setChains_bound {α : Type} (l : List (Nat × α)) (e : Nat) (c : α)
    (hl : ∀ p ∈ l, p.1 + Model.SparseRatchet.epochsKept ≤ Std.U64.max)
    (he : e + Model.SparseRatchet.epochsKept ≤ Std.U64.max) :
    ∀ p ∈ (l.filter (fun p => !(p.1 == e))) ++ [(e, c)],
      p.1 + Model.SparseRatchet.epochsKept ≤ Std.U64.max := by
  intro p hp
  simp only [List.mem_append, List.mem_filter, List.mem_singleton] at hp
  rcases hp with ⟨hp1, -⟩ | hp2
  · exact hl p hp1
  · rw [hp2]; exact he

/-- Filtering, appending one entry, then filtering again never grows a list past
one more than it started with: the fully generic shape both `setChains` (a
retain then a push) and `clearOldEpochs` afterward take, stated once so the
appended value never needs spelling out. -/
theorem filter_append_filter_len_le {α : Type} (l : List (Nat × α)) (e : Nat) (c : α)
    (p1 p2 : Nat × α → Bool) :
    ((l.filter p1 ++ [(e, c)]).filter p2).length ≤ l.length + 1 := by
  have h1 := List.length_filter_le p2 (l.filter p1 ++ [(e, c)])
  have h2 := List.length_filter_le p1 l
  simp only [List.length_append, List.length_singleton] at h1
  omega

/-- Filtering by a second predicate after already filtering by a first one
never leaves more matches than filtering by the second predicate alone: the
first filter can only have dropped candidates, never added them. Used to
carry an "at most one match" fact through `clearOldEpochs`'s own filtering. -/
theorem List.filter_filter_length_le {α : Type} (l : List α) (p q : α → Bool) :
    ((l.filter p).filter q).length ≤ (l.filter q).length := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.filter_cons]
    by_cases hp : p hd <;> by_cases hq : q hd <;> simp_all <;> omega

/-- `advance` grows the chain table by at most the one epoch it opens: `setChains`
retains (never grows) then appends one, and `clearOldEpochs` only retains. Needed
by every caller that carries a chains-length room bound across a `maybe_advance`
call. -/
theorem advance_chains_len_le (M : Model.SparseRatchet.State) (o : Model.SparseRatchet.Output)
    (M' : Model.SparseRatchet.State) (h : Model.SparseRatchet.advance M o = some M') :
    M'.chains.length ≤ M.chains.length + 1 := by
  unfold Model.SparseRatchet.advance at h
  split at h
  · injection h with h
    subst h
    simp only [Model.SparseRatchet.clearOldEpochs, Model.SparseRatchet.setChains]
    exact filter_append_filter_len_le M.chains o.keyEpoch _ _ _
  · simp at h

/-- `advance` never grows the skipped-key store: `clearOldEpochs`, the last
step, only filters it. -/
theorem advance_skipped_len_le (M : Model.SparseRatchet.State) (o : Model.SparseRatchet.Output)
    (M' : Model.SparseRatchet.State) (h : Model.SparseRatchet.advance M o = some M') :
    M'.skipped.length ≤ M.skipped.length := by
  unfold Model.SparseRatchet.advance at h
  split at h
  · injection h with h
    subst h
    simp only [Model.SparseRatchet.clearOldEpochs, Model.SparseRatchet.setChains]
    exact List.length_filter_le _ _
  · simp at h

/-- `advance`'s effect on the skipped-key store is exactly `clearOldEpochs`'s
own filter, stated as an equation so a caller can rewrite with it directly. -/
theorem advance_skipped_eq (M : Model.SparseRatchet.State) (o : Model.SparseRatchet.Output)
    (M' : Model.SparseRatchet.State) (h : Model.SparseRatchet.advance M o = some M') :
    M'.skipped = M.skipped.filter
      (fun x => decide (o.keyEpoch < x.1 + Model.SparseRatchet.epochsKept)) := by
  unfold Model.SparseRatchet.advance at h
  split at h
  · injection h with h
    subst h
    simp only [Model.SparseRatchet.clearOldEpochs, Model.SparseRatchet.setChains]
  · simp at h

/-- `setChains` never grows the chains table past one more than it started
with: a retain then a push. -/
theorem setChains_chains_len_le (st : Model.SparseRatchet.State) (e : Nat)
    (c : Model.SparseRatchet.Chains) :
    (Model.SparseRatchet.setChains st e c).chains.length ≤ st.chains.length + 1 := by
  simp only [Model.SparseRatchet.setChains]
  have := List.length_filter_le (fun p => !(p.1 == e)) st.chains
  simp only [List.length_append, List.length_singleton]
  omega

/-- `skipMessageKeys` never grows the chains table past one more than it
started with: it either leaves the state untouched or calls `setChains`
once. -/
theorem skipMessageKeys_chains_len_le (M : Model.SparseRatchet.State) (e upto : Nat)
    (M' : Model.SparseRatchet.State) (h : Model.SparseRatchet.skipMessageKeys M e upto = some M') :
    M'.chains.length ≤ M.chains.length + 1 := by
  unfold Model.SparseRatchet.skipMessageKeys at h
  split at h
  · simp at h
  split at h
  · simp at h
  split at h
  · injection h with h; subst h; omega
  split at h
  · simp at h
  split at h
  · simp at h
  · injection h with h
    subst h
    exact setChains_chains_len_le _ _ _

/-- Every chain the table holds, on either side, has a counter still below
`Std.U64.max` -- the real precondition `send`/`receive` need to justify
incrementing it by one. Stated over the model's chains list (`Nat`-valued
counters, no overflow to speak of on that side) so the two preservation
lemmas below can be proved by unfolding `List.filter`/`List.mem_of_find?`
alone, with no opaque call and no new assumption. -/
def ChainCounterBounded (chains : List (Nat × Model.SparseRatchet.Chains)) : Prop :=
  ∀ p ∈ chains, ∀ ch : Model.SparseRatchet.Chain,
    (p.2.send = some ch ∨ p.2.receive = some ch) → ch.n < Std.U64.max

/-- A successful `findChains` names a real entry of the table, not just a
value that happens to equal one -- needed to hand `ChainCounterBounded` the
membership fact it asks for. -/
theorem findChains_mem (st : Model.SparseRatchet.State) (e : Nat)
    (cs : Model.SparseRatchet.Chains) (h : Model.SparseRatchet.findChains st e = some cs) :
    (e, cs) ∈ st.chains := by
  unfold Model.SparseRatchet.findChains at h
  rcases hf : st.chains.find? (fun p => p.1 == e) with _ | p
  · simp [hf] at h
  · simp only [hf, Option.map_some, Option.some.injEq] at h
    have hmem := List.mem_of_find?_eq_some hf
    have hprop := List.find?_some hf
    simp only [beq_iff_eq] at hprop
    rw [← h, ← hprop]
    exact hmem

/-- `advance` preserves `ChainCounterBounded`: every surviving entry passed
through `clearOldEpochs`'s and `setChains`'s filters is untouched, drawn
straight from the input, and the one entry `setChains` adds is fresh with
both counters at zero. -/
theorem advance_chain_counter_bounded (M : Model.SparseRatchet.State)
    (o : Model.SparseRatchet.Output) (M' : Model.SparseRatchet.State)
    (hadv : Model.SparseRatchet.advance M o = some M')
    (hb : ChainCounterBounded M.chains) : ChainCounterBounded M'.chains := by
  unfold Model.SparseRatchet.advance at hadv
  split at hadv
  · injection hadv with hadv
    subst hadv
    intro p hp ch hch
    unfold Model.SparseRatchet.clearOldEpochs Model.SparseRatchet.setChains at hp
    simp only [List.mem_filter] at hp
    obtain ⟨hp1, _⟩ := hp
    simp only [List.mem_append, List.mem_filter, List.mem_singleton] at hp1
    rcases hp1 with ⟨hp2, _⟩ | hp3
    · exact hb p hp2 ch hch
    · subst hp3
      rcases hch with hch | hch <;>
        (simp only [Option.some.injEq] at hch; rw [← hch]; show (0 : Nat) < Std.U64.max; scalar_tac)
  · simp at hadv

/-- On the same shape of maybe-nothing-happened path `maybe_advance_refines`
itself matches on: no agreement output leaves the table untouched, and one
delegates to `advance`'s own preservation above. -/
theorem maybeAdvance_chain_counter_bounded (M : Model.SparseRatchet.State)
    (out : Option Model.SparseRatchet.Output) (M' : Model.SparseRatchet.State)
    (hadv : (match out with | none => some M | some o => Model.SparseRatchet.advance M o) = some M')
    (hb : ChainCounterBounded M.chains) : ChainCounterBounded M'.chains := by
  cases out with
  | none => injection hadv with hadv; subst hadv; exact hb
  | some o => exact advance_chain_counter_bounded M o M' hadv hb

/-- `skipMessageKeys` preserves `ChainCounterBounded`, given the counter it
may write (`upto`) is itself below `Std.U64.max` -- true at both call sites
here since `upto` is always a real `U64`'s value less one. Every branch
either leaves the table alone or calls `setChains` once, with the new
entry's receiving side carrying `upto` and its sending side carrying
whatever the found entry already had. -/
theorem skipMessageKeys_chain_counter_bounded (M : Model.SparseRatchet.State) (e upto : Nat)
    (M' : Model.SparseRatchet.State) (hupto : upto < Std.U64.max)
    (hskip : Model.SparseRatchet.skipMessageKeys M e upto = some M')
    (hb : ChainCounterBounded M.chains) : ChainCounterBounded M'.chains := by
  unfold Model.SparseRatchet.skipMessageKeys at hskip
  rcases hfc : Model.SparseRatchet.findChains M e with _ | cs
  · simp [hfc] at hskip
  · simp only [hfc] at hskip
    rcases hcr : cs.receive with _ | ch
    · simp [hcr] at hskip
    · simp only [hcr] at hskip
      split at hskip
      · injection hskip with hskip; subst hskip; exact hb
      · split at hskip
        · simp at hskip
        · split at hskip
          · simp at hskip
          · injection hskip with hskip
            subst hskip
            intro p hp ch hch
            unfold Model.SparseRatchet.setChains at hp
            simp only [List.mem_append, List.mem_filter, List.mem_singleton] at hp
            rcases hp with ⟨hp1, _⟩ | hp2
            · exact hb p hp1 ch hch
            · subst hp2
              rcases hch with hch | hch
              · exact hb (e, cs) (findChains_mem M e cs hfc) ch (Or.inl (by simpa using hch))
              · simp only [Option.some.injEq] at hch
                rw [← hch]; exact hupto

/-- The real state's own per-chain counter bound, correctly scoped to the
input rather than to every value the type can hold, carries over to a
`ChainCounterBounded` fact about the model state it refines -- the bridge
that lets `send_refines`/`receive_refines_continuation` reach the model-level
preservation lemmas above from the real hypothesis a caller actually
supplies. -/
theorem chainCounterBounded_of_real {s : State} {m : Model.SparseRatchet.State}
    (hrel : StateRefines s m)
    (hcounter : ∀ p ∈ s.chains.val, ∀ ch : Chain,
      (p.2.send = some ch ∨ p.2.receive = some ch) → ch.n.val < Std.U64.max) :
    ChainCounterBounded m.chains := by
  intro p hp ch hch
  rw [← hrel.chains] at hp
  simp only [List.mem_map] at hp
  obtain ⟨q, hq, hqeq⟩ := hp
  subst hqeq
  simp only [chainsEntryOf, chainsOf] at hch
  rcases hch with hch | hch
  · simp only [Option.map_eq_some_iff] at hch
    obtain ⟨rch, hrch, hrcheq⟩ := hch
    have := hcounter q hq rch (Or.inl hrch)
    rw [← hrcheq]; simp only [chainOf]; exact this
  · simp only [Option.map_eq_some_iff] at hch
    obtain ⟨rch, hrch, hrcheq⟩ := hch
    have := hcounter q hq rch (Or.inr hrch)
    rw [← hrcheq]; simp only [chainOf]; exact this

/-- The saturating addition at its value, given room: the same fact
`T3.lean`'s own `saturating_add_val` states for `U32`, restated for `U64`
since each scalar width is its own instance. -/
theorem saturating_add_val (x y : Std.U64) :
    (UScalar.saturating_add x y).val = min U64.max (x.val + y.val) := by
  simp only [UScalar.saturating_add, UScalar.val, BitVec.toNat_ofNat]
  have h : min (UScalar.max UScalarTy.U64) (x.val + y.val) < 2 ^ UScalarTy.U64.numBits := by
    have := Nat.min_le_left (UScalar.max UScalarTy.U64) (x.val + y.val)
    simp only [UScalar.max, UScalarTy.numBits] at *
    omega
  simpa [U64.max] using Nat.mod_eq_of_lt h

/-! ## `set_chains` refines the model's -/

theorem set_chains_refines (hret : VecRetainAgrees)
    {s : State} {m : Model.SparseRatchet.State} (hrel : StateRefines s m)
    (e : Std.U64) (c : Chains) (hroom : s.chains.val.length < Usize.max) :
    State.set_chains s e c ⦃ fun r =>
      StateRefines r (Model.SparseRatchet.setChains m e.val (chainsOf c)) ⦄ := by
  unfold State.set_chains
  obtain ⟨v, hv, hveq⟩ := hret Global
    State.set_chains.closure.Insts.CoreOpsFunctionFnMutTupleSharedPairU64ChainsBool
    s.chains e (fun x => x.1 != e) (fun _ => rfl)
  simp only [hv]
  have hflen : (s.chains.val.filter (fun x => x.1 != e)).length ≤ s.chains.val.length :=
    List.length_filter_le _ _
  step*
  refine ⟨hrel.rk, hrel.epoch, ?_, hrel.skipped, hrel.direction⟩
  simp only [Model.SparseRatchet.setChains]
  rw [← hrel.chains, v1_post, List.map_append, hveq]
  congr 1
  exact List.filter_map_comm s.chains.val chainsEntryOf (fun x => x.1 != e)
    (fun p => !(p.1 == e.val)) (fun x => by
      simp only [chainsEntryOf]
      by_cases h : x.1 = e
      · simp [h]
      · have h2 : x.1.val ≠ e.val := fun hc => h (by scalar_tac)
        have hb : (x.1 != e) = true := by simpa [bne_iff_ne]
        have hb2 : (x.1.val == e.val) = false := by simpa [beq_eq_false_iff_ne]
        simp [hb, hb2])

/-! ## `clear_old_epochs` refines the model's -/

theorem clear_old_epochs_refines (hret : VecRetainAgrees)
    {s : State} {m : Model.SparseRatchet.State} (hrel : StateRefines s m)
    (current : Std.U64)
    (hcb : ∀ p ∈ s.chains.val, p.1.val + Model.SparseRatchet.epochsKept ≤ Std.U64.max)
    (hsb : ∀ sk ∈ s.skipped.val, sk.epoch.val + Model.SparseRatchet.epochsKept ≤ Std.U64.max) :
    State.clear_old_epochs s current ⦃ fun r =>
      StateRefines r (Model.SparseRatchet.clearOldEpochs m current.val) ⦄ := by
  unfold State.clear_old_epochs
  obtain ⟨v, hv, hveq⟩ := hret Global
    State.clear_old_epochs.closure.Insts.CoreOpsFunctionFnMutTupleSharedPairU64ChainsBool
    s.chains current (fun x => current < x.1.saturating_add EPOCHS_KEPT)
    (fun _ => rfl)
  obtain ⟨v1, hv1, hv1eq⟩ := hret Global
    State.clear_old_epochs.closure_1.Insts.CoreOpsFunctionFnMutTupleSharedSkippedBool
    s.skipped current (fun x => current < x.epoch.saturating_add EPOCHS_KEPT)
    (fun _ => rfl)
  simp only [hv, hv1]
  step*
  refine ⟨hrel.rk, hrel.epoch, ?_, ?_, hrel.direction⟩
  · show List.map chainsEntryOf v.val = (Model.SparseRatchet.clearOldEpochs m current.val).chains
    rw [Model.SparseRatchet.clearOldEpochs, ← hrel.chains, hveq]
    apply List.filter_map_comm_mem s.chains.val chainsEntryOf
    intro x hx
    have hxb := hcb x hx
    simp only [chainsEntryOf, Model.SparseRatchet.epochsKept] at hxb ⊢
    have heps : (EPOCHS_KEPT : Std.U64).val = 2 := by simp [global_simps]
    have hsat : (x.1.saturating_add EPOCHS_KEPT).val = x.1.val + 2 := by
      rw [saturating_add_val, heps]
      omega
    by_cases hlt : current < x.1.saturating_add EPOCHS_KEPT
    · have hc : current.val < (x.1.saturating_add EPOCHS_KEPT).val := hlt
      rw [hsat] at hc
      simp [hlt, hc]
    · have hge : ¬ current.val < (x.1.saturating_add EPOCHS_KEPT).val := hlt
      rw [hsat] at hge
      simp [hlt, hge]
  · show List.map skippedOf v1.val = (Model.SparseRatchet.clearOldEpochs m current.val).skipped
    rw [Model.SparseRatchet.clearOldEpochs, ← hrel.skipped, hv1eq]
    apply List.filter_map_comm_mem s.skipped.val skippedOf
    intro x hx
    have hxb := hsb x hx
    simp only [skippedOf, Model.SparseRatchet.epochsKept] at hxb ⊢
    have heps : (EPOCHS_KEPT : Std.U64).val = 2 := by simp [global_simps]
    have hsat : (x.epoch.saturating_add EPOCHS_KEPT).val = x.epoch.val + 2 := by
      rw [saturating_add_val, heps]
      omega
    by_cases hlt : current < x.epoch.saturating_add EPOCHS_KEPT
    · have hc : current.val < (x.epoch.saturating_add EPOCHS_KEPT).val := hlt
      rw [hsat] at hc
      simp [hlt, hc]
    · have hge : ¬ current.val < (x.epoch.saturating_add EPOCHS_KEPT).val := hlt
      rw [hsat] at hge
      simp [hlt, hge]

/-! ## `advance`/`maybe_advance` refine the model's -/

/-- A translated agreement output as the model's. -/
def outputOf (o : Output) : Model.SparseRatchet.Output := ⟨o.key_epoch.val, keyOf o.key⟩

theorem advance_refines (hkr : SpqrHkdfAgrees) (hz96 : ZeroizingRoundTrips96)
    (hret : VecRetainAgrees)
    (hz : Tacenta.SpqrT1.ZeroizeTotal)
    {s : State} {m : Model.SparseRatchet.State} (hrel : StateRefines s m)
    (out : Output)
    (hepoch : s.epoch.val < Std.U64.max)
    (hroom : s.chains.val.length + 1 < Usize.max)
    (hcb : ∀ p ∈ s.chains.val, p.1.val + Model.SparseRatchet.epochsKept ≤ Std.U64.max)
    (hsb : ∀ sk ∈ s.skipped.val, sk.epoch.val + Model.SparseRatchet.epochsKept ≤ Std.U64.max)
    (hnewb : out.key_epoch.val + Model.SparseRatchet.epochsKept ≤ Std.U64.max) :
    State.advance s out ⦃ fun r =>
      match Model.SparseRatchet.advance m (outputOf out) with
      | none => r.1 = core.result.Result.Err SpqrError.EpochOutOfOrder ∧ r.2 = s
      | some m' => r.1 = core.result.Result.Ok () ∧ StateRefines r.2 m' ⦄ := by
  unfold State.advance
  -- **The epoch increment is a `checked_add`, so the code has three
  -- branches.** The exhaustion branch cannot arise here: `hepoch` is exactly
  -- the hypothesis that excludes it. So exhaustion is
  -- *refuted* rather than refined, which is the honest shape -- the model
  -- counts in unbounded naturals and has no saturated counter to refine
  -- against. Binding the successor as `i` keeps the two branches below
  -- untouched.
  rcases hadd : s.epoch.checked_add 1#u64 with _ | i
  · exfalso
    have hspec := U64.checked_add_bv_spec s.epoch 1#u64
    rw [hadd] at hspec
    simp_all
    omega
  simp only [lift]
  have i_post : i.val = s.epoch.val + 1 := by
    have hspec := U64.checked_add_bv_spec s.epoch 1#u64
    rw [hadd] at hspec
    -- The spec is a three-way conjunction (in range, the value, the bitvector);
    -- only the middle conjunct is the equation the branches below use.
    exact hspec.2.1
  step*
  · -- The real code took the mismatch branch: both sides reject.
    rename_i hmis
    have hi : i.val = s.epoch.val + 1 := i_post
    have hne : out.key_epoch ≠ i := by simpa using hmis
    have hcond : ¬ (out.key_epoch.val = m.epoch + 1) := by
      rw [← hrel.epoch]
      intro hc
      exact hne (UScalar.eq_of_val_eq (by omega))
    simp [Model.SparseRatchet.advance, outputOf, hcond]
  · -- The real code took the match branch: fold the secret in.
    rename_i hmatch
    have hi : i.val = s.epoch.val + 1 := i_post
    have heq : out.key_epoch = i := UScalar.eq_of_val_eq (by simpa using hmatch)
    have hcond : out.key_epoch.val = m.epoch + 1 := by
      rw [← hrel.epoch, heq]
      exact hi
    simp only [Model.SparseRatchet.advance, outputOf, if_pos hcond]
    step with kdf_rk_refines hkr hz96 s.rk out.key
    have hrk : keyOf rk = (Model.SparseRatchet.kdfRk m.rk (keyOf out.key)).1 := by
      rw [← hrel.rk]; exact congrArg Prod.fst rk_post
    have hk1 : keyOf k1 = (Model.SparseRatchet.kdfRk m.rk (keyOf out.key)).2.1 := by
      rw [← hrel.rk]; exact congrArg (Prod.fst ∘ Prod.snd) rk_post
    have hk2 : keyOf k2 = (Model.SparseRatchet.kdfRk m.rk (keyOf out.key)).2.2 := by
      rw [← hrel.rk]; exact congrArg (Prod.snd ∘ Prod.snd) rk_post
    have hmdir := hrel.direction
    match hdir : s.direction with
    | .A2b =>
      simp only
      have hmdir' : m.direction = Model.SparseRatchet.Direction.a2b := by
        rw [← hmdir, hdir]; rfl
      step*
      have hrel1 : StateRefines
          { s with rk := rk, epoch := out.key_epoch, direction := Direction.A2b }
          { m with rk := (Model.SparseRatchet.kdfRk m.rk (keyOf out.key)).1, epoch := out.key_epoch.val } :=
        ⟨hrk, rfl, hrel.chains, hrel.skipped, hmdir'.symm⟩
      have hroom' : s.chains.val.length < Usize.max := by omega
      obtain ⟨_, hzr⟩ := hz (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes) s.rk
      simp only [hzr]
      step*
      step with set_chains_refines hret hrel1 out.key_epoch
        { send := some { ck := k1, n := 0#u64 }, receive := some { ck := k2, n := 0#u64 } } hroom'
      rename_i self1_post
      have hcbm : ∀ q ∈ m.chains, q.1 + Model.SparseRatchet.epochsKept ≤ Std.U64.max := by
        rw [← hrel.chains]
        intro q hq
        simp only [List.mem_map] at hq
        obtain ⟨p', hp', hpeq⟩ := hq
        rw [← hpeq]
        simpa [chainsEntryOf] using hcb p' hp'
      have hcb1 : ∀ p ∈ self1.chains.val, p.1.val + Model.SparseRatchet.epochsKept ≤ Std.U64.max := by
        intro p hp
        have hmem : chainsEntryOf p ∈ self1.chains.val.map chainsEntryOf := List.mem_map_of_mem hp
        rw [self1_post.chains, Model.SparseRatchet.setChains] at hmem
        have hb := setChains_bound m.chains out.key_epoch.val
          (chainsOf { send := some { ck := k1, n := 0#u64 }, receive := some { ck := k2, n := 0#u64 } })
          hcbm hnewb (chainsEntryOf p) hmem
        simpa [chainsEntryOf] using hb
      have hsb1 : ∀ sk ∈ self1.skipped.val, sk.epoch.val + Model.SparseRatchet.epochsKept ≤ Std.U64.max := by
        intro sk hsk
        have hmem : skippedOf sk ∈ self1.skipped.val.map skippedOf := List.mem_map_of_mem hsk
        rw [self1_post.skipped, ← hrel.skipped] at hmem
        obtain ⟨sk', hsk', hskeq⟩ := List.mem_map.mp hmem
        have hep : sk'.epoch.val = sk.epoch.val := congrArg Prod.fst hskeq
        rw [← hep]
        exact hsb sk' hsk'
      step with clear_old_epochs_refines hret self1_post out.key_epoch hcb1 hsb1
      rename_i self2_post
      simpa [chainsOf, chainOf, hk1, hk2, hmdir'] using self2_post
    -- (B2a branch below)
    | .B2a =>
      simp only
      have hmdir' : m.direction = Model.SparseRatchet.Direction.b2a := by
        rw [← hmdir, hdir]; rfl
      step*
      have hrel1 : StateRefines
          { s with rk := rk, epoch := out.key_epoch, direction := Direction.B2a }
          { m with rk := (Model.SparseRatchet.kdfRk m.rk (keyOf out.key)).1, epoch := out.key_epoch.val } :=
        ⟨hrk, rfl, hrel.chains, hrel.skipped, hmdir'.symm⟩
      have hroom' : s.chains.val.length < Usize.max := by omega
      obtain ⟨_, hzr⟩ := hz (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes) s.rk
      simp only [hzr]
      step*
      step with set_chains_refines hret hrel1 out.key_epoch
        { send := some { ck := k2, n := 0#u64 }, receive := some { ck := k1, n := 0#u64 } } hroom'
      rename_i self1_post
      have hcbm : ∀ q ∈ m.chains, q.1 + Model.SparseRatchet.epochsKept ≤ Std.U64.max := by
        rw [← hrel.chains]
        intro q hq
        simp only [List.mem_map] at hq
        obtain ⟨p', hp', hpeq⟩ := hq
        rw [← hpeq]
        simpa [chainsEntryOf] using hcb p' hp'
      have hcb1 : ∀ p ∈ self1.chains.val, p.1.val + Model.SparseRatchet.epochsKept ≤ Std.U64.max := by
        intro p hp
        have hmem : chainsEntryOf p ∈ self1.chains.val.map chainsEntryOf := List.mem_map_of_mem hp
        rw [self1_post.chains, Model.SparseRatchet.setChains] at hmem
        have hb := setChains_bound m.chains out.key_epoch.val
          (chainsOf { send := some { ck := k2, n := 0#u64 }, receive := some { ck := k1, n := 0#u64 } })
          hcbm hnewb (chainsEntryOf p) hmem
        simpa [chainsEntryOf] using hb
      have hsb1 : ∀ sk ∈ self1.skipped.val, sk.epoch.val + Model.SparseRatchet.epochsKept ≤ Std.U64.max := by
        intro sk hsk
        have hmem : skippedOf sk ∈ self1.skipped.val.map skippedOf := List.mem_map_of_mem hsk
        rw [self1_post.skipped, ← hrel.skipped] at hmem
        obtain ⟨sk', hsk', hskeq⟩ := List.mem_map.mp hmem
        have hep : sk'.epoch.val = sk.epoch.val := congrArg Prod.fst hskeq
        rw [← hep]
        exact hsb sk' hsk'
      step with clear_old_epochs_refines hret self1_post out.key_epoch hcb1 hsb1
      rename_i self2_post
      simpa [chainsOf, chainOf, hk1, hk2, hmdir'] using self2_post

theorem maybe_advance_refines (hkr : SpqrHkdfAgrees) (hz96 : ZeroizingRoundTrips96)
    (hret : VecRetainAgrees)
    (hz : Tacenta.SpqrT1.ZeroizeTotal)
    {s : State} {m : Model.SparseRatchet.State} (hrel : StateRefines s m)
    (out : Option Output)
    (hepoch : s.epoch.val < Std.U64.max)
    (hroom : s.chains.val.length + 1 < Usize.max)
    (hcb : ∀ p ∈ s.chains.val, p.1.val + Model.SparseRatchet.epochsKept ≤ Std.U64.max)
    (hsb : ∀ sk ∈ s.skipped.val, sk.epoch.val + Model.SparseRatchet.epochsKept ≤ Std.U64.max)
    (hnewb : ∀ o : Output, out = some o →
      o.key_epoch.val + Model.SparseRatchet.epochsKept ≤ Std.U64.max) :
    State.maybe_advance s out ⦃ fun r =>
      match (match out with
        | none => some m
        | some o => Model.SparseRatchet.advance m (outputOf o)) with
      | none => ∃ o, out = some o ∧
          r.1 = core.result.Result.Err SpqrError.EpochOutOfOrder ∧ r.2 = s
      | some m' => r.1 = core.result.Result.Ok () ∧ StateRefines r.2 m' ⦄ := by
  unfold State.maybe_advance
  match out with
  | none => simp [hrel]
  | some o =>
    simp only []
    refine Std.WP.spec_mono (advance_refines hkr hz96 hret hz hrel o hepoch hroom hcb hsb (hnewb o rfl)) ?_
    intro r hr
    rcases hcase : Model.SparseRatchet.advance m (outputOf o) with _ | m' <;>
      simp only [hcase] at hr ⊢
    · exact ⟨o, rfl, hr⟩
    · exact hr

/-! ## `send` refines the model's -/

theorem send_refines (hkr : SpqrHkdfAgrees)
    (hz96 : ZeroizingRoundTrips96) (hz64 : ZeroizingRoundTrips64) (hret : VecRetainAgrees)
    (hz : Tacenta.SpqrT1.ZeroizeTotal) (hopt : Tacenta.SpqrT1.OptionCloneTotal)
    {s : State} {m : Model.SparseRatchet.State} (hrel : StateRefines s m)
    (sending_epoch : Std.U64) (out : Option Output)
    (hepoch : s.epoch.val < Std.U64.max)
    (hroom : s.chains.val.length + 1 < Usize.max)
    (hcb : ∀ p ∈ s.chains.val, p.1.val + Model.SparseRatchet.epochsKept ≤ Std.U64.max)
    (hsb : ∀ sk ∈ s.skipped.val, sk.epoch.val + Model.SparseRatchet.epochsKept ≤ Std.U64.max)
    (hnewb : ∀ o : Output, out = some o →
      o.key_epoch.val + Model.SparseRatchet.epochsKept ≤ Std.U64.max)
    (hcounter : ∀ p ∈ s.chains.val, ∀ ch : Chain,
      (p.2.send = some ch ∨ p.2.receive = some ch) → ch.n.val < Std.U64.max) :
    State.send s sending_epoch out ⦃ fun r =>
      (∀ n mk, r.1 = core.result.Result.Ok (n, mk) →
        ∃ m', Model.SparseRatchet.send m sending_epoch.val (out.map outputOf)
            = some (m', n.val, keyOf mk)
          ∧ StateRefines r.2 m')
      ∧ (∀ e, r.1 = core.result.Result.Err e →
          Model.SparseRatchet.send m sending_epoch.val (out.map outputOf) = none) ⦄ := by
  unfold State.send
  step with maybe_advance_refines hkr hz96 hret hz hrel out hepoch hroom hcb hsb hnewb
  have hbridge : (match out with | none => some m | some o => Model.SparseRatchet.advance m (outputOf o))
      = (match Option.map outputOf out with | none => some m | some o => Model.SparseRatchet.advance m o) := by
    cases out <;> rfl
  rcases hsc : (match out with
      | none => some m | some o => Model.SparseRatchet.advance m (outputOf o)) with _ | m'
  · -- The model's `maybe_advance` also rejects: the real code must reject too.
    have hsc' : (match Option.map outputOf out with
        | none => some m | some o => Model.SparseRatchet.advance m o) = none := by
      rw [← hbridge]; exact hsc
    rw [hsc] at r_post
    obtain ⟨o, hoeq, hrerr, hself1eq⟩ := r_post
    rw [hrerr] at *
    step*
    refine ⟨?_, ?_⟩
    · intro n mk hcon; rw [r1_post3] at hcon; injection hcon
    · intro e he
      simp_all [Model.SparseRatchet.send]
  · -- The model's `maybe_advance` succeeds with `m'`: proceed to look up the chain.
    have hsc' : (match Option.map outputOf out with
        | none => some m | some o => Model.SparseRatchet.advance m o) = some m' := by
      rw [← hbridge]; exact hsc
    rw [hsc] at r_post
    obtain ⟨hrok, hself1⟩ := r_post
    rw [hrok] at *
    step*
    · -- No chains for this epoch.
      rename_i hoeq
      have hfeq : (self1.chains.val.map chainsEntryOf).find? (fun p => p.1 == sending_epoch.val) = none := by
        have h2 := o_post
        rw [hoeq] at h2
        simpa using h2.symm
      refine ⟨?_, ?_⟩
      · intro n mk hcon; injection hcon
      · intro e he
        have hfindeq : Model.SparseRatchet.findChains m' sending_epoch.val = none := by
          simp [Model.SparseRatchet.findChains, ← hself1.chains, hfeq]
        rcases hout : out with _ | o
        · rw [hout] at hsc
          simp only [Option.some.injEq] at hsc
          simp [Model.SparseRatchet.send, hsc, hfindeq]
        · rw [hout] at hsc
          simp [Model.SparseRatchet.send, hsc, hfindeq]
    · -- Chains for this epoch exist: clone them and check the sending side.
      rename_i cs hoeq
      have hfindeq : Model.SparseRatchet.findChains m' sending_epoch.val = some (chainsOf cs) := by
        have h2 := o_post
        rw [hoeq] at h2
        simp only [Model.SparseRatchet.findChains, ← hself1.chains]
        simpa using h2.symm
      step with Tacenta.SpqrT1.chains_clone_spec hopt cs
      rename_i cs1_post
      rcases hcss1 : cs1.send with _ | ch
      · -- This chain has been retired.
        have hcss : cs.send = none := by rw [← cs1_post]; exact hcss1
        refine ⟨?_, ?_⟩
        · intro n mk hcon; injection hcon
        · intro e he
          have hcssnone : (chainsOf cs).send = none := by simp [chainsOf, hcss]
          rcases hout : out with _ | o
          · rw [hout] at hsc
            simp only [Option.some.injEq] at hsc
            simp [Model.SparseRatchet.send, hsc, hfindeq, hcssnone]
          · rw [hout] at hsc
            simp [Model.SparseRatchet.send, hsc, hfindeq, hcssnone]
      · -- Ready to send: derive the next chain key and message key.
        have hcss : cs.send = some ch := by rw [← cs1_post]; exact hcss1
        step with Tacenta.SpqrT1.chain_clone_spec ch
        rename_i r r_post
        have hchsend : (chainsOf cs).send = some (chainOf ch) := by simp [chainsOf, hcss]
        have hnval : ch.n.val < Std.U64.max := by
          have hcb0 : ChainCounterBounded m.chains := chainCounterBounded_of_real hrel hcounter
          have hcb1 : ChainCounterBounded m'.chains :=
            maybeAdvance_chain_counter_bounded m (Option.map outputOf out) m' hsc' hcb0
          have hmem := findChains_mem m' sending_epoch.val (chainsOf cs) hfindeq
          have := hcb1 (sending_epoch.val, chainsOf cs) hmem (chainOf ch) (Or.inl hchsend)
          simpa [chainOf] using this
        -- **The message number is a `checked_add`.** The extra
        -- branch is refuted by `hnval` just above, which is what `hcounter`
        -- was carried for: a chain whose counter is already at the maximum
        -- cannot be reached from a state satisfying the theorem's hypotheses.
        -- The model counts in unbounded naturals, so there is nothing there for
        -- exhaustion to refine against, and refutation is the right shape.
        rcases hadd : r.n.checked_add 1#u64 with _ | n
        · exfalso
          have hspec := U64.checked_add_bv_spec r.n 1#u64
          rw [hadd] at hspec
          simp_all
          omega
        simp only [lift]
        -- `step*` would introduce this alongside the binder; binding the
        -- successor by hand means supplying it by hand.
        have n_post : n.val = r.n.val + 1 := by
          have hspec := U64.checked_add_bv_spec r.n 1#u64
          rw [hadd] at hspec
          exact hspec.2.1
        step*
        step with kdf_ck_refines hkr hz64 r.ck n
        have hckeq : keyOf r.ck = (chainOf ch).ck := by simp [chainOf, ← r_post]
        step with hopt Chain.Insts.CoreCloneClone cs1.receive
          (fun x _ => Tacenta.SpqrT1.chain_clone_spec x)
        have hroom2 : self1.chains.val.length < Usize.max := by
          have hlen : self1.chains.val.length = m'.chains.length := by
            rw [← List.length_map chainsEntryOf, hself1.chains]
          have hmlen : m'.chains.length ≤ m.chains.length + 1 := by
            rcases hout2 : out with _ | o
            · rw [hout2] at hsc; simp only [Option.some.injEq] at hsc; rw [← hsc]; omega
            · rw [hout2] at hsc; exact advance_chains_len_le m (outputOf o) m' hsc
          have hslen : m.chains.length = s.chains.val.length := by
            rw [← List.length_map chainsEntryOf, hrel.chains]
          omega
        step with set_chains_refines hret hself1 sending_epoch
          { send := some { ck := next, n := n }, receive := o2 } hroom2
        rename_i self2_post
        refine ⟨?_, ?_⟩
        · intro n1 mk1 hcon
          simp only [core.result.Result.Ok.injEq, Prod.mk.injEq] at hcon
          obtain ⟨hn1, hmk1⟩ := hcon
          subst hn1; subst hmk1
          have hnexteq : keyOf next = (Model.SparseRatchet.kdfCk (keyOf r.ck) n.val).1 :=
            congrArg Prod.fst next_post
          have hmkeq : keyOf mk = (Model.SparseRatchet.kdfCk (keyOf r.ck) n.val).2 :=
            congrArg Prod.snd next_post
          have hnval2 : n.val = ch.n.val + 1 := by rw [n_post, r_post]
          refine ⟨Model.SparseRatchet.setChains m' sending_epoch.val
              (chainsOf { send := some { ck := next, n := n }, receive := o2 }), ?_, ?_⟩
          · rcases hout : out with _ | o
            · rw [hout] at hsc
              simp only [Option.some.injEq] at hsc
              simp [Model.SparseRatchet.send, hsc, hfindeq, chainOf, chainsOf,
                r_post, hnval2, hnexteq, hmkeq, hcss, o2_post, cs1_post]
            · rw [hout] at hsc
              simp [Model.SparseRatchet.send, hsc, hfindeq, chainOf, chainsOf,
                r_post, hnval2, hnexteq, hmkeq, hcss, o2_post, cs1_post]
          · exact self2_post
        · intro e he; injection he

/-! ## `try_skipped` refines the model's

The scan removes at the first matching index; the model deletes every match.
The two agree only given at most one match for the `(e, n)` looked up, so
`hone` carries that bound in, the same way `T3.lean`'s ratchet skipped-key scan
needed it -- discharged there by the store staying a map, which this crate's
own T2 correctness proof would supply for a real caller. -/

theorem try_skipped_loop_refines (hrm : VecRemoveAgrees) (st : State) (e n : Std.U64) (i : Usize)
    (hone : ((st.skipped.val.map skippedOf).filter
      (fun x => x.1 == e.val && x.2.1 == n.val)).length ≤ 1)
    (hpre : ((st.skipped.val.map skippedOf).take i.val).filter
              (fun x => x.1 == e.val && x.2.1 == n.val) = []) :
    State.try_skipped_loop st e n i ⦃ fun r =>
      r.2.2.2.1 = st.chains ∧ r.2.1 = st.rk ∧ r.2.2.1 = st.epoch ∧ r.2.2.2.2.2 = st.direction ∧
      match (st.skipped.val.map skippedOf).find? (fun x => x.1 == e.val && x.2.1 == n.val) with
      | none => r.1 = none ∧ r.2.2.2.2.1 = st.skipped
      | some x => ∃ key : Array Std.U8 32#usize, r.1 = some key ∧ keyOf key = x.2.2 ∧
          r.2.2.2.2.1.val.map skippedOf
            = (st.skipped.val.map skippedOf).filter (fun y => !(y.1 == e.val && y.2.1 == n.val)) ⦄ := by
  unfold State.try_skipped_loop
  apply loop.spec_decr_nat
    (measure := fun j => st.skipped.val.length - j.val)
    (inv := fun j => ((st.skipped.val.map skippedOf).take j.val).filter
      (fun x => x.1 == e.val && x.2.1 == n.val) = [])
  · rintro j hinv
    obtain ⟨⟨removed, v'⟩, hrm', hval, herase⟩ := hrm Global st.skipped j
    simp only [State.try_skipped_loop.body]
    by_cases hlt : j.val < st.skipped.val.length <;> step*
    · -- The epoch and the number both match: this is the one, remove it.
      rename_i heq1 heq2
      simp only [hrm']
      have hjm : j.val < (st.skipped.val.map skippedOf).length := by simpa using hlt
      have hpj : (fun x : Nat × Nat × Model.State.Key => x.1 == e.val && x.2.1 == n.val)
          (st.skipped.val.map skippedOf)[j.val] = true := by
        rw [List.getElem_map, ← s_post, skippedOf]; simp [heq1, heq2]
      have hsp : (st.skipped.val.map skippedOf)
          = ((st.skipped.val.map skippedOf).take j.val)
            ++ (st.skipped.val.map skippedOf)[j.val]
              :: (st.skipped.val.map skippedOf).drop (j.val + 1) := by
        rw [← List.drop_eq_getElem_cons hjm, List.take_append_drop]
      have hvaleq : removed = st.skipped.val[j.val]'(by simpa using hlt) := hval _
      refine ⟨rfl, rfl, rfl, rfl, ?_⟩
      rw [hsp, find?_eq_of_split _ _ _ _ hinv hpj]
      refine ⟨removed.key, rfl, ?_, ?_⟩
      · rw [hvaleq, List.getElem_map]; simp [skippedOf]
      · have herase' : v'.val = st.skipped.val.eraseIdx j.val := herase
        rw [herase', map_eraseIdx, ← hsp]
        exact (filter_not_eq_eraseIdx _ (st.skipped.val.map skippedOf) j.val hjm hpj hone).symm
    · -- The number differs: keep scanning past it.
      rename_i heq1 heq2
      have hjm : j.val < (st.skipped.val.map skippedOf).length := by simpa using hlt
      have hnm : (fun x : Nat × Nat × Model.State.Key => x.1 == e.val && x.2.1 == n.val)
          (st.skipped.val.map skippedOf)[j.val] = false := by
        rw [List.getElem_map, ← s_post]
        simp only [skippedOf, heq1, Bool.and_eq_false_iff]
        right
        simpa [beq_eq_false_iff_ne] using heq2
      rw [List.getElem_map] at hnm
      rw [i2_post]
      rw [List.take_add_one, List.getElem?_eq_getElem hjm, List.filter_append, hinv]
      simp [hnm]
      scalar_tac
    · -- The epoch differs: keep scanning past it.
      rename_i heq1
      have hjm : j.val < (st.skipped.val.map skippedOf).length := by simpa using hlt
      have hnm : (fun x : Nat × Nat × Model.State.Key => x.1 == e.val && x.2.1 == n.val)
          (st.skipped.val.map skippedOf)[j.val] = false := by
        rw [List.getElem_map, ← s_post]
        simp only [skippedOf, Bool.and_eq_false_iff]
        left
        simpa [beq_eq_false_iff_ne] using heq1
      rw [List.getElem_map] at hnm
      rw [i2_post]
      rw [List.take_add_one, List.getElem?_eq_getElem hjm, List.filter_append, hinv]
      simp [hnm]
      scalar_tac
    · -- The scan is spent: nothing matched anywhere.
      rw [find?_eq_none_of_scanned _ _ j.val (by simpa using hlt) hinv]
      simp
  · exact hpre

/-- `State.try_skipped` refines `Model.SparseRatchet.trySkipped`: it takes a stored
key for this epoch and number, removing it, given at most one entry can match. -/
theorem try_skipped_refines (hrm : VecRemoveAgrees) {s : State} {m : Model.SparseRatchet.State}
    (hrel : StateRefines s m) (e n : Std.U64)
    (hone : (m.skipped.filter (fun x => x.1 == e.val && x.2.1 == n.val)).length ≤ 1) :
    State.try_skipped s e n ⦃ fun r =>
      match Model.SparseRatchet.trySkipped m e.val n.val with
      | none => r.1 = none ∧ StateRefines r.2 m
      | some p => ∃ key, r.1 = some key ∧ keyOf key = p.2 ∧ StateRefines r.2 p.1 ⦄ := by
  unfold State.try_skipped
  have hone' : ((s.skipped.val.map skippedOf).filter
      (fun x => x.1 == e.val && x.2.1 == n.val)).length ≤ 1 := by
    rw [hrel.skipped]; exact hone
  have h := try_skipped_loop_refines hrm s e n 0#usize hone' (by simp)
  step with h
  rw [hrel.skipped] at o_post5
  rcases hfind : m.skipped.find? (fun x => x.1 == e.val && x.2.1 == n.val) with _ | y
  · simp only [Model.SparseRatchet.trySkipped, hfind]
    rw [hfind] at o_post5
    obtain ⟨hn, hsk⟩ := o_post5
    exact ⟨hn, by rw [o_post2]; exact hrel.rk, by rw [o_post3]; exact hrel.epoch,
      by rw [o_post1]; exact hrel.chains, by rw [hsk]; exact hrel.skipped,
      by rw [o_post4]; exact hrel.direction⟩
  · simp only [Model.SparseRatchet.trySkipped, hfind]
    rw [hfind] at o_post5
    obtain ⟨key, hkeq, hkval, hsk⟩ := o_post5
    exact ⟨key, hkeq, hkval, by rw [o_post2]; exact hrel.rk, by rw [o_post3]; exact hrel.epoch,
      by rw [o_post1]; exact hrel.chains, hsk, by rw [o_post4]; exact hrel.direction⟩

/-! ## `skip_message_keys` refines the model's -/

/-- The model derives exactly `count` keys: one per number walked. Needed to turn
the loop refinement's `map` equality into a length, which is what the guarded
`Vec::append` hypothesis below asks the caller for. -/
theorem deriveInto_snd_length (ck : Model.State.Key) (start count : Nat) :
    (Model.SparseRatchet.skipMessageKeys.deriveInto ck start count).2.length = count := by
  induction count generalizing ck start with
  | zero => simp [Model.SparseRatchet.skipMessageKeys.deriveInto]
  | succ c ih => simp [Model.SparseRatchet.skipMessageKeys.deriveInto, ih]

/-- `Vec::append` returns the concatenation, not just the length `SpqrT1.lean`
stated. An **eighth** constant, distinct from that file's `VecAppendTotal`
per the established per-crate counting rule.

Guarded like `VecAppendTotal` (see its docstring): unguarded, it would be
refutable in Lean and leave `skip_message_keys_refines`,
`receive_refines_continuation` and `receive_refines` provable from `False`. -/
def VecAppendAgrees : Prop :=
  ∀ {T : Type} (A : Type) (v w : alloc.vec.Vec T),
    v.length + w.length ≤ Usize.max →
    ∃ r, alloc.vec.Vec.append A v w = ok r ∧ r.1.val = v.val ++ w.val

theorem VecAppendAgrees.total (h : VecAppendAgrees) : Tacenta.SpqrT1.VecAppendTotal := by
  intro T A v w hlen
  obtain ⟨r, hr, hv⟩ := h A v w hlen
  exact ⟨r, hr, by simp [alloc.vec.Vec.length, hv]⟩

/-- `deriveInto`'s left-peeling recursion splits into two consecutive runs:
however many steps a loop has already taken, and however many remain. Proved
once here rather than reproved at every call, since the real loop below walks
forward one step at a time and needs to relate its progress back to a single
whole-count call to `deriveInto`. -/
theorem deriveInto_split (ck0 : Model.State.Key) (start a b : Nat) :
    Model.SparseRatchet.skipMessageKeys.deriveInto ck0 start (a + b)
      = ((Model.SparseRatchet.skipMessageKeys.deriveInto
            (Model.SparseRatchet.skipMessageKeys.deriveInto ck0 start a).1 (start + a) b).1,
         (Model.SparseRatchet.skipMessageKeys.deriveInto ck0 start a).2 ++
           (Model.SparseRatchet.skipMessageKeys.deriveInto
              (Model.SparseRatchet.skipMessageKeys.deriveInto ck0 start a).1 (start + a) b).2) := by
  induction a generalizing start ck0 with
  | zero => simp [Model.SparseRatchet.skipMessageKeys.deriveInto]
  | succ k ih =>
    have hcomm : k + 1 + b = k + b + 1 := by omega
    rw [hcomm, show start + (k + 1) = start + 1 + k by omega]
    simp only [Model.SparseRatchet.skipMessageKeys.deriveInto]
    rw [ih]
    rfl

theorem deriveInto_split_fst (ck0 : Model.State.Key) (start a b : Nat) :
    (Model.SparseRatchet.skipMessageKeys.deriveInto ck0 start (a + b)).1
      = (Model.SparseRatchet.skipMessageKeys.deriveInto
          (Model.SparseRatchet.skipMessageKeys.deriveInto ck0 start a).1 (start + a) b).1 := by
  rw [deriveInto_split]

theorem deriveInto_split_snd (ck0 : Model.State.Key) (start a b : Nat) :
    (Model.SparseRatchet.skipMessageKeys.deriveInto ck0 start (a + b)).2
      = (Model.SparseRatchet.skipMessageKeys.deriveInto ck0 start a).2 ++
        (Model.SparseRatchet.skipMessageKeys.deriveInto
          (Model.SparseRatchet.skipMessageKeys.deriveInto ck0 start a).1 (start + a) b).2 := by
  rw [deriveInto_split]

/-- The forward-derivation loop refines `deriveInto`: each turn steps the chain
key once via `kdf_ck` and stores the message key passed, exactly the recursive
structure `deriveInto` itself has (confirmed one step at a time via
`deriveInto_split` at `b = 1`). -/
theorem skip_message_keys_loop_refines (hkr : SpqrHkdfAgrees) (hz64 : ZeroizingRoundTrips64)
    (hz : Tacenta.SpqrT1.ZeroizeTotal)
    (e upto : Std.U64) (ck0 : Array Std.U8 32#usize) (derived0 : alloc.vec.Vec Skipped)
    (num0 : Std.U64) (hnum : num0.val ≤ upto.val) (hderived0 : derived0.val = [])
    (hroom : upto.val - num0.val < Usize.max) :
    State.skip_message_keys_loop e upto ck0 derived0 num0 ⦃ fun r =>
      keyOf r.1 = (Model.SparseRatchet.skipMessageKeys.deriveInto
        (keyOf ck0) num0.val (upto.val - num0.val)).1 ∧
      r.2.val.map (fun s => (s.n.val, keyOf s.key))
        = (Model.SparseRatchet.skipMessageKeys.deriveInto
            (keyOf ck0) num0.val (upto.val - num0.val)).2 ∧
      ∀ s ∈ r.2.val, s.epoch = e ⦄ := by
  unfold State.skip_message_keys_loop
  apply loop.spec_decr_nat
    (measure := fun p => upto.val - p.2.2.val)
    (inv := fun p =>
      num0.val ≤ p.2.2.val ∧ p.2.2.val ≤ upto.val ∧
      p.2.1.val.length ≤ p.2.2.val - num0.val ∧
      keyOf p.1 = (Model.SparseRatchet.skipMessageKeys.deriveInto
        (keyOf ck0) num0.val (p.2.2.val - num0.val)).1 ∧
      p.2.1.val.map (fun s => (s.n.val, keyOf s.key))
        = (Model.SparseRatchet.skipMessageKeys.deriveInto
            (keyOf ck0) num0.val (p.2.2.val - num0.val)).2 ∧
      ∀ s ∈ p.2.1.val, s.epoch = e)
  · rintro ⟨ckA, derivedA, numA⟩ ⟨hge, hle, hlenA, hkeq, hlist, hepoch⟩
    dsimp only at hge hle hlenA hkeq hlist hepoch ⊢
    simp only [State.skip_message_keys_loop.body]
    by_cases hlt : numA.val < upto.val <;> step*
    · -- One more turn: step the chain key, zeroize the old one, store the
      -- message key passed.
      obtain ⟨_, hzr⟩ := hz (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes) ckA
      simp only [hzr]
      step with kdf_ck_refines hkr hz64 ckA num1
      have hroom' : derivedA.val.length < Usize.max := by omega
      step with alloc.vec.Vec.push_spec derivedA
        ({ epoch := e, n := num1, key := mk } : Skipped) hroom'
      have hmkeq : keyOf mk = (Model.SparseRatchet.kdfCk (keyOf ckA) num1.val).2 := by
        rw [← next_post]
      have hcount : num1.val - num0.val = numA.val - num0.val + 1 := by omega
      have hstart : num0.val + (numA.val - num0.val) = numA.val := by omega
      have hone : Model.SparseRatchet.skipMessageKeys.deriveInto (keyOf ckA) numA.val 1
          = ((Model.SparseRatchet.kdfCk (keyOf ckA) num1.val).1,
             [(num1.val, (Model.SparseRatchet.kdfCk (keyOf ckA) num1.val).2)]) := by
        simp only [Model.SparseRatchet.skipMessageKeys.deriveInto]
        have hn : numA.val + 1 = num1.val := by omega
        rw [hn]
      have hkey1 : (Model.SparseRatchet.skipMessageKeys.deriveInto
          (keyOf ck0) num0.val (num1.val - num0.val)).1
          = (Model.SparseRatchet.kdfCk (keyOf ckA) num1.val).1 := by
        rw [hcount, deriveInto_split_fst (keyOf ck0) num0.val (numA.val - num0.val) 1,
          ← hkeq, hstart, hone]
      have hlist1 : (Model.SparseRatchet.skipMessageKeys.deriveInto
          (keyOf ck0) num0.val (num1.val - num0.val)).2
          = (Model.SparseRatchet.skipMessageKeys.deriveInto
              (keyOf ck0) num0.val (numA.val - num0.val)).2
            ++ [(num1.val, (Model.SparseRatchet.kdfCk (keyOf ckA) num1.val).2)] := by
        rw [hcount, deriveInto_split_snd (keyOf ck0) num0.val (numA.val - num0.val) 1,
          ← hkeq, hstart, hone]
      refine ⟨by omega, by omega, by rw [derived1_post]; simp; omega, ?_, ?_, ?_, by omega⟩
      · rw [hkey1, ← next_post]
      · rw [hlist1, ← hlist, derived1_post]
        simp only [List.map_append, List.map_singleton, hmkeq]
      · intro s hs
        rw [derived1_post] at hs
        simp only [List.mem_append, List.mem_singleton] at hs
        rcases hs with hs | hs
        · exact hepoch s hs
        · rw [hs]
  · refine ⟨le_refl _, hnum, by simp [hderived0], ?_, ?_, by simp [hderived0]⟩
    · simp [Model.SparseRatchet.skipMessageKeys.deriveInto]
    · simp [Model.SparseRatchet.skipMessageKeys.deriveInto, hderived0]

/-- The real forward-skip limit is the model's. -/
theorem max_skip_agrees : MAX_SKIP.val = Model.SparseRatchet.maxSkip := by native_decide

/-- The real skipped-store limit is the model's. -/
theorem max_skipped_store_agrees :
    MAX_SKIPPED_STORE.val = Model.SparseRatchet.maxSkippedStore := by native_decide

/-- `MAX_SKIP`'s own value, stated as a literal rather than routed through the
model, for the arithmetic that never needs the model side at all. -/
theorem max_skip_val : MAX_SKIP.val = 1000 := by native_decide

/-- `State.skip_message_keys` refines `Model.SparseRatchet.skipMessageKeys`: it
steps the receiving chain forward to `upto`, storing every key passed, and
fails exactly where the model does (no chain, chain retired, too many skipped,
or the store full). -/
theorem skip_message_keys_refines (hkr : SpqrHkdfAgrees) (hz64 : ZeroizingRoundTrips64)
    (hret : VecRetainAgrees)
    (happ : VecAppendAgrees) (hz : Tacenta.SpqrT1.ZeroizeTotal)
    (hopt : Tacenta.SpqrT1.OptionCloneTotal)
    {s : State} {m : Model.SparseRatchet.State} (hrel : StateRefines s m) (e upto : Std.U64)
    (hroom : s.chains.val.length < Usize.max)
    (hskiproom : s.skipped.val.length + MAX_SKIP.val ≤ Usize.max) :
    State.skip_message_keys s e upto ⦃ fun r =>
      match Model.SparseRatchet.skipMessageKeys m e.val upto.val with
      | none => ∃ err, r.1 = core.result.Result.Err err ∧ r.2 = s
      | some m' => r.1 = core.result.Result.Ok () ∧ StateRefines r.2 m' ⦄ := by
  unfold State.skip_message_keys
  step with findChains_refines hrel e
  simp only [Model.SparseRatchet.skipMessageKeys]
  rcases ho : o with _ | cs
  · rw [ho] at o_post
    simp only [Option.map_none] at o_post
    rw [← o_post]
    step*
  · rw [ho] at o_post
    simp only [Option.map_some] at o_post
    rw [← o_post]
    step*
    step with Tacenta.SpqrT1.chains_clone_spec hopt cs
    rw [cs1_post]
    rcases hcsr : cs.receive with _ | ch
    · simp only [chainsOf, hcsr, Option.map_none]
      step*
    · simp only [chainsOf, hcsr, Option.map_some]
      step*
      · -- Already caught up: no derivation needed.
        have hle' : upto.val ≤ (chainOf ch).n := by simp only [chainOf]; scalar_tac
        simp only [hle']
        exact hrel
      · -- Too many skipped.
        have hnotA : ¬ upto.val ≤ (chainOf ch).n := by simp only [chainOf]; scalar_tac
        have hB : upto.val > (chainOf ch).n + Model.SparseRatchet.maxSkip := by
          simp only [chainOf]
          have := max_skip_agrees
          scalar_tac
        simp only [hnotA, hB]
        exact ⟨SpqrError.TooManySkipped, rfl⟩
      · -- The intermediate index arithmetic cannot overflow: the request is
        -- bounded by `MAX_SKIP`, a small constant far under `Usize.max`.
        have hi1 : i1.val = count.val := by
          have := max_skip_val
          rw [i1_post, UScalar.cast_val_eq]
          rcases System.Platform.numBits_eq with hbits | hbits <;> simp_all <;> scalar_tac
        scalar_tac
      · -- The skipped-key store would overflow.
        have hnotA : ¬ upto.val ≤ (chainOf ch).n := by simp only [chainOf]; scalar_tac
        have hnotB : ¬ upto.val > (chainOf ch).n + Model.SparseRatchet.maxSkip := by
          simp only [chainOf]
          have := max_skip_agrees
          scalar_tac
        have hskipeq : s.skipped.val.length = m.skipped.length := by
          rw [← hrel.skipped]; simp
        have hi1 : i1.val = count.val := by
          have := max_skip_val
          rw [i1_post, UScalar.cast_val_eq]
          rcases System.Platform.numBits_eq with hbits | hbits <;> simp_all <;> scalar_tac
        have hC : m.skipped.length + (upto.val - (chainOf ch).n)
            > Model.SparseRatchet.maxSkippedStore := by
          simp only [chainOf]
          have := max_skipped_store_agrees
          rw [← hskipeq]
          scalar_tac
        simp only [hnotA, hnotB, hC]
        exact ⟨SpqrError.SkippedStoreFull, rfl⟩
      · -- Room for the walk: derive the forward keys, retain everything else,
        -- append what was just derived, and replace this epoch's chains.
        have hnotA : ¬ upto.val ≤ (chainOf ch).n := by simp only [chainOf]; scalar_tac
        have hnotB : ¬ upto.val > (chainOf ch).n + Model.SparseRatchet.maxSkip := by
          simp only [chainOf]
          have := max_skip_agrees
          scalar_tac
        have hskipeq : s.skipped.val.length = m.skipped.length := by
          rw [← hrel.skipped]; simp
        have hi1 : i1.val = count.val := by
          have := max_skip_val
          rw [i1_post, UScalar.cast_val_eq]
          rcases System.Platform.numBits_eq with hbits | hbits <;> simp_all <;> scalar_tac
        have hi3 : i3.val = count.val := by
          have := max_skip_val
          rw [i3_post, UScalar.cast_val_eq]
          rcases System.Platform.numBits_eq with hbits | hbits <;> simp_all <;> scalar_tac
        have hnotC : ¬ m.skipped.length + (upto.val - (chainOf ch).n)
            > Model.SparseRatchet.maxSkippedStore := by
          simp only [chainOf]
          have := max_skipped_store_agrees
          rw [← hskipeq]
          scalar_tac
        simp only [hnotA, hnotB, hnotC]
        have hloomprep : (alloc.vec.Vec.with_capacity Skipped i3).val = [] := by
          simp [alloc.vec.Vec.with_capacity, alloc.vec.Vec.new]
        step with skip_message_keys_loop_refines hkr hz64 hz e upto ch1.ck
          (alloc.vec.Vec.with_capacity Skipped i3) ch1.n
          (by scalar_tac) hloomprep (by have := max_skip_val; scalar_tac)
        obtain ⟨v, hv, hveq⟩ := hret Global
          State.skip_message_keys.closure.Insts.CoreOpsFunctionFnMutTupleSharedSkippedBool
          s.skipped (e, ch1.n, upto)
          (fun x => !(x.epoch == e && ch1.n < x.n && x.n ≤ upto))
          (fun x => by
            by_cases h1 : x.epoch = e <;> by_cases h2 : ch1.n < x.n <;> by_cases h3 : x.n ≤ upto <;>
              simp [
                State.skip_message_keys.closure.Insts.CoreOpsFunctionFnMutTupleSharedSkippedBool.call_mut,
                h1, h2, h3] <;>
              (try split) <;>
              simp_all <;>
              first
                | rfl
                | (congr 1; congr 1; scalar_tac)
                | (congr 1; congr 1; simp [h1]))
        simp only [hv]
        have hretain := hveq
        step*
        -- The guard on `append`: the retained store is
        -- no longer than the store it came from; the derived keys number
        -- exactly the count walked (the loop refinement's `map` equality, read
        -- through `deriveInto_snd_length`); that count is at most `MAX_SKIP`
        -- (the source's check, `hnotB`); and `hskiproom` says store plus
        -- `MAX_SKIP` fits. So the two lengths fit together.
        obtain ⟨r, hr, hrveq⟩ := happ Global v derived1 (by
          have hvlen : v.val.length ≤ s.skipped.val.length := by
            rw [hretain]; exact List.length_filter_le _ _
          have hdlen : derived1.val.length = upto.val - ch1.n.val := by
            simpa [List.length_map, deriveInto_snd_length] using congrArg List.length ck_post2
          have hn : (chainOf ch).n = ch1.n.val := by simp [chainOf, ch1_post]
          have := max_skip_agrees
          simp only [alloc.vec.Vec.length]
          scalar_tac)
        simp only [hr]
        step*
        obtain ⟨v1, w⟩ := r
        dsimp only at hrveq ⊢
        step with hopt Chain.Insts.CoreCloneClone cs.send (fun x _ => Tacenta.SpqrT1.chain_clone_spec x)
        have hveq : v.val = s.skipped.val.filter
            (fun x => !(x.epoch == e && ch1.n < x.n && x.n ≤ upto)) := hretain
        have hv1eq : v1.val = v.val ++ derived1.val := hrveq
        have hskipped1 : v1.val.map skippedOf
            = m.skipped.filter
                (fun x => !(x.1 == e.val && (chainOf ch).n < x.2.1 && x.2.1 ≤ upto.val))
              ++ (Model.SparseRatchet.skipMessageKeys.deriveInto (chainOf ch).ck (chainOf ch).n
                    (upto.val - (chainOf ch).n)).2.map (fun p => (e.val, p.1, p.2)) := by
          have hderived1eq : derived1.val.map skippedOf
              = (derived1.val.map (fun s => (s.n.val, keyOf s.key))).map (fun p => (e.val, p.1, p.2)) := by
            rw [List.map_map]
            apply List.map_congr_left
            intro s hs
            simp only [skippedOf, Function.comp]
            rw [ck_post3 s hs]
          rw [hv1eq, List.map_append, hveq, hderived1eq]
          rw [show (chainOf ch).ck = keyOf ch1.ck by simp [chainOf, ch1_post],
            show (chainOf ch).n = ch1.n.val by simp [chainOf, ch1_post], ck_post2]
          congr 1
          rw [← hrel.skipped]
          exact List.filter_map_comm s.skipped.val skippedOf
            (fun x => !(x.epoch == e && ch1.n < x.n && x.n ≤ upto))
            (fun x => !(x.1 == e.val && ch1.n.val < x.2.1 && x.2.1 ≤ upto.val))
            (fun x => by
              simp only [skippedOf, ch1_post]
              congr 1
              congr 1
              congr 1 <;> first | rfl | scalar_tac | simp [UScalar.eq_equiv])
        set newSkipped : List (Nat × Nat × Model.State.Key) :=
          m.skipped.filter
              (fun x => !(x.1 == e.val && (chainOf ch).n < x.2.1 && x.2.1 ≤ upto.val))
            ++ (Model.SparseRatchet.skipMessageKeys.deriveInto (chainOf ch).ck (chainOf ch).n
                  (upto.val - (chainOf ch).n)).2.map (fun p => (e.val, p.1, p.2))
          with hnewSkipped
        have hrel1 : StateRefines { s with skipped := v1 } { m with skipped := newSkipped } :=
          ⟨hrel.rk, hrel.epoch, hrel.chains, hskipped1, hrel.direction⟩
        step with set_chains_refines hret hrel1 e
          ({ send := r, receive := some { ck, n := upto } } : Chains) hroom
        simpa [chainOf, chainsOf, ch1_post, r_post, hnewSkipped, ck_post1] using self1_post

/-! ## `receive` refines the model's -/

/-- The part of `receive` after `maybe_advance`: a stored-key check, a forward
skip, and the receiving chain's own step. Factored out on its own so
`receive_refines` below can call it once rather than duplicating it across
`out`'s two cases. -/
theorem receive_refines_continuation (hkr : SpqrHkdfAgrees) (hz64 : ZeroizingRoundTrips64)
    (hret : VecRetainAgrees)
    (happ : VecAppendAgrees) (hrm : VecRemoveAgrees) (hz : Tacenta.SpqrT1.ZeroizeTotal)
    (hopt : Tacenta.SpqrT1.OptionCloneTotal)
    {self1 : State} {m1 : Model.SparseRatchet.State} (hrel1 : StateRefines self1 m1)
    (receiving_epoch n : Std.U64)
    (hroom : self1.chains.val.length + 1 < Usize.max)
    (hskiproom : self1.skipped.val.length + MAX_SKIP.val ≤ Usize.max)
    (hone : (m1.skipped.filter
      (fun x => x.1 == receiving_epoch.val && x.2.1 == n.val)).length ≤ 1)
    (hccb1 : ChainCounterBounded m1.chains) :
    (do
      let (o, self2) ← State.try_skipped self1 receiving_epoch n
      match o with
      | none =>
        let i ← lift (core.num.U64.saturating_sub n 1#u64)
        let (r1, self3) ← self2.skip_message_keys receiving_epoch i
        let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
        match cf1 with
        | core.ops.control_flow.ControlFlow.Continue _ =>
          let o1 ← self3.find_chains receiving_epoch
          match o1 with
          | none => ok (core.result.Result.Err SpqrError.NoChain, self3)
          | some cs =>
            let cs1 ← Chains.Insts.CoreCloneClone.clone cs
            match cs1.receive with
            | none => ok (core.result.Result.Err SpqrError.ChainRetired, self3)
            | some ch =>
              let ch1 ← Chain.Insts.CoreCloneClone.clone ch
              -- The counter check is a `checked_add`, so this statement
              -- carries the exhaustion branch the generated code has. It
              -- is unreachable under `hccb1` and discharged as such below.
              let o2 ← lift (Std.U64.checked_add ch1.n 1#u64)
              match o2 with
              | none => ok (core.result.Result.Err SpqrError.ChainExhausted, self3)
              | some expected =>
                if n != expected then ok (core.result.Result.Err SpqrError.OutOfOrder, self3)
                else
                  let (next, mk) ← kdf_ck ch1.ck n
                  let o3 ← core.option.Option.Insts.CoreCloneClone.clone
                    Chain.Insts.CoreCloneClone cs1.send
                  let self4 ← self3.set_chains receiving_epoch
                    { send := o3, receive := some { ck := next, n } }
                  ok (core.result.Result.Ok mk, self4)
        | core.ops.control_flow.ControlFlow.Break residual =>
          let r2 ←
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
              (Array Std.U8 32#usize) (core.convert.FromSame SpqrError) residual
          ok (r2, self3)
      | some k => ok (core.result.Result.Ok k, self2)) ⦃ fun r =>
      match
        (match Model.SparseRatchet.trySkipped m1 receiving_epoch.val n.val with
         | some res => some res
         | none =>
           match Model.SparseRatchet.skipMessageKeys m1 receiving_epoch.val (n.val - 1) with
           | none => none
           | some st2 =>
             match Model.SparseRatchet.findChains st2 receiving_epoch.val with
             | none => none
             | some cs =>
               match cs.receive with
               | none => none
               | some ch =>
                 if n.val = ch.n + 1 then
                   some (Model.SparseRatchet.setChains st2 receiving_epoch.val
                     { cs with
                       receive := some
                         { ck := (Model.SparseRatchet.kdfCk ch.ck n.val).1, n := n.val } },
                     (Model.SparseRatchet.kdfCk ch.ck n.val).2)
                 else none) with
      | none => ∃ err, r.1 = core.result.Result.Err err
      | some (m', k) => ∃ key, r.1 = core.result.Result.Ok key ∧ keyOf key = k ∧
          StateRefines r.2 m' ⦄ := by
  step with try_skipped_refines hrm hrel1 receiving_epoch n hone
  rcases hts : Model.SparseRatchet.trySkipped m1 receiving_epoch.val n.val with _ | res
  · rw [hts] at o_post
    obtain ⟨hno, hself2⟩ := o_post
    simp only [hno]
    simp only [lift]
    step*
    have hchainlen1 := congrArg List.length hself2.chains
    have hchainlen2 := congrArg List.length hrel1.chains
    simp only [List.length_map] at hchainlen1 hchainlen2
    have hskiplen1 := congrArg List.length hself2.skipped
    have hskiplen2 := congrArg List.length hrel1.skipped
    simp only [List.length_map] at hskiplen1 hskiplen2
    have hnsub : (core.num.U64.saturating_sub n 1#u64).val = n.val - 1 := by
      unfold core.num.U64.saturating_sub UScalar.saturating_sub UScalar.val
      simp only [BitVec.toNat_ofNat]
      have h1 : (1#u64 : Std.U64).bv.toNat = 1 := by native_decide
      rw [h1]
      simp only [Nat.zero_max]
      have h2 : n.bv.toNat < 2 ^ UScalarTy.U64.numBits := n.bv.isLt
      rw [Nat.mod_eq_of_lt (by omega)]
    step with skip_message_keys_refines hkr hz64 hret happ hz hopt hself2 receiving_epoch
      (core.num.U64.saturating_sub n 1#u64)
      (by scalar_tac) (by scalar_tac)
    step
    rw [hnsub] at r1_post
    rcases hsmk : Model.SparseRatchet.skipMessageKeys m1 receiving_epoch.val (n.val - 1)
      with _ | st2
    · rw [hsmk] at r1_post
      obtain ⟨err, herr, _⟩ := r1_post
      rw [herr] at cf1_post
      simp only [cf1_post]
      exact ⟨_, rfl⟩
    · rw [hsmk] at r1_post
      obtain ⟨hrOk, hself3⟩ := r1_post
      rw [hrOk] at cf1_post
      simp only [cf1_post]
      have hsmklen := skipMessageKeys_chains_len_le m1 receiving_epoch.val (n.val - 1) st2 hsmk
      step with findChains_refines hself3 receiving_epoch
      rcases ho1 : o1 with _ | cs
      · rw [ho1] at o1_post
        simp only [Option.map_none] at o1_post
        rw [← o1_post]
        step*
      · rw [ho1] at o1_post
        simp only [Option.map_some] at o1_post
        rw [← o1_post]
        step*
        step with Tacenta.SpqrT1.chains_clone_spec hopt cs
        rw [cs1_post]
        rcases hcsr : cs.receive with _ | ch
        · simp only [chainsOf, hcsr, Option.map_none]
          step*
        · simp only [chainsOf, hcsr, Option.map_some]
          have hcnt : ch.n.val < Std.U64.max := by
            have hcb1 : ChainCounterBounded st2.chains :=
              skipMessageKeys_chain_counter_bounded m1 receiving_epoch.val (n.val - 1) st2
                (by scalar_tac) hsmk hccb1
            have hcsofeq : (chainsOf cs).receive = some (chainOf ch) := by simp [chainsOf, hcsr]
            have hmem := findChains_mem st2 receiving_epoch.val (chainsOf cs) o1_post.symm
            have := hcb1 (receiving_epoch.val, chainsOf cs) hmem (chainOf ch) (Or.inr hcsofeq)
            simpa [chainOf] using this
          -- Introduce the clone first, then split the `checked_add` by hand, so
          -- the unreachable branch can be refuted from `hcnt` above rather than
          -- left for `step*` to present as a third case with no model
          -- counterpart.
          step with Tacenta.SpqrT1.chain_clone_spec ch
          rcases hadd : ch1.n.checked_add 1#u64 with _ | expected
          · exfalso
            have hn1 : ch1.n.val = ch.n.val := by rw [← ch1_post]
            have hspec := Std.U64.checked_add_bv_spec ch1.n 1#u64
            rw [hadd] at hspec
            simp_all
            omega
          simp only
          have expected_post : expected.val = ch.n.val + 1 := by
            have hn1 : ch1.n.val = ch.n.val := by rw [← ch1_post]
            have hspec := Std.U64.checked_add_bv_spec ch1.n 1#u64
            rw [hadd] at hspec
            rw [← hn1]
            exact hspec.2.1
          step*
          · have hnv : (chainOf ch).n = ch.n.val := rfl
            have hne' : ¬ n.val = ch.n.val + 1 := by scalar_tac
            simp only [hnv, hne']
            exact ⟨_, rfl⟩
          · have hnv : (chainOf ch).n = ch.n.val := rfl
            have hne : n.val = ch.n.val + 1 := by scalar_tac
            simp only [hnv, hne]
            step with kdf_ck_refines hkr hz64 ch1.ck n
            rw [ch1_post, hne] at next_post
            step with hopt Chain.Insts.CoreCloneClone cs.send
              (fun x _ => Tacenta.SpqrT1.chain_clone_spec x)
            have hchainlen3 := congrArg List.length hself3.chains
            have hchainlen3' := congrArg List.length hself2.chains
            simp only [List.length_map] at hchainlen3 hchainlen3'
            have hroom3 : self3.chains.val.length < Usize.max := by scalar_tac
            step with set_chains_refines hret hself3 receiving_epoch
              ({ send := o3, receive := some { ck := next, n } } : Chains) hroom3
            refine ⟨mk, rfl, ?_, ?_⟩
            · exact congrArg Prod.snd next_post
            · have hckeq : keyOf next
                  = (Model.SparseRatchet.kdfCk (keyOf ch.ck) (ch.n.val + 1)).1 := by
                rw [← next_post]
              simpa [chainOf, chainsOf, hcsr, o3_post, hckeq, hne] using self4_post
  · rw [hts] at o_post
    obtain ⟨key, hokey, hkeyeq, hrefines⟩ := o_post
    rw [hokey]
    exact ⟨key, rfl, hkeyeq, hrefines⟩

-- The receiving path's `checked_add` branch on the chain counter puts the
-- elaboration past the default heartbeat allowance, so this theorem needs a
-- larger one; the same setting is used in `BraidT3` and twice in `ProtobufT3`.
set_option maxHeartbeats 1000000 in
/-- `State.receive` refines `Model.SparseRatchet.receive`: it composes
`maybe_advance`, a stored-key check, a forward skip, and the receiving chain's
own step, in that order -- the same order the model's own `receive` composes
its four pieces. -/
theorem receive_refines (hkr : SpqrHkdfAgrees)
    (hz96 : ZeroizingRoundTrips96) (hz64 : ZeroizingRoundTrips64) (hret : VecRetainAgrees)
    (happ : VecAppendAgrees) (hrm : VecRemoveAgrees) (hz : Tacenta.SpqrT1.ZeroizeTotal)
    (hopt : Tacenta.SpqrT1.OptionCloneTotal)
    {s : State} {m : Model.SparseRatchet.State} (hrel : StateRefines s m)
    (receiving_epoch : Std.U64) (out : Option Output) (n : Std.U64)
    (hepoch : s.epoch.val < Std.U64.max)
    (hroom : s.chains.val.length + 2 < Usize.max)
    (hcb : ∀ p ∈ s.chains.val, p.1.val + Model.SparseRatchet.epochsKept ≤ Std.U64.max)
    (hsb : ∀ sk ∈ s.skipped.val, sk.epoch.val + Model.SparseRatchet.epochsKept ≤ Std.U64.max)
    (hnewb : ∀ o : Output, out = some o →
      o.key_epoch.val + Model.SparseRatchet.epochsKept ≤ Std.U64.max)
    (hskiproom : s.skipped.val.length + MAX_SKIP.val ≤ Usize.max)
    (hone : (m.skipped.filter (fun x => x.1 == receiving_epoch.val && x.2.1 == n.val)).length ≤ 1)
    (hcounter : ∀ p ∈ s.chains.val, ∀ ch : Chain,
      (p.2.send = some ch ∨ p.2.receive = some ch) → ch.n.val < Std.U64.max) :
    State.receive s receiving_epoch out n ⦃ fun r =>
      match Model.SparseRatchet.receive m receiving_epoch.val (out.map outputOf) n.val with
      | none => ∃ err, r.1 = core.result.Result.Err err
      | some (m', k) => ∃ key, r.1 = core.result.Result.Ok key ∧ keyOf key = k ∧
          StateRefines r.2 m' ⦄ := by
  unfold State.receive Model.SparseRatchet.receive
  step with maybe_advance_refines hkr hz96 hret hz hrel out hepoch (by scalar_tac) hcb hsb hnewb
  step
  rcases hout : out with _ | o
  · simp only [hout, Option.map_none] at r_post ⊢
    obtain ⟨hrOk, hrel1⟩ := r_post
    rw [hrOk] at cf_post
    simp only [cf_post]
    have hskiplen1 := congrArg List.length hrel1.skipped
    have hskiplen2 := congrArg List.length hrel.skipped
    simp only [List.length_map] at hskiplen1 hskiplen2
    have hchainlen1 := congrArg List.length hrel1.chains
    have hchainlen2 := congrArg List.length hrel.chains
    simp only [List.length_map] at hchainlen1 hchainlen2
    have hskiproom1 : self1.skipped.val.length + MAX_SKIP.val ≤ Usize.max := by scalar_tac
    exact receive_refines_continuation hkr hz64 hret happ hrm hz hopt hrel1 receiving_epoch n
      (by scalar_tac) hskiproom1 hone (chainCounterBounded_of_real hrel hcounter)
  · simp only [hout, Option.map_some] at r_post ⊢
    rcases hadv : (Model.SparseRatchet.advance m (outputOf o)) with _ | m1
    · rw [hadv] at r_post
      obtain ⟨o', hno, herr, hstate⟩ := r_post
      simp only
      rw [herr] at cf_post
      simp only [cf_post]
      exact ⟨_, rfl⟩
    · rw [hadv] at r_post
      obtain ⟨hrOk, hrel1⟩ := r_post
      simp only
      rw [hrOk] at cf_post
      simp only [cf_post]
      have hlen := advance_skipped_len_le m (outputOf o) m1 hadv
      have hclen := advance_chains_len_le m (outputOf o) m1 hadv
      have hskiplen1 := congrArg List.length hrel1.skipped
      have hskiplen2 := congrArg List.length hrel.skipped
      simp only [List.length_map] at hskiplen1 hskiplen2
      have hchainlen1 := congrArg List.length hrel1.chains
      have hchainlen2 := congrArg List.length hrel.chains
      simp only [List.length_map] at hchainlen1 hchainlen2
      have hskiproom1 : self1.skipped.val.length + MAX_SKIP.val ≤ Usize.max := by scalar_tac
      have hmskip := advance_skipped_eq m (outputOf o) m1 hadv
      have hone1 : (m1.skipped.filter
          (fun x => x.1 == receiving_epoch.val && x.2.1 == n.val)).length ≤ 1 := by
        rw [hmskip]
        exact le_trans (List.filter_filter_length_le m.skipped
          (fun x => decide ((outputOf o).keyEpoch < x.1 + Model.SparseRatchet.epochsKept))
          (fun x => x.1 == receiving_epoch.val && x.2.1 == n.val)) hone
      exact receive_refines_continuation hkr hz64 hret happ hrm hz hopt hrel1 receiving_epoch n
        (by scalar_tac) hskiproom1 hone1
        (advance_chain_counter_bounded m (outputOf o) m1 hadv (chainCounterBounded_of_real hrel hcounter))

/-! ## Where this stands

**Proved:** `send_refines` and `receive_refines`, the crate's two entry
points, compute what `Model.SparseRatchet.send`/`receive` compute -- the key
returned, the output reported, and the state transitioned to -- across every
branch each can take, not merely that they cannot fail (`SpqrT1.lean`'s
claim). Everything underneath them (`kdf_init`/`kdf_rk`/`kdf_ck`,
`find_chains`, `set_chains`, `clear_old_epochs`, `advance`/`maybe_advance`,
`try_skipped`, `skip_message_keys`) is refined along the way, since `send`
and `receive` call all of it.

`Model.SparseRatchet.lean` had no lemma library to build on, unlike
`Model.Braid.lean`'s nine theorems `BraidT3.lean` could reuse directly. This
file adds the ones `send`/`receive`'s own proofs needed: `deriveInto_split`
and its two projections, `advance_chains_len_le`/`advance_skipped_len_le`/
`advance_skipped_eq`, `setChains_chains_len_le`/`skipMessageKeys_chains_len_le`,
and the generic `List.filter_filter_length_le`. None claims more than the
specific bound its call site needed.

**Eight assumptions back this file, six of them new constants and two reused
outright from `SpqrT1.lean`.** `SpqrHkdfAgrees` states agreement one level
below `SpqrT1.lean`'s totality-only `KdfRkTotal`/`KdfCkTotal`, at the opaque
`hkdf_sha256` call itself, and with `ZeroizingRoundTrips96`/
`ZeroizingRoundTrips64` -- the `zeroize` wrapper each expansion now passes
through on its way to being split -- subsumes both, so this file states the
KDF boundary once rather than twice. `VecRetainAgrees` and `VecRemoveAgrees`
likewise state what `retain`/`remove` return, not only that they return, and
are each strictly stronger than their `SpqrT1.lean` namesake, so neither
totality hypothesis is separately assumed here. `VecAppendAgrees` is genuinely
new: `SpqrT1.lean` needed only `VecAppendTotal`, since nothing there depended
on what `skip_message_keys`'s concatenation actually produced, and this file
does. `Tacenta.SpqrT1.ZeroizeTotal` and `Tacenta.SpqrT1.OptionCloneTotal`
carry over unchanged, since neither proof needed strengthening to a value
claim -- the buffer wipe and the direction clone are never read back from,
only required to complete.

As with `SpqrT1.lean` and `BraidT3.lean`, count by constant, not by name:
none of these eight is the same proposition as any other file's assumption of
a similar shape, including `T1.lean`'s or `BraidT1.lean`'s own copies of
`Vec::retain`/`Vec::remove`/`Vec::append`, `Zeroize`, a KDF call, or
`T3.lean`'s `ZeroizingRoundTrips`/`ZeroizingRoundTrips80` at the ratchet's own
wrapper constants.

**`hcounter`, on `send_refines`/`receive_refines`, is scoped to
`s.chains.val`**, matching `hcb`/`hsb`'s own style. Quantified over every
value the type can hold instead (`∀ ch : Chain, ∀ cs : Chains, cs.send = some
ch → ch.n.val < Std.U64.max`) it would be unsatisfiable -- a four-line
counterexample shows it -- and the theorems true but uncallable, which
neither `lake build` nor `#print axioms` can flag. `ChainCounterBounded`,
`findChains_mem`, `advance_chain_counter_bounded`,
`maybeAdvance_chain_counter_bounded`, `skipMessageKeys_chain_counter_bounded`,
and `chainCounterBounded_of_real` (all above, ahead of `send_refines`) are
what let the internal proofs reach the specific chain each needs the bound
for; `SpqrT1.lean` scopes its own `hcounter` the same way. See
`LIMITATIONS.md`. -/

end Tacenta.SpqrT3
