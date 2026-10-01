import Translation.SessionUnitBraidPreserve
import Translation.SessionUnitBraidImportInv
import Translation.UnitSatisfiabilityJoint

/-!
# The Braid's preservation theorems on the session unit: what a decoded Braid, the receive
theorems and the two laws add

`SessionUnitBraidPreserve.lean` (the count-checked port of `BraidPreserve.lean`) shows that a
successful `send`, `receive`, `commit` or constructor keeps `State.sized`.  This module adds what only
the session unit can say, because only there is the erasure decoder a translated definition:

* `sized_decoders_bounded`: `sized` gives `State.decoders_bounded`, so it supplies both premises of
  the unit's receive theorems.
* `invariant_true_gives_sized`, `from_bytes_sized`: a Braid `Braid::from_bytes` returns has `sized`.
  `Braid::invariant` calls `Decoder::invariant` and `decoder_sized` on every decoder, and
  `decoder_sized` says the decoder's `size` is the protocol constant.
* `Braid.Run.sized_of_start`, `Braid.Run.inv`: every Braid a run reaches from the constructors and
  from decoded Braids has `sized`, and so `Braid.Inv`, the mirror `SessionUnitBraidImportInv` states.
* `Braid.Run.receive_no_panic`, `Braid.Run.receive_refines`: the unit's receive theorems for such a
  Braid, without their `ct1_bounded` and `decoders_bounded` premises.
* `inv_not_sized`: `Braid.Inv` is not closed under the transitions by itself.  It does not say the
  decoder that makes `ct1` is sized for at most 4096 bytes, and `sized` does.  The statement is about
  every key pair, so it needs no inhabitant of the opaque key-pair type.
* `TruncateLen_is`, `laws_model`: the two laws `Laws` assumes have a model.  `TruncateLen` is a
  consequence of the prefix law the joint model of `UnitSatisfiabilityJoint.lean` already
  satisfies (`model_truncate_is_take`), and `DivCeilValue` is the field of `StdLaws` that model
  satisfies.  This is consistency of the statements in the joint model of the unit's opaque
  constants, as `LIMITATIONS.md` records for the five laws, and not a model of the real `Vec::truncate`
  and `usize::div_ceil`.

Nothing here assumes the behaviour of an opaque operation beyond the two laws and the KEM length
constants (`Ct1LenTotal` and the three like it), each of which a statement names.
-/

open Aeneas Aeneas.Std Result
open tacenta_session_unit.tacenta_braid
open tacenta_session_unit.tacenta_erasure
open Tacenta.SessionUnitBraidT1
open Tacenta.SessionUnitBraidPreserveDecoder
open Tacenta.SessionUnitBraidPreserve
open Tacenta.SessionUnitDecoderBound (bind_eq_ok_inv)

namespace Tacenta.SessionUnitBraidPreserveFacts

/-! ## A. `sized` gives the unit's two premises -/

/-- `sized` gives `State.decoders_bounded`: a `Good` decoder needs at most `MAX_CODEWORDS` chunks. -/
theorem sized_decoders_bounded {s : State} (h : State.sized s) : State.decoders_bounded s := by
  rcases s with _|_|_|_|_|_|_|_|_|_|_|_ <;>
    simp_all [State.sized, State.decoders_bounded, Good]

/-- A Braid with `sized` has `Braid.Inv`, the two-field mirror of `Braid::invariant`. -/
theorem sized_inv {b : Braid} (h : Braid.sized b) :
    Tacenta.SessionUnitBraidImportInv.Braid.Inv b :=
  ⟨State.sized_ct1_bounded h, sized_decoders_bounded h⟩

/-! ## B. A decoded Braid has `sized` -/

/-- `if c then X else ok false` returned `true`: the condition held and `X` returned `true`. -/
theorem if_ok_false_true {c : Prop} [Decidable c] {X : Result Bool}
    (h : (if c then X else ok false) = ok true) : c ∧ X = ok true := by
  by_cases hc : c
  · rw [if_pos hc] at h
    exact ⟨hc, h⟩
  · rw [if_neg hc] at h
    simp at h

/-- The check `Braid::invariant` makes on a decoder's size. -/
theorem decoder_sized_eq {d : Decoder} {n : Usize} {b : Bool}
    (h : decoder_sized d n = ok b) (hb : b = true) : d.size = n := by
  unfold decoder_sized at h
  obtain ⟨i, hi, h⟩ := bind_eq_ok_inv h
  unfold Decoder.impl.size at hi
  simp only [ok.injEq] at hi h
  subst hi
  subst hb
  simpa using h

/-- A decoder that passes `Decoder::invariant` needs at most `MAX_CODEWORDS` chunks. -/
theorem invariant_needed_le {d : Decoder} {b : Bool}
    (h : Decoder.invariant d = ok b) (hb : b = true) : d.needed.val ≤ 65536 := by
  subst hb
  exact Tacenta.SessionUnitDecoderBound.invariant_true_needed_le d h

/-- A decoder that passes `Decoder::invariant` and `decoder_sized` at a length of at most `n` is
good for `n`. -/
theorem good_of_checks {d : Decoder} {len : Usize} {n : Nat} {b1 b2 : Bool}
    (hinv : Decoder.invariant d = ok b1) (hb1 : b1 = true)
    (hs : decoder_sized d len = ok b2) (hb2 : b2 = true) (hn : len.val ≤ n) :
    Good n d :=
  ⟨by rw [decoder_sized_eq hs hb2]; exact hn, invariant_needed_le hinv hb1⟩

/-- A vector whose length equals a constant of at most 4096 has at most 4096 elements. -/
theorem vec_len_le {v : alloc.vec.Vec U8} {i : Usize} (hlen : alloc.vec.Vec.len v = i)
    (hi : i.val ≤ 4096) : v.length ≤ 4096 := by
  have := alloc.vec.Vec.len_val v
  rw [hlen] at this
  omega

/-- **A Braid whose translated `invariant` returns `true` has `sized`.**  The clauses are read
off the arms of `Braid::invariant`: `Vec::len ct1 = CT1_LEN`, `Decoder::invariant` on every
decoder, and `decoder_sized` against the protocol constant each decoder is built with.  The
hypotheses are the four KEM length constants being at most 4096 (the real ones are 1408, 160, 64
and 1536). -/
theorem invariant_true_gives_sized (hct1 : Ct1LenTotal) (hct2 : Ct2LenTotal)
    (hhdr : HeaderLenTotal) (hek : EkVectorLenTotal) (b : Braid)
    (h : Braid.invariant b = ok true) : Braid.sized b := by
  unfold Braid.sized
  rw [Braid.invariant] at h
  rcases hst : b.state with
    ⟨epoch, auth⟩ | ⟨epoch, auth, kp, hdr_enc⟩ | ⟨epoch, auth, kp, ct1_dec, ek_enc⟩
    | ⟨epoch, auth, kp, ct1, ek_enc⟩ | ⟨epoch, auth, kp, ct1, ct2_dec⟩
    | ⟨epoch, auth, hdr_dec⟩ | ⟨epoch, auth, header, ek_dec⟩
    | ⟨epoch, auth, header, encaps, ct1, ct1_enc, ek_dec⟩
    | ⟨epoch, auth, encaps, ct1, ek_vector, ct1_enc⟩
    | ⟨epoch, auth, header, encaps, ct1, ek_dec⟩ | ⟨epoch, auth, ct2_enc⟩ | - <;>
    rw [hst] at h
  · trivial
  · trivial
  · -- HeaderSent
    obtain ⟨-, h⟩ := if_ok_false_true h
    obtain ⟨b1, hb1, h⟩ := bind_eq_ok_inv h
    obtain ⟨hb1t, h⟩ := if_ok_false_true h
    obtain ⟨i, hi, h⟩ := bind_eq_ok_inv h
    obtain ⟨b2, hb2, h⟩ := bind_eq_ok_inv h
    obtain ⟨hb2t, h⟩ := if_ok_false_true h
    exact good_of_checks hb1 hb1t hb2 hb2t (len_le hct1 hi)
  · -- Ct1Received
    obtain ⟨-, h⟩ := if_ok_false_true h
    obtain ⟨i1, hi1, h⟩ := bind_eq_ok_inv h
    obtain ⟨hlen, h⟩ := if_ok_false_true h
    exact vec_len_le hlen (len_le hct1 hi1)
  · -- EkSentCt1Received
    obtain ⟨-, h⟩ := if_ok_false_true h
    obtain ⟨i1, hi1, h⟩ := bind_eq_ok_inv h
    obtain ⟨hlen, h⟩ := if_ok_false_true h
    obtain ⟨b1, hb1, h⟩ := bind_eq_ok_inv h
    obtain ⟨hb1t, h⟩ := if_ok_false_true h
    obtain ⟨i2, hi2, h⟩ := bind_eq_ok_inv h
    obtain ⟨i3, hi3, h⟩ := bind_eq_ok_inv h
    obtain ⟨b2, hb2, h⟩ := bind_eq_ok_inv h
    obtain ⟨hb2t, h⟩ := if_ok_false_true h
    exact ⟨vec_len_le hlen (len_le hct1 hi1),
      good_of_checks hb1 hb1t hb2 hb2t (add_mac_le (len_le hct2 hi2) hi3)⟩
  · -- NoHeaderReceived
    obtain ⟨-, h⟩ := if_ok_false_true h
    obtain ⟨b1, hb1, h⟩ := bind_eq_ok_inv h
    obtain ⟨hb1t, h⟩ := if_ok_false_true h
    obtain ⟨i, hi, h⟩ := bind_eq_ok_inv h
    obtain ⟨i1, hi1, h⟩ := bind_eq_ok_inv h
    exact good_of_checks hb1 hb1t h rfl (add_mac_le (len_le hhdr hi) hi1)
  · -- HeaderReceived
    obtain ⟨-, h⟩ := if_ok_false_true h
    obtain ⟨i1, hi1, h⟩ := bind_eq_ok_inv h
    obtain ⟨-, h⟩ := if_ok_false_true h
    obtain ⟨b1, hb1, h⟩ := bind_eq_ok_inv h
    obtain ⟨hb1t, h⟩ := if_ok_false_true h
    obtain ⟨i2, hi2, h⟩ := bind_eq_ok_inv h
    exact good_of_checks hb1 hb1t h rfl (le_trans (len_le hek hi2) (by omega))
  · -- Ct1Sampled
    obtain ⟨-, h⟩ := if_ok_false_true h
    obtain ⟨i1, hi1, h⟩ := bind_eq_ok_inv h
    obtain ⟨-, h⟩ := if_ok_false_true h
    obtain ⟨i3, hi3, h⟩ := bind_eq_ok_inv h
    obtain ⟨hlen, h⟩ := if_ok_false_true h
    obtain ⟨b, hb, h⟩ := bind_eq_ok_inv h
    obtain ⟨-, h⟩ := if_ok_false_true h
    obtain ⟨b1, hb1, h⟩ := bind_eq_ok_inv h
    obtain ⟨-, h⟩ := if_ok_false_true h
    obtain ⟨b2, hb2, h⟩ := bind_eq_ok_inv h
    obtain ⟨hb2t, h⟩ := if_ok_false_true h
    obtain ⟨i4, hi4, h⟩ := bind_eq_ok_inv h
    exact ⟨vec_len_le hlen (len_le hct1 hi3),
      good_of_checks hb2 hb2t h rfl (le_trans (len_le hek hi4) (by omega))⟩
  · -- EkReceivedCt1Sampled
    obtain ⟨-, h⟩ := if_ok_false_true h
    obtain ⟨i1, hi1, h⟩ := bind_eq_ok_inv h
    obtain ⟨hlen, h⟩ := if_ok_false_true h
    exact vec_len_le hlen (len_le hct1 hi1)
  · -- Ct1Acknowledged
    obtain ⟨-, h⟩ := if_ok_false_true h
    obtain ⟨i1, hi1, h⟩ := bind_eq_ok_inv h
    obtain ⟨-, h⟩ := if_ok_false_true h
    obtain ⟨i3, hi3, h⟩ := bind_eq_ok_inv h
    obtain ⟨hlen, h⟩ := if_ok_false_true h
    obtain ⟨b1, hb1, h⟩ := bind_eq_ok_inv h
    obtain ⟨hb1t, h⟩ := if_ok_false_true h
    obtain ⟨i4, hi4, h⟩ := bind_eq_ok_inv h
    exact ⟨vec_len_le hlen (len_le hct1 hi3),
      good_of_checks hb1 hb1t h rfl (le_trans (len_le hek hi4) (by omega))⟩
  · trivial
  · trivial

/-- **A Braid `Braid::from_bytes` returns has `sized`.** -/
theorem from_bytes_sized (hct1 : Ct1LenTotal) (hct2 : Ct2LenTotal) (hhdr : HeaderLenTotal)
    (hek : EkVectorLenTotal) (bytes : Slice U8) (b : Braid)
    (h : Braid.from_bytes bytes = ok (core.result.Result.Ok b)) : Braid.sized b :=
  invariant_true_gives_sized hct1 hct2 hhdr hek b
    (Tacenta.SessionUnitBraidImportInv.Braid.from_bytes_establishes_invariant bytes b h)

/-! ## C. Every Braid a run reaches, from constructors and from decoded Braids -/

/-- A Braid `Braid::from_bytes` returns. -/
def Braid.Decoded (b : Braid) : Prop :=
  ∃ bytes, Braid.from_bytes bytes = ok (core.result.Result.Ok b)

/-- The Braids a run starts from: the constructors' and the decoded ones. -/
def Braid.Start (b : Braid) : Prop := Braid.Constructed b ∨ Braid.Decoded b

theorem Braid.Start.sized (hl : Laws) (hct1 : Ct1LenTotal) (hct2 : Ct2LenTotal)
    (hhdr : HeaderLenTotal) (hek : EkVectorLenTotal) {b : Braid} (h : Braid.Start b) :
    Braid.sized b := by
  rcases h with h | ⟨bytes, h⟩
  · exact Braid.Constructed.sized hl hhdr h
  · exact from_bytes_sized hct1 hct2 hhdr hek bytes b h

/-- **Every Braid a run reaches from the constructors and from decoded Braids has `sized`.** -/
theorem Braid.Run.sized_of_start (hl : Laws) (hct1 : Ct1LenTotal) (hct2 : Ct2LenTotal)
    (hhdr : HeaderLenTotal) (hek : EkVectorLenTotal) (hencaps1 : Encapsulate1Total)
    {b : Braid} (hr : Braid.Run Braid.Start b) : Braid.sized b :=
  Braid.Run.sized hl hct1 hct2 hhdr hek hencaps1
    (fun _ hb => Braid.Start.sized hl hct1 hct2 hhdr hek hb) hr

/-- **Every Braid a run reaches from the constructors and from decoded Braids has
`Braid.Inv`**, the two-field mirror of `Braid::invariant` the unit's decoded-state theorems use. -/
theorem Braid.Run.inv (hl : Laws) (hct1 : Ct1LenTotal) (hct2 : Ct2LenTotal)
    (hhdr : HeaderLenTotal) (hek : EkVectorLenTotal) (hencaps1 : Encapsulate1Total)
    {b : Braid} (hr : Braid.Run Braid.Start b) :
    Tacenta.SessionUnitBraidImportInv.Braid.Inv b :=
  sized_inv (Braid.Run.sized_of_start hl hct1 hct2 hhdr hek hencaps1 hr)

/-! ## D. The unit's receive theorems for such a Braid -/

/-- **`receive` cannot panic on a Braid a run reaches**, with neither `ct1_bounded` nor
`decoders_bounded` as a premise. -/
theorem Braid.Run.receive_no_panic (hl : Laws) (hencaps1 : Encapsulate1Total)
    (hdnew : DecoderNewTotal) (hdadd : DecoderAddChunkTotal)
    (hdmsg : DecoderMessageTotal) (hct1len : Ct1LenTotal) (hct2len : Ct2LenTotal)
    (hhdrlen : HeaderLenTotal) (hekveclen : EkVectorLenTotal) (hekvec : KeyPairEkVectorTotal)
    (henew : EncoderNewTotal) (hdecap : KeyPairDecapsulateTotal) (hkdf : HkdfSha256Total)
    (hmac : HmacSha256Total) (hvalek : ValidateEkTotal) (hencaps2 : Encapsulate2Total)
    (henc : EncoderCloneTotal) (hdec : DecoderCloneTotal) (hkp : KeyPairCloneTotal)
    (hes : EncapsStateCloneTotal) (hopt : OptionCloneTotal)
    (hz : ZeroizingArrayRoundTrip) (hzz : ArrayZeroizeTotal) (hrf : RangeFullIndexTotal)
    {self : Braid} (hrun : Braid.Run Braid.Start self) (msg : Msg) :
    Braid.receive self msg ⦃ fun _result => True ⦄ :=
  have hs := Braid.Run.sized_of_start hl hct1len hct2len hhdrlen hekveclen hencaps1 hrun
  Braid.receive_no_panic hdnew hdadd hdmsg hct1len hct2len hhdrlen hekveclen hekvec henew hdecap
    hkdf hmac hvalek hencaps2 henc hdec hkp hes hopt hz hzz hrf self msg
    (State.sized_ct1_bounded hs) (sized_decoders_bounded hs)

/-- **`receive` refines `Model.Braid.receive` on a Braid a run reaches**, under the premises of
`SessionUnitBraidT3.Braid.receive_refines` other than `ct1_bounded` and `decoders_bounded`.  Beyond
its own premises it takes `Laws`, `Encapsulate1Total`, the run `hrun` and `hekveclenB`, the
`EkVectorLenTotal` the T1 theorem takes. -/
theorem Braid.Run.receive_refines {K : Model.Braid.Kem} (hl : Laws) (hencaps1 : Encapsulate1Total)
    (hka : Tacenta.SessionUnitBraidT3.KemAgreesFor K) (hea : Tacenta.SessionUnitBraidT3.ErasureAgrees)
    (hmac : Tacenta.SessionUnitBraidT3.BraidHmacAgrees)
    (hkdf : Tacenta.SessionUnitBraidT3.BraidHkdfAgrees)
    (hlens : Tacenta.SessionUnitBraidT3.KemLenAgrees K)
    (hvalek : Tacenta.SessionUnitBraidT3.ValidateEkAgrees K)
    (hencaps2len : Encapsulate2Total) (hdadd : DecoderAddChunkTotal)
    (hdmsg : DecoderMessageTotal)
    (hct1lenB : Ct1LenTotal) (hct2lenB : Ct2LenTotal) (hheaderlenB : HeaderLenTotal)
    (hekveclenB : EkVectorLenTotal)
    (hkcl : Tacenta.SessionUnitBraidT3.KemCloneAgrees)
    (hecl : Tacenta.SessionUnitBraidT3.ErasureCloneAgrees)
    (henc : EncoderCloneTotal) (hdec : DecoderCloneTotal)
    (hkp : KeyPairCloneTotal) (hes : EncapsStateCloneTotal) (hopt : OptionCloneTotal)
    (hz : ZeroizingArrayRoundTrip) (hzz : ArrayZeroizeTotal) (hrf : RangeFullIndexTotal)
    {self : Braid} (hrun : Braid.Run Braid.Start self) (msg : Msg)
    (hepoch : (State.epoch_val self.state).val + 1 < Std.U64.max)
    {model : Model.Braid.BraidState} {modelMsg : Model.Braid.Msg}
    (hrel : Tacenta.SessionUnitBraidT3.StateRefines K self.state model)
    (hmsg : Tacenta.SessionUnitBraidT3.MsgRefines msg modelMsg)
    (hhonest : Tacenta.SessionUnitBraidT3.HonestChunk model modelMsg) :
    Braid.receive self msg ⦃ fun result =>
      result.1.val = (Model.Braid.receive K model modelMsg).2.2.epoch - 1 ∧
      Tacenta.SessionUnitBraidT3.OptionOutputRefines result.2.1 (Model.Braid.receive K model modelMsg).2.1 ∧
      Tacenta.SessionUnitBraidT3.StateRefines K result.2.2.state
        (Model.Braid.receive K model modelMsg).2.2 ⦄ :=
  have hs := Braid.Run.sized_of_start hl hct1lenB hct2lenB hheaderlenB hekveclenB hencaps1 hrun
  Tacenta.SessionUnitBraidT3.Braid.receive_refines hka hea hmac hkdf hlens hvalek hencaps2len
    hdadd hdmsg hct1lenB hct2lenB hheaderlenB hkcl hecl henc hdec hkp hes hopt hz hzz hrf self msg
    (State.sized_ct1_bounded hs) (sized_decoders_bounded hs) hepoch hrel hmsg hhonest

/-! ## E. The two-field mirror is not closed under the transitions by itself -/

/-- **`Braid.Inv` does not say what `sized` says.**  A `HeaderSent` state whose `ct1` decoder is
sized for 4097 bytes (and so needs 129 chunks) meets `ct1_bounded` and `decoders_bounded`, and so
`Braid.Inv`, and does not meet `sized`.  From it the chunk that completes the decoder makes a `ct1`
of 4097 bytes, over the bound `ct1_bounded` asks for: the real `Decoder::message` returns
`size` bytes.  That step is not a Lean theorem, because the translated `Decoder::message` is not
computed in Lean.  `Braid::invariant` rejects the state
(`decoder_sized` against `CT1_LEN` fails), so no decoded or constructed Braid is such a state.
Stated for every epoch, authenticator, key pair and encoder, so it needs no inhabitant of the
opaque key-pair and encoder types. -/
theorem inv_not_sized (epoch : U64) (auth : Auth) (kp : tacenta_session_unit.tacenta_kem.IncrementalKeyPair)
    (ek_enc : Encoder) :
    let d : Decoder := { size := 4097#usize, needed := 129#usize, «have» := alloc.vec.Vec.new Chunk }
    let s := State.HeaderSent epoch auth kp d ek_enc
    Tacenta.SessionUnitBraidImportInv.Braid.Inv ({ state := s } : Braid) ∧ ¬ Braid.sized { state := s } := by
  refine ⟨⟨by simp [State.ct1_bounded], by simp [State.decoders_bounded]⟩, ?_⟩
  simp only [Braid.sized, State.sized, Good, not_and]
  intro h
  simp at h

/-! ## F. The two laws have a model -/

/-- `TruncateLen` with the function abstracted.  `TruncateLen_is` ties it to the unit's
`Vec::truncate` by `Iff.rfl`, so a change to the statement of `TruncateLen` stops this file from
building. -/
def TruncateLenShape (f : {T : Type} → Type → alloc.vec.Vec T → Usize → Result (alloc.vec.Vec T)) :
    Prop :=
  ∀ (v : alloc.vec.Vec U8) (n : Usize), ∃ r, f Global v n = ok r ∧ r.length ≤ n.val

theorem TruncateLen_is :
    TruncateLen ↔ TruncateLenShape Tacenta.UnitSatisfiabilityJoint.Interp.real.vecTruncate :=
  Iff.rfl

/-- The joint model's `Vec::truncate` satisfies `TruncateLen`: it is a prefix. -/
theorem truncateLen_model :
    TruncateLenShape Tacenta.UnitSatisfiabilityJoint.Interp.model.vecTruncate := by
  intro v n
  obtain ⟨r, hr, hv⟩ := Tacenta.UnitSatisfiabilityJoint.model_truncate_is_take v n
  refine ⟨r, hr, ?_⟩
  simp only [alloc.vec.Vec.length, hv, List.length_take]
  exact Nat.min_le_left _ _

/-- **The two laws are bound to the unit's constants and hold in the joint model of
`UnitSatisfiabilityJoint.lean`, which satisfies every axiom-level field of the four session records
and the five laws of `LIMITATIONS.md` at once.**  `DivCeilValueShape` is that module's. -/
theorem laws_model :
    (Laws ↔ TruncateLenShape Tacenta.UnitSatisfiabilityJoint.Interp.real.vecTruncate ∧
      Tacenta.UnitSatisfiabilityJoint.DivCeilValueShape Tacenta.UnitSatisfiabilityJoint.Interp.real) ∧
    TruncateLenShape Tacenta.UnitSatisfiabilityJoint.Interp.model.vecTruncate ∧
    Tacenta.UnitSatisfiabilityJoint.DivCeilValueShape Tacenta.UnitSatisfiabilityJoint.Interp.model ∧
    Tacenta.UnitSatisfiabilityJoint.StdLaws Tacenta.UnitSatisfiabilityJoint.Interp.model :=
  ⟨Iff.and TruncateLen_is Tacenta.UnitSatisfiabilityJoint.DivCeilValue_is,
    truncateLen_model, Tacenta.UnitSatisfiabilityJoint.model_DivCeilValue,
    Tacenta.UnitSatisfiabilityJoint.model_StdLaws⟩

end Tacenta.SessionUnitBraidPreserveFacts

/-! ## Axiom pins

The axiom base of each result, held by the build. -/

/--
info: 'Tacenta.SessionUnitBraidPreserveFacts.sized_decoders_bounded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kem.EncapsState,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair]
-/
#guard_msgs in
#print axioms Tacenta.SessionUnitBraidPreserveFacts.sized_decoders_bounded

/--
info: 'Tacenta.SessionUnitBraidPreserveFacts.invariant_true_gives_sized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kem.CT1_LEN,
 tacenta_session_unit.tacenta_kem.CT2_LEN,
 tacenta_session_unit.tacenta_kem.EK_VECTOR_LEN,
 tacenta_session_unit.tacenta_kem.EncapsState,
 tacenta_session_unit.tacenta_kem.HEADER_LEN,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair,
 tacenta_session_unit.tacenta_kem.validate_ek,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.header,
 tacenta_session_unit.core.num.Usize.div_ceil]
-/
#guard_msgs in
#print axioms Tacenta.SessionUnitBraidPreserveFacts.invariant_true_gives_sized

/--
info: 'Tacenta.SessionUnitBraidPreserveFacts.from_bytes_sized' depends on axioms: [propext,
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
#print axioms Tacenta.SessionUnitBraidPreserveFacts.from_bytes_sized

/--
info: 'Tacenta.SessionUnitBraidPreserveFacts.Braid.Run.sized_of_start' depends on axioms: [propext,
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
 tacenta_session_unit.tacenta_kem.EncapsState.from_bytes,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.from_bytes,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.generate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.header,
 tacenta_session_unit.zeroize.Zeroizing.new,
 tacenta_session_unit.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.alloc.vec.Vec.truncate,
 tacenta_session_unit.core.num.Usize.div_ceil,
 tacenta_session_unit.zeroize.Zeroize.Blanket.zeroize,
 tacenta_session_unit.tacenta_kem.EncapsState.Insts.CoreCloneClone.clone,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 tacenta_session_unit.core.option.Option.Insts.CoreCloneClone.clone,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut]
-/
#guard_msgs in
#print axioms Tacenta.SessionUnitBraidPreserveFacts.Braid.Run.sized_of_start

/--
info: 'Tacenta.SessionUnitBraidPreserveFacts.Braid.Run.inv' depends on axioms: [propext,
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
 tacenta_session_unit.tacenta_kem.EncapsState.from_bytes,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.from_bytes,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.generate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.header,
 tacenta_session_unit.zeroize.Zeroizing.new,
 tacenta_session_unit.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.alloc.vec.Vec.truncate,
 tacenta_session_unit.core.num.Usize.div_ceil,
 tacenta_session_unit.zeroize.Zeroize.Blanket.zeroize,
 tacenta_session_unit.tacenta_kem.EncapsState.Insts.CoreCloneClone.clone,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 tacenta_session_unit.core.option.Option.Insts.CoreCloneClone.clone,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut]
-/
#guard_msgs in
#print axioms Tacenta.SessionUnitBraidPreserveFacts.Braid.Run.inv

/--
info: 'Tacenta.SessionUnitBraidPreserveFacts.Braid.Run.receive_no_panic' depends on axioms: [propext,
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
 tacenta_session_unit.tacenta_kem.EncapsState.from_bytes,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.from_bytes,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.generate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.header,
 tacenta_session_unit.zeroize.Zeroizing.new,
 tacenta_session_unit.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.alloc.vec.Vec.truncate,
 tacenta_session_unit.core.num.Usize.div_ceil,
 tacenta_session_unit.zeroize.Zeroize.Blanket.zeroize,
 tacenta_session_unit.tacenta_kem.EncapsState.Insts.CoreCloneClone.clone,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 tacenta_session_unit.core.option.Option.Insts.CoreCloneClone.clone,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut]
-/
#guard_msgs in
#print axioms Tacenta.SessionUnitBraidPreserveFacts.Braid.Run.receive_no_panic

/--
info: 'Tacenta.SessionUnitBraidPreserveFacts.Braid.Run.receive_refines' depends on axioms: [propext,
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
 tacenta_session_unit.tacenta_kem.EncapsState.from_bytes,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.from_bytes,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.generate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.header,
 tacenta_session_unit.zeroize.Zeroizing.new,
 tacenta_session_unit.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.alloc.vec.Vec.truncate,
 tacenta_session_unit.core.num.Usize.div_ceil,
 tacenta_session_unit.zeroize.Zeroize.Blanket.zeroize,
 tacenta_session_unit.tacenta_kem.EncapsState.Insts.CoreCloneClone.clone,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 tacenta_session_unit.core.option.Option.Insts.CoreCloneClone.clone,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut]
-/
#guard_msgs in
#print axioms Tacenta.SessionUnitBraidPreserveFacts.Braid.Run.receive_refines

/--
info: 'Tacenta.SessionUnitBraidPreserveFacts.inv_not_sized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kem.EncapsState,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair]
-/
#guard_msgs in
#print axioms Tacenta.SessionUnitBraidPreserveFacts.inv_not_sized

/--
info: 'Tacenta.SessionUnitBraidPreserveFacts.TruncateLen_is' depends on axioms: [propext,
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
#print axioms Tacenta.SessionUnitBraidPreserveFacts.TruncateLen_is

/--
info: 'Tacenta.SessionUnitBraidPreserveFacts.truncateLen_model' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.rand_core_1.error.Error]
-/
#guard_msgs in
#print axioms Tacenta.SessionUnitBraidPreserveFacts.truncateLen_model

/--
info: 'Tacenta.SessionUnitBraidPreserveFacts.laws_model' depends on axioms: [propext,
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
#print axioms Tacenta.SessionUnitBraidPreserveFacts.laws_model

/-! ## Statement pins

The axiom pins hold the constants a result depends on and not what it says.  These hold the
statements of the results below while they are present; no gate requires a statement pin to exist. -/

/--
info: Tacenta.SessionUnitBraidPreserveFacts.invariant_true_gives_sized (hct1 : Ct1LenTotal) (hct2 : Ct2LenTotal)
  (hhdr : HeaderLenTotal) (hek : EkVectorLenTotal) (b : Braid) (h : b.invariant = ok true) : Braid.sized b
-/
#guard_msgs in
#check Tacenta.SessionUnitBraidPreserveFacts.invariant_true_gives_sized

/--
info: Tacenta.SessionUnitBraidPreserveFacts.Braid.Run.sized_of_start (hl : Laws) (hct1 : Ct1LenTotal) (hct2 : Ct2LenTotal)
  (hhdr : HeaderLenTotal) (hek : EkVectorLenTotal) (hencaps1 : Encapsulate1Total) {b : Braid}
  (hr : Braid.Run Tacenta.SessionUnitBraidPreserveFacts.Braid.Start b) : Braid.sized b
-/
#guard_msgs in
#check Tacenta.SessionUnitBraidPreserveFacts.Braid.Run.sized_of_start

/--
info: Tacenta.SessionUnitBraidPreserveFacts.inv_not_sized (epoch : U64) (auth : Auth)
  (kp : tacenta_session_unit.tacenta_kem.IncrementalKeyPair) (ek_enc : Encoder) :
  have d := { size := 4097#usize, needed := 129#usize, «have» := alloc.vec.Vec.new Chunk };
  have s := State.HeaderSent epoch auth kp d ek_enc;
  Tacenta.SessionUnitBraidImportInv.Braid.Inv { state := s } ∧ ¬Braid.sized { state := s }
-/
#guard_msgs in
#check Tacenta.SessionUnitBraidPreserveFacts.inv_not_sized

/--
info: Tacenta.SessionUnitBraidPreserveFacts.laws_model :
  (Laws ↔
      (Tacenta.SessionUnitBraidPreserveFacts.TruncateLenShape fun {T} =>
          Tacenta.UnitSatisfiabilityJoint.Interp.real.vecTruncate) ∧
        Tacenta.UnitSatisfiabilityJoint.DivCeilValueShape Tacenta.UnitSatisfiabilityJoint.Interp.real) ∧
    (Tacenta.SessionUnitBraidPreserveFacts.TruncateLenShape fun {T} =>
        Tacenta.UnitSatisfiabilityJoint.Interp.model.vecTruncate) ∧
      Tacenta.UnitSatisfiabilityJoint.DivCeilValueShape Tacenta.UnitSatisfiabilityJoint.Interp.model ∧
        Tacenta.UnitSatisfiabilityJoint.StdLaws Tacenta.UnitSatisfiabilityJoint.Interp.model
-/
#guard_msgs in
#check Tacenta.SessionUnitBraidPreserveFacts.laws_model

/--
info: Tacenta.SessionUnitBraidPreserveFacts.Braid.Run.receive_no_panic (hl : Laws) (hencaps1 : Encapsulate1Total)
  (hdnew : DecoderNewTotal) (hdadd : DecoderAddChunkTotal) (hdmsg : DecoderMessageTotal) (hct1len : Ct1LenTotal)
  (hct2len : Ct2LenTotal) (hhdrlen : HeaderLenTotal) (hekveclen : EkVectorLenTotal) (hekvec : KeyPairEkVectorTotal)
  (henew : EncoderNewTotal) (hdecap : KeyPairDecapsulateTotal) (hkdf : HkdfSha256Total) (hmac : HmacSha256Total)
  (hvalek : ValidateEkTotal) (hencaps2 : Encapsulate2Total) (henc : EncoderCloneTotal) (hdec : DecoderCloneTotal)
  (hkp : KeyPairCloneTotal) (hes : EncapsStateCloneTotal) (hopt : OptionCloneTotal) (hz : ZeroizingArrayRoundTrip)
  (hzz : ArrayZeroizeTotal) (hrf : RangeFullIndexTotal) {self : Braid}
  (hrun : Braid.Run Tacenta.SessionUnitBraidPreserveFacts.Braid.Start self) (msg : Msg) :
  self.receive msg ⦃ _result => True ⦄
-/
#guard_msgs in
#check Tacenta.SessionUnitBraidPreserveFacts.Braid.Run.receive_no_panic

/--
info: Tacenta.SessionUnitBraidPreserveFacts.sized_decoders_bounded {s : State} (h : State.sized s) : State.decoders_bounded s
-/
#guard_msgs in
#check Tacenta.SessionUnitBraidPreserveFacts.sized_decoders_bounded

/--
info: Tacenta.SessionUnitBraidPreserveFacts.from_bytes_sized (hct1 : Ct1LenTotal) (hct2 : Ct2LenTotal) (hhdr : HeaderLenTotal)
  (hek : EkVectorLenTotal) (bytes : Slice U8) (b : Braid) (h : Braid.from_bytes bytes = ok (core.result.Result.Ok b)) :
  Braid.sized b
-/
#guard_msgs in
#check Tacenta.SessionUnitBraidPreserveFacts.from_bytes_sized

/--
info: Tacenta.SessionUnitBraidPreserveFacts.Braid.Run.inv (hl : Laws) (hct1 : Ct1LenTotal) (hct2 : Ct2LenTotal)
  (hhdr : HeaderLenTotal) (hek : EkVectorLenTotal) (hencaps1 : Encapsulate1Total) {b : Braid}
  (hr : Braid.Run Tacenta.SessionUnitBraidPreserveFacts.Braid.Start b) : Tacenta.SessionUnitBraidImportInv.Braid.Inv b
-/
#guard_msgs in
#check Tacenta.SessionUnitBraidPreserveFacts.Braid.Run.inv

/--
info: Tacenta.SessionUnitBraidPreserveFacts.Braid.Run.receive_refines {K : Model.Braid.Kem} (hl : Laws)
  (hencaps1 : Encapsulate1Total) (hka : Tacenta.SessionUnitBraidT3.KemAgreesFor K)
  (hea : Tacenta.SessionUnitBraidT3.ErasureAgrees) (hmac : Tacenta.SessionUnitBraidT3.BraidHmacAgrees)
  (hkdf : Tacenta.SessionUnitBraidT3.BraidHkdfAgrees) (hlens : Tacenta.SessionUnitBraidT3.KemLenAgrees K)
  (hvalek : Tacenta.SessionUnitBraidT3.ValidateEkAgrees K) (hencaps2len : Encapsulate2Total)
  (hdadd : DecoderAddChunkTotal) (hdmsg : DecoderMessageTotal) (hct1lenB : Ct1LenTotal) (hct2lenB : Ct2LenTotal)
  (hheaderlenB : HeaderLenTotal) (hekveclenB : EkVectorLenTotal) (hkcl : Tacenta.SessionUnitBraidT3.KemCloneAgrees)
  (hecl : Tacenta.SessionUnitBraidT3.ErasureCloneAgrees) (henc : EncoderCloneTotal) (hdec : DecoderCloneTotal)
  (hkp : KeyPairCloneTotal) (hes : EncapsStateCloneTotal) (hopt : OptionCloneTotal) (hz : ZeroizingArrayRoundTrip)
  (hzz : ArrayZeroizeTotal) (hrf : RangeFullIndexTotal) {self : Braid}
  (hrun : Braid.Run Tacenta.SessionUnitBraidPreserveFacts.Braid.Start self) (msg : Msg)
  (hepoch : ↑(State.epoch_val self.state) + 1 < U64.max) {model : Model.Braid.BraidState} {modelMsg : Model.Braid.Msg}
  (hrel : Tacenta.SessionUnitBraidT3.StateRefines K self.state model)
  (hmsg : Tacenta.SessionUnitBraidT3.MsgRefines msg modelMsg)
  (hhonest : Tacenta.SessionUnitBraidT3.HonestChunk model modelMsg) :
  self.receive msg ⦃ result =>
    ↑result.1 = (Model.Braid.receive K model modelMsg).2.2.epoch - 1 ∧
      Tacenta.SessionUnitBraidT3.OptionOutputRefines result.2.1 (Model.Braid.receive K model modelMsg).2.1 ∧
        Tacenta.SessionUnitBraidT3.StateRefines K result.2.2.state (Model.Braid.receive K model modelMsg).2.2 ⦄
-/
#guard_msgs in
#check Tacenta.SessionUnitBraidPreserveFacts.Braid.Run.receive_refines

/--
info: Tacenta.SessionUnitBraidPreserveFacts.TruncateLen_is :
  TruncateLen ↔
    Tacenta.SessionUnitBraidPreserveFacts.TruncateLenShape fun {T} =>
      Tacenta.UnitSatisfiabilityJoint.Interp.real.vecTruncate
-/
#guard_msgs in
#check Tacenta.SessionUnitBraidPreserveFacts.TruncateLen_is

/--
info: Tacenta.SessionUnitBraidPreserveFacts.truncateLen_model :
  Tacenta.SessionUnitBraidPreserveFacts.TruncateLenShape fun {T} =>
    Tacenta.UnitSatisfiabilityJoint.Interp.model.vecTruncate
-/
#guard_msgs in
#check Tacenta.SessionUnitBraidPreserveFacts.truncateLen_model

/-! ## Definition pins

The definitions that carry the claim.  A change to a clause, a constructor or a law fails the
build while its pin is present; no gate requires a definition pin to exist. -/

/--
info: def Tacenta.SessionUnitBraidPreserveFacts.Braid.Decoded : Braid → Prop :=
fun b => ∃ bytes, Braid.from_bytes bytes = ok (core.result.Result.Ok b)
-/
#guard_msgs in
#print Tacenta.SessionUnitBraidPreserveFacts.Braid.Decoded

/--
info: def Tacenta.SessionUnitBraidPreserveFacts.Braid.Start : Braid → Prop :=
fun b => Braid.Constructed b ∨ Tacenta.SessionUnitBraidPreserveFacts.Braid.Decoded b
-/
#guard_msgs in
#print Tacenta.SessionUnitBraidPreserveFacts.Braid.Start

/--
info: def Tacenta.SessionUnitBraidPreserveFacts.TruncateLenShape : ({T : Type} →
    Type → alloc.vec.Vec T → Usize → Result (alloc.vec.Vec T)) →
  Prop :=
fun f => ∀ (v : alloc.vec.Vec U8) (n : Usize), ∃ r, f Global v n = ok r ∧ r.length ≤ ↑n
-/
#guard_msgs in
#print Tacenta.SessionUnitBraidPreserveFacts.TruncateLenShape
