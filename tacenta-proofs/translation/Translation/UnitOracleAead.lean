import Translation.UnitOracleModel

/-!
# The AEAD clauses of `OracleOf`: `aeadSeal`, `aeadOpen`

`UnitLifecycleIntegrationScreen.lean` left these two clauses undecided. Decision: both are
satisfiable, jointly with #220's axiom base and #234's laws, by an oracle that is not degenerate.

* `UnitOracleShape.lean` derives each from its law, for every interpretation:
  `aeadSealClause_of_laws` (`encrypt` returns, from `AeadSealBounded`) and `aeadOpenClause_of_laws`
  (`decrypt` returns, `AeadOpenTotal`). Keys, nonces and byte strings are viewed by `arrayOf` and
  `sliceOf`, which are injective, so no view law is needed.
* `aead_clauses_in_model`, here: both clauses hold at the joint interpretation of
  `UnitOracleModel.lean`, and the oracle there opens what it seals (for a plaintext shorter than
  the largest `usize`) and refuses the empty ciphertext.

The clauses pass the fourth and fifth arguments of `aead::encrypt` to the fourth and fifth of the
oracle's `aeadSeal` in order. `tacenta-core/boundary/src/aead.rs` takes the plaintext fourth and the
associated data fifth, and the model calls `aeadSeal` with the plaintext fourth, so the order agrees;
`OracleOf` names its two binders `ad` and `plaintext`, the other way round, which changes nothing
in the statement.

What this does not show: that the real AEAD authenticates or hides anything. The model's AEAD is a
toy (a zero byte in front).
-/

open Aeneas Aeneas.Std Result
open tacenta_session_unit
open Tacenta.UnitLifecycleT3
open Tacenta.UnitOracleShape
open Tacenta.UnitOracleModel

namespace Tacenta.UnitOracleAead

open Tacenta.UnitLifecycleIntegrationScreen (kemModelValid)

theorem model_aeadSealClause : AeadSealClause M oracleM :=
  aeadSealClause_of_laws InterpO.model dhM kemM kemModelValid kemModelE signS
    modelO_AeadSealBounded

theorem model_aeadOpenClause : AeadOpenClause M oracleM :=
  aeadOpenClause_of_laws InterpO.model dhM kemM kemModelValid kemModelE signS modelO_AeadOpen

theorem oracleM_aeadSeal (k1 k2 : Array U8 32#usize) (iv : Array U8 16#usize)
    (x4 x5 : Slice U8) :
    oracleM.aeadSeal (arrayOf k1) (arrayOf k2) (arrayOf iv) (sliceOf x4) (sliceOf x5) =
      vecOf (sealModel x4) := by
  obtain ⟨r, h, hv⟩ := model_aeadSealClause k1 k2 iv x4 x5
  have : r = sealModel x4 := by simpa [M, InterpO.model] using h.symm
  subst this
  exact hv.symm

theorem oracleM_aeadOpen (k1 k2 : Array U8 32#usize) (iv : Array U8 16#usize)
    (c ad : Slice U8) :
    oracleM.aeadOpen (arrayOf k1) (arrayOf k2) (arrayOf iv) (sliceOf c) (sliceOf ad) =
      resultOptionOf vecOf (openModel c) := by
  obtain ⟨r, h, hv⟩ := model_aeadOpenClause k1 k2 iv c ad
  have : r = openModel c := by simpa [M, InterpO.model] using h.symm
  subst this
  exact hv.symm

theorem openModel_zero_cons (c : Slice U8) (rest : List U8) (h : c.val = 0#u8 :: rest) :
    ∃ v : alloc.vec.Vec U8, openModel c = .Ok v ∧ v.val = rest := by
  unfold openModel
  split
  · rename_i x rest' h'
    rw [h] at h'
    injection h' with hx hr
    subst hx; subst hr
    exact ⟨_, if_pos rfl, rfl⟩
  · rename_i h'
    rw [h] at h'
    cases h'

theorem openModel_nil (c : Slice U8) (h : c.val = []) : openModel c = .Err () := by
  unfold openModel
  split
  · rename_i x rest h'
    rw [h] at h'
    cases h'
  · rfl

/-- **The two AEAD clauses hold at the joint interpretation, and its AEAD is not degenerate.** The
oracle opens what it seals, for a plaintext shorter than the largest `usize`, and refuses the empty
ciphertext. -/
theorem aead_clauses_in_model :
    AeadSealClause M oracleM ∧ AeadOpenClause M oracleM ∧
      (∀ (k1 k2 : Array U8 32#usize) (iv : Array U8 16#usize) (plaintext ad : Slice U8),
        plaintext.val.length + 1 ≤ Usize.max →
        oracleM.aeadOpen (arrayOf k1) (arrayOf k2) (arrayOf iv)
            (oracleM.aeadSeal (arrayOf k1) (arrayOf k2) (arrayOf iv) (sliceOf plaintext)
              (sliceOf ad))
            (sliceOf ad) = some (sliceOf plaintext)) ∧
      (∀ (k1 k2 : Array U8 32#usize) (iv : Array U8 16#usize) (ad : Slice U8),
        oracleM.aeadOpen (arrayOf k1) (arrayOf k2) (arrayOf iv) [] (sliceOf ad) = none) := by
  refine ⟨model_aeadSealClause, model_aeadOpenClause, ?_, ?_⟩
  · intro k1 k2 iv plaintext ad hlen
    rw [oracleM_aeadSeal]
    let c : Slice U8 := ⟨(sealModel plaintext).val, (sealModel plaintext).property⟩
    have hc : vecOf (sealModel plaintext) = sliceOf c := rfl
    have hcv : c.val = 0#u8 :: plaintext.val := by
      show (sealModel plaintext).val = _
      unfold sealModel
      rw [dif_pos hlen]
    rw [hc, oracleM_aeadOpen]
    obtain ⟨v, hv, hvv⟩ := openModel_zero_cons c plaintext.val hcv
    rw [hv]
    simp only [resultOptionOf, vecOf, sliceOf, hvv]
  · intro k1 k2 iv ad
    have h := oracleM_aeadOpen k1 k2 iv (Slice.new U8) ad
    rw [openModel_nil _ rfl] at h
    exact h
end Tacenta.UnitOracleAead

/-! ## Pins

The axiom list and the statement of each result, held by the build. `attest.py` requires them
(`REQUIRED_PINS`, `REQUIRED_STATEMENT_PINS`). -/

/--
info: 'Tacenta.UnitOracleAead.aead_clauses_in_model' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 rand_core_1.error.Error]
-/
#guard_msgs in
#print axioms Tacenta.UnitOracleAead.aead_clauses_in_model

/--
info: Tacenta.UnitOracleAead.aead_clauses_in_model : AeadSealClause M oracleM ∧
  AeadOpenClause M oracleM ∧
    (∀ (k1 k2 : Std.Array U8 32#usize) (iv : Std.Array U8 16#usize) (plaintext ad : Slice U8),
        (↑plaintext).length + 1 ≤ Usize.max →
          oracleM.aeadOpen (arrayOf k1) (arrayOf k2) (arrayOf iv)
              (oracleM.aeadSeal (arrayOf k1) (arrayOf k2) (arrayOf iv) (sliceOf plaintext) (sliceOf ad)) (sliceOf ad) =
            some (sliceOf plaintext)) ∧
      ∀ (k1 k2 : Std.Array U8 32#usize) (iv : Std.Array U8 16#usize) (ad : Slice U8),
        oracleM.aeadOpen (arrayOf k1) (arrayOf k2) (arrayOf iv) [] (sliceOf ad) = none
-/
#guard_msgs in
#check @Tacenta.UnitOracleAead.aead_clauses_in_model

/--
info: 'Tacenta.UnitOracleAead.oracleM_aeadSeal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 rand_core_1.error.Error]
-/
#guard_msgs in
#print axioms Tacenta.UnitOracleAead.oracleM_aeadSeal

/--
info: Tacenta.UnitOracleAead.oracleM_aeadSeal : ∀ (k1 k2 : Std.Array U8 32#usize) (iv : Std.Array U8 16#usize)
  (x4 x5 : Slice U8),
  oracleM.aeadSeal (arrayOf k1) (arrayOf k2) (arrayOf iv) (sliceOf x4) (sliceOf x5) = vecOf (sealModel x4)
-/
#guard_msgs in
#check @Tacenta.UnitOracleAead.oracleM_aeadSeal

/--
info: 'Tacenta.UnitOracleAead.oracleM_aeadOpen' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 rand_core_1.error.Error]
-/
#guard_msgs in
#print axioms Tacenta.UnitOracleAead.oracleM_aeadOpen

/--
info: Tacenta.UnitOracleAead.oracleM_aeadOpen : ∀ (k1 k2 : Std.Array U8 32#usize) (iv : Std.Array U8 16#usize)
  (c ad : Slice U8),
  oracleM.aeadOpen (arrayOf k1) (arrayOf k2) (arrayOf iv) (sliceOf c) (sliceOf ad) = resultOptionOf vecOf (openModel c)
-/
#guard_msgs in
#check @Tacenta.UnitOracleAead.oracleM_aeadOpen

/--
info: 'Tacenta.UnitOracleAead.openModel_zero_cons' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitOracleAead.openModel_zero_cons

/--
info: 'Tacenta.UnitOracleAead.openModel_nil' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitOracleAead.openModel_nil
