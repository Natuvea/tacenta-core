import Translation.UnitOracleModel

/-!
# The DH clauses of `OracleOf`: `dhPublic`, `dhAgree`, `identityValid`

`UnitLifecycleIntegrationScreen.lean` left these three clauses undecided. Decision: each is
satisfiable, jointly with #220's axiom base and #234's laws, by an oracle that is not degenerate.

* `UnitOracleShape.lean` derives each from its law, for every interpretation:
  `dhPublicClause_of_laws` (`public_key` returns, the private-key view is injective),
  `dhAgreeClause_of_laws` (`agree` returns, both views injective), and
  `identityValidClause_of_laws` (`as_bytes` and `is_prime_order_public` return, the public-key view
  is injective; the canonical-encoding test is translated code, and `is_canonical_x25519_spec`
  shows it returns).
* `dh_clauses_in_model`, here: the three clauses hold at the joint interpretation of
  `UnitOracleModel.lean`, where #220's axiom base and the other laws hold too (`modelO_laws`), and
  the oracle there is not degenerate. Its `dhPublic` is the model's public key; its `dhAgree`
  gives both sides of an exchange the same answer, refuses some pairs and accepts others; its
  `identityValid` refuses the zero key and accepts another.

What this does not show: that the real `agree`, `public_key` or `is_prime_order_public` compute
X25519 or the identity-key rule. The clauses relate the code to the oracle and say nothing about
what the oracle computes; the model's DH is a toy (exclusive or).
-/

open Aeneas Aeneas.Std Result
open tacenta_session_unit
open Tacenta.UnitLifecycleT3
open Tacenta.UnitOracleShape
open Tacenta.UnitOracleModel

namespace Tacenta.UnitOracleDh

open Tacenta.UnitLifecycleIntegrationScreen (kemModelValid)

/-- The key `1, 0, ..., 0`: canonical and not zero. -/
def one32 : Array U8 32#usize := ⟨1#u8 :: List.replicate 31 0#u8, by simp⟩

theorem model_dhPublicClause : DhPublicClause M dhM oracleM :=
  dhPublicClause_of_laws InterpO.model dhM kemM kemModelValid kemModelE signS modelO_DhCodec
    modelO_dhViewInjective.1

theorem model_dhAgreeClause : DhAgreeClause M dhM oracleM :=
  dhAgreeClause_of_laws InterpO.model dhM kemM kemModelValid kemModelE signS modelO_DhAgree
    modelO_dhViewInjective

theorem model_identityValidClause : IdentityValidClause M dhM oracleM :=
  identityValidClause_of_laws InterpO.model dhM kemM kemModelValid kemModelE signS modelO_DhCodec
    modelO_DhIdentity modelO_dhViewInjective.2

theorem oracleM_dhPublic (k : Array U8 32#usize) : oracleM.dhPublic (arrayOf k) = arrayOf k := by
  obtain ⟨pk, h, hv⟩ := model_dhPublicClause k
  have : pk = k := by simpa [M, InterpO.model] using h.symm
  subst this
  exact hv.symm

theorem oracleM_dhAgree (a b : Array U8 32#usize) :
    oracleM.dhAgree (arrayOf a) (arrayOf b) = (agreeModel a b).map arrayOf := by
  obtain ⟨r, h, hv⟩ := model_dhAgreeClause a b
  have : r = agreeModel a b := by simpa [M, InterpO.model] using h.symm
  subst this
  exact hv.symm

theorem xor32_comm (a b : Array U8 32#usize) : xor32 a b = xor32 b a := by
  apply Subtype.ext
  simp only [xor32]
  rw [List.zipWith_comm]
  congr 1
  funext x y
  congr 1
  exact BitVec.xor_comm _ _

theorem xor32_self (a : Array U8 32#usize) : (xor32 a a).val = zero32.val := by
  obtain ⟨l, hl⟩ := a
  simp only [xor32, zero32, Array.repeat, List.zipWith_self, BitVec.xor_self]
  rw [List.map_const', hl]
  rfl

theorem oracleM_identityValid (k : Array U8 32#usize) :
    oracleM.identityValid (arrayOf k) =
      (Tacenta.SessionUnitSessionT1.canonicalX25519 k && decide (k.val ≠ zero32.val)) := by
  obtain ⟨r, h, hv⟩ := model_identityValidClause k
  change oracleM.identityValid (dhM.publicKey k) = _
  rw [← hv]
  obtain ⟨c, hc, hcv⟩ :=
    Std.WP.spec_imp_exists (Tacenta.SessionUnitSessionT1.is_canonical_x25519_spec k)
  simp only [isValidIdentityKeyOf, isCanonicalKeyOf, M, InterpO.model, bind_tc_ok, hc] at h
  subst hcv
  split at h <;> simp_all

/-- **The three DH clauses hold at the joint interpretation, and its DH is not degenerate.** The
oracle's public key is the model's; agreement gives the two sides of an exchange the same answer;
it refuses a key paired with itself and accepts the pair of the zero key and `one32`; the
identity test refuses the zero key and accepts `one32`. -/
theorem dh_clauses_in_model :
    DhPublicClause M dhM oracleM ∧ DhAgreeClause M dhM oracleM ∧
      IdentityValidClause M dhM oracleM ∧
      (∀ k : Array U8 32#usize, oracleM.dhPublic (arrayOf k) = arrayOf k) ∧
      (∀ a b : Array U8 32#usize,
        oracleM.dhAgree (arrayOf a) (oracleM.dhPublic (arrayOf b)) =
          oracleM.dhAgree (arrayOf b) (oracleM.dhPublic (arrayOf a))) ∧
      (∀ a : Array U8 32#usize, oracleM.dhAgree (arrayOf a) (arrayOf a) = none) ∧
      oracleM.dhAgree (arrayOf zero32) (arrayOf one32) = some (arrayOf one32) ∧
      oracleM.identityValid (arrayOf zero32) = false ∧
      oracleM.identityValid (arrayOf one32) = true := by
  refine ⟨model_dhPublicClause, model_dhAgreeClause, model_identityValidClause,
    oracleM_dhPublic, ?_, ?_, ?_, ?_, ?_⟩
  · intro a b
    rw [oracleM_dhPublic, oracleM_dhPublic, oracleM_dhAgree, oracleM_dhAgree]
    simp only [agreeModel, xor32_comm a b]
  · intro a
    rw [oracleM_dhAgree]
    simp [agreeModel, xor32_self]
  · rw [oracleM_dhAgree]
    decide
  · rw [oracleM_identityValid]
    simp
  · rw [oracleM_identityValid]
    decide

end Tacenta.UnitOracleDh

/-! ## Pins

The axiom list and the statement of each result, held by the build. `attest.py` requires them
(`REQUIRED_PINS`, `REQUIRED_STATEMENT_PINS`). -/

/--
info: 'Tacenta.UnitOracleDh.dh_clauses_in_model' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 rand_core_1.error.Error]
-/
#guard_msgs in
#print axioms Tacenta.UnitOracleDh.dh_clauses_in_model

/--
info: Tacenta.UnitOracleDh.dh_clauses_in_model : DhPublicClause M dhM oracleM ∧
  DhAgreeClause M dhM oracleM ∧
    IdentityValidClause M dhM oracleM ∧
      (∀ (k : Std.Array U8 32#usize), oracleM.dhPublic (arrayOf k) = arrayOf k) ∧
        (∀ (a b : Std.Array U8 32#usize),
            oracleM.dhAgree (arrayOf a) (oracleM.dhPublic (arrayOf b)) =
              oracleM.dhAgree (arrayOf b) (oracleM.dhPublic (arrayOf a))) ∧
          (∀ (a : Std.Array U8 32#usize), oracleM.dhAgree (arrayOf a) (arrayOf a) = none) ∧
            oracleM.dhAgree (arrayOf zero32) (arrayOf Tacenta.UnitOracleDh.one32) =
                some (arrayOf Tacenta.UnitOracleDh.one32) ∧
              oracleM.identityValid (arrayOf zero32) = false ∧
                oracleM.identityValid (arrayOf Tacenta.UnitOracleDh.one32) = true
-/
#guard_msgs in
#check @Tacenta.UnitOracleDh.dh_clauses_in_model

/--
info: 'Tacenta.UnitOracleDh.oracleM_dhPublic' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 rand_core_1.error.Error]
-/
#guard_msgs in
#print axioms Tacenta.UnitOracleDh.oracleM_dhPublic

/--
info: 'Tacenta.UnitOracleDh.oracleM_dhAgree' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 rand_core_1.error.Error]
-/
#guard_msgs in
#print axioms Tacenta.UnitOracleDh.oracleM_dhAgree

/--
info: 'Tacenta.UnitOracleDh.oracleM_identityValid' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 rand_core_1.error.Error]
-/
#guard_msgs in
#print axioms Tacenta.UnitOracleDh.oracleM_identityValid

/--
info: Tacenta.UnitOracleDh.oracleM_identityValid : ∀ (k : Std.Array U8 32#usize),
  oracleM.identityValid (arrayOf k) = (Tacenta.SessionUnitSessionT1.canonicalX25519 k && decide (↑k ≠ ↑zero32))
-/
#guard_msgs in
#check @Tacenta.UnitOracleDh.oracleM_identityValid

/--
info: 'Tacenta.UnitOracleDh.xor32_comm' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitOracleDh.xor32_comm

/--
info: 'Tacenta.UnitOracleDh.xor32_self' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitOracleDh.xor32_self
