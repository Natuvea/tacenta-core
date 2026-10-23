import Translation.KdfTripleUnitT3Kdf
import Translation.KdfBridgeHmac
import Translation.KdfBridgeHkdf
import Translation.UnitT3
import Translation.UnitSpqrT3
import Translation.UnitTripleT3
import Translation.UnitSatisfiabilityTripleLaws

/-!
# The three-leaf unit's KDF hypotheses, as theorems

The three-leaf unit's translation includes `tacenta-kdf`'s bodies (`run-aeneas.sh`, `--include-kdf`), so its
`tacenta_kdf.hmac_sha256` and `tacenta_kdf.hkdf_sha256` are definitions. This module proves, for the unit's own
constants, the KDF hypotheses its T1 and T3 results take (`UnitT1.HmacTotal`, `UnitT1.HkdfTotal`,
`UnitT3.HmacAgrees`, `UnitT3.HkdfAgrees`, `UnitSpqrT3.SpqrHkdfAgrees`, `UnitTripleT3.TripleHkdfAgrees`) and
`UnitSatisfiabilityTripleLaws.LawHkdf`, from which that module derives the sparse ratchet's and the Triple's
`KdfRkTotal`, `KdfCkTotal` and `KdfInitTotal`. The proofs are the copied ones ported onto this translation
(`KdfTripleUnitT*`, written by `scripts/port-kdf-proofs.sh`) and the bridge to tacenta-model's KDF.

No result here takes a hypothesis, and each rests on the kernel's three axioms. The theorems that take these
hypotheses keep them.

What it does not show: that tacenta-model's KDF is RFC 4231's HMAC or RFC 5869's HKDF (vectors, not
proof); any cryptographic property; timing or erasure; the translation's fidelity.
-/

namespace Tacenta.KdfTripleUnitAgreements

open Aeneas Aeneas.Std Result

theorem hmacAgrees : Tacenta.UnitT3.HmacAgrees := by
  intro key data
  obtain ⟨r, hr, hv⟩ := WP.spec_imp_exists (Tacenta.KdfProofTripleUnit.hmac_sha256_spec key data)
  rw [KdfBridge.hmac_eq] at hv
  exact ⟨r, by unfold tacenta_triple_unit.tacenta_kdf.hmac_sha256; exact hr, hv⟩

theorem hkdfAgrees : Tacenta.UnitT3.HkdfAgrees := by
  intro N salt ikm info hN
  obtain ⟨r, hr, hv⟩ :=
    WP.spec_imp_exists (Tacenta.KdfProofTripleUnit.hkdf_sha256_spec N salt ikm info hN)
  rw [KdfBridge.hkdf_eq] at hv
  exact ⟨r, by unfold tacenta_triple_unit.tacenta_kdf.hkdf_sha256; exact hr, hv⟩

theorem hmacTotal : Tacenta.UnitT1.HmacTotal :=
  Tacenta.UnitT3.HmacAgrees.total hmacAgrees

theorem hkdfTotal : Tacenta.UnitT1.HkdfTotal :=
  Tacenta.UnitT3.HkdfAgrees.total hkdfAgrees

theorem spqrHkdfAgrees : Tacenta.UnitSpqrT3.SpqrHkdfAgrees := by
  intro N salt ikm info hN
  exact hkdfAgrees N salt ikm info hN

theorem tripleHkdfAgrees : Tacenta.UnitTripleT3.TripleHkdfAgrees := by
  intro N salt ikm info hN
  exact hkdfAgrees N salt ikm info hN

theorem lawHkdf : Tacenta.UnitSatisfiabilityTripleLaws.LawHkdf := by
  intro N salt ikm info hN
  obtain ⟨r, hr, _⟩ := hkdfAgrees N salt ikm info hN
  exact ⟨r, hr⟩

end Tacenta.KdfTripleUnitAgreements

/-! ## Pins

The constants each result depends on, and the statement of each result and definition, held by the
build.  `attest.py` requires every one of them (`REQUIRED_PINS`, `REQUIRED_STATEMENT_PINS`,
`REQUIRED_PRINT_FORM`). -/

/--
info: 'Tacenta.KdfTripleUnitAgreements.hmacAgrees' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.KdfTripleUnitAgreements.hmacAgrees

/--
info: 'Tacenta.KdfTripleUnitAgreements.hkdfAgrees' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.KdfTripleUnitAgreements.hkdfAgrees

/--
info: 'Tacenta.KdfTripleUnitAgreements.hmacTotal' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.KdfTripleUnitAgreements.hmacTotal

/--
info: 'Tacenta.KdfTripleUnitAgreements.hkdfTotal' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.KdfTripleUnitAgreements.hkdfTotal

/--
info: 'Tacenta.KdfTripleUnitAgreements.spqrHkdfAgrees' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.KdfTripleUnitAgreements.spqrHkdfAgrees

/--
info: 'Tacenta.KdfTripleUnitAgreements.tripleHkdfAgrees' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.KdfTripleUnitAgreements.tripleHkdfAgrees

/--
info: 'Tacenta.KdfTripleUnitAgreements.lawHkdf' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.KdfTripleUnitAgreements.lawHkdf

/--
info: Tacenta.KdfTripleUnitAgreements.hmacAgrees : Tacenta.UnitT3.HmacAgrees
-/
#guard_msgs in
#check @Tacenta.KdfTripleUnitAgreements.hmacAgrees

/--
info: Tacenta.KdfTripleUnitAgreements.hkdfAgrees : Tacenta.UnitT3.HkdfAgrees
-/
#guard_msgs in
#check @Tacenta.KdfTripleUnitAgreements.hkdfAgrees

/--
info: Tacenta.KdfTripleUnitAgreements.hmacTotal : Tacenta.UnitT1.HmacTotal
-/
#guard_msgs in
#check @Tacenta.KdfTripleUnitAgreements.hmacTotal

/--
info: Tacenta.KdfTripleUnitAgreements.hkdfTotal : Tacenta.UnitT1.HkdfTotal
-/
#guard_msgs in
#check @Tacenta.KdfTripleUnitAgreements.hkdfTotal

/--
info: Tacenta.KdfTripleUnitAgreements.spqrHkdfAgrees : Tacenta.UnitSpqrT3.SpqrHkdfAgrees
-/
#guard_msgs in
#check @Tacenta.KdfTripleUnitAgreements.spqrHkdfAgrees

/--
info: Tacenta.KdfTripleUnitAgreements.tripleHkdfAgrees : Tacenta.UnitTripleT3.TripleHkdfAgrees
-/
#guard_msgs in
#check @Tacenta.KdfTripleUnitAgreements.tripleHkdfAgrees

/--
info: Tacenta.KdfTripleUnitAgreements.lawHkdf : Tacenta.UnitSatisfiabilityTripleLaws.LawHkdf
-/
#guard_msgs in
#check @Tacenta.KdfTripleUnitAgreements.lawHkdf
