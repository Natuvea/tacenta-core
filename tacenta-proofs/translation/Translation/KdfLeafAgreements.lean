import Translation.KdfRatchetT3Kdf
import Translation.KdfSessionT3Kdf
import Translation.KdfSpqrT3Kdf
import Translation.KdfBraidT3Kdf
import Translation.KdfBridgeHmac
import Translation.KdfBridgeHkdf
import Translation.T3
import Translation.SessionT3
import Translation.SpqrT3
import Translation.BraidT3
import Translation.SatisfiabilitySpqrLaws

/-!
# The leaf translations' KDF hypotheses, as theorems

The classical ratchet, PQXDH session, sparse ratchet and Braid translations include `tacenta-kdf`'s bodies
(`run-aeneas.sh`, `--include-kdf`), so their `tacenta_kdf.hmac_sha256` and `tacenta_kdf.hkdf_sha256` are
definitions, one-line wrappers over the translated `hmac.hmac_sha256` and `hkdf.hkdf_sha256`. Each leaf's T1
and T3 results take hypotheses about them (`T1.HmacTotal`, `T3.HkdfAgrees`, `BraidT3.BraidHmacAgrees`, ...);
this module proves every one of them, for that leaf's own constants, from the copied proofs ported onto
each translation (`Kdf<Leaf>T*`, written by `scripts/port-kdf-proofs.sh`) and the bridge from their model
to tacenta-model's (`KdfBridge.hmac_eq`, `KdfBridge.hkdf_eq`). `SatisfiabilitySpqrLaws.LawHkdf`, from which
that module derives the sparse ratchet's `KdfRkTotal` and `KdfCkTotal`, is proved too.

No result here takes a hypothesis, and each rests on the kernel's three axioms. The theorems that take these
hypotheses keep them: what changes is that a reader can now supply each from here.

What it does not show: that tacenta-model's KDF is RFC 4231's HMAC or RFC 5869's HKDF (vectors, not
proof); any cryptographic property; timing or erasure; the translation's fidelity.
-/

namespace Tacenta.KdfLeafAgreements

open Aeneas Aeneas.Std Result

/-! ## The classical ratchet -/

theorem ratchet_hmacAgrees : Tacenta.T3.HmacAgrees := by
  intro key data
  obtain ⟨r, hr, hv⟩ := WP.spec_imp_exists (Tacenta.KdfProofRatchet.hmac_sha256_spec key data)
  rw [KdfBridge.hmac_eq] at hv
  exact ⟨r, by unfold tacenta_ratchet.tacenta_kdf.hmac_sha256; exact hr, hv⟩

theorem ratchet_hkdfAgrees : Tacenta.T3.HkdfAgrees := by
  intro N salt ikm info hN
  obtain ⟨r, hr, hv⟩ := WP.spec_imp_exists (Tacenta.KdfProofRatchet.hkdf_sha256_spec N salt ikm info hN)
  rw [KdfBridge.hkdf_eq] at hv
  exact ⟨r, by unfold tacenta_ratchet.tacenta_kdf.hkdf_sha256; exact hr, hv⟩

theorem ratchet_hmacTotal : Tacenta.T1.HmacTotal :=
  Tacenta.T3.HmacAgrees.total ratchet_hmacAgrees

theorem ratchet_hkdfTotal : Tacenta.T1.HkdfTotal :=
  Tacenta.T3.HkdfAgrees.total ratchet_hkdfAgrees

/-! ## The PQXDH session -/

theorem session_hkdfAgrees : Tacenta.SessionT3.HkdfAgrees := by
  intro salt ikm info
  obtain ⟨r, hr, hv⟩ :=
    WP.spec_imp_exists (Tacenta.KdfProofSession.hkdf_sha256_spec 32#usize salt ikm info (by simp))
  rw [KdfBridge.hkdf_eq] at hv
  unfold tacenta_session.tacenta_kdf.hkdf_sha256
  rw [hr, WP.spec_ok]
  exact hv

theorem session_hkdfTotal : Tacenta.SessionT1.HkdfTotal := by
  intro N salt ikm info hN
  obtain ⟨r, hr, _⟩ := WP.spec_imp_exists (Tacenta.KdfProofSession.hkdf_sha256_spec N salt ikm info hN)
  exact ⟨r, by unfold tacenta_session.tacenta_kdf.hkdf_sha256; exact hr⟩

/-! ## The sparse ratchet -/

theorem spqr_hkdfAgrees : Tacenta.SpqrT3.SpqrHkdfAgrees := by
  intro N salt ikm info hN
  obtain ⟨r, hr, hv⟩ := WP.spec_imp_exists (Tacenta.KdfProofSpqr.hkdf_sha256_spec N salt ikm info hN)
  rw [KdfBridge.hkdf_eq] at hv
  exact ⟨r, by unfold tacenta_spqr.tacenta_kdf.hkdf_sha256; exact hr, hv⟩

theorem spqr_lawHkdf : Tacenta.SatisfiabilitySpqrLaws.LawHkdf := by
  intro N salt ikm info hN
  obtain ⟨r, hr, _⟩ := spqr_hkdfAgrees N salt ikm info hN
  exact ⟨r, hr⟩

/-! ## The Braid -/

theorem braid_hmacAgrees : Tacenta.BraidT3.BraidHmacAgrees := by
  intro key data
  obtain ⟨r, hr, hv⟩ := WP.spec_imp_exists (Tacenta.KdfProofBraid.hmac_sha256_spec key data)
  rw [KdfBridge.hmac_eq] at hv
  exact ⟨r, by unfold tacenta_braid.tacenta_kdf.hmac_sha256; exact hr, hv⟩

theorem braid_hkdfAgrees : Tacenta.BraidT3.BraidHkdfAgrees := by
  intro N salt ikm info hN
  obtain ⟨r, hr, hv⟩ := WP.spec_imp_exists (Tacenta.KdfProofBraid.hkdf_sha256_spec N salt ikm info hN)
  rw [KdfBridge.hkdf_eq] at hv
  exact ⟨r, by unfold tacenta_braid.tacenta_kdf.hkdf_sha256; exact hr, hv⟩

theorem braid_hmacTotal : Tacenta.BraidT1.HmacSha256Total :=
  Tacenta.BraidT3.BraidHmacAgrees.total braid_hmacAgrees

theorem braid_hkdfTotal : Tacenta.BraidT1.HkdfSha256Total :=
  Tacenta.BraidT3.BraidHkdfAgrees.total braid_hkdfAgrees

end Tacenta.KdfLeafAgreements

/-! ## Pins

The constants each result depends on, and the statement of each result and definition, held by the
build.  `attest.py` requires every one of them (`REQUIRED_PINS`, `REQUIRED_STATEMENT_PINS`,
`REQUIRED_PRINT_FORM`). -/

/--
info: 'Tacenta.KdfLeafAgreements.ratchet_hmacAgrees' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.KdfLeafAgreements.ratchet_hmacAgrees

/--
info: 'Tacenta.KdfLeafAgreements.ratchet_hkdfAgrees' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.KdfLeafAgreements.ratchet_hkdfAgrees

/--
info: 'Tacenta.KdfLeafAgreements.ratchet_hmacTotal' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.KdfLeafAgreements.ratchet_hmacTotal

/--
info: 'Tacenta.KdfLeafAgreements.ratchet_hkdfTotal' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.KdfLeafAgreements.ratchet_hkdfTotal

/--
info: 'Tacenta.KdfLeafAgreements.session_hkdfAgrees' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.KdfLeafAgreements.session_hkdfAgrees

/--
info: 'Tacenta.KdfLeafAgreements.session_hkdfTotal' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.KdfLeafAgreements.session_hkdfTotal

/--
info: 'Tacenta.KdfLeafAgreements.spqr_hkdfAgrees' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.KdfLeafAgreements.spqr_hkdfAgrees

/--
info: 'Tacenta.KdfLeafAgreements.spqr_lawHkdf' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.KdfLeafAgreements.spqr_lawHkdf

/--
info: 'Tacenta.KdfLeafAgreements.braid_hmacAgrees' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.KdfLeafAgreements.braid_hmacAgrees

/--
info: 'Tacenta.KdfLeafAgreements.braid_hkdfAgrees' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.KdfLeafAgreements.braid_hkdfAgrees

/--
info: 'Tacenta.KdfLeafAgreements.braid_hmacTotal' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.KdfLeafAgreements.braid_hmacTotal

/--
info: 'Tacenta.KdfLeafAgreements.braid_hkdfTotal' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.KdfLeafAgreements.braid_hkdfTotal

/--
info: Tacenta.KdfLeafAgreements.ratchet_hmacAgrees : Tacenta.T3.HmacAgrees
-/
#guard_msgs in
#check @Tacenta.KdfLeafAgreements.ratchet_hmacAgrees

/--
info: Tacenta.KdfLeafAgreements.ratchet_hkdfAgrees : Tacenta.T3.HkdfAgrees
-/
#guard_msgs in
#check @Tacenta.KdfLeafAgreements.ratchet_hkdfAgrees

/--
info: Tacenta.KdfLeafAgreements.ratchet_hmacTotal : Tacenta.T1.HmacTotal
-/
#guard_msgs in
#check @Tacenta.KdfLeafAgreements.ratchet_hmacTotal

/--
info: Tacenta.KdfLeafAgreements.ratchet_hkdfTotal : Tacenta.T1.HkdfTotal
-/
#guard_msgs in
#check @Tacenta.KdfLeafAgreements.ratchet_hkdfTotal

/--
info: Tacenta.KdfLeafAgreements.session_hkdfAgrees : Tacenta.SessionT3.HkdfAgrees
-/
#guard_msgs in
#check @Tacenta.KdfLeafAgreements.session_hkdfAgrees

/--
info: Tacenta.KdfLeafAgreements.session_hkdfTotal : Tacenta.SessionT1.HkdfTotal
-/
#guard_msgs in
#check @Tacenta.KdfLeafAgreements.session_hkdfTotal

/--
info: Tacenta.KdfLeafAgreements.spqr_hkdfAgrees : Tacenta.SpqrT3.SpqrHkdfAgrees
-/
#guard_msgs in
#check @Tacenta.KdfLeafAgreements.spqr_hkdfAgrees

/--
info: Tacenta.KdfLeafAgreements.spqr_lawHkdf : Tacenta.SatisfiabilitySpqrLaws.LawHkdf
-/
#guard_msgs in
#check @Tacenta.KdfLeafAgreements.spqr_lawHkdf

/--
info: Tacenta.KdfLeafAgreements.braid_hmacAgrees : Tacenta.BraidT3.BraidHmacAgrees
-/
#guard_msgs in
#check @Tacenta.KdfLeafAgreements.braid_hmacAgrees

/--
info: Tacenta.KdfLeafAgreements.braid_hkdfAgrees : Tacenta.BraidT3.BraidHkdfAgrees
-/
#guard_msgs in
#check @Tacenta.KdfLeafAgreements.braid_hkdfAgrees

/--
info: Tacenta.KdfLeafAgreements.braid_hmacTotal : Tacenta.BraidT1.HmacSha256Total
-/
#guard_msgs in
#check @Tacenta.KdfLeafAgreements.braid_hmacTotal

/--
info: Tacenta.KdfLeafAgreements.braid_hkdfTotal : Tacenta.BraidT1.HkdfSha256Total
-/
#guard_msgs in
#check @Tacenta.KdfLeafAgreements.braid_hkdfTotal
