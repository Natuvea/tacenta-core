/- Copied from a separate, unpublished repository, written by the maintainer with tool assistance and
read so far only by tool-assisted sessions (no human has yet read the three Rust files or their
proofs), that holds a SHA-256, HMAC-SHA256 and HKDF-SHA256 with their proofs, the source of `tacenta-core/kdf/src` (pinned there by
commit and file digests): its bridge file `Hmac.lean`, at commit `646fcdadb943`. Elaborated
here against the Session unit's own translation of those bodies. Changes from the source: the
translated crate's namespace is `tacenta_session_unit.tacenta_kdf`, the Session unit's
translation of `tacenta-kdf`; the source's other namespaces are renamed `KdfStandardModel`,
`Tacenta.KdfProof` and `KdfBridge`; its imports name this package's `Kdf*` modules.
Of the source's model only the SHA-256, HMAC and HKDF files were copied. "This repository" in the
prose below means that implementation, and a path such as `scripts/...` or `std/...` names one of
its files. -/
import Translation.KdfBridgeSha256
import Translation.KdfModelHmac
import Model.Kdf

/-!
# Bridge: HMAC-SHA256

`KdfStandardModel.hmac k m = Model.Kdf.hmac k m` for every key and message.

With `KdfBridge.sha256_eq` the hashes agree, so what remains is the key
preprocessing and the pads. This repository's `Hmac.K0` follows FIPS 198-1 §4
steps 1–3 as three cases; tacenta-model hashes a key longer than 64 bytes and
then zero-pads to 64 bytes in one step. They agree because a digest is 32
bytes (`K0_eq`). The pads: `xorBytes k0 ipad` (a `zipWith` against 64 copies
of 0x36) is `k0.map (· ^^^ 0x36)` because `k0` is 64 bytes (`xorBytes_replicate`).
-/

namespace KdfBridge.Hmac

/-- tacenta-model's padded key, `k` in `Model.Kdf.hmac`. -/
def tacentaKey (key : List UInt8) : List UInt8 :=
  let k0 := if key.length > Model.Kdf.blockSize then Model.Sha256.hash key else key
  k0 ++ List.replicate (Model.Kdf.blockSize - k0.length) 0

theorem K0_eq (key : List UInt8) : KdfStandardModel.Hmac.K0 key = tacentaKey key := by
  unfold KdfStandardModel.Hmac.K0 tacentaKey
  simp only [KdfStandardModel.Hmac.B, KdfStandardModel.Hmac.L, Model.Kdf.blockSize]
  by_cases h1 : key.length = 64
  · simp [h1]
  · by_cases h2 : key.length > 64
    · simp [h1, h2, KdfBridge.sha256_eq, Model.Sha256.hash_length]
    · simp [h1, h2]

theorem xorBytes_replicate (k : List UInt8) (c : UInt8) :
    KdfStandardModel.xorBytes k (List.replicate k.length c) = k.map (· ^^^ c) := by
  induction k with
  | nil => rfl
  | cons x k ih =>
    simp only [KdfStandardModel.xorBytes, List.length_cons, List.replicate_succ,
      List.zipWith_cons_cons, List.map_cons] at ih ⊢
    rw [ih]

end KdfBridge.Hmac

open KdfBridge.Hmac in
/-- **HMAC bridge.** This repository's HMAC-SHA256 equals tacenta-model's, for
every key and message. -/
theorem KdfBridge.hmac_eq (k m : List UInt8) : KdfStandardModel.hmac k m = Model.Kdf.hmac k m := by
  have hlen : (tacentaKey k).length = 64 := by
    rw [← K0_eq]; exact KdfStandardModel.Hmac.K0_length k
  have hi : KdfStandardModel.Hmac.ipad = List.replicate (tacentaKey k).length 0x36 := by
    rw [hlen]; rfl
  have ho : KdfStandardModel.Hmac.opad = List.replicate (tacentaKey k).length 0x5c := by
    rw [hlen]; rfl
  simp only [KdfStandardModel.hmac, Model.Kdf.hmac, K0_eq, hi, ho, xorBytes_replicate,
    KdfBridge.sha256_eq]
  rfl
