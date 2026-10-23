/- Copied from an independent verified implementation of SHA-256, HMAC-SHA256 and HKDF-SHA256, the
source of `tacenta-core/kdf/src`: its bridge file `Hkdf.lean`, at commit `646fcdadb943`. Elaborated
here against the Session unit's own translation of those bodies. Changes from the source: the
translated crate's namespace is `tacenta_session_unit.tacenta_kdf`, the Session unit's
translation of `tacenta-kdf`; the source's other namespaces are renamed `KdfStandardModel`,
`Tacenta.KdfProof` and `KdfBridge`; its imports name this package's `Kdf*` modules.
Of the source's model only the SHA-256, HMAC and HKDF files were copied. "This repository" in the
prose below means that implementation, and a path such as `scripts/...` or `std/...` names one of
its files. -/
import Translation.KdfBridgeHmac
import Translation.KdfModelHkdf
import Model.Kdf

/-!
# Bridge: HKDF-SHA256

`KdfStandardModel.hkdf salt ikm info L = Model.Kdf.hkdf salt ikm info L` for every
salt, IKM, info and length `L`, with no bound on `L`.

* Extract: tacenta-model replaces an empty salt with 32 zero bytes, this
  repository's model passes it to HMAC as is. Both keys pad to the same
  64 zero bytes (FIPS 198-1 §4 step 3), so the PRKs agree (`extract_eq`).
* Expand: this repository's `expandBlocks` recursion and tacenta-model's
  `foldl expandStep` over `List.range' 1 N` build the same blocks
  (`foldl_expandStep`). The counter octet is `i.toUInt8` in one and
  `UInt8.ofNat i` in the other, which are the same function (`Nat.toUInt8` is
  defined as `UInt8.ofNat`), so the two agree past RFC 5869 §2.3's bound
  L ≤ 255·HashLen = 8160 too: both wrap the counter mod 256 there.
-/

namespace KdfBridge.Hkdf

theorem extract_eq (salt ikm : List UInt8) :
    KdfStandardModel.Hkdf.extract salt ikm = Model.Kdf.extract salt ikm := by
  unfold KdfStandardModel.Hkdf.extract Model.Kdf.extract
  rw [KdfBridge.hmac_eq]
  cases salt with
  | cons x xs => rfl
  | nil =>
    simp only [List.isEmpty_nil, if_true, Model.Kdf.hmac, Model.Kdf.blockSize,
      Model.Kdf.hashLen]
    simp

theorem foldl_expandStep (prk info prev acc : List UInt8) (i n : Nat) :
    ((List.range' i n).foldl (Model.Kdf.expandStep prk info) (prev, acc)).2 =
      acc ++ KdfStandardModel.Hkdf.expandBlocks prk info prev i n := by
  induction n generalizing i prev acc with
  | zero => simp [KdfStandardModel.Hkdf.expandBlocks]
  | succ n ih =>
    rw [List.range'_succ, List.foldl_cons]
    simp only [Model.Kdf.expandStep]
    rw [ih]
    simp only [KdfStandardModel.Hkdf.expandBlocks, KdfBridge.hmac_eq, List.append_assoc]

theorem expand_eq (prk info : List UInt8) (L : Nat) :
    KdfStandardModel.Hkdf.expand prk info L = Model.Kdf.expand prk info L := by
  simp only [KdfStandardModel.Hkdf.expand, Model.Kdf.expand, foldl_expandStep,
    KdfStandardModel.Hkdf.HashLen, Model.Kdf.hashLen, List.nil_append]

end KdfBridge.Hkdf

/-- **HKDF bridge.** This repository's HKDF-SHA256 equals tacenta-model's, for
every salt, IKM, info and output length (no bound on `L`). -/
theorem KdfBridge.hkdf_eq (salt ikm info : List UInt8) (L : Nat) :
    KdfStandardModel.hkdf salt ikm info L = Model.Kdf.hkdf salt ikm info L := by
  unfold KdfStandardModel.hkdf Model.Kdf.hkdf
  rw [KdfBridge.Hkdf.extract_eq, KdfBridge.Hkdf.expand_eq]
