/- Copied from a separate, unpublished repository that holds a SHA-256, HMAC-SHA256 and HKDF-SHA256 with their proofs, the source of `tacenta-core/kdf/src` (pinned there by
commit and file digests): its model file `Hkdf.lean`, at commit `646fcdadb943`. Elaborated
here against the Session unit's own translation of those bodies. Changes from the source: the
translated crate's namespace is `tacenta_session_unit.tacenta_kdf`, the Session unit's
translation of `tacenta-kdf`; the source's other namespaces are renamed `KdfStandardModel`,
`Tacenta.KdfProof` and `KdfBridge`; its imports name this package's `Kdf*` modules.
Local edits: dropped a reference to the source's review record.
Of the source's model only the SHA-256, HMAC and HKDF files were copied. "This repository" in the
prose below means that implementation, and a path such as `scripts/...` or `std/...` names one of
its files.
The code: written by the maintainer with tool assistance in a separate, unpublished repository; the three Rust
files were read in full by the maintainer on 2026-10-23, and before that only by tool-assisted sessions; no
reader independent of the maintainer has read the three files, and no human has read their proofs. -/
import Translation.KdfModelHmac

/-!
# HKDF-SHA256 (RFC 5869)

RFC 5869 §2.2 (extract) and §2.3 (expand) with Hash = SHA-256 and
HMAC-Hash = `hmac`, so HashLen = 32.

**The bound on L.** §2.3 requires L ≤ 255·HashLen = 8160. The model's
`expand` is total and does not enforce it; the bound is the separate
predicate `expandInDomain`. Beyond it, the model keeps computing
T(N) = HMAC-Hash(PRK, T(N−1) ‖ info ‖ N) with the counter written as the one
octet N mod 256 (§2.3: "the constant concatenated to the end of each T(n) is
a single octet"), so T(256) uses the octet 0x00, T(257) 0x01, and so on. That
output is not HKDF: RFC 5869 does not define it, and the counter repeats. It
is chosen because it keeps `expand` total and agrees with the RFC for every
L in its domain. Any continuation that kept computing blocks would also keep
every output a prefix of a longer one (`hkdf_take`); nothing rests on this
particular one. `expand_length`, `expand_take`, `hkdf_length` and
`hkdf_take` are stated for every L, so for L > 8160 they describe these
out-of-domain values, not HKDF. The refinement proof of the Rust is stated
only for L ≤ 8160 (where the Rust does not panic), so no claim about the
implementation rests on the out-of-domain choice.
PRK is always 32 bytes here, since it is an HMAC output, so §2.3's
"at least HashLen octets" holds for every PRK the model produces.

**The salt.** §2.2 says a salt that is "not provided" is "set to a string of
HashLen zeros". The model always takes the salt as bytes; a caller with no salt
passes `List.replicate 32 0`. The empty salt gives the same PRK
(`extract_empty_salt`), because HMAC pads both keys to the same 64 zero bytes.
-/

namespace KdfStandardModel

namespace Hkdf

/-- RFC 5869 §2.2: HashLen, the output length of the hash in octets
(32 for SHA-256). -/
def HashLen : Nat := 32

/-- RFC 5869 §2.2: HKDF-Extract(salt, IKM) = HMAC-Hash(salt, IKM), the PRK. -/
def extract (salt ikm : Bytes) : Bytes := hmac salt ikm

/-- RFC 5869 §2.3: T(i) ‖ T(i+1) ‖ … ‖ T(i+n−1), given `prev` = T(i−1), where
T(j) = HMAC-Hash(PRK, T(j−1) ‖ info ‖ j) and j is written as a single octet
(`j.toUInt8`, which is j mod 256; j ≤ 255 inside `expandInDomain`). -/
def expandBlocks (prk info : Bytes) : Bytes → Nat → Nat → Bytes
  | _, _, 0 => []
  | prev, i, n + 1 =>
    let t := hmac prk (prev ++ info ++ [i.toUInt8])
    t ++ expandBlocks prk info t (i + 1) n

/-- RFC 5869 §2.3: HKDF-Expand(PRK, info, L). N = ceil(L/HashLen);
T = T(1) ‖ T(2) ‖ … ‖ T(N) with T(0) the empty string; OKM = the first L
octets of T. Total: for L > 255·HashLen see the module note. -/
def expand (prk info : Bytes) (L : Nat) : Bytes :=
  let N := (L + HashLen - 1) / HashLen
  (expandBlocks prk info [] 1 N).take L

/-- RFC 5869 §2.3: the domain of L, "L ≤ 255*HashLen". -/
def expandInDomain (L : Nat) : Prop := L ≤ 255 * HashLen

instance (L : Nat) : Decidable (expandInDomain L) :=
  inferInstanceAs (Decidable (L ≤ 255 * HashLen))

/-- `expandBlocks` over `n` blocks produces 32·n octets. -/
theorem expandBlocks_length (prk info prev : Bytes) (i n : Nat) :
    (expandBlocks prk info prev i n).length = 32 * n := by
  induction n generalizing prev i with
  | zero => rfl
  | succ n ih =>
    simp only [expandBlocks, List.length_append, hmac_length, ih]
    omega

/-- More blocks extend fewer: T(1..n) is a prefix of T(1..n+m). -/
theorem expandBlocks_add (prk info prev : Bytes) (i n m : Nat) :
    ∃ rest, expandBlocks prk info prev i (n + m) =
      expandBlocks prk info prev i n ++ rest := by
  induction n generalizing prev i with
  | zero => exact ⟨expandBlocks prk info prev i m, by simp [expandBlocks]⟩
  | succ n ih =>
    obtain ⟨rest, h⟩ := ih (hmac prk (prev ++ info ++ [i.toUInt8])) (i + 1)
    refine ⟨rest, ?_⟩
    rw [Nat.succ_add]
    simp only [expandBlocks, List.append_assoc] at h ⊢
    rw [h]

end Hkdf

open Hkdf in
/-- RFC 5869 §2: HKDF(salt, IKM, info, L) = HKDF-Expand(HKDF-Extract(salt, IKM),
info, L), with SHA-256. -/
def hkdf (salt ikm info : Bytes) (L : Nat) : Bytes := expand (extract salt ikm) info L

namespace Hkdf

/-- HKDF-Expand returns exactly L octets (for every L; the RFC's domain is
L ≤ 8160). -/
theorem expand_length (prk info : Bytes) (L : Nat) : (expand prk info L).length = L := by
  simp only [expand, List.length_take, expandBlocks_length, HashLen]
  omega

/-- Expand's prefix property: the first M octets of an L-octet output are the
M-octet output, for M ≤ L. -/
theorem expand_take (prk info : Bytes) (L M : Nat) (h : M ≤ L) :
    (expand prk info L).take M = expand prk info M := by
  simp only [expand, List.take_take, HashLen]
  rw [Nat.min_eq_left h]
  have hN : (M + 32 - 1) / 32 ≤ (L + 32 - 1) / 32 := Nat.div_le_div_right (by omega)
  obtain ⟨rest, hr⟩ := expandBlocks_add prk info [] 1 ((M + 32 - 1) / 32)
    ((L + 32 - 1) / 32 - (M + 32 - 1) / 32)
  rw [Nat.add_sub_cancel' hN] at hr
  rw [hr, List.take_append_of_le_length]
  rw [expandBlocks_length]; omega

/-- RFC 5869 §2.2's "not provided" salt (HashLen zeros) and the empty salt give
the same PRK: HMAC pads both to 64 zero bytes (FIPS 198-1 §4 step 3). -/
theorem extract_empty_salt (ikm : Bytes) :
    extract [] ikm = extract (List.replicate HashLen 0) ikm := by
  simp only [extract, hmac, Hmac.K0, Hmac.B, Hmac.L, HashLen]
  simp

end Hkdf

/-- HKDF output length is L (RFC 5869 §2.3, "OKM … (of L octets)"). -/
theorem hkdf_length (salt ikm info : Bytes) (L : Nat) :
    (hkdf salt ikm info L).length = L := Hkdf.expand_length _ _ _

/-- HKDF prefix property: for M ≤ L, the first M octets of the L-octet output
are the M-octet output. -/
theorem hkdf_take (salt ikm info : Bytes) (L M : Nat) (h : M ≤ L) :
    (hkdf salt ikm info L).take M = hkdf salt ikm info M :=
  Hkdf.expand_take _ _ _ _ h

end KdfStandardModel
