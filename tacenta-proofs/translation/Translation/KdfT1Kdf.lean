/- Copied from a separate, unpublished repository that holds a SHA-256, HMAC-SHA256 and HKDF-SHA256 with their proofs, the source of `tacenta-core/kdf/src` (pinned there by
commit and file digests): its proofs file `T1Kdf.lean`, at commit `646fcdadb943`. Elaborated
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
import Translation.KdfT1Sha

/-!
# T1, part 2: HMAC-SHA256 and HKDF-SHA256 never fail

HMAC: the key is copied into the 64-byte `K0` only when it is at most 64
bytes long, and hashed otherwise. HKDF: the one precondition is RFC 5869's
`L ≤ 255 · 32`, which `hkdf_sha256_into`'s own `assert!` checks and
`hkdf_sha256`'s `N` must meet. Under it the byte counter `i` never
overflows: at the head of every iteration that writes, `pos = 32 · (i - 1)`
and `pos < L ≤ 8160`, so `i ≤ 255`.
-/

open Aeneas Aeneas.Std Result
namespace Tacenta.KdfProof
open tacenta_session_unit.tacenta_kdf

/-- The invariant of an `HmacSha256` reachable from `new`: its inner hash is
well formed. -/
def HmacWf (m : hmac.HmacSha256) : Prop := Sha256Wf m.inner

@[step]
theorem hmac_new_loop0_no_panic (k0 : Array U8 64#usize) (hashed : Array U8 32#usize)
    (i : Usize) (hi : i.val ≤ 32) :
    hmac.HmacSha256.new_loop0 k0 hashed i ⦃ fun _ => True ⦄ := by
  unfold hmac.HmacSha256.new_loop0
  apply loop.spec_decr_nat (measure := fun p => 32 - p.2.val) (inv := fun p => p.2.val ≤ 32)
  · rintro ⟨k1, i1⟩ h
    unfold hmac.HmacSha256.new_loop0.body
    simp only []
    split
    · step*
    · simp
  · exact hi

@[step]
theorem hmac_new_loop2_no_panic (key : Slice U8) (k0 : Array U8 64#usize) (i : Usize)
    (hk : key.length ≤ 64) (hi : i.val ≤ key.length) :
    hmac.HmacSha256.new_loop2 key k0 i ⦃ fun _ => True ⦄ := by
  unfold hmac.HmacSha256.new_loop2
  apply loop.spec_decr_nat (measure := fun p => key.length - p.2.val)
    (inv := fun p => p.2.val ≤ key.length)
  · rintro ⟨k1, i1⟩ h
    unfold hmac.HmacSha256.new_loop2.body
    simp only []
    split
    · step*
    · simp
  · exact hi

@[step]
theorem hmac_new_loop1_no_panic (k0 ib ob : Array U8 64#usize) (i : Usize) (hi : i.val ≤ 64) :
    hmac.HmacSha256.new_loop1 k0 ib ob i ⦃ fun _ => True ⦄ := by
  unfold hmac.HmacSha256.new_loop1
  apply loop.spec_decr_nat (measure := fun p => 64 - p.2.2.val) (inv := fun p => p.2.2.val ≤ 64)
  · rintro ⟨ib1, ob1, i1⟩ h
    unfold hmac.HmacSha256.new_loop1.body
    simp only [hmac.BLOCK]
    split
    · step*
    · simp
  · exact hi

@[step]
theorem hmac_new_loop3_no_panic (k0 ib ob : Array U8 64#usize) (i : Usize) (hi : i.val ≤ 64) :
    hmac.HmacSha256.new_loop3 k0 ib ob i ⦃ fun _ => True ⦄ := by
  unfold hmac.HmacSha256.new_loop3
  apply loop.spec_decr_nat (measure := fun p => 64 - p.2.2.val) (inv := fun p => p.2.2.val ≤ 64)
  · rintro ⟨ib1, ob1, i1⟩ h
    unfold hmac.HmacSha256.new_loop3.body
    simp only [hmac.BLOCK]
    split
    · step*
    · simp
  · exact hi

@[step]
theorem hmac_new_no_panic (key : Slice U8) :
    hmac.HmacSha256.new key ⦃ fun m => HmacWf m ⦄ := by
  unfold hmac.HmacSha256.new HmacWf
  simp only [hmac.BLOCK]
  split
  · step*
  · step*

@[step]
theorem hmac_update_no_panic (m : hmac.HmacSha256) (data : Slice U8) (hm : HmacWf m) :
    hmac.HmacSha256.update m data ⦃ fun m' => HmacWf m' ⦄ := by
  unfold HmacWf at hm
  unfold hmac.HmacSha256.update HmacWf
  step*

@[step]
theorem hmac_finalize_no_panic (m : hmac.HmacSha256) (hm : HmacWf m) :
    hmac.HmacSha256.finalize m ⦃ fun _ => True ⦄ := by
  unfold HmacWf at hm
  unfold hmac.HmacSha256.finalize
  step*

/-- **T1 for `hmac_sha256`**: never fails, for every key and message. -/
@[step]
theorem hmac_sha256_no_panic (key data : Slice U8) :
    hmac.hmac_sha256 key data ⦃ fun _ => True ⦄ := by
  unfold hmac.hmac_sha256; step*

@[step]
theorem extract_no_panic (salt ikm : Slice U8) :
    hkdf.extract salt ikm ⦃ fun _ => True ⦄ := by
  unfold hkdf.extract; step*

/-- The inner copy loop writes `T(i)` from `pos` on, stopping after 32 bytes
or at the end of `out`. -/
@[step]
theorem expand_inner_no_panic (out : Slice U8) (t : Array U8 32#usize) (pos j : Usize)
    (hj : j.val ≤ 32) (hp : pos.val ≤ out.length) :
    hkdf.expand_loop0_loop0 out t pos j ⦃ fun r =>
      r.1.length = out.length ∧ r.2.val ≤ out.length ∧
      (r.2.val = pos.val + (32 - j.val) ∨ r.2.val = out.length) ∧
      pos.val ≤ r.2.val ⦄ := by
  unfold hkdf.expand_loop0_loop0
  apply loop.spec_decr_nat (measure := fun p => 32 - p.2.2.val)
    (inv := fun p => p.1.length = out.length ∧ p.2.2.val ≤ 32 ∧
      p.2.1.val ≤ out.length ∧ p.2.1.val + j.val = pos.val + p.2.2.val)
  · rintro ⟨o1, pos1, j1⟩ ⟨h1, h2, h3, h4⟩
    dsimp only at h1 h2 h3 h4
    unfold hkdf.expand_loop0_loop0.body
    simp only [hkdf.HASH_LEN]
    split
    · split
      · step*
        simp_all only [Slice.set_length]
        scalar_tac
      · simp only [WP.spec_ok]; scalar_tac
    · simp only [WP.spec_ok]; scalar_tac
  · exact ⟨rfl, hj, hp, rfl⟩

@[step]
theorem expand_loop_no_panic (prk : Array U8 32#usize) (info out : Slice U8)
    (t : Array U8 32#usize) (pos : Usize) (i : U8)
    (hL : out.length ≤ 8160) (hi : 1 ≤ i.val)
    (hpos : pos.val = 32 * (i.val - 1) ∨ out.length ≤ pos.val) (hp : pos.val ≤ out.length) :
    hkdf.expand_loop0 prk info out t pos i ⦃ fun r => r.length = out.length ⦄ := by
  unfold hkdf.expand_loop0
  apply loop.spec_decr_nat (measure := fun p => out.length - p.2.2.1.val)
    (inv := fun p => p.1.length = out.length ∧ 1 ≤ p.2.2.2.val ∧
      (p.2.2.1.val = 32 * (p.2.2.2.val - 1) ∨ out.length ≤ p.2.2.1.val) ∧
      p.2.2.1.val ≤ out.length)
  · rintro ⟨o1, t1, pos1, i1⟩ ⟨h1, h2, h3, h4⟩
    dsimp only at h1 h2 h3 h4
    unfold hkdf.expand_loop0.body
    simp only []
    split
    · repeat' (first | step | split)
      all_goals first
        | scalar_tac
        | (refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> scalar_tac)
    · simp_all
  · exact ⟨rfl, hi, hpos, hp⟩

@[step]
theorem expand_no_panic (prk : Array U8 32#usize) (info out : Slice U8)
    (hL : out.length ≤ 8160) :
    hkdf.expand prk info out ⦃ fun r => r.length = out.length ⦄ := by
  unfold hkdf.expand
  step*

/-- **T1 for `hkdf_sha256_into`**: never fails when `out.len() ≤ 255 · 32`,
which is exactly when the Rust's `assert!` holds. -/
@[step]
theorem hkdf_sha256_into_no_panic (salt ikm info out : Slice U8)
    (hL : out.length ≤ 8160) :
    hkdf.hkdf_sha256_into salt ikm info out ⦃ fun r => r.length = out.length ⦄ := by
  unfold hkdf.hkdf_sha256_into hkdf.MAX_OUTPUT_LEN
  simp only [hkdf.HASH_LEN]
  step*

/-- **T1 for `hkdf_sha256::<N>`**: never fails when `N ≤ 255 · 32`. -/
@[step]
theorem hkdf_sha256_no_panic (N : Usize) (salt ikm info : Slice U8) (hN : N.val ≤ 8160) :
    hkdf.hkdf_sha256 N salt ikm info ⦃ fun _ => True ⦄ := by
  unfold hkdf.hkdf_sha256
  step*

end Tacenta.KdfProof

/-! ## Above the bound: the refusal

T1 and T3 are stated for outputs of at most 8160 bytes. Above that the Rust
panics, as `tacenta-kdf`'s `expect` does. These two theorems say so, and
they name the failure (`assertionFailure`, the `assert!`). A weaker "does
not succeed" would also hold for a mutant that deleted the `assert!` and
let the `u8` counter overflow instead. -/

namespace Tacenta.KdfProof
open Aeneas Aeneas.Std Result tacenta_session_unit.tacenta_kdf

/-- Above `255 · 32` bytes, `hkdf_sha256_into` fails at its `assert!`. -/
theorem hkdf_sha256_into_refuses (salt ikm info out : Slice U8) (h : 8160 < out.length) :
    hkdf.hkdf_sha256_into salt ikm info out = fail .assertionFailure := by
  unfold hkdf.hkdf_sha256_into hkdf.MAX_OUTPUT_LEN
  simp only [hkdf.HASH_LEN]
  obtain ⟨z, hz, hv⟩ := WP.spec_imp_exists
    (Usize.mul_spec (x := 255#usize) (y := 32#usize) (by scalar_tac))
  rw [hz]
  simp only [bind_tc_ok, massert]
  rw [if_neg (by simp [Slice.len, Slice.length] at h ⊢; scalar_tac)]
  rfl

/-- `hkdf_sha256::<N>` for `N > 255 · 32` fails the same way. -/
theorem hkdf_sha256_refuses (N : Usize) (salt ikm info : Slice U8) (h : 8160 < N.val) :
    hkdf.hkdf_sha256 N salt ikm info = fail .assertionFailure := by
  have hlen : 8160 < (Array.repeat N 0#u8).to_slice.length := by
    simp only [Array.to_slice, Slice.length, Std.Array.repeat_val, List.length_replicate]; exact h
  unfold hkdf.hkdf_sha256
  simp only [lift, bind_tc_ok, Array.to_slice_mut]
  change (do
      let s1 ← hkdf.hkdf_sha256_into salt ikm info (Array.repeat N 0#u8).to_slice
      ok ((Array.repeat N 0#u8).from_slice s1)) = _
  rw [hkdf_sha256_into_refuses salt ikm info _ hlen]
  rfl

end Tacenta.KdfProof
