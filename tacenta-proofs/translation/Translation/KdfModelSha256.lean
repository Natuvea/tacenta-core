/- Copied from a separate, unpublished repository of this project's maintainer that holds a SHA-256,
HMAC-SHA256 and HKDF-SHA256 with their proofs, the source of `tacenta-core/kdf/src` (pinned there by
commit and file digests): its model file `Sha256.lean`, at commit `646fcdadb943`. Elaborated
here against the Session unit's own translation of those bodies. Changes from the source: the
translated crate's namespace is `tacenta_session_unit.tacenta_kdf`, the Session unit's
translation of `tacenta-kdf`; the source's other namespaces are renamed `KdfStandardModel`,
`Tacenta.KdfProof` and `KdfBridge`; its imports name this package's `Kdf*` modules.
Of the source's model only the SHA-256, HMAC and HKDF files were copied. "This repository" in the
prose below means that implementation, and a path such as `scripts/...` or `std/...` names one of
its files. -/
import Translation.KdfModelBasic
import Translation.KdfModelSha256Tables

/-!
# SHA-256 (FIPS 180-4)

SHA-256 over byte messages, in the standard's whole-message form: pad the
message (§5.1.1), parse the padded message into 512-bit blocks (§5.2.1), set
H(0) (§5.3.3, §6.2.1), then process the blocks in order (§6.2.2) and output
H(N) as the digest.

The model covers messages whose length ℓ in bits is a multiple of 8 (byte
strings). FIPS 180-4 §1 limits SHA-256 to messages with ℓ < 2^64 bits. The
model is total: for ℓ ≥ 2^64, §5.1.1's 64-bit length block is taken to be
`ℓ mod 2^64` (see `lengthBlock`). That value is outside the standard's domain
and matches no statement of FIPS 180-4; it is a choice made so the function is
total, and no claim about such inputs rests on the standard.
-/

namespace KdfStandardModel.Sha256

/-! ## §2.2.2 / §3.2 operations on 32-bit words -/

/-- FIPS 180-4 §2.2.2 and §3.2 item 4: ROTR^n(x) = (x >> n) ∨ (x << w − n),
with w = 32 and 0 ≤ n < w. `>>>`/`<<<` on `UInt32` are the §2.2.2 shifts
(bits shifted out are discarded, zeros shifted in) for shift amounts below 32.
For n = 0 the second shift amount is 32, which `UInt32` reduces mod 32 to 0;
the result is then x ∨ x = x, the same as the standard's x ∨ 0 = x, so the
definition agrees with the standard on its whole domain 0 ≤ n < 32. -/
def ROTR (n x : UInt32) : UInt32 := (x >>> n) ||| (x <<< (32 - n))

/-- FIPS 180-4 §2.2.2 and §3.2 item 3: SHR^n(x) = x >> n, 0 ≤ n < 32. -/
def SHR (n x : UInt32) : UInt32 := x >>> n

/-! ## §4.1.2 the six logical functions -/

/-- FIPS 180-4 §4.1.2, equation (4.2): Ch(x, y, z) = (x ∧ y) ⊕ (¬x ∧ z). -/
def Ch (x y z : UInt32) : UInt32 := (x &&& y) ^^^ (~~~x &&& z)

/-- FIPS 180-4 §4.1.2, equation (4.3):
Maj(x, y, z) = (x ∧ y) ⊕ (x ∧ z) ⊕ (y ∧ z). -/
def Maj (x y z : UInt32) : UInt32 := (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)

/-- FIPS 180-4 §4.1.2, equation (4.4):
Σ0{256}(x) = ROTR^2(x) ⊕ ROTR^13(x) ⊕ ROTR^22(x). -/
def Sigma0 (x : UInt32) : UInt32 := ROTR 2 x ^^^ ROTR 13 x ^^^ ROTR 22 x

/-- FIPS 180-4 §4.1.2, equation (4.5):
Σ1{256}(x) = ROTR^6(x) ⊕ ROTR^11(x) ⊕ ROTR^25(x). -/
def Sigma1 (x : UInt32) : UInt32 := ROTR 6 x ^^^ ROTR 11 x ^^^ ROTR 25 x

/-- FIPS 180-4 §4.1.2, equation (4.6):
σ0{256}(x) = ROTR^7(x) ⊕ ROTR^18(x) ⊕ SHR^3(x). -/
def sigma0 (x : UInt32) : UInt32 := ROTR 7 x ^^^ ROTR 18 x ^^^ SHR 3 x

/-- FIPS 180-4 §4.1.2, equation (4.7):
σ1{256}(x) = ROTR^17(x) ⊕ ROTR^19(x) ⊕ SHR^10(x). -/
def sigma1 (x : UInt32) : UInt32 := ROTR 17 x ^^^ ROTR 19 x ^^^ SHR 10 x

/-! ## §4.2.2 and §5.3.3 the tables, against their definitions

`K` and `H0` themselves are extracted from the standard's text by
`scripts/gen_sha256_tables.py` into `Sha256Tables.lean`. The theorems below
check each table against the sentence that defines it.

"The first 32 bits of the fractional part of x" is ⌊frac(x)·2^32⌋, and for
x ≥ 0 that equals ⌊x·2^32⌋ mod 2^32. With x = p^(1/3),
⌊x·2^32⌋ = ⌊(p·2^96)^(1/3)⌋, the integer cube root r of p·2^96, pinned down by
r^3 ≤ p·2^96 < (r+1)^3. Likewise for square roots with p·2^64. So the theorems
are stated over integers only, with no real numbers and no trust in the root
function: each states the root inequalities themselves. -/

/-- Trial-division primality: n ≥ 2 and no d with 2 ≤ d < n divides n (the
definition of a prime, checked literally). Used only to state the table
theorems. -/
def isPrime (n : Nat) : Bool :=
  2 ≤ n && (List.range n).all (fun d => d < 2 || n % d != 0)

/-- The primes below `n`, in increasing order. Used only to state the table
theorems. -/
def primesBelow (n : Nat) : List Nat := (List.range n).filter isPrime

/-- The first sixty-four primes (FIPS 180-4 §4.2.2): the primes below 312.
`first64Primes_length` shows there are 64 of them, so they are exactly the 64
smallest primes. -/
def first64Primes : List Nat := primesBelow 312

/-- The first eight primes (FIPS 180-4 §5.3.3). -/
def first8Primes : List Nat := first64Primes.take 8

/-- One step of a bit-by-bit integer k-th root: try setting bit `b`. Used only
to supply the witness in the table theorems; the theorems check the root
inequalities directly, so nothing depends on this being correct. -/
def irootAux (k n : Nat) : Nat → Nat → Nat
  | 0, r => r
  | b + 1, r => irootAux k n b (if (r + 2 ^ b) ^ k ≤ n then r + 2 ^ b else r)

/-- ⌊n^(1/k)⌋ for n < 2^(64k), bit by bit from bit 63. Witness only. -/
def iroot (k n : Nat) : Nat := irootAux k n 64 0

theorem first64Primes_length : first64Primes.length = 64 := by decide +kernel

theorem first8Primes_eq : first8Primes = [2, 3, 5, 7, 11, 13, 17, 19] := by
  decide +kernel

/-- All the numbers below 312 that are not in `first64Primes` are not prime,
and all in it are (restating `primesBelow`'s definition as a check). -/
theorem first64Primes_spec :
    ∀ n, n < 312 → (n ∈ first64Primes ↔ isPrime n = true) := by
  intro n hn
  simp [first64Primes, primesBelow, List.mem_filter, List.mem_range, hn]

/-- The table check for K, as one kernel-decidable Boolean. -/
def checkK : Bool :=
  (List.range 64).all fun i =>
    let p := first64Primes.getD i 0
    let r := iroot 3 (p * 2 ^ 96)
    decide (r ^ 3 ≤ p * 2 ^ 96) && decide (p * 2 ^ 96 < (r + 1) ^ 3) &&
      (K.getD i 0).toNat == r % 2 ^ 32

/-- The table check for H(0), as one kernel-decidable Boolean. -/
def checkH0 : Bool :=
  (List.range 8).all fun i =>
    let p := first8Primes.getD i 0
    let r := iroot 2 (p * 2 ^ 64)
    decide (r ^ 2 ≤ p * 2 ^ 64) && decide (p * 2 ^ 64 < (r + 1) ^ 2) &&
      (H0.getD i 0).toNat == r % 2 ^ 32

theorem checkK_true : checkK = true := by decide +kernel

theorem checkH0_true : checkH0 = true := by decide +kernel

theorem K_length : K.length = 64 := by decide +kernel

theorem H0_length : H0.length = 8 := by decide +kernel

/-- FIPS 180-4 §4.2.2: K{256}_i is the first thirty-two bits of the fractional
part of the cube root of the i-th prime (from 0): there is an integer
r = ⌊p^(1/3)·2^32⌋, characterised by r^3 ≤ p·2^96 < (r+1)^3, whose low 32
bits are K_i. -/
theorem K_eq_cube_roots :
    ∀ i, i < 64 →
      ∃ r, r ^ 3 ≤ first64Primes.getD i 0 * 2 ^ 96 ∧
        first64Primes.getD i 0 * 2 ^ 96 < (r + 1) ^ 3 ∧
        (K.getD i 0).toNat = r % 2 ^ 32 := by
  intro i hi
  have h := checkK_true
  simp only [checkK, List.all_eq_true, List.mem_range, Bool.and_eq_true,
    decide_eq_true_eq, beq_iff_eq] at h
  exact ⟨_, (h i hi).1.1, (h i hi).1.2, (h i hi).2⟩

/-- FIPS 180-4 §5.3.3: H(0)_i is the first thirty-two bits of the fractional
part of the square root of the i-th prime (from 0): there is an integer
r = ⌊p^(1/2)·2^32⌋, characterised by r^2 ≤ p·2^64 < (r+1)^2, whose low 32
bits are H(0)_i. -/
theorem H0_eq_sqrt_primes :
    ∀ i, i < 8 →
      ∃ r, r ^ 2 ≤ first8Primes.getD i 0 * 2 ^ 64 ∧
        first8Primes.getD i 0 * 2 ^ 64 < (r + 1) ^ 2 ∧
        (H0.getD i 0).toNat = r % 2 ^ 32 := by
  intro i hi
  have h := checkH0_true
  simp only [checkH0, List.all_eq_true, List.mem_range, Bool.and_eq_true,
    decide_eq_true_eq, beq_iff_eq] at h
  exact ⟨_, (h i hi).1.1, (h i hi).1.2, (h i hi).2⟩

/-! ## §5.1.1 padding -/

/-- FIPS 180-4 §5.1.1: k, "the smallest, non-negative solution to the equation
ℓ + 1 + k ≡ 448 mod 512". -/
def padZeroBits (ℓ : Nat) : Nat := (448 + 512 - (ℓ + 1) % 512) % 512

/-- The 64-bit big-endian encoding of `n` (FIPS 180-4 §3.1 item 2: the most
significant byte first). Takes the low 64 bits of `n`. -/
def be64 (n : Nat) : Bytes :=
  [7, 6, 5, 4, 3, 2, 1, 0].map fun i => (n / 256 ^ i % 256).toUInt8

/-- FIPS 180-4 §5.1.1: "the 64-bit block that is equal to the number ℓ
expressed using a binary representation". For ℓ ≥ 2^64 (outside FIPS 180-4's
domain, §1) the model takes ℓ mod 2^64: a documented choice, not the
standard. -/
def lengthBlock (ℓ : Nat) : Bytes := be64 (ℓ % 2 ^ 64)

/-- FIPS 180-4 §5.1.1, for a message M of ℓ = 8·|M| bits: append the bit "1",
then k zero bits (`padZeroBits`), then the 64-bit length block. Because ℓ is a
multiple of 8, k ≡ 7 (mod 8) (`padZeroBits_mod8`), so the "1" bit and the
first 7 of the k zero bits form the byte 0x80, and the remaining k − 7 zero
bits are (k − 7)/8 zero bytes. -/
def pad (M : Bytes) : Bytes :=
  let ℓ := 8 * M.length
  let k := padZeroBits ℓ
  M ++ [0x80] ++ List.replicate ((k - 7) / 8) 0 ++ lengthBlock ℓ

theorem padZeroBits_mod8 (n : Nat) : padZeroBits (8 * n) % 8 = 7 := by
  unfold padZeroBits; omega

theorem padZeroBits_spec (ℓ : Nat) :
    (ℓ + 1 + padZeroBits ℓ) % 512 = 448 % 512 ∧ padZeroBits ℓ < 512 := by
  unfold padZeroBits; omega

theorem be64_length (n : Nat) : (be64 n).length = 8 := by simp [be64]

/-- §5.1.1: "The length of the padded message should now be a multiple of
512 bits." -/
theorem pad_length_mod (M : Bytes) : (pad M).length % 64 = 0 := by
  simp only [pad, List.length_append, List.length_replicate, List.length_cons,
    List.length_nil, lengthBlock, be64_length]
  have := padZeroBits_mod8 M.length
  have := padZeroBits_spec (8 * M.length)
  omega

/-! ## §5.2.1 parsing -/

/-- A 32-bit word from four bytes, the first byte most significant
(FIPS 180-4 §3.1 item 2, big-endian). -/
def word (b0 b1 b2 b3 : UInt8) : UInt32 :=
  (b0.toUInt32 <<< 24) ||| (b1.toUInt32 <<< 16) ||| (b2.toUInt32 <<< 8) |||
    b3.toUInt32

/-- FIPS 180-4 §5.2.1: a 512-bit block as sixteen 32-bit words
M(i)_0 … M(i)_15, "the first 32 bits of message block i are denoted M(i)_0,
the next 32 bits are M(i)_1, and so on". -/
def parseBlock (B : Bytes) : List UInt32 :=
  (List.range 16).map fun j =>
    word (B.getD (4 * j) 0) (B.getD (4 * j + 1) 0) (B.getD (4 * j + 2) 0)
      (B.getD (4 * j + 3) 0)

/-- FIPS 180-4 §5.2.1: "the message and its padding are parsed into N 512-bit
blocks, M(1), M(2), …, M(N)", each as its sixteen words. -/
def parse (M' : Bytes) : List (List UInt32) :=
  (chunks 64 (M'.length / 64) M').map parseBlock

/-! ## §6.2.2 hash computation -/

/-- FIPS 180-4 §6.2.2 step 1, one word: given W_0 … W_(t−1) with 16 ≤ t,
append W_t = σ1(W_(t−2)) + W_(t−7) + σ0(W_(t−15)) + W_(t−16), addition
mod 2^32. -/
def scheduleStep (W : List UInt32) : List UInt32 :=
  let t := W.length
  W ++ [sigma1 (W.getD (t - 2) 0) + W.getD (t - 7) 0 +
        sigma0 (W.getD (t - 15) 0) + W.getD (t - 16) 0]

/-- `n` applications of `scheduleStep`. -/
def scheduleAux : Nat → List UInt32 → List UInt32
  | 0, W => W
  | n + 1, W => scheduleAux n (scheduleStep W)

/-- FIPS 180-4 §6.2.2 step 1: the message schedule {W_t}, t = 0 … 63:
W_t = M(i)_t for 0 ≤ t ≤ 15, then the 48 words for 16 ≤ t ≤ 63. -/
def schedule (Mi : List UInt32) : List UInt32 := scheduleAux 48 Mi

/-- FIPS 180-4 §6.2: the eight working variables a, b, c, d, e, f, g, h. -/
structure Vars where
  a : UInt32
  b : UInt32
  c : UInt32
  d : UInt32
  e : UInt32
  f : UInt32
  g : UInt32
  h : UInt32

/-- FIPS 180-4 §6.2.2 step 2: initialise a … h with H(i−1)_0 … H(i−1)_7. -/
def initVars (H : List UInt32) : Vars :=
  ⟨H.getD 0 0, H.getD 1 0, H.getD 2 0, H.getD 3 0,
   H.getD 4 0, H.getD 5 0, H.getD 6 0, H.getD 7 0⟩

/-- FIPS 180-4 §6.2.2 step 3, the body for one t:
T1 = h + Σ1(e) + Ch(e, f, g) + K_t + W_t; T2 = Σ0(a) + Maj(a, b, c);
h = g; g = f; f = e; e = d + T1; d = c; c = b; b = a; a = T1 + T2. -/
def round (W : List UInt32) (v : Vars) (t : Nat) : Vars :=
  let T1 := v.h + Sigma1 v.e + Ch v.e v.f v.g + K.getD t 0 + W.getD t 0
  let T2 := Sigma0 v.a + Maj v.a v.b v.c
  { h := v.g, g := v.f, f := v.e, e := v.d + T1,
    d := v.c, c := v.b, b := v.a, a := T1 + T2 }

/-- FIPS 180-4 §6.2.2, steps 1–4 for one block: from H(i−1) and M(i), compute
H(i). Step 3 is "For t = 0 to 63", a left fold of `round` over 0 … 63; step 4
is H(i)_j = (working variable j) + H(i−1)_j. -/
def compress (H : List UInt32) (Mi : List UInt32) : List UInt32 :=
  let W := schedule Mi
  let v := (List.range 64).foldl (round W) (initVars H)
  [v.a + H.getD 0 0, v.b + H.getD 1 0, v.c + H.getD 2 0, v.d + H.getD 3 0,
   v.e + H.getD 4 0, v.f + H.getD 5 0, v.g + H.getD 6 0, v.h + H.getD 7 0]

/-- A 32-bit word as four bytes, most significant first (FIPS 180-4 §3.1). -/
def wordBytes (w : UInt32) : Bytes :=
  [(w >>> 24).toUInt8, (w >>> 16).toUInt8, (w >>> 8).toUInt8, w.toUInt8]

/-- FIPS 180-4 §6.2.1 and §6.2.2: set H(0) (§5.3.3), pad and parse the message
(§5, `pad`, `parse`), process M(1) … M(N) in order ("For i = 1 to N", a left
fold of `compress`), and output "the resulting 256-bit message digest"
H(N)_0 ‖ H(N)_1 ‖ … ‖ H(N)_7, each word big-endian. -/
def hash (M : Bytes) : Bytes :=
  let H := (parse (pad M)).foldl compress H0
  H.flatMap wordBytes

theorem compress_length (H Mi : List UInt32) : (compress H Mi).length = 8 := rfl

theorem foldl_compress_length (bs : List (List UInt32)) (H : List UInt32)
    (h : H.length = 8) : (bs.foldl compress H).length = 8 := by
  induction bs generalizing H with
  | nil => exact h
  | cons b bs ih => exact ih _ (compress_length _ _)

theorem flatMap_wordBytes_length (H : List UInt32) :
    (H.flatMap wordBytes).length = 4 * H.length := by
  induction H with
  | nil => rfl
  | cons w H ih =>
    simp only [List.flatMap_cons, List.length_append, ih, List.length_cons]
    simp [wordBytes]; omega

theorem hash_length (M : Bytes) : (hash M).length = 32 := by
  simp only [hash, flatMap_wordBytes_length, foldl_compress_length _ _ H0_length]

end Sha256

/-- SHA-256 of a byte string (FIPS 180-4 §6.2), `Sha256.hash`. -/
def sha256 (M : Bytes) : Bytes := Sha256.hash M

/-- SHA-256 digests are 32 bytes (FIPS 180-4 §1, Figure 1: 256-bit digest). -/
theorem sha256_length (M : Bytes) : (sha256 M).length = 32 := Sha256.hash_length M

end KdfStandardModel
