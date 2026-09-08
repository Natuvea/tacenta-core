/-
Model.Sha256: SHA-256 (FIPS 180-4), a self-contained implementation with no
dependency and no mathlib. The model's key-derivation functions are built on
this, so the model computes the Double Ratchet key schedule to exact bytes and
can act as the protocol vector oracle. Correctness is anchored to the NIST
known-answer values checked at the bottom of this file.
-/
namespace Model.Sha256

/-- Rotate a 32-bit word right by `n` bits (`0 < n < 32`). -/
@[inline] def rotr (x : UInt32) (n : UInt32) : UInt32 :=
  (x >>> n) ||| (x <<< (32 - n))

/-- The 64 round constants (first 32 bits of the fractional parts of the cube
    roots of the first 64 primes). -/
def roundConstants : Array UInt32 := #[
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5,
  0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
  0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3,
  0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
  0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc,
  0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7,
  0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
  0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13,
  0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
  0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3,
  0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5,
  0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
  0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208,
  0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]

/-- The initial hash value (first 32 bits of the fractional parts of the square
    roots of the first 8 primes). -/
def initialHash : Array UInt32 := #[
  0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
  0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19]

/-- Assemble four big-endian bytes into a 32-bit word. -/
@[inline] def beWord (b0 b1 b2 b3 : UInt8) : UInt32 :=
  (b0.toUInt32 <<< 24) ||| (b1.toUInt32 <<< 16) ||| (b2.toUInt32 <<< 8) ||| b3.toUInt32

/-- Split a 32-bit word into its four big-endian bytes. -/
@[inline] def wordBytes (w : UInt32) : List UInt8 :=
  [(w >>> 24).toUInt8, (w >>> 16).toUInt8, (w >>> 8).toUInt8, w.toUInt8]

/-- Pad a message to a whole number of 64-byte blocks per the FIPS 180-4 rule:
    a `0x80` byte, then zeros, then the 64-bit big-endian bit length. -/
def pad (msg : List UInt8) : List UInt8 :=
  let len := msg.length
  let bitLen : UInt64 := (UInt64.ofNat len) * 8
  -- After the appended 0x80 the length is len+1; pad with zeros until the
  -- residue mod 64 is 56, then append the 8-byte length.
  let zeros := (56 + 64 - ((len + 1) % 64)) % 64
  let lengthBytes : List UInt8 :=
    (List.range 8).map (fun i => (bitLen >>> (UInt64.ofNat ((7 - i) * 8))).toUInt8)
  msg ++ [0x80] ++ List.replicate zeros 0 ++ lengthBytes

/-- Compress one 64-byte block into the running hash state. -/
def compress (h : Array UInt32) (block : Array UInt8) : Array UInt32 := Id.run do
  -- Message schedule.
  let mut w : Array UInt32 := Array.replicate 64 0
  for i in [0:16] do
    let j := i * 4
    w := w.set! i (beWord block[j]! block[j+1]! block[j+2]! block[j+3]!)
  for t in [16:64] do
    let s0 := (rotr w[t-15]! 7) ^^^ (rotr w[t-15]! 18) ^^^ (w[t-15]! >>> 3)
    let s1 := (rotr w[t-2]! 17) ^^^ (rotr w[t-2]! 19) ^^^ (w[t-2]! >>> 10)
    w := w.set! t (w[t-16]! + s0 + w[t-7]! + s1)
  -- Compression.
  let mut a := h[0]!
  let mut b := h[1]!
  let mut c := h[2]!
  let mut d := h[3]!
  let mut e := h[4]!
  let mut f := h[5]!
  let mut g := h[6]!
  let mut hh := h[7]!
  for t in [0:64] do
    let bigS1 := (rotr e 6) ^^^ (rotr e 11) ^^^ (rotr e 25)
    let ch := (e &&& f) ^^^ ((~~~e) &&& g)
    let temp1 := hh + bigS1 + ch + roundConstants[t]! + w[t]!
    let bigS0 := (rotr a 2) ^^^ (rotr a 13) ^^^ (rotr a 22)
    let maj := (a &&& b) ^^^ (a &&& c) ^^^ (b &&& c)
    let temp2 := bigS0 + maj
    hh := g; g := f; f := e; e := d + temp1
    d := c; c := b; b := a; a := temp1 + temp2
  pure #[h[0]!+a, h[1]!+b, h[2]!+c, h[3]!+d, h[4]!+e, h[5]!+f, h[6]!+g, h[7]!+hh]

theorem compress_size (h : Array UInt32) (block : Array UInt8) :
    (compress h block).size = 8 := by
  first
    | rfl
    | simp [compress, Id.run]
    | decide

/-- Folding the compression over any list of blocks keeps the state eight words
wide, because each step replaces it with a literal eight-word array. -/
theorem foldl_compress_size {α : Type} (l : List α) (h0 : Array UInt32)
    (g : α → Array UInt8) (hh : h0.size = 8) :
    (l.foldl (fun h b => compress h (g b)) h0).size = 8 := by
  induction l generalizing h0 with
  | nil => simpa using hh
  | cons a t ih => exact ih _ (compress_size _ _)

/-- SHA-256 of a byte message. -/
def hash (msg : List UInt8) : List UInt8 :=
  let padded := (pad msg).toArray
  let blocks := padded.size / 64
  -- A fold rather than a `for` loop, so the state's width can be carried across
  -- the iteration by induction (`hash_length`). The two compute the same thing,
  -- and the FIPS known-answer checks below are what says so.
  let h := (List.range blocks).foldl
    (fun h blk => compress h (padded.extract (blk*64) (blk*64+64))) initialHash
  (h.toList).flatMap wordBytes

/-- Each word contributes four bytes, so the digest is four times the state's
width. -/
theorem flatMap_wordBytes_length (l : List UInt32) :
    (l.flatMap wordBytes).length = 4 * l.length := by
  induction l with
  | nil => simp
  | cons a t ih => simp [wordBytes, ih]; omega

/-- The digest is thirty-two bytes, for every message. The model's known-answer
checks cover two; this covers all of them, and everything downstream copies a
fixed thirty-two bytes out of it. -/
theorem hash_length (msg : List UInt8) : (hash msg).length = 32 := by
  simp only [hash, flatMap_wordBytes_length, Array.length_toList]
  rw [foldl_compress_size _ _ _ (by rfl)]

-- Known-answer checks (FIPS 180-4 / NIST examples). These elaborate at build
-- time; a wrong implementation fails the build.

/-- SHA-256("") -/
example : hash [] =
    [0xe3,0xb0,0xc4,0x42,0x98,0xfc,0x1c,0x14,0x9a,0xfb,0xf4,0xc8,0x99,0x6f,0xb9,0x24,
     0x27,0xae,0x41,0xe4,0x64,0x9b,0x93,0x4c,0xa4,0x95,0x99,0x1b,0x78,0x52,0xb8,0x55] := by
  native_decide

/-- SHA-256("abc") -/
example : hash [0x61,0x62,0x63] =
    [0xba,0x78,0x16,0xbf,0x8f,0x01,0xcf,0xea,0x41,0x41,0x40,0xde,0x5d,0xae,0x22,0x23,
     0xb0,0x03,0x61,0xa3,0x96,0x17,0x7a,0x9c,0xb4,0x10,0xff,0x61,0xf2,0x00,0x15,0xad] := by
  native_decide

end Model.Sha256
