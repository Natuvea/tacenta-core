/-
Model.Erasure: the erasure code the ML-KEM Braid sends its large values through,
byte for byte, and the persisted formats of its two coders.

Written from tacenta-spec/protocol/mlkem-braid.md, "The erasure code" (chunks,
codewords, decoding, the encoder's lifetime), and from
tacenta-spec/protocol/session-persistence.md, "Erasure coder sub-formats" and
the erasure encoder and decoder rules under "Semantic rules of the leaf
formats".

`Model.Braid` holds the code at its contract, a decoder that succeeds once it
holds enough codewords from one encoder, and `Model.Polynomial` proves the
interpolation that contract rests on. Neither says which bytes a codeword
carries, where a value is cut into chunks, or which of two codewords at one
index a decoder keeps. This module says those things, so that the vectors
generated from it pin them. It adds nothing to the Braid's model and nothing
here is used by it.

The field elements, their arithmetic and the interpolation are
`Model.Gf65536` and `Model.Polynomial`; nothing below re-derives them.
-/
import Model.Polynomial

namespace Model.Erasure

open Model.Gf65536 (Elem)

abbrev Bytes := List UInt8

/-- The chunk size in bytes (`CHUNK_BYTES` in CONSTANTS.md). -/
def chunkBytes : Nat := 32

/-- Field elements per chunk. -/
def lanes : Nat := 16

/-- The number of distinct indices, and so the most codewords one encoder issues
    and the most chunks a stored encoder or decoder may name. -/
def maxCodewords : Nat := 65536

/-- The last index an encoder issues. -/
def lastIndex : Nat := 65535

/-! ## Chunks and codewords -/

/-- `k = ceil(n / 32)`. -/
def chunkCount (n : Nat) : Nat := (n + chunkBytes - 1) / chunkBytes

/-- A value cut into `k` chunks in order, the last padded with zero bytes. -/
def chunks (m : Bytes) : List Bytes :=
  (List.range (chunkCount m.length)).map fun t =>
    let c := (m.drop (t * chunkBytes)).take chunkBytes
    c ++ List.replicate (chunkBytes - c.length) 0

/-- Element `j` of a chunk: bytes `2j` and `2j + 1`, read big-endian. -/
def element (c : Bytes) (j : Nat) : Elem :=
  BitVec.ofNat 16 ((c.getD (2 * j) 0).toNat * 256 + (c.getD (2 * j + 1) 0).toNat)

/-- An element written back as its two bytes, big-endian. -/
def elementBytes (e : Elem) : Bytes :=
  [UInt8.ofNat (e.toNat / 256), UInt8.ofNat (e.toNat % 256)]

/-- An index used as a field element: the element with the same sixteen bits. -/
def node (i : Nat) : Elem := BitVec.ofNat 16 i

/-- Sixteen lanes, each a value of the field, as the 32 bytes of a codeword. -/
def ofLanes (lane : Nat → Elem) : Bytes :=
  ((List.range lanes).map fun j => elementBytes (lane j)).flatten

/-- Codeword `i` of the stream over the chunks `cs`: for `i < k` the chunk
    itself, and otherwise element `j` is `P_j(i)`, the polynomial of degree
    below `k` through `(t, element j of chunk t)` evaluated at `i`. -/
def codeword (cs : List Bytes) (i : Nat) : Bytes :=
  if i < cs.length then cs.getD i []
  else
    let points (j : Nat) : List (Elem × Elem) :=
      ((List.range cs.length).zip cs).map fun p => (node p.1, element p.2 j)
    ofLanes fun j => Model.Polynomial.interp (points j) (node i)

/-- The systematic prefix is the chunks themselves. -/
theorem codeword_systematic (cs : List Bytes) (i : Nat) (h : i < cs.length) :
    codeword cs i = cs.getD i [] := by
  simp [codeword, h]

/-! ## The encoder

It holds at most the first 65,536 chunks of its value. It issues indices 0, 1,
2 and so on, never one twice, and once it has issued index 65,535 it issues
nothing more. `next` is the index it issues next; `exhausted` records that the
last index has gone, and `next` stays there. -/

structure Encoder where
  chunks : List Bytes
  next : Nat
  exhausted : Bool
  deriving Repr, DecidableEq, Inhabited

/-- A new encoder holds the value's chunks, at most the first 65,536 of them
    (mlkem-braid.md, The erasure code, Codewords). Every index it issues is below
    65,536, so no codeword depends on a chunk past the cap
    (`Encoder.new_issue_nextCodeword`), and the cap is what keeps a new encoder
    within its own rules (`Encoder.new_issue_keeps`). -/
def Encoder.new (m : Bytes) : Encoder := ⟨(Model.Erasure.chunks m).take maxCodewords, 0, false⟩

/-- The index the next codeword takes and the encoder after it, without the
    codeword's bytes, so that the lifetime can be run to its end cheaply. -/
def Encoder.advance (e : Encoder) : Option (Nat × Encoder) :=
  if e.exhausted then none
  else if e.next = lastIndex then some (e.next, { e with exhausted := true })
  else some (e.next, { e with next := e.next + 1 })

/-- The next codeword, as its index and its bytes, and the encoder after it. -/
def Encoder.nextCodeword (e : Encoder) : Option ((Nat × Bytes) × Encoder) :=
  e.advance.map fun p => ((p.1, codeword e.chunks p.1), p.2)

/-- The encoder after `n` codewords, or after its last if that comes first. -/
def Encoder.issue : Nat → Encoder → Encoder
  | 0, e => e
  | n + 1, e =>
    match e.advance with
    | none => e
    | some p => Encoder.issue n p.2

/-- How many more codewords the encoder issues, counted up to `fuel`. -/
def Encoder.remaining : Nat → Encoder → Nat → Nat
  | 0, _, acc => acc
  | fuel + 1, e, acc =>
    match e.advance with
    | none => acc
    | some p => Encoder.remaining fuel p.2 (acc + 1)

/-! ## The decoder

It knows the value's length before any codeword arrives. It keeps the first
codeword at each index, ignores a later one at an index it holds whatever its
bytes, and once it holds `k` ignores every further one. -/

structure Decoder where
  size : Nat
  needed : Nat
  held : List (Nat × Bytes)
  deriving Repr, DecidableEq, Inhabited

def Decoder.new (n : Nat) : Decoder := ⟨n, chunkCount n, []⟩

/-- Offer one codeword; the held list keeps arrival order. -/
def Decoder.add (d : Decoder) (cw : Nat × Bytes) : Decoder :=
  if d.held.length ≥ d.needed then d
  else if d.held.any (fun h => h.1 == cw.1) then d
  else { d with held := d.held ++ [cw] }

def Decoder.addAll (d : Decoder) (cws : List (Nat × Bytes)) : Decoder :=
  cws.foldl Decoder.add d

/-- Chunk `t`: the codeword held at index `t` if there is one, and otherwise
    element `j` is the interpolant through the held codewords' element `j`,
    evaluated at `t`. -/
def Decoder.chunk (d : Decoder) (t : Nat) : Bytes :=
  match d.held.find? (fun h => h.1 == t) with
  | some h => h.2
  | none =>
    ofLanes fun j =>
      Model.Polynomial.interp (d.held.map fun h => (node h.1, element h.2 j)) (node t)

/-- The value, once `k` codewords are held: the `k` chunks in order, truncated
    to `n` bytes. A decoder for zero bytes holds the empty value at once. -/
def Decoder.message (d : Decoder) : Option Bytes :=
  if d.held.length < d.needed then none
  else some (((List.range d.needed).map d.chunk).flatten.take d.size)

/-! ## The persisted formats

```
encoder  = next(2) || exhausted(1) || count(4) || chunk(32)[count]
decoder  = size(8) || needed(8) || count(4) || codeword[count]
codeword = index(2) || chunk(32)
```

Big-endian throughout. A reader refuses: an `exhausted` byte other than `0x00`
or `0x01`; a `needed` above 65,536 or a `size` above 2,097,152; a count the
buffer does not hold; bytes after the last entry; and a state the coder's rules
exclude. The encoder's: at most 65,536 chunks, and `exhausted` only when `next`
is 65,535. The decoder's: `needed` is `ceil(size / 32)` and at most 65,536, at
most `needed` codewords are held, and no two share an index. -/

/-- `n` as `width` big-endian bytes. -/
def be (width n : Nat) : Bytes :=
  (List.range width).reverse.map fun i => UInt8.ofNat (n / 256 ^ i % 256)

/-- A `width`-byte big-endian integer from the front of `bs`. -/
def readBe (width : Nat) (bs : Bytes) : Option (Nat × Bytes) :=
  if bs.length < width then none
  else some ((bs.take width).foldl (fun acc b => acc * 256 + b.toNat) 0, bs.drop width)

def Encoder.toBytes (e : Encoder) : Bytes :=
  be 2 e.next ++ [if e.exhausted then 1 else 0] ++ be 4 e.chunks.length ++ e.chunks.flatten

def Encoder.invariant (e : Encoder) : Bool :=
  decide (e.chunks.length ≤ maxCodewords) && (!e.exhausted || e.next == lastIndex)

/-- `count` chunks of `chunkBytes` each from the front of `bs`. -/
def takeChunks : Nat → Bytes → Option (List Bytes × Bytes)
  | 0, bs => some ([], bs)
  | n + 1, bs =>
    if bs.length < chunkBytes then none
    else
      match takeChunks n (bs.drop chunkBytes) with
      | none => none
      | some (cs, rest) => some (bs.take chunkBytes :: cs, rest)

def Encoder.ofBytes (bs : Bytes) : Option Encoder := do
  let (next, r1) ← readBe 2 bs
  let (flag, r2) ← readBe 1 r1
  let exhausted ← if flag = 0 then some false else if flag = 1 then some true else none
  let (count, r3) ← readBe 4 r2
  let (cs, rest) ← takeChunks count r3
  let e : Encoder := ⟨cs, next, exhausted⟩
  if rest.isEmpty && e.invariant then some e else none

def Decoder.toBytes (d : Decoder) : Bytes :=
  be 8 d.size ++ be 8 d.needed ++ be 4 d.held.length ++
    (d.held.map fun h => be 2 h.1 ++ h.2).flatten

/-- No index appears twice. -/
def distinct : List Nat → Bool
  | [] => true
  | x :: xs => !xs.contains x && distinct xs

def Decoder.invariant (d : Decoder) : Bool :=
  d.needed == chunkCount d.size && decide (d.needed ≤ maxCodewords)
    && decide (d.held.length ≤ d.needed) && distinct (d.held.map Prod.fst)

/-- `count` codewords, each an index and a chunk, from the front of `bs`. -/
def takeCodewords : Nat → Bytes → Option (List (Nat × Bytes) × Bytes)
  | 0, bs => some ([], bs)
  | n + 1, bs =>
    if bs.length < 2 + chunkBytes then none
    else
      match readBe 2 bs, takeCodewords n (bs.drop (2 + chunkBytes)) with
      | some (i, r), some (cws, rest) => some ((i, r.take chunkBytes) :: cws, rest)
      | _, _ => none

def Decoder.ofBytes (bs : Bytes) : Option Decoder := do
  let (size, r1) ← readBe 8 bs
  let (needed, r2) ← readBe 8 r1
  let (count, r3) ← readBe 4 r2
  let (held, rest) ← takeCodewords count r3
  let d : Decoder := ⟨size, needed, held⟩
  if decide (needed ≤ maxCodewords) && decide (size ≤ maxCodewords * chunkBytes)
      && rest.isEmpty && d.invariant
  then some d else none

/-! ## What the encoder's cap keeps

An encoder holds at most the first 65,536 chunks of its value. So every encoder
`new` builds, after any number of codewords, keeps the encoder's rules, is read
back by `ofBytes` from what `toBytes` writes, and issues what it would issue if
it held every chunk. Without the cap, an encoder over a value of more than
65,536 chunks broke the first two and not the third. -/

/-- Every chunk of a value is 32 bytes. -/
theorem chunks_length (m : Bytes) : ∀ c ∈ chunks m, c.length = chunkBytes := by
  intro c hc
  simp only [chunks, List.mem_map, List.mem_range] at hc
  obtain ⟨t, -, rfl⟩ := hc
  simp only [List.length_append, List.length_take, List.length_replicate, List.length_drop]
  omega

theorem Encoder.new_invariant (m : Bytes) : (Encoder.new m).invariant = true := by
  simp [Encoder.invariant, Encoder.new, Nat.min_le_left]

/-- One codeword keeps the encoder's rules, its chunks, and `next` at most the
    last index; and the index it takes is below 65,536. -/
theorem Encoder.advance_keeps {e : Encoder} {p : Nat × Encoder}
    (hinv : e.invariant = true) (hnext : e.next ≤ lastIndex) (ha : e.advance = some p) :
    p.2.invariant = true ∧ p.2.next ≤ lastIndex ∧ p.2.chunks = e.chunks ∧
      p.1 < maxCodewords := by
  unfold Encoder.advance at ha
  by_cases hx : e.exhausted = true
  · simp [hx] at ha
  · by_cases hn : e.next = lastIndex
    · simp only [hx, hn, Bool.false_eq_true, if_false, if_true, Option.some.injEq] at ha
      subst ha
      simp_all [Encoder.invariant, lastIndex, maxCodewords]
    · simp only [hx, hn, Bool.false_eq_true, if_false, Option.some.injEq] at ha
      subst ha
      simp_all [Encoder.invariant, lastIndex, maxCodewords] <;> omega

/-- So do any number of codewords. -/
theorem Encoder.issue_keeps (n : Nat) {e : Encoder}
    (hinv : e.invariant = true) (hnext : e.next ≤ lastIndex) :
    (e.issue n).invariant = true ∧ (e.issue n).next ≤ lastIndex ∧
      (e.issue n).chunks = e.chunks := by
  induction n generalizing e with
  | zero => exact ⟨hinv, hnext, rfl⟩
  | succ n ih =>
    simp only [Encoder.issue]
    split
    · exact ⟨hinv, hnext, rfl⟩
    · rename_i p hp
      obtain ⟨h1, h2, h3, -⟩ := Encoder.advance_keeps hinv hnext hp
      obtain ⟨k1, k2, k3⟩ := ih h1 h2
      exact ⟨k1, k2, k3.trans h3⟩

/-- An encoder `new` builds, after any number of codewords, keeps the encoder's
    rules and holds the value's first 65,536 chunks at most. -/
theorem Encoder.new_issue_keeps (m : Bytes) (n : Nat) :
    ((Encoder.new m).issue n).invariant = true ∧
      ((Encoder.new m).issue n).next ≤ lastIndex ∧
      ((Encoder.new m).issue n).chunks = (Model.Erasure.chunks m).take maxCodewords :=
  Encoder.issue_keeps n (Encoder.new_invariant m) (by simp [Encoder.new])

/-- At an index below 65,536, the codeword over a value's first 65,536 chunks is
    the codeword over all of them. -/
theorem codeword_take_maxCodewords (cs : List Bytes) {i : Nat} (hi : i < maxCodewords) :
    codeword (cs.take maxCodewords) i = codeword cs i := by
  by_cases hc : cs.length ≤ maxCodewords
  · rw [List.take_of_length_le hc]
  · have h1 : i < (cs.take maxCodewords).length := by
      simp only [List.length_take]; omega
    rw [codeword_systematic _ _ h1, codeword_systematic _ _ (by omega)]
    simp [List.getD_eq_getElem?_getD, hi]

/-- The cap changes nothing an encoder issues: after any number of codewords, a
    new encoder's next codeword is the one over every chunk of its value. -/
theorem Encoder.new_issue_nextCodeword (m : Bytes) (n : Nat) :
    ((Encoder.new m).issue n).nextCodeword =
      ((Encoder.new m).issue n).advance.map
        fun p => ((p.1, codeword (Model.Erasure.chunks m) p.1), p.2) := by
  obtain ⟨hinv, hnext, hchunks⟩ := Encoder.new_issue_keeps m n
  unfold Encoder.nextCodeword
  cases ha : ((Encoder.new m).issue n).advance with
  | none => simp
  | some p =>
    obtain ⟨-, -, -, hi⟩ := Encoder.advance_keeps hinv hnext ha
    simp [hchunks, codeword_take_maxCodewords _ hi]

/-- `width` big-endian bytes read back from any accumulator. -/
theorem foldl_be (width n acc : Nat) :
    (be width n).foldl (fun acc b => acc * 256 + b.toNat) acc =
      acc * 256 ^ width + n % 256 ^ width := by
  induction width generalizing acc with
  | zero => simp [be, Nat.mod_one]
  | succ w ih =>
    have hbe : be (w + 1) n = UInt8.ofNat (n / 256 ^ w % 256) :: be w n := by
      simp [be, List.range_succ]
    rw [hbe, List.foldl_cons, ih, Nat.mod_pow_succ]
    simp only [UInt8.toNat_ofNat', Nat.reducePow, Nat.mod_mod, Nat.pow_succ,
      Nat.mul_add, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    omega

theorem readBe_append (bs rest : Bytes) :
    readBe bs.length (bs ++ rest) =
      some (bs.foldl (fun acc b => acc * 256 + b.toNat) 0, rest) := by
  simp [readBe]

theorem readBe_be (width n : Nat) (rest : Bytes) (h : n < 256 ^ width) :
    readBe width (be width n ++ rest) = some (n, rest) := by
  have := readBe_append (be width n) rest
  rw [be_length] at this
  rw [this, foldl_be, Nat.zero_mul, Nat.zero_add, Nat.mod_eq_of_lt h]
where
  be_length : (be width n).length = width := by simp [be]

theorem takeChunks_flatten (cs : List Bytes) (rest : Bytes)
    (h : ∀ c ∈ cs, c.length = chunkBytes) :
    takeChunks cs.length (cs.flatten ++ rest) = some (cs, rest) := by
  induction cs with
  | nil => simp [takeChunks]
  | cons c cs ih =>
    have hc : c.length = chunkBytes := h c (by simp)
    have ih' := ih (fun c' hc' => h c' (by simp [hc']))
    simp only [List.length_cons, List.flatten_cons, List.append_assoc, takeChunks]
    rw [if_neg (by simp [hc]), List.drop_left' hc, ih', List.take_left' hc]

/-- An encoder that keeps its rules, with `next` at most the last index and
    32-byte chunks, is read back from the bytes it is written as. -/
theorem Encoder.ofBytes_toBytes (e : Encoder) (hinv : e.invariant = true)
    (hnext : e.next ≤ lastIndex) (hc : ∀ c ∈ e.chunks, c.length = chunkBytes) :
    Encoder.ofBytes e.toBytes = some e := by
  have hlen : e.chunks.length ≤ maxCodewords := by
    simp only [Encoder.invariant, Bool.and_eq_true, decide_eq_true_eq] at hinv
    exact hinv.1
  have h2 : e.next < 256 ^ 2 := by simp only [lastIndex] at hnext; omega
  have h4 : e.chunks.length < 256 ^ 4 := by simp only [maxCodewords] at hlen; omega
  have h1 : (if e.exhausted then 1 else 0 : Nat) < 256 ^ 1 := by split <;> omega
  have hflag : ([if e.exhausted then 1 else 0] : Bytes) = be 1 (if e.exhausted then 1 else 0) := by
    cases e.exhausted <;> rfl
  simp only [Encoder.toBytes, Encoder.ofBytes, List.append_assoc, hflag]
  rw [readBe_be 2 _ _ h2, Option.bind_eq_bind]
  simp only [Option.bind_some]
  rw [readBe_be 1 _ _ h1]
  simp only [Option.bind_some]
  rw [readBe_be 4 _ _ h4]
  simp only [Option.bind_some]
  have := takeChunks_flatten e.chunks [] hc
  rw [List.append_nil] at this
  rw [this]
  obtain ⟨cs, nx, ex⟩ := e
  cases ex <;> simp_all

/-! ## Build-time checks

Executable instances of what the text says, as `Model.Polynomial`'s concrete
erasure is: they catch a definition here that is wrong on its own terms. -/

private def sample : Bytes := (List.range 100).map fun i => UInt8.ofNat (i * 7 + 3)

private def stream (m : Bytes) (is : List Nat) : List (Nat × Bytes) :=
  is.map fun i => (i, codeword (chunks m) i)

/-- 100 bytes is four chunks, the last padded with 28 zero bytes. -/
example : (chunks sample).length = 4 ∧ (chunks sample).getD 3 [] =
    sample.drop 96 ++ List.replicate 28 0 := by native_decide

/-- Every codeword from the parity half alone recovers the value. -/
example : (Decoder.new 100 |>.addAll (stream sample [4, 5, 6, 7])).message = some sample := by
  native_decide

/-- So does a mixture, in any order. -/
example : (Decoder.new 100 |>.addAll (stream sample [9, 2, 70, 0])).message = some sample := by
  native_decide

/-- One short is no value. -/
example : (Decoder.new 100 |>.addAll (stream sample [9, 2, 70])).message = none := by
  native_decide

/-- The first copy at an index wins: a corrupt copy first spoils the value, and
    the same corrupt copy after the genuine one changes nothing. -/
example :
    let bad : Nat × Bytes := (5, List.replicate 32 0xff)
    (Decoder.new 100 |>.addAll (bad :: stream sample [5, 1, 2, 3])).message ≠ some sample ∧
    (Decoder.new 100 |>.addAll (stream sample [5] ++ bad :: stream sample [1, 2, 3])).message
      = some sample := by
  native_decide

/-- The stream issues exactly 65,536 codewords and then nothing. -/
example : (Encoder.new sample).remaining (maxCodewords + 1) 0 = maxCodewords := by native_decide

/-- Both persisted formats read back what they wrote, mid-stream. -/
example :
    let e := (Encoder.new sample).issue 6
    let d := Decoder.new 100 |>.addAll (stream sample [6, 1])
    Encoder.ofBytes e.toBytes = some e ∧ Decoder.ofBytes d.toBytes = some d := by
  native_decide

end Model.Erasure
