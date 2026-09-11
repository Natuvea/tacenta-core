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

It issues indices 0, 1, 2 and so on, never one twice, and once it has issued
index 65,535 it issues nothing more. `next` is the index it issues next;
`exhausted` records that the last index has gone, and `next` stays there. -/

structure Encoder where
  chunks : List Bytes
  next : Nat
  exhausted : Bool
  deriving Repr, DecidableEq, Inhabited

def Encoder.new (m : Bytes) : Encoder := ⟨Model.Erasure.chunks m, 0, false⟩

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
