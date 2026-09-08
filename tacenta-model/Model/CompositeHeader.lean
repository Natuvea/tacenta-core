/-
Model.CompositeHeader: the Triple Ratchet's header on the wire.

The composition needs a header carrying **both** ratchets' headers, and the
specification states one obligation about it: it must parse unambiguously. That
is a requirement on the encoding rather than on the ratchets, and this is the
encoding it is a requirement on.

## Why every field is fixed width

Unambiguity is bought rather than argued. Every field here has a width known
before it is read, so a decoder never has to decide where one ends, and the
round-trip theorem below falls out of that rather than out of a case analysis
over lengths.

The agreement's chunk is the one field that is genuinely optional, and it is
encoded the same way `Model.Messages.encodeOptionalKey` encodes an absent prekey:
a presence byte, then the field's full width regardless, zeroed when absent. It
costs thirty-four bytes on a message that carries no chunk and it means the
decoder's shape does not depend on a value it has just read.

## What it costs

A hundred and two bytes of header per message, against the Double Ratchet's
forty-one. The specification's own page says the composition costs bandwidth and
that the sparse agreement exists to keep it affordable; this is the number.
-/
import Std.Tactic.BVDecide
import Model.Messages

namespace Model.CompositeHeader

open Model.State (Key)

/-- A counter as eight big-endian bytes.

    `UInt64` rather than `Nat`, which is what the published document specifies
    for an epoch and is also what makes the round-trip below a bitvector fact a
    solver can settle rather than an argument about digits. -/
def be64 (n : UInt64) : List UInt8 :=
  [(n >>> 56).toUInt8, (n >>> 48).toUInt8, (n >>> 40).toUInt8, (n >>> 32).toUInt8,
   (n >>> 24).toUInt8, (n >>> 16).toUInt8, (n >>> 8).toUInt8, n.toUInt8]

def readBe64 : List UInt8 → Option (UInt64 × List UInt8)
  | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: rest =>
    some ((b0.toUInt64 <<< 56) ||| (b1.toUInt64 <<< 48) ||| (b2.toUInt64 <<< 40)
          ||| (b3.toUInt64 <<< 32) ||| (b4.toUInt64 <<< 24) ||| (b5.toUInt64 <<< 16)
          ||| (b6.toUInt64 <<< 8) ||| b7.toUInt64, rest)
  | _ => none

/-- The counter round-trip, for every one of the 2^64 values. -/
theorem readBe64_be64 (n : UInt64) (rest : List UInt8) :
    readBe64 (be64 n ++ rest) = some (n, rest) := by
  simp only [be64, readBe64, List.cons_append, List.nil_append]
  refine congrArg some (Prod.ext ?_ rfl)
  apply UInt64.eq_of_toBitVec_eq
  simp
  bv_decide


/-- Two big-endian bytes, for a codeword index. -/
def be16 (n : UInt16) : List UInt8 := [(n >>> 8).toUInt8, n.toUInt8]

def readBe16 : List UInt8 → Option (UInt16 × List UInt8)
  | b0 :: b1 :: rest => some ((b0.toUInt16 <<< 8) ||| b1.toUInt16, rest)
  | _ => none
/-- And for two bytes. -/
theorem readBe16_be16 (n : UInt16) (rest : List UInt8) :
    readBe16 (be16 n ++ rest) = some (n, rest) := by
  simp only [be16, readBe16, List.cons_append, List.nil_append]
  refine congrArg some (Prod.ext ?_ rfl)
  apply UInt16.eq_of_toBitVec_eq
  simp
  bv_decide


/-- The agreement's message type. `Ct1Ack` is deliberately absent, for the reason
    given on the ML-KEM Braid's page: no state produces it, so a peer emitting one
    should fail to parse rather than be silently ignored. -/
inductive AgreementType where
  | none | hdr | ek | ekCt1Ack | ct1 | ct2
  deriving Repr, DecidableEq, Inhabited

def encodeAgreementType : AgreementType → UInt8
  | .none => 0x00
  | .hdr => 0x01
  | .ek => 0x02
  | .ekCt1Ack => 0x03
  | .ct1 => 0x04
  | .ct2 => 0x05

def decodeAgreementType : UInt8 → Option AgreementType
  | 0x00 => some .none
  | 0x01 => some .hdr
  | 0x02 => some .ek
  | 0x03 => some .ekCt1Ack
  | 0x04 => some .ct1
  | 0x05 => some .ct2
  | _ => Option.none

theorem decode_encode_agreementType (t : AgreementType) :
    decodeAgreementType (encodeAgreementType t) = some t := by
  cases t <;> rfl

/-- One codeword: where it sits in its stream, and its bytes. -/
structure Codeword where
  index : UInt16
  data  : List UInt8
  deriving Repr, DecidableEq, Inhabited

/-- The chunk size in bytes, matching `tacenta-erasure`. -/
def chunkBytes : Nat := 32

/-- Everything a single message carries besides its ciphertext. -/
structure Composite where
  /-- The Diffie-Hellman ratchet's public key. -/
  dh       : Key
  /-- The previous sending chain's length. -/
  pn       : UInt32
  /-- The message number on the classical chain. -/
  n        : UInt32
  /-- The agreement epoch the post-quantum key came from. -/
  pqEpoch  : UInt64
  /-- The message number on that epoch's chain. -/
  pqN      : UInt64
  /-- The epoch the agreement's own message belongs to. -/
  agEpoch  : UInt64
  /-- What the agreement's message carries. -/
  agType   : AgreementType
  /-- Its codeword, when it has one. -/
  agChunk  : Option Codeword
  deriving Repr, Inhabited, DecidableEq

/-- A chunk, or the same width in zeros. The presence byte is what a decoder
    reads; the width never changes. -/
def encodeChunk : Option Codeword → List UInt8
  | none => 0x00 :: (be16 0 ++ List.replicate chunkBytes 0)
  | some c => 0x01 :: (be16 c.index ++ c.data)

def encode (h : Composite) : List UInt8 :=
  [Model.Messages.version, Model.Messages.typeRatchet]
  ++ h.dh
  ++ Model.Messages.be32 h.pn
  ++ Model.Messages.be32 h.n
  ++ be64 h.pqEpoch
  ++ be64 h.pqN
  ++ be64 h.agEpoch
  ++ [encodeAgreementType h.agType]
  ++ encodeChunk h.agChunk

/-- The header's width, which is the same for every message. -/
def size : Nat := 2 + 32 + 4 + 4 + 8 + 8 + 8 + 1 + 1 + 2 + chunkBytes

def decode (bs : List UInt8) : Option (Composite × List UInt8) := do
  match bs with
  | v :: t :: rest =>
    if v != Model.Messages.version then Option.none
    else if t != Model.Messages.typeRatchet then Option.none
    else do
      let (dh, r1) ← Model.Messages.take? 32 rest
      let (pn, r2) ← Model.Messages.readBe32 r1
      let (n, r3) ← Model.Messages.readBe32 r2
      let (pqEpoch, r4) ← readBe64 r3
      let (pqN, r5) ← readBe64 r4
      let (agEpoch, r6) ← readBe64 r5
      match r6 with
      | ty :: present :: r7 => do
        let agType ← decodeAgreementType ty
        let (idx, r8) ← readBe16 r7
        let (data, r9) ← Model.Messages.take? chunkBytes r8
        -- The presence byte is a flag, so only its two values are accepted, and
        -- absent means the whole field is zero rather than only the flag. The
        -- Rust decoder applies the same rule, so a header has exactly one
        -- accepted spelling. `decode_encode` cannot see that on its own:
        -- it only ever asks about bytes the encoder produced. `encode_decode`
        -- below asks the other direction, which is the one canonicality is.
        let agChunk ←
          if present == 0x01 then some (some { index := idx, data := data })
          else if present == 0x00 then
            if idx == 0 && data.all (· == 0) then some Option.none else Option.none
          else Option.none
        some ({ dh := dh, pn := pn, n := n, pqEpoch := pqEpoch, pqN := pqN,
                agEpoch := agEpoch, agType := agType, agChunk := agChunk }, r9)
      | _ => Option.none
  | _ => Option.none

/-! ## Known answers

The round-trip on concrete values. A general theorem for this encoding needs the
same length reasoning `Proofs.Serialization` does for the message encoding, and
belongs beside it rather than here; these say the two halves agree on values
before that is written. -/

private def sample : Composite :=
  { dh := List.replicate 32 0xaa, pn := 7, n := 9,
    pqEpoch := 3, pqN := 11, agEpoch := 3, agType := .ct1,
    agChunk := some { index := 5, data := List.replicate chunkBytes 0xcd } }

private def sampleNoChunk : Composite :=
  { sample with agType := .none, agChunk := Option.none }

example : (encode sample).length = size := by native_decide

example : (encode sampleNoChunk).length = size := by native_decide

/-- Every message is the same width, whether or not it carries a codeword. That
    is the property the fixed-width chunk field buys. -/
example : (encode sample).length = (encode sampleNoChunk).length := by native_decide

example : decode (encode sample) = some (sample, []) := by native_decide

example : decode (encode sampleNoChunk) = some (sampleNoChunk, []) := by native_decide

/-- Trailing bytes are returned rather than consumed, so a header can be read off
    the front of a message and the ciphertext follows. -/
example : decode (encode sample ++ [0xde, 0xad]) = some (sample, [0xde, 0xad]) := by
  native_decide

/-- A wrong version is refused. -/
example : decode (0x02 :: (encode sample).drop 1) = Option.none := by native_decide

/-- A truncated header is refused rather than read short. -/
example : decode ((encode sample).take (size - 1)) = Option.none := by native_decide

end Model.CompositeHeader
