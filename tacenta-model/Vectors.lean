/-
Vectors: generate Double Ratchet protocol test vectors from the model, so the
implementation is checked against the model's byte output rather than against
itself. Run with `lake exe genvectors`; it prints the vector file described by
tacenta-test-vectors/schema/ratchet-vector.schema.json to stdout.

The Diffie-Hellman outputs in a scenario are produced by a deterministic,
symmetric stand-in (`mockDh`), so the scenario is internally consistent
(`DH(a, b) = DH(b, a)`). It is not X25519; the real-curve values are recorded in
`tacenta-spec/CONSTANTS.md`. The
message keys the vectors record are the model's, and the runner checks the core
reproduces them exactly, which is the ratchet's key schedule. Each step also
records the message-key expansion (`messageKeys`: AEAD key, MAC key, IV), the
last derivation before the cipher, so that its label, salt and split order are
pinned by bytes and not only by the refinement theorem.

With an argument it prints one of the other files `regenerate-vectors.sh`
lists instead: the known-answer files for the session secret, the encodings
and the post-quantum derivations, and, at the end of this file, those with
refusals as well as answers, for the erasure code and its persisted coders
(`Model.Erasure`), the protobuf profile (`Model.Protobuf`) and the AEAD.
-/
import Model.Ratchet
import Model.Sha256
import Model.SessionEstablishment
import Model.Messages
import Model.Polynomial
import Model.SparseRatchet
import Model.Braid
import Model.TripleRatchet
import Model.CompositeHeader
import Model.Erasure
import Model.PersistedState
import Model.Protobuf

open Model.State
open Model.Ratchet

namespace Vectors

/-- A 32-byte key filled with one byte value. -/
def fill (b : UInt8) : Key := List.replicate 32 b

/-- A deterministic, symmetric stand-in for a Diffie-Hellman output: hash the
    byte-wise minimum concatenated with the byte-wise maximum, so the result does
    not depend on argument order. Not X25519. -/
def mockDh (a b : Key) : Key :=
  let lo := List.zipWith (fun x y => if x ≤ y then x else y) a b
  let hi := List.zipWith (fun x y => if x ≤ y then y else x) a b
  Model.Sha256.hash (lo ++ hi)

def hexDigit (n : UInt8) : Char :=
  let m := n.toNat
  if m < 10 then Char.ofNat (48 + m) else Char.ofNat (97 + m - 10)

def byteHex (b : UInt8) : String :=
  String.ofList [hexDigit (b >>> 4), hexDigit (b &&& 0x0f)]

def toHex (bs : List UInt8) : String :=
  String.join (bs.map byteHex)

def hexNibbles : List Char → List UInt8
  | a :: b :: rest =>
    let v (c : Char) : Nat := if c.isDigit then c.toNat - 48 else c.toNat - 87
    UInt8.ofNat (v a * 16 + v b) :: hexNibbles rest
  | _ => []

def ofHex (s : String) : List UInt8 := hexNibbles s.toList

/-- Fixed keys used across the scenarios. -/
def sk : Key := fill 0x01
def aPub : Key := fill 0x0a
def bPub : Key := fill 0x0b
def bPub2 : Key := fill 0x2b
def zero : Key := fill 0x00

def aPub2 : Key := fill 0x1a
def bPub3 : Key := fill 0x3b
def bPub4 : Key := fill 0x4b

def dhAB : Key := mockDh aPub bPub
def dhSendB : Key := mockDh bPub2 aPub

/-- The message-key expansion for a step: the AEAD key, the MAC key and the IV
    that `messageKeys` derives from `mk`. Recorded on every step so that the
    label (`mkInfo`), the zero salt and the split order are pinned by bytes.
    The ratchet-level key alone does not pin them: an error in any of the
    three changes every ciphertext key while every `mk` stays right. -/
def messageKeysJson (mk : Key) : String :=
  let (enc, mac, iv) := messageKeys mk .tacenta
  "\"message_keys\": { \"enc\": \"" ++ toHex enc ++ "\", \"mac\": \"" ++ toHex mac ++
  "\", \"iv\": \"" ++ toHex iv ++ "\" }"

/-- JSON for one send step (the runner drives the actor's send and checks `mk`
    and its expansion). -/
def sendStep (actor : String) (mk : Key) : String :=
  "{ \"actor\": \"" ++ actor ++ "\", \"op\": \"send\", \"mk\": \"" ++ toHex mk ++ "\", " ++
  messageKeysJson mk ++ " }"

/-- JSON for one receive step. -/
def recvStep (actor : String) (h : Header) (dhR dhS np mk : Key) : String :=
  "{ \"actor\": \"" ++ actor ++ "\", \"op\": \"receive\", " ++
  "\"header\": { \"dh\": \"" ++ toHex h.dh ++ "\", \"pn\": " ++ toString h.pn ++
  ", \"n\": " ++ toString h.n ++ " }, " ++
  "\"dh_recv\": \"" ++ toHex dhR ++ "\", \"dh_send\": \"" ++ toHex dhS ++
  "\", \"new_pub\": \"" ++ toHex np ++ "\", \"mk\": \"" ++ toHex mk ++ "\", " ++
  messageKeysJson mk ++ " }"

/-- Assemble a vector object from an id, a comment, and its steps. -/
def vector (id comment : String) (steps : List String) : String :=
  "    {\n      \"id\": \"" ++ id ++ "\",\n      \"comment\": \"" ++ comment ++ "\",\n" ++
  "      \"init\": { \"sk\": \"" ++ toHex sk ++ "\", \"alice_pub\": \"" ++ toHex aPub ++
  "\", \"bob_pub\": \"" ++ toHex bPub ++ "\", \"dh_ab\": \"" ++ toHex dhAB ++ "\" },\n" ++
  "      \"steps\": [\n        " ++ String.intercalate ",\n        " steps ++ "\n      ]\n    }"

/-- In order: Alice sends three messages, Bob receives them in order. Bob's first
    receive takes the opening DH ratchet step; the rest are same-chain. -/
def scenarioInOrder : String := Id.run do
  let stA0 := initSender sk aPub bPub dhAB .tacenta
  let (stA1, h0, ak0) := (send stA0).get!
  let (stA2, h1, ak1) := (send stA1).get!
  let (_, h2, ak2) := (send stA2).get!
  let stB0 := initReceiver sk bPub .tacenta
  let (stB1, bk0) := (receive stB0 h0 dhAB dhSendB bPub2).get!
  let (stB2, bk1) := (receive stB1 h1 zero zero zero).get!
  let (_, bk2) := (receive stB2 h2 zero zero zero).get!
  let steps := [
    sendStep "alice" ak0, sendStep "alice" ak1, sendStep "alice" ak2,
    recvStep "bob" h0 dhAB dhSendB bPub2 bk0,
    recvStep "bob" h1 zero zero zero bk1,
    recvStep "bob" h2 zero zero zero bk2]
  pure (vector "in-order-3" "alice sends three, bob receives in order" steps)

/-- Out of order: Alice sends three, Bob receives the third first (storing the
    first two as skipped), then the first two from the store. -/
def scenarioOutOfOrder : String := Id.run do
  let stA0 := initSender sk aPub bPub dhAB .tacenta
  let (stA1, h0, ak0) := (send stA0).get!
  let (stA2, h1, ak1) := (send stA1).get!
  let (_, h2, ak2) := (send stA2).get!
  let stB0 := initReceiver sk bPub .tacenta
  let (stB1, bk2) := (receive stB0 h2 dhAB dhSendB bPub2).get!
  let (stB2, bk0) := (receive stB1 h0 zero zero zero).get!
  let (_, bk1) := (receive stB2 h1 zero zero zero).get!
  let steps := [
    sendStep "alice" ak0, sendStep "alice" ak1, sendStep "alice" ak2,
    recvStep "bob" h2 dhAB dhSendB bPub2 bk2,
    recvStep "bob" h0 zero zero zero bk0,
    recvStep "bob" h1 zero zero zero bk1]
  pure (vector "out-of-order-skip" "alice sends three, bob receives third then first then second" steps)

/-- A peer that returns to a ratchet key it had left. Bob stores skipped keys
    under one ratchet key, is moved onto a second, then is sent the first again,
    which starts a fresh chain numbered from zero under a key the store already
    holds entries for. Nothing in receive forbids it, since the peer chooses the
    key in the header.

    This is the case that separates a store that replaces from one that
    accumulates: accumulating leaves a pair holding two keys, and the second
    can never be found. Storing replaces, and this vector is what checks an
    implementation agrees rather than merely not crashing. -/
def scenarioRevisit : String := Id.run do
  let stB0 := initReceiver sk bPub .tacenta
  let h0 : Header := { dh := aPub, pn := 0, n := 2 }
  let dhR1 := mockDh bPub2 aPub2
  let dhS1 := mockDh bPub3 aPub2
  let dhR2 := mockDh bPub3 aPub
  let dhS2 := mockDh bPub4 aPub
  let (stB1, bk0) := (receive stB0 h0 dhAB dhSendB bPub2).get!
  let h1 : Header := { dh := aPub2, pn := 5, n := 0 }
  let (stB2, bk1) := (receive stB1 h1 dhR1 dhS1 bPub3).get!
  let h2 : Header := { dh := aPub, pn := 0, n := 2 }
  let (_, bk2) := (receive stB2 h2 dhR2 dhS2 bPub4).get!
  let steps := [
    recvStep "bob" h0 dhAB dhSendB bPub2 bk0,
    recvStep "bob" h1 dhR1 dhS1 bPub3 bk1,
    recvStep "bob" h2 dhR2 dhS2 bPub4 bk2]
  pure (vector "peer-revisits-ratchet-key"
    "bob's peer returns to a ratchet key it had left, numbering a fresh chain from zero under a key already in the store"
    steps)

/-- Bidirectional: Alice sends, Bob receives and replies, Alice receives the
    reply and sends again, Bob receives that. Each side takes a DH ratchet step
    on the other's new ratchet key. `mockDh` is symmetric, so the reused pairs
    line up. -/
def scenarioBidi : String := Id.run do
  let aPub2 := fill 0x1a
  let bPub3 := fill 0x3b
  let dhAB2 := mockDh aPub bPub2
  let dhA2B2 := mockDh aPub2 bPub2
  let dhB3A2 := mockDh bPub3 aPub2
  let sa0 := initSender sk aPub bPub dhAB .tacenta
  let (sa1, h0, ak0) := (send sa0).get!
  let sb0 := initReceiver sk bPub .tacenta
  let (sb1, bk0) := (receive sb0 h0 dhAB dhAB2 bPub2).get!
  let (sb2, hr0, br0) := (send sb1).get!
  let (sa2, ar0) := (receive sa1 hr0 dhAB2 dhA2B2 aPub2).get!
  let (_, h1, ak1) := (send sa2).get!
  let (_, bk1) := (receive sb2 h1 dhA2B2 dhB3A2 bPub3).get!
  let steps := [
    sendStep "alice" ak0,
    recvStep "bob" h0 dhAB dhAB2 bPub2 bk0,
    sendStep "bob" br0,
    recvStep "alice" hr0 dhAB2 dhA2B2 aPub2 ar0,
    sendStep "alice" ak1,
    recvStep "bob" h1 dhA2B2 dhB3A2 bPub3 bk1]
  pure (vector "bidirectional" "alice and bob take turns, each ratcheting on the other's new key" steps)

def file : String :=
  "{\n" ++
  "  \"schema_version\": 1,\n" ++
  "  \"algorithm\": \"double-ratchet\",\n" ++
  "  \"source\": \"generated by tacenta-model Vectors.lean (lake exe genvectors)\",\n" ++
  "  \"vectors\": [\n" ++
  String.intercalate ",\n" [scenarioInOrder, scenarioOutOfOrder, scenarioBidi, scenarioRevisit] ++
  "\n  ]\n}"

/-- One PQXDH shared-secret vector, in the flat primitive-vector shape
    (schema/vector.schema.json): named byte inputs and one expected output. -/
def pqxdhVector (id : String) (dh1 dh2 dh3 : Key) (dh4 : Option Key) (ss : Key) : String :=
  let sk := Model.SessionEstablishment.sharedSecret dh1 dh2 dh3 dh4 ss
  let dh4Field :=
    match dh4 with
    | none => ""
    | some d => ", \"dh4\": \"" ++ toHex d ++ "\""
  "    { \"id\": \"" ++ id ++ "\", \"inputs\": { " ++
  "\"dh1\": \"" ++ toHex dh1 ++ "\", \"dh2\": \"" ++ toHex dh2 ++
  "\", \"dh3\": \"" ++ toHex dh3 ++ "\"" ++ dh4Field ++
  ", \"ss\": \"" ++ toHex ss ++ "\" }, \"output\": \"" ++ toHex sk ++ "\" }"

/-- The PQXDH shared-secret vectors: with and without a one-time curve prekey,
    which is the only structural variation in the derivation. -/
def pqxdhFile : String :=
  let dh1 := fill 0x11
  let dh2 := fill 0x22
  let dh3 := fill 0x33
  let dh4 := fill 0x44
  let ss := fill 0x55
  "{\n" ++
  "  \"schema_version\": 1,\n" ++
  "  \"algorithm\": \"pqxdh-sk\",\n" ++
  "  \"source\": \"generated by tacenta-model Vectors.lean (lake exe genvectors pqxdh)\",\n" ++
  "  \"vectors\": [\n" ++
  String.intercalate ",\n" [
    pqxdhVector "without-one-time-curve-prekey" dh1 dh2 dh3 none ss,
    pqxdhVector "with-one-time-curve-prekey" dh1 dh2 dh3 (some dh4) ss] ++
  "\n  ]\n}"

/-- One message-encoding vector: the header fields and ciphertext in, the
    canonical encoding out. Counters are written as four big-endian bytes so the
    whole vector stays in the flat hex shape. -/
def encodingVector (id : String) (h : Model.CompositeHeader.Composite)
    (ct : List UInt8) : String :=
  let encoded := Model.CompositeHeader.encode h ++ ct
  let chunkPresent := match h.agChunk with | none => "00" | some _ => "01"
  let chunkIndex := match h.agChunk with
    | none => "0000"
    | some c => toHex (Model.CompositeHeader.be16 c.index)
  let chunkData := match h.agChunk with
    | none => toHex (List.replicate Model.CompositeHeader.chunkBytes 0)
    | some c => toHex c.data
  "    { \"id\": \"" ++ id ++ "\", \"inputs\": { \"dh\": \"" ++ toHex h.dh ++
  "\", \"pn\": \"" ++ toHex (Model.Messages.be32 h.pn) ++
  "\", \"n\": \"" ++ toHex (Model.Messages.be32 h.n) ++
  "\", \"pq_epoch\": \"" ++ toHex (Model.CompositeHeader.be64 h.pqEpoch) ++
  "\", \"pq_n\": \"" ++ toHex (Model.CompositeHeader.be64 h.pqN) ++
  "\", \"ag_epoch\": \"" ++ toHex (Model.CompositeHeader.be64 h.agEpoch) ++
  "\", \"ag_type\": \"" ++ byteHex (Model.CompositeHeader.encodeAgreementType h.agType) ++
  "\", \"chunk_present\": \"" ++ chunkPresent ++
  "\", \"chunk_index\": \"" ++ chunkIndex ++
  "\", \"chunk_data\": \"" ++ chunkData ++
  "\", \"ciphertext\": \"" ++ toHex ct ++ "\" }, \"output\": \"" ++ toHex encoded ++ "\" }"

/-- Message-encoding vectors: a typical message, an empty ciphertext, and
    counters that exercise every byte of the big-endian fields. -/
def encodingFile : String :=
  "{\n" ++
  "  \"schema_version\": 1,\n" ++
  "  \"algorithm\": \"message-encoding\",\n" ++
  "  \"source\": \"generated by tacenta-model Vectors.lean (lake exe genvectors serialization)\",\n" ++
  "  \"vectors\": [\n" ++
  String.intercalate ",\n" [
    encodingVector "typical"
      { dh := fill 0x0a, pn := 7, n := 9, pqEpoch := 3, pqN := 11, agEpoch := 3,
        agType := .ct1, agChunk := some { index := 5, data := fill 0xcd } }
      [0xde, 0xad, 0xbe, 0xef],
    encodingVector "empty-ciphertext"
      { dh := fill 0x0b, pn := 0, n := 0, pqEpoch := 0, pqN := 0, agEpoch := 0,
        agType := .hdr, agChunk := some { index := 0, data := fill 0x00 } }
      [],
    -- The agreement half absent, which a message carries whenever the braid has
    -- nothing to send. A vector set without it would never exercise the
    -- presence byte's zero branch.
    encodingVector "no-agreement-chunk"
      { dh := fill 0x0c, pn := 0x01020304, n := 0xfffefdfc, pqEpoch := 9, pqN := 4,
        agEpoch := 9, agType := .none, agChunk := Option.none }
      [0x00]] ++
  "\n  ]\n}"

/-- One initial-message vector. The identifiers are written as four big-endian
    bytes, like the counters above, so the whole vector stays in the flat hex
    shape the runner reads. -/
def initialVector (id : String) (identity ephemeral kemCt : List UInt8)
    (spkId otpId kemId : UInt32) (ratchetMsg : List UInt8) : String :=
  let encoded := Model.Messages.encodeInitial identity ephemeral kemCt spkId
    otpId kemId ratchetMsg
  "    { \"id\": \"" ++ id ++ "\", \"inputs\": { " ++
  "\"identity\": \"" ++ toHex identity ++
  "\", \"ephemeral\": \"" ++ toHex ephemeral ++
  "\", \"kem_ciphertext\": \"" ++ toHex kemCt ++
  "\", \"signed_prekey_id\": \"" ++ toHex (Model.Messages.be32 spkId) ++
  "\", \"one_time_prekey_id\": \"" ++ toHex (Model.Messages.be32 otpId) ++
  "\", \"kem_prekey_id\": \"" ++ toHex (Model.Messages.be32 kemId) ++
  "\", \"ratchet_message\": \"" ++ toHex ratchetMsg ++
  "\" }, \"output\": \"" ++ toHex encoded ++ "\" }"

/-- Initial-message vectors: one naming a one-time curve prekey, one without
    (the absent identifier, which must not change the message's shape), and one
    with an empty KEM ciphertext to exercise the length prefix at zero. -/
def initialFile : String :=
  let ident := 0x05 :: fill 0x0a
  let ephem := 0x05 :: fill 0x0b
  "{\n" ++
  "  \"schema_version\": 1,\n" ++
  "  \"algorithm\": \"initial-message-encoding\",\n" ++
  "  \"source\": \"generated by tacenta-model Vectors.lean (lake exe genvectors initial)\",\n" ++
  "  \"vectors\": [\n" ++
  String.intercalate ",\n" [
    initialVector "with-one-time-prekey" ident ephem [0xc0, 0xde] 3 4 5
      [0xde, 0xad],
    initialVector "without-one-time-prekey" ident ephem [0xc0, 0xde] 3
      Model.Messages.absentId 5 [0xde, 0xad],
    initialVector "empty-kem-ciphertext" ident ephem [] 0x01020304 0xfffefdfc
      0x00010203 [0x00]] ++
  "\n  ]\n}"

/-! ## Post-quantum vectors

The five post-quantum crates are transcribed from these models by hand, and a
hand transcription is where a saturating subtraction becomes a wrapping one,
two chains number messages from different starts, or a protocol label differs
between the model and the implementation so that every derived key differs
with it.

So these cover the derivations rather than the state machines. A state machine
is checked by running it; a derivation is checked by its bytes, and bytes are
what a hand transcription gets wrong. -/

/-- A field element as four hex digits. -/
def bv16Hex (v : Model.Gf65536.Elem) : String :=
  byteHex (UInt8.ofNat ((v >>> 8).toNat)) ++ byteHex (UInt8.ofNat (v.toNat))

def gfVector (id : String) (a b : Model.Gf65536.Elem) : String :=
  "    { \"id\": \"" ++ id ++ "\", \"inputs\": { \"a\": \"" ++ bv16Hex a ++
  "\", \"b\": \"" ++ bv16Hex b ++ "\" }, \"output\": \"" ++
  bv16Hex (Model.Gf65536.mul a b) ++ "\" }"

def invVector (id : String) (a : Model.Gf65536.Elem) : String :=
  "    { \"id\": \"" ++ id ++ "\", \"inputs\": { \"a\": \"" ++ bv16Hex a ++
  "\" }, \"output\": \"" ++ bv16Hex (Model.Gf65536.inv a) ++ "\" }"

/-- Multiplication, chosen to exercise the reduction rather than to look tidy:
    the top bit set on either side is what forces a fold. -/
def gfFile : String :=
  "{\n" ++
  "  \"schema_version\": 1,\n" ++
  "  \"algorithm\": \"gf65536-mul\",\n" ++
  "  \"source\": \"generated by tacenta-model Vectors.lean (lake exe genvectors gf)\",\n" ++
  "  \"vectors\": [\n" ++
  String.intercalate ",\n" [
    gfVector "one-times-one" 1 1,
    gfVector "zero-annihilates" 0x1234 0,
    gfVector "identity" 0xabcd 1,
    gfVector "doubling-no-fold" 0x0001 2,
    gfVector "doubling-folds" 0x8000 2,
    gfVector "both-high-bits" 0xffff 0xffff,
    gfVector "asymmetric" 0x1234 0x5678,
    gfVector "generator-square" 0x0003 0x0003] ++
  "\n  ]\n}"

def invFile : String :=
  "{\n" ++
  "  \"schema_version\": 1,\n" ++
  "  \"algorithm\": \"gf65536-inv\",\n" ++
  "  \"source\": \"generated by tacenta-model Vectors.lean (lake exe genvectors inv)\",\n" ++
  "  \"vectors\": [\n" ++
  String.intercalate ",\n" [
    invVector "one" 1,
    invVector "two" 2,
    invVector "high-bit" 0x8000,
    invVector "all-ones" 0xffff,
    invVector "arbitrary" 0x1234] ++
  "\n  ]\n}"

/-- Interpolation at a node the points do not contain, which is the operation a
    decoder performs and the one the delta property does not by itself pin. -/
def interpVector (id : String) (pts : List (Model.Gf65536.Elem × Model.Gf65536.Elem))
    (x : Model.Gf65536.Elem) : String :=
  let nodes := String.intercalate "" (pts.map (fun p => bv16Hex p.1))
  let vals := String.intercalate "" (pts.map (fun p => bv16Hex p.2))
  "    { \"id\": \"" ++ id ++ "\", \"inputs\": { \"nodes\": \"" ++ nodes ++
  "\", \"values\": \"" ++ vals ++ "\", \"x\": \"" ++ bv16Hex x ++
  "\" }, \"output\": \"" ++ bv16Hex (Model.Polynomial.interp pts x) ++ "\" }"

def interpFile : String :=
  let three : List (Model.Gf65536.Elem × Model.Gf65536.Elem) :=
    [(0, 0x0005), (1, 0x0003), (2, 0x0008)]
  let scattered : List (Model.Gf65536.Elem × Model.Gf65536.Elem) :=
    [(0x0007, 0xbeef), (0x0011, 0x1234), (0x00ff, 0xcafe), (0x8000, 0x0001)]
  "{\n" ++
  "  \"schema_version\": 1,\n" ++
  "  \"algorithm\": \"polynomial-interp\",\n" ++
  "  \"source\": \"generated by tacenta-model Vectors.lean (lake exe genvectors interp)\",\n" ++
  "  \"vectors\": [\n" ++
  String.intercalate ",\n" [
    interpVector "at-a-given-node" three 1,
    interpVector "at-a-lost-node" three 3,
    interpVector "far-from-the-nodes" three 0x4321,
    interpVector "scattered-nodes" scattered 0x0002,
    interpVector "scattered-at-a-node" scattered 0x00ff] ++
  "\n  ]\n}"

/-- The sparse ratchet's chain step. The message number is an input here and a
    constant in the Double Ratchet's, so this is the derivation most likely to
    be transcribed from the wrong one. -/
def spqrCkVector (id : String) (ck : Key) (n : Nat) : String :=
  let r := Model.SparseRatchet.kdfCk ck n
  "    { \"id\": \"" ++ id ++ "\", \"inputs\": { \"ck\": \"" ++ toHex ck ++
  "\", \"n\": \"" ++ toHex (Model.SparseRatchet.be64 n) ++
  "\" }, \"output\": \"" ++ toHex (r.1 ++ r.2) ++ "\" }"

def spqrFile : String :=
  "{\n" ++
  "  \"schema_version\": 1,\n" ++
  "  \"algorithm\": \"spqr-kdf-ck\",\n" ++
  "  \"source\": \"generated by tacenta-model Vectors.lean (lake exe genvectors spqr)\",\n" ++
  "  \"vectors\": [\n" ++
  String.intercalate ",\n" [
    spqrCkVector "first-message" (fill 0x01) 1,
    spqrCkVector "second-message" (fill 0x01) 2,
    spqrCkVector "far-along-the-chain" (fill 0xab) 1000,
    spqrCkVector "number-crosses-a-byte" (fill 0x7f) 256,
    spqrCkVector "zero-chain-key" (fill 0x00) 1] ++
  "\n  ]\n}"

/-- The Braid's epoch key. It carries `PROTOCOL_INFO`, so a label that differs
    between the model and the implementation shows up here as every derived
    key differing. -/
def braidOkVector (id : String) (ss : Key) (epoch : Nat) : String :=
  "    { \"id\": \"" ++ id ++ "\", \"inputs\": { \"ss\": \"" ++ toHex ss ++
  "\", \"epoch\": \"" ++ toHex (Model.SparseRatchet.be64 epoch) ++
  "\" }, \"output\": \"" ++ toHex (Model.Braid.kdfOk ss epoch) ++ "\" }"

def braidFile : String :=
  "{\n" ++
  "  \"schema_version\": 1,\n" ++
  "  \"algorithm\": \"braid-kdf-ok\",\n" ++
  "  \"source\": \"generated by tacenta-model Vectors.lean (lake exe genvectors braid)\",\n" ++
  "  \"vectors\": [\n" ++
  String.intercalate ",\n" [
    braidOkVector "epoch-one" (fill 0x11) 1,
    braidOkVector "epoch-two" (fill 0x11) 2,
    braidOkVector "epoch-crosses-a-byte" (fill 0x22) 256,
    braidOkVector "zero-secret" (fill 0x00) 1] ++
  "\n  ]\n}"

/-- The Braid's authenticator ratchet: a root key and new material in, a new
    root key and MAC key out. -/
def braidAuthVector (id : String) (root : Key) (key : Key) (epoch : Nat) : String :=
  let a : Model.Braid.Auth := ⟨root, []⟩
  let a' := a.update epoch key
  "    { \"id\": \"" ++ id ++ "\", \"inputs\": { \"root\": \"" ++ toHex root ++
  "\", \"key\": \"" ++ toHex key ++
  "\", \"epoch\": \"" ++ toHex (Model.SparseRatchet.be64 epoch) ++
  "\" }, \"output\": \"" ++ toHex (a'.rootKey ++ a'.macKey) ++ "\" }"

def braidAuthFile : String :=
  "{\n" ++
  "  \"schema_version\": 1,\n" ++
  "  \"algorithm\": \"braid-auth-update\",\n" ++
  "  \"source\": \"generated by tacenta-model Vectors.lean (lake exe genvectors auth)\",\n" ++
  "  \"vectors\": [\n" ++
  String.intercalate ",\n" [
    braidAuthVector "from-zero" (List.replicate 32 0) (fill 0x33) 1,
    braidAuthVector "second-epoch" (fill 0x44) (fill 0x55) 2,
    braidAuthVector "epoch-crosses-a-byte" (fill 0x44) (fill 0x55) 256] ++
  "\n  ]\n}"

/-- The composition's two derivations. The Triple Ratchet is the thinnest layer
    in the stack and was the least verified, so pinning it costs least and is
    worth most. -/
def tripleVector (id : String) (a b : Key) : String :=
  "    { \"id\": \"" ++ id ++ "\", \"inputs\": { \"mk_ec\": \"" ++ toHex a ++
  "\", \"mk_pq\": \"" ++ toHex b ++ "\" }, \"output\": \"" ++
  toHex (Model.TripleRatchet.combine a b) ++ "\" }"

def tripleFile : String :=
  "{\n" ++
  "  \"schema_version\": 1,\n" ++
  "  \"algorithm\": \"triple-combine\",\n" ++
  "  \"source\": \"generated by tacenta-model Vectors.lean (lake exe genvectors triple)\",\n" ++
  "  \"vectors\": [\n" ++
  String.intercalate ",\n" [
    tripleVector "distinct-inputs" (fill 0x11) (fill 0x22),
    tripleVector "swapped" (fill 0x22) (fill 0x11),
    tripleVector "equal-inputs" (fill 0x33) (fill 0x33),
    tripleVector "zero-classical" (List.replicate 32 0) (fill 0x44),
    tripleVector "zero-post-quantum" (fill 0x44) (List.replicate 32 0)] ++
  "\n  ]\n}"

def splitVector (id : String) (sk : Key) : String :=
  let r := Model.TripleRatchet.splitSecret sk
  "    { \"id\": \"" ++ id ++ "\", \"inputs\": { \"sk\": \"" ++ toHex sk ++
  "\" }, \"output\": \"" ++ toHex (r.1 ++ r.2) ++ "\" }"

def splitFile : String :=
  "{\n" ++
  "  \"schema_version\": 1,\n" ++
  "  \"algorithm\": \"triple-split\",\n" ++
  "  \"source\": \"generated by tacenta-model Vectors.lean (lake exe genvectors split)\",\n" ++
  "  \"vectors\": [\n" ++
  String.intercalate ",\n" [
    splitVector "ones" (fill 0x01),
    splitVector "zeros" (List.replicate 32 0),
    splitVector "mixed" (fill 0xa5)] ++
  "\n  ]\n}"

/-! ### The composite header

Nearly tautological as a vector, and worth having anyway: what it pins is the
field *order* and the field *widths*, which is exactly what drifts when an
encoding is transcribed by hand. -/

def compositeVector (id : String) (h : Model.CompositeHeader.Composite) : String :=
  let chunkPresent := match h.agChunk with | none => "00" | some _ => "01"
  let chunkIndex := match h.agChunk with
    | none => "0000"
    | some c => toHex (Model.CompositeHeader.be16 c.index)
  let chunkData := match h.agChunk with
    | none => toHex (List.replicate Model.CompositeHeader.chunkBytes 0)
    | some c => toHex c.data
  "    { \"id\": \"" ++ id ++ "\", \"inputs\": { \"dh\": \"" ++ toHex h.dh ++
  "\", \"pn\": \"" ++ toHex (Model.Messages.be32 h.pn) ++
  "\", \"n\": \"" ++ toHex (Model.Messages.be32 h.n) ++
  "\", \"pq_epoch\": \"" ++ toHex (Model.CompositeHeader.be64 h.pqEpoch) ++
  "\", \"pq_n\": \"" ++ toHex (Model.CompositeHeader.be64 h.pqN) ++
  "\", \"ag_epoch\": \"" ++ toHex (Model.CompositeHeader.be64 h.agEpoch) ++
  "\", \"ag_type\": \"" ++ byteHex (Model.CompositeHeader.encodeAgreementType h.agType) ++
  "\", \"chunk_present\": \"" ++ chunkPresent ++
  "\", \"chunk_index\": \"" ++ chunkIndex ++
  "\", \"chunk_data\": \"" ++ chunkData ++
  "\" }, \"output\": \"" ++ toHex (Model.CompositeHeader.encode h) ++ "\" }"

-- The ratchet key is a canonical curve key, since the implementation's decoder,
-- which the runner round-trips each vector through, refuses any other spelling
-- (message-format.md, Curve public keys).
private def compA : Model.CompositeHeader.Composite :=
  { dh := fill 0x5a, pn := 7, n := 9, pqEpoch := 3, pqN := 11, agEpoch := 3,
    agType := .ct1,
    agChunk := some { index := 5, data := fill 0xcd } }

private def compB : Model.CompositeHeader.Composite :=
  { compA with agType := .none, agChunk := Option.none }

private def compC : Model.CompositeHeader.Composite :=
  { dh := fill 0x00, pn := 0xffffffff, n := 0xffffffff,
    pqEpoch := 0xffffffffffffffff, pqN := 0xffffffffffffffff,
    agEpoch := 0xffffffffffffffff, agType := .ekCt1Ack,
    agChunk := some { index := 0xffff, data := fill 0xff } }

def compositeFile : String :=
  "{\n" ++
  "  \"schema_version\": 1,\n" ++
  "  \"algorithm\": \"composite-header\",\n" ++
  "  \"source\": \"generated by tacenta-model Vectors.lean (lake exe genvectors composite)\",\n" ++
  "  \"vectors\": [\n" ++
  String.intercalate ",\n" [
    compositeVector "with-a-codeword" compA,
    compositeVector "without-a-codeword" compB,
    compositeVector "every-counter-saturated" compC] ++
  "\n  ]\n}"

/-! ### A re-spelled curve key, refused at decode

Every curve public key a peer sends is refused unless it is its canonical
encoding (message-format.md, Curve public keys). These vectors put a key in each
position the composite header's and the prekey bundle's decoders read one. Each
key is accepted in its canonical spelling, and refused spelled with bit 255 set
or with p = 2^255 - 19 added. The model's decoders are the oracle for both
verdicts: the generator fails, rather than writing the file, if the model does
not give a vector the result it records. -/

/-- `v` as `len` little-endian bytes, any bits past them dropped. -/
def leBytes : Nat → Nat → List UInt8
  | _, 0 => []
  | v, len + 1 => UInt8.ofNat (v % 256) :: leBytes (v / 256) len

/-- `k` with bit 255 set: the same key to X25519, spelled again. -/
def withBit255 (k : Key) : Key := k.take 31 ++ [k.getD 31 0 ||| 0x80]

/-- `k` with p added: the same key to X25519, spelled again. For a key below 19
    the sum stays below 2^255, so that spelling is refused for its value alone. -/
def plusP (k : Key) : Key :=
  leBytes (Model.Messages.leValue k + Model.Messages.curveP) 32

/-- The base point's u-coordinate, 9: a key small enough that `plusP` leaves
    bit 255 clear. -/
def nine : Key := 9 :: List.replicate 31 0

/-- p - 1, the largest canonical key. -/
def pMinusOne : Key := leBytes (Model.Messages.curveP - 1) 32

/-- p itself, the key 0 to X25519: the smallest value a decoder refuses with
    bit 255 clear, and the one a decoder that refuses only values above p
    accepts. -/
def pItself : Key := leBytes Model.Messages.curveP 32

/-- One decoder vector: the encoding in; for an accepted one, the re-encoding of
    what it decoded to out, and for a refused one, `result: invalid`. -/
def decodeVector (id comment : String) (encoding : List UInt8)
    (accepted : Option (List UInt8)) : String :=
  "    { \"id\": \"" ++ id ++ "\", \"comment\": \"" ++ comment ++ "\", " ++
  (match accepted with
   | some out =>
     "\"inputs\": { \"encoding\": \"" ++ toHex encoding ++ "\" }, \"output\": \"" ++
       toHex out ++ "\" }"
   | none =>
     "\"result\": \"invalid\", \"inputs\": { \"encoding\": \"" ++ toHex encoding ++ "\" } }")

/-- A composite-header decoder vector, written only when the model's decoder
    accepts the encoding exactly when `accept` says it does. -/
@[never_extract]
def compositeDecodeVector (id comment : String) (h : Model.CompositeHeader.Composite)
    (accept : Bool) : Except String String :=
  let encoding := Model.CompositeHeader.encode h
  match Model.CompositeHeader.decode encoding, accept with
  | some (d, rest), true =>
    .ok (decodeVector id comment encoding (some (Model.CompositeHeader.encode d ++ rest)))
  | Option.none, false => .ok (decodeVector id comment encoding Option.none)
  | _, _ => .error ("genvectors: the model's composite-header decoder does not give " ++
      id ++ " the result the vector records")

/-- A function of `Unit` and `never_extract`, as the files further down are
    (Known-answer files with refusals), so a run computes only the file it
    prints. -/
@[never_extract]
def compositeDecodeFile (_ : Unit) : Except String String := do
  let vectors ← [
    compositeDecodeVector "canonical-dh"
      "a ratchet key that is its canonical encoding is accepted" compA true,
    compositeDecodeVector "largest-canonical-dh"
      "p - 1, the largest canonical key, is accepted" { compA with dh := pMinusOne } true,
    compositeDecodeVector "dh-with-bit-255-set"
      "the canonical-dh key with bit 255 set, the same key to X25519, is refused"
      { compA with dh := withBit255 compA.dh } false,
    compositeDecodeVector "dh-plus-p"
      "the key 9 spelled as 9 + p, bit 255 clear and the value at least p, is refused"
      { compA with dh := plusP nine } false,
    compositeDecodeVector "dh-equal-to-p"
      "p itself, the key 0 to X25519 and the smallest value at least p, is refused"
      { compA with dh := pItself } false].mapM id
  pure ("{\n" ++
    "  \"schema_version\": 1,\n" ++
    "  \"algorithm\": \"composite-header-decode\",\n" ++
    "  \"source\": \"generated by tacenta-model Vectors.lean (lake exe genvectors composite-decode), from Model.CompositeHeader.decode; an accepted vector's output is the re-encoding of the header it decodes to, and the generator writes no vector whose result the model does not give\",\n" ++
    "  \"vectors\": [\n" ++
    String.intercalate ",\n" vectors ++
    "\n  ]\n}")

/-- The bundle the bundle vectors vary: every key canonical, the one-time
    prekey present. -/
private def bundleBase : Model.Messages.Bundle :=
  { identityKey := fill 0x11, signedPrekey := fill 0x22,
    signedPrekeySig := List.replicate 64 0x33,
    kemPrekey := List.replicate Model.Messages.kemPrekeyLen 0x44,
    kemPrekeySig := List.replicate 64 0x55, oneTimePrekey := some (fill 0x66),
    signedPrekeyId := 7, oneTimeId := 8, kemPrekeyId := 9 }

/-- A prekey-bundle decoder vector, written only when the model's decoder
    accepts the encoding exactly when `accept` says it does. -/
@[never_extract]
def bundleDecodeVector (id comment : String) (b : Model.Messages.Bundle)
    (accept : Bool) : Except String String :=
  let encoding := Model.Messages.encodeBundle b
  match Model.Messages.decodeBundle encoding, accept with
  | some d, true =>
    .ok (decodeVector id comment encoding (some (Model.Messages.encodeBundle d)))
  | Option.none, false => .ok (decodeVector id comment encoding Option.none)
  | _, _ => .error ("genvectors: the model's prekey-bundle decoder does not give " ++
      id ++ " the result the vector records")

@[never_extract]
def bundleDecodeFile (_ : Unit) : Except String String := do
  let vectors ← [
    bundleDecodeVector "every-key-canonical"
      "identity_key, signed_prekey and one_time_prekey each their canonical encoding: accepted"
      bundleBase true,
    bundleDecodeVector "every-key-the-largest-canonical"
      "p - 1, the largest canonical key, in all three positions: accepted"
      { bundleBase with
          identityKey := pMinusOne
          signedPrekey := pMinusOne
          oneTimePrekey := some pMinusOne } true,
    bundleDecodeVector "identity-key-with-bit-255-set"
      "the every-key-canonical identity_key with bit 255 set: refused"
      { bundleBase with identityKey := withBit255 bundleBase.identityKey } false,
    bundleDecodeVector "identity-key-plus-p"
      "identity_key the key 9 spelled as 9 + p: refused"
      { bundleBase with identityKey := plusP nine } false,
    bundleDecodeVector "identity-key-equal-to-p"
      "identity_key exactly p, the key 0 to X25519: refused"
      { bundleBase with identityKey := pItself } false,
    bundleDecodeVector "signed-prekey-with-bit-255-set"
      "the every-key-canonical signed_prekey with bit 255 set: refused"
      { bundleBase with signedPrekey := withBit255 bundleBase.signedPrekey } false,
    bundleDecodeVector "signed-prekey-plus-p"
      "signed_prekey the key 9 spelled as 9 + p: refused"
      { bundleBase with signedPrekey := plusP nine } false,
    bundleDecodeVector "signed-prekey-equal-to-p"
      "signed_prekey exactly p, the key 0 to X25519: refused"
      { bundleBase with signedPrekey := pItself } false,
    bundleDecodeVector "one-time-prekey-with-bit-255-set"
      "the every-key-canonical one_time_prekey with bit 255 set: refused"
      { bundleBase with oneTimePrekey := some (withBit255 (fill 0x66)) } false,
    bundleDecodeVector "one-time-prekey-plus-p"
      "one_time_prekey the key 9 spelled as 9 + p: refused"
      { bundleBase with oneTimePrekey := some (plusP nine) } false,
    bundleDecodeVector "one-time-prekey-equal-to-p"
      "one_time_prekey exactly p, the key 0 to X25519: refused"
      { bundleBase with oneTimePrekey := some pItself } false].mapM id
  pure ("{\n" ++
    "  \"schema_version\": 1,\n" ++
    "  \"algorithm\": \"prekey-bundle-decode\",\n" ++
    "  \"source\": \"generated by tacenta-model Vectors.lean (lake exe genvectors bundle-decode), from Model.Messages.decodeBundle; an accepted vector's output is the re-encoding of the bundle it decodes to, and the generator writes no vector whose result the model does not give\",\n" ++
    "  \"vectors\": [\n" ++
    String.intercalate ",\n" vectors ++
    "\n  ]\n}")

/-- A curve key in `EncodeEC` form: the curve byte, then the key's thirty-two
    bytes, as an initial message carries its `identity` and `ephemeral`. -/
def ecForm (k : Key) : List UInt8 := Model.Messages.ecCurveByte :: k

/-- An initial-message decoder vector: the given `identity` and `ephemeral`
    around a fixed KEM ciphertext, identifiers and ratchet message, written only
    when the model's decoder accepts the encoding exactly when `accept` says it
    does. -/
@[never_extract]
def initialDecodeVector (id comment : String) (identity ephemeral : List UInt8)
    (accept : Bool) : Except String String :=
  let encoding :=
    Model.Messages.encodeInitial identity ephemeral [0xc0, 0xde] 3 4 5 [0xde, 0xad]
  match Model.Messages.decodeInitial encoding, accept with
  | some d, true =>
    .ok (decodeVector id comment encoding (some (Model.Messages.encodeInitial d.identity
      d.ephemeral d.kemCiphertext d.signedPrekeyId d.oneTimeId d.kemPrekeyId d.ratchetMessage)))
  | Option.none, false => .ok (decodeVector id comment encoding Option.none)
  | _, _ => .error ("genvectors: the model's initial-message decoder does not give " ++
      id ++ " the result the vector records")

@[never_extract]
def initialDecodeFile (_ : Unit) : Except String String := do
  let vectors ← [
    initialDecodeVector "every-key-canonical"
      "identity and ephemeral each the curve byte and a canonical key: accepted"
      (ecForm (fill 0x0a)) (ecForm (fill 0x0b)) true,
    initialDecodeVector "every-key-the-largest-canonical"
      "p - 1, the largest canonical key, as both identity and ephemeral: accepted"
      (ecForm pMinusOne) (ecForm pMinusOne) true,
    initialDecodeVector "identity-with-bit-255-set"
      "the every-key-canonical identity's key with bit 255 set, its curve byte unchanged: refused"
      (ecForm (withBit255 (fill 0x0a))) (ecForm (fill 0x0b)) false,
    initialDecodeVector "identity-plus-p"
      "identity the curve byte and the key 9 spelled as 9 + p: refused"
      (ecForm (plusP nine)) (ecForm (fill 0x0b)) false,
    initialDecodeVector "identity-equal-to-p"
      "identity the curve byte and exactly p, the key 0 to X25519: refused"
      (ecForm pItself) (ecForm (fill 0x0b)) false,
    initialDecodeVector "ephemeral-with-bit-255-set"
      "the every-key-canonical ephemeral's key with bit 255 set, its curve byte unchanged: refused"
      (ecForm (fill 0x0a)) (ecForm (withBit255 (fill 0x0b))) false,
    initialDecodeVector "ephemeral-plus-p"
      "ephemeral the curve byte and the key 9 spelled as 9 + p: refused"
      (ecForm (fill 0x0a)) (ecForm (plusP nine)) false,
    initialDecodeVector "ephemeral-equal-to-p"
      "ephemeral the curve byte and exactly p, the key 0 to X25519: refused"
      (ecForm (fill 0x0a)) (ecForm pItself) false].mapM id
  pure ("{\n" ++
    "  \"schema_version\": 1,\n" ++
    "  \"algorithm\": \"initial-message-decode\",\n" ++
    "  \"source\": \"generated by tacenta-model Vectors.lean (lake exe genvectors initial-decode), from Model.Messages.decodeInitial; an accepted vector's output is the re-encoding of the initial message it decodes to, and the generator writes no vector whose result the model does not give\",\n" ++
    "  \"vectors\": [\n" ++
    String.intercalate ",\n" vectors ++
    "\n  ]\n}")

/-- Print a generated file, or fail the run with the generator's reason. -/
def printOrFail (file : Except String String) : IO Unit :=
  match file with
  | .ok s => IO.println s
  | .error e => throw (IO.userError e)

/-! ## Known-answer files with refusals

Each file below is a function of `Unit`, and each vector builder is
`never_extract`: a closed `String` constant is computed when the program starts,
whichever file was asked for, and the erasure vectors interpolate over up to 48
nodes, which is seconds of field arithmetic apiece. This way a run computes only
the file it prints.

The files below carry refusals as well as answers: a vector the model accepts
has an `output` (or, for a decoder, `fields`), and one it refuses has
`result: invalid` and neither. What the vector says is what the model returned,
not what the input was built to provoke. -/

/-- `n` as `width` big-endian bytes. -/
def beN (width n : Nat) : List UInt8 :=
  (List.range width).reverse.map fun i => UInt8.ofNat (n / 256 ^ i % 256)

def jsonObject (kvs : List (String × String)) : String :=
  "{ " ++ String.intercalate ", " (kvs.map fun p => "\"" ++ p.1 ++ "\": \"" ++ p.2 ++ "\"") ++ " }"

def vectorHead (id comment : String) : String :=
  "    { \"id\": \"" ++ id ++ "\", \"comment\": \"" ++ comment ++ "\", "

/-- A vector with named inputs, and an output when the model gives one. -/
def answerVector (id comment : String) (inputs : List (String × List UInt8))
    (output : Option (List UInt8)) : String :=
  let ins := jsonObject (inputs.map fun p => (p.1, toHex p.2))
  vectorHead id comment ++
  (match output with
   | some o => "\"inputs\": " ++ ins ++ ", \"output\": \"" ++ toHex o ++ "\" }"
   | none => "\"result\": \"invalid\", \"inputs\": " ++ ins ++ " }")

/-- A decode vector: one input, and the named values it decodes to when the
    model accepts it. -/
def fieldsVector (id comment : String) (name : String) (input : List UInt8)
    (fields : Option (List (String × List UInt8))) : String :=
  let ins := jsonObject [(name, toHex input)]
  vectorHead id comment ++
  (match fields with
   | some fs => "\"inputs\": " ++ ins ++ ", \"fields\": " ++
       jsonObject (fs.map fun p => (p.1, toHex p.2)) ++ " }"
   | none => "\"result\": \"invalid\", \"inputs\": " ++ ins ++ " }")

def answerFile (algorithm source : String) (vectors : List String) : String :=
  "{\n" ++
  "  \"schema_version\": 1,\n" ++
  "  \"algorithm\": \"" ++ algorithm ++ "\",\n" ++
  "  \"source\": \"" ++ source ++ "\",\n" ++
  "  \"vectors\": [\n" ++
  String.intercalate ",\n" vectors ++
  "\n  ]\n}"

/-- `n` bytes running through the byte values with a stride, so that no two
    chunks of a value are alike. -/
def ramp (n stride start : Nat) : List UInt8 :=
  (List.range n).map fun i => UInt8.ofNat (i * stride + start)

def replaceAt (bs : List UInt8) (i : Nat) (b : UInt8) : List UInt8 := bs.set i b

/-! ### The erasure code (`Model.Erasure`) -/

@[never_extract]
def codewordsOf (m : List UInt8) (is : List Nat) : List (Nat × List UInt8) :=
  is.map fun i => (i, Model.Erasure.codeword (Model.Erasure.chunks m) i)

/-- The same index with every byte changed. -/
def corrupt (c : Nat × List UInt8) : Nat × List UInt8 := (c.1, c.2.map (· ^^^ 0x5a))

def codewordBytes (cws : List (Nat × List UInt8)) : List UInt8 :=
  (cws.map fun c => beN 2 c.1 ++ c.2).flatten

/-- The codewords a fresh encoder gives at the listed indices, concatenated. With
    `withLength`, also how many codewords the stream issues in all. -/
@[never_extract]
def erasureEncodeVector (id comment : String) (m : List UInt8) (is : List Nat)
    (withLength : Bool) : String :=
  let len := (Model.Erasure.Encoder.new m).remaining (Model.Erasure.maxCodewords + 1) 0
  answerVector id comment
    ([("message", m), ("indices", (is.map (beN 2)).flatten)] ++
      (if withLength then [("stream_length", beN 4 len)] else []))
    (some ((codewordsOf m is).map Prod.snd).flatten)

def m3 : List UInt8 := [0x01, 0x02, 0x03]
def m32 : List UInt8 := ramp 32 3 9
def m96 : List UInt8 := ramp 96 7 3
def m100 : List UInt8 := ramp 100 13 1
def m192 : List UInt8 := ramp 192 29 5
def m1536 : List UInt8 := ramp 1536 31 17

@[never_extract]
def erasureEncodeFile (_ : Unit) : String :=
  answerFile "erasure-encode"
    "generated by tacenta-model Vectors.lean (lake exe genvectors erasure-encode), from Model.Erasure"
    [ erasureEncodeVector "one-chunk-padded"
        "a 3-byte value is one chunk padded with zero bytes; with k = 1 every parity codeword is that chunk again"
        m3 [0, 1, 2, 3] false,
      erasureEncodeVector "header-and-mac"
        "96 bytes, the Braid's header with its MAC: three chunks, then parity"
        m96 [0, 1, 2, 3, 4, 5, 6, 7, 8] false,
      erasureEncodeVector "last-chunk-padded"
        "100 bytes: four chunks, the last padded with 28 zero bytes, and the parity interpolates the padding"
        m100 [0, 1, 2, 3, 4, 5, 6, 7, 8, 9] false,
      erasureEncodeVector "ct2-and-mac-far-indices"
        "192 bytes, the second ciphertext half with its MAC: six chunks, parity just after them and at indices whose high byte is set"
        m192 [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 255, 256, 4096] false,
      erasureEncodeVector "ek-vector"
        "1536 bytes, the encapsulation-key vector: 48 chunks, the last two systematic codewords and two parity codewords"
        m1536 [46, 47, 48, 1000] false,
      erasureEncodeVector "stream-exhaustion"
        "the stream issues indices 0 to 65535, one codeword each, and nothing after; stream_length is how many it issues in all"
        m32 [0, 1, 65534, 65535] true,
      erasureEncodeVector "zero-length-value"
        "a value of zero bytes is zero chunks, so the polynomials have no points and every codeword is 32 zero bytes; the stream still issues indices 0 to 65535, one codeword each, and nothing after"
        [] [0, 1, 2, 65535] true ]

@[never_extract]
def erasureDecodeVector (id comment : String) (size : Nat)
    (cws : List (Nat × List UInt8)) : String :=
  answerVector id comment [("size", beN 4 size), ("codewords", codewordBytes cws)]
    ((Model.Erasure.Decoder.new size).addAll cws).message

@[never_extract]
def erasureDecodeFile (_ : Unit) : String :=
  answerFile "erasure-decode"
    "generated by tacenta-model Vectors.lean (lake exe genvectors erasure-decode), from Model.Erasure; codewords are offered in the order listed, and a vector with no output is a decoder that holds no value"
    [ erasureDecodeVector "systematic-in-order"
        "the four chunks themselves, in order" 100 (codewordsOf m100 [0, 1, 2, 3]),
      erasureDecodeVector "parity-only"
        "no systematic codeword arrives, so every chunk is interpolated" 100
        (codewordsOf m100 [4, 5, 6, 7]),
      erasureDecodeVector "mixed-out-of-order"
        "systematic and parity codewords arriving out of order" 192
        (codewordsOf m192 [9, 2, 7, 0, 11, 5]),
      erasureDecodeVector "far-indices"
        "codewords from the far end of the stream" 96
        (codewordsOf m96 [65535, 40000, 1000]),
      erasureDecodeVector "ek-vector-two-chunks-lost"
        "1536 bytes: chunks 46 and 47 are interpolated from 46 systematic codewords and two parity codewords" 1536
        (codewordsOf m1536 (List.range 46 ++ [1000, 48])),
      erasureDecodeVector "later-copy-ignored"
        "a corrupt copy at an index already held is ignored, so the value is recovered" 96
        (let cw := codewordsOf m96 [3, 0, 4]
         cw.take 1 ++ [corrupt (cw.getD 0 (0, []))] ++ cw.drop 1),
      erasureDecodeVector "first-copy-wins-though-corrupt"
        "the first copy at an index is kept even when a later one differs, so a corrupt parity codeword first yields a different value" 96
        (let cw := codewordsOf m96 [4, 0, 5]
         [corrupt (cw.getD 0 (0, []))] ++ cw),
      erasureDecodeVector "held-chunk-taken-as-it-is"
        "a systematic codeword held at index t is chunk t, corrupt or not, and enters the interpolation of the rest" 96
        (let cw := codewordsOf m96 [1, 0, 5]
         [corrupt (cw.getD 0 (0, []))] ++ cw),
      erasureDecodeVector "ignored-once-full"
        "once k codewords are held every further one is ignored, a systematic one included" 96
        (codewordsOf m96 [5, 1, 0] ++ (codewordsOf m96 [2, 3]).map corrupt),
      erasureDecodeVector "short-value-truncated"
        "one parity codeword recovers a 3-byte value, truncated from its padded chunk" 3
        (codewordsOf m3 [7]),
      erasureDecodeVector "empty-value" "a decoder for zero bytes holds the empty value at once" 0 [],
      erasureDecodeVector "empty-value-ignores-codewords"
        "a decoder for zero bytes already holds k = 0 codewords, so it ignores what arrives" 0
        (codewordsOf m3 [0]),
      erasureDecodeVector "one-short" "k - 1 codewords are not a value" 96 (codewordsOf m96 [0, 5]),
      erasureDecodeVector "repeats-do-not-count"
        "three codewords at one index are one codeword" 96
        (let cw := codewordsOf m96 [1]
         cw ++ cw ++ cw.map corrupt),
      erasureDecodeVector "nothing-arrived" "no codeword, no value" 100 [] ]

/-! ### The erasure coders' persisted formats (`Model.Erasure`) -/

/-- The bytes an encoder is stored as after issuing `n` codewords, when the
    model's reader reads them back to the same encoder. -/
@[never_extract]
def encoderStateVector (id comment : String) (m : List UInt8) (n : Nat) : String :=
  let e := (Model.Erasure.Encoder.new m).issue n
  answerVector id comment [("message", m), ("issued", beN 4 n)]
    (if Model.Erasure.Encoder.ofBytes e.toBytes = some e then some e.toBytes else none)

/-- Stored bytes offered to the reader: accepted, with the encoder they hold
    written back, or refused. -/
@[never_extract]
def encoderBytesVector (id comment : String) (bs : List UInt8) : String :=
  answerVector id comment [("bytes", bs)]
    ((Model.Erasure.Encoder.ofBytes bs).map Model.Erasure.Encoder.toBytes)

def m40 : List UInt8 := ramp 40 11 7

def storedEncoder : List UInt8 := ((Model.Erasure.Encoder.new m40).issue 1).toBytes

@[never_extract]
def erasureEncoderFile (_ : Unit) : String :=
  answerFile "erasure-encoder-state"
    "generated by tacenta-model Vectors.lean (lake exe genvectors erasure-encoder-state), from Model.Erasure"
    [ encoderStateVector "fresh" "an encoder that has issued nothing" m100 0,
      encoderStateVector "mid-prefix" "two systematic codewords issued" m100 2,
      encoderStateVector "past-the-prefix" "six codewords issued, two of them parity" m100 6,
      encoderStateVector "zero-length-value" "an encoder for zero bytes holds no chunks" [] 0,
      encoderStateVector "last-index-next" "65535 issued, so next is the last index and the encoder is not yet exhausted" m32 65535,
      encoderStateVector "exhausted" "every index issued: next stays at 65535 and exhausted is set" m32 65536,
      encoderBytesVector "exhausted-at-the-last-index" "stored bytes the reader accepts" (replaceAt (replaceAt (replaceAt storedEncoder 0 0xff) 1 0xff) 2 0x01),
      encoderBytesVector "exhausted-byte-two" "exhausted is 0x00 or 0x01 and nothing else" (replaceAt storedEncoder 2 0x02),
      encoderBytesVector "exhausted-before-the-last-index" "exhausted only when next is 65535" (replaceAt storedEncoder 2 0x01),
      encoderBytesVector "count-beyond-the-buffer" "a count the buffer does not hold" (replaceAt storedEncoder 6 0x03),
      encoderBytesVector "count-short-of-the-buffer" "bytes left after the last chunk the count names" (replaceAt storedEncoder 6 0x01),
      encoderBytesVector "trailing-byte" "one byte after the last chunk" (storedEncoder ++ [0x00]),
      encoderBytesVector "shorter-than-the-fixed-fields" "six bytes cannot hold next, exhausted and count" (storedEncoder.take 6) ]

/-- The bytes a decoder is stored as after being offered `cws`, when the
    model's reader reads them back to the same decoder. -/
@[never_extract]
def decoderStateVector (id comment : String) (size : Nat)
    (cws : List (Nat × List UInt8)) : String :=
  let d := (Model.Erasure.Decoder.new size).addAll cws
  answerVector id comment [("size", beN 4 size), ("codewords", codewordBytes cws)]
    (if Model.Erasure.Decoder.ofBytes d.toBytes = some d then some d.toBytes else none)

@[never_extract]
def decoderBytesVector (id comment : String) (bs : List UInt8) : String :=
  answerVector id comment [("bytes", bs)]
    ((Model.Erasure.Decoder.ofBytes bs).map Model.Erasure.Decoder.toBytes)

def storedDecoder (size needed : Nat) (cws : List (Nat × List UInt8)) : List UInt8 :=
  beN 8 size ++ beN 8 needed ++ beN 4 cws.length ++ codewordBytes cws

@[never_extract]
def erasureDecoderFile (_ : Unit) : String :=
  let cw := codewordsOf m100 [6, 1]
  let c6 := cw.take 1
  answerFile "erasure-decoder-state"
    "generated by tacenta-model Vectors.lean (lake exe genvectors erasure-decoder-state), from Model.Erasure; codewords are offered in the order listed"
    [ decoderStateVector "fresh" "a decoder holding nothing" 100 [],
      decoderStateVector "partial" "two of four codewords, held in arrival order" 100 cw,
      decoderStateVector "full" "k codewords held" 96 (codewordsOf m96 [5, 1, 0]),
      decoderStateVector "repeats-and-extras-not-held"
        "a repeat at a held index and a codeword after the kth are not stored" 96
        (let c := codewordsOf m96 [2, 7, 0, 9]
         c.take 1 ++ (c.take 1).map corrupt ++ c.drop 1),
      decoderStateVector "zero-length-value" "a decoder for zero bytes" 0 [],
      decoderBytesVector "widest-the-field-allows" "size 2097152 and needed 65536 sit exactly on both bounds" (storedDecoder 2097152 65536 []),
      decoderBytesVector "needed-not-the-chunk-count" "needed is ceil(size / 32)" (storedDecoder 100 5 cw),
      decoderBytesVector "needed-above-the-field" "needed above 65536, with size agreeing" (storedDecoder 2097184 65537 []),
      decoderBytesVector "fits-only-after-narrowing" "both values bounded as 64-bit integers: their low halves alone would be a valid decoder" (storedDecoder (4294967296 + 96) (4294967296 + 3) []),
      decoderBytesVector "duplicate-index" "no two held codewords share an index" (storedDecoder 100 4 (c6 ++ c6)),
      decoderBytesVector "more-than-needed" "at most needed codewords are held" (storedDecoder 32 1 cw),
      decoderBytesVector "count-beyond-the-buffer" "a count the buffer does not hold" (replaceAt (storedDecoder 100 4 cw) 19 0x03),
      decoderBytesVector "trailing-byte" "one byte after the last codeword" (storedDecoder 100 4 cw ++ [0x00]) ]

/-! ### The ratchets' persisted states (`Model.PersistedState`)

A state's stored bytes are either the result of operations the vector lists,
run from a fresh state or from stored bytes the reader accepts, or bytes
offered to the reader. The generator writes an operations vector only if the
model accepts every operation and the state it reaches reads back to itself,
with the bytes of that state read back beside it; and it writes a bytes vector
only if the model's reader gives it the result the vector records, for a
refusal the refusal too. -/

/-- The name a vector gives a refusal: session-persistence.md, Rejection's
    "wrong version" and "short or malformed". -/
def refusalName : Model.PersistedState.Refusal → String
  | .wrongVersion => "wrong-version"
  | .shortOrMalformed => "short-or-malformed"

/-- A refused stored-state vector: its bytes, and the refusal. -/
def refusedStateVector (id comment : String) (bs : List UInt8)
    (r : Model.PersistedState.Refusal) : String :=
  vectorHead id comment ++ "\"result\": \"invalid\", \"refusal\": \"" ++ refusalName r ++
    "\", \"inputs\": " ++ jsonObject [("bytes", toHex bs)] ++ " }"

/-- Operations whose last step is refused at a counter's ceiling: the inputs,
    and the refusal, counter exhaustion (ratchet.md, Sending and receiving;
    sparse-pq-ratchet.md, Sending and Receiving). -/
def refusedOpsVector (id comment : String) (inputs : List (String × List UInt8)) : String :=
  vectorHead id comment ++ "\"result\": \"invalid\", \"refusal\": \"counter-exhaustion\", \"inputs\": " ++
    jsonObject (inputs.map fun p => (p.1, toHex p.2)) ++ " }"

/-- Stored bytes offered to a reader: accepted, with the fields `fieldsOf`
    names, when `expect` is `none`; refused with `expect` otherwise. -/
@[never_extract]
def storedStateVector {σ : Type}
    (reader : List UInt8 → Except Model.PersistedState.Refusal σ)
    (fieldsOf : σ → List (String × List UInt8)) (id comment : String) (bs : List UInt8)
    (expect : Option Model.PersistedState.Refusal) : Except String String :=
  match reader bs, expect with
  | .ok st, none => .ok (fieldsVector id comment "bytes" bs (some (fieldsOf st)))
  | .error r, some r' =>
    if r = r' then .ok (refusedStateVector id comment bs r)
    else .error ("genvectors: the model's reader refuses " ++ id ++
      " as " ++ refusalName r ++ ", not as the vector records")
  | _, _ => .error ("genvectors: the model's reader does not give " ++ id ++
      " the result the vector records")

-- `u32Max` and `u64Max`, the largest values the formats' counters hold, are
-- the model's own: `Model.State.u32Max` and `Model.SparseRatchet.u64Max`.
open Model.SparseRatchet (u64Max)

/-! #### The classical ratchet's state -/

/-- One operation on a classical ratchet state. -/
inductive RatchetStep where
  | send
  | receive (h : Header) (dhRecv dhSend newPub : Key)

/-- `00` for a send; `01`, then the header's `dh(32) || pn(4) || n(4)`, then
    `dh_recv(32) || dh_send(32) || new_pub(32)`, for a receive. -/
def RatchetStep.bytes : RatchetStep → List UInt8
  | .send => [0x00]
  | .receive h r d np => [0x01] ++ h.dh ++ beN 4 h.pn ++ beN 4 h.n ++ r ++ d ++ np

/-- The state after the steps, or `none` if the model refuses one. -/
def runRatchet (st : State) : List RatchetStep → Option State
  | [] => some st
  | .send :: rest =>
    match send st with
    | some (st', _, _) => runRatchet st' rest
    | none => none
  | .receive h r d np :: rest =>
    match receive st h r d np with
    | some (st', _) => runRatchet st' rest
    | none => none

/-- Where a classical ratchet vector's operations start. -/
inductive RatchetStart where
  | initiator
  | responder
  | stored (st : State)

def RatchetStart.state : RatchetStart → State
  | .initiator => initSender sk aPub bPub dhAB .tacenta
  | .responder => initReceiver sk bPub .tacenta
  | .stored st => st

def RatchetStart.inputs : RatchetStart → List (String × List UInt8)
  | .initiator => [("role", [0x00]), ("sk", sk), ("our_pub", aPub), ("peer_pub", bPub), ("dh_out", dhAB)]
  | .responder => [("role", [0x01]), ("sk", sk), ("our_pub", bPub)]
  | .stored st => [("start", Model.PersistedState.RatchetState.toBytes st)]

/-- The fields an accepted classical ratchet state holds, as the vectors name
    them: an absent key is left out, every integer is its field's big-endian
    bytes, and `skipped` is the stored keys laid out back to back. -/
def ratchetFields (st : State) : List (String × List UInt8) :=
  [("dhs_pub", st.dhsPub)] ++ st.dhrPub.toList.map (("dhr_pub", ·)) ++ [("rk", st.rk)] ++
    st.cks.toList.map (("cks", ·)) ++ st.ckr.toList.map (("ckr", ·)) ++
    [("ns", beN 4 st.ns), ("nr", beN 4 st.nr), ("pn", beN 4 st.pn), ("events", beN 4 st.events),
     ("labels", [Model.PersistedState.RatchetState.labelsByte st.labels]),
     ("skipped", (st.skipped.map Model.PersistedState.RatchetState.entryBytes).flatten)]

@[never_extract]
def ratchetStored (id comment : String) (bs : List UInt8)
    (expect : Option Model.PersistedState.Refusal) : Except String String :=
  storedStateVector Model.PersistedState.RatchetState.ofBytes ratchetFields id comment bs expect

def ratchetReadsBack (st : State) : Bool :=
  Model.PersistedState.readsBackTo
    (Model.PersistedState.RatchetState.ofBytes (Model.PersistedState.RatchetState.toBytes st)) st

/-- A state built by operations, and its stored bytes read back. -/
@[never_extract]
def ratchetOps (id comment : String) (start : RatchetStart) (steps : List RatchetStep) :
    Except String (List String) :=
  let startOk := match start with
    | .stored st => ratchetReadsBack st
    | _ => true
  match runRatchet start.state steps with
  | none => .error ("genvectors: " ++ id ++ ": the model refuses an operation the vector lists")
  | some st =>
    if startOk && ratchetReadsBack st then do
      let bs := Model.PersistedState.RatchetState.toBytes st
      let back ← ratchetStored (id ++ "-read-back") ("the stored bytes of " ++ id ++ ", read back") bs none
      pure [answerVector id comment
        (start.inputs ++ [("steps", (steps.map RatchetStep.bytes).flatten)]) (some bs), back]
    else .error ("genvectors: " ++ id ++ ": a stored state does not read back to itself")

/-- Operations whose last step the model refuses at a counter's ceiling. The
    generator writes one only if the start reads back, the model takes every
    step before the last and refuses the last, and `atCeiling` holds of the
    state the last is refused from, so that the refusal is the ceiling's. -/
@[never_extract]
def ratchetRefused (id comment : String) (start : RatchetStart) (steps : List RatchetStep)
    (last : RatchetStep) (atCeiling : State → Bool) : Except String String :=
  let startOk := match start with
    | .stored st => ratchetReadsBack st
    | _ => true
  match runRatchet start.state steps with
  | none => .error ("genvectors: " ++ id ++ ": the model refuses a step before the last")
  | some st =>
    if !startOk then
      .error ("genvectors: " ++ id ++ ": a stored state does not read back to itself")
    else if (runRatchet st [last]).isSome then
      .error ("genvectors: " ++ id ++ ": the model takes the step the vector refuses")
    else if !atCeiling st then
      .error ("genvectors: " ++ id ++ ": the refused step is not at a counter's ceiling")
    else
      .ok (refusedOpsVector id comment
        (start.inputs ++ [("steps", ((steps ++ [last]).map RatchetStep.bytes).flatten)]))

/-- The messages the classical vectors pass between the two parties: Alice's
    first three, Bob's reply once he has taken the first, and Alice's first on
    her second chain once she has taken the reply. -/
structure RatchetScript where
  h0 : Header
  h1 : Header
  h2 : Header
  r0 : Header
  h3 : Header

def ratchetScript : Option RatchetScript := do
  let (a1, h0, _) ← send (initSender sk aPub bPub dhAB .tacenta)
  let (a2, h1, _) ← send a1
  let (a3, h2, _) ← send a2
  let (b1, _) ← receive (initReceiver sk bPub .tacenta) h0 dhAB dhSendB bPub2
  let (_, r0, _) ← send b1
  let (a4, _) ← receive a3 r0 (mockDh aPub bPub2) (mockDh aPub2 bPub2) aPub2
  let (_, h3, _) ← send a4
  pure { h0, h1, h2, r0, h3 }

/-- A state that `runRatchet` reaches, or the generator's refusal. -/
def reachRatchet (what : String) (start : RatchetStart) (steps : List RatchetStep) :
    Except String State :=
  match runRatchet start.state steps with
  | some st => .ok st
  | none => .error ("genvectors: the model refuses the steps to " ++ what)

@[never_extract]
def ratchetStateFile (_ : Unit) : Except String String := do
  let some s := ratchetScript
    | throw "genvectors: the model refuses the classical ratchet's script"
  let first := RatchetStep.receive s.h0 dhAB dhSendB bPub2
  let thirdFirst := RatchetStep.receive s.h2 dhAB dhSendB bPub2
  let same (h : Header) := RatchetStep.receive h zero zero zero
  let replied := RatchetStep.receive s.r0 (mockDh aPub bPub2) (mockDh aPub2 bPub2) aPub2
  let secondChain := RatchetStep.receive s.h3 (mockDh bPub2 aPub2) (mockDh bPub3 aPub2) bPub3
  let answered ← reachRatchet "a responder's first receive" .responder [first]
  let withStore ← reachRatchet "a responder's stored keys" .responder [thirdFirst]
  let fresh := RatchetStart.responder.state
  let e0 := withStore.skipped.getD 0 (zero, 0, 0, zero)
  let clockStart : State :=
    { withStore with events := u32Max - 2,
                     skipped := withStore.skipped.map fun e => (e.1, e.2.1, u32Max - 2, e.2.2.2) }
  let clockStop : State :=
    { withStore with events := u32Max - 1,
                     skipped := withStore.skipped.map fun e => (e.1, e.2.1, u32Max - 1, e.2.2.2) }
  let ops ← [
    ratchetOps "fresh-initiator"
      "init_sender: a sending chain and the peer's ratchet key, nothing stored" .initiator [],
    ratchetOps "fresh-responder"
      "init_receiver: no chain and no peer ratchet key" .responder [],
    ratchetOps "initiator-after-three-sends"
      "three sends on the first chain: ns is 3" .initiator [.send, .send, .send],
    ratchetOps "responder-after-a-receive"
      "the first receive takes the Diffie-Hellman step: both chains, the peer's key, one event" .responder [first],
    ratchetOps "responder-stores-skipped-keys"
      "the third message first: keys 0 and 1 stored under the peer's key at stored_at 0" .responder [thirdFirst],
    ratchetOps "responder-uses-a-stored-key"
      "then the first message, from the store: key 1 is left and events is 2" .responder [thirdFirst, same s.h0],
    ratchetOps "initiator-after-a-reply"
      "three sends, the reply taken with a Diffie-Hellman step, and a send on the new chain: pn is 3" .initiator
      [.send, .send, .send, replied, .send],
    ratchetOps "responder-stores-across-a-step"
      "the first message, a reply, then the initiator's second chain with pn 3: keys 1 and 2 of the old chain are stored at the step, and key 1 is then used" .responder
      [first, .send, secondChain, same s.h1],
    ratchetOps "clock-reaches-its-stop"
      "from events u32::MAX - 2, a receive from the store: events reaches u32::MAX - 1 and the other key, stored at u32::MAX - 2, is kept"
      (.stored clockStart) [same s.h0],
    ratchetOps "send-counter-reaches-u32-max"
      "from ns u32::MAX - 1, a send: ns is u32::MAX, which no rule constrains"
      (.stored { RatchetStart.initiator.state with ns := u32Max - 1 }) [.send],
    ratchetOps "receive-counter-reaches-u32-max"
      "from nr u32::MAX - 1, the message numbered u32::MAX - 1: nr is u32::MAX"
      (.stored { answered with nr := u32Max - 1 })
      [same { dh := aPub, pn := 0, n := u32Max - 1 }],
    ratchetOps "clock-stays-at-its-stop"
      "from events u32::MAX - 1, the clock's stop, a receive from the store: events stays u32::MAX - 1, and the other key, stored at u32::MAX - 1, is kept"
      (.stored clockStop) [same s.h0],
    ratchetOps "clock-stays-at-its-stop-on-the-chain"
      "from events u32::MAX - 1, the next message on the chain: events stays u32::MAX - 1"
      (.stored { answered with events := u32Max - 1 }) [same s.h1]
  ].mapM id
  let refusals ← [
    ratchetRefused "send-at-u32-max-refused"
      "from ns u32::MAX, a send: refused as counter exhaustion (ChainExhausted), since message number u32::MAX is never used"
      (.stored { RatchetStart.initiator.state with ns := u32Max }) [] .send
      (fun st => st.cks.isSome && st.ns == u32Max),
    ratchetRefused "receive-at-nr-u32-max-refused"
      "from nr u32::MAX, the message numbered u32::MAX on the same chain: refused as counter exhaustion (ChainExhausted)"
      (.stored { answered with nr := u32Max }) [] (same { dh := aPub, pn := 0, n := u32Max })
      (fun st => st.ckr.isSome && st.nr == u32Max)
  ].mapM id
  let respBytes := Model.PersistedState.RatchetState.toBytes answered
  let freshBytes := Model.PersistedState.RatchetState.toBytes fresh
  let storeBytes := Model.PersistedState.RatchetState.toBytes withStore
  let enc (st : State) := Model.PersistedState.RatchetState.toBytes st
  let withEntry0 (e : Key × Nat × Nat × Key) : State :=
    { withStore with skipped := e :: withStore.skipped.drop 1 }
  let bytesVectors ← [
    ratchetStored "every-key-the-largest-canonical"
      "p - 1, the largest canonical key, as dhs_pub, dhr_pub and each stored key's dh: accepted"
      (enc { withStore with dhsPub := pMinusOne, dhrPub := some pMinusOne,
                            skipped := withStore.skipped.map fun e => (pMinusOne, e.2) }) none,
    ratchetStored "counters-with-no-chains"
      "ns 5, nr 7 and pn 3 with no chain: no rule constrains them (ADR-0007)"
      (enc { fresh with ns := 5, nr := 7, pn := 3 }) none,
    ratchetStored "stored-at-equal-to-events"
      "a stored key's stored_at equal to events: accepted" (enc { withStore with events := 0 }) none,
    ratchetStored "stored-keys-in-any-order"
      "stored keys out of the order they were stored, and one with the same n under another ratchet key: accepted, in the order read"
      (enc { withStore with skipped := withStore.skipped.reverse ++ [(bPub3, 1, 0, fill 0x5c)] }) none,
    ratchetStored "empty" "no bytes" [] (some .shortOrMalformed),
    ratchetStored "version-zero" "a first byte of 0x00" (replaceAt respBytes 0 0x00) (some .wrongVersion),
    ratchetStored "version-two" "a first byte of 0x02" (replaceAt respBytes 0 0x02) (some .wrongVersion),
    ratchetStored "shorter-than-the-fixed-fields" "184 bytes of a fresh responder's 185"
      (freshBytes.take 184) (some .shortOrMalformed),
    ratchetStored "dhr-presence-tag-two" "dhr_pub_present 0x02" (replaceAt respBytes 33 0x02) (some .shortOrMalformed),
    ratchetStored "cks-presence-tag-two" "cks_present 0x02" (replaceAt respBytes 98 0x02) (some .shortOrMalformed),
    ratchetStored "ckr-presence-tag-ff" "ckr_present 0xff" (replaceAt respBytes 131 0xff) (some .shortOrMalformed),
    ratchetStored "absent-dhr-not-zeroed" "dhr_pub absent, its last byte 0x01" (replaceAt freshBytes 65 0x01) (some .shortOrMalformed),
    ratchetStored "absent-cks-not-zeroed" "cks absent, its first byte 0x01" (replaceAt freshBytes 99 0x01) (some .shortOrMalformed),
    ratchetStored "absent-ckr-not-zeroed" "ckr absent, a byte inside it 0x80" (replaceAt freshBytes 150 0x80) (some .shortOrMalformed),
    ratchetStored "labels-tag-one" "a labels tag that names no variant" (replaceAt respBytes 180 0x01) (some .shortOrMalformed),
    ratchetStored "count-beyond-the-buffer" "skipped_count 3 with two entries" (replaceAt storeBytes 184 0x03) (some .shortOrMalformed),
    ratchetStored "count-short-of-the-buffer" "skipped_count 1 with two entries: bytes after the last" (replaceAt storeBytes 184 0x01) (some .shortOrMalformed),
    ratchetStored "trailing-byte" "one byte after the last stored key" (storeBytes ++ [0x00]) (some .shortOrMalformed),
    ratchetStored "entry-cut-short" "the last stored key one byte short" (storeBytes.take (storeBytes.length - 1)) (some .shortOrMalformed),
    ratchetStored "store-over-its-bound" "2001 stored keys: the store holds at most MAX_SKIPPED_STORE (2000)"
      (enc { withStore with skipped := (List.range 2001).map fun i => (aPub, i, 0, fill 0x5c) }) (some .shortOrMalformed),
    ratchetStored "clock-at-u32-max" "events u32::MAX: the clock is below it"
      (enc { answered with events := u32Max }) (some .shortOrMalformed),
    ratchetStored "stored-after-the-clock" "a stored key's stored_at one past events"
      (enc (withEntry0 (e0.1, e0.2.1, 2, e0.2.2.2))) (some .shortOrMalformed),
    ratchetStored "two-keys-one-pair" "two stored keys under one ratchet key and message number"
      (enc { withStore with skipped := [e0, (e0.1, e0.2.1, e0.2.2.1, fill 0x5c)] }) (some .shortOrMalformed),
    ratchetStored "receiving-chain-without-a-sending-chain" "ckr present and cks absent"
      (enc { answered with cks := none }) (some .shortOrMalformed),
    ratchetStored "receiving-chain-without-a-peer-key" "ckr present and dhr_pub absent"
      (enc { answered with dhrPub := none }) (some .shortOrMalformed),
    ratchetStored "dhs-pub-with-bit-255-set" "dhs_pub with bit 255 set: the same key to X25519"
      (enc { answered with dhsPub := withBit255 answered.dhsPub }) (some .shortOrMalformed),
    ratchetStored "dhs-pub-plus-p" "dhs_pub the key 9 spelled as 9 + p"
      (enc { answered with dhsPub := plusP nine }) (some .shortOrMalformed),
    ratchetStored "dhs-pub-equal-to-p" "dhs_pub exactly p, the key 0 to X25519"
      (enc { answered with dhsPub := pItself }) (some .shortOrMalformed),
    ratchetStored "dhr-pub-with-bit-255-set" "dhr_pub with bit 255 set"
      (enc { answered with dhrPub := answered.dhrPub.map withBit255 }) (some .shortOrMalformed),
    ratchetStored "dhr-pub-plus-p" "dhr_pub the key 9 spelled as 9 + p"
      (enc { answered with dhrPub := some (plusP nine) }) (some .shortOrMalformed),
    ratchetStored "dhr-pub-equal-to-p" "dhr_pub exactly p"
      (enc { answered with dhrPub := some pItself }) (some .shortOrMalformed),
    ratchetStored "stored-dh-with-bit-255-set" "a stored key's dh with bit 255 set"
      (enc (withEntry0 (withBit255 e0.1, e0.2))) (some .shortOrMalformed),
    ratchetStored "stored-dh-plus-p" "a stored key's dh the key 9 spelled as 9 + p"
      (enc (withEntry0 (plusP nine, e0.2))) (some .shortOrMalformed),
    ratchetStored "stored-dh-equal-to-p" "a stored key's dh exactly p"
      (enc (withEntry0 (pItself, e0.2))) (some .shortOrMalformed)
  ].mapM id
  pure ("{\n" ++
    "  \"schema_version\": 1,\n" ++
    "  \"algorithm\": \"ratchet-state\",\n" ++
    "  \"source\": \"generated by tacenta-model Vectors.lean (lake exe genvectors ratchet-state), from Model.PersistedState.RatchetState and Model.Ratchet; Diffie-Hellman outputs are the generator's symmetric stand-in, not X25519, and the generator writes no vector whose result the model does not give\",\n" ++
    "  \"vectors\": [\n" ++
    String.intercalate ",\n" (ops.flatten ++ refusals ++ bytesVectors) ++
    "\n  ]\n}")

/-! #### The sparse ratchet's state -/

/-- One operation on a sparse ratchet state. -/
inductive SparseStep where
  | send (epoch : Nat) (out : Option Model.SparseRatchet.Output)
  | receive (epoch : Nat) (out : Option Model.SparseRatchet.Output) (n : Nat)

/-- `output_present(1) || output_epoch(8) || output_key(32)`, zeroed when
    absent. -/
def sparseOutputBytes : Option Model.SparseRatchet.Output → List UInt8
  | none => List.replicate 41 0
  | some o => [0x01] ++ beN 8 o.keyEpoch ++ o.key

/-- `op(1) || epoch(8) || output`, `op` `00` for a send and `01` for a
    receive, which is followed by the message number `n(8)`. -/
def SparseStep.bytes : SparseStep → List UInt8
  | .send e o => [0x00] ++ beN 8 e ++ sparseOutputBytes o
  | .receive e o n => [0x01] ++ beN 8 e ++ sparseOutputBytes o ++ beN 8 n

def runSparse (st : Model.SparseRatchet.State) : List SparseStep → Option Model.SparseRatchet.State
  | [] => some st
  | .send e o :: rest =>
    match Model.SparseRatchet.send st e o with
    | some (st', _, _) => runSparse st' rest
    | none => none
  | .receive e o n :: rest =>
    match Model.SparseRatchet.receive st e o n with
    | some (st', _) => runSparse st' rest
    | none => none

inductive SparseStart where
  | alice
  | bob
  | stored (st : Model.SparseRatchet.State)

def SparseStart.state : SparseStart → Model.SparseRatchet.State
  | .alice => Model.SparseRatchet.initAlice sk
  | .bob => Model.SparseRatchet.initBob sk
  | .stored st => st

def SparseStart.inputs : SparseStart → List (String × List UInt8)
  | .alice => [("direction", [0x00]), ("sk", sk)]
  | .bob => [("direction", [0x01]), ("sk", sk)]
  | .stored st => [("start", Model.PersistedState.SparseState.toBytes st)]

/-- The fields an accepted sparse ratchet state holds: `chains` and `skipped`
    are their entries laid out back to back. -/
def sparseFields (st : Model.SparseRatchet.State) : List (String × List UInt8) :=
  [("rk", st.rk), ("epoch", beN 8 st.epoch),
   ("direction", [Model.PersistedState.SparseState.directionByte st.direction]),
   ("chains", (st.chains.map Model.PersistedState.SparseState.chainsEntryBytes).flatten),
   ("skipped", (st.skipped.map Model.PersistedState.SparseState.skippedBytes).flatten)]

@[never_extract]
def sparseStored (id comment : String) (bs : List UInt8)
    (expect : Option Model.PersistedState.Refusal) : Except String String :=
  storedStateVector Model.PersistedState.SparseState.ofBytes sparseFields id comment bs expect

def sparseReadsBack (st : Model.SparseRatchet.State) : Bool :=
  Model.PersistedState.readsBackTo
    (Model.PersistedState.SparseState.ofBytes (Model.PersistedState.SparseState.toBytes st)) st

@[never_extract]
def sparseOps (id comment : String) (start : SparseStart) (steps : List SparseStep) :
    Except String (List String) :=
  let startOk := match start with
    | .stored st => sparseReadsBack st
    | _ => true
  match runSparse start.state steps with
  | none => .error ("genvectors: " ++ id ++ ": the model refuses an operation the vector lists")
  | some st =>
    if startOk && sparseReadsBack st then do
      let bs := Model.PersistedState.SparseState.toBytes st
      let back ← sparseStored (id ++ "-read-back") ("the stored bytes of " ++ id ++ ", read back") bs none
      pure [answerVector id comment
        (start.inputs ++ [("steps", (steps.map SparseStep.bytes).flatten)]) (some bs), back]
    else .error ("genvectors: " ++ id ++ ": a stored state does not read back to itself")

/-- Operations whose last step the model refuses at a counter's ceiling, as
    `ratchetRefused` writes them for the classical ratchet. -/
@[never_extract]
def sparseRefused (id comment : String) (start : SparseStart) (steps : List SparseStep)
    (last : SparseStep) (atCeiling : Model.SparseRatchet.State → Bool) : Except String String :=
  let startOk := match start with
    | .stored st => sparseReadsBack st
    | _ => true
  match runSparse start.state steps with
  | none => .error ("genvectors: " ++ id ++ ": the model refuses a step before the last")
  | some st =>
    if !startOk then
      .error ("genvectors: " ++ id ++ ": a stored state does not read back to itself")
    else if (runSparse st [last]).isSome then
      .error ("genvectors: " ++ id ++ ": the model takes the step the vector refuses")
    else if !atCeiling st then
      .error ("genvectors: " ++ id ++ ": the refused step is not at a counter's ceiling")
    else
      .ok (refusedOpsVector id comment
        (start.inputs ++ [("steps", ((steps ++ [last]).map SparseStep.bytes).flatten)]))

def reachSparse (what : String) (start : SparseStart) (steps : List SparseStep) :
    Except String Model.SparseRatchet.State :=
  match runSparse start.state steps with
  | some st => .ok st
  | none => .error ("genvectors: the model refuses the steps to " ++ what)

@[never_extract]
def sparseRatchetStateFile (_ : Unit) : Except String String := do
  let out (e : Nat) (b : UInt8) : Option Model.SparseRatchet.Output := some { keyEpoch := e, key := fill b }
  let alice := SparseStart.alice.state
  let bob := SparseStart.bob.state
  let cs := (alice.chains.getD 0 (0, default)).2
  let bobCs := (bob.chains.getD 0 (0, default)).2
  let withChain (st : Model.SparseRatchet.State) (f : Model.SparseRatchet.Chain → Model.SparseRatchet.Chain)
      (sendSide : Bool) : Model.SparseRatchet.State :=
    { st with chains := st.chains.map fun p =>
        (p.1, if sendSide then { p.2 with send := p.2.send.map f } else { p.2 with receive := p.2.receive.map f }) }
  let bobStore ← reachSparse "Bob's stored keys" .bob [.receive 0 none 3]
  let ops ← [
    sparseOps "fresh-alice" "init with direction A2b: epoch 0's two chains, nothing stored" .alice [],
    sparseOps "fresh-bob" "init with direction B2a: the same chain keys, assigned the other way" .bob [],
    sparseOps "alice-after-two-sends" "two sends on epoch 0: its sending chain's n is 2" .alice
      [.send 0 none, .send 0 none],
    sparseOps "bob-stores-skipped-keys" "message 3 first: keys 1 and 2 of epoch 0 stored" .bob [.receive 0 none 3],
    sparseOps "bob-uses-a-stored-key" "then message 1, from the store" .bob [.receive 0 none 3, .receive 0 none 1],
    sparseOps "alice-opens-an-epoch"
      "a send carrying epoch 1's secret, on epoch 0: both epochs' chains, epoch 0's entry rewritten last" .alice
      [.send 0 (out 1 0xa1)],
    sparseOps "bob-follows-into-the-epoch" "that message received, then a send on epoch 1" .bob
      [.receive 0 (out 1 0xa1) 1, .send 1 none],
    sparseOps "bob-retires-an-epoch-with-its-keys"
      "keys 1 and 2 of epoch 0 stored, then epochs 1 and 2 opened: epoch 0's chains and keys are retired" .bob
      [.receive 0 none 3, .receive 0 (out 1 0xa1) 4, .receive 1 (out 2 0xa2) 1],
    sparseOps "epoch-reaches-one-below-the-ceiling"
      "from epoch u64::MAX - 2, a receive carrying epoch u64::MAX - 1's secret: the window's sum saturates, and epochs u64::MAX - 2 and u64::MAX - 1 are kept"
      (.stored { bob with epoch := u64Max - 2, chains := [(u64Max - 3, bobCs), (u64Max - 2, bobCs)] })
      [.receive (u64Max - 2) (out (u64Max - 1) 0xa3) 1],
    sparseOps "send-counter-reaches-u64-max" "from a sending chain at n u64::MAX - 1, a send: message number u64::MAX is usable"
      (.stored (withChain alice (fun c => { c with n := u64Max - 1 }) true)) [.send 0 none],
    sparseOps "receive-counter-reaches-u64-max" "from a receiving chain at n u64::MAX - 1, message u64::MAX"
      (.stored (withChain bob (fun c => { c with n := u64Max - 1 }) false)) [.receive 0 none u64Max]
  ].mapM id
  let counterAt (st : Model.SparseRatchet.State) (e : Nat) (sendSide : Bool) : Option Nat :=
    (Model.SparseRatchet.findChains st e).bind fun c =>
      (if sendSide then c.send else c.receive).map (·.n)
  let refusals ← [
    sparseRefused "advance-onto-u64-max-refused"
      "from epoch u64::MAX - 1, a receive carrying epoch u64::MAX's secret: refused as counter exhaustion (ChainExhausted), since epoch u64::MAX is reserved"
      (.stored { bob with epoch := u64Max - 1, chains := [(u64Max - 2, bobCs), (u64Max - 1, bobCs)] })
      [] (.receive (u64Max - 1) (out u64Max 0xa4) 1) (fun st => st.epoch + 1 == u64Max),
    sparseRefused "send-past-u64-max-refused"
      "from a sending chain at n u64::MAX, a send: refused as counter exhaustion (ChainExhausted)"
      (.stored (withChain alice (fun c => { c with n := u64Max }) true)) [] (.send 0 none)
      (fun st => counterAt st 0 true == some u64Max),
    sparseRefused "receive-past-u64-max-refused"
      "from a receiving chain at n u64::MAX, message u64::MAX: refused as counter exhaustion (ChainExhausted)"
      (.stored (withChain bob (fun c => { c with n := u64Max }) false)) [] (.receive 0 none u64Max)
      (fun st => counterAt st 0 false == some u64Max)
  ].mapM id
  let enc (st : Model.SparseRatchet.State) := Model.PersistedState.SparseState.toBytes st
  let aliceBytes := enc alice
  let storeBytes := enc bobStore
  let absentSend : Model.SparseRatchet.State :=
    { alice with chains := [(0, { cs with send := none })] }
  let absentBytes := enc absentSend
  let key (b : UInt8) := fill b
  let bytesVectors ← [
    sparseStored "absent-chain-accepted" "a chain whose presence byte is 0x00, zeroed: accepted, though no operation produces one"
      absentBytes none,
    sparseStored "stored-key-numbered-zero" "a stored key numbered 0: no rule relates a key's number to its chain (ADR-0007)"
      (enc { bobStore with skipped := [(0, 0, key 0x5c)] }) none,
    sparseStored "stored-key-past-its-counter" "a stored key numbered 9 on a receiving chain at 3: accepted (ADR-0007)"
      (enc { bobStore with skipped := [(0, 9, key 0x5c)] }) none,
    sparseStored "stored-keys-in-any-order" "stored keys newest first: accepted, in the order read"
      (enc { bobStore with skipped := bobStore.skipped.reverse }) none,
    sparseStored "empty" "no bytes" [] (some .shortOrMalformed),
    sparseStored "version-zero" "a first byte of 0x00" (replaceAt aliceBytes 0 0x00) (some .wrongVersion),
    sparseStored "version-two" "a first byte of 0x02" (replaceAt aliceBytes 0 0x02) (some .wrongVersion),
    sparseStored "shorter-than-the-prefix" "45 bytes: the version, rk, epoch and direction, and three bytes of chains_count"
      (aliceBytes.take 45) (some .shortOrMalformed),
    sparseStored "direction-tag-two" "a direction tag of 0x02" (replaceAt aliceBytes 41 0x02) (some .shortOrMalformed),
    sparseStored "send-presence-tag-two" "a send chain presence byte of 0x02" (replaceAt aliceBytes 54 0x02) (some .shortOrMalformed),
    sparseStored "receive-presence-tag-ff" "a receive chain presence byte of 0xff" (replaceAt aliceBytes 95 0xff) (some .shortOrMalformed),
    sparseStored "absent-chain-ck-not-zeroed" "an absent chain whose ck has a byte 0x01" (replaceAt absentBytes 55 0x01) (some .shortOrMalformed),
    sparseStored "absent-chain-n-not-zeroed" "an absent chain whose n is 1" (replaceAt absentBytes 94 0x01) (some .shortOrMalformed),
    sparseStored "chains-count-beyond-the-buffer" "chains_count 2 with one entry" (replaceAt aliceBytes 45 0x02) (some .shortOrMalformed),
    sparseStored "skipped-count-beyond-the-buffer" "skipped_count 3 with two entries"
      (replaceAt storeBytes 139 0x03) (some .shortOrMalformed),
    sparseStored "no-skipped-count" "the bytes end after the chains" (aliceBytes.take 136) (some .shortOrMalformed),
    sparseStored "trailing-byte" "one byte after the last stored key" (storeBytes ++ [0x00]) (some .shortOrMalformed),
    sparseStored "store-over-its-bound" "2001 stored keys: the store holds at most MAX_SKIPPED_STORE (2000)"
      (enc { bobStore with skipped := (List.range 2001).map fun i => (0, i + 1, key 0x5c) }) (some .shortOrMalformed),
    sparseStored "chains-epoch-after-the-current" "an entry for epoch 1 at epoch 0"
      (enc { alice with chains := [(0, cs), (1, cs)] }) (some .shortOrMalformed),
    sparseStored "chains-epoch-outside-the-window" "an entry for epoch 0 at epoch 2: 2 is not below 0 + EPOCHS_KEPT"
      (enc { alice with epoch := 2, chains := [(0, cs), (2, cs)] }) (some .shortOrMalformed),
    sparseStored "two-entries-one-epoch" "two entries for epoch 0"
      (enc { alice with chains := [(0, cs), (0, cs)] }) (some .shortOrMalformed),
    sparseStored "current-epoch-without-an-entry" "epoch 1 with an entry for epoch 0 only"
      (enc { alice with epoch := 1 }) (some .shortOrMalformed),
    sparseStored "stored-key-epoch-without-an-entry" "a stored key under epoch 1 with an entry for epoch 0 only"
      (enc { bobStore with skipped := [(1, 1, key 0x5c)] }) (some .shortOrMalformed),
    sparseStored "two-stored-keys-one-pair" "two stored keys for epoch 0, message 1"
      (enc { bobStore with skipped := [(0, 1, key 0x5c), (0, 1, key 0x5d)] }) (some .shortOrMalformed),
    sparseStored "epoch-at-the-ceiling" "epoch u64::MAX with its own entry: u64::MAX is not below the saturated u64::MAX + EPOCHS_KEPT"
      (enc { alice with epoch := u64Max, chains := [(u64Max, cs)] }) (some .shortOrMalformed)
  ].mapM id
  pure ("{\n" ++
    "  \"schema_version\": 1,\n" ++
    "  \"algorithm\": \"sparse-ratchet-state\",\n" ++
    "  \"source\": \"generated by tacenta-model Vectors.lean (lake exe genvectors sparse-ratchet-state), from Model.PersistedState.SparseState and Model.SparseRatchet; the agreement's outputs are fixed byte strings, and the generator writes no vector whose result the model does not give\",\n" ++
    "  \"vectors\": [\n" ++
    String.intercalate ",\n" (ops.flatten ++ refusals ++ bytesVectors) ++
    "\n  ]\n}")

/-! #### The Triple Ratchet's state

The composition of the two states above, each length-prefixed. Its own rule is
the one only the composition can state: while the classical ratchet still
shows the role it started in, the sparse ratchet's `direction` agrees with
it. -/

/-- One operation on a Triple Ratchet state. -/
inductive TripleStep where
  | send (sendingEpoch : Nat) (out : Option Model.SparseRatchet.Output)
  | receive (h : Model.Triple.Header) (dhRecv dhSend newPub : Key)
      (out : Option Model.SparseRatchet.Output)

/-- `00` a send, with the epoch it sends on and the agreement's output; `01` a
    receive, with the classical header's `dh(32) || pn(4) || n(4)`, the step's
    `dh_recv(32) || dh_send(32) || new_pub(32)`, the sparse half's
    `epoch(8) || pq_n(8)`, and the output last. An output is
    `output_present(1) || output_epoch(8) || output_key(32)`, zeroed when
    absent, as in `sparse-ratchet-state.json`. -/
def TripleStep.bytes : TripleStep → List UInt8
  | .send e o => [0x00] ++ beN 8 e ++ sparseOutputBytes o
  | .receive h r d np o =>
    [0x01] ++ h.dr.dh ++ beN 4 h.dr.pn ++ beN 4 h.dr.n ++ r ++ d ++ np
      ++ beN 8 h.epoch ++ beN 8 h.pqN ++ sparseOutputBytes o

def runTriple (st : Model.Triple.State) : List TripleStep → Option Model.Triple.State
  | [] => some st
  | .send e o :: rest =>
    match Model.Triple.send st e o with
    | some (st', _, _) => runTriple st' rest
    | none => none
  | .receive h r d np o :: rest =>
    match Model.Triple.receive st h r d np o with
    | some (st', _) => runTriple st' rest
    | none => none

inductive TripleStart where
  | initiator
  | responder
  | stored (st : Model.Triple.State)

def TripleStart.state : TripleStart → Model.Triple.State
  | .initiator => Model.Triple.initAlice sk aPub bPub dhAB .tacenta
  | .responder => Model.Triple.initBob sk bPub .tacenta
  | .stored st => st

def TripleStart.inputs : TripleStart → List (String × List UInt8)
  | .initiator =>
    [("role", [0x00]), ("sk", sk), ("our_pub", aPub), ("peer_pub", bPub), ("dh_out", dhAB)]
  | .responder => [("role", [0x01]), ("sk", sk), ("our_pub", bPub)]
  | .stored st => [("start", Model.PersistedState.TripleState.toBytes st)]

/-- The fields an accepted Triple Ratchet state holds: each half's own stored
    bytes, which is all this format carries. -/
def tripleFields (st : Model.Triple.State) : List (String × List UInt8) :=
  [("classical", Model.PersistedState.RatchetState.toBytes st.classical),
   ("post_quantum", Model.PersistedState.SparseState.toBytes st.postQuantum)]

@[never_extract]
def tripleStored (id comment : String) (bs : List UInt8)
    (expect : Option Model.PersistedState.Refusal) : Except String String :=
  storedStateVector Model.PersistedState.TripleState.ofBytes tripleFields id comment bs expect

def tripleReadsBack (st : Model.Triple.State) : Bool :=
  Model.PersistedState.readsBackTo
    (Model.PersistedState.TripleState.ofBytes (Model.PersistedState.TripleState.toBytes st)) st

@[never_extract]
def tripleOps (id comment : String) (start : TripleStart) (steps : List TripleStep) :
    Except String (List String) :=
  let startOk := match start with
    | .stored st => tripleReadsBack st
    | _ => true
  match runTriple start.state steps with
  | none => .error ("genvectors: " ++ id ++ ": the model refuses an operation the vector lists")
  | some st =>
    if startOk && tripleReadsBack st then do
      let bs := Model.PersistedState.TripleState.toBytes st
      let back ← tripleStored (id ++ "-read-back")
        ("the stored bytes of " ++ id ++ ", read back") bs none
      pure [answerVector id comment
        (start.inputs ++ [("steps", (steps.map TripleStep.bytes).flatten)]) (some bs), back]
    else .error ("genvectors: " ++ id ++ ": a stored state does not read back to itself")

@[never_extract]
def tripleStateFile (_ : Unit) : Except String String := do
  let alice := TripleStart.initiator.state
  let bob := TripleStart.responder.state
  let some (_, h0, _) := Model.Triple.send alice 0 Option.none
    | throw "genvectors: the model refuses the Triple Ratchet's opening send"
  let firstReceive := TripleStep.receive h0 dhAB dhSendB bPub2 Option.none
  let ops ← [
    tripleOps "fresh-initiator"
      "init_alice: the classical half's sending chain and the sparse half's A2b direction, which is the role the two agree on" .initiator [],
    tripleOps "fresh-responder"
      "init_bob: neither classical chain and the sparse half's B2a direction" .responder [],
    tripleOps "initiator-after-a-send"
      "one send on epoch 0: both halves step, and the classical half still shows the sender's role" .initiator
      [.send 0 Option.none],
    tripleOps "responder-after-a-receive"
      "the initiator's first message: the classical half takes its Diffie-Hellman step, after which it shows no role and the rule holds vacuously" .responder
      [firstReceive]
  ].mapM id
  let aliceBytes := Model.PersistedState.TripleState.toBytes alice
  let classicalLen := (Model.PersistedState.RatchetState.toBytes alice.classical).length
  -- The inner spqr_state's version byte: the outer version, the first length,
  -- the classical half, and the second length.
  let sparseVersionAt := 1 + 4 + classicalLen + 4
  let mixed : Model.Triple.State :=
    { classical := alice.classical, postQuantum := bob.postQuantum }
  let bytesVectors ← [
    tripleStored "empty" "no bytes" [] (some .shortOrMalformed),
    tripleStored "version-zero" "a first byte of 0x00" (replaceAt aliceBytes 0 0x00)
      (some .wrongVersion),
    tripleStored "version-two" "a first byte of 0x02" (replaceAt aliceBytes 0 0x02)
      (some .wrongVersion),
    tripleStored "classical-half-with-an-unknown-version"
      "the ratchet_state's own version byte is 0x02: short or malformed, not a wrong version, since this format's version namespace is its own"
      (replaceAt aliceBytes 5 0x02) (some .shortOrMalformed),
    tripleStored "sparse-half-with-an-unknown-version"
      "the spqr_state's own version byte is 0x02: short or malformed for the same reason"
      (replaceAt aliceBytes sparseVersionAt 0x02) (some .shortOrMalformed),
    tripleStored "classical-half-malformed"
      "the ratchet_state's labels tag names no variant, so its own reader refuses it"
      (replaceAt aliceBytes (5 + 180) 0x01) (some .shortOrMalformed),
    tripleStored "first-length-overruns"
      "the classical half's length one byte past its own, so the half its reader is handed is not the half that was written"
      (replaceAt aliceBytes 4 (UInt8.ofNat ((classicalLen + 1) % 256))) (some .shortOrMalformed),
    tripleStored "second-half-missing" "the bytes end after the classical half"
      (aliceBytes.take (1 + 4 + classicalLen)) (some .shortOrMalformed),
    tripleStored "trailing-byte" "one byte after the sparse half"
      (aliceBytes ++ [0x00]) (some .shortOrMalformed),
    tripleStored "halves-disagree-on-the-role"
      "the initiator's classical half beside the responder's sparse half: each half's own reader accepts its bytes and the composition refuses them"
      (Model.PersistedState.TripleState.toBytes mixed) (some .shortOrMalformed)
  ].mapM id
  pure ("{\n" ++
    "  \"schema_version\": 1,\n" ++
    "  \"algorithm\": \"triple-ratchet-state\",\n" ++
    "  \"source\": \"generated by tacenta-model Vectors.lean (lake exe genvectors triple-ratchet-state), from Model.PersistedState.TripleState and Model.Triple; Diffie-Hellman outputs are the generator's symmetric stand-in, not X25519, and the generator writes no vector whose result the model does not give\",\n" ++
    "  \"vectors\": [\n" ++
    String.intercalate ",\n" (ops.flatten ++ bytesVectors) ++
    "\n  ]\n}")


/-! #### The prekey store's state

**Accepted vectors are fixtures, not generated, and that is the point.** The
model has no signatures (`Model.PersistedState.PrekeyStoreState` says why at
length), so it cannot produce a store whose stored signatures verify, and
`tacenta-core` refuses one whose signatures do not. The three accepted vectors
below therefore carry bytes produced once by `tacenta-core` itself
(`print_prekey_store_fixtures`, a `FixedRng` so they are a property of that code
and not of whichever PRNG `rand` ships), and the model's own reader is run over
them here: the generator writes them only if its reader accepts them and writes
them back unchanged.

**Refusal vectors are built by changing one field of a fixture**, not by
assembling a store from stand-ins. A stand-in KEM key pair would be refused by
`tacenta-core` at `kem::KeyPair::from_bytes`, before the rule the vector claims
to test was ever reached -- the vector would pass, for the wrong reason, and
nothing would say so. Starting from a fixture keeps every other field valid, so
the rule under test is the only thing wrong. -/

def prekeyFixture_no_one_time : String :=
  "04132c442be010fbd57e72603328aa76e71fccc1503aae219327d14d9c9993f472111013121514171619181b1a1d1c1f1e010003020504070609080b0a0d0c0f0e00000001c75c780d5973455dbf8e77d6e47be08329ca1ee00026e7e7349b6d27baa52a44152aa5661c433b9126410a9cf3ad49c14db7f703e68a22d373dd9ca14141390f0000000000001280d6e98d2587a2468092d3239d6565bee644927af38f2d48ce66f905b27338453b5095b50554da8c85e13df80232f7d33d07e69467d7bc0fa6c785a22d29f324d4673ddfc7a5319289eb132cc86a6d11e35b23e37cefb832a3b843b57c3b9ae626743a061d5a7d44672817919ded62a6e877ad356a5ff447ba9a524bf46cb72b42af9303a2304a073e1648c794ae5e297177e76709d87050a160c1c818ed9a85ab1112f5b91b3a78269a82935c543a64973ff4031609cc62e03734bd178852f148ab40981507cfaa6173b0765a59a309f43b5106a58ec562458e36c178b98dd239653f35958c22b79d26b5e23610daa03d70fa4b44b46fe639a1ae2c384b730b76652da5c2af3812b061e5c018ab2544e16cbb639a17c180ae3c701f87856f3ba8dc4613258128a21706fd444589481a9a4bc6f3da7d70838cb909cb76062c69161fb7c965c99442e1a48b50a440df72c29ef784ff69b5f275773deb6b7a1b102ef77e90d3c694ab7ccbd2838392bc0b008fb71070b62110b607baccda70b3b8a78c2a8feefb70f4c31a2dc99509934d07718cb82c3c14e5c1ab21a5d3875b84014335633b3edb9b54bcae8f2b9dbedc3db9c5bfb3441e97e69f85948363b2a87cf62521f484d55450a49b08b5fb8094fa7cb219976a726c785a38deb77be964b897045a9e21c129b415f3962bb5635254737cc15722a0e007911586c520a848493644c253e918269dbb7b5ab857428aab9ab2897fb651f9e70c069b0ddbb68132d687406a97c16069d64b6021b8252dea05c5d16ba08933fa518136925b93c72aca27658fc7bb531ba927d829839ac4b5891d7d46143cd1064daa16f08a3ad37ac6d0a58a742308d6eb041107883927951f804436e445be7072bfbb4237e0153aba3b349499f62a63f268c52fa7717d46042dd27458606c4199351cd0787cb9c2cfd8c3aa03a97a405451b9cd96a1a76f1045ef696523ecc5df7875a0391b83b9210ec66a44d895d2f535cc019ab3fc95ed00621a00c8e5a182532954b53b6fb2eb40b638a0665bb1fb27365df71f83359151f95c17a12146205a0d78bfe581b4de8793bcb622f30906ea05a2be3219ec35206a7c247d20c4a64a3515c7073cabc9c6354dc0253261a80d6082573879a2d267b8d7a00c21e8583d9acfb20b1504d63b0a5324ddcc7a9dc19fc41126b1328f4b886e67b0876beb48f6a29ad9d86e12863762d3a7ba34b23eeca430052627909b66166523e18d41836030d3bea99741d4d38bdbb2bbba42c6c484c8b9473e01c28ac935591bc25163b15988485f3003bf6f420085954b5f0508f33b0d1b7513c286c99507c8ab03613f715a2d58a65abcabd811a75d8338061b1fadcb39c60883be20c9bef45b78a97711b26b3a56534dd4630edbaee20ca7cbc07726109698896a786b3f730a181cca3473071ae950189f69c144cb52091c32a9c1bb3d8bc3c2fb226148a650d85a01a074b4da3da90ac961735de26aaca372b40e4650bf431f07b04c4b031c7cd7183f26bd622abe1fc1a68c6504a0b26eb4356514983375790d2d719229119aff5b00da6b526a38b55ef2023b61c3b4c5ba2b38c3338988d23a9575a02c40806864ca99166906e1b522c6a862f5628189c9c77149ccf577704079aed85b0ee6376736b3ac198012b812372ed6b52e84b989ba5ed44a353a222b61a8622e7946835072ecd14cc82267ae0a2b62052d1531254033893d171a315a0067436ff791092f0a49f05c0b3366b6a27b4be3c3b238a31aa9a849b6467df65c9648b09cd9c9187f470a08e61c858483b59187b65a907bec017647323a0c21f013615798b111daa1df0a5112b61ff2a27fcd15369bc6ab567334294976a87ba914a541bc52bd9ebc262a3b878f56cc44b50c87d47bd053772d5b35b9d7b713327e1708632a60742dc8cc703b1850db4ed3e905e86ba1d645475ab4a210f59f7224bd0b950f497c54f8a87512250f33f832d9047208631ee4571fd8826340b97db9f4ade08850f9bc6562f59510db6cb76533c32c70f083b702e5435788a4acbb48458985c8e7a542ec3c0443637f02c623eccd7d201d349219a6646e26a12a7cf76877aac31102b8095154fc4231c438358058c49ddcbe60b27fd641cef910998568cafb1781b78909df6b44e638b526f4a26cb6736c3b2413c538047227421919ac05c07ea6741882726a3a5bd6a49c68b12faeb32621f79a493b8a47c7059c1b7225215bf58aa6d9d6a070f067dd89aee0d55d69046a4bf629e1767c0e0c12e8f0336a358571430fd9facfdd63a9f8278ebad05a4785549d3c82d6b05b9bc0519fd6c9427a88f0539e82d5c372155bc4e2945830634f53525fa6a11f70572d07478c6a852c57565aa1b08b4c727a2a8f0ea75a4c646de3e7506c3742a4571a28328258c077f0a8bffc7310dcd0b1c142ab834b34a4a0acc520a5ed7a0d3d2bc0ffe0b4bac898e3178ec13aae04f6b6451a05a58b35a32bbf7cba4e42ac483c9825ba3aa5dd1ba18779302c70b5e473bb9e3b153eb855706b9c0aab0f81e09be60027c8bcbce3dc94a4650dee9209f5296d783c0194e61edfaa9aa1524af6e2b106c03aa8b0943ff8a1eb37b600712b9c5a6a268857d6ac7aa25567281b42b9154b0cb4a9ff630aeba664d4f49d30f10bdad5a0b189356fc5272ba5c245d8c25b7456b4e4955bb53b4214509f4618975c2c104429f64706fa0ad0aa710077c7c080d782b1594a29713ba44a44a680bb2dab3487086ee279c58cbc53390923536a97068b40ed7949c0769b2026bd1e7c74c94b4f726474f49786fef27de65095b43c80b69789528a7c09e416a37963d3052756035b0f97ba03dc0b14ba33a38280551b6051c4a6d7b4168f29af3b454ac2fa304f517d04ea1d8cacab99c6b33e26966f0b66b78b684278b4a29a69d9547076c873ad03752b869e6d9c26c2955c43099d573268de9372f2449f4d82c5ef211c79b6732d18bbf1539b86b54f91495c423202d193147d9899625b2590e4a9d81c0035c82de9a133d7d3925a2520176404c2e4169b0b6298780725e5cbfadac0423c38ea674ad2b0565d851ac375aaa027578b9c036a757e4555a8ff725d58462aa7b686bb090983979398c4c2f5b1868e5b667484a4c5e175cb8c47514a282559ab92f900af4716c42bccefe00a5428752936155d0509ffb06c7bb528802ca421b881bb309a7b5100cda0a78502c0616abb0bec44f27759b08b1be62897cd802c5b776794f1a5cf5b333156caed698674d093a65cc7337b24bd146394a87d7cf9185f50c3cc854f4a43323f8a9bd89623ce2c247b8b8ca0e96926495bf566c64814befc44618c389873dc08e4cb744d16b72b7b6da9a5811cfb676de9adfd8660b07390255c25560623b89b4c15db0a67d0703f53340c73374b71a258758adbb6169aa96ea21b99113c9db498b77f9c8af45a675c29abdba3cdf96587c262345521ca346508bd2c7f2eda67b4b24c98d154023a1cae68c79834026a5815ea9795ab9004c175ade999c87f82166332c314270db5f6baa82c07b5667e29fa58d87aa7c63bc5e42637389431a6d84271f514bed87f43d07e9a009490f485c847acd9c39d8a8c24fbb131fbe76961127755a11a521c6ef0a85de14a692db5c4ac8c19a6b0302b49a33d21440777b269669bcfa09b88731b74a7936982c2023b1b219c909a6c6f532b6c2549c2dde2bcdf7932712b30658b8d9a35047fe548bff54cd35011987039de22cce9dc555c5c8dd499abfd0a19eacb5241f525ea552ea5a23ac4aaaff4945ceda2741c0142edd90d0b8515f10a757dd48fba1c438752cb7b277655d39a941a820563bc3ba872f1b64b8de96257679eed24bca8d012468715efe5a4e8e10e14b66340d97b487a2f3bbc16b7fb31e7a4cd5bd5c80ad68fd2e65dc360cf0820aa5877802705378210055b6b47e0e677f217b425078c2eb573b5b67bfbd30ea931a29480b163331d6fa824af17138bd15e0182a4c1b37644496ac50c9f567b316ee225ee795f1ff3673148cbbd68a2f8986ef6e4bba637715d50cc099acbded6c77785c9ddd920d08359b1783a5496cbf1178bc458a0212b2b4e109c91f93c177307f7d69badf43fef72c271793b21d19886f9575a01b6f3a5ae2ca50e92fc21b5b8255c032119e412016bc0a87a0da3b89be1722ff9aaab48c03345143d05f2a9bd535688f558d0379f4eb50562488c4e368902821ced7152fdb89a1982965e1933fcdaaea42828174764b3d080a6770168147f445cbbd0c51feb715870a8712eac273bd1600eb310c8e1974801bae51943663c8ad591cb7c4ad8c6fdbef06db4c722f1cc2e01f28cba32be19907cb8d6dcf7580f5eef0e05042a5e092c354a7861642815183a17c9d8a307e7953eb1ead629f8cc111013121514171619181b1a1d1c1f1e010003020504070609080b0a0d0c0f0ee638b526f4a26cb6736c3b2413c538047227421919ac05c07ea6741882726a3a5bd6a49c68b12faeb32621f79a493b8a47c7059c1b7225215bf58aa6d9d6a070f067dd89aee0d55d69046a4bf629e1767c0e0c12e8f0336a358571430fd9facfdd63a9f8278ebad05a4785549d3c82d6b05b9bc0519fd6c9427a88f0539e82d5c372155bc4e2945830634f53525fa6a11f70572d07478c6a852c57565aa1b08b4c727a2a8f0ea75a4c646de3e7506c3742a4571a28328258c077f0a8bffc7310dcd0b1c142ab834b34a4a0acc520a5ed7a0d3d2bc0ffe0b4bac898e3178ec13aae04f6b6451a05a58b35a32bbf7cba4e42ac483c9825ba3aa5dd1ba18779302c70b5e473bb9e3b153eb855706b9c0aab0f81e09be60027c8bcbce3dc94a4650dee9209f5296d783c0194e61edfaa9aa1524af6e2b106c03aa8b0943ff8a1eb37b600712b9c5a6a268857d6ac7aa25567281b42b9154b0cb4a9ff630aeba664d4f49d30f10bdad5a0b189356fc5272ba5c245d8c25b7456b4e4955bb53b4214509f4618975c2c104429f64706fa0ad0aa710077c7c080d782b1594a29713ba44a44a680bb2dab3487086ee279c58cbc53390923536a97068b40ed7949c0769b2026bd1e7c74c94b4f726474f49786fef27de65095b43c80b69789528a7c09e416a37963d3052756035b0f97ba03dc0b14ba33a38280551b6051c4a6d7b4168f29af3b454ac2fa304f517d04ea1d8cacab99c6b33e26966f0b66b78b684278b4a29a69d9547076c873ad03752b869e6d9c26c2955c43099d573268de9372f2449f4d82c5ef211c79b6732d18bbf1539b86b54f91495c423202d193147d9899625b2590e4a9d81c0035c82de9a133d7d3925a2520176404c2e4169b0b6298780725e5cbfadac0423c38ea674ad2b0565d851ac375aaa027578b9c036a757e4555a8ff725d58462aa7b686bb090983979398c4c2f5b1868e5b667484a4c5e175cb8c47514a282559ab92f900af4716c42bccefe00a5428752936155d0509ffb06c7bb528802ca421b881bb309a7b5100cda0a78502c0616abb0bec44f27759b08b1be62897cd802c5b776794f1a5cf5b333156caed698674d093a65cc7337b24bd146394a87d7cf9185f50c3cc854f4a43323f8a9bd89623ce2c247b8b8ca0e96926495bf566c64814befc44618c389873dc08e4cb744d16b72b7b6da9a5811cfb676de9adfd8660b07390255c25560623b89b4c15db0a67d0703f53340c73374b71a258758adbb6169aa96ea21b99113c9db498b77f9c8af45a675c29abdba3cdf96587c262345521ca346508bd2c7f2eda67b4b24c98d154023a1cae68c79834026a5815ea9795ab9004c175ade999c87f82166332c314270db5f6baa82c07b5667e29fa58d87aa7c63bc5e42637389431a6d84271f514bed87f43d07e9a009490f485c847acd9c39d8a8c24fbb131fbe76961127755a11a521c6ef0a85de14a692db5c4ac8c19a6b0302b49a33d21440777b269669bcfa09b88731b74a7936982c2023b1b219c909a6c6f532b6c2549c2dde2bcdf7932712b30658b8d9a35047fe548bff54cd35011987039de22cce9dc555c5c8dd499abfd0a19eacb5241f525ea552ea5a23ac4aaaff4945ceda2741c0142edd90d0b8515f10a757dd48fba1c438752cb7b277655d39a941a820563bc3ba872f1b64b8de96257679eed24bca8d012468715efe5a4e8e10e14b66340d97b487a2f3bbc16b7fb31e7a4cd5bd5c80ad68fd2e65dc360cf0820aa5877802705378210055b6b47e0e677f217b425078c2eb573b5b67bfbd30ea931a29480b163331d6fa824af17138bd15e0182a4c1b37644496ac50c9f567b316ee225ee795f1ff3673148cbbd68a2f8986ef6e4bba637715d50cc099acbded6c77785c9ddd920d08359b1783a5496cbf1178bc458a0212b2b4e109c91f93c177307f7d69badf43fef72c271793b21d19886f9575a01b6f3a5ae2ca50e92fc21b5b8255c032119e412016bc0a87a0da3b89be1722ff9aaab48c03345143d05f2a9bd535688f558d0379f4eb50562488c4e368902821ced7152fdb89a1982965e1933fcdaaea42828174764b3d080a6770168147f445cbbd0c51feb715870a8712eac273bd1600eb310c8e1974801bae51943663c8ad591cb7c4ad8c6fdbef06db4c722f1cc2e01f28cba32be19907cb8d6dcf7580f00000002853e7369ad89000e3f6b94f43d5641147d27ab9ebc8bea0e2e53d163e018856fc4936c85661e9b6d5f4c1d6579c29d9bb8130dbdb3d4d58b27fc1828592bc6040000000000000003000000000000"

def prekeyFixture_one_one_time : String :=
  "04132c442be010fbd57e72603328aa76e71fccc1503aae219327d14d9c9993f472111013121514171619181b1a1d1c1f1e010003020504070609080b0a0d0c0f0e00000001c75c780d5973455dbf8e77d6e47be08329ca1ee00026e7e7349b6d27baa52a44152aa5661c433b9126410a9cf3ad49c14db7f703e68a22d373dd9ca14141390f0000000100000002313033323534373639383b3a3d3c3f3e212023222524272629282b2a2d2c2f2e00001280d8da756f367bafc77828bc3514db24d21acbad933d3902c6cd19b60cdbac370aa1c7857d7788bd21eb1014354379918d43f77dd44318846c2e09045716993ad9ea05e0396b41c38e7b002902bbb4eeb433b6d6830fd2cccb49b56fb9a9cf472dd4254566e7aedf7754d8324fa16bcc65c5312550991d930e27b8cd113200e3223063d762812636c1d8561d9bb2591137b76985c16207be6084dd8aabe8b05d9eb6b333456b26057e9c192dfeb72dee2a127e8a3da3272206f2637fcbb342105a7b83b8778777cf99c099cc5105d26846326d17b98b0e95beb087931a4c230d7a5d5da953e371b6472c1bacd9252ad0a4ed168fc993b6f0b5204da2a5215249201ab497464a1f517ca5016864147ce8845617dbbea4a59954da79caf5138e8523d072cde2541cc7343f6be6ad98dc38d6eb21fb752191d0ca98057f2bf6788cd275ef3313459175f9a2b1c3751463914b4620397d61979aca82b1675c39c6037fcbb1924cad68a1c339a82675d33454953d9fd537dd73620b5a19515279c1a99532c2bf0d2ab86e665366c157cce01c28e33dfb025e3798293447aaeb02c9f69436f8ac767e842deef474ad988cc6f15d8c14359ca1adeb937c70fb5fea9a548cb80e017a66ca1351f0cb451bea8092bc1e10994a31612f4a67522fe90d78c1125616ba241a2a5f4309ca34a10575432c654e4fe2b8ed16b6a4858df32122d5faa857c036a33295f9c4bb0c771fd4283d7a27a72f89cb714c60acd586dd836987317fa057459aaa1b058c1461443fba43712e8b1a180aac5142cd1461bb07834bf97bca20526db6f4cb1c044636a36d9944c71b339b3d74a7c9914d1c5b398df39a26096f10263f393458763bcf96396e4bba497ca35566bc77c9d026ce0aa760f83639b80ce0b3c2ff71a6d21a61dab95b855870b37b51f04ccbbeb7609c7b3cccf4313863a155456f4b7c3756d1a0a55c9d9a071832930c9b84bceda31e6000c01f0cd070717975727d1bec6e926761417c8e37594b4c3cb697fa29210b236a624aca09c62551c00039c492b3cb636590b46456275b68a4478f901549be6c2bd9a509e8c748346c62d1146f136822546901619c45d8489c3f06c9bf905836db7e6496598944b6bf1764ab7c053969170bba42c6b403b486600f1973e1a9c912bcaddae3515b103e1ae3773c749a38687040c405f5b5a55612b52fcb882e0c721681620e106d08c52b0436a5cc8cb00ceb8f49470653ca6461579ffc160a2bd50e8080a7bdd8477d69c0f3d41c82bc1bce0c3c55e6aa99e7256642046c3cb14af35ba2db9cf48a1ab4258d53041437e68fcb19523a1ca6c0076bff15be5f9c9236db4258f9c7ffb2cbc09298fdc0bafdf205abe3260025b9ea354d89b66186c790c9b490d540ac11270f7fcca9a4c94657f67fcd52c89234b5cccc49f267c8f3a2a7b7e721ed193bb5d019964c345d65b90475c4c0e22cea098a1cb4380b131d9705094c55b0cbd80f5adc03f13a29bb3587df7479da3aa853694ded5c1a27e492deaa1ce835359b131d73389d623053f6d0b5cc5b0af26b938751a8b7610006e4c39573739fbb15fa51b59e57c9572c1d9af4a499c2a0afe0b33266c740fabc647330591241bd5c06da699d5f008c52c42bd2556d9dea0dc64704893391feb4789fe40187213d7a9a174e0c6731dba97333cb1457b45bc81beca2863e34b2008103df5725331649f5b07192b370df17616512b4fd3654bd6c3f0e41bc167740aaa635b79c80ab5c117e029425e27a7b8237ea9a301941938a9453fba4612004205162a7904c78ea32cfe062717bf54142db418246c6bc8786b8773b43ba912013abb162b9ad50ccc09833da061458ba2f4b04870c01010117505be77ae0f03e47e7c2337083d04c6a3b22a247d370686c55d7f40cf0640b24d44de7379a8a672d55716d9b62959835c5c9a10844a99c12a26f1f841e14e52d9d26a7439770bdc01a494ac3e5a6bbeac67ba52cc64663cc69f5c2475726d89c92f8904a1df988a595795d880906510d70082f94e987c0e794adb2902fbb2eccea1089ec89f7066f2ab9afbcc0aa9f25577fe37355e903ec086c7ab25443e41b590c96e025162047a93fd444e59a2e61517f8a516d426158887a1b983a10c406045a05749ac65eb6e158fcb20877110d866b149de7688e9987d8d97b92f417c676afe0cab248d9ad170476d9678f1ad14a50824d9be0910181096a8224c65c7f40dc24f5065706fc02b4a8c128f111a3523d47c101e67a6980d05d3cb37682902055528f23b451c1aa35c3e902d55a2feeb3a04d0457bd24c6f6a920e14b60c9317630a83dc3a94389141befd81409271533c686e9715227eb52314b41232085cd947383582ce1c4496c74bc552175bc7c469a946fceaa29887c2454830c77bc00478775535b0a6596b1fc78bb12757e3fa17354bcad7910976c7113539505f1e95914c2aefec5ab4e6416831c6661916b4a395a329ba98483be4eb33077d36aaa8491512750b4003249a5be93e723b043ce5ccc94540b8f772ba86c02b865facca4306fc0180bd9526b1e1525bef867d210532a22665c5619c1d4aac8a71666b8c3cb2c2d87b9075b6c971cea069cdc1302f63d1daa406500c9bd4ab88af9401bd49f01a62250e86cbf5c5a6b44bbb7c77b79916016986f14d65cea4a8413f62eaf899ce1e351167b74203b9a2da94f6e22ad9e047dad7352d596a1aa0695ab234061856acf135c94d4c2a7174b1d88be5b7acb5deab2c407aa4dea3684c4bc69e9772d9701b81babbc59c13f62ce622b193177b2a4340fd1b22584882d39d46c6c337aded8bf6c9a6ece281a1c754420f038050727060a211e5230622aaac90825fe4520e1c85ee26c424a128eb4f716dd167c43a80dc1198b1ad3aef728392aaa6807276f0e9051979084ab5c375f189358e3aaf34b6224155f2f670cae9736c8d2c9c2d95c5ac5a572b08cafcacb2cf8be0ba279b61263a86907e68b350a948772a31d37c607690c099ef4020910a0835c1c8be7a9b7ea24b214a3e5304700f4c0246b2f3a11a8403859ba928e63c24f56724fb423101cec3a124951fecc611ce332f8480a3cca8adb90a14e270df6529b9410c0e18a749c220d5c92b6d1f28465c065f42521e52404bfd228503a4c7a3c7f9ebb5bed03cd6909636803415964c8739b8f9594c59bf5282aaa283cb588a47c22c17c7f3f301fadba41d9e1385481c32b0b100e5516f0455e263675c3313bc2d458c8eb3b8e84a15ea2c944bb3d4ec424a29a04306603d5c94580d68802aa5d6a9450caeca2e8a167d7f76d66db42473776d8a1c8b9d1951e251f82e976f8c806467a7456a4c46f7835883caf1f4b7250764bb439aed36b87a04487f1755623a059559989fee8310172a213272908c96bbac44b6690a3bc48ad9c1c4657006e0e4839c027249fb1b94c245aafe4bea6150aa3949321aca9a87106b38c3923c44d1fd63871c4653f0cca033a934ac8bf5a4b68d4057c9ab49907b7cf6ae3a7114402ebfa897c8a79895731828a44d1c42e7e46400472a232977cdfa9c95d992682d2c99d82acc201bc5030113a339c0ab67e8e025cb05b681d052a258a34c897876d25b5c8bbadf6f81b49a4177ba29d41a07147b90568958d6aa7337fc379abe39550f53d4e030726100332919769b9b5b639285e29753d507615a7c3392c15f7954d6450504af98d47c7001d55a44bf1bcfcaac1e552ad1dea9220f39432e88c2fa95484eaccc14498301a2ac785a33b9cae46e3438dbcb2b1e77d188a6d3471680a5c3c473c513a289f75f12825742fd5069054208ac43ccef9726cb8232c72aca31305bddf0c658046048816bb9da93c94e548a2b732dd080f75e3c7e604b4559040d906858512265d78868d72b2b1bb389edb661a0c9d4450775724a0e57037838c3e4abc78f177a85647024b699eda893249e59cfd4215b96807ff4578c8fc69943c8a56734bb1604e9962559f1b6abdf548aa221e45b6ccb31931f6ca62b936a5f4cc1a89ea437eb25633c134bab10f3c983abf880261cace1279ab5aeaaeb99a332eac2300567fa06a740225229e116b1400b8f98789d3a96003fc9808b72d02a34df60117804321db7477a6acce9c381be3d60b4af99d77eabe718207a05813716596f5cb864a7c76ab922bdd713c49a1b4665663e37886aed11f469c2952a1b625794e2468956e0b344214bc816acb47a361b7c32a1c1c76b9da14ed574a963449ada924ba726a542870a82b7d6cf0cb789520fbea2c1fe27c6c3784d5db37b204c7a903a1e98b4cf1b26b3236287637907dbc1be9318b83f4b1b318c5a6af9a8a35f2e9903bd817f2a70551c8b09320a7b50ccca40399da3cb4376113b0075369c69fec0165d6857e7d5a85e84e313033323534373639383b3a3d3c3f3e212023222524272629282b2a2d2c2f2eb6e158fcb20877110d866b149de7688e9987d8d97b92f417c676afe0cab248d9ad170476d9678f1ad14a50824d9be0910181096a8224c65c7f40dc24f5065706fc02b4a8c128f111a3523d47c101e67a6980d05d3cb37682902055528f23b451c1aa35c3e902d55a2feeb3a04d0457bd24c6f6a920e14b60c9317630a83dc3a94389141befd81409271533c686e9715227eb52314b41232085cd947383582ce1c4496c74bc552175bc7c469a946fceaa29887c2454830c77bc00478775535b0a6596b1fc78bb12757e3fa17354bcad7910976c7113539505f1e95914c2aefec5ab4e6416831c6661916b4a395a329ba98483be4eb33077d36aaa8491512750b4003249a5be93e723b043ce5ccc94540b8f772ba86c02b865facca4306fc0180bd9526b1e1525bef867d210532a22665c5619c1d4aac8a71666b8c3cb2c2d87b9075b6c971cea069cdc1302f63d1daa406500c9bd4ab88af9401bd49f01a62250e86cbf5c5a6b44bbb7c77b79916016986f14d65cea4a8413f62eaf899ce1e351167b74203b9a2da94f6e22ad9e047dad7352d596a1aa0695ab234061856acf135c94d4c2a7174b1d88be5b7acb5deab2c407aa4dea3684c4bc69e9772d9701b81babbc59c13f62ce622b193177b2a4340fd1b22584882d39d46c6c337aded8bf6c9a6ece281a1c754420f038050727060a211e5230622aaac90825fe4520e1c85ee26c424a128eb4f716dd167c43a80dc1198b1ad3aef728392aaa6807276f0e9051979084ab5c375f189358e3aaf34b6224155f2f670cae9736c8d2c9c2d95c5ac5a572b08cafcacb2cf8be0ba279b61263a86907e68b350a948772a31d37c607690c099ef4020910a0835c1c8be7a9b7ea24b214a3e5304700f4c0246b2f3a11a8403859ba928e63c24f56724fb423101cec3a124951fecc611ce332f8480a3cca8adb90a14e270df6529b9410c0e18a749c220d5c92b6d1f28465c065f42521e52404bfd228503a4c7a3c7f9ebb5bed03cd6909636803415964c8739b8f9594c59bf5282aaa283cb588a47c22c17c7f3f301fadba41d9e1385481c32b0b100e5516f0455e263675c3313bc2d458c8eb3b8e84a15ea2c944bb3d4ec424a29a04306603d5c94580d68802aa5d6a9450caeca2e8a167d7f76d66db42473776d8a1c8b9d1951e251f82e976f8c806467a7456a4c46f7835883caf1f4b7250764bb439aed36b87a04487f1755623a059559989fee8310172a213272908c96bbac44b6690a3bc48ad9c1c4657006e0e4839c027249fb1b94c245aafe4bea6150aa3949321aca9a87106b38c3923c44d1fd63871c4653f0cca033a934ac8bf5a4b68d4057c9ab49907b7cf6ae3a7114402ebfa897c8a79895731828a44d1c42e7e46400472a232977cdfa9c95d992682d2c99d82acc201bc5030113a339c0ab67e8e025cb05b681d052a258a34c897876d25b5c8bbadf6f81b49a4177ba29d41a07147b90568958d6aa7337fc379abe39550f53d4e030726100332919769b9b5b639285e29753d507615a7c3392c15f7954d6450504af98d47c7001d55a44bf1bcfcaac1e552ad1dea9220f39432e88c2fa95484eaccc14498301a2ac785a33b9cae46e3438dbcb2b1e77d188a6d3471680a5c3c473c513a289f75f12825742fd5069054208ac43ccef9726cb8232c72aca31305bddf0c658046048816bb9da93c94e548a2b732dd080f75e3c7e604b4559040d906858512265d78868d72b2b1bb389edb661a0c9d4450775724a0e57037838c3e4abc78f177a85647024b699eda893249e59cfd4215b96807ff4578c8fc69943c8a56734bb1604e9962559f1b6abdf548aa221e45b6ccb31931f6ca62b936a5f4cc1a89ea437eb25633c134bab10f3c983abf880261cace1279ab5aeaaeb99a332eac2300567fa06a740225229e116b1400b8f98789d3a96003fc9808b72d02a34df60117804321db7477a6acce9c381be3d60b4af99d77eabe718207a05813716596f5cb864a7c76ab922bdd713c49a1b4665663e37886aed11f469c2952a1b625794e2468956e0b344214bc816acb47a361b7c32a1c1c76b9da14ed574a963449ada924ba726a542870a82b7d6cf0cb789520fbea2c1fe27c6c3784d5db37b204c7a903a1e98b4cf1b26b3236287637907dbc1be9318b83f4b1b318c5a6af9a8a35f2e9903bd817f2a70551c8b000000003682b80d5c17b8d147801044154b37c3b4e0c097238430ba1c2e97c6d2074a5b729096939cce74b1ffb3df2e1dad7cbad48742218712f5f2ce93c7aaa7355f505000000010000000400001280d8da756f367bafc77828bc3514db24d21acbad933d3902c6cd19b60cdbac370aa1c7857d7788bd21eb1014354379918d43f77dd44318846c2e09045716993ad9ea05e0396b41c38e7b002902bbb4eeb433b6d6830fd2cccb49b56fb9a9cf472dd4254566e7aedf7754d8324fa16bcc65c5312550991d930e27b8cd113200e3223063d762812636c1d8561d9bb2591137b76985c16207be6084dd8aabe8b05d9eb6b333456b26057e9c192dfeb72dee2a127e8a3da3272206f2637fcbb342105a7b83b8778777cf99c099cc5105d26846326d17b98b0e95beb087931a4c230d7a5d5da953e371b6472c1bacd9252ad0a4ed168fc993b6f0b5204da2a5215249201ab497464a1f517ca5016864147ce8845617dbbea4a59954da79caf5138e8523d072cde2541cc7343f6be6ad98dc38d6eb21fb752191d0ca98057f2bf6788cd275ef3313459175f9a2b1c3751463914b4620397d61979aca82b1675c39c6037fcbb1924cad68a1c339a82675d33454953d9fd537dd73620b5a19515279c1a99532c2bf0d2ab86e665366c157cce01c28e33dfb025e3798293447aaeb02c9f69436f8ac767e842deef474ad988cc6f15d8c14359ca1adeb937c70fb5fea9a548cb80e017a66ca1351f0cb451bea8092bc1e10994a31612f4a67522fe90d78c1125616ba241a2a5f4309ca34a10575432c654e4fe2b8ed16b6a4858df32122d5faa857c036a33295f9c4bb0c771fd4283d7a27a72f89cb714c60acd586dd836987317fa057459aaa1b058c1461443fba43712e8b1a180aac5142cd1461bb07834bf97bca20526db6f4cb1c044636a36d9944c71b339b3d74a7c9914d1c5b398df39a26096f10263f393458763bcf96396e4bba497ca35566bc77c9d026ce0aa760f83639b80ce0b3c2ff71a6d21a61dab95b855870b37b51f04ccbbeb7609c7b3cccf4313863a155456f4b7c3756d1a0a55c9d9a071832930c9b84bceda31e6000c01f0cd070717975727d1bec6e926761417c8e37594b4c3cb697fa29210b236a624aca09c62551c00039c492b3cb636590b46456275b68a4478f901549be6c2bd9a509e8c748346c62d1146f136822546901619c45d8489c3f06c9bf905836db7e6496598944b6bf1764ab7c053969170bba42c6b403b486600f1973e1a9c912bcaddae3515b103e1ae3773c749a38687040c405f5b5a55612b52fcb882e0c721681620e106d08c52b0436a5cc8cb00ceb8f49470653ca6461579ffc160a2bd50e8080a7bdd8477d69c0f3d41c82bc1bce0c3c55e6aa99e7256642046c3cb14af35ba2db9cf48a1ab4258d53041437e68fcb19523a1ca6c0076bff15be5f9c9236db4258f9c7ffb2cbc09298fdc0bafdf205abe3260025b9ea354d89b66186c790c9b490d540ac11270f7fcca9a4c94657f67fcd52c89234b5cccc49f267c8f3a2a7b7e721ed193bb5d019964c345d65b90475c4c0e22cea098a1cb4380b131d9705094c55b0cbd80f5adc03f13a29bb3587df7479da3aa853694ded5c1a27e492deaa1ce835359b131d73389d623053f6d0b5cc5b0af26b938751a8b7610006e4c39573739fbb15fa51b59e57c9572c1d9af4a499c2a0afe0b33266c740fabc647330591241bd5c06da699d5f008c52c42bd2556d9dea0dc64704893391feb4789fe40187213d7a9a174e0c6731dba97333cb1457b45bc81beca2863e34b2008103df5725331649f5b07192b370df17616512b4fd3654bd6c3f0e41bc167740aaa635b79c80ab5c117e029425e27a7b8237ea9a301941938a9453fba4612004205162a7904c78ea32cfe062717bf54142db418246c6bc8786b8773b43ba912013abb162b9ad50ccc09833da061458ba2f4b04870c01010117505be77ae0f03e47e7c2337083d04c6a3b22a247d370686c55d7f40cf0640b24d44de7379a8a672d55716d9b62959835c5c9a10844a99c12a26f1f841e14e52d9d26a7439770bdc01a494ac3e5a6bbeac67ba52cc64663cc69f5c2475726d89c92f8904a1df988a595795d880906510d70082f94e987c0e794adb2902fbb2eccea1089ec89f7066f2ab9afbcc0aa9f25577fe37355e903ec086c7ab25443e41b590c96e025162047a93fd444e59a2e61517f8a516d426158887a1b983a10c406045a05749ac65eb6e158fcb20877110d866b149de7688e9987d8d97b92f417c676afe0cab248d9ad170476d9678f1ad14a50824d9be0910181096a8224c65c7f40dc24f5065706fc02b4a8c128f111a3523d47c101e67a6980d05d3cb37682902055528f23b451c1aa35c3e902d55a2feeb3a04d0457bd24c6f6a920e14b60c9317630a83dc3a94389141befd81409271533c686e9715227eb52314b41232085cd947383582ce1c4496c74bc552175bc7c469a946fceaa29887c2454830c77bc00478775535b0a6596b1fc78bb12757e3fa17354bcad7910976c7113539505f1e95914c2aefec5ab4e6416831c6661916b4a395a329ba98483be4eb33077d36aaa8491512750b4003249a5be93e723b043ce5ccc94540b8f772ba86c02b865facca4306fc0180bd9526b1e1525bef867d210532a22665c5619c1d4aac8a71666b8c3cb2c2d87b9075b6c971cea069cdc1302f63d1daa406500c9bd4ab88af9401bd49f01a62250e86cbf5c5a6b44bbb7c77b79916016986f14d65cea4a8413f62eaf899ce1e351167b74203b9a2da94f6e22ad9e047dad7352d596a1aa0695ab234061856acf135c94d4c2a7174b1d88be5b7acb5deab2c407aa4dea3684c4bc69e9772d9701b81babbc59c13f62ce622b193177b2a4340fd1b22584882d39d46c6c337aded8bf6c9a6ece281a1c754420f038050727060a211e5230622aaac90825fe4520e1c85ee26c424a128eb4f716dd167c43a80dc1198b1ad3aef728392aaa6807276f0e9051979084ab5c375f189358e3aaf34b6224155f2f670cae9736c8d2c9c2d95c5ac5a572b08cafcacb2cf8be0ba279b61263a86907e68b350a948772a31d37c607690c099ef4020910a0835c1c8be7a9b7ea24b214a3e5304700f4c0246b2f3a11a8403859ba928e63c24f56724fb423101cec3a124951fecc611ce332f8480a3cca8adb90a14e270df6529b9410c0e18a749c220d5c92b6d1f28465c065f42521e52404bfd228503a4c7a3c7f9ebb5bed03cd6909636803415964c8739b8f9594c59bf5282aaa283cb588a47c22c17c7f3f301fadba41d9e1385481c32b0b100e5516f0455e263675c3313bc2d458c8eb3b8e84a15ea2c944bb3d4ec424a29a04306603d5c94580d68802aa5d6a9450caeca2e8a167d7f76d66db42473776d8a1c8b9d1951e251f82e976f8c806467a7456a4c46f7835883caf1f4b7250764bb439aed36b87a04487f1755623a059559989fee8310172a213272908c96bbac44b6690a3bc48ad9c1c4657006e0e4839c027249fb1b94c245aafe4bea6150aa3949321aca9a87106b38c3923c44d1fd63871c4653f0cca033a934ac8bf5a4b68d4057c9ab49907b7cf6ae3a7114402ebfa897c8a79895731828a44d1c42e7e46400472a232977cdfa9c95d992682d2c99d82acc201bc5030113a339c0ab67e8e025cb05b681d052a258a34c897876d25b5c8bbadf6f81b49a4177ba29d41a07147b90568958d6aa7337fc379abe39550f53d4e030726100332919769b9b5b639285e29753d507615a7c3392c15f7954d6450504af98d47c7001d55a44bf1bcfcaac1e552ad1dea9220f39432e88c2fa95484eaccc14498301a2ac785a33b9cae46e3438dbcb2b1e77d188a6d3471680a5c3c473c513a289f75f12825742fd5069054208ac43ccef9726cb8232c72aca31305bddf0c658046048816bb9da93c94e548a2b732dd080f75e3c7e604b4559040d906858512265d78868d72b2b1bb389edb661a0c9d4450775724a0e57037838c3e4abc78f177a85647024b699eda893249e59cfd4215b96807ff4578c8fc69943c8a56734bb1604e9962559f1b6abdf548aa221e45b6ccb31931f6ca62b936a5f4cc1a89ea437eb25633c134bab10f3c983abf880261cace1279ab5aeaaeb99a332eac2300567fa06a740225229e116b1400b8f98789d3a96003fc9808b72d02a34df60117804321db7477a6acce9c381be3d60b4af99d77eabe718207a05813716596f5cb864a7c76ab922bdd713c49a1b4665663e37886aed11f469c2952a1b625794e2468956e0b344214bc816acb47a361b7c32a1c1c76b9da14ed574a963449ada924ba726a542870a82b7d6cf0cb789520fbea2c1fe27c6c3784d5db37b204c7a903a1e98b4cf1b26b3236287637907dbc1be9318b83f4b1b318c5a6af9a8a35f2e9903bd817f2a70551c8b09320a7b50ccca40399da3cb4376113b0075369c69fec0165d6857e7d5a85e84e313033323534373639383b3a3d3c3f3e212023222524272629282b2a2d2c2f2eb6e158fcb20877110d866b149de7688e9987d8d97b92f417c676afe0cab248d9ad170476d9678f1ad14a50824d9be0910181096a8224c65c7f40dc24f5065706fc02b4a8c128f111a3523d47c101e67a6980d05d3cb37682902055528f23b451c1aa35c3e902d55a2feeb3a04d0457bd24c6f6a920e14b60c9317630a83dc3a94389141befd81409271533c686e9715227eb52314b41232085cd947383582ce1c4496c74bc552175bc7c469a946fceaa29887c2454830c77bc00478775535b0a6596b1fc78bb12757e3fa17354bcad7910976c7113539505f1e95914c2aefec5ab4e6416831c6661916b4a395a329ba98483be4eb33077d36aaa8491512750b4003249a5be93e723b043ce5ccc94540b8f772ba86c02b865facca4306fc0180bd9526b1e1525bef867d210532a22665c5619c1d4aac8a71666b8c3cb2c2d87b9075b6c971cea069cdc1302f63d1daa406500c9bd4ab88af9401bd49f01a62250e86cbf5c5a6b44bbb7c77b79916016986f14d65cea4a8413f62eaf899ce1e351167b74203b9a2da94f6e22ad9e047dad7352d596a1aa0695ab234061856acf135c94d4c2a7174b1d88be5b7acb5deab2c407aa4dea3684c4bc69e9772d9701b81babbc59c13f62ce622b193177b2a4340fd1b22584882d39d46c6c337aded8bf6c9a6ece281a1c754420f038050727060a211e5230622aaac90825fe4520e1c85ee26c424a128eb4f716dd167c43a80dc1198b1ad3aef728392aaa6807276f0e9051979084ab5c375f189358e3aaf34b6224155f2f670cae9736c8d2c9c2d95c5ac5a572b08cafcacb2cf8be0ba279b61263a86907e68b350a948772a31d37c607690c099ef4020910a0835c1c8be7a9b7ea24b214a3e5304700f4c0246b2f3a11a8403859ba928e63c24f56724fb423101cec3a124951fecc611ce332f8480a3cca8adb90a14e270df6529b9410c0e18a749c220d5c92b6d1f28465c065f42521e52404bfd228503a4c7a3c7f9ebb5bed03cd6909636803415964c8739b8f9594c59bf5282aaa283cb588a47c22c17c7f3f301fadba41d9e1385481c32b0b100e5516f0455e263675c3313bc2d458c8eb3b8e84a15ea2c944bb3d4ec424a29a04306603d5c94580d68802aa5d6a9450caeca2e8a167d7f76d66db42473776d8a1c8b9d1951e251f82e976f8c806467a7456a4c46f7835883caf1f4b7250764bb439aed36b87a04487f1755623a059559989fee8310172a213272908c96bbac44b6690a3bc48ad9c1c4657006e0e4839c027249fb1b94c245aafe4bea6150aa3949321aca9a87106b38c3923c44d1fd63871c4653f0cca033a934ac8bf5a4b68d4057c9ab49907b7cf6ae3a7114402ebfa897c8a79895731828a44d1c42e7e46400472a232977cdfa9c95d992682d2c99d82acc201bc5030113a339c0ab67e8e025cb05b681d052a258a34c897876d25b5c8bbadf6f81b49a4177ba29d41a07147b90568958d6aa7337fc379abe39550f53d4e030726100332919769b9b5b639285e29753d507615a7c3392c15f7954d6450504af98d47c7001d55a44bf1bcfcaac1e552ad1dea9220f39432e88c2fa95484eaccc14498301a2ac785a33b9cae46e3438dbcb2b1e77d188a6d3471680a5c3c473c513a289f75f12825742fd5069054208ac43ccef9726cb8232c72aca31305bddf0c658046048816bb9da93c94e548a2b732dd080f75e3c7e604b4559040d906858512265d78868d72b2b1bb389edb661a0c9d4450775724a0e57037838c3e4abc78f177a85647024b699eda893249e59cfd4215b96807ff4578c8fc69943c8a56734bb1604e9962559f1b6abdf548aa221e45b6ccb31931f6ca62b936a5f4cc1a89ea437eb25633c134bab10f3c983abf880261cace1279ab5aeaaeb99a332eac2300567fa06a740225229e116b1400b8f98789d3a96003fc9808b72d02a34df60117804321db7477a6acce9c381be3d60b4af99d77eabe718207a05813716596f5cb864a7c76ab922bdd713c49a1b4665663e37886aed11f469c2952a1b625794e2468956e0b344214bc816acb47a361b7c32a1c1c76b9da14ed574a963449ada924ba726a542870a82b7d6cf0cb789520fbea2c1fe27c6c3784d5db37b204c7a903a1e98b4cf1b26b3236287637907dbc1be9318b83f4b1b318c5a6af9a8a35f2e9903bd817f2a70551c8b0682b80d5c17b8d147801044154b37c3b4e0c097238430ba1c2e97c6d2074a5b729096939cce74b1ffb3df2e1dad7cbad48742218712f5f2ce93c7aaa7355f50500000005000000000000"

def prekeyFixture_retired_signed : String :=
  "04132c442be010fbd57e72603328aa76e71fccc1503aae219327d14d9c9993f472313033323534373639383b3a3d3c3f3e212023222524272629282b2a2d2c2f2e000000036533ab90fc95c9951439f2f6390a190019169d23fd3d273642944104598f5a67846e8995340a250fba2c057d430a08f3e9fc489a16a3bd567ec5d705412808020000000000001280d6e98d2587a2468092d3239d6565bee644927af38f2d48ce66f905b27338453b5095b50554da8c85e13df80232f7d33d07e69467d7bc0fa6c785a22d29f324d4673ddfc7a5319289eb132cc86a6d11e35b23e37cefb832a3b843b57c3b9ae626743a061d5a7d44672817919ded62a6e877ad356a5ff447ba9a524bf46cb72b42af9303a2304a073e1648c794ae5e297177e76709d87050a160c1c818ed9a85ab1112f5b91b3a78269a82935c543a64973ff4031609cc62e03734bd178852f148ab40981507cfaa6173b0765a59a309f43b5106a58ec562458e36c178b98dd239653f35958c22b79d26b5e23610daa03d70fa4b44b46fe639a1ae2c384b730b76652da5c2af3812b061e5c018ab2544e16cbb639a17c180ae3c701f87856f3ba8dc4613258128a21706fd444589481a9a4bc6f3da7d70838cb909cb76062c69161fb7c965c99442e1a48b50a440df72c29ef784ff69b5f275773deb6b7a1b102ef77e90d3c694ab7ccbd2838392bc0b008fb71070b62110b607baccda70b3b8a78c2a8feefb70f4c31a2dc99509934d07718cb82c3c14e5c1ab21a5d3875b84014335633b3edb9b54bcae8f2b9dbedc3db9c5bfb3441e97e69f85948363b2a87cf62521f484d55450a49b08b5fb8094fa7cb219976a726c785a38deb77be964b897045a9e21c129b415f3962bb5635254737cc15722a0e007911586c520a848493644c253e918269dbb7b5ab857428aab9ab2897fb651f9e70c069b0ddbb68132d687406a97c16069d64b6021b8252dea05c5d16ba08933fa518136925b93c72aca27658fc7bb531ba927d829839ac4b5891d7d46143cd1064daa16f08a3ad37ac6d0a58a742308d6eb041107883927951f804436e445be7072bfbb4237e0153aba3b349499f62a63f268c52fa7717d46042dd27458606c4199351cd0787cb9c2cfd8c3aa03a97a405451b9cd96a1a76f1045ef696523ecc5df7875a0391b83b9210ec66a44d895d2f535cc019ab3fc95ed00621a00c8e5a182532954b53b6fb2eb40b638a0665bb1fb27365df71f83359151f95c17a12146205a0d78bfe581b4de8793bcb622f30906ea05a2be3219ec35206a7c247d20c4a64a3515c7073cabc9c6354dc0253261a80d6082573879a2d267b8d7a00c21e8583d9acfb20b1504d63b0a5324ddcc7a9dc19fc41126b1328f4b886e67b0876beb48f6a29ad9d86e12863762d3a7ba34b23eeca430052627909b66166523e18d41836030d3bea99741d4d38bdbb2bbba42c6c484c8b9473e01c28ac935591bc25163b15988485f3003bf6f420085954b5f0508f33b0d1b7513c286c99507c8ab03613f715a2d58a65abcabd811a75d8338061b1fadcb39c60883be20c9bef45b78a97711b26b3a56534dd4630edbaee20ca7cbc07726109698896a786b3f730a181cca3473071ae950189f69c144cb52091c32a9c1bb3d8bc3c2fb226148a650d85a01a074b4da3da90ac961735de26aaca372b40e4650bf431f07b04c4b031c7cd7183f26bd622abe1fc1a68c6504a0b26eb4356514983375790d2d719229119aff5b00da6b526a38b55ef2023b61c3b4c5ba2b38c3338988d23a9575a02c40806864ca99166906e1b522c6a862f5628189c9c77149ccf577704079aed85b0ee6376736b3ac198012b812372ed6b52e84b989ba5ed44a353a222b61a8622e7946835072ecd14cc82267ae0a2b62052d1531254033893d171a315a0067436ff791092f0a49f05c0b3366b6a27b4be3c3b238a31aa9a849b6467df65c9648b09cd9c9187f470a08e61c858483b59187b65a907bec017647323a0c21f013615798b111daa1df0a5112b61ff2a27fcd15369bc6ab567334294976a87ba914a541bc52bd9ebc262a3b878f56cc44b50c87d47bd053772d5b35b9d7b713327e1708632a60742dc8cc703b1850db4ed3e905e86ba1d645475ab4a210f59f7224bd0b950f497c54f8a87512250f33f832d9047208631ee4571fd8826340b97db9f4ade08850f9bc6562f59510db6cb76533c32c70f083b702e5435788a4acbb48458985c8e7a542ec3c0443637f02c623eccd7d201d349219a6646e26a12a7cf76877aac31102b8095154fc4231c438358058c49ddcbe60b27fd641cef910998568cafb1781b78909df6b44e638b526f4a26cb6736c3b2413c538047227421919ac05c07ea6741882726a3a5bd6a49c68b12faeb32621f79a493b8a47c7059c1b7225215bf58aa6d9d6a070f067dd89aee0d55d69046a4bf629e1767c0e0c12e8f0336a358571430fd9facfdd63a9f8278ebad05a4785549d3c82d6b05b9bc0519fd6c9427a88f0539e82d5c372155bc4e2945830634f53525fa6a11f70572d07478c6a852c57565aa1b08b4c727a2a8f0ea75a4c646de3e7506c3742a4571a28328258c077f0a8bffc7310dcd0b1c142ab834b34a4a0acc520a5ed7a0d3d2bc0ffe0b4bac898e3178ec13aae04f6b6451a05a58b35a32bbf7cba4e42ac483c9825ba3aa5dd1ba18779302c70b5e473bb9e3b153eb855706b9c0aab0f81e09be60027c8bcbce3dc94a4650dee9209f5296d783c0194e61edfaa9aa1524af6e2b106c03aa8b0943ff8a1eb37b600712b9c5a6a268857d6ac7aa25567281b42b9154b0cb4a9ff630aeba664d4f49d30f10bdad5a0b189356fc5272ba5c245d8c25b7456b4e4955bb53b4214509f4618975c2c104429f64706fa0ad0aa710077c7c080d782b1594a29713ba44a44a680bb2dab3487086ee279c58cbc53390923536a97068b40ed7949c0769b2026bd1e7c74c94b4f726474f49786fef27de65095b43c80b69789528a7c09e416a37963d3052756035b0f97ba03dc0b14ba33a38280551b6051c4a6d7b4168f29af3b454ac2fa304f517d04ea1d8cacab99c6b33e26966f0b66b78b684278b4a29a69d9547076c873ad03752b869e6d9c26c2955c43099d573268de9372f2449f4d82c5ef211c79b6732d18bbf1539b86b54f91495c423202d193147d9899625b2590e4a9d81c0035c82de9a133d7d3925a2520176404c2e4169b0b6298780725e5cbfadac0423c38ea674ad2b0565d851ac375aaa027578b9c036a757e4555a8ff725d58462aa7b686bb090983979398c4c2f5b1868e5b667484a4c5e175cb8c47514a282559ab92f900af4716c42bccefe00a5428752936155d0509ffb06c7bb528802ca421b881bb309a7b5100cda0a78502c0616abb0bec44f27759b08b1be62897cd802c5b776794f1a5cf5b333156caed698674d093a65cc7337b24bd146394a87d7cf9185f50c3cc854f4a43323f8a9bd89623ce2c247b8b8ca0e96926495bf566c64814befc44618c389873dc08e4cb744d16b72b7b6da9a5811cfb676de9adfd8660b07390255c25560623b89b4c15db0a67d0703f53340c73374b71a258758adbb6169aa96ea21b99113c9db498b77f9c8af45a675c29abdba3cdf96587c262345521ca346508bd2c7f2eda67b4b24c98d154023a1cae68c79834026a5815ea9795ab9004c175ade999c87f82166332c314270db5f6baa82c07b5667e29fa58d87aa7c63bc5e42637389431a6d84271f514bed87f43d07e9a009490f485c847acd9c39d8a8c24fbb131fbe76961127755a11a521c6ef0a85de14a692db5c4ac8c19a6b0302b49a33d21440777b269669bcfa09b88731b74a7936982c2023b1b219c909a6c6f532b6c2549c2dde2bcdf7932712b30658b8d9a35047fe548bff54cd35011987039de22cce9dc555c5c8dd499abfd0a19eacb5241f525ea552ea5a23ac4aaaff4945ceda2741c0142edd90d0b8515f10a757dd48fba1c438752cb7b277655d39a941a820563bc3ba872f1b64b8de96257679eed24bca8d012468715efe5a4e8e10e14b66340d97b487a2f3bbc16b7fb31e7a4cd5bd5c80ad68fd2e65dc360cf0820aa5877802705378210055b6b47e0e677f217b425078c2eb573b5b67bfbd30ea931a29480b163331d6fa824af17138bd15e0182a4c1b37644496ac50c9f567b316ee225ee795f1ff3673148cbbd68a2f8986ef6e4bba637715d50cc099acbded6c77785c9ddd920d08359b1783a5496cbf1178bc458a0212b2b4e109c91f93c177307f7d69badf43fef72c271793b21d19886f9575a01b6f3a5ae2ca50e92fc21b5b8255c032119e412016bc0a87a0da3b89be1722ff9aaab48c03345143d05f2a9bd535688f558d0379f4eb50562488c4e368902821ced7152fdb89a1982965e1933fcdaaea42828174764b3d080a6770168147f445cbbd0c51feb715870a8712eac273bd1600eb310c8e1974801bae51943663c8ad591cb7c4ad8c6fdbef06db4c722f1cc2e01f28cba32be19907cb8d6dcf7580f5eef0e05042a5e092c354a7861642815183a17c9d8a307e7953eb1ead629f8cc111013121514171619181b1a1d1c1f1e010003020504070609080b0a0d0c0f0ee638b526f4a26cb6736c3b2413c538047227421919ac05c07ea6741882726a3a5bd6a49c68b12faeb32621f79a493b8a47c7059c1b7225215bf58aa6d9d6a070f067dd89aee0d55d69046a4bf629e1767c0e0c12e8f0336a358571430fd9facfdd63a9f8278ebad05a4785549d3c82d6b05b9bc0519fd6c9427a88f0539e82d5c372155bc4e2945830634f53525fa6a11f70572d07478c6a852c57565aa1b08b4c727a2a8f0ea75a4c646de3e7506c3742a4571a28328258c077f0a8bffc7310dcd0b1c142ab834b34a4a0acc520a5ed7a0d3d2bc0ffe0b4bac898e3178ec13aae04f6b6451a05a58b35a32bbf7cba4e42ac483c9825ba3aa5dd1ba18779302c70b5e473bb9e3b153eb855706b9c0aab0f81e09be60027c8bcbce3dc94a4650dee9209f5296d783c0194e61edfaa9aa1524af6e2b106c03aa8b0943ff8a1eb37b600712b9c5a6a268857d6ac7aa25567281b42b9154b0cb4a9ff630aeba664d4f49d30f10bdad5a0b189356fc5272ba5c245d8c25b7456b4e4955bb53b4214509f4618975c2c104429f64706fa0ad0aa710077c7c080d782b1594a29713ba44a44a680bb2dab3487086ee279c58cbc53390923536a97068b40ed7949c0769b2026bd1e7c74c94b4f726474f49786fef27de65095b43c80b69789528a7c09e416a37963d3052756035b0f97ba03dc0b14ba33a38280551b6051c4a6d7b4168f29af3b454ac2fa304f517d04ea1d8cacab99c6b33e26966f0b66b78b684278b4a29a69d9547076c873ad03752b869e6d9c26c2955c43099d573268de9372f2449f4d82c5ef211c79b6732d18bbf1539b86b54f91495c423202d193147d9899625b2590e4a9d81c0035c82de9a133d7d3925a2520176404c2e4169b0b6298780725e5cbfadac0423c38ea674ad2b0565d851ac375aaa027578b9c036a757e4555a8ff725d58462aa7b686bb090983979398c4c2f5b1868e5b667484a4c5e175cb8c47514a282559ab92f900af4716c42bccefe00a5428752936155d0509ffb06c7bb528802ca421b881bb309a7b5100cda0a78502c0616abb0bec44f27759b08b1be62897cd802c5b776794f1a5cf5b333156caed698674d093a65cc7337b24bd146394a87d7cf9185f50c3cc854f4a43323f8a9bd89623ce2c247b8b8ca0e96926495bf566c64814befc44618c389873dc08e4cb744d16b72b7b6da9a5811cfb676de9adfd8660b07390255c25560623b89b4c15db0a67d0703f53340c73374b71a258758adbb6169aa96ea21b99113c9db498b77f9c8af45a675c29abdba3cdf96587c262345521ca346508bd2c7f2eda67b4b24c98d154023a1cae68c79834026a5815ea9795ab9004c175ade999c87f82166332c314270db5f6baa82c07b5667e29fa58d87aa7c63bc5e42637389431a6d84271f514bed87f43d07e9a009490f485c847acd9c39d8a8c24fbb131fbe76961127755a11a521c6ef0a85de14a692db5c4ac8c19a6b0302b49a33d21440777b269669bcfa09b88731b74a7936982c2023b1b219c909a6c6f532b6c2549c2dde2bcdf7932712b30658b8d9a35047fe548bff54cd35011987039de22cce9dc555c5c8dd499abfd0a19eacb5241f525ea552ea5a23ac4aaaff4945ceda2741c0142edd90d0b8515f10a757dd48fba1c438752cb7b277655d39a941a820563bc3ba872f1b64b8de96257679eed24bca8d012468715efe5a4e8e10e14b66340d97b487a2f3bbc16b7fb31e7a4cd5bd5c80ad68fd2e65dc360cf0820aa5877802705378210055b6b47e0e677f217b425078c2eb573b5b67bfbd30ea931a29480b163331d6fa824af17138bd15e0182a4c1b37644496ac50c9f567b316ee225ee795f1ff3673148cbbd68a2f8986ef6e4bba637715d50cc099acbded6c77785c9ddd920d08359b1783a5496cbf1178bc458a0212b2b4e109c91f93c177307f7d69badf43fef72c271793b21d19886f9575a01b6f3a5ae2ca50e92fc21b5b8255c032119e412016bc0a87a0da3b89be1722ff9aaab48c03345143d05f2a9bd535688f558d0379f4eb50562488c4e368902821ced7152fdb89a1982965e1933fcdaaea42828174764b3d080a6770168147f445cbbd0c51feb715870a8712eac273bd1600eb310c8e1974801bae51943663c8ad591cb7c4ad8c6fdbef06db4c722f1cc2e01f28cba32be19907cb8d6dcf7580f00000002853e7369ad89000e3f6b94f43d5641147d27ab9ebc8bea0e2e53d163e018856fc4936c85661e9b6d5f4c1d6579c29d9bb8130dbdb3d4d58b27fc1828592bc60400000000000000040000000001111013121514171619181b1a1d1c1f1e010003020504070609080b0a0d0c0f0e00000001c75c780d5973455dbf8e77d6e47be08329ca1ee00026e7e7349b6d27baa52a44152aa5661c433b9126410a9cf3ad49c14db7f703e68a22d373dd9ca14141390f00"

def prekeyStoreFields (st : Model.PersistedState.PrekeyStoreState.Store) :
    List (String × List UInt8) :=
  [("identity_public", st.identityPublic),
   ("signed_prekey_secret", st.signedPrekeySecret),
   ("signed_prekey_id", Model.Erasure.be 4 st.signedPrekeyId),
   ("signed_prekey_sig", st.signedPrekeySig),
   ("kem_id", Model.Erasure.be 4 st.kemId),
   ("kem_sig", st.kemSig),
   ("next_id", Model.Erasure.be 4 st.nextId),
   -- Counts rather than contents: an ML-KEM key pair is 4,736 bytes, and
   -- repeating it in a field would double the file for nothing a reader
   -- cannot get from the bytes it already has.
   ("one_time_count", Model.Erasure.be 4 st.oneTime.length),
   ("kem_one_time_count", Model.Erasure.be 4 st.kemOneTime.length),
   ("seen_count", Model.Erasure.be 4 st.seen.length),
   ("previous_signed_present", [if st.previousSigned.isSome then 1 else 0]),
   ("previous_kem_present", [if st.previousKem.isSome then 1 else 0])]

@[never_extract]
def prekeyStored (id comment : String) (bs : List UInt8)
    (expect : Option Model.PersistedState.Refusal) : Except String String :=
  storedStateVector Model.PersistedState.PrekeyStoreState.ofBytes prekeyStoreFields
    id comment bs expect

/-- Read a fixture, or fail loudly: a fixture the model's own reader refuses is
    a disagreement with `tacenta-core`, not a vector. -/
def prekeyBase (hex : String) : Except String Model.PersistedState.PrekeyStoreState.Store :=
  match Model.PersistedState.PrekeyStoreState.ofBytes (ofHex hex) with
  | .ok st => .ok st
  | .error _ => .error "genvectors: the model refuses a prekey-store fixture tacenta-core accepts"

@[never_extract]
def prekeyStoreStateFile (_ : Unit) : Except String String := do
  let base ← prekeyBase prekeyFixture_no_one_time
  let mutate (f : Model.PersistedState.PrekeyStoreState.Store →
      Model.PersistedState.PrekeyStoreState.Store) : List UInt8 :=
    Model.PersistedState.PrekeyStoreState.toBytes (f base)
  let baseBytes := ofHex prekeyFixture_no_one_time
  let accepted ← [
    prekeyStored "current-version"
      "a store tacenta-core wrote: the current version, one KEM prekey, no one-time prekeys, nothing retired"
      baseBytes none,
    prekeyStored "one-time-kem-prekey"
      "a store with a one-time curve prekey and a one-time KEM prekey, so the one-time sub-formats carry data"
      (ofHex prekeyFixture_one_one_time) none,
    prekeyStored "retired-signed-prekey"
      "a store after a signed-prekey rotation, so the retired fields are present"
      (ofHex prekeyFixture_retired_signed) none
  ].mapM id
  let refusals := [
    -- The version byte.
    prekeyStored "version-unknown" "a first byte naming no version this reader reads"
      (0x05 :: baseBytes.drop 1) (some .wrongVersion),
    prekeyStored "version-zero" "a first byte of zero"
      (0x00 :: baseBytes.drop 1) (some .wrongVersion),
    -- The buffer.
    prekeyStored "empty" "no bytes at all" [] (some .shortOrMalformed),
    prekeyStored "truncated" "the last byte removed"
      (baseBytes.take (baseBytes.length - 1)) (some .shortOrMalformed),
    prekeyStored "trailing-byte" "a byte after the last field"
      (baseBytes ++ [0x00]) (some .shortOrMalformed),
    -- The four semantic rules.
    prekeyStored "identity-public-not-canonical"
      "identity_public spelled above the curve order, which no operation produces and a peer's bundle decoder refuses"
      (mutate (fun s => { s with identityPublic := List.replicate 32 0xff }))
      (some .shortOrMalformed),
    prekeyStored "identifier-zero"
      "the signed prekey numbered zero, the absent-identifier sentinel an initial message reads as none"
      (mutate (fun s => { s with signedPrekeyId := 0 })) (some .shortOrMalformed),
    prekeyStored "identifier-at-next-id"
      "an identifier equal to next_id: the counter wound back, so the next key handed out collides with a live one"
      (mutate (fun s => { s with signedPrekeyId := s.nextId })) (some .shortOrMalformed),
    prekeyStored "identifier-above-next-id"
      "an identifier past next_id"
      (mutate (fun s => { s with signedPrekeyId := s.nextId + 5 })) (some .shortOrMalformed),
    prekeyStored "identifiers-repeated"
      "the signed prekey and the KEM prekey under one identifier, which one counter numbering both cannot produce"
      (mutate (fun s => { s with kemId := s.signedPrekeyId })) (some .shortOrMalformed),
    -- The replay record SEC-1 bypassed.
    prekeyStored "record-entry-under-an-unknown-key"
      "a replay-record entry tagged with an identifier that is neither last-resort key: it has no budget, not an untouched one"
      (mutate (fun s => { s with seen := [(s.nextId + 1, List.replicate 32 0x01)] }))
      (some .shortOrMalformed),
    prekeyStored "record-fingerprint-repeated"
      "one fingerprint twice under the live key, which the responder refuses before it could be recorded"
      (mutate (fun s => { s with
        seen := [(s.kemId, List.replicate 32 0x01), (s.kemId, List.replicate 32 0x01)] }))
      (some .shortOrMalformed),
    prekeyStored "record-over-budget-for-one-key"
      "MAX_LAST_RESORT_SEEN + 1 entries under the live key: the bound is per key, and a file holding more is refused however plausible its count"
      (mutate (fun s => { s with
        seen := (List.range (Model.PersistedState.PrekeyStoreState.maxLastResortSeen + 1)).map
          (fun i => (s.kemId, Model.Erasure.be 32 i)) }))
      (some .shortOrMalformed),
    -- The accepting side of the same boundary. Its signatures are the
    -- fixture's and still verify, because the record is not what they cover,
    -- so this is a store both readers accept rather than a refusal.
    prekeyStored "record-at-budget"
      "exactly MAX_LAST_RESORT_SEEN entries under the live key, each fingerprint distinct: the bound is inclusive, and this is the largest record one key may hold"
      (mutate (fun s => { s with
        seen := (List.range Model.PersistedState.PrekeyStoreState.maxLastResortSeen).map
          (fun i => (s.kemId, Model.Erasure.be 32 i)) }))
      none
  ].mapM id
  let refusals ← refusals
  pure ("{\n" ++
    "  \"schema_version\": 1,\n" ++
    "  \"algorithm\": \"prekey-store-state\",\n" ++
    "  \"source\": \"generated by tacenta-model Vectors.lean (lake exe genvectors prekey-store-state), from Model.PersistedState.PrekeyStoreState; the three accepted vectors carry bytes tacenta-core produced under a fixed byte source, because the model has no signatures and cannot make a store whose signatures verify, and every refusal is one field of that fixture changed so the rule under test is the only thing wrong; the generator writes no vector whose result the model does not give\",\n" ++
    "  \"vectors\": [\n" ++
    String.intercalate ",\n" (accepted ++ refusals) ++
    "\n  ]\n}")

/-! #### The ML-KEM Braid's state

The tag, the epoch and authenticator every live state carries, and the tag's
own length-prefixed fields. `key_pair` and `encaps` are the two values whose
layout the page delegates (ADR-0006, point 5): the model checks their lengths
and nothing inside them, so no accepted vector here carries a `key_pair` --
tags 1 to 4 appear only in refusals, and the README and the manifest say
so. -/

open Model.PersistedState.BraidState (headerLen ekVectorLen ct1Len ct2Len macLen
  keyPairLen encapsLen)

/-- A value of `n` bytes for a coder to stream. -/
def braidValue (n : Nat) : List UInt8 := ramp n 7 3

/-- An encoder over an `n`-byte value, after `issued` codewords. -/
def braidEncoder (n issued : Nat) : List UInt8 :=
  ((Model.Erasure.Encoder.new (braidValue n)).issue issued).toBytes

/-- A decoder for an `n`-byte value, holding the codewords at `is`. -/
def braidDecoder (n : Nat) (is : List Nat) : List UInt8 :=
  ((Model.Erasure.Decoder.new n).addAll (codewordsOf (braidValue n) is)).toBytes

/-- A stand-in for one of the two delegated values: the right length and
    nothing else, which is all the model's reader looks at. -/
def opaqueField (n : Nat) (b : UInt8) : List UInt8 := List.replicate n b

def braidAuth : List UInt8 := ramp 64 5 1

def braidAt (tag : UInt8) (epoch : Nat) (fields : List (List UInt8)) :
    Model.PersistedState.BraidState.State :=
  { tag := tag, epoch := epoch, auth := braidAuth, fields := fields }

def braidFailed : Model.PersistedState.BraidState.State :=
  { tag := 11, epoch := 0, auth := [], fields := [] }

/-- The fields an accepted Braid state holds. `Failed` carries only its tag:
    the format writes no epoch, no authenticator and no fields for it. -/
def braidFields (st : Model.PersistedState.BraidState.State) : List (String × List UInt8) :=
  if st.tag = 11 then [("state_tag", [st.tag])]
  else
    [("state_tag", [st.tag]), ("epoch", beN 8 st.epoch), ("auth", st.auth),
     ("fields", (st.fields.map fun f => beN 4 f.length ++ f).flatten)]

@[never_extract]
def braidStored (id comment : String) (bs : List UInt8)
    (expect : Option Model.PersistedState.Refusal) : Except String String :=
  storedStateVector Model.PersistedState.BraidState.ofBytes braidFields id comment bs expect

/-- A state written and read back, and its bytes offered to the reader beside
    it. -/
@[never_extract]
def braidState (id comment : String) (st : Model.PersistedState.BraidState.State) :
    Except String (List String) :=
  let bs := Model.PersistedState.BraidState.toBytes st
  if Model.PersistedState.readsBackTo (Model.PersistedState.BraidState.ofBytes bs) st then do
    let back ← braidStored id comment bs none
    pure [back]
  else .error ("genvectors: " ++ id ++ ": a stored Braid state does not read back to itself")

/-- One received Braid message: `epoch(8) || type(1) || chunk_present(1) ||
    chunk_index(2) || chunk(32)`, as the composite header carries one
    (message-format.md, Ratchet message; `AgreementType` in CONSTANTS.md).
    The two transitions a stored state can drive read no codeword, so every
    step here is a `None` message carrying none. -/
inductive BraidStep where
  | receive (epoch : Nat)

def BraidStep.bytes : BraidStep → List UInt8
  | .receive e => beN 8 e ++ [0x00] ++ [0x00] ++ beN 2 0 ++ List.replicate 32 0

/-- The model's own `receive`, on the one state a stored Braid can be put back
    into (`Model.PersistedState.BraidState.toCt2Sampled`). -/
def runBraid (st : Model.PersistedState.BraidState.State) :
    List BraidStep → Option Model.PersistedState.BraidState.State
  | [] => some st
  | .receive e :: rest =>
    match Model.PersistedState.BraidState.toCt2Sampled st with
    | none => none
    | some bst =>
      match Model.PersistedState.BraidState.ofBraid
          (Model.Braid.receive Model.Braid.toyKem bst
            { epoch := e, type := Model.Braid.MsgType.none, data := Option.none }).2.2 with
      | none => none
      | some st' => runBraid st' rest

/-- Operations on a stored Braid state, with the state they reach. -/
@[never_extract]
def braidOps (id comment : String) (start : Model.PersistedState.BraidState.State)
    (steps : List BraidStep) : Except String (List String) :=
  let startBytes := Model.PersistedState.BraidState.toBytes start
  if !Model.PersistedState.readsBackTo
      (Model.PersistedState.BraidState.ofBytes startBytes) start then
    .error ("genvectors: " ++ id ++ ": the start does not read back to itself")
  else
    match runBraid start steps with
    | none => .error ("genvectors: " ++ id ++ ": the model refuses an operation the vector lists")
    | some st =>
      let bs := Model.PersistedState.BraidState.toBytes st
      if Model.PersistedState.readsBackTo (Model.PersistedState.BraidState.ofBytes bs) st then
        .ok [answerVector id comment
          [("start", startBytes), ("steps", (steps.map BraidStep.bytes).flatten)] (some bs)]
      else .error ("genvectors: " ++ id ++ ": the state reached does not read back to itself")

@[never_extract]
def braidStateFile (_ : Unit) : Except String String := do
  let hdrValue := headerLen + macLen
  let ct2Value := ct2Len + macLen
  let header := braidValue headerLen
  let ct1 := braidValue ct1Len
  let ekVector := braidValue ekVectorLen
  let encaps := opaqueField encapsLen 0x5e
  let keyPair := opaqueField keyPairLen 0x4b
  let tag0 := braidAt 0 1 []
  let tag5 := braidAt 5 1 [braidDecoder hdrValue []]
  let tag6 := braidAt 6 1 [header, braidDecoder ekVectorLen []]
  let tag7 := braidAt 7 1
    [header, encaps, ct1, braidEncoder ct1Len 1, braidDecoder ekVectorLen [0]]
  let tag8 := braidAt 8 2 [encaps, ct1, ekVector, braidEncoder ct1Len 2]
  let tag9 := braidAt 9 1 [header, encaps, ct1, braidDecoder ekVectorLen [1, 0]]
  let tag10 := braidAt 10 1 [braidEncoder ct2Value 1]
  let accepted ← [
    braidState "keys-unsampled"
      "tag 0: the epoch and the authenticator, and no field at all" tag0,
    braidState "no-header-received"
      "tag 5: the header decoder, sized for the 96 bytes of the header and its MAC" tag5,
    braidState "header-received"
      "tag 6: the 64-byte header and an ek_vector decoder for 1,536 bytes" tag6,
    braidState "ct1-sampled"
      "tag 7: the header, an encapsulation state checked for its length alone, ct1, a ct1 encoder and an ek_vector decoder holding one codeword" tag7,
    braidState "ek-received-ct1-sampled"
      "tag 8: an encapsulation state, ct1, the completed ek_vector and a ct1 encoder, at epoch 2" tag8,
    braidState "ct1-acknowledged"
      "tag 9: the header, an encapsulation state, ct1 and an ek_vector decoder holding two codewords" tag9,
    braidState "ct2-sampled" "tag 10: the ct2 encoder, sized for 192 bytes" tag10,
    braidState "failed" "tag 11: two bytes, the version and the tag, and nothing else" braidFailed,
    braidState "epoch-at-the-largest-accepted"
      "tag 0 at u64::MAX - 1, the largest epoch a reader accepts"
      (braidAt 0 (Model.PersistedState.BraidState.largestEpoch) [])
  ].mapM id
  let ops ← [
    braidOps "ct2-sampled-below-the-ceiling-steps"
      "tag 10 at u64::MAX - 2, a message at the next epoch: transition (13) to tag 0 at u64::MAX - 1"
      (braidAt 10 (Model.Braid.u64Max - 2) [braidEncoder ct2Value 1])
      [.receive (Model.Braid.u64Max - 1)],
    braidOps "ct2-sampled-at-the-ceiling-fails"
      "tag 10 at u64::MAX - 1, where the step would land on the reserved epoch: the Braid fails instead, whatever the message (mlkem-braid.md, Failure)"
      (braidAt 10 (Model.Braid.u64Max - 1) [braidEncoder ct2Value 1])
      [.receive Model.Braid.u64Max]
  ].mapM id
  let enc (st : Model.PersistedState.BraidState.State) :=
    Model.PersistedState.BraidState.toBytes st
  let tag0Bytes := enc tag0
  let tag5Bytes := enc tag5
  let refusals ← [
    braidStored "empty" "no bytes" [] (some .shortOrMalformed),
    braidStored "version-only" "one byte: the version, and no tag" [0x01]
      (some .shortOrMalformed),
    braidStored "version-zero" "a first byte of 0x00" (replaceAt tag0Bytes 0 0x00)
      (some .wrongVersion),
    braidStored "version-two" "a first byte of 0x02" (replaceAt tag0Bytes 0 0x02)
      (some .wrongVersion),
    braidStored "tag-twelve" "a tag one past Failed" (replaceAt tag0Bytes 1 0x0c)
      (some .shortOrMalformed),
    braidStored "tag-255" "a tag no state has" (replaceAt tag0Bytes 1 0xff)
      (some .shortOrMalformed),
    braidStored "epoch-u64-max"
      "a stored epoch of u64::MAX, the value the Braid reserves and its reader refuses"
      (enc (braidAt 0 Model.Braid.u64Max [])) (some .shortOrMalformed),
    braidStored "epoch-zero" "a live state's epoch is at least 1"
      (enc (braidAt 0 0 [])) (some .shortOrMalformed),
    braidStored "failed-with-a-trailing-byte" "Failed carries nothing at all"
      (enc braidFailed ++ [0x00]) (some .shortOrMalformed),
    braidStored "auth-cut-short" "the authenticator one byte short of its 64"
      (tag0Bytes.take (tag0Bytes.length - 1)) (some .shortOrMalformed),
    braidStored "trailing-byte" "one byte after the last field"
      (tag5Bytes ++ [0x00]) (some .shortOrMalformed),
    braidStored "field-length-overruns" "a field length the buffer does not hold"
      (replaceAt tag5Bytes 77 0xff) (some .shortOrMalformed),
    braidStored "header-wrong-length" "tag 6's header is 64 bytes and this one is 63"
      (enc (braidAt 6 1 [header.take 63, braidDecoder ekVectorLen []]))
      (some .shortOrMalformed),
    braidStored "ct1-wrong-length" "tag 7's ct1 is 1,408 bytes and this one is 1,407"
      (enc (braidAt 7 1 [header, encaps, ct1.take (ct1Len - 1), braidEncoder ct1Len 1,
        braidDecoder ekVectorLen []])) (some .shortOrMalformed),
    braidStored "ek-vector-wrong-length" "tag 8's ek_vector is 1,536 bytes and this one is 1,535"
      (enc (braidAt 8 2 [encaps, ct1, ekVector.take (ekVectorLen - 1), braidEncoder ct1Len 2]))
      (some .shortOrMalformed),
    braidStored "encaps-wrong-length"
      "an encapsulation state of 2,591 bytes: its length is the whole of what the page has the reader check in it"
      (enc (braidAt 7 1 [header, encaps.take (encapsLen - 1), ct1, braidEncoder ct1Len 1,
        braidDecoder ekVectorLen []])) (some .shortOrMalformed),
    braidStored "key-pair-wrong-length"
      "a key pair of 11,871 bytes in tag 1: the length is the part of the key-pair rule a reader can apply without the layout the page delegates"
      (enc (braidAt 1 1 [keyPair.take (keyPairLen - 1), braidEncoder hdrValue 1]))
      (some .shortOrMalformed),
    braidStored "decoder-sized-for-another-value"
      "tag 5's decoder is sized for 96 bytes and this one for 1,536"
      (enc (braidAt 5 1 [braidDecoder ekVectorLen []])) (some .shortOrMalformed),
    braidStored "encoder-sized-for-another-value"
      "tag 10's encoder is sized for 192 bytes and this one for 96"
      (enc (braidAt 10 1 [braidEncoder hdrValue 1])) (some .shortOrMalformed),
    braidStored "coder-its-own-reader-refuses"
      "tag 5's decoder with a needed that is not ceil(size / 32), which the erasure decoder's own rules exclude"
      (enc (braidAt 5 1 [beN 8 hdrValue ++ beN 8 5 ++ beN 4 0])) (some .shortOrMalformed),
    braidStored "too-few-fields" "tag 6 carries a header and a decoder, and this carries one field"
      (enc (braidAt 6 1 [header])) (some .shortOrMalformed),
    braidStored "too-many-fields" "tag 0 carries no field at all"
      (enc (braidAt 0 1 [header])) (some .shortOrMalformed)
  ].mapM id
  pure ("{\n" ++
    "  \"schema_version\": 1,\n" ++
    "  \"algorithm\": \"braid-state\",\n" ++
    "  \"source\": \"generated by tacenta-model Vectors.lean (lake exe genvectors braid-state), from Model.PersistedState.BraidState and Model.Braid; key_pair and encaps are stand-ins of the right length, since the page delegates their layout, so no accepted vector carries a key_pair and tags 1 to 4 appear only in refusals; the generator writes no vector whose result the model does not give\",\n" ++
    "  \"vectors\": [\n" ++
    String.intercalate ",\n" (accepted.flatten ++ ops.flatten ++ refusals) ++
    "\n  ]\n}")

/-! ### The bounded protobuf profile (`Model.Protobuf`) -/

def pbLd (field : Nat) (v : List UInt8) : List UInt8 :=
  Model.Protobuf.encodeVarint (field * 8 + 2) ++ Model.Protobuf.encodeVarint v.length ++ v

def pbV (field n : Nat) : List UInt8 :=
  Model.Protobuf.encodeVarint (field * 8) ++ Model.Protobuf.encodeVarint n

@[never_extract]
def ratchetBodyVector (id comment : String) (region : List UInt8) : String :=
  fieldsVector id comment "region" region
    ((Model.Protobuf.parseRatchetBody region).map fun b =>
      [("ratchet_key", b.ratchetKey), ("counter", beN 4 b.counter),
       ("previous_counter", beN 4 b.previousCounter), ("ciphertext", b.ciphertext),
       ("pq", b.pq)])

def rbKey : List UInt8 := 0x05 :: fill 0x0a
def rb1 : List UInt8 := pbLd 1 rbKey
def rb2 : List UInt8 := pbV 2 7
def rb3 : List UInt8 := pbV 3 3
def rb4 : List UInt8 := pbLd 4 (ramp 20 5 0x30)
def rb5 : List UInt8 := pbLd 5 [0xa1, 0xa2, 0xa3, 0xa4]

/-- A body whose ciphertext is sized so the region is `total` bytes, for totals
    whose ciphertext length takes a two-byte varint. -/
def rbOfLength (total : Nat) : List UInt8 :=
  let others := rb1 ++ rb2 ++ rb3 ++ rb5
  rb1 ++ rb2 ++ rb3 ++ pbLd 4 (ramp (total - others.length - 3) 1 0) ++ rb5

@[never_extract]
def ratchetBodyFile (_ : Unit) : String :=
  answerFile "protobuf-ratchet-body"
    "generated by tacenta-model Vectors.lean (lake exe genvectors protobuf-ratchet-body), from Model.Protobuf.parseRatchetBody; varint fields are written as four big-endian bytes"
    [ ratchetBodyVector "ascending-order" "all five fields in field-number order" (rb1 ++ rb2 ++ rb3 ++ rb4 ++ rb5),
      ratchetBodyVector "descending-order" "field order is free" (rb5 ++ rb4 ++ rb3 ++ rb2 ++ rb1),
      ratchetBodyVector "interleaved-order" "field order is free" (rb3 ++ rb1 ++ rb5 ++ rb2 ++ rb4),
      ratchetBodyVector "empty-values-and-zero-counters" "a length of zero and a value of zero are both accepted" (pbLd 1 [] ++ pbV 2 0 ++ pbV 3 0 ++ pbLd 4 [] ++ pbLd 5 []),
      ratchetBodyVector "widest-varints" "a five-byte varint at 2^32 - 1, a two-byte one, and a two-byte length" (rb1 ++ pbV 2 4294967295 ++ pbV 3 300 ++ pbLd 4 (ramp 300 3 1) ++ rb5),
      ratchetBodyVector "at-the-length-bound" "a region of exactly 16384 bytes" (rbOfLength 16384),
      ratchetBodyVector "over-the-length-bound" "a region of 16385 bytes" (rbOfLength 16385),
      ratchetBodyVector "empty-region" "no fields, so every required field is missing" [],
      ratchetBodyVector "missing-pq" "every field is required" (rb1 ++ rb2 ++ rb3 ++ rb4),
      ratchetBodyVector "repeated-counter" "a repeated field is refused, not resolved" (rb1 ++ rb2 ++ pbV 2 8 ++ rb3 ++ rb4 ++ rb5),
      ratchetBodyVector "repeated-after-all-five" "a field after all five is a repeat" (rb1 ++ rb2 ++ rb3 ++ rb4 ++ rb5 ++ rb1),
      ratchetBodyVector "field-six" "a field number the message type does not define" (pbV 6 1 ++ rb1 ++ rb2 ++ rb3 ++ rb4 ++ rb5),
      ratchetBodyVector "field-zero" "field number 0" ([0x02, 0x00] ++ rb1 ++ rb2 ++ rb3 ++ rb4 ++ rb5),
      ratchetBodyVector "field-sixteen" "a field number above 15, refused rather than skipped" ([0x82, 0x01, 0x00] ++ rb1 ++ rb2 ++ rb3 ++ rb4 ++ rb5),
      ratchetBodyVector "wire-type-one" "wire type 1" (rb1 ++ [0x11, 0, 0, 0, 0, 0, 0, 0, 0] ++ rb3 ++ rb4 ++ rb5),
      ratchetBodyVector "wire-type-five" "wire type 5" (rb1 ++ [0x15, 0, 0, 0, 0] ++ rb3 ++ rb4 ++ rb5),
      ratchetBodyVector "counter-length-delimited" "a defined field number with the other wire type" (rb1 ++ pbLd 2 [0x07] ++ rb3 ++ rb4 ++ rb5),
      ratchetBodyVector "ciphertext-varint" "a defined field number with the other wire type" (rb1 ++ rb2 ++ rb3 ++ pbV 4 7 ++ rb5),
      ratchetBodyVector "non-minimal-varint" "7 spelled in two bytes" (rb1 ++ [0x10, 0x87, 0x00] ++ rb3 ++ rb4 ++ rb5),
      ratchetBodyVector "non-minimal-tag" "the counter's tag spelled in two bytes" (rb1 ++ [0x90, 0x00, 0x07] ++ rb3 ++ rb4 ++ rb5),
      ratchetBodyVector "non-minimal-length" "a length of 4 spelled in two bytes" (rb1 ++ rb2 ++ rb3 ++ rb4 ++ [0x2a, 0x84, 0x00, 0xa1, 0xa2, 0xa3, 0xa4]),
      ratchetBodyVector "six-byte-varint" "a fifth byte with its top bit set" (rb1 ++ [0x10, 0x80, 0x80, 0x80, 0x80, 0x80, 0x01] ++ rb3 ++ rb4 ++ rb5),
      ratchetBodyVector "varint-over-32-bits" "five bytes carrying 2^32" (rb1 ++ [0x10, 0x80, 0x80, 0x80, 0x80, 0x10] ++ rb3 ++ rb4 ++ rb5),
      ratchetBodyVector "varint-truncated" "the region ends before a varint's final byte" (rb1 ++ rb3 ++ rb4 ++ rb5 ++ [0x10, 0x80]),
      ratchetBodyVector "length-overruns-the-region" "a length of 50 with 10 bytes left" (rb1 ++ rb2 ++ rb3 ++ rb5 ++ [0x22, 0x32] ++ ramp 10 1 0),
      ratchetBodyVector "trailing-zero-byte" "a byte after the last field is read as a tag, and 0x00 is field 0" (rb1 ++ rb2 ++ rb3 ++ rb4 ++ rb5 ++ [0x00]) ]

@[never_extract]
def prekeyEnvelopeVector (id comment : String) (region : List UInt8) : String :=
  fieldsVector id comment "region" region
    ((Model.Protobuf.parsePrekeyBody region).map fun b =>
      (match b.prekeyId with
       | some i => [("prekey_id", beN 4 i)]
       | none => []) ++
      [("base_key", b.baseKey), ("identity_key", b.identityKey), ("message", b.message),
       ("registration_id", beN 4 b.registrationId), ("signed_prekey_id", beN 4 b.signedPrekeyId),
       ("pq_prekey_id", beN 4 b.pqPrekeyId), ("kem", b.kem)])

def pe1 : List UInt8 := pbV 1 77
def pe2 : List UInt8 := pbLd 2 (0x05 :: fill 0x0b)
def pe3 : List UInt8 := pbLd 3 (0x05 :: fill 0x0c)
def pe4 : List UInt8 := pbLd 4 (rb1 ++ rb2 ++ rb3 ++ rb4 ++ rb5)
def pe5 : List UInt8 := pbV 5 12345
def pe6 : List UInt8 := pbV 6 0x01020304
def pe7 : List UInt8 := pbV 7 9
def pe8 : List UInt8 := pbLd 8 (ramp 30 9 0x40)

def pe2to7 : List UInt8 := pe2 ++ pe3 ++ pe4 ++ pe5 ++ pe6 ++ pe7

@[never_extract]
def prekeyEnvelopeFile (_ : Unit) : String :=
  let kemFor (total : Nat) : List UInt8 :=
    let others := pe1 ++ pe2to7
    pbLd 8 (ramp (total - others.length - 3) 1 0)
  answerFile "protobuf-prekey-envelope"
    "generated by tacenta-model Vectors.lean (lake exe genvectors protobuf-prekey-envelope), from Model.Protobuf.parsePrekeyBody; varint fields are written as four big-endian bytes, and prekey_id is left out when the field is absent"
    [ prekeyEnvelopeVector "all-eight-ascending" "every field, in field-number order" (pe1 ++ pe2to7 ++ pe8),
      prekeyEnvelopeVector "prekey-id-absent" "field 1 is optional and absent means no identifier" (pe2to7 ++ pe8),
      prekeyEnvelopeVector "prekey-id-zero" "a present field 1 of value 0 is the identifier 0, not an absent one" (pbV 1 0 ++ pe2to7 ++ pe8),
      prekeyEnvelopeVector "shuffled-order" "field order is free" (pe8 ++ pe1 ++ pe6 ++ pe2 ++ pe5 ++ pe3 ++ pe7 ++ pe4),
      prekeyEnvelopeVector "empty-values-and-zero-identifiers" "nothing inside a field is validated" (pbLd 2 [] ++ pbLd 3 [] ++ pbLd 4 [] ++ pbV 5 0 ++ pbV 6 0 ++ pbV 7 0 ++ pbLd 8 []),
      prekeyEnvelopeVector "inner-message-not-parsed" "the message field is carried as bytes, whatever they are" (pe1 ++ pe2 ++ pe3 ++ pbLd 4 [0xff, 0xff, 0xff] ++ pe5 ++ pe6 ++ pe7 ++ pe8),
      prekeyEnvelopeVector "at-the-length-bound" "a region of exactly 16384 bytes" (pe1 ++ pe2to7 ++ kemFor 16384),
      prekeyEnvelopeVector "over-the-length-bound" "a region of 16385 bytes" (pe1 ++ pe2to7 ++ kemFor 16385),
      prekeyEnvelopeVector "repeated-prekey-id" "a repeated field 1 is refused" (pe1 ++ pe1 ++ pe2to7 ++ pe8),
      prekeyEnvelopeVector "missing-kem" "fields 2 to 8 are required" (pe1 ++ pe2to7),
      prekeyEnvelopeVector "missing-registration-id" "fields 2 to 8 are required" (pe1 ++ pe2 ++ pe3 ++ pe4 ++ pe6 ++ pe7 ++ pe8),
      prekeyEnvelopeVector "field-nine" "a field number the message type does not define" (pe1 ++ pe2to7 ++ pe8 ++ pbV 9 1),
      prekeyEnvelopeVector "field-fifteen" "field 15 passes the tag check and is then refused" (pbV 15 1 ++ pe2to7 ++ pe8),
      prekeyEnvelopeVector "prekey-id-length-delimited" "a defined field number with the other wire type" (pbLd 1 [77] ++ pe2to7 ++ pe8),
      prekeyEnvelopeVector "kem-varint" "a defined field number with the other wire type" (pe1 ++ pe2to7 ++ pbV 8 1),
      prekeyEnvelopeVector "registration-id-over-32-bits" "five bytes carrying 2^35 - 1" (pe1 ++ pe2 ++ pe3 ++ pe4 ++ [0x28, 0xff, 0xff, 0xff, 0xff, 0x7f] ++ pe6 ++ pe7 ++ pe8) ]

/-! ### Authenticated encryption

`message-format.md`, Authenticated encryption. The padding, the IV arithmetic,
the tag and the receiver's four steps are computed here from that section, the
tag with the model's HMAC (`Model.Kdf.hmac`). The model does not implement AES,
so no block is enciphered here: every AES-256 block value is a known answer
from NIST SP 800-38A under its AES-256 key -- the four ECB-AES256 pairs of F.1.5
and the CBC-AES256 chain of F.2.5 -- and a block outside that table stops the
file from being valid JSON rather than being guessed. Each IV is chosen so that
the cipher's input is one of those blocks. -/

def nistKey : List UInt8 := ofHex "603deb1015ca71be2b73aef0857d77811f352c073b6108d72d9810a30914dff4"
def nistIv : List UInt8 := ofHex "000102030405060708090a0b0c0d0e0f"

/-- The four plaintext blocks both examples encipher. -/
def nistPlain : List (List UInt8) := [
  ofHex "6bc1bee22e409f96e93d7e117393172a", ofHex "ae2d8a571e03ac9c9eb76fac45af8e51",
  ofHex "30c81c46a35ce411e5fbc1191a0a52ef", ofHex "f69f2445df4f9b17ad2b417be66c3710"]

/-- F.1.5, ECB-AES256.Encrypt: each plaintext block enciphered on its own. -/
def nistEcb : List (List UInt8) := [
  ofHex "f3eed1bdb5d2a03c064b5a7e3db181f8", ofHex "591ccb10d410ed26dc5ba74a31362870",
  ofHex "b6ed21b99ca6f4f9f153e7b1beafed1d", ofHex "23304b7a39f9f3ff067d8d8f9e24ecc7"]

/-- F.2.5, CBC-AES256.Encrypt, under `nistIv`. -/
def nistCbc : List (List UInt8) := [
  ofHex "f58c4c04d6e5f1ba779eabfb5f7bfbd6", ofHex "9cfc4e967edb808d679f777bc6702c7d",
  ofHex "39f23369a9d9bacfa530e26304231461", ofHex "b2eb05e2c39be9fcda6c19078c6a9d1b"]

def xorBytes (a b : List UInt8) : List UInt8 := List.zipWith (· ^^^ ·) a b

/-- Every (input, output) pair of the block cipher under `nistKey` the two
    examples give: F.1.5's directly, and F.2.5's as the block that was
    enciphered, which is the plaintext block xored with the previous ciphertext
    block (the IV for the first). -/
def aesTable : List (List UInt8 × List UInt8) :=
  nistPlain.zip nistEcb ++
  ((nistPlain.zip (nistIv :: nistCbc)).map fun p => xorBytes p.1 p.2).zip nistCbc

def aesEncryptBlock (b : List UInt8) : Option (List UInt8) :=
  (aesTable.find? fun p => p.1 == b).map Prod.snd

def aesDecryptBlock (c : List UInt8) : Option (List UInt8) :=
  (aesTable.find? fun p => p.2 == c).map Prod.fst

def blocks : Nat → List UInt8 → List (List UInt8)
  | 0, _ => []
  | fuel + 1, bs => if bs.isEmpty then [] else bs.take 16 :: blocks fuel (bs.drop 16)

/-- CBC, from the table; `none` when a block is not in it. -/
def cbcEncrypt (iv padded : List UInt8) : Option (List UInt8) :=
  let step (acc : Option (List UInt8 × List UInt8)) (b : List UInt8) :=
    acc.bind fun (prev, out) => (aesEncryptBlock (xorBytes b prev)).map fun c => (c, out ++ c)
  ((blocks padded.length padded).foldl step (some (iv, []))).map Prod.snd

def cbcDecrypt (iv ct : List UInt8) : Option (List UInt8) :=
  let step (acc : Option (List UInt8 × List UInt8)) (c : List UInt8) :=
    acc.bind fun (prev, out) => (aesDecryptBlock c).map fun d => (c, out ++ xorBytes d prev)
  ((blocks ct.length ct).foldl step (some (iv, []))).map Prod.snd

def aeadMacKey : List UInt8 := ramp 32 1 0xc0

def pkcs7 (pt : List UInt8) : List UInt8 :=
  let p := 16 - pt.length % 16
  pt ++ List.replicate p (UInt8.ofNat p)

/-- The sender: `ciphertext || HMAC-SHA256(mac_key, AD || ciphertext)`. -/
def aeadSeal (iv ad pt : List UInt8) : Option (List UInt8) :=
  (cbcEncrypt iv (pkcs7 pt)).map fun ct => ct ++ Model.Kdf.hmac aeadMacKey (ad ++ ct)

/-- The receiver's four steps. The outer `none` is a block outside the table;
    the inner one is a refusal. -/
def aeadOpen (iv ad input : List UInt8) : Option (Option (List UInt8)) :=
  if input.length < 32 then some none
  else
    let ct := input.take (input.length - 32)
    let tag := input.drop (input.length - 32)
    if Model.Kdf.hmac aeadMacKey (ad ++ ct) != tag then some none
    else if ct.isEmpty || ct.length % 16 != 0 then some none
    else
      (cbcDecrypt iv ct).map fun padded =>
        let p := (padded.getD (padded.length - 1) 0).toNat
        if 1 ≤ p && p ≤ 16 && (padded.drop (padded.length - p)).all (· == UInt8.ofNat p)
        then some (padded.take (padded.length - p)) else none

def aeadInputs (iv ad : List UInt8) : List (String × List UInt8) :=
  [("enc_key", nistKey), ("mac_key", aeadMacKey), ("iv", iv), ("ad", ad)]

def unlisted (id : String) : String :=
  "    { \"id\": \"" ++ id ++ "\" an AES block outside the NIST SP 800-38A table }"

/-- One block of plaintext (at most 15 bytes, so the padding stays in the block)
    under an IV that makes the cipher's input F.1.5's plaintext block `i`. -/
def ivFor (pt : List UInt8) (i : Nat) : List UInt8 :=
  xorBytes (pkcs7 pt) (nistPlain.getD i [])

@[never_extract]
def sealVector (id comment : String) (iv ad pt : List UInt8) : String :=
  match aeadSeal iv ad pt with
  | some out => answerVector id comment (aeadInputs iv ad ++ [("plaintext", pt)]) (some out)
  | none => unlisted id

@[never_extract]
def openVector (id comment : String) (iv ad input : List UInt8) : String :=
  match aeadOpen iv ad input with
  | some out => answerVector id comment (aeadInputs iv ad ++ [("input", input)]) out
  | none => unlisted id

/-- The associated data a session passes: `CONCAT(ad, header)`, with `ad` the
    two identity keys and the header a composite header. -/
def sessionAd : List UInt8 :=
  Model.Messages.concatAd ((0x05 :: fill 0x0a) ++ (0x05 :: fill 0x0b))
    (Model.CompositeHeader.encode compA)

def aeadSource (kind : String) : String :=
  "generated by tacenta-model Vectors.lean (lake exe genvectors " ++ kind ++
  "): the padding, the IV, the HMAC-SHA256 tag over AD || ciphertext and the receiver's steps are computed from message-format.md, Authenticated encryption, with the model's HMAC; the model does not implement AES, so every AES-256 block value is a known answer from NIST SP 800-38A (F.1.5 ECB-AES256 and F.2.5 CBC-AES256) under that standard's key, each IV chosen so the cipher's input is one of its blocks; the keys are therefore not an output of the message-key expansion, which vectors/ratchet/double-ratchet.json pins"

@[never_extract]
def aeadEncryptFile (_ : Unit) : String :=
  answerFile "aead-encrypt" (aeadSource "aead-encrypt")
    [ sealVector "empty-plaintext" "an empty plaintext gains a whole block of padding" (ivFor [] 0) [] [],
      sealVector "fifteen-bytes" "fifteen bytes gain one padding byte" (ivFor (ramp 15 17 2) 1) (ramp 20 3 0x61) (ramp 15 17 2),
      sealVector "one-byte" "one byte gains fifteen" (ivFor [0x2a] 2) [0x00] [0x2a],
      sealVector "session-associated-data" "AD is CONCAT(ad, header): a length, the identity keys, then a composite header" (ivFor (ramp 8 1 0x70) 3) sessionAd (ramp 8 1 0x70) ]

@[never_extract]
def aeadDecryptFile (_ : Unit) : String :=
  let ad := ramp 20 3 0x61
  let ct (i : Nat) := nistEcb.getD i []
  let tagged (ad c : List UInt8) := c ++ Model.Kdf.hmac aeadMacKey (ad ++ c)
  let good := tagged ad (ct 1)
  let ivGood := ivFor (ramp 15 17 2) 1
  let ivDecryptingTo (block : List UInt8) (i : Nat) := xorBytes block (nistPlain.getD i [])
  answerFile "aead-decrypt" (aeadSource "aead-decrypt")
    [ openVector "fifteen-bytes" "the tag verifies and one padding byte is removed" ivGood ad good,
      openVector "empty-plaintext" "a whole block of padding removed leaves nothing" (ivFor [] 0) [] (tagged [] (ct 0)),
      openVector "session-associated-data" "AD is CONCAT(ad, header)" (ivFor (ramp 8 1 0x70) 3) sessionAd (tagged sessionAd (ct 3)),
      openVector "shorter-than-a-tag" "31 bytes" ivGood ad (good.take 31),
      openVector "tag-with-no-ciphertext" "a valid tag over an empty ciphertext is refused after the tag check" ivGood ad (tagged ad []),
      openVector "ciphertext-not-whole-blocks" "a valid tag over 15 bytes of ciphertext" ivGood ad (tagged ad ((ct 1).take 15)),
      openVector "tag-altered" "the last tag byte changed" ivGood ad (replaceAt good 47 (good.getD 47 0 ^^^ 0x01)),
      openVector "ciphertext-altered" "the first ciphertext byte changed" ivGood ad (replaceAt good 0 (good.getD 0 0 ^^^ 0x01)),
      openVector "associated-data-differs" "the same input under other associated data" ivGood (ramp 20 3 0x62) good,
      openVector "padding-byte-zero" "the tag verifies and the last byte decrypts to 0" (ivDecryptingTo (List.replicate 16 0x00) 2) ad (tagged ad (ct 2)),
      openVector "padding-byte-seventeen" "the tag verifies and the last byte decrypts to 17" (ivDecryptingTo (List.replicate 16 0x11) 2) ad (tagged ad (ct 2)),
      openVector "padding-bytes-disagree" "the last byte decrypts to 2 and the byte before it to 3" (ivDecryptingTo (List.replicate 14 0x41 ++ [0x03, 0x02]) 3) ad (tagged ad (ct 3)),
      openVector "last-byte-sixteen-rest-not" "F.2.5's four blocks: the last byte decrypts to 16 and the fifteen before it do not" nistIv ad (tagged ad (nistCbc.flatten)) ]

end Vectors

def main (args : List String) : IO Unit :=
  if args.contains "pqxdh" then
    IO.println Vectors.pqxdhFile
  else if args.contains "serialization" then
    IO.println Vectors.encodingFile
  else if args.contains "initial" then
    IO.println Vectors.initialFile
  else if args.contains "gf" then
    IO.println Vectors.gfFile
  else if args.contains "inv" then
    IO.println Vectors.invFile
  else if args.contains "interp" then
    IO.println Vectors.interpFile
  else if args.contains "spqr" then
    IO.println Vectors.spqrFile
  else if args.contains "braid" then
    IO.println Vectors.braidFile
  else if args.contains "auth" then
    IO.println Vectors.braidAuthFile
  else if args.contains "triple" then
    IO.println Vectors.tripleFile
  else if args.contains "split" then
    IO.println Vectors.splitFile
  else if args.contains "composite" then
    IO.println Vectors.compositeFile
  else if args.contains "composite-decode" then
    Vectors.printOrFail (Vectors.compositeDecodeFile ())
  else if args.contains "bundle-decode" then
    Vectors.printOrFail (Vectors.bundleDecodeFile ())
  else if args.contains "initial-decode" then
    Vectors.printOrFail (Vectors.initialDecodeFile ())
  else if args.contains "erasure-encode" then
    IO.println (Vectors.erasureEncodeFile ())
  else if args.contains "erasure-decode" then
    IO.println (Vectors.erasureDecodeFile ())
  else if args.contains "erasure-encoder-state" then
    IO.println (Vectors.erasureEncoderFile ())
  else if args.contains "erasure-decoder-state" then
    IO.println (Vectors.erasureDecoderFile ())
  else if args.contains "ratchet-state" then
    Vectors.printOrFail (Vectors.ratchetStateFile ())
  else if args.contains "sparse-ratchet-state" then
    Vectors.printOrFail (Vectors.sparseRatchetStateFile ())
  else if args.contains "triple-ratchet-state" then
    Vectors.printOrFail (Vectors.tripleStateFile ())
  else if args.contains "braid-state" then
    Vectors.printOrFail (Vectors.braidStateFile ())
  else if args.contains "prekey-store-state" then
    Vectors.printOrFail (Vectors.prekeyStoreStateFile ())
  else if args.contains "protobuf-ratchet-body" then
    IO.println (Vectors.ratchetBodyFile ())
  else if args.contains "protobuf-prekey-envelope" then
    IO.println (Vectors.prekeyEnvelopeFile ())
  else if args.contains "aead-encrypt" then
    IO.println (Vectors.aeadEncryptFile ())
  else if args.contains "aead-decrypt" then
    IO.println (Vectors.aeadDecryptFile ())
  else
    IO.println Vectors.file
