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

private def compA : Model.CompositeHeader.Composite :=
  { dh := fill 0xaa, pn := 7, n := 9, pqEpoch := 3, pqN := 11, agEpoch := 3,
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
        m32 [0, 1, 65534, 65535] true ]

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

def hexNibbles : List Char → List UInt8
  | a :: b :: rest =>
    let v (c : Char) : Nat := if c.isDigit then c.toNat - 48 else c.toNat - 87
    UInt8.ofNat (v a * 16 + v b) :: hexNibbles rest
  | _ => []

def ofHex (s : String) : List UInt8 := hexNibbles s.toList

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
  else if args.contains "erasure-encode" then
    IO.println (Vectors.erasureEncodeFile ())
  else if args.contains "erasure-decode" then
    IO.println (Vectors.erasureDecodeFile ())
  else if args.contains "erasure-encoder-state" then
    IO.println (Vectors.erasureEncoderFile ())
  else if args.contains "erasure-decoder-state" then
    IO.println (Vectors.erasureDecoderFile ())
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
