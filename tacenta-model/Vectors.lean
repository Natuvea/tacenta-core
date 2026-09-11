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
def compositeDecodeVector (id comment : String) (h : Model.CompositeHeader.Composite)
    (accept : Bool) : Except String String :=
  let encoding := Model.CompositeHeader.encode h
  match Model.CompositeHeader.decode encoding, accept with
  | some (d, rest), true =>
    .ok (decodeVector id comment encoding (some (Model.CompositeHeader.encode d ++ rest)))
  | Option.none, false => .ok (decodeVector id comment encoding Option.none)
  | _, _ => .error ("genvectors: the model's composite-header decoder does not give " ++
      id ++ " the result the vector records")

def compositeDecodeFile : Except String String := do
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
      { compA with dh := plusP nine } false].mapM id
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
def bundleDecodeVector (id comment : String) (b : Model.Messages.Bundle)
    (accept : Bool) : Except String String :=
  let encoding := Model.Messages.encodeBundle b
  match Model.Messages.decodeBundle encoding, accept with
  | some d, true =>
    .ok (decodeVector id comment encoding (some (Model.Messages.encodeBundle d)))
  | Option.none, false => .ok (decodeVector id comment encoding Option.none)
  | _, _ => .error ("genvectors: the model's prekey-bundle decoder does not give " ++
      id ++ " the result the vector records")

def bundleDecodeFile : Except String String := do
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
    bundleDecodeVector "signed-prekey-with-bit-255-set"
      "the every-key-canonical signed_prekey with bit 255 set: refused"
      { bundleBase with signedPrekey := withBit255 bundleBase.signedPrekey } false,
    bundleDecodeVector "signed-prekey-plus-p"
      "signed_prekey the key 9 spelled as 9 + p: refused"
      { bundleBase with signedPrekey := plusP nine } false,
    bundleDecodeVector "one-time-prekey-with-bit-255-set"
      "the every-key-canonical one_time_prekey with bit 255 set: refused"
      { bundleBase with oneTimePrekey := some (withBit255 (fill 0x66)) } false,
    bundleDecodeVector "one-time-prekey-plus-p"
      "one_time_prekey the key 9 spelled as 9 + p: refused"
      { bundleBase with oneTimePrekey := some (plusP nine) } false].mapM id
  pure ("{\n" ++
    "  \"schema_version\": 1,\n" ++
    "  \"algorithm\": \"prekey-bundle-decode\",\n" ++
    "  \"source\": \"generated by tacenta-model Vectors.lean (lake exe genvectors bundle-decode), from Model.Messages.decodeBundle; an accepted vector's output is the re-encoding of the bundle it decodes to, and the generator writes no vector whose result the model does not give\",\n" ++
    "  \"vectors\": [\n" ++
    String.intercalate ",\n" vectors ++
    "\n  ]\n}")

/-- Print a generated file, or fail the run with the generator's reason. -/
def printOrFail (file : Except String String) : IO Unit :=
  match file with
  | .ok s => IO.println s
  | .error e => throw (IO.userError e)

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
    Vectors.printOrFail Vectors.compositeDecodeFile
  else if args.contains "bundle-decode" then
    Vectors.printOrFail Vectors.bundleDecodeFile
  else
    IO.println Vectors.file
