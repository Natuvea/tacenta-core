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
    "wrong version", "short or malformed", and the session's "inconsistent". -/
def refusalName : Model.PersistedState.Refusal → String
  | .wrongVersion => "wrong-version"
  | .shortOrMalformed => "short-or-malformed"
  | .inconsistent => "inconsistent"

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
  "04132c442be010fbd57e72603328aa76e71fccc1503aae219327d14d9c9993f472be63d18c035eea04353a20a0aa859635ea0f2bb265a3e89509451b53b7c168b9000000019565bb39905cf99b938461619cda94cfdf7dfad4d290c583626d2cd0853140cbcb693cf07d8381ed5723b78ad1f350c5053ddb24595d1c5aac9bba5324938304000000000000128076584152ab318db5ca7c06914c0b0e11ba0f324377f4f299f7352aa6257ba306a43e412b932cbfd156493e8501cbd812f6a81776b40481e254b3f80c64f2c53b2108bbac35c15324ea1430f81c2f19c8c1fe140760b2336119bd09fc9e54b9abdbcb06b67a4df6d614ad1c9bb91322e0176e317380646b2500362f069a861944b817cb3a7826ac0a268910d74a121156a6a0787f2a282fe23aefbc7ea8d7a5405742c4b94645ca976fc0191301422e05c4f9b9ce30e2cf9afb059a190a956cb3fb932ec23052cec49a6c9b2968688d29daca041c87bf5c49cb58c76d754ee01052b5b85e4cf837664cb3ec80aa49939c26c57c7ef87e888018c92c50054267dbd346e6353ef91b80644209a866819f894e18d6b033b6605af11142373bcbc467dd67a3f17a7c944298009b1fa195c6753364f06c7de8d70f04d487c4e043c6d545025716734c5c65174a99231846302d3aec3df02075d0c0c6e233cb3a060f58909e280164fa585b7fea2abb592bbfd4285a2c2d5d1792a79518f2414c9fa461864a1aaff7a333b361e5b51f234aad16a919e0c05d1cd815ee015f850cc2b92309ca3a2aa3366780f653a50382b9e5bb16e15e24233ad33728203b42297a2208e0b6fd989fce94283a4319d74cc88810248350c96a7b823919c85f06cdf1892bcc4b4cdbc26d00e78aab3b3a19406b68b112e7d55fbe34a7dde23693267044d363d71ac767021e5d818af6d46cf34c153778c2b9292e084b2357152cf208914ac5c556152e8e1b0ea911b926345aa75a36af7b9581bb15eb071d2e045ef0126b59abc8eb8091a67c617c4a25c00a1268d9044498607fb9024d6411fef21580ebbed40189d7087b70e44102d138973a62758ab7b7b472fc8a639aaa172213b8be025fe3357a11a6a0d23ab6400327a3fc0fd9a3393fab734f1246a763a7b8f15eb5a5cb1548c83e9a310759443c10b04d4145738534d41975322b6ab7ac4f12b8c0e0154ade64542799c91c157a7cbc901dc877be04034a5407b2512cdbec1acd2b8e11b0b1e0c21cf724038fa505d3b115ff24790876286aa4107de768d3b11ae13071aeda718b877f78b76b9d3511b1c20219b23eff20853d55ce61856fc84c7b195cce06755c6be504546c8af078b829a3b68c55771e66109009506096a5f2c4c7c8f25f6d6c40bf3341e4a271c00b513db917678449fae298284a7818f912e281a0e6755170828b2eb36908d244998459c23440bf0418d51bac593113ce3cbe7494a501e20d9cea3f3b1c9646b57558e410ee08a3fbc8627db221e4b0b6830b6df91469a3526adc030c9df0b5e6e73c3ddc7dcf681817a1a8311a69fe7ca948c728e9f7ab814a745ba58fd06805171a4b0e3c564470b6478c5daf8a6a9cdba2ef5845ea5439b7912647630828042768726e0a389321eaaa7ef575066bc7423283c13402fee268293010265566e6a69d875badb666cb8fda37f19223a9d77fec0ca87300a719f696265537d5440cbfba3eca6cb91bcb28c044af2a5c73cd95907d59be1b566d44482d0ffb7c6293695ebb745bb63dcc1938e7e93af9fb277716c68a074123254c5bc40e59a22cf49a9cf9f6c3dda7069d0c26b3ab1ae96b1e3de403dc2506df287edbf58a0d7213ad4657309b0b86973e47a6cd60a441f473b9a7d8a68ea7b03ccb4b0748642d122e9a2786a7f732da71c7b3b7115eaa6854b409cfeb6ee7b045036b075729ad19b43f1b379dd37308d03bb2d5109509c306e4e1165390a0c965898e272c6941700bfab9d66420fb2c911450b60125a34c4002de2c40241a17bc173b77c81f7d6c8612207d0ec077feab35a3bb0059ccaf69612b5b3b5e77472fcfbb870e1ac4767c9309403e5b919d5564b803d4a84e46a4e79b5e4e7c557ec086669837383c7265dc1ae3b06928c8ac9e500d0a808c66670caf6a84618a5664cb6e818390c76ca0dbbb23f2c0312dc43a395c98b8e415e88a78a2b6b1ed32c4d3383841d995b8a20d592a3804528e242a1d84dc02a6ba5c4203a2ceba08f6592110eb0a1bcc7f39066e4dc3cce9a9017b8c376ac071eff8c46659ccc25cb4d8d811ed146f2de8a411db863c2891d46789b593c4ff47ae98051923c67aba39c81594b9e7b7ca92a4b7544b89bd821dd175c46796745211bf47b776956bb866416e1791584781cbba33331bb6b811bbb06dd43903d65606c8074447054464cfb6f70876246eae8a5447cc48187a1af6bba938bb54b7144b63aa59e8f941e2b373a9e205cfe589421bb98ab4b2afd38b3df901bf04cc58b3802970882b661169859a1135cd795b3445915ad336bfc1b80379d7bd877449c5c46bfb899d07f0be1eeac331d15f0c6a7e0d53125127878a701bec01c190a8a24f747334b5aff092061988a97fe05e9e54cdb93cbb83fc5feca0342118293e7a91fb5165b0079c4e774979411c5da1596614b1c1ab3fe49bbc1ebb27c12141593a9eca9b821f7508816079dac131e1b8239dda83b6f1b001e71bf92290080a77c44837cd3b3c21c8c1ddb18626a3a739b061e4c359bd6b72ccb80ca6346badea3e7c5137408372076593c0999002555a1bc748393b365d86250142719717cbfad33187a880aac13c23f4b44daa76cc731beac7c72ac4144efa0c2ffa64b22b23a13639d88ccbc8daa0546779fe58267eb4188bb33f7e8589d48218569811f9bcc9507bb1905055b2a166625485f59109add09304210b9b359b7929003906a2daf6c362064012611589954acd84689634944953517f0679f52ba30d978deb56cbcb691f16da1ffd6c3e542a1da31c1493ba6147f9c00e331229d3cc06a1077adc71818abaa1c78da4cb0d6f24160bc67dd3530e3de2a0adb27e5ec72304c774e8a99132b244f3b585c9027505729c22040ab42209b696998de3070be95c766624f0bcca1a1b95d4d114c0b0bbdad0010a50376315aa936acd5d938f49ca0edd754c7a262922b683c474059d32220fe3878ea3cd5052cf3f4a2925387e1d643484bb7b4e0b0955145342ac7bfcc48556601a48b73ccfd906c71b5bf1b1004a6c39d387a6f2b0c943060cb4d0cd46a913aee815365b3d954809175625af676257d6afee61b36a4839782457c1153fdf07b46dd1c522c561446c7071d07fb511498e755ef3d23990c726c24860caf521adf04a496240ee63319c3596b4f9257ddace19d0bfeb050f35727ce283c718b9664a377aaa247104fa67b8b521c16a2a92b8959ab211bada37582701cae882cef75047ab8bc9423cab7269a3a404c300a16360660c5a0aec45a59345391c1800e4c10a0b96c482373601ca3510cca0d5932945e997ad773e182ab652243b0e7438d9a7c82a0a86669b29e5b67df4a50adbb625741a3db44a516e82b0f4faa3019167fbe031771a9bbf38991510b594847be919c23e131331c75f69f950a8f12fe34a245ee7be0ffa7b0fe7076f33547fb94e9416a5e2d07882849bf3eabe806c8bf0687ad6a0722ba079d9d2b57e00bbaaeac7532a69ed8383471bb6b73a59b8364e385c22148c8b92c0335f14c6f185504e8246219aaaa9d8bf42d4a515ec024f09cd1117b3a0d96e8cd8ccf80b21da6229889b7e7b465c3e33ace29393fe9c6f7488cf58139168f50bf6dc7683f28b959b0c1c688865899e6a5409f8539e891888328602ee56a3baf68a19584c6a2437a8c3223bcbcd75a21943439879243663cb32cedb180a9235be2bb2f4f967f287757d442b62252556f6bf93208e5eca4f0b68c80478161cc05a5a866b243867cc0cca8eba883558cf4e39be430b687df078714b134b5c045058169bb2766b815bbe97040b043f4ae55fb97b6a1cc603c3a29258a9549bc447c627cff0a040d61a312f0493ea8663aab5b0ecb330ba07867ff1000cf1881627a87a8030485968e4d0096f0a243e2265458649ad64781daab9865aca9db8cf14d9375d2c05faf9427da35016ea6594cb2ad18069db9351e9113cc34213973886c2c5550c51ad18bc0cf5ba75fdd6815cf916391836afb74ccd423df47a15c9d239d36cb881eb6b1904bcabd147ab40604a6277905a9c11f7a5bef1b9dd34160503154f066bbb07466f2bb9ba935414e9cd40fb7f26570c599226b21b12dc786f359736257c38b8b102b92220cbc86c46660a81e780c9d48ca9c4bf3652c4f9c0092d3a6255c1ad17238e5eb1cd8b03bb8323a79d52791f7a070b96b06e9c6140991ccbd6b4c10b0b686b4765664520217298cc156ec99974732ffb07aa72f3acd3718cc0c293b84738d9c16331cbb97508c50eb43faf355c7f55bc92585368395f0e3160588a955ba77e44b431131d9edb13d385e02576f74891eaec6271a2087439584ef9d8f60403757c2dd061cbf5054922ea240803b79503f9bca2d83ca69a791ccf1ed6224256b3878c0c57024c4c317674abe8ce019c301a2a080e627048df0b6813de5a2641aa47b776956bb866416e1791584781cbba33331bb6b811bbb06dd43903d65606c8074447054464cfb6f70876246eae8a5447cc48187a1af6bba938bb54b7144b63aa59e8f941e2b373a9e205cfe589421bb98ab4b2afd38b3df901bf04cc58b3802970882b661169859a1135cd795b3445915ad336bfc1b80379d7bd877449c5c46bfb899d07f0be1eeac331d15f0c6a7e0d53125127878a701bec01c190a8a24f747334b5aff092061988a97fe05e9e54cdb93cbb83fc5feca0342118293e7a91fb5165b0079c4e774979411c5da1596614b1c1ab3fe49bbc1ebb27c12141593a9eca9b821f7508816079dac131e1b8239dda83b6f1b001e71bf92290080a77c44837cd3b3c21c8c1ddb18626a3a739b061e4c359bd6b72ccb80ca6346badea3e7c5137408372076593c0999002555a1bc748393b365d86250142719717cbfad33187a880aac13c23f4b44daa76cc731beac7c72ac4144efa0c2ffa64b22b23a13639d88ccbc8daa0546779fe58267eb4188bb33f7e8589d48218569811f9bcc9507bb1905055b2a166625485f59109add09304210b9b359b7929003906a2daf6c362064012611589954acd84689634944953517f0679f52ba30d978deb56cbcb691f16da1ffd6c3e542a1da31c1493ba6147f9c00e331229d3cc06a1077adc71818abaa1c78da4cb0d6f24160bc67dd3530e3de2a0adb27e5ec72304c774e8a99132b244f3b585c9027505729c22040ab42209b696998de3070be95c766624f0bcca1a1b95d4d114c0b0bbdad0010a50376315aa936acd5d938f49ca0edd754c7a262922b683c474059d32220fe3878ea3cd5052cf3f4a2925387e1d643484bb7b4e0b0955145342ac7bfcc48556601a48b73ccfd906c71b5bf1b1004a6c39d387a6f2b0c943060cb4d0cd46a913aee815365b3d954809175625af676257d6afee61b36a4839782457c1153fdf07b46dd1c522c561446c7071d07fb511498e755ef3d23990c726c24860caf521adf04a496240ee63319c3596b4f9257ddace19d0bfeb050f35727ce283c718b9664a377aaa247104fa67b8b521c16a2a92b8959ab211bada37582701cae882cef75047ab8bc9423cab7269a3a404c300a16360660c5a0aec45a59345391c1800e4c10a0b96c482373601ca3510cca0d5932945e997ad773e182ab652243b0e7438d9a7c82a0a86669b29e5b67df4a50adbb625741a3db44a516e82b0f4faa3019167fbe031771a9bbf38991510b594847be919c23e131331c75f69f950a8f12fe34a245ee7be0ffa7b0fe7076f33547fb94e9416a5e2d07882849bf3eabe806c8bf0687ad6a0722ba079d9d2b57e00bbaaeac7532a69ed8383471bb6b73a59b8364e385c22148c8b92c0335f14c6f185504e8246219aaaa9d8bf42d4a515ec024f09cd1117b3a0d96e8cd8ccf80b21da6229889b7e7b465c3e33ace29393fe9c6f7488cf58139168f50bf6dc7683f28b959b0c1c688865899e6a5409f8539e891888328602ee56a3baf68a19584c6a2437a8c3223bcbcd75a21943439879243663cb32cedb180a9235be2bb2f4f967f287757d442b62252556f6bf93208e5eca4f0b68c80478161cc05a5a866b243867cc0cca8eba883558cf4e39be430b687df078714b134b5c045058169bb2766b815bbe97040b043f4ae55fb97b6a1cc603c3a29258a9549bc447c627cff0a040d61a312f0493ea8663aab5b0ecb330ba07867ff1000cf1881627a87a8030485968e4d0096f0a243e2265458649ad64781daab9865aca9db8cf14d9375d2c05faf9427da35016ea6594cb2ad18069db9351e9113cc34213973886c2c5550c51ad18bc0cf5ba75fdd6815cf916391836afb74ccd423df47a15c9d239d36cb881eb6b1904bcabd147ab40604a6277905a9c11f7a5bef1b9dd34160503154f066bbb07466f2bb9ba935414e9cd40fb7f26570c599226b21b12dc786f359736257c38b8b102b92220cbc86c46660a81e780c9d48ca9c4bf3652c4f9c0092d3a6255c1ad17238e5eb1cd8b03bb8323a79d52791f7a070b96b06e9c6140991ccbd6b4c10b0b686b4765664520217298cc156ec99974732ffb07aa72f3acd3718cc0c293b84738d9c16331cbb97508c50eb43faf355c7f55bc92585368395f0e3160588a955ba77e44b431131d9edb13d385e02576f74891eaec6271a2087439584ef9d8f604037500000002d23623d701243a0b789c12730af4acefc5af3341f02540943d955b801e847ced5369e34f6cd4c173bd8581a22b72719d0b2f597fb5c0142954e2e8815ac080010000000000000003000000000000"

def prekeyFixture_one_one_time : String :=
  "04132c442be010fbd57e72603328aa76e71fccc1503aae219327d14d9c9993f472be63d18c035eea04353a20a0aa859635ea0f2bb265a3e89509451b53b7c168b9000000019565bb39905cf99b938461619cda94cfdf7dfad4d290c583626d2cd0853140cbcb693cf07d8381ed5723b78ad1f350c5053ddb24595d1c5aac9bba532493830400000001000000021584946c080414f93ef6f619463e19742f3417ccc101eb655f7a7e2b25d9955300001280c598c860c7ce63b78975733856a63871127309993e24da8936bc7ebd41760232804a4c5a6ada66124c6a3b56283cab29501554b45712ada8c65d379ea698cefe136710e32ac042b48893578b7824c04c10d6f82a6ae55c4433b7e29258bdec96cd7193dd589cfcb0cad53a4bc7b352e4729b519731c8396d592937f0dca8ad0034a3ea26cb4b1c584775f727263d35709505686ef24406f9ad3ec4071f56575de47da6f83bd0467351771223f49e0d434b6abc8afed77d1d246ce0821c1a798d829c8267452fc4a68ad3dc103e028c77346e5bca9bdf0798b47660db073c27f91780d35a8710a5493a1921f2a8b88783f9e66640e3a06af982ad810b55a11901647e94720e60123b55e45da9025b1f9a5c5a6c219c9567e6440d02c64c3bd7972452807984abd7216ea3aa4ba2e29f5e90b4928287f5cb5253b50db3274de9b836d8ba63c08624d958cdb052468f6b529e1c5622b092b6305375d373a028c691c2cd51e4c0bbf4756dd337755200d9a553e627a79642350ac07f489b0c2f524ae8903513498c11c933b0b361703cc0631a2a200c1fbc234338f2ab0f1a455aa9b4224385a8ec1b53c38ee582ca8b2160c5c1a67828b29bdb0a76968bc785bbc4782c324226fb0c6378c91cd0c842cf9b8ec00503d40738eebcaeb3338e77f49a13d5708eb4c501ec45a5085cf880aa1ed16e8294c0ca281b9bf1aeb85860678097e0f6220765035de21556082aaa155fe88973c8124d23d773c7c4af4a454b9f1461814355b1098694298caa4a81e957a182b6259f73494c515a7a1b8c92a98588943417a89330aaba21eb3c95e2c8c55698be5857ca137857d96285bb4cc46104e3e4b45b9c5cb6f2cf30731a39cb6fe9110a488ca1d03775a3d76026ac5f20092307337206913c77958767922a0f51479581cd7b5283d2571ee789387453bc9f40be648165c53290bc9914330c263e8733d99a01d68c4adeb985b3238ad22435d6e67f4a533ee3a9cde604cd21abc5dba07b2aba666f914102c6a257e07c9d25220df121c0f766058c4ffce4c2de0bbe975b6a53935e1ca44de2d75fe3867930796fcb4bc8ead68922916288c6692d0424abb3bf35f56191eb421cfa4a333a6f87a4a56fd7c81be9ab2b88405f3293a290cd2a55b1a9d0cb3170035bab39494a2ca3422e2118295fc4a870727e67bc8891e24796c6b9c2a32ae4770071cb2ab991c01a23cfa459016c219210b55fd66456441a17f3c76934f97fb2f870420a61be9a0e59432480fb1152c74cb3034f37f32cc8564ca8697ea4c30d0731742edc7881b4c2c01c2b89036c2b679662b3067c56c793b678818924cfa0326e3a545fc8ccc09a7dfae926cc0bc029315a9cc2828008ad486a8887c554e546010e4aa828fb8e0c0b37afc562246c9d1c181291017b84470ac09a2af7e972a63ab580b4ce4b105c636a59ee33cb2c821b535c60e3e7cb8b3b2ca28a1bec695d0b4ca334d63855a27cfb13395561ce05066dc44c58e694266dc0027aa16030c0080fd8af3197afa253432039cae2d51296463baf0018a0653a59360bd1bc05aba02d4cd6a987042f936029f7e79605c95ec287927da32f24db4b3ac11ee2c0abfffc5f17644024cac8854c973735a8ace71e2196ae70412ab7d4bce9655cb9261539b416deac24e764bea81bca65f1c2f011072bc916d50505d8179b7ae488455998b486197adc7770b1a918e177d94a5d237939daea27696330fbc0a65da8c31b7aa035ca0ba09b9ea19686411ba4552bbd40646972f82fe89544999142b627cb200c934f746771a5877ffaa153b79c8d822109ea732b4c1fbe20af2482aa2f9caf598472ecbb80bc715ef501796d3569dc671b2a7c1f3d96338b624d9489b47cd910f3a65c6a65188ce302356b10f3c51dfd87527052757ec0a98085b1d944b86eb3120821ac2bd4c09477518b96cf0269c0ec1948c6bb5bf3704a4f7c69d5a0534c9c5388d04029610630146df8204c6ca669b0734822681822d5c757487843993a5d522a093c149da8030324c8710b3034e5887f29ce31f7180b9283dcbcb9831b23b8f22b0d469d9567b043b7ba772c1009a23c39aab612b94dedb276145326a9b4989be89867e7a9780c74517ba1472552fcc810763c337d130552ac14d9060661945336f86f2016b48242910f37a66785bfd9116aea536a00e81f903b35c0884277d3c3c5a8cddac92218d687508b88e78c3253a16694a6913d6891abd36024d087fdc012922b35c96305e11baeea5c044f6606ca361ee9b22135849b7389acda721844b3c465730efaec7b5336aca9468e2c861fc9b9cf4f94b3d950584959013306c54358737ef05b379c7260f9aa91b81d0912bd7a721a08700684f319a7d73ff051b8e567028a06498603305f31ca2da96007085844703d55a1a32fcccf5915a12e74b59accaae995ba917089bca710cb4c2ef0b4bec0c826a5817f908667af0730606039394bc66df6c22bc0b7f0845e8ae6051b68c1406bc554268aebd5c06e1947df3b38a8515b408b9bab54a3466763bb8c39e5ec02e227a339f71e0cc17b114a586f698b834075578a3d745a9c26c8ab424514489673bfc72eede348bed92c3211a6f32122bc4b0017f1754a4bcab54a5754e3154cdba812f4bda2812652b697af803c621940f748ab41692d43bc2e14a4b49abc53ba48b82c5a5829e4b226e190e57770263b8113f39ca5a37a9d4566528bc716d1433356276fdb43c77a626c2bad375b0fdd06282431262087bab8270ee45780bf030315e5be3d04a097981b3a98440b921207a0a9828b80773a616d32b4b4c97b9ff8b6a4c23d2c0b5602f60bd3c52dbe42be4aac2c774b8b75d5470193865d818a9bd5413010afb34132a29ca5655a75033583415c835e2a606b49a8f0d20fcc213dd771460a676aa656b6e882ce18044aa313172e030a27e697d47717c156cd10462345e934f6b3a05cc36191f3ab2b9950daaa7e5d78a44a975a217a9821d15b4fe2413805c05f7c3b80f71bc7356176c6b6730b84d1b84db0da7b3140af447218a7e7668d6969ad5769d3845708e21520733d5a2486a80383cfea57ae731d80043196416a2c291931da9e1092691f33b0a94c7a0d495ab01b5bae3743fe5660a792163bd329b4ec8079f4818ba37c96d3aa0b171819c53465f4bd1ec1846923a00bf53e3f7425ee462d36286b396351bfb8bbd65b741d6805957a5b2b720f9908bd497454256c7046c13a6d4431e1f7ae1322128ae140a7002df7fa9bc16587d4f3c032864ce5ac97fd4c20e205a439b77c8de7a76667ca176121d498160f772d5814bd60f724cf26b00a991c8826386c570879406fb3938ab43677a434099425818a1451677576efa92471a8cfb7f4135686bbfd51b1a681327d5ac568c2aed10b45e509015936351195165f945d0f31b16328088eb551e721a3f995529137793ac91fa9739f2d232845da7c8ca92759286b49f56aaf35206e2712ec0479214418e305a7c1604fe4e52aff048cf7c740ae430b59b17a5e368f7321976e06674a09413763cba0933a7358c68871c55e22cc1e1a47cb8bad719145fe724be0f42d8084bd70096aeef46f2f439b5758326cbc90bb1abf65d5a24dd08254f73fb1104b580b8460d54cf456452c2b84b9c999efd8be732c37f910026d34bba3e964520c2eab6b4972c63fb02950a56c8f81c102843697754919cc339da0d1b0a4168f1bf8b948eb90db8b949f72b610322ea5f70e40cbc826f40301b291fc49a0401720cf8352ab7a40cc838573e862242a7f9fb335a2f1130246c477dc885007410a25cda8aa8ac2e52db43151a7d29b68357f9a0709b6d99f8ab10ea9fa651ad538bbb78b70447d3611c5d9b18ea13028bfc294c63284fabbcd45724ef6e53814a70c9a8657fd509405f553aea21440207c6a8b84a52b5b2f11c7938bbfc4d4343957589a123a6300c2268c605edc665f0264bdb05a4102378b52a1b75141de4a83d9469556a57e8db685b3f15136b320e75574ee5001e065626695a8e2dc80ee7cc0411540f33c79dfd0beb3838caa5962070b0081e67f18b89f132b4b3f612b09b82268188564d60a23b93c9ff5259c7acb21552190c702690c0b9e381960c9608d379cdee91ac4f1899b0326f8179bfb67904c978436c20b4c5a037cb65a69044b7e893e392b43cb289cdc253c13174f564a69775045128759d8d4bdead5c50389912868196eda325046b43946b5b2a1699618ab9e1c24c6015564f639f49bb629118d74da5421d9670a8b938dbb54d21515f4f94534373bd209b1763457f58b39c9f5b53437752a4f89a35a48ca0936c04264c451bc03fb8dd7bd6b6f1fc269f9e27617291d1613d155da48b17881ebf2ad730d6bad6e88c96d9aefbb0d212ea852563e99c290258eba95ae0014cc9577740991e499d449363f2395ea0fb765bd22a46161945336f86f2016b48242910f37a66785bfd9116aea536a00e81f903b35c0884277d3c3c5a8cddac92218d687508b88e78c3253a16694a6913d6891abd36024d087fdc012922b35c96305e11baeea5c044f6606ca361ee9b22135849b7389acda721844b3c465730efaec7b5336aca9468e2c861fc9b9cf4f94b3d950584959013306c54358737ef05b379c7260f9aa91b81d0912bd7a721a08700684f319a7d73ff051b8e567028a06498603305f31ca2da96007085844703d55a1a32fcccf5915a12e74b59accaae995ba917089bca710cb4c2ef0b4bec0c826a5817f908667af0730606039394bc66df6c22bc0b7f0845e8ae6051b68c1406bc554268aebd5c06e1947df3b38a8515b408b9bab54a3466763bb8c39e5ec02e227a339f71e0cc17b114a586f698b834075578a3d745a9c26c8ab424514489673bfc72eede348bed92c3211a6f32122bc4b0017f1754a4bcab54a5754e3154cdba812f4bda2812652b697af803c621940f748ab41692d43bc2e14a4b49abc53ba48b82c5a5829e4b226e190e57770263b8113f39ca5a37a9d4566528bc716d1433356276fdb43c77a626c2bad375b0fdd06282431262087bab8270ee45780bf030315e5be3d04a097981b3a98440b921207a0a9828b80773a616d32b4b4c97b9ff8b6a4c23d2c0b5602f60bd3c52dbe42be4aac2c774b8b75d5470193865d818a9bd5413010afb34132a29ca5655a75033583415c835e2a606b49a8f0d20fcc213dd771460a676aa656b6e882ce18044aa313172e030a27e697d47717c156cd10462345e934f6b3a05cc36191f3ab2b9950daaa7e5d78a44a975a217a9821d15b4fe2413805c05f7c3b80f71bc7356176c6b6730b84d1b84db0da7b3140af447218a7e7668d6969ad5769d3845708e21520733d5a2486a80383cfea57ae731d80043196416a2c291931da9e1092691f33b0a94c7a0d495ab01b5bae3743fe5660a792163bd329b4ec8079f4818ba37c96d3aa0b171819c53465f4bd1ec1846923a00bf53e3f7425ee462d36286b396351bfb8bbd65b741d6805957a5b2b720f9908bd497454256c7046c13a6d4431e1f7ae1322128ae140a7002df7fa9bc16587d4f3c032864ce5ac97fd4c20e205a439b77c8de7a76667ca176121d498160f772d5814bd60f724cf26b00a991c8826386c570879406fb3938ab43677a434099425818a1451677576efa92471a8cfb7f4135686bbfd51b1a681327d5ac568c2aed10b45e509015936351195165f945d0f31b16328088eb551e721a3f995529137793ac91fa9739f2d232845da7c8ca92759286b49f56aaf35206e2712ec0479214418e305a7c1604fe4e52aff048cf7c740ae430b59b17a5e368f7321976e06674a09413763cba0933a7358c68871c55e22cc1e1a47cb8bad719145fe724be0f42d8084bd70096aeef46f2f439b5758326cbc90bb1abf65d5a24dd08254f73fb1104b580b8460d54cf456452c2b84b9c999efd8be732c37f910026d34bba3e964520c2eab6b4972c63fb02950a56c8f81c102843697754919cc339da0d1b0a4168f1bf8b948eb90db8b949f72b610322ea5f70e40cbc826f40301b291fc49a0401720cf8352ab7a40cc838573e862242a7f9fb335a2f1130246c477dc885007410a25cda8aa8ac2e52db43151a7d29b68357f9a0709b6d99f8ab10ea9fa651ad538bbb78b70447d3611c5d9b18ea13028bfc294c63284fabbcd45724ef6e53814a70c9a8657fd509405f553aea21440207c6a8b84a52b5b2f11c7938bbfc4d4343957589a123a6300c2268c605edc665f0264bdb05a4102378b52a1b75141de4a83d9469556a57e8db685b3f15136b320e75574ee5001e065626695a8e2dc80ee7cc0411540f33c79dfd0beb3838caa5962070b0081e67f18b89f132b4b3f612b09b82268188564d60a23b93c9ff5259c7acb21552190c702690c0b9e381960c9608d379cdee91ac4f1899b0326f8179bfb67904c978436c20b4c5a037cb65a69044b7e893e392b43cb289cdc253c13174f564a69775045128759d8d4bdead5c50389912868196eda325046b43946b5b2a1699618ab9e1c24c6015564f639f49bb629118d74da5421d9670a8b938dbb54d21515f4f94534373bd209b1763457f58b39c9f5b53437752a4f89a35a48ca0936c04264c451bc03fb8dd7bd6b6f1fc269f9e2761700000003428b517a63fb157a071fce17b775ea9009940fdc4e14302e87fdbd104a8cb2568b3e0312ebd5091a5a59bc971d9726da7714c5d895589e83d066341218b7f907000000010000000400001280fb273758a5c23a90129de14c5607c8ab95b160f5c7f5492b5ba3866289a6df112e2f2339c9838483614a2db41e451863e543271acb227f498d09469c6539cef2a5c9fd188dffe85c6291b4b571350cda23f0c888f78a46649101edeb10b0e2981c598fc19c35be08364de8b602e22480e5247cdb15d725a095d356bf2865daf201e2e5a48a144217976ed7c11510a1346ffa8761573c0d4b4a82694a7c2a48410224c2c151b40b7f1886acb90b87d346c9aea6a55af608ad60cae6480cccacb44aa08330c60e13170b814c00060aa0f49a92bb7b17ea561da16c9825757d9d9ba35e0766f8d31b9f5a3c03f907126818f4339c7ed5cbd25b56e7854710c27c4e808eada42b0f488fd809cabf152f98869f10c45e34c15117f5c1cc82256db1cac399076219493ac5b9c0e9a22e9ba2046c7ce89c738a848720918531941980052bff6b174957b7c0dc9f5333176e272c51f36b0b030770fa0ee69236d64493f8f0857d2b8dd1d827e2b6127b2c676f1505ca6180f28a93de3c0571e355be40ac784408fe9b7568f0c963741120f5b90927559c5a1cfff462c854b68c03c34410afff629e0592607cf185d9b8aa7dd6b66330503591761725c910b1aa10d2698995ba1d5acc26e26bbee582c9d13ed0023e1bea725bd9877a9779326ac2861923223a0d4f2c51a2322c88400c63944e7ae7852cb31f01293cbb3c0a1252b1cff102dbac40e600baa99bb7ce9aadb2838dd1921f2919390d0371e2db8988f08b555096bc5b6cc3a287269a303008ba3a10a69de3948e91b58b172daf4514a9c18a413450151459fc2979605642b3584270e518095793a13914989435c2738dc6e910711ca465d0ca94f7104a719e627c72292a57a6d8c99e4340744cc6cc7a6704333e9a5a5a9eec1b3a4175febcc9aecca5bd01a22fb51f04534cb4978851171c2f664c21b0c5ee3879fb35667e4cbc4253a741c66a80cb7a7e2659b48253b1cc289c904632628e91032810d9b1cc5517d5b554a9d7ccbf3a3c77843436e60fc2296939f77ad12519a2d755bc811aee8750a85751c008bf02531d9c2966c9b8b94131a1e55c1a71f0afee0501742c9e18233db91415921078b546c314c9a3a0e9a844929db8467b78fc5d0f201bb24c024555c91b58b92f95611f3c6af077afe1a532be56598d01792cf07a60f80eb63aa1ba04b76df69baa0b49fca2113d49568c83b75db21802503c93ab49ab403008823109c0a6294c2ca7ab934f49858ffb5b21d2850b96b9e4c9a07de35d8ab686747b2c0d660f20f2c4067147d05b75ef51aa5bec13443929b76814aa60c950f9c5ad2288219082683aa7e4b7be4026b0a28c12e1c262141c1e8eda9fa1bca6c41638730015863a26de1a92783ba1db645cc3ec139f47be4345be64eaa774636109912ac80c592c609848f90db1a0ceb65441ccb82fbd876801e2b464bcbd84c34b7865679fd0729f372bc7c80645d048ccb15e23231c9c213e9c150146793ec801ca5f5a6d2ab19914812bbd856af7fc2771a9234cc66e2d28009f47343ed42e3d42cbe5855f83a343cff34912a638284b1505f72ea8149e46421668549517032c945ab6c010703d72be23e9c7ecf133cb643101c18e456aa68d92251d959c2a8bc6953c995a584d0f77210ba829ebd32442b398f10106e2436febdc065fa75fa5a4570fecadd4e0a32ac799c0239566c1af921861bf2b0cd7205bc841a45afc7904a13151e55151449cbe36a9d82005bad52a0e5c3829dc2f10f7900093378a0a5295624c3b14860b1955cefa299301395b496b66f05190b729080040154b89e96695cd286112eac6fd358ae2325f84ab75606bc9d04008cf8103cb8b9cf53a9e2bdca8a76508e16058ae5258498493491c96cc113ad3a70f51c6c8cc3622f6903b9e6932cec259e51953157764b5e396a2526fe1941f53e622ce865af974679131acd2f426c38038029a572ae72bb9aa7bf105034a0a18d4c17b0927c7ff0207f83072d3072210c6c66051bd85b038557273c8eabf1085613e235edd629e6d194ed64c8e60852db0d97db821386927b2aa3a46a22a78815c312b71c147b753d4f8bad41c6e446252d193b287981ca7b0bc3504b21602aa379892cc9ccd99b54121337c4b4052da4174b2988403d64a6feb691e8c4ce03924f3c8380017ba8f971e3a4a9a3e886895d77f7eb7011b7c3374258201189609d67cd71ab3afc61e6bf0733d82a34476331cd8687dd0c9e76b03d808a3a795871bf02875379a704741fa691545247225136bc7db7ef423c1db74291b6a0d5bcc32743b50770588a72b4f9294ae266755a8a4a11cc81e9d705a17e27c1ea000382b6c6a675e0caaaebb1b72ebca784e30c397092d13e2bd6c37b5afbb76f7d32293d20089270446451cccdc4a4d4ac558bc6eee0a519bd89598520a372397f0555c9d7c50de2a1b13851ecf65bd61380fbd1cbb720173fbca7c0a8cb57ae008c0705ed64a548e25ba34b1225c25cf8951253077787a80ad3b7bcfc12390edf9b6bf30a52cc1959969505ca9614a8731d425470ba00bc9e34289e921e2d49190665d8923c9442c0aa4f82e90e40802c5500591344fa55067b58b0f2049373b1f143c2759d31d9a57724c4846bd470dd5f7b28095c236cb6fead6bf5a9aab98f13a1b475b4dd90428a16a44c07bdc3a471f594bdf2cae3214385eb50757d87c1e02c042d9077897692d11838e6251cac78e189a518b6a6001aa57a307a16378203dfb0eb9e13e65bc7523c56108ea3795d2ba02b87ce1c574c2a619e9095ef51381973493c0056306282da3bc6c82158673b198ad725a8536272f17245a5332a91b609c263a17fccc8ca4ac44787ccb4202b304ba1b93be46a81c45687824f506ec478faaca68c0779ff0817f7a865402e8b928a821ff4680f6e926df691eb560bab4793f09a61c3ebab8ce6c5f7f56103202423ba2b561a57b25002d0c5c1a16b37d3412befac33e6a407cdb5096ac41c3852aac291b2b30b7ad5bc3070f4083d13146a2e780e34953909182558b313e02a0e319472c23048c1a06f60c3376666264bc727088424f22ac0a88106f12947c6a8dc76cb490366fed7a26d2b96ac1743a033068058561c6f2c94701b7df2a5ec5286385c2cd4437ba6cd20568cac100f73de5f999f330262334750c9446990a31c9765e2ee768d9f398828c2b3384411411c02f69b1e2579655a0c3369352a6e94348e40f7a6b3d02e27873e40b49a445d8d70bbbe35cf0386b3a856edc188e53c64fa2c47decebc0dfecb3271104f4992168818be2b73c173b9bd42700a1e381d310c33f692e98604cecb442c717cf332006d2d35ebddc8f623b9c6297060a2c19050081c2d02d47ec8c55cc471c569c504099c3f42fec451faaa38fd573358d9117cf356314d82f97a6028eb2b24978b46fa5bf746051196050c5f325966433f86518a5f79fee49a3933424e4184e83fc9e4c10781091b9b0529f781ac1f84cb821e000d45a9ee3479942a95019f39870b0224b74954108bdad1b100183c5b1a33eb42676dc259ce41171cc7552de989e5dc63f65177b0bea0c21dc7ea2c51aa553894f1b0258d3b482347b9e045a9d958d1cbbbc7617548d80cb821a5f4d5c3367381f34e84172801a60f136cb929c1cf57bdc6189450ab0ade6ac3278bf78d19700e968f7b472992827ad819b3c9b8aed878b2587283045189a572f9c28114a9912a650beb350c72402a0403727fb570bfdb6793e8523066c8161d55ea9a07ba85b8bd092c10f30700eb084408a942c30bcf0f207a50b8f4b15794da933547c57a5063ec94442cd5145723875ccea8707f8c258452bebfbce1adb9b1d3cb1203078332214375272dc9c11b001be22cb01f78129367638a544653aaaa6382479dc5a1ee6d0aae47a93a302852890b850839f68432f04239161aa68db735b629432e8774a20c90eb52cc521820b8fc50017016ea35a1dd6c0cb23f894f95876aa39a535c1a948357b8efc1f585876092a2eadb11e9c6b7f86308aa36214aea599315303289b6cd999b57bd817d4ba99d9f147dfd96f6aecc4d6f5a988e55db0663bf5b446699ac09c109546bcce0b070569d49c06f4944d826b290c0ad37a79827a4964558ad5eab675e69a1584025fc07462340f1f47aba7d6aadfd97fd5711e26d765a1fb137720c0d94304af7605a25421373473e6498e2203360387548cdb05891154f1b61ce7d69b14a91d55b20e8c69a28235ba510a3e9ad433cfe6830e14cb245ba7f977cdd6d5cbd9e061929051b6f526798b89e37380cac965ce8a66f86a08982a96f2bce4e2a7b124893a55f73e967509f223427a348b979c99a141ff62a5db6d5b6e846a4fee2173f6eaa6f8dabbed2bef5a8422b67c2e16889ecf84e21fd4b62a673e883dd92ae366ec16dd5521b61655969ff108eccba9e5c992dfcba54b16ff6feb691e8c4ce03924f3c8380017ba8f971e3a4a9a3e886895d77f7eb7011b7c3374258201189609d67cd71ab3afc61e6bf0733d82a34476331cd8687dd0c9e76b03d808a3a795871bf02875379a704741fa691545247225136bc7db7ef423c1db74291b6a0d5bcc32743b50770588a72b4f9294ae266755a8a4a11cc81e9d705a17e27c1ea000382b6c6a675e0caaaebb1b72ebca784e30c397092d13e2bd6c37b5afbb76f7d32293d20089270446451cccdc4a4d4ac558bc6eee0a519bd89598520a372397f0555c9d7c50de2a1b13851ecf65bd61380fbd1cbb720173fbca7c0a8cb57ae008c0705ed64a548e25ba34b1225c25cf8951253077787a80ad3b7bcfc12390edf9b6bf30a52cc1959969505ca9614a8731d425470ba00bc9e34289e921e2d49190665d8923c9442c0aa4f82e90e40802c5500591344fa55067b58b0f2049373b1f143c2759d31d9a57724c4846bd470dd5f7b28095c236cb6fead6bf5a9aab98f13a1b475b4dd90428a16a44c07bdc3a471f594bdf2cae3214385eb50757d87c1e02c042d9077897692d11838e6251cac78e189a518b6a6001aa57a307a16378203dfb0eb9e13e65bc7523c56108ea3795d2ba02b87ce1c574c2a619e9095ef51381973493c0056306282da3bc6c82158673b198ad725a8536272f17245a5332a91b609c263a17fccc8ca4ac44787ccb4202b304ba1b93be46a81c45687824f506ec478faaca68c0779ff0817f7a865402e8b928a821ff4680f6e926df691eb560bab4793f09a61c3ebab8ce6c5f7f56103202423ba2b561a57b25002d0c5c1a16b37d3412befac33e6a407cdb5096ac41c3852aac291b2b30b7ad5bc3070f4083d13146a2e780e34953909182558b313e02a0e319472c23048c1a06f60c3376666264bc727088424f22ac0a88106f12947c6a8dc76cb490366fed7a26d2b96ac1743a033068058561c6f2c94701b7df2a5ec5286385c2cd4437ba6cd20568cac100f73de5f999f330262334750c9446990a31c9765e2ee768d9f398828c2b3384411411c02f69b1e2579655a0c3369352a6e94348e40f7a6b3d02e27873e40b49a445d8d70bbbe35cf0386b3a856edc188e53c64fa2c47decebc0dfecb3271104f4992168818be2b73c173b9bd42700a1e381d310c33f692e98604cecb442c717cf332006d2d35ebddc8f623b9c6297060a2c19050081c2d02d47ec8c55cc471c569c504099c3f42fec451faaa38fd573358d9117cf356314d82f97a6028eb2b24978b46fa5bf746051196050c5f325966433f86518a5f79fee49a3933424e4184e83fc9e4c10781091b9b0529f781ac1f84cb821e000d45a9ee3479942a95019f39870b0224b74954108bdad1b100183c5b1a33eb42676dc259ce41171cc7552de989e5dc63f65177b0bea0c21dc7ea2c51aa553894f1b0258d3b482347b9e045a9d958d1cbbbc7617548d80cb821a5f4d5c3367381f34e84172801a60f136cb929c1cf57bdc6189450ab0ade6ac3278bf78d19700e968f7b472992827ad819b3c9b8aed878b2587283045189a572f9c28114a9912a650beb350c72402a0403727fb570bfdb6793e8523066c8161d55ea9a07ba85b8bd092c10f30700eb084408a942c30bcf0f207a50b8f4b15794da933547c57a5063ec94442cd5145723875ccea8707f8c258452bebfbce1adb9b1d3cb1203078332214375272dc9c11b001be22cb01f78129367638a544653aaaa6382479dc5a1ee6d0aae47a93a302852890b850839f68432f04239161aa68db735b629432e8774a20c90eb52cc521820b8fc50017016ea35a1dd6c0cb23f894f95876aa39a535c1a948357b8efc1f585876092a2eadb11e9c6b7f86308aa36214aea599315303289b6cd999b57bd817d4ba99d9f147dfd96f6aecc4d6f5a988e55db0663bf5b446699ac09c109546bcce0b070569d49c06f4944d826b290c0ad37a79827a4964558ad5eab675e69a1584025fc07462340f1f47aba7d6aadfd97fd5711e26d765a1fb137720c0d94304af7605a25421373473e6498e2203360387548cdb05891154f1b61ce7d69b14a91d55b20e8c69a28235ba510a3e9ad433cfe6830e14cb245ba7f977cdd6d5cbd9e061929051b6f526798b89e37380cac965ce8a66f86a08982a96f2bce4e2a7b124893a55f73e967509f223427a348b979c99a141ff62a5db6d5b5df252766ebed8cf207effcfe196e728a9e766c63ca5a42d5954dbdc28ba61e6629043e101d296f03e935b12d0e5f63077e8181726cbe8c6c2d30ef14b037b0800000005000000000000"

def prekeyFixture_retired_signed : String :=
  "04132c442be010fbd57e72603328aa76e71fccc1503aae219327d14d9c9993f47289d1160df60c641f9243761d2d04afc0e9eae9a697be9655fde149688debfaa300000003fed34b5338f53b0e56d8ec2cdffbd21fefa1abbbe5fca1a85b6f4f5b880b5eb06bdff477d66d8bfd58c7a5387daa563bb0d474c05da43e59d19471dc390eca0a000000000000128076584152ab318db5ca7c06914c0b0e11ba0f324377f4f299f7352aa6257ba306a43e412b932cbfd156493e8501cbd812f6a81776b40481e254b3f80c64f2c53b2108bbac35c15324ea1430f81c2f19c8c1fe140760b2336119bd09fc9e54b9abdbcb06b67a4df6d614ad1c9bb91322e0176e317380646b2500362f069a861944b817cb3a7826ac0a268910d74a121156a6a0787f2a282fe23aefbc7ea8d7a5405742c4b94645ca976fc0191301422e05c4f9b9ce30e2cf9afb059a190a956cb3fb932ec23052cec49a6c9b2968688d29daca041c87bf5c49cb58c76d754ee01052b5b85e4cf837664cb3ec80aa49939c26c57c7ef87e888018c92c50054267dbd346e6353ef91b80644209a866819f894e18d6b033b6605af11142373bcbc467dd67a3f17a7c944298009b1fa195c6753364f06c7de8d70f04d487c4e043c6d545025716734c5c65174a99231846302d3aec3df02075d0c0c6e233cb3a060f58909e280164fa585b7fea2abb592bbfd4285a2c2d5d1792a79518f2414c9fa461864a1aaff7a333b361e5b51f234aad16a919e0c05d1cd815ee015f850cc2b92309ca3a2aa3366780f653a50382b9e5bb16e15e24233ad33728203b42297a2208e0b6fd989fce94283a4319d74cc88810248350c96a7b823919c85f06cdf1892bcc4b4cdbc26d00e78aab3b3a19406b68b112e7d55fbe34a7dde23693267044d363d71ac767021e5d818af6d46cf34c153778c2b9292e084b2357152cf208914ac5c556152e8e1b0ea911b926345aa75a36af7b9581bb15eb071d2e045ef0126b59abc8eb8091a67c617c4a25c00a1268d9044498607fb9024d6411fef21580ebbed40189d7087b70e44102d138973a62758ab7b7b472fc8a639aaa172213b8be025fe3357a11a6a0d23ab6400327a3fc0fd9a3393fab734f1246a763a7b8f15eb5a5cb1548c83e9a310759443c10b04d4145738534d41975322b6ab7ac4f12b8c0e0154ade64542799c91c157a7cbc901dc877be04034a5407b2512cdbec1acd2b8e11b0b1e0c21cf724038fa505d3b115ff24790876286aa4107de768d3b11ae13071aeda718b877f78b76b9d3511b1c20219b23eff20853d55ce61856fc84c7b195cce06755c6be504546c8af078b829a3b68c55771e66109009506096a5f2c4c7c8f25f6d6c40bf3341e4a271c00b513db917678449fae298284a7818f912e281a0e6755170828b2eb36908d244998459c23440bf0418d51bac593113ce3cbe7494a501e20d9cea3f3b1c9646b57558e410ee08a3fbc8627db221e4b0b6830b6df91469a3526adc030c9df0b5e6e73c3ddc7dcf681817a1a8311a69fe7ca948c728e9f7ab814a745ba58fd06805171a4b0e3c564470b6478c5daf8a6a9cdba2ef5845ea5439b7912647630828042768726e0a389321eaaa7ef575066bc7423283c13402fee268293010265566e6a69d875badb666cb8fda37f19223a9d77fec0ca87300a719f696265537d5440cbfba3eca6cb91bcb28c044af2a5c73cd95907d59be1b566d44482d0ffb7c6293695ebb745bb63dcc1938e7e93af9fb277716c68a074123254c5bc40e59a22cf49a9cf9f6c3dda7069d0c26b3ab1ae96b1e3de403dc2506df287edbf58a0d7213ad4657309b0b86973e47a6cd60a441f473b9a7d8a68ea7b03ccb4b0748642d122e9a2786a7f732da71c7b3b7115eaa6854b409cfeb6ee7b045036b075729ad19b43f1b379dd37308d03bb2d5109509c306e4e1165390a0c965898e272c6941700bfab9d66420fb2c911450b60125a34c4002de2c40241a17bc173b77c81f7d6c8612207d0ec077feab35a3bb0059ccaf69612b5b3b5e77472fcfbb870e1ac4767c9309403e5b919d5564b803d4a84e46a4e79b5e4e7c557ec086669837383c7265dc1ae3b06928c8ac9e500d0a808c66670caf6a84618a5664cb6e818390c76ca0dbbb23f2c0312dc43a395c98b8e415e88a78a2b6b1ed32c4d3383841d995b8a20d592a3804528e242a1d84dc02a6ba5c4203a2ceba08f6592110eb0a1bcc7f39066e4dc3cce9a9017b8c376ac071eff8c46659ccc25cb4d8d811ed146f2de8a411db863c2891d46789b593c4ff47ae98051923c67aba39c81594b9e7b7ca92a4b7544b89bd821dd175c46796745211bf47b776956bb866416e1791584781cbba33331bb6b811bbb06dd43903d65606c8074447054464cfb6f70876246eae8a5447cc48187a1af6bba938bb54b7144b63aa59e8f941e2b373a9e205cfe589421bb98ab4b2afd38b3df901bf04cc58b3802970882b661169859a1135cd795b3445915ad336bfc1b80379d7bd877449c5c46bfb899d07f0be1eeac331d15f0c6a7e0d53125127878a701bec01c190a8a24f747334b5aff092061988a97fe05e9e54cdb93cbb83fc5feca0342118293e7a91fb5165b0079c4e774979411c5da1596614b1c1ab3fe49bbc1ebb27c12141593a9eca9b821f7508816079dac131e1b8239dda83b6f1b001e71bf92290080a77c44837cd3b3c21c8c1ddb18626a3a739b061e4c359bd6b72ccb80ca6346badea3e7c5137408372076593c0999002555a1bc748393b365d86250142719717cbfad33187a880aac13c23f4b44daa76cc731beac7c72ac4144efa0c2ffa64b22b23a13639d88ccbc8daa0546779fe58267eb4188bb33f7e8589d48218569811f9bcc9507bb1905055b2a166625485f59109add09304210b9b359b7929003906a2daf6c362064012611589954acd84689634944953517f0679f52ba30d978deb56cbcb691f16da1ffd6c3e542a1da31c1493ba6147f9c00e331229d3cc06a1077adc71818abaa1c78da4cb0d6f24160bc67dd3530e3de2a0adb27e5ec72304c774e8a99132b244f3b585c9027505729c22040ab42209b696998de3070be95c766624f0bcca1a1b95d4d114c0b0bbdad0010a50376315aa936acd5d938f49ca0edd754c7a262922b683c474059d32220fe3878ea3cd5052cf3f4a2925387e1d643484bb7b4e0b0955145342ac7bfcc48556601a48b73ccfd906c71b5bf1b1004a6c39d387a6f2b0c943060cb4d0cd46a913aee815365b3d954809175625af676257d6afee61b36a4839782457c1153fdf07b46dd1c522c561446c7071d07fb511498e755ef3d23990c726c24860caf521adf04a496240ee63319c3596b4f9257ddace19d0bfeb050f35727ce283c718b9664a377aaa247104fa67b8b521c16a2a92b8959ab211bada37582701cae882cef75047ab8bc9423cab7269a3a404c300a16360660c5a0aec45a59345391c1800e4c10a0b96c482373601ca3510cca0d5932945e997ad773e182ab652243b0e7438d9a7c82a0a86669b29e5b67df4a50adbb625741a3db44a516e82b0f4faa3019167fbe031771a9bbf38991510b594847be919c23e131331c75f69f950a8f12fe34a245ee7be0ffa7b0fe7076f33547fb94e9416a5e2d07882849bf3eabe806c8bf0687ad6a0722ba079d9d2b57e00bbaaeac7532a69ed8383471bb6b73a59b8364e385c22148c8b92c0335f14c6f185504e8246219aaaa9d8bf42d4a515ec024f09cd1117b3a0d96e8cd8ccf80b21da6229889b7e7b465c3e33ace29393fe9c6f7488cf58139168f50bf6dc7683f28b959b0c1c688865899e6a5409f8539e891888328602ee56a3baf68a19584c6a2437a8c3223bcbcd75a21943439879243663cb32cedb180a9235be2bb2f4f967f287757d442b62252556f6bf93208e5eca4f0b68c80478161cc05a5a866b243867cc0cca8eba883558cf4e39be430b687df078714b134b5c045058169bb2766b815bbe97040b043f4ae55fb97b6a1cc603c3a29258a9549bc447c627cff0a040d61a312f0493ea8663aab5b0ecb330ba07867ff1000cf1881627a87a8030485968e4d0096f0a243e2265458649ad64781daab9865aca9db8cf14d9375d2c05faf9427da35016ea6594cb2ad18069db9351e9113cc34213973886c2c5550c51ad18bc0cf5ba75fdd6815cf916391836afb74ccd423df47a15c9d239d36cb881eb6b1904bcabd147ab40604a6277905a9c11f7a5bef1b9dd34160503154f066bbb07466f2bb9ba935414e9cd40fb7f26570c599226b21b12dc786f359736257c38b8b102b92220cbc86c46660a81e780c9d48ca9c4bf3652c4f9c0092d3a6255c1ad17238e5eb1cd8b03bb8323a79d52791f7a070b96b06e9c6140991ccbd6b4c10b0b686b4765664520217298cc156ec99974732ffb07aa72f3acd3718cc0c293b84738d9c16331cbb97508c50eb43faf355c7f55bc92585368395f0e3160588a955ba77e44b431131d9edb13d385e02576f74891eaec6271a2087439584ef9d8f60403757c2dd061cbf5054922ea240803b79503f9bca2d83ca69a791ccf1ed6224256b3878c0c57024c4c317674abe8ce019c301a2a080e627048df0b6813de5a2641aa47b776956bb866416e1791584781cbba33331bb6b811bbb06dd43903d65606c8074447054464cfb6f70876246eae8a5447cc48187a1af6bba938bb54b7144b63aa59e8f941e2b373a9e205cfe589421bb98ab4b2afd38b3df901bf04cc58b3802970882b661169859a1135cd795b3445915ad336bfc1b80379d7bd877449c5c46bfb899d07f0be1eeac331d15f0c6a7e0d53125127878a701bec01c190a8a24f747334b5aff092061988a97fe05e9e54cdb93cbb83fc5feca0342118293e7a91fb5165b0079c4e774979411c5da1596614b1c1ab3fe49bbc1ebb27c12141593a9eca9b821f7508816079dac131e1b8239dda83b6f1b001e71bf92290080a77c44837cd3b3c21c8c1ddb18626a3a739b061e4c359bd6b72ccb80ca6346badea3e7c5137408372076593c0999002555a1bc748393b365d86250142719717cbfad33187a880aac13c23f4b44daa76cc731beac7c72ac4144efa0c2ffa64b22b23a13639d88ccbc8daa0546779fe58267eb4188bb33f7e8589d48218569811f9bcc9507bb1905055b2a166625485f59109add09304210b9b359b7929003906a2daf6c362064012611589954acd84689634944953517f0679f52ba30d978deb56cbcb691f16da1ffd6c3e542a1da31c1493ba6147f9c00e331229d3cc06a1077adc71818abaa1c78da4cb0d6f24160bc67dd3530e3de2a0adb27e5ec72304c774e8a99132b244f3b585c9027505729c22040ab42209b696998de3070be95c766624f0bcca1a1b95d4d114c0b0bbdad0010a50376315aa936acd5d938f49ca0edd754c7a262922b683c474059d32220fe3878ea3cd5052cf3f4a2925387e1d643484bb7b4e0b0955145342ac7bfcc48556601a48b73ccfd906c71b5bf1b1004a6c39d387a6f2b0c943060cb4d0cd46a913aee815365b3d954809175625af676257d6afee61b36a4839782457c1153fdf07b46dd1c522c561446c7071d07fb511498e755ef3d23990c726c24860caf521adf04a496240ee63319c3596b4f9257ddace19d0bfeb050f35727ce283c718b9664a377aaa247104fa67b8b521c16a2a92b8959ab211bada37582701cae882cef75047ab8bc9423cab7269a3a404c300a16360660c5a0aec45a59345391c1800e4c10a0b96c482373601ca3510cca0d5932945e997ad773e182ab652243b0e7438d9a7c82a0a86669b29e5b67df4a50adbb625741a3db44a516e82b0f4faa3019167fbe031771a9bbf38991510b594847be919c23e131331c75f69f950a8f12fe34a245ee7be0ffa7b0fe7076f33547fb94e9416a5e2d07882849bf3eabe806c8bf0687ad6a0722ba079d9d2b57e00bbaaeac7532a69ed8383471bb6b73a59b8364e385c22148c8b92c0335f14c6f185504e8246219aaaa9d8bf42d4a515ec024f09cd1117b3a0d96e8cd8ccf80b21da6229889b7e7b465c3e33ace29393fe9c6f7488cf58139168f50bf6dc7683f28b959b0c1c688865899e6a5409f8539e891888328602ee56a3baf68a19584c6a2437a8c3223bcbcd75a21943439879243663cb32cedb180a9235be2bb2f4f967f287757d442b62252556f6bf93208e5eca4f0b68c80478161cc05a5a866b243867cc0cca8eba883558cf4e39be430b687df078714b134b5c045058169bb2766b815bbe97040b043f4ae55fb97b6a1cc603c3a29258a9549bc447c627cff0a040d61a312f0493ea8663aab5b0ecb330ba07867ff1000cf1881627a87a8030485968e4d0096f0a243e2265458649ad64781daab9865aca9db8cf14d9375d2c05faf9427da35016ea6594cb2ad18069db9351e9113cc34213973886c2c5550c51ad18bc0cf5ba75fdd6815cf916391836afb74ccd423df47a15c9d239d36cb881eb6b1904bcabd147ab40604a6277905a9c11f7a5bef1b9dd34160503154f066bbb07466f2bb9ba935414e9cd40fb7f26570c599226b21b12dc786f359736257c38b8b102b92220cbc86c46660a81e780c9d48ca9c4bf3652c4f9c0092d3a6255c1ad17238e5eb1cd8b03bb8323a79d52791f7a070b96b06e9c6140991ccbd6b4c10b0b686b4765664520217298cc156ec99974732ffb07aa72f3acd3718cc0c293b84738d9c16331cbb97508c50eb43faf355c7f55bc92585368395f0e3160588a955ba77e44b431131d9edb13d385e02576f74891eaec6271a2087439584ef9d8f604037500000002d23623d701243a0b789c12730af4acefc5af3341f02540943d955b801e847ced5369e34f6cd4c173bd8581a22b72719d0b2f597fb5c0142954e2e8815ac0800100000000000000040000000001be63d18c035eea04353a20a0aa859635ea0f2bb265a3e89509451b53b7c168b9000000019565bb39905cf99b938461619cda94cfdf7dfad4d290c583626d2cd0853140cbcb693cf07d8381ed5723b78ad1f350c5053ddb24595d1c5aac9bba532493830400"

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


/-! #### The session's state

Accepted vectors are fixtures for the same reason the prekey store's are: the
model cannot build a session whose `ratchet_private` matches the classical
ratchet's `dhs_pub`, because it does not compute the curve. The three below are
`tacenta-core`'s own exports under the counter-based `FixedRng` in
`lifecycle.rs`, chosen so the optional fields differ -- an initiator nobody has
answered, a responder, and an initiator whose peer has answered.

Refusals change one field of a fixture, again so the rule under test is the
only thing wrong. They carry `inconsistent` where the page says the session's
semantic rules are inconsistent rather than malformed. -/

def sessionFixture_session_pending : String :=
  "010000014e01000000b90120b0f7776f19dc534b7cd38b4c3e9d7cce7680390f450a472fa47b30402c3a0e0112896686a8994b109c800cc12eee10d0464c7fcb32f3929b9860a476ed49c6614c75f3d17791a586582e95c424c8fddacb70f1a0d932f49ee8ec117d181aefb701a6df655109f0943c4c9a242d7b3eac77c9b10f049ebcc2cf3d6a5a4ccc0c6c220000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000008c0156e2462f46c7da22410a89138b976ce63c3a0c9663a7dfe078ab498e431a035e00000000000000000000000001000000000000000001e06740126008303a1ce70d8d10a48cdbce1d826dd51373f58fe34ceb30b3101f00000000000000010145cebd925b32aafe3527ed47c5707701a5c1f62166bc388bb441f270d6cededc00000000000000000000000000002f1901010000000000000001f4918009fb615cf797128d55f3c542b4b5fb3dd19622efec566e6d87246253fab1f3a423153bb110203500a715d98335146957148558fe5bbcedf52fba96d59300002e6074d3616cdea12a815fa535b9e96991542977c7aeb0b94202a1367e7ad75fdf013dc5a0db9cd7940b3f78088b72f63734032c08e9e266cda7c85b389b1471d9491e352723638a4e4cca5edcaed5775266705c9c0201907842173982fbe25574803a190cad3d7c1fba5517214c7b8b65912dd62868f4452fc352ed7c9e7a60aa2847afd5d4629138906713308e01c8476195eaf58ac0374ae9879459d7a3c6bc814ac85205595873971c7c491bda25473fa3aeed4a3eb8d5c09c418b44121e6d1bb21fa67c74d291d8169b931abd0da92bbe6b24a507ca6a7058f954332bf9be241874034798eaec42ba7c7eef943c3c931ed75b479158c65b84c560a8351841233d826a7666234fb3a4d96c1156d597b10b3f77cb60b84aae9baa01a34a2387435e08730507d66e2ab2c2b3b89b851709c462b59f12365835313f204ac64a43157b64656ab634513225bca810c84a0b4ca12da4ca8afc7f371236f1d090a82838e8485ac99bbc18a6ceefb767bdfc3609725b100197a4b523ed098bdda030576233a07629a943c347da3d8d4b24b4a463cef47928e642ccab523ceb2fdff0bc411c71220c2e2c58634e0166ed6c50ba0203a133c8d273c5c4ab6ce18ac1bcb046dc94813f66b32e354f1cab69f8539a4e6654043b98cf0ba2a7970f764650460c51bd86cf281470942a005739a44027709aac2721a13dbe5c85ce32079b451955201f2172130d91b7af10056f2613e5f193d3f72d562615bba04bc40a5919db12f2d5054a576db8252a2bc7944a37c86915749dc1c470db0b71f81109082a46ac1350d105d6006642a0c05a157f7a0bc831a7720b76a96244333b34107d722b80b1b4efa04adf74b8aae31c01d4c5ac99211d336d58f4ca91845c024633f1d9212a0380cc03939500b0ea974eb4294735935c63371ff92996e84881ffd4b30bf590fce7b449bb609a71cc9b72912029952426a00439cd228bc262a83acba980af445d503ac623e05773b07cd0f776b7a43e8e66c719c2689e47b55a95bd9dc6886fab1e0d087060f268cd624226360e112c12e1f404477ca7a78027f9a5544e83b956e1bf33d3612eeba2c91a15f0419117089a592bb168e0b2d6d812eaa7637189a594cac87e14827b46b314812b8214928193bb0939059687b74b71b1b72192cff895699c96f2c7c3c916643db65e4fd2cc588543b8d22e9ee2b61f6953a770b2d39022635655efb19940e542d2bc89a3f419e066923f12874d9bab74909b36b31689e196b6b3ceed005b8cd84fe7b59bfd53abc6775dfb14c22042629051cfa4e16616779a3814680d1971f0c1643bd043b8c68f62447afb67584516bc6f009437b126c163b2037c3a8302523a77ce21860751972e4d798d72d67c9ad1a7dec5093565b3bfa7c8e75320a9cc81cd681ab333b2abe4895a7c7a0bc20ffd0a4825993b59832870133209792806a657ca3c837d188405495e837bcbf0a90b74a1ae49c950f3891d743a46686017962ac3ba27bd5c11004ea5029fa9131fbb5033ebbe945a68d8c727f5544723f54a2c404b8b72884107cf686b586cf493f6f8362d73b037715e67999040c9c25ef199eb8bc3c7bc9745596f64621b4861bab451b437623d343b0237809c93c03a47203834996de551ba67d88c819b528f596098db087128a0ea426d5d511f26d8bad8919793ca400c2cac2d1348003a0ef407292a0420b0d2bde6b38d3d7b8370c61c22358d77a35ffb8055577659286c2f5bca9b5dca5abc766d21b9536cf14b6feccf1dac070e76124e414277389fa4da903176a97ca1ad984668a7089981204cc5fcbc9a5615878867d7bb7a787670008d75f8ac7b3b282386ec0f568577ef13c36600a32fe4188d421e55c0b12a634c472999eeacacec0224ba05b59038459fea13f4604e57d920be51279d42c9c7344674764a0829907110c14c8a958b443566806022e9412229cfe6b184e2abb437f86c0a8817ef073aeb4920afcaa9aeaa774344b6a86789069361f657449807c3c96740a8fa1b9ca76450c5c4221a05309a523ffb0b54357d4d9b2d519cb8f2787aa4ba58da2911bf633d5bc592b1e893807ca905137c724a5aeb354c4159ab26d3cf0598907580882aa618c9674d6cb229fb46292d06c1894331d7bb0132258318c395ab9298ff6ba0b504a2fdb9531caacc22084a30e72ace3980c887bda76066f454cec5d36208ea74207418766c9854b56e7fac1a0353a6518b0ce6a5b07d60389d0030fd47fa3804bdfad4ff4300b101d802acfa25018602b5fd6905d4002afcc9043efc30fe3a0308035b01aafcc3fe7201fdfd53063efa7efcc0030afa2afed50015004a057afcd4fb12fadb0061041804eb01aefc46fe0806220699f9680147063103f60466fd5402fbfb4cfe7dfd6b024904410516fa24fc2f0355034b06060415fdaafa80ffe30346fcd8fccbfe66068a013206e60127fc2200f7017f038afe6cfe2afebe05a8024afaecfe94fdecfb8afa4a061a016b03a2ff96fd94f94a04590689fbfef952ffc0fddf05fe03df027cfa04fedefa85037306cd049d0318011a04030099fa8ffb500565fca0fbae011d047203430105ffa3fdbefdeffeb2fae7003a0210fc920494006e0450fed9fab80324038c025e03fc02d6044e057efcb404b404eafb140683f94fff3bfc49011afee802e402cdfde8055bfdfb02af007600c3febc003a06eafc7dfe55fe0301470409fcb6ff06fc2dfb50faeefb81ff1b04abfcda02680413fdb905befcce0568fc8bf95201af029d0066fefb053d0063fa7701f5031505cf0512ff410635fa22ff09fc81ffaf026f06ff007bfd78fe6c03f104d5fcdefc1cfc0c060cffcefb2b0161fd32faa2040d04970047fd57fd01fa730628fd79038efe5dfda3fbddf93cfcd7fdfafc74fab7f9d4ff4ffa0c052afbdafab0fc6ffb27ff3201e1fb1c024efbd4ffbbfa8cfafcfa2dffe9fc5d0320fc3dfcbc04bbfedcffa30255064b032f03d2fe73fd3704ebfeb4fd1f05a004b7010cfcfbff48fe7402dbfec3ff51fbb1031efe00fb7c063c02ad0509fb5cfdf9faf6fe14053702f404edfb2006f402b4f911fe3f02a702ce04de02efff8ffb6303d800400240014dfe60fe47fb3c053b0112fdb900d4f9d5045203a9fff804b9febbfc7f05570602fd4afc0e0379061e0420030e046eff170670fcfdfbd5015eff1dfa920046051e0086fb2c00d0fbb705d7f966020a01d9028bf9b5fb7b03ec04bdfd65fcd6fc72febdfa350066fb58002a0000fc8803cbfd7703a7fdae007d0682009bf94afeb8fa61fb28fdca04d5f9b9032306b1fd34fab201bc0051fbcff9dffc3c0686054a0649000000aa05960356fe7afeac0411fc07038a0033053cfb6c064ffb03036d02e3ff0a0698fd0efee7fa5f03ea031506a6ff8d0454007004230597048bfbe8059cfa04061d03c0f987fba8ff2efcaa05ba0341fd6f0266054801d005d902a705cefcf6040ffaae04fafdb8fc2dfe7702830555fbfdfd5706ee03c1fa440401fd8dffa40456fec7033f0621020d03250244fbe10093fdf401cdfe03015602bcfccb023c0230ffc403e2fb3e037701fdfe55053cfa15ffbcfc6a057604ddff1b026b0463ffb60050007d037cfccbfd51047bfc030648ff890104ff5f03d4fb4efa06062afa21fc2004f2fad9fcc504a9037a03e4fe5500d004aa04f0038b04af057dfc1ffb83fab8ff4afb8ef957060f01210375ffde04f3f9780258fb960329fdd4fc18fdc5020104df05430041fae3fae003f00257fa45fda4fed5046603a6feebfce1f9a10117fa87fe15fa2500ee0090fe5104910330fa68044700defce304790221008a03dcff130168fbb503760286fe210382f91903e905d6fab7fd96fbec026803eafa33fff8fd5cfa9bfa1dfa7dfebf03350267fcd3fa3d04dd040c01b9fb3ffb6bfffffd5206c7fd8bfe40fd4ffcfbfa1d0224fcc1ffa1fb0b03a502c1fd24fff3fe4502d40379061e0065005804ac019303ecfd090405039102ee026203d4041400ecf9e6f9dcfb1ffea7fa540095f98cfa9dfc2f03cef9c900b900f8fb12fe94fa57021303930018ff35023e030ffb3a037afdccfa690697fdf6fb55faf500b803b2fcd002f6ff87ff4dff4b01affa860179faf4ffb4fc9f003a065d0228fe1d0100045005fc013afd9c05b4fb17fb4005e1fab8f93b03e7ff1b03cafaf7fafcfe0b01700118ff470596f92e0524fe7efa2204d5039dfa68040c04b7fef5025f008f028102fe0119fc1400830061fae6fb88049b05da03ea020503f603d002ad040cfcd7fd4f0349ffe1f94505d80266014c05550303ffb005e1058dfa29ff51ff25fed1fbd9fce0005600a4054aff26fa8904d8fb4a0217fbd7f9e0fb4d0564016f0301fcf502b3ff67fc14ff5dfbdfffb9fc790482fe44029d03fdfb41fe240445ff43005b069afb6c01feffff056c06d40037ff43ffdbf996f9fdfcd600ec043bfad4fe78fca20119039a02300100fb54fb95fc2206f705a9fb87ff21fef703acfc5c04b2fed903fffd050491019b00c9fe76fbe20378064901f2ff8a053606790439fa290074fc7905090197035a007afb9d0520ff99fe750354009f0210fde6009d0248ff2b0516ffc300fafce1fa30001ffbc203dd0267fa4103affa48fe0f03ddfc9704d1fc1bff28025eff670043035404e303400373fa46055e0466fd53041e02bf0511fd49fca204c4fff90030fa7b0692fd760133fda3fdcb02520030fb260507fb7cfb3805d5fba80458fc03060006b40342fbd1fcc30129fc72fd8fff35004a0332017205be050101e3ff0efed0fc730417fa57fe5f03b3fb5ffbdb02b3fced00f6008dfb16fc2006d10294fe0cfa65031d008f02d2ff67fa87ff9d00350244fb9ffff7feacf9cefe1d030efdf9fb61005202acfa13fba0000106b6022a04af001dfbcb04e6008405f5fe0b045eff78062902c1047701d6fce5fac1fe35faab00b6fb53019af963051effb90133007105e2f916fd5301e405270063005b0472024dfde20198fb6504bdfc90fddefa2c011400de0389fe3003b101ef03dcfa77fe3f0141fcd3013d05430458fa69fbe700d4013ffba7fe20fad6fc2cfd11fc5bfe730567fee3054c0043e312af24916e6bf7502cb500bbd90c1b556694eac8a9f99f0afe0f9c1b57b2370bc304f70945067e03770746097b077f0a690b090a9e0b3601b40b4d0004053b01e209a506510834021701920c970c6901b308f7082e012500cc05fd0ccb037b025e0bd706bf08ac084b03a501a601350468052b02c602730adf07cf00df09890959017e0a3f01740bde01ec0b9e0b1e036f051b00ef02570a7109d6031a0452022009ef0277017b08fa049c022803b50ab9018f05380471011b07e100bb04e409440ac707a50050091c0464055c0a220c3a07af0b650098096e0ad90b1102310cd4062e078f07150aa60492029e0760098c0b5a0ae00848050d05600c6a08a2098d0cc70a130a1600050afe096703a309d80c44025904a302f7028f0099025d093c07f202a3041f044204e90298033a034b07680c5b01a50609057904420bdd0431090e00560c7d0605007c088603b80a7d0cca02c305bd079209380abf01f909c503d60c180a120591008a03a2069401380c1c02b90c4207290837006a0b7b00020593020a0135064d074706010cc60714032a01b5050a0bd2004009f3091505ec0a2d08cb0bf5076e01400bfd0917027e042e0ad9007a0179088100510af30c2b06da07840c5c00750c28043301720b0403fd08e406cc06d5044e024102c501be05f909910920017a05350b800203076e001f09130c0a094205d6055903760909029f025503e9003702810c920301053202080bd7029d059b095802e500220b700c82046f0aa6091f062201f10cfd02b90574085c07d8089701b107a40a0105c603e602da07e10696099b09b00c1e015005bb01f10a0a07ec0be503480bad0ba70352062e060509d800a6055c08b9053603660cb205ab0b5708b70773030308bc023f02f9068706ec0a6706a10949046e0a3c0a2d0ad7024a000e0abc00a20bfb0ce800a7014f04180cd808b003690adb08270aff018e0448088706ae0c6605700b9302cf0cb00a25090f091b066d0552055a03a0092a0910042203d6008e0292068600d10b70078a048f091309e5001105e8031802400c7307d302e109970b1c00b7097309930abf0506048d08b3033d0b600940000d02ef0929038f009b03eb04270b1e0500097b02bb07930a3b0c9304aa047b0742062a08530c4d07c8072b044d069f0c1b05740a840cac0bcb08ed038d04630785050107de02f0077300090841064d08fe00320a7a0bfd055103820c210097074a02d50c0b09ac070500c1074900b508c5087805ca04a00b8209e7041806c506d40c640a3b034d02320cc602270a6a0caa0c3207ca077a02320417029604b908840bf102c8046006580a980479051204d40c83030b0ad509c107e509360a73077c0b6804a500900c1203c9062f04e10c800b1d06c207dc0a3a098a0114048204b904330868005508b900dc0c2609030bea0144077409eb02b3063b06a407dc052f07650745073f053809dc09b709f8031d06a202530217074107c70c2705a40cd405f30a7a0114030c023c07af0bbe07ff063308610174062d0ca400e503a90a2a06e509ec031602000c69015509200724097d0b170a980b4507910c330970001a0c8409c4077f076605b1058a0a98096d01f502bf0cb10519016100d20ce9054705d503a407bc06d50c0c07240ab607d00b64012009480bd4057d001006340a6f080509d708d50c9f0c1a0632099a02b30a2104df0a6402c404210cb403910bac04550cfe078a07ad0296059b0c1502a106c6087e02050354015c08560c5100e7038804a10cdb027206fe0a9507f70b3b029e08ca0833000701e902500af30b5304b102a408b70c83017103350c4106b105250b7f03da06230132063a06b40713080d0baa023407c1029609000b350cef03b7075f09de0c2f04f400260cea05f601fb0cee071d0ac600e9084007240b23017803fd0b950c29098e07bb030f08660bf40bac0168027907f5046d05980b9c0aa60bbd010109d807f4081307f002c7093b03c607f60573067b021807b509320bc007fa091203aa07b60a3d0367074d0365009000cc0aab09c60adb03bc010e01af071009ee02d402e20b1809da085508900b4d00dc0552091b09fb0459026f01f20362044108ac09050705040606ce0cf9049c057f05b807d607db0892045706e6024b05770cb0000f0b9f09bc0004017404ae0238034401cf05440ba10aaf0c660a3c03d105cf0a7401f801d8081b008d04cb0be80c5603920069070d04750bc5022f05b60046090e02d509fa030a0925063502e4038d0a6c0454088d012607870873014f02650ac50b56022c0762022a08ef098600910a3400dc0bce0097023606f5062c050d0bd60718088f03a104d50040093c0735045705a30a54029f0a2c0be60657099b067b011e00b8025c08700a5d040404a6010c075d0c82020b071909b30583016a0b450a9f06a203150343014703a20b310b690433008e0a17036308fe08d9017d0ce1028300d20693016f015b0a7b08b80cfa0a0a018208cb0546085a05880685096006460ce6013e07b30059002505ca02b207d10739086f031605170ab1080e02ea05f5045c06ca0755007607f108e809520b730a41043b01b0020c09010a420a2b02c1026b039e01ea05e606bb0c6f011204e201d3093c06fd0334067107d10993056908de076407e206fe04c80320069c03580264082e06eb0b4903ed03390bf8083a046e02380253052405bd07880ba10b7d05fa00150a28009c06a90b2c076003cd0b8104a30c9a079c01ae03330091088c00ae038002a8068102ef08a4042000920a1f0b6e019a03f3066609bd05a901db09280650064403ba028200840aab0c57032f0cdd02ec05780c1a05be0678039108900a77086c07a603cc008f02ba005002ec05eb000405a5044c00a404df0a15093300020bec02bf0a860b4206a2068601d0010b07890562013f05a90cdb0c8902f60aeb027101600abe04a707de0376072e0ad702d10ad0041a027c02c006560b2602a30b41022309d905e10a860b4009c3056c0b0c06aa0b87062d0cee00360a6f09e005ba08fc00ea06de05770ba208ea031c0ac306bb07af04ce0aed0a4300d502a204ba04fc067304e20816008403a20b8c0add062104b609ac0a5901cd0c9e0058060a09a40c960024073304c6043a010d01e40254041101030667040f0ba002100b7d08e508330976015f05e70a27011b085201c90665090101d7051708db028400bd039909cd0ac40200041401390cdc085704f402d709a70a1a0cbb076d078a01bf0ba3039c032b019203ad003409c6050402db08bf0b13004d030905f10b2402fa00b2039f0064066706fa083f08c9066a02b50571003c0a760a2c003f008307d70ab90be409e0080e0c69081008d009cb032e05af02b30123089d08040cbf0825042d0a1f010906b504d508b109cd020c0c250553021e0cc5060d03590b1e03620bc9029308730b8805c2085d0c2c08390ad70575036d07c30c63041d093e07b30955097207cc0587067306c3005809840875022a091d0c05021600610a8201b50a89031206ca084108d302ce0b670436064e007c05ca02ab0caa08ff0a7702b80afa08ae07850afb014a054d09bb063604f7044309850c5b07b0076c005a063309b5041005d2081e049f0692090a0a2f0ab3037f0bb500e3012a0aad0ab40224072a0cfe0aa40715093c0964056b068f069400a1026903bd05a00b5606720544042903b8032e088a0860098208ae03430a9004090608086907b900e104e0090f091a091d0a32045506ce09b109370be900b901ce0351092208b9096001830750013e03c4025d0c4409cd03e8059903b9088a0b94000705490582024c054408bd06280cc50748001d05c20bd40a4e03fc0c8e090c02ff0641029c08e60b330cc4036c094a0ab208a60b8b002f0460084f0ba40bc6043d052b035f04d900be041c0a05004f0bd400e104ec050006b4027d04b90bca0ae10c3e0092060108ab0c1700eb006905fe03a20450059e026c07630b1f00ca0c8004190b8b055901800b2208460789018c01e002fb0b45071005f204dc03620bd507be0889044704b406d108c2007f009d0b3f08ec00ef02b502b408670a1505fc05f90c95035005e307f706d80b820430082a01ae0a910417017f019d0557072d088300430b55011d0a48092c0aa204cc02ab01be04cc090b0b5d065902cd0a77031f09db0c3404e9021c0bbe09ac01cd087f005c00710bfc05620a8d0485015b021a0b4c08d20b8208c306ca04c705dc07750cf9069a045103ce026405d708b007ac05e706a3004a06c802250a6e02f203380c4f011c005c09930a2407b1020b0a910caa039703630415086f045102f3016d069903570a40086e023e08a5015d01620b3d06f70c500cf90974096e016309c9037c03f401d105d402a2058000300522034504b90949082f05bd01ab0bc304af0a4d03340551053507cd06410288058a04460ba60c9d02620be209110947091300b706b8046c0c1c02de0b9b097e0694008a01e0068a047c0b270a8906e5029701800691022109860a3f04ed01e9032d060d08bf099e034701d0069604c5017801a00ba905920a0c0c88063005b7007202060bce07f1053305a3032409e00a2c071f01a1075d0a3d05660a39065c05b107eb0a0204340518051107ff0095049b043409c0033b08c90cea020e0aff03000ab90b7d08a7099306220a2a049e0b4c0ab400de0c5601400164049200f30863083c06c90362050c04560a8d011b00be06100c4f09ac0a3c064c0488044407fa06450cc70c9904090073029901c5016d03cc0b6805f90a4e09b002640a24035a06f407a908a30b0705b5035e06220ac606380304050e026b0956069106e805b7083f0326049204c909100cdd0900094407f104c305ec08dd031409150560025d0c89030a03210990067d050d0be10186045605d10a5e04ba0b7d05c1001502ce0951073c07ef023f030507940631010a07b806d9025904ea0140047a0b1c06aa06b600b50af005e3046d06fa0c2f0c2d03c905e201fd081d00160b720359065806a70688054d00c3088801c200030c1106570bd803ab067000fa014f089905c9029b014b01a201a9065d08af094805fa0928067904e9006702010830062d00e0003d096e001d07c302c308bf022e0997012501fb097a0b1107bd00b304440cd207ba0c72040c0106031508c70528079e06ab03790239025905740c560304036b0194080105e80555065b03b406250bca0b5e0ad2049f056604300243072c025a06830af305c50558016107d8073c0b930b2107e4076b028d0c5f040a016e0a810814028b06240bd00c56019b08cd036c089b010808a904720ca40ce50b94078c0bcc0930098d0cd50b9a0a6e03d800740b5507530a9f00bf086c0c230842081d0c71043201b7062103030c5808a10b8404750404036202a6087109ec07be00e00c090ca306b301c703d8019c0c61031e0b4a07d3028306e605f2008406b80a1505f604960a6e09650c7208220ce3020e08f60abc028a0a8600ca005601a2048b0c2d0a0e066f0cb90c3205d30a0600e2077e0c710836041f024807f60ca40447071a0972089905e501b8074c059f03850a8204e0073d0ca7057405690bbf08de07e50971077507800053075a020c00a70b49033f0b5e03bf012e05e308590c3902840a8401850cfe01b00a3c003507ef05db05e70bc903af06800ada070b02ee068f0c1701cd00e2000c0a0b08500907037501f5032805d50bb907bd0481035e047809310a0e0b86013801540aa20c4106f2098f01d3010a07ca03b8080c09f30156007509d308fa09f80c280bfe0bac070b01b30153029206a50b150c8a07f506a10c9902fd0628016b06a60867074104a803f600da095f0a89071e05c809510bac0b670c250c0e007f0ce900360067062d04e60965032b08d10c550620044205610a0501640a7608ed088b09dd097704c102fb05710c0204d5022509910c9b00120313081a091e0a24038606f90b5e0647082601320a1c03d503e6069a020905e009d2001304e10a1109fd006600000a0200160c470bcc0a1907bc0538086f008f0539076b04e40a340b4109a300f905be00c0058d0a8a056f012204b708ee07070643052b053f051901e107cb03c304f803c001590240077a0b8a0a8109f105c00641085b0c3301dd057c06ae0b2004cb018c01430c430bd80cb1038407fd00480cea03f80320013e041908df079a021808910b6609c507c70137017004a800bb0971005907af0af70a4a0c510988061b001a07c801f2044a00250667023b089a08020982045a01fb03ac06db007e0144048801600650018a091c08a6012e0c2b01da0c2e096603ee0b5d08700377007205c7037704bd046d0a9b05b4019e01980c78055709250c220b5102a6016200b105ba0666070c091f01270a3706390831072c07340b0104d000b605980bed079708b80727081703d90283007700fd0b6401ec0ac3005e04ca037f08c9049d04760b21035e0b94046705580c3d094d050f046d0294079407c5041c0b490a2f0662010d01860cee08410946076d00a005c2033c09b7084b0778050e0985034a017209b700ba08820ca205ab05b70a4d0b7708400c090c02021d008702b2060801ef08160a6a01680cd60c84054603740554018007820cd10c8a06b3018900530ac40a2b09aa016806f9060701c605110ac3066d0ceb0c9f0ad20ad5007601550cd10026033705f80946001b07c60609085401c901a709eb038e091b06e704e200730554093a0a6c03230308043d08ca0c4a006d08a00ba903b8003103a00cc30414077a0b31022208c907a5089902ae08e707850ba308b905500ac8005708cd0bf403210a7c04b100a80b9008da04e3047d01540bda0b3d0c850936091906b10cbb0a940bca06ad031f04770394027800bd06530661000508ce007407710c3d0860037806d607b909f100e2041a07840cc0029b06ea017a0a1803a00cc100a0004702630cc7089001e90c12027c0672056e026601f1043c0615085806670c000dd00c9d04bc092308bf085c05cf0ba00782016a078504ae001d0977056c04f4009c040000d80047060e0cbc042a025d0c58024301c40bef00970573077b08ab035607ae06a80486043107170053076005980404098b0504026e03040c11076f0b9d04aa0a610a9c00390c3408470b8e043b01a80986016309da070c0524096808e207ed09a007f207a9008e049d06ef0a1a05190b20085404bd0bef06f701f10ae108d008870699046307070064041d071b0a2a0a1702fd00180c230b0c02ef075e01370bf209b503f30afc06f40609080304a2004f003a08d8082e0190028208340a4d059408230cf9021d06f60473080e0a6108460a310706085306a20715032d084509d905bb08430a74013d01b700b003c1043b03b407700bc6093b0b3507ea06c70a54022303570b14077502930a0503f20699005f05c601fd04e401910cc006530bb301810131007301740b47024f0af1023f006e051d0c76033f008f0557085e0b6d026e081e0afe068f01ca09fa05c709560a810bf201b1002b04cf049e0b320c430b04023307780b07095c08940cc00cf809170aaa05f80a9a0af707320adf061c064f03230402053c09e0067d035e083b051c06260b520c960a1e05de0823033f042004bb094d0489025f08340c0c00140a4d03f20bda0343098908dd051506d608b801f50aca034c0159090b093f0c9501ba01490b0c083904fe06ab0c7007430b290b6e0a6f0bcd043d04c906b505180299042a05b7001204610a9a046d07c80519081f08660983001c071e06390389098c072c0c8208ec0cb50a030c580b5605e7095802d408350c960389006c06490af105680019061b08a10b7b057e0b6d081900c505f40a910c3a00b604700b4a04570cf500ff0c3504610bb701a4039c058d0c510a7f071c0be6013d058c089e062708480a2b0a4b063109b00c3700d60717016d052007650b06003a0ce2053a04e40133070604e1091e0a07095109940265087a0cce0abb04e308fc004e00d70243071b017b090f00ef02e105b40a5a07170cdc041a053e0217004706e300d7078e06e207560a370b61077e00e20b680290020801740bb40b35011000990ca504d90add0b1a05f104b402bc0a19047400dc08bd03cf0b8600810a1e08a7079a013e072800100cb9009d0b810c650a7d07b6080f0c4702f2084607a0096b0c4900630bfb003c07550cb604650027051401dd01100cb5004e00410a1601b603b20c870cf90c9c071503a60a7e0ace016d09d5034103100a0a0bf6079d0b83046a0af102c9079d055a035f0cbc07a503300c0a030b0b78005804900c7100a2048e013e092e01a804520b5802030055068b0b430cca073f04ba022d054a09e504240ba90953036b05fd068d049f089e050407e2092709000abc05690b9c0b5b0b8904cd0b7103ad01d308f4058800ae02e90c370c990965025103e2076900dc076f08300c6e00e30114099c00ad01cf07cf08f906a70a5307940c4904b10ac60b5c0cb309d20bf2092d08b6037a01a2011a0755038508010b3d07640b3f0643069d06d3010504a90c12062f0c710923037e049b03090c950b8d037600c7053808a8001404e80c940b31098407e5057c086003fa071006950500099f0b6901ec05f0045a047a06a50c50016208c70adf00eb03830111075b05200a9105460bbc0a6d026e0a1f03cb071004f20a9c06720991006000ce08a701210a9e079f08f506560959027508fd094f0586062e0a5603ed0c4f05e707b503c50b7e04a508e307d6078c069c0ae904ad05f80ab5056a0a150102073c0347006706b005ff064e03aa0cfb0ce6059e07f605a104d90847067b035f042f0c8103bf0a860a0f07aa0b0e081108f70b6008bd09de0238053002b201000463015004ba088e014a000302d206b8024106b80c3d0c27000308b601980320070600ca0bbe04ef09a500350a66055909e704d80b7e0327072c085803ca02aa07de023e05c707c8041e044c0c2806c7096307e00c590aa30c8e0970036b0b130889021703e708930812067500530b040b2e0bdf025a01cd0a0e01520a300ada072e07ed0366076b000f00610b3d0348067e03e802b900890b850651080c0724053d0a3c092f021807e608ae00410bcb0ad60669015505ad051f0b5c05d403b707e0068a0ac40b4b074c093309c709f00c80070d08b4023000ca07310650096c0abd0a4e0cce028e072e01f303fb012105f9040900fb01d6080c0307087a0580033504200c900b32076f025b09b80659094c04190837035305e5056002d100b909970a0304bf07d30be80bf2015f002f086e0007039003ef0b0309eb02a4045e0ad5002805d705ec01030c1f003802b604d200660940051306ac0440036e073602030a720645083705ac04d80a6b0b75040b0c2f0ac4019509880ccb03f305e50c4b0452061e09d307200930017c030d04d6003a0131058f087e0c9707bf05d500e6000a0ab504c304b50a4407c401be0b2a06ce02c905db00f50aaf028c0866045505570cae0988026704bc089408c5056707b304de020c053c0acf055806fa038c0716024707570a0d07a708690099023600f90cb708d7051c00970149051f022207920352095405ed02dd077e0a2204dc039404b503fd099703a402500b6005e50b0703a809590ba100b707cc007607a20ce103da04c80ccf0818047e01000d5b05de064d0a58006d03cb05970049091e0c7304720270052b028203b50a8c0c410628003b033602170baa09410a6b03cc0ad2003d01a9058f03980c150b21068f002c00200aef0688047505cf0541084f07c40977083f03f7051d045e035e026c06c10a0b0c0c079f0ac00762076907d703080931011f092209b60422073a03ef079c05250060050f09e20337044008c205e20060076d02ca06800477001b0432084301b3023907330b190487058a039109f9025a02880bc309a70032004900c902540ad701b6026c08d30a000cfd06180856097f08f808430b140cc1055208ab021b05400c9302eb04430434038808210b7c0b1b06970aba046b05f30a88002f0cf3080e08de029c090e063e08900ae50793029d084d02d308cd016c00bf02fb0ce509b8057b091f07820cc9044a0ba80bd3080a002e0345022b067706590470085b0b0804cf0a1709a80b4f072f04010b2104d305d201ba0ac60b820adc038505e408030b2e0948096606020a3203b406bb03b00c8d028605360c7400cb0a320afd0ac307e3055605b8095f007d07530a13004d025c001a063906ae0605030506d905320931008305b70cca06310612025e04ee08790b67052c0c0906bf06700466097e02d1079f043e057a02590b510ae809fd00da0a8d057b09190a2d082f0b52067901b60056090206f4087a01650ca30082058b0731049505d80881086b01a4000a02f302df0c360a560c2f0c4609110aa504ad09430a5d07d20640044806840c68057101bd0c9505090b20079606b803fc0214091203450ca70774099602270b6201830448058e0a75096f00f601880c770c9503e004750a170606092808640560002b02ec025205e6085d0a4d052408cf0bd30b82094a01dd004b062c0cf20c200ca1091d009d0b87087e08c908f1029405d40802068908b80b7f0c5e054c08520c300ccc0aaf046f034f09a5044e069604d102cb08b00be90b500518015f0234006e02b200300af40b3400fa047a0c7800ec0a440307082600900670088a0c8009fb081806d809b3022c06ad08a30cc7009401a80c130c2c0a78033d034507ae097006f400eb016c05b302030cba0bee028609ba0a9e08a802d60159082d088f0a60015b09ee050e0c200b85014b03070a8907b40837070502a4088e0bcf0c4c001002110b3d02bd03b509620b81039302670bf50ce9036d093a0a10077b057305bb077a054a03fd05d902b1097109ac0749098b05d401b80a800a640b20034008be054a001c0807094b00eb04d4066407650160018d0033028203e305540c17093305bd0835000e04e50c410c370a860588021c08f40af4080b0b02003a0b2008d70c950a8205290a4e045d0bde06af0c620bfa084f046202080be400eb089b0a8204e102af0992030c0b65043a02e50cf40bd4034507270a7d0a4e01e60115033b002008eb05a50066000709aa003a00ea02ba090706070b02083702710359048e06cb0070060200b108fc033e011d0b7d00db067a07e30cce083804fa0381089e007103ee07110be104b0092d090f042d09180af103eb0059045f05dc0969023f0ccb052f0a7307830c7f04cf049c0b5f060b07e101f709ce05ed00f208fd072300cf005a0589025d01c007bf0a4f09ac021101b103be00ac0417093c0bb707fd01ae06b5072e036f090f0bbd0a2f020600b00684076e022007bb0405079605c60ae00c1e02780c57058e066e0cdf00e3018307360cc0084f05190b6309000000670001000000000374d3616cdea12a815fa535b9e96991542977c7aeb0b94202a1367e7ad75fdf013dc5a0db9cd7940b3f78088b72f63734032c08e9e266cda7c85b389b1471d949542d6804f537000de61cea08c4f0f5f2408018405a1a4fda7770acd7b7d785c60b35b9fe3c1de9b44091479a780748d5fab501b339d1bff41fd318fe4faee74000000042057b4e909bbe7ffe44c465a220037d608ee35897d31ef972f07f74892cb0f73f13050faa684ed28867b97f4a6a2dee5df8ce974e76b7018e3f22a1c4cf2678570f207b4e909bbe7ffe44c465a220037d608ee35897d31ef972f07f74892cb0f73f130faa684ed28867b97f4a6a2dee5df8ce974e76b7018e3f22a1c4cf2678570f20010000065073aeaa5c7753f83b28083cdfbc9b6f55f108e11580b1f7bd2f266aff173efd5a0000062028fd05f5a598513dbce932e2af4b5feb8ad20c8ceb29a7ee70bd69c3f37f9d4f37f4cd5e424274ff17e90c6a464297c1296ad86385bfb367da5f51ffb71cdab6dd8985d9b2f882dfc01385ba042446a9be26000e2d85d8b4cf38ab69efd7d1f690851dc0935756aedf533d39d773f11f7159ec4e27d528a3d597208482f3c280fce396180523fb806ff2dc7555a698c53aad39cbfc9a364931dcf91214e8b4e3436c26f51d4e036c68434a6429d15e09602617567ce3bc7dbfe16fe2cd8219a39b00f35bd40b2f390ed4ddcb18737e89db546fef8092b920aab0be09ca922299cd4f0c372211c894b05b31d08e0aefe976aa0ada718fa232d20c5cbfec38b9a75b4199c5a400da952c5f9bf3aaa3af58c280cf9202ad7ab3b4ae496973c2d7ef2106191451eaeb5fcaf6de672645c4fba4e86a89d075375e7966cc2a158ab2a10dadd3e9cedfceff0bfdbac9663eb24fd5b00e677b97b9c80d7669d2d5441f6a60f735f0463362f8781c2afd74dfcc7af92c206527abfd25a2b7b58a19aac32ee31d725a8cb9607d70095e9cf2e9917c8c522935eece08b3b9a5b70bd9aeef6c2fd2db618c7e813c6c1d93bba62767fdc41fd7d671b87f987ea800893b3a2f436654804c846e344c08da498bc61202668f2e2292d935c7c51e71eeeb23829a966cc8e0cf9579b6a8b43fc3ebab9cd46625bc31647935e57098d891a3e728bb386569a12223cbfab51b22c3e58e58b1ac44abf4e9bb9a69dcd2e8fb3cdfd61d8ce072f00cec0f6239ec23bee2f1506c67826394054afd2069d7031c4eef1f342ffeb4e47cfa31d4fa38a2faeec58f01f9aa2a1e162e015f4d7401b838e8a54097f57de0929fe14d6b6190e205220b0f6ab8e2d08e24bd1813593447e27460dc785634c15c252f66f7da381f0d5c2fc274178a739c6c3afd2f34a034bb27e2c895e3b179e31e49147d7ab4b1879ef396382066a332b38205f414fa9841c5517d518c950c3ce59055ccba3cf5f05d96449d688063b64753920222aa30a7b11a4f9d929e835155225a27cf3197504cdc390a9742a836f805df9d903ed151ab0d40006dd2be77cbbb323adadc52685339faf06fee2473ab45d3351c97d0ffca23dce28a1f239624bad698038c1c940dcecc57337c079ae5f7bc795dce6e688093bbdcf3ebff69da9b76264b7d97ab8f2abf87d40c4c3df7572272afa6f1844c7592fb642042a08a7026cb0bcff4f2b20a512d7c7a4025fe85e0585e80163cf83a6c7ed4545ecae04a34e7330fc900d8300cf738554cb41c50c703d1e990e81b3c4631363cd21ea157b9f47a02602e9882f3815efc15a4efdf685dc85b24b53897973dca297c9b06655f60a9e6facc0b742e735f3faff510bc571083dd43698c45f6f38a74907629c2e5abac01250c066516f64d2e5c35cbb26573f466c0be9bfe205f17338d02cfe9279642616d4265589184ca83476ecdde4486d0f2e64103857e7f648121ed4bf8f2b402d27ec789b0ed5e7d68f30330544c4a720121832f261f166dad12879264b64c4d888cdbcbeb047446fa034e67bfb4cc6b51db20eb4962dadc8f8cc8e40ef260f0e7d39921f926fcc3b4c82041360924d6dfe7074caf443a2801358c84662c56f0e8002832a6ccc5b3f59d8e3a60d93f4e23afa6b3d32e8d0dde89d1b872a4b858b2040e9c9c7dd271e3e419d10afe0cb31ff37ef983dc6fa54d1b17679e8c880093b07a706cf5b05376a1173fc6c50badd1e4491d7a44ab268f7bf3692eb768144fe3f4b2cc642357f2123d00ca4da9ef17a2194d8d88d2123cf7775f8b4e805410bc0c0dbdc33060fc6a78e031520b447f9a9df398bda3c61c54bbf00e234ac7ad447222cb7b8fcbe61321a815cbe9814aa7a694b98e3e4acba4c087a0f2fb630f282628e709779e23a8826965857e3c4a7aa2ccd44120fe5223ccb56163de2b9b934e69ecaff3b1664c23f96e0f8b23eb2915a77000eb0399fd8ff289784483ce13350732dcf75e7e887b12ac09dbc8da641f877facc8878d51e2e0616ce9515ecef4396003659c599f57b8acfa400066c972e968d76e279bb722f6df438efb1870cfe7b9c648204efc05daaaf13638c10b6f199568ec201466551cc854b6c687ec2b8425d291614b7b493d679ff5bba0fd633ead933506762db076f63513607f41ab3dd1b655ad1c9c29bf8443f9d58e8d5bb937b28c00000001000000030000000600"

def sessionFixture_session_responder : String :=
  "010000014e01000000b901fa7eb959824024a75ff72caac2c2801f6536a03c9f77ab0a7a342e764cb7b0090120b0f7776f19dc534b7cd38b4c3e9d7cce7680390f450a472fa47b30402c3a0e350938e847057d9ab36a0adbb208ecbb8a1e4290b8201c7651aaf8f2911197b001e5679489be01d1de733a79703405688343a95d2b6f4b084e498237caf316083d01a6df655109f0943c4c9a242d7b3eac77c9b10f049ebcc2cf3d6a5a4ccc0c6c220000000000000001000000000000000100000000000000008c0156e2462f46c7da22410a89138b976ce63c3a0c9663a7dfe078ab498e431a035e0000000000000000010000000100000000000000000145cebd925b32aafe3527ed47c5707701a5c1f62166bc388bb441f270d6cededc000000000000000001e06740126008303a1ce70d8d10a48cdbce1d826dd51373f58fe34ceb30b3101f0000000000000001000000000000008401050000000000000001f4918009fb615cf797128d55f3c542b4b5fb3dd19622efec566e6d87246253fab1f3a423153bb110203500a715d98335146957148558fe5bbcedf52fba96d593000000360000000000000060000000000000000300000001000074d3616cdea12a815fa535b9e96991542977c7aeb0b94202a1367e7ad75fdf01bd810108886cfada036392d52aa00da9b3d9bfa8d94016f65b49b32515963bf000000042057b4e909bbe7ffe44c465a220037d608ee35897d31ef972f07f74892cb0f73f13050faa684ed28867b97f4a6a2dee5df8ce974e76b7018e3f22a1c4cf2678570f200faa684ed28867b97f4a6a2dee5df8ce974e76b7018e3f22a1c4cf2678570f207b4e909bbe7ffe44c465a220037d608ee35897d31ef972f07f74892cb0f73f130001000000210573aeaa5c7753f83b28083cdfbc9b6f55f108e11580b1f7bd2f266aff173efd5a"

def sessionFixture_session_answered : String :=
  "010000014e01000000b901fb44e3ec6b4b8aa008087aaf89845243f95e721af64632d3e531364b601a952801fa7eb959824024a75ff72caac2c2801f6536a03c9f77ab0a7a342e764cb7b009c06d531ce4c8439dc1f568138b645991105c9d5b0c9169925ab653541dc82fd0016af29cd8ec23e93c05a8922ec5f47ecb89670f2920eb2602a9d9e64c2c9f37ef0144c72f1f04b1bc2c48adc71e79750ab01d3d5166780d70994e910d262ea4d0e70000000000000001000000010000000100000000000000008c0156e2462f46c7da22410a89138b976ce63c3a0c9663a7dfe078ab498e431a035e00000000000000000000000001000000000000000001e06740126008303a1ce70d8d10a48cdbce1d826dd51373f58fe34ceb30b3101f000000000000000101260843e36990adc114697973bb614c4be53994581f49cdd5aefd5564dcb0855700000000000000010000000000002f1901010000000000000001f4918009fb615cf797128d55f3c542b4b5fb3dd19622efec566e6d87246253fab1f3a423153bb110203500a715d98335146957148558fe5bbcedf52fba96d59300002e6074d3616cdea12a815fa535b9e96991542977c7aeb0b94202a1367e7ad75fdf013dc5a0db9cd7940b3f78088b72f63734032c08e9e266cda7c85b389b1471d9491e352723638a4e4cca5edcaed5775266705c9c0201907842173982fbe25574803a190cad3d7c1fba5517214c7b8b65912dd62868f4452fc352ed7c9e7a60aa2847afd5d4629138906713308e01c8476195eaf58ac0374ae9879459d7a3c6bc814ac85205595873971c7c491bda25473fa3aeed4a3eb8d5c09c418b44121e6d1bb21fa67c74d291d8169b931abd0da92bbe6b24a507ca6a7058f954332bf9be241874034798eaec42ba7c7eef943c3c931ed75b479158c65b84c560a8351841233d826a7666234fb3a4d96c1156d597b10b3f77cb60b84aae9baa01a34a2387435e08730507d66e2ab2c2b3b89b851709c462b59f12365835313f204ac64a43157b64656ab634513225bca810c84a0b4ca12da4ca8afc7f371236f1d090a82838e8485ac99bbc18a6ceefb767bdfc3609725b100197a4b523ed098bdda030576233a07629a943c347da3d8d4b24b4a463cef47928e642ccab523ceb2fdff0bc411c71220c2e2c58634e0166ed6c50ba0203a133c8d273c5c4ab6ce18ac1bcb046dc94813f66b32e354f1cab69f8539a4e6654043b98cf0ba2a7970f764650460c51bd86cf281470942a005739a44027709aac2721a13dbe5c85ce32079b451955201f2172130d91b7af10056f2613e5f193d3f72d562615bba04bc40a5919db12f2d5054a576db8252a2bc7944a37c86915749dc1c470db0b71f81109082a46ac1350d105d6006642a0c05a157f7a0bc831a7720b76a96244333b34107d722b80b1b4efa04adf74b8aae31c01d4c5ac99211d336d58f4ca91845c024633f1d9212a0380cc03939500b0ea974eb4294735935c63371ff92996e84881ffd4b30bf590fce7b449bb609a71cc9b72912029952426a00439cd228bc262a83acba980af445d503ac623e05773b07cd0f776b7a43e8e66c719c2689e47b55a95bd9dc6886fab1e0d087060f268cd624226360e112c12e1f404477ca7a78027f9a5544e83b956e1bf33d3612eeba2c91a15f0419117089a592bb168e0b2d6d812eaa7637189a594cac87e14827b46b314812b8214928193bb0939059687b74b71b1b72192cff895699c96f2c7c3c916643db65e4fd2cc588543b8d22e9ee2b61f6953a770b2d39022635655efb19940e542d2bc89a3f419e066923f12874d9bab74909b36b31689e196b6b3ceed005b8cd84fe7b59bfd53abc6775dfb14c22042629051cfa4e16616779a3814680d1971f0c1643bd043b8c68f62447afb67584516bc6f009437b126c163b2037c3a8302523a77ce21860751972e4d798d72d67c9ad1a7dec5093565b3bfa7c8e75320a9cc81cd681ab333b2abe4895a7c7a0bc20ffd0a4825993b59832870133209792806a657ca3c837d188405495e837bcbf0a90b74a1ae49c950f3891d743a46686017962ac3ba27bd5c11004ea5029fa9131fbb5033ebbe945a68d8c727f5544723f54a2c404b8b72884107cf686b586cf493f6f8362d73b037715e67999040c9c25ef199eb8bc3c7bc9745596f64621b4861bab451b437623d343b0237809c93c03a47203834996de551ba67d88c819b528f596098db087128a0ea426d5d511f26d8bad8919793ca400c2cac2d1348003a0ef407292a0420b0d2bde6b38d3d7b8370c61c22358d77a35ffb8055577659286c2f5bca9b5dca5abc766d21b9536cf14b6feccf1dac070e76124e414277389fa4da903176a97ca1ad984668a7089981204cc5fcbc9a5615878867d7bb7a787670008d75f8ac7b3b282386ec0f568577ef13c36600a32fe4188d421e55c0b12a634c472999eeacacec0224ba05b59038459fea13f4604e57d920be51279d42c9c7344674764a0829907110c14c8a958b443566806022e9412229cfe6b184e2abb437f86c0a8817ef073aeb4920afcaa9aeaa774344b6a86789069361f657449807c3c96740a8fa1b9ca76450c5c4221a05309a523ffb0b54357d4d9b2d519cb8f2787aa4ba58da2911bf633d5bc592b1e893807ca905137c724a5aeb354c4159ab26d3cf0598907580882aa618c9674d6cb229fb46292d06c1894331d7bb0132258318c395ab9298ff6ba0b504a2fdb9531caacc22084a30e72ace3980c887bda76066f454cec5d36208ea74207418766c9854b56e7fac1a0353a6518b0ce6a5b07d60389d0030fd47fa3804bdfad4ff4300b101d802acfa25018602b5fd6905d4002afcc9043efc30fe3a0308035b01aafcc3fe7201fdfd53063efa7efcc0030afa2afed50015004a057afcd4fb12fadb0061041804eb01aefc46fe0806220699f9680147063103f60466fd5402fbfb4cfe7dfd6b024904410516fa24fc2f0355034b06060415fdaafa80ffe30346fcd8fccbfe66068a013206e60127fc2200f7017f038afe6cfe2afebe05a8024afaecfe94fdecfb8afa4a061a016b03a2ff96fd94f94a04590689fbfef952ffc0fddf05fe03df027cfa04fedefa85037306cd049d0318011a04030099fa8ffb500565fca0fbae011d047203430105ffa3fdbefdeffeb2fae7003a0210fc920494006e0450fed9fab80324038c025e03fc02d6044e057efcb404b404eafb140683f94fff3bfc49011afee802e402cdfde8055bfdfb02af007600c3febc003a06eafc7dfe55fe0301470409fcb6ff06fc2dfb50faeefb81ff1b04abfcda02680413fdb905befcce0568fc8bf95201af029d0066fefb053d0063fa7701f5031505cf0512ff410635fa22ff09fc81ffaf026f06ff007bfd78fe6c03f104d5fcdefc1cfc0c060cffcefb2b0161fd32faa2040d04970047fd57fd01fa730628fd79038efe5dfda3fbddf93cfcd7fdfafc74fab7f9d4ff4ffa0c052afbdafab0fc6ffb27ff3201e1fb1c024efbd4ffbbfa8cfafcfa2dffe9fc5d0320fc3dfcbc04bbfedcffa30255064b032f03d2fe73fd3704ebfeb4fd1f05a004b7010cfcfbff48fe7402dbfec3ff51fbb1031efe00fb7c063c02ad0509fb5cfdf9faf6fe14053702f404edfb2006f402b4f911fe3f02a702ce04de02efff8ffb6303d800400240014dfe60fe47fb3c053b0112fdb900d4f9d5045203a9fff804b9febbfc7f05570602fd4afc0e0379061e0420030e046eff170670fcfdfbd5015eff1dfa920046051e0086fb2c00d0fbb705d7f966020a01d9028bf9b5fb7b03ec04bdfd65fcd6fc72febdfa350066fb58002a0000fc8803cbfd7703a7fdae007d0682009bf94afeb8fa61fb28fdca04d5f9b9032306b1fd34fab201bc0051fbcff9dffc3c0686054a0649000000aa05960356fe7afeac0411fc07038a0033053cfb6c064ffb03036d02e3ff0a0698fd0efee7fa5f03ea031506a6ff8d0454007004230597048bfbe8059cfa04061d03c0f987fba8ff2efcaa05ba0341fd6f0266054801d005d902a705cefcf6040ffaae04fafdb8fc2dfe7702830555fbfdfd5706ee03c1fa440401fd8dffa40456fec7033f0621020d03250244fbe10093fdf401cdfe03015602bcfccb023c0230ffc403e2fb3e037701fdfe55053cfa15ffbcfc6a057604ddff1b026b0463ffb60050007d037cfccbfd51047bfc030648ff890104ff5f03d4fb4efa06062afa21fc2004f2fad9fcc504a9037a03e4fe5500d004aa04f0038b04af057dfc1ffb83fab8ff4afb8ef957060f01210375ffde04f3f9780258fb960329fdd4fc18fdc5020104df05430041fae3fae003f00257fa45fda4fed5046603a6feebfce1f9a10117fa87fe15fa2500ee0090fe5104910330fa68044700defce304790221008a03dcff130168fbb503760286fe210382f91903e905d6fab7fd96fbec026803eafa33fff8fd5cfa9bfa1dfa7dfebf03350267fcd3fa3d04dd040c01b9fb3ffb6bfffffd5206c7fd8bfe40fd4ffcfbfa1d0224fcc1ffa1fb0b03a502c1fd24fff3fe4502d40379061e0065005804ac019303ecfd090405039102ee026203d4041400ecf9e6f9dcfb1ffea7fa540095f98cfa9dfc2f03cef9c900b900f8fb12fe94fa57021303930018ff35023e030ffb3a037afdccfa690697fdf6fb55faf500b803b2fcd002f6ff87ff4dff4b01affa860179faf4ffb4fc9f003a065d0228fe1d0100045005fc013afd9c05b4fb17fb4005e1fab8f93b03e7ff1b03cafaf7fafcfe0b01700118ff470596f92e0524fe7efa2204d5039dfa68040c04b7fef5025f008f028102fe0119fc1400830061fae6fb88049b05da03ea020503f603d002ad040cfcd7fd4f0349ffe1f94505d80266014c05550303ffb005e1058dfa29ff51ff25fed1fbd9fce0005600a4054aff26fa8904d8fb4a0217fbd7f9e0fb4d0564016f0301fcf502b3ff67fc14ff5dfbdfffb9fc790482fe44029d03fdfb41fe240445ff43005b069afb6c01feffff056c06d40037ff43ffdbf996f9fdfcd600ec043bfad4fe78fca20119039a02300100fb54fb95fc2206f705a9fb87ff21fef703acfc5c04b2fed903fffd050491019b00c9fe76fbe20378064901f2ff8a053606790439fa290074fc7905090197035a007afb9d0520ff99fe750354009f0210fde6009d0248ff2b0516ffc300fafce1fa30001ffbc203dd0267fa4103affa48fe0f03ddfc9704d1fc1bff28025eff670043035404e303400373fa46055e0466fd53041e02bf0511fd49fca204c4fff90030fa7b0692fd760133fda3fdcb02520030fb260507fb7cfb3805d5fba80458fc03060006b40342fbd1fcc30129fc72fd8fff35004a0332017205be050101e3ff0efed0fc730417fa57fe5f03b3fb5ffbdb02b3fced00f6008dfb16fc2006d10294fe0cfa65031d008f02d2ff67fa87ff9d00350244fb9ffff7feacf9cefe1d030efdf9fb61005202acfa13fba0000106b6022a04af001dfbcb04e6008405f5fe0b045eff78062902c1047701d6fce5fac1fe35faab00b6fb53019af963051effb90133007105e2f916fd5301e405270063005b0472024dfde20198fb6504bdfc90fddefa2c011400de0389fe3003b101ef03dcfa77fe3f0141fcd3013d05430458fa69fbe700d4013ffba7fe20fad6fc2cfd11fc5bfe730567fee3054c0043e312af24916e6bf7502cb500bbd90c1b556694eac8a9f99f0afe0f9c1b57b2370bc304f70945067e03770746097b077f0a690b090a9e0b3601b40b4d0004053b01e209a506510834021701920c970c6901b308f7082e012500cc05fd0ccb037b025e0bd706bf08ac084b03a501a601350468052b02c602730adf07cf00df09890959017e0a3f01740bde01ec0b9e0b1e036f051b00ef02570a7109d6031a0452022009ef0277017b08fa049c022803b50ab9018f05380471011b07e100bb04e409440ac707a50050091c0464055c0a220c3a07af0b650098096e0ad90b1102310cd4062e078f07150aa60492029e0760098c0b5a0ae00848050d05600c6a08a2098d0cc70a130a1600050afe096703a309d80c44025904a302f7028f0099025d093c07f202a3041f044204e90298033a034b07680c5b01a50609057904420bdd0431090e00560c7d0605007c088603b80a7d0cca02c305bd079209380abf01f909c503d60c180a120591008a03a2069401380c1c02b90c4207290837006a0b7b00020593020a0135064d074706010cc60714032a01b5050a0bd2004009f3091505ec0a2d08cb0bf5076e01400bfd0917027e042e0ad9007a0179088100510af30c2b06da07840c5c00750c28043301720b0403fd08e406cc06d5044e024102c501be05f909910920017a05350b800203076e001f09130c0a094205d6055903760909029f025503e9003702810c920301053202080bd7029d059b095802e500220b700c82046f0aa6091f062201f10cfd02b90574085c07d8089701b107a40a0105c603e602da07e10696099b09b00c1e015005bb01f10a0a07ec0be503480bad0ba70352062e060509d800a6055c08b9053603660cb205ab0b5708b70773030308bc023f02f9068706ec0a6706a10949046e0a3c0a2d0ad7024a000e0abc00a20bfb0ce800a7014f04180cd808b003690adb08270aff018e0448088706ae0c6605700b9302cf0cb00a25090f091b066d0552055a03a0092a0910042203d6008e0292068600d10b70078a048f091309e5001105e8031802400c7307d302e109970b1c00b7097309930abf0506048d08b3033d0b600940000d02ef0929038f009b03eb04270b1e0500097b02bb07930a3b0c9304aa047b0742062a08530c4d07c8072b044d069f0c1b05740a840cac0bcb08ed038d04630785050107de02f0077300090841064d08fe00320a7a0bfd055103820c210097074a02d50c0b09ac070500c1074900b508c5087805ca04a00b8209e7041806c506d40c640a3b034d02320cc602270a6a0caa0c3207ca077a02320417029604b908840bf102c8046006580a980479051204d40c83030b0ad509c107e509360a73077c0b6804a500900c1203c9062f04e10c800b1d06c207dc0a3a098a0114048204b904330868005508b900dc0c2609030bea0144077409eb02b3063b06a407dc052f07650745073f053809dc09b709f8031d06a202530217074107c70c2705a40cd405f30a7a0114030c023c07af0bbe07ff063308610174062d0ca400e503a90a2a06e509ec031602000c69015509200724097d0b170a980b4507910c330970001a0c8409c4077f076605b1058a0a98096d01f502bf0cb10519016100d20ce9054705d503a407bc06d50c0c07240ab607d00b64012009480bd4057d001006340a6f080509d708d50c9f0c1a0632099a02b30a2104df0a6402c404210cb403910bac04550cfe078a07ad0296059b0c1502a106c6087e02050354015c08560c5100e7038804a10cdb027206fe0a9507f70b3b029e08ca0833000701e902500af30b5304b102a408b70c83017103350c4106b105250b7f03da06230132063a06b40713080d0baa023407c1029609000b350cef03b7075f09de0c2f04f400260cea05f601fb0cee071d0ac600e9084007240b23017803fd0b950c29098e07bb030f08660bf40bac0168027907f5046d05980b9c0aa60bbd010109d807f4081307f002c7093b03c607f60573067b021807b509320bc007fa091203aa07b60a3d0367074d0365009000cc0aab09c60adb03bc010e01af071009ee02d402e20b1809da085508900b4d00dc0552091b09fb0459026f01f20362044108ac09050705040606ce0cf9049c057f05b807d607db0892045706e6024b05770cb0000f0b9f09bc0004017404ae0238034401cf05440ba10aaf0c660a3c03d105cf0a7401f801d8081b008d04cb0be80c5603920069070d04750bc5022f05b60046090e02d509fa030a0925063502e4038d0a6c0454088d012607870873014f02650ac50b56022c0762022a08ef098600910a3400dc0bce0097023606f5062c050d0bd60718088f03a104d50040093c0735045705a30a54029f0a2c0be60657099b067b011e00b8025c08700a5d040404a6010c075d0c82020b071909b30583016a0b450a9f06a203150343014703a20b310b690433008e0a17036308fe08d9017d0ce1028300d20693016f015b0a7b08b80cfa0a0a018208cb0546085a05880685096006460ce6013e07b30059002505ca02b207d10739086f031605170ab1080e02ea05f5045c06ca0755007607f108e809520b730a41043b01b0020c09010a420a2b02c1026b039e01ea05e606bb0c6f011204e201d3093c06fd0334067107d10993056908de076407e206fe04c80320069c03580264082e06eb0b4903ed03390bf8083a046e02380253052405bd07880ba10b7d05fa00150a28009c06a90b2c076003cd0b8104a30c9a079c01ae03330091088c00ae038002a8068102ef08a4042000920a1f0b6e019a03f3066609bd05a901db09280650064403ba028200840aab0c57032f0cdd02ec05780c1a05be0678039108900a77086c07a603cc008f02ba005002ec05eb000405a5044c00a404df0a15093300020bec02bf0a860b4206a2068601d0010b07890562013f05a90cdb0c8902f60aeb027101600abe04a707de0376072e0ad702d10ad0041a027c02c006560b2602a30b41022309d905e10a860b4009c3056c0b0c06aa0b87062d0cee00360a6f09e005ba08fc00ea06de05770ba208ea031c0ac306bb07af04ce0aed0a4300d502a204ba04fc067304e20816008403a20b8c0add062104b609ac0a5901cd0c9e0058060a09a40c960024073304c6043a010d01e40254041101030667040f0ba002100b7d08e508330976015f05e70a27011b085201c90665090101d7051708db028400bd039909cd0ac40200041401390cdc085704f402d709a70a1a0cbb076d078a01bf0ba3039c032b019203ad003409c6050402db08bf0b13004d030905f10b2402fa00b2039f0064066706fa083f08c9066a02b50571003c0a760a2c003f008307d70ab90be409e0080e0c69081008d009cb032e05af02b30123089d08040cbf0825042d0a1f010906b504d508b109cd020c0c250553021e0cc5060d03590b1e03620bc9029308730b8805c2085d0c2c08390ad70575036d07c30c63041d093e07b30955097207cc0587067306c3005809840875022a091d0c05021600610a8201b50a89031206ca084108d302ce0b670436064e007c05ca02ab0caa08ff0a7702b80afa08ae07850afb014a054d09bb063604f7044309850c5b07b0076c005a063309b5041005d2081e049f0692090a0a2f0ab3037f0bb500e3012a0aad0ab40224072a0cfe0aa40715093c0964056b068f069400a1026903bd05a00b5606720544042903b8032e088a0860098208ae03430a9004090608086907b900e104e0090f091a091d0a32045506ce09b109370be900b901ce0351092208b9096001830750013e03c4025d0c4409cd03e8059903b9088a0b94000705490582024c054408bd06280cc50748001d05c20bd40a4e03fc0c8e090c02ff0641029c08e60b330cc4036c094a0ab208a60b8b002f0460084f0ba40bc6043d052b035f04d900be041c0a05004f0bd400e104ec050006b4027d04b90bca0ae10c3e0092060108ab0c1700eb006905fe03a20450059e026c07630b1f00ca0c8004190b8b055901800b2208460789018c01e002fb0b45071005f204dc03620bd507be0889044704b406d108c2007f009d0b3f08ec00ef02b502b408670a1505fc05f90c95035005e307f706d80b820430082a01ae0a910417017f019d0557072d088300430b55011d0a48092c0aa204cc02ab01be04cc090b0b5d065902cd0a77031f09db0c3404e9021c0bbe09ac01cd087f005c00710bfc05620a8d0485015b021a0b4c08d20b8208c306ca04c705dc07750cf9069a045103ce026405d708b007ac05e706a3004a06c802250a6e02f203380c4f011c005c09930a2407b1020b0a910caa039703630415086f045102f3016d069903570a40086e023e08a5015d01620b3d06f70c500cf90974096e016309c9037c03f401d105d402a2058000300522034504b90949082f05bd01ab0bc304af0a4d03340551053507cd06410288058a04460ba60c9d02620be209110947091300b706b8046c0c1c02de0b9b097e0694008a01e0068a047c0b270a8906e5029701800691022109860a3f04ed01e9032d060d08bf099e034701d0069604c5017801a00ba905920a0c0c88063005b7007202060bce07f1053305a3032409e00a2c071f01a1075d0a3d05660a39065c05b107eb0a0204340518051107ff0095049b043409c0033b08c90cea020e0aff03000ab90b7d08a7099306220a2a049e0b4c0ab400de0c5601400164049200f30863083c06c90362050c04560a8d011b00be06100c4f09ac0a3c064c0488044407fa06450cc70c9904090073029901c5016d03cc0b6805f90a4e09b002640a24035a06f407a908a30b0705b5035e06220ac606380304050e026b0956069106e805b7083f0326049204c909100cdd0900094407f104c305ec08dd031409150560025d0c89030a03210990067d050d0be10186045605d10a5e04ba0b7d05c1001502ce0951073c07ef023f030507940631010a07b806d9025904ea0140047a0b1c06aa06b600b50af005e3046d06fa0c2f0c2d03c905e201fd081d00160b720359065806a70688054d00c3088801c200030c1106570bd803ab067000fa014f089905c9029b014b01a201a9065d08af094805fa0928067904e9006702010830062d00e0003d096e001d07c302c308bf022e0997012501fb097a0b1107bd00b304440cd207ba0c72040c0106031508c70528079e06ab03790239025905740c560304036b0194080105e80555065b03b406250bca0b5e0ad2049f056604300243072c025a06830af305c50558016107d8073c0b930b2107e4076b028d0c5f040a016e0a810814028b06240bd00c56019b08cd036c089b010808a904720ca40ce50b94078c0bcc0930098d0cd50b9a0a6e03d800740b5507530a9f00bf086c0c230842081d0c71043201b7062103030c5808a10b8404750404036202a6087109ec07be00e00c090ca306b301c703d8019c0c61031e0b4a07d3028306e605f2008406b80a1505f604960a6e09650c7208220ce3020e08f60abc028a0a8600ca005601a2048b0c2d0a0e066f0cb90c3205d30a0600e2077e0c710836041f024807f60ca40447071a0972089905e501b8074c059f03850a8204e0073d0ca7057405690bbf08de07e50971077507800053075a020c00a70b49033f0b5e03bf012e05e308590c3902840a8401850cfe01b00a3c003507ef05db05e70bc903af06800ada070b02ee068f0c1701cd00e2000c0a0b08500907037501f5032805d50bb907bd0481035e047809310a0e0b86013801540aa20c4106f2098f01d3010a07ca03b8080c09f30156007509d308fa09f80c280bfe0bac070b01b30153029206a50b150c8a07f506a10c9902fd0628016b06a60867074104a803f600da095f0a89071e05c809510bac0b670c250c0e007f0ce900360067062d04e60965032b08d10c550620044205610a0501640a7608ed088b09dd097704c102fb05710c0204d5022509910c9b00120313081a091e0a24038606f90b5e0647082601320a1c03d503e6069a020905e009d2001304e10a1109fd006600000a0200160c470bcc0a1907bc0538086f008f0539076b04e40a340b4109a300f905be00c0058d0a8a056f012204b708ee07070643052b053f051901e107cb03c304f803c001590240077a0b8a0a8109f105c00641085b0c3301dd057c06ae0b2004cb018c01430c430bd80cb1038407fd00480cea03f80320013e041908df079a021808910b6609c507c70137017004a800bb0971005907af0af70a4a0c510988061b001a07c801f2044a00250667023b089a08020982045a01fb03ac06db007e0144048801600650018a091c08a6012e0c2b01da0c2e096603ee0b5d08700377007205c7037704bd046d0a9b05b4019e01980c78055709250c220b5102a6016200b105ba0666070c091f01270a3706390831072c07340b0104d000b605980bed079708b80727081703d90283007700fd0b6401ec0ac3005e04ca037f08c9049d04760b21035e0b94046705580c3d094d050f046d0294079407c5041c0b490a2f0662010d01860cee08410946076d00a005c2033c09b7084b0778050e0985034a017209b700ba08820ca205ab05b70a4d0b7708400c090c02021d008702b2060801ef08160a6a01680cd60c84054603740554018007820cd10c8a06b3018900530ac40a2b09aa016806f9060701c605110ac3066d0ceb0c9f0ad20ad5007601550cd10026033705f80946001b07c60609085401c901a709eb038e091b06e704e200730554093a0a6c03230308043d08ca0c4a006d08a00ba903b8003103a00cc30414077a0b31022208c907a5089902ae08e707850ba308b905500ac8005708cd0bf403210a7c04b100a80b9008da04e3047d01540bda0b3d0c850936091906b10cbb0a940bca06ad031f04770394027800bd06530661000508ce007407710c3d0860037806d607b909f100e2041a07840cc0029b06ea017a0a1803a00cc100a0004702630cc7089001e90c12027c0672056e026601f1043c0615085806670c000dd00c9d04bc092308bf085c05cf0ba00782016a078504ae001d0977056c04f4009c040000d80047060e0cbc042a025d0c58024301c40bef00970573077b08ab035607ae06a80486043107170053076005980404098b0504026e03040c11076f0b9d04aa0a610a9c00390c3408470b8e043b01a80986016309da070c0524096808e207ed09a007f207a9008e049d06ef0a1a05190b20085404bd0bef06f701f10ae108d008870699046307070064041d071b0a2a0a1702fd00180c230b0c02ef075e01370bf209b503f30afc06f40609080304a2004f003a08d8082e0190028208340a4d059408230cf9021d06f60473080e0a6108460a310706085306a20715032d084509d905bb08430a74013d01b700b003c1043b03b407700bc6093b0b3507ea06c70a54022303570b14077502930a0503f20699005f05c601fd04e401910cc006530bb301810131007301740b47024f0af1023f006e051d0c76033f008f0557085e0b6d026e081e0afe068f01ca09fa05c709560a810bf201b1002b04cf049e0b320c430b04023307780b07095c08940cc00cf809170aaa05f80a9a0af707320adf061c064f03230402053c09e0067d035e083b051c06260b520c960a1e05de0823033f042004bb094d0489025f08340c0c00140a4d03f20bda0343098908dd051506d608b801f50aca034c0159090b093f0c9501ba01490b0c083904fe06ab0c7007430b290b6e0a6f0bcd043d04c906b505180299042a05b7001204610a9a046d07c80519081f08660983001c071e06390389098c072c0c8208ec0cb50a030c580b5605e7095802d408350c960389006c06490af105680019061b08a10b7b057e0b6d081900c505f40a910c3a00b604700b4a04570cf500ff0c3504610bb701a4039c058d0c510a7f071c0be6013d058c089e062708480a2b0a4b063109b00c3700d60717016d052007650b06003a0ce2053a04e40133070604e1091e0a07095109940265087a0cce0abb04e308fc004e00d70243071b017b090f00ef02e105b40a5a07170cdc041a053e0217004706e300d7078e06e207560a370b61077e00e20b680290020801740bb40b35011000990ca504d90add0b1a05f104b402bc0a19047400dc08bd03cf0b8600810a1e08a7079a013e072800100cb9009d0b810c650a7d07b6080f0c4702f2084607a0096b0c4900630bfb003c07550cb604650027051401dd01100cb5004e00410a1601b603b20c870cf90c9c071503a60a7e0ace016d09d5034103100a0a0bf6079d0b83046a0af102c9079d055a035f0cbc07a503300c0a030b0b78005804900c7100a2048e013e092e01a804520b5802030055068b0b430cca073f04ba022d054a09e504240ba90953036b05fd068d049f089e050407e2092709000abc05690b9c0b5b0b8904cd0b7103ad01d308f4058800ae02e90c370c990965025103e2076900dc076f08300c6e00e30114099c00ad01cf07cf08f906a70a5307940c4904b10ac60b5c0cb309d20bf2092d08b6037a01a2011a0755038508010b3d07640b3f0643069d06d3010504a90c12062f0c710923037e049b03090c950b8d037600c7053808a8001404e80c940b31098407e5057c086003fa071006950500099f0b6901ec05f0045a047a06a50c50016208c70adf00eb03830111075b05200a9105460bbc0a6d026e0a1f03cb071004f20a9c06720991006000ce08a701210a9e079f08f506560959027508fd094f0586062e0a5603ed0c4f05e707b503c50b7e04a508e307d6078c069c0ae904ad05f80ab5056a0a150102073c0347006706b005ff064e03aa0cfb0ce6059e07f605a104d90847067b035f042f0c8103bf0a860a0f07aa0b0e081108f70b6008bd09de0238053002b201000463015004ba088e014a000302d206b8024106b80c3d0c27000308b601980320070600ca0bbe04ef09a500350a66055909e704d80b7e0327072c085803ca02aa07de023e05c707c8041e044c0c2806c7096307e00c590aa30c8e0970036b0b130889021703e708930812067500530b040b2e0bdf025a01cd0a0e01520a300ada072e07ed0366076b000f00610b3d0348067e03e802b900890b850651080c0724053d0a3c092f021807e608ae00410bcb0ad60669015505ad051f0b5c05d403b707e0068a0ac40b4b074c093309c709f00c80070d08b4023000ca07310650096c0abd0a4e0cce028e072e01f303fb012105f9040900fb01d6080c0307087a0580033504200c900b32076f025b09b80659094c04190837035305e5056002d100b909970a0304bf07d30be80bf2015f002f086e0007039003ef0b0309eb02a4045e0ad5002805d705ec01030c1f003802b604d200660940051306ac0440036e073602030a720645083705ac04d80a6b0b75040b0c2f0ac4019509880ccb03f305e50c4b0452061e09d307200930017c030d04d6003a0131058f087e0c9707bf05d500e6000a0ab504c304b50a4407c401be0b2a06ce02c905db00f50aaf028c0866045505570cae0988026704bc089408c5056707b304de020c053c0acf055806fa038c0716024707570a0d07a708690099023600f90cb708d7051c00970149051f022207920352095405ed02dd077e0a2204dc039404b503fd099703a402500b6005e50b0703a809590ba100b707cc007607a20ce103da04c80ccf0818047e01000d5b05de064d0a58006d03cb05970049091e0c7304720270052b028203b50a8c0c410628003b033602170baa09410a6b03cc0ad2003d01a9058f03980c150b21068f002c00200aef0688047505cf0541084f07c40977083f03f7051d045e035e026c06c10a0b0c0c079f0ac00762076907d703080931011f092209b60422073a03ef079c05250060050f09e20337044008c205e20060076d02ca06800477001b0432084301b3023907330b190487058a039109f9025a02880bc309a70032004900c902540ad701b6026c08d30a000cfd06180856097f08f808430b140cc1055208ab021b05400c9302eb04430434038808210b7c0b1b06970aba046b05f30a88002f0cf3080e08de029c090e063e08900ae50793029d084d02d308cd016c00bf02fb0ce509b8057b091f07820cc9044a0ba80bd3080a002e0345022b067706590470085b0b0804cf0a1709a80b4f072f04010b2104d305d201ba0ac60b820adc038505e408030b2e0948096606020a3203b406bb03b00c8d028605360c7400cb0a320afd0ac307e3055605b8095f007d07530a13004d025c001a063906ae0605030506d905320931008305b70cca06310612025e04ee08790b67052c0c0906bf06700466097e02d1079f043e057a02590b510ae809fd00da0a8d057b09190a2d082f0b52067901b60056090206f4087a01650ca30082058b0731049505d80881086b01a4000a02f302df0c360a560c2f0c4609110aa504ad09430a5d07d20640044806840c68057101bd0c9505090b20079606b803fc0214091203450ca70774099602270b6201830448058e0a75096f00f601880c770c9503e004750a170606092808640560002b02ec025205e6085d0a4d052408cf0bd30b82094a01dd004b062c0cf20c200ca1091d009d0b87087e08c908f1029405d40802068908b80b7f0c5e054c08520c300ccc0aaf046f034f09a5044e069604d102cb08b00be90b500518015f0234006e02b200300af40b3400fa047a0c7800ec0a440307082600900670088a0c8009fb081806d809b3022c06ad08a30cc7009401a80c130c2c0a78033d034507ae097006f400eb016c05b302030cba0bee028609ba0a9e08a802d60159082d088f0a60015b09ee050e0c200b85014b03070a8907b40837070502a4088e0bcf0c4c001002110b3d02bd03b509620b81039302670bf50ce9036d093a0a10077b057305bb077a054a03fd05d902b1097109ac0749098b05d401b80a800a640b20034008be054a001c0807094b00eb04d4066407650160018d0033028203e305540c17093305bd0835000e04e50c410c370a860588021c08f40af4080b0b02003a0b2008d70c950a8205290a4e045d0bde06af0c620bfa084f046202080be400eb089b0a8204e102af0992030c0b65043a02e50cf40bd4034507270a7d0a4e01e60115033b002008eb05a50066000709aa003a00ea02ba090706070b02083702710359048e06cb0070060200b108fc033e011d0b7d00db067a07e30cce083804fa0381089e007103ee07110be104b0092d090f042d09180af103eb0059045f05dc0969023f0ccb052f0a7307830c7f04cf049c0b5f060b07e101f709ce05ed00f208fd072300cf005a0589025d01c007bf0a4f09ac021101b103be00ac0417093c0bb707fd01ae06b5072e036f090f0bbd0a2f020600b00684076e022007bb0405079605c60ae00c1e02780c57058e066e0cdf00e3018307360cc0084f05190b6309000000670001000000000374d3616cdea12a815fa535b9e96991542977c7aeb0b94202a1367e7ad75fdf013dc5a0db9cd7940b3f78088b72f63734032c08e9e266cda7c85b389b1471d949542d6804f537000de61cea08c4f0f5f2408018405a1a4fda7770acd7b7d785c65a2dc92ceafce1afaef3dc760aa90728bebaf4f79b65912067a7861e173239dc00000042057b4e909bbe7ffe44c465a220037d608ee35897d31ef972f07f74892cb0f73f13050faa684ed28867b97f4a6a2dee5df8ce974e76b7018e3f22a1c4cf2678570f207b4e909bbe7ffe44c465a220037d608ee35897d31ef972f07f74892cb0f73f130faa684ed28867b97f4a6a2dee5df8ce974e76b7018e3f22a1c4cf2678570f200000"

/-- Small, checkable fields only: the halves are kilobytes and a reader has
    their bytes already. -/
def sessionFields (s : Model.PersistedState.SessionState.Session) :
    List (String × List UInt8) :=
  [("ratchet_private", s.ratchetPrivate),
   ("our_identity_public", s.ourIdentityPublic),
   ("peer_identity_public", s.peerIdentityPublic),
   ("identity_ad", s.identityAd),
   ("braid_tag", [s.braid.tag]),
   ("braid_epoch", Model.Erasure.be 8 s.braid.epoch),
   ("sparse_epoch", Model.Erasure.be 8 s.triple.postQuantum.epoch),
   ("pending_initial_present", [if s.pendingInitial.isSome then 1 else 0]),
   ("established_ephemeral_present", [if s.establishedEphemeral.isSome then 1 else 0])]

@[never_extract]
def sessionStored (id comment : String) (bs : List UInt8)
    (expect : Option Model.PersistedState.Refusal) : Except String String :=
  storedStateVector Model.PersistedState.SessionState.ofBytes sessionFields
    id comment bs expect

def sessionBase (hex : String) :
    Except String Model.PersistedState.SessionState.Session :=
  match Model.PersistedState.SessionState.ofBytes (ofHex hex) with
  | .ok s => .ok s
  | .error _ => .error "genvectors: the model refuses a session fixture tacenta-core accepts"

@[never_extract]
def sessionStateFile (_ : Unit) : Except String String := do
  -- The responder is the small fixture, so the refusals built from it cost a
  -- kilobyte each rather than twenty-five.
  let base ← sessionBase sessionFixture_session_responder
  let baseBytes := ofHex sessionFixture_session_responder
  let mutate (f : Model.PersistedState.SessionState.Session →
      Model.PersistedState.SessionState.Session) : List UInt8 :=
    Model.PersistedState.SessionState.toBytes (f base)
  let accepted ← [
    sessionStored "responder"
      "a responder tacenta-core wrote: established_ephemeral present, no pending initial"
      baseBytes none,
    sessionStored "initiator-unanswered"
      "an initiator that has sent its initial message and heard nothing: pending_initial present"
      (ofHex sessionFixture_session_pending) none,
    sessionStored "initiator-answered"
      "an initiator whose peer has replied, which drops pending_initial: neither optional field"
      (ofHex sessionFixture_session_answered) none
  ].mapM id
  let refusals ← [
    sessionStored "version-unknown" "a first byte naming no version this reader reads"
      (0x02 :: baseBytes.drop 1) (some .wrongVersion),
    sessionStored "empty" "no bytes at all" [] (some .shortOrMalformed),
    sessionStored "truncated" "the last byte removed"
      (baseBytes.take (baseBytes.length - 1)) (some .shortOrMalformed),
    sessionStored "trailing-byte" "a byte after the last field"
      (baseBytes ++ [0x00]) (some .shortOrMalformed),
    sessionStored "sparse-epoch-does-not-follow-the-braid"
      "the sparse ratchet's epoch one past what the Braid's state tag allows: outside the relation the sparse ratchet refuses the next agreement output on every message and the session never recovers"
      -- The Braid's epoch rather than the sparse ratchet's, and by two rather
      -- than one. Bumping the sparse ratchet's breaks its own reader's rules,
      -- so that half is refused as malformed before the session's relation is
      -- reached -- which the page predicts and the generator's guard caught.
      -- Two rather than one keeps the epoch's parity, so the role rule still
      -- holds and this vector breaks the one rule it names.
      (mutate (fun s => { s with
        braid := { s.braid with epoch := s.braid.epoch + 2 } }))
      (some .inconsistent),
    sessionStored "associated-data-wrong-orientation"
      "identity_ad with the two identities the other way round, which is an AEAD failure on every message in both directions"
      (mutate (fun s => { s with
        identityAd := Model.PersistedState.SessionState.encodeEc s.ourIdentityPublic
          ++ Model.PersistedState.SessionState.encodeEc s.peerIdentityPublic }))
      (some .inconsistent),
    sessionStored "halves-disagree-on-the-role"
      "the sparse ratchet's direction flipped, so the two halves no longer agree on which side this is"
      (mutate (fun s => { s with triple := { s.triple with
        postQuantum := { s.triple.postQuantum with
          direction := Model.SparseRatchet.Direction.a2b } } }))
      (some .inconsistent),
    sessionStored "peer-identity-not-canonical"
      "peer_identity_public spelled above the curve order: it is used as its bytes, in the associated data and in what the session reports as the peer's key"
      (mutate (fun s => { s with peerIdentityPublic := List.replicate 32 0xff }))
      (some .inconsistent),
    sessionStored "established-ephemeral-wrong-curve-byte"
      "established_ephemeral whose first byte is not the EncodeEC type byte, so DecodeEC does not accept it"
      (mutate (fun s => { s with
        establishedEphemeral := s.establishedEphemeral.map
          (fun e => 0x04 :: e.drop 1) }))
      (some .inconsistent),
    sessionStored "established-ephemeral-key-not-canonical"
      "established_ephemeral whose key is re-spelled: it is compared with a repeat byte for byte, so this would refuse every genuine repeat"
      (mutate (fun s => { s with
        establishedEphemeral := s.establishedEphemeral.map
          (fun e => e.take 1 ++ List.replicate 32 0xff) }))
      (some .inconsistent)
  ].mapM id
  pure ("{\n" ++
    "  \"schema_version\": 1,\n" ++
    "  \"algorithm\": \"session-state\",\n" ++
    "  \"source\": \"generated by tacenta-model Vectors.lean (lake exe genvectors session-state), from Model.PersistedState.SessionState; the three accepted vectors carry sessions tacenta-core exported under the counter-based FixedRng in lifecycle.rs, because the model does not compute the curve and so cannot build a session whose ratchet_private matches the classical ratchet's dhs_pub, and every refusal is one field of a fixture changed so the rule under test is the only thing wrong; the semantic rules carry the refusal inconsistent, which the page distinguishes from malformed; the generator writes no vector whose result the model does not give\",\n" ++
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
  else if args.contains "session-state" then
    Vectors.printOrFail (Vectors.sessionStateFile ())
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
