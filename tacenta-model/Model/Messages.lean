/-
Model.Messages: the wire encoding, written from
tacenta-spec/protocol/message-format.md.

Encoding is where a format can be quietly wrong in ways the key schedule cannot:
a non-canonical spelling that still authenticates, or an associated-data
concatenation that parses two ways. So the encoders and decoders are modelled
here as pure functions, and the round-trip property is proved in tacenta-proofs
rather than only sampled by tests.

Wire-sensitive constants are gathered at the top (message-format.md,
Wire-sensitive values).
-/
import Model.State

namespace Model.Messages

open Model.State (Key)

/-- The message version byte. Wire-sensitive. -/
def version : UInt8 := 0x01

/-- Message type: a ratchet message. Wire-sensitive. -/
def typeRatchet : UInt8 := 0x01

/-- Message type: an initial (prekey) message. Wire-sensitive. -/
def typeInitial : UInt8 := 0x02

/-- Type byte for a published prekey bundle. A bundle is not a message and never
    travels as one, but sharing this framing means a decoder given the wrong
    bytes says so rather than misreading them. -/
def typeBundle : UInt8 := 0x03

/-- The identifier meaning "no prekey was used". Wire-sensitive. -/
def absentId : UInt32 := 0

/-- The `EncodeEC` curve byte, the first byte of an initial message's `identity`
    and `ephemeral`. Wire-sensitive (CONSTANTS.md, `EncodeEC` type byte). -/
def ecCurveByte : UInt8 := 0x05

/-- The length a bundle's KEM prekey must have: the ML-KEM-1024
    encapsulation-key length, 1,568 bytes (FIPS 203; CONSTANTS.md, Bundle KEM
    prekey length). -/
def kemPrekeyLen : Nat := 1568

/-- A 32-bit value as four big-endian bytes. -/
def be32 (n : UInt32) : List UInt8 :=
  [(n >>> 24).toUInt8, (n >>> 16).toUInt8, (n >>> 8).toUInt8, n.toUInt8]

/-- Read four big-endian bytes back. -/
def readBe32 : List UInt8 → Option (UInt32 × List UInt8)
  | b0 :: b1 :: b2 :: b3 :: rest =>
    some ((b0.toUInt32 <<< 24) ||| (b1.toUInt32 <<< 16) ||| (b2.toUInt32 <<< 8) ||| b3.toUInt32,
          rest)
  | _ => none

/-- Split exactly `n` bytes off the front, or fail. -/
def take? (n : Nat) (bs : List UInt8) : Option (List UInt8 × List UInt8) :=
  if bs.length < n then none else some (bs.take n, bs.drop n)

/-! ## Curve public keys

A curve public key on the wire is thirty-two bytes, the little-endian
u-coordinate of RFC 7748. X25519 ignores bit 255 and reduces a value at or above
p, so several byte strings name one key, and every decoder accepts only the
canonical one (message-format.md, Curve public keys). -/

/-- p = 2^255 - 19, the prime of Curve25519's field (RFC 7748, section 4.1). -/
def curveP : Nat := 2 ^ 255 - 19

/-- A byte string read as a little-endian integer, every bit included. X25519
    ignores bit 255 of a key; this does not, so a key with that bit set reads as
    at least 2^255. -/
def leValue : List UInt8 → Nat
  | [] => 0
  | b :: bs => b.toNat + 256 * leValue bs

/-- Whether a curve public key is its canonical encoding: its bytes, read as a
    little-endian integer, are below p. That one comparison refuses both other
    spellings of a key: bit 255 set, which reads as at least 2^255, and a value
    at least p with that bit clear. The decoders apply it to exactly thirty-two
    bytes. -/
def canonicalKey (k : List UInt8) : Bool :=
  decide (leValue k < curveP)

/-- `some ()` when `k` is a canonical curve public key, `none` otherwise. A
    function of its own, bound in the decoders, for the reason `checkCurve`
    is. -/
def checkKey (k : List UInt8) : Option Unit :=
  if canonicalKey k then some () else none

theorem leValue_append (xs ys : List UInt8) :
    leValue (xs ++ ys) = leValue xs + 256 ^ xs.length * leValue ys := by
  induction xs with
  | nil => simp [leValue]
  | cons x xs ih =>
    simp only [List.cons_append, leValue, ih, List.length_cons, Nat.pow_succ, Nat.mul_add]
    rw [Nat.mul_assoc (256 ^ xs.length) 256, Nat.mul_left_comm 256 (256 ^ xs.length),
      Nat.add_assoc]

theorem leValue_lt (l : List UInt8) : leValue l < 256 ^ l.length := by
  induction l with
  | nil => simp [leValue]
  | cons x xs ih =>
    have hx := x.toNat_lt
    simp only [leValue, List.length_cons, Nat.pow_succ]
    omega

/-- The value is the largest the length allows exactly when every byte is
    `0xff`. -/
theorem leValue_eq_max (l : List UInt8) :
    leValue l = 256 ^ l.length - 1 ↔ ∀ x ∈ l, x.toNat = 255 := by
  induction l with
  | nil => simp [leValue]
  | cons x xs ih =>
    have hx := x.toNat_lt
    have hv := leValue_lt xs
    simp only [leValue, List.length_cons, Nat.pow_succ, List.mem_cons, forall_eq_or_imp, ← ih]
    omega

theorem all_range'_ff_iff (k : List UInt8) (h : k.length = 32) :
    (List.range' 1 30).all (fun j => k[j]!.toNat == 255) = true ↔
      ∀ x ∈ (k.drop 1).take 30, x.toNat = 255 := by
  rw [List.all_eq_true]
  constructor
  · intro hall x hx
    rw [List.mem_iff_getElem] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    have hi' : i < 30 := by simp at hi; omega
    have := hall (i + 1) (by simp [List.mem_range'_1]; omega)
    simp only [beq_iff_eq] at this
    simpa [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem (by omega : i + 1 < k.length),
      Nat.add_comm] using this
  · intro hall j hj
    rw [List.mem_range'_1] at hj
    have hmem : k[j]! ∈ (k.drop 1).take 30 := by
      rw [List.mem_iff_getElem]
      refine ⟨j - 1, by simp; omega, ?_⟩
      simp [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem (by omega : j < k.length)]
      congr 1; omega
    simpa using hall _ hmem

theorem split32 (k : List UInt8) (h : k.length = 32) :
    k = [k[0]!] ++ ((k.drop 1).take 30 ++ [k[31]!]) := by
  apply List.ext_getElem
  · simp; omega
  · intro i h1 h2
    simp only [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem (by omega : 0 < k.length),
      List.getElem?_eq_getElem (by omega : 31 < k.length), Option.getD_some]
    rcases Nat.lt_or_ge i 1 with hi | hi
    · have : i = 0 := by omega
      subst this; simp
    · rcases Nat.lt_or_ge i 31 with hj | hj
      · rw [List.getElem_append_right (by simp; omega)]
        rw [List.getElem_append_left (by simp; omega)]
        simp; congr 1; omega
      · have : i = 31 := by omega
        subst this
        rw [List.getElem_append_right (by simp)]
        rw [List.getElem_append_right (by simp; omega)]
        simp

/-- **"Below p" is a test on three places in the key.** With bit 255 clear, a
    thirty-two-byte value is at least p = 2^255 - 19 exactly when its last byte
    is `0x7f`, the thirty bytes between are all `0xff`, and its first byte is at
    least `0xed`. This is the form an implementation checks, and the form the
    refinement proofs meet the code in. -/
theorem canonicalKey_bytes (k : List UInt8) (h : k.length = 32) :
    canonicalKey k = (decide (k[31]!.toNat < 128) &&
      !(decide (k[31]!.toNat = 127) && (List.range' 1 30).all (fun j => k[j]!.toNat == 255)
        && decide (237 ≤ k[0]!.toNat))) := by
  have hmid : ((k.drop 1).take 30).length = 30 := by simp; omega
  have hsplit : leValue k =
      k[0]!.toNat + 256 * (leValue ((k.drop 1).take 30) + 256 ^ 30 * k[31]!.toNat) := by
    have e := congrArg leValue (split32 k h)
    rw [e, List.singleton_append, leValue, leValue_append, hmid]
    simp [leValue]
  have hM := leValue_lt ((k.drop 1).take 30)
  rw [hmid] at hM
  have hmax := leValue_eq_max ((k.drop 1).take 30)
  rw [hmid] at hmax
  have hall : (List.range' 1 30).all (fun j => k[j]!.toNat == 255)
      = decide (leValue ((k.drop 1).take 30) = 256 ^ 30 - 1) := by
    rw [Bool.eq_iff_iff, all_range'_ff_iff k h, decide_eq_true_eq, hmax]
  have h0 := (k[0]!).toNat_lt
  have h31 := (k[31]!).toNat_lt
  rw [hall]
  unfold canonicalKey curveP
  rw [hsplit]
  generalize leValue ((k.drop 1).take 30) = M at *
  generalize (k[0]!).toNat = a at *
  generalize (k[31]!).toNat = b at *
  simp only [Nat.reducePow, Nat.reduceSub] at *
  by_cases hb128 : b < 128 <;> by_cases hb127 : b = 127 <;>
    by_cases hmax' : M = 1766847064778384329583297500742918515827483896875618958121606201292619775 <;>
    by_cases ha : 237 ≤ a <;> simp [hb128, hb127, hmax', ha] <;> omega

/-- The largest canonical key, p - 1, and the two refused spellings at the
    boundary, p and 2^255 - 1. -/
example : canonicalKey (0xec :: List.replicate 30 0xff ++ [0x7f]) = true := by decide
example : canonicalKey (0xed :: List.replicate 30 0xff ++ [0x7f]) = false := by decide
example : canonicalKey (0xff :: List.replicate 30 0xff ++ [0x7f]) = false := by decide
/-- Bit 255 set on an otherwise small key. -/
example : canonicalKey (List.replicate 31 0x11 ++ [0x91]) = false := by decide

/-! A ratchet message -- the composite header, then the AEAD output -- is modelled
in `Model.CompositeHeader` (`encodeMessage`, `decodeMessage`), which imports this
module. The Double Ratchet's forty-byte header on its own is not a message
(message-format.md, Ratchet message), and nothing here models one. -/

/-- Encode an initial (prekey) message: version, type, the initiator's identity
    and ephemeral keys in `EncodeEC` form, the length-prefixed KEM ciphertext,
    the three prekey identifiers, then a complete ratchet message.

    The identifiers name which of the recipient's prekeys were used, so the
    recipient can load the matching private keys. `oneTimeId` is `absentId` when
    the bundle carried no one-time curve prekey, which keeps the message a fixed
    shape rather than making the field optional (message-format.md). -/
def encodeInitial (identity ephemeral : List UInt8) (kemCiphertext : List UInt8)
    (signedPrekeyId oneTimeId kemPrekeyId : UInt32)
    (ratchetMessage : List UInt8) : List UInt8 :=
  version :: typeInitial ::
    (identity ++ ephemeral
      ++ be32 (UInt32.ofNat kemCiphertext.length) ++ kemCiphertext
      ++ be32 signedPrekeyId ++ be32 oneTimeId ++ be32 kemPrekeyId
      ++ ratchetMessage)

/-- A decoded initial message. A structure rather than a tuple, both because it
    mirrors the implementation's `DecodedInitial` and because a seven-tuple has
    no derivable decidable equality, which the build-time checks need. -/
structure Initial where
  identity : List UInt8
  ephemeral : List UInt8
  kemCiphertext : List UInt8
  signedPrekeyId : UInt32
  oneTimeId : UInt32
  kemPrekeyId : UInt32
  ratchetMessage : List UInt8
  deriving Repr, Inhabited, DecidableEq

/-- `some ()` when `k` begins with the `EncodeEC` curve byte, `none` otherwise
    (the empty list included).

    A function of its own, bound in `decodeInitial`, rather than an `if` written
    inline in its `do` block: an inline `if` there becomes a join point, and the
    proofs' rewriting cannot see through one. -/
def checkCurve (k : List UInt8) : Option Unit :=
  if k.head? = some ecCurveByte then some () else none

/-- Decode an initial message, or `none` if the input is not a canonical
    encoding.

    The identity and ephemeral keys are 33 bytes each: a curve type byte and the
    public key. Either one whose first byte is not `ecCurveByte` is not an
    `EncodeEC` form, and the message is refused (message-format.md, Initial
    message). The KEM ciphertext is length-prefixed because its size depends on
    the KEM, so it cannot be read positionally. -/
def decodeInitial (bs : List UInt8) : Option Initial :=
  match bs with
  | v :: t :: rest =>
    if v != version || t != typeInitial then none
    else do
      let (identity, rest) ← take? 33 rest
      let (ephemeral, rest) ← take? 33 rest
      checkCurve identity
      checkCurve ephemeral
      let (ctLen, rest) ← readBe32 rest
      let (kemCiphertext, rest) ← take? ctLen.toNat rest
      let (signedPrekeyId, rest) ← readBe32 rest
      let (oneTimeId, rest) ← readBe32 rest
      let (kemPrekeyId, rest) ← readBe32 rest
      pure { identity, ephemeral, kemCiphertext, signedPrekeyId, oneTimeId,
             kemPrekeyId, ratchetMessage := rest }
  | _ => none

/-- `CONCAT(ad, header)`: the length of the application's associated data, then
    that data, then the serialized header. The length is what makes the pair
    parse uniquely, which the Double Ratchet specification requires when the
    application's part is not self-delimiting. -/
def concatAd (ad : List UInt8) (header : List UInt8) : List UInt8 :=
  be32 (UInt32.ofNat ad.length) ++ ad ++ header

/-- Recover the pair from a `CONCAT` output, demonstrating it parses uniquely. -/
def splitAd (bs : List UInt8) : Option (List UInt8 × List UInt8) := do
  let (len, rest) ← readBe32 bs
  let (ad, header) ← take? len.toNat rest
  pure (ad, header)

-- Build-time checks.

/-- An initial message round-trips, with a one-time prekey named. -/
example :
    decodeInitial (encodeInitial (0x05 :: List.replicate 32 0x0a)
      (0x05 :: List.replicate 32 0x0b) [0xc0, 0xde] 3 4 5 [0xde, 0xad])
      = some { identity := 0x05 :: List.replicate 32 0x0a,
               ephemeral := 0x05 :: List.replicate 32 0x0b,
               kemCiphertext := [0xc0, 0xde], signedPrekeyId := 3,
               oneTimeId := 4, kemPrekeyId := 5,
               ratchetMessage := [0xde, 0xad] } := by
  native_decide

/-- It round-trips with no one-time prekey too. The absent identifier is carried
    as a value rather than by omitting a field, so the shape does not change. -/
example :
    decodeInitial (encodeInitial (0x05 :: List.replicate 32 0x0a)
      (0x05 :: List.replicate 32 0x0b) [] 3 absentId 5 [0xde, 0xad])
      = some { identity := 0x05 :: List.replicate 32 0x0a,
               ephemeral := 0x05 :: List.replicate 32 0x0b,
               kemCiphertext := [], signedPrekeyId := 3,
               oneTimeId := absentId, kemPrekeyId := 5,
               ratchetMessage := [0xde, 0xad] } := by
  native_decide

/-- A ratchet message's type byte is not accepted as an initial message, the
    other half of telling the two apart. -/
example :
    decodeInitial (version :: typeRatchet
      :: (List.replicate 33 0x0a ++ List.replicate 33 0x0b ++ be32 0)) = none := by
  native_decide

/-- A KEM ciphertext length that runs past the end is rejected rather than
    truncated, which is what stops a length prefix being a parsing oracle. -/
example :
    decodeInitial (version :: typeInitial
      :: ((ecCurveByte :: List.replicate 32 0x0a) ++ (ecCurveByte :: List.replicate 32 0x0b)
          ++ be32 99 ++ [0xc0, 0xde])) = none := by
  native_decide

/-- An identity whose first byte is not the curve byte is not an `EncodeEC`
    form, and the message is refused although every length in it is right. -/
example :
    decodeInitial (encodeInitial (0x06 :: List.replicate 32 0x0a)
      (ecCurveByte :: List.replicate 32 0x0b) [0xc0, 0xde] 3 4 5 [0xde, 0xad]) = none := by
  native_decide

/-- The same for the ephemeral. -/
example :
    decodeInitial (encodeInitial (ecCurveByte :: List.replicate 32 0x0a)
      (0x00 :: List.replicate 32 0x0b) [0xc0, 0xde] 3 4 5 [0xde, 0xad]) = none := by
  native_decide

/-- The associated-data pair parses uniquely. -/
example :
    splitAd (concatAd [0x01, 0x02] (List.replicate 40 0xbb))
      = some ([0x01, 0x02], List.replicate 40 0xbb) := by
  native_decide

/-- Moving a byte across the boundary produces a different encoding, which is
    what the length prefix buys: without it both splits would concatenate to the
    same bytes. -/
example :
    concatAd [0x01, 0x02] (List.replicate 40 0xbb)
      ≠ concatAd [0x01] (0x02 :: List.replicate 40 0xbb) := by
  native_decide

/-! ## Prekey bundles

A bundle is public key material and the identifiers a recipient echoes back. It
is not part of any published specification -- the documents describe what a
bundle contains, not how it travels -- so this encoding is ours, and its only
obligation is to be unambiguous. -/

/-- A bundle's fields on the wire. -/
structure Bundle where
  identityKey : List UInt8
  signedPrekey : List UInt8
  signedPrekeySig : List UInt8
  kemPrekey : List UInt8
  kemPrekeySig : List UInt8
  oneTimePrekey : Option (List UInt8)
  signedPrekeyId : UInt32
  oneTimeId : UInt32
  kemPrekeyId : UInt32
  deriving Repr, Inhabited, DecidableEq

/-- The optional one-time prekey's encoding: a presence byte, then thirty-two
    bytes either way.

    **Fixed width, deliberately.** Emitting the key only when present would save
    thirty-two bytes on a bundle of about seventeen hundred, and would make the
    encoding variable-length, which forces both the encoder and the decoder to
    branch. A fixed layout keeps the decoder straight-line, which is what lets
    the round trip below be proved rather than sampled. The zeros are never read:
    the presence byte alone decides. -/
def encodeOptionalKey : Option (List UInt8) → List UInt8
  | none => 0 :: List.replicate 32 0
  | some k => 1 :: k

/-- The optional one-time prekey's presence byte and thirty-two bytes, decoded:
    `some none` for absent, `some (some k)` for present, `none` for neither.

    **Absent means the whole field is zero, not merely the flag.** Accepting any
    thirty-two bytes behind a zero presence byte would give one bundle 2^256
    other spellings (message-format.md, Prekey bundle). The composite header's
    absent codeword follows the same rule.

    **Present means a canonical key.** A present key that is not its canonical
    encoding is refused (message-format.md, Curve public keys). -/
def decodeOptionalKey (presence keyBytes : List UInt8) : Option (Option (List UInt8)) :=
  if presence == [0] then (if keyBytes.all (· == 0) then some none else none)
  else if presence == [1] then (if canonicalKey keyBytes then some (some keyBytes) else none)
  else none

/-- Encode a bundle.

    The KEM prekey is length-prefixed because its size depends on the parameter
    set. The one-time prekey carries a presence byte rather than being inferred
    from what remains, so the two shapes cannot be read as one another. -/
def encodeBundle (b : Bundle) : List UInt8 :=
  version :: typeBundle ::
    (b.identityKey ++ b.signedPrekey ++ b.signedPrekeySig
      ++ be32 (UInt32.ofNat b.kemPrekey.length) ++ b.kemPrekey
      ++ b.kemPrekeySig
      ++ encodeOptionalKey b.oneTimePrekey
      ++ be32 b.signedPrekeyId ++ be32 b.oneTimeId ++ be32 b.kemPrekeyId)

/-- `some ()` when a KEM prekey length read off the wire is `kemPrekeyLen`,
    `none` otherwise. A function of its own for the reason `checkCurve` is. -/
def checkKemLen (n : UInt32) : Option Unit :=
  if n.toNat = kemPrekeyLen then some () else none

/-- Decode a bundle, or `none` if the input is not a canonical encoding.

    A KEM prekey length other than `kemPrekeyLen` is refused as soon as it is
    read, whether or not that many bytes follow (message-format.md, Prekey
    bundle).

    Trailing bytes are rejected: a bundle is a whole object rather than a prefix
    of a stream, so a decoder that ignored what followed would accept two
    different byte strings as the same bundle.

    Every curve key is refused unless it is its canonical encoding
    (message-format.md, Curve public keys): the one-time prekey inside
    `decodeOptionalKey`, and the identity key and signed prekey once the whole
    bundle has been read. Where a refusal is checked does not change what is
    refused. -/
def decodeBundle (bs : List UInt8) : Option Bundle :=
  match bs with
  | v :: t :: rest =>
    if v != version || t != typeBundle then none
    else do
      let (identityKey, rest) ← take? 32 rest
      let (signedPrekey, rest) ← take? 32 rest
      let (signedPrekeySig, rest) ← take? 64 rest
      let (kemLen, rest) ← readBe32 rest
      checkKemLen kemLen
      let (kemPrekey, rest) ← take? kemLen.toNat rest
      let (kemPrekeySig, rest) ← take? 64 rest
      -- Fixed layout: the presence byte and thirty-two bytes are always there,
      -- so this reads them unconditionally and only then decides what they mean.
      let (presence, rest) ← take? 1 rest
      let (keyBytes, rest) ← take? 32 rest
      let oneTimePrekey ← decodeOptionalKey presence keyBytes
      let (signedPrekeyId, rest) ← readBe32 rest
      let (oneTimeId, rest) ← readBe32 rest
      let (kemPrekeyId, rest) ← readBe32 rest
      checkKey identityKey
      checkKey signedPrekey
      if rest.isEmpty then
        pure { identityKey, signedPrekey, signedPrekeySig, kemPrekey,
               kemPrekeySig, oneTimePrekey, signedPrekeyId, oneTimeId,
               kemPrekeyId }
      else none
  | _ => none

private def sampleBundle (oneTime : Option (List UInt8)) : Bundle :=
  { identityKey := List.replicate 32 0x11
    signedPrekey := List.replicate 32 0x22
    signedPrekeySig := List.replicate 64 0x33
    kemPrekey := List.replicate 1568 0x44
    kemPrekeySig := List.replicate 64 0x55
    oneTimePrekey := oneTime
    signedPrekeyId := 7
    oneTimeId := 8
    kemPrekeyId := 9 }

/-- Both shapes round-trip. -/
example : decodeBundle (encodeBundle (sampleBundle (some (List.replicate 32 0x66))))
    = some (sampleBundle (some (List.replicate 32 0x66))) := by native_decide

example : decodeBundle (encodeBundle (sampleBundle none)) = some (sampleBundle none) := by
  native_decide

/-- An absent one-time prekey over non-zero padding is not a bundle: the
    presence byte alone does not make the field absent. -/
example :
    decodeBundle ((encodeBundle (sampleBundle none)).set (1811 - 12 - 32) 0x01) = none := by
  native_decide

/-- A KEM prekey that is not 1,568 bytes is not a bundle, even when its length
    prefix is honest about the bytes that follow: one byte short, and one over. -/
example :
    decodeBundle (encodeBundle { sampleBundle none with kemPrekey := List.replicate 1567 0x44 })
      = none := by
  native_decide

example :
    decodeBundle (encodeBundle { sampleBundle none with kemPrekey := List.replicate 1569 0x44 })
      = none := by
  native_decide

/-- p = 2^255 - 19 as a key, the refused spelling of zero. -/
private def keyP : List UInt8 := 0xed :: List.replicate 30 0xff ++ [0x7f]

/-- p - 1, the largest canonical key. -/
private def keyPMinusOne : List UInt8 := 0xec :: List.replicate 30 0xff ++ [0x7f]

/-- The sample identity key with bit 255 set: the same key, spelled again. -/
private def keyHigh : List UInt8 := List.replicate 31 0x11 ++ [0x91]

/-- A re-spelled key in any of a bundle's three positions is not a bundle
    (message-format.md, Curve public keys). -/
example :
    decodeBundle (encodeBundle { sampleBundle none with identityKey := keyHigh }) = none := by
  native_decide

example :
    decodeBundle (encodeBundle { sampleBundle none with signedPrekey := keyP }) = none := by
  native_decide

example : decodeBundle (encodeBundle (sampleBundle (some keyP))) = none := by
  native_decide

/-- The largest canonical key is accepted in every position. -/
example :
    decodeBundle (encodeBundle { sampleBundle (some keyPMinusOne) with
        identityKey := keyPMinusOne, signedPrekey := keyPMinusOne })
      = some { sampleBundle (some keyPMinusOne) with
        identityKey := keyPMinusOne, signedPrekey := keyPMinusOne } := by
  native_decide

end Model.Messages
