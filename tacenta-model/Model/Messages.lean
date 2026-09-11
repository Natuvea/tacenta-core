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

/-- Decode an initial message, or `none` if the input is not a canonical
    encoding.

    The identity and ephemeral keys are 33 bytes each: a curve type byte and the
    public key. The KEM ciphertext is length-prefixed because its size depends on
    the KEM, so it cannot be read positionally. -/
def decodeInitial (bs : List UInt8) : Option Initial :=
  match bs with
  | v :: t :: rest =>
    if v != version || t != typeInitial then none
    else do
      let (identity, rest) ← take? 33 rest
      let (ephemeral, rest) ← take? 33 rest
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
      :: (List.replicate 33 0x0a ++ List.replicate 33 0x0b ++ be32 99
          ++ [0xc0, 0xde])) = none := by
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
    absent codeword follows the same rule. -/
def decodeOptionalKey (presence keyBytes : List UInt8) : Option (Option (List UInt8)) :=
  if presence == [0] then (if keyBytes.all (· == 0) then some none else none)
  else if presence == [1] then some (some keyBytes)
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

/-- Decode a bundle, or `none` if the input is not a canonical encoding.

    Trailing bytes are rejected: a bundle is a whole object rather than a prefix
    of a stream, so a decoder that ignored what followed would accept two
    different byte strings as the same bundle. -/
def decodeBundle (bs : List UInt8) : Option Bundle :=
  match bs with
  | v :: t :: rest =>
    if v != version || t != typeBundle then none
    else do
      let (identityKey, rest) ← take? 32 rest
      let (signedPrekey, rest) ← take? 32 rest
      let (signedPrekeySig, rest) ← take? 64 rest
      let (kemLen, rest) ← readBe32 rest
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

end Model.Messages
