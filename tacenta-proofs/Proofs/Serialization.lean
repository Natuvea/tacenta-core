/-
Proofs.Serialization: the wire encoding round-trips (proof tier T2).

The headline theorem is that decoding an encoded message returns exactly what was
encoded. That is the property a format most needs and a test can only sample: a
round-trip test checks the messages it happens to try, while this covers every
composite header and every ciphertext.

The bit-level step (reading four big-endian bytes inverts writing them) is
discharged by `bv_decide`, which settles it for all 2^32 values rather than the
handful a test would reach.
-/
import Model.Messages
import Model.CompositeHeader
import Std.Tactic.BVDecide

namespace Proofs.Serialization

open Model.Messages
open Model.CompositeHeader (readBe64_be64 readBe16_be16 decode_encode_agreementType
  encode decode encodeChunk chunkBytes Composite AgreementType Codeword)
open Model.State (Key)

/-- Reading four big-endian bytes inverts writing them, for every 32-bit value. -/
theorem readBe32_be32 (n : UInt32) (rest : List UInt8) :
    readBe32 (be32 n ++ rest) = some (n, rest) := by
  simp only [be32, readBe32, List.cons_append, List.nil_append, Option.some.injEq,
    Prod.mk.injEq, and_true]
  bv_decide

/-- Taking exactly as many bytes as the prefix has returns that prefix and the
    rest, which is what makes every length-prefixed field unambiguous. -/
theorem take?_append (n : Nat) (xs ys : List UInt8) (h : xs.length = n) :
    take? n (xs ++ ys) = some (xs, ys) := by
  unfold take?
  have hlen : ¬ ((xs ++ ys).length < n) := by
    simp [List.length_append, h]
  rw [if_neg hlen, List.take_left' h, List.drop_left' h]

/-! ## Bundles round-trip too

The same property as the two above, and the encoding is shaped to make it
provable. The optional one-time prekey is fixed-width: a variable-length field,
present only when there is one, would force a branch on both sides and put the
encoder's own match under the decoder's, where nothing rewrites.

The fixed width costs thirty-two bytes on a bundle of about seventeen hundred
and makes the decoder straight-line, so both sides share one shape and this
proof is the same shape as the message one. Writing the definition in the form
the proof can use is cheaper than proving the form that was already there. -/

/-- Taking one byte from a cons gives that byte and the rest, whatever the rest
is. The presence byte arrives as a cons where the fixed-width fields arrive as
appends, so `take?_append` does not match it and this does. -/
theorem take?_one_cons (x : UInt8) (xs : List UInt8) :
    take? 1 (x :: xs) = some ([x], xs) := by
  simp [take?]

/-- The last field has nothing after it, so the append form does not match it. -/
theorem readBe32_be32_nil (n : UInt32) : readBe32 (be32 n) = some (n, []) := by
  have := readBe32_be32 n []
  simpa using this

/-- Decoding an encoded bundle returns exactly the bundle encoded.

The hypotheses are the format's own requirements rather than conveniences: a key
that is not thirty-two bytes is not a key this encoding carries, a curve key
that is not its canonical encoding is one the decoder refuses
(message-format.md, Curve public keys), and a KEM prekey that is not
`kemPrekeyLen` bytes, the ML-KEM-1024 encapsulation-key length, is one the
decoder refuses too (message-format.md, Prekey bundle). Stating the theorem
without them would make it false, not more general. -/
theorem decodeBundle_encodeBundle (b : Bundle)
    (hid : b.identityKey.length = 32)
    (hsp : b.signedPrekey.length = 32)
    (hss : b.signedPrekeySig.length = 64)
    (hks : b.kemPrekeySig.length = 64)
    (hot : ∀ k ∈ b.oneTimePrekey, k.length = 32)
    (hkem : b.kemPrekey.length = kemPrekeyLen)
    (hidc : canonicalKey b.identityKey = true)
    (hspc : canonicalKey b.signedPrekey = true)
    (hotc : ∀ k ∈ b.oneTimePrekey, canonicalKey k = true) :
    decodeBundle (encodeBundle b) = some b := by
  simp only [encodeBundle, decodeBundle, bne_self_eq_false, Bool.or_self,
    Bool.false_eq_true, if_false, List.append_assoc]
  rw [take?_append 32 b.identityKey _ hid]
  simp only [Option.bind_eq_bind, Option.bind]
  rw [take?_append 32 b.signedPrekey _ hsp]
  simp only
  rw [take?_append 64 b.signedPrekeySig _ hss]
  simp only
  rw [readBe32_be32]
  simp only
  -- The length fits a `u32`, so it comes back unchanged, and it is the one
  -- length the decoder accepts.
  have hround : (UInt32.ofNat b.kemPrekey.length).toNat = b.kemPrekey.length := by
    rw [hkem]; rfl
  have hcheck : checkKemLen (UInt32.ofNat b.kemPrekey.length) = some () := by
    unfold checkKemLen
    rw [hround, if_pos hkem]
  rw [hcheck]
  simp only
  rw [hround, take?_append b.kemPrekey.length b.kemPrekey _ rfl]
  simp only
  rw [take?_append 64 b.kemPrekeySig _ hks]
  simp only
  -- The layout is fixed-width, so both shapes read the same two fields and only
  -- the presence byte's value decides what they mean.
  cases hone : b.oneTimePrekey with
  | none =>
    simp only [encodeOptionalKey, List.cons_append]
    rw [take?_one_cons]
    simp only
    rw [take?_append 32 (List.replicate 32 0) _ (by simp)]
    -- The presence byte is checked before the identifiers are read, so reduce
    -- that decision before stepping past them.
    simp only [decodeOptionalKey, beq_self_eq_true, if_true, readBe32_be32, readBe32_be32_nil]
    simp [← hone, checkKey, hidc, hspc]
  | some k =>
    have hk : k.length = 32 := hot k (by simp [hone])
    have hkc : canonicalKey k = true := hotc k (by simp [hone])
    simp only [encodeOptionalKey, List.cons_append]
    rw [take?_one_cons]
    simp only
    rw [take?_append 32 k _ hk]
    simp only [decodeOptionalKey, beq_self_eq_true, if_true, readBe32_be32, readBe32_be32_nil, hkc]
    simp [← hone, checkKey, hidc, hspc]

/-! ## The composite header round-trips

The Triple Ratchet's header carries both ratchets' headers, and the composition's
specification states exactly one obligation about it: it must parse
unambiguously. This is that obligation discharged.

The proof is short for the same reason the bundle's is. Every field has a width
known before it is read, including the agreement's optional codeword, which is a
presence byte followed by the full width regardless. So the decoder is
straight-line and the rewrites land in order, rather than the encoder's match
sitting under the decoder's.

That is the fourth encoding in this repository where fixed width is chosen
for the proof's sake and pays for itself immediately. -/

/-- Encoding a composite header and decoding it returns the header and whatever
followed it, for every header whose curve key is thirty-two bytes and its
canonical encoding, and whose codeword, if it has one, is a full chunk. A
ratchet key in any other spelling is one the decoder refuses
(message-format.md, Curve public keys). -/
theorem decode_encode_composite (h : Composite)
    (rest : List UInt8)
    (hdh : h.dh.length = 32)
    (hdhc : canonicalKey h.dh = true)
    (hchunk : ∀ c, h.agChunk = some c → c.data.length = chunkBytes) :
    decode (encode h ++ rest) = some (h, rest) := by
  obtain ⟨dh, pn, n, pqE, pqN, agE, agT, agC⟩ := h
  simp only [encode, decode, List.cons_append, List.append_assoc, List.nil_append,
    bne_self_eq_false, Bool.false_eq_true, if_false]
  rw [take?_append 32 dh _ hdh]
  have hck : checkKey dh = some () := by
    simp only [checkKey]
    rw [if_pos hdhc]
  simp only [Option.bind_eq_bind, Option.bind]
  rw [hck]
  simp only
  rw [readBe32_be32]
  simp only
  rw [readBe32_be32]
  simp only
  rw [readBe64_be64]
  simp only
  rw [readBe64_be64]
  simp only
  rw [readBe64_be64]
  simp only
  cases agC with
  | none =>
    simp only [encodeChunk, List.cons_append, List.append_assoc]
    rw [readBe16_be16]
    simp only
    rw [take?_append chunkBytes (List.replicate chunkBytes 0) _ (by simp)]
    simp [decode_encode_agreementType]
  | some c =>
    have hc : c.data.length = chunkBytes := hchunk c rfl
    simp only [encodeChunk, List.cons_append, List.append_assoc]
    rw [readBe16_be16]
    simp only
    rw [take?_append chunkBytes c.data _ hc]
    simp [decode_encode_agreementType]


/-- **Round trip.** Decoding an encoded ratchet message -- the composite header,
    then the ciphertext -- returns exactly that header and that ciphertext, for
    every header whose curve key is thirty-two bytes and its canonical
    encoding, and whose codeword, if it has one, is a full chunk, and for every
    ciphertext. The message is the header with the ciphertext as the bytes that
    follow it, so this is `decode_encode_composite` read at the message's own
    type. -/
theorem decode_encode (h : Composite) (ct : List UInt8)
    (hdh : h.dh.length = 32)
    (hdhc : canonicalKey h.dh = true)
    (hchunk : ∀ c, h.agChunk = some c → c.data.length = chunkBytes) :
    Model.CompositeHeader.decodeMessage (Model.CompositeHeader.encodeMessage h ct)
      = some (h, ct) :=
  decode_encode_composite h ct hdh hdhc hchunk

end Proofs.Serialization
