/-
Proofs.SessionEstablishment: what the PQXDH derivation guarantees about its own
inputs (proof tier T2).

The key derivation is a hash, so nothing here can say that different inputs give
different secrets; that is a property of SHA-256 and not something a proof about
this model can reach. What a proof *can* settle is the question underneath it,
and it is the one that has broken real protocols: whether two different tuples of
agreement outputs can reach the derivation as the same bytes. If they can, the
hash's strength is irrelevant, because the confusion happened before it.

They cannot, and the reason is worth stating: every component is a fixed
thirty-two bytes, and the presence of the one-time output changes the total
length, so the bytes determine both which components were supplied and what each
one was.

The associated data is the same question with a different answer, and that is the
part of this file worth reading twice.
-/
import Model.SessionEstablishment

namespace Proofs.SessionEstablishment

open Model.State (Key)
open Model.SessionEstablishment

/-! ## The input keying material is unambiguous

Stated as: equal `km` bytes force equal components. Each step is `List.append_inj`
at a known length, which is exactly the reasoning the fixed widths exist to
support. -/

/-- With the one-time output absent on both sides. -/
theorem km_inj_none {dh1 dh2 dh3 ss dh1' dh2' dh3' ss' : Key}
    (h1 : dh1.length = 32) (h2 : dh2.length = 32) (h3 : dh3.length = 32)
    (h1' : dh1'.length = 32) (h2' : dh2'.length = 32) (h3' : dh3'.length = 32)
    (h : km dh1 dh2 dh3 none ss = km dh1' dh2' dh3' none ss') :
    dh1 = dh1' ∧ dh2 = dh2' ∧ dh3 = dh3' ∧ ss = ss' := by
  -- `++` groups to the left, so the splits peel from the right: the last
  -- component comes off first and the first comes off last.
  simp only [km] at h
  obtain ⟨ha, hss⟩ := List.append_inj h (by simp [h1, h2, h3, h1', h2', h3'])
  obtain ⟨hb, e3⟩ := List.append_inj ha (by simp [h1, h2, h1', h2'])
  obtain ⟨e1, e2⟩ := List.append_inj hb (by omega)
  exact ⟨e1, e2, e3, hss⟩

/-- With the one-time output present on both sides. -/
theorem km_inj_some {dh1 dh2 dh3 d4 ss dh1' dh2' dh3' d4' ss' : Key}
    (h1 : dh1.length = 32) (h2 : dh2.length = 32) (h3 : dh3.length = 32)
    (h4 : d4.length = 32)
    (h1' : dh1'.length = 32) (h2' : dh2'.length = 32) (h3' : dh3'.length = 32)
    (h4' : d4'.length = 32)
    (h : km dh1 dh2 dh3 (some d4) ss = km dh1' dh2' dh3' (some d4') ss') :
    dh1 = dh1' ∧ dh2 = dh2' ∧ dh3 = dh3' ∧ d4 = d4' ∧ ss = ss' := by
  simp only [km] at h
  obtain ⟨ha, hss⟩ :=
    List.append_inj h (by simp [h1, h2, h3, h4, h1', h2', h3', h4'])
  obtain ⟨hb, e4⟩ := List.append_inj ha (by simp [h1, h2, h3, h1', h2', h3'])
  obtain ⟨hc, e3⟩ := List.append_inj hb (by simp [h1, h2, h1', h2'])
  obtain ⟨e1, e2⟩ := List.append_inj hc (by omega)
  exact ⟨e1, e2, e3, e4, hss⟩

/-- The two cases cannot be confused for one another.

This is the one that would not hold if the components were variable-length, and
it is what stops a session established with a one-time prekey from presenting the
same keying material as one established without. The lengths differ by exactly
one component, so no choice of `ss` on either side can close the gap. -/
theorem km_none_ne_some {dh1 dh2 dh3 ss dh1' dh2' dh3' d4' ss' : Key}
    (h1 : dh1.length = 32) (h2 : dh2.length = 32) (h3 : dh3.length = 32)
    (hs : ss.length = 32)
    (h1' : dh1'.length = 32) (h2' : dh2'.length = 32) (h3' : dh3'.length = 32)
    (h4' : d4'.length = 32) (hs' : ss'.length = 32) :
    km dh1 dh2 dh3 none ss ≠ km dh1' dh2' dh3' (some d4') ss' := by
  intro h
  have hlen := congrArg List.length h
  simp only [km, List.length_append, h1, h2, h3, hs, h1', h2', h3', h4', hs'] at hlen
  omega

/-- Put together: the keying material determines the tuple that produced it, over
all five components and both shapes. -/
theorem km_determines
    {dh1 dh2 dh3 ss dh1' dh2' dh3' ss' : Key} {dh4 dh4' : Option Key}
    (h1 : dh1.length = 32) (h2 : dh2.length = 32) (h3 : dh3.length = 32)
    (hs : ss.length = 32) (h4 : ∀ d ∈ dh4, d.length = 32)
    (h1' : dh1'.length = 32) (h2' : dh2'.length = 32) (h3' : dh3'.length = 32)
    (hs' : ss'.length = 32) (h4' : ∀ d ∈ dh4', d.length = 32)
    (h : km dh1 dh2 dh3 dh4 ss = km dh1' dh2' dh3' dh4' ss') :
    dh1 = dh1' ∧ dh2 = dh2' ∧ dh3 = dh3' ∧ dh4 = dh4' ∧ ss = ss' := by
  cases dh4 with
  | none =>
    cases dh4' with
    | none =>
      obtain ⟨e1, e2, e3, e4⟩ := km_inj_none h1 h2 h3 h1' h2' h3' h
      exact ⟨e1, e2, e3, rfl, e4⟩
    | some d4' =>
      exact absurd h (km_none_ne_some h1 h2 h3 hs h1' h2' h3'
        (h4' d4' (by simp)) hs')
  | some d4 =>
    cases dh4' with
    | none =>
      exact absurd h.symm (km_none_ne_some h1' h2' h3' hs' h1 h2 h3
        (h4 d4 (by simp)) hs)
    | some d4' =>
      obtain ⟨e1, e2, e3, e4, e5⟩ :=
        km_inj_some h1 h2 h3 (h4 d4 (by simp)) h1' h2' h3'
          (h4' d4' (by simp)) h
      exact ⟨e1, e2, e3, by rw [e4], e5⟩

/-! ## The associated data is *not* unambiguous on its own

The same question asked of `associatedData` gets the opposite answer, and it is
worth being exact about why. The identity keys are concatenated with nothing
between them and no length before them, so the split is recoverable only from
knowing how long the first one is. The model takes the encoded forms as given and
says nothing about their length, so at this level the function is genuinely
ambiguous.

That is not a flaw being reported; the encodings are fixed-width in practice. It
is a *requirement being located*. The safety of this function lives entirely in
the encoder, so the encoder is where it has to be stated, and
`session-establishment.md` says so. -/

/-- Two different pairs of identity keys, one associated data. Concrete, because
a counterexample is the only honest way to state that something does not hold. -/
example :
    associatedData [0x01] [0x02, 0x03] = associatedData [0x01, 0x02] [0x03] := by
  native_decide

/-- Given the first encoding has a known length, the pair is recoverable. This is
the property the protocol actually relies on, with its hypothesis made visible
rather than assumed. -/
theorem associatedData_inj_of_length {a b a' b' : List UInt8}
    (hl : a.length = a'.length)
    (h : associatedData a b = associatedData a' b') :
    a = a' ∧ b = b' :=
  List.append_inj h hl

/-- The same for the form that binds the KEM prekey, which needs both of the
first two lengths, not just one. -/
theorem associatedDataWithKem_inj_of_length {a b c a' b' c' : List UInt8}
    (hl : a.length = a'.length) (hl2 : b.length = b'.length)
    (h : associatedDataWithKem a b c = associatedDataWithKem a' b' c') :
    a = a' ∧ b = b' ∧ c = c' := by
  simp only [associatedDataWithKem] at h
  obtain ⟨ha, e3⟩ := List.append_inj h (by simp [hl, hl2])
  obtain ⟨e1, e2⟩ := List.append_inj ha hl
  exact ⟨e1, e2, e3⟩

/-! ## Domain separation

The thirty-two `0xFF` bytes are not decoration. The same identity key is used by
XEdDSA, and the prefix is what keeps this derivation's input from ever being a
valid encoding of a scalar or a point, so no input here can be made to collide
with one there. What is provable at this level is that the prefix is present,
whole, and ahead of everything else. -/

/-- Every derivation input opens with thirty-two `0xFF` bytes, whatever the
keying material is. -/
theorem kdf_input_opens_with_ff (kmBytes : List UInt8) :
    ∀ b ∈ (fPrefix ++ kmBytes).take 32, b = 0xFF := by
  intro b hb
  rw [List.take_left' (by simp [fPrefix])] at hb
  simpa [fPrefix] using List.eq_of_mem_replicate hb

/-- The prefix is thirty-two bytes of `0xFF`, none of them anything else. -/
theorem fPrefix_all_ff : ∀ b ∈ fPrefix, b = 0xFF := by
  intro b hb
  simpa [fPrefix] using List.eq_of_mem_replicate hb

theorem fPrefix_length : fPrefix.length = 32 := by simp [fPrefix]

/-! ## The derived secret is the right size, for every input

The two sampled checks in the model cover two tuples. This covers all of them,
which matters because a caller copies a fixed thirty-two bytes out of it. -/

theorem sharedSecret_length (dh1 dh2 dh3 : Key) (dh4 : Option Key) (ss : Key) :
    (sharedSecret dh1 dh2 dh3 dh4 ss).length = 32 := by
  simp only [sharedSecret, kdf]
  exact Model.Kdf.hkdf_length _ _ _ _

end Proofs.SessionEstablishment
