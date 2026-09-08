/-
Properties.Authentication: what the key schedule contributes to knowing who sent
something, and what it does not.

This is the last of the four attacker-facing properties and the one this model
serves least, so the boundary is worth drawing before anything is claimed.

Authentication asks: if a message verifies, who made it? That is a property of
the *authenticated encryption*, and in a symbolic model it is an assumption, not
a derivation -- the same kind of assumption as one-wayness for the key
derivation. Nothing here proves that a ciphertext cannot be forged, and nothing
here could.

What the protocol contributes underneath that assumption is that the key doing
the authenticating is *the right key*: bound to one session and one position in
it, and unavailable to anyone outside. Given unforgeability, that is what turns
"this verifies" into "this came from my peer, in this conversation, at this
point". If keys collided across sessions, unforgeability would still hold and
authentication would still fail, because a message forged for one conversation
would verify in another.

That part is provable, and it is what this file proves.
-/
import Properties.Secrecy

namespace Properties.Authentication

open Model.Adversary
open Properties.ForwardSecrecy (ckAt mkAt depth_ckAt)
open Properties.Secrecy (reaches_ckAt_inv)

/-! ## Distinct sessions, distinct keys

Two sessions seeded differently never derive the same key, at any step. A
collision would let a message made for one conversation verify in another, which
is an authentication failure that no amount of unforgeability prevents. -/

/-- Chain keys determine both their session and their position. -/
theorem ckAt_inj {s t n m : Nat} (h : ckAt s n = ckAt t m) : s = t ∧ n = m := by
  have hd := congrArg depth h
  rw [depth_ckAt, depth_ckAt] at hd
  subst hd
  induction n with
  | zero => exact ⟨by simpa [ckAt] using h, rfl⟩
  | succ n ih =>
    simp only [ckAt, Sym.chain.injEq] at h
    exact ⟨(ih h).1, rfl⟩

/-- And so do message keys. -/
theorem mkAt_inj {s t n m : Nat} (h : mkAt s n = mkAt t m) : s = t ∧ n = m := by
  simp only [mkAt, Sym.msg.injEq] at h
  exact ckAt_inj h

/-! ## Sessions do not leak into one another

Stronger than distinctness, and the statement that matters: an attacker who takes
a whole session learns nothing in another. Compromising one conversation does not
compromise the next. -/

/-- Everything reachable from one session's chain key stays in that session. -/
theorem no_cross_session_chain {s t n m : Nat} (hst : s ≠ t) :
    ¬ Knows (· = ckAt s n) (ckAt t m) := by
  intro hk
  obtain ⟨x, hx, hr⟩ := knows_reaches hk
  subst hx
  obtain ⟨k, -, hbad⟩ := reaches_ckAt_inv hr
  exact hst (ckAt_inj hbad.symm).1.symm

/-- Nor any message key of another session. -/
theorem no_cross_session_message {s t n m : Nat} (hst : s ≠ t) :
    ¬ Knows (· = ckAt s n) (mkAt t m) := by
  intro hk
  obtain ⟨x, hx, hr⟩ := knows_reaches hk
  subst hx
  rcases reaches_msg_inv hr with heq | hr'
  · exact absurd heq (by cases n <;> simp [ckAt])
  · obtain ⟨k, -, hbad⟩ := reaches_ckAt_inv hr'
    exact hst (ckAt_inj hbad.symm).1.symm

/-! ## What is assumed, and it is the larger half

**Unforgeability of the authenticated encryption.** That a ciphertext verifying
under a key was made by someone holding that key is assumed, not proved, and
cannot be proved in a symbolic model: it is the model's premise. Everything above
is the protocol's contribution *given* that premise.

**The identity binding.** The associated data binds both identities, so a
ciphertext accepted in one session was made for that session and not moved into
it. That the binding is unambiguous is proved -- in
`Proofs.SessionEstablishment`, where the encoding lives, and where the width
requirement that makes it work is stated. It is not restated here, but it is part
of the same argument and neither half is sufficient alone.

**Who the identity belongs to.** Nothing here or anywhere in this project proves
that an identity key belongs to the person a user means. That is trust on first
use and the directory's problem, and it is the assumption a user actually bears.
-/

end Properties.Authentication
