/-
Properties.ForwardSecrecy: an attacker who takes a party's state cannot read the
messages that came before it.

This is the property the ratchet exists for. It is stated here against the symbolic attacker
in `Model.Adversary`, for the reason set out there: over byte strings the claim
reduces to "the chain step cannot be inverted", which is an assumption about
SHA-256 rather than anything this protocol does.

What is proved is the protocol's own half. Given a key derivation that cannot be
run backwards, the ratchet's structure leaks nothing about its past. Whether the
derivation really cannot be run backwards is the assumption, and it is stated in
`Model.Adversary` rather than hidden here.
-/
import Model.Adversary

namespace Properties.ForwardSecrecy

open Model.Adversary

/-! ## A chain

The sending chain of one session: a seed, and each step the chain key after it.
The message key at step `n` is read off the chain key at step `n`. -/

/-- The chain key after `n` steps of the chain seeded by session `s`.

    Carrying the session index rather than fixing one costs nothing here and is
    what lets `Properties.Authentication` say that two sessions never meet. -/
def ckAt (s : Nat) : Nat → Sym
  | 0 => .seed s
  | n + 1 => .chain (ckAt s n)

/-- The message key at step `n` of session `s`. -/
def mkAt (s n : Nat) : Sym := .msg (ckAt s n)

theorem depth_ckAt (s n : Nat) : depth (ckAt s n) = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [ckAt, depth, ih]

/-- A chain key is a seed or a chain step, never a message key. What keeps the
two apart is that they are built by different constructors, which is the whole
reason the attacker's world is terms. -/
theorem ckAt_ne_msg (s n : Nat) (x : Sym) : ckAt s n ≠ .msg x := by
  cases n <;> simp [ckAt]

/-! ## The theorem

Compromise at step `n` means the attacker takes the chain key the party holds
then, and nothing else. -/

/-- **Forward secrecy.** An attacker who takes the chain key at step `n` cannot
derive the message key of any earlier step.

    The whole content is that no rule runs a chain backwards, so everything
    derivable sits at or above what was taken, and every earlier message key sits
    strictly below it. The proof is that observation and nothing more, which is
    what it should be: if this needed a clever argument, the protocol would be
    doing something delicate rather than something structural. -/
theorem past_message_keys_are_safe (s n m : Nat) (h : m < n) :
    ¬ Knows (· = ckAt s n) (mkAt s m) := by
  intro hk
  obtain ⟨s, hs, hr⟩ := knows_reaches hk
  subst hs
  -- The only ways to reach a message key are to *be* it, or to reach the chain
  -- key under it. The first is impossible by shape; the second by depth.
  rcases reaches_msg_inv hr with heq | hr'
  · exact ckAt_ne_msg s n (ckAt s m) heq
  · have := depth_le_of_reaches hr'
    rw [depth_ckAt, depth_ckAt] at this
    omega

/-- The same for chain keys: the attacker cannot recover an earlier chain key,
so it cannot reconstruct the earlier message keys either, one at a time. -/
theorem past_chain_keys_are_safe (s n m : Nat) (h : m < n) :
    ¬ Knows (· = ckAt s n) (ckAt s m) := by
  intro hk
  obtain ⟨s, hs, hr⟩ := knows_reaches hk
  subst hs
  have := depth_le_of_reaches hr
  rw [depth_ckAt, depth_ckAt] at this
  omega

/-! ## What it does not say

Two limits, both real.

**The future is not secret.** An attacker holding the chain key at step `n` can
derive every message key from `n` onward, and that is a theorem here rather than
an omission: the chain runs forward by design, and recovering from a compromise
is what the Diffie-Hellman ratchet is for, not what this chain is for. -/

/-- Compromise is total going forward. Stated because a reader who saw only the
theorem above might take it for more than it is. -/
theorem future_message_keys_are_exposed (s n k : Nat) :
    Knows (· = ckAt s n) (mkAt s (n + k)) := by
  have step : ∀ j, Knows (· = ckAt s n) (ckAt s (n + j)) := by
    intro j
    induction j with
    | zero => exact .held rfl
    | succ j ih =>
      have : ckAt s (n + (j + 1)) = .chain (ckAt s (n + j)) := by
        simp [ckAt]
      rw [this]
      exact .chain ih
  exact .msg (step k)

/-! **This is one chain, not a session.** A real session interleaves chains, root
steps and Diffie-Hellman outputs, and its state holds more than one key at a
time. The statement above is the chain in isolation, which is where forward
secrecy within an epoch comes from; carrying it to a whole session means relating
these terms to `Model.State`, and that relation is not written yet. -/

end Properties.ForwardSecrecy
