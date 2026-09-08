/-
Properties.Secrecy: one key leaking does not leak another.

Forward secrecy and post-compromise security are both about compromise of a
*chain* key: what a party holds, and what an attacker gets by taking it. This is
the other question, and it is the one that decides how bad a smaller accident is.
A message key can escape without the chain escaping -- it is handed to the
encryption layer, it may be logged, it may sit in a buffer the ratchet no longer
controls -- and the question is whether losing one costs anything beyond the one
message it opened.

It costs nothing. A message key is a dead end: nothing in the key schedule takes
one as input, so an attacker holding it can build terms *on* it but can never
reach the chain it came from or any sibling.

Same symbolic attacker, same assumption, as set out in `Model.Adversary`.
-/
import Properties.ForwardSecrecy

namespace Properties.Secrecy

open Model.Adversary
open Properties.ForwardSecrecy (ckAt mkAt depth_ckAt)

/-! ## Chain keys are only reachable from earlier chain keys

The structural fact this rests on. A chain key is built of `chain` applied to a
seed and nothing else, so anything reaching one is itself a chain key from
earlier in the same chain. In particular a *message* key is not, whatever its
depth -- which is why the depth argument that settles forward secrecy is not
enough here. -/

theorem reaches_ckAt_inv {a : Sym} {s m : Nat} (h : Reaches a (ckAt s m)) :
    ∃ k, k ≤ m ∧ a = ckAt s k := by
  induction m with
  | zero => exact ⟨0, Nat.le_refl _, reaches_seed_inv h⟩
  | succ m ih =>
    rcases reaches_chain_inv h with rfl | h'
    · exact ⟨m + 1, Nat.le_refl _, rfl⟩
    · obtain ⟨k, hk, rfl⟩ := ih h'
      exact ⟨k, Nat.le_succ_of_le hk, rfl⟩

/-! ## The theorem -/

/-- **A leaked message key leaks nothing else.** An attacker holding the message
key of one step derives no other message key, at any step, in either direction.

    The reason is that no rule takes a message key as input. It is the end of the
    line: everything the attacker can build sits *above* it, and no other message
    key does. -/
theorem message_keys_are_independent (s n m : Nat) (h : n ≠ m) :
    ¬ Knows (· = mkAt s n) (mkAt s m) := by
  intro hk
  obtain ⟨s, hs, hr⟩ := knows_reaches hk
  subst hs
  rcases reaches_msg_inv hr with heq | hr'
  · -- Being the same message key would make the two steps the same step.
    simp only [mkAt, Sym.msg.injEq] at heq
    have hd := congrArg depth heq
    rw [depth_ckAt, depth_ckAt] at hd
    exact h hd
  · -- Or reaching the chain the other key came from, which a message key never
    -- does: everything reaching a chain key is itself a chain key.
    obtain ⟨k, -, hbad⟩ := reaches_ckAt_inv hr'
    exact absurd hbad (by cases k <;> simp [mkAt, ckAt])

/-- And it does not reach the chain it came from, so it cannot be run forward
into the message keys that followed it either. -/
theorem a_message_key_does_not_expose_its_chain (s n m : Nat) :
    ¬ Knows (· = mkAt s n) (ckAt s m) := by
  intro hk
  obtain ⟨s, hs, hr⟩ := knows_reaches hk
  subst hs
  obtain ⟨k, -, hbad⟩ := reaches_ckAt_inv hr
  exact absurd hbad (by cases k <;> simp [mkAt, ckAt])

/-! ## What it does not say

**This is about the key schedule, not about the ciphertext.** A message key opens
its own message, and that is what it is for. The claim is only that it opens
nothing else.

**It says nothing about how a message key escapes.** Whether one can escape at
all is a property of the code that handles it after the ratchet returns it, which
is where the erasure work sits, and no proof here reaches that far.

**One chain, as before.** Relating these terms to `Model.State` is still not
written. -/

end Properties.Secrecy
