/-
Properties.PostCompromise: a session heals from compromise, once a Diffie-Hellman
step brings in an agreement the attacker did not take.

The counterpart to forward secrecy, and the reason there are two ratchets. The
symmetric chain protects the past and cannot protect the future: an attacker with
a chain key runs it forward for ever, which
`Properties.ForwardSecrecy.future_message_keys_are_exposed` states as a theorem
rather than leaving as an omission. Healing is the other ratchet's job, and this
is what it does.

Same symbolic attacker as forward secrecy, and the same assumption behind it,
set out in `Model.Adversary`.
-/
import Model.Adversary

namespace Properties.PostCompromise

open Model.Adversary

/-! ## The step that heals

A Diffie-Hellman step folds an agreement output into the root key and derives a
fresh chain from the pair. The rule needs *both*: the old root key and the new
output. An attacker holding the first and not the second is stuck, and that is
the whole mechanism. -/

/-- **Post-compromise security.** An attacker who took the root key cannot derive
the chain key of the next epoch, provided the agreement output of that step is
one it did not take.

    The proof is the arity of the rule. Deriving the new chain key needs the
    agreement output as well as the root key, an agreement output is a leaf, and
    a leaf is reachable only by having been taken. Nothing subtler is happening,
    which is as it should be: the security comes from the protocol requiring two
    things and the attacker having one. -/
theorem fresh_agreement_heals (rk : Sym) (i : Nat) (hne : rk ≠ .dhOut i) :
    ¬ Knows (· = rk) (.chainOf rk (.dhOut i)) := by
  intro hk
  rcases knows_chainOf_inv hk with hheld | ⟨-, hdh⟩
  · -- It would have had to take the derived key itself, which is a strictly
    -- bigger term than the root key it took.
    have := congrArg depth hheld
    simp only [depth] at this
    omega
  · -- Or know the agreement output, which is a leaf it did not take.
    obtain ⟨s, hs, hr⟩ := knows_reaches hdh
    subst hs
    exact hne (reaches_dhOut_inv hr)

/-- The new root key is out of reach for the same reason, so the epoch after
that one is too. Healing is not a single step's property; it persists. -/
theorem fresh_agreement_heals_the_root (rk : Sym) (i : Nat) (hne : rk ≠ .dhOut i) :
    ¬ Knows (· = rk) (.rootNext rk (.dhOut i)) := by
  intro hk
  rcases knows_rootNext_inv hk with hheld | ⟨-, hdh⟩
  · have := congrArg depth hheld
    simp only [depth] at this
    omega
  · obtain ⟨s, hs, hr⟩ := knows_reaches hdh
    subst hs
    exact hne (reaches_dhOut_inv hr)

/-! ## What it does not say

**Healing needs an agreement the attacker did not take.** Stated as a hypothesis
because it is the condition, not a detail: an attacker who took the ratchet
private key computes the agreement output itself and nothing heals. That is what
makes a compromise of long-lived key material worse than a compromise of a chain,
and no ratchet repairs it.

**It says nothing about when.** A step heals; how many messages pass before one
happens depends on the conversation, and a party that only sends never takes one.
The specification is explicit that recovery waits on the peer replying, and this
model has no notion of time or turn-taking to say more.

**One step, not a session.** As with forward secrecy, these are statements about
terms rather than about `Model.State`, and the relation between them is not
written. -/

end Properties.PostCompromise
