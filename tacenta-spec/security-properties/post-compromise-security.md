# Post-compromise security

A session that has been compromised recovers, once a Diffie-Hellman step brings
in an agreement the attacker did not take. This page says what that means, what
it needs, and what it does not give.

## Why there are two ratchets

The symmetric-key ratchet protects the past and cannot protect the future. Its
chain runs one way: an attacker holding a chain key derives every message key
after it, for as long as the chain lasts. That is not a weakness to be fixed but
the shape of the thing, and it is proved rather than assumed
(`Properties.ForwardSecrecy.future_message_keys_are_exposed`).

Recovery is the Diffie-Hellman ratchet's job. Each step folds a fresh agreement
into the root key and derives new chains from the pair, so an attacker holding
the old root key and not the new agreement cannot follow.

## What the guarantee is

**An attacker who took a party's root key cannot derive the keys of the next
epoch, provided it did not also take that epoch's agreement output.**

Proved in `Properties.PostCompromise`, against the symbolic attacker described
in `Model.Adversary`. The argument is the arity of the rule: deriving the new
chain needs the agreement output as well as the root key, an agreement output is
a leaf, and a leaf is available only to an attacker that took it. Nothing
subtler happens, which is as it should be. The security is that the protocol
requires two things and the attacker has one.

The new root key is equally out of reach, so the epoch after that is too. Healing
is not one step's property; it persists.

## What it needs

**An agreement the attacker did not take.** This is the condition, not a detail.
An attacker holding a ratchet private key computes the agreement output for
itself, and nothing heals: it follows every step. That is what makes compromise
of long-lived key material worse in kind than compromise of a chain, and no
ratchet repairs it.

**A step to happen at all.** A step comes from receiving a message under a
ratchet key not yet seen, so a party that only sends never takes one. How many
messages pass before recovery is a property of the conversation rather than of
the protocol, and this page does not promise a bound.

## What is not proved

**The fidelity assumption.** The attacker is symbolic: it derives keys only by
the rules given, and the rules mirror the key schedule with none that runs a
derivation backwards. Against the real protocol that holds only if the key
derivation is one-way and collision-resistant, which is not proved here or
anywhere in this project. What is proved is the protocol's own half -- given such
a derivation, the structure leaks nothing -- which is exactly the part a protocol
can get wrong by itself.

**A session, as opposed to a step.** The statements are about the attacker's
terms, not about `Model.State`. Relating the two is not written, so "this session
has healed" is not yet a sentence this project can prove about a running session.

**Anything about the post-quantum ratchet.** Recovery there is slower by design,
because the agreement it heals from is sparse. That ratchet is specified on its
own page, and none of the above covers it.

## Sources

- Signal's published Double Ratchet specification, **revision 4, 2025-11-04**,
  for the Diffie-Hellman ratchet and its recovery properties, and for the
  observation that a compromised chain runs forward unaided. Archived and pinned
  in the conformance manifest.
- The forward-secrecy page, which is the same mechanism read in the other
  direction.
