# Post-compromise security

A session that has been compromised recovers once a Diffie-Hellman step brings
in an agreement the attacker did not take. This page says what that means, what
it needs and what it does not give, and states it as numbered requirements.

## How the requirements are stated

Each requirement has a statement and five entries:

- **Protects:** the assets (threat-model/assets.md).
- **Holds against:** the adversaries (threat-model/adversaries.md).
- **Rests on:** the assumptions (threat-model/assumptions.md).
- **Status:** one of three.
  - *Proved* names the theorem, its tier and the section of
    `tacenta-proofs/CLAIMS.md` that records it.
  - *Assumed* names the assumptions that carry it, and anything proved
    beneath it.
  - *Tested only* names the tests or vectors.
- **Does not cover:** what a reader might take it to cover.

A proved requirement is proved about the model, or about the translated leaf
crates of `tacenta-core`. It is not proved about that implementation's session
layer (ASM-19; limitations.md, LIM-05).

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

### REQ-PCS-01: a fresh agreement heals the classical ratchet

**An attacker who took a party's root key cannot derive the next epoch's chain
key or its next root key, provided it did not also take that epoch's agreement
output.**

Proved in `Properties.PostCompromise`, against the symbolic attacker described
in `Model.Adversary`. The argument is the arity of the rule: deriving the new
chain needs the agreement output as well as the root key, an agreement output is
a leaf, and a leaf is available only to an attacker that took it. Nothing
subtler happens, which is as it should be. The security is that the protocol
requires two things and the attacker has one.

The new root key is out of reach for the same reason, which is a second theorem
about the same step. Both are about one step. Whether healing carries to the
step after it -- to the root key that root step derives, or to the sending chain
`dhRatchet` derives second, from the intermediate root key and the other
agreement output -- is not proved.

- **Protects:** AS-01, AS-05, AS-08.
- **Holds against:** ADV-02 taking a root key, then ADV-01, provided it does
  not take the next agreement output.
- **Rests on:** ASM-01, ASM-02, ASM-05, ASM-10, ASM-13, ASM-17.
- **Status: proved, model-level, against the symbolic attacker.**
  `Properties.PostCompromise.fresh_agreement_heals` and
  `Properties.PostCompromise.fresh_agreement_heals_the_root` (T2, CLAIMS.md,
  "Proved (tier T2, model-level security properties against the symbolic
  attacker)").
- **Does not cover:** what "What it needs" and "What is not proved", below,
  set out.

### REQ-PCS-02: a step uses a fresh key pair, paired as specified

A Diffie-Hellman ratchet step seeds the new receiving chain from the party's
current ratchet private key and the header's new key. It then generates a
fresh key pair, and seeds the new sending chain from the fresh private key and
the header's key (ratchet.md, The Diffie-Hellman ratchet). Without a fresh key
pair, the step brings in no agreement output that REQ-PCS-01's attacker did not
take.

- **Protects:** AS-05.
- **Holds against:** ADV-02 holding the ratchet private key the step replaces.
- **Rests on:** ASM-01, ASM-02, ASM-19.
- **Status: tested only.** `a_session_dh_step_pairs_the_old_key_with_the_peers_new_key`
  (`tacenta-core/tests/handshake_to_ratchet.rs`) drives a real session through
  a step. Which key pair produces which output is decided outside every proof
  and every vector: the leaf theorems take both agreement outputs and the
  fresh public key as bytes (`dh_ratchet_refines`, `receive_refines`;
  CLAIMS.md, "Read this first: what is not proved").
- **Does not cover:** whether the fresh key pair is unpredictable (ASM-01).

### REQ-PCS-03: a completed epoch heals the post-quantum ratchet

After a party's state is compromised, suppose the Braid completes an epoch to
which that party contributed a key pair or an encapsulation made after the
compromise, and whose messages the attacker did not replace. Then the sparse
ratchet's root key and chains from that epoch on are out of the attacker's
reach. Because the agreement is ML-KEM-1024, this holds against an attacker
that also breaks X25519 (ADV-03).

- **Protects:** AS-01, AS-06, AS-08.
- **Holds against:** ADV-02, then ADV-01 or ADV-03, provided it stays passive
  while the epoch completes.
- **Rests on:** ASM-01, ASM-04, ASM-05, ASM-13.
- **Status: assumed (ASM-04, ASM-05).** No symbolic theorem covers the sparse
  ratchet or the Braid (limitations.md, LIM-04). Proved beneath it:
  - the code folds an agreement output into the sparse ratchet's root key as
    the model does: `advance_refines` (T3, CLAIMS.md, "Proved (tier T3, the
    sparse post-quantum ratchet's translated code refines the model)");
  - the Braid's code takes the model's transitions: `Braid.send_refines` and
    `Braid.receive_refines` (T3, "Proved (tier T3, the ML-KEM Braid's
    translated code refines the model)").
- **Does not cover:**
  - An attacker that holds the Braid's authenticator keys and replaces the
    epoch's messages. It takes the agreement, and nothing heals.
  - How long an epoch takes. At these parameters, with strict alternation, it
    is about a hundred messages, measured in
    `tacenta-core/tests/post_quantum_stack.rs` (mlkem-braid.md, Properties a
    caller must know).

## What it needs

**An agreement the attacker did not take.** This is the condition, not a detail.
An attacker holding a ratchet private key computes the agreement output for
itself, and nothing heals: it follows every step. That is what makes compromise
of long-lived key material worse in kind than compromise of a chain, and no
ratchet repairs it. REQ-PCS-03 has the same condition for the Braid: an epoch
whose shared secret the attacker did not take.

**A step to happen at all.** A step comes from receiving a message under a
ratchet key not yet seen, so a party that only sends never takes one. How many
messages pass before recovery is a property of the conversation rather than of
the protocol, and this page does not promise a bound. A Braid epoch completes
only if both sides send.

## What is not proved

**An attacker holding more than the root key.** The theorems give the attacker
exactly the root key. One that also holds other material from the session -- a
chain key, a stored skipped key -- is not what they are about, and this page
does not claim they cover it.

**The fidelity assumption.** The attacker is symbolic: it derives keys only by
the rules given, and the rules mirror the key schedule with none that runs a
derivation backwards. Against the real protocol that holds only if the key
derivation is one-way and collision-resistant, which is not proved here or
anywhere in this project (ASM-10). What is proved is the protocol's own half --
given such a derivation, the structure leaks nothing -- which is exactly the
part a protocol can get wrong by itself.

**A session, as opposed to a step.** The statements are about the attacker's
terms, not about `Model.State`. Relating the two is not written, so "this session
has healed" is not yet a sentence this project can prove about a running session
(limitations.md, LIM-03).

**Anything about the post-quantum ratchet.** Recovery there is slower by design,
because the agreement it heals from is sparse. That ratchet is specified on its
own page, and none of the theorems above covers it. REQ-PCS-03 states what is
assumed there.

## Sources

- Signal's published Double Ratchet specification, **revision 4, 2025-11-04**,
  for the Diffie-Hellman ratchet and its recovery properties, and for the
  observation that a compromised chain runs forward unaided. Archived and pinned
  in the conformance manifest.
- Forward secrecy is the same mechanism read in the other direction. It is
  stated in security-properties/forward-secrecy.md, and
  `protocol/key-deletion.md` gives the deletions it rests on.
