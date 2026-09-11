# Adversaries

The adversaries the requirements in `security-properties/` are stated against.
Each is numbered, and for each this page says what it can do, what it cannot do
while the assumptions hold (assumptions.md), and how the proofs represent it.

**One adversary appears in any proof, and it is symbolic.** `Model.Adversary`
in `tacenta-model` defines `Knows held k`: the attacker holds the keys `held`
and derives a key only by rules that mirror the key schedule, none of which
runs a derivation backwards. The security theorems in `tacenta-model/Properties/`
give it exactly one key. It has no network, no messages, no sessions interleaving
and no time. So ADV-02's compromise is represented by what it holds, and nothing
of ADV-01's control of the network is represented at all. Relating the symbolic
attacker to a real one is ASM-10.

## ADV-01: the network adversary

An active attacker in the style of Dolev and Yao, in control of every channel
between the parties and between a party and the directory.

It can:
- read every byte sent;
- drop, delay, reorder and replay messages;
- inject any bytes, including messages assembled from parts of others, and
  forged messages claiming a far-future number, which make a receiver derive
  up to `MAX_SKIP` keys before it refuses them;
- fetch any party's published bundle, and replace a bundle in transit (ADV-04's
  power over bundles);
- register an identity of its own and establish sessions under it with honest
  parties, towards whom it is then also ADV-06.

It cannot, while ASM-02 to ASM-07 hold:
- compute a key it was not given;
- make a message that authenticates under a key it does not hold;
- make a signature under an identity key whose secret it does not hold.

Proofs: none represents it (ASM-13). Its power reaches the symbolic theorems
only through the keys it holds, which are none.

## ADV-02: compromise of a party's state at a point in time

An attacker that takes a copy of some or all of a party's secrets at one moment
-- any of AS-02 to AS-09 as the party held them then -- and afterwards acts as
ADV-01. With the identity secret it can also act as the party. It does not stay
in the endpoint, and it does not take the state a second time. An attacker that
does either is EX-02.

The requirements distinguish what was taken:

1. one message key (AS-08);
2. one chain key (AS-05, AS-06);
3. a root key (AS-05, AS-06);
4. a ratchet private key, or the Braid's decapsulation key or authenticator
   keys (AS-05, AS-07);
5. the identity secret or a prekey secret (AS-02, AS-03);
6. everything the party holds, including its persisted state (AS-09).

An attacker that reads the store without writing it is this adversary, not
ADV-05.

Proofs: the symbolic attacker holding exactly one term. It holds a chain key
in `Properties.ForwardSecrecy`, a message key in `Properties.Secrecy`, a root
key in `Properties.PostCompromise`, and one session's chain key in
`Properties.Authentication`. Cases 4 to 6 have no theorem.

## ADV-03: the future quantum adversary (harvest now, decrypt later)

An attacker that records everything ADV-01 can read, from before a session is
established. At some later time it gains a quantum computer that computes
discrete logarithms on curve25519. It then recovers every X25519 private key
from its public key, so it computes every agreement output `DH1` to `DH4` and
every Diffie-Hellman ratchet output of the recorded traffic, and it can forge
XEdDSA signatures.

It cannot, while ASM-04 to ASM-07 hold against a quantum adversary:
- recover an ML-KEM-1024 shared secret;
- distinguish HKDF-SHA256 or HMAC-SHA256 output from random;
- break AES-256.

It is passive until it has the computer. An attacker with that power while a
handshake runs is outside this specification (EX-11).

Proofs: none.

## ADV-04: a malicious or compromised directory

The server a party publishes its keys to and fetches bundles from
(session-establishment.md, Publishing keys; key-deletion.md, Prekeys at rest).
Its own behaviour is unspecified (EX-06).

It can:
- serve, for any identity, any bundle: an old one, one whose one-time prekeys it
  has already served, one with no one-time curve prekey, one naming only the
  last-resort KEM prekey, or one it built around an identity key of its own;
- serve one one-time prekey to many initiators, or all of them at once;
- withhold bundles;
- see who fetches whose bundle (EX-01).

It cannot make a bundle whose prekey signatures verify under an honest party's
identity key without that key's secret (ASM-03). Whether the identity key in a
bundle is the one the initiator means to reach is not something the protocol
can check: that is ASM-14, and, where the initiator names the key she expects,
REQ-AUTH-02.

Proofs: none.

## ADV-05: a writer of the persisted store

An attacker that writes a party's persisted session or prekey store between an
export and the next import. It can substitute any bytes:
- another party's export;
- an earlier export of the same state (a rollback);
- a state it constructed that keeps every semantic rule the readers check
  (session-persistence.md).

Were it in scope, a rollback would:
- bring back a message key already used (REQ-CONF-04);
- bring back one-time prekeys already deleted, and forget entries of the
  last-resort replay record (REQ-AUTH-12);
- undo a rotation.

**This adversary is outside this specification** (ADR-0007; exclusions.md,
EX-07). A reader checks persisted bytes against corruption, not against a
writer (session-persistence.md, Principles). It is listed so that no
requirement is read as holding against it.

## ADV-06: a malicious peer

A party that holds an honestly established session with its victim. It holds
that session's keys, so it reads what the victim sends it and authenticates
what it sends.

It can, within that session:
- skip ahead, to fill the victim's skipped-key stores or make the victim evict
  stored keys (ratchet.md, Skipped keys; sparse-pq-ratchet.md);
- drive the count by which stored keys expire, to age out keys the victim holds
  for delayed messages (key-deletion.md);
- claim a far-future message number, making the victim derive up to `MAX_SKIP`
  keys before the forgery is found;
- never reply, so that no Diffie-Hellman step and no Braid epoch completes
  (REQ-PCS-01, REQ-PCS-03);
- send Braid chunks that fail the authenticator, moving the victim's agreement
  to `Failed` (mlkem-braid.md, Failure);
- return to a ratchet key it used before.

It cannot, while the assumptions hold:
- read or write in another session of the victim (REQ-CONF-08);
- be believed as a different identity (REQ-AUTH-03).

It is not an adversary against the confidentiality of what the victim sends
it.

Proofs: none.
