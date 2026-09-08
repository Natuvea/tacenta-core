# The Sparse Post-Quantum Ratchet

This page describes the second message ratchet: one that derives message keys
from a post-quantum key agreement rather than from Diffie-Hellman. It is our own
description, written from the published specification named in Sources.

It is not a replacement for the Double Ratchet. The two run side by side and
each produces a message key; the key that actually encrypts is derived from
both. That composition is the Triple Ratchet, described on its own page. Read
this page as one half of it.

## Why a second ratchet at all

The Double Ratchet's forward secrecy and post-compromise security rest on
Diffie-Hellman assumptions, which do not survive a cryptographically relevant
quantum computer. Session establishment already folds in a post-quantum
encapsulation, so a session begins with post-quantum protection; but nothing
after that reintroduces it. An attacker who records traffic today and gains a
quantum computer later is limited by what the *handshake* mixed in, and the
Diffie-Hellman ratchet's ongoing reseeding adds nothing against them.

The obvious repair is to ratchet with a post-quantum key encapsulation instead
of Diffie-Hellman. The obstacle is size. Post-quantum encapsulation keys and
ciphertexts are on the order of a kilobyte where a curve key is thirty-two
bytes, so attaching one to every message is not affordable on a constrained
link.

The specification's answer is to weaken what the key agreement promises. A
*continuous* key agreement produces a fresh secret with every message and
requires the parties to alternate. A **sparse** continuous key agreement drops
both requirements: secrets arrive only occasionally, and either party may speak
twice. That is enough to ratchet with, and it is achievable within a bandwidth
budget, because a large key exchange can be spread across many messages instead
of riding on one.

## What this ratchet assumes underneath it

This ratchet is defined over *any* sparse continuous key agreement. The
agreement itself is a separate protocol with its own specification, and this
page treats it as a boundary, in the same way the ratchet page treats
Diffie-Hellman.

The boundary offers two operations. **Sending** returns a message to carry, the
latest epoch the receiver is guaranteed to know once it has processed that
message, and *optionally* a new secret together with the epoch that secret
belongs to. **Receiving** takes such a message and returns the epoch the sender
was working in, and again optionally a new secret and its epoch.

Two things follow from that shape and both matter:

- **Secrets are occasional.** Most sends and receives produce none. The ratchet
  advances only when one appears.
- **Epochs are the unit of synchronisation.** Every message names the epoch its
  key came from, and the agreement guarantees the counterpart can reach that
  epoch. Nothing else keeps the two sides aligned.

The agreement we use is the [ML-KEM Braid](mlkem-braid.md) protocol, specified
separately and pinned in the conformance manifest.

## State

Beyond the agreement's own opaque state, a party holds:

| Variable | Meaning |
| --- | --- |
| `RK` | the root key, thirty-two bytes |
| `epoch` | the latest epoch whose secret has been folded into `RK` |
| `kdfchains` | per epoch, a sending chain and a receiving chain |
| `MKSKIPPED` | per epoch, message keys stored for messages not yet arrived |
| `direction` | which side of the session this party is |

Two differences from the Double Ratchet's state deserve attention, because they
are what makes this ratchet structurally heavier:

**Chains are held per epoch, not one pair at a time.** The Double Ratchet holds
one sending chain and one receiving chain and replaces them at each step. Here
both sides may keep sending across the gap between two secrets, so a new epoch
brings a *pair* of fresh chains into a table while the previous pair is still
live.

**Skipped keys are indexed by epoch as well as by message number.** The Double
Ratchet's store is keyed by the ratchet public key and the number. Here it is
keyed by epoch and number, and it is a map in exactly the same sense: one pair,
one key.

## Derivations

Three, all keyed hash derivations, and each distinguished by a constant that
names the protocol and its parameters so that no output can collide with a
derivation from anywhere else in the system.

- **Initialisation** takes the shared secret from session establishment and
  yields a root key and both chain keys at once.
- **The root step** takes the current root key and a secret from the agreement,
  and yields a new root key and both chain keys.
- **The chain step** takes a chain key and the message number, and yields the
  next chain key and a message key.

The chain step differs from the Double Ratchet's in taking the *counter* as an
input rather than a fixed constant. That is a real difference and not a
presentational one: it binds each message key to its position in the chain.

## Initialisation

Both parties begin from the same shared secret and derive the same root key and
the same pair of chain keys. **The two sides then assign that pair oppositely**:
what one party uses to send, the other uses to receive. Getting this backwards
produces two parties who agree on every derivation and can decrypt nothing, so
the direction flag exists precisely to make the asymmetry explicit rather than
implicit in the order of two variables.

Both start at epoch zero with one pair of chains.

## Sending

The party asks the agreement for a message. If it returns a secret, the ratchet
advances first: the root key absorbs the secret, both chain keys are derived
from it, they are assigned according to direction, and a fresh pair of chains is
placed in the table under the new epoch. The specification requires the new
epoch to be exactly one past the current one, so a gap is an error rather than
something to accommodate.

Then, whether or not the ratchet advanced, the sending chain for the epoch the
agreement named is stepped once, and the resulting message key encrypts. The
header carries the agreement's message and the message number.

## Receiving

The mirror, with one addition. The agreement's message is handed to it; if a
secret comes back, the root key advances exactly as above.

Then, before deriving anything, the store of skipped keys is consulted for this
epoch and number. If a key is there it is used and **removed**. That is the
only path by which a stored key is consumed, and removing it is what makes it
one-use.

Otherwise the receiving chain for the named epoch is stepped forward to the
message's number, storing every key it passes, and then once more to produce the
key for the message itself. Stepping forward is bounded: a header demanding more
than the permitted number of skips is rejected rather than served, so a peer
cannot induce unbounded work by claiming a distant message number.

### The store also has a total bound

**This bound is this implementation's addition.** The published algorithm
bounds a *single* request against the permitted number of skips, and separately
retires whole epochs. This implementation additionally caps the store's total
size, so the store is bounded independently of how many messages are skipped
within an epoch. Epochs are sparse by design, so one may span a great many
messages.

The Double Ratchet is bounded here with a cap on the store's total size. The
same cap applies here, for the same reason, and a request that would exceed it
is refused. `Proofs.SparseRatchetCorrectness` proves
the bound holds rather than checking it at sample points.

## Retiring old epochs

The ratchet keeps chains for a bounded number of epochs and discards the rest,
**including the skipped keys stored under them**. The specification is explicit
that this limits how far out of order a message may arrive and still be
decryptable, and equally explicit about who that suits: deployments where
messages are often dropped but rarely arrive very late.

The specification offers a second approach, mirroring the Double Ratchet's:
carry the previous chain's length in the header and use it to seal that chain
when the epoch advances. It attaches a warning to it, and the warning is worth
repeating: **under that approach nothing bounds the store of skipped keys, and
an implementation must supply its own mechanism or it grows without limit.**

We take the first approach, the one in the main text. Two reasons. It bounds the
store by construction rather than by a policy we would have to choose and
defend, and it is what a faithful reading gives by default. Our expiry mechanism
for the Double Ratchet's store exists because that ratchet has the second
problem; there is no reason to import the problem here in order to reuse the
solution.

## What this does not provide on its own

Running this ratchet *instead of* the Double Ratchet would trade one assumption
for another, not add to it: post-quantum security in place of the elliptic-curve
guarantees rather than alongside them. The composition that gives both is on the
Triple Ratchet page, and it is the only configuration we intend to deploy.

Post-compromise security also arrives more slowly here than in the Double
Ratchet. Recovery waits on the agreement producing a fresh secret, which by
design is occasional, so more messages must pass before a compromised party is
healed. That is the price of the bandwidth saving and the specification is
direct about it.

## Sources

- Signal's published Double Ratchet specification (Trevor Perrin, editor; Moxie
  Marlinspike; Rolfe Schmidt), **revision 4, 2025-11-04**, Section 5. It defines
  the sparse continuous key agreement interface, the state variables, the three
  derivations, initialisation for both parties, the sending and receiving
  procedures, the skipped-key handling with its bound, and both approaches to
  retiring old epochs. The archived copy this page was written from is pinned by
  SHA-256 in the conformance manifest.
- The ML-KEM Braid specification (Rolfe Schmidt), **revision 1, 2025-02-21, last
  updated 2025-09-26**, for the agreement this ratchet is instantiated with. It
  is restated on [its own page](mlkem-braid.md) and pinned alongside.

The constants in each derivation split two ways, and
[CONSTANTS.md](../CONSTANTS.md) keeps them apart. The initialisation suffix
`"Chain Start"` is **stated literally by the Double Ratchet specification**,
tier `fact`, and the engine uses it. The root and chain step suffixes are not
the specification's: it names the epoch-advance suffix `"Chain Add Epoch"`,
and the engine derives its root step under `"Root"` and its chain step under
`"Chain"` -- tier `ours`, matched by the model and the conformance vectors,
and recorded as a departure. The constant that names the protocol is not
fixed by the specification either: it requires one and fixes no value, so ours
is a free choice at tier `ours`. Neither is an open interoperability question:
`SPQR_PROTOCOL_INFO` is unobtainable by any black-box route and message-layer
interoperability is not attempted, so there is no peer for these to match.
