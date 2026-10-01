# Group epochs: equivocation and forks

Part of the draft group-epochs.md (the entry page). Status: draft, awaiting review; see group-epochs.md for the review record and what the draft is not.

This part holds the rest of Siblings: Equivocation, What the order does not
resolve and Fork hint, and "check N" in it means a successor check of
group-epochs-successor.md unless a genesis or checkpoint check is named.

### Equivocation

When `c` and the head have the same writer, one device signed two different
epochs for one predecessor: equivocation, or a device that assembled a batch
twice. The rank chooses between them by commitment, and the verifier gives the
caller both signed epochs, the head and `c`, with the result (`displaced` or
`refused(outranked)`), as a record that the device signed both. Nothing in this
draft acts on that record: no state keeps it, no check reads it, and the verifier
goes on accepting. The draft does not say what a product does with it. A pair
shows that one device signed two epochs for one predecessor and nothing about
intent: a device that assembles a batch twice produces one honestly, and every
replay of an `outranked` epoch of the head's writer gives the same pair again. A
product that acts on a pair, by removing the device or alerting a user, can be
driven by anyone who holds two such epochs; it counts a repeated pair once, and
acts, if at all, only on a pair whose two epochs list different operations.
Stopping a verifier on equivocation would let one device stop it for good with
two signatures. The verifier keeps no candidate that is not its head, so it
reports a pair only when one of the two is its head: two epochs of one writer
that both rank after the head, or that arrive after a successor, are not
reported.

### What the order does not resolve

The rank applies only while the head has the siblings' epoch number. Once a
verifier accepts a successor of its head, a sibling of that head is `superseded`
(check 2), whatever its rank: the draft does not undo two epochs. An epoch is
therefore final at a verifier, in the sense that no sibling displaces it there,
once that verifier has accepted a successor of it, and not before. A head that
has no successor is therefore provisional however long it stays the head, and in
a quiet group it stays so until an authority writes an epoch with no operation,
which starts a key epoch (group-epochs-limits.md, Cadence, under What is not checked). The rank settles
a race only at the verifiers that receive the siblings before they accept a
successor of any of them, and no verifier can tell whether a sibling that ranks
before its head is still to come. When some verifiers have accepted a successor
of the sibling that ranks second and others hold the one that ranks first, the
group is on two branches: each side answers the other's later epochs
`missing-predecessor` or `superseded`, nothing in this draft brings them
together, and nothing tells a user. A writer that signs a successor of its own
sibling at once, before a sibling that ranks first arrives, turns a race it
would lose into such a split at the verifiers whose delivery it can arrange, and
a network that delivers a successor built on the second sibling first does the
same.

Verifiers that judge one sibling differently also end on different heads. One
whose caller refuses the sibling's evidence (check 12), whose product's verdict
denies it (check 11), or that does not support a policy version it sets
(`unsupported`, check 6) keeps its head, and another is displaced.

So do verifiers that receive in different orders a removal or demotion of a
device of the owner's principal, written by a device of that principal that
ranks after it, and a sibling written by the removed device, and, with three or
more such devices, verifiers of which only one received a replay of a sibling
that the other refused (group-epochs-siblings.md, Owner devices).

A verifier whose head is the checkpoint it started from judges no sibling of it
(check 2), and cannot follow a sibling that displaces the checkpoint at the
other verifiers (group-epochs-genesis-and-joining.md, Joining from a checkpoint, After the checkpoint).

A `close` has no successor (check 3), so it is never final: a sibling written by
a device of the owner's principal that ranks before the device that wrote the
`close`, or by that device with a lower commitment, displaces it whenever it
arrives, and the group is open again at that verifier. A `close` removes no
device, so the rule for owner devices never protects it. And at a verifier that
received first a sibling, written by another device of the owner's principal,
that removes or demotes the device that wrote the `close`, the `close` is
`removed-by-head` and does not take effect there while that sibling is the head
(group-epochs-siblings.md, Owner devices). No operation reopens a group, but a displacement is not an
operation, and a `close` is final at no verifier. A `close` written by the
device that ranks first among the owner's devices is displaced only by that
device's own epochs, and is refused only where an epoch of another owner device
that removes or demotes that device arrived first.

The rank is a choice between branches at depth one and at no other depth. No
rule here selects a winner from a service's order or a timestamp, and a
commitment's value orders only two epochs that one writer device signed. Beyond
depth one the order of arrival decides which branch a verifier is on, and a
verifier on the other branch of a deeper fork is on a branch that nothing here
brings back; starting a new verifier from a checkpoint does not choose between
branches either (group-epochs-genesis-and-joining.md, Joining from a checkpoint). Recovery from such a fork is
separate work that this draft does not specify.

### Fork hint

Let `m` be a candidate's epoch number and `n` the head's. A candidate that
decodes and names the head's `group_id` (checks 1 and 2) can name, as its
predecessor, an epoch that the verifier holds, and still not be the epoch the
verifier holds for its own number: it would be a sibling of an accepted epoch.
For such a candidate the verifier returns the hint `possible-fork` beside the
result that check 2 gives, in two cases:

- `m` < `n`, the result is `refused(superseded)`, and the candidate's
  `predecessor_commitment` is `index[m - 1]`, where that entry is held;
- the head is the checkpoint the verifier started from, `m` = `n`, the result
  is `missing-predecessor`, and the candidate's `predecessor_commitment` is the
  head's own `predecessor_commitment`.

The hint has no rule behind it. It changes no result, no accepted state and no
record, and the verifier keeps nothing for it. Nothing is verified for it:
check 2 answers before check 5, so neither the signature nor the writer's
authority has been checked, and anyone who knows the commitment of an accepted
epoch can make a verifier return the hint with bytes of their own. It is not
evidence of a fork. It is also returned without a fork: for a sibling that
ranked after the epoch that won its slot and arrived after a successor of that
epoch, and for every replay of such a sibling. A product may count the hint and
show the count. The verifier offers no way to judge a candidate that carried it
against the epoch at `m - 1`, which is not its head, and this draft has no rule
for doing so. Because anyone can raise the hint as often as they can send bytes,
a product bounds how often it counts it, shows it or acts on it, and does not
stop proposing, discard state or start recovery on the hint alone. What a
product does about a fork that is real is recovery, which this draft does not
specify.
