# Group epochs: key epochs and obligations

Part of the draft group-epochs.md (the entry page). Status: draft, awaiting review; see group-epochs.md for the review record and what the draft is not.

This part holds Key epochs, with Obligations on the key engine, and Obligations
at the product boundary, and "check N" in it means a successor check of
group-epochs-successor.md unless a genesis or checkpoint check is named.

## Key epochs

Every accepted successor starts a new key epoch: `key_epoch` is the
predecessor's plus 1 (check 9; group-epochs-decisions.md, Open decision D-2). So in a chain that starts at
genesis `key_epoch` equals `epoch_number`, and material bound to an earlier
epoch is never current in a later one. A sibling that displaces the head has the
head's `key_epoch`, since both are one more than `prior`'s, and a different
commitment, so its key binding differs from the displaced head's (group-epochs-siblings.md, Siblings). A
verifier that started from a checkpoint takes the checkpoint's `key_epoch` on
the inviter's word: no check relates it to the checkpoint's epoch number, so the
equality is not established for it, only that each later epoch's `key_epoch` is
one more than its predecessor's. A checkpoint whose `key_epoch` is 2^64 - 1 has
no successor (check 9). The field is written out so that a rule that advances it
only on some epochs (group-epochs-decisions.md, Open decision D-2) changes one check and not the encoding.

The key binding of an epoch `E` is the triple `key_binding(E)` = (`group_id`,
`key_epoch`, `epoch_commitment(E)`).

### Obligations on the key engine

The key engine is not yet specified. Whatever it is, these are what it takes
from accepted state, and each is a requirement on the engine that this page
states for the engine's own specification to meet.

1. **Binding.** Every unit of group key material is created for exactly one
   accepted epoch `E`, and records `key_binding(E)` at creation. The recorded
   binding is never rewritten.
2. **Distribution.** Material is distributed to a device only if its recorded
   binding equals `key_binding(head)` and the device is a member device of
   `head`. Recipients are never taken from a directory, an inventory statement,
   a pending invitation or an earlier epoch, including on a retry.
3. **Use.** Material is current only if its recorded binding equals
   `key_binding(head)`. Any other material is retired: it is not used to send,
   it is not accepted as current-epoch traffic, and it is never relabelled as
   current. What the engine may still do with retired material, such as decrypt
   a message received earlier, is the engine's own rule.
4. **Retirement.** Accepting a successor, or displacing the head, retires all
   material bound to the previous head in the same durable step. There is no
   state in which the successor or the displacing sibling is the head and the
   previous head's material is still current.
5. **Displacement.** Material bound to a displaced epoch is retired as if that
   epoch had never been accepted, and is never current again: a displaced epoch
   does not become the head again (group-epochs-siblings.md, Siblings). No material of the displacing
   sibling or of a later epoch is derived from it, and nothing the engine does
   for a later epoch relies on a device having received it. A device that the
   displaced epoch listed and the displacing sibling does not may already hold
   it.

These five are bookkeeping. They fix which epoch material is bound to, who is
sent it and when it stops being current. They do not say that material created
for a later epoch cannot be computed from material an earlier member holds,
which includes a removed device: a key engine could derive every later key from
an earlier one and meet all five. That independence is what makes a removal mean
anything against a device that keeps its keys. It is the key engine's
obligation. This draft does not list it among the five obligations above and does
not establish it (group-epochs-removal.md, The removal invariant, What it does not claim).

## Obligations at the product boundary

These are not checked by this draft, and the product's tests are where they are
exercised. Items 1 to 5 are the parts of the removal property that a product
supplies. Items 6 to 10 are what a coordinator, an inviter and the product's
stores do so that a sibling race settles, so that a split is less frequent, and
so that a failure part-way through a step cannot make a verifier refuse the same
epoch for good. Item 7 is the product's part of the order among the owner's
devices and of the rule for them (group-epochs-siblings.md, Siblings, Rank and Owner devices). They are
requirements on the product, and none of them changes a check or a result.

1. The product commits an epoch that becomes the head, by acceptance or by
   displacing the head, durably before it distributes key material or
   dispatches application traffic for it.
2. When the head changes, by accepting a successor or by a displacement, the
   product cancels every unsent item and every remaining retry addressed to a
   device that is not a member device of the new head, and keeps the record of
   what was handed off before. That covers a device that a successor removes,
   and a device that a displaced epoch admitted and the displacing sibling does
   not list.
3. The product takes the recipients of every distribution and send from the
   head, not from a directory. It does not propose or distribute while it knows
   of a gap in the chain from its own fetch of it, or while the only successor
   of the head that it has seen is `unsupported`. It does not propose again a
   batch that it assembled against a head that has since moved. A
   `missing-predecessor` result on candidate bytes alone is not that knowledge
   of a gap, because anyone can produce one.
4. A removed device is treated as a new device if a later epoch admits it: it
   receives no application history and no key material of an earlier epoch.
5. The product starts a verifier from a checkpoint only on an invitation it has
   authenticated as made by the inviter the joiner means to trust and as
   unmodified, and it pins the checkpoint commitment from that invitation alone:
   not from a directory, an inventory statement, a service's list of heads or
   the bytes of the epoch. A device that already holds state for the group
   discards it, and what is tied to it, before it starts from a checkpoint,
   because a verifier that holds a head refuses one. It does so only when the
   user has chosen to replace that group, and not because a checkpoint was
   refused as `already-started`: an inviter chooses the `group_id` its epoch
   names, and can name one the device already holds.
6. When an epoch that the coordinator proposed is displaced at its verifier, or
   is refused there as `outranked` or `removed-by-head`, the change it carried
   has not taken effect at that slot. The coordinator does not treat it as
   made: it proposes the change again, as a new batch against the new head, if
   the intent still holds and, for an admission, with a statement that the
   caller's freshness rule accepts (group-epochs-siblings.md, Siblings, Evidence of a sibling). Before
   each new proposal it waits for a time that grows with each loss and has a
   random part, and after a number of losses that the product states it stops
   and tells its user. A writer whose epochs a writer that ranks before it keeps
   displacing, such as one of the owner's devices or the admin whose handle
   sorts first, can wait without bound (group-epochs-siblings.md, Siblings, Rank), and the product tells
   that writer's user so. Traffic sent under the displaced epoch's material is
   the product's to send again, under the new head's material and to the new
   head's member devices, if it is still to be delivered.
7. The product shows the owner which of the devices of the owner's principal
   ranks first among them (group-epochs-siblings.md, Siblings, Rank). The product has a removal of a
   device of that principal written by the device of that principal that ranks
   first among those the removal leaves in place. A removal written by another
   device can be displaced by an honest device that ranks before the writer and
   that the removal leaves in place, and the removed device is then a member
   device with authority of the new head, if that sibling lists it (group-epochs-siblings.md, Siblings,
   Owner devices). The product treats the loss of any device of that principal,
   whatever its rank, as needing recovery outside this draft (group-epochs-limits.md, Recovery, under
   What is not checked).
8. A coordinator proposes an epoch only on a head that has settled: one that it
   has held for at least a delivery bound that the product states, so that no
   sibling of it that ranks before it can still arrive within that bound, or one
   that already has an accepted successor. So it does not build a second epoch
   on one it proposed until that one has settled. It may instead rely on an
   ordering hint: a service that refuses a second proposal for one predecessor
   commitment, so that one writer proposes at a time. The hint gains no
   authority. Verifiers judge every epoch by this draft's rules whatever the
   service said, a service that does not keep to the hint can still split a
   group (group-epochs-limits.md, Order, under What is not checked), and the hint only makes races less
   frequent. A head that has settled under the product's bound is not final
   (group-epochs-siblings-forks.md, Siblings, What the order does not resolve).
9. The step in which a candidate is accepted, or displaces the head (group-epochs-successor-effects.md, Effects),
   spans three stores: accepted state (`head`, `prior`, `index`), the caller's
   record of generations (group-epochs-successor.md, Inputs) and the key engine's material. The caller
   evaluates its freshness rule again before the step, as Inputs (group-epochs-successor.md) says. Then it
   commits the durable step of accepted state, before anything else. The
   caller's record of the candidate's generations is part of the same write, or,
   if it is in another store, is written after it and is derived again from
   accepted state on restart: the generations to record are those that the head
   carries for the devices it lists and `prior` does not (every device, for
   genesis; none, for a checkpoint), with the head's group and epoch number, and
   recording one again changes nothing, since a stored value never decreases.
   The key engine's current binding is a function of the head at every use, and
   not only on restart: the engine keeps no record of currency of its own that
   could still name an earlier head, and a product that keeps one allows no send
   or distribution until that record names the head (items 1 and 2). On restart
   it is `key_binding(head)`, all other material is retired (Obligations on the
   key engine, 3), and retiring material twice is the same as retiring it once.
   So a crash between the stores leaves no retired epoch's material current and
   no generation recorded for a head that was not kept, and cannot make the
   verifier refuse the same epoch for good. The record made for an `outranked`
   or `removed-by-head` sibling is in one store and needs no order. This page
   requires that order and that derivation. How each store is written, and what
   a verifier does after its state is restored from a backup (group-epochs-limits.md, Storage, under
   What is not checked), are the product's.
10. An inviter gives as a checkpoint only an epoch that already has an accepted
    successor at its own verifier, or waits until it has one, and then gives
    that epoch, not its successor. A joiner started at an epoch that has no
    successor is stranded for good if a sibling displaces that epoch at the
    other verifiers (group-epochs-genesis-and-joining.md, Joining from a checkpoint, After the checkpoint). In a
    quiet group that means writing an epoch with no operation (group-epochs-limits.md, Cadence, under
    What is not checked), which starts a key epoch. Only an authority device can
    write one (group-epochs-encoding.md, Policy version 1), so an inviter that is not one waits for an
    authority device to write it, with no bound that this draft states.

A caller may keep, while the head is unchanged, the epoch number and commitment
of a candidate that the verifier answered `outranked` or `removed-by-head`, and
answer a later copy of that commitment itself, without offering it to the
verifier, so that a replay does not cost the work of checks 1 to 12 again
(group-epochs-limits.md, Sizes and costs, under What is not checked). This page permits it. The answer
is the same refusal: the head is unchanged, the commitment covers the body, and
the candidate's generations were recorded the first time. A full judgement of
the copy could differ only in the kind of its refusal, where the copy's
signature bytes, the evidence, the verdict or the caller's store differ from
the first time, and it would change no accepted state and no record either. The
caller drops the entries when the head changes, since a sibling that the old
head refused can displace a new one.
