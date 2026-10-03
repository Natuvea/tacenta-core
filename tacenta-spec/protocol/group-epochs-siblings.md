# Group epochs: siblings

Part of the draft group-epochs.md (the entry page). Status: draft, awaiting review; see group-epochs.md for the review record and what the draft is not.

This part holds Siblings: Rank, Owner devices, Displacement and Evidence of a
sibling, and "check N" in it means a successor check of
group-epochs-successor.md unless a genesis or checkpoint check is named.

## Siblings

A verifier holds one epoch for each epoch number. When two authorised writers
write different successors of one epoch, or one writer writes two, the two are
siblings: they have the same predecessor `P` and different commitments, and each
can be valid against `P`. A verifier that holds one of them as its head and
receives the other judges it against `P`, which is `prior`, by every check of
Accepting a successor (group-epochs-successor.md), and then compares the two by a fixed order, the rank,
after one rule for two devices of the owner's principal (Owner devices, below).
The one that ranks first is the head, except where the rule for owner devices
refuses it, and the other is not accepted state. The rank depends only on `P`,
on which device wrote each sibling and, between two epochs of one device, on
their commitments, so every verifier that holds `P`, receives the same siblings
that pass every check, in any order, and judges each of them the same way, ends
on the same one (group-epochs-siblings-forks.md, What the order does not resolve, below). That holds on two
conditions. The verifier accepts no successor of any of them before the last one
arrives, which no verifier can detect. And no sibling written by a device of the
owner's principal removes or demotes another device of that principal that ranks
before its writer and has written one of the siblings (Owner devices). When the
second does not hold, the head can depend on the order of arrival, and a replay
of a sibling can change it (Owner devices). This is Open decision D-12, option
F (group-epochs-decisions.md). There is no sibling of genesis: a second genesis epoch is refused as
`superseded` (genesis check 2).

Siblings arise without bad faith. An authority device that is one epoch behind
writes a sibling of a head it has not seen. Two devices of one account each
propose the same change, and since the writer is in the body the two are
different epochs. A retry assembles a batch again. A service that kept the
losing epoch of a race delivers it later, and anyone who holds its bytes can do
the same without a key. None of these stops a verifier, and none of them leaves
two verifiers on different heads when the siblings reach both before a successor
does, apart from the case that Owner devices describes: a replay of an epoch
that ranks after the head is `refused(outranked)`, or `refused(removed-by-head)`
where the rule for owner devices applies, and changes neither the head nor
`index`, and an epoch that ranks before the head displaces it at every verifier
it reaches, except where that rule refuses it. In that case a replay is not
harmless: the refusal depended on the head at the time, and the same bytes can
displace a different head later (Owner devices).

### Rank

Let `P` be the predecessor of a sibling `c`, and let the writer of `c` be the
device that its `writer_account` and `writer_binding` name. Check 4 finds that
device in `P` as an authority device, and check 5 shows that its key signed the
body. The rank of `c` is this tuple, compared component by component; the lower
tuple ranks first:

1. the role, in `P`, of the writer's principal: 1 (owner) before 2 (admin);
2. the position of the writer's principal among the `principals` of `P`, in
   their encoding order (group-epochs-encoding.md, Order);
3. the position of the writer's device among that principal's `devices` in
   `P`, in their encoding order;
4. the commitment of `c`, as 32 bytes in byte-wise order.

Two siblings with different writers differ in the first three components, so
the fourth decides only between two epochs that one writer device signed. `P`
lists each identity key at most once (check 7, which `P` passed when it became
the head, or checkpoint check 5 or genesis check 5 for a first head), so the
device whose key signed an epoch has one position in `P`.

No field of a body moves the first three components: `P` and the device that
signed fix them. A writer can vary its body, and so its commitment, through the
operations it lists or, for the owner, the `policy_commitment` it sets, but a
commitment orders only that writer's own epochs. The draft does not order two
writers by commitment: a writer that can vary its body could try many bodies,
sign the one with the lowest commitment, and so win every race against another
writer. A principal that holds several authority devices can sign with
whichever of them ranks first. That is a choice among its own devices.

The order is fixed, and it is not neutral. The owner's devices rank before every
admin's. Among admins it follows the byte order of their account handles
(group-epochs-encoding.md, Order), so an admin whose handle sorts first displaces the epoch of any other
admin while that epoch has no successor, and an account that can choose its
handle chooses its place; an owner that makes a principal an admin gives it
that place. Among the devices of one principal it follows their bindings, so
`device_id` first. For the owner's principal that is not a choice among equals:
the device that ranks first wins every dispute between the owner's devices that
the rule for owner devices does not decide, and so holds the owner's power
against the others at depth one. This draft does not assign `device_id` and does
not choose which device that is (group-epochs-key-epochs.md, Obligations at the product boundary, 7).

### Owner devices

Let the writers of a sibling `c` and of the head `H` be two different devices
of the owner's principal in `P`. An epoch removes a device of that principal
when its operations include `remove_device` for that device's binding, and it
demotes every device of that principal when they include `transfer_ownership`.
If `H` removes or demotes the writer of `c`, the result for `c` is
`refused(removed-by-head)`, whatever its rank, and the caller records the
generations of its statements as for `outranked` (Evidence of a sibling).
Otherwise `c` is ranked against `H` as Rank says. Two epochs that one device
wrote are always ranked, by commitment, and a sibling written by an admin is
always ranked.

So a device of the owner's principal that another of its devices removed, or
that lost the owner role by a `transfer_ownership` that another of its devices
wrote, cannot displace the head that did it, whatever its place, and a transfer
that a verifier has accepted is not redirected there by another device of the
former owner. The rule only refuses. It never lets a sibling displace a head
that ranks before it, so the head at one epoch number still moves only to an
epoch that ranks before it (Displacement).

**What the rule does not give.** It protects a head only against the devices
that the head removes or demotes. A device of the owner's principal that the
head neither removes nor demotes displaces the head with a sibling that passes
every check, if it ranks before the head's writer, whatever else the head does
(Displacement). So a head that removes a device of that principal is protected
against every other device of the principal only if it demotes them all, as a
`transfer_ownership` does, or if every other device that ranks before its writer
is also removed by it, that is, if its writer ranks first among the devices of
the principal that it leaves in place. Otherwise an honest device that ranks
before the writer and that the head leaves in place can displace it. Let three
devices of the owner's principal rank first, second and third. The first is lost
or stolen, and the third writes an epoch `R` that removes it. The second, honest
and not yet aware of `R`, has written a sibling `s` that lists the first. At a
verifier that accepted `R` first, `s` ranks before `R` and `R` does not remove
its writer, so `s` displaces `R`. The first device is then a member device with
authority of the new head. The first device's own sibling ranks before `s`, and
`s` does not remove it, so that sibling displaces `s` in turn; or the first
device writes a successor of `s`. A removal written by the device that ranks
first among those it leaves in place has no such sibling to meet: the devices it
removes cannot displace it, and the others rank after it. Obligations at the
product boundary, 7 (group-epochs-key-epochs.md), asks the product to write a removal that way. This draft
cannot see who wrote a removal, and it does not say what a product does when
that device is not available. Whether the rule should also refuse a sibling of
another owner device that still lists a device the head removed is open (group-epochs-decisions.md, Open
decision D-12), and this draft does not extend it.

The rule costs independence from the order of arrival, and from replays, in one
case. When a sibling written by a device of the owner's principal removes or
demotes another device of that principal that ranks before its writer, and that
other device has written a sibling too, the head depends on which of the two a
verifier received first. At a verifier that received the removal first, the
other device's sibling is `removed-by-head`. At one that received the other
device's sibling first, the removal ranks after it and is `outranked`. Two
verifiers that receive them in different orders end on different heads, and
nothing here brings them together. Mutual removal, in which each of two owner
devices removes or demotes the other, is always such a case: the sibling that
arrives second is refused, whichever it is. With three or more devices of the
principal there is more: a refusal depends on the head at the time, so after the
head has changed the same bytes offered again can displace the new head. A
replay of a sibling refused as `removed-by-head` can therefore change the head,
and two verifiers that received the same siblings in the same order can end on
different heads if only one of them also received a replay. No rule in this draft
avoids that split without choosing which of two owner devices to believe. The
rank alone believes the device that ranks first, a stolen one included; a rule
that let the removal displace the other device's sibling whatever its rank
would, with three or more owner devices, let a displaced epoch become the head
again. Apart from these cases the rule adds no dependence on the order of
arrival or on replays.

The cost falls unevenly. At a verifier that received a removal first, the
removed device's sibling is refused whatever its rank. So a compromised device
of the owner's principal, of any rank and not only the one that ranks first, can
keep the honest device that ranks first out of that verifier with one delivery:
an epoch that removes it, or a `transfer_ownership`, delivered before that
device's sibling. While that epoch is the head the honest device's siblings are
refused there, and once a successor of it is accepted they are `superseded`
(check 2). Under the rank alone the compromised device needed two deliveries,
its epoch and a successor of it, accepted before that sibling arrived. The theft
of a device of the owner's principal, whichever it is, is therefore a loss that
the rank does not contain, and a product treats it as needing recovery
(group-epochs-key-epochs.md, Obligations at the product boundary, 7; group-epochs-limits.md, Recovery, under What is not checked).

### Displacement

Let `H` be the head, at epoch number `n`, and `c` a sibling of it that passes
every check against `P` = `prior` and that the rule for owner devices does not
refuse (Owner devices, above).

- If `c` ranks before `H`, the result is `displaced`. In one durable step `head`
  becomes `c` with its signature, `index[n]` becomes `c`'s commitment, `prior`
  is unchanged, the key material bound to `H` is retired (group-epochs-key-epochs.md, Obligations on the
  key engine, 4 and 5), and the caller records the generations of `c`'s
  statements (group-epochs-successor.md, Accepting a successor, Inputs). `H` is no longer accepted state.
- Otherwise the result is `refused(outranked)`. Accepted state does not change,
  and the caller records the generations of `c`'s statements (Evidence of a
  sibling, below).

A candidate whose commitment is the head's is a `duplicate`, and a candidate for
a slot the chain has passed is `superseded` (check 2), whatever its rank. A
sibling is ranked only after it has passed every check, so a candidate that is
not authenticated, or whose evidence the caller refuses, cannot displace a
head. The head at one epoch number moves only to an epoch that ranks before it,
so a displaced epoch never becomes the head again, and the head a verifier ends
on is the sibling that ranks first among those it has received that pass every
check, whatever order they came in, as long as it accepts no successor of any of
them in between, except in the case that Owner devices describes, where the
order of arrival and a replay can decide.

A sibling whose writer the head removed, or demoted, is ranked like any other
unless the head's writer is another device of the owner's principal (Owner
devices, above). Under policy version 1 and Open decision D-9 (group-epochs-decisions.md, option B) only an
owner removes a device of an admin or demotes an admin, and the owner's devices
rank before every admin's, so such a sibling written by an admin is always
`outranked`. A device of the owner's principal that another of its devices
removed or demoted in the head is `removed-by-head`. The device that wrote a
removal or a transfer can still displace it with an epoch of its own that has a
lower commitment, so an owner can race its own transfer. And a device of the
owner's principal that the head does not remove or demote still displaces the
head if it ranks before the head's writer: a lost or stolen owner device that
ranks first displaces, until it has a successor, any epoch of the owner's
other devices that does not remove it, and its own sibling can remove those
devices (group-epochs-limits.md, Recovery, under What is not checked). And an honest device of the
owner's principal that ranks before the writer of an epoch that removes a lost
device, and that the epoch leaves in place, displaces that epoch in the same way
(Owner devices).

### Evidence of a sibling

A sibling is judged against `prior`, but the caller's freshness record already
holds what was recorded when the head was accepted. A sibling that admits a
device on the same statement as the head, or on an older one, would be refused
as `evidence-refused`, under a freshness rule that refuses such a generation, at
a verifier that accepted the head first, and accepted at one that did not; the
order of arrival would then choose the head. So the caller's freshness rule
judges a sibling's statements as it would if nothing had been recorded for a
candidate of the head's epoch number (group-epochs-successor.md, Accepting a successor, Inputs), and every
sibling of one slot is judged against the same record, whichever came first. A
sibling can therefore be accepted on a statement older than one that this
verifier has seen in another sibling of the same slot, as it would have been had
it arrived first. That includes a statement from before a revocation. Let the
head admit an account's new device on a statement of generation 5 that revokes
the account's old device, and a sibling that ranks first admit the old device on
the statement of generation 4 that still listed it. The caller's freshness rule
would refuse generation 4 after generation 5 for a successor, and it accepts it
for the sibling: the sibling displaces the head, and the revoked device becomes
a member device of the head and a recipient of its key material, at a verifier
that had recorded generation 5. That is a cost of making the head independent of
the order of arrival (apart from the case of Owner devices), and it is this
page's rule and not the caller's (group-epochs-limits.md, Inventory, under What is not checked). Its
limit: only the records made for the slot being decided are set aside. A
generation recorded for another slot of the group, for another group, or by
another use of the procedure still applies to the sibling.

The rule only sets those records aside. They stay recorded, since a stored value
never decreases (identities-and-devices.md, Accepting a signed statement), and
the record kept after the slot holds the generations of every sibling that
passed every check at that verifier, the `outranked` and `removed-by-head` ones
included, so it does not depend on the order in which they came among
themselves. Three limits follow. Two verifiers that received different sets of
siblings hold different records: a later candidate whose statement is older than
a generation that only one of them recorded can be accepted at one and refused
at the other, as other uses of the procedure can already cause (group-epochs-decisions.md, Open decision
D-6). And the displaced head's generations stay recorded, so a freshness rule
that refuses a generation equal to a recorded one refuses the displaced head's
admission when its proposer offers it again on the same statement; a rule that
accepts an equal generation does not. And a sibling that arrives after a
successor of the slot is `superseded` and records nothing, so the record depends
on which siblings arrived before that successor. A verifier that recorded a
losing sibling's generation refuses, under a freshness rule that refuses an
equal generation, a later candidate on a statement of the same generation that
another verifier, which received the losing sibling only after the successor,
accepts.

A sibling written by a device that the head removed is refused as
`removed-by-head`, and the caller records the generations of its statements all
the same. A removed owner device that holds a genuine statement can therefore
still change the caller's store in this one way: it raises the generation
recorded for an account at that slot, and a freshness rule that refuses an equal
generation then refuses a later admission of that account on the same statement,
at a later slot. The effect is bounded: it needs a statement that the account's
issuer made, and a stored value only rises.
