# Group epochs: genesis and joining from a checkpoint

Part of the draft group-epochs.md (the entry page). Status: draft, awaiting review; see group-epochs.md for the review record and what the draft is not.

This part holds Genesis and Joining from a checkpoint, with the genesis checks
and the checkpoint checks, and "check N" in it means a successor check of
group-epochs-successor.md unless a genesis or checkpoint check is named.

## Genesis

Genesis is the epoch with `epoch_number` 0 and `predecessor_tag` 0. It has no
predecessor and so no prior authority. Its legitimacy is a bootstrap anchor that
the caller fixes separately, and does not come from a signature over itself
(group-epochs-decisions.md, Open decision D-1). A verifier that holds no anchor for the group refuses every
genesis candidate that decodes and passes the position check as
`anchor-mismatch`. A genesis candidate is judged in this order, and the verifier
stops at the first check that does not pass and returns its result:

1. **Decode.** As Decoding above (group-epochs-encoding.md).
2. **Position.** If the verifier has a head: the candidate's `group_id` equals
   the head's, else `wrong-group`; the candidate is a `duplicate` if its
   commitment is `index[0]`, and is otherwise refused `superseded`.
3. **Anchor.** The candidate's commitment equals the anchor the caller
   supplies, else `anchor-mismatch`. [D-1 default: the anchor is the genesis
   commitment.]
4. **Profile.** `policy_version` is one the verifier supports, else
   `unsupported`. The anchor has already fixed the candidate, so this result
   cannot be caused by an unauthenticated one.
5. **Shape.** The conditions of successor check 7, in that order. Then, in
   addition, genesis lists exactly one principal, whose role is owner, else
   `invalid-roles` (group-epochs-decisions.md, Open decision D-8). With one principal, successor check 7
   already requires that its role be owner, so what this rule adds is the count
   of principals.
6. **Writer.** `writer_account` and `writer_binding` name a device listed in
   the candidate itself whose `update_authority` is 1, else
   `writer-not-authorised`. This is the only check that uses a candidate's own
   authority set to authorise it, and only because the anchor has already fixed
   the candidate.
7. **Signature.** As Signature above (group-epochs-encoding.md), else `bad-signature`.
8. **Evidence.** Every member device is treated as newly admitted (successor
   check 12).

On acceptance `head` is the candidate, `prior` is absent and `index[0]` is its
commitment.

A device that joins after genesis has no genesis to accept. It starts from a
checkpoint, which may be the genesis epoch itself (Joining from a checkpoint).

## Joining from a checkpoint

Acceptance of an epoch, as "Accepting a successor" (group-epochs-successor.md) defines it, is against an
accepted predecessor, and a device that joins a group after genesis has none. It
starts from a checkpoint instead: an epoch of the group, carried by an
authenticated invitation, that it takes as its first head. This is Open decision
D-11, option C (group-epochs-decisions.md), the recommended default, adopted on the maintainer's general
instruction of 2026-09-30; its review is pending. **It is
a trust assumption, and it is stated under Trust assumption below.** The whole
section is new text, written for that default, and is awaiting review.

A checkpoint starts a verifier that has no accepted state for the group. A
verifier that has state does not replace it with a checkpoint (checkpoint check
2 below). A device that means to resume from a checkpoint discards its state for
the group and starts as a new verifier. When a product should do that is the
product's (group-epochs-key-epochs.md, Obligations at the product boundary, 5).

### The checkpoint

A checkpoint has two parts:

```text
checkpoint_commitment    32 bytes: the epoch_commitment of the epoch it names
checkpoint_epoch         a signed epoch (group-epochs-encoding.md, Canonical encoding): the body, then the
                         64-byte signature; predecessor_tag is 0 for the genesis
                         epoch of the group and 1 for any later epoch
```

- **The commitment is the anchor.** The caller pins `checkpoint_commitment` as
  it pins a genesis commitment (Genesis; group-epochs-decisions.md, Open decision D-1). It takes the value
  from an authenticated invitation and from nothing else.
- **The epoch is the state.** Under Open decision D-7 (group-epochs-decisions.md, option A, for the draft)
  an epoch's body carries the full resulting principals and devices, each device
  with its binding, `update_authority`, `inventory_generation` and
  `inventory_commitment`, and it carries `group_id`, `epoch_number`,
  `key_epoch`, `closure_state`, `policy_version` and `policy_commitment`. These
  are the fields that the checks of "Accepting a successor" (group-epochs-successor.md) read from the head
  (group-epochs.md, The accepted state). Those checks read `prior`, and `index` below the head,
  only to judge a sibling or an older epoch, and a joiner has nothing to judge
  one against. So a checkpoint needs no more than the epoch and its commitment.
  If Open decision D-7 (group-epochs-decisions.md) goes to option B, the checkpoint carries the snapshot
  that option describes, and the checks below change with it.
- **Where the epoch comes from.** The invitation may carry the epoch, or the
  epoch may reach the joiner some other way. Checkpoint check 3 below binds its
  body to the commitment either way. The commitment does not cover the signature
  (group-epochs-encoding.md, Commitment), so checkpoint check 6 checks the signature on its own: a carrier
  that alters the signature causes a `bad-signature` refusal and nothing else.
- **Its bound.** The epoch is bounded as any epoch is (group-epochs-encoding.md, Decoding), and the
  commitment adds 32 bytes. This section sets no bound of its own. How large an
  epoch is in practice is what Open decision D-7 (group-epochs-decisions.md) asks to be measured.

### Trust assumption

**Trust assumption (group-epochs-decisions.md, Open decision D-11, option C).** A joiner trusts its inviter
for the checkpoint. It relies on the inviter's word that the epoch the
commitment names is an epoch of the group it means to join, that the members of
the group accepted it, and that it is the group's head or close to it. Nothing
in this draft lets the joiner check any of that (What a joiner cannot verify). It
takes the checkpoint's members, roles, devices, policy and closure state as the
group's, and every epoch it accepts afterwards is a successor of that state. If
the inviter is mistaken or hostile, the joiner holds a state that the group may
never have had, and cannot tell it from a real one: an inviter can write an
epoch that lists whatever members it likes, itself as owner among them, sign it
under a key it made, and give its commitment as the anchor. The checks below
accept it.

A joiner already relies on its inviter, whose identity key it takes to be the
inviter's (ASM-14; EX-09), for which group it is joining and who is in it, since
it has no other way to learn either. The checkpoint extends that reliance from
who the group is to what the group's state was at one epoch. It is a wider
reliance than genesis needs. A verifier that starts from genesis trusts its
anchor for one epoch that lists the owner and no one else (group-epochs-decisions.md, Open decision D-8),
and checks every later epoch against the one before it. A verifier that starts
from a checkpoint trusts its anchor for the whole state of the group at that
epoch, and checks only the epochs after it. A joiner whose checkpoint is the
genesis epoch relies on its inviter for that one epoch only, as a verifier that
starts from genesis does, and differs from it in holding no evidence for the
creator's devices.

The invitation is the product's (group-epochs.md, Scope). This draft requires of a caller that
starts a verifier from a checkpoint only that the value it pins came from an
invitation it has authenticated as made by the inviter it means to trust and as
unmodified, and from nothing else (group-epochs-key-epochs.md, Obligations at the product boundary, 5). It
does not say who may invite, that the inviter is a member of the group, or that
anyone else accepted the inviter's state.

### Checks for a checkpoint

The decision is a deterministic function of the verifier's accepted state, the
checkpoint's epoch bytes, the anchor, the policy versions the verifier supports,
and the signature and identity-key rules. The caller offers the epoch as a
checkpoint, with its anchor, and not as a candidate; the offering mode is an
input (group-epochs-successor.md, Accepting a successor, Inputs). An epoch with `predecessor_tag` 1 that is
offered as a candidate to a verifier with no head is `missing-predecessor`
(group-epochs-successor.md, Accepting a successor, check 2).

The epoch may be the genesis epoch of the group (`predecessor_tag` 0, epoch
number 0). A joiner holds no inventory statement, and the last check of Genesis
needs one for every device, so a genesis epoch that is offered as a checkpoint
is judged by the checks below and not under Genesis. The checks add for it the
two rules of Genesis that need no evidence, one in checkpoint check 5 and one in
checkpoint check 6. A verifier that accepts it holds the state that a verifier
holds after it accepted the same epoch under Genesis: `head` the epoch, `prior`
absent and `index[0]` its commitment. The difference is that the creator's
devices carry evidence that the joiner never saw (What a joiner cannot verify).
A genesis epoch offered as a candidate, and not as a checkpoint, is judged under
Genesis. The checks run in this order, and the verifier stops at the first that
does not pass and returns its result:

1. **Decode.** As Decoding above (group-epochs-encoding.md): `malformed`, `wrong-version` or
   `non-canonical`.
2. **Position.** If the verifier has a head: the epoch's `group_id` equals the
   head's, else `wrong-group`; the epoch is a `duplicate` if its commitment is
   `index[m]`, for `m` its epoch number, where that entry is held (an entry that
   is not held is never equal to a commitment: The accepted state (group-epochs.md)), and is
   otherwise `refused(already-started)`. A verifier that holds accepted state
   does not replace it with a checkpoint.
3. **Anchor.** The epoch's commitment equals the anchor the caller supplies,
   else `anchor-mismatch`. A verifier that is given no anchor refuses every
   checkpoint that decodes and passes the position check as `anchor-mismatch`.
4. **Profile.** `policy_version` is one the verifier supports, else
   `unsupported`. The anchor has already fixed the epoch, so an unauthenticated
   candidate cannot cause this result.
5. **Shape.** The conditions of successor check 7, on the epoch's own
   principals, in that order: `invalid-roles`, `authority-mismatch` or
   `duplicate-device`. For a genesis epoch, then Genesis's further rule too:
   exactly one principal, whose role is owner, else `invalid-roles`. For any
   other epoch that rule does not apply.
6. **Signature.** For a genesis epoch, first the rule of genesis check 6:
   `writer_account` and `writer_binding` name a device that the epoch itself
   lists with `update_authority` 1, else `writer-not-authorised`. Then, for
   every epoch, as Signature above (group-epochs-encoding.md), else `bad-signature`. This shows that the
   key `writer_binding` names signed the body. It does not show that the writer
   was authorised, because the joiner holds no predecessor to read authority
   from. For an epoch that is not a genesis epoch the writer need not be listed
   in the checkpoint: a device may sign the epoch that removes it.
7. **Keys.** The `identity_public_key` of every member device the epoch lists,
   in encoding order, passes the identity-key rule (identities-and-devices.md,
   Identity keys), else `refused(invalid-identity-key)`. A joiner holds no
   inventory statement for these devices, so the verifier applies the rule
   itself here, and this is the only place it is applied to them (group-epochs.md, The accepted
   state, Identity keys in accepted state). The writer's key, when the
   checkpoint does not list the writer, is held to the same rule by checkpoint
   check 6.

On acceptance the verifier makes one durable step: `head` is the epoch with its
signature and commitment, `prior` is absent, `index` holds the commitment at the
epoch's number and nothing below it. A refusal changes nothing. The step creates
no key material and retires none.

The checkpoint need not list the joiner's device, and no check asks that it
does. A device can start from the epoch before the one that admits it and become
a member device by accepting that successor, which is judged like any other. A
device receives key material only as a permitted recipient, and a device is one
only if the head lists it (group-epochs-key-epochs.md, Obligations on the key engine, 2).

`already-started` and `invalid-identity-key` are refusal kinds that this page
names for a checkpoint, and genesis check 8 and check 12 of "Accepting a
successor" (group-epochs-successor.md) use the second as well. CONSTANTS.md has no rows for refusal kinds,
and error-handling.md leaves the names of error variants to an implementation,
so the draft's refusal kinds are in neither.

### After the checkpoint

Successors are judged under "Accepting a successor" (group-epochs-successor.md), as for any head, and its
check 2 says what the entries a joiner does not hold mean. Two things follow.
The first successor is judged against the checkpoint as `P`, so the devices the
checkpoint lists are retained ones unless that successor removes them: they need
no evidence, and a retained one keeps its entry byte for byte (successor check
8). And a joiner judges no sibling of its checkpoint (successor check 2). If a
sibling that ranks before the checkpoint displaces it at the other verifiers of
the group, the joiner cannot judge that sibling, and every later epoch of the
group is `missing-predecessor` at the joiner, which stays at its checkpoint
(group-epochs-siblings.md, Siblings). Beside `missing-predecessor` for that sibling the joiner returns the
hint `possible-fork`, which shows only that a candidate names the checkpoint's
predecessor (group-epochs-siblings-forks.md, Siblings, Fork hint). An inviter avoids that case by giving as a
checkpoint only an epoch that already has an accepted successor at its own
verifier (group-epochs-key-epochs.md, Obligations at the product boundary, 10). A checkpoint whose
`closure_state` is 1 is accepted like any other and has no successor (successor
check 3). Once the joiner accepts the first successor, `prior` is the checkpoint
and the verifier is like any other.

### What a joiner cannot verify

From a checkpoint a joiner cannot verify, and this draft does not claim, any of
the following. It takes each from the inviter.

- That the group exists apart from the inviter's word, or that the epoch the
  commitment names belongs to the group the joiner means to join. `group_id` is
  a field of the body, and nothing binds it to a genesis. An inviter can name
  any `group_id`, including one the joiner already holds for another group, and
  a joiner that holds state for it refuses the checkpoint (checkpoint check 2).
- That the checkpoint's writer was authorised by the epoch before it, that its
  operations produce its principals from that epoch, that its key epoch follows
  that epoch's or is below 2^64 - 1, or that policy version 1 allowed what it
  did (group-epochs-successor.md, Accepting a successor, checks 4, 8, 9 and 10). The joiner holds no
  predecessor. It checks only that the key the named writer holds signed the
  body. No check reads the operations that a checkpoint carries: it can carry
  operations that contradict its principals or its closure state, and the
  verifier holds it as given. The one rule that reads the operations of a head,
  at the end of the successor list (group-epochs-siblings.md, Siblings, Owner devices), judges a sibling
  of the head, and the verifier judges no sibling of a checkpoint (group-epochs-successor.md, Accepting a
  successor, check 2), so it never reads them.
- That any epoch before the checkpoint was written, signed or accepted by
  anyone, or that a device the group removed earlier is absent from the
  checkpoint.
- That any device the checkpoint lists was admitted with evidence. The joiner
  holds no inventory statement for them, so their `inventory_generation` and
  `inventory_commitment` are values it stores and cannot check (group-epochs-successor.md, Accepting a
  successor, check 12).
- That the checkpoint is the group's head, or a recent one. A stale checkpoint
  looks like the head: it can list a device that a later epoch removed, or an
  owner that a later epoch replaced, and the joiner learns of a later epoch only
  when it receives one (group-epochs-limits.md, Freshness, under What is not checked).
- That the group has one chain, or that the checkpoint will stay the group's
  epoch for its number. The joiner cannot tell whether another branch leaves
  the checkpoint or an earlier epoch, it judges no sibling of the checkpoint
  (group-epochs-successor.md, Accepting a successor, check 2), and it cannot tell whether the inviter gave
  every joiner the same checkpoint. A checkpoint that has no accepted successor
  can still be displaced at the other verifiers by a sibling that ranks before
  it, and the joiner then cannot follow the group (After the checkpoint; group-epochs-key-epochs.md,
  Obligations at the product boundary, 10).
- That the invitation is fresh, single-use or meant for this joiner. This draft
  asks of the caller only that the pinned commitment came from an invitation
  authenticated as made by the inviter and as unmodified (group-epochs-key-epochs.md, Obligations at the
  product boundary, 5). A genuine old invitation, replayed, gives a joiner a
  genuine but stale head, and the rules of this draft then treat the devices that
  head lists as permitted recipients, including a device that a later epoch
  removed. Withheld later epochs have the same effect after a legitimate join,
  and a replay lets its sender choose how far back. An inviter can also give a
  checkpoint whose epoch number is 2^64 - 1, which has no successor (group-epochs-successor.md, The
  checks).
- That the signature authenticates anything about the group. At a checkpoint
  that is not a genesis epoch, the signature check shows only that the key
  `writer_binding` names signed the body, and the writer need not be listed in
  the checkpoint. Anyone who can make the epoch can sign it under a key of their
  own, and an inviter can then give its commitment as the anchor. With the
  commitment pinned, the check adds only that the stored signature belongs to
  the stored body.
- That the chain can be verified from genesis in place of trusting the inviter
  (group-epochs-decisions.md, Open decision D-11, option A). The evidence for an admission is not part of
  the signed record (group-epochs-limits.md, Evidence carriage), so verifying every epoch from genesis
  would need every inventory statement ever used, and the draft does not say that
  anyone keeps them. Option A is therefore not a way out of trusting the inviter
  on this draft's terms.
- That a listed key belongs to the person a member means (ASM-14; EX-09). It
  checks only that each key is an identity key.

It does check that the epoch is a well-formed epoch that its anchor names, that
its policy version is supported, that its roles, authority flags and device keys
are consistent with each other, that the key its `writer_binding` names signed
it, and that every listed device key is an identity key (checkpoint checks 5, 6
and 7 above). None of this makes the checkpoint a verified one.

A checkpoint is not recovery. It starts a new verifier on the inviter's word. It
does not choose between the branches of a fork, and a device that leaves one
branch by discarding its state and joining from a checkpoint of the other has
trusted that checkpoint's inviter for the whole state of the group. A product
that wants evidence about the chain before a checkpoint has to obtain and verify
the chain from genesis itself. This draft does not specify that.
