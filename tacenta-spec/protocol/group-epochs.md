# Group epochs

Signed, hash-chained group membership epochs: what an epoch is, the bytes it
is written as, and the checks a client applies before it accepts one.

Status: draft, awaiting review. It is proposed for review under ADR-0008, rule
7, and it is not ratified. Until a reviewed change replaces this line, nothing
on this page is a conformance target, no model or vector states it, and the
decisions under Open decisions are open: a mark "Adopted" there means a
recommended default that the maintainer said to go with, not a decision made
after review. Adopting a default does not ratify the text it shapes. The page
is a draft in the sense of README.md, "Normative status".

Review record. ADR-0008, rule 7 asks that a change to this specification be
reviewed against that record before it merges, by the maintainer or by a
reviewer the maintainer delegates to, that the review be written on the pull
request, and that the merge wait for green checks. It does not ask that a
person read the change. The main branch requires the CI status checks and
linear history and requires no pull-request review (ASSURANCE.md, row 7), and
no job in the CI workflow checks the rules of this page: the one tool that
opens it scans every tracked file for unresolved conflict markers. The
maintainer intends a person to read this page before it merges; the repository
does not enforce that. The review passes the page has been through so far were
working checks directed by the maintainer. They are not the rule-7 review,
which is pending, and their reports are not recorded on the pull request or in
this repository.

What this page does not give. It gives no secrecy of later key material from a
removed device, since how key material is derived is not specified. It chooses
between two competing epochs for one slot only while no successor of either has
been accepted, and not even then when a device of the owner's principal removes
or demotes another that ranks before it: the order of arrival decides that case
(group-epochs-siblings.md, Siblings). It gives no recovery from a fork deeper than that, no agreement
among members once a successor has been built on the losing epoch, and no signal
to a user that a group has split, only a hint that anyone can cause and that a
group that has not split also produces (group-epochs-siblings-forks.md, Siblings, Fork hint). Until a successor
of an accepted epoch is accepted, a competing epoch that ranks before it can
replace it, so a removal is final at a verifier only from then on. For the
owner's own devices the page protects a removal only against the devices that it
removes or demotes (group-epochs-siblings.md, Siblings, Owner devices). It gives no evidence that anyone
accepted an epoch before a checkpoint. It gives no anonymity. It has no model,
vector, code, proof or worked example, and its byte layout depends on decisions
that are open (group-epochs-decisions.md, Open decisions D-2, D-4 and D-7).

Dependency note, to be deleted at ratification: this page cites "Accepting a
signed statement", "Identity keys" and "Verifying a signature" in
identities-and-devices.md. "Accepting a signed statement" is on main (core pull
request #200, merged as commit 4dcb8cc). "Identity keys", and the rule in
"Verifying a signature" that the key a signature is checked under be an identity
key, came with core pull request #205 (merged as commit e06f8f4). Both are on
main. Both merged on a rule 7 comment written by the account that authored the
changes. Those comments record tool-assisted reads and say that no reviewer
independent of the maintainer has read the change; the comment on #200 adds that
the maintainer has not read its specification text end to end, and the comment
on #205 does not say whether a person read it (ASSURANCE.md, row 7). This page
relies on text that no independent reader has read. The drafter (the party that
prepared this page's text for the maintainer; README.md at the root of the
repository, Development assistance, and ADR-0008, Context, say how changes are
prepared) read this page against their merged text; that reading is not a
review. "Accepting a signed statement" has seven checks, in this order: account,
issuer binding, signature, freshness, device id, identity key, policy. Four
rules in these sections matter here. The identity-key check admits one spelling
of an identity key, which the byte comparison of Open decision D-10 (group-epochs-decisions.md) relies on.
"Identity keys" lists where a party applies that rule and says a decoder does
not apply it, which bears on Decoding (group-epochs-encoding.md) and on Signature (group-epochs-encoding.md). The freshness check must
have no effect of its own, and a generation is recorded as seen only after the
statement is accepted, in one atomic step that evaluates the rule again, which
bears on the inputs to "Accepting a successor" (group-epochs-successor.md). And a verifier must not refuse a
statement solely because a replacement's marker names no listed binding, which
bears on the non-claim about a replacement's chain of custody. This page cites
these sections by their names and by the names of their checks, never by their
numbers, so a change to the order there would need those four places read again.
The "Adopted" marks under Open decisions (group-epochs-decisions.md) are drafting records, and they go with
this note, as do the statements in the text that give a decision's adoption (in
Joining from a checkpoint, The checkpoint (group-epochs-genesis-and-joining.md), Aliasing and Inventory under What is
not checked (group-epochs-limits.md), and the introduction to Open decisions (group-epochs-decisions.md)), and so does the History
paragraph of Open decision D-12 (group-epochs-decisions.md), which describes revisions of this draft that
never merged.

## Parts

The draft is this entry page and the ten parts below, read in this order. The
entry page holds the status, the review record, Scope, Layers, Terms, Encoding
conventions, Constants and The accepted state. Elsewhere on the entry page,
"this page" means the whole draft; in a part, "this draft" means the whole draft
and "this page" means the part. "check N" means the successor checks of
group-epochs-successor.md unless a genesis or checkpoint check is named.

- [group-epochs-encoding.md](group-epochs-encoding.md): Canonical encoding,
  Operations and Policy version 1.
- [group-epochs-genesis-and-joining.md](group-epochs-genesis-and-joining.md):
  Genesis and Joining from a checkpoint.
- [group-epochs-successor.md](group-epochs-successor.md): Accepting a successor:
  Inputs, Results and The checks.
- [group-epochs-successor-effects.md](group-epochs-successor-effects.md): the
  rest of Accepting a successor: Effects and Policy verdict.
- [group-epochs-siblings.md](group-epochs-siblings.md): Siblings: Rank, Owner
  devices, Displacement and Evidence of a sibling.
- [group-epochs-siblings-forks.md](group-epochs-siblings-forks.md): the rest of
  Siblings: Equivocation, What the order does not resolve and Fork hint.
- [group-epochs-key-epochs.md](group-epochs-key-epochs.md): Key epochs, with
  Obligations on the key engine, and Obligations at the product boundary.
- [group-epochs-limits.md](group-epochs-limits.md): What is not checked, and
  what is not claimed.
- [group-epochs-removal.md](group-epochs-removal.md): The removal invariant (a
  target, not shown).
- [group-epochs-decisions.md](group-epochs-decisions.md): Open decisions,
  Related published work and Sources.

## Scope

This page specifies:

- what a group epoch is, and the state a client keeps once it has accepted one;
- the canonical encoding of an epoch, with its bounds and refusals;
- genesis, and the checks for a successor, in a fixed order, with the results
  they return and the effect of each on the accepted state;
- how a device that joins after genesis starts: a checkpoint that an
  authenticated invitation carries, the checks a joiner applies to it, and the
  trust it rests on (group-epochs-genesis-and-joining.md, Joining from a checkpoint);
- the operations an epoch carries, and how a batch of them takes effect;
- policy version 1, an owner, admin and member baseline;
- an optional policy verdict that a product supplies and that can only refuse
  (group-epochs-successor-effects.md, Policy verdict);
- how a verifier chooses between its head and a valid sibling of it, by a fixed
  order of their writers and one rule for two devices of the owner's principal,
  while the head has no accepted successor, what that order does not resolve,
  and a hint, with no effect, that a candidate may show a fork (group-epochs-siblings.md, Siblings);
- the key epoch of an epoch, and what a client must take from accepted state
  before it distributes or uses group key material (group-epochs-key-epochs.md, Key epochs; group-epochs-key-epochs.md, Obligations on
  the key engine);
- obligations at the product boundary: what a product, its coordinator and its
  stores do for the removal property, so that a race between siblings settles,
  and so that a failure part-way through a step cannot make a verifier refuse
  the same epoch for good (group-epochs-key-epochs.md, Obligations at the product boundary);
- one scoped property, the removal invariant, stated as a target and not shown,
  about recipient sets and retired key material and not about how key material
  is derived, with its adversary, its assumptions and its limits.

It does not specify a group cipher, a sender-key format, how key material is
derived or carried to a device (it states only which devices may be sent it:
Obligations on the key engine, 2 (group-epochs-key-epochs.md)), the ordering or storage service that carries
epochs, invitations (their form, and how they are authenticated), recovery from
a lost or compromised authority or from a fork deeper than one epoch, or a
product's roles and user interface. It assumes that each accepted epoch starts a
key epoch (group-epochs-decisions.md, Open decision D-2), and it does not choose between sender keys and
pairwise fan-out (group-messaging.md, Open questions). Where a rule below needs
one of these, it names the boundary and says what it takes from the far side.

EX-04 (threat-model/exclusions.md) records groups as unspecified, and it stands
until a reviewed change ratifies this page.

## Layers

Three parties take part in accepting an epoch, and this page fixes only the
first.

- **This page.** The bytes of an epoch, the checks a verifier applies and the
  state it keeps. Every check is a function of the verifier's accepted state,
  the candidate bytes, the evidence and the caller-supplied inputs named under
  "Genesis" (group-epochs-genesis-and-joining.md), "Joining from a checkpoint" (group-epochs-genesis-and-joining.md) and "Accepting a successor" (group-epochs-successor.md).
- **The key engine.** The group key material created for an epoch. It is not
  yet specified. This page states what it must take from accepted state and
  what it must refuse (group-epochs-key-epochs.md, Obligations on the key engine).
- **The product and its services.** Account resolution, invitations, user
  intent, durable effects and any service that orders or stores candidates. A
  product may narrow acceptance (group-epochs-successor-effects.md, Policy verdict); it never widens it. A
  position a service assigns to a candidate never authorises it. A service may
  refuse a second proposal for one predecessor, as a hint to proposers, and
  gains no authority by it (group-epochs-key-epochs.md, Obligations at the product boundary, 8). A
  product's own membership format is outside this page, and nothing here maps
  one to an epoch.

## Terms

- **Account.** An account handle as an inventory statement names it: non-empty
  UTF-8, at most `MAX_ACCOUNT_BYTES` (256) bytes (identities-and-devices.md,
  Hosted device-inventory statements), compared byte for byte. UTF-8 is as RFC
  3629 defines it (group-epochs-decisions.md, Sources), so a surrogate code point or an overlong form is
  not UTF-8. This page defines no normalisation, so two spellings are two
  accounts.
- **Principal.** An account an epoch lists, with one role.
- **Device binding.** `DeviceBinding` (identities-and-devices.md, Hosted
  device-inventory statements), compared as its whole canonical encoding. The
  page also uses "binding" for the key binding of an epoch (group-epochs-key-epochs.md, Key epochs) and for
  the caller's issuer-key binding (group-epochs-successor.md, Accepting a successor, Inputs), and says
  which where it matters.
- **Member.** The role with value 3 in policy version 1. The page says "member
  device" for a device that an epoch lists, and uses "members of the group" in
  ordinary prose for the participants of a group; neither is the role.
- **Member device.** A device binding an accepted epoch lists under a
  principal. Only member devices are recipients of an epoch's key material.
- **Epoch.** The unsigned body defined below and the writer's signature over it.
- **Candidate.** An epoch a verifier has received and not yet accepted, and that
  the caller offers as a candidate and not as a checkpoint.
- **Verifier.** A client that keeps accepted state for one group and applies
  the checks on this page.
- **Coordinator.** The part of a product that proposes epochs and distributes
  them, and the key material and traffic that go with them. This page does not
  specify it. Where it says a verifier's coordinator, it means the coordinator
  of the product that runs that verifier, and Obligations at the product
  boundary (group-epochs-key-epochs.md, 3, 6 and 8) say what it must and must not do.
- **Product, caller.** The product is the application that runs a verifier, with
  the services it uses (Layers); its coordinator is the part that proposes and
  distributes epochs. The caller is the code of the product that offers an epoch
  to a verifier and supplies the inputs named under Accepting a successor,
  Inputs (group-epochs-successor.md).
- **Head, prior.** The latest accepted epoch, and the accepted epoch before it.
  A verifier that started from a checkpoint has no prior until it accepts a
  successor of it. When a sibling displaces the head, the sibling becomes the
  head and `prior` stays as it was, since it is the predecessor of both
  (group-epochs-siblings.md, Siblings).
- **Successor.** A candidate whose `predecessor_commitment` is the commitment of
  the head, so that its epoch number is the head's plus 1 (group-epochs-successor.md, Accepting a
  successor, check 2).
- **Sibling.** A candidate that has the head's epoch number and the head's
  predecessor, and a commitment other than the head's. It is judged against
  `prior` and not against the head (group-epochs-successor.md, Accepting a successor, check 2), and, if it
  passes every check, it is ranked against the head, after the rule for owner
  devices (group-epochs-siblings.md, Siblings). Two epochs with the same predecessor and different
  commitments are also called siblings.
- **Slot.** One epoch number of a group. Siblings compete for one slot, and a
  verifier holds one epoch for each slot it has accepted.
- **Final.** An accepted epoch is final at a verifier once that verifier has
  accepted a successor of it: from then on no sibling displaces it there
  (group-epochs-siblings-forks.md, Siblings, What the order does not resolve). An epoch that has no accepted
  successor, a `close` included, is not final.
- **Checkpoint.** A signed epoch, with its commitment, that an authenticated
  invitation gives to a device that has no accepted state for the group. The
  device takes it as its first head (group-epochs-genesis-and-joining.md, Joining from a checkpoint). It may be the
  genesis epoch of the group or a later epoch. The caller says which way it
  offers an epoch, as a candidate or as a checkpoint (group-epochs-successor.md, Accepting a successor,
  Inputs).
- **Joiner, inviter.** The device that starts from a checkpoint, and the party
  whose authenticated invitation carried it.
- **Anchor.** The commitment that the caller supplies for a genesis epoch or a
  checkpoint. The epoch's own commitment must equal it (genesis check 3,
  checkpoint check 3). It does not come from a signature over the epoch (group-epochs-decisions.md, Open
  decision D-1).
- **Writer.** The device a candidate names as its signer, by `writer_account`
  and `writer_binding`. Successor check 4 reads it in the predecessor. The
  candidate need not list it.
- **Rank.** The order in which a verifier places two siblings: by the role and
  the position, in their shared predecessor, of the device that wrote each, and,
  only between two epochs that one device wrote, by commitment (group-epochs-siblings.md, Siblings, Rank).
  Between two devices of the owner's principal, a sibling whose writer the head
  removed or demoted is refused before the rank is read (group-epochs-siblings.md, Siblings, Owner
  devices).
- **Displaced.** The result for a sibling of the head that passes every check,
  ranks before the head and is not refused by the rule for owner devices
  (group-epochs-siblings.md, Siblings, Owner devices). The sibling becomes the head, and the epoch it
  replaces, a displaced epoch, is no longer accepted state (group-epochs-siblings.md, Siblings).
- **Equivocation.** Two different epochs that one writer device signed for the
  same predecessor (group-epochs-siblings-forks.md, Siblings, Equivocation).
- **Fork hint.** The value `possible-fork`, which a verifier returns beside some
  results for a candidate that may show a fork. It is not a result, changes
  nothing and is not authenticated (group-epochs-siblings-forks.md, Siblings, Fork hint).
- **Authority set.** The member devices of an epoch whose `update_authority` is
  1, each as a pair of its principal's account and its binding. A candidate's
  writer must be in the authority set of its predecessor: the head for a
  successor, `prior` for a sibling (successor check 4). An authority device is a
  member device whose `update_authority` is 1.
- **Evidence.** Signed inventory statements supplied to acceptance beside a
  candidate. Evidence is not part of the epoch and is not signed by its writer.
- **Key epoch.** The number `key_epoch` in an epoch's body. It names the
  generation of group key material that belongs to the epoch.
- **Check numbers.** The page has three ordered lists of checks: Genesis (group-epochs-genesis-and-joining.md, eight
  checks), Joining from a checkpoint (group-epochs-genesis-and-joining.md, seven) and Accepting a successor
  (group-epochs-successor.md, twelve). Outside its own list a check is cited with the list: "successor
  check 7", "genesis check 5", "checkpoint check 7". In Accepting a successor (group-epochs-successor.md),
  Siblings (group-epochs-siblings.md), Key epochs (group-epochs-key-epochs.md), Obligations at the product boundary (group-epochs-key-epochs.md), What is not
  checked (group-epochs-limits.md), the section on the removal invariant (group-epochs-removal.md) and Open decisions (group-epochs-decisions.md), a bare
  "check N" is a successor check.

## Encoding conventions

Integers are big-endian. A length or a count is a `u32`. A sequence written as
"sorted" is strictly ascending, so it has no duplicate, under the comparison
stated where it appears. An account handle is written as a `u32` length and
that many UTF-8 bytes. `DeviceBinding` is written exactly as
identities-and-devices.md writes it, including its optional replacement
predecessor.

## Constants

Every value is a choice made for this draft, for which this page cites no
source, and is listed as tier `ours` (CONSTANTS.md: free choices, authorised by
nobody but us). That tier assumes that no published document supplies the value,
and whether any does has not been checked. The page's other choices (the fields
and their order, the order of the checks, the roles and the operations) are
likewise its own and have no tier, because CONSTANTS.md tiers constants only.
These are draft values. They are not in CONSTANTS.md or tacenta-core/LABELS.md,
which register what the engine emits or accepts and what its code derives with,
until the page is ratified. tooling/check-labels.sh reads Rust sources only, so
no tool checks a label that exists only in this page.

| Name | Value | Meaning |
|---|---|---|
| `EPOCH_DOMAIN` | ASCII `Tacenta Group Epoch v1` (22 bytes) | First bytes of every epoch body. |
| `EPOCH_COMMITMENT_LABEL` | `Tacenta:group:epoch-commitment:v1\xff` | Prefix of the SHA-256 input for an epoch commitment. |
| `EPOCH_SIGNING_LABEL` | `Tacenta:group:epoch-signature:v1\xff` | Prefix of the XEdDSA input for a writer signature. |
| `INVENTORY_EVIDENCE_LABEL` | `Tacenta:group:inventory-evidence:v1\xff` | Prefix of the SHA-256 input for an inventory commitment. |
| `MAX_GROUP_PRINCIPALS` | 512 | Principals in one epoch. |
| `MAX_DEVICES_PER_PRINCIPAL` | 8 | Member devices under one principal; the inventory profile's `MAX_ACTIVE_BINDINGS`. |
| `MAX_GROUP_DEVICES` | 4096 | Member devices in one epoch: 512 principals at eight devices. The two bounds above imply it; it is named so that a decoder can size an allocation before it reads. |
| `MAX_EPOCH_OPERATIONS` | 4096 | Operations in one epoch (group-epochs-decisions.md, Open decision D-5). |

In a label, `\xff` is the single byte 255 (`0xFF`): the label is its ASCII text
followed by that byte.

The bounds are choices of this draft: groups of up to 512 principals with up to
eight devices each. No profile document in this repository states them, and
eight is the inventory profile's `MAX_ACTIVE_BINDINGS`. They are ceilings, not a
promise that a group of that size is supported. By these counts and the field
sizes no epoch is longer than 2,167,845 bytes: 619,557 for everything but the
operations (the 549 fixed bytes of the header, the writer and the signature, 512
principals with 256-byte accounts, and 4096 devices with 77-byte bindings), and
1,548,288 for 4096 operations of the longest kind. That is an upper bound and
not a typical size; Open decision D-7 (group-epochs-decisions.md) asks for a measurement. None of the three
labels is a prefix of `EPOCH_DOMAIN`, of another of the three, or of a row of
tacenta-core/LABELS.md (the two group commitment labels of group-messaging.md
are among those rows), and none of them has any of those strings as a prefix.
That was checked by comparing the strings, and no tool checks it. `EPOCH_DOMAIN`
is the first part of an epoch body and is never signed or hashed by itself, so
it has no terminator byte.

## The accepted state

A verifier that has accepted the genesis epoch of a group, or has started from
a checkpoint (group-epochs-genesis-and-joining.md, Joining from a checkpoint), keeps, for that group:

```text
head       the latest accepted epoch: its body, its signature and its commitment
prior      the accepted epoch before head; absent while head is genesis, and
           while head is the checkpoint the verifier started from
index      the epoch commitment of every accepted epoch, by epoch number; a
           verifier that started from a checkpoint holds the checkpoint's entry
           and later ones, and none below. A displaced epoch is not accepted
           state, and the entry for its number holds the commitment of the
           sibling that displaced it (group-epochs-siblings.md, Siblings)
```

The head carries these semantic components, each a field of the body:

| Component | Body field |
|---|---|
| Profile and format version | the `EPOCH_DOMAIN` prefix; `policy_version` |
| Group identifier | `group_id` |
| Epoch number and exact predecessor commitment | `epoch_number`, `predecessor_commitment` |
| Device bindings and their inventory evidence | each principal's devices: `binding`, `inventory_generation`, `inventory_commitment` |
| Update authority | each device's `update_authority`, and each principal's `role` |
| Product-policy version and commitment | `policy_version`, `policy_commitment` |
| Key-epoch record | `key_epoch` |
| Closure state and declared operations | `closure_state`, `operations` |
| Writer evidence | `writer_account`, `writer_binding`, and the signature over the body |

A candidate is not accepted state. A directory response or an inventory
statement is not an accepted binding: a member device exists only because an
accepted epoch lists it.

An entry of `index` that is not held is never equal to a commitment. An entry
is not held below the checkpoint a verifier started from, and above its head.
Every rule that compares a commitment with an `index` entry reads it that way.

Accepting an epoch is one durable step that replaces `head`, `prior` and the
`index` entry together and retires the previous head's key material (group-epochs-key-epochs.md, Obligations
on the key engine). Displacing the head is one durable step that replaces
`head` and the `index` entry for its number together, leaves `prior` as it was,
and retires the displaced head's key material (group-epochs-siblings.md, Siblings). Any other result
changes none of the three.

### Identity keys in accepted state

The identity-key rule (identities-and-devices.md, Identity keys) admits exactly
one spelling of an identity key. The decoder does not apply it (group-epochs-encoding.md, Decoding). The
verifier applies it itself to the key of every device that enters accepted
state, and each way a key can enter has one place where it does:

| How the key enters | Where the rule is applied | Who applies it |
|---|---|---|
| A new device, at genesis (genesis check 8) or in a successor (successor check 12) | Successor check 12, to the `identity_public_key` of each new device. The caller's inventory acceptance procedure applies the identity-key check of "Accepting a signed statement" to every key in the statement as well | The verifier; and the procedure, again |
| A device listed by a checkpoint | Checkpoint check 7, to every key the epoch lists | The verifier |
| The key of a checkpoint's writer that the checkpoint does not list | Verifying a signature, when checkpoint check 6 verifies the signature | The verifier |
| A device that a later epoch retains | Not applied again: the entry is kept byte for byte (successor check 8), so the key is one that passed | Nobody |

So every `identity_public_key` of a member device has passed the rule, and has
exactly one spelling, whether or not the caller's acceptance procedure applies
it. The verifier does not rely on the procedure for this. The cost is one test
of the kind that successor check 5 already runs on the writer's key, for each
new device.

So successor check 7 compares identity keys as bytes. Two member devices that
hold one key cannot be spelled differently, and the comparison needs no curve
arithmetic (group-epochs-decisions.md, Open decision D-10). A candidate that lists a respelling of a key
already in the group is refused at successor check 12, as
`invalid-identity-key`, and not at successor check 7, which sees two different
byte strings. What the byte comparison does not cover is stated under Aliasing
in What is not checked (group-epochs-limits.md).
