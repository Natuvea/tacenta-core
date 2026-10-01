# Group epochs

Signed, hash-chained group membership epochs: what an epoch is, the bytes it
is written as, and the checks a client applies before it accepts one.

Status: draft. It has had no human review. The reviews it has had were run by
automated reviewers working for the maintainer, and they are not independent of
the maintainer. It is proposed for review under ADR-0008, rule 7, and it is not
ratified. Until a reviewed change replaces this line, nothing on this page is a
conformance target, no model or vector states it, and the decisions under Open
decisions are open: a mark "Adopted" there means a recommended default that the
maintainer said to go with, not a choice that anyone has reviewed. Adopting a
default does not ratify the text it shapes. The page has the standing of a
scaffold (README.md, "Normative status"), with more text.

Review record. ADR-0008, rule 7 requires that a change to this specification be
reviewed against that record before it merges, by the maintainer or by a
reviewer the maintainer delegates to, that the review be written on the pull
request, and that the merge wait for green checks. It does not require that a
person read the change. The main branch requires the CI status checks and
linear history and requires no pull-request review (ASSURANCE.md, row 7), and
no job in the CI workflow checks the rules of this page: the one tool that
opens it scans every tracked file for unresolved conflict markers. So nothing
in the repository requires or enforces a reading of this page by a person. The
reports of the reviews mentioned above are not recorded on the pull request or
in this repository.

What this page does not give. It gives no secrecy of later key material from a
removed device, since how key material is derived is not specified. It gives no
recovery: a verifier that sees a valid sibling of its head stops accepting for
good, and the page offers no way out, no choice between branches, and no signal
to a user that either has happened. It gives no agreement among members who
receive epochs in different orders, and no evidence that anyone accepted an
epoch before a checkpoint. It gives no anonymity. It has no model, vector, code,
proof or worked example, and its byte layout depends on decisions that are open
(Open decisions D-2, D-4 and D-7).

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
prepared this page's text for the maintainer; README.md, Development assistance,
and ADR-0008, Context, say how changes are prepared) read this page against
their merged text; that reading is not a review. "Accepting a signed statement"
has seven checks, in this order: account, issuer binding, signature, freshness,
device id, identity key, policy. Four rules in these sections matter here. The
identity-key check admits one spelling of an identity key, which the byte
comparison of Open decision D-10 relies on. "Identity keys" lists where a party
applies that rule and says a decoder does not apply it, which bears on Decoding
and on Signature. The freshness check must have no effect of its own, and a
generation is recorded as seen only after the statement is accepted, in one
atomic step that evaluates the rule again, which bears on the inputs to
"Accepting a successor". And a verifier must not refuse a statement solely
because a replacement's marker names no listed binding, which bears on the
non-claim about a replacement's chain of custody. This page cites these sections
by their names and by the names of their checks, never by their numbers, so a
change to the order there would need those four places read again. The "Adopted"
marks under Open decisions are drafting records, and they go with this note, as
do the statements in the text that give a decision's adoption (in Joining from a
checkpoint, The checkpoint, Aliasing and Inventory under What is not checked,
and the introduction to Open decisions).

## Scope

This page specifies:

- what a group epoch is, and the state a client keeps once it has accepted one;
- the canonical encoding of an epoch, with its bounds and refusals;
- genesis, and the checks for a successor, in a fixed order, with the results
  they return and the effect of each on the accepted state;
- how a device that joins after genesis starts: a checkpoint that an
  authenticated invitation carries, the checks a joiner applies to it, and the
  trust it rests on (Joining from a checkpoint);
- the operations an epoch carries, and how a batch of them takes effect;
- policy version 1, an owner, admin and member baseline;
- an optional policy verdict that a product supplies and that can only refuse
  (Policy verdict);
- the marker that a verifier sets when it sees a valid sibling of its head, and
  that nothing on the page clears (Conflict);
- the key epoch of an epoch, and what a client must take from accepted state
  before it distributes or uses group key material (Key epochs; Obligations on
  the key engine);
- one scoped property, the removal invariant, stated as a target and not shown,
  about recipient sets and retired key material and not about how key material
  is derived, with its adversary, its assumptions and its limits.

It does not specify a group cipher, a sender-key format, how key material is
derived or carried to a device (it states only which devices may be sent it:
Obligations on the key engine, 2), the ordering or storage service that carries
epochs, invitations (their form, and how they are authenticated), recovery from
a lost or compromised authority, from a frozen verifier or from a fork, or a
product's roles and user interface. It assumes that each accepted epoch starts a
key epoch (Open decision D-2), and it does not choose between sender keys and
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
  "Genesis", "Joining from a checkpoint" and "Accepting a successor".
- **The key engine.** The group key material created for an epoch. It is not
  yet specified. This page states what it must take from accepted state and
  what it must refuse (Obligations on the key engine).
- **The product and its services.** Account resolution, invitations, user
  intent, durable effects and any service that orders or stores candidates. A
  product may narrow acceptance (Policy verdict); it never widens it. A
  position a service assigns to a candidate never authorises it. A product's
  own membership format is outside this page, and nothing here maps one to an
  epoch.

## Terms

- **Account.** An account handle as an inventory statement names it: non-empty
  UTF-8, at most `MAX_ACCOUNT_BYTES` (256) bytes (identities-and-devices.md,
  Hosted device-inventory statements), compared byte for byte. UTF-8 is as RFC
  3629 defines it (Sources), so a surrogate code point or an overlong form is
  not UTF-8. This page defines no normalisation, so two spellings are two
  accounts.
- **Principal.** An account an epoch lists, with one role.
- **Device binding.** `DeviceBinding` (identities-and-devices.md, Hosted
  device-inventory statements), compared as its whole canonical encoding. The
  page also uses "binding" for the key binding of an epoch (Key epochs) and for
  the caller's issuer-key binding (Accepting a successor, Inputs), and says
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
  boundary (3) says what it must not do.
- **Product, caller.** The product is the application that runs a verifier, with
  the services it uses (Layers); its coordinator is the part that proposes and
  distributes epochs. The caller is the code of the product that offers an epoch
  to a verifier and supplies the inputs named under Accepting a successor,
  Inputs.
- **Head, prior.** The latest accepted epoch, and the accepted epoch before it.
  A verifier that started from a checkpoint has no prior until it accepts a
  successor of it.
- **Successor.** A candidate whose `predecessor_commitment` is the commitment of
  the head, so that its epoch number is the head's plus 1 (Accepting a
  successor, check 2).
- **Sibling.** A candidate that has the head's epoch number and the head's
  predecessor, and a commitment other than the head's. It is judged against
  `prior` and not against the head (Accepting a successor, check 2).
- **Checkpoint.** A signed epoch, with its commitment, that an authenticated
  invitation gives to a device that has no accepted state for the group. The
  device takes it as its first head (Joining from a checkpoint). It may be the
  genesis epoch of the group or a later epoch. The caller says which way it
  offers an epoch, as a candidate or as a checkpoint (Accepting a successor,
  Inputs).
- **Joiner, inviter.** The device that starts from a checkpoint, and the party
  whose authenticated invitation carried it.
- **Anchor.** The commitment that the caller supplies for a genesis epoch or a
  checkpoint. The epoch's own commitment must equal it (genesis check 3,
  checkpoint check 3). It does not come from a signature over the epoch (Open
  decision D-1).
- **Writer.** The device a candidate names as its signer, by `writer_account`
  and `writer_binding`. Successor check 5 reads it in the predecessor. The
  candidate need not list it.
- **Marker.** The state `conflict`, which a verifier sets when it sees a valid
  sibling of its head. While it is set the verifier accepts nothing (Conflict).
  A verifier whose marker is set is a frozen verifier. The page also calls the
  result that sets the marker `conflict`, and the field of accepted state.
- **Authority set.** The member devices of an epoch whose `update_authority` is
  1, each as a pair of its principal's account and its binding. A successor's
  writer must be in the predecessor's authority set and, for a sibling of the
  head, in the head's as well. An authority device is a member device whose
  `update_authority` is 1.
- **Evidence.** Signed inventory statements supplied to acceptance beside a
  candidate. Evidence is not part of the epoch and is not signed by its writer.
- **Key epoch.** The number `key_epoch` in an epoch's body. It names the
  generation of group key material that belongs to the epoch.
- **Check numbers.** The page has three ordered lists of checks: Genesis (eight
  checks), Joining from a checkpoint (seven) and Accepting a successor
  (thirteen). Outside its own list a check is cited with the list: "successor
  check 8", "genesis check 5", "checkpoint check 7". In Accepting a successor,
  Conflict, Key epochs, What is not checked, the section on the removal
  invariant and Open decisions, a bare "check N" is a successor check.

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
| `MAX_EPOCH_OPERATIONS` | 4096 | Operations in one epoch (Open decision D-5). |

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
not a typical size; Open decision D-7 asks for a measurement. None of the three
labels is a prefix of `EPOCH_DOMAIN`, of another of the three, or of a row of
tacenta-core/LABELS.md (the two group commitment labels of group-messaging.md
are among those rows), and none of them has any of those strings as a prefix.
That was checked by comparing the strings, and no tool checks it. `EPOCH_DOMAIN`
is the first part of an epoch body and is never signed or hashed by itself, so
it has no terminator byte.

## The accepted state

A verifier that has accepted the genesis epoch of a group, or has started from
a checkpoint (Joining from a checkpoint), keeps, for that group:

```text
head       the latest accepted epoch: its body, its signature and its commitment
prior      the accepted epoch before head; absent while head is genesis, and
           while head is the checkpoint the verifier started from
index      the epoch commitment of every accepted epoch, by epoch number; a
           verifier that started from a checkpoint holds the checkpoint's entry
           and later ones, and none below
conflict   absent, or set: a valid candidate conflicted with head (Conflict).
           It carries no content. A `conflict` result sets it, and nothing on
           this page clears it
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
`index` entry together and retires the previous head's key material (Obligations
on the key engine). It happens only while `conflict` is absent (successor check
3). A refusal changes none of the four.

### Identity keys in accepted state

The identity-key rule (identities-and-devices.md, Identity keys) admits exactly
one spelling of an identity key. The decoder does not apply it (Decoding). The
verifier applies it itself to the key of every device that enters accepted
state, and each way a key can enter has one place where it does:

| How the key enters | Where the rule is applied | Who applies it |
|---|---|---|
| A new device, at genesis (genesis check 8) or in a successor (successor check 13) | Successor check 13, to the `identity_public_key` of each new device. The caller's inventory acceptance procedure applies the identity-key check of "Accepting a signed statement" to every key in the statement as well | The verifier; and the procedure, again |
| A device listed by a checkpoint | Checkpoint check 7, to every key the epoch lists | The verifier |
| The key of a checkpoint's writer that the checkpoint does not list | Verifying a signature, when checkpoint check 6 verifies the signature | The verifier |
| A device that a later epoch retains | Not applied again: the entry is kept byte for byte (successor check 9), so the key is one that passed | Nobody |

So every `identity_public_key` of a member device has passed the rule, and has
exactly one spelling, whether or not the caller's acceptance procedure applies
it. The verifier does not rely on the procedure for this. The cost is one test
of the kind that successor check 6 already runs on the writer's key, for each
new device.

So successor check 8 compares identity keys as bytes. Two member devices that
hold one key cannot be spelled differently, and the comparison needs no curve
arithmetic (Open decision D-10). A candidate that lists a respelling of a key
already in the group is refused at successor check 13, as
`invalid-identity-key`, and not at successor check 8, which sees two different
byte strings. What the byte comparison does not cover is stated under Aliasing
in What is not checked.

## Canonical encoding

### The body

The unsigned body is the concatenation of:

```text
EPOCH_DOMAIN                  22 bytes
group_id                      32 bytes
epoch_number                  u64
predecessor_tag               1 byte: 0 or 1
predecessor_commitment        32 bytes, present when predecessor_tag is 1
key_epoch                     u64
policy_version                u32
policy_commitment             32 bytes
closure_state                 1 byte: 0 open, 1 closed
principal_count               u32
principals                    principal_count x Principal
operation_count               u32
operations                    operation_count x Operation
writer_account                u32 length, UTF-8 bytes
writer_binding                DeviceBinding
```

`Principal` is:

```text
account                       u32 length, UTF-8 bytes
role                          1 byte: 1 owner, 2 admin, 3 member
device_count                  u32
devices                       device_count x GroupDevice
```

`GroupDevice` is:

```text
binding                       DeviceBinding
update_authority              1 byte: 0 or 1
inventory_generation          u64
inventory_commitment          32 bytes
```

`Operation` is a kind byte and a body that depends on the kind:

| Kind | Name | Body |
|---|---|---|
| 1 | `admit_device` | account, then `DeviceBinding`, `inventory_generation` (u64) and `inventory_commitment` (32 bytes): a `GroupDevice` without its `update_authority`, which `apply` derives |
| 2 | `remove_device` | account, then `DeviceBinding` |
| 3 | `set_role` | account, then `role`: 2 or 3 |
| 4 | `transfer_ownership` | new owner's account, then the former owner's new `role`: 2 or 3 |
| 5 | `set_policy` | `policy_version` (u32), then `policy_commitment` (32 bytes) |
| 6 | `close` | empty |

A signed epoch is the body followed by a 64-byte signature (Signature).

`policy_commitment` is an opaque 32-byte value. The verifier binds it, changes
it only by `set_policy`, and does not interpret it (Open decision D-4). The
body carries the full resulting principals and devices, as well as the
operations that produced them (Open decision D-7).

### Order

- `principals` are sorted by the byte-wise lexicographic order of the account's
  UTF-8 bytes, not of its length-prefixed encoding.
- A principal's `devices` are sorted by the lexicographic order of the complete
  encoding of `binding`.
- `operations` are sorted by the lexicographic order of the complete encoding
  of each operation, so its kind byte orders first.

In the first order a proper prefix sorts before the longer string: an account
`a` sorts before an account `ab`.

The first order compares account bytes and the third compares whole encodings,
in which the kind byte and then the `u32` length of the account come first, so
they differ. With accounts `b` and `aa`, the principals sort `aa` before `b`,
and two `admit_device` operations sort the one for `b` before the one for `aa`,
because a length of 1 precedes a length of 2. An implementation that reuses one
comparator for both produces `non-canonical` on a valid epoch.

### Decoding

A decoder consumes exactly the bytes of a signed epoch, rebuilds the value,
re-encodes the body, and refuses if the bytes differ; every such case is one of
the refusals below. It refuses before it allocates more than these bounds imply,
and it reports the first refusal in this order:

1. the length test;
2. the domain test;
3. the fields, in the order of the layout above: the first field that is out of
   range, truncated or invalid;
4. the bytes after the body;
5. the form of the body;
6. `non-canonical`, which is judged only once the whole body has been read
   (principals first, then each principal's devices in principal order, then
   operations).

The refusals are:

- input of fewer than 22 bytes, or whose bytes after the last body field are
  not exactly 64: `malformed`;
- input of at least 22 bytes whose first 22 bytes are not `EPOCH_DOMAIN`:
  `wrong-version`;
- a count, length, tag, role, flag or kind byte outside its range, trailing
  bytes, truncation inside a field, or an account handle that is empty, longer
  than 256 bytes, or not UTF-8: `malformed`. Ranges are: `predecessor_tag` 0 or
  1; `closure_state` 0 or 1; `update_authority` 0 or 1; `role` 1 to 3 in a
  principal and 2 or 3 in `set_role` and `transfer_ownership`; operation kind 1
  to 6; `principal_count` 1 to `MAX_GROUP_PRINCIPALS`; `device_count` 1 to
  `MAX_DEVICES_PER_PRINCIPAL`; total member devices at most
  `MAX_GROUP_DEVICES`; `operation_count` at most `MAX_EPOCH_OPERATIONS`;
- a `DeviceBinding` that the inventory profile would refuse, or whose
  capability word is not exactly `GROUP_EPOCH_V1` (1): `malformed`;
- a body whose form is inconsistent: `predecessor_tag` 0 with a non-zero
  `epoch_number`, `key_epoch`, `closure_state` or `operation_count`, or
  `predecessor_tag` 1 with `epoch_number` 0: `malformed`;
- a sequence that is not sorted, or a duplicate entry, in `principals`, a
  principal's `devices` or `operations`: `non-canonical`.

The first bullet gives the condition on the bytes after the body together with
the length test, while the order above places the bytes after the body at step
4, after the domain test. For an input of at least 22 bytes with another domain
and a tail that is not 64 bytes, the first bullet gives `malformed` and the
order gives `wrong-version`. The page does not say which; this point is open.

Two conditions in the list restate others: the limit on the total number of
member devices is implied by the two counts before it, and the capability word
is already required by the inventory profile (identities-and-devices.md,
DeviceBinding).

A body has a single canonical encoding. Two candidates with equal bodies have
equal commitments whatever their signatures are.

The decoder reads the 32 bytes of an `identity_public_key` and does not apply
the identity-key rule to them (identities-and-devices.md, Identity keys). A
key that the rule refuses does not make an epoch malformed. Where the rule is
applied to the keys of an epoch is stated under The accepted state.

### Commitment

`epoch_commitment(body)` is the 32-byte SHA-256 digest of:

```text
EPOCH_COMMITMENT_LABEL || body
```

It covers the body and not the signature. XEdDSA signing draws fresh random
bytes (identities-and-devices.md, Signing), so one body can be signed twice
with different bytes. A commitment over the signed bytes would make an honest
re-signing look like a second proposal.

`predecessor_commitment` in a successor is the `epoch_commitment` of its
predecessor's body. Together with `group_id` and `epoch_number`, which are in
the body, this chains every epoch to genesis.

### Signature

The writer signs with the identity key of `writer_binding`. The input is:

```text
EPOCH_SIGNING_LABEL || body
```

and the signature is XEdDSA as identities-and-devices.md, Signing, defines it. A
verifier checks it as Verifying a signature defines, under
`writer_binding.identity_public_key`. That procedure requires the key to be an
identity key (identities-and-devices.md, Identity keys), so a signature under a
writer key that is not one does not verify, and the result is `bad-signature`.
Verifying a signature answers only yes or no, so this page reports the writer's
key as `bad-signature` and keeps `invalid-identity-key` for the keys of listed
devices (error-handling.md, An invalid identity key is a third outcome). The
label is what keeps this signature from being accepted as an application
signature, a prekey signature or an inventory-statement signature made by the
same key.

### Inventory commitment

`inventory_commitment` in a `GroupDevice` is the 32-byte SHA-256 digest of:

```text
INVENTORY_EVIDENCE_LABEL || unsigned_preimage
```

where `unsigned_preimage` is the canonical unsigned inventory statement of
identities-and-devices.md that admitted the device. It covers the unsigned
preimage because the issuer's signature is randomised in the same way.

## Operations

An epoch's operations take effect together. Each operation's preconditions and
authorisation are evaluated against the predecessor, never against the result
of another operation in the list. A candidate is one batch: it passes every
check below and is accepted as one epoch, or it has no effect.

A batch whose result would exceed a bound of Decoding (more than eight devices
under a principal, more than 4096 devices or 512 principals in all) or that
lists more than `MAX_EPOCH_OPERATIONS` operations has no candidate that both
decodes and equals `apply`. The candidate that tells the truth does not decode,
and a candidate that leaves a device out is refused as `projection-mismatch`
(successor check 9). No further refusal kind exists for it.

Let `P` be the predecessor and `ops` the operation list of a candidate.
`apply(P, ops)` is the following, in this order:

1. for each `admit_device(a, d)`, in list order: if `a` is a principal of `P`
   or of an earlier `admit_device` in the list, add `d` to that principal's
   devices; otherwise add a principal `a` with role 3 and the one device `d`;
2. for each `remove_device(a, b)`: remove `b` from `a`'s devices;
3. for each `set_role(a, r)`: set `a`'s role to `r`;
4. for `transfer_ownership(n, f)`: set the role of `P`'s owner to `f` and the
   role of `n` to 1;
5. remove every principal left with no devices;
6. set every device's `update_authority` to 1 when its principal's role is 1 or
   2, and to 0 otherwise;
7. take `policy_version` and `policy_commitment` from `set_policy` if the list
   has one, and from `P` otherwise; take `closure_state` 1 if the list has
   `close`, and `P`'s otherwise.

Every difference between a candidate and its predecessor in the principals, the
closure state and the policy fields is therefore named by an operation. A
candidate that lists a device its predecessor did not, or omits one, without the
matching operation, does not equal `apply(P, ops)` and is refused (successor
check 9). The one byte of a retained device's entry that can change without an
operation naming the device is its `update_authority`, and only when its
principal's role changes (step 6). The epoch number, the key epoch, the
predecessor commitment and the writer are not operations; successor checks 2, 5
and 10 govern them.

A device removed and admitted again in the same batch is not a refresh. The
batch is refused (successor check 9), whether the device is admitted under the
same binding or under another binding with the same identity key (Open decision
D-13). To bring a removed binding back, a later epoch admits it as an ordinary
admission, with evidence the caller's freshness rule accepts, and it receives no
key material of any earlier key epoch.

A principal leaves the group when a batch removes every one of its devices and
admits none for it. Leaving the group, or asking to be removed, is not an
operation: it has no effect until an authorised writer commits the removal.

## Policy version 1

Policy version 1 is an owner, admin and member baseline. It is content of this
page, not a product's private rule, because the baseline for accepting a
candidate must not depend on which product evaluates it (Open decision D-3). A
product may add constraints of its own through the policy verdict, which can
only refuse; it cannot remove these.

The roles are 1 owner, 2 admin and 3 member. They are exclusive, and every
principal has exactly one. Exactly one principal is the owner. A device has
`update_authority` 1 exactly when its principal is an owner or an admin. This
is the authority mapping of version 1.

The rules use roles in `P` only. A role, an authority flag or an operation in
the candidate never authorises the candidate itself. The rules of `P`'s
`policy_version` govern successor check 11. Only version 1 exists on this page,
and a candidate changes the version in force only by `set_policy`, which an
owner writes. A lesser role therefore cannot reach `unsupported`: its
`set_policy` is `writer-role-insufficient`, and a header that changes the
version without one is a `projection-mismatch`. A former owner that the head has
demoted to admin is a lesser role in the head but an owner in the head's
predecessor. For a sibling of the head, whose `P` is that predecessor, it can
therefore still cause `unsupported`, with no change of state and no marker. A
sibling is not a successor of the head, so this does not stop a coordinator
(Obligations at the product boundary, 3).

| Operation | Who may write it | Restriction, read in `P` |
|---|---|---|
| `admit_device(a, d)` | an owner; an admin, when `a`'s role in `P` is member (3) or `a` is not a principal of `P` (Open decision D-9) | `a` enters as a member if new; its evidence is checked (successor check 13) |
| `remove_device(a, b)` | an owner; an admin, when `a`'s role in `P` is member (3) (Open decision D-9) | `b` is a member device of `a` in `P` |
| `set_role(a, r)` | an owner | `a` is a principal of `P` other than the owner; `r` is 2 or 3 |
| `transfer_ownership(n, f)` | an owner | `n` is a principal of `P` other than the owner; `f` is 2 or 3 |
| `set_policy(v, c)` | an owner | `v` and `c` are the candidate's `policy_version` and `policy_commitment` (successor check 9). A `v` the verifier does not support gives `unsupported` (successor check 7) |
| `close` | an owner | the only operation in the list |

Further rules:

- The principal that is owner in the result is `P`'s owner unless the list has
  `transfer_ownership`. The owner cannot be removed or demoted except by a
  transfer, which the owner writes.
- A transfer may remove every device of the former owner in the same batch. The
  former owner then leaves the group as the transfer takes effect.
- A closed epoch has no successor, and no operation reopens a group.
- An admin cannot promote itself, appoint or demote an admin, transfer
  ownership, change the policy or close the group. Adding such an operation to
  a candidate the admin signs makes no difference, because the rule reads
  roles in `P`.
- The result has at least one member device under every principal, at least one
  under the owner, and one owner. Each of these follows from `apply` and from
  successor check 8.

## Genesis

Genesis is the epoch with `epoch_number` 0 and `predecessor_tag` 0. It has no
predecessor and so no prior authority. Its legitimacy is a bootstrap anchor that
the caller fixes separately, and does not come from a signature over itself
(Open decision D-1). A verifier that holds no anchor for the group refuses every
genesis candidate that decodes and passes the position check as
`anchor-mismatch`. A genesis candidate is judged in this order, and the verifier
stops at the first check that does not pass and returns its result:

1. **Decode.** As Decoding above.
2. **Position.** If the verifier has a head: the candidate's `group_id` equals
   the head's, else `wrong-group`; the candidate is a `duplicate` if its
   commitment is `index[0]`, and is otherwise refused `superseded`.
3. **Anchor.** The candidate's commitment equals the anchor the caller
   supplies, else `anchor-mismatch`. [D-1 default: the anchor is the genesis
   commitment.]
4. **Profile.** `policy_version` is one the verifier supports, else
   `unsupported`. The anchor has already fixed the candidate, so this result
   cannot be caused by an unauthenticated one.
5. **Shape.** The checks of "Accepting a successor", check 8, in that order.
   Then, in addition, genesis lists exactly one principal, whose role is owner,
   else `invalid-roles` (Open decision D-8). With one principal, successor check
   8 already requires that its role be owner, so what this rule adds is the
   count of principals.
6. **Writer.** `writer_account` and `writer_binding` name a device listed in
   the candidate itself whose `update_authority` is 1, else
   `writer-not-authorised`. This is the only check that uses a candidate's own
   authority set to authorise it, and only because the anchor has already fixed
   the candidate.
7. **Signature.** As Signature above, else `bad-signature`.
8. **Evidence.** Every member device is treated as newly admitted (successor
   check 13).

On acceptance `head` is the candidate, `prior` is absent and `index[0]` is its
commitment.

A device that joins after genesis has no genesis to accept. It starts from a
checkpoint, which may be the genesis epoch itself (Joining from a checkpoint).

## Joining from a checkpoint

Acceptance of an epoch, as "Accepting a successor" defines it, is against an
accepted predecessor, and a device that joins a group after genesis has none. It
starts from a checkpoint instead: an epoch of the group, carried by an
authenticated invitation, that it takes as its first head. This is Open decision
D-11, option C, the recommended default, adopted on the maintainer's general
instruction of 2026-09-30; the maintainer has not otherwise reviewed it. **It is
a trust assumption, and it is stated under Trust assumption below.** The whole
section is new text, written for that default, and has had no human review.

A checkpoint starts a verifier that has no accepted state for the group. A
verifier that has state does not replace it with a checkpoint (checkpoint check
2 below). A device that means to resume from a checkpoint discards its state for
the group and starts as a new verifier. When a product should do that is the
product's (Obligations at the product boundary, 5).

### The checkpoint

A checkpoint has two parts:

```text
checkpoint_commitment    32 bytes: the epoch_commitment of the epoch it names
checkpoint_epoch         a signed epoch (Canonical encoding): the body, then the
                         64-byte signature; predecessor_tag is 0 for the genesis
                         epoch of the group and 1 for any later epoch
```

- **The commitment is the anchor.** The caller pins `checkpoint_commitment` as it
  pins a genesis commitment (Genesis; Open decision D-1). It takes the value from
  an authenticated invitation and from nothing else.
- **The epoch is the state.** Under Open decision D-7 (option A, for the draft)
  an epoch's body carries the full resulting principals and devices, each device
  with its binding, `update_authority`, `inventory_generation` and
  `inventory_commitment`, and it carries `group_id`, `epoch_number`, `key_epoch`,
  `closure_state`, `policy_version` and `policy_commitment`. These are the fields
  that the checks of "Accepting a successor" read from the head (The accepted
  state). Those checks read `prior`, and `index` below the head, only to judge a
  sibling or an older epoch, and a joiner has nothing to judge one against. So a
  checkpoint needs no more than the epoch and its commitment. If Open decision
  D-7 goes to option B, the checkpoint carries the snapshot that option
  describes, and the checks below change with it.
- **Where the epoch comes from.** The invitation may carry the epoch, or the
  epoch may reach the joiner some other way. Checkpoint check 3 below binds its
  body to the commitment either way. The commitment does not cover the signature
  (Commitment), so checkpoint check 6 checks the signature on its own: a carrier
  that alters the signature causes a `bad-signature` refusal and nothing else.
- **Its bound.** The epoch is bounded as any epoch is (Decoding), and the
  commitment adds 32 bytes. This section sets no bound of its own. How large an
  epoch is in practice is what Open decision D-7 asks to be measured.

### Trust assumption

**Trust assumption (Open decision D-11, option C).** A joiner trusts its inviter
for the checkpoint. It relies on the inviter's word that the epoch the commitment
names is an epoch of the group it means to join, that the members of the group
accepted it, and that it is the group's head or close to it. Nothing on this page
lets the joiner check any of that (What a joiner cannot verify). It takes the
checkpoint's members, roles, devices, policy and closure state as the group's,
and every epoch it accepts afterwards is a successor of that state. If the
inviter is mistaken or hostile, the joiner holds a state that the group may never
have had, and cannot tell it from a real one: an inviter can write an epoch that
lists whatever members it likes, itself as owner among them, sign it under a key
it made, and give its commitment as the anchor. The checks below accept it.

A joiner already relies on its inviter, whose identity key it takes to be the
inviter's (ASM-14; EX-09), for which group it is joining and who is in it, since
it has no other way to learn either. The checkpoint extends that reliance from
who the group is to what the group's state was at one epoch. It is a wider
reliance than genesis needs. A verifier that starts from
genesis trusts its anchor for one epoch that lists the owner and no one else
(Open decision D-8), and checks every later epoch against the one before it. A
verifier that starts from a checkpoint trusts its anchor for the whole state of
the group at that epoch, and checks only the epochs after it. A joiner whose
checkpoint is the genesis epoch relies on its inviter for that one epoch only,
as a verifier that starts from genesis does, and differs from it in holding no
evidence for the creator's devices.

The invitation is the product's (Scope). This page requires of a caller that
starts a verifier from a checkpoint only that the value it pins came from an
invitation it has authenticated as made by the inviter it means to trust and as
unmodified, and from nothing else (Obligations at the product boundary, 5). It
does not say who may invite, that the inviter is a member of the group, or that
anyone else accepted the inviter's state.

### Checks for a checkpoint

The decision is a deterministic function of the verifier's accepted state, the
checkpoint's epoch bytes, the anchor, the policy versions the verifier supports,
and the signature and identity-key rules. The caller offers the epoch as a
checkpoint, with its anchor, and not as a candidate; the offering mode is an
input (Accepting a successor, Inputs). An epoch with `predecessor_tag` 1 that is
offered as a candidate to a verifier with no head is `missing-predecessor`
(Accepting a successor, check 2).

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

1. **Decode.** As Decoding above: `malformed`, `wrong-version` or
   `non-canonical`.
2. **Position.** If the verifier has a head: the epoch's `group_id` equals the
   head's, else `wrong-group`; the epoch is a `duplicate` if its commitment is
   `index[m]`, for `m` its epoch number, where that entry is held (an entry that
   is not held is never equal to a commitment: The accepted state), and is
   otherwise `refused(already-started)`. A verifier that holds accepted state
   does not replace it with a checkpoint.
3. **Anchor.** The epoch's commitment equals the anchor the caller supplies,
   else `anchor-mismatch`. A verifier that is given no anchor refuses every
   checkpoint that decodes and passes the position check as `anchor-mismatch`.
4. **Profile.** `policy_version` is one the verifier supports, else
   `unsupported`. The anchor has already fixed the epoch, so an unauthenticated
   candidate cannot cause this result.
5. **Shape.** The checks of "Accepting a successor", check 8, on the epoch's own
   principals, in that order: `invalid-roles`, `authority-mismatch` or
   `duplicate-device`. For a genesis epoch, then Genesis's further rule too:
   exactly one principal, whose role is owner, else `invalid-roles`. For any
   other epoch that rule does not apply.
6. **Signature.** For a genesis epoch, first the rule of Genesis, check 6:
   `writer_account` and `writer_binding` name a device that the epoch itself
   lists with `update_authority` 1, else `writer-not-authorised`. Then, for every
   epoch, as Signature above, else `bad-signature`. This shows that the key
   `writer_binding` names signed the body. It does not show that the writer was
   authorised, because the joiner holds no predecessor to read authority from.
   For an epoch that is not a genesis epoch the writer need not be listed in the
   checkpoint: a device may sign the epoch that removes it.
7. **Keys.** The `identity_public_key` of every member device the epoch lists,
   in encoding order, passes the identity-key rule (identities-and-devices.md,
   Identity keys), else `refused(invalid-identity-key)`. A joiner holds no
   inventory statement for these devices, so the verifier applies the rule
   itself here, and this is the only place it is applied to them (The accepted
   state, Identity keys in accepted state). The writer's key, when the
   checkpoint does not list the writer, is held to the same rule by checkpoint
   check 6.

On acceptance the verifier makes one durable step: `head` is the epoch with its
signature and commitment, `prior` is absent, `index` holds the commitment at the
epoch's number and nothing below it, and `conflict` is absent. A refusal changes
nothing. The step creates no key material and retires none.

The checkpoint need not list the joiner's device, and no check asks that it does.
A device can start from the epoch before the one that admits it and become a
member device by accepting that successor, which is judged like any other. A
device receives key material only as a permitted recipient, and a device is one
only if the head lists it (Obligations on the key engine, 2).

`already-started` and `invalid-identity-key` are new refusal kinds, and check 13
of "Accepting a successor" uses the second as well. CONSTANTS.md has no rows for
refusal kinds, and error-handling.md leaves the names of error variants to an
implementation, so the page's refusal kinds are in neither.

### After the checkpoint

Successors are judged under "Accepting a successor", as for any head, and its
check 2 says what the entries a joiner does not hold mean. Two things follow.
The first successor is judged against the checkpoint as `P`, so the devices the
checkpoint lists are retained ones unless that successor removes them: they need
no evidence, and a retained one keeps its entry byte for byte (successor check
9). And a joiner judges no sibling of its checkpoint, so it can neither see a
`conflict` at that slot nor be frozen by one. A checkpoint whose `closure_state`
is 1 is accepted like any other and has no successor (successor check 4). Once
the joiner accepts the first successor, `prior` is the checkpoint and the
verifier is like any other.

### What a joiner cannot verify

From a checkpoint a joiner cannot verify, and this page does not claim, any of
the following. It takes each from the inviter.

- That the group exists apart from the inviter's word, or that the epoch the
  commitment names belongs to the group the joiner means to join. `group_id` is
  a field of the body, and nothing binds it to a genesis. An inviter can name
  any `group_id`, including one the joiner already holds for another group, and
  a joiner that holds state for it refuses the checkpoint (checkpoint check 2).
- That the checkpoint's writer was authorised by the epoch before it, that its
  operations produce its principals from that epoch, that its key epoch follows
  that epoch's or is below 2^64 - 1, or that policy version 1 allowed what it
  did (Accepting a successor, checks 5, 9, 10 and 11). The joiner holds no
  predecessor. It checks only that the key the named writer holds signed the
  body. The operations that the head carries are stored with it and no check
  reads them: a checkpoint can carry operations that contradict its principals
  or its closure state, and the verifier holds it as given.
- That any epoch before the checkpoint was written, signed or accepted by anyone,
  or that a device the group removed earlier is absent from the checkpoint.
- That any device the checkpoint lists was admitted with evidence. The joiner
  holds no inventory statement for them, so their `inventory_generation` and
  `inventory_commitment` are values it stores and cannot check (Accepting a
  successor, check 13).
- That the checkpoint is the group's head, or a recent one. A stale checkpoint
  looks like the head: it can list a device that a later epoch removed, or an
  owner that a later epoch replaced, and the joiner learns of a later epoch only
  when it receives one (Freshness, under What is not checked).
- That the group has one chain. The joiner cannot tell whether another branch
  leaves the checkpoint or an earlier epoch, it judges no sibling of the
  checkpoint (Accepting a successor, check 2), and it cannot tell whether the
  inviter gave every joiner the same checkpoint.
- That the invitation is fresh, single-use or meant for this joiner. This page
  asks of the caller only that the pinned commitment came from an invitation
  authenticated as made by the inviter and as unmodified (Obligations at the
  product boundary, 5). A genuine old invitation, replayed, gives a joiner a
  genuine but stale head, and the rules of this page then treat the devices that
  head lists as permitted recipients, including a device that a later epoch
  removed. Withheld later epochs have the same effect after a legitimate join,
  and a replay lets its sender choose how far back. An inviter can also give a
  checkpoint whose epoch number is 2^64 - 1, which has no successor (The
  checks).
- That the signature authenticates anything about the group. At a checkpoint
  that is not a genesis epoch, the signature check shows only that the key
  `writer_binding` names signed the body, and the writer need not be listed in
  the checkpoint. Anyone who can make the epoch can sign it under a key of their
  own, and an inviter can then give its commitment as the anchor. With the
  commitment pinned, the check adds only that the stored signature belongs to
  the stored body.
- That the chain can be verified from genesis in place of trusting the inviter
  (Open decision D-11, option A). The evidence for an admission is not part of
  the signed record (Evidence carriage), so verifying every epoch from genesis
  would need every inventory statement ever used, and the page does not say that
  anyone keeps them. Option A is therefore not a way out of trusting the inviter
  on this page's terms.
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
the chain from genesis itself. This page does not specify that.

## Accepting a successor

### Inputs

A verifier decides on a candidate from these inputs, and from nothing else:

- its accepted state (`head`, `prior`, `index`, `conflict`);
- the candidate's bytes;
- the offering mode: whether the caller offers an epoch as a candidate or as a
  checkpoint (Joining from a checkpoint). It decides which list of checks judges
  the epoch. An epoch whose `predecessor_tag` is 0, offered as a candidate, is
  judged under Genesis and needs evidence for every device; offered as a
  checkpoint, it is judged by the checks of Joining from a checkpoint, which
  need none. An epoch whose `predecessor_tag` is 1, offered as a candidate, is
  judged by the checks of this section, and by a verifier with no head it is
  `missing-predecessor`; offered as a checkpoint, it is judged by the checks of
  Joining from a checkpoint. The mode also changes the kind that a verifier with
  a head gives to an epoch of its own group that it has not accepted: offered as
  a checkpoint it is `already-started`, and offered as a candidate it is judged
  by its position (a genesis epoch is `superseded`);
- the policy versions it supports (check 7). The signature rule and the
  identity-key rule (Signature; Identity keys) are fixed by
  identities-and-devices.md and are not inputs;
- the evidence: a set of signed inventory statements;
- the inventory acceptance procedure, supplied by the caller: for a signed
  statement and an account, it applies "Accepting a signed statement"
  (identities-and-devices.md), including the caller's issuer-key binding, its
  freshness rule and its binding and statement policies, and whether the
  candidate is being evaluated live or replayed from history (Open decision
  D-6). The procedure has no effect of its own on the caller's records, as that
  section requires of its freshness check: a candidate can still be refused on a
  later principal's evidence, so the caller records the generation of each
  statement as seen only when the candidate is `accepted`. That record is the
  atomic step the section describes, which evaluates the caller's freshness rule
  again against the value then stored. If it now refuses a statement of the
  candidate, the candidate is `refused(evidence-refused)` and no generation of
  it is recorded. The re-evaluation of every statement, the recording of every
  generation and the durable step of Effects are one atomic step: if any
  statement is refused, none is recorded and nothing else changes;
- optionally, a policy verdict (below).

The decision is a function of these inputs, with the caller's inventory
acceptance procedure taken as it stands when the check runs. The store that the
procedure reads is not part of the verifier's accepted state: other uses of the
same procedure can write it, so two verifiers with the same accepted state and
the same bytes can differ (Open decision D-6). Whether a candidate is evaluated
live or replayed is an input too. This page does not say who sets it, or that a
coordinator may not, and whoever sets it chooses whether the freshness rule can
refuse a stale statement. This page reads no clock (ASM-11), no directory, and
no position or timestamp a service attached to the candidate. A caller's
freshness rule is an input, and may itself read one. For genesis and for a
checkpoint the anchor the caller supplies is an input as well.

### Results

| Result | Meaning | Effect on accepted state |
|---|---|---|
| `accepted` | The candidate is the new head. | `head` and `prior` are replaced, and `index` gains the candidate's entry, together. |
| `duplicate` | The candidate is, by commitment, an epoch already accepted. The signature bytes are not examined. | None. |
| `conflict` | The candidate is a valid successor of the head's predecessor, signed by a writer the head still authorises, and is not the head. | None, except that `conflict` is set (Conflict). |
| `missing-predecessor` | The candidate's predecessor is not an accepted epoch here: a gap, or another branch. | None. The verifier must obtain the predecessor before it can decide, except for a sibling of a checkpoint head, which it does not wait to judge (check 2). Anyone can produce this result from any bytes, so it is not by itself evidence of a gap (Obligations at the product boundary, 3). |
| `unsupported` | The candidate, signed by an owner of its predecessor, sets a policy version this verifier does not implement. | None. It is not evidence that the candidate is invalid: the verifier has judged only checks 1 to 6 and the conditions of check 7. It cannot decide until it supports the version. Its coordinator does not propose or distribute while this is the only successor of the head that it has seen, and that ends when the verifier supports the version, which judges the candidate afresh, or when it accepts another successor of its head. Only an owner of the predecessor can cause it (check 7), so neither an unauthenticated candidate nor a lesser role can. For a genesis epoch or a checkpoint it is returned after the anchor (Genesis, Joining from a checkpoint, check 4). |
| `refused(kind)` | The candidate fails a check. | None. |

A kind named without `refused(...)` (`malformed`, `wrong-group`,
`anchor-mismatch`, `bad-signature` and the others in Decoding, Genesis, Joining
from a checkpoint and The checks) is the kind of a `refused` result.
`duplicate`, `conflict`, `missing-predecessor` and `unsupported` are results of
their own.

The table lists every result and every refusal kind that this page names, the
checks that produce it, and what its condition reads at most: the candidate's
bytes (bytes), also the verifier's accepted state (state), or also an input of
the caller (input). The names are the spellings this draft uses. Whether a
conforming implementation must report them is not decided here (The checks).

| Name | Produced by | Reads |
|---|---|---|
| `accepted` | the end of each of the three lists, when every check passed | every check of the list |
| `duplicate` | successor check 2; genesis check 2; checkpoint check 2 | state |
| `conflict` | the end of the successor list, when `P` is `prior` | state |
| `missing-predecessor` | successor check 2 | state |
| `unsupported` | successor check 7; genesis check 4; checkpoint check 4 | input (the supported versions) |
| `malformed` | check 1 of each of the three lists (Decoding) | bytes |
| `wrong-version` | check 1 of each of the three lists (Decoding) | bytes |
| `non-canonical` | check 1 of each of the three lists (Decoding) | bytes |
| `wrong-group` | successor check 2; genesis check 2; checkpoint check 2 | state |
| `superseded` | successor check 2; genesis check 2 | state |
| `already-started` | checkpoint check 2 | state |
| `anchor-mismatch` | genesis check 3; checkpoint check 3 | input (the anchor) |
| `invalid-roles` | successor check 8; genesis check 5; checkpoint check 5 | bytes |
| `authority-mismatch` | successor check 8; genesis check 5; checkpoint check 5 | bytes |
| `duplicate-device` | successor check 8; genesis check 5; checkpoint check 5 | bytes |
| `writer-not-authorised` | successor check 5; genesis check 6; checkpoint check 6, for a genesis epoch | state at successor check 5, bytes at the others |
| `bad-signature` | successor check 6; genesis check 7; checkpoint check 6 | bytes |
| `invalid-identity-key` | successor check 13; genesis check 8; checkpoint check 7 | bytes |
| `blocked-by-conflict` | successor check 3 | state |
| `group-closed` | successor check 4 | state |
| `conflicting-operations` | successor check 9 | bytes |
| `unknown-target` | successor check 9 | state |
| `already-member` | successor check 9 | state |
| `projection-mismatch` | successor check 9 | state |
| `key-epoch` | successor check 10 | state |
| `writer-role-insufficient` | successor check 11 | state |
| `target-protected` | successor check 11 | state |
| `verdict-mismatch` | successor check 12 | input (the verdict) |
| `verdict-denied` | successor check 12 | input (the verdict) |
| `evidence-missing` | successor check 13; genesis check 8 | input (the evidence) |
| `evidence-mismatch` | successor check 13; genesis check 8 | input (the evidence) |
| `evidence-refused` | successor check 13; genesis check 8; the recording step under Inputs | input (the acceptance procedure and the store it reads) |

That is five results and 27 refusal kinds. Where several kinds can apply, the
order of the checks decides which is reported. At successor check 13,
`invalid-identity-key` reads bytes, but it is reached only after the evidence
conditions for the same principal have passed, so the evidence decides whether
it is reported.

A refusal is terminal for the same state and the same inputs: the same bytes are
refused the same way. A result or a kind marked state can change when the
verifier accepts, or learns of, another epoch, so the order in which epochs
reach a verifier can change it. A result or kind marked input can change when
the caller's input changes: `anchor-mismatch`, `unsupported`, and the refusals
of successor checks 12 and 13 (`verdict-mismatch`, `verdict-denied`,
`evidence-missing`, `evidence-mismatch`, `invalid-identity-key` and
`evidence-refused`).

### The checks

A candidate whose `predecessor_tag` is 0 is a genesis candidate and is judged
under Genesis above from its second check on. (An epoch with `predecessor_tag` 0
that the caller offers as a checkpoint is not a candidate; Joining from a
checkpoint judges it.) For any other candidate the checks run in the order
below. The verifier stops at the first that fails and returns its result. In
this draft the order is fixed: it decides which result is returned and which
state effect goes with it, and, among refusals, which kind is reported. Whether
a conforming implementation must report the same refusal kind where several
apply is not decided here: error-handling.md leaves the choice of reported
refusal to an implementation unless a page fixes an order because it is
observable in a way that matters. The order places every result that has an
effect after the checks that an unauthenticated candidate fails: a candidate
that is not canonical, or has not passed checks 5 and 6, cannot set `conflict`
and cannot cause `unsupported`, and check 7 lets only an owner of `P` cause
`unsupported`.

Arithmetic in the checks is over unbounded integers, so an epoch numbered
2^64 - 1, or with a `key_epoch` of 2^64 - 1, has no successor. Within a check
the conditions are tried in the order listed, and where a condition ranges over
principals, devices or operations it is tried over them in encoding order
(principals, then each principal's devices, then operations); the first that
fails decides. Where a check names a loop (check 11: each operation; check 13:
each principal), that loop is the outer one: all its conditions are tried for
one item before the next item. Elsewhere each condition is tried over all its
items before the next condition.

1. **Decode.** As Decoding above: `malformed`, `wrong-version` or
   `non-canonical`.
2. **Group and position.** With no head, `missing-predecessor`. Otherwise let
   `n` be the head's epoch number and `m` the candidate's. The candidate's
   `group_id` equals the head's, else `wrong-group`. Then:
   - `m` = `n` + 1: if `predecessor_commitment` is `index[n]`, the predecessor
     is the head; otherwise `missing-predecessor`;
   - `m` = `n`: if `predecessor_commitment` is `index[n - 1]`, the candidate is
     a `duplicate` when its commitment is `index[n]`, and is otherwise a
     sibling of the head, judged against `prior` in the checks below;
     if it is not `index[n - 1]`, `missing-predecessor`;
   - `m` < `n`: a `duplicate` when the candidate's commitment is `index[m]`,
     otherwise `refused(superseded)`. The verifier does not judge a competing
     epoch for a slot the chain has passed;
   - `m` > `n` + 1: `missing-predecessor`.

   In the checks below `P` is the predecessor this selects: the head for a
   successor, `prior` for a sibling. A candidate with `predecessor_tag` 1 has
   `m` >= 1, so `index[n - 1]` exists whenever `m` = `n`, unless the head is the
   checkpoint the verifier started from.

   An entry of `index` that is not held is never equal to a candidate's
   commitment (The accepted state). While the head is the checkpoint (Joining
   from a checkpoint), `prior` is absent and `index[n - 1]` is not held, so the
   case `m` = `n` reads:
   a `duplicate` when the candidate's commitment is `index[n]`, and otherwise
   `missing-predecessor`. The head's predecessor is not an accepted epoch here,
   so no sibling of the head can be judged, and the verifier does not wait to
   judge one: that is a limit and not a gap. The other cases read as written,
   and a candidate numbered below the checkpoint is `refused(superseded)`. When
   a successor of the checkpoint has been accepted, `prior` is the checkpoint
   and `index` holds its entry, and every case reads as written.
3. **Conflict marker.** If `conflict` is set, `refused(blocked-by-conflict)`.
   Only a successor of the head or a sibling of it reaches this check (check 2),
   so a replay of an accepted epoch is still a `duplicate`, and a candidate for a
   slot the chain has passed is still `superseded`. Every other candidate is
   refused here, whoever signed it, before its signature is examined (Conflict;
   Open decision D-12).
4. **Closure.** `P`'s `closure_state` is 0, else `refused(group-closed)`.
5. **Writer authority.** The principal of `P` whose account is
   `writer_account` lists a device whose `binding` equals `writer_binding` byte
   for byte and whose `update_authority` is 1, else
   `refused(writer-not-authorised)`. The candidate's own authority set is not
   consulted, and the writer need not be listed in the candidate: a device may
   sign the epoch that removes it. For a sibling of the head, the writer must
   also be in the head's authority set, else `refused(writer-not-authorised)`
   (Conflict; Open decision D-12).
6. **Signature.** As Signature above, else `refused(bad-signature)`.
7. **Profile.** Let `v` be the candidate's `policy_version`. The check passes if
   the verifier supports `v`. Otherwise the result is `unsupported` when all
   three hold: the list has exactly one `set_policy`; that operation names `v`
   and the candidate's `policy_commitment`; and the principal of `P` whose
   account is `writer_account` has role 1. When they do not all hold, the check
   passes without judging `v`, and the candidate goes on to be refused. `P`'s
   version is supported (it was accepted under this check, or under check 4 of
   Genesis or of Joining from a checkpoint), so an unsupported `v` reaches a
   header only through a `set_policy`. A header that is not what `apply` gives
   is refused at check 9, and a `set_policy` written by a principal that is not
   an owner is refused at check 11. It follows from these checks, as this page
   reads them, that no candidate that names an unsupported version is accepted
   and that an admin cannot force `unsupported` with any header or operation
   list. No model or test states this.
8. **Shape.** Of the candidate's own principals: exactly one has role 1, else
   `refused(invalid-roles)`; every device's `update_authority` equals 1 when its
   principal's role is 1 or 2 and 0 otherwise, else
   `refused(authority-mismatch)`; no two member devices, under any principal,
   have the same `identity_public_key` bytes (compared as bytes: Open decision
   D-10, and Identity keys in accepted state), and no `device_id` occurs twice
   under one principal, else `refused(duplicate-device)`.
9. **Operations.**
   - `refused(conflicting-operations)` if: a device binding is named by more
     than one `admit_device` or `remove_device` (so a device removed and
     admitted again in one list is refused); an `admit_device` names an identity
     public key that a `remove_device` in the list also names (Open decision
     D-13); there is more than one `transfer_ownership` or more than one
     `set_policy`; a principal is named by more than one `set_role` or
     `transfer_ownership`; or `close` is listed with any other operation.
   - `refused(unknown-target)` if a `remove_device` names a binding that is not
     a member device of that account in `P`, or a `set_role` or
     `transfer_ownership` names an account that is not a principal of `P`.
   - `refused(already-member)` if an `admit_device` names a binding that is
     already a member device of `P` under any account.
   - `refused(projection-mismatch)` if `apply(P, ops)` does not equal the
     candidate's principals, `closure_state`, `policy_version` and
     `policy_commitment` exactly. A retained member device (one that `P` lists
     and no `remove_device` removes) keeps the entry `P` has for it in
     `apply(P, ops)`, byte for byte, except its `update_authority`, which step 6
     of `apply` sets from its principal's role. So a role change is accepted: a
     `set_role` or `transfer_ownership` that changes a principal's role changes
     the `update_authority` byte of that principal's retained devices, and the
     candidate must carry the byte step 6 gives. Any other difference between a
     retained entry in the candidate and in `P` (its binding, its
     `inventory_generation`, its `inventory_commitment`, or an
     `update_authority` that step 6 does not give) is a mismatch. A stale
     `update_authority` on its own is `authority-mismatch` at successor check 8,
     which runs first.
10. **Key epoch.** `key_epoch` equals `P`'s `key_epoch` plus 1, else
    `refused(key-epoch)` (Open decision D-2). A `P` whose `key_epoch` is
    2^64 - 1 has no successor, so every candidate for it is refused here.
11. **Policy.** Each operation, in list order, satisfies Policy version 1 with
    roles read in `P`: first the writer's role, then the target. The results are
    `refused(writer-role-insufficient)` where an operation needs an owner and
    the writer is not one; and `refused(target-protected)` where an admin's
    `remove_device` or `admit_device` names an owner's or an admin's principal
    (Open decision D-9), or where `set_role` or `transfer_ownership` names the
    owner.
12. **Verdict.** If the caller supplies a policy verdict, its
    `prior_commitment` is `P`'s commitment and its `candidate_commitment` is the
    candidate's, else `refused(verdict-mismatch)`; and its result is `allow`,
    else `refused(verdict-denied)`.
13. **Evidence.** A device is new if the candidate lists it and `P` does not
    (every device, for genesis). For each principal with new devices, in
    principal order: the new devices all carry one `inventory_generation` and
    one `inventory_commitment`, else `refused(evidence-mismatch)`; the evidence
    holds exactly one signed statement for the principal's account, else
    `refused(evidence-missing)` for none and `refused(evidence-mismatch)` for
    more than one; the statement's `inventory_generation` and the commitment of
    its unsigned preimage equal those the new devices carry, else
    `refused(evidence-mismatch)`; the statement's `active` list holds each new
    device's `binding` exactly, else `refused(evidence-mismatch)`; the
    `identity_public_key` of each new device passes the identity-key rule
    (identities-and-devices.md, Identity keys), else
    `refused(invalid-identity-key)`; and the inventory acceptance procedure
    accepts the statement for that account, else `refused(evidence-refused)`.
    The verifier applies the identity-key rule itself and does not rely on the
    procedure for it (The accepted state, Identity keys in accepted state).
    Devices the candidate retains keep the
    generation and commitment they were admitted with and need no evidence.
    Evidence for an account that has no new device is neither required nor
    examined.

The order decides which kind a candidate with several faults gets. Check 8
judges the candidate's own principals before check 9 compares them with
`apply`, so a kind of check 9 or 11 is reached only by a candidate that passes
check 8. A lone `set_role` naming the owner is `invalid-roles` if the candidate
reflects `apply` (it has no owner) and `projection-mismatch` if it does not, and
check 11's `target-protected` for it is reached only when the list also
transfers ownership. An `admit_device` naming a binding that `P` lists under
another account is `duplicate-device` if the candidate reflects `apply` (two
devices with one key), and `already-member` if it omits the device from its
first account.

If every check passes, the result is `accepted` when `P` is the head. When `P`
is `prior`, the candidate is a valid competing successor of the head's
predecessor, and the result is `conflict`.

### Effects

- **accepted.** One durable step sets `prior` to the old head, `head` to the
  candidate with its signature and `index[m]` to its commitment, and retires the
  old head's key material.
- **conflict.** `conflict` is set. Nothing else changes.
- **every other result.** Nothing changes.

### Policy verdict

A product whose policy is stricter than version 1 supplies a verdict. It is an
input to accepting a successor only (check 12). Genesis and Joining from a
checkpoint have no predecessor for it to name, and a product narrows those by
the anchor it pins.

```text
prior_commitment              32 bytes
candidate_commitment          32 bytes
result                        allow or deny
```

The verifier does not interpret the reason for a `deny`. A verdict can only
refuse: a missing verdict does not stop a candidate that passes every other
check, and an `allow` does not accept a candidate that fails one. The verdict
binds the exact predecessor and candidate it was made about, so a verdict for
another pair is refused. The product's own role model, invitation and consent
rules are its own; nothing on this page proves that a candidate met them.

A verdict is requested at check 12, before check 13 applies the identity-key
rule to the new device keys and examines the evidence. A product's verdict code
therefore sees candidates whose new keys have not passed the rule and whose
evidence is unverified. identities-and-devices.md, Accepting a signed statement,
applies the key rule to every entry before its policies for that reason. The
verdict also applies to a sibling, like any candidate (check 12), so a product
can refuse siblings and not be frozen. Two products that differ in this diverge
on one group, and the page does not say that a product should or may do it.

## Conflict

There is one accepted successor for a predecessor commitment. A replay of it is
a `duplicate`. A different candidate for the same predecessor that passes every
check is a `conflict`: two authorised writers proposed different successors from
one epoch. A `conflict` needs a candidate that passes checks 1 to 13, so an
unauthenticated candidate cannot cause one. Any writer that is still authorised
can: by proposing a sibling, by replaying an earlier sibling, or by an honest
race with another writer. So can anyone who holds the bytes of a valid sibling
and delivers them, whether or not the writer meant them to be delivered. No key
is needed for that. The writer is in the body, so the same content signed by two
writers is two candidates and conflicts. A verifier whose head is the checkpoint
it started from judges no sibling of it (Accepting a successor, check 2), so it
neither sees a `conflict` there nor can be frozen by one.

Whether a sibling is a `conflict` depends on the caller's inputs. A sibling that
admits new devices is judged at check 13 by the caller's freshness rule, and a
rule that refuses a generation the verifier has already recorded refuses the
sibling as `evidence-refused`, with no marker (Open decision D-6). A verifier
under such a rule never sees that equivocation as a `conflict`.

A writer that the head has removed from the authority set is not such a writer.
A candidate it signs as a sibling of the head is refused at check 5, and is not
a `conflict`. Without that rule, a writer removed by the head could freeze every
verifier that accepted the removal by signing a sibling of the removal epoch,
which its old authority in the predecessor would still validate (Open decision
D-12). A verifier that accepted the removed writer's epoch before the removal
is on another branch, and learns of it only if it receives the removal as a
`conflict`.

### The marker

`conflict` is set by a `conflict` result and holds nothing: not the sibling's
commitment, its writer, its bytes, its operations or its device set. While it
is set the verifier accepts nothing. Check 3 refuses every successor of the head
and every sibling of it, `blocked-by-conflict`, before its signature is
examined, so a candidate that arrives afterwards is neither authenticated nor
recorded. Replays of accepted epochs stay `duplicate` and candidates for slots
the chain has passed stay `superseded`. The verifier's coordinator proposes and
distributes nothing (Obligations at the product boundary, 3). The verifier
records the marker in the durable step that sets it, and a restart returns it
to the last committed state, marker included.

**This page gives no way out of a frozen state.** Nothing that any writer signs,
and no replay, verdict, timer, caller instruction or position a service
assigns, clears the marker. Starting a new verifier from a checkpoint is not a
way out: it discards the frozen state, it trusts the inviter for the whole state
of the group at one epoch, and it does not choose between the branches (Joining
from a checkpoint). Recovery from a frozen verifier, and from a fork between
verifiers, is separate work that this page does not specify. This page has no
fork choice: no rule here selects a winner from a service's order, a timestamp
or a commitment's numeric value, and a verifier that accepted the sibling
instead of the head is on another branch that nothing here brings back.

The marker records no writer. Whom to remove is a question for the recovery
that this page does not specify, and a record of the sibling's writer could not
answer it here: the network chooses which valid sibling arrives first, so the
writer named would be the first one delivered, whether or not it acted in bad
faith, and no check on this page reads it (Open decision D-12).

## Key epochs

Every accepted successor starts a new key epoch: `key_epoch` is the
predecessor's plus 1 (check 10; Open decision D-2). So in a chain that starts at
genesis `key_epoch` equals `epoch_number`, and material bound to an earlier epoch
is never current in a later one. A verifier that started from a checkpoint takes
the checkpoint's `key_epoch` on the inviter's word: no check relates it to the
checkpoint's epoch number, so the equality is not established for it, only that
each later epoch's `key_epoch` is one more than its predecessor's. A checkpoint
whose `key_epoch` is 2^64 - 1 has no successor (check 10). The field is written
out so that a rule that advances it only on some epochs (Open decision D-2)
changes one check and not the encoding.

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
4. **Retirement.** Accepting a successor retires all material bound to the
   previous head in the same durable step. There is no state in which the
   successor is accepted and the previous head's material is still current.

These four are bookkeeping. They fix which epoch material is bound to, who is
sent it and when it stops being current. They do not say that material created
for a later epoch cannot be computed from material an earlier member holds,
which includes a removed device: a key engine could derive every later key from
an earlier one and meet all four. That independence is what makes a removal mean
anything against a device that keeps its keys. It is the key engine's
obligation. This page does not list it among the four obligations above and does
not establish it (The removal invariant, What it does not claim).

### Obligations at the product boundary

These are not checked by this page. They are the parts of the removal property
that a product supplies, and the product's tests are where they are exercised.

1. The product commits an accepted epoch durably before it distributes key
   material or dispatches application traffic for it.
2. On accepting a successor that removes a device, the product cancels every
   unsent item and every remaining retry addressed to that device, and keeps
   the record of what was handed off before.
3. The product takes the recipients of every distribution and send from the
   head, not from a directory. It does not propose or distribute while
   `conflict` is set, while it knows of a gap in the chain from its own fetch of
   it, or while the only successor of the head that it has seen is
   `unsupported`. It does not propose again a batch that it assembled against a
   head that has since moved. A `missing-predecessor` result on candidate bytes
   alone is not that knowledge of a gap, because anyone can produce one.
4. A removed device is treated as a new device if a later epoch admits it: it
   receives no application history and no key material of an earlier epoch.
5. The product starts a verifier from a checkpoint only on an invitation it has
   authenticated as made by the inviter the joiner means to trust and as
   unmodified, and it pins the checkpoint commitment from that invitation alone:
   not from a directory, an inventory statement, a service's list of heads or the
   bytes of the epoch. A device that already holds state for the group discards
   it, and what is tied to it, before it starts from a checkpoint, because a
   verifier that holds a head refuses one. It does so only when the user has
   chosen to replace that group, and not because a checkpoint was refused as
   `already-started`: an inviter chooses the `group_id` its epoch names, and can
   name one the device already holds.

## What is not checked, and what is not claimed

The checks above do not establish, and nothing on this page claims, any of the
following.

- **Equivocation.** An authorised writer can send different valid successors
  to different verifiers. A verifier sees that only if it receives both, and
  then only as a `conflict`, as a refusal (a writer the head removed, or
  `evidence-refused` under a freshness rule that refuses a recorded generation),
  or as `superseded` (a slot the chain has passed, which is not judged). A
  `conflict` records nothing of who the writer was.
- **Availability.** A `conflict` freezes a verifier for good as far as this page
  goes: nothing on this page clears it (Conflict). The window in which a
  verifier can be frozen is not a race between authorities that act together. It
  is the staleness of any authority device. A device that writes an epoch
  against a head that has since moved writes a sibling: because it was one epoch
  behind, because a second device of the same account wrote one too, because a
  retry assembled a batch again, or because a delivery service kept a candidate
  that lost a race. Every verifier that has accepted the head and receives both
  siblings before it accepts a successor of the head is frozen. A device two or
  more epochs behind writes a candidate that is `superseded` at a verifier that
  has accepted the head, so a device exactly one epoch behind is the case that
  matters. The authority set can be every member device, since an owner can make
  every principal an admin, and policy version 1 fixes authority by role, so the
  page has no way to name the one device that proposes. A service that rejects
  the loser of a race still holds a valid sibling, which nothing expires and
  which freezes any verifier still at the head it was written for. No key is
  needed for that: anyone who holds the bytes of a sibling that needs no
  evidence, such as an epoch with no operation or one that only removes a
  device, can deliver them to such a verifier. Verifiers that receive the
  siblings in different orders end on different heads, each frozen at the one it
  saw first or not yet frozen. A product that lets one writer at a time propose
  does not cover a device that is behind, a second device of the same account, a
  retry, or a service that kept a losing candidate, and this page does not
  require it. This page gives no way out of a frozen state and no way to bring
  verifiers on different branches together.
- **Removal of an authority.** An authority that an owner removes can keep
  chosen verifiers from ever accepting its removal. Let `C` be the owner's epoch
  that removes it, and let the authority write another successor `S` of the same
  head, even an epoch with no operation. A verifier that accepts `S` first
  receives `C` as a sibling of its head. `C` passes check 5, because its owner
  is still in the authority set of the head, which an admin cannot change: the
  result is `conflict`, the verifier is frozen, and the removed authority is
  still a member device of its head and a permitted recipient there (Obligations
  on the key engine, 2). The rule that refuses a sibling from a writer the head
  removed does not help, since the head is the authority's own `S`. The removal
  invariant holds for the verifiers that accepted `C` and says nothing of these.
- **Cadence.** A writer with authority can write an epoch with no operation.
  Under Open decision D-2, option A, that starts a new key epoch and the
  redistribution after it, and nothing on this page limits how often an
  authority device writes one.
- **Silence.** A frozen verifier, and a group that has split across branches,
  give no signal to a user on this page's rules. A frozen verifier returns
  `blocked-by-conflict` to its caller, and nothing requires the product to show
  it. A split shows only as `missing-predecessor`, which a gap or a delay also
  causes. A frozen verifier keeps the key material of its head current
  (Obligations on the key engine, 3). Obligations at the product boundary (3)
  stops its coordinator from proposing and distributing; it does not stop the
  product from sending application traffic from that head, or from taking that
  head's member devices as recipients, and peers that have moved on do not
  accept that traffic as current.
- **Catching up.** A device that has been away accepts the epochs it missed by
  judging each of them again, and under the default freshness rule (Open
  decision D-6, option A) that can stall for good. The caller's freshness rule
  can refuse a generation that the caller has already recorded for the account,
  for example from another group or a pairwise flow. A stored generation never
  decreases (identities-and-devices.md, Accepting a signed statement,
  freshness), so the same bytes with the same evidence are refused again as
  `evidence-refused`, and the epochs after that one are `missing-predecessor`.
  The same rule lets an account holder's own action (raising a generation) make
  some verifiers refuse an in-flight epoch as `evidence-refused` and others
  accept it. The page names a replay input to the freshness rule (Inputs) and
  gives no criterion for setting it. It does not say who may set it, and whoever
  sets it chooses whether a statement older than a revocation is accepted. It
  also does not say who keeps the historical statements that a replay needs, or
  the issuer-key bindings that signed them: the procedure reads those as they
  stand when the check runs, and a binding that no longer resolves makes the
  epoch `evidence-refused`.
- **Unsupported versions.** An owner can write a policy version that some
  verifiers do not implement (`unsupported`); they stop, and a group that goes
  on without them is on another branch from them. The owner's epoch need not be
  valid in any other respect for that: check 7 runs before checks 8 to 13, so an
  owner's candidate with such a `set_policy` and a wrong `key_epoch`, or with an
  `admit_device` and no evidence, is `unsupported` too. `unsupported` can be a
  circular wait. Its exit is that the verifier supports the version or accepts
  another successor of its head (Results). While `unsupported` is the only
  successor of the head that a verifier has seen, its coordinator proposes
  nothing (Obligations at the product boundary, 3), so if every verifier in the
  group answers `unsupported`, no coordinator may propose, no other successor
  appears, and the page provides no exit. A verifier keeps nothing when it
  answers `unsupported` (Effects), so judging the candidate afresh needs the
  product to hold it. The page gives an owner no way to learn which versions the
  member devices support: the only capability bit is `GROUP_EPOCH_V1`, so a move
  to a second policy version has no negotiation, and a device that does not
  support it stops at `unsupported`. Nothing here bounds how long an unsupported
  policy version, a gap or a missing statement keeps a group from progressing.
- **Retention and re-offer.** A verifier keeps nothing about a candidate it has
  not accepted, except the marker. When it answers `missing-predecessor`, the
  product has to keep the candidate and offer it again after the predecessor is
  accepted, and this page does not say for how long, in what order, or how many.
  A candidate cannot be authenticated before its predecessor is accepted,
  because authority is read from the predecessor, so a product that buffers
  holds unauthenticated bytes, each up to 2,167,845 bytes, with no bound that
  this page states. The order in which a backlog is offered decides whether a
  verifier is frozen. With candidates A and B that are siblings, and C a
  successor of A, a verifier that is offered A, B, C is frozen at B (and C is
  `blocked-by-conflict`), and one that is offered A, C, B is not (B is then
  `superseded`). Two products that offer a backlog in different orders end in
  different states on the same bytes.
- **Freshness.** A verifier decides against the head it has. It cannot know of
  a successor it has not received. A withheld successor is undetected, and a
  removed device can go on using what it holds with any peer that has not
  accepted the removal.
- **The chain before a checkpoint.** For a verifier that started from a
  checkpoint, everything listed under What a joiner cannot verify (Joining from a
  checkpoint). It takes the checkpoint's state from the inviter, and claims
  nothing about the epochs before it.
- **Order.** The order or position a service assigns never authorises a
  candidate, and never resolves a `conflict`.
- **`duplicate`.** `duplicate` is decided from the commitment alone, and the
  commitment excludes the signature (Commitment), so bytes that carry an
  accepted epoch's body and a corrupt signature are `duplicate`. It is not
  evidence that the bytes are valid. A caller that stores or forwards bytes it
  has been told are duplicates can pass on the corrupt signature, and a joiner
  given such bytes as a checkpoint is protected only by checkpoint check 6. A
  store or negative cache keyed by commitment alone that keeps the first copy it
  sees lets whoever delivers a body first, with a garbage signature, displace
  the genuine copy: the verifier answers `bad-signature`, and a product that
  drops later copies of that commitment as repeats never offers the genuine one.
  The page does not require the caller to keep the signature it accepted first.
- **Results before the signature.** Successor checks 2 to 5 return their results
  before the signature is examined: `wrong-group`, `missing-predecessor`,
  `duplicate`, `superseded`, `blocked-by-conflict`, `group-closed` and
  `writer-not-authorised` are given for bytes that nobody has authenticated. A
  product that shows these results to a sender, or to a peer that probes, tells
  it whether the verifier is frozen, whether the group is closed, and which
  pairs of account and binding are authority devices of the head. The anonymity
  non-claim covers the roster only.
- **Delivery.** That a recipient has received an epoch, that a removed device
  has learned of its removal, or that any message reached anyone.
- **Recall.** Anything a removed device already received: plaintext,
  ciphertext, key material, or the accepted epochs it saw.
- **Traffic under retired material.** Obligations on the key engine (3) leaves
  to the engine what it does with retired material, such as decrypting a message
  that arrives later. A removed device keeps its old keys. If a peer that has
  accepted `C` still accepts a late arrival under that material, the removed
  device can pass messages off as earlier ones. RM-2 says nothing about this.
- **Honest members.** That members do not share plaintext or key material. An
  authorised writer can also write any epoch that policy version 1 allows,
  including one that harms the group.
- **Consent and intent.** That an account agreed to be admitted, that an
  invitation was made, or that an operation matches what a user meant. These
  are the product's.
- **Identity.** That an identity key belongs to the person an administrator
  means (ASM-14; EX-09), or that two account handles denote different accounts.
- **Aliasing.** Removal is per exact binding. Keys are compared as bytes (Open
  decision D-10, option A adopted). That relies on the verifier applying the
  identity-key rule to the key of every device that enters accepted state, and
  on the rule admitting one spelling of a key (The accepted state, Identity keys
  in accepted state). On that premise two member devices of one epoch cannot
  hold one key under two spellings. A later epoch can still admit a removed key
  again under another binding, and that is another member device (Open decision
  D-13).
- **Inventory.** That an inventory statement is current or complete, or that its
  issuer is honest. A compromised issuer can list a device for an account. It
  cannot admit that device: only an epoch written by an authorised writer does.
  Under Open decision D-9 (adopted B) an admin can write an admission only for a
  member principal or for a new principal, which enters as a member, so an admin
  and a compromised issuer together can add a member device that has no
  authority in the epoch that admits it. An owner writes the epoch that gives a
  principal authority, and that epoch gives it to every device already under the
  principal, including one added earlier (`apply`, step 6). Currency is not
  checked either. A revocation in an account's inventory does not remove a
  device from a group, and a service that carries evidence (ADV-01, ADV-04) can
  serve a statement older than a revocation. A caller whose freshness rule (Open
  decision D-6) accepts it lets a writer admit a device that the account has
  since revoked. That rule is the caller's.
- **Promotion and re-entry.** `set_role` and `transfer_ownership` name an
  account, not its devices. `apply`, step 6, gives `update_authority` 1 to every
  device under a principal whose role becomes owner or admin, including a device
  that an admin added earlier while the principal was a member, and a device
  whose admission rested on a statement from a compromised issuer. The operation
  lists no devices, so it does not show the owner which devices gain authority.
  Removal is by binding, and a removed device can return under another binding
  if a writer allowed to admit for its account admits one that the account's
  inventory lists (Open decision D-13; Aliasing). When the holder of the removed
  device controls that inventory, as with a stolen phone, only the same-batch,
  same-key case is refused.
- **Chain of custody for a replacement.** That a binding's
  `replacement_predecessor` names any binding. This page gives it no meaning and
  no check above reads it. The inventory section does not let a verifier refuse
  a statement solely because a replacement's marker names no listed binding, and
  this page adds no such rule, so a device whose binding carries a marker is
  admitted on the same evidence as any other.
- **Evidence carriage.** Who stores or serves the inventory statements a
  candidate needs. A verifier without them cannot follow the chain past that
  epoch (`evidence-missing`).
- **The evidence set.** Evidence is not signed by the writer, is not committed
  in the epoch and is not authenticated in delivery. Successor check 13 refuses
  a candidate for which the evidence holds more than one signed statement for a
  principal's account (`evidence-mismatch`). A party that delivers the evidence
  can therefore add a second genuine statement for that account, for example an
  older one: the same candidate is refused at the verifiers given that set and
  accepted at those given the clean one, and the refusal costs the verifier the
  work of check 13 up to that point. The refusal is not terminal (Results), and
  the page has no rule for choosing between two statements. Inputs calls the
  evidence a set of signed inventory statements, and the page does not say how
  an entry is counted that does not decode as a signed statement, that repeats a
  statement with other signature bytes, or whose unsigned preimage equals
  another entry's. Those points are open: this page fixes no result for them.
- **Anonymity.** An epoch lists account handles and device keys. Whoever holds
  the epoch learns them. Nothing here hides who is in a group.
- **Recovery.** A lost or compromised owner, a compromised admin, a frozen
  verifier, or a fork between verifiers. This page gives no way out of a frozen
  state (Conflict). Nothing on this page lets an authority establish its own
  replacement. A checkpoint is not recovery (Joining from a checkpoint).
- **Post-quantum authority.** Writer signatures are classical XEdDSA
  signatures (EX-11).
- **Storage.** A verifier whose stored state is rolled back or rewritten
  accepts what its restored state allows (ASM-12; EX-07).
- **The key engine.** That any key engine meets the obligations above. That is
  its specification's and its proof's to show. It also covers what those
  obligations leave out: that a removed device cannot compute the key material of
  a later epoch (Obligations on the key engine).
- **Agreement on key material.** An epoch commits to membership, roles, policy
  and closure state, and to a `key_epoch` number. It does not commit to any key
  material. Nothing on this page makes members check that they hold the same
  material for an epoch, or that an admitted device received what the others
  hold: `key_binding` is a record that each holder keeps (Obligations on the key
  engine, 1). A member that gives different recipients different material, or
  gives an admitted device material that no one else holds, breaks no check
  here. What an epoch body commits to is fixed by the encoding.
- **Single points of failure.** Policy version 1 makes some people necessary,
  and the page does not weigh that. Only an owner adds or removes a device of an
  owner or admin principal, sets a role, transfers ownership, sets the policy or
  closes the group (Open decision D-9, option B). An owner whose devices, at
  most eight, are all lost cannot be replaced: no one can transfer ownership,
  and an admin cannot appoint an admin. An admin who loses a device needs the
  owner to replace it. A member cannot remove its own device, and leaving the
  group is not an operation, so a lost device stays a member device and a
  permitted recipient until an admin or the owner commits its removal. `close`
  cannot be undone, and a verifier that accepted a sibling first never accepts
  it and is frozen. Recovery is not specified (Recovery).
- **The atomic step.** The step in which a candidate is accepted spans three
  stores: this page's accepted state, the caller's record of the generations it
  has seen (Inputs), and the key engine's retirement of the previous head's
  material. The page requires one atomic step across them and gives no order or
  recovery for a failure part-way. If the generations are recorded and the head
  is not, a freshness rule that refuses a generation already recorded refuses
  the same epoch for good. If the head is kept and the generations are not, an
  older statement can be accepted later. A restored backup returns an older head
  and drops the marker (assumption 1 of the removal invariant excludes it), and
  the page says nothing of what a verifier does after a restore.
- **Sizes and costs.** That an epoch of the largest size is affordable to send,
  fetch or verify. The ceiling of 2,167,845 bytes is derived from the bounds and
  is not stated as a test that runs before anything is read, and the number and
  total size of the signed statements in the evidence have no bound on this
  page, although a verifier has to decode each to see which account it is for.
  The loop over principals is the outer loop of successor check 13, so a
  candidate whose last principal in byte order fails a cheap condition
  (`evidence-missing`, `evidence-mismatch`) has already cost, for every earlier
  principal with new devices, the whole work of the acceptance procedure; the
  page does not say whether a verifier may remember a refusal. The size of an
  epoch does not shrink with the size of the change: every epoch carries the
  full state (Open decision D-7), so one operation in a group of 512 principals
  with eight devices each is still at least 352,256 bytes of device entries
  (4096 devices at 86 bytes, a binding without a replacement marker being 45
  bytes). A verifier keeps `head` and `prior`, each up to the ceiling, and a
  32-byte index entry for every accepted epoch.

## The removal invariant (a target, not shown)

This section states one property so that a model and a proof can be written
against it. It is a statement of what is to be shown. It is not shown: there is
no model, vector, test or proof for it, `tacenta-proofs/CLAIMS.md` has no entry
for it, and nothing on this page is a claim of assurance.

The three statements below concern membership acceptance and recipient sets:
which devices a verifier that has accepted an epoch counts as members, who may
be sent key material, and which material is current. They say nothing about
whether a removed device can compute later key material from what it held. That
is the key engine's obligation and is not established here (Obligations on the
key engine).

### Statement

Let a verifier hold accepted state whose head is `P`. Let it accept a candidate
`C` as `P`'s successor whose operations include `remove_device` for `r`, one exact
device binding. Check 9 makes `r` a member device of `P` (an operation that names
a device `P` does not list is `unknown-target`) and makes `r` not a member device
of `C` (a candidate that still lists it does not equal `apply(P, ops)`). The
statement is keyed on the operation and not on the absence of `r` from `C`,
because a statement that only assumed the absence would hold of any checks,
including none. Then, in the verifier's state after that:

- **RM-1: no fresh distribution to `r`.** `r` is not a permitted recipient of
  any key material (Obligations on the key engine, 2), and stays so in every
  later state of the verifier until it accepts an epoch that admits `r` by
  `admit_device`, as an ordinary admission with evidence the caller's freshness
  rule accepts. This is a statement about the binding `r`. A device that holds
  the same key under another binding, admitted by a later epoch, is another
  member device (Open decision D-13). Check 8 keeps two member devices of one
  epoch from holding one key.
- **RM-2: no current use of retired material.** No key material bound to an
  epoch earlier than `C` is current (Obligations on the key engine, 3), which
  includes every unit of material `r` was ever a permitted recipient of, and
  `key_epoch(C)` exceeds the `key_epoch` of every epoch this verifier accepted
  in which `r` was a member device. Nothing on this page relabels retired
  material as current. That no one else can is Obligation 1's, on the key
  engine.
- **RM-3: no new dispatch to `r`.** The product does not start a new send,
  distribution or retry addressed to `r`, from stale pending work or otherwise,
  once it has durably committed `C` (Obligations at the product boundary, 2).

A `conflict` does not put the sibling's devices into the verifier's state: the
sibling that froze it is never accepted. It does not bring a removal about
either. A verifier that is frozen before it accepts `C` stays on a head that
still lists `r`, and these three statements are not made of it (assumption 3).

RM-1 to RM-3 restate obligations. RM-1 follows from Obligations on the key
engine (2) once `r` is not a member device of the head. RM-2 follows from
Obligations on the key engine (3) and (4), and, for its clause on `key_epoch`,
from check 10. RM-3 is Obligations at the product boundary (2). With assumption
5, that the engine and the product meet their obligations, the three statements
are consequences of those obligations and of `apply`, and they have little
security content beyond them. What the checks add is this: the head moves by
exactly one key epoch (check 10), so material bound to an earlier epoch is never
current in a later one; a removal cannot be hidden in a batch (check 9); and a
removed binding is not a member device again unless a later epoch admits it with
evidence (check 9 and `apply`). The three statements are about recipient sets
and retired material. They are not a statement that a removed device is excluded
from the group's secrets; that depends on the key engine (Obligations on the key
engine; What it does not claim).

### Adversary

The adversary chooses the candidate bytes, the evidence and their delivery:
their order, their timing, their replay and their omission. It may be:

- a removed device, holding everything it held while a member (ADV-02, as to
  its state, and ADV-06, as a former peer);
- a network and service that orders, delays, drops and replays (ADV-01) and
  serves a directory that lies (ADV-04);
- a writer in `P`'s authority set, restricted to what policy version 1 lets
  that role write.

It cannot forge a signature under a key it does not hold (ASM-03), find a
SHA-256 collision (ASM-07), or write the verifier's storage (ADV-05 is outside
scope).

### Assumptions

1. The verifier's accepted state is durable and is not rolled back or rewritten
   (ASM-12; EX-07).
2. XEdDSA signatures and SHA-256 are as ASM-03 and ASM-07 assume.
3. The verifier has accepted `C`. Nothing is claimed of a verifier that has
   not.
4. The remaining members run conforming implementations and do not give `r` key
   material or plaintext. This excludes a writer in `P`'s authority set that
   remains a member after `C` from giving `r` key material, although the
   adversary below includes such a writer.
5. The key engine meets Obligations on the key engine, and the product meets
   Obligations at the product boundary.
6. The caller's inputs to acceptance (the anchor, the issuer binding and the
   freshness rule) are as they intended.
7. For a verifier that started from a checkpoint, the checkpoint is a head that
   the group's members accepted, and its inviter was right about it (Joining
   from a checkpoint, Trust assumption). The invariant is stated from the
   checkpoint on.
8. Nothing above is an assumption about how key material is derived. Whether a
   removed device can compute the material of a later epoch from what it held
   is not among the obligations stated on this page and is not covered by RM-1
   to RM-3.

Assumptions 1 and 2 cite entries of the threat model. Assumptions 4 to 7 are
this page's own, and they are in no register (ADR-0008, rule 2 asks
threat-model/assumptions.md to state what the protocol and the proofs assume).
The identifiers RM-1 to RM-3 are labels used on this page and are not
requirement identifiers.

The inventory issuer is not an assumption of RM-1 or RM-2 once `C` is accepted:
removal needs no evidence. The issuer matters to admission, which decides who is
a member device to begin with.

### What it does not claim

- Instant or global revocation. It concerns a verifier that has accepted `C`.
- Anything about a peer that has not accepted `C`, or an offline device.
- That every verifier accepts `C`. An authority that `C` removes can keep chosen
  verifiers from ever accepting it (Availability, under What is not checked):
  they accept a sibling written by that authority first and are then frozen by
  `C`.
- That `r` learns it was removed.
- Recall of anything `r` already received, or protection of past messages from
  `r`.
- Detection of a withheld or unseen successor.
- That an authorised member cannot share plaintext or keys.
- Post-compromise security of the group, or recovery from a compromised
  authority.
- Anonymity, or that `C` was a sensible thing to write.
- Secrecy of later key material from a removed device. Nothing here says that
  the key material of the epoch after a removal cannot be computed from material
  the removed device held, or from public values. That is the key engine's
  obligation, and it is not established here.
- Anything before a checkpoint. A verifier that started from a checkpoint holds
  it as its first head, and the invariant applies to what it accepts after that.
  It says nothing about whether a device the group removed earlier is absent from
  the checkpoint, which the joiner takes from its inviter.
- Anything across a discard. The invariant is about one verifier for its
  lifetime, not about a device. A device that discards its state and starts from
  a checkpoint is a new verifier, and a checkpoint older than what the device
  once accepted can list a device the group has since removed (What a joiner
  cannot verify).
- Removal of a device by key. It is by binding. A later epoch can admit the same
  key under another binding (Open decision D-13; Aliasing, under What is not
  checked).

Retained old keys are the limit that matters most. `r` keeps every key it held
at `P`. It can read what it already could, and it can send under retired
material to any peer that has not yet accepted `C`. A peer that has accepted
`C` refuses that material as current (RM-2).

## Open decisions

The page's text uses a stated default for each only so that it can be read and
checked as one piece. A default is not a decision that anyone has reviewed.
Two dates appear in the marks below. On 2026-09-29 the maintainer said "go" to a
recommended plan that named D-3, D-7, D-9, D-12 (then option E) and D-13; a mark
"Adopted: X (go of 2026-09-29)" means the recommended default of that plan. On
2026-09-30 the maintainer gave a general instruction to go with the
recommendations; a mark "Adopted: X (instruction of 2026-09-30)" means a
recommended default written to the draft on that instruction. The plan and the
instructions are not recorded in this repository. Six decisions carry a mark:
D-3, D-7, D-9 and D-13 (go of 2026-09-29), and D-10 and D-11 (instruction of
2026-09-30). D-12 carries no mark: its default, D, is a recommended default
under the instruction of 2026-09-30 that replaces option E, which the plan of
2026-09-29 adopted. In none of these cases has the maintainer otherwise reviewed
the page. D-7 is adopted for the draft and is to be settled again with
measurements before the encoding is frozen. D-1, D-2, D-4, D-5, D-6 and D-8 keep
a default that the drafter chose and that no one has reviewed. Adopting a
default fixes the choice the text is written to, and it does not ratify the
text.

**D-1: how genesis is anchored, and what `group_id` is.** Options: (A) the
caller pins the genesis commitment, and `group_id` is 32 random bytes the
creator chose; (B) the caller pins `group_id` and the creator's device
binding; (C) `group_id` is the genesis commitment, with a fixed placeholder in
genesis's own `group_id` field. Default: A.

**D-2: key-epoch cadence.** Options: (A) every accepted successor starts a new
key epoch; (B) only a successor that changes the set of member devices does;
(C) the key epoch is not a field of the epoch and belongs to the key engine.
Default: A.

**D-3: who evaluates the policy.** Options: (A) the verifier evaluates policy
version 1 as written here, and a product verdict is not part of acceptance; (B)
only a product verdict decides, and the verifier checks that it names the right
predecessor and candidate; (C) the verifier evaluates policy version 1, and a
product verdict can only narrow. Options A and C put a role matrix in the
verifier, which one reading of the split between the verifier and the product
(Layers; Scope) would leave to the product. Default: C. Adopted: C (go of
2026-09-29).

**D-4: what `policy_commitment` commits to.** Options: (A) nothing in version 1,
so the field is a fixed constant; (B) an opaque 32-byte value a product defines,
which the verifier binds and changes only by `set_policy`; (C) the field is
absent until a second policy version exists. Default: B.

**D-5: the bound on operations in one epoch.** Options: (A) a limit equal to
`MAX_GROUP_DEVICES`, which is the value `MAX_EPOCH_OPERATIONS` has in this
draft, 4096; (B) a small limit chosen to bound the cost of one epoch and of the
key redistribution it causes; (C) a limit set from measurement. Default: A.
Under A an epoch carries at most 4096 operations. A batch can remove up to 4096
devices and admit up to 4096, so replacing every device of a full group is 8192
operations and cannot be written as one epoch, and neither can a replacement of
more than 2048 devices of a full group. That is a cost of option A, the
default.

**D-6: freshness of inventory evidence.** Options: (A) the caller's freshness
rule applies when a verifier first evaluates a candidate live, and a caller
replaying accepted history supplies a rule that accepts the generation named at
admission; (B) evidence is historical and the writer alone is responsible for
freshness; (C) a fixed bound on how far behind the issuer's current generation
the evidence may be, which needs the issuer's current generation as an input.
Under A, whether a candidate is live or replayed is an input to acceptance, so
two verifiers with equal bytes and equal state can differ if one has evaluated
the candidate before. Default: A.

**D-7: full state or a delta.** Options: (A) each epoch carries the full
resulting principals and devices, as this page writes it; (B) each epoch carries
the operation list and a commitment to the resulting state, and a joining
device receives a snapshot separately. The rules above are defined on the
resulting state, so B changes the encoding and not the checks. Default: A.
Adopted: A for this draft (go of 2026-09-29), to be decided again with
measurements of an epoch's size before the encoding is frozen. No vector is to
be written until then.

**D-8: who is in genesis.** Options: (A) only the owner principal, with its
devices; (B) any initial set. Default: A.

**D-9: an admin's power over owner and admin principals.** Options: (A) an admin
may add a device to any principal, and remove a device of an owner or admin
other than the owner's last device and other than a whole admin principal; (B)
an admin acts on member principals only, and on a principal that is new, which
enters as a member, and an owner alone adds or removes devices of an owner or
admin. Under A an admin can admit a device under the owner's principal, which
then carries owner-level authority in the next epoch, with only an inventory
statement standing in the way. Under B an admin cannot manage its own devices,
or another admin's, and the owner must write every such change. Default: B.
Adopted: B (go of 2026-09-29). B is narrower than A.

**D-10: aliasing of identity keys among member devices.** Options: (A) two
member devices may not share the same 32 identity-key bytes; (B) they may not
share an X25519 agreement class (session-establishment.md), which also refuses a
respelling of one key. The identity-key check of "Accepting a signed statement"
admits one spelling of a key (a canonical encoding of a point of the prime-order
subgroup), and the verifier applies that rule to the key of every device that
enters accepted state (The accepted state, Identity keys in accepted state). So
no member device holds a respelling of another's key, and option A suffices;
option B would add a comparison of agreement classes to a rule that already
leaves one spelling of each key. Default: A. Adopted: A (instruction of
2026-09-30). Keys are compared as bytes (check 8). The rule that the byte
comparison relies on is merged text and not a pending one: "Accepting a signed
statement" admits exactly one spelling of an identity key, and "Identity keys"
says where a party applies it. session-establishment.md makes the same argument
for a session: it compares the peer's identity key by bytes, because an identity
key has one canonical spelling. Not part of the adoption: that the verifier
applies the rule itself at check 13 and does not rely on the caller's acceptance
procedure for it. Its cost is one subgroup test per new device, and a candidate
whose new device key fails the rule is `invalid-identity-key` where the
procedure alone would give `evidence-refused`.

**D-11: joining or resuming from an epoch after genesis.** This page defines
acceptance only against an accepted predecessor. A device that joins at epoch
`n` needs an anchor for epoch `n`. Options: (A) it verifies the whole chain from
genesis; (B) it accepts a checkpoint that an authorised writer of epoch `n`
signed, trusting that writer's identity key as ASM-14 describes; (C) it accepts
a checkpoint carried in an authenticated invitation. Default: C. Adopted: C
(instruction of 2026-09-30), as a stated trust assumption: the joiner trusts its
inviter for the checkpoint (Joining from a checkpoint, Trust assumption). Not
chosen: A's cost grows with the whole history of the group, since a joiner would
fetch and verify every epoch since genesis, with the evidence each needs, and
the chain grows with every change to the group. B is not a trust root: a
checkpoint signed by a writer of epoch `n` is judged against nothing the joiner
holds, and an attacker can sign a self-consistent epoch that lists itself. C
trusts the inviter, which a joiner does anyway, and the page says so. The
adoption fixes the choice and not the text. The section is new and has had no
human review, and these parts of it are drafting choices made under C, not part
of what was adopted: the checkpoint's two parts (a pinned commitment and the
epoch), its seven checks, the identity-key check on its devices, the refusals
`already-started` and `invalid-identity-key`, the rule that a verifier that
holds state refuses a checkpoint, so that a device that resumes from one starts
a new verifier, and the acceptance of a genesis epoch as a checkpoint under the
same checks plus the two rules of Genesis that need no evidence. The choice does
not settle the invitation, whose form and authentication are the product's.

**D-12: handling a conflict.** Options: (A) any valid sibling of the head is a
conflict, and a conflict stops acceptance, proposing and distribution until an
unspecified recovery; (B) as A, but a conflict stops only proposing and
distributing, and the verifier keeps accepting successors of the head; (C)
choose deterministically between the siblings, for example by commitment order,
which requires a verifier to undo an epoch it has accepted; (D) as A, except
that a sibling whose writer is not in the head's authority set is refused and is
not a conflict, as check 5 and Conflict write it; (E) as D, and a successor of
the head signed by a device of the head's owner principal clears the conflict in
the step that accepts it. Under A a writer the head removed can still publish a
valid sibling and freeze every verifier that accepted the removal; under D it
cannot, and the fork it makes is visible only as a refusal. Under A to D a
still-authorised writer can freeze a verifier by a sibling, by replay of an
earlier sibling or by an honest race, and A to D give no way out. Default: D.
Option D is a recommended default that this draft is written to under the
maintainer's general instruction of 2026-09-30. It is not an adopted option, and
the maintainer has not otherwise reviewed the page. Option E was adopted (go of
2026-09-29), and this draft does not implement it: D replaces E. The reason is
that E's clear does not recover the group. It moves the cleared verifier onto a
branch that diverges from every peer that kept going: the peers' next
admin-signed epoch is blocked at the cleared verifier, or is a sibling of the
clearing epoch and freezes it again, and a verifier on the other branch of a
fork has no clear at all. Under D, recovery from a frozen verifier is not
specified (Conflict; Recovery, under What is not checked). This page records no
reason for choosing D over B. Adopting a default fixes the choice and does not
ratify the text.

**D-13: the same key admitted again in the batch that removes it.** Options: (A)
an `admit_device` naming an identity public key that a `remove_device` in the
same list names is refused, as check 9 writes it; (B) it is allowed, as a
replacement that changes only the `device_id`, and removal is then per binding
in the strict sense. Under B the holder of a removed key is a permitted
recipient of the same epoch that removed it. Under A a replacement that keeps
its key and changes its `device_id` takes two epochs. Default: A. Adopted: A (go of
2026-09-29).

## Related published work

RFC 9420, The Messaging Layer Security (MLS) Protocol (IETF, July 2023), is
named here because it is published work on group messaging. This page states
nothing about what it covers or how it relates to this page.

This page has not been compared with RFC 9420, and it quotes no text of it. This
repository does not record what the drafter had read of it before writing, so
independence from it is not shown. A comparison is required before the key
engine is fixed. Until a person has made it, from the RFC itself, this page
makes no statement about how its epochs relate to MLS.

The Signal Private Group System (Chase, Perrin and Zaverucha, IACR ePrint
2019/1416) is listed in group-messaging.md, Published material, which says what
it covers. This page has not been compared with it either.

## Sources

- identities-and-devices.md: the `DeviceBinding` encoding, the inventory
  statement, XEdDSA signing and verification, "Accepting a signed statement",
  and "Identity keys".
- group-messaging.md: the two group commitment labels this page's labels stay
  prefix-free against; and "Published material", which Related published work
  points to for the Private Group System.
- RFC 3629, UTF-8 (IETF, 2003): the definition of UTF-8 that the Account term
  uses. Tier `fact` (CONSTANTS.md: standards).
- RFC 9420 and IACR ePrint 2019/1416: named under Related published work only.
  This page cites no rule, field or check as taken from either.
- session-establishment.md: the X25519 agreement class, for option B of Open
  decision D-10, which is not adopted.
- error-handling.md: what is left to an implementation (Accepting a successor,
  Results and The checks).
- CONSTANTS.md: the provenance tiers named under Constants.
- README.md, "Normative status": the standing named in the status paragraph.
- threat-model/: ADV-01, ADV-02, ADV-04, ADV-05, ADV-06; ASM-03, ASM-07, ASM-11,
  ASM-12, ASM-14; EX-04, EX-07, EX-09, EX-11.
- ADR-0003, ADR-0006 and ADR-0008: the research boundary, the
  specification-first rule and the review rule this draft is subject to.

Apart from the sections of this specification and the standard listed above,
this page cites no source for any field, label, bound, rule or check. Whether
any published document or implementation also supplies one has not been
checked, and that check is needed before the page is ratified. ADR-0003 says
that its policy binds every contributor and every tool used to make a change,
and this repository records no statement of what the drafter had read or been
given, so the page does not show that it is independent of RFC 9420 or of any
implementation.
