# Group epochs: encoding, operations and policy

Part of the draft group-epochs.md (the entry page). Status: draft, awaiting review; see group-epochs.md for the review record and what the draft is not.

This part holds Canonical encoding, Operations and Policy version 1, and
"check N" in it means a successor check of group-epochs-successor.md unless a
genesis or checkpoint check is named.

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
it only by `set_policy`, and does not interpret it (group-epochs-decisions.md, Open decision D-4). The
body carries the full resulting principals and devices, as well as the
operations that produced them (group-epochs-decisions.md, Open decision D-7).

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
  `MAX_DEVICES_PER_PRINCIPAL`; total member devices at most `MAX_GROUP_DEVICES`;
  `operation_count` at most `MAX_EPOCH_OPERATIONS`;
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
order gives `wrong-version`. The draft does not say which; this point is open.

Two conditions in the list restate others: the limit on the total number of
member devices is implied by the two counts before it, and the capability word
is already required by the inventory profile (identities-and-devices.md,
DeviceBinding).

A body has a single canonical encoding. Two candidates with equal bodies have
equal commitments whatever their signatures are.

The decoder reads the 32 bytes of an `identity_public_key` and does not apply
the identity-key rule to them (identities-and-devices.md, Identity keys). A
key that the rule refuses does not make an epoch malformed. Where the rule is
applied to the keys of an epoch is stated under The accepted state (group-epochs.md).

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
Verifying a signature answers only yes or no, so this draft reports the writer's
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
of another operation in the list. A candidate is one batch: either all of its
operations take effect, when it passes every check below and becomes the head,
or none of them does.

A batch whose result would exceed a bound of Decoding (more than eight devices
under a principal, more than 4096 devices or 512 principals in all) or that
lists more than `MAX_EPOCH_OPERATIONS` operations has no candidate that both
decodes and equals `apply`. The candidate that tells the truth does not decode,
and a candidate that leaves a device out is refused at successor check 8 as
`projection-mismatch`, unless an earlier check refuses it. No further refusal
kind exists for it.

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
check 8). The one byte of a retained device's entry that can change without an
operation naming the device is its `update_authority`, and only when its
principal's role changes (step 6). The epoch number, the key epoch, the
predecessor commitment and the writer are not operations; successor checks 2, 4
and 9 govern them.

A device removed and admitted again in the same batch is not a refresh. The
batch is refused (successor check 8), whether the device is admitted under the
same binding or under another binding with the same identity key (group-epochs-decisions.md, Open decision
D-13). To bring a removed binding back, a later epoch admits it as an ordinary
admission, with evidence the caller's freshness rule accepts, and it receives no
key material of any earlier key epoch.

A principal leaves the group when a batch removes every one of its devices and
admits none for it. Leaving the group, or asking to be removed, is not an
operation: it has no effect until an authorised writer commits the removal.

## Policy version 1

Policy version 1 is an owner, admin and member baseline. It is content of this
page, not a product's private rule, because the baseline for accepting a
candidate must not depend on which product evaluates it (group-epochs-decisions.md, Open decision D-3). A
product may add constraints of its own through the policy verdict, which can
only refuse; it cannot remove these.

The roles are 1 owner, 2 admin and 3 member. They are exclusive, and every
principal has exactly one. Exactly one principal is the owner. A device has
`update_authority` 1 exactly when its principal is an owner or an admin. This
is the authority mapping of version 1.

The rules use roles in `P` only. A role, an authority flag or an operation in
the candidate never authorises the candidate itself. The rules of `P`'s
`policy_version` govern successor check 10. Only version 1 exists in this draft,
and a candidate changes the version in force only by `set_policy`, which an
owner writes. A lesser role therefore cannot reach `unsupported`: its
`set_policy` is `writer-role-insufficient`, and a header that changes the
version without one is a `projection-mismatch`. A former owner that the head has
demoted to admin is a lesser role in the head but an owner in the head's
predecessor. For a sibling of the head, whose `P` is that predecessor, it can
therefore still cause `unsupported`, with no change of state. A sibling that
another of its devices writes, one that did not write the head, is refused as
`removed-by-head` once it has passed every check, and one that the head's own
writer writes is ranked against the head by commitment (group-epochs-siblings.md, Siblings, Owner
devices). A sibling is not a successor of the head, so `unsupported` for it
does not stop a coordinator (group-epochs-key-epochs.md, Obligations at the product boundary, 3).

| Operation | Who may write it | Restriction, read in `P` |
|---|---|---|
| `admit_device(a, d)` | an owner; an admin, when `a`'s role in `P` is member (3) or `a` is not a principal of `P` (group-epochs-decisions.md, Open decision D-9) | `a` enters as a member if new; its evidence is checked (successor check 12) |
| `remove_device(a, b)` | an owner; an admin, when `a`'s role in `P` is member (3) (group-epochs-decisions.md, Open decision D-9) | `b` is a member device of `a` in `P` |
| `set_role(a, r)` | an owner | `a` is a principal of `P` other than the owner; `r` is 2 or 3 |
| `transfer_ownership(n, f)` | an owner | `n` is a principal of `P` other than the owner; `f` is 2 or 3 |
| `set_policy(v, c)` | an owner | `v` and `c` are the candidate's `policy_version` and `policy_commitment` (successor check 8). A `v` the verifier does not support gives `unsupported` (successor check 6) |
| `close` | an owner | the only operation in the list |

Further rules:

- The principal that is owner in the result is `P`'s owner unless the list has
  `transfer_ownership`. The owner cannot be removed or demoted except by a
  transfer, which the owner writes.
- A transfer may remove every device of the former owner in the same batch. The
  former owner then leaves the group as the transfer takes effect.
- A closed epoch has no successor, and no operation reopens a group. A close is
  still not final: since it has no successor, a sibling that ranks before it
  displaces it whenever it arrives, and the group is then open at that verifier
  (group-epochs-siblings-forks.md, Siblings, What the order does not resolve).
- An admin cannot promote itself, appoint or demote an admin, transfer
  ownership, change the policy or close the group. Such an operation in a
  candidate that an admin signs is refused, as `writer-role-insufficient` at
  successor check 10 unless an earlier check refuses the candidate first,
  because the rule reads roles in `P`.
- The result has at least one member device under every principal, at least one
  under the owner, and one owner. Each of these follows from `apply` and from
  successor check 7.
