# Group epochs: the removal invariant

Part of the draft group-epochs.md (the entry page). Status: draft, awaiting review; see group-epochs.md for the review record and what the draft is not.

This part holds The removal invariant (a target, not shown), with its statement,
adversary, assumptions and limits, and "check N" in it means a successor check
of group-epochs-successor.md unless a genesis or checkpoint check is named.

## The removal invariant (a target, not shown)

This section states one property so that a model and a proof can be written
against it. It is a statement of what is to be shown. It is not shown: there is
no model, vector, test or proof for it, `tacenta-proofs/CLAIMS.md` has no entry
for it, and nothing in this draft is a claim of assurance.

The three statements below concern membership acceptance and recipient sets:
which devices a verifier that has accepted an epoch counts as members, who may
be sent key material, and which material is current. They say nothing about
whether a removed device can compute later key material from what it held. That
is the key engine's obligation and is not established here (group-epochs-key-epochs.md, Obligations on the
key engine).

### Statement

Let a verifier make an epoch `C` its head, by accepting it as a successor of
its head or by displacing its head with it (group-epochs-siblings.md, Siblings), where `C`'s operations
include `remove_device` for `r`, one exact device binding, and let `P` be `C`'s
predecessor. Check 8 makes `r` a member device of `P` (an operation that names a
device `P` does not list is `unknown-target`) and makes `r` not a member device
of `C` (a candidate that still lists it does not equal `apply(P, ops)`). The
statement is keyed on the operation and not on the absence of `r` from `C`,
because a statement that only assumed the absence would hold of any checks,
including none. Then, in every later state of the verifier in which `index`
still holds `C`'s commitment:

- **RM-1: no fresh distribution to `r`.** `r` is not a permitted recipient of
  any key material (group-epochs-key-epochs.md, Obligations on the key engine, 2), until an epoch that
  admits `r` by `admit_device` becomes the verifier's head, by acceptance or by
  displacement, on evidence that successor check 12 accepts as Inputs (group-epochs-successor.md) says,
  with the records of a sibling's slot set aside. This is a statement about
  the binding `r`. A device that holds the same key under another binding,
  admitted by a later epoch, is another member device (group-epochs-decisions.md, Open decision D-13).
  Check 7 keeps two member devices of one epoch from holding one key.
- **RM-2: no current use of retired material.** No key material bound to an
  epoch earlier than `C`, or to a sibling of `C` that `C` displaced, is current
  (group-epochs-key-epochs.md, Obligations on the key engine, 3 and 5), which includes every unit of
  material `r` was ever a permitted recipient of. `key_epoch(C)` exceeds the
  `key_epoch` of every epoch before `C` in this verifier's chain in which `r`
  was a member device; a sibling of `C` that the verifier held as its head
  before `C` displaced it has `C`'s `key_epoch`, and its material was retired in
  the step that displaced it (group-epochs-key-epochs.md, Obligations on the key engine, 4). Nothing in this
  draft relabels retired material as current. That no one else can is Obligation
  1's, on the key engine.
- **RM-3: no new dispatch to `r`.** The product does not start a new send,
  distribution or retry addressed to `r`, from stale pending work or otherwise,
  once it has durably committed `C` (group-epochs-key-epochs.md, Obligations at the product boundary, 2).

**What a sibling can undo.** Until the verifier accepts a successor of `C`, a
sibling of `C` that ranks before it displaces it (group-epochs-siblings.md, Siblings), and from that step
`index` no longer holds `C` and the three statements are not made of it. Who can
do that depends on who wrote `C`. If a device of the owner's principal wrote
`C`, only the owner's own devices can: another device of that principal that
ranks before `C`'s writer and that `C` does not remove or demote, or `C`'s
writer with a lower commitment. A device of that principal that `C` removes or
demotes cannot displace `C` (group-epochs-siblings.md, Siblings, Owner devices); where its sibling arrived
before `C`, `C` is `outranked` and never becomes the head, if that device ranks
before `C`'s writer. A device of that principal that ranks before `C`'s writer,
and that `C` neither removes nor demotes, displaces `C` with a sibling even when
`C` removes another device of the principal: the removal did not happen at that
slot, and the removed device is a member device of the new head if that sibling
lists it (group-epochs-siblings.md, Siblings, Owner devices). If an admin wrote `C`, as an admin's removal
of a member device, a sibling written by any device of the owner's principal, by
an admin device that ranks before `C`'s writer, or by `C`'s writer with a lower
commitment displaces it, whether or not that sibling removes `r`. The removal
then did not happen at that slot, `r` is a member device of the new head, and
the proposer has to propose the removal again (group-epochs-key-epochs.md, Obligations at the product
boundary, 6). A removal is therefore final at a verifier only once that verifier
has accepted a successor of `C`. A verifier that accepts a sibling of `C`, and a
successor of that sibling, before `C` arrives answers `C` with `superseded`,
never makes `C` its head, and these three statements are not made of it
(assumption 3).

RM-1 to RM-3 restate obligations. RM-1 follows from Obligations on the key
engine (group-epochs-key-epochs.md, 2) once `r` is not a member device of the head. RM-2 follows from
Obligations on the key engine (group-epochs-key-epochs.md, 3), (4) and (5), and, for its clause on
`key_epoch`, from check 9. RM-3 is Obligations at the product boundary (group-epochs-key-epochs.md, 2). With
assumption 5, that the engine and the product meet their obligations, the three
statements are consequences of those obligations and of `apply`, and they have
little security content beyond them. What the checks add is this: the head moves
by exactly one key epoch (check 9), or keeps its key epoch under another
commitment when a sibling displaces it, so material bound to an earlier epoch is
never current in a later one; a removal cannot be hidden in a batch (check 8);
and, while `C` is held, a removed binding is not a member device again unless a
later epoch admits it with evidence (check 8 and `apply`). The three statements
are about recipient sets and retired material. They are not a statement that a
removed device is excluded from the group's secrets; that depends on the key
engine (group-epochs-key-epochs.md, Obligations on the key engine; What it does not claim).

### Adversary

The adversary chooses the candidate bytes, the evidence and their delivery:
their order, their timing, their replay and their omission. It may be:

- a removed device, holding everything it held while a member (ADV-02, as to
  its state, and ADV-06, as a former peer);
- a network and service that orders, delays, drops and replays (ADV-01) and
  serves a directory that lies (ADV-04);
- a writer in `P`'s authority set, restricted to what policy version 1 lets
  that role write, whose siblings rank by its device's place in `P`.

It cannot forge a signature under a key it does not hold (ASM-03), find a
SHA-256 collision (ASM-07), or write the verifier's storage (ADV-05 is outside
scope).

### Assumptions

1. The verifier's accepted state is durable and is not rolled back or rewritten
   (ASM-12; EX-07).
2. XEdDSA signatures and SHA-256 are as ASM-03 and ASM-07 assume.
3. The verifier has made `C` its head, and `index` still holds `C`'s
   commitment. Nothing is claimed of a verifier that has not, or of one from the
   step in which a sibling displaces `C`.
4. The remaining members run conforming implementations and do not give `r` key
   material or plaintext. This excludes a writer in `P`'s authority set that
   remains a member after `C` from giving `r` key material, although the
   adversary above includes such a writer.
5. The key engine meets Obligations on the key engine (group-epochs-key-epochs.md), and the product meets
   Obligations at the product boundary (group-epochs-key-epochs.md).
6. The caller's inputs to acceptance (the anchor, the issuer binding and the
   freshness rule) are as they intended.
7. For a verifier that started from a checkpoint, the checkpoint is a head that
   the group's members accepted, and its inviter was right about it (group-epochs-genesis-and-joining.md, Joining
   from a checkpoint, Trust assumption). The invariant is stated from the
   checkpoint on.
8. Nothing above is an assumption about how key material is derived. Whether a
   removed device can compute the material of a later epoch from what it held
   is not among the obligations stated in this draft and is not covered by RM-1
   to RM-3.

Assumptions 1 and 2 cite entries of the threat model. Assumptions 3 to 7 are
this page's own, and they are in no register (ADR-0008, rule 2 asks
threat-model/assumptions.md to state what the protocol and the proofs assume).
Item 8 states what no assumption covers and is not an assumption. The
identifiers RM-1 to RM-3 are labels used in this draft and are not requirement
identifiers.

The inventory issuer is not an assumption of RM-1 or RM-2 once `C` is accepted:
removal needs no evidence. The issuer matters to admission, which decides who is
a member device to begin with.

### What it does not claim

- Instant or global revocation. It concerns a verifier that has made `C` its
  head and still holds it.
- Anything about a peer that has not accepted `C`, or an offline device.
- That every verifier makes `C` its head, or keeps it. An authority that `C`
  removes can keep chosen verifiers from ever accepting `C`, by having them
  accept a sibling of `C` and a successor of that sibling before `C` arrives
  (group-epochs-limits.md, Removal of an admin, under What is not checked). Until a verifier accepts
  a successor of `C`, a sibling that ranks before `C` displaces it there (What a
  sibling can undo, above).
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
  It says nothing about whether a device the group removed earlier is absent
  from the checkpoint, which the joiner takes from its inviter.
- Anything across a discard. The invariant is about one verifier for its
  lifetime, not about a device. A device that discards its state and starts from
  a checkpoint is a new verifier, and a checkpoint older than what the device
  once accepted can list a device the group has since removed (group-epochs-genesis-and-joining.md, What a joiner
  cannot verify).
- Removal of a device by key. It is by binding. A later epoch can admit the same
  key under another binding (group-epochs-decisions.md, Open decision D-13; group-epochs-limits.md, Aliasing, under What is not
  checked).

Retained old keys are the limit that matters most. `r` keeps every key it held
at `P`. It can read what it already could, and it can send under retired
material to any peer that has not yet accepted `C`. A peer that has accepted
`C` refuses that material as current (RM-2).
