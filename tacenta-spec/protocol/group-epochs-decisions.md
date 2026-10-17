# Group epochs: open decisions and sources

Part of the draft group-epochs.md (the entry page). Status: draft, awaiting review; see group-epochs.md for the review record and what the draft is not.

This part holds Open decisions D-1 to D-13, Related published work and Sources,
and "check N" in it means a successor check of group-epochs-successor.md unless
a genesis or checkpoint check is named.

## Open decisions

The draft's text uses a stated default for each only so that it can be read and
checked as one piece. A default is not a decision made after review. Three
dates appear in the marks below. On 2026-09-29 the maintainer said "go" to a
recommended plan that named D-3, D-7, D-9, D-12 (then option E) and D-13; a mark
"Adopted: X (go of 2026-09-29)" means the recommended default of that plan. On
2026-09-30 the maintainer gave a general instruction to go with the
recommendations; a mark "Adopted: X (instruction of 2026-09-30)" means a
recommended default written to the draft on that instruction. On 2026-10-01 the
maintainer gave an explicit go to option F of D-12; the mark "Adopted: F (go of
2026-10-01)" means that decision. The plan and the instructions are not recorded
in this repository. Seven decisions carry a mark: D-3, D-7, D-9 and D-13 (go of
2026-09-29), D-10 and D-11 (instruction of 2026-09-30), and D-12 (go of
2026-10-01). D-12's option F replaces D, an earlier default of this draft
written under the instruction of 2026-09-30, which had replaced option E, the
option that the plan of 2026-09-29 adopted. In none of these cases has the draft's review taken place yet.
D-7 is adopted for the draft and is to be settled again with measurements before
the encoding is frozen. D-1, D-2, D-4, D-5, D-6 and D-8 keep a default that the
drafter chose and whose review is pending. Adopting a default fixes the choice
the text is written to, and it does not ratify the text.

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
(group-epochs.md, Layers; group-epochs.md, Scope) would leave to the product. Default: C. Adopted: C (go of
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
the candidate before. Under A a sibling of the head is judged with the records
made for its epoch number set aside (group-epochs-successor.md, Accepting a successor, Inputs). Default:
A.

**D-7: full state or a delta.** Options: (A) each epoch carries the full
resulting principals and devices, as this draft writes it; (B) each epoch carries
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
statement standing in the way; and an admin could remove another admin's
device, whose sibling then displaces the removal if it ranks before the
remover (group-epochs-siblings.md, Siblings, Displacement). Under B an admin cannot manage its own
devices, or another admin's, and the owner must write every such change.
Default: B. Adopted: B (go of 2026-09-29). B is narrower than A.

**D-10: aliasing of identity keys among member devices.** Options: (A) two
member devices may not share the same 32 identity-key bytes; (B) they may not
share an X25519 agreement class (session-establishment.md), which also refuses a
respelling of one key. The identity-key check of "Accepting a signed statement"
admits one spelling of a key (a canonical encoding of a point of the prime-order
subgroup), and the verifier applies that rule to the key of every device that
enters accepted state (group-epochs.md, The accepted state, Identity keys in accepted state). So
no member device holds a respelling of another's key, and option A suffices;
option B would add a comparison of agreement classes to a rule that already
leaves one spelling of each key. Default: A. Adopted: A (instruction of
2026-09-30). Keys are compared as bytes (check 7). The rule that the byte
comparison relies on is merged text and not a pending one: "Accepting a signed
statement" admits exactly one spelling of an identity key, and "Identity keys"
says where a party applies it. session-establishment.md makes the same argument
for a session: it compares the peer's identity key by bytes, because an identity
key has one canonical spelling. Not part of the adoption: that the verifier
applies the rule itself at check 12 and does not rely on the caller's acceptance
procedure for it. Its cost is one subgroup test per new device, and a candidate
whose new device key fails the rule is `invalid-identity-key` where the
procedure alone would give `evidence-refused`.

**D-11: joining or resuming from an epoch after genesis.** This draft defines
acceptance only against an accepted predecessor. A device that joins at epoch
`n` needs an anchor for epoch `n`. Options: (A) it verifies the whole chain from
genesis; (B) it accepts a checkpoint that an authorised writer of epoch `n`
signed, trusting that writer's identity key as ASM-14 describes; (C) it accepts
a checkpoint carried in an authenticated invitation. Default: C. Adopted: C
(instruction of 2026-09-30), as a stated trust assumption: the joiner trusts its
inviter for the checkpoint (group-epochs-genesis-and-joining.md, Joining from a checkpoint, Trust assumption). Not
chosen: A's cost grows with the whole history of the group, since a joiner would
fetch and verify every epoch since genesis, with the evidence each needs, and
the chain grows with every change to the group. B is not a trust root: a
checkpoint signed by a writer of epoch `n` is judged against nothing the joiner
holds, and an attacker can sign a self-consistent epoch that lists itself. C
trusts the inviter, which a joiner does anyway, and the draft says so. The
adoption fixes the choice and not the text. The section is new and is awaiting
review, and these parts of it are drafting choices made under C, not part
of what was adopted: the checkpoint's two parts (a pinned commitment and the
epoch), its seven checks, the identity-key check on its devices, the refusals
`already-started` and `invalid-identity-key`, the rule that a verifier that
holds state refuses a checkpoint, so that a device that resumes from one starts
a new verifier, and the acceptance of a genesis epoch as a checkpoint under the
same checks plus the two rules of Genesis (group-epochs-genesis-and-joining.md) that need no evidence. The choice does
not settle the invitation, whose form and authentication are the product's.

**D-12: two valid epochs for one slot.** Options: (A) any valid sibling of the
head is a conflict: the verifier sets a marker, accepts nothing more, and
nothing clears the marker; (B) as A, but the marker stops only proposing and
distributing, and the verifier keeps accepting successors of the head; (C)
choose deterministically between the siblings by commitment order, which
requires a verifier to replace an epoch it has accepted; (D) as A, except that
a sibling whose writer is not in the head's authority set is refused and sets
no marker; (E) as D, and a successor of the head signed by a device of the
head's owner principal clears the marker in the step that accepts it; (F)
ordered siblings, as Siblings (group-epochs-siblings.md) writes it: there is no marker, and while the head
has no accepted successor, a sibling of the head that passes every check
displaces the head if it ranks before it, by the role and the position in the
predecessor of the device that wrote it and, between two epochs of one device,
by commitment, and is refused as `outranked` otherwise; except that, when the
sibling and the head were written by two different devices of the owner's
principal and the head removes or demotes the sibling's writer, the sibling is
refused as `removed-by-head` whatever its rank; and the verifier returns the
hint `possible-fork`, which has no effect, beside `superseded`, and beside
`missing-predecessor` at a checkpoint head, for a candidate whose predecessor is
the epoch it holds for the number before. Default: F. Adopted: F (go of
2026-10-01).

Not chosen. Under A and D one valid sibling stops a verifier for good, and
under E until a device of the owner's principal clears it. An authority device
one epoch behind, a second device of one account that proposes the same change,
a retry, or a service that kept the losing epoch of a race, and anyone who
delivers that epoch's bytes, without a key, stops every verifier that holds the
head and receives both. A stopped verifier tells no user, and
an authority that an owner removes stops, with one epoch of its own, the
verifiers that receive that epoch first, which then never accept the removal.
D adds to A only that a writer the head removed cannot stop a verifier that
accepted the removal first. E's clear does not bring a group together: it moves
the cleared verifier onto a branch that diverges from every peer that kept
going, the peers' next admin-signed epoch is refused there or stops it again,
and a verifier on the other branch has no clear. Under B no verifier is
stopped, but each keeps the sibling it saw first, so any race splits the group,
silently. Under C a writer that can vary its body can try bodies until its
commitment is the lowest and so win every race; F orders writers by their place
in the predecessor, which no body changes, and uses the commitment only between
one device's own epochs. What F gives up: an accepted epoch is final only once
it has a successor; a writer that ranks first can undo, at depth one, the epoch
of any writer that ranks after it, except as Owner devices (group-epochs-siblings.md) says; and a fork
deeper than one epoch still splits a group (group-epochs-siblings-forks.md, Siblings, What the order does not
resolve). F keeps D's refusal of a sibling whose writer the head removed only
between two devices of the owner's principal. Under policy version 1 an admin
that the head removed was removed by the owner, whose devices rank first, so the
rank already refuses its sibling. Between the owner's devices the rank alone
would let a lost or stolen device that ranks first undo its own removal and
remove the others; the refusal stops the removed device's own sibling where the
removal arrived first, but not an honest device that ranks before the remover
and that the removal leaves in place, and it makes the outcome depend on the
order of arrival when the removed device ranks before its remover, mutual
removal included (group-epochs-siblings.md, Siblings, Owner devices). Whether to extend the refusal to a
sibling that still lists a device the head removed is open, and F does not. The
hint gives an operator something to count; it is not authenticated and fires
without a fork too (group-epochs-siblings-forks.md, Siblings, Fork hint).

History. Option E was adopted (go of 2026-09-29). An earlier revision of this
draft, which was awaiting review, was written to D in place of E under the
instruction of 2026-09-30, and froze a verifier at the first valid sibling of
its head with no way out. F replaces D in the same draft. The draft was
written to F as a recommended default, and the maintainer gave an explicit go to
F on 2026-10-01. Its review is pending. Adopting a default fixes the choice and
does not ratify the text.

**D-13: the same key admitted again in the batch that removes it.** Options: (A)
an `admit_device` naming an identity public key that a `remove_device` in the
same list names is refused, as check 8 writes it; (B) it is allowed, as a
replacement that changes only the `device_id`, and removal is then per binding
in the strict sense. Under B the holder of a removed key is a permitted
recipient of the same epoch that removed it. Under A a replacement that keeps
its key and changes its `device_id` takes two epochs. Default: A. Adopted: A (go
of 2026-09-29).

## Related published work

RFC 9420, The Messaging Layer Security (MLS) Protocol (IETF, July 2023), is
named here because it is published work on group messaging. This draft states
nothing about what it covers or how it relates to this draft.

This draft has not been compared with RFC 9420, and it quotes no text of it. This
repository does not record what the drafter had read of it before writing, so
independence from it is not shown. A comparison is required before the key
engine is fixed. Until a person has made it, from the RFC itself, this draft
makes no statement about how its epochs relate to MLS.

The Signal Private Group System (Chase, Perrin and Zaverucha, IACR ePrint
2019/1416) is listed in group-messaging.md, Published material, which says what
it covers. This draft has not been compared with it either.

## Sources

- identities-and-devices.md: the `DeviceBinding` encoding, the inventory
  statement, XEdDSA signing and verification, "Accepting a signed statement",
  and "Identity keys".
- group-messaging.md: the two group commitment labels this draft's labels stay
  prefix-free against; and "Published material", which Related published work
  points to for the Private Group System.
- RFC 3629, UTF-8 (IETF, 2003): the definition of UTF-8 that the Account term
  (group-epochs.md) uses. Tier `fact` (CONSTANTS.md: standards).
- RFC 9420 and IACR ePrint 2019/1416: named under Related published work only.
  This draft cites no rule, field or check as taken from either.
- session-establishment.md: the X25519 agreement class, for option B of Open
  decision D-10, which is not chosen.
- error-handling.md: what is left to an implementation (group-epochs-successor.md, Accepting a successor,
  Results and The checks).
- CONSTANTS.md: the provenance tiers named under Constants (group-epochs.md).
- README.md, "Normative status": the standing named in the status paragraph (group-epochs.md);
  and README.md at the root of the repository, "Development assistance", which
  the dependency note (group-epochs.md) cites for how changes are prepared.
- ASSURANCE.md, row 7: the review requirement of the main branch, cited in the
  review record (group-epochs.md) and the dependency note (group-epochs.md).
- tacenta-core/LABELS.md: the registered labels this draft's labels stay
  prefix-free against, and where the labels are not yet registered.
- threat-model/: ADV-01, ADV-02, ADV-04, ADV-05, ADV-06; ASM-03, ASM-07, ASM-11,
  ASM-12, ASM-14; EX-04, EX-07, EX-09, EX-11.
- ADR-0003, ADR-0006 and ADR-0008: the research boundary, the
  specification-first rule and the review rule this draft is subject to.

Apart from the sections of this specification and the standard listed above,
this draft cites no source for any field, label, bound, rule or check. Whether
any published document or implementation also supplies one has not been
checked, and that check is needed before the draft is ratified. ADR-0003 says
that its policy binds every contributor and every tool used to make a change,
and this repository records no statement of what the drafter had read or been
given, so the draft does not show that it is independent of RFC 9420 or of any
implementation.
