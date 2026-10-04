# Group epochs: accepting a successor

Part of the draft group-epochs.md (the entry page). Status: draft, awaiting review; see group-epochs.md for the review record and what the draft is not.

This part holds Accepting a successor: Inputs, Results (every result and refusal
kind) and The checks, and "check N" in it means one of the twelve successor
checks below unless a genesis or checkpoint check is named.

## Accepting a successor

### Inputs

A verifier decides on a candidate from these inputs, and from nothing else:

- its accepted state (`head`, `prior`, `index`);
- the candidate's bytes;
- the offering mode: whether the caller offers an epoch as a candidate or as a
  checkpoint (group-epochs-genesis-and-joining.md, Joining from a checkpoint). It decides which list of checks judges
  the epoch. An epoch whose `predecessor_tag` is 0, offered as a candidate, is
  judged under Genesis (group-epochs-genesis-and-joining.md) and needs evidence for every device; offered as a
  checkpoint, it is judged by the checks of Joining from a checkpoint (group-epochs-genesis-and-joining.md), which
  need none. An epoch whose `predecessor_tag` is 1, offered as a candidate, is
  judged by the checks of this section, and by a verifier with no head it is
  `missing-predecessor`; offered as a checkpoint, it is judged by the checks of
  Joining from a checkpoint (group-epochs-genesis-and-joining.md). The mode also changes the kind that a verifier with
  a head gives to an epoch of its own group that it has not accepted: offered as
  a checkpoint it is `already-started`, and offered as a candidate it is judged
  by its position (a genesis epoch is `superseded`);
- the policy versions it supports (check 6). The signature rule and the
  identity-key rule (group-epochs-encoding.md, Signature; Identity keys) are fixed by
  identities-and-devices.md and are not inputs;
- the evidence: a set of signed inventory statements;
- the inventory acceptance procedure, supplied by the caller: for a signed
  statement and an account, it applies "Accepting a signed statement"
  (identities-and-devices.md), including the caller's issuer-key binding, its
  freshness rule and its binding and statement policies, and whether the
  candidate is being evaluated live or replayed from history (group-epochs-decisions.md, Open decision
  D-6). The procedure has no effect of its own on the caller's records, as that
  section requires of its freshness check: a candidate can still be refused on a
  later principal's evidence, so the caller records the generation of each
  statement as seen only when the candidate has passed every check, that is,
  when it is `accepted` or `displaced`, or is a sibling refused as `outranked`
  or `removed-by-head`. That record is the atomic step the section describes,
  which evaluates the caller's freshness rule again against the value then
  stored. If it now refuses a statement of the candidate, the candidate is
  `refused(evidence-refused)` and no generation of it is recorded. The
  re-evaluation of every statement, the recording of every generation and the
  durable step of Effects (group-epochs-successor-effects.md) are one atomic step: if any statement is refused, none
  is recorded and nothing else changes (Obligations at the product boundary, 9 (group-epochs-key-epochs.md),
  says how a product whose stores are separate keeps that). For a sibling of the
  head, the caller's freshness rule judges each statement, at check 12 and in
  that atomic step, as it would if no generation had been recorded for a
  candidate with the head's epoch number; so the caller keeps, with each
  generation it records, the group and the epoch number of the candidate it was
  recorded for. Those records are set aside only in that judgement: they stay
  recorded, and no stored value is lowered (group-epochs-siblings.md, Siblings, Evidence of a sibling);
- optionally, a policy verdict (group-epochs-successor-effects.md, below).

The decision is a function of these inputs, with the caller's inventory
acceptance procedure taken as it stands when the check runs. The store that the
procedure reads is not part of the verifier's accepted state: other uses of the
same procedure can write it, so two verifiers with the same accepted state and
the same bytes can differ (group-epochs-decisions.md, Open decision D-6). Whether a candidate is evaluated
live or replayed is an input too. This draft does not say who sets it, or that a
coordinator may not, and whoever sets it chooses whether the freshness rule can
refuse a stale statement. This draft reads no clock (ASM-11), no directory, and
no position or timestamp a service attached to the candidate. A caller's
freshness rule is an input, and may itself read one. For genesis and for a
checkpoint the anchor the caller supplies is an input as well.

### Results

| Result | Meaning | Effect on accepted state |
|---|---|---|
| `accepted` | The candidate is the new head. | `head` and `prior` are replaced, and `index` gains the candidate's entry, together. |
| `displaced` | The candidate is a sibling of the head that passes every check, ranks before the head and is not refused by the rule for owner devices (group-epochs-siblings.md, Siblings, Owner devices). It is the new head in the head's place. | `head` and the `index` entry for its number are replaced together; `prior` is unchanged. |
| `duplicate` | The candidate is, by commitment, an epoch already accepted and not displaced (an entry of `index`). The signature bytes are not examined. | None. |
| `missing-predecessor` | The candidate's predecessor is not an accepted epoch here: a gap, or another branch. | None. The verifier must obtain the predecessor before it can decide, except for a sibling of a checkpoint head, which it does not wait to judge (check 2). Anyone can produce this result from any bytes, so it is not by itself evidence of a gap (group-epochs-key-epochs.md, Obligations at the product boundary, 3). |
| `unsupported` | The candidate, signed by an owner of its predecessor, sets a policy version this verifier does not implement. | None. It is not evidence that the candidate is invalid: the verifier has judged only checks 1 to 5 and the conditions of check 6. It cannot decide until it supports the version. Its coordinator does not propose or distribute while this is the only successor of the head that it has seen, and that ends when the verifier supports the version, which judges the candidate afresh, or when it accepts another successor of its head. Only an owner of the predecessor can cause it (check 6), so neither an unauthenticated candidate nor a lesser role can. For a genesis epoch or a checkpoint it is returned after the anchor (genesis check 4, checkpoint check 4). |
| `refused(kind)` | The candidate fails a check, or, as `refused(outranked)` or `refused(removed-by-head)`, is a sibling of the head that passes every check and does not displace the head (group-epochs-siblings.md, Siblings). | None. For `outranked` and `removed-by-head` the caller records the generations of the candidate's statements (Inputs); that record is not accepted state. |

A kind named without `refused(...)` (`malformed`, `wrong-group`,
`anchor-mismatch`, `bad-signature` and the others in Decoding (group-epochs-encoding.md), Genesis (group-epochs-genesis-and-joining.md), Joining
from a checkpoint (group-epochs-genesis-and-joining.md) and The checks) is the kind of a `refused` result.
`duplicate`, `displaced`, `missing-predecessor` and `unsupported` are results of
their own. When a sibling of the head and the head have the same writer, the
verifier gives the caller both signed epochs with the result, `displaced` or
`refused(outranked)` (group-epochs-siblings-forks.md, Siblings, Equivocation). Beside `refused(superseded)`, and
beside `missing-predecessor` in one case, the verifier can also return the hint
`possible-fork` (check 2; group-epochs-siblings-forks.md, Siblings, Fork hint). The hint is not a result or a
refusal kind, and no result depends on it.

The table lists every result and every refusal kind that this draft names, the
checks that produce it, and what its condition reads at most: the candidate's
bytes (bytes), also the verifier's accepted state (state), or also an input of
the caller (input). The names are the spellings this draft uses. Whether a
conforming implementation must report them is not decided here (The checks).

| Name | Produced by | Reads |
|---|---|---|
| `accepted` | the end of each of the three lists, when every check passed and, for the successor list, `P` is the head | every check of the list |
| `duplicate` | successor check 2; genesis check 2; checkpoint check 2 | state |
| `displaced` | the end of the successor list, when `P` is `prior` | every check of the list, and the head's writer, operations and commitment (input) |
| `missing-predecessor` | successor check 2 | state |
| `unsupported` | successor check 6; genesis check 4; checkpoint check 4 | input (the supported versions) |
| `malformed` | check 1 of each of the three lists (group-epochs-encoding.md, Decoding) | bytes |
| `wrong-version` | check 1 of each of the three lists (group-epochs-encoding.md, Decoding) | bytes |
| `non-canonical` | check 1 of each of the three lists (group-epochs-encoding.md, Decoding) | bytes |
| `wrong-group` | successor check 2; genesis check 2; checkpoint check 2 | state |
| `superseded` | successor check 2; genesis check 2 | state |
| `already-started` | checkpoint check 2 | state |
| `anchor-mismatch` | genesis check 3; checkpoint check 3 | input (the anchor) |
| `invalid-roles` | successor check 7; genesis check 5; checkpoint check 5 | bytes |
| `authority-mismatch` | successor check 7; genesis check 5; checkpoint check 5 | bytes |
| `duplicate-device` | successor check 7; genesis check 5; checkpoint check 5 | bytes |
| `writer-not-authorised` | successor check 4; genesis check 6; checkpoint check 6, for a genesis epoch | state at successor check 4, bytes at the others |
| `bad-signature` | successor check 5; genesis check 7; checkpoint check 6 | bytes |
| `invalid-identity-key` | successor check 12; genesis check 8; checkpoint check 7 | bytes |
| `group-closed` | successor check 3 | state |
| `conflicting-operations` | successor check 8 | bytes |
| `unknown-target` | successor check 8 | state |
| `already-member` | successor check 8 | state |
| `projection-mismatch` | successor check 8 | state |
| `key-epoch` | successor check 9 | state |
| `writer-role-insufficient` | successor check 10 | state |
| `target-protected` | successor check 10 | state |
| `verdict-mismatch` | successor check 11 | input (the verdict) |
| `verdict-denied` | successor check 11 | input (the verdict) |
| `evidence-missing` | successor check 12; genesis check 8 | input (the evidence) |
| `evidence-mismatch` | successor check 12; genesis check 8 | input (the evidence) |
| `evidence-refused` | successor check 12; genesis check 8; the recording step under Inputs | input (the acceptance procedure and the store it reads) |
| `outranked` | the end of the successor list, when `P` is `prior` | every check of the list, and the head's writer, operations and commitment (input) |
| `removed-by-head` | the end of the successor list, when `P` is `prior`, the writers of the candidate and the head are two different devices of the owner's principal, and the head removes or demotes the candidate's writer (group-epochs-siblings.md, Siblings, Owner devices) | every check of the list, and the head's writer and operations (input) |

That is five results besides `refused`, and 28 refusal kinds. Where several
kinds can apply, the order of the checks decides which is reported. At successor
check 12, `invalid-identity-key` reads bytes, but it is reached only after the
evidence conditions for the same principal have passed, so the evidence decides
whether it is reported.

A refusal is terminal for the same state and the same inputs: the same bytes are
refused the same way. A result or a kind marked state can change when the
verifier accepts, or learns of, another epoch, so the order in which epochs
reach a verifier can change it. A result or kind that depends on an input of the
caller can change when that input changes: `anchor-mismatch`, `unsupported`, the
refusals of successor checks 11 and 12 (`verdict-mismatch`, `verdict-denied`,
`evidence-missing`, `evidence-mismatch`, `evidence-refused`, and
`invalid-identity-key`, which reads bytes but is reached only after the evidence
conditions of its principal), and the results of the end of the successor list.

### The checks

A candidate whose `predecessor_tag` is 0 is a genesis candidate and is judged
under Genesis above (group-epochs-genesis-and-joining.md) from its second check on. (An epoch with `predecessor_tag` 0
that the caller offers as a checkpoint is not a candidate; Joining from a
checkpoint (group-epochs-genesis-and-joining.md) judges it.) For any other candidate the checks run in the order
below. The verifier stops at the first that fails and returns its result. In
this draft the order is fixed: it decides which result is returned and which
state effect goes with it, and, among refusals, which kind is reported. Whether
a conforming implementation must report the same refusal kind where several
apply is not decided here: error-handling.md leaves the choice of reported
refusal to an implementation unless a page fixes an order because it is
observable in a way that matters. The order places every result that has an
effect after the checks that an unauthenticated candidate fails: a candidate
that is not canonical, or has not passed checks 4 and 5, cannot displace the
head and cannot cause `unsupported`, and check 6 lets only an owner of `P` cause
`unsupported`. A sibling is ranked against the head only after it has passed
every check, check 12 included (group-epochs-siblings.md, Siblings).

Arithmetic in the checks is over unbounded integers, so an epoch numbered
2^64 - 1, or with a `key_epoch` of 2^64 - 1, has no successor. Within a check
the conditions are tried in the order listed, and where a condition ranges over
principals, devices or operations it is tried over them in encoding order
(principals, then each principal's devices, then operations); the first that
fails decides. Where a check names a loop (check 10: each operation; check 12:
each principal), that loop is the outer one: all its conditions are tried for
one item before the next item. Elsewhere each condition is tried over all its
items before the next condition.

1. **Decode.** As Decoding above (group-epochs-encoding.md): `malformed`, `wrong-version` or
   `non-canonical`.
2. **Group and position.** With no head, `missing-predecessor`. Otherwise let
   `n` be the head's epoch number and `m` the candidate's. The candidate's
   `group_id` equals the head's, else `wrong-group`. Then:
   - `m` = `n` + 1: if `predecessor_commitment` is `index[n]`, the predecessor
     is the head; otherwise `missing-predecessor`;
   - `m` = `n`: if `predecessor_commitment` is `index[n - 1]`, the candidate is
     a `duplicate` when its commitment is `index[n]`, and is otherwise a
     sibling of the head, judged against `prior` in the checks below and
     ranked against the head after them (group-epochs-siblings.md, Siblings); if it is not
     `index[n - 1]`, `missing-predecessor`;
   - `m` < `n`: a `duplicate` when the candidate's commitment is `index[m]`,
     otherwise `refused(superseded)`. The verifier does not judge a competing
     epoch for a slot the chain has passed, whatever its rank (group-epochs-siblings.md, Siblings). When
     `index[m - 1]` is held and the candidate's `predecessor_commitment` is
     `index[m - 1]`, the verifier also returns the hint `possible-fork`
     (group-epochs-siblings-forks.md, Siblings, Fork hint);
   - `m` > `n` + 1: `missing-predecessor`.

   In the checks below `P` is the predecessor this selects: the head for a
   successor, `prior` for a sibling. A candidate with `predecessor_tag` 1 has
   `m` >= 1, so `index[n - 1]` exists whenever `m` = `n`, unless the head is the
   checkpoint the verifier started from.

   An entry of `index` that is not held is never equal to a candidate's
   commitment (group-epochs.md, The accepted state). While the head is the checkpoint (group-epochs-genesis-and-joining.md, Joining
   from a checkpoint), `prior` is absent and `index[n - 1]` is not held. For
   that head the case `m` = `n` above is replaced by this: a `duplicate` when
   the candidate's commitment is `index[n]`, and otherwise
   `missing-predecessor`, with the hint `possible-fork` when the candidate's
   `predecessor_commitment` is the head's own `predecessor_commitment`
   (group-epochs-siblings-forks.md, Siblings, Fork hint). The head's predecessor is not an accepted epoch here,
   so no sibling of the head can be judged, and the verifier does not wait to
   judge one: that is a limit and not a gap. The other cases read as written,
   and a candidate numbered below the checkpoint is `refused(superseded)`. When
   a successor of the checkpoint has been accepted, `prior` is the checkpoint
   and `index` holds its entry, and every case reads as written.
3. **Closure.** `P`'s `closure_state` is 0, else `refused(group-closed)`.
4. **Writer authority.** The principal of `P` whose account is
   `writer_account` lists a device whose `binding` equals `writer_binding` byte
   for byte and whose `update_authority` is 1, else
   `refused(writer-not-authorised)`. The candidate's own authority set is not
   consulted, and the writer need not be listed in the candidate: a device may
   sign the epoch that removes it. For a sibling of the head `P` is `prior`, so
   a writer that the head removed is still judged by its authority in `prior`,
   and its rank decides what its sibling does, except that a device of the
   owner's principal that another such device removed or demoted in the head
   is refused at the end of the list (group-epochs-siblings.md, Siblings, Owner devices; group-epochs-decisions.md, Open decision
   D-12).
5. **Signature.** As Signature above (group-epochs-encoding.md), else `refused(bad-signature)`.
6. **Profile.** Let `v` be the candidate's `policy_version`. The check passes if
   the verifier supports `v`. Otherwise the result is `unsupported` when all
   three hold: the list has exactly one `set_policy`; that operation names `v`
   and the candidate's `policy_commitment`; and the principal of `P` whose
   account is `writer_account` has role 1. When they do not all hold, the check
   passes without judging `v`, and the candidate goes on to be refused. `P`'s
   version is supported (it was accepted under this check, or under genesis
   check 4 or checkpoint check 4), so an unsupported `v` reaches a
   header only through a `set_policy`. A header that is not what `apply` gives
   is refused at check 8, and a `set_policy` written by a principal that is not
   an owner is refused at check 10. It follows from these checks, as this page
   reads them, that no candidate that names an unsupported version is accepted
   and that an admin cannot force `unsupported` with any header or operation
   list. No model or test states this.
7. **Shape.** Of the candidate's own principals: exactly one has role 1, else
   `refused(invalid-roles)`; every device's `update_authority` equals 1 when its
   principal's role is 1 or 2 and 0 otherwise, else
   `refused(authority-mismatch)`; no two member devices, under any principal,
   have the same `identity_public_key` bytes (compared as bytes: Open decision
   D-10 (group-epochs-decisions.md), and Identity keys in accepted state (group-epochs.md)), and no `device_id` occurs twice
   under one principal, else `refused(duplicate-device)`.
8. **Operations.**
   - `refused(conflicting-operations)` if: a device binding is named by more
     than one `admit_device` or `remove_device` (so a device removed and
     admitted again in one list is refused); an `admit_device` names an identity
     public key that a `remove_device` in the list also names (group-epochs-decisions.md, Open decision
     D-13); there is more than one `transfer_ownership` or more than one
     `set_policy`; a principal is named by more than one `set_role` or
     `transfer_ownership`; or `close` is listed with any other operation. The
     clause on a principal named by more than one `set_role` or
     `transfer_ownership` can be read as one count over both kinds, or as a
     count within each kind. The readings differ for a list that names one
     principal in a `set_role` and in a `transfer_ownership`, and this draft does
     not say which is meant; this point is open.
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
     `update_authority` on its own is `authority-mismatch` at successor check 7,
     which runs first.
9. **Key epoch.** `key_epoch` equals `P`'s `key_epoch` plus 1, else
   `refused(key-epoch)` (group-epochs-decisions.md, Open decision D-2). A `P` whose `key_epoch` is
   2^64 - 1 has no successor, so every candidate for it is refused here.
10. **Policy.** Each operation, in list order, satisfies Policy version 1 (group-epochs-encoding.md) with
    roles read in `P`: first the writer's role, then the target. The results are
    `refused(writer-role-insufficient)` where an operation needs an owner and
    the writer is not one; and `refused(target-protected)` where an admin's
    `remove_device` or `admit_device` names an owner's or an admin's principal
    (group-epochs-decisions.md, Open decision D-9), or where `set_role` or `transfer_ownership` names the
    owner.
11. **Verdict.** If the caller supplies a policy verdict, its
    `prior_commitment` is `P`'s commitment and its `candidate_commitment` is the
    candidate's, else `refused(verdict-mismatch)`; and its result is `allow`,
    else `refused(verdict-denied)`.
12. **Evidence.** A device is new if the candidate lists it and `P` does not
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
    accepts the statement for that account, else `refused(evidence-refused)`;
    for a sibling of the head, the procedure judges it with the records made for
    the head's epoch number set aside (Inputs). The verifier applies the
    identity-key rule itself and does not rely on the procedure for it (group-epochs.md, The
    accepted state, Identity keys in accepted state). Devices the candidate
    retains keep the generation and commitment they were admitted with and need
    no evidence. Evidence for an account that has no new device is neither
    required nor examined.

The order decides which kind a candidate with several faults gets. Check 7
judges the candidate's own principals before check 8 compares them with
`apply`, so a kind of check 8 or 10 is reached only by a candidate that passes
check 7. A lone `set_role` naming the owner is `invalid-roles` if the candidate
reflects `apply` (it has no owner) and `projection-mismatch` if it does not, and
check 10's `target-protected` for it is reached only when the list also
transfers ownership. An `admit_device` naming a binding that `P` lists under
another account is `duplicate-device` if the candidate reflects `apply` (two
devices with one key), and `already-member` if it omits the device from its
first account.

If every check passes, the result is `accepted` when `P` is the head. When `P`
is `prior`, the candidate is a sibling of the head that passes every check
against the head's predecessor, and the verifier compares it with the head
(group-epochs-siblings.md, Siblings). When the writers of the candidate and of the head are two different
devices of the owner's principal in `P`, and the head removes or demotes the
candidate's writer, the result is `refused(removed-by-head)` (group-epochs-siblings.md, Siblings, Owner
devices). Otherwise the verifier compares the candidate's rank with the head's
(group-epochs-siblings.md, Siblings, Rank): the result is `displaced` when the candidate ranks before the
head, and `refused(outranked)` otherwise. When the candidate and the head have
the same writer, the verifier gives the caller both signed epochs with the
result (group-epochs-siblings-forks.md, Siblings, Equivocation).
