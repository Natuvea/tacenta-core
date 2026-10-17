# Group epochs: what is not checked or claimed

Part of the draft group-epochs.md (the entry page). Status: draft, awaiting review; see group-epochs.md for the review record and what the draft is not.

This part holds What is not checked, and what is not claimed, and "check N" in
it means a successor check of group-epochs-successor.md unless a genesis or
checkpoint check is named.

## What is not checked, and what is not claimed

The checks above do not establish, and nothing in this draft claims, any of the
following.

- **Equivocation.** An authorised writer can send different valid successors
  to different verifiers. A verifier sees that only when it receives two of them
  while one is its head: it then gives its caller the pair and keeps the one
  that ranks first (group-epochs-siblings-forks.md, Siblings, Equivocation). It does not see it when both rank
  after its head, when it has already accepted a successor (`superseded`), or
  when it receives only one. Siblings from different writers are not
  equivocation and are not reported.
- **Availability and agreement.** No sibling stops a verifier: a sibling never
  leaves a verifier refusing the successors of its head. One stale authority
  device, a replayed losing epoch, a retry, or a second device of one account
  that proposes the same change leaves no verifier refusing the successors of
  its head because of a sibling. It leaves no two verifiers on different heads
  when the siblings reach each of them before a successor of any of them does,
  a condition that no verifier can detect, outside the case of owner devices
  below: each ends on the sibling that ranks first, and the writer of the other
  proposes again (group-epochs-key-epochs.md, Obligations at the product boundary, 6). The draft claims no
  more than that. A sibling that arrives after a successor of its head is
  `superseded`, so a race in which some verifiers accept a successor of the
  sibling that ranks second before the first arrives leaves the group on two
  branches for good, and nothing here brings them together (group-epochs-siblings-forks.md, Siblings, What the
  order does not resolve). A verifier on the branch that the rest of the group
  does not follow goes on answering `missing-predecessor` to the others' epochs,
  which for its user is a stop. How often that happens depends on how soon an
  authority proposes after it accepts a head and on the delays of the network.
  Obligations at the product boundary, 6 and 8 (group-epochs-key-epochs.md), make it less frequent, and
  nothing in this draft bounds it. A network that shows different verifiers
  different siblings first, and holds back the one that ranks first until a
  successor of another exists, can split a group when it chooses. Verifiers
  whose callers, verdicts or supported policy versions judge one sibling
  differently end on different heads, and so do verifiers that receive in
  different orders a removal or demotion of a device of the owner's principal by
  another that ranks after it and a sibling of the removed device, and verifiers
  of which only one receives a replay of a sibling that the other refused
  (group-epochs-siblings.md, Siblings, Owner devices). And a head is not final until a successor of it is
  accepted, so a writer that ranks first can undo, at depth one, the epoch of
  any writer that ranks after it, as often as that writer proposes (group-epochs-siblings.md, Siblings,
  Rank), except that a device of the owner's principal cannot undo, at a
  verifier that accepted it first, an epoch of another such device that removes
  or demotes it (group-epochs-siblings.md, Siblings, Owner devices). The positions are not even: the
  writer that ranks first needs one delivery, its sibling, and the writer that
  ranks after it needs two, its epoch and a successor of it, accepted before
  that sibling arrives. Between devices of the owner's principal that is not so
  for a removal or a transfer: a device of any rank needs one delivery, the
  removal, before the sibling of the device it removes (group-epochs-siblings.md, Siblings, Owner
  devices).
- **Removal of an admin.** An admin that an owner removes can still keep
  chosen verifiers from accepting its removal. Let `C` be the owner's epoch that
  removes it, and `S` another successor of the same head that the admin writes,
  even an epoch with no operation. `C` ranks before `S`, since the
  owner's devices rank before every admin's, so a verifier that receives both
  before it accepts a successor of either ends on `C`, whichever came first. But
  the admin can write a successor `S2` of `S` at once, and a verifier that
  accepts `S` and `S2` before `C` arrives answers `C` with `superseded`: the
  removed admin stays a member device of its head and a permitted recipient
  there (group-epochs-key-epochs.md, Obligations on the key engine, 2), and nothing here brings that
  verifier back. A network that delivers `S` and a successor of it first,
  written by any authority whose verifier accepted `S`, does the same without
  the removed admin's help. The removal invariant says nothing of these
  verifiers. What the rank changes is that the admin now needs a successor of
  its own sibling at those verifiers before the removal arrives; a sibling
  alone is not enough. A removed device of the owner's principal is another
  case, since its sibling can rank before the removal: Siblings, Owner devices (group-epochs-siblings.md),
  and Recovery, below.
- **Cadence.** A writer with authority can write an epoch with no operation.
  Under Open decision D-2, option A (group-epochs-decisions.md), that starts a new key epoch and the
  redistribution after it, and nothing in this draft limits how often an
  authority device writes one. A writer can also displace its own head, at one
  slot, with another epoch whose commitment is lower, as often as it can make
  and sign one: each displacement retires the head's material and starts a
  redistribution, the epoch number does not advance, and each gives the caller
  an equivocation pair. Nothing here limits that either. A product's verdict
  can refuse such a sibling (group-epochs-successor-effects.md, Policy verdict), and verifiers whose verdicts
  differ then end on different heads.
- **Silence.** A group that has split across branches gives no signal to a
  user on this draft's rules. A split shows only as `missing-predecessor` or
  `superseded`, which a gap, a delay or a replay also causes. The hint
  `possible-fork` beside them is returned for a split, and also for a late
  losing sibling, a replay and bytes that anyone can make, so it is not a
  signal of a split on its own (group-epochs-siblings-forks.md, Siblings, Fork hint). A displacement is
  returned to the caller as `displaced`, and equivocation as a pair of signed
  epochs with a result (group-epochs-siblings-forks.md, Siblings, Equivocation); nothing requires the product to
  show either. A verifier on one branch keeps the key material of its head
  current (group-epochs-key-epochs.md, Obligations on the key engine, 3), and peers on the other branch do
  not accept that traffic as current.
- **Catching up.** A device that has been away accepts the epochs it missed by
  judging each of them again, and under the default freshness rule (group-epochs-decisions.md, Open
  decision D-6, option A) that can stall for good. The caller's freshness rule
  can refuse a generation that the caller has already recorded for the account,
  for example from another group or a pairwise flow. A stored generation never
  decreases (identities-and-devices.md, Accepting a signed statement,
  freshness), so the same bytes with the same evidence are refused again as
  `evidence-refused`, and the epochs after that one are `missing-predecessor`.
  The same rule lets an account holder's own action (raising a generation) make
  some verifiers refuse an in-flight epoch as `evidence-refused` and others
  accept it. The draft names a replay input to the freshness rule (group-epochs-successor.md, Inputs) and
  gives no criterion for setting it. It does not say who may set it, and whoever
  sets it chooses whether a statement older than a revocation is accepted. It
  also does not say who keeps the historical statements that a replay needs, or
  the issuer-key bindings that signed them: the procedure reads those as they
  stand when the check runs, and a binding that no longer resolves makes the
  epoch `evidence-refused`.
- **Unsupported versions.** An owner can write a policy version that some
  verifiers do not implement (`unsupported`); they stop, and a group that goes
  on without them is on another branch from them. The owner's epoch need not be
  valid in any other respect for that: check 6 runs before checks 7 to 12, so an
  owner's candidate with such a `set_policy` and a wrong `key_epoch`, or with an
  `admit_device` and no evidence, is `unsupported` too. `unsupported` can be a
  circular wait. Its exit is that the verifier supports the version or accepts
  another successor of its head (group-epochs-successor.md, Results). While `unsupported` is the only
  successor of the head that a verifier has seen, its coordinator proposes
  nothing (group-epochs-key-epochs.md, Obligations at the product boundary, 3), so if every verifier in the
  group answers `unsupported`, no coordinator may propose, no other successor
  appears, and the draft provides no exit. A verifier keeps nothing when it
  answers `unsupported` (group-epochs-successor-effects.md, Effects), so judging the candidate afresh needs the
  product to hold it. The draft gives an owner no way to learn which versions the
  member devices support: the only capability bit is `GROUP_EPOCH_V1`, so a move
  to a second policy version has no negotiation, and a device that does not
  support it stops at `unsupported`. Nothing here bounds how long an unsupported
  policy version, a gap or a missing statement keeps a group from progressing.
- **Retention and re-offer.** A verifier keeps nothing about a candidate it has
  not accepted. When it answers `missing-predecessor`, the product has to keep
  the candidate and offer it again after the predecessor is accepted, and this
  draft does not say for how long, in what order, or how many. A candidate cannot
  be authenticated before its predecessor is accepted, because authority is read
  from the predecessor, so a product that buffers holds unauthenticated bytes,
  each up to 2,167,845 bytes, with no bound that this draft states. The order in
  which a backlog is offered can decide the head. With siblings A and B, where B
  ranks before A and the rule for owner devices does not refuse B, and C a
  successor of A, a verifier that is offered A, B, C ends on B and answers C
  `missing-predecessor`, and one that is offered A, C, B ends on C and answers B
  `superseded`. Two products that offer a backlog in different orders end in
  different states on the same bytes.
- **Freshness.** A verifier decides against the head it has. It cannot know of
  a successor it has not received. A withheld successor is undetected, and a
  removed device can go on using what it holds with any peer that has not
  accepted the removal.
- **The chain before a checkpoint.** For a verifier that started from a
  checkpoint, everything listed under What a joiner cannot verify (group-epochs-genesis-and-joining.md, Joining from
  a checkpoint). It takes the checkpoint's state from the inviter, and claims
  nothing about the epochs before it.
- **Order.** The order or position a service assigns never authorises a
  candidate, and never decides between siblings (group-epochs-siblings.md, Siblings). A service that
  refuses a second proposal for one predecessor (group-epochs-key-epochs.md, Obligations at the product
  boundary, 8) gains no authority either, and a service that does not keep to
  that is not detected.
- **`duplicate`.** `duplicate` is decided from the commitment alone, and the
  commitment excludes the signature (group-epochs-encoding.md, Commitment), so bytes that carry an
  accepted epoch's body and a corrupt signature are `duplicate`. It is not
  evidence that the bytes are valid. A caller that stores or forwards bytes it
  has been told are duplicates can pass on the corrupt signature, and a joiner
  given such bytes as a checkpoint is protected only by checkpoint check 6. A
  store or negative cache keyed by commitment alone that keeps the first copy it
  sees lets whoever delivers a body first, with a garbage signature, take the
  place of the genuine copy: the verifier answers `bad-signature`, and a product
  that drops later copies of that commitment as repeats never offers the genuine
  one. The draft does not require the caller to keep the signature it accepted
  first.
- **Results before the signature.** Successor checks 2 to 4 return their results
  before the signature is examined: `wrong-group`, `missing-predecessor`,
  `duplicate`, `superseded`, `group-closed` and `writer-not-authorised` are
  given for bytes that nobody has authenticated. A product that shows these
  results to a sender, or to a peer that probes, tells it which epoch is the
  head, whether the group is closed, and which pairs of account and binding are
  authority devices of the head or of `prior`. The hint `possible-fork`
  (group-epochs-siblings-forks.md, Siblings, Fork hint) is also returned before the signature is examined: a
  prober who sends bytes with a chosen epoch number and predecessor commitment
  learns from it whether that commitment is the one the verifier holds for the
  number before, or, at a checkpoint head, the predecessor of the checkpoint.
  The anonymity non-claim covers the roster only.
- **Delivery.** That a recipient has received an epoch, that a removed device
  has learned of its removal, or that any message reached anyone.
- **Recall.** Anything a removed device already received: plaintext,
  ciphertext, key material, or the accepted epochs it saw; and the same for a
  device that only a displaced epoch admitted (group-epochs-key-epochs.md, Obligations on the key engine,
  5).
- **Traffic under retired material.** Obligations on the key engine (group-epochs-key-epochs.md, 3) leaves
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
- **Aliasing.** Removal is per exact binding. Keys are compared as bytes (group-epochs-decisions.md, Open
  decision D-10, option A adopted). That relies on the verifier applying the
  identity-key rule to the key of every device that enters accepted state, and
  on the rule admitting one spelling of a key (group-epochs.md, The accepted state, Identity keys
  in accepted state). On that premise two member devices of one epoch cannot
  hold one key under two spellings. A later epoch can still admit a removed key
  again under another binding, and that is another member device (group-epochs-decisions.md, Open decision
  D-13).
- **Inventory.** That an inventory statement is current or complete, or that its
  issuer is honest. A compromised issuer can list a device for an account. It
  cannot admit that device: only an epoch written by an authorised writer does.
  Under Open decision D-9 (group-epochs-decisions.md, adopted B) an admin can write an admission only for a
  member principal or for a new principal, which enters as a member, so an admin
  and a compromised issuer together can add a member device that has no
  authority in the epoch that admits it. An owner writes the epoch that gives a
  principal authority, and that epoch gives it to every device already under the
  principal, including one added earlier (`apply`, step 6). Currency is not
  checked either. A revocation in an account's inventory does not remove a
  device from a group, and a service that carries evidence (ADV-01, ADV-04) can
  serve a statement older than a revocation. A caller whose freshness rule (group-epochs-decisions.md, Open
  decision D-6) accepts it lets a writer admit a device that the account has
  since revoked. For a successor that rule is the caller's. For a sibling of the
  head it is not only the caller's: this draft sets aside the records made for
  the slot (group-epochs-siblings.md, Siblings, Evidence of a sibling), so a sibling can be accepted on a
  statement older than one that this verifier recorded for another sibling of
  the same slot, including a statement from before a revocation that the
  recorded one carried, and the revoked device then becomes a member device of
  the head. That is a cost of making the head independent of the order of
  arrival (apart from the case of Owner devices (group-epochs-siblings.md)). Its limit is that records made
  for other slots, for other groups and by other uses of the procedure still
  apply.
- **Promotion and re-entry.** `set_role` and `transfer_ownership` name an
  account, not its devices. `apply`, step 6, gives `update_authority` 1 to every
  device under a principal whose role becomes owner or admin, including a device
  that an admin added earlier while the principal was a member, and a device
  whose admission rested on a statement from a compromised issuer. The operation
  lists no devices, so it does not show the owner which devices gain authority.
  Removal is by binding, and a removed device can return under another binding
  if a writer allowed to admit for its account admits one that the account's
  inventory lists (group-epochs-decisions.md, Open decision D-13; Aliasing). When the holder of the removed
  device controls that inventory, as with a stolen phone, only the same-batch,
  same-key case is refused.
- **Chain of custody for a replacement.** That a binding's
  `replacement_predecessor` names any binding. This draft gives it no meaning and
  no check above reads it. The inventory section does not let a verifier refuse
  a statement solely because a replacement's marker names no listed binding, and
  this draft adds no such rule, so a device whose binding carries a marker is
  admitted on the same evidence as any other.
- **Evidence carriage.** Who stores or serves the inventory statements a
  candidate needs. A verifier without them cannot follow the chain past that
  epoch (`evidence-missing`).
- **The evidence set.** Evidence is not signed by the writer, is not committed
  in the epoch and is not authenticated in delivery. Successor check 12 refuses
  a candidate for which the evidence holds more than one signed statement for a
  principal's account (`evidence-mismatch`). A party that delivers the evidence
  can therefore add a second genuine statement for that account, for example an
  older one: the same candidate is refused at the verifiers given that set and
  accepted at those given the clean one, and the refusal costs the verifier the
  work of check 12 up to that point. The refusal is not terminal (group-epochs-successor.md, Results), and
  the draft has no rule for choosing between two statements. Inputs (group-epochs-successor.md) calls the
  evidence a set of signed inventory statements, and the draft does not say how
  an entry is counted that does not decode as a signed statement, that repeats a
  statement with other signature bytes, or whose unsigned preimage equals
  another entry's. Those points are open: this draft fixes no result for them.
- **Anonymity.** An epoch lists account handles and device keys. Whoever holds
  the epoch learns them. Nothing here hides who is in a group.
- **Recovery.** A lost or compromised owner, a compromised admin, or a fork
  between verifiers deeper than one epoch (group-epochs-siblings-forks.md, Siblings, What the order does not
  resolve). A lost or stolen device of the owner's principal holds the owner's
  power until an epoch that removes it has a successor at a verifier. If it is
  faster than the owner's other devices, it can remove them, or transfer
  ownership, and make that final with one more epoch; the owner's other devices
  are then not authority devices of the head, and this draft gives them no way
  back. A removal of it by another of the owner's devices is protected against
  its own sibling at a verifier that accepted the removal first, but not against
  an honest device that ranks before the remover and that the removal leaves in
  place: that device's sibling displaces the removal, and the lost device is
  then a member device with authority of the new head, if that sibling lists it
  (group-epochs-siblings.md, Siblings, Owner devices). Where its own sibling arrived first and it ranks
  before the remover, the removal is `outranked`; and when it and another owner
  device remove or demote each other in one slot, the order of arrival decides
  and the group splits. A compromised device of the owner's principal, of any
  rank, can keep the honest device that ranks first out of a verifier with one
  delivery (group-epochs-siblings.md, Siblings, Owner devices). If the lost device ranks first among the
  owner's devices, it also displaces, at depth one, any epoch of the others that
  does not remove it (group-epochs-siblings.md, Siblings, Displacement). Nothing in this draft lets an
  authority establish its own replacement. A checkpoint is not recovery (group-epochs-genesis-and-joining.md, Joining
  from a checkpoint).
- **Post-quantum authority.** Writer signatures are classical XEdDSA
  signatures (EX-11).
- **Storage.** A verifier whose stored state is rolled back or rewritten
  accepts what its restored state allows (ASM-12; EX-07).
- **The key engine.** That any key engine meets the obligations above. That is
  its specification's and its proof's to show. It also covers what those
  obligations leave out: that a removed device cannot compute the key material
  of a later epoch (group-epochs-key-epochs.md, Obligations on the key engine).
- **Agreement on key material.** An epoch commits to membership, roles, policy
  and closure state, and to a `key_epoch` number. It does not commit to any key
  material. Nothing in this draft makes members check that they hold the same
  material for an epoch, or that an admitted device received what the others
  hold: `key_binding` is a record that each holder keeps (group-epochs-key-epochs.md, Obligations on the key
  engine, 1). A member that gives different recipients different material, or
  gives an admitted device material that no one else holds, breaks no check
  here. What an epoch body commits to is fixed by the encoding.
- **Single points of failure.** Policy version 1 makes some people necessary,
  and the draft does not weigh that. Only an owner adds or removes a device of an
  owner or admin principal, sets a role, transfers ownership, sets the policy or
  closes the group (group-epochs-decisions.md, Open decision D-9, option B). An owner whose devices, at
  most eight, are all lost cannot be replaced: no one can transfer ownership,
  and an admin cannot appoint an admin. An admin who loses a device needs the
  owner to replace it. A member cannot remove its own device, and leaving the
  group is not an operation, so a lost device stays a member device and a
  permitted recipient until an admin or the owner commits its removal. No
  operation undoes a `close`, but a `close` is never final: it has no
  successor, so a sibling written by a device of the owner's principal that
  ranks before the device that wrote it, or by that device with a lower
  commitment, displaces it whenever it arrives; and where a sibling of another
  owner device that removes or demotes the `close`'s writer arrived first, that
  sibling takes effect instead (group-epochs-siblings-forks.md, Siblings, What the order does not resolve).
  Recovery is not specified (Recovery).
- **The atomic step.** The step in which a candidate is accepted, or displaces
  the head, spans three stores: this draft's accepted state, the caller's record
  of the generations it has seen (group-epochs-successor.md, Inputs), and the key engine's retirement of
  the previous head's material. Obligations at the product boundary, 9 (group-epochs-key-epochs.md), gives
  the order and the recovery that this draft requires: accepted state first, the
  caller's record with it or derived from it again on restart, and the key
  engine's current material derived from the head. Without that order, a record
  written before a head that was not kept would make a freshness rule that
  refuses a recorded generation refuse the same epoch for good. Nothing in this
  draft checks that a product keeps the order. How each store is written is the
  product's. A restored backup returns an older head (assumption 1 of the
  removal invariant excludes it), which can be an epoch that a sibling has since
  displaced, and the draft says nothing of what a verifier does after a
  restore.
- **Sizes and costs.** That an epoch of the largest size is affordable to send,
  fetch or verify. The ceiling of 2,167,845 bytes is derived from the bounds and
  is not stated as a test that runs before anything is read, and the number and
  total size of the signed statements in the evidence have no bound in this
  draft, although a verifier has to decode each to see which account it is for.
  The loop over principals is the outer loop of successor check 12, so a
  candidate whose last principal in byte order fails a cheap condition
  (`evidence-missing`, `evidence-mismatch`) has already cost, for every earlier
  principal with new devices, the whole work of the acceptance procedure; the
  draft does not say whether a verifier may remember such a refusal. A sibling is
  ranked only after every check, so a party that replays a sibling that ranks
  after the head, or one that the rule for owner devices refuses, makes the
  verifier do the whole work of checks 1 to 12, the caller's acceptance
  procedure included, each time before it answers `outranked` or
  `removed-by-head`, unless the caller keeps the record of such answers that
  Obligations at the product boundary (group-epochs-key-epochs.md) permits. The size of an epoch does not
  shrink with the size of the change: every epoch carries the full state (group-epochs-decisions.md, Open
  decision D-7), so one operation in a group of 512 principals with eight
  devices each is still at least 352,256 bytes of device entries (4096 devices
  at 86 bytes, a binding without a replacement marker being 45 bytes). A
  verifier keeps `head` and `prior`, each up to the ceiling, and a 32-byte index
  entry for every accepted epoch.
- **What a verifier can show later.** A verifier keeps `head`, `prior` and the
  commitments in `index`, and nothing else. After a displacement it keeps only
  the commitment of the sibling that displaced its head, so it cannot produce
  the displaced epoch that it may have sent traffic under, say which devices
  that epoch listed, or answer which devices could read a message sent under
  it. It reports equivocation only while one of the two epochs is its head
  (group-epochs-siblings-forks.md, Siblings, Equivocation). It keeps nothing that shows that another verifier
  was on another branch. Below `prior` it holds commitments and not epochs, so
  it cannot give a peer the chain to catch up with or show the members in force
  when an earlier message was sent. A product that needs any of these keeps its
  own record of the epochs its verifier held.
