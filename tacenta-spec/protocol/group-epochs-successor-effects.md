# Group epochs: effects and the policy verdict

Part of the draft group-epochs.md (the entry page). Status: draft, awaiting review; see group-epochs.md for the review record and what the draft is not.

This part holds Effects and Policy verdict, the end of Accepting a successor,
and "check N" in it means a successor check of group-epochs-successor.md unless
a genesis or checkpoint check is named.

### Effects

- **accepted.** One durable step sets `prior` to the old head, `head` to the
  candidate with its signature and `index[m]` to its commitment, and retires the
  old head's key material; the caller records the generations of the
  candidate's statements in the same step (group-epochs-successor.md, Inputs).
- **displaced.** One durable step sets `head` to the candidate with its
  signature and `index[m]` to its commitment, leaves `prior` as it was, and
  retires the displaced head's key material (group-epochs-key-epochs.md, Obligations on the key engine, 4
  and 5), and the caller records the generations of the candidate's statements
  in the same step (group-epochs-successor.md, Inputs). The displaced epoch is no longer accepted state.
- **outranked, removed-by-head.** Accepted state does not change. The caller
  records the generations of the candidate's statements (group-epochs-successor.md, Inputs).
- **every other result.** Nothing changes. Nor does the hint `possible-fork`
  change anything (group-epochs-siblings-forks.md, Siblings, Fork hint).

The step for `accepted` and `displaced` spans three stores: accepted state, the
caller's record and the key engine's material. The order in which they are
written, and how a verifier recovers from a failure part-way, are in
Obligations at the product boundary, 9 (group-epochs-key-epochs.md).

### Policy verdict

A product whose policy is stricter than version 1 supplies a verdict. It is an
input to accepting a successor only (check 11). Genesis (group-epochs-genesis-and-joining.md) and Joining from a
checkpoint (group-epochs-genesis-and-joining.md) have no predecessor for it to name, and a product narrows those by
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
rules are its own; nothing in this draft proves that a candidate met them.

A verdict is requested at check 11, before check 12 applies the identity-key
rule to the new device keys and examines the evidence. A product's verdict code
therefore sees candidates whose new keys have not passed the rule and whose
evidence is unverified. identities-and-devices.md, Accepting a signed statement,
applies the key rule to every entry before its policies for that reason. The
verdict also applies to a sibling, like any candidate (check 11), so a product
can refuse a sibling that would displace its head. Two products that differ in
this end on different heads for one group, and the draft does not say that a
product should or may do it.
