import Translation.SpqrT3

/-!
# The statement of the sparse skip's refinement, pinned

`Tacenta.SpqrT3.skip_message_keys_refines` says the translated
`State.skip_message_keys` computes `Model.SparseRatchet.skipMessageKeys`,
refusals included, under the hypotheses it lists. Since the total bound counts
the store a skip leaves (`sparse-pq-ratchet.md`, The store also has a total
bound), the same statement means a different thing: the model it refers to
changed, and the theorem's own text did not. A pin on the axiom list cannot see a
change to a hypothesis or to the conclusion, and a hypothesis nothing satisfies
would leave the theorem true and empty, so this file holds the whole statement.
The arithmetic hypotheses are `hroom` and `hskiproom`; neither is new here. For a
state `State::from_bytes` returns they follow from the decoded-state invariant
(`Tacenta.ImportInv.Spqr.inv_gives_chain_room` and `inv_gives_skip_room`), which
`CLAIMS.md` records. The conclusion's refusal case, `r.2 = s`, says that a
refused skip leaves the state as it was.

The three-leaf and Session units carry copies generated from this theorem by
`scripts/port-unit-proofs.sh` and `scripts/port-session-unit-proofs.sh`, whose
`--check` modes refuse any other text, so this one pin covers all three. It is
here and not in `SpqrT3.lean`, which those scripts copy: a pin's expected text
is the pretty-printer's output, which differs between the leaf and the unit.
-/

/--
info: Tacenta.SpqrT3.skip_message_keys_refines (hkr : Tacenta.SpqrT3.SpqrHkdfAgrees)
  (hz64 : Tacenta.SpqrT3.ZeroizingRoundTrips64) (hret : Tacenta.SpqrT3.VecRetainAgrees)
  (hret_total : Tacenta.SpqrT1.VecRetainTotal) (hz : Tacenta.SpqrT1.ZeroizeTotal)
  (hopt : Tacenta.SpqrT1.OptionCloneTotal) {s : tacenta_spqr.State} {m : Model.SparseRatchet.State}
  (hrel : Tacenta.SpqrT3.StateRefines s m) (e upto : Aeneas.Std.U64) (hroom : (↑s.chains).length < Aeneas.Std.Usize.max)
  (hskiproom : (↑s.skipped).length + ↑tacenta_spqr.MAX_SKIP ≤ Aeneas.Std.Usize.max) :
  Aeneas.Std.WP.spec (s.skip_message_keys e upto) fun r =>
    match Model.SparseRatchet.skipMessageKeys m ↑e ↑upto with
    | none => ∃ err, r.1 = Aeneas.Std.core.result.Result.Err err ∧ r.2 = s
    | some m' => r.1 = Aeneas.Std.core.result.Result.Ok () ∧ Tacenta.SpqrT3.StateRefines r.2 m'
-/
#guard_msgs in
#check Tacenta.SpqrT3.skip_message_keys_refines
