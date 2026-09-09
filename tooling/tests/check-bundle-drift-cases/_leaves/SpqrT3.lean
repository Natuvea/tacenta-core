-- A stand-in for `Translation/SpqrT3.lean`; see the note in `T3.lean` beside
-- it. Cut to the two theorems the sparse bundle mirrors plus the three
-- declarations the checker's bridges name.
namespace Tacenta.SpqrT3

def chainsEntryOf (p : Std.U64 × Chains) : Nat × Model.SparseRatchet.Chains :=
  (p.1.val, chainsOf p.2)

structure StateRefines (s : State) (m : Model.SparseRatchet.State) : Prop where
  chains : s.chains.val.map chainsEntryOf = m.chains

theorem max_skip_agrees : MAX_SKIP.val = Model.SparseRatchet.maxSkip := by simp

theorem chainCounterBounded_of_real {s : State} {m : Model.SparseRatchet.State}
    (hrel : StateRefines s m) : ChainCounterBounded m.chains := by simp

theorem send_refines (hkr : SpqrHkdfAgrees)
    (hz96 : ZeroizingRoundTrips96) (hz64 : ZeroizingRoundTrips64) (hret : VecRetainAgrees)
    (hz : Tacenta.SpqrT1.ZeroizeTotal) (hopt : Tacenta.SpqrT1.OptionCloneTotal)
    {s : State} {m : Model.SparseRatchet.State} (hrel : StateRefines s m)
    (sending_epoch : Std.U64) (out : Option Output)
    (hepoch : s.epoch.val + 1 < Std.U64.max)
    (hroom : s.chains.val.length + 1 < Usize.max)
    (hcb : ∀ p ∈ s.chains.val, p.1.val + Model.SparseRatchet.epochsKept ≤ Std.U64.max)
    (hsb : ∀ sk ∈ s.skipped.val, sk.epoch.val + Model.SparseRatchet.epochsKept ≤ Std.U64.max)
    (hnewb : ∀ o : Output, out = some o →
      o.key_epoch.val + Model.SparseRatchet.epochsKept ≤ Std.U64.max)
    (hcounter : ∀ p ∈ s.chains.val, ∀ ch : Chain,
      (p.2.send = some ch ∨ p.2.receive = some ch) → ch.n.val < Std.U64.max) :
    State.send s sending_epoch out ⦃ fun r =>
      (∀ n mk, r.1 = core.result.Result.Ok (n, mk) →
        ∃ m', Model.SparseRatchet.send m sending_epoch.val (out.map outputOf)
            = some (m', n.val, keyOf mk)
          ∧ StateRefines r.2 m')
      ∧ (∀ e, r.1 = core.result.Result.Err e →
          Model.SparseRatchet.send m sending_epoch.val (out.map outputOf) = none) ⦄ := by simp

theorem receive_refines (hkr : SpqrHkdfAgrees)
    (hz96 : ZeroizingRoundTrips96) (hz64 : ZeroizingRoundTrips64) (hret : VecRetainAgrees)
    (happ : VecAppendAgrees) (hrm : VecRemoveAgrees) (hz : Tacenta.SpqrT1.ZeroizeTotal)
    (hopt : Tacenta.SpqrT1.OptionCloneTotal)
    {s : State} {m : Model.SparseRatchet.State} (hrel : StateRefines s m)
    (receiving_epoch : Std.U64) (out : Option Output) (n : Std.U64)
    (hepoch : s.epoch.val + 1 < Std.U64.max)
    (hroom : s.chains.val.length + 2 < Usize.max)
    (hcb : ∀ p ∈ s.chains.val, p.1.val + Model.SparseRatchet.epochsKept ≤ Std.U64.max)
    (hsb : ∀ sk ∈ s.skipped.val, sk.epoch.val + Model.SparseRatchet.epochsKept ≤ Std.U64.max)
    (hnewb : ∀ o : Output, out = some o →
      o.key_epoch.val + Model.SparseRatchet.epochsKept ≤ Std.U64.max)
    (hskiproom : s.skipped.val.length + MAX_SKIP.val ≤ Usize.max)
    (hone : (m.skipped.filter (fun x => x.1 == receiving_epoch.val && x.2.1 == n.val)).length ≤ 1)
    (hcounter : ∀ p ∈ s.chains.val, ∀ ch : Chain,
      (p.2.send = some ch ∨ p.2.receive = some ch) → ch.n.val < Std.U64.max) :
    State.receive s receiving_epoch out n ⦃ fun r =>
      match Model.SparseRatchet.receive m receiving_epoch.val (out.map outputOf) n.val with
      | none => ∃ err, r.1 = core.result.Result.Err err
      | some (m', k) => ∃ key, r.1 = core.result.Result.Ok key ∧ keyOf key = k ∧
          StateRefines r.2 m' ⦄ := by simp

end Tacenta.SpqrT3
