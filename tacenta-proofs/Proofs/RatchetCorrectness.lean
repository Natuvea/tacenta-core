/-
Proofs.RatchetCorrectness: proved functional properties of the Double Ratchet
model (proof tier T2). These are universally quantified theorems about the
model's symmetric-chain derivation and its skipped-key handling, machine-checked
by the Lean kernel (they rest only on `propext` and `Quot.sound`, not on
`native_decide`'s compiler trust). They establish why out-of-order recovery is
correct, the skipped keys are exactly the in-order chain keys, and why the
memory bound is sound, skipping stores exactly the requested number of keys.

The model is imported from tacenta-model; the concrete byte behaviour it derives
is checked separately by the generated vectors in tacenta-test-vectors.
-/
import Model.State

namespace Proofs.RatchetCorrectness

open Model.State

/-- The chain key reached by advancing the symmetric ratchet `n` steps. -/
def advanceCk (ck : Key) : Nat → Key
  | 0 => ck
  | n + 1 => advanceCk (kdfCk ck).1 n

/-- Deriving a chain of `c` steps stores exactly `c` message keys. This is the
    invariant behind the `MAX_SKIP` memory bound: a bounded `upto` stores a
    bounded number of keys. -/
theorem deriveChain_length (ck : Key) (start c : Nat) :
    (deriveChain ck start c).2.length = c := by
  induction c generalizing ck start with
  | zero => rfl
  | succ c ih =>
    show ((start, (kdfCk ck).2) :: (deriveChain (kdfCk ck).1 (start + 1) c).2).length = c + 1
    rw [List.length_cons, ih]

/-- The final chain key after deriving `c` steps is the chain advanced `c`
    times. The starting message number does not affect the chain key. -/
theorem deriveChain_fst (ck : Key) (start c : Nat) :
    (deriveChain ck start c).1 = advanceCk ck c := by
  induction c generalizing ck start with
  | zero => rfl
  | succ c ih =>
    show (deriveChain (kdfCk ck).1 (start + 1) c).1 = advanceCk (kdfCk ck).1 c
    exact ih (kdfCk ck).1 (start + 1)

/-- The `i`-th message key stored by a derivation is the key of the chain
    advanced `i` steps, at message number `start + i`. This is the exact
    statement that a skipped key equals the key an in-order receive would derive,
    which is what makes out-of-order delivery recover the right message. -/
theorem deriveChain_get (ck : Key) (start c i : Nat) (h : i < c) :
    (deriveChain ck start c).2[i]'(by rw [deriveChain_length]; exact h)
      = (start + i, (kdfCk (advanceCk ck i)).2) := by
  induction i generalizing ck start c with
  | zero =>
    match c, h with
    | c + 1, _ =>
      show (start, (kdfCk ck).2) = (start + 0, (kdfCk (advanceCk ck 0)).2)
      rfl
  | succ i ih =>
    match c, h with
    | c + 1, h =>
      have hi : i < c := Nat.lt_of_succ_lt_succ h
      show (deriveChain (kdfCk ck).1 (start + 1) c).2[i]'(by rw [deriveChain_length]; exact hi)
        = (start + (i + 1), (kdfCk (advanceCk ck (i + 1))).2)
      rw [ih (kdfCk ck).1 (start + 1) c hi]
      show (start + 1 + i, (kdfCk (advanceCk (kdfCk ck).1 i)).2)
        = (start + (i + 1), (kdfCk (advanceCk (kdfCk ck).1 i)).2)
      rw [Nat.add_right_comm, Nat.add_assoc]

/-- A successful skip advances `nr` to `upto` and adds `upto - nr` entries to
    the stored-key list, so the list grows by *at most* that many. It succeeds
    only when the request is within `maxSkip` on this chain and the store stays
    within `maxSkippedStore` in total; those two rejections together are the
    memory-safety argument, since a per-chain bound alone would not bound a
    store that a fresh chain per Diffie-Hellman step keeps adding to.

    This is an inequality rather than an equality because storing replaces
    rather than accumulates, so that the store is the map it is documented to be
    (Properties.Invariants). A skip that lands on numbers already held under the
    same ratchet key displaces them, and the store grows by less. The
    inequality is the direction the bound needs. -/
theorem skipMessageKeys_growth (st : State) (ck dhr : Key) (upto : Nat)
    (hckr : st.ckr = some ck) (hdhr : st.dhrPub = some dhr)
    (hlo : st.nr < upto) (hhi : upto ≤ st.nr + maxSkip)
    (hstore : st.skipped.length + (upto - st.nr) ≤ maxSkippedStore) :
    ∃ st', skipMessageKeys st upto = some st'
      ∧ st'.nr = upto
      ∧ st'.skipped.length ≤ st.skipped.length + (upto - st.nr) := by
  have h1 : ¬ (upto ≤ st.nr) := Nat.not_le.mpr hlo
  have h2 : ¬ (st.nr + maxSkip < upto) := Nat.not_lt.mpr hhi
  have h3 : ¬ (maxSkippedStore < st.skipped.length + (upto - st.nr)) :=
    Nat.not_lt.mpr hstore
  simp only [skipMessageKeys, hckr, hdhr, if_neg h1, gt_iff_lt, if_neg h2, if_neg h3]
  refine ⟨_, rfl, rfl, ?_⟩
  simp only [List.length_append, List.length_map, deriveChain_length]
  have := List.length_filter_le
    (fun e => !(e.1 == dhr && decide (st.nr ≤ e.2.1) && decide (e.2.1 < upto)))
    st.skipped
  omega

/-- The store never exceeds its bound: any state `skipMessageKeys` returns has a
    stored-key list within `maxSkippedStore`, given a state that was already
    within it. This is the invariant the bound exists to maintain. -/
theorem skipMessageKeys_store_bounded (st : State) (upto : Nat) (st' : State)
    (hpre : st.skipped.length ≤ maxSkippedStore)
    (h : skipMessageKeys st upto = some st') :
    st'.skipped.length ≤ maxSkippedStore := by
  unfold skipMessageKeys at h
  repeat' split at h
  all_goals
    first
      | (simp at h; done)
      | (injection h with h'
         subst h'
         first
           | exact hpre
           | (simp only [List.length_append, List.length_map, deriveChain_length]
              -- Storing replaces, so what lands in the store is a filtered
              -- prefix of what was there plus the new entries. Let the
              -- predicate come from the goal rather than naming it: it mentions
              -- the ratchet key, which is bound anonymously by the split.
              exact Nat.le_trans
                (Nat.add_le_add_right (List.length_filter_le _ _) _) (by omega)))

end Proofs.RatchetCorrectness
