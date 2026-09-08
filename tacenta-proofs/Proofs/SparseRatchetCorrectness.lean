/-
Proofs.SparseRatchetCorrectness: functional properties of the sparse
post-quantum ratchet's model (proof tier T2).

Two kinds of statement, and the second is why this file exists.

The first kind says the ratchet is *correct*: a key stored when a message was
skipped is the key an in-order receive would have derived, so a message that
arrives late is still readable. That is the whole purpose of storing them and it
is the property a test can only sample.

The second says the ratchet is *bounded*. The total bound on the store is this
implementation's addition: the per-call bound and epoch retirement are the
specification's, and the total cap is added so the store's size is bounded
independently of how many messages are skipped within an epoch.
`Model.SparseRatchet` records this. Having added a bound, proving it holds is
the minimum; a bound that is
checked in three places and true in general is worth less than one that is
checked once and proved.
-/
import Model.SparseRatchet

namespace Proofs.SparseRatchetCorrectness

open Model.SparseRatchet
open Model.State (Key)

/-! ## What a skipped batch contains

`deriveInto` is the private recursion `skipMessageKeys` uses. These are its three
facts: how many keys it produces, what they are numbered, and that each is the
key the chain would have produced in order. -/

/-- Skipping `c` steps stores exactly `c` keys. -/
theorem deriveInto_length (ck : Key) (start c : Nat) :
    (skipMessageKeys.deriveInto ck start c).2.length = c := by
  induction c generalizing ck start with
  | zero => rfl
  | succ c ih => simpa [skipMessageKeys.deriveInto] using ih (kdfCk ck (start + 1)).1 (start + 1)

/-- Every stored key is numbered above where the walk started. -/
theorem deriveInto_num_gt (ck : Key) (start c : Nat) :
    ∀ x ∈ (skipMessageKeys.deriveInto ck start c).2, start < x.1 := by
  induction c generalizing ck start with
  | zero => simp [skipMessageKeys.deriveInto]
  | succ c ih =>
    intro x hx
    have h : (skipMessageKeys.deriveInto ck start (c + 1)).2
        = (start + 1, (kdfCk ck (start + 1)).2)
          :: (skipMessageKeys.deriveInto (kdfCk ck (start + 1)).1 (start + 1) c).2 := rfl
    rw [h, List.mem_cons] at hx
    rcases hx with rfl | hx
    · omega
    · have := ih (kdfCk ck (start + 1)).1 (start + 1) x hx
      omega

/-- And no higher than where it stopped. -/
theorem deriveInto_num_le (ck : Key) (start c : Nat) :
    ∀ x ∈ (skipMessageKeys.deriveInto ck start c).2, x.1 ≤ start + c := by
  induction c generalizing ck start with
  | zero => simp [skipMessageKeys.deriveInto]
  | succ c ih =>
    intro x hx
    have h : (skipMessageKeys.deriveInto ck start (c + 1)).2
        = (start + 1, (kdfCk ck (start + 1)).2)
          :: (skipMessageKeys.deriveInto (kdfCk ck (start + 1)).1 (start + 1) c).2 := rfl
    rw [h, List.mem_cons] at hx
    rcases hx with rfl | hx
    · omega
    · have := ih (kdfCk ck (start + 1)).1 (start + 1) x hx
      omega

/-- The numbers are distinct, so a batch is a map on its own. -/
theorem deriveInto_nodup (ck : Key) (start c : Nat) :
    (skipMessageKeys.deriveInto ck start c).2.Pairwise fun a b => a.1 ≠ b.1 := by
  induction c generalizing ck start with
  | zero => simp [skipMessageKeys.deriveInto]
  | succ c ih =>
    have h : (skipMessageKeys.deriveInto ck start (c + 1)).2
        = (start + 1, (kdfCk ck (start + 1)).2)
          :: (skipMessageKeys.deriveInto (kdfCk ck (start + 1)).1 (start + 1) c).2 := rfl
    rw [h, List.pairwise_cons]
    refine ⟨?_, ih (kdfCk ck (start + 1)).1 (start + 1)⟩
    intro b hb
    have := deriveInto_num_gt (kdfCk ck (start + 1)).1 (start + 1) c b hb
    omega

/-! ## A stored key is the key an in-order receive would derive

The property the store exists for, and the one a test can only sample. Everything
above counts and numbers the batch; this says what is *in* it.

`chainAfter` walks the chain the way `deriveInto` does, from the front. Written
the other way -- advancing from the end -- it would describe the same sequence
and not be the same term, and the induction would not go through. -/

/-- The chain key after `i` steps, walking from the front. -/
def chainAfter (ck : Key) (start : Nat) : Nat → Key
  | 0 => ck
  | i + 1 => chainAfter (kdfCk ck (start + 1)).1 (start + 1) i

/-- The message key an in-order receive derives at offset `i`. -/
def keyAt (ck : Key) (start i : Nat) : Key :=
  (kdfCk (chainAfter ck start i) (start + 1 + i)).2

/-- The `i`-th key a skip stores is numbered `start + 1 + i` and is exactly the
key an in-order receive would have derived there.

This is what makes out-of-order delivery work: a message that arrives late is
decrypted with the same key it would have been decrypted with had it arrived on
time. -/
theorem deriveInto_get (ck : Key) (start c i : Nat) (h : i < c) :
    (skipMessageKeys.deriveInto ck start c).2[i]! = (start + 1 + i, keyAt ck start i) := by
  induction c generalizing ck start i with
  | zero => omega
  | succ c ih =>
    have hd : (skipMessageKeys.deriveInto ck start (c + 1)).2
        = (start + 1, (kdfCk ck (start + 1)).2)
          :: (skipMessageKeys.deriveInto (kdfCk ck (start + 1)).1 (start + 1) c).2 := rfl
    cases i with
    | zero => simp [hd, keyAt, chainAfter]
    | succ i =>
      have hlt : i < c := by omega
      rw [hd]
      simp only [List.getElem!_cons_succ]
      rw [ih (kdfCk ck (start + 1)).1 (start + 1) i hlt]
      simp only [keyAt, chainAfter]
      -- The two sides differ only in how the index is associated.
      have harith : start + 1 + 1 + i = start + 1 + (i + 1) := by omega
      rw [harith]

/-! ## The store stays bounded

The bound we added, proved rather than sampled. `skipMessageKeys` either rejects
or returns a store within the cap, whatever it was given -- including a store
already over the cap, which it cannot make worse because it refuses. -/

/-- A successful skip leaves the store within the total bound.

The interesting case is a request inside `maxSkip` that the total check
refuses. -/
theorem skipMessageKeys_store_bounded (st : State) (e upto : Nat) (st' : State)
    (h : skipMessageKeys st e upto = some st') :
    st'.skipped.length ≤ max st.skipped.length maxSkippedStore := by
  unfold skipMessageKeys at h
  split at h
  · exact absurd h (by simp)
  · rename_i cs _
    split at h
    · exact absurd h (by simp)
    · rename_i ch _
      split at h
      · injection h with h'; subst h'; exact Nat.le_max_left _ _
      · split at h
        · exact absurd h (by simp)
        · split at h
          · exact absurd h (by simp)
          · injection h with h'
            subst h'
            simp only [setChains, List.length_append, List.length_map,
              deriveInto_length]
            -- Written with `==` rather than `decide (· = ·)`: the two are the
            -- same proposition and not the same term, and the goal uses this one.
            have hfil := List.length_filter_le
              (fun x : Nat × Nat × Key =>
                !(x.1 == e && decide (ch.n < x.2.1) && decide (x.2.1 ≤ upto)))
              st.skipped
            rename_i hcap _
            simp only [Nat.not_lt] at hcap
            omega

/-- Retiring old epochs never grows the store. Trivial, and worth stating
because the bound above is only half the argument: the other half is that
nothing else adds to it. -/
theorem clearOldEpochs_store_le (st : State) (e : Nat) :
    (clearOldEpochs st e).skipped.length ≤ st.skipped.length := by
  simpa [clearOldEpochs] using List.length_filter_le _ _

/-- Taking a stored key never grows the store either. -/
theorem trySkipped_store_lt (st : State) (e n : Nat) (r : State × Key)
    (h : trySkipped st e n = some r) :
    r.1.skipped.length ≤ st.skipped.length := by
  unfold trySkipped at h
  split at h
  · exact absurd h (by simp)
  · injection h with h'
    subst h'
    simpa using List.length_filter_le _ _

/-! ## The store is a map

The same invariant the Double Ratchet's store needed, and needed for the same
reason: both the lookup and the deletion assume one entry per key, and nothing
in the shape of an association list enforces it. Here the key is the pair of
epoch and message number. -/

/-- No two entries share an epoch and a message number. -/
def StoreIsMap (l : List (Nat × Nat × Key)) : Prop :=
  l.Pairwise fun a b => ¬(a.1 = b.1 ∧ a.2.1 = b.2.1)

/-- A successful skip leaves the store a map, given it was one.

Three parts, as before: what survives the replacement is still a map, the new
batch is one on its own, and the two cannot collide. The third is why
`skipMessageKeys` filters before appending rather than simply appending, and it
is what stops a peer that returns to a chain from making one pair hold two
keys. -/
theorem skipMessageKeys_preserves_map (st : State) (e upto : Nat) (st' : State)
    (hpre : StoreIsMap st.skipped)
    (h : skipMessageKeys st e upto = some st') :
    StoreIsMap st'.skipped := by
  unfold skipMessageKeys at h
  split at h
  · exact absurd h (by simp)
  · rename_i cs _
    split at h
    · exact absurd h (by simp)
    · rename_i ch _
      split at h
      · injection h with h'; subst h'; exact hpre
      · split at h
        · exact absurd h (by simp)
        · split at h
          · exact absurd h (by simp)
          · injection h with h'
            subst h'
            simp only [setChains, StoreIsMap]
            rw [List.pairwise_append]
            refine ⟨hpre.filter _, ?_, ?_⟩
            · -- the batch shares an epoch, and its numbers are distinct
              have hnd := deriveInto_nodup ch.ck ch.n (upto - ch.n)
              refine List.Pairwise.map _ ?_ hnd
              intro a b hab
              simp only
              rintro ⟨-, hn⟩
              exact hab hn
            · -- what survived was outside the replaced range; the batch is inside
              intro a ha b hb
              simp only [List.mem_filter] at ha
              simp only [List.mem_map] at hb
              obtain ⟨hamem, hakeep⟩ := ha
              obtain ⟨y, hy, rfl⟩ := hb
              simp only [Bool.not_eq_true', Bool.and_eq_false_iff,
                beq_eq_false_iff_ne, decide_eq_false_iff_not] at hakeep
              intro ⟨hep, hn⟩
              have hlo := deriveInto_num_gt ch.ck ch.n (upto - ch.n) y hy
              have hhi := deriveInto_num_le ch.ck ch.n (upto - ch.n) y hy
              simp only at hep hn
              have hup : ch.n + (upto - ch.n) = upto := by
                rename_i hle _ _
                simp only [Nat.not_le] at hle
                omega
              rw [hup] at hhi
              rcases hakeep with hk | hk
              · rcases hk with hk | hk
                · exact hk hep
                · omega
              · omega

end Proofs.SparseRatchetCorrectness
