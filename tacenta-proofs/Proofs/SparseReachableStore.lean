/-
Proofs.SparseReachableStore: on every state the sparse ratchet's model reaches
from `init`, no stored key is at or past its chain's counter, and the store is
within the total bound (proof tier T2, about the model).

`sparse-pq-ratchet.md`, Receiving, says that a skip stores numbers up to one
below the message's number and the receive then moves the counter to the
message's number, so no operation leaves a key stored past its chain's counter;
and The store also has a total bound says that, on a state the operations
produced, the deletion of a skip's step 2 removes nothing, so the count of its
step 3 is the length of the store. This file proves both of
`Model.SparseRatchet`:

* `KeysBelowCounter`: every stored key's epoch has a receiving chain and the
  key's number is below that chain's counter. `init` meets it; `send`,
  `receive`, `advance`, the optional advance that opens a send or a receive
  (`receiveAdvance`), `trySkipped`, `evictOldest` and `clearOldEpochs` keep it;
  the four that may open an epoch (`advance`, `receiveAdvance`, `send`,
  `receive`) need `ChainsNotAhead` too (no chain held for an epoch past the
  current one), which `init` meets and `advance`, `send` and `receive` keep;
* a skip alone keeps only the non-strict form, `KeysAtMostCounter` (no key past
  its counter), since the last key it stores is at the new counter; from the
  strict form it leaves every key below its counter except that the skipped
  epoch's keys may reach it, and `receive`'s last step moves the counter past
  them;
* on a state with no key past its counter, the keys a skip from the counter
  keeps are the whole store (`skipSurvivors_eq_of_keysAtMostCounter`);
* `send`, `receive` and `evictOldest` keep the store within `maxSkippedStore`;
* over any list of the three public operations (a send, a receive, an
  eviction), each refused one leaving the state it was given, all three facts
  hold of every state reached from `init` (`run_reachableStore`,
  `reachable_keysBelowCounter`, `reachable_store_bounded`,
  `reachable_skipSurvivors_eq`), and the bound alone holds of every state
  reached from any state within it (`run_store_bounded`).

The one-step forms take the invariant (and, for the bound, a store already
within it) as a hypothesis; the forms over a sequence from `init` take none. The
witnesses show the statements
have content: a reached state holding two stored keys
(`witness_reachable_holds_stored_keys`, the trace of the vector
`bob-stores-skipped-keys`); a state with a key past its counter, which fails
the predicate and on which a skip deletes that key
(`witness_store_past_its_counter_fails`); a skip that leaves a key at its
counter (`skip_alone_leaves_a_key_at_the_counter`); and an advance that breaks
the strict form from a state with a chain ahead of the current epoch
(`chainsNotAhead_needed_for_advance`).

## What it does not show

* anything about the Rust: `tacenta-spqr`'s operations are tested for the same
  property (`no_operation_leaves_a_stored_key_at_or_past_its_chain_counter`),
  and no theorem composes these results with the refinement theorems;
* that a state read from storage has no key at or past its counter: the
  reader accepts one that has (ADR-0007, the vector
  `stored-key-past-its-counter`), and the results about the counter over a
  sequence start from `init`;
* the bound across the Session's operations, its eviction and retry, or its
  import, which no theorem here states;
* that a caller keeps its own copy when an operation is refused: `run` models
  a refused operation as leaving the state it was given, which is what the page
  asks of a caller and not something this file checks;
* that the store is a map, that the stored keys are the right keys, or any
  property of a key's bytes.
-/
import Proofs.SparseReplacementBound

namespace Proofs.SparseReachableStore

open Model.SparseRatchet
open Model.State (Key)

/-! ## The invariant -/

/-- Every stored key's epoch has a receiving chain, and the key's number is
below that chain's counter. -/
def KeysBelowCounter (st : State) : Prop :=
  ∀ x ∈ st.skipped, ∃ cs ch, findChains st x.1 = some cs ∧ cs.receive = some ch ∧ x.2.1 < ch.n

/-- The same with the key allowed at the counter itself: no stored key is past
its chain's counter. -/
def KeysAtMostCounter (st : State) : Prop :=
  ∀ x ∈ st.skipped, ∃ cs ch, findChains st x.1 = some cs ∧ cs.receive = some ch ∧ x.2.1 ≤ ch.n

/-- No chain is held for an epoch past the state's current one. -/
def ChainsNotAhead (st : State) : Prop :=
  ∀ p ∈ st.chains, p.1 ≤ st.epoch

/-- The general form the proofs carry: below the counter, or at it for an epoch
`atOk` admits. -/
def KeysUpTo (atOk : Nat → Prop) (st : State) : Prop :=
  ∀ x ∈ st.skipped, ∃ cs ch, findChains st x.1 = some cs ∧ cs.receive = some ch ∧
    (x.2.1 < ch.n ∨ (atOk x.1 ∧ x.2.1 = ch.n))

theorem keysBelowCounter_iff (st : State) :
    KeysBelowCounter st ↔ KeysUpTo (fun _ => False) st := by
  constructor
  · intro h x hx
    obtain ⟨cs, ch, h1, h2, h3⟩ := h x hx
    exact ⟨cs, ch, h1, h2, Or.inl h3⟩
  · intro h x hx
    obtain ⟨cs, ch, h1, h2, h3⟩ := h x hx
    refine ⟨cs, ch, h1, h2, ?_⟩
    rcases h3 with h3 | ⟨h3, -⟩
    · exact h3
    · exact h3.elim

theorem keysAtMostCounter_iff (st : State) :
    KeysAtMostCounter st ↔ KeysUpTo (fun _ => True) st := by
  constructor
  · intro h x hx
    obtain ⟨cs, ch, h1, h2, h3⟩ := h x hx
    refine ⟨cs, ch, h1, h2, ?_⟩
    rcases Nat.lt_or_eq_of_le h3 with h3 | h3
    · exact Or.inl h3
    · exact Or.inr ⟨trivial, h3⟩
  · intro h x hx
    obtain ⟨cs, ch, h1, h2, h3⟩ := h x hx
    refine ⟨cs, ch, h1, h2, ?_⟩
    rcases h3 with h3 | ⟨-, h3⟩ <;> omega

theorem keysUpTo_mono {A B : Nat → Prop} (hAB : ∀ e, A e → B e) {st : State}
    (h : KeysUpTo A st) : KeysUpTo B st := by
  intro x hx
  obtain ⟨cs, ch, h1, h2, h3⟩ := h x hx
  refine ⟨cs, ch, h1, h2, ?_⟩
  rcases h3 with h3 | ⟨ha, h3⟩
  · exact Or.inl h3
  · exact Or.inr ⟨hAB _ ha, h3⟩

/-- The strict form gives the other. -/
theorem keysAtMostCounter_of_keysBelowCounter {st : State} (h : KeysBelowCounter st) :
    KeysAtMostCounter st :=
  (keysAtMostCounter_iff st).2
    (keysUpTo_mono (fun _ _ => trivial) ((keysBelowCounter_iff st).1 h))

/-! ## Lookups -/

theorem find?_filter_of_imp {α : Type} (l : List α) (p q : α → Bool)
    (h : ∀ x, p x = true → q x = true) : (l.filter q).find? p = l.find? p := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    by_cases hq : q a = true
    · by_cases hp : p a = true
      · simp [hq, hp]
      · simp [hq, hp, ih]
    · have hp : ¬ p a = true := fun hp => hq (h a hp)
      simp [hq, hp, ih]

theorem findChains_setChains_self (st : State) (e : Nat) (c : Chains) :
    findChains (setChains st e c) e = some c := by
  simp only [findChains, setChains, List.find?_append]
  rw [List.find?_eq_none.mpr]
  · simp
  · intro x hx
    simp only [List.mem_filter, Bool.not_eq_true', beq_eq_false_iff_ne] at hx
    simpa using hx.2

theorem findChains_setChains_ne (st : State) (e e' : Nat) (c : Chains) (h : e' ≠ e) :
    findChains (setChains st e c) e' = findChains st e' := by
  unfold findChains setChains
  simp only [List.find?_append]
  rw [find?_filter_of_imp]
  · have hne : (e == e') = false := by simpa using fun h' => h h'.symm
    simp [hne]
  · intro x hx
    simp only [beq_iff_eq] at hx
    simp only [Bool.not_eq_true', beq_eq_false_iff_ne]
    omega

theorem findChains_clearOldEpochs (st : State) (current e : Nat)
    (h : current < e + epochsKept) :
    findChains (clearOldEpochs st current) e = findChains st e := by
  unfold findChains clearOldEpochs
  simp only
  rw [find?_filter_of_imp]
  intro x hx
  simp only [beq_iff_eq] at hx
  simp only [decide_eq_true_eq]
  omega

theorem findChains_mem (st : State) (e : Nat) (cs : Chains)
    (h : findChains st e = some cs) : (e, cs) ∈ st.chains := by
  unfold findChains at h
  cases hf : st.chains.find? (fun p => p.1 == e) with
  | none => simp [hf] at h
  | some p =>
    simp only [hf, Option.map_some, Option.some.injEq] at h
    have hm := List.mem_of_find?_eq_some hf
    have hp := List.find?_some hf
    obtain ⟨a, b⟩ := p
    simp only [beq_iff_eq] at hp h
    subst hp
    subst h
    exact hm

theorem epoch_le_of_findChains {st : State} {e : Nat} {cs : Chains}
    (hc : ChainsNotAhead st) (h : findChains st e = some cs) : e ≤ st.epoch :=
  hc (e, cs) (findChains_mem st e cs h)

/-! ## Each operation -/

/-- Replacing an epoch's chains by ones with the same receiving chain keeps the
invariant. -/
theorem setChains_keysUpTo {A : Nat → Prop} {st : State} {e : Nat} {cs c : Chains}
    (h : KeysUpTo A st) (hcs : findChains st e = some cs) (hr : c.receive = cs.receive) :
    KeysUpTo A (setChains st e c) := by
  intro x hx
  obtain ⟨cs', ch, h1, h2, h3⟩ := h x hx
  by_cases hxe : x.1 = e
  · rw [hxe, hcs] at h1
    cases h1
    refine ⟨c, ch, ?_, ?_, h3⟩
    · rw [hxe]; exact findChains_setChains_self st e c
    · rw [hr]; exact h2
  · exact ⟨cs', ch, by rw [findChains_setChains_ne _ _ _ _ hxe]; exact h1, h2, h3⟩

theorem setChains_chainsNotAhead {st : State} {e : Nat} {c : Chains}
    (hc : ChainsNotAhead st) (he : e ≤ st.epoch) : ChainsNotAhead (setChains st e c) := by
  intro p hp
  simp only [setChains, List.mem_append, List.mem_filter, List.mem_singleton] at hp
  show p.1 ≤ st.epoch
  rcases hp with ⟨hp, -⟩ | rfl
  · exact hc p hp
  · exact he

/-- `init` holds nothing, and its one chain is at the current epoch. -/
theorem init_keysBelowCounter (sk : Key) (dir : Direction) : KeysBelowCounter (init sk dir) := by
  intro x hx
  simp [init] at hx

/-- `init`'s one chain is for epoch 0, the current one. -/
theorem init_chainsNotAhead (sk : Key) (dir : Direction) : ChainsNotAhead (init sk dir) := by
  intro p hp
  simp [init] at hp
  subst hp
  simp [init]

/-- `init`'s store is empty. -/
theorem init_store_bounded (sk : Key) (dir : Direction) :
    (init sk dir).skipped.length ≤ maxSkippedStore := by
  simp [init]

theorem clearOldEpochs_keysUpTo {A : Nat → Prop} {st : State} (current : Nat)
    (h : KeysUpTo A st) : KeysUpTo A (clearOldEpochs st current) := by
  intro x hx
  simp only [clearOldEpochs, List.mem_filter, decide_eq_true_eq] at hx
  obtain ⟨cs, ch, h1, h2, h3⟩ := h x hx.1
  exact ⟨cs, ch, by rw [findChains_clearOldEpochs _ _ _ hx.2]; exact h1, h2, h3⟩

theorem advance_keysUpTo {A : Nat → Prop} {st st' : State} {out : Output}
    (h : KeysUpTo A st) (hc : ChainsNotAhead st) (hs : advance st out = some st') :
    KeysUpTo A st' := by
  unfold advance at hs
  split at hs
  · rename_i hcond
    injection hs with hs
    subst hs
    intro x hx
    simp only [clearOldEpochs, setChains, List.mem_filter, decide_eq_true_eq] at hx
    obtain ⟨hx, hkeep⟩ := hx
    obtain ⟨cs, ch, h1, h2, h3⟩ := h x hx
    have hle := epoch_le_of_findChains hc h1
    refine ⟨cs, ch, ?_, h2, h3⟩
    rw [findChains_clearOldEpochs _ _ _ hkeep, findChains_setChains_ne _ _ _ _ (by omega)]
    exact h1
  · simp at hs

/-- An advance that succeeds opens chains only for its new current epoch. -/
theorem advance_chainsNotAhead {st st' : State} {out : Output}
    (hc : ChainsNotAhead st) (hs : advance st out = some st') : ChainsNotAhead st' := by
  unfold advance at hs
  split at hs
  · rename_i hcond
    injection hs with hs
    subst hs
    intro p hp
    simp only [clearOldEpochs, setChains, List.mem_filter, List.mem_append,
      List.mem_singleton] at hp
    show p.1 ≤ out.keyEpoch
    rcases hp with ⟨⟨hp, -⟩ | rfl, -⟩
    · have := hc p hp
      omega
    · exact Nat.le_refl _
  · simp at hs

/-- The optional advance that opens a receive or a send. -/
theorem receiveAdvance_keysUpTo {A : Nat → Prop} {st st1 : State} {out : Option Output}
    (h : KeysUpTo A st) (hc : ChainsNotAhead st) (hs : receiveAdvance st out = some st1) :
    KeysUpTo A st1 ∧ ChainsNotAhead st1 := by
  cases out with
  | none =>
    simp only [receiveAdvance, Option.some.injEq] at hs
    subst hs
    exact ⟨h, hc⟩
  | some o => exact ⟨advance_keysUpTo h hc hs, advance_chainsNotAhead hc hs⟩

theorem receiveAdvance_store_le {st st1 : State} {out : Option Output}
    (hs : receiveAdvance st out = some st1) : st1.skipped.length ≤ st.skipped.length := by
  cases out with
  | none =>
    simp only [receiveAdvance, Option.some.injEq] at hs
    subst hs
    exact Nat.le_refl _
  | some o =>
    simp only [receiveAdvance] at hs
    unfold advance at hs
    split at hs
    · injection hs with hs
      subst hs
      simpa [clearOldEpochs, setChains] using List.length_filter_le _ _
    · simp at hs

theorem trySkipped_keysUpTo {A : Nat → Prop} {st : State} {e n : Nat} {r : State × Key}
    (h : KeysUpTo A st) (hs : trySkipped st e n = some r) : KeysUpTo A r.1 := by
  unfold trySkipped at hs
  split at hs
  · simp at hs
  · injection hs with hs
    subst hs
    intro x hx
    simp only [List.mem_filter] at hx
    exact h x hx.1

theorem evictOldest_keysUpTo {A : Nat → Prop} {st : State} (count : Nat)
    (h : KeysUpTo A st) : KeysUpTo A (evictOldest st count).1 := by
  intro x hx
  simp only [evictOldest] at hx
  exact h x (List.mem_of_mem_drop hx)

/-- A skip that succeeds keeps the invariant for any `atOk` that admits the
skipped epoch: a key it keeps for that epoch is below the new counter, and the
keys it stores run up to the new counter, the last one at it. -/
theorem skipMessageKeys_keysUpTo {A : Nat → Prop} {st st' : State} {e upto : Nat}
    (hA : A e) (h : KeysUpTo A st) (hs : skipMessageKeys st e upto = some st') :
    KeysUpTo A st' := by
  unfold skipMessageKeys at hs
  split at hs
  · simp at hs
  · rename_i cs hcs
    split at hs
    · simp at hs
    · rename_i ch hch
      split at hs
      · injection hs with hs
        subst hs
        exact h
      · rename_i hlo
        split at hs
        · simp at hs
        · split at hs
          · simp at hs
          · injection hs with hs
            subst hs
            intro x hx
            change x ∈ skipSurvivors st e ch.n upto ++ _ at hx
            rw [List.mem_append] at hx
            rcases hx with hx | hx
            · obtain ⟨hx, -⟩ :=
                (Proofs.SparseReplacementBound.mem_skipSurvivors_iff st e ch.n upto x).1 hx
              obtain ⟨cs', ch', h1, h2, h3⟩ := h x hx
              by_cases hxe : x.1 = e
              · rw [hxe, hcs] at h1
                cases h1
                rw [hch] at h2
                cases h2
                refine ⟨_, _, by rw [hxe]; exact findChains_setChains_self _ _ _, rfl, ?_⟩
                left
                show x.2.1 < upto
                rcases h3 with h3 | ⟨-, h3⟩ <;> omega
              · exact ⟨cs', ch', by rw [findChains_setChains_ne _ _ _ _ hxe]; exact h1, h2, h3⟩
            · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
              have hgt := Proofs.SparseRatchetCorrectness.deriveInto_num_gt ch.ck ch.n (upto - ch.n) y hy
              have hle := Proofs.SparseRatchetCorrectness.deriveInto_num_le ch.ck ch.n (upto - ch.n) y hy
              refine ⟨_, _, findChains_setChains_self _ _ _, rfl, ?_⟩
              show y.1 < upto ∨ (A e ∧ y.1 = upto)
              by_cases hy' : y.1 < upto
              · exact Or.inl hy'
              · exact Or.inr ⟨hA, by omega⟩

theorem skipMessageKeys_chainsNotAhead {st st' : State} {e upto : Nat}
    (hc : ChainsNotAhead st) (hs : skipMessageKeys st e upto = some st') :
    ChainsNotAhead st' := by
  unfold skipMessageKeys at hs
  split at hs
  · simp at hs
  · rename_i cs hcs
    split at hs
    · simp at hs
    · split at hs
      · injection hs with hs
        subst hs
        exact hc
      · split at hs
        · simp at hs
        · split at hs
          · simp at hs
          · injection hs with hs
            subst hs
            exact setChains_chainsNotAhead (st := { st with skipped := _ }) hc
              (epoch_le_of_findChains hc hcs)

/-- A send keeps the invariant: it may open an epoch, and it steps a sending
chain, which leaves the receiving chain as it was. -/
theorem send_keysUpTo {A : Nat → Prop} {st : State} {e : Nat} {out : Option Output}
    {r : State × Nat × Key}
    (h : KeysUpTo A st) (hc : ChainsNotAhead st) (hs : send st e out = some r) :
    KeysUpTo A r.1 ∧ ChainsNotAhead r.1 := by
  unfold send at hs
  split at hs
  · simp at hs
  · rename_i st1 hst1
    obtain ⟨h1, hc1⟩ := receiveAdvance_keysUpTo (out := out) h hc hst1
    split at hs
    · simp at hs
    · rename_i cs hcs
      split at hs
      · simp at hs
      · split at hs
        · injection hs with hs
          subst hs
          exact ⟨setChains_keysUpTo h1 hcs rfl,
            setChains_chainsNotAhead hc1 (epoch_le_of_findChains hc1 hcs)⟩
        · simp at hs

theorem send_store_le {st : State} {e : Nat} {out : Option Output} {r : State × Nat × Key}
    (hs : send st e out = some r) : r.1.skipped.length ≤ st.skipped.length := by
  unfold send at hs
  split at hs
  · simp at hs
  · rename_i st1 hst1
    have hle := receiveAdvance_store_le (out := out) hst1
    split at hs
    · simp at hs
    · split at hs
      · simp at hs
      · split at hs
        · injection hs with hs
          subst hs
          exact hle
        · simp at hs

/-- A receive keeps the invariant for any `atOk`: the skip may leave a key at
the counter of the message's epoch, and the step to the message's own number
then moves the counter past it. -/
theorem receive_keysUpTo {A : Nat → Prop} {st : State} {e : Nat} {out : Option Output}
    {n : Nat} {r : State × Key}
    (h : KeysUpTo A st) (hc : ChainsNotAhead st) (hs : receive st e out n = some r) :
    KeysUpTo A r.1 ∧ ChainsNotAhead r.1 := by
  unfold receive at hs
  split at hs
  · simp at hs
  · rename_i st1 hst1
    obtain ⟨h1, hc1⟩ := receiveAdvance_keysUpTo h hc hst1
    split at hs
    · rename_i res hres
      injection hs with hs
      subst hs
      exact ⟨trySkipped_keysUpTo h1 hres, by
        unfold trySkipped at hres
        split at hres
        · simp at hres
        · injection hres with hres
          subst hres
          exact hc1⟩
    · split at hs
      · simp at hs
      · rename_i st2 hst2
        have h2 : KeysUpTo (fun x => A x ∨ x = e) st2 :=
          skipMessageKeys_keysUpTo (Or.inr rfl) (keysUpTo_mono (fun _ ha => Or.inl ha) h1) hst2
        have hc2 := skipMessageKeys_chainsNotAhead hc1 hst2
        split at hs
        · simp at hs
        · rename_i cs hcs
          split at hs
          · simp at hs
          · rename_i ch hch
            split at hs
            · split at hs
              · rename_i hn
                injection hs with hs
                subst hs
                refine ⟨?_, setChains_chainsNotAhead hc2 (epoch_le_of_findChains hc2 hcs)⟩
                intro x hx
                obtain ⟨cs', ch', h1', h2', h3'⟩ := h2 x hx
                by_cases hxe : x.1 = e
                · rw [hxe, hcs] at h1'
                  cases h1'
                  rw [hch] at h2'
                  cases h2'
                  refine ⟨_, _, by rw [hxe]; exact findChains_setChains_self _ _ _, rfl, ?_⟩
                  left
                  show x.2.1 < n
                  rcases h3' with h3' | ⟨-, h3'⟩ <;> omega
                · refine ⟨cs', ch', by rw [findChains_setChains_ne _ _ _ _ hxe]; exact h1', h2', ?_⟩
                  rcases h3' with h3' | ⟨h3' | h3', h4'⟩
                  · exact Or.inl h3'
                  · exact Or.inr ⟨h3', h4'⟩
                  · exact absurd h3' hxe
              · simp at hs
            · simp at hs

/-! ## The named results -/

/-- A send that succeeds keeps the invariant, given no chain is held past the
current epoch. -/
theorem send_keysBelowCounter {st : State} {e : Nat} {out : Option Output} {r : State × Nat × Key}
    (h : KeysBelowCounter st) (hc : ChainsNotAhead st) (hs : send st e out = some r) :
    KeysBelowCounter r.1 :=
  (keysBelowCounter_iff _).2 (send_keysUpTo ((keysBelowCounter_iff _).1 h) hc hs).1

/-- An advance that succeeds keeps the invariant, given no chain is held past the
current epoch: the chains it opens are for an epoch no stored key names. -/
theorem advance_keysBelowCounter {st st' : State} {out : Output}
    (h : KeysBelowCounter st) (hc : ChainsNotAhead st) (hs : advance st out = some st') :
    KeysBelowCounter st' :=
  (keysBelowCounter_iff _).2 (advance_keysUpTo ((keysBelowCounter_iff _).1 h) hc hs)

/-- The optional advance that opens a send or a receive keeps the invariant. -/
theorem receiveAdvance_keysBelowCounter {st st' : State} {out : Option Output}
    (h : KeysBelowCounter st) (hc : ChainsNotAhead st) (hs : receiveAdvance st out = some st') :
    KeysBelowCounter st' :=
  (keysBelowCounter_iff _).2 (receiveAdvance_keysUpTo ((keysBelowCounter_iff _).1 h) hc hs).1

/-- Taking a stored key keeps the invariant: it only removes keys. -/
theorem trySkipped_keysBelowCounter {st : State} {e n : Nat} {r : State × Key}
    (h : KeysBelowCounter st) (hs : trySkipped st e n = some r) : KeysBelowCounter r.1 :=
  (keysBelowCounter_iff _).2 (trySkipped_keysUpTo ((keysBelowCounter_iff _).1 h) hs)

/-- Eviction keeps the invariant: it only removes keys. -/
theorem evictOldest_keysBelowCounter {st : State} (count : Nat)
    (h : KeysBelowCounter st) : KeysBelowCounter (evictOldest st count).1 :=
  (keysBelowCounter_iff _).2 (evictOldest_keysUpTo count ((keysBelowCounter_iff _).1 h))

/-- Retiring old epochs keeps the invariant: a key is kept exactly when its
epoch's chains are. -/
theorem clearOldEpochs_keysBelowCounter {st : State} (current : Nat)
    (h : KeysBelowCounter st) : KeysBelowCounter (clearOldEpochs st current) :=
  (keysBelowCounter_iff _).2 (clearOldEpochs_keysUpTo current ((keysBelowCounter_iff _).1 h))

/-- A receive that succeeds keeps the invariant, given no chain is held past the
current epoch. -/
theorem receive_keysBelowCounter {st : State} {e : Nat} {out : Option Output} {n : Nat}
    {r : State × Key}
    (h : KeysBelowCounter st) (hc : ChainsNotAhead st) (hs : receive st e out n = some r) :
    KeysBelowCounter r.1 :=
  (keysBelowCounter_iff _).2 (receive_keysUpTo ((keysBelowCounter_iff _).1 h) hc hs).1

/-- A skip alone keeps the non-strict form: no key past its counter. The strict
form is not kept by a skip alone (`skip_alone_leaves_a_key_at_the_counter`);
`receive`'s last step restores it. -/
theorem skipMessageKeys_keysAtMostCounter {st st' : State} {e upto : Nat}
    (h : KeysAtMostCounter st) (hs : skipMessageKeys st e upto = some st') :
    KeysAtMostCounter st' :=
  (keysAtMostCounter_iff _).2
    (skipMessageKeys_keysUpTo trivial ((keysAtMostCounter_iff _).1 h) hs)

/-- From the strict form, a skip on epoch `e` leaves every key below its counter
except that the keys of `e` may reach it. -/
theorem skipMessageKeys_keysBelowCounter_off {st st' : State} {e upto : Nat}
    (h : KeysBelowCounter st) (hs : skipMessageKeys st e upto = some st') :
    ∀ x ∈ st'.skipped, ∃ cs ch, findChains st' x.1 = some cs ∧ cs.receive = some ch ∧
      (x.2.1 < ch.n ∨ (x.1 = e ∧ x.2.1 = ch.n)) :=
  skipMessageKeys_keysUpTo (A := fun x => x = e) rfl
    (keysUpTo_mono (fun _ hf => hf.elim) ((keysBelowCounter_iff _).1 h)) hs

theorem receiveAdvance_chainsNotAhead {st st1 : State} {out : Option Output}
    (hc : ChainsNotAhead st) (hs : receiveAdvance st out = some st1) : ChainsNotAhead st1 := by
  cases out with
  | none =>
    simp only [receiveAdvance, Option.some.injEq] at hs
    subst hs
    exact hc
  | some o => exact advance_chainsNotAhead hc hs

/-- A send that succeeds holds no chain past its current epoch. -/
theorem send_chainsNotAhead {st : State} {e : Nat} {out : Option Output} {r : State × Nat × Key}
    (hc : ChainsNotAhead st) (hs : send st e out = some r) : ChainsNotAhead r.1 := by
  unfold send at hs
  split at hs
  · simp at hs
  · rename_i st1 hst1
    have hc1 := receiveAdvance_chainsNotAhead (out := out) hc hst1
    split at hs
    · simp at hs
    · rename_i cs hcs
      split at hs
      · simp at hs
      · split at hs
        · injection hs with hs
          subst hs
          exact setChains_chainsNotAhead hc1 (epoch_le_of_findChains hc1 hcs)
        · simp at hs

/-- A receive that succeeds holds no chain past its current epoch. -/
theorem receive_chainsNotAhead {st : State} {e : Nat} {out : Option Output} {n : Nat}
    {r : State × Key} (hc : ChainsNotAhead st) (hs : receive st e out n = some r) :
    ChainsNotAhead r.1 := by
  unfold receive at hs
  split at hs
  · simp at hs
  · rename_i st1 hst1
    have hc1 := receiveAdvance_chainsNotAhead hc hst1
    split at hs
    · rename_i res hres
      injection hs with hs
      subst hs
      unfold trySkipped at hres
      split at hres
      · simp at hres
      · injection hres with hres
        subst hres
        exact hc1
    · split at hs
      · simp at hs
      · rename_i st2 hst2
        have hc2 := skipMessageKeys_chainsNotAhead hc1 hst2
        split at hs
        · simp at hs
        · rename_i cs hcs
          split at hs
          · simp at hs
          · split at hs
            · split at hs
              · injection hs with hs
                subst hs
                exact setChains_chainsNotAhead hc2 (epoch_le_of_findChains hc2 hcs)
              · simp at hs
            · simp at hs

/-! ## On such a state the skip deletes nothing -/

/-- On a state with no key past its counter, the keys a skip from the counter
keeps are the whole store, whatever `upto` is: the deletion of step 2 removes
nothing, and the count of step 3 is the store's length. -/
theorem skipSurvivors_eq_of_keysAtMostCounter {st : State} {e upto : Nat} {cs : Chains}
    {ch : Chain} (h : KeysAtMostCounter st) (hc : findChains st e = some cs)
    (hr : cs.receive = some ch) :
    skipSurvivors st e ch.n upto = st.skipped := by
  unfold skipSurvivors
  rw [List.filter_eq_self]
  intro x hx
  obtain ⟨cs', ch', h1, h2, h3⟩ := h x hx
  simp only [Bool.not_eq_true', Bool.and_eq_false_iff, beq_eq_false_iff_ne,
    decide_eq_false_iff_not]
  by_cases hxe : x.1 = e
  · left; right
    rw [hxe, hc] at h1
    cases h1
    rw [hr] at h2
    cases h2
    omega
  · left; left; exact hxe

theorem skipSurvivors_eq_of_keysBelowCounter {st : State} {e upto : Nat} {cs : Chains}
    {ch : Chain} (h : KeysBelowCounter st) (hc : findChains st e = some cs)
    (hr : cs.receive = some ch) :
    skipSurvivors st e ch.n upto = st.skipped :=
  skipSurvivors_eq_of_keysAtMostCounter (keysAtMostCounter_of_keysBelowCounter h) hc hr

/-! ## The total bound across the operations -/

/-- A send that succeeds keeps the store within the total bound: it never
lengthens the store. -/
theorem send_store_bounded {st : State} {e : Nat} {out : Option Output} {r : State × Nat × Key}
    (hb : st.skipped.length ≤ maxSkippedStore) (hs : send st e out = some r) :
    r.1.skipped.length ≤ maxSkippedStore :=
  Nat.le_trans (send_store_le hs) hb

/-- A receive that succeeds keeps the store within the total bound. -/
theorem receive_store_bounded {st : State} {e : Nat} {out : Option Output} {n : Nat}
    {r : State × Key}
    (hb : st.skipped.length ≤ maxSkippedStore) (hs : receive st e out n = some r) :
    r.1.skipped.length ≤ maxSkippedStore := by
  unfold receive at hs
  split at hs
  · simp at hs
  · rename_i st1 hst1
    have hb1 := Nat.le_trans (receiveAdvance_store_le hst1) hb
    split at hs
    · rename_i res hres
      injection hs with hs
      subst hs
      exact Nat.le_trans (Proofs.SparseRatchetCorrectness.trySkipped_store_lt _ _ _ _ hres) hb1
    · split at hs
      · simp at hs
      · rename_i st2 hst2
        have hb2 := Proofs.SparseRatchetCorrectness.skipMessageKeys_store_bounded _ _ _ _ hst2
        have hb2' : st2.skipped.length ≤ maxSkippedStore := by
          have := Nat.max_le.2 ⟨hb1, Nat.le_refl maxSkippedStore⟩
          omega
        split at hs
        · simp at hs
        · split at hs
          · simp at hs
          · split at hs
            · split at hs
              · injection hs with hs
                subst hs
                exact hb2'
              · simp at hs
            · simp at hs

/-- Eviction keeps the store within the total bound. -/
theorem evictOldest_store_bounded {st : State} (count : Nat)
    (hb : st.skipped.length ≤ maxSkippedStore) :
    (evictOldest st count).1.skipped.length ≤ maxSkippedStore := by
  simp only [evictOldest, List.length_drop]
  omega

/-! ## Any sequence of operations -/

/-- One of the operations the sparse ratchet's public interface offers on a
state: a send, a receive, or an eviction of the oldest stored keys. -/
inductive Op where
  | send (e : Nat) (out : Option Output)
  | receive (e : Nat) (out : Option Output) (n : Nat)
  | evict (count : Nat)

/-- Apply one operation. A refused send or receive leaves the state it was
given: the caller ran it on a copy and keeps its own (sparse-pq-ratchet.md,
Receiving). -/
def Op.apply (st : State) : Op → State
  | .send e out =>
    match Model.SparseRatchet.send st e out with
    | some r => r.1
    | none => st
  | .receive e out n =>
    match Model.SparseRatchet.receive st e out n with
    | some r => r.1
    | none => st
  | .evict count => (evictOldest st count).1

/-- Apply a list of operations in order. -/
def run (st : State) : List Op → State
  | [] => st
  | op :: ops => run (op.apply st) ops

/-- The invariant carried across operations: no stored key at or past its
chain's counter, no chain for an epoch past the current one, and the store
within the total bound. -/
def ReachableStore (st : State) : Prop :=
  KeysBelowCounter st ∧ ChainsNotAhead st ∧ st.skipped.length ≤ maxSkippedStore

/-- `init` meets the three parts of `ReachableStore`. -/
theorem init_reachableStore (sk : Key) (dir : Direction) : ReachableStore (init sk dir) :=
  ⟨init_keysBelowCounter sk dir, init_chainsNotAhead sk dir, init_store_bounded sk dir⟩

/-- Any one operation, taken or refused, keeps `ReachableStore`. -/
theorem apply_reachableStore {st : State} (h : ReachableStore st) (op : Op) :
    ReachableStore (op.apply st) := by
  obtain ⟨hk, hc, hb⟩ := h
  cases op with
  | send e out =>
    simp only [Op.apply]
    split
    · rename_i r hr
      exact ⟨send_keysBelowCounter hk hc hr, send_chainsNotAhead hc hr, send_store_bounded hb hr⟩
    · exact ⟨hk, hc, hb⟩
  | receive e out n =>
    simp only [Op.apply]
    split
    · rename_i r hr
      exact ⟨receive_keysBelowCounter hk hc hr, receive_chainsNotAhead hc hr,
        receive_store_bounded hb hr⟩
    · exact ⟨hk, hc, hb⟩
  | evict count =>
    simp only [Op.apply]
    exact ⟨evictOldest_keysBelowCounter count hk, hc, evictOldest_store_bounded count hb⟩

/-- Any sequence of operations keeps `ReachableStore`. -/
theorem run_reachableStore {st : State} (h : ReachableStore st) (ops : List Op) :
    ReachableStore (run st ops) := by
  induction ops generalizing st with
  | nil => exact h
  | cons op ops ih => exact ih (apply_reachableStore h op)

/-- The bound alone needs nothing else: any sequence of operations from a state
whose store is within the total bound leaves a store within it. -/
theorem run_store_bounded {st : State} (hb : st.skipped.length ≤ maxSkippedStore)
    (ops : List Op) : (run st ops).skipped.length ≤ maxSkippedStore := by
  induction ops generalizing st with
  | nil => exact hb
  | cons op ops ih =>
    apply ih
    cases op with
    | send e out =>
      simp only [Op.apply]
      split
      · rename_i r hr
        exact send_store_bounded hb hr
      · exact hb
    | receive e out n =>
      simp only [Op.apply]
      split
      · rename_i r hr
        exact receive_store_bounded hb hr
      · exact hb
    | evict count => exact evictOldest_store_bounded count hb

/-- Every state a sequence of operations produces from `init` holds no stored
key at or past its chain's counter. -/
theorem reachable_keysBelowCounter (sk : Key) (dir : Direction) (ops : List Op) :
    KeysBelowCounter (run (init sk dir) ops) :=
  (run_reachableStore (init_reachableStore sk dir) ops).1

/-- Every state a sequence of operations produces from `init` holds at most
`maxSkippedStore` keys. -/
theorem reachable_store_bounded (sk : Key) (dir : Direction) (ops : List Op) :
    (run (init sk dir) ops).skipped.length ≤ maxSkippedStore :=
  (run_reachableStore (init_reachableStore sk dir) ops).2.2

/-- On every such state a skip from the counter deletes nothing: the keys it
keeps are the whole store, so the count before the deletion and the count after
it are the same. -/
theorem reachable_skipSurvivors_eq (sk : Key) (dir : Direction) (ops : List Op)
    {e upto : Nat} {cs : Chains} {ch : Chain}
    (hc : findChains (run (init sk dir) ops) e = some cs) (hr : cs.receive = some ch) :
    skipSurvivors (run (init sk dir) ops) e ch.n upto = (run (init sk dir) ops).skipped :=
  skipSurvivors_eq_of_keysBelowCounter (reachable_keysBelowCounter sk dir ops) hc hr

/-! ## The invariant has content -/

/-- A state the operations reach holds stored keys: Bob, from `init`, receives
message 3 of epoch 0 first (the trace of the vector `bob-stores-skipped-keys`
in `sparse-ratchet-state.json`, for any shared secret). The store then holds
keys 1 and 2 of epoch 0, and the receiving chain is at 3. So the conclusions of
`reachable_keysBelowCounter` and `reachable_skipSurvivors_eq` are about a
non-empty store. -/
theorem witness_reachable_holds_stored_keys (sk : Key) :
    (run (init sk .b2a) [.receive 0 none 3]).skipped.map (fun x => (x.1, x.2.1)) =
        [(0, 1), (0, 2)] ∧
      ∃ cs ch, findChains (run (init sk .b2a) [.receive 0 none 3]) 0 = some cs ∧
        cs.receive = some ch ∧ ch.n = 3 := by
  simp [run, Op.apply, Model.SparseRatchet.receive, trySkipped, init, skipMessageKeys,
    findChains, setChains, skipSurvivors, skipMessageKeys.deriveInto, maxSkip,
    Model.State.maxSkip, maxSkippedStore, Model.State.maxSkippedStore, u64Max]

/-- The predicate is not true of every state: a state holding a key past its
chain's counter fails it, and on that state a skip deletes the key, so the
corollary `skipSurvivors_eq_of_keysAtMostCounter` does not hold without its
premise. The state is `init`'s with one key stored for epoch 0 at number 1 while
the receiving counter is 0, the shape of the vector `stored-key-past-its-counter`
in `sparse-ratchet-state.json`, which the reader accepts. -/
theorem witness_store_past_its_counter_fails (sk k : Key) :
    let st : State := { init sk .b2a with skipped := [(0, 1, k)] }
    ¬ KeysAtMostCounter st ∧ ¬ KeysBelowCounter st ∧
      skipSurvivors st 0 0 1 = [] ∧ st.skipped ≠ [] := by
  intro st
  have hfind : findChains st 0 =
      some ⟨some ⟨(kdfInit sk).2.2, 0⟩, some ⟨(kdfInit sk).2.1, 0⟩⟩ := by
    simp [st, findChains, init]
  have hnot : ¬ KeysAtMostCounter st := by
    intro h
    obtain ⟨cs, ch, h1, h2, h3⟩ := h (0, 1, k) (by simp [st])
    simp only at h1 h3
    rw [hfind] at h1
    cases h1
    cases h2
    simp at h3
  refine ⟨hnot, fun h => hnot (keysAtMostCounter_of_keysBelowCounter h), ?_, by simp [st]⟩
  simp [st, skipSurvivors]

/-- A stored key whose epoch's receiving chain is at or below its number breaks
the strict form. -/
theorem not_keysBelowCounter_of_mem {st : State} {x : Nat × Nat × Key} {cs : Chains}
    {ch : Chain} (hx : x ∈ st.skipped) (h1 : findChains st x.1 = some cs)
    (h2 : cs.receive = some ch) (h3 : ch.n ≤ x.2.1) : ¬ KeysBelowCounter st := by
  intro h
  obtain ⟨cs', ch', h1', h2', h3'⟩ := h x hx
  rw [h1] at h1'
  cases h1'
  rw [h2] at h2'
  cases h2'
  omega

/-- A skip on its own does not keep the strict form: from `init`, a skip to 2
stores keys 1 and 2 and leaves the counter at 2, so key 2 is at the counter. That
is why the skip is stated with the non-strict form
(`skipMessageKeys_keysAtMostCounter`) and the strict form through `receive`. -/
theorem skip_alone_leaves_a_key_at_the_counter (sk : Key) :
    ∃ st', skipMessageKeys (init sk .b2a) 0 2 = some st' ∧
      KeysAtMostCounter st' ∧ ¬ KeysBelowCounter st' := by
  have hcomp : (skipMessageKeys (init sk .b2a) 0 2).map
      (fun st => (st.skipped.map (fun x => (x.1, x.2.1)),
        ((findChains st 0).bind (·.receive)).map (·.n))) = some ([(0, 1), (0, 2)], some 2) := by
    simp [skipMessageKeys, init, findChains, setChains, skipSurvivors,
      skipMessageKeys.deriveInto, maxSkip, Model.State.maxSkip, maxSkippedStore,
      Model.State.maxSkippedStore]
  cases hs : skipMessageKeys (init sk .b2a) 0 2 with
  | none =>
    rw [hs] at hcomp
    simp at hcomp
  | some st' =>
    rw [hs] at hcomp
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hcomp
    obtain ⟨hmap, hch⟩ := hcomp
    have hmem : ((0 : Nat), (2 : Nat)) ∈ st'.skipped.map (fun x => (x.1, x.2.1)) := by
      rw [hmap]; simp
    obtain ⟨x, hx, hfx⟩ := List.mem_map.mp hmem
    simp only [Prod.mk.injEq] at hfx
    refine ⟨st', rfl, skipMessageKeys_keysAtMostCounter
      (keysAtMostCounter_of_keysBelowCounter (init_keysBelowCounter sk .b2a)) hs, ?_⟩
    cases hf : findChains st' 0 with
    | none =>
      rw [hf] at hch
      simp at hch
    | some cs =>
      cases hr : cs.receive with
      | none =>
        rw [hf] at hch
        simp [hr] at hch
      | some ch =>
        rw [hf] at hch
        simp [hr] at hch
        exact not_keysBelowCounter_of_mem hx (by rw [hfx.1]; exact hf) hr (by omega)

/-- `ChainsNotAhead` is needed for an advance: a state that holds a key below its
counter under a chain for an epoch past the current one meets `KeysBelowCounter`,
and the advance onto that epoch opens fresh chains over it, at counter 0, so the
key is then past its counter. No operation produces such a state
(`run_reachableStore`); a decoded one is not covered here. -/
theorem chainsNotAhead_needed_for_advance (rk ck k key : Key) (dir : Direction) :
    let st : State :=
      { rk := rk, epoch := 0,
        chains := [(0, ⟨none, some ⟨ck, 0⟩⟩), (1, ⟨none, some ⟨ck, 5⟩⟩)],
        skipped := [(1, 1, k)], direction := dir }
    KeysBelowCounter st ∧ ¬ ChainsNotAhead st ∧
      ∃ st', advance st ⟨1, key⟩ = some st' ∧ ¬ KeysBelowCounter st' := by
  intro st
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    simp only [st, List.mem_singleton] at hx
    subst hx
    exact ⟨⟨none, some ⟨ck, 5⟩⟩, ⟨ck, 5⟩, by simp [st, findChains], rfl, by show 1 < 5; omega⟩
  · intro h
    have := h (1, ⟨none, some ⟨ck, 5⟩⟩) (by simp [st])
    simp [st] at this
  · have hcomp : (advance st ⟨1, key⟩).map
        (fun st' => (st'.skipped.map (fun x => (x.1, x.2.1)),
          ((findChains st' 1).bind (·.receive)).map (·.n))) = some ([(1, 1)], some 0) := by
      simp [st, advance, clearOldEpochs, setChains, findChains, epochsKept, u64Max]
    cases hs : advance st ⟨1, key⟩ with
    | none =>
      rw [hs] at hcomp
      simp at hcomp
    | some st' =>
      rw [hs] at hcomp
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hcomp
      obtain ⟨hmap, hch⟩ := hcomp
      have hmem : ((1 : Nat), (1 : Nat)) ∈ st'.skipped.map (fun x => (x.1, x.2.1)) := by
        rw [hmap]; simp
      obtain ⟨x, hx, hfx⟩ := List.mem_map.mp hmem
      simp only [Prod.mk.injEq] at hfx
      refine ⟨st', rfl, ?_⟩
      cases hf : findChains st' 1 with
      | none =>
        rw [hf] at hch
        simp at hch
      | some cs =>
        cases hr : cs.receive with
        | none =>
          rw [hf] at hch
          simp [hr] at hch
        | some ch =>
          rw [hf] at hch
          simp [hr] at hch
          exact not_keysBelowCounter_of_mem hx (by rw [hfx.1]; exact hf) hr (by omega)

end Proofs.SparseReachableStore

/--
info: def Proofs.SparseReachableStore.KeysBelowCounter : Model.SparseRatchet.State → Prop :=
fun st =>
  ∀ (x : Nat × Nat × Model.State.Key),
    x ∈ st.skipped →
      ∃ cs ch, Model.SparseRatchet.findChains st x.fst = some cs ∧ cs.receive = some ch ∧ x.snd.fst < ch.n
-/
#guard_msgs in
#print Proofs.SparseReachableStore.KeysBelowCounter

/--
info: def Proofs.SparseReachableStore.KeysAtMostCounter : Model.SparseRatchet.State → Prop :=
fun st =>
  ∀ (x : Nat × Nat × Model.State.Key),
    x ∈ st.skipped →
      ∃ cs ch, Model.SparseRatchet.findChains st x.fst = some cs ∧ cs.receive = some ch ∧ x.snd.fst ≤ ch.n
-/
#guard_msgs in
#print Proofs.SparseReachableStore.KeysAtMostCounter

/--
info: def Proofs.SparseReachableStore.ChainsNotAhead : Model.SparseRatchet.State → Prop :=
fun st => ∀ (p : Nat × Model.SparseRatchet.Chains), p ∈ st.chains → p.fst ≤ st.epoch
-/
#guard_msgs in
#print Proofs.SparseReachableStore.ChainsNotAhead

/--
info: def Proofs.SparseReachableStore.ReachableStore : Model.SparseRatchet.State → Prop :=
fun st =>
  Proofs.SparseReachableStore.KeysBelowCounter st ∧
    Proofs.SparseReachableStore.ChainsNotAhead st ∧ st.skipped.length ≤ Model.SparseRatchet.maxSkippedStore
-/
#guard_msgs in
#print Proofs.SparseReachableStore.ReachableStore

/--
info: inductive Proofs.SparseReachableStore.Op : Type
number of parameters: 0
constructors:
Proofs.SparseReachableStore.Op.send : Nat → Option Model.SparseRatchet.Output → Proofs.SparseReachableStore.Op
Proofs.SparseReachableStore.Op.receive : Nat → Option Model.SparseRatchet.Output → Nat → Proofs.SparseReachableStore.Op
Proofs.SparseReachableStore.Op.evict : Nat → Proofs.SparseReachableStore.Op
-/
#guard_msgs in
#print Proofs.SparseReachableStore.Op

/--
info: def Proofs.SparseReachableStore.Op.apply : Model.SparseRatchet.State →
  Proofs.SparseReachableStore.Op → Model.SparseRatchet.State :=
fun st x =>
  match x with
  | Proofs.SparseReachableStore.Op.send e out =>
    match Model.SparseRatchet.send st e out with
    | some r => r.fst
    | none => st
  | Proofs.SparseReachableStore.Op.receive e out n =>
    match Model.SparseRatchet.receive st e out n with
    | some r => r.fst
    | none => st
  | Proofs.SparseReachableStore.Op.evict count => (Model.SparseRatchet.evictOldest st count).fst
-/
#guard_msgs in
#print Proofs.SparseReachableStore.Op.apply

/--
info: def Proofs.SparseReachableStore.run : Model.SparseRatchet.State →
  List Proofs.SparseReachableStore.Op → Model.SparseRatchet.State :=
fun st x =>
  List.brecOn (motive := fun x => Model.SparseRatchet.State → Model.SparseRatchet.State) x
    Proofs.SparseReachableStore.run._f st
-/
#guard_msgs in
#print Proofs.SparseReachableStore.run

/--
info: Proofs.SparseReachableStore.init_keysBelowCounter (sk : Model.State.Key) (dir : Model.SparseRatchet.Direction) :
  Proofs.SparseReachableStore.KeysBelowCounter (Model.SparseRatchet.init sk dir)
-/
#guard_msgs in
#check Proofs.SparseReachableStore.init_keysBelowCounter

/--
info: Proofs.SparseReachableStore.init_chainsNotAhead (sk : Model.State.Key) (dir : Model.SparseRatchet.Direction) :
  Proofs.SparseReachableStore.ChainsNotAhead (Model.SparseRatchet.init sk dir)
-/
#guard_msgs in
#check Proofs.SparseReachableStore.init_chainsNotAhead

/--
info: Proofs.SparseReachableStore.init_reachableStore (sk : Model.State.Key) (dir : Model.SparseRatchet.Direction) :
  Proofs.SparseReachableStore.ReachableStore (Model.SparseRatchet.init sk dir)
-/
#guard_msgs in
#check Proofs.SparseReachableStore.init_reachableStore

/--
info: Proofs.SparseReachableStore.advance_keysBelowCounter {st st' : Model.SparseRatchet.State}
  {out : Model.SparseRatchet.Output} (h : Proofs.SparseReachableStore.KeysBelowCounter st)
  (hc : Proofs.SparseReachableStore.ChainsNotAhead st) (hs : Model.SparseRatchet.advance st out = some st') :
  Proofs.SparseReachableStore.KeysBelowCounter st'
-/
#guard_msgs in
#check Proofs.SparseReachableStore.advance_keysBelowCounter

/--
info: Proofs.SparseReachableStore.advance_chainsNotAhead {st st' : Model.SparseRatchet.State}
  {out : Model.SparseRatchet.Output} (hc : Proofs.SparseReachableStore.ChainsNotAhead st)
  (hs : Model.SparseRatchet.advance st out = some st') : Proofs.SparseReachableStore.ChainsNotAhead st'
-/
#guard_msgs in
#check Proofs.SparseReachableStore.advance_chainsNotAhead

/--
info: Proofs.SparseReachableStore.receiveAdvance_keysBelowCounter {st st' : Model.SparseRatchet.State}
  {out : Option Model.SparseRatchet.Output} (h : Proofs.SparseReachableStore.KeysBelowCounter st)
  (hc : Proofs.SparseReachableStore.ChainsNotAhead st) (hs : Model.SparseRatchet.receiveAdvance st out = some st') :
  Proofs.SparseReachableStore.KeysBelowCounter st'
-/
#guard_msgs in
#check Proofs.SparseReachableStore.receiveAdvance_keysBelowCounter

/--
info: Proofs.SparseReachableStore.send_keysBelowCounter {st : Model.SparseRatchet.State} {e : Nat}
  {out : Option Model.SparseRatchet.Output} {r : Model.SparseRatchet.State × Nat × Model.State.Key}
  (h : Proofs.SparseReachableStore.KeysBelowCounter st) (hc : Proofs.SparseReachableStore.ChainsNotAhead st)
  (hs : Model.SparseRatchet.send st e out = some r) : Proofs.SparseReachableStore.KeysBelowCounter r.fst
-/
#guard_msgs in
#check Proofs.SparseReachableStore.send_keysBelowCounter

/--
info: Proofs.SparseReachableStore.send_chainsNotAhead {st : Model.SparseRatchet.State} {e : Nat}
  {out : Option Model.SparseRatchet.Output} {r : Model.SparseRatchet.State × Nat × Model.State.Key}
  (hc : Proofs.SparseReachableStore.ChainsNotAhead st) (hs : Model.SparseRatchet.send st e out = some r) :
  Proofs.SparseReachableStore.ChainsNotAhead r.fst
-/
#guard_msgs in
#check Proofs.SparseReachableStore.send_chainsNotAhead

/--
info: Proofs.SparseReachableStore.send_store_bounded {st : Model.SparseRatchet.State} {e : Nat}
  {out : Option Model.SparseRatchet.Output} {r : Model.SparseRatchet.State × Nat × Model.State.Key}
  (hb : st.skipped.length ≤ Model.SparseRatchet.maxSkippedStore) (hs : Model.SparseRatchet.send st e out = some r) :
  r.fst.skipped.length ≤ Model.SparseRatchet.maxSkippedStore
-/
#guard_msgs in
#check Proofs.SparseReachableStore.send_store_bounded

/--
info: Proofs.SparseReachableStore.trySkipped_keysBelowCounter {st : Model.SparseRatchet.State} {e n : Nat}
  {r : Model.SparseRatchet.State × Model.State.Key} (h : Proofs.SparseReachableStore.KeysBelowCounter st)
  (hs : Model.SparseRatchet.trySkipped st e n = some r) : Proofs.SparseReachableStore.KeysBelowCounter r.fst
-/
#guard_msgs in
#check Proofs.SparseReachableStore.trySkipped_keysBelowCounter

/--
info: Proofs.SparseReachableStore.skipMessageKeys_keysAtMostCounter {st st' : Model.SparseRatchet.State} {e upto : Nat}
  (h : Proofs.SparseReachableStore.KeysAtMostCounter st)
  (hs : Model.SparseRatchet.skipMessageKeys st e upto = some st') : Proofs.SparseReachableStore.KeysAtMostCounter st'
-/
#guard_msgs in
#check Proofs.SparseReachableStore.skipMessageKeys_keysAtMostCounter

/--
info: Proofs.SparseReachableStore.skipMessageKeys_keysBelowCounter_off {st st' : Model.SparseRatchet.State} {e upto : Nat}
  (h : Proofs.SparseReachableStore.KeysBelowCounter st) (hs : Model.SparseRatchet.skipMessageKeys st e upto = some st')
  (x : Nat × Nat × Model.State.Key) :
  x ∈ st'.skipped →
    ∃ cs ch,
      Model.SparseRatchet.findChains st' x.fst = some cs ∧
        cs.receive = some ch ∧ (x.snd.fst < ch.n ∨ x.fst = e ∧ x.snd.fst = ch.n)
-/
#guard_msgs in
#check Proofs.SparseReachableStore.skipMessageKeys_keysBelowCounter_off

/--
info: Proofs.SparseReachableStore.receive_keysBelowCounter {st : Model.SparseRatchet.State} {e : Nat}
  {out : Option Model.SparseRatchet.Output} {n : Nat} {r : Model.SparseRatchet.State × Model.State.Key}
  (h : Proofs.SparseReachableStore.KeysBelowCounter st) (hc : Proofs.SparseReachableStore.ChainsNotAhead st)
  (hs : Model.SparseRatchet.receive st e out n = some r) : Proofs.SparseReachableStore.KeysBelowCounter r.fst
-/
#guard_msgs in
#check Proofs.SparseReachableStore.receive_keysBelowCounter

/--
info: Proofs.SparseReachableStore.receive_chainsNotAhead {st : Model.SparseRatchet.State} {e : Nat}
  {out : Option Model.SparseRatchet.Output} {n : Nat} {r : Model.SparseRatchet.State × Model.State.Key}
  (hc : Proofs.SparseReachableStore.ChainsNotAhead st) (hs : Model.SparseRatchet.receive st e out n = some r) :
  Proofs.SparseReachableStore.ChainsNotAhead r.fst
-/
#guard_msgs in
#check Proofs.SparseReachableStore.receive_chainsNotAhead

/--
info: Proofs.SparseReachableStore.receive_store_bounded {st : Model.SparseRatchet.State} {e : Nat}
  {out : Option Model.SparseRatchet.Output} {n : Nat} {r : Model.SparseRatchet.State × Model.State.Key}
  (hb : st.skipped.length ≤ Model.SparseRatchet.maxSkippedStore)
  (hs : Model.SparseRatchet.receive st e out n = some r) : r.fst.skipped.length ≤ Model.SparseRatchet.maxSkippedStore
-/
#guard_msgs in
#check Proofs.SparseReachableStore.receive_store_bounded

/--
info: Proofs.SparseReachableStore.evictOldest_keysBelowCounter {st : Model.SparseRatchet.State} (count : Nat)
  (h : Proofs.SparseReachableStore.KeysBelowCounter st) :
  Proofs.SparseReachableStore.KeysBelowCounter (Model.SparseRatchet.evictOldest st count).fst
-/
#guard_msgs in
#check Proofs.SparseReachableStore.evictOldest_keysBelowCounter

/--
info: Proofs.SparseReachableStore.evictOldest_store_bounded {st : Model.SparseRatchet.State} (count : Nat)
  (hb : st.skipped.length ≤ Model.SparseRatchet.maxSkippedStore) :
  (Model.SparseRatchet.evictOldest st count).fst.skipped.length ≤ Model.SparseRatchet.maxSkippedStore
-/
#guard_msgs in
#check Proofs.SparseReachableStore.evictOldest_store_bounded

/--
info: Proofs.SparseReachableStore.clearOldEpochs_keysBelowCounter {st : Model.SparseRatchet.State} (current : Nat)
  (h : Proofs.SparseReachableStore.KeysBelowCounter st) :
  Proofs.SparseReachableStore.KeysBelowCounter (Model.SparseRatchet.clearOldEpochs st current)
-/
#guard_msgs in
#check Proofs.SparseReachableStore.clearOldEpochs_keysBelowCounter

/--
info: Proofs.SparseReachableStore.skipSurvivors_eq_of_keysAtMostCounter {st : Model.SparseRatchet.State} {e upto : Nat}
  {cs : Model.SparseRatchet.Chains} {ch : Model.SparseRatchet.Chain}
  (h : Proofs.SparseReachableStore.KeysAtMostCounter st) (hc : Model.SparseRatchet.findChains st e = some cs)
  (hr : cs.receive = some ch) : Model.SparseRatchet.skipSurvivors st e ch.n upto = st.skipped
-/
#guard_msgs in
#check Proofs.SparseReachableStore.skipSurvivors_eq_of_keysAtMostCounter

/--
info: Proofs.SparseReachableStore.skipSurvivors_eq_of_keysBelowCounter {st : Model.SparseRatchet.State} {e upto : Nat}
  {cs : Model.SparseRatchet.Chains} {ch : Model.SparseRatchet.Chain}
  (h : Proofs.SparseReachableStore.KeysBelowCounter st) (hc : Model.SparseRatchet.findChains st e = some cs)
  (hr : cs.receive = some ch) : Model.SparseRatchet.skipSurvivors st e ch.n upto = st.skipped
-/
#guard_msgs in
#check Proofs.SparseReachableStore.skipSurvivors_eq_of_keysBelowCounter

/--
info: Proofs.SparseReachableStore.apply_reachableStore {st : Model.SparseRatchet.State}
  (h : Proofs.SparseReachableStore.ReachableStore st) (op : Proofs.SparseReachableStore.Op) :
  Proofs.SparseReachableStore.ReachableStore (Proofs.SparseReachableStore.Op.apply st op)
-/
#guard_msgs in
#check Proofs.SparseReachableStore.apply_reachableStore

/--
info: Proofs.SparseReachableStore.run_reachableStore {st : Model.SparseRatchet.State}
  (h : Proofs.SparseReachableStore.ReachableStore st) (ops : List Proofs.SparseReachableStore.Op) :
  Proofs.SparseReachableStore.ReachableStore (Proofs.SparseReachableStore.run st ops)
-/
#guard_msgs in
#check Proofs.SparseReachableStore.run_reachableStore

/--
info: Proofs.SparseReachableStore.run_store_bounded {st : Model.SparseRatchet.State}
  (hb : st.skipped.length ≤ Model.SparseRatchet.maxSkippedStore) (ops : List Proofs.SparseReachableStore.Op) :
  (Proofs.SparseReachableStore.run st ops).skipped.length ≤ Model.SparseRatchet.maxSkippedStore
-/
#guard_msgs in
#check Proofs.SparseReachableStore.run_store_bounded

/--
info: Proofs.SparseReachableStore.reachable_keysBelowCounter (sk : Model.State.Key) (dir : Model.SparseRatchet.Direction)
  (ops : List Proofs.SparseReachableStore.Op) :
  Proofs.SparseReachableStore.KeysBelowCounter (Proofs.SparseReachableStore.run (Model.SparseRatchet.init sk dir) ops)
-/
#guard_msgs in
#check Proofs.SparseReachableStore.reachable_keysBelowCounter

/--
info: Proofs.SparseReachableStore.reachable_store_bounded (sk : Model.State.Key) (dir : Model.SparseRatchet.Direction)
  (ops : List Proofs.SparseReachableStore.Op) :
  (Proofs.SparseReachableStore.run (Model.SparseRatchet.init sk dir) ops).skipped.length ≤
    Model.SparseRatchet.maxSkippedStore
-/
#guard_msgs in
#check Proofs.SparseReachableStore.reachable_store_bounded

/--
info: Proofs.SparseReachableStore.reachable_skipSurvivors_eq (sk : Model.State.Key) (dir : Model.SparseRatchet.Direction)
  (ops : List Proofs.SparseReachableStore.Op) {e upto : Nat} {cs : Model.SparseRatchet.Chains}
  {ch : Model.SparseRatchet.Chain}
  (hc :
    Model.SparseRatchet.findChains (Proofs.SparseReachableStore.run (Model.SparseRatchet.init sk dir) ops) e = some cs)
  (hr : cs.receive = some ch) :
  Model.SparseRatchet.skipSurvivors (Proofs.SparseReachableStore.run (Model.SparseRatchet.init sk dir) ops) e ch.n
      upto =
    (Proofs.SparseReachableStore.run (Model.SparseRatchet.init sk dir) ops).skipped
-/
#guard_msgs in
#check Proofs.SparseReachableStore.reachable_skipSurvivors_eq

/--
info: Proofs.SparseReachableStore.witness_reachable_holds_stored_keys (sk : Model.State.Key) :
  List.map (fun x => (x.fst, x.snd.fst))
        (Proofs.SparseReachableStore.run (Model.SparseRatchet.init sk Model.SparseRatchet.Direction.b2a)
            [Proofs.SparseReachableStore.Op.receive 0 none 3]).skipped =
      [(0, 1), (0, 2)] ∧
    ∃ cs ch,
      Model.SparseRatchet.findChains
            (Proofs.SparseReachableStore.run (Model.SparseRatchet.init sk Model.SparseRatchet.Direction.b2a)
              [Proofs.SparseReachableStore.Op.receive 0 none 3])
            0 =
          some cs ∧
        cs.receive = some ch ∧ ch.n = 3
-/
#guard_msgs in
#check Proofs.SparseReachableStore.witness_reachable_holds_stored_keys

/--
info: Proofs.SparseReachableStore.witness_store_past_its_counter_fails (sk k : Model.State.Key) :
  have st :=
    have __src := Model.SparseRatchet.init sk Model.SparseRatchet.Direction.b2a;
    { rk := __src.rk, epoch := __src.epoch, chains := __src.chains, skipped := [(0, 1, k)],
      direction := __src.direction };
  ¬Proofs.SparseReachableStore.KeysAtMostCounter st ∧
    ¬Proofs.SparseReachableStore.KeysBelowCounter st ∧ Model.SparseRatchet.skipSurvivors st 0 0 1 = [] ∧ st.skipped ≠ []
-/
#guard_msgs in
#check Proofs.SparseReachableStore.witness_store_past_its_counter_fails

/--
info: Proofs.SparseReachableStore.skip_alone_leaves_a_key_at_the_counter (sk : Model.State.Key) :
  ∃ st',
    Model.SparseRatchet.skipMessageKeys (Model.SparseRatchet.init sk Model.SparseRatchet.Direction.b2a) 0 2 = some st' ∧
      Proofs.SparseReachableStore.KeysAtMostCounter st' ∧ ¬Proofs.SparseReachableStore.KeysBelowCounter st'
-/
#guard_msgs in
#check Proofs.SparseReachableStore.skip_alone_leaves_a_key_at_the_counter

/--
info: Proofs.SparseReachableStore.chainsNotAhead_needed_for_advance (rk ck k key : Model.State.Key)
  (dir : Model.SparseRatchet.Direction) :
  have st :=
    { rk := rk, epoch := 0,
      chains :=
        [(0, { send := none, receive := some { ck := ck, n := 0 } }),
          (1, { send := none, receive := some { ck := ck, n := 5 } })],
      skipped := [(1, 1, k)], direction := dir };
  Proofs.SparseReachableStore.KeysBelowCounter st ∧
    ¬Proofs.SparseReachableStore.ChainsNotAhead st ∧
      ∃ st',
        Model.SparseRatchet.advance st { keyEpoch := 1, key := key } = some st' ∧
          ¬Proofs.SparseReachableStore.KeysBelowCounter st'
-/
#guard_msgs in
#check Proofs.SparseReachableStore.chainsNotAhead_needed_for_advance

/--
info: 'Proofs.SparseReachableStore.init_keysBelowCounter' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Proofs.SparseReachableStore.init_keysBelowCounter

/--
info: 'Proofs.SparseReachableStore.init_chainsNotAhead' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Proofs.SparseReachableStore.init_chainsNotAhead

/--
info: 'Proofs.SparseReachableStore.init_reachableStore' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Proofs.SparseReachableStore.init_reachableStore

/--
info: 'Proofs.SparseReachableStore.advance_keysBelowCounter' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Proofs.SparseReachableStore.advance_keysBelowCounter

/--
info: 'Proofs.SparseReachableStore.advance_chainsNotAhead' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Proofs.SparseReachableStore.advance_chainsNotAhead

/--
info: 'Proofs.SparseReachableStore.receiveAdvance_keysBelowCounter' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Proofs.SparseReachableStore.receiveAdvance_keysBelowCounter

/--
info: 'Proofs.SparseReachableStore.send_keysBelowCounter' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Proofs.SparseReachableStore.send_keysBelowCounter

/--
info: 'Proofs.SparseReachableStore.send_chainsNotAhead' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Proofs.SparseReachableStore.send_chainsNotAhead

/--
info: 'Proofs.SparseReachableStore.send_store_bounded' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Proofs.SparseReachableStore.send_store_bounded

/--
info: 'Proofs.SparseReachableStore.trySkipped_keysBelowCounter' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Proofs.SparseReachableStore.trySkipped_keysBelowCounter

/--
info: 'Proofs.SparseReachableStore.skipMessageKeys_keysAtMostCounter' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Proofs.SparseReachableStore.skipMessageKeys_keysAtMostCounter

/--
info: 'Proofs.SparseReachableStore.skipMessageKeys_keysBelowCounter_off' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Proofs.SparseReachableStore.skipMessageKeys_keysBelowCounter_off

/--
info: 'Proofs.SparseReachableStore.receive_keysBelowCounter' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Proofs.SparseReachableStore.receive_keysBelowCounter

/--
info: 'Proofs.SparseReachableStore.receive_chainsNotAhead' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Proofs.SparseReachableStore.receive_chainsNotAhead

/--
info: 'Proofs.SparseReachableStore.receive_store_bounded' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Proofs.SparseReachableStore.receive_store_bounded

/--
info: 'Proofs.SparseReachableStore.evictOldest_keysBelowCounter' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Proofs.SparseReachableStore.evictOldest_keysBelowCounter

/--
info: 'Proofs.SparseReachableStore.evictOldest_store_bounded' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Proofs.SparseReachableStore.evictOldest_store_bounded

/--
info: 'Proofs.SparseReachableStore.clearOldEpochs_keysBelowCounter' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Proofs.SparseReachableStore.clearOldEpochs_keysBelowCounter

/--
info: 'Proofs.SparseReachableStore.skipSurvivors_eq_of_keysAtMostCounter' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Proofs.SparseReachableStore.skipSurvivors_eq_of_keysAtMostCounter

/--
info: 'Proofs.SparseReachableStore.skipSurvivors_eq_of_keysBelowCounter' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Proofs.SparseReachableStore.skipSurvivors_eq_of_keysBelowCounter

/--
info: 'Proofs.SparseReachableStore.apply_reachableStore' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Proofs.SparseReachableStore.apply_reachableStore

/--
info: 'Proofs.SparseReachableStore.run_reachableStore' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Proofs.SparseReachableStore.run_reachableStore

/--
info: 'Proofs.SparseReachableStore.run_store_bounded' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Proofs.SparseReachableStore.run_store_bounded

/--
info: 'Proofs.SparseReachableStore.reachable_keysBelowCounter' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Proofs.SparseReachableStore.reachable_keysBelowCounter

/--
info: 'Proofs.SparseReachableStore.reachable_store_bounded' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Proofs.SparseReachableStore.reachable_store_bounded

/--
info: 'Proofs.SparseReachableStore.reachable_skipSurvivors_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Proofs.SparseReachableStore.reachable_skipSurvivors_eq

/--
info: 'Proofs.SparseReachableStore.witness_reachable_holds_stored_keys' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Proofs.SparseReachableStore.witness_reachable_holds_stored_keys

/--
info: 'Proofs.SparseReachableStore.witness_store_past_its_counter_fails' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Proofs.SparseReachableStore.witness_store_past_its_counter_fails

/--
info: 'Proofs.SparseReachableStore.skip_alone_leaves_a_key_at_the_counter' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Proofs.SparseReachableStore.skip_alone_leaves_a_key_at_the_counter

/--
info: 'Proofs.SparseReachableStore.chainsNotAhead_needed_for_advance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Proofs.SparseReachableStore.chainsNotAhead_needed_for_advance
