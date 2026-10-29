import Translation.UnitLifecycleDecryptCompose
import Batteries.Tactic.OpenPrivate

/-!
# `Session::decrypt` keeps `Session::invariant` at every frame: a stored key, a skip, an eviction

`UnitLifecycleDecryptPreserve` shows that a successful `decrypt_ratchet` or `decrypt` keeps `Session::invariant` and
spends at most one unit of the counter budget, given the relation after the call and a model step in the in-order scope
(`ReceiveStep`: no stored key used, no message skipped on either chain, no eviction), and
`UnitLifecycleDecryptCompose` composes that with the decrypt refinement for a frame in that scope (`FrameInOrder`).
This module drops the scope.  Its model step, `ReceiveStepAny`, is the model's receive with eviction
(`Model.Lifecycle.receiveWithEviction`) of any header, so it includes a stored key used, a skip on either chain (on the
classical side on the peer's chain, or on the chain being left and on the new one) and the retry that evicts the oldest
stored keys from a full store.  The model's own `decryptRatchet` of every frame is such a step with no hypothesis, so
composed with the decrypt refinement neither the relation after the call, nor the model step, nor a scope is a
hypothesis.

## What it shows

* The classical receive, every case: `ratchet_receive_cases` (a stored key taken, or the chain chosen, `SteppedTo`, a
  skip to the header's number and the step), `ratchet_receive_any_frame` (the sending key kept or the candidate, the
  clock up by at most one), and `modelRatchetInv_receive_any`: every successful classical receive keeps
  `ModelRatchetInv` given a canonical header key and, on a Diffie-Hellman step, a canonical candidate
  (`modelRatchetInv_skip`: the skip's own check bounds the store, the skipped keys are stored at the clock, the store
  stays a map).
* The sparse receive, every case: `modelSpqrInv_receive_any`: every successful sparse receive without the agreement's
  output keeps `ModelSpqrInv`, the epoch and the direction, and moves every chain counter by at most `maxSkip + 1`.
* Eviction: `receiveWithEviction_ok_shrunk`: every successful receive with eviction is one Triple receive at a state
  whose two stores are sublists of the session's (`StoreShrunk`), for every fuel of the model's retry loop
  (`loop_ok_shrunk`, which names the private loop through `open private`, as `UnitLifecycleRetryLoopT3` does).
* The Triple: `triple_receive_any`, `triple_receive_any_frame`: every successful Triple receive at every header, with or
  without the agreement's output, keeps `ModelTripleInv` and its frame.
* The session's step: `decryptRatchet_receiveStepAny`, `decrypt_receiveStepAny` (the model's step of every frame is a
  `ReceiveStepAny`, no hypothesis); `modelTripleInv_stepAny`, `modelCounterRoom_stepAny`, `step_frame_stepAny` (such a
  step keeps the Triple's invariant, spends at most one unit of the budget, and keeps the direction, clause (b) and the
  role).
* The keys a receive leaves: `decryptRatchet_consumes`: on every frame the model accepts, no stored classical key for
  the frame's ratchet key and number and no stored sparse key for its epoch and number is kept.
* The code: `decrypt_ratchet_keeps_invariant_any`, `decrypt_keeps_invariant_any`: every successful `decrypt_ratchet`
  and `decrypt` whose session refines a `ReceiveStepAny` from the model session keeps `Session::invariant` and spends one
  unit of the budget; the relation after the call and the step are hypotheses.
* Composed: `decrypt_ratchet_refines_keeps_invariant_any`, `decrypt_refines_keeps_invariant_any`,
  `restored_decrypt_keeps_invariant_any`: the in-order compositions of `UnitLifecycleDecryptCompose` without
  `FrameInOrder`; `decrypt_ratchet_refines_consumes_any` adds the stored keys the returned session keeps, read through
  the relation's abstractions.

## The laws and premises

* No new law.  The step takes `ReceiveInvariantLaws`, the oracle's `dhPublic` clause and the codec relation, as
  `decrypt_ratchet_keeps_invariant` does; the composed results take the hypotheses of
  `decrypt_ratchet_refines_of_invariant` and `ReceiveInvariantLaws`.  The model lemmas take none.
* `DecryptOracleOf`'s `aeadOpen` clause is, by reading, false of the shipping AEAD at long lengths (row
  `AEAD-LENGTH-CONTRACTS`), so each composed result is conditional on a proposition that does not hold and says nothing
  about the shipping code at any length until that contract is repaired.
* The canonicity of the sending key a Diffie-Hellman step installs comes from the code (clause (a) and
  `DhPublicValid`), as in the in-order step.

## Non-vacuity

* The hypotheses of `decrypt_ratchet_refines_of_invariant` hold together at one witness session under named laws
  (`UnitLifecycleDecryptRunBounds.decrypt_of_invariant_hypotheses_jointly_satisfiable`), at a frame the screen's oracle
  refuses; no theorem shows the composed hypotheses jointly satisfiable with a successful receive, and no run reaches a
  stored key used, a skip or an eviction.  The model lemmas need no witness: the model's step and its stored-key effect
  hold of every frame.

## What it does not show

* A witness or run that exhibits the composed hypotheses with a successful receive at any frame, in or out of order:
  the success branch has no witness, and no run reaches a stored key used, a skip or an eviction.
* That the shipping AEAD meets `DecryptOracleOf` (false by reading at long lengths), or that the shipping KEM and the
  other functions meet `ReceiveInvariantLaws`, the agreements and the contracts.
* An initial-type frame through the public `decrypt`: only ratchet-type frames are composed.
* A restored session outside the restored scope, or the budget of a restored session without the caller's check.
* That the ceilings are kept (false of the code, so the statements spend a budget), or what a receive does at a session
  without the budget premise.
* The store effect for the public `decrypt` (stated for `decrypt_ratchet` only), or which keys a skip stores beyond
  their numbers.
* That a delayed frame is still decrypted after an eviction or after its key aged out.
* That `Session::invariant` says a session is reachable: it is a predicate on fields.
-/

open Aeneas Aeneas.Std Result
open tacenta_session_unit
open Tacenta.SessionUnitRatchetImportInv (bind_eq_ok_inv)

namespace Tacenta.UnitLifecycleOutOfOrderReceive

open Model.State (Key)
open Tacenta.UnitTripleInvModel
open Tacenta.UnitLifecycleSendPreserve (CounterRoom ModelCounterRoom counterRoom_zero counterRoom_iff_model
  session_invariant_iff findChains_mem mem_sent_chains)
open Tacenta.UnitLifecycleEncryptPreserve (InChain advance_ok_parts counterRoom_mono decrypt_ratchet_err_keeps_invariant
  decrypt_err_keeps_invariant braid_eta)
open Tacenta.UnitLifecycleReceivePreserve (classicalTail sparseTail sparseTail_ok keyOf_dhs clause_a_of_structural
  structural_clear_pending decrypt_ok_inner)
open Tacenta.UnitLifecycleDecryptPreserve (ReceiveInvariantLaws advancedOf triple_receive_advance
  modelTripleInv_advanced receive_epoch_le receive_clauses ModelClauseB modelIsInit CodeClauseB braidLens_of_totals
  decrypt_ratchet_ok_live braid_receive_keeps_invariant modelClauseB_of_structural braid_reads_refines
  codeClauseB_of_model structural_after)
open Tacenta.UnitLifecycleEstablishInitiatorShape (dhPublicValid_canonical)
open Tacenta.UnitLifecycleT3 (DhView DhCodecOf SessionRefines StepRefines sliceOf arrayOf
  decrypt_frame_too_long_step_refines decrypt_ratchet_message_refines message_type_refines_ratchet)
open Tacenta.UnitLifecycleDecryptRatchetT3 (DecryptOracleOf DecryptRatchetAgreements)
open Tacenta.UnitLifecycleDecryptRunBounds (CounterHeadroom DecryptRatchetRunInputs
  decrypt_ratchet_refines_of_invariant)
open Tacenta.UnitLifecycleRestoredSession (RestoredScope restoredModelOf import_ok_gives_invariant
  sessionRefines_restored honestChunk_restored)
open Tacenta.UnitLifecycleImportBudget (roomCheck counterRoom_iff_roomCheck)

/-! ## The classical receive, every case -/

/-- The chain the classical receive reads from when no stored key matches: the state itself on the peer's chain, or
the Diffie-Hellman step from the skip on the chain being left. -/
def SteppedTo (st : Model.State.State) (hdr : Model.State.Header) (dr ds np : Key) (st1 : Model.State.State) :
    Prop :=
  (st.dhrPub = some hdr.dh ∧ st1 = st) ∨
    (st.dhrPub ≠ some hdr.dh ∧ ∃ sk, Model.State.skipMessageKeys st hdr.pn = some sk ∧
      st1 = Model.Ratchet.dhRatchet sk hdr dr ds np)

/-- **Every successful classical receive is one of two cases**: a stored key taken (and the store aged), or no stored
key, the chain chosen (`SteppedTo`), a skip on it to the header's number, and the tail.  Model only. -/
theorem ratchet_receive_cases {st st' : Model.State.State} {hdr : Model.State.Header} {dr ds np mk : Key}
    (hr : Model.Ratchet.receiveDetailed st hdr dr ds np = .ok (st', mk)) :
    (∃ next, Model.Ratchet.trySkipped st hdr = some (next, mk) ∧ st' = Model.State.ageStore next) ∨
      (Model.Ratchet.trySkipped st hdr = none ∧ ∃ st1 st2, SteppedTo st hdr dr ds np st1 ∧
        Model.State.skipMessageKeys st1 hdr.n = some st2 ∧ classicalTail st2 hdr = .ok (st', mk)) := by
  unfold Model.Ratchet.receiveDetailed at hr
  rcases ht : Model.Ratchet.trySkipped st hdr with _ | ⟨next, k⟩
  · rw [ht] at hr
    right
    refine ⟨rfl, ?_⟩
    simp only at hr
    by_cases hd : st.dhrPub = some hdr.dh
    · have hb : (st.dhrPub == some hdr.dh) = true := by simp [hd]
      simp only [hb, if_true] at hr
      rcases hs : Model.Ratchet.skipMessageKeysDetailed st hdr.n with r | st2
      · rw [hs] at hr; simp at hr
      rw [hs] at hr
      refine ⟨st, st2, Or.inl ⟨hd, rfl⟩, (Model.Ratchet.skipMessageKeysDetailed_ok_iff _ _ _).mp hs, ?_⟩
      exact hr
    · have hb : (st.dhrPub == some hdr.dh) = false := by simpa using hd
      simp only [hb, Bool.false_eq_true, if_false] at hr
      rcases hs1 : Model.Ratchet.skipMessageKeysDetailed st hdr.pn with r | sk
      · rw [hs1] at hr; simp at hr
      rw [hs1] at hr
      simp only at hr
      rcases hs : Model.Ratchet.skipMessageKeysDetailed (Model.Ratchet.dhRatchet sk hdr dr ds np) hdr.n with r | st2
      · rw [hs] at hr; simp at hr
      rw [hs] at hr
      refine ⟨_, st2, Or.inr ⟨hd, sk, (Model.Ratchet.skipMessageKeysDetailed_ok_iff _ _ _).mp hs1, rfl⟩,
        (Model.Ratchet.skipMessageKeysDetailed_ok_iff _ _ _).mp hs, ?_⟩
      exact hr
  · rw [ht] at hr
    simp only [Except.ok.injEq, Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    exact Or.inl ⟨next, rfl, rfl⟩

/-- A stored key taken leaves the state with a store that is a sublist of the old one and every other field as it
was.  Model only. -/
theorem ratchet_trySkipped_shape {st next : Model.State.State} {hdr : Model.State.Header} {mk : Key}
    (h : Model.Ratchet.trySkipped st hdr = some (next, mk)) :
    next = { st with skipped := next.skipped } ∧ next.skipped.Sublist st.skipped := by
  unfold Model.Ratchet.trySkipped at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact ⟨rfl, List.filter_sublist⟩
  · simp at h

/-- **A store shrunk to a sublist keeps `ModelRatchetInv`.**  Model only. -/
theorem modelRatchetInv_shrink {st : Model.State.State} {l : List (Key × Nat × Nat × Key)}
    (h : ModelRatchetInv st) (hl : l.Sublist st.skipped) : ModelRatchetInv { st with skipped := l } :=
  ⟨Nat.le_trans hl.length_le h.store_bound, h.clock_room, fun e he => h.fresh e (hl.subset he),
    h.store_map.sublist hl, h.chains, h.dhs_canonical, h.dhr_canonical,
    by simpa using fun e he => h.store_canonical e (hl.subset he)⟩

/-- **Ageing the store keeps `ModelRatchetInv`.**  Model only. -/
theorem modelRatchetInv_ageStore {st : Model.State.State} (h : ModelRatchetInv st) :
    ModelRatchetInv (Model.State.ageStore st) := by
  have hmax : st.events ≤ Model.State.maxEvents := by
    have := h.clock_room; unfold Model.State.maxEvents; omega
  have hsub : (st.skipped.filter fun e => decide (min (st.events + 1) Model.State.maxEvents - e.2.2.1 <
      Model.State.maxSkippedAge)).Sublist st.skipped := List.filter_sublist
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Model.State.ageStore]; exact Nat.le_trans hsub.length_le h.store_bound
  · exact Model.State.ageStore_events_lt _
  · simp only [Model.State.ageStore]
    intro e he
    have := h.fresh e (hsub.subset he)
    omega
  · simp only [Model.State.ageStore]; exact h.store_map.sublist hsub
  · simpa [Model.State.ageStore] using h.chains
  · simpa [Model.State.ageStore] using h.dhs_canonical
  · simpa [Model.State.ageStore] using h.dhr_canonical
  · simp only [Model.State.ageStore]
    intro e he
    exact h.store_canonical e (hsub.subset he)

theorem deriveChain_length (ck : Key) (start c : Nat) :
    (Model.State.deriveChain ck start c).2.length = c := by
  induction c generalizing ck start with
  | zero => rfl
  | succ c ih =>
    show ((start, (Model.State.kdfCk ck).2) :: (Model.State.deriveChain (Model.State.kdfCk ck).1 (start + 1) c).2).length
      = c + 1
    rw [List.length_cons, ih]

theorem deriveChain_num_ge (ck : Key) (start c : Nat) :
    ∀ x ∈ (Model.State.deriveChain ck start c).2, start ≤ x.1 := by
  induction c generalizing ck start with
  | zero => simp [Model.State.deriveChain]
  | succ c ih =>
    intro x hx
    have : (Model.State.deriveChain ck start (c + 1)).2
        = (start, (Model.State.kdfCk ck).2) :: (Model.State.deriveChain (Model.State.kdfCk ck).1 (start + 1) c).2 :=
      rfl
    rw [this, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact Nat.le_refl _
    · exact Nat.le_of_succ_le (ih (Model.State.kdfCk ck).1 (start + 1) x hx)

theorem deriveChain_num_lt (ck : Key) (start c : Nat) :
    ∀ x ∈ (Model.State.deriveChain ck start c).2, x.1 < start + c := by
  induction c generalizing ck start with
  | zero => simp [Model.State.deriveChain]
  | succ c ih =>
    intro x hx
    have : (Model.State.deriveChain ck start (c + 1)).2
        = (start, (Model.State.kdfCk ck).2) :: (Model.State.deriveChain (Model.State.kdfCk ck).1 (start + 1) c).2 :=
      rfl
    rw [this, List.mem_cons] at hx
    rcases hx with rfl | hx
    · omega
    · have := ih (Model.State.kdfCk ck).1 (start + 1) x hx
      omega

theorem deriveChain_nodup (ck : Key) (start c : Nat) :
    (Model.State.deriveChain ck start c).2.Pairwise fun a b => a.1 ≠ b.1 := by
  induction c generalizing ck start with
  | zero => simp [Model.State.deriveChain]
  | succ c ih =>
    have heq : (Model.State.deriveChain ck start (c + 1)).2
        = (start, (Model.State.kdfCk ck).2) :: (Model.State.deriveChain (Model.State.kdfCk ck).1 (start + 1) c).2 :=
      rfl
    rw [heq, List.pairwise_cons]
    refine ⟨?_, ih (Model.State.kdfCk ck).1 (start + 1)⟩
    intro b hb
    have := deriveChain_num_ge (Model.State.kdfCk ck).1 (start + 1) c b hb
    omega

/-- **A successful classical skip keeps `ModelRatchetInv`**, and leaves the sending key, the peer's key, the clock and
the presence of a receiving chain as they were.  Model only. -/
theorem modelRatchetInv_skip {st st' : Model.State.State} {upto : Nat}
    (h : ModelRatchetInv st) (hs : Model.State.skipMessageKeys st upto = some st') :
    ModelRatchetInv st' ∧ st'.dhsPub = st.dhsPub ∧ st'.dhrPub = st.dhrPub ∧ st'.events = st.events ∧
      st'.cks = st.cks ∧ st'.ckr.isSome = st.ckr.isSome := by
  unfold Model.State.skipMessageKeys at hs
  split at hs
  · rename_i ck dhr hck hdhr
    split at hs
    · simp only [Option.some.injEq] at hs; subst hs
      exact ⟨h, rfl, rfl, rfl, rfl, rfl⟩
    split at hs
    · simp at hs
    split at hs
    · simp at hs
    rename_i hle hmax hbound
    simp only [Option.some.injEq] at hs
    subst hs
    refine ⟨⟨?_, h.clock_room, ?_, ?_, ?_, h.dhs_canonical, h.dhr_canonical, ?_⟩, rfl, rfl, rfl, rfl,
      by simp [hck]⟩
    · simp only [List.length_append, List.length_map, deriveChain_length]
      omega
    · intro e he
      simp only [List.mem_append, List.mem_map] at he
      rcases he with he | ⟨x, -, rfl⟩
      · exact h.fresh e (List.mem_filter.mp he).1
      · exact Nat.le_refl _
    · rw [List.pairwise_append]
      refine ⟨h.store_map.sublist List.filter_sublist, ?_, ?_⟩
      · refine List.Pairwise.map _ ?_ (deriveChain_nodup ck st.nr (upto - st.nr))
        intro a b hab
        rintro ⟨-, hn⟩
        exact hab hn
      · intro a ha b hb
        simp only [Model.State.skipSurvivors, List.mem_filter] at ha
        simp only [List.mem_map] at hb
        obtain ⟨-, hakeep⟩ := ha
        obtain ⟨y, hy, rfl⟩ := hb
        simp only [Bool.not_eq_true', Bool.and_eq_false_iff, beq_eq_false_iff_ne,
          decide_eq_false_iff_not] at hakeep
        intro ⟨hdh, hn⟩
        have hlo := deriveChain_num_ge ck st.nr (upto - st.nr) y hy
        have hhi := deriveChain_num_lt ck st.nr (upto - st.nr) y hy
        simp only at hdh hn
        rcases hakeep with hk | hk
        · rcases hk with hk | hk
          · exact hk hdh
          · omega
        · omega
    · simpa [hck, hdhr] using h.chains
    · intro e he
      simp only [List.mem_append, List.mem_map] at he
      rcases he with he | ⟨x, -, rfl⟩
      · exact h.store_canonical e (List.mem_filter.mp he).1
      · exact h.dhr_canonical dhr hdhr
  · simp only [Option.some.injEq] at hs; subst hs
    exact ⟨h, rfl, rfl, rfl, rfl, rfl⟩

/-- **The Diffie-Hellman step keeps `ModelRatchetInv`** given a canonical header key and a canonical candidate key.
Model only. -/
theorem modelRatchetInv_dhRatchet {st : Model.State.State} {hdr : Model.State.Header} {dr ds np : Key}
    (h : ModelRatchetInv st) (hhdr : Model.Messages.canonicalKey hdr.dh = true)
    (hnp : Model.Messages.canonicalKey np = true) :
    ModelRatchetInv (Model.Ratchet.dhRatchet st hdr dr ds np) := by
  refine ⟨h.store_bound, h.clock_room, h.fresh, h.store_map, fun _ => ⟨rfl, rfl⟩, hnp, ?_, h.store_canonical⟩
  intro k hk
  simp only [Model.Ratchet.dhRatchet, Option.some.injEq] at hk
  rw [← hk]; exact hhdr

/-- **The classical tail keeps `ModelRatchetInv`.**  Model only. -/
theorem modelRatchetInv_classicalTail {st st' : Model.State.State} {hdr : Model.State.Header} {mk : Key}
    (h : ModelRatchetInv st) (ht : classicalTail st hdr = .ok (st', mk)) : ModelRatchetInv st' ∧
      st'.dhsPub = st.dhsPub ∧ st'.events ≤ st.events + 1 := by
  unfold classicalTail at ht
  split at ht
  · simp at ht
  rcases hc : st.ckr with _ | ck
  · rw [hc] at ht; simp at ht
  rw [hc] at ht
  simp only at ht
  split at ht
  · simp only [Except.ok.injEq, Prod.mk.injEq] at ht
    obtain ⟨rfl, -⟩ := ht
    refine ⟨modelRatchetInv_ageStore ⟨h.store_bound, h.clock_room, h.fresh, h.store_map, ?_, h.dhs_canonical,
      h.dhr_canonical, h.store_canonical⟩, rfl, ?_⟩
    · intro _; exact h.chains (by rw [hc]; rfl)
    · simp only [Model.State.ageStore]; omega
  · simp at ht

/-- **Every successful classical receive keeps `ModelRatchetInv`**: a stored key taken, a skip on the peer's chain,
a skip on the chain being left and on the new one, given a canonical header key and, when the receive takes a
Diffie-Hellman step, a canonical candidate key.  Model only. -/
theorem modelRatchetInv_receive_any {st st' : Model.State.State} {hdr : Model.State.Header}
    {dr ds np mk : Key} (h : ModelRatchetInv st) (hhdr : Model.Messages.canonicalKey hdr.dh = true)
    (hnp : Model.Ratchet.trySkipped st hdr = none → st.dhrPub ≠ some hdr.dh →
      Model.Messages.canonicalKey np = true)
    (hr : Model.Ratchet.receiveDetailed st hdr dr ds np = .ok (st', mk)) :
    ModelRatchetInv st' := by
  rcases ratchet_receive_cases hr with ⟨next, ht, rfl⟩ | ⟨ht, st1, st2, hst1, hs2, htail⟩
  · obtain ⟨hn, hsub⟩ := ratchet_trySkipped_shape ht
    rw [hn]
    exact modelRatchetInv_ageStore (modelRatchetInv_shrink h hsub)
  · have h1 : ModelRatchetInv st1 := by
      rcases hst1 with ⟨-, rfl⟩ | ⟨hd, sk, hsk, rfl⟩
      · exact h
      · exact modelRatchetInv_dhRatchet (modelRatchetInv_skip h hsk).1 hhdr (hnp ht hd)
    exact (modelRatchetInv_classicalTail (modelRatchetInv_skip h1 hs2).1 htail).1

/-- A successful classical skip leaves the sending key, the sending chain, the clock and the presence of a receiving
chain as they were.  Model only. -/
theorem skip_frame {st st' : Model.State.State} {upto : Nat}
    (hs : Model.State.skipMessageKeys st upto = some st') :
    st'.dhsPub = st.dhsPub ∧ st'.events = st.events ∧ st'.cks = st.cks := by
  unfold Model.State.skipMessageKeys at hs
  split at hs
  · split at hs
    · simp only [Option.some.injEq] at hs; subst hs; exact ⟨rfl, rfl, rfl⟩
    split at hs
    · simp at hs
    split at hs
    · simp at hs
    simp only [Option.some.injEq] at hs; subst hs; exact ⟨rfl, rfl, rfl⟩
  · simp only [Option.some.injEq] at hs; subst hs; exact ⟨rfl, rfl, rfl⟩

/-- **The classical receive's frame, every case**: on a Diffie-Hellman step (no stored key, a new peer key) the
sending key is the candidate; otherwise, and in every case, it is kept or is the candidate; the clock rises by at most
one; and either both chains are as they were (a stored key taken) or a receiving chain is held.  Model only. -/
theorem ratchet_receive_any_frame {st st' : Model.State.State} {hdr : Model.State.Header} {dr ds np mk : Key}
    (hr : Model.Ratchet.receiveDetailed st hdr dr ds np = .ok (st', mk)) :
    (Model.Ratchet.trySkipped st hdr = none → st.dhrPub ≠ some hdr.dh → st'.dhsPub = np) ∧
      (st'.dhsPub = st.dhsPub ∨ st'.dhsPub = np) ∧ st'.events ≤ st.events + 1 ∧
      ((st'.cks = st.cks ∧ st'.ckr = st.ckr) ∨ st'.ckr.isSome = true) := by
  rcases ratchet_receive_cases hr with ⟨next, ht, rfl⟩ | ⟨ht, st1, st2, hst1, hs2, htail⟩
  · obtain ⟨hn, -⟩ := ratchet_trySkipped_shape ht
    rw [hn]
    refine ⟨fun h => absurd (ht.symm.trans h) (by simp), Or.inl rfl, ?_, Or.inl ⟨rfl, rfl⟩⟩
    simp only [Model.State.ageStore]; omega
  · have htl : st'.dhsPub = st2.dhsPub ∧ st'.events ≤ st2.events + 1 ∧ st'.ckr.isSome = true := by
      obtain ⟨ck, -, -, rfl⟩ := Tacenta.UnitLifecycleReceivePreserve.classicalTail_ok htail
      refine ⟨rfl, ?_, rfl⟩
      simp only [Model.State.ageStore]; omega
    obtain ⟨h2d, h2e, -⟩ := skip_frame hs2
    rcases hst1 with ⟨hd, rfl⟩ | ⟨hd, sk, hsk1, rfl⟩
    · exact ⟨fun _ h => absurd hd h, Or.inl (htl.1.trans h2d), by omega, Or.inr htl.2.2⟩
    · obtain ⟨-, h1e, -⟩ := skip_frame hsk1
      have hev : (Model.Ratchet.dhRatchet sk hdr dr ds np).events = sk.events := rfl
      have hdn : st'.dhsPub = np := htl.1.trans h2d
      exact ⟨fun _ _ => hdn, Or.inr hdn, by omega, Or.inr htl.2.2⟩

/-! ## The sparse receive, every case -/

/-- Replacing one entry of the table at an epoch it holds keeps every clause of `ModelSpqrInv` that reads the table,
for every store whose entries are chained in the old table. -/
theorem modelSpqrInv_setChains {st : Model.SparseRatchet.State} {e : Nat} {cs c' : Model.SparseRatchet.Chains}
    {l : List (Nat × Nat × Key)}
    (h : ModelSpqrInv st) (hmem : (e, cs) ∈ st.chains)
    (hbound : l.length ≤ Model.SparseRatchet.maxSkippedStore)
    (hchained : ∀ a ∈ l, ∃ q ∈ st.chains, q.1 = a.1)
    (hmap : l.Pairwise (fun a b => ¬ (a.1 = b.1 ∧ a.2.1 = b.2.1))) :
    ModelSpqrInv (Model.SparseRatchet.setChains { st with skipped := l } e c') := by
  refine ⟨hbound, ?_, ?_, ?_, ?_, hmap⟩
  · intro q hq
    simp only [Model.SparseRatchet.setChains] at hq ⊢
    rcases mem_sent_chains hq with ⟨hq', -⟩ | rfl
    · exact h.epoch_window q hq'
    · exact h.epoch_window (e, cs) hmem
  · simp only [Model.SparseRatchet.setChains]
    rw [List.pairwise_append]
    refine ⟨h.chains_distinct.sublist List.filter_sublist, List.pairwise_singleton _ _, ?_⟩
    intro a ha b hb
    simp only [List.mem_filter, Bool.not_eq_true', beq_eq_false_iff_ne] at ha
    simp only [List.mem_singleton] at hb
    subst hb
    exact ha.2
  · obtain ⟨q, hq, hqe⟩ := h.current_present
    simp only [Model.SparseRatchet.setChains]
    by_cases hqe' : q.1 = e
    · exact ⟨(e, _), List.mem_append_right _ (List.mem_singleton_self _), by rw [← hqe', hqe]⟩
    · exact ⟨q, List.mem_append_left _ (List.mem_filter.mpr ⟨hq, by simpa using hqe'⟩), hqe⟩
  · intro a ha
    obtain ⟨q, hq, hqa⟩ := hchained a ha
    simp only [Model.SparseRatchet.setChains]
    by_cases hqe' : q.1 = e
    · exact ⟨(e, _), List.mem_append_right _ (List.mem_singleton_self _), by rw [← hqe', hqa]⟩
    · exact ⟨q, List.mem_append_left _ (List.mem_filter.mpr ⟨hq, by simpa using hqe'⟩), hqa⟩

theorem deriveInto_length (ck : Key) (start c : Nat) :
    (Model.SparseRatchet.skipMessageKeys.deriveInto ck start c).2.length = c := by
  induction c generalizing ck start with
  | zero => rfl
  | succ c ih =>
    simpa [Model.SparseRatchet.skipMessageKeys.deriveInto] using
      ih (Model.SparseRatchet.kdfCk ck (start + 1)).1 (start + 1)

theorem deriveInto_num_gt (ck : Key) (start c : Nat) :
    ∀ x ∈ (Model.SparseRatchet.skipMessageKeys.deriveInto ck start c).2, start < x.1 := by
  induction c generalizing ck start with
  | zero => simp [Model.SparseRatchet.skipMessageKeys.deriveInto]
  | succ c ih =>
    intro x hx
    have h : (Model.SparseRatchet.skipMessageKeys.deriveInto ck start (c + 1)).2
        = (start + 1, (Model.SparseRatchet.kdfCk ck (start + 1)).2)
          :: (Model.SparseRatchet.skipMessageKeys.deriveInto (Model.SparseRatchet.kdfCk ck (start + 1)).1
            (start + 1) c).2 := rfl
    rw [h, List.mem_cons] at hx
    rcases hx with rfl | hx
    · omega
    · have := ih (Model.SparseRatchet.kdfCk ck (start + 1)).1 (start + 1) x hx
      omega

theorem deriveInto_num_le (ck : Key) (start c : Nat) :
    ∀ x ∈ (Model.SparseRatchet.skipMessageKeys.deriveInto ck start c).2, x.1 ≤ start + c := by
  induction c generalizing ck start with
  | zero => simp [Model.SparseRatchet.skipMessageKeys.deriveInto]
  | succ c ih =>
    intro x hx
    have h : (Model.SparseRatchet.skipMessageKeys.deriveInto ck start (c + 1)).2
        = (start + 1, (Model.SparseRatchet.kdfCk ck (start + 1)).2)
          :: (Model.SparseRatchet.skipMessageKeys.deriveInto (Model.SparseRatchet.kdfCk ck (start + 1)).1
            (start + 1) c).2 := rfl
    rw [h, List.mem_cons] at hx
    rcases hx with rfl | hx
    · omega
    · have := ih (Model.SparseRatchet.kdfCk ck (start + 1)).1 (start + 1) x hx
      omega

theorem deriveInto_nodup (ck : Key) (start c : Nat) :
    (Model.SparseRatchet.skipMessageKeys.deriveInto ck start c).2.Pairwise fun a b => a.1 ≠ b.1 := by
  induction c generalizing ck start with
  | zero => simp [Model.SparseRatchet.skipMessageKeys.deriveInto]
  | succ c ih =>
    have h : (Model.SparseRatchet.skipMessageKeys.deriveInto ck start (c + 1)).2
        = (start + 1, (Model.SparseRatchet.kdfCk ck (start + 1)).2)
          :: (Model.SparseRatchet.skipMessageKeys.deriveInto (Model.SparseRatchet.kdfCk ck (start + 1)).1
            (start + 1) c).2 := rfl
    rw [h, List.pairwise_cons]
    refine ⟨?_, ih (Model.SparseRatchet.kdfCk ck (start + 1)).1 (start + 1)⟩
    intro b hb
    have := deriveInto_num_gt (Model.SparseRatchet.kdfCk ck (start + 1)).1 (start + 1) c b hb
    omega

/-- **A successful sparse skip keeps `ModelSpqrInv`**, the epoch and the direction, and every chain counter of the
new table is a counter of the old table or the skipped chain's counter moved by at most `maxSkip`.  Model only. -/
theorem modelSpqrInv_skip {st st' : Model.SparseRatchet.State} {e upto : Nat}
    (h : ModelSpqrInv st) (hs : Model.SparseRatchet.skipMessageKeys st e upto = some st') :
    ModelSpqrInv st' ∧ st'.epoch = st.epoch ∧ st'.direction = st.direction ∧
      ∀ p ∈ st'.chains, ∀ c, InChain p c → ∃ p0 ∈ st.chains, ∃ c0, InChain p0 c0 ∧
        c.n ≤ c0.n + Model.SparseRatchet.maxSkip := by
  unfold Model.SparseRatchet.skipMessageKeys at hs
  rcases hf : Model.SparseRatchet.findChains st e with _ | cs
  · rw [hf] at hs; simp at hs
  rw [hf] at hs
  simp only at hs
  rcases hr : cs.receive with _ | ch
  · rw [hr] at hs; simp at hs
  rw [hr] at hs
  simp only at hs
  have hmem := findChains_mem hf
  have hsame : ∀ p ∈ st.chains, ∀ c, InChain p c → ∃ p0 ∈ st.chains, ∃ c0, InChain p0 c0 ∧
      c.n ≤ c0.n + Model.SparseRatchet.maxSkip := fun p hp c hc => ⟨p, hp, c, hc, Nat.le_add_right _ _⟩
  split at hs
  · simp only [Option.some.injEq] at hs; subst hs
    exact ⟨h, rfl, rfl, hsame⟩
  split at hs
  · simp at hs
  split at hs
  · simp at hs
  rename_i hle hmax hbound
  simp only [Option.some.injEq] at hs
  subst hs
  refine ⟨modelSpqrInv_setChains h hmem ?_ ?_ ?_, rfl, rfl, ?_⟩
  · simp only [List.length_append, List.length_map, deriveInto_length]
    omega
  · intro a ha
    simp only [List.mem_append, List.mem_map] at ha
    rcases ha with ha | ⟨x, -, rfl⟩
    · exact h.skipped_chained a (List.mem_filter.mp ha).1
    · exact ⟨(e, cs), hmem, rfl⟩
  · rw [List.pairwise_append]
    refine ⟨h.skipped_map.sublist List.filter_sublist, ?_, ?_⟩
    · refine List.Pairwise.map _ ?_ (deriveInto_nodup ch.ck ch.n (upto - ch.n))
      intro a b hab
      rintro ⟨-, hn⟩
      exact hab hn
    · intro a ha b hb
      simp only [Model.SparseRatchet.skipSurvivors, List.mem_filter] at ha
      simp only [List.mem_map] at hb
      obtain ⟨-, hakeep⟩ := ha
      obtain ⟨y, hy, rfl⟩ := hb
      simp only [Bool.not_eq_true', Bool.and_eq_false_iff, beq_eq_false_iff_ne,
        decide_eq_false_iff_not] at hakeep
      intro ⟨hep, hn⟩
      have hlo := deriveInto_num_gt ch.ck ch.n (upto - ch.n) y hy
      have hhi := deriveInto_num_le ch.ck ch.n (upto - ch.n) y hy
      simp only at hep hn
      rcases hakeep with hk | hk
      · rcases hk with hk | hk
        · exact hk hep
        · omega
      · omega
  · intro p hp c hc
    simp only [Model.SparseRatchet.setChains] at hp
    rcases mem_sent_chains hp with ⟨hp', -⟩ | rfl
    · exact ⟨p, hp', c, hc, Nat.le_add_right _ _⟩
    · rcases hc with hc | hc
      · exact ⟨(e, cs), hmem, c, Or.inl hc, Nat.le_add_right _ _⟩
      · simp only [Option.some.injEq] at hc
        subst hc
        refine ⟨(e, cs), hmem, ch, Or.inr hr, ?_⟩
        simp only
        omega

/-- **The sparse tail keeps `ModelSpqrInv`**, the epoch and the direction, and steps one chain counter by one.  Model
only. -/
theorem modelSpqrInv_sparseTail {st st' : Model.SparseRatchet.State} {e n : Nat} {mk : Key}
    (h : ModelSpqrInv st) (ht : sparseTail st e n = .ok (st', mk)) :
    ModelSpqrInv st' ∧ st'.epoch = st.epoch ∧ st'.direction = st.direction ∧
      ∀ p ∈ st'.chains, ∀ c, InChain p c → ∃ p0 ∈ st.chains, ∃ c0, InChain p0 c0 ∧ c.n ≤ c0.n + 1 := by
  obtain ⟨cs, ch, hmem, hrecv, hn, -, rfl⟩ := sparseTail_ok ht
  refine ⟨?_, rfl, rfl, ?_⟩
  · exact modelSpqrInv_setChains (l := st.skipped) h hmem h.store_bound h.skipped_chained h.skipped_map
  · intro p hp c hc
    simp only [Model.SparseRatchet.setChains] at hp
    rcases mem_sent_chains hp with ⟨hp', -⟩ | rfl
    · exact ⟨p, hp', c, hc, Nat.le_add_right _ _⟩
    · rcases hc with hc | hc
      · exact ⟨(e, cs), hmem, c, Or.inl hc, Nat.le_add_right _ _⟩
      · simp only [Option.some.injEq] at hc
        subst hc
        exact ⟨(e, cs), hmem, ch, Or.inr hrecv, by simp only; omega⟩

/-- Every successful sparse receive without an agreement output: a stored key taken, or a skip and the tail. -/
theorem spqr_receive_cases {st st' : Model.SparseRatchet.State} {e n : Nat} {mk : Key}
    (hr : Model.SparseRatchet.receiveDetailed st e none n = .ok (st', mk)) :
    Model.SparseRatchet.trySkipped st e n = some (st', mk) ∨
      (Model.SparseRatchet.trySkipped st e n = none ∧ ∃ st2,
        Model.SparseRatchet.skipMessageKeys st e (n - 1) = some st2 ∧ sparseTail st2 e n = .ok (st', mk)) := by
  unfold Model.SparseRatchet.receiveDetailed Model.SparseRatchet.maybeAdvanceReceiveDetailed
    Model.SparseRatchet.maybeAdvanceDetailed at hr
  simp only at hr
  rcases ht : Model.SparseRatchet.trySkipped st e n with _ | r
  · rw [ht] at hr
    simp only at hr
    right
    refine ⟨rfl, ?_⟩
    rcases hs : Model.SparseRatchet.skipMessageKeysDetailed st e (n - 1) with r | st2
    · rw [hs] at hr; simp at hr
    rw [hs] at hr
    refine ⟨st2, (Model.SparseRatchet.skipMessageKeysDetailed_ok_iff _ _ _ _).mp hs, ?_⟩
    simp only at hr
    unfold sparseTail
    exact hr
  · rw [ht] at hr
    simp only [Except.ok.injEq] at hr
    left; rw [hr]

/-- A stored sparse key taken leaves the state with a store that is a sublist of the old one and every other field as
it was. -/
theorem spqr_trySkipped_shape {st st' : Model.SparseRatchet.State} {e n : Nat} {mk : Key}
    (h : Model.SparseRatchet.trySkipped st e n = some (st', mk)) :
    st' = { st with skipped := st'.skipped } ∧ st'.skipped.Sublist st.skipped := by
  unfold Model.SparseRatchet.trySkipped at h
  split at h
  · simp at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact ⟨rfl, List.filter_sublist⟩

theorem modelSpqrInv_shrink {st : Model.SparseRatchet.State} {l : List (Nat × Nat × Key)}
    (h : ModelSpqrInv st) (hl : l.Sublist st.skipped) : ModelSpqrInv { st with skipped := l } :=
  ⟨Nat.le_trans hl.length_le h.store_bound, by simpa using h.epoch_window, h.chains_distinct, h.current_present,
    fun a ha => h.skipped_chained a (hl.subset ha), h.skipped_map.sublist hl⟩

/-- **Every successful sparse receive without an agreement output keeps `ModelSpqrInv`**, the epoch and the
direction, and every chain counter of the new table is at most `maxSkip + 1` more than a counter of the old table.
Model only. -/
theorem modelSpqrInv_receive_any {st st' : Model.SparseRatchet.State} {e n : Nat} {mk : Key}
    (h : ModelSpqrInv st) (hr : Model.SparseRatchet.receiveDetailed st e none n = .ok (st', mk)) :
    ModelSpqrInv st' ∧ st'.epoch = st.epoch ∧ st'.direction = st.direction ∧
      ∀ p ∈ st'.chains, ∀ c, InChain p c → ∃ p0 ∈ st.chains, ∃ c0, InChain p0 c0 ∧
        c.n ≤ c0.n + Model.SparseRatchet.maxSkip + 1 := by
  rcases spqr_receive_cases hr with ht | ⟨-, st2, hs, htail⟩
  · obtain ⟨hst, hsub⟩ := spqr_trySkipped_shape ht
    rw [hst]
    exact ⟨modelSpqrInv_shrink h hsub, rfl, rfl, fun p hp c hc => ⟨p, hp, c, hc, by omega⟩⟩
  · obtain ⟨h2, he2, hd2, hc2⟩ := modelSpqrInv_skip h hs
    obtain ⟨h3, he3, hd3, hc3⟩ := modelSpqrInv_sparseTail h2 htail
    refine ⟨h3, he3.trans he2, hd3.trans hd2, fun p hp c hc => ?_⟩
    obtain ⟨p1, hp1, c1, hc1, hle1⟩ := hc3 p hp c hc
    obtain ⟨p0, hp0, c0, hc0, hle0⟩ := hc2 p1 hp1 c1 hc1
    exact ⟨p0, hp0, c0, hc0, by omega⟩


/-! ## Eviction from a full store -/

/-- **A Triple whose two stores are sublists of another's, every other field the same**: what eviction leaves. -/
def StoreShrunk (t t0 : Model.Triple.State) : Prop :=
  t0 = { classical := { t.classical with skipped := t0.classical.skipped },
         postQuantum := { t.postQuantum with skipped := t0.postQuantum.skipped } } ∧
    t0.classical.skipped.Sublist t.classical.skipped ∧ t0.postQuantum.skipped.Sublist t.postQuantum.skipped

theorem storeShrunk_refl (t : Model.Triple.State) : StoreShrunk t t := by
  simp [StoreShrunk]

theorem storeShrunk_trans {t t1 t2 : Model.Triple.State} (h1 : StoreShrunk t t1) (h2 : StoreShrunk t1 t2) :
    StoreShrunk t t2 := by
  obtain ⟨he1, hc1, hp1⟩ := h1
  obtain ⟨he2, hc2, hp2⟩ := h2
  refine ⟨?_, hc2.trans hc1, hp2.trans hp1⟩
  rw [he2]
  simp only [Model.Triple.State.mk.injEq]
  rw [he1]
  exact ⟨rfl, rfl⟩

theorem eraseFirstSkipped_sublist (target : Model.Ratchet.SkippedEntry) (l : List Model.Ratchet.SkippedEntry) :
    (Model.Ratchet.eraseFirstSkipped target l).Sublist l := by
  induction l with
  | nil => simp [Model.Ratchet.eraseFirstSkipped]
  | cons a rest ih =>
    simp only [Model.Ratchet.eraseFirstSkipped]
    split
    · exact List.sublist_cons_self _ _
    · exact ih.cons_cons _

/-- The classical eviction removes entries and leaves every other field. -/
theorem ratchet_evictOldest_shape (st : Model.State.State) (n : Nat) :
    (Model.Ratchet.evictOldest st n).1 = { st with skipped := (Model.Ratchet.evictOldest st n).1.skipped } ∧
      (Model.Ratchet.evictOldest st n).1.skipped.Sublist st.skipped := by
  induction n generalizing st with
  | zero => simp [Model.Ratchet.evictOldest]
  | succ n ih =>
    simp only [Model.Ratchet.evictOldest]
    split
    · exact ⟨rfl, List.Sublist.refl _⟩
    · rename_i oldest _
      obtain ⟨he, hs⟩ := ih { st with skipped := Model.Ratchet.eraseFirstSkipped oldest st.skipped }
      exact ⟨he, hs.trans (eraseFirstSkipped_sublist _ _)⟩

theorem evictOldestClassical_shrunk (t : Model.Triple.State) (n : Nat) :
    StoreShrunk t (Model.Triple.evictOldestClassical t n).1 := by
  obtain ⟨he, hs⟩ := ratchet_evictOldest_shape t.classical n
  refine ⟨?_, hs, List.Sublist.refl _⟩
  simp only [Model.Triple.evictOldestClassical]
  rw [← he]

theorem evictOldestPostQuantum_shrunk (t : Model.Triple.State) (n : Nat) :
    StoreShrunk t (Model.Triple.evictOldestPostQuantum t n).1 := by
  refine ⟨rfl, List.Sublist.refl _, ?_⟩
  simp only [Model.Triple.evictOldestPostQuantum, Model.SparseRatchet.evictOldest]
  exact List.drop_sublist _ _

open private receiveWithEvictionLoop from Model.Lifecycle in
theorem loop_ok_shrunk (composite : Model.CompositeHeader.Composite) (header : Model.Triple.Header)
    (dr ds np : Key) (out : Option Model.SparseRatchet.Output) (r : Model.Triple.State × Key) :
    ∀ (fuel : Nat) (state : Model.Triple.State) (pending : Model.Triple.ReceiveRefusal)
      (half : Model.Lifecycle.FullStore) (batch : Nat),
      Model.Lifecycle.ReceiveWithEvictionLoopResult state composite header dr ds np out pending half batch fuel
        (.ok r) →
      ∃ t0, StoreShrunk state t0 ∧ Model.Triple.receiveDetailed t0 header dr ds np out = .ok r := by
  intro fuel
  induction fuel with
  | zero =>
    intro state pending half batch h
    unfold Model.Lifecycle.ReceiveWithEvictionLoopResult at h
    simp [receiveWithEvictionLoop] at h
  | succ fuel ih =>
    intro state pending half batch h
    unfold Model.Lifecycle.ReceiveWithEvictionLoopResult at h
    cases half
    · simp only [receiveWithEvictionLoop] at h
      have hev := evictOldestClassical_shrunk state batch
      split at h
      · simp at h
      rcases hrd : Model.Triple.receiveDetailed (Model.Triple.evictOldestClassical state batch).1 header dr ds np out with reason | res
      · rw [hrd] at h
        simp only at h
        rcases hfs : Model.Lifecycle.fullStore reason with _ | next
        · rw [hfs] at h; simp at h
        rw [hfs] at h
        simp only at h
        split at h
        · obtain ⟨t0, h0, h1⟩ := ih (Model.Triple.evictOldestClassical state batch).1 reason next _ h
          exact ⟨t0, storeShrunk_trans hev h0, h1⟩
        · obtain ⟨t0, h0, h1⟩ := ih (Model.Triple.evictOldestClassical state batch).1 reason next _ h
          exact ⟨t0, storeShrunk_trans hev h0, h1⟩
      · rw [hrd] at h
        simp only [Except.ok.injEq] at h
        subst h
        exact ⟨(Model.Triple.evictOldestClassical state batch).1, hev, hrd⟩
    · simp only [receiveWithEvictionLoop] at h
      have hev := evictOldestPostQuantum_shrunk state batch
      split at h
      · simp at h
      rcases hrd : Model.Triple.receiveDetailed (Model.Triple.evictOldestPostQuantum state batch).1 header dr ds np out with reason | res
      · rw [hrd] at h
        simp only at h
        rcases hfs : Model.Lifecycle.fullStore reason with _ | next
        · rw [hfs] at h; simp at h
        rw [hfs] at h
        simp only at h
        split at h
        · obtain ⟨t0, h0, h1⟩ := ih (Model.Triple.evictOldestPostQuantum state batch).1 reason next _ h
          exact ⟨t0, storeShrunk_trans hev h0, h1⟩
        · obtain ⟨t0, h0, h1⟩ := ih (Model.Triple.evictOldestPostQuantum state batch).1 reason next _ h
          exact ⟨t0, storeShrunk_trans hev h0, h1⟩
      · rw [hrd] at h
        simp only [Except.ok.injEq] at h
        subst h
        exact ⟨(Model.Triple.evictOldestPostQuantum state batch).1, hev, hrd⟩

/-- **A successful receive with eviction is one Triple receive at a state whose stores are sublists of the
session's**: either the direct receive, or a receive after one or more evictions of the oldest stored keys.  Model
only. -/
theorem receiveWithEviction_ok_shrunk {t : Model.Triple.State} {composite : Model.CompositeHeader.Composite}
    {header : Model.Triple.Header} {dr ds np : Key} {out : Option Model.SparseRatchet.Output}
    {r : Model.Triple.State × Key}
    (h : Model.Lifecycle.receiveWithEviction t composite header dr ds np out = .ok r) :
    ∃ t0, StoreShrunk t t0 ∧ Model.Triple.receiveDetailed t0 header dr ds np out = .ok r := by
  unfold Model.Lifecycle.receiveWithEviction at h
  rcases hd : Model.Triple.receiveDetailed t header dr ds np out with reason | res
  · rw [hd] at h
    simp only at h
    rcases hfs : Model.Lifecycle.fullStore reason with _ | half
    · rw [hfs] at h; simp at h
    rw [hfs] at h
    exact loop_ok_shrunk composite header dr ds np out r _ t reason half _ h
  · rw [hd] at h
    simp only [Except.ok.injEq] at h
    subst h
    exact ⟨t, storeShrunk_refl t, hd⟩


/-! ## The Triple's receive at every header -/

/-- A Triple receive is a classical receive and a sparse receive.  Model only. -/
theorem triple_receive_split {t t' : Model.Triple.State} {hdr : Model.Triple.Header} {dr ds np k : Key}
    {out : Option Model.SparseRatchet.Output}
    (hs : Model.Triple.receiveDetailed t hdr dr ds np out = .ok (t', k)) :
    (∃ k1, Model.Ratchet.receiveDetailed t.classical hdr.dr dr ds np = .ok (t'.classical, k1)) ∧
      ∃ k2, Model.SparseRatchet.receiveDetailed t.postQuantum hdr.epoch out hdr.pqN = .ok (t'.postQuantum, k2) := by
  unfold Model.Triple.receiveDetailed at hs
  rcases hc : Model.Ratchet.receiveDetailed t.classical hdr.dr dr ds np with _ | ⟨c, mkc⟩
  · rw [hc] at hs; simp at hs
  rw [hc] at hs
  simp only at hs
  rcases hp : Model.SparseRatchet.receiveDetailed t.postQuantum hdr.epoch out hdr.pqN with _ | ⟨q, mkq⟩
  · rw [hp] at hs; simp at hs
  rw [hp] at hs
  simp only [Except.ok.injEq, Prod.mk.injEq] at hs
  obtain ⟨rfl, -⟩ := hs
  exact ⟨⟨mkc, rfl⟩, ⟨mkq, rfl⟩⟩

/-- The chains the sparse `advance` leaves: each is a fresh chain at counter zero or a chain of the table before.
Model only. -/
theorem advanced_chains {st st1 : Model.SparseRatchet.State} {out : Option Model.SparseRatchet.Output}
    (ha : advancedOf st out = some st1) :
    ∀ p ∈ st1.chains, ∀ c, InChain p c → c.n = 0 ∨ ∃ p0 ∈ st.chains, InChain p0 c := by
  unfold advancedOf Model.SparseRatchet.maybeAdvanceReceiveDetailed Model.SparseRatchet.maybeAdvanceDetailed at ha
  rcases out with _ | o
  · simp only [Option.some.injEq] at ha; subst ha
    exact fun p hp c hc => Or.inr ⟨p, hp, hc⟩
  · simp only at ha
    rcases hadv : Model.SparseRatchet.advanceDetailed st o with e | st2
    · rw [hadv] at ha; simp at ha
    rw [hadv] at ha; simp only [Option.some.injEq] at ha; subst ha
    obtain ⟨-, -, -, -, -, c0, hc0, hch⟩ := advance_ok_parts hadv
    intro p hp c hc
    rw [hch, List.mem_filter] at hp
    rcases mem_sent_chains hp.1 with ⟨hp', -⟩ | rfl
    · exact Or.inr ⟨p, hp', hc⟩
    · exact Or.inl (hc0 c hc)

/-- **The frame of every successful Triple receive, at every header**: the direction is kept; the sparse epoch is
kept without the agreement's output and is the output's epoch, one more, with one; the sending key is kept or is the
candidate; the clock rises by at most one; every chain counter is at most `maxSkip + 1`, or at most `maxSkip + 1` more
than a counter of the table before.  Model only. -/
theorem triple_receive_any_frame {t0 t' : Model.Triple.State} {hdr : Model.Triple.Header} {dr ds np k : Key}
    {out : Option Model.SparseRatchet.Output} (h : ModelTripleInv t0)
    (hs : Model.Triple.receiveDetailed t0 hdr dr ds np out = .ok (t', k)) :
    t'.postQuantum.direction = t0.postQuantum.direction ∧
      (out = none → t'.postQuantum.epoch = t0.postQuantum.epoch) ∧
      (∀ o, out = some o → t'.postQuantum.epoch = o.keyEpoch ∧ o.keyEpoch = t0.postQuantum.epoch + 1) ∧
      (t'.classical.dhsPub = t0.classical.dhsPub ∨ t'.classical.dhsPub = np) ∧
      t'.classical.events ≤ t0.classical.events + 1 ∧
      ∀ p ∈ t'.postQuantum.chains, ∀ c, InChain p c → c.n ≤ Model.SparseRatchet.maxSkip + 1 ∨
        ∃ p0 ∈ t0.postQuantum.chains, ∃ c0, InChain p0 c0 ∧ c.n ≤ c0.n + Model.SparseRatchet.maxSkip + 1 := by
  obtain ⟨st1, ha, hs1⟩ := triple_receive_advance hs
  obtain ⟨hinv1, hdir1, hnone1, hsome1⟩ := modelTripleInv_advanced h ha
  obtain ⟨⟨k1, hc⟩, ⟨k2, hp⟩⟩ := triple_receive_split hs1
  simp only at hc hp
  obtain ⟨-, hdhs, hev, -⟩ := ratchet_receive_any_frame hc
  obtain ⟨-, hep', hdir', hcnt'⟩ := modelSpqrInv_receive_any hinv1.2.1 hp
  refine ⟨by rw [hdir', hdir1], ?_, ?_, hdhs, hev, ?_⟩
  · intro hn; rw [hep', hnone1 hn]
  · intro o ho; obtain ⟨h1, h2⟩ := hsome1 o ho; exact ⟨by rw [hep', h1], h2⟩
  · intro p hp' c hc'
    obtain ⟨p1, hp1, c1, hc1, hle⟩ := hcnt' p hp' c hc'
    rcases advanced_chains ha p1 hp1 c1 hc1 with h0 | ⟨p0, hp0, hc0⟩
    · left; omega
    · exact Or.inr ⟨p0, hp0, c1, hc0, hle⟩

/-- **Every successful Triple receive, at every header, keeps `ModelTripleInv`**: a stored key taken on either
chain, a skip on either chain (on the classical side on the peer's chain, or on the chain being left and the new
one), with or without the agreement's output, given a canonical header key and a canonical sending key after the
call (on a Diffie-Hellman step that key is the candidate; the code supplies its canonicity).  Model only. -/
theorem triple_receive_any {t0 t' : Model.Triple.State} {hdr : Model.Triple.Header} {dr ds np k : Key}
    {out : Option Model.SparseRatchet.Output} (h : ModelTripleInv t0)
    (hhdr : Model.Messages.canonicalKey hdr.dr.dh = true)
    (hdhs' : Model.Messages.canonicalKey t'.classical.dhsPub = true)
    (hs : Model.Triple.receiveDetailed t0 hdr dr ds np out = .ok (t', k)) : ModelTripleInv t' := by
  obtain ⟨st1, ha, hs1⟩ := triple_receive_advance hs
  obtain ⟨hinv1, hdir1, -, -⟩ := modelTripleInv_advanced h ha
  obtain ⟨⟨k1, hc⟩, ⟨k2, hp⟩⟩ := triple_receive_split hs1
  simp only at hc hp
  obtain ⟨hnpEq, -, -, hch⟩ := ratchet_receive_any_frame hc
  have hnp : Model.Ratchet.trySkipped t0.classical hdr.dr = none → t0.classical.dhrPub ≠ some hdr.dr.dh →
      Model.Messages.canonicalKey np = true := fun h1 h2 => by rw [← hnpEq h1 h2]; exact hdhs'
  obtain ⟨hr0, hq0, hroles0⟩ := hinv1
  obtain ⟨hq', -, hdir', -⟩ := modelSpqrInv_receive_any hq0 hp
  refine ⟨modelRatchetInv_receive_any hr0 hhdr hnp hc, hq', ?_⟩
  unfold ModelRolesAgree at hroles0 ⊢
  simp only at hroles0
  rw [hdir']
  rcases hch with ⟨hcs, hcr⟩ | hck
  · rw [hcs, hcr]; exact hroles0
  · rcases hk : t'.classical.ckr with _ | x
    · rw [hk] at hck; simp at hck
    · rcases t'.classical.cks <;> simp

/-- **Shrinking both stores keeps `ModelTripleInv`.**  Model only. -/
theorem modelTripleInv_shrunk {t t0 : Model.Triple.State} (h : ModelTripleInv t) (hs : StoreShrunk t t0) :
    ModelTripleInv t0 := by
  obtain ⟨he, hc, hp⟩ := hs
  obtain ⟨hr, hq, hroles⟩ := h
  rw [he]
  refine ⟨modelRatchetInv_shrink hr hc, modelSpqrInv_shrink hq hp, ?_⟩
  unfold ModelRolesAgree at hroles ⊢
  exact hroles

/-! ## The session's receive step at every frame -/

/-- **A receive step at every frame**: the session as it was, or the agreement's next state for some message, with
the Triple the model's receive with eviction (`Model.Lifecycle.receiveWithEviction`, the retry that evicts the oldest
stored keys from a full store) of a header whose key is canonical, with the oracle's public key of the draw `cand` as
the candidate, and the ratchet key replaced by `cand` exactly when the sending key changed.  No scope: a stored key, a
skip on either chain and an eviction are all included.  What the model's `decryptRatchet` does on every frame
(`decryptRatchet_receiveStepAny`). -/
def ReceiveStepAny (oracle : Model.Lifecycle.Oracle) (m m' : Model.Lifecycle.Session) : Prop :=
  (m'.triple = m.triple ∧ m'.ratchetPrivate = m.ratchetPrivate ∧ m'.braid = m.braid) ∨
    ∃ (msgB : Model.Braid.Msg) (c : Model.CompositeHeader.Composite) (hdr : Model.Triple.Header)
      (dr ds cand mk : Key),
      m'.braid = (Model.Braid.receive oracle.braidKem m.braid msgB).2.2 ∧
      Model.Messages.canonicalKey hdr.dr.dh = true ∧
      Model.Lifecycle.receiveWithEviction m.triple c hdr dr ds (oracle.dhPublic cand)
        (Model.Lifecycle.sparseOutputOf (Model.Braid.receive oracle.braidKem m.braid msgB).2.1) =
          .ok (m'.triple, mk) ∧
      m'.ratchetPrivate = if m'.triple.classical.dhsPub == m.triple.classical.dhsPub then m.ratchetPrivate else cand

/-- **The model's `decryptRatchet` of every frame is a `ReceiveStepAny`**, at every agreement state, with no
hypothesis.  Model only. -/
theorem decryptRatchet_receiveStepAny (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle)
    (m : Model.Lifecycle.Session) (msg : Model.Lifecycle.Bytes) :
    ReceiveStepAny oracle m (Model.Lifecycle.decryptRatchet view oracle m msg).session := by
  have stay : ReceiveStepAny oracle m m := Or.inl ⟨rfl, rfl, rfl⟩
  unfold Model.Lifecycle.decryptRatchet
  by_cases hf : Model.Lifecycle.agreementFailed m = true
  · simp only [hf, if_true]; exact stay
  simp only [hf, Bool.false_eq_true, if_false]
  rcases hd : Model.CompositeHeader.decodeDetailed msg with reason | ⟨c, ct⟩
  · exact stay
  have hcan : Model.Messages.canonicalKey c.dh = true :=
    Tacenta.UnitLifecycleReceivePreserve.decode_dh_canonical
      ((Model.CompositeHeader.decodeDetailed_ok_iff _ _).mp hd)
  simp only
  rcases oracle.dhAgree m.ratchetPrivate c.dh with _ | dr
  · exact stay
  simp only
  rcases Model.Lifecycle.random32 oracle with _ | ⟨cand, o'⟩
  · exact stay
  simp only
  rcases oracle.dhAgree cand c.dh with _ | ds
  · exact stay
  simp only
  rcases hr : Model.Lifecycle.receiveWithEviction m.triple c (Model.Lifecycle.tripleHeaderOf c) dr ds
      (oracle.dhPublic cand) (Model.Lifecycle.sparseOutputOf
        (Model.Braid.receive oracle.braidKem m.braid (Model.Lifecycle.braidMessageOf view m.braid c)).2.1)
      with reason | ⟨t', mk⟩
  · exact stay
  simp only
  split
  · exact stay
  · exact Or.inr ⟨_, c, Model.Lifecycle.tripleHeaderOf c, dr, ds, cand, mk, rfl, hcan, hr, rfl⟩

/-- **The model's public `decrypt` of a message the dispatch passes on is a `ReceiveStepAny`**, with no hypothesis
beyond the dispatch.  Model only. -/
theorem decrypt_receiveStepAny (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle)
    (m : Model.Lifecycle.Session) (msg inner : Model.Lifecycle.Bytes)
    (hdisp : Model.Lifecycle.dispatchDecrypt oracle m msg = .ok inner) :
    ReceiveStepAny oracle m (Model.Lifecycle.decrypt view oracle m msg).session := by
  have h := decryptRatchet_receiveStepAny view oracle m inner
  unfold Model.Lifecycle.decrypt
  rw [hdisp]
  simp only
  split
  · exact h
  · exact h

/-- What a non-trivial step's Triple is: one Triple receive at a state whose stores are sublists of the session's.
Model only. -/
theorem receiveStepAny_parts {oracle : Model.Lifecycle.Oracle} {m m' : Model.Lifecycle.Session}
    {msgB : Model.Braid.Msg} {c : Model.CompositeHeader.Composite} {hdr : Model.Triple.Header} {dr ds cand mk : Key}
    (hr : Model.Lifecycle.receiveWithEviction m.triple c hdr dr ds (oracle.dhPublic cand)
        (Model.Lifecycle.sparseOutputOf (Model.Braid.receive oracle.braidKem m.braid msgB).2.1) =
          .ok (m'.triple, mk)) :
    ∃ t0, StoreShrunk m.triple t0 ∧ Model.Triple.receiveDetailed t0 hdr dr ds (oracle.dhPublic cand)
      (Model.Lifecycle.sparseOutputOf (Model.Braid.receive oracle.braidKem m.braid msgB).2.1) = .ok (m'.triple, mk) :=
  receiveWithEviction_ok_shrunk hr

/-- **A receive step at every frame keeps `ModelTripleInv`**, given a canonical sending key after it.  Model only. -/
theorem modelTripleInv_stepAny (oracle : Model.Lifecycle.Oracle) {m m' : Model.Lifecycle.Session}
    (hstep : ReceiveStepAny oracle m m') (h : ModelTripleInv m.triple)
    (hdhs' : Model.Messages.canonicalKey m'.triple.classical.dhsPub = true) : ModelTripleInv m'.triple := by
  rcases hstep with ⟨htr, -⟩ | ⟨msgB, c, hdr, dr, ds, cand, mk, -, hcan, hr, -⟩
  · rw [htr]; exact h
  obtain ⟨t0, hshr, hs⟩ := receiveStepAny_parts hr
  exact triple_receive_any (modelTripleInv_shrunk h hshr) hcan hdhs' hs

/-- **A receive step at every frame spends at most one unit of the budget**: the clock rises by at most one, the
sparse epoch and the agreement's epoch by at most one, and every chain counter is at most `maxSkip + 1`, or at most
`maxSkip + 1` more than a counter before, which the budget's `1001` per operation covers.  Model only. -/
theorem modelCounterRoom_stepAny (oracle : Model.Lifecycle.Oracle) {m m' : Model.Lifecycle.Session} (k : Nat)
    (hstep : ReceiveStepAny oracle m m') (h : ModelTripleInv m.triple)
    (hroom : ModelCounterRoom m (k + 1)) : ModelCounterRoom m' k := by
  obtain ⟨h1, h2, h3, h4⟩ := hroom
  rcases hstep with ⟨htr, -, hb⟩ | ⟨msgB, c, hdr, dr, ds, cand, mk, hb, -, hr, -⟩
  · refine ⟨?_, ?_, ?_, ?_⟩
    · rw [htr]; omega
    · rw [htr]; omega
    · rw [htr]; intro p hp ch hch; have := h3 p hp ch hch; omega
    · rw [hb]; omega
  have hk : k < 2 ^ 32 := by
    have : Std.U32.max = 2 ^ 32 - 1 := by simp [Std.U32.max_eq]
    omega
  have hU : Std.U64.max = 2 ^ 64 - 1 := by simp [Std.U64.max_eq]
  obtain ⟨t0, hshr, hs⟩ := receiveStepAny_parts hr
  obtain ⟨-, hnone, hsome, -, hev, hcnt⟩ := triple_receive_any_frame (modelTripleInv_shrunk h hshr) hs
  obtain ⟨he, -, -⟩ := hshr
  have hcl : t0.classical.events = m.triple.classical.events := by rw [he]
  have hep : t0.postQuantum.epoch = m.triple.postQuantum.epoch := by rw [he]
  have hchs : t0.postQuantum.chains = m.triple.postQuantum.chains := by rw [he]
  have hms : Model.SparseRatchet.maxSkip = 1000 := rfl
  refine ⟨by omega, ?_, ?_, ?_⟩
  · rcases hout : Model.Lifecycle.sparseOutputOf (Model.Braid.receive oracle.braidKem m.braid msgB).2.1 with _ | o
    · rw [hnone hout]; omega
    · obtain ⟨h5, h6⟩ := hsome o hout; omega
  · intro p hp ch hch
    rcases hcnt p hp ch hch with h0 | ⟨p0, hp0, c0, hc0, hle⟩
    · omega
    · rw [hchs] at hp0
      have := h3 p0 hp0 c0 hc0
      omega
  · rw [hb]
    have := receive_epoch_le oracle.braidKem m.braid msgB
    omega

/-- **What a receive step at every frame leaves of the Triple's direction and sending key, and of clause (b) and the
role**: the direction is kept; a changed sending key is the oracle's public key of the new ratchet key; clause (b)
holds after the step at the new sparse epoch when it held before; and the agreement after is failed or reads the same
role.  Model only. -/
theorem step_frame_stepAny (oracle : Model.Lifecycle.Oracle) {m m' : Model.Lifecycle.Session}
    (hstep : ReceiveStepAny oracle m m') (h : ModelTripleInv m.triple)
    (hcb : ModelClauseB m.triple.postQuantum.epoch m.braid) :
    m'.triple.postQuantum.direction = m.triple.postQuantum.direction ∧
      (m'.triple.classical.dhsPub ≠ m.triple.classical.dhsPub →
        m'.triple.classical.dhsPub = oracle.dhPublic m'.ratchetPrivate) ∧
      ModelClauseB m'.triple.postQuantum.epoch m'.braid ∧
      (m'.braid = .failed ∨ modelIsInit m'.braid = modelIsInit m.braid) := by
  rcases hstep with ⟨htr, hrp, hb⟩ | ⟨msgB, c, hdr, dr, ds, cand, mk, hb, -, hr, hrp⟩
  · rw [htr, hb]; exact ⟨rfl, fun h => absurd rfl h, hcb, Or.inr rfl⟩
  obtain ⟨t0, hshr, hs⟩ := receiveStepAny_parts hr
  obtain ⟨hdir, hnone, hsome, hdhs, -, -⟩ := triple_receive_any_frame (modelTripleInv_shrunk h hshr) hs
  obtain ⟨he, -, -⟩ := hshr
  have hdir0 : t0.postQuantum.direction = m.triple.postQuantum.direction := by rw [he]
  have hep0 : t0.postQuantum.epoch = m.triple.postQuantum.epoch := by rw [he]
  have hdhs0 : t0.classical.dhsPub = m.triple.classical.dhsPub := by rw [he]
  obtain ⟨hrole, hcbn, hcbs⟩ := receive_clauses oracle.braidKem m.braid msgB _ hcb
  refine ⟨by rw [hdir, hdir0], fun hne => ?_, ?_, by rw [hb]; exact hrole⟩
  · have hrp' : m'.ratchetPrivate = cand := by rw [hrp]; simp [hne]
    rw [hrp']
    rcases hdhs with h0 | h0
    · exact absurd (h0.trans hdhs0) hne
    · exact h0
  · rw [hb]
    rcases hout : (Model.Braid.receive oracle.braidKem m.braid msgB).2.1 with _ | o
    · have : Model.Lifecycle.sparseOutputOf (Model.Braid.receive oracle.braidKem m.braid msgB).2.1 = none := by
        rw [hout]; rfl
      rw [hnone this, hep0]; exact hcbn hout
    · have : Model.Lifecycle.sparseOutputOf (Model.Braid.receive oracle.braidKem m.braid msgB).2.1 =
          some { keyEpoch := o.keyEpoch, key := o.key } := by
        rw [hout]; rfl
      rw [(hsome _ this).1]
      exact (hcbs o hout).2

/-! ## The key a receive uses is not kept -/

/-- A classical skip stores only keys of the peer's chain, numbered from its counter up to the bound; every other
entry was there before.  Model only. -/
theorem skip_stored {st st' : Model.State.State} {upto : Nat}
    (hs : Model.State.skipMessageKeys st upto = some st') :
    ∀ e ∈ st'.skipped, e ∈ st.skipped ∨ (st.dhrPub = some e.1 ∧ st.nr ≤ e.2.1 ∧ e.2.1 < upto) := by
  unfold Model.State.skipMessageKeys at hs
  split at hs
  · rename_i ck dhr hck hdhr
    split at hs
    · simp only [Option.some.injEq] at hs; subst hs; exact fun e he => Or.inl he
    rename_i hle
    split at hs
    · simp at hs
    split at hs
    · simp at hs
    simp only [Option.some.injEq] at hs
    subst hs
    intro e he
    simp only [List.mem_append, List.mem_map] at he
    rcases he with he | ⟨x, hx, rfl⟩
    · exact Or.inl (List.mem_filter.mp he).1
    · right
      have h1 := deriveChain_num_ge ck st.nr (upto - st.nr) x hx
      have h2 := deriveChain_num_lt ck st.nr (upto - st.nr) x hx
      exact ⟨hdhr, h1, by simp only; omega⟩
  · simp only [Option.some.injEq] at hs; subst hs; exact fun e he => Or.inl he

/-- **A successful classical receive keeps no stored key for the header's ratchet key and number**: a stored key it
used is removed, and a skip stores only numbers below the header's on the header's chain, or keys of another chain.
Model only. -/
theorem ratchet_receive_consumes {st st' : Model.State.State} {hdr : Model.State.Header} {dr ds np mk : Key}
    (hr : Model.Ratchet.receiveDetailed st hdr dr ds np = .ok (st', mk)) :
    ∀ e ∈ st'.skipped, ¬ (e.1 = hdr.dh ∧ e.2.1 = hdr.n) := by
  rcases ratchet_receive_cases hr with ⟨next, ht, rfl⟩ | ⟨ht, st1, st2, hst1, hs2, htail⟩
  · unfold Model.Ratchet.trySkipped at ht
    split at ht
    · simp only [Option.some.injEq, Prod.mk.injEq] at ht
      obtain ⟨rfl, -⟩ := ht
      intro e he ⟨h1, h2⟩
      simp only [Model.State.ageStore, List.mem_filter] at he
      obtain ⟨⟨-, hkeep⟩, -⟩ := he
      obtain ⟨a, b, c, d⟩ := e
      simp only at h1 h2
      simp [h1, h2] at hkeep
    · simp at ht
  · have hnone : ∀ e ∈ st.skipped, ¬ (e.1 = hdr.dh ∧ e.2.1 = hdr.n) := by
      unfold Model.Ratchet.trySkipped at ht
      split at ht
      · simp at ht
      · rename_i hf
        intro e he ⟨h1, h2⟩
        have := List.find?_eq_none.mp hf e he
        obtain ⟨a, b, c, d⟩ := e
        simp only at h1 h2
        simp [h1, h2] at this
    obtain ⟨ck, -, -, rfl⟩ := Tacenta.UnitLifecycleReceivePreserve.classicalTail_ok htail
    intro e he ⟨h1, h2⟩
    simp only [Model.State.ageStore, List.mem_filter] at he
    rcases skip_stored hs2 e he.1 with he1 | ⟨-, -, hhi⟩
    · rcases hst1 with ⟨-, rfl⟩ | ⟨hd, sk, hsk, rfl⟩
      · exact hnone e he1 ⟨h1, h2⟩
      · rcases skip_stored hsk e he1 with he0 | ⟨hd0, -, -⟩
        · exact hnone e he0 ⟨h1, h2⟩
        · exact hd (by rw [hd0, h1])
    · omega

/-- A sparse skip stores only keys of the skipped epoch, numbered above zero up to the bound; every other entry was
there before.  Model only. -/
theorem spqr_skip_stored {st st' : Model.SparseRatchet.State} {ep upto : Nat}
    (hs : Model.SparseRatchet.skipMessageKeys st ep upto = some st') :
    ∀ x ∈ st'.skipped, x ∈ st.skipped ∨ (x.1 = ep ∧ 0 < x.2.1 ∧ x.2.1 ≤ upto) := by
  unfold Model.SparseRatchet.skipMessageKeys at hs
  rcases hf : Model.SparseRatchet.findChains st ep with _ | cs
  · rw [hf] at hs; simp at hs
  rw [hf] at hs
  simp only at hs
  rcases hr : cs.receive with _ | ch
  · rw [hr] at hs; simp at hs
  rw [hr] at hs
  simp only at hs
  split at hs
  · simp only [Option.some.injEq] at hs; subst hs; exact fun x hx => Or.inl hx
  rename_i hle
  split at hs
  · simp at hs
  split at hs
  · simp at hs
  simp only [Option.some.injEq] at hs
  subst hs
  intro x hx
  simp only [Model.SparseRatchet.setChains, List.mem_append, List.mem_map] at hx
  rcases hx with hx | ⟨y, hy, rfl⟩
  · exact Or.inl (List.mem_filter.mp hx).1
  · right
    have h1 := deriveInto_num_gt ch.ck ch.n (upto - ch.n) y hy
    have h2 := deriveInto_num_le ch.ck ch.n (upto - ch.n) y hy
    exact ⟨rfl, by simp only; omega, by simp only; omega⟩

/-- **A successful sparse receive without an agreement output keeps no stored key for the header's epoch and
number.**  Model only. -/
theorem spqr_receive_consumes {st st' : Model.SparseRatchet.State} {ep n : Nat} {mk : Key}
    (hr : Model.SparseRatchet.receiveDetailed st ep none n = .ok (st', mk)) :
    ∀ x ∈ st'.skipped, ¬ (x.1 = ep ∧ x.2.1 = n) := by
  rcases spqr_receive_cases hr with ht | ⟨ht, st2, hs, htail⟩
  · unfold Model.SparseRatchet.trySkipped at ht
    split at ht
    · simp at ht
    · simp only [Option.some.injEq, Prod.mk.injEq] at ht
      obtain ⟨rfl, -⟩ := ht
      intro x hx ⟨h1, h2⟩
      have hkeep := (List.mem_filter.mp hx).2
      simp [h1, h2] at hkeep
  · have hnone : ∀ x ∈ st.skipped, ¬ (x.1 = ep ∧ x.2.1 = n) := by
      unfold Model.SparseRatchet.trySkipped at ht
      split at ht
      · rename_i hf
        intro x hx ⟨h1, h2⟩
        have := List.find?_eq_none.mp hf x hx
        simp [h1, h2] at this
      · simp at ht
    obtain ⟨cs, ch, -, -, -, -, rfl⟩ := sparseTail_ok htail
    intro x hx ⟨h1, h2⟩
    rcases spqr_skip_stored hs x hx with hx0 | ⟨-, hlo, hhi⟩
    · exact hnone x hx0 ⟨h1, h2⟩
    · omega

/-- **A successful Triple receive, at every header, keeps no stored key for the header's classical ratchet key and
number, nor for its sparse epoch and number**, with or without the agreement's output.  Model only. -/
theorem triple_receive_consumes {t0 t' : Model.Triple.State} {hdr : Model.Triple.Header} {dr ds np k : Key}
    {out : Option Model.SparseRatchet.Output}
    (hs : Model.Triple.receiveDetailed t0 hdr dr ds np out = .ok (t', k)) :
    (∀ e ∈ t'.classical.skipped, ¬ (e.1 = hdr.dr.dh ∧ e.2.1 = hdr.dr.n)) ∧
      ∀ x ∈ t'.postQuantum.skipped, ¬ (x.1 = hdr.epoch ∧ x.2.1 = hdr.pqN) := by
  obtain ⟨st1, -, hs1⟩ := triple_receive_advance hs
  obtain ⟨⟨k1, hc⟩, ⟨k2, hp⟩⟩ := triple_receive_split hs1
  exact ⟨ratchet_receive_consumes hc, spqr_receive_consumes hp⟩

/-- **The model's `decryptRatchet`, on every frame it accepts, keeps no stored key for the frame's classical ratchet
key and number, nor for its sparse epoch and number**: whether it used a stored key (removed), skipped on either
chain (the frame's own number is never stored), or evicted first.  Model only. -/
theorem decryptRatchet_consumes (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle)
    (m : Model.Lifecycle.Session) (msg : Model.Lifecycle.Bytes) (c : Model.CompositeHeader.Composite)
    (ct : Model.Lifecycle.Bytes) (hd : Model.CompositeHeader.decodeDetailed msg = .ok (c, ct))
    (pt : Model.Lifecycle.Bytes) (hok : (Model.Lifecycle.decryptRatchet view oracle m msg).result = .ok pt) :
    (∀ e ∈ (Model.Lifecycle.decryptRatchet view oracle m msg).session.triple.classical.skipped,
        ¬ (e.1 = c.dh ∧ e.2.1 = c.n.toNat)) ∧
      ∀ x ∈ (Model.Lifecycle.decryptRatchet view oracle m msg).session.triple.postQuantum.skipped,
        ¬ (x.1 = c.pqEpoch.toNat ∧ x.2.1 = c.pqN.toNat) := by
  revert hok
  unfold Model.Lifecycle.decryptRatchet
  by_cases hf : Model.Lifecycle.agreementFailed m = true
  · simp [hf]
  simp only [hf, Bool.false_eq_true, if_false, hd]
  rcases oracle.dhAgree m.ratchetPrivate c.dh with _ | dr
  · simp
  simp only
  rcases Model.Lifecycle.random32 oracle with _ | ⟨cand, o'⟩
  · simp
  simp only
  rcases oracle.dhAgree cand c.dh with _ | ds
  · simp
  simp only
  rcases hr : Model.Lifecycle.receiveWithEviction m.triple c (Model.Lifecycle.tripleHeaderOf c) dr ds
      (oracle.dhPublic cand) (Model.Lifecycle.sparseOutputOf
        (Model.Braid.receive oracle.braidKem m.braid (Model.Lifecycle.braidMessageOf view m.braid c)).2.1)
      with reason | ⟨t', mk⟩
  · simp
  simp only
  split
  · simp
  · intro _
    obtain ⟨t0, -, hs⟩ := receiveWithEviction_ok_shrunk hr
    exact triple_receive_consumes hs

/-! ## `decrypt_ratchet` and `decrypt` keep the invariant at every frame -/

/-- **`Session::decrypt_ratchet` keeps `Session::invariant` and spends one unit of the counter budget, at every frame
and every agreement state**: as `UnitLifecycleDecryptPreserve.decrypt_ratchet_keeps_invariant`, with the model step a
`ReceiveStepAny` (a stored key used, a skip on either chain, an eviction from a full store, or none of these) instead
of a step in the in-order scope.  The relation after the call and the step are hypotheses; nothing here calls a
refinement theorem.  Under `ReceiveInvariantLaws`, the oracle's `dhPublic` clause and the view's codec relation. -/
theorem decrypt_ratchet_keeps_invariant_any (laws : ReceiveInvariantLaws)
    {R : Type} (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R)
    (dh : DhView) (codec : DhCodecOf dh) (K : Model.Braid.Kem) (oracle : Model.Lifecycle.Oracle)
    (hdhPublic : ∀ secret, ∃ publicKey, tacenta_boundary.dh.PrivateKey.public_key secret = ok publicKey ∧
      dh.publicKey publicKey = oracle.dhPublic (dh.privateKey secret))
    (s : lifecycle.Session) (m m' : Model.Lifecycle.Session) (k : Nat)
    (hinv : lifecycle.Session.invariant s = ok true) (hroom : CounterRoom s (k + 1))
    (hrel : SessionRefines dh K s m)
    (msg : Slice U8) (rng : R) (pt : alloc.vec.Vec U8) (s' : lifecycle.Session) (rng' : R)
    (hcall : lifecycle.Session.decrypt_ratchet rc crc s msg rng = ok (core.result.Result.Ok pt, s', rng'))
    (hrel' : SessionRefines dh K s' m') (hstep : ReceiveStepAny oracle m m') :
    lifecycle.Session.invariant s' = ok true ∧ CounterRoom s' k := by
  obtain ⟨L⟩ := braidLens_of_totals laws.headerLen laws.ekVectorLen laws.ct1Len laws.ct2Len
  have hoeq := laws.optionEq
  have hpub := laws.dhPublicValid
  obtain ⟨hstr, htri, hbr⟩ := (session_invariant_iff s).mp hinv
  have hsnf := decrypt_ratchet_ok_live rc crc s msg rng pt s' rng' hcall
  obtain ⟨msgB, x, y, bc, a, ck, pkb, new, hrecv, -, -, hpkb, hnew, hcases⟩ :=
    Tacenta.UnitLifecycleResponderSuccessor.decrypt_ratchet_ok_parts rc crc s msg rng pt s' rng' hcall
  have hbc : s'.braid = bc := by rcases hcases with ⟨-, h⟩ | ⟨-, h⟩ <;> rw [h]
  -- the agreement half, at every state
  have hbinv : tacenta_braid.Braid.invariant bc = ok true :=
    braid_receive_keeps_invariant L laws.kemClone laws.divCeil laws.truncate laws.keyPairEkVector
      laws.encapsulate2Len s.braid msgB x y bc hbr hrecv
  have hmodel := (triple_invariant_iff_model hrel.triple).mp htri
  -- the model's step: direction, the sending key, clause (b) and the role
  have hcb : ModelClauseB m.triple.postQuantum.epoch m.braid :=
    modelClauseB_of_structural hoeq hrel hstr hsnf (by have := hroom.sparseEpoch; omega)
  obtain ⟨hdirM, hdhsM, hcb', hrole⟩ := step_frame_stepAny oracle hstep hmodel hcb
  have hdir : s'.triple.post_quantum.direction = s.triple.post_quantum.direction := by
    have h1 := congrArg Model.SparseRatchet.State.direction hrel'.triple.2
    have h0 := congrArg Model.SparseRatchet.State.direction hrel.triple.2
    simp only [Tacenta.SessionUnitTripleT3.spqrAbs] at h1 h0
    have hd : Tacenta.SessionUnitSpqrT3.directionOf s'.triple.post_quantum.direction =
        Tacenta.SessionUnitSpqrT3.directionOf s.triple.post_quantum.direction := by
      rw [h1, h0, hdirM]
    revert hd
    cases s'.triple.post_quantum.direction <;> cases s.triple.post_quantum.direction <;>
      simp [Tacenta.SessionUnitSpqrT3.directionOf]
  have hk0 := keyOf_dhs hrel.triple
  have hk1 := keyOf_dhs hrel'.triple
  -- clause (a) at the session the call returns
  have ha : ∃ pk, tacenta_boundary.dh.PrivateKey.public_key s'.ratchet_private = ok pk ∧
      tacenta_boundary.dh.PublicKeyBytes.as_bytes pk = ok s'.triple.classical.dhs_pub := by
    rcases hcases with ⟨hne, hs'⟩ | ⟨hsame, hs'⟩
    · have hrp : s'.ratchet_private = ck := by rw [hs']
      have hneM : m'.triple.classical.dhsPub ≠ m.triple.classical.dhsPub := by
        rw [← hk0, ← hk1]
        exact fun h => hne (keyOf_injective h)
      have hM := hdhsM hneM
      obtain ⟨pk, hpk, hpkv⟩ := hdhPublic ck
      rw [hpkb] at hpk
      cases hpk
      obtain ⟨b, hb, hbv⟩ := codec.asBytes pkb
      rw [hnew] at hb
      cases hb
      have hd : s'.triple.classical.dhs_pub = new := by
        apply keyOf_injective
        show Tacenta.SessionUnitT3.keyOf _ = arrayOf new
        rw [hk1, hM, ← hrel'.ratchetPrivate, hrp, ← hpkv, hbv]
      rw [hrp, hd]
      exact ⟨pkb, hpkb, hnew⟩
    · have hrp : s'.ratchet_private = s.ratchet_private := by rw [hs']
      rw [hrp, hsame]
      exact clause_a_of_structural s hstr
  obtain ⟨pk', hpk', hb'⟩ := ha
  have hcan' : Tacenta.SessionUnitT1.canonicalX25519 s'.triple.classical.dhs_pub = true :=
    dhPublicValid_canonical hpub hpk' hb'
  have hcanM : Model.Messages.canonicalKey m'.triple.classical.dhsPub = true := by
    rw [← hk1, canonicalKey_keyOf]; exact hcan'
  -- the Triple half, through the model: every case of the step, the sending key's canonicity from the code
  have hmodel' : ModelTripleInv m'.triple := modelTripleInv_stepAny oracle hstep hmodel hcanM
  have htri' : tacenta_triple.State.invariant s'.triple = ok true :=
    (triple_invariant_iff_model hrel'.triple).mpr hmodel'
  -- the session's own clauses
  have hs'eq : s' = { s with triple := s'.triple, braid := bc, ratchet_private := s'.ratchet_private } := by
    rcases hcases with ⟨-, h⟩ | ⟨-, h⟩ <;> rw [h]
  obtain ⟨-, -, hfm, him⟩ := braid_reads_refines hrel'.braid
  obtain ⟨-, -, -, him0⟩ := braid_reads_refines hrel.braid
  rw [← braid_eta, hbc] at hfm him
  rw [← braid_eta] at him0
  have hcase : tacenta_braid.Braid.failed bc = ok true ∨
      (tacenta_braid.Braid.failed bc = ok false ∧
        tacenta_braid.Braid.is_initiator bc = tacenta_braid.Braid.is_initiator s.braid ∧
        CodeClauseB s'.triple bc) := by
    by_cases hmf : m'.braid = .failed
    · left; rw [hfm, hmf]; rfl
    · right
      have hnf : Model.Lifecycle.braidFailed m'.braid = false := by
        revert hmf; cases m'.braid <;> simp [Model.Lifecycle.braidFailed]
      refine ⟨by rw [hfm, hnf], ?_, ?_⟩
      · rw [him, him0]
        rcases hrole with h | h
        · exact absurd h hmf
        · rw [h]
      · have := codeClauseB_of_model hrel'.triple hrel'.braid hcb' hmf
        rwa [← braid_eta, hbc] at this
  have hstr' : lifecycle.Session.structural_invariant s' = ok true := by
    rw [hs'eq]
    exact structural_after hoeq s s'.triple bc s'.ratchet_private hstr pk' hpk' hb' hdir hsnf hcase
  refine ⟨(session_invariant_iff s').mpr ⟨hstr', htri', hbc ▸ hbinv⟩, ?_⟩
  exact (counterRoom_iff_model hrel' k).mpr
    (modelCounterRoom_stepAny oracle k hstep hmodel ((counterRoom_iff_model hrel (k + 1)).mp hroom))

/-- **`Session::decrypt` keeps `Session::invariant` and spends one unit of the counter budget, at every frame and
every agreement state**: as `decrypt_ratchet_keeps_invariant_any`, for the public call, whose success is a successful
inner `decrypt_ratchet` with the pending initial message cleared (`decrypt_ok_inner`). -/
theorem decrypt_keeps_invariant_any (laws : ReceiveInvariantLaws)
    {R : Type} (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R)
    (dh : DhView) (codec : DhCodecOf dh) (K : Model.Braid.Kem) (oracle : Model.Lifecycle.Oracle)
    (hdhPublic : ∀ secret, ∃ publicKey, tacenta_boundary.dh.PrivateKey.public_key secret = ok publicKey ∧
      dh.publicKey publicKey = oracle.dhPublic (dh.privateKey secret))
    (s : lifecycle.Session) (m m' : Model.Lifecycle.Session) (k : Nat)
    (hinv : lifecycle.Session.invariant s = ok true) (hroom : CounterRoom s (k + 1))
    (hrel : SessionRefines dh K s m)
    (msg : Slice U8) (rng : R) (pt : alloc.vec.Vec U8) (s' : lifecycle.Session) (rng' : R)
    (hcall : lifecycle.Session.decrypt rc crc s msg rng = ok (core.result.Result.Ok pt, s', rng'))
    (hrel' : SessionRefines dh K s' m') (hstep : ReceiveStepAny oracle m m') :
    lifecycle.Session.invariant s' = ok true ∧ CounterRoom s' k := by
  obtain ⟨inner, s1, hin, rfl⟩ := decrypt_ok_inner rc crc s msg rng pt s' rng' hcall
  have hw := Tacenta.UnitLifecycleAtomicity.decrypt_ratchet_ok_writes rc crc s inner rng pt s1 rng' hin
  have hpend : s1.pending_initial = s.pending_initial := by rw [hw]
  have hrel1 : SessionRefines dh K s1 { m' with pendingInitial := m.pendingInitial } :=
    ⟨hrel'.triple, hrel'.braid, hrel'.ratchetPrivate, hrel'.identityAd, hrel'.ourIdentityPublic,
      hrel'.peerIdentityPublic, by rw [hpend]; exact hrel.pendingInitial, hrel'.establishedEphemeral⟩
  obtain ⟨hinv1, hroom1⟩ := decrypt_ratchet_keeps_invariant_any laws rc crc dh codec K oracle hdhPublic
    s m _ k hinv hroom hrel inner rng pt s1 rng' hin hrel1 hstep
  obtain ⟨hstr1, htri1, hbr1⟩ := (session_invariant_iff s1).mp hinv1
  obtain ⟨r1, r2, r3, r4⟩ := hroom1
  exact ⟨(session_invariant_iff _).mpr ⟨structural_clear_pending s1 hstr1, htri1, hbr1⟩, ⟨r1, r2, r3, r4⟩⟩

/-! ## Composed with the decrypt refinement: every frame -/

/-- **`Session::decrypt_ratchet` refines the model's step and keeps `Session::invariant` and the counter budget, at
every frame**: as `UnitLifecycleDecryptCompose.decrypt_ratchet_refines_keeps_invariant` with the in-order scope
(`FrameInOrder`) dropped.  For every session `s` that passes `Session::invariant`, has room for `k + 1` operations and
refines a model session `m`, and every frame, under the hypotheses of `decrypt_ratchet_refines_of_invariant` and
`ReceiveInvariantLaws`, `decrypt_ratchet` returns, its result, session and draws refine the model's `decryptRatchet`
(which uses a stored key, skips on either chain, or evicts from a full store as the frame requires), and the session
it returns passes `Session::invariant` and has room for `k`, whether the call succeeds or refuses.  The relation after
the call and the model step are derived: the relation from the refinement, the step from the model's own
`decryptRatchet` (`decryptRatchet_receiveStepAny`, no hypothesis). -/
theorem decrypt_ratchet_refines_keeps_invariant_any (laws : ReceiveInvariantLaws) {R : Type}
    (rngCore : rand_core_1.RngCore R) (cryptoRng : rand_core_1.CryptoRng R)
    (trace : R → List Model.Lifecycle.Key) (dh : DhView)
    (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle)
    (oracleOf : DecryptOracleOf rngCore cryptoRng dh trace oracle)
    (codec : DhCodecOf dh)
    (contracts : Tacenta.UnitLifecycleT1.DecryptRatchetContracts rngCore)
    [Tacenta.SessionUnitT1.DerivedKeysModel]
    (agreements : DecryptRatchetAgreements oracle.braidKem)
    (s : lifecycle.Session) (m : Model.Lifecycle.Session) (message : Slice Std.U8) (rng : R) (k : Nat)
    (hinv : lifecycle.Session.invariant s = ok true)
    (hrel : SessionRefines dh oracle.braidKem s m)
    (hroom : CounterRoom s (k + 1))
    (htrace : trace rng = oracle.draws)
    (inputs : DecryptRatchetRunInputs view oracle trace s m message rng) :
    ∃ output,
      lifecycle.Session.decrypt_ratchet rngCore cryptoRng s message rng = ok output ∧
      StepRefines trace dh oracle.braidKem output
        (Model.Lifecycle.decryptRatchet view oracle m (sliceOf message)) ∧
      lifecycle.Session.invariant output.2.1 = ok true ∧ CounterRoom output.2.1 k := by
  have hc : CounterHeadroom s := (counterRoom_zero s).mp (counterRoom_mono s (Nat.zero_le _) hroom)
  obtain ⟨⟨res, s', rng'⟩, hcall, hstep⟩ := decrypt_ratchet_refines_of_invariant rngCore cryptoRng trace dh
    view oracle oracleOf codec contracts agreements s m message rng hinv hrel hc htrace inputs
  refine ⟨_, hcall, hstep, ?_⟩
  rcases res with pt | e
  · exact decrypt_ratchet_keeps_invariant_any laws rngCore cryptoRng dh codec oracle.braidKem oracle
      oracleOf.dhPublic s m _ k hinv hroom hrel message rng pt s' rng' hcall hstep.session
      (decryptRatchet_receiveStepAny view oracle m (sliceOf message))
  · obtain ⟨h1, h2⟩ := decrypt_ratchet_err_keeps_invariant rngCore cryptoRng s message rng e s' rng' hinv hcall
    exact ⟨h1, h2 k (counterRoom_mono s (Nat.le_succ k) hroom)⟩

/-- **What a successful `Session::decrypt_ratchet` leaves in the two stores, at every frame**: under the hypotheses
of `decrypt_ratchet_refines_keeps_invariant_any`, for a frame whose header decodes to `c`, the call returns, refines
the model's step, keeps the invariant and has room for `k`, and when it succeeds the session it returns holds no
stored classical key for `c`'s ratchet key and number and no stored sparse key for `c`'s epoch and number (read through
the abstractions the relation uses): a stored key the call used is removed, a skip never stores the frame's own number,
and an eviction only removes (`decryptRatchet_consumes`, carried to the code by the relation after the call). -/
theorem decrypt_ratchet_refines_consumes_any (laws : ReceiveInvariantLaws) {R : Type}
    (rngCore : rand_core_1.RngCore R) (cryptoRng : rand_core_1.CryptoRng R)
    (trace : R → List Model.Lifecycle.Key) (dh : DhView)
    (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle)
    (oracleOf : DecryptOracleOf rngCore cryptoRng dh trace oracle)
    (codec : DhCodecOf dh)
    (contracts : Tacenta.UnitLifecycleT1.DecryptRatchetContracts rngCore)
    [Tacenta.SessionUnitT1.DerivedKeysModel]
    (agreements : DecryptRatchetAgreements oracle.braidKem)
    (s : lifecycle.Session) (m : Model.Lifecycle.Session) (message : Slice Std.U8) (rng : R) (k : Nat)
    (hinv : lifecycle.Session.invariant s = ok true)
    (hrel : SessionRefines dh oracle.braidKem s m)
    (hroom : CounterRoom s (k + 1))
    (htrace : trace rng = oracle.draws)
    (inputs : DecryptRatchetRunInputs view oracle trace s m message rng)
    (c : Model.CompositeHeader.Composite) (ct : Model.Lifecycle.Bytes)
    (hd : Model.CompositeHeader.decodeDetailed (sliceOf message) = .ok (c, ct)) :
    ∃ output,
      lifecycle.Session.decrypt_ratchet rngCore cryptoRng s message rng = ok output ∧
      StepRefines trace dh oracle.braidKem output
        (Model.Lifecycle.decryptRatchet view oracle m (sliceOf message)) ∧
      lifecycle.Session.invariant output.2.1 = ok true ∧ CounterRoom output.2.1 k ∧
      ∀ pt, output.1 = core.result.Result.Ok pt →
        (∀ e ∈ (Tacenta.SessionUnitTripleT3.ratchetAbs output.2.1.triple.classical).skipped,
            ¬ (e.1 = c.dh ∧ e.2.1 = c.n.toNat)) ∧
          ∀ x ∈ (Tacenta.SessionUnitTripleT3.spqrAbs output.2.1.triple.post_quantum).skipped,
            ¬ (x.1 = c.pqEpoch.toNat ∧ x.2.1 = c.pqN.toNat) := by
  obtain ⟨output, hcall, hstep, hinv', hroom'⟩ := decrypt_ratchet_refines_keeps_invariant_any laws rngCore cryptoRng
    trace dh view oracle oracleOf codec contracts agreements s m message rng k hinv hrel hroom htrace inputs
  refine ⟨output, hcall, hstep, hinv', hroom', fun pt hpt => ?_⟩
  have hres := hstep.result
  rw [hpt] at hres
  rcases hm : (Model.Lifecycle.decryptRatchet view oracle m (sliceOf message)).result with r | b
  · rw [hm] at hres; exact absurd hres (by simp [Tacenta.UnitLifecycleT3.ResultRefines])
  obtain ⟨hcl, hpq⟩ := decryptRatchet_consumes view oracle m (sliceOf message) c ct hd b hm
  rw [hstep.session.triple.1, hstep.session.triple.2]
  exact ⟨hcl, hpq⟩

/-- **The public `Session::decrypt` of a ratchet-type frame refines the model's `decrypt` and keeps
`Session::invariant` and the counter budget, at every frame**: as `decrypt_ratchet_refines_keeps_invariant_any`, for
the public call on a frame whose type byte is the ratchet type.  A frame over the size bound is refused with the
session unchanged; otherwise the model's dispatch passes the frame on (`dispatchDecrypt_passthrough`), and the step is
the model's own `decrypt` (`decrypt_receiveStepAny`). -/
theorem decrypt_refines_keeps_invariant_any (laws : ReceiveInvariantLaws) {R : Type}
    (rngCore : rand_core_1.RngCore R) (cryptoRng : rand_core_1.CryptoRng R)
    (trace : R → List Model.Lifecycle.Key) (dh : DhView)
    (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle)
    (oracleOf : DecryptOracleOf rngCore cryptoRng dh trace oracle)
    (codec : DhCodecOf dh)
    (contracts : Tacenta.UnitLifecycleT1.DecryptRatchetContracts rngCore)
    [Tacenta.SessionUnitT1.DerivedKeysModel]
    (agreements : DecryptRatchetAgreements oracle.braidKem)
    (s : lifecycle.Session) (m : Model.Lifecycle.Session) (message : Slice Std.U8) (rng : R) (k : Nat)
    (hinv : lifecycle.Session.invariant s = ok true)
    (hrel : SessionRefines dh oracle.braidKem s m)
    (hroom : CounterRoom s (k + 1))
    (htype : serialization.message_type message = ok (some serialization.MessageType.Ratchet))
    (htrace : trace rng = oracle.draws)
    (inputs : DecryptRatchetRunInputs view oracle trace s m message rng) :
    ∃ output,
      lifecycle.Session.decrypt rngCore cryptoRng s message rng = ok output ∧
      StepRefines trace dh oracle.braidKem output
        (Model.Lifecycle.decrypt view oracle m (sliceOf message)) ∧
      lifecycle.Session.invariant output.2.1 = ok true ∧ CounterRoom output.2.1 k := by
  have hkeep : CounterRoom s k := counterRoom_mono s (Nat.le_succ k) hroom
  by_cases hlong : Model.Lifecycle.frameTooLong (sliceOf message) = true
  · obtain ⟨hreal, hstep⟩ := decrypt_frame_too_long_step_refines rngCore cryptoRng trace dh oracle.braidKem
      view oracle s m message rng hrel htrace hlong
    exact ⟨_, hreal, hstep, hinv, hkeep⟩
  have hsize : Model.Lifecycle.frameTooLong (sliceOf message) = false := by simpa using hlong
  obtain ⟨inner, hin, hstepIn, -⟩ := decrypt_ratchet_refines_keeps_invariant_any laws rngCore cryptoRng trace dh
    view oracle oracleOf codec contracts agreements s m message rng k hinv hrel hroom htrace inputs
  obtain ⟨⟨res, s', rng'⟩, hcall, hstep⟩ := decrypt_ratchet_message_refines rngCore cryptoRng trace dh
    oracle.braidKem view oracle s m message rng inner hsize htype hin hstepIn
  refine ⟨_, hcall, hstep, ?_⟩
  rcases res with pt | e
  · have hdisp : Model.Lifecycle.dispatchDecrypt oracle m (sliceOf message) = .ok (sliceOf message) :=
      Model.Lifecycle.dispatchDecrypt_passthrough oracle m _ hsize
        (by rw [message_type_refines_ratchet message htype]; simp)
    exact decrypt_keeps_invariant_any laws rngCore cryptoRng dh codec oracle.braidKem oracle oracleOf.dhPublic
      s m _ k hinv hroom hrel message rng pt s' rng' hcall hstep.session
      (decrypt_receiveStepAny view oracle m (sliceOf message) (sliceOf message) hdisp)
  · obtain ⟨h1, h2⟩ := decrypt_err_keeps_invariant rngCore cryptoRng s message rng e s' rng' hinv hcall
    exact ⟨h1, h2 k hkeep⟩

/-- **From the bytes `Session::import` accepted to the next `Session::decrypt`, refined and kept, at every frame**:
as `UnitLifecycleDecryptCompose.restored_decrypt_keeps_invariant` with the in-order scope dropped.  For every byte
string `import` accepts with a session `s` in the restored scope (`RestoredScope`) whose counters pass
`roomCheck s (k + 1)`, and every ratchet-type frame, the public `decrypt` returns, refines the model's `decrypt` at
`restoredModelOf dh s`, and leaves a session that passes `Session::invariant` and has room for `k`.  `import` makes no
such check, and acceptance gives no budget (`UnitLifecycleImportBudget.acceptance_does_not_give_headroom`). -/
theorem restored_decrypt_keeps_invariant_any (laws : ReceiveInvariantLaws) {R : Type}
    (rngCore : rand_core_1.RngCore R) (cryptoRng : rand_core_1.CryptoRng R)
    (trace : R → List Model.Lifecycle.Key) (dh : DhView)
    (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle)
    (oracleOf : DecryptOracleOf rngCore cryptoRng dh trace oracle)
    (codec : DhCodecOf dh)
    (contracts : Tacenta.UnitLifecycleT1.DecryptRatchetContracts rngCore)
    [Tacenta.SessionUnitT1.DerivedKeysModel]
    (agreements : DecryptRatchetAgreements oracle.braidKem)
    (bytes : Slice Std.U8) (s : lifecycle.Session) (k : Nat)
    (h : lifecycle.Session.import bytes = ok (core.result.Result.Ok s))
    (hscope : RestoredScope s) (hcheck : roomCheck s (k + 1) = true)
    (message : Slice Std.U8) (rng : R)
    (htype : serialization.message_type message = ok (some serialization.MessageType.Ratchet))
    (htrace : trace rng = oracle.draws)
    (hchunk : ∀ (realComposite : tacenta_wire.Composite)
      (modelComposite : Model.CompositeHeader.Composite) (ciphertext : Model.Lifecycle.Bytes),
      Model.CompositeHeader.decodeDetailed (sliceOf message) = .ok (modelComposite, ciphertext) →
      Tacenta.UnitLifecycleT3.CompositeRefines realComposite modelComposite →
      Tacenta.UnitLifecycleT3.IncomingChunkRefines view (restoredModelOf dh s).braid realComposite
        modelComposite)
    (hdraw : ∃ draw rest, trace rng = draw :: rest) :
    ∃ output,
      lifecycle.Session.decrypt rngCore cryptoRng s message rng = ok output ∧
      StepRefines trace dh oracle.braidKem output
        (Model.Lifecycle.decrypt view oracle (restoredModelOf dh s) (sliceOf message)) ∧
      lifecycle.Session.invariant output.2.1 = ok true ∧ CounterRoom output.2.1 k := by
  exact decrypt_refines_keeps_invariant_any laws rngCore cryptoRng trace dh view oracle oracleOf codec contracts
    agreements s (restoredModelOf dh s) message rng k (import_ok_gives_invariant bytes s h)
    (sessionRefines_restored dh oracle.braidKem s hscope) ((counterRoom_iff_roomCheck s (k + 1)).mpr hcheck)
    htype htrace ⟨hchunk, fun _ _ _ => honestChunk_restored dh s hscope _, hdraw⟩

end Tacenta.UnitLifecycleOutOfOrderReceive

-- The pins `genpins.py` writes after this line print each statement whole: with no cut at depth 50
-- (`pp.deepTerms`) and each omitted proof with its proposition, `(⋯ : P)` (`pp.proofs.withType`). `attest.py`
-- refuses a statement pin that prints a bare `⋯`, and every other `pp` option.
set_option pp.deepTerms true
set_option pp.proofs.withType true

/-! ## Pins

The constants each result depends on, and the statement of each result and definition, held by the
build.  `attest.py` requires every one of them (`REQUIRED_PINS`, `REQUIRED_STATEMENT_PINS`,
`REQUIRED_PRINT_FORM`). -/

/--
info: 'Tacenta.UnitLifecycleOutOfOrderReceive.ratchet_receive_cases' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleOutOfOrderReceive.ratchet_receive_cases

/--
info: 'Tacenta.UnitLifecycleOutOfOrderReceive.ratchet_trySkipped_shape' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleOutOfOrderReceive.ratchet_trySkipped_shape

/--
info: 'Tacenta.UnitLifecycleOutOfOrderReceive.modelRatchetInv_shrink' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleOutOfOrderReceive.modelRatchetInv_shrink

/--
info: 'Tacenta.UnitLifecycleOutOfOrderReceive.modelRatchetInv_ageStore' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleOutOfOrderReceive.modelRatchetInv_ageStore

/--
info: 'Tacenta.UnitLifecycleOutOfOrderReceive.deriveChain_length' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleOutOfOrderReceive.deriveChain_length

/--
info: 'Tacenta.UnitLifecycleOutOfOrderReceive.deriveChain_num_ge' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleOutOfOrderReceive.deriveChain_num_ge

/--
info: 'Tacenta.UnitLifecycleOutOfOrderReceive.deriveChain_num_lt' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleOutOfOrderReceive.deriveChain_num_lt

/--
info: 'Tacenta.UnitLifecycleOutOfOrderReceive.deriveChain_nodup' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleOutOfOrderReceive.deriveChain_nodup

/--
info: 'Tacenta.UnitLifecycleOutOfOrderReceive.modelRatchetInv_skip' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleOutOfOrderReceive.modelRatchetInv_skip

/--
info: 'Tacenta.UnitLifecycleOutOfOrderReceive.modelRatchetInv_dhRatchet' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleOutOfOrderReceive.modelRatchetInv_dhRatchet

/--
info: 'Tacenta.UnitLifecycleOutOfOrderReceive.modelRatchetInv_classicalTail' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleOutOfOrderReceive.modelRatchetInv_classicalTail

/--
info: 'Tacenta.UnitLifecycleOutOfOrderReceive.modelRatchetInv_receive_any' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleOutOfOrderReceive.modelRatchetInv_receive_any

/--
info: 'Tacenta.UnitLifecycleOutOfOrderReceive.skip_frame' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleOutOfOrderReceive.skip_frame

/--
info: 'Tacenta.UnitLifecycleOutOfOrderReceive.ratchet_receive_any_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleOutOfOrderReceive.ratchet_receive_any_frame

/--
info: 'Tacenta.UnitLifecycleOutOfOrderReceive.modelSpqrInv_setChains' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleOutOfOrderReceive.modelSpqrInv_setChains

/--
info: 'Tacenta.UnitLifecycleOutOfOrderReceive.deriveInto_length' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleOutOfOrderReceive.deriveInto_length

/--
info: 'Tacenta.UnitLifecycleOutOfOrderReceive.deriveInto_num_gt' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleOutOfOrderReceive.deriveInto_num_gt

/--
info: 'Tacenta.UnitLifecycleOutOfOrderReceive.deriveInto_num_le' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleOutOfOrderReceive.deriveInto_num_le

/--
info: 'Tacenta.UnitLifecycleOutOfOrderReceive.deriveInto_nodup' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleOutOfOrderReceive.deriveInto_nodup

/--
info: 'Tacenta.UnitLifecycleOutOfOrderReceive.modelSpqrInv_skip' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleOutOfOrderReceive.modelSpqrInv_skip

/--
info: 'Tacenta.UnitLifecycleOutOfOrderReceive.modelSpqrInv_sparseTail' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleOutOfOrderReceive.modelSpqrInv_sparseTail

/--
info: 'Tacenta.UnitLifecycleOutOfOrderReceive.spqr_receive_cases' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleOutOfOrderReceive.spqr_receive_cases

/--
info: 'Tacenta.UnitLifecycleOutOfOrderReceive.spqr_trySkipped_shape' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleOutOfOrderReceive.spqr_trySkipped_shape

/--
info: 'Tacenta.UnitLifecycleOutOfOrderReceive.modelSpqrInv_shrink' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleOutOfOrderReceive.modelSpqrInv_shrink

/--
info: 'Tacenta.UnitLifecycleOutOfOrderReceive.modelSpqrInv_receive_any' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleOutOfOrderReceive.modelSpqrInv_receive_any

/--
info: 'Tacenta.UnitLifecycleOutOfOrderReceive.storeShrunk_refl' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleOutOfOrderReceive.storeShrunk_refl

/--
info: 'Tacenta.UnitLifecycleOutOfOrderReceive.storeShrunk_trans' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleOutOfOrderReceive.storeShrunk_trans

/--
info: 'Tacenta.UnitLifecycleOutOfOrderReceive.eraseFirstSkipped_sublist' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleOutOfOrderReceive.eraseFirstSkipped_sublist

/--
info: 'Tacenta.UnitLifecycleOutOfOrderReceive.ratchet_evictOldest_shape' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleOutOfOrderReceive.ratchet_evictOldest_shape

/--
info: 'Tacenta.UnitLifecycleOutOfOrderReceive.evictOldestClassical_shrunk' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleOutOfOrderReceive.evictOldestClassical_shrunk

/--
info: 'Tacenta.UnitLifecycleOutOfOrderReceive.evictOldestPostQuantum_shrunk' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleOutOfOrderReceive.evictOldestPostQuantum_shrunk

/--
info: 'Tacenta.UnitLifecycleOutOfOrderReceive.loop_ok_shrunk' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleOutOfOrderReceive.loop_ok_shrunk

/--
info: 'Tacenta.UnitLifecycleOutOfOrderReceive.receiveWithEviction_ok_shrunk' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleOutOfOrderReceive.receiveWithEviction_ok_shrunk

/--
info: 'Tacenta.UnitLifecycleOutOfOrderReceive.triple_receive_split' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleOutOfOrderReceive.triple_receive_split

/--
info: 'Tacenta.UnitLifecycleOutOfOrderReceive.advanced_chains' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleOutOfOrderReceive.advanced_chains

/--
info: 'Tacenta.UnitLifecycleOutOfOrderReceive.triple_receive_any_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleOutOfOrderReceive.triple_receive_any_frame

/--
info: 'Tacenta.UnitLifecycleOutOfOrderReceive.triple_receive_any' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleOutOfOrderReceive.triple_receive_any

/--
info: 'Tacenta.UnitLifecycleOutOfOrderReceive.modelTripleInv_shrunk' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleOutOfOrderReceive.modelTripleInv_shrunk

/--
info: 'Tacenta.UnitLifecycleOutOfOrderReceive.decryptRatchet_receiveStepAny' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleOutOfOrderReceive.decryptRatchet_receiveStepAny

/--
info: 'Tacenta.UnitLifecycleOutOfOrderReceive.decrypt_receiveStepAny' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleOutOfOrderReceive.decrypt_receiveStepAny

/--
info: 'Tacenta.UnitLifecycleOutOfOrderReceive.receiveStepAny_parts' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleOutOfOrderReceive.receiveStepAny_parts

/--
info: 'Tacenta.UnitLifecycleOutOfOrderReceive.modelTripleInv_stepAny' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleOutOfOrderReceive.modelTripleInv_stepAny

/--
info: 'Tacenta.UnitLifecycleOutOfOrderReceive.modelCounterRoom_stepAny' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleOutOfOrderReceive.modelCounterRoom_stepAny

/--
info: 'Tacenta.UnitLifecycleOutOfOrderReceive.step_frame_stepAny' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleOutOfOrderReceive.step_frame_stepAny

/--
info: 'Tacenta.UnitLifecycleOutOfOrderReceive.skip_stored' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleOutOfOrderReceive.skip_stored

/--
info: 'Tacenta.UnitLifecycleOutOfOrderReceive.ratchet_receive_consumes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleOutOfOrderReceive.ratchet_receive_consumes

/--
info: 'Tacenta.UnitLifecycleOutOfOrderReceive.spqr_skip_stored' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleOutOfOrderReceive.spqr_skip_stored

/--
info: 'Tacenta.UnitLifecycleOutOfOrderReceive.spqr_receive_consumes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleOutOfOrderReceive.spqr_receive_consumes

/--
info: 'Tacenta.UnitLifecycleOutOfOrderReceive.triple_receive_consumes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleOutOfOrderReceive.triple_receive_consumes

/--
info: 'Tacenta.UnitLifecycleOutOfOrderReceive.decryptRatchet_consumes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleOutOfOrderReceive.decryptRatchet_consumes

/--
info: 'Tacenta.UnitLifecycleOutOfOrderReceive.decrypt_ratchet_keeps_invariant_any' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_kem.CT1_LEN,
 tacenta_kem.CT2_LEN,
 tacenta_kem.EK_VECTOR_LEN,
 tacenta_kem.EncapsState,
 tacenta_kem.HEADER_LEN,
 tacenta_kem.IncrementalKeyPair,
 tacenta_kem.encapsulate1,
 tacenta_kem.encapsulate2,
 tacenta_kem.validate_ek,
 zeroize.Zeroizing,
 rand_core_1.error.Error,
 tacenta_boundary.aead.decrypt,
 tacenta_boundary.aead.encrypt,
 tacenta_boundary.dh.PrivateKey,
 tacenta_boundary.dh.PublicKeyBytes,
 tacenta_boundary.dh.is_prime_order_public,
 tacenta_boundary.kem.KeyPair,
 tacenta_boundary.kem.ciphertext_len,
 tacenta_boundary.kem.decapsulate,
 tacenta_boundary.kem.encapsulate,
 tacenta_boundary.xeddsa.verify,
 tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_kem.IncrementalKeyPair.generate,
 tacenta_kem.IncrementalKeyPair.header,
 zeroize.Zeroizing.new,
 Array.Insts.ZeroizeZeroize.zeroize,
 Pair.Insts.ZeroizeZeroize.zeroize,
 TupleABC.Insts.ZeroizeZeroize.zeroize,
 alloc.vec.Vec.capacity,
 alloc.vec.Vec.pop,
 alloc.vec.Vec.truncate,
 core.num.Usize.div_ceil,
 core.option.Option.as_mut,
 tacenta_boundary.dh.PrivateKey.agree,
 tacenta_boundary.dh.PrivateKey.from_bytes,
 tacenta_boundary.dh.PrivateKey.public_key,
 tacenta_boundary.dh.PrivateKey.to_bytes,
 tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_boundary.dh.PublicKeyBytes.from_bytes,
 zeroize.Zeroize.Blanket.zeroize,
 tacenta_kem.EncapsState.Insts.CoreCloneClone.clone,
 tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone,
 zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 core.option.Option.Insts.CoreCloneClone.clone,
 core.option.Option.Insts.CoreCmpPartialEqOption.eq,
 tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes.eq,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleOutOfOrderReceive.decrypt_ratchet_keeps_invariant_any

/--
info: 'Tacenta.UnitLifecycleOutOfOrderReceive.decrypt_keeps_invariant_any' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_kem.CT1_LEN,
 tacenta_kem.CT2_LEN,
 tacenta_kem.EK_VECTOR_LEN,
 tacenta_kem.EncapsState,
 tacenta_kem.HEADER_LEN,
 tacenta_kem.IncrementalKeyPair,
 tacenta_kem.encapsulate1,
 tacenta_kem.encapsulate2,
 tacenta_kem.validate_ek,
 zeroize.Zeroizing,
 rand_core_1.error.Error,
 tacenta_boundary.aead.decrypt,
 tacenta_boundary.aead.encrypt,
 tacenta_boundary.dh.PrivateKey,
 tacenta_boundary.dh.PublicKeyBytes,
 tacenta_boundary.dh.is_prime_order_public,
 tacenta_boundary.kem.KeyPair,
 tacenta_boundary.kem.ciphertext_len,
 tacenta_boundary.kem.decapsulate,
 tacenta_boundary.kem.encapsulate,
 tacenta_boundary.xeddsa.verify,
 tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_kem.IncrementalKeyPair.generate,
 tacenta_kem.IncrementalKeyPair.header,
 zeroize.Zeroizing.new,
 Array.Insts.ZeroizeZeroize.zeroize,
 Pair.Insts.ZeroizeZeroize.zeroize,
 TupleABC.Insts.ZeroizeZeroize.zeroize,
 alloc.vec.Vec.capacity,
 alloc.vec.Vec.pop,
 alloc.vec.Vec.truncate,
 core.num.Usize.div_ceil,
 core.option.Option.as_mut,
 tacenta_boundary.dh.PrivateKey.agree,
 tacenta_boundary.dh.PrivateKey.from_bytes,
 tacenta_boundary.dh.PrivateKey.public_key,
 tacenta_boundary.dh.PrivateKey.to_bytes,
 tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_boundary.dh.PublicKeyBytes.from_bytes,
 zeroize.Zeroize.Blanket.zeroize,
 tacenta_kem.EncapsState.Insts.CoreCloneClone.clone,
 tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone,
 zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 core.option.Option.Insts.CoreCloneClone.clone,
 core.option.Option.Insts.CoreCmpPartialEqOption.eq,
 tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes.eq,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleOutOfOrderReceive.decrypt_keeps_invariant_any

/--
info: 'Tacenta.UnitLifecycleOutOfOrderReceive.decrypt_ratchet_refines_keeps_invariant_any' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_kem.CT1_LEN,
 tacenta_kem.CT2_LEN,
 tacenta_kem.EK_VECTOR_LEN,
 tacenta_kem.EncapsState,
 tacenta_kem.HEADER_LEN,
 tacenta_kem.IncrementalKeyPair,
 tacenta_kem.encapsulate1,
 tacenta_kem.encapsulate2,
 tacenta_kem.validate_ek,
 zeroize.Zeroizing,
 rand_core_1.error.Error,
 tacenta_boundary.aead.decrypt,
 tacenta_boundary.aead.encrypt,
 tacenta_boundary.dh.PrivateKey,
 tacenta_boundary.dh.PublicKeyBytes,
 tacenta_boundary.dh.is_prime_order_public,
 tacenta_boundary.kem.KeyPair,
 tacenta_boundary.kem.ciphertext_len,
 tacenta_boundary.kem.decapsulate,
 tacenta_boundary.kem.encapsulate,
 tacenta_boundary.xeddsa.verify,
 tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_kem.IncrementalKeyPair.generate,
 tacenta_kem.IncrementalKeyPair.header,
 zeroize.Zeroizing.new,
 Array.Insts.ZeroizeZeroize.zeroize,
 Pair.Insts.ZeroizeZeroize.zeroize,
 TupleABC.Insts.ZeroizeZeroize.zeroize,
 alloc.vec.Vec.capacity,
 alloc.vec.Vec.pop,
 alloc.vec.Vec.truncate,
 core.num.Usize.div_ceil,
 core.option.Option.as_mut,
 tacenta_boundary.dh.PrivateKey.agree,
 tacenta_boundary.dh.PrivateKey.from_bytes,
 tacenta_boundary.dh.PrivateKey.public_key,
 tacenta_boundary.dh.PrivateKey.to_bytes,
 tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_boundary.dh.PublicKeyBytes.from_bytes,
 zeroize.Zeroize.Blanket.zeroize,
 tacenta_kem.EncapsState.Insts.CoreCloneClone.clone,
 tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone,
 zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 core.option.Option.Insts.CoreCloneClone.clone,
 core.option.Option.Insts.CoreCmpPartialEqOption.eq,
 tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes.eq,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleOutOfOrderReceive.decrypt_ratchet_refines_keeps_invariant_any

/--
info: 'Tacenta.UnitLifecycleOutOfOrderReceive.decrypt_ratchet_refines_consumes_any' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_kem.CT1_LEN,
 tacenta_kem.CT2_LEN,
 tacenta_kem.EK_VECTOR_LEN,
 tacenta_kem.EncapsState,
 tacenta_kem.HEADER_LEN,
 tacenta_kem.IncrementalKeyPair,
 tacenta_kem.encapsulate1,
 tacenta_kem.encapsulate2,
 tacenta_kem.validate_ek,
 zeroize.Zeroizing,
 rand_core_1.error.Error,
 tacenta_boundary.aead.decrypt,
 tacenta_boundary.aead.encrypt,
 tacenta_boundary.dh.PrivateKey,
 tacenta_boundary.dh.PublicKeyBytes,
 tacenta_boundary.dh.is_prime_order_public,
 tacenta_boundary.kem.KeyPair,
 tacenta_boundary.kem.ciphertext_len,
 tacenta_boundary.kem.decapsulate,
 tacenta_boundary.kem.encapsulate,
 tacenta_boundary.xeddsa.verify,
 tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_kem.IncrementalKeyPair.generate,
 tacenta_kem.IncrementalKeyPair.header,
 zeroize.Zeroizing.new,
 Array.Insts.ZeroizeZeroize.zeroize,
 Pair.Insts.ZeroizeZeroize.zeroize,
 TupleABC.Insts.ZeroizeZeroize.zeroize,
 alloc.vec.Vec.capacity,
 alloc.vec.Vec.pop,
 alloc.vec.Vec.truncate,
 core.num.Usize.div_ceil,
 core.option.Option.as_mut,
 tacenta_boundary.dh.PrivateKey.agree,
 tacenta_boundary.dh.PrivateKey.from_bytes,
 tacenta_boundary.dh.PrivateKey.public_key,
 tacenta_boundary.dh.PrivateKey.to_bytes,
 tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_boundary.dh.PublicKeyBytes.from_bytes,
 zeroize.Zeroize.Blanket.zeroize,
 tacenta_kem.EncapsState.Insts.CoreCloneClone.clone,
 tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone,
 zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 core.option.Option.Insts.CoreCloneClone.clone,
 core.option.Option.Insts.CoreCmpPartialEqOption.eq,
 tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes.eq,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleOutOfOrderReceive.decrypt_ratchet_refines_consumes_any

/--
info: 'Tacenta.UnitLifecycleOutOfOrderReceive.decrypt_refines_keeps_invariant_any' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_kem.CT1_LEN,
 tacenta_kem.CT2_LEN,
 tacenta_kem.EK_VECTOR_LEN,
 tacenta_kem.EncapsState,
 tacenta_kem.HEADER_LEN,
 tacenta_kem.IncrementalKeyPair,
 tacenta_kem.encapsulate1,
 tacenta_kem.encapsulate2,
 tacenta_kem.validate_ek,
 zeroize.Zeroizing,
 rand_core_1.error.Error,
 tacenta_boundary.aead.decrypt,
 tacenta_boundary.aead.encrypt,
 tacenta_boundary.dh.PrivateKey,
 tacenta_boundary.dh.PublicKeyBytes,
 tacenta_boundary.dh.is_prime_order_public,
 tacenta_boundary.kem.KeyPair,
 tacenta_boundary.kem.ciphertext_len,
 tacenta_boundary.kem.decapsulate,
 tacenta_boundary.kem.encapsulate,
 tacenta_boundary.xeddsa.verify,
 tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_kem.IncrementalKeyPair.generate,
 tacenta_kem.IncrementalKeyPair.header,
 zeroize.Zeroizing.new,
 Array.Insts.ZeroizeZeroize.zeroize,
 Pair.Insts.ZeroizeZeroize.zeroize,
 TupleABC.Insts.ZeroizeZeroize.zeroize,
 alloc.vec.Vec.capacity,
 alloc.vec.Vec.pop,
 alloc.vec.Vec.truncate,
 core.num.Usize.div_ceil,
 core.option.Option.as_mut,
 tacenta_boundary.dh.PrivateKey.agree,
 tacenta_boundary.dh.PrivateKey.from_bytes,
 tacenta_boundary.dh.PrivateKey.public_key,
 tacenta_boundary.dh.PrivateKey.to_bytes,
 tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_boundary.dh.PublicKeyBytes.from_bytes,
 zeroize.Zeroize.Blanket.zeroize,
 tacenta_kem.EncapsState.Insts.CoreCloneClone.clone,
 tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone,
 zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 core.option.Option.Insts.CoreCloneClone.clone,
 core.option.Option.Insts.CoreCmpPartialEqOption.eq,
 tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes.eq,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleOutOfOrderReceive.decrypt_refines_keeps_invariant_any

/--
info: 'Tacenta.UnitLifecycleOutOfOrderReceive.restored_decrypt_keeps_invariant_any' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_kem.CT1_LEN,
 tacenta_kem.CT2_LEN,
 tacenta_kem.EK_VECTOR_LEN,
 tacenta_kem.EncapsState,
 tacenta_kem.HEADER_LEN,
 tacenta_kem.IncrementalKeyPair,
 tacenta_kem.encapsulate1,
 tacenta_kem.encapsulate2,
 tacenta_kem.validate_ek,
 zeroize.Zeroizing,
 rand_core_1.error.Error,
 tacenta_boundary.aead.decrypt,
 tacenta_boundary.aead.encrypt,
 tacenta_boundary.dh.PrivateKey,
 tacenta_boundary.dh.PublicKeyBytes,
 tacenta_boundary.dh.is_prime_order_public,
 tacenta_boundary.kem.KeyPair,
 tacenta_boundary.kem.ciphertext_len,
 tacenta_boundary.kem.decapsulate,
 tacenta_boundary.kem.encapsulate,
 tacenta_boundary.xeddsa.verify,
 tacenta_kem.EncapsState.from_bytes,
 tacenta_kem.EncapsState.to_bytes,
 tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_kem.IncrementalKeyPair.from_bytes,
 tacenta_kem.IncrementalKeyPair.generate,
 tacenta_kem.IncrementalKeyPair.header,
 tacenta_kem.IncrementalKeyPair.to_bytes,
 zeroize.Zeroizing.new,
 Array.Insts.ZeroizeZeroize.zeroize,
 Pair.Insts.ZeroizeZeroize.zeroize,
 TupleABC.Insts.ZeroizeZeroize.zeroize,
 alloc.vec.Vec.as_slice,
 alloc.vec.Vec.capacity,
 alloc.vec.Vec.pop,
 alloc.vec.Vec.truncate,
 core.num.Usize.div_ceil,
 core.option.Option.as_mut,
 tacenta_boundary.dh.PrivateKey.agree,
 tacenta_boundary.dh.PrivateKey.from_bytes,
 tacenta_boundary.dh.PrivateKey.public_key,
 tacenta_boundary.dh.PrivateKey.to_bytes,
 tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_boundary.dh.PublicKeyBytes.from_bytes,
 zeroize.Zeroize.Blanket.zeroize,
 tacenta_kem.EncapsState.Insts.CoreCloneClone.clone,
 tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone,
 zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 core.option.Option.Insts.CoreCloneClone.clone,
 core.option.Option.Insts.CoreCmpPartialEqOption.eq,
 core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual,
 core.option.Option.Insts.CoreOpsTry_traitTry.branch,
 lifecycle.PrekeyStore.to_bytes._native.decide.ax_1,
 tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes.eq,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleOutOfOrderReceive.restored_decrypt_keeps_invariant_any

/--
info: @Tacenta.UnitLifecycleOutOfOrderReceive.ratchet_receive_cases : ∀ {st st' : Model.State.State}
  {hdr : Model.State.Header} {dr ds np mk : Model.State.Key},
  Model.Ratchet.receiveDetailed st hdr dr ds np = Except.ok (st', mk) →
    (∃ next, Model.Ratchet.trySkipped st hdr = some (next, mk) ∧ st' = Model.State.ageStore next) ∨
      Model.Ratchet.trySkipped st hdr = none ∧
        ∃ st1 st2,
          Tacenta.UnitLifecycleOutOfOrderReceive.SteppedTo st hdr dr ds np st1 ∧
            Model.State.skipMessageKeys st1 hdr.n = some st2 ∧
              Tacenta.UnitLifecycleReceivePreserve.classicalTail st2 hdr = Except.ok (st', mk)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleOutOfOrderReceive.ratchet_receive_cases

/--
info: @Tacenta.UnitLifecycleOutOfOrderReceive.ratchet_trySkipped_shape : ∀ {st next : Model.State.State}
  {hdr : Model.State.Header} {mk : Model.State.Key},
  Model.Ratchet.trySkipped st hdr = some (next, mk) →
    next =
        { dhsPub := st.dhsPub, dhrPub := st.dhrPub, rk := st.rk, cks := st.cks, ckr := st.ckr, ns := st.ns, nr := st.nr,
          pn := st.pn, skipped := next.skipped, events := st.events, labels := st.labels } ∧
      next.skipped.Sublist st.skipped
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleOutOfOrderReceive.ratchet_trySkipped_shape

/--
info: @Tacenta.UnitLifecycleOutOfOrderReceive.modelRatchetInv_shrink : ∀ {st : Model.State.State}
  {l : List (Model.State.Key × ℕ × ℕ × Model.State.Key)},
  Tacenta.UnitTripleInvModel.ModelRatchetInv st →
    l.Sublist st.skipped →
      Tacenta.UnitTripleInvModel.ModelRatchetInv
        { dhsPub := st.dhsPub, dhrPub := st.dhrPub, rk := st.rk, cks := st.cks, ckr := st.ckr, ns := st.ns, nr := st.nr,
          pn := st.pn, skipped := l, events := st.events, labels := st.labels }
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleOutOfOrderReceive.modelRatchetInv_shrink

/--
info: @Tacenta.UnitLifecycleOutOfOrderReceive.modelRatchetInv_ageStore : ∀ {st : Model.State.State},
  Tacenta.UnitTripleInvModel.ModelRatchetInv st → Tacenta.UnitTripleInvModel.ModelRatchetInv (Model.State.ageStore st)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleOutOfOrderReceive.modelRatchetInv_ageStore

/--
info: Tacenta.UnitLifecycleOutOfOrderReceive.deriveChain_length : ∀ (ck : Model.State.Key) (start c : ℕ),
  (Model.State.deriveChain ck start c).2.length = c
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleOutOfOrderReceive.deriveChain_length

/--
info: Tacenta.UnitLifecycleOutOfOrderReceive.deriveChain_num_ge : ∀ (ck : Model.State.Key) (start c : ℕ),
  ∀ x ∈ (Model.State.deriveChain ck start c).2, start ≤ x.1
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleOutOfOrderReceive.deriveChain_num_ge

/--
info: Tacenta.UnitLifecycleOutOfOrderReceive.deriveChain_num_lt : ∀ (ck : Model.State.Key) (start c : ℕ),
  ∀ x ∈ (Model.State.deriveChain ck start c).2, x.1 < start + c
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleOutOfOrderReceive.deriveChain_num_lt

/--
info: Tacenta.UnitLifecycleOutOfOrderReceive.deriveChain_nodup : ∀ (ck : Model.State.Key) (start c : ℕ),
  List.Pairwise (fun a b => a.1 ≠ b.1) (Model.State.deriveChain ck start c).2
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleOutOfOrderReceive.deriveChain_nodup

/--
info: @Tacenta.UnitLifecycleOutOfOrderReceive.modelRatchetInv_skip : ∀ {st st' : Model.State.State} {upto : ℕ},
  Tacenta.UnitTripleInvModel.ModelRatchetInv st →
    Model.State.skipMessageKeys st upto = some st' →
      Tacenta.UnitTripleInvModel.ModelRatchetInv st' ∧
        st'.dhsPub = st.dhsPub ∧
          st'.dhrPub = st.dhrPub ∧ st'.events = st.events ∧ st'.cks = st.cks ∧ st'.ckr.isSome = st.ckr.isSome
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleOutOfOrderReceive.modelRatchetInv_skip

/--
info: @Tacenta.UnitLifecycleOutOfOrderReceive.modelRatchetInv_dhRatchet : ∀ {st : Model.State.State}
  {hdr : Model.State.Header} {dr ds np : Model.State.Key},
  Tacenta.UnitTripleInvModel.ModelRatchetInv st →
    Model.Messages.canonicalKey hdr.dh = true →
      Model.Messages.canonicalKey np = true →
        Tacenta.UnitTripleInvModel.ModelRatchetInv (Model.Ratchet.dhRatchet st hdr dr ds np)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleOutOfOrderReceive.modelRatchetInv_dhRatchet

/--
info: @Tacenta.UnitLifecycleOutOfOrderReceive.modelRatchetInv_classicalTail : ∀ {st st' : Model.State.State}
  {hdr : Model.State.Header} {mk : Model.State.Key},
  Tacenta.UnitTripleInvModel.ModelRatchetInv st →
    Tacenta.UnitLifecycleReceivePreserve.classicalTail st hdr = Except.ok (st', mk) →
      Tacenta.UnitTripleInvModel.ModelRatchetInv st' ∧ st'.dhsPub = st.dhsPub ∧ st'.events ≤ st.events + 1
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleOutOfOrderReceive.modelRatchetInv_classicalTail

/--
info: @Tacenta.UnitLifecycleOutOfOrderReceive.modelRatchetInv_receive_any : ∀ {st st' : Model.State.State}
  {hdr : Model.State.Header} {dr ds np mk : Model.State.Key},
  Tacenta.UnitTripleInvModel.ModelRatchetInv st →
    Model.Messages.canonicalKey hdr.dh = true →
      (Model.Ratchet.trySkipped st hdr = none → st.dhrPub ≠ some hdr.dh → Model.Messages.canonicalKey np = true) →
        Model.Ratchet.receiveDetailed st hdr dr ds np = Except.ok (st', mk) →
          Tacenta.UnitTripleInvModel.ModelRatchetInv st'
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleOutOfOrderReceive.modelRatchetInv_receive_any

/--
info: @Tacenta.UnitLifecycleOutOfOrderReceive.skip_frame : ∀ {st st' : Model.State.State} {upto : ℕ},
  Model.State.skipMessageKeys st upto = some st' → st'.dhsPub = st.dhsPub ∧ st'.events = st.events ∧ st'.cks = st.cks
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleOutOfOrderReceive.skip_frame

/--
info: @Tacenta.UnitLifecycleOutOfOrderReceive.ratchet_receive_any_frame : ∀ {st st' : Model.State.State}
  {hdr : Model.State.Header} {dr ds np mk : Model.State.Key},
  Model.Ratchet.receiveDetailed st hdr dr ds np = Except.ok (st', mk) →
    (Model.Ratchet.trySkipped st hdr = none → st.dhrPub ≠ some hdr.dh → st'.dhsPub = np) ∧
      (st'.dhsPub = st.dhsPub ∨ st'.dhsPub = np) ∧
        st'.events ≤ st.events + 1 ∧ (st'.cks = st.cks ∧ st'.ckr = st.ckr ∨ st'.ckr.isSome = true)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleOutOfOrderReceive.ratchet_receive_any_frame

/--
info: @Tacenta.UnitLifecycleOutOfOrderReceive.modelSpqrInv_setChains : ∀ {st : Model.SparseRatchet.State} {e : ℕ}
  {cs c' : Model.SparseRatchet.Chains} {l : List (ℕ × ℕ × Model.State.Key)},
  Tacenta.UnitTripleInvModel.ModelSpqrInv st →
    (e, cs) ∈ st.chains →
      l.length ≤ Model.SparseRatchet.maxSkippedStore →
        (∀ a ∈ l, ∃ q ∈ st.chains, q.1 = a.1) →
          List.Pairwise (fun a b => ¬(a.1 = b.1 ∧ a.2.1 = b.2.1)) l →
            Tacenta.UnitTripleInvModel.ModelSpqrInv
              (Model.SparseRatchet.setChains
                { rk := st.rk, epoch := st.epoch, chains := st.chains, skipped := l, direction := st.direction } e c')
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleOutOfOrderReceive.modelSpqrInv_setChains

/--
info: Tacenta.UnitLifecycleOutOfOrderReceive.deriveInto_length : ∀ (ck : Model.State.Key) (start c : ℕ),
  (Model.SparseRatchet.skipMessageKeys.deriveInto ck start c).2.length = c
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleOutOfOrderReceive.deriveInto_length

/--
info: Tacenta.UnitLifecycleOutOfOrderReceive.deriveInto_num_gt : ∀ (ck : Model.State.Key) (start c : ℕ),
  ∀ x ∈ (Model.SparseRatchet.skipMessageKeys.deriveInto ck start c).2, start < x.1
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleOutOfOrderReceive.deriveInto_num_gt

/--
info: Tacenta.UnitLifecycleOutOfOrderReceive.deriveInto_num_le : ∀ (ck : Model.State.Key) (start c : ℕ),
  ∀ x ∈ (Model.SparseRatchet.skipMessageKeys.deriveInto ck start c).2, x.1 ≤ start + c
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleOutOfOrderReceive.deriveInto_num_le

/--
info: Tacenta.UnitLifecycleOutOfOrderReceive.deriveInto_nodup : ∀ (ck : Model.State.Key) (start c : ℕ),
  List.Pairwise (fun a b => a.1 ≠ b.1) (Model.SparseRatchet.skipMessageKeys.deriveInto ck start c).2
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleOutOfOrderReceive.deriveInto_nodup

/--
info: @Tacenta.UnitLifecycleOutOfOrderReceive.modelSpqrInv_skip : ∀ {st st' : Model.SparseRatchet.State} {e upto : ℕ},
  Tacenta.UnitTripleInvModel.ModelSpqrInv st →
    Model.SparseRatchet.skipMessageKeys st e upto = some st' →
      Tacenta.UnitTripleInvModel.ModelSpqrInv st' ∧
        st'.epoch = st.epoch ∧
          st'.direction = st.direction ∧
            ∀ p ∈ st'.chains,
              ∀ (c : Model.SparseRatchet.Chain),
                Tacenta.UnitLifecycleEncryptPreserve.InChain p c →
                  ∃ p0 ∈ st.chains,
                    ∃ c0, Tacenta.UnitLifecycleEncryptPreserve.InChain p0 c0 ∧ c.n ≤ c0.n + Model.SparseRatchet.maxSkip
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleOutOfOrderReceive.modelSpqrInv_skip

/--
info: @Tacenta.UnitLifecycleOutOfOrderReceive.modelSpqrInv_sparseTail : ∀ {st st' : Model.SparseRatchet.State} {e n : ℕ}
  {mk : Model.State.Key},
  Tacenta.UnitTripleInvModel.ModelSpqrInv st →
    Tacenta.UnitLifecycleReceivePreserve.sparseTail st e n = Except.ok (st', mk) →
      Tacenta.UnitTripleInvModel.ModelSpqrInv st' ∧
        st'.epoch = st.epoch ∧
          st'.direction = st.direction ∧
            ∀ p ∈ st'.chains,
              ∀ (c : Model.SparseRatchet.Chain),
                Tacenta.UnitLifecycleEncryptPreserve.InChain p c →
                  ∃ p0 ∈ st.chains, ∃ c0, Tacenta.UnitLifecycleEncryptPreserve.InChain p0 c0 ∧ c.n ≤ c0.n + 1
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleOutOfOrderReceive.modelSpqrInv_sparseTail

/--
info: @Tacenta.UnitLifecycleOutOfOrderReceive.spqr_receive_cases : ∀ {st st' : Model.SparseRatchet.State} {e n : ℕ}
  {mk : Model.State.Key},
  Model.SparseRatchet.receiveDetailed st e none n = Except.ok (st', mk) →
    Model.SparseRatchet.trySkipped st e n = some (st', mk) ∨
      Model.SparseRatchet.trySkipped st e n = none ∧
        ∃ st2,
          Model.SparseRatchet.skipMessageKeys st e (n - 1) = some st2 ∧
            Tacenta.UnitLifecycleReceivePreserve.sparseTail st2 e n = Except.ok (st', mk)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleOutOfOrderReceive.spqr_receive_cases

/--
info: @Tacenta.UnitLifecycleOutOfOrderReceive.spqr_trySkipped_shape : ∀ {st st' : Model.SparseRatchet.State} {e n : ℕ}
  {mk : Model.State.Key},
  Model.SparseRatchet.trySkipped st e n = some (st', mk) →
    st' = { rk := st.rk, epoch := st.epoch, chains := st.chains, skipped := st'.skipped, direction := st.direction } ∧
      st'.skipped.Sublist st.skipped
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleOutOfOrderReceive.spqr_trySkipped_shape

/--
info: @Tacenta.UnitLifecycleOutOfOrderReceive.modelSpqrInv_shrink : ∀ {st : Model.SparseRatchet.State}
  {l : List (ℕ × ℕ × Model.State.Key)},
  Tacenta.UnitTripleInvModel.ModelSpqrInv st →
    l.Sublist st.skipped →
      Tacenta.UnitTripleInvModel.ModelSpqrInv
        { rk := st.rk, epoch := st.epoch, chains := st.chains, skipped := l, direction := st.direction }
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleOutOfOrderReceive.modelSpqrInv_shrink

/--
info: @Tacenta.UnitLifecycleOutOfOrderReceive.modelSpqrInv_receive_any : ∀ {st st' : Model.SparseRatchet.State} {e n : ℕ}
  {mk : Model.State.Key},
  Tacenta.UnitTripleInvModel.ModelSpqrInv st →
    Model.SparseRatchet.receiveDetailed st e none n = Except.ok (st', mk) →
      Tacenta.UnitTripleInvModel.ModelSpqrInv st' ∧
        st'.epoch = st.epoch ∧
          st'.direction = st.direction ∧
            ∀ p ∈ st'.chains,
              ∀ (c : Model.SparseRatchet.Chain),
                Tacenta.UnitLifecycleEncryptPreserve.InChain p c →
                  ∃ p0 ∈ st.chains,
                    ∃ c0,
                      Tacenta.UnitLifecycleEncryptPreserve.InChain p0 c0 ∧ c.n ≤ c0.n + Model.SparseRatchet.maxSkip + 1
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleOutOfOrderReceive.modelSpqrInv_receive_any

/--
info: Tacenta.UnitLifecycleOutOfOrderReceive.storeShrunk_refl : ∀ (t : Model.Triple.State),
  Tacenta.UnitLifecycleOutOfOrderReceive.StoreShrunk t t
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleOutOfOrderReceive.storeShrunk_refl

/--
info: @Tacenta.UnitLifecycleOutOfOrderReceive.storeShrunk_trans : ∀ {t t1 t2 : Model.Triple.State},
  Tacenta.UnitLifecycleOutOfOrderReceive.StoreShrunk t t1 →
    Tacenta.UnitLifecycleOutOfOrderReceive.StoreShrunk t1 t2 → Tacenta.UnitLifecycleOutOfOrderReceive.StoreShrunk t t2
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleOutOfOrderReceive.storeShrunk_trans

/--
info: Tacenta.UnitLifecycleOutOfOrderReceive.eraseFirstSkipped_sublist : ∀ (target : Model.Ratchet.SkippedEntry)
  (l : List Model.Ratchet.SkippedEntry), (Model.Ratchet.eraseFirstSkipped target l).Sublist l
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleOutOfOrderReceive.eraseFirstSkipped_sublist

/--
info: Tacenta.UnitLifecycleOutOfOrderReceive.ratchet_evictOldest_shape : ∀ (st : Model.State.State) (n : ℕ),
  (Model.Ratchet.evictOldest st n).1 =
      { dhsPub := st.dhsPub, dhrPub := st.dhrPub, rk := st.rk, cks := st.cks, ckr := st.ckr, ns := st.ns, nr := st.nr,
        pn := st.pn, skipped := (Model.Ratchet.evictOldest st n).1.skipped, events := st.events, labels := st.labels } ∧
    (Model.Ratchet.evictOldest st n).1.skipped.Sublist st.skipped
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleOutOfOrderReceive.ratchet_evictOldest_shape

/--
info: Tacenta.UnitLifecycleOutOfOrderReceive.evictOldestClassical_shrunk : ∀ (t : Model.Triple.State) (n : ℕ),
  Tacenta.UnitLifecycleOutOfOrderReceive.StoreShrunk t (Model.Triple.evictOldestClassical t n).1
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleOutOfOrderReceive.evictOldestClassical_shrunk

/--
info: Tacenta.UnitLifecycleOutOfOrderReceive.evictOldestPostQuantum_shrunk : ∀ (t : Model.Triple.State) (n : ℕ),
  Tacenta.UnitLifecycleOutOfOrderReceive.StoreShrunk t (Model.Triple.evictOldestPostQuantum t n).1
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleOutOfOrderReceive.evictOldestPostQuantum_shrunk

/--
info: Tacenta.UnitLifecycleOutOfOrderReceive.loop_ok_shrunk : ∀ (composite : Model.CompositeHeader.Composite)
  (header : Model.Triple.Header) (dr ds np : Model.State.Key) (out : Option Model.SparseRatchet.Output)
  (r : Model.Triple.State × Model.State.Key) (fuel : ℕ) (state : Model.Triple.State)
  (pending : Model.Triple.ReceiveRefusal) (half : Model.Lifecycle.FullStore) (batch : ℕ),
  Model.Lifecycle.ReceiveWithEvictionLoopResult state composite header dr ds np out pending half batch fuel
      (Except.ok r) →
    ∃ t0,
      Tacenta.UnitLifecycleOutOfOrderReceive.StoreShrunk state t0 ∧
        Model.Triple.receiveDetailed t0 header dr ds np out = Except.ok r
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleOutOfOrderReceive.loop_ok_shrunk

/--
info: @Tacenta.UnitLifecycleOutOfOrderReceive.receiveWithEviction_ok_shrunk : ∀ {t : Model.Triple.State}
  {composite : Model.CompositeHeader.Composite} {header : Model.Triple.Header} {dr ds np : Model.State.Key}
  {out : Option Model.SparseRatchet.Output} {r : Model.Triple.State × Model.State.Key},
  Model.Lifecycle.receiveWithEviction t composite header dr ds np out = Except.ok r →
    ∃ t0,
      Tacenta.UnitLifecycleOutOfOrderReceive.StoreShrunk t t0 ∧
        Model.Triple.receiveDetailed t0 header dr ds np out = Except.ok r
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleOutOfOrderReceive.receiveWithEviction_ok_shrunk

/--
info: @Tacenta.UnitLifecycleOutOfOrderReceive.triple_receive_split : ∀ {t t' : Model.Triple.State} {hdr : Model.Triple.Header}
  {dr ds np k : Model.State.Key} {out : Option Model.SparseRatchet.Output},
  Model.Triple.receiveDetailed t hdr dr ds np out = Except.ok (t', k) →
    (∃ k1, Model.Ratchet.receiveDetailed t.classical hdr.dr dr ds np = Except.ok (t'.classical, k1)) ∧
      ∃ k2, Model.SparseRatchet.receiveDetailed t.postQuantum hdr.epoch out hdr.pqN = Except.ok (t'.postQuantum, k2)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleOutOfOrderReceive.triple_receive_split

/--
info: @Tacenta.UnitLifecycleOutOfOrderReceive.advanced_chains : ∀ {st st1 : Model.SparseRatchet.State}
  {out : Option Model.SparseRatchet.Output},
  Tacenta.UnitLifecycleDecryptPreserve.advancedOf st out = some st1 →
    ∀ p ∈ st1.chains,
      ∀ (c : Model.SparseRatchet.Chain),
        Tacenta.UnitLifecycleEncryptPreserve.InChain p c →
          c.n = 0 ∨ ∃ p0 ∈ st.chains, Tacenta.UnitLifecycleEncryptPreserve.InChain p0 c
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleOutOfOrderReceive.advanced_chains

/--
info: @Tacenta.UnitLifecycleOutOfOrderReceive.triple_receive_any_frame : ∀ {t0 t' : Model.Triple.State}
  {hdr : Model.Triple.Header} {dr ds np k : Model.State.Key} {out : Option Model.SparseRatchet.Output},
  Tacenta.UnitTripleInvModel.ModelTripleInv t0 →
    Model.Triple.receiveDetailed t0 hdr dr ds np out = Except.ok (t', k) →
      t'.postQuantum.direction = t0.postQuantum.direction ∧
        (out = none → t'.postQuantum.epoch = t0.postQuantum.epoch) ∧
          (∀ (o : Model.SparseRatchet.Output),
              out = some o → t'.postQuantum.epoch = o.keyEpoch ∧ o.keyEpoch = t0.postQuantum.epoch + 1) ∧
            (t'.classical.dhsPub = t0.classical.dhsPub ∨ t'.classical.dhsPub = np) ∧
              t'.classical.events ≤ t0.classical.events + 1 ∧
                ∀ p ∈ t'.postQuantum.chains,
                  ∀ (c : Model.SparseRatchet.Chain),
                    Tacenta.UnitLifecycleEncryptPreserve.InChain p c →
                      c.n ≤ Model.SparseRatchet.maxSkip + 1 ∨
                        ∃ p0 ∈ t0.postQuantum.chains,
                          ∃ c0,
                            Tacenta.UnitLifecycleEncryptPreserve.InChain p0 c0 ∧
                              c.n ≤ c0.n + Model.SparseRatchet.maxSkip + 1
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleOutOfOrderReceive.triple_receive_any_frame

/--
info: @Tacenta.UnitLifecycleOutOfOrderReceive.triple_receive_any : ∀ {t0 t' : Model.Triple.State} {hdr : Model.Triple.Header}
  {dr ds np k : Model.State.Key} {out : Option Model.SparseRatchet.Output},
  Tacenta.UnitTripleInvModel.ModelTripleInv t0 →
    Model.Messages.canonicalKey hdr.dr.dh = true →
      Model.Messages.canonicalKey t'.classical.dhsPub = true →
        Model.Triple.receiveDetailed t0 hdr dr ds np out = Except.ok (t', k) →
          Tacenta.UnitTripleInvModel.ModelTripleInv t'
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleOutOfOrderReceive.triple_receive_any

/--
info: @Tacenta.UnitLifecycleOutOfOrderReceive.modelTripleInv_shrunk : ∀ {t t0 : Model.Triple.State},
  Tacenta.UnitTripleInvModel.ModelTripleInv t →
    Tacenta.UnitLifecycleOutOfOrderReceive.StoreShrunk t t0 → Tacenta.UnitTripleInvModel.ModelTripleInv t0
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleOutOfOrderReceive.modelTripleInv_shrunk

/--
info: Tacenta.UnitLifecycleOutOfOrderReceive.decryptRatchet_receiveStepAny : ∀ (view : Model.Lifecycle.CodewordView)
  (oracle : Model.Lifecycle.Oracle) (m : Model.Lifecycle.Session) (msg : Model.Lifecycle.Bytes),
  Tacenta.UnitLifecycleOutOfOrderReceive.ReceiveStepAny oracle m
    (Model.Lifecycle.decryptRatchet view oracle m msg).session
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleOutOfOrderReceive.decryptRatchet_receiveStepAny

/--
info: Tacenta.UnitLifecycleOutOfOrderReceive.decrypt_receiveStepAny : ∀ (view : Model.Lifecycle.CodewordView)
  (oracle : Model.Lifecycle.Oracle) (m : Model.Lifecycle.Session) (msg inner : Model.Lifecycle.Bytes),
  Model.Lifecycle.dispatchDecrypt oracle m msg = Except.ok inner →
    Tacenta.UnitLifecycleOutOfOrderReceive.ReceiveStepAny oracle m (Model.Lifecycle.decrypt view oracle m msg).session
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleOutOfOrderReceive.decrypt_receiveStepAny

/--
info: @Tacenta.UnitLifecycleOutOfOrderReceive.receiveStepAny_parts : ∀ {oracle : Model.Lifecycle.Oracle}
  {m m' : Model.Lifecycle.Session} {msgB : Model.Braid.Msg} {c : Model.CompositeHeader.Composite}
  {hdr : Model.Triple.Header} {dr ds cand mk : Model.State.Key},
  Model.Lifecycle.receiveWithEviction m.triple c hdr dr ds (oracle.dhPublic cand)
        (Model.Lifecycle.sparseOutputOf (Model.Braid.receive oracle.braidKem m.braid msgB).2.1) =
      Except.ok (m'.triple, mk) →
    ∃ t0,
      Tacenta.UnitLifecycleOutOfOrderReceive.StoreShrunk m.triple t0 ∧
        Model.Triple.receiveDetailed t0 hdr dr ds (oracle.dhPublic cand)
            (Model.Lifecycle.sparseOutputOf (Model.Braid.receive oracle.braidKem m.braid msgB).2.1) =
          Except.ok (m'.triple, mk)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleOutOfOrderReceive.receiveStepAny_parts

/--
info: Tacenta.UnitLifecycleOutOfOrderReceive.modelTripleInv_stepAny : ∀ (oracle : Model.Lifecycle.Oracle)
  {m m' : Model.Lifecycle.Session},
  Tacenta.UnitLifecycleOutOfOrderReceive.ReceiveStepAny oracle m m' →
    Tacenta.UnitTripleInvModel.ModelTripleInv m.triple →
      Model.Messages.canonicalKey m'.triple.classical.dhsPub = true →
        Tacenta.UnitTripleInvModel.ModelTripleInv m'.triple
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleOutOfOrderReceive.modelTripleInv_stepAny

/--
info: Tacenta.UnitLifecycleOutOfOrderReceive.modelCounterRoom_stepAny : ∀ (oracle : Model.Lifecycle.Oracle)
  {m m' : Model.Lifecycle.Session} (k : ℕ),
  Tacenta.UnitLifecycleOutOfOrderReceive.ReceiveStepAny oracle m m' →
    Tacenta.UnitTripleInvModel.ModelTripleInv m.triple →
      Tacenta.UnitLifecycleSendPreserve.ModelCounterRoom m (k + 1) →
        Tacenta.UnitLifecycleSendPreserve.ModelCounterRoom m' k
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleOutOfOrderReceive.modelCounterRoom_stepAny

/--
info: Tacenta.UnitLifecycleOutOfOrderReceive.step_frame_stepAny : ∀ (oracle : Model.Lifecycle.Oracle)
  {m m' : Model.Lifecycle.Session},
  Tacenta.UnitLifecycleOutOfOrderReceive.ReceiveStepAny oracle m m' →
    Tacenta.UnitTripleInvModel.ModelTripleInv m.triple →
      Tacenta.UnitLifecycleDecryptPreserve.ModelClauseB m.triple.postQuantum.epoch m.braid →
        m'.triple.postQuantum.direction = m.triple.postQuantum.direction ∧
          (m'.triple.classical.dhsPub ≠ m.triple.classical.dhsPub →
              m'.triple.classical.dhsPub = oracle.dhPublic m'.ratchetPrivate) ∧
            Tacenta.UnitLifecycleDecryptPreserve.ModelClauseB m'.triple.postQuantum.epoch m'.braid ∧
              (m'.braid = Model.Braid.BraidState.failed ∨
                Tacenta.UnitLifecycleDecryptPreserve.modelIsInit m'.braid =
                  Tacenta.UnitLifecycleDecryptPreserve.modelIsInit m.braid)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleOutOfOrderReceive.step_frame_stepAny

/--
info: @Tacenta.UnitLifecycleOutOfOrderReceive.skip_stored : ∀ {st st' : Model.State.State} {upto : ℕ},
  Model.State.skipMessageKeys st upto = some st' →
    ∀ e ∈ st'.skipped, e ∈ st.skipped ∨ st.dhrPub = some e.1 ∧ st.nr ≤ e.2.1 ∧ e.2.1 < upto
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleOutOfOrderReceive.skip_stored

/--
info: @Tacenta.UnitLifecycleOutOfOrderReceive.ratchet_receive_consumes : ∀ {st st' : Model.State.State}
  {hdr : Model.State.Header} {dr ds np mk : Model.State.Key},
  Model.Ratchet.receiveDetailed st hdr dr ds np = Except.ok (st', mk) →
    ∀ e ∈ st'.skipped, ¬(e.1 = hdr.dh ∧ e.2.1 = hdr.n)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleOutOfOrderReceive.ratchet_receive_consumes

/--
info: @Tacenta.UnitLifecycleOutOfOrderReceive.spqr_skip_stored : ∀ {st st' : Model.SparseRatchet.State} {ep upto : ℕ},
  Model.SparseRatchet.skipMessageKeys st ep upto = some st' →
    ∀ x ∈ st'.skipped, x ∈ st.skipped ∨ x.1 = ep ∧ 0 < x.2.1 ∧ x.2.1 ≤ upto
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleOutOfOrderReceive.spqr_skip_stored

/--
info: @Tacenta.UnitLifecycleOutOfOrderReceive.spqr_receive_consumes : ∀ {st st' : Model.SparseRatchet.State} {ep n : ℕ}
  {mk : Model.State.Key},
  Model.SparseRatchet.receiveDetailed st ep none n = Except.ok (st', mk) → ∀ x ∈ st'.skipped, ¬(x.1 = ep ∧ x.2.1 = n)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleOutOfOrderReceive.spqr_receive_consumes

/--
info: @Tacenta.UnitLifecycleOutOfOrderReceive.triple_receive_consumes : ∀ {t0 t' : Model.Triple.State}
  {hdr : Model.Triple.Header} {dr ds np k : Model.State.Key} {out : Option Model.SparseRatchet.Output},
  Model.Triple.receiveDetailed t0 hdr dr ds np out = Except.ok (t', k) →
    (∀ e ∈ t'.classical.skipped, ¬(e.1 = hdr.dr.dh ∧ e.2.1 = hdr.dr.n)) ∧
      ∀ x ∈ t'.postQuantum.skipped, ¬(x.1 = hdr.epoch ∧ x.2.1 = hdr.pqN)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleOutOfOrderReceive.triple_receive_consumes

/--
info: Tacenta.UnitLifecycleOutOfOrderReceive.decryptRatchet_consumes : ∀ (view : Model.Lifecycle.CodewordView)
  (oracle : Model.Lifecycle.Oracle) (m : Model.Lifecycle.Session) (msg : Model.Lifecycle.Bytes)
  (c : Model.CompositeHeader.Composite) (ct : Model.Lifecycle.Bytes),
  Model.CompositeHeader.decodeDetailed msg = Except.ok (c, ct) →
    ∀ (pt : Model.Lifecycle.Bytes),
      (Model.Lifecycle.decryptRatchet view oracle m msg).result = Except.ok pt →
        (∀ e ∈ (Model.Lifecycle.decryptRatchet view oracle m msg).session.triple.classical.skipped,
            ¬(e.1 = c.dh ∧ e.2.1 = c.n.toNat)) ∧
          ∀ x ∈ (Model.Lifecycle.decryptRatchet view oracle m msg).session.triple.postQuantum.skipped,
            ¬(x.1 = c.pqEpoch.toNat ∧ x.2.1 = c.pqN.toNat)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleOutOfOrderReceive.decryptRatchet_consumes

/--
info: Tacenta.UnitLifecycleOutOfOrderReceive.decrypt_ratchet_keeps_invariant_any : Tacenta.UnitLifecycleDecryptPreserve.ReceiveInvariantLaws →
  ∀ {R : Type} (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R) (dh : Tacenta.UnitLifecycleT3.DhView),
    Tacenta.UnitLifecycleT3.DhCodecOf dh →
      ∀ (K : Model.Braid.Kem) (oracle : Model.Lifecycle.Oracle),
        (∀ (secret : tacenta_boundary.dh.PrivateKey),
            ∃ publicKey,
              secret.public_key = ok publicKey ∧ dh.publicKey publicKey = oracle.dhPublic (dh.privateKey secret)) →
          ∀ (s : lifecycle.Session) (m m' : Model.Lifecycle.Session) (k : ℕ),
            s.invariant = ok true →
              Tacenta.UnitLifecycleSendPreserve.CounterRoom s (k + 1) →
                Tacenta.UnitLifecycleT3.SessionRefines dh K s m →
                  ∀ (msg : Slice U8) (rng : R) (pt : alloc.vec.Vec U8) (s' : lifecycle.Session) (rng' : R),
                    lifecycle.Session.decrypt_ratchet rc crc s msg rng = ok (core.result.Result.Ok pt, s', rng') →
                      Tacenta.UnitLifecycleT3.SessionRefines dh K s' m' →
                        Tacenta.UnitLifecycleOutOfOrderReceive.ReceiveStepAny oracle m m' →
                          s'.invariant = ok true ∧ Tacenta.UnitLifecycleSendPreserve.CounterRoom s' k
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleOutOfOrderReceive.decrypt_ratchet_keeps_invariant_any

/--
info: Tacenta.UnitLifecycleOutOfOrderReceive.decrypt_keeps_invariant_any : Tacenta.UnitLifecycleDecryptPreserve.ReceiveInvariantLaws →
  ∀ {R : Type} (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R) (dh : Tacenta.UnitLifecycleT3.DhView),
    Tacenta.UnitLifecycleT3.DhCodecOf dh →
      ∀ (K : Model.Braid.Kem) (oracle : Model.Lifecycle.Oracle),
        (∀ (secret : tacenta_boundary.dh.PrivateKey),
            ∃ publicKey,
              secret.public_key = ok publicKey ∧ dh.publicKey publicKey = oracle.dhPublic (dh.privateKey secret)) →
          ∀ (s : lifecycle.Session) (m m' : Model.Lifecycle.Session) (k : ℕ),
            s.invariant = ok true →
              Tacenta.UnitLifecycleSendPreserve.CounterRoom s (k + 1) →
                Tacenta.UnitLifecycleT3.SessionRefines dh K s m →
                  ∀ (msg : Slice U8) (rng : R) (pt : alloc.vec.Vec U8) (s' : lifecycle.Session) (rng' : R),
                    lifecycle.Session.decrypt rc crc s msg rng = ok (core.result.Result.Ok pt, s', rng') →
                      Tacenta.UnitLifecycleT3.SessionRefines dh K s' m' →
                        Tacenta.UnitLifecycleOutOfOrderReceive.ReceiveStepAny oracle m m' →
                          s'.invariant = ok true ∧ Tacenta.UnitLifecycleSendPreserve.CounterRoom s' k
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleOutOfOrderReceive.decrypt_keeps_invariant_any

/--
info: Tacenta.UnitLifecycleOutOfOrderReceive.decrypt_ratchet_refines_keeps_invariant_any : Tacenta.UnitLifecycleDecryptPreserve.ReceiveInvariantLaws →
  ∀ {R : Type} (rngCore : rand_core_1.RngCore R) (cryptoRng : rand_core_1.CryptoRng R)
    (trace : R → List Model.Lifecycle.Key) (dh : Tacenta.UnitLifecycleT3.DhView) (view : Model.Lifecycle.CodewordView)
    (oracle : Model.Lifecycle.Oracle),
    Tacenta.UnitLifecycleDecryptRatchetT3.DecryptOracleOf rngCore cryptoRng dh trace oracle →
      Tacenta.UnitLifecycleT3.DhCodecOf dh →
        Tacenta.UnitLifecycleT1.DecryptRatchetContracts rngCore →
          ∀ [Tacenta.SessionUnitT1.DerivedKeysModel],
            Tacenta.UnitLifecycleDecryptRatchetT3.DecryptRatchetAgreements oracle.braidKem →
              ∀ (s : lifecycle.Session) (m : Model.Lifecycle.Session) (message : Slice U8) (rng : R) (k : ℕ),
                s.invariant = ok true →
                  Tacenta.UnitLifecycleT3.SessionRefines dh oracle.braidKem s m →
                    Tacenta.UnitLifecycleSendPreserve.CounterRoom s (k + 1) →
                      trace rng = oracle.draws →
                        Tacenta.UnitLifecycleDecryptRunBounds.DecryptRatchetRunInputs view oracle trace s m message
                            rng →
                          ∃ output,
                            lifecycle.Session.decrypt_ratchet rngCore cryptoRng s message rng = ok output ∧
                              Tacenta.UnitLifecycleT3.StepRefines trace dh oracle.braidKem output
                                  (Model.Lifecycle.decryptRatchet view oracle m
                                    (Tacenta.UnitLifecycleT3.sliceOf message)) ∧
                                output.2.1.invariant = ok true ∧
                                  Tacenta.UnitLifecycleSendPreserve.CounterRoom output.2.1 k
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleOutOfOrderReceive.decrypt_ratchet_refines_keeps_invariant_any

/--
info: Tacenta.UnitLifecycleOutOfOrderReceive.decrypt_ratchet_refines_consumes_any : Tacenta.UnitLifecycleDecryptPreserve.ReceiveInvariantLaws →
  ∀ {R : Type} (rngCore : rand_core_1.RngCore R) (cryptoRng : rand_core_1.CryptoRng R)
    (trace : R → List Model.Lifecycle.Key) (dh : Tacenta.UnitLifecycleT3.DhView) (view : Model.Lifecycle.CodewordView)
    (oracle : Model.Lifecycle.Oracle),
    Tacenta.UnitLifecycleDecryptRatchetT3.DecryptOracleOf rngCore cryptoRng dh trace oracle →
      Tacenta.UnitLifecycleT3.DhCodecOf dh →
        Tacenta.UnitLifecycleT1.DecryptRatchetContracts rngCore →
          ∀ [Tacenta.SessionUnitT1.DerivedKeysModel],
            Tacenta.UnitLifecycleDecryptRatchetT3.DecryptRatchetAgreements oracle.braidKem →
              ∀ (s : lifecycle.Session) (m : Model.Lifecycle.Session) (message : Slice U8) (rng : R) (k : ℕ),
                s.invariant = ok true →
                  Tacenta.UnitLifecycleT3.SessionRefines dh oracle.braidKem s m →
                    Tacenta.UnitLifecycleSendPreserve.CounterRoom s (k + 1) →
                      trace rng = oracle.draws →
                        Tacenta.UnitLifecycleDecryptRunBounds.DecryptRatchetRunInputs view oracle trace s m message
                            rng →
                          ∀ (c : Model.CompositeHeader.Composite) (ct : Model.Lifecycle.Bytes),
                            Model.CompositeHeader.decodeDetailed (Tacenta.UnitLifecycleT3.sliceOf message) =
                                Except.ok (c, ct) →
                              ∃ output,
                                lifecycle.Session.decrypt_ratchet rngCore cryptoRng s message rng = ok output ∧
                                  Tacenta.UnitLifecycleT3.StepRefines trace dh oracle.braidKem output
                                      (Model.Lifecycle.decryptRatchet view oracle m
                                        (Tacenta.UnitLifecycleT3.sliceOf message)) ∧
                                    output.2.1.invariant = ok true ∧
                                      Tacenta.UnitLifecycleSendPreserve.CounterRoom output.2.1 k ∧
                                        ∀ (pt : alloc.vec.Vec U8),
                                          output.1 = core.result.Result.Ok pt →
                                            (∀
                                                e ∈
                                                  (Tacenta.SessionUnitTripleT3.ratchetAbs
                                                      output.2.1.triple.classical).skipped,
                                                ¬(e.1 = c.dh ∧ e.2.1 = c.n.toNat)) ∧
                                              ∀
                                                x ∈
                                                  (Tacenta.SessionUnitTripleT3.spqrAbs
                                                      output.2.1.triple.post_quantum).skipped,
                                                ¬(x.1 = c.pqEpoch.toNat ∧ x.2.1 = c.pqN.toNat)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleOutOfOrderReceive.decrypt_ratchet_refines_consumes_any

/--
info: Tacenta.UnitLifecycleOutOfOrderReceive.decrypt_refines_keeps_invariant_any : Tacenta.UnitLifecycleDecryptPreserve.ReceiveInvariantLaws →
  ∀ {R : Type} (rngCore : rand_core_1.RngCore R) (cryptoRng : rand_core_1.CryptoRng R)
    (trace : R → List Model.Lifecycle.Key) (dh : Tacenta.UnitLifecycleT3.DhView) (view : Model.Lifecycle.CodewordView)
    (oracle : Model.Lifecycle.Oracle),
    Tacenta.UnitLifecycleDecryptRatchetT3.DecryptOracleOf rngCore cryptoRng dh trace oracle →
      Tacenta.UnitLifecycleT3.DhCodecOf dh →
        Tacenta.UnitLifecycleT1.DecryptRatchetContracts rngCore →
          ∀ [Tacenta.SessionUnitT1.DerivedKeysModel],
            Tacenta.UnitLifecycleDecryptRatchetT3.DecryptRatchetAgreements oracle.braidKem →
              ∀ (s : lifecycle.Session) (m : Model.Lifecycle.Session) (message : Slice U8) (rng : R) (k : ℕ),
                s.invariant = ok true →
                  Tacenta.UnitLifecycleT3.SessionRefines dh oracle.braidKem s m →
                    Tacenta.UnitLifecycleSendPreserve.CounterRoom s (k + 1) →
                      serialization.message_type message = ok (some serialization.MessageType.Ratchet) →
                        trace rng = oracle.draws →
                          Tacenta.UnitLifecycleDecryptRunBounds.DecryptRatchetRunInputs view oracle trace s m message
                              rng →
                            ∃ output,
                              lifecycle.Session.decrypt rngCore cryptoRng s message rng = ok output ∧
                                Tacenta.UnitLifecycleT3.StepRefines trace dh oracle.braidKem output
                                    (Model.Lifecycle.decrypt view oracle m (Tacenta.UnitLifecycleT3.sliceOf message)) ∧
                                  output.2.1.invariant = ok true ∧
                                    Tacenta.UnitLifecycleSendPreserve.CounterRoom output.2.1 k
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleOutOfOrderReceive.decrypt_refines_keeps_invariant_any

/--
info: Tacenta.UnitLifecycleOutOfOrderReceive.restored_decrypt_keeps_invariant_any : Tacenta.UnitLifecycleDecryptPreserve.ReceiveInvariantLaws →
  ∀ {R : Type} (rngCore : rand_core_1.RngCore R) (cryptoRng : rand_core_1.CryptoRng R)
    (trace : R → List Model.Lifecycle.Key) (dh : Tacenta.UnitLifecycleT3.DhView) (view : Model.Lifecycle.CodewordView)
    (oracle : Model.Lifecycle.Oracle),
    Tacenta.UnitLifecycleDecryptRatchetT3.DecryptOracleOf rngCore cryptoRng dh trace oracle →
      Tacenta.UnitLifecycleT3.DhCodecOf dh →
        Tacenta.UnitLifecycleT1.DecryptRatchetContracts rngCore →
          ∀ [Tacenta.SessionUnitT1.DerivedKeysModel],
            Tacenta.UnitLifecycleDecryptRatchetT3.DecryptRatchetAgreements oracle.braidKem →
              ∀ (bytes : Slice U8) (s : lifecycle.Session) (k : ℕ),
                lifecycle.Session.import bytes = ok (core.result.Result.Ok s) →
                  Tacenta.UnitLifecycleRestoredSession.RestoredScope s →
                    Tacenta.UnitLifecycleImportBudget.roomCheck s (k + 1) = true →
                      ∀ (message : Slice U8) (rng : R),
                        serialization.message_type message = ok (some serialization.MessageType.Ratchet) →
                          trace rng = oracle.draws →
                            (∀ (realComposite : tacenta_wire.Composite)
                                (modelComposite : Model.CompositeHeader.Composite) (ciphertext : Model.Lifecycle.Bytes),
                                Model.CompositeHeader.decodeDetailed (Tacenta.UnitLifecycleT3.sliceOf message) =
                                    Except.ok (modelComposite, ciphertext) →
                                  Tacenta.UnitLifecycleT3.CompositeRefines realComposite modelComposite →
                                    Tacenta.UnitLifecycleT3.IncomingChunkRefines view
                                      (Tacenta.UnitLifecycleRestoredSession.restoredModelOf dh s).braid realComposite
                                      modelComposite) →
                              (∃ draw rest, trace rng = draw :: rest) →
                                ∃ output,
                                  lifecycle.Session.decrypt rngCore cryptoRng s message rng = ok output ∧
                                    Tacenta.UnitLifecycleT3.StepRefines trace dh oracle.braidKem output
                                        (Model.Lifecycle.decrypt view oracle
                                          (Tacenta.UnitLifecycleRestoredSession.restoredModelOf dh s)
                                          (Tacenta.UnitLifecycleT3.sliceOf message)) ∧
                                      output.2.1.invariant = ok true ∧
                                        Tacenta.UnitLifecycleSendPreserve.CounterRoom output.2.1 k
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleOutOfOrderReceive.restored_decrypt_keeps_invariant_any

/--
info: def Tacenta.UnitLifecycleOutOfOrderReceive.SteppedTo : Model.State.State →
  Model.State.Header → Model.State.Key → Model.State.Key → Model.State.Key → Model.State.State → Prop :=
fun st hdr dr ds np st1 =>
  st.dhrPub = some hdr.dh ∧ st1 = st ∨
    st.dhrPub ≠ some hdr.dh ∧
      ∃ sk, Model.State.skipMessageKeys st hdr.pn = some sk ∧ st1 = Model.Ratchet.dhRatchet sk hdr dr ds np
-/
#guard_msgs in
#print Tacenta.UnitLifecycleOutOfOrderReceive.SteppedTo

/--
info: def Tacenta.UnitLifecycleOutOfOrderReceive.StoreShrunk : Model.Triple.State → Model.Triple.State → Prop :=
fun t t0 =>
  t0 =
      {
        classical :=
          have __src := t.classical;
          { dhsPub := __src.dhsPub, dhrPub := __src.dhrPub, rk := __src.rk, cks := __src.cks, ckr := __src.ckr,
            ns := __src.ns, nr := __src.nr, pn := __src.pn, skipped := t0.classical.skipped, events := __src.events,
            labels := __src.labels },
        postQuantum :=
          have __src := t.postQuantum;
          { rk := __src.rk, epoch := __src.epoch, chains := __src.chains, skipped := t0.postQuantum.skipped,
            direction := __src.direction } } ∧
    t0.classical.skipped.Sublist t.classical.skipped ∧ t0.postQuantum.skipped.Sublist t.postQuantum.skipped
-/
#guard_msgs in
#print Tacenta.UnitLifecycleOutOfOrderReceive.StoreShrunk

/--
info: def Tacenta.UnitLifecycleOutOfOrderReceive.ReceiveStepAny : Model.Lifecycle.Oracle →
  Model.Lifecycle.Session → Model.Lifecycle.Session → Prop :=
fun oracle m m' =>
  m'.triple = m.triple ∧ m'.ratchetPrivate = m.ratchetPrivate ∧ m'.braid = m.braid ∨
    ∃ msgB c hdr dr ds cand mk,
      m'.braid = (Model.Braid.receive oracle.braidKem m.braid msgB).2.2 ∧
        Model.Messages.canonicalKey hdr.dr.dh = true ∧
          Model.Lifecycle.receiveWithEviction m.triple c hdr dr ds (oracle.dhPublic cand)
                (Model.Lifecycle.sparseOutputOf (Model.Braid.receive oracle.braidKem m.braid msgB).2.1) =
              Except.ok (m'.triple, mk) ∧
            m'.ratchetPrivate =
              if (m'.triple.classical.dhsPub == m.triple.classical.dhsPub) = true then m.ratchetPrivate else cand
-/
#guard_msgs in
#print Tacenta.UnitLifecycleOutOfOrderReceive.ReceiveStepAny
