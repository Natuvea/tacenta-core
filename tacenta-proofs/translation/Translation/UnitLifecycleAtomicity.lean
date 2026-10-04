import Translation.TacentaSessionUnit

/-!
# What a refused lifecycle call leaves behind

`Session::encrypt`, `Session::decrypt`, `decrypt_ratchet` and `establish_responder`, as the
Session unit translates them, return the state they were given on every refusal (with one
recorded exception in `encrypt`), and change a named set of fields on success. The results here
are about the translated bodies and take **no hypothesis about any opaque operation**: the
cryptographic primitives, the random source, the key types and the standard-library calls are
free in every statement, so each result holds for every interpretation of them. That is the
point of the module. The lifecycle T3 branch lemmas take evidence records and `OracleOf`, which
are hypotheses about the opaque operations that nothing in this tree shows hold of the shipped
primitives; a statement that quantifies over the opaque constants and assumes nothing about them
is not made empty by such a hypothesis.

What a statement here says is about a call that returns normally. Each is of the form "if the
call is `ok (result, state', rng')` and the result is a refusal, then `state'` is the input
state". A call that fails (a panic in the translation's sense) or does not terminate has no
such result, and `UnitLifecyclePublicT1.lean` (T1, conditional on its contract and headroom
records) is what says the calls return. Nothing here relates a result to the model
(`Model.Lifecycle`): that is T3, which this module is not.

What is not said:

* The random source. A refused call can still have drawn from it; `rng'` is unconstrained.
* Heap residue. The translation ignores `Drop` and `zeroize`, so what a discarded candidate
  state leaves in memory is outside it.
* That a refusal is reachable. The statements are true of a body that never refuses. The terminal
  refusals are shown at the end of the module, for every session whose agreement reports failed,
  without exhibiting a session; no other arm is shown reached. That the walk below is sensitive to
  a write before a refusal is held by `scripts/check-atomicity-negatives.py`, which plants such a
  write in a copy of each body and requires the same proof to fail, and the Rust tests that refuse a
  message and compare the exported state are the evidence for the other arms.
* The Session unit is assembled from the shipping lifecycle leaf by `#[path]` and a count-checked
  copy (`scripts/assemble-session-unit.sh`); these results are about that unit's translation.

The method is one walk over the translated `do` block. `Post` is a postcondition on the pair of
result and returned state; `Post.bind` and `Post.leaf` are the two steps, and `split` handles
the `match` and `if`. A bind whose first part is `decrypt_ratchet` is the one place the walk
needs a fact about a callee, which the result for `decrypt_ratchet` supplies.
-/

namespace Tacenta.UnitLifecycleAtomicity

open Aeneas Aeneas.Std Result
open tacenta_session_unit

theorem bind_eq_ok_iff {α β : Type} {x : Result α} {f : α → Result β} {y : β} :
    (x >>= f) = ok y ↔ ∃ a, x = ok a ∧ f a = ok y := by
  cases x <;> simp

/-- `Post Q f`: whenever the call `f` returns normally with result `r` and state `s'`, `Q r s'`. -/
def Post {α E S R : Type} (Q : core.result.Result α E → S → Prop)
    (f : Result (core.result.Result α E × S × R)) : Prop :=
  ∀ r s' rng', f = ok (r, s', rng') → Q r s'

theorem Post.bind {α E S R A : Type} {Q : core.result.Result α E → S → Prop}
    {x : Result A} {k : A → Result (core.result.Result α E × S × R)}
    (h : ∀ a, x = ok a → Post Q (k a)) : Post Q (x >>= k) := by
  intro r s' rng' hx
  obtain ⟨a, ha, hk⟩ := bind_eq_ok_iff.mp hx
  exact h a ha r s' rng' hk

theorem Post.leaf {α E S R : Type} {Q : core.result.Result α E → S → Prop}
    {r : core.result.Result α E} {s : S} {rng : R} (h : Q r s) :
    Post Q (ok (r, s, rng) : Result (core.result.Result α E × S × R)) := by
  intro r' s' rng' hx
  simp at hx
  obtain ⟨rfl, rfl, rfl⟩ := hx
  exact h

/-! ## The walk

Every proof below is the same walk over a translated `do` block: `Post.bind` takes a bind (the
bound value and the equation that it came from the call are introduced and not used), `split` takes
a `match` or an `if`, and a leaf is a returned `ok (result, state, rng)`. A leaf is closed by
`rfl` (the state is the given one, or the planted field list is the stated one) or by the
impossibility of the result being the other constructor. The walk is spelled out in each proof and
not as a tactic macro, because `check-lean-constructs.sh` refuses elaboration-time code in this
package; `scripts/check-atomicity-negatives.py` reads the four proof texts back from this file and
applies them to changed copies of the generated bodies. -/

/-- The postcondition of `decrypt_ratchet` and of `decrypt` is two-sided: on a refusal the state
returned is the state given; on success it differs from it in at most the named fields. -/
abbrev RatchetFrame (self : lifecycle.Session) :
    core.result.Result (alloc.vec.Vec U8) lifecycle.Error → lifecycle.Session → Prop :=
  fun r s' =>
    (∀ e, r = core.result.Result.Err e → s' = self) ∧
    (∀ v, r = core.result.Result.Ok v →
      s' = { self with triple := s'.triple, braid := s'.braid,
                       ratchet_private := s'.ratchet_private })

abbrev DecryptFrame (self : lifecycle.Session) :
    core.result.Result (alloc.vec.Vec U8) lifecycle.Error → lifecycle.Session → Prop :=
  fun r s' =>
    (∀ e, r = core.result.Result.Err e → s' = self) ∧
    (∀ v, r = core.result.Result.Ok v →
      s' = { self with triple := s'.triple, braid := s'.braid,
                       ratchet_private := s'.ratchet_private, pending_initial := none })

abbrev ResponderFrame (store : lifecycle.PrekeyStore) :
    core.result.Result (lifecycle.Session × alloc.vec.Vec U8) lifecycle.Error →
      lifecycle.PrekeyStore → Prop :=
  fun r s' => ∀ e, r = core.result.Result.Err e → s' = store

/-- The agreement exception of `encrypt`: the one refusal that writes. When the agreement's send
reaches its terminal state, the call commits that state so every later call refuses too
(`triple-ratchet.md`, the paragraph on an agreement send that enters `Failed`). -/
abbrev EncryptFrame (self : lifecycle.Session) :
    core.result.Result (alloc.vec.Vec U8) lifecycle.Error → lifecycle.Session → Prop :=
  fun r s' =>
    (∀ e, r = core.result.Result.Err e →
      s' = self ∨ (e = lifecycle.Error.AgreementFailed ∧
        ∃ b, s' = { self with braid := b } ∧ tacenta_braid.Braid.failed b = ok true)) ∧
    (∀ v, r = core.result.Result.Ok v →
      s' = { self with triple := s'.triple, braid := s'.braid })

/-! ## `decrypt_ratchet` -/

theorem decrypt_ratchet_frame {R : Type}
    (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R)
    (self : lifecycle.Session) (message : Slice U8) (rng : R) :
    Post (RatchetFrame self) (lifecycle.Session.decrypt_ratchet rc crc self message rng) := by
  unfold lifecycle.Session.decrypt_ratchet
  repeat' first
    | (apply Post.bind; intro _ _)
    | split
    | (apply Post.leaf
       refine ⟨fun e he => ?_, fun v hv => ?_⟩ <;> first | rfl | (cases he))

/-- A refused `decrypt_ratchet` returns the session it was given, field for field. Every write
to `self` in the body sits after the AEAD check. -/
theorem decrypt_ratchet_err_leaves_state {R : Type}
    (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R)
    (self : lifecycle.Session) (message : Slice U8) (rng : R)
    (e : lifecycle.Error) (self' : lifecycle.Session) (rng' : R)
    (h : lifecycle.Session.decrypt_ratchet rc crc self message rng =
      ok (core.result.Result.Err e, self', rng')) :
    self' = self :=
  (decrypt_ratchet_frame rc crc self message rng _ _ _ h).1 e rfl

/-- A successful `decrypt_ratchet` writes the Triple Ratchet, the agreement and the ratchet
private key, and nothing else: the associated data, both identities, the pending initial message
and the established ephemeral are the ones it was given. -/
theorem decrypt_ratchet_ok_writes {R : Type}
    (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R)
    (self : lifecycle.Session) (message : Slice U8) (rng : R)
    (v : alloc.vec.Vec U8) (self' : lifecycle.Session) (rng' : R)
    (h : lifecycle.Session.decrypt_ratchet rc crc self message rng =
      ok (core.result.Result.Ok v, self', rng')) :
    self' = { self with triple := self'.triple, braid := self'.braid,
                        ratchet_private := self'.ratchet_private } :=
  (decrypt_ratchet_frame rc crc self message rng _ _ _ h).2 v rfl

/-! ## `decrypt` -/

/-- A bind whose first part is a call with a known postcondition: the continuation may use it. -/
theorem Post.bind_call {α E S R A : Type} {Q : core.result.Result α E → S → Prop}
    {P : core.result.Result A E → S → Prop}
    {x : Result (core.result.Result A E × S × R)} (hx : Post P x)
    {k : (core.result.Result A E × S × R) → Result (core.result.Result α E × S × R)}
    (h : ∀ r s1 rng1, x = ok (r, s1, rng1) → P r s1 → Post Q (k (r, s1, rng1))) :
    Post Q (x >>= k) := by
  apply Post.bind
  rintro ⟨r, s1, rng1⟩ ha
  exact h r s1 rng1 ha (hx r s1 rng1 ha)

/-- The success arm of `decrypt`: the state `decrypt_ratchet` returned, with `pending_initial`
cleared, differs from the given state in the named fields only. -/
theorem decrypt_ok_arm (self s1 : lifecycle.Session)
    (hw : s1 = { self with triple := s1.triple, braid := s1.braid,
                           ratchet_private := s1.ratchet_private }) :
    { s1 with pending_initial := none } =
      { self with triple := s1.triple, braid := s1.braid,
                  ratchet_private := s1.ratchet_private, pending_initial := none } := by
  have h1 := congrArg lifecycle.Session.identity_ad hw
  have h2 := congrArg lifecycle.Session.our_identity_public hw
  have h3 := congrArg lifecycle.Session.peer_identity_public hw
  have h4 := congrArg lifecycle.Session.established_ephemeral hw
  simp only [] at h1 h2 h3 h4
  rw [h1, h2, h3, h4]

theorem decrypt_frame {R : Type}
    (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R)
    (self : lifecycle.Session) (message : Slice U8) (rng : R) :
    Post (DecryptFrame self) (lifecycle.Session.decrypt rc crc self message rng) := by
  unfold lifecycle.Session.decrypt
  repeat' first
    | dsimp only
    | (refine Post.bind_call (decrypt_ratchet_frame _ _ _ _ _) ?_
       intro r s1 rng1 hx hr
       try dsimp only
       rcases r with v | e
       · apply Post.bind; intro cf hcf
         simp [core.result.Result.Insts.CoreOpsTry.branch] at hcf
         subst hcf
         apply Post.leaf
         refine ⟨fun e he => (by cases he), fun v' hv' => ?_⟩
         exact decrypt_ok_arm _ _ (hr.2 v rfl)
       · have h1 := hr.1 e rfl
         subst h1
         apply Post.bind; intro cf hcf
         simp [core.result.Result.Insts.CoreOpsTry.branch] at hcf
         subst hcf
         apply Post.bind; intro r1 hr1
         simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
           at hr1
         subst hr1
         apply Post.leaf
         refine ⟨fun e he => ?_, fun v hv => ?_⟩ <;> first | rfl | (cases he) | (cases hv))
    | (apply Post.bind; intro _ _)
    | split
    | (apply Post.leaf
       refine ⟨fun e he => ?_, fun v hv => ?_⟩ <;> first | rfl | (cases he) | (cases hv))

/-- A refused `decrypt` returns the session it was given, field for field: the initial-message
dispatch, the repeat recognition and the inner receive all refuse without a write, and the one
write after the inner receive (`pending_initial := none`) is on the success path only. -/
theorem decrypt_err_leaves_state {R : Type}
    (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R)
    (self : lifecycle.Session) (message : Slice U8) (rng : R)
    (e : lifecycle.Error) (self' : lifecycle.Session) (rng' : R)
    (h : lifecycle.Session.decrypt rc crc self message rng =
      ok (core.result.Result.Err e, self', rng')) :
    self' = self :=
  (decrypt_frame rc crc self message rng _ _ _ h).1 e rfl

/-- A successful `decrypt` writes the Triple Ratchet, the agreement and the ratchet private key,
and clears the pending initial message; the associated data, both identities and the established
ephemeral are the ones it was given. -/
theorem decrypt_ok_writes {R : Type}
    (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R)
    (self : lifecycle.Session) (message : Slice U8) (rng : R)
    (v : alloc.vec.Vec U8) (self' : lifecycle.Session) (rng' : R)
    (h : lifecycle.Session.decrypt rc crc self message rng =
      ok (core.result.Result.Ok v, self', rng')) :
    self' = { self with triple := self'.triple, braid := self'.braid,
                        ratchet_private := self'.ratchet_private, pending_initial := none } :=
  (decrypt_frame rc crc self message rng _ _ _ h).2 v rfl

/-! ## `establish_responder` -/

theorem establish_responder_frame {R : Type}
    (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R)
    (identity : lifecycle.Identity) (store : lifecycle.PrekeyStore)
    (message : Slice U8) (rng : R) :
    Post (ResponderFrame store) (lifecycle.establish_responder rc crc identity store message rng) := by
  unfold lifecycle.establish_responder
  repeat' first
    | (apply Post.bind; intro _ _)
    | split
    | (apply Post.leaf; intro e he; first | rfl | (cases he))

/-- A refused `establish_responder` returns the prekey store it was given, field for field. The
one-time removals and the replay-record append come after the inner authenticated receive. -/
theorem establish_responder_err_leaves_store {R : Type}
    (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R)
    (identity : lifecycle.Identity) (store : lifecycle.PrekeyStore)
    (message : Slice U8) (rng : R)
    (e : lifecycle.Error) (store' : lifecycle.PrekeyStore) (rng' : R)
    (h : lifecycle.establish_responder rc crc identity store message rng =
      ok (core.result.Result.Err e, store', rng')) :
    store' = store :=
  (establish_responder_frame rc crc identity store message rng _ _ _ h) e rfl

/-! ## `encrypt` -/

/-- The first two binds and the check of the agreement's next state are taken by hand because that
check is the one place a refusal writes; the rest is the generic walk. -/
theorem encrypt_frame {R : Type}
    (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R)
    (self : lifecycle.Session) (plaintext : Slice U8) (rng : R) :
    Post (EncryptFrame self) (lifecycle.Session.encrypt rc crc self plaintext rng) := by
  unfold lifecycle.Session.encrypt
  apply Post.bind; intro guard _
  split
  · apply Post.leaf
    refine ⟨fun e he => ?_, fun v hv => ?_⟩ <;> first | (exact Or.inl rfl) | rfl
  · apply Post.bind; intro sent _
    rcases sent with ⟨⟨agMsg, sendingEpoch, output, braidNext⟩, rng1⟩
    try dsimp only
    apply Post.bind; intro failedNext hfailed
    split
    · rename_i hnext
      apply Post.leaf
      refine ⟨fun e he => ?_, fun v hv => (by cases hv)⟩
      simp at he
      subst he
      refine Or.inr ⟨rfl, braidNext, rfl, ?_⟩
      rw [hnext] at hfailed
      exact hfailed
    · apply Post.bind; intro spqrOutput _
      apply Post.bind; intro candidateAndSent _
      rcases candidateAndSent with ⟨candidate, sent⟩
      dsimp only [Aeneas.Std.uncurry]
      split
      · repeat' first
          | (apply Post.bind; intro _ _)
          | split
          | (apply Post.leaf
             refine ⟨fun e he => ?_, fun v hv => ?_⟩ <;>
               first | (exact Or.inl rfl) | rfl | (cases he))
      · apply Post.leaf
        refine ⟨fun e he => ?_, fun v hv => ?_⟩ <;>
          first | (exact Or.inl rfl) | rfl

/-- A refused `encrypt` returns the session it was given, except that an agreement send that
reaches the terminal state is committed, with the error `AgreementFailed`. -/
theorem encrypt_err_leaves_state {R : Type}
    (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R)
    (self : lifecycle.Session) (plaintext : Slice U8) (rng : R)
    (e : lifecycle.Error) (self' : lifecycle.Session) (rng' : R)
    (h : lifecycle.Session.encrypt rc crc self plaintext rng =
      ok (core.result.Result.Err e, self', rng')) :
    self' = self ∨ (e = lifecycle.Error.AgreementFailed ∧
      ∃ b, self' = { self with braid := b } ∧ tacenta_braid.Braid.failed b = ok true) :=
  (encrypt_frame rc crc self plaintext rng _ _ _ h).1 e rfl

/-- A successful `encrypt` writes the Triple Ratchet and the agreement and nothing else. In
particular it never clears `pending_initial`: an initiator keeps wrapping its messages until a
decrypt succeeds. -/
theorem encrypt_ok_writes {R : Type}
    (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R)
    (self : lifecycle.Session) (plaintext : Slice U8) (rng : R)
    (v : alloc.vec.Vec U8) (self' : lifecycle.Session) (rng' : R)
    (h : lifecycle.Session.encrypt rc crc self plaintext rng =
      ok (core.result.Result.Ok v, self', rng')) :
    self' = { self with triple := self'.triple, braid := self'.braid } :=
  (encrypt_frame rc crc self plaintext rng _ _ _ h).2 v rfl

/-! ## The terminal refusal arms

The statements above say nothing if no call refuses. What is shown here is one case, the terminal
one: for every session whose agreement reports failed, `encrypt`, `decrypt_ratchet` and `decrypt`
on an empty message each refuse with `AgreementFailed` and return the session they were given.
`braid_failed_of_failed_state` shows that `Braid::failed` reports true of the closed value
`State::Failed`, so the hypothesis is not empty as a statement about the agreement. These
results are stated for every such session and do not exhibit one: `lifecycle.Session` has fields
of the opaque key types `tacenta_boundary.dh.PrivateKey` and `PublicKeyBytes`, no inhabitant of
which is derivable here, so that a `Session` value exists is not shown in Lean.

Nothing here shows that any success arm, or any other refusal arm, is reached: no premise of the
`_ok_writes` theorems is shown to hold of any run, and the arms for a refused initial message, a
refused repeat and a refused responder establishment are reached, if at all, by the Rust tests
named in `CLAIMS.md` (`failed_decrypt_changes_nothing.rs` and the unit test
`a_failed_triple_send_does_not_commit_the_agreement` in `lifecycle.rs`), not by a theorem. -/

theorem braid_failed_of_failed_state :
    tacenta_braid.Braid.failed { state := tacenta_braid.State.Failed } = ok true := by
  unfold tacenta_braid.Braid.failed
  rfl

theorem encrypt_refuses_failed_agreement {R : Type}
    (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R)
    (self : lifecycle.Session) (plaintext : Slice U8) (rng : R)
    (h : tacenta_braid.Braid.failed self.braid = ok true) :
    lifecycle.Session.encrypt rc crc self plaintext rng =
      ok (core.result.Result.Err lifecycle.Error.AgreementFailed, self, rng) := by
  unfold lifecycle.Session.encrypt
  simp [h]

theorem decrypt_ratchet_refuses_failed_agreement {R : Type}
    (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R)
    (self : lifecycle.Session) (message : Slice U8) (rng : R)
    (h : tacenta_braid.Braid.failed self.braid = ok true) :
    lifecycle.Session.decrypt_ratchet rc crc self message rng =
      ok (core.result.Result.Err lifecycle.Error.AgreementFailed, self, rng) := by
  unfold lifecycle.Session.decrypt_ratchet
  simp [h]

/-- `decrypt` on an empty message is not an initial message, so it goes to `decrypt_ratchet`, which
refuses a failed agreement. -/
theorem decrypt_empty_message_refuses_failed_agreement {R : Type}
    (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R)
    (self : lifecycle.Session) (rng : R)
    (h : tacenta_braid.Braid.failed self.braid = ok true) :
    lifecycle.Session.decrypt rc crc self (⟨[], by scalar_tac⟩ : Slice U8) rng =
      ok (core.result.Result.Err lifecycle.Error.AgreementFailed, self, rng) := by
  have hmt : serialization.message_type (⟨[], by scalar_tac⟩ : Slice U8) = ok none := by
    unfold serialization.message_type
    simp [Slice.len]
  unfold lifecycle.Session.decrypt
  rw [hmt]
  simp only [bind_tc_ok]
  have hdr := decrypt_ratchet_refuses_failed_agreement rc crc self
    (alloc.vec.Vec.deref (⟨[], by scalar_tac⟩ : alloc.vec.Vec U8)) rng h
  have hv : alloc.slice.Slice.to_vec core.clone.CloneU8 (⟨[], by scalar_tac⟩ : Slice U8) =
      ok ⟨[], by scalar_tac⟩ := by
    unfold alloc.slice.Slice.to_vec
    simp [Slice.clone, List.clone]
    rfl
  rw [hv]
  simp only [bind_tc_ok]
  have hd : alloc.vec.Vec.deref (⟨[], by scalar_tac⟩ : alloc.vec.Vec U8) =
      (⟨[], by scalar_tac⟩ : Slice U8) := rfl
  rw [hd] at hdr ⊢
  rw [hdr]
  simp [core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]

end Tacenta.UnitLifecycleAtomicity

/--
info: 'Tacenta.UnitLifecycleAtomicity.decrypt_ratchet_err_leaves_state' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kdf.hkdf_sha256,
 tacenta_session_unit.tacenta_kdf.hmac_sha256,
 tacenta_session_unit.tacenta_kem.CT1_LEN,
 tacenta_session_unit.tacenta_kem.CT2_LEN,
 tacenta_session_unit.tacenta_kem.EK_VECTOR_LEN,
 tacenta_session_unit.tacenta_kem.EncapsState,
 tacenta_session_unit.tacenta_kem.HEADER_LEN,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair,
 tacenta_session_unit.tacenta_kem.encapsulate2,
 tacenta_session_unit.tacenta_kem.validate_ek,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.rand_core_1.error.Error,
 tacenta_session_unit.tacenta_boundary.aead.decrypt,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_session_unit.zeroize.Zeroizing.new,
 tacenta_session_unit.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.Pair.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.TupleABC.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.alloc.vec.Vec.capacity,
 tacenta_session_unit.alloc.vec.Vec.pop,
 tacenta_session_unit.alloc.vec.Vec.truncate,
 tacenta_session_unit.core.num.Usize.div_ceil,
 tacenta_session_unit.core.option.Option.as_mut,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.agree,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.from_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.public_key,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.from_bytes,
 tacenta_session_unit.zeroize.Zeroize.Blanket.zeroize,
 tacenta_session_unit.tacenta_kem.EncapsState.Insts.CoreCloneClone.clone,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 tacenta_session_unit.alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.core.option.Option.Insts.CoreCloneClone.clone,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleAtomicity.decrypt_ratchet_err_leaves_state

/--
info: 'Tacenta.UnitLifecycleAtomicity.decrypt_ratchet_ok_writes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kdf.hkdf_sha256,
 tacenta_session_unit.tacenta_kdf.hmac_sha256,
 tacenta_session_unit.tacenta_kem.CT1_LEN,
 tacenta_session_unit.tacenta_kem.CT2_LEN,
 tacenta_session_unit.tacenta_kem.EK_VECTOR_LEN,
 tacenta_session_unit.tacenta_kem.EncapsState,
 tacenta_session_unit.tacenta_kem.HEADER_LEN,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair,
 tacenta_session_unit.tacenta_kem.encapsulate2,
 tacenta_session_unit.tacenta_kem.validate_ek,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.rand_core_1.error.Error,
 tacenta_session_unit.tacenta_boundary.aead.decrypt,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_session_unit.zeroize.Zeroizing.new,
 tacenta_session_unit.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.Pair.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.TupleABC.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.alloc.vec.Vec.capacity,
 tacenta_session_unit.alloc.vec.Vec.pop,
 tacenta_session_unit.alloc.vec.Vec.truncate,
 tacenta_session_unit.core.num.Usize.div_ceil,
 tacenta_session_unit.core.option.Option.as_mut,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.agree,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.from_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.public_key,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.from_bytes,
 tacenta_session_unit.zeroize.Zeroize.Blanket.zeroize,
 tacenta_session_unit.tacenta_kem.EncapsState.Insts.CoreCloneClone.clone,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 tacenta_session_unit.alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.core.option.Option.Insts.CoreCloneClone.clone,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleAtomicity.decrypt_ratchet_ok_writes

/--
info: 'Tacenta.UnitLifecycleAtomicity.decrypt_err_leaves_state' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kdf.hkdf_sha256,
 tacenta_session_unit.tacenta_kdf.hmac_sha256,
 tacenta_session_unit.tacenta_kem.CT1_LEN,
 tacenta_session_unit.tacenta_kem.CT2_LEN,
 tacenta_session_unit.tacenta_kem.EK_VECTOR_LEN,
 tacenta_session_unit.tacenta_kem.EncapsState,
 tacenta_session_unit.tacenta_kem.HEADER_LEN,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair,
 tacenta_session_unit.tacenta_kem.encapsulate2,
 tacenta_session_unit.tacenta_kem.validate_ek,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.rand_core_1.error.Error,
 tacenta_session_unit.tacenta_boundary.aead.decrypt,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_session_unit.zeroize.Zeroizing.new,
 tacenta_session_unit.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.Pair.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.TupleABC.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.alloc.vec.Vec.capacity,
 tacenta_session_unit.alloc.vec.Vec.pop,
 tacenta_session_unit.alloc.vec.Vec.truncate,
 tacenta_session_unit.core.num.Usize.div_ceil,
 tacenta_session_unit.core.option.Option.as_mut,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.agree,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.from_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.public_key,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.from_bytes,
 tacenta_session_unit.zeroize.Zeroize.Blanket.zeroize,
 tacenta_session_unit.tacenta_kem.EncapsState.Insts.CoreCloneClone.clone,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 tacenta_session_unit.alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.core.option.Option.Insts.CoreCloneClone.clone,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleAtomicity.decrypt_err_leaves_state

/--
info: 'Tacenta.UnitLifecycleAtomicity.decrypt_ok_writes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kdf.hkdf_sha256,
 tacenta_session_unit.tacenta_kdf.hmac_sha256,
 tacenta_session_unit.tacenta_kem.CT1_LEN,
 tacenta_session_unit.tacenta_kem.CT2_LEN,
 tacenta_session_unit.tacenta_kem.EK_VECTOR_LEN,
 tacenta_session_unit.tacenta_kem.EncapsState,
 tacenta_session_unit.tacenta_kem.HEADER_LEN,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair,
 tacenta_session_unit.tacenta_kem.encapsulate2,
 tacenta_session_unit.tacenta_kem.validate_ek,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.rand_core_1.error.Error,
 tacenta_session_unit.tacenta_boundary.aead.decrypt,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_session_unit.zeroize.Zeroizing.new,
 tacenta_session_unit.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.Pair.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.TupleABC.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.alloc.vec.Vec.capacity,
 tacenta_session_unit.alloc.vec.Vec.pop,
 tacenta_session_unit.alloc.vec.Vec.truncate,
 tacenta_session_unit.core.num.Usize.div_ceil,
 tacenta_session_unit.core.option.Option.as_mut,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.agree,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.from_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.public_key,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.from_bytes,
 tacenta_session_unit.zeroize.Zeroize.Blanket.zeroize,
 tacenta_session_unit.tacenta_kem.EncapsState.Insts.CoreCloneClone.clone,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 tacenta_session_unit.alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.core.option.Option.Insts.CoreCloneClone.clone,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleAtomicity.decrypt_ok_writes

/--
info: 'Tacenta.UnitLifecycleAtomicity.establish_responder_err_leaves_store' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kdf.hkdf_sha256,
 tacenta_session_unit.tacenta_kdf.hmac_sha256,
 tacenta_session_unit.tacenta_kem.CT1_LEN,
 tacenta_session_unit.tacenta_kem.CT2_LEN,
 tacenta_session_unit.tacenta_kem.EK_VECTOR_LEN,
 tacenta_session_unit.tacenta_kem.EncapsState,
 tacenta_session_unit.tacenta_kem.HEADER_LEN,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair,
 tacenta_session_unit.tacenta_kem.encapsulate2,
 tacenta_session_unit.tacenta_kem.validate_ek,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.rand_core_1.error.Error,
 tacenta_session_unit.tacenta_boundary.aead.decrypt,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_boundary.dh.is_prime_order_public,
 tacenta_session_unit.tacenta_boundary.kem.KeyPair,
 tacenta_session_unit.tacenta_boundary.kem.decapsulate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_session_unit.zeroize.Zeroizing.new,
 tacenta_session_unit.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.Pair.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.TupleABC.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.alloc.vec.Vec.capacity,
 tacenta_session_unit.alloc.vec.Vec.pop,
 tacenta_session_unit.alloc.vec.Vec.truncate,
 tacenta_session_unit.core.num.Usize.div_ceil,
 tacenta_session_unit.core.option.Option.as_mut,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.agree,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.from_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.public_key,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.from_bytes,
 tacenta_session_unit.zeroize.Zeroize.Blanket.zeroize,
 tacenta_session_unit.tacenta_kem.EncapsState.Insts.CoreCloneClone.clone,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 tacenta_session_unit.alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.core.option.Option.Insts.CoreCloneClone.clone,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleAtomicity.establish_responder_err_leaves_store

/--
info: 'Tacenta.UnitLifecycleAtomicity.encrypt_err_leaves_state' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kdf.hkdf_sha256,
 tacenta_session_unit.tacenta_kdf.hmac_sha256,
 tacenta_session_unit.tacenta_kem.EncapsState,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair,
 tacenta_session_unit.tacenta_kem.encapsulate1,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.rand_core_1.error.Error,
 tacenta_session_unit.tacenta_boundary.aead.encrypt,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.generate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.header,
 tacenta_session_unit.zeroize.Zeroizing.new,
 tacenta_session_unit.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.Pair.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.TupleABC.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.alloc.vec.Vec.capacity,
 tacenta_session_unit.alloc.vec.Vec.pop,
 tacenta_session_unit.core.num.Usize.div_ceil,
 tacenta_session_unit.core.option.Option.as_mut,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_session_unit.zeroize.Zeroize.Blanket.zeroize,
 tacenta_session_unit.tacenta_kem.EncapsState.Insts.CoreCloneClone.clone,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 tacenta_session_unit.alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.core.option.Option.Insts.CoreCloneClone.clone,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleAtomicity.encrypt_err_leaves_state

/--
info: 'Tacenta.UnitLifecycleAtomicity.encrypt_ok_writes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kdf.hkdf_sha256,
 tacenta_session_unit.tacenta_kdf.hmac_sha256,
 tacenta_session_unit.tacenta_kem.EncapsState,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair,
 tacenta_session_unit.tacenta_kem.encapsulate1,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.rand_core_1.error.Error,
 tacenta_session_unit.tacenta_boundary.aead.encrypt,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.generate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.header,
 tacenta_session_unit.zeroize.Zeroizing.new,
 tacenta_session_unit.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.Pair.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.TupleABC.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.alloc.vec.Vec.capacity,
 tacenta_session_unit.alloc.vec.Vec.pop,
 tacenta_session_unit.core.num.Usize.div_ceil,
 tacenta_session_unit.core.option.Option.as_mut,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_session_unit.zeroize.Zeroize.Blanket.zeroize,
 tacenta_session_unit.tacenta_kem.EncapsState.Insts.CoreCloneClone.clone,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 tacenta_session_unit.alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.core.option.Option.Insts.CoreCloneClone.clone,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleAtomicity.encrypt_ok_writes

/-! ## Statement pins

The axiom pins above hold the constants a result depends on and not what it says. These hold the
statements of the seven results, so that a weaker statement, a stronger hypothesis or a different
conclusion fails the module. -/

/--
info: Tacenta.UnitLifecycleAtomicity.decrypt_ratchet_err_leaves_state {R : Type}
  (rc : tacenta_session_unit.rand_core_1.RngCore R) (crc : tacenta_session_unit.rand_core_1.CryptoRng R)
  (self : tacenta_session_unit.lifecycle.Session) (message : Aeneas.Std.Slice Aeneas.Std.U8) (rng : R)
  (e : tacenta_session_unit.lifecycle.Error) (self' : tacenta_session_unit.lifecycle.Session) (rng' : R)
  (h :
    tacenta_session_unit.lifecycle.Session.decrypt_ratchet rc crc self message rng =
      Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Err e, self', rng')) :
  self' = self
-/
#guard_msgs in
#check Tacenta.UnitLifecycleAtomicity.decrypt_ratchet_err_leaves_state

/--
info: Tacenta.UnitLifecycleAtomicity.decrypt_ratchet_ok_writes {R : Type} (rc : tacenta_session_unit.rand_core_1.RngCore R)
  (crc : tacenta_session_unit.rand_core_1.CryptoRng R) (self : tacenta_session_unit.lifecycle.Session)
  (message : Aeneas.Std.Slice Aeneas.Std.U8) (rng : R) (v : Aeneas.Std.alloc.vec.Vec Aeneas.Std.U8)
  (self' : tacenta_session_unit.lifecycle.Session) (rng' : R)
  (h :
    tacenta_session_unit.lifecycle.Session.decrypt_ratchet rc crc self message rng =
      Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok v, self', rng')) :
  self' =
    { triple := self'.triple, braid := self'.braid, ratchet_private := self'.ratchet_private,
      identity_ad := self.identity_ad, our_identity_public := self.our_identity_public,
      peer_identity_public := self.peer_identity_public, pending_initial := self.pending_initial,
      established_ephemeral := self.established_ephemeral }
-/
#guard_msgs in
#check Tacenta.UnitLifecycleAtomicity.decrypt_ratchet_ok_writes

/--
info: Tacenta.UnitLifecycleAtomicity.decrypt_err_leaves_state {R : Type} (rc : tacenta_session_unit.rand_core_1.RngCore R)
  (crc : tacenta_session_unit.rand_core_1.CryptoRng R) (self : tacenta_session_unit.lifecycle.Session)
  (message : Aeneas.Std.Slice Aeneas.Std.U8) (rng : R) (e : tacenta_session_unit.lifecycle.Error)
  (self' : tacenta_session_unit.lifecycle.Session) (rng' : R)
  (h :
    tacenta_session_unit.lifecycle.Session.decrypt rc crc self message rng =
      Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Err e, self', rng')) :
  self' = self
-/
#guard_msgs in
#check Tacenta.UnitLifecycleAtomicity.decrypt_err_leaves_state

/--
info: Tacenta.UnitLifecycleAtomicity.decrypt_ok_writes {R : Type} (rc : tacenta_session_unit.rand_core_1.RngCore R)
  (crc : tacenta_session_unit.rand_core_1.CryptoRng R) (self : tacenta_session_unit.lifecycle.Session)
  (message : Aeneas.Std.Slice Aeneas.Std.U8) (rng : R) (v : Aeneas.Std.alloc.vec.Vec Aeneas.Std.U8)
  (self' : tacenta_session_unit.lifecycle.Session) (rng' : R)
  (h :
    tacenta_session_unit.lifecycle.Session.decrypt rc crc self message rng =
      Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok v, self', rng')) :
  self' =
    { triple := self'.triple, braid := self'.braid, ratchet_private := self'.ratchet_private,
      identity_ad := self.identity_ad, our_identity_public := self.our_identity_public,
      peer_identity_public := self.peer_identity_public, pending_initial := none,
      established_ephemeral := self.established_ephemeral }
-/
#guard_msgs in
#check Tacenta.UnitLifecycleAtomicity.decrypt_ok_writes

/--
info: Tacenta.UnitLifecycleAtomicity.establish_responder_err_leaves_store {R : Type}
  (rc : tacenta_session_unit.rand_core_1.RngCore R) (crc : tacenta_session_unit.rand_core_1.CryptoRng R)
  (identity : tacenta_session_unit.lifecycle.Identity) (store : tacenta_session_unit.lifecycle.PrekeyStore)
  (message : Aeneas.Std.Slice Aeneas.Std.U8) (rng : R) (e : tacenta_session_unit.lifecycle.Error)
  (store' : tacenta_session_unit.lifecycle.PrekeyStore) (rng' : R)
  (h :
    tacenta_session_unit.lifecycle.establish_responder rc crc identity store message rng =
      Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Err e, store', rng')) :
  store' = store
-/
#guard_msgs in
#check Tacenta.UnitLifecycleAtomicity.establish_responder_err_leaves_store

/--
info: Tacenta.UnitLifecycleAtomicity.encrypt_err_leaves_state {R : Type} (rc : tacenta_session_unit.rand_core_1.RngCore R)
  (crc : tacenta_session_unit.rand_core_1.CryptoRng R) (self : tacenta_session_unit.lifecycle.Session)
  (plaintext : Aeneas.Std.Slice Aeneas.Std.U8) (rng : R) (e : tacenta_session_unit.lifecycle.Error)
  (self' : tacenta_session_unit.lifecycle.Session) (rng' : R)
  (h :
    tacenta_session_unit.lifecycle.Session.encrypt rc crc self plaintext rng =
      Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Err e, self', rng')) :
  self' = self ∨
    e = tacenta_session_unit.lifecycle.Error.AgreementFailed ∧
      ∃ b,
        self' =
            { triple := self.triple, braid := b, ratchet_private := self.ratchet_private,
              identity_ad := self.identity_ad, our_identity_public := self.our_identity_public,
              peer_identity_public := self.peer_identity_public, pending_initial := self.pending_initial,
              established_ephemeral := self.established_ephemeral } ∧
          b.failed = Aeneas.Std.Result.ok true
-/
#guard_msgs in
#check Tacenta.UnitLifecycleAtomicity.encrypt_err_leaves_state

/--
info: Tacenta.UnitLifecycleAtomicity.encrypt_ok_writes {R : Type} (rc : tacenta_session_unit.rand_core_1.RngCore R)
  (crc : tacenta_session_unit.rand_core_1.CryptoRng R) (self : tacenta_session_unit.lifecycle.Session)
  (plaintext : Aeneas.Std.Slice Aeneas.Std.U8) (rng : R) (v : Aeneas.Std.alloc.vec.Vec Aeneas.Std.U8)
  (self' : tacenta_session_unit.lifecycle.Session) (rng' : R)
  (h :
    tacenta_session_unit.lifecycle.Session.encrypt rc crc self plaintext rng =
      Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok v, self', rng')) :
  self' =
    { triple := self'.triple, braid := self'.braid, ratchet_private := self.ratchet_private,
      identity_ad := self.identity_ad, our_identity_public := self.our_identity_public,
      peer_identity_public := self.peer_identity_public, pending_initial := self.pending_initial,
      established_ephemeral := self.established_ephemeral }
-/
#guard_msgs in
#check Tacenta.UnitLifecycleAtomicity.encrypt_ok_writes
